module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrBase

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

section Dictionary

variable {n : ℕ} {M : Model n} {K L X : Subgroup G} [(L.subgroupOf X).Normal]
  {Ψ : ↥K →* Equiv.Perm (Fin n)} {β : M.W →* ↥X ⧸ L.subgroupOf X}

theorem SecData.conj_mem (h : SecData M K L X Ψ β) {k : G} (hk : k ∈ K) {x : G} (hx : x ∈ X) :
    k * x * k⁻¹ ∈ X := by
  obtain ⟨u, hu⟩ := h.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
  exact (h.equiv ⟨k, hk⟩ u ⟨x, hx⟩ hu).1

theorem SecData.beta_comm (h : SecData M K L X Ψ β) {a : G} (haK : a ∈ K) {u : M.W} {x : ↥X}
    (hu : β u = QuotientGroup.mk x) :
    ∃ hax : a * (x : G) * a⁻¹ * (x : G)⁻¹ ∈ X,
      β (M.act (Ψ ⟨a, haK⟩) u * u⁻¹) = QuotientGroup.mk ⟨a * (x : G) * a⁻¹ * (x : G)⁻¹, hax⟩ := by
  obtain ⟨hax, h1⟩ := h.equiv ⟨a, haK⟩ u x hu
  have hax' : a * (x : G) * a⁻¹ * (x : G)⁻¹ ∈ X := X.mul_mem hax (X.inv_mem x.2)
  refine ⟨hax', ?_⟩
  rw [map_mul, map_inv, h1, hu, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

theorem SecData.relIndex_fixSecIn {A : Subgroup G} (h : SecData M K L X Ψ β) (hLX : L ≤ X)
    (hAK : A ≤ K) :
    (fixSecIn A L X).relIndex X = (fixW M ((A.subgroupOf K).map Ψ)).index := by
  have hcomap : (fixSecIn A L X).subgroupOf X =
      ((fixW M ((A.subgroupOf K).map Ψ)).map β).comap (QuotientGroup.mk' (L.subgroupOf X)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_map, X1512.mem_fixSecIn hLX]
    constructor
    · rintro ⟨-, hx⟩
      obtain ⟨u, hu⟩ := h.surj (QuotientGroup.mk x)
      refine ⟨u, ?_, hu⟩
      rintro σ ⟨a', ha', rfl⟩
      obtain ⟨hax, h'⟩ := h.equiv a' u x hu
      apply h.inj
      rw [h', hu]
      exact ((X1512.mk_eq_iff hLX).mpr (hx a' (Subgroup.mem_subgroupOf.mp ha'))).symm
    · rintro ⟨u, hu, hux⟩
      refine ⟨x.2, fun a ha => ?_⟩
      have haK : a ∈ K := hAK ha
      have hux' : β u = QuotientGroup.mk x := hux
      obtain ⟨hax, h'⟩ := h.equiv ⟨a, haK⟩ u x hux'
      have hfix := hu (Ψ ⟨a, haK⟩) ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hfix, hux'] at h'
      exact (X1512.mk_eq_iff hLX).mp h'
  unfold Subgroup.relIndex
  rw [hcomap]
  refine (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)).trans ?_
  exact Subgroup.index_map_of_bijective ⟨h.inj, h.surj⟩ _

theorem SecData.commutator_le (h : SecData M K L X Ψ β) {A : Subgroup G} (hAK : A ≤ K) :
    ⁅X, A⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have h1 := h.conj_mem (hAK ha) (X.inv_mem hx)
  have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact X.mul_mem hx h1

theorem SecData.map_commW (h : SecData M K L X Ψ β) (hLX : L ≤ X) {A : Subgroup G}
    (hAK : A ≤ K) :
    (commW M ((A.subgroupOf K).map Ψ) ⊤).map β =
      ((commSec A L X).subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) := by
  apply le_antisymm
  ·
    unfold commW
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨σ, ⟨a', ha', rfl⟩, u, -, rfl⟩, rfl⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
    obtain ⟨hax, h1⟩ := h.beta_comm a'.2 hx.symm
    have hmem : a' * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹ ∈ commSec A L X := by
      have e : (a' : G) * (x : G) * (a' : G)⁻¹ * (x : G)⁻¹ = (⁅(x : G), (a' : G)⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      refine Subgroup.mem_sup_left ?_
      rw [e]
      exact ⁅X, A⁆.inv_mem (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_subgroupOf.mp ha'))
    exact ⟨⟨_, hax⟩, hmem, h1.symm⟩
  ·
    set S' := (commW M ((A.subgroupOf K).map Ψ) ⊤).map β with hS'
    rw [Subgroup.map_le_iff_le_comap]
    have hC : commSec A L X ≤ (S'.comap (QuotientGroup.mk' (L.subgroupOf X))).map X.subtype := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx a ha
        have haK : a ∈ K := hAK ha
        have hcx : ⁅x, a⁆ ∈ X := h.commutator_le hAK (Subgroup.commutator_mem_commutator hx ha)
        refine ⟨⟨⁅x, a⁆, hcx⟩, ?_, rfl⟩
        obtain ⟨u, hu⟩ := h.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
        obtain ⟨hax, h1⟩ := h.beta_comm haK hu
        have hg : M.act (Ψ ⟨a, haK⟩) u * u⁻¹ ∈ commW M ((A.subgroupOf K).map Ψ) ⊤ :=
          Subgroup.subset_closure ⟨Ψ ⟨a, haK⟩, ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, u,
            Subgroup.mem_top _, rfl⟩
        have hinv : β ((M.act (Ψ ⟨a, haK⟩) u * u⁻¹)⁻¹) ∈ S' :=
          ⟨_, Subgroup.inv_mem _ hg, rfl⟩
        rw [map_inv, h1] at hinv
        show (QuotientGroup.mk' (L.subgroupOf X)) ⟨⁅x, a⁆, hcx⟩ ∈ S'
        have : (⟨⁅x, a⁆, hcx⟩ : ↥X) = (⟨a * x * a⁻¹ * x⁻¹, hax⟩ : ↥X)⁻¹ := by
          apply Subtype.ext
          simp only [commutatorElement_def, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
        rw [this]
        simpa using hinv
      · intro l hl
        refine ⟨⟨l, hLX hl⟩, ?_, rfl⟩
        show (QuotientGroup.mk' (L.subgroupOf X)) ⟨l, hLX hl⟩ ∈ S'
        have : (QuotientGroup.mk' (L.subgroupOf X)) ⟨l, hLX hl⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hl
        rw [this]
        exact S'.one_mem
    intro c hc
    obtain ⟨y, hy, hyc⟩ := hC (Subgroup.mem_subgroupOf.mp hc)
    have : y = c := Subtype.ext hyc
    rw [← this]
    exact hy

theorem SecData.card_commSec {A : Subgroup G} (h : SecData M K L X Ψ β) (hLX : L ≤ X)
    (hAK : A ≤ K) :
    L.relIndex (commSec A L X) = Nat.card (commW M ((A.subgroupOf K).map Ψ) ⊤) := by
  have hCX : commSec A L X ≤ X := sup_le (h.commutator_le hAK) hLX
  have hk : (QuotientGroup.mk' (L.subgroupOf X)).ker = L.subgroupOf X :=
    QuotientGroup.ker_mk' _
  have h1 : L.relIndex (commSec A L X) =
      Nat.card (((commSec A L X).subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X))) := by
    rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hCX]
  rw [h1, ← h.map_commW hLX hAK]
  exact Subgroup.card_map_of_injective h.inj

theorem SecData.quadratic_iff {A : Subgroup G} (h : SecData M K L X Ψ β) (hLX : L ≤ X)
    (hAK : A ≤ K) :
    ⁅commSec A L X, A⁆ ≤ L ↔
      commW M ((A.subgroupOf K).map Ψ) (commW M ((A.subgroupOf K).map Ψ) ⊤) = ⊥ := by
  have hmap := h.map_commW hLX hAK
  have hCX : commSec A L X ≤ X := sup_le (h.commutator_le hAK) hLX
  set V := commW M ((A.subgroupOf K).map Ψ) ⊤ with hV
  have hVC : ∀ w, w ∈ V ↔ ∃ c : ↥X, (c : G) ∈ commSec A L X ∧ β w = QuotientGroup.mk c := by
    intro w
    constructor
    · intro hw
      have : β w ∈ V.map β := ⟨w, hw, rfl⟩
      rw [hV, hmap] at this
      obtain ⟨c, hc, hcw⟩ := this
      exact ⟨c, Subgroup.mem_subgroupOf.mp hc, hcw.symm⟩
    · rintro ⟨c, hc, hcw⟩
      have : β w ∈ ((commSec A L X).subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) :=
        ⟨c, Subgroup.mem_subgroupOf.mpr hc, hcw.symm⟩
      rw [← hmap] at this
      obtain ⟨w', hw', hww'⟩ := this
      rw [← h.inj hww']
      exact hw'
  have hcomm : ∀ (a' : ↥K) (c : ↥X) (w : M.W), β w = QuotientGroup.mk c →
      (β (M.act (Ψ a') w * w⁻¹) = 1 ↔ ⁅(c : G), (a' : G)⁆ ∈ L) := by
    intro a' c w hw
    obtain ⟨hax, h1⟩ := h.beta_comm a'.2 hw
    have h1' : β (M.act (Ψ a') w * w⁻¹) = _ := h1
    rw [h1', QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show (a' : G) * (c : G) * (a' : G)⁻¹ * (c : G)⁻¹ ∈ L ↔ _
    have e : (a' : G) * (c : G) * (a' : G)⁻¹ * (c : G)⁻¹ = (⁅(c : G), (a' : G)⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact ⟨fun hh => by simpa using L.inv_mem hh, fun hh => L.inv_mem hh⟩
  unfold commW
  rw [Subgroup.closure_eq_bot_iff, Subgroup.commutator_le]
  constructor
  · intro hq w hw
    obtain ⟨b, hb, u, hu, rfl⟩ := hw
    obtain ⟨a', ha', rfl⟩ := hb
    obtain ⟨c, hc, hβ⟩ := (hVC u).mp hu
    have h2 := (hcomm a' c u hβ).mpr (hq _ hc _ (Subgroup.mem_subgroupOf.mp ha'))
    rw [← map_one β] at h2
    exact h.inj h2
  · intro hq c hc a ha
    have hcX : c ∈ X := hCX hc
    have haK : a ∈ K := hAK ha
    obtain ⟨w, hw⟩ := h.surj (QuotientGroup.mk (⟨c, hcX⟩ : ↥X))
    have hwV : w ∈ V := (hVC w).mpr ⟨⟨c, hcX⟩, hc, hw⟩
    have hgen : M.act (Ψ ⟨a, haK⟩) w * w⁻¹ ∈ {w | ∃ b ∈ Subgroup.map Ψ (A.subgroupOf K),
        ∃ u ∈ V, w = (M.act b) u * u⁻¹} :=
      ⟨Ψ ⟨a, haK⟩, ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, w, hwV, rfl⟩
    have h3 : M.act (Ψ ⟨a, haK⟩) w * w⁻¹ = 1 := hq hgen
    exact (hcomm ⟨a, haK⟩ ⟨c, hcX⟩ w hw).mp (by rw [h3, map_one])

theorem SecData.invariant_iff_sub {U K₀ : Subgroup G} (h : SecData M K L X Ψ β) (hK₀ : K₀ ≤ K)
    (hLU : L ≤ U) (hUX : U ≤ X) :
    (∀ k ∈ K₀, ∀ u ∈ U, k * u * k⁻¹ ∈ U) ↔
      ∃ Y : Subgroup M.W, (∀ σ ∈ (K₀.subgroupOf K).map Ψ, ∀ y ∈ Y, M.act σ y ∈ Y) ∧
        Y.map β = (U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) := by
  constructor
  · intro hU
    refine ⟨((U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X))).comap β, ?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩ y hy
      obtain ⟨c, hc, hcy⟩ := Subgroup.mem_comap.mp hy
      obtain ⟨hkc, h1⟩ := h.equiv k y c hcy.symm
      rw [Subgroup.mem_comap, h1]
      refine ⟨⟨(k : G) * c * (k : G)⁻¹, hkc⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (hU k (Subgroup.mem_subgroupOf.mp hk) c (Subgroup.mem_subgroupOf.mp hc))
    · exact Subgroup.map_comap_eq_self_of_surjective h.surj _
  · rintro ⟨Y, hY, hYm⟩ k hk u hu
    have hux : u ∈ X := hUX hu
    have hkK : k ∈ K := hK₀ hk
    have hmem : (QuotientGroup.mk' (L.subgroupOf X)) ⟨u, hux⟩ ∈ Y.map β := by
      rw [hYm]; exact ⟨⟨u, hux⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    obtain ⟨y, hy, hyu⟩ := hmem
    obtain ⟨hkx, h1⟩ := h.equiv ⟨k, hkK⟩ y ⟨u, hux⟩ hyu
    have h2 : β (M.act (Ψ ⟨k, hkK⟩) y) ∈ Y.map β :=
      ⟨_, hY _ ⟨⟨k, hkK⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩ y hy, rfl⟩
    rw [h1, hYm] at h2
    obtain ⟨c, hc, hcm⟩ := h2
    have h3 : (k * u * k⁻¹) * (c : G)⁻¹ ∈ L :=
      (X1512.mk_eq_iff (hLU.trans hUX)).mp hcm
    have h4 : (k * u * k⁻¹) = ((k * u * k⁻¹) * (c : G)⁻¹) * (c : G) := by group
    rw [h4]
    exact U.mul_mem (hLU h3) (Subgroup.mem_subgroupOf.mp hc)

theorem SecData.invariant_iff {U : Subgroup G} (h : SecData M K L X Ψ β)
    (hΨ : Function.Surjective Ψ) (hLU : L ≤ U) (hUX : U ≤ X) :
    (∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) ↔
      ∃ Y : Subgroup M.W, (∀ σ : Equiv.Perm (Fin n), ∀ y ∈ Y, M.act σ y ∈ Y) ∧
        Y.map β = (U.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) := by
  have hr : ∀ σ : Equiv.Perm (Fin n), σ ∈ (K.subgroupOf K).map Ψ := fun σ => by
    obtain ⟨k, rfl⟩ := hΨ σ
    exact ⟨k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  rw [h.invariant_iff_sub le_rfl hLU hUX]
  exact exists_congr fun Y => and_congr_left fun _ =>
    ⟨fun H σ => H σ (hr σ), fun H σ _ => H σ⟩

theorem SecData.secIdx_eq_idx (h : SecData M K L X Ψ β) (hLX : L ≤ X) {a : G} (ha : a ∈ K) :
    secIdx (Subgroup.zpowers a) L X = idx M (Ψ ⟨a, ha⟩) := by
  have hle : Subgroup.zpowers a ≤ K := (Subgroup.zpowers_le).mpr ha
  have h1 := h.relIndex_fixSecIn hLX hle
  have h2 : ((Subgroup.zpowers a).subgroupOf K).map Ψ = Subgroup.zpowers (Ψ ⟨a, ha⟩) := by
    have : (Subgroup.zpowers a).subgroupOf K = Subgroup.zpowers (⟨a, ha⟩ : ↥K) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, by simp⟩
    rw [this, MonoidHom.map_zpowers]
  unfold secIdx idx
  rw [h1, h2]

theorem SecData.relIndex_eq (h : SecData M K L X Ψ β) : L.relIndex X = Nat.card M.W := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective β ⟨h.inj, h.surj⟩)).symm

end Dictionary

theorem mem_cSecIn_iff_of_ker {n : ℕ} {F L X : Subgroup G} {θ : ↥F →* Equiv.Perm (Fin n)}
    (hk : θ.ker = (cSecIn F L X).subgroupOf F) {d : G} (hd : d ∈ F) :
    θ ⟨d, hd⟩ = 1 ↔ d ∈ cSecIn F L X := by
  rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf]

theorem IsModelSec.isSec {n : ℕ} {M : Model n} {F L X : Subgroup G} (h : IsModelSec M F L X)
    (hLX : L ≤ X) : IsSec F L X := by
  obtain ⟨hnorm, θ, β, -, -, hsd⟩ := h
  have hconj : ∀ k ∈ F, ∀ x ∈ X, k * x * k⁻¹ ∈ X := fun k hk x hx => hsd.conj_mem hk hx
  have hconjL : ∀ k ∈ F, ∀ l ∈ L, k * l * k⁻¹ ∈ L := by
    intro k hk l hl
    have hlX : l ∈ X := hLX hl
    have h1 : β 1 = QuotientGroup.mk (⟨l, hlX⟩ : ↥X) := by
      rw [map_one]
      exact ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hl)).symm
    obtain ⟨hkx, h2⟩ := hsd.equiv ⟨k, hk⟩ 1 ⟨l, hlX⟩ h1
    rw [map_one, map_one] at h2
    have := (QuotientGroup.eq_one_iff _).mp h2.symm
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨hLX, X1512.le_normalizer_of_forall hconj, X1512.le_normalizer_of_forall hconjL, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
    obtain ⟨v, hv⟩ := hsd.surj (QuotientGroup.mk (⟨y, hy⟩ : ↥X))
    have h1 : u * v * u⁻¹ * v⁻¹ = 1 := by
      rw [mul_comm u v, mul_inv_cancel_right, mul_inv_cancel]
    have h2 : β (u * v * u⁻¹ * v⁻¹) = 1 := by rw [h1, map_one]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu, hv] at h2
    have h3 : (QuotientGroup.mk (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥X)⁻¹ * (⟨y, hy⟩ : ↥X)⁻¹) :
        ↥X ⧸ L.subgroupOf X) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      exact h2
    have := (QuotientGroup.eq_one_iff _).mp h3
    simpa using Subgroup.mem_subgroupOf.mp this
  · intro x hx
    obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
    have h2 : β (u * u) = 1 := by rw [M.sq u, map_one]
    rw [map_mul, hu] at h2
    have h3 : (QuotientGroup.mk (⟨x, hx⟩ * (⟨x, hx⟩ : ↥X)) : ↥X ⧸ L.subgroupOf X) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact h2
    have := (QuotientGroup.eq_one_iff _).mp h3
    simpa [pow_two] using Subgroup.mem_subgroupOf.mp this

end CFSG.Quasithin.F53Mod
