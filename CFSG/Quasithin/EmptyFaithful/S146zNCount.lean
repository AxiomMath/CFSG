module

public import CFSG.Quasithin.EmptyFaithful.S146zNKlein
public import Certificates.Kernel.J4Count.FixCE

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section Generic

variable {G : Type} [Group G]


theorem comm_mem_swap {Z : Subgroup G} {a b : G} :
    a * b * a⁻¹ * b⁻¹ ∈ Z ↔ b * a * b⁻¹ * a⁻¹ ∈ Z := by
  have e : b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  rw [e, Subgroup.inv_mem_iff]

variable [Finite G]

theorem one_le_mIdx_centralizerMod {Z E X : Subgroup G} (hE : IsPGroup 2 E) {x w : G} (hx : x ∈ X)
    (hw : w ∈ E) (hn : x * w * x⁻¹ * w⁻¹ ∉ Z) : 1 ≤ mIdx E (centralizerMod Z E X) := by
  by_contra h
  have h0 : mIdx E (centralizerMod Z E X) = 0 := by omega
  have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := centralizerMod Z E X) hE
  rw [h0, pow_zero] at e1
  have hle : E ≤ centralizerMod Z E X := Subgroup.relIndex_eq_one.mp e1
  exact hn (comm_mem_swap.mp ((hle hw).2.2 x hx))

theorem eq_of_mIdx_le {E A B : Subgroup G} (hE : IsPGroup 2 E) (hAB : A ≤ B) (hBE : B ≤ E)
    (h : mIdx E A ≤ mIdx E B) : A = B := by
  have h1 := mIdx_add hE hBE hAB
  have h0 : mIdx B A = 0 := by omega
  have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := A) (hE.to_le hBE)
  rw [h0, pow_zero] at e1
  exact le_antisymm hAB (Subgroup.relIndex_eq_one.mp e1)

omit [Finite G] in
theorem centralizerMod_anti {Z E X Y : Subgroup G} (h : Y ≤ X) :
    centralizerMod Z E X ≤ centralizerMod Z E Y :=
  fun _ hu => ⟨hu.1, hu.2.1, fun e he => hu.2.2 e (h he)⟩

theorem centralizerMod_eq_zpowers {Z E X : Subgroup G} (hE : IsPGroup 2 E) {a w : G} (ha : a ∈ X)
    (hw : w ∈ E) (hn : a * w * a⁻¹ * w⁻¹ ∉ Z) (h1 : mIdx E (centralizerMod Z E X) = 1) :
    centralizerMod Z E X = centralizerMod Z E (Subgroup.zpowers a) := by
  have hanti : centralizerMod Z E X ≤ centralizerMod Z E (Subgroup.zpowers a) :=
    centralizerMod_anti (Subgroup.zpowers_le.mpr ha)
  have hge : 1 ≤ mIdx E (centralizerMod Z E (Subgroup.zpowers a)) :=
    one_le_mIdx_centralizerMod hE (Subgroup.mem_zpowers a) hw hn
  exact eq_of_mIdx_le hE hanti (centralizerMod_le_left _ _ _) (by omega)

end Generic

section Inner

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem CCtx.nontrivial_both (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) (haU₁ : conjSub a U₁ = U₁)
    (hnt : ¬ ∀ y ∈ U₁ ⊔ U₂, a * y * a⁻¹ * y⁻¹ ∈ Zz) :
    (∃ w ∈ U₁, a * w * a⁻¹ * w⁻¹ ∉ Zz) ∧ (∃ w ∈ U₂, a * w * a⁻¹ * w⁻¹ ∉ Zz) := by
  classical
  have hsZ := c.hsZ
  constructor
  · by_contra h
    push Not at h
    exact hnt (c.trivial_of_centralizes S haK haU haZ
      (c.centralizes_of_trivial₁ haK haZ (mem_normalizer_of_conjSub_eq haU₁) h))
  · by_contra h
    push Not at h
    set a' := s⁻¹ * a * s with ha'
    have ha'K : a' ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ c.hsK) haK) c.hsK
    have ha'Z : a' ∈ Subgroup.normalizer (Zz : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsZ) haZ) hsZ
    have ha'U₁ := c.conjSub_s_inner S haK haU haZ haU₁
    have hcent' := c.centralizes_of_trivial₁ ha'K ha'Z (mem_normalizer_of_conjSub_eq ha'U₁)
      (c.comm_conj_s h)
    have hcent : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro k hk
      have hk' : s⁻¹ * k * s ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ c.hsK) k).mp hk
        simpa using this
      have h2 := hcent' _ hk'
      have e : a * k * a⁻¹ * k⁻¹ =
          s * (a' * (s⁻¹ * k * s) * a'⁻¹ * (s⁻¹ * k * s)⁻¹) * s⁻¹ := by rw [ha']; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 K c.hsK) _).mp h2
    exact hnt (c.trivial_of_centralizes S haK haU haZ hcent)

theorem CCtx.swap_case (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {X : Subgroup G}
    (hXH : X ≤ mcOf T) (hXab : IsElemAbelian 2 X) {a : G} (haX : a ∈ X)
    (hsw : conjSub a U₁ = U₂) :
    3 ≤ mIdx (U₁ ⊔ U₂) (centralizerMod Zz (U₁ ⊔ U₂) X) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUKp : IsPGroup 2 ↥(U₁ ⊔ U₂) :=
    (isPGroup_of_isElemAbelian hUab).to_le (sup_le c.hU₁U c.hU₂U)
  have haZ : a ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact hXH haX
  have ha2 : a * a = 1 := by simpa [pow_two] using isElemAbelian_pow_eq_one hXab haX
  have h8 := c.not_swap S haZ ha2 hsw
  have hle : centralizerMod Zz (U₁ ⊔ U₂) X ≤ centralizerMod Zz (U₁ ⊔ U₂) (Subgroup.zpowers a) :=
    centralizerMod_anti (Subgroup.zpowers_le.mpr haX)
  have hdvd := Subgroup.relIndex_dvd_of_le_left (U₁ ⊔ U₂) hle
  have hpos : 0 < (centralizerMod Zz (U₁ ⊔ U₂) X).relIndex (U₁ ⊔ U₂) :=
    Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
  have h8' := h8.trans (Nat.le_of_dvd hpos hdvd)
  rw [HypF98.relIndex_eq_two_pow_mIdx hUKp] at h8'
  by_contra hlt
  have h2 : 2 ^ mIdx (U₁ ⊔ U₂) (centralizerMod Zz (U₁ ⊔ U₂) X) ≤ 4 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : mIdx (U₁ ⊔ U₂)
      (centralizerMod Zz (U₁ ⊔ U₂) X) ≤ 2)) (by norm_num)
  omega

theorem CCtx.inner_case (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {X : Subgroup G}
    (hXH : X ≤ mcOf T) (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hXab : IsElemAbelian 2 X)
    (hin : ∀ a ∈ X, conjSub a U₁ = U₁) (hn : ¬ X ≤ centralizerMod Zz X (U₁ ⊔ U₂)) :
    mIdx X (centralizerMod Zz X (U₁ ⊔ U₂)) + 1 ≤
      mIdx (U₁ ⊔ U₂) (centralizerMod Zz (U₁ ⊔ U₂) X) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hUKU : U₁ ⊔ U₂ ≤ uOfL22 T M := sup_le c.hU₁U c.hU₂U
  have hUKp : IsPGroup 2 ↥(U₁ ⊔ U₂) := hUp.to_le hUKU
  have hU₁p : IsPGroup 2 U₁ := hUp.to_le c.hU₁U
  have hU₂p : IsPGroup 2 U₂ := hUp.to_le c.hU₂U
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hXZ : X ≤ Subgroup.normalizer (Zz : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hXH he
  have hXU : X ≤ Subgroup.normalizer (uOfL22 T M : Set G) := fun e he =>
    le_normalizer_conjClosure _ _ (hXH he)
  have hin₂ : ∀ a ∈ X, conjSub a U₂ = U₂ := fun a ha =>
    c.conjSub_U₂ S (hXK ha) (hXU ha) (hXZ ha) (hin a ha)
  have hr2 := c.rank_le_two S hXH hXK hXab
  set X₀ := centralizerMod Zz X (U₁ ⊔ U₂) with hX₀
  have hsum : mIdx U₁ (centralizerMod Zz U₁ X) + mIdx U₂ (centralizerMod Zz U₂ X) ≤
      mIdx (U₁ ⊔ U₂) (centralizerMod Zz (U₁ ⊔ U₂) X) :=
    mIdx_centralizerMod_sum_le hUKp
      (fun x hx y hy => isElemAbelian_comm hUab (hUKU hx) (hUKU hy))
      le_sup_left le_sup_right c.hSec.le c.hZU₂ c.inf_U₂_eq (hUKU.trans hUN)
      (fun e he z hz => (Subgroup.mem_normalizer_iff.mp (hXZ he) z).mp hz)
      (fun e he y hy =>
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_conjSub_eq (hin e he)) y).mp hy)
      (fun e he y hy =>
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_conjSub_eq (hin₂ e he)) y).mp hy)
      (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
        (c.mem_normalizer_sup (hXK he) (hXU he) (hXZ he)) y).mp hy)
  have hnt : ∀ a ∈ X, a ∉ X₀ → (∃ w ∈ U₁, a * w * a⁻¹ * w⁻¹ ∉ Zz) ∧
      (∃ w ∈ U₂, a * w * a⁻¹ * w⁻¹ ∉ Zz) := by
    intro a ha han
    refine c.nontrivial_both S (hXK ha) (hXU ha) (hXZ ha) (hin a ha) ?_
    intro hall
    exact han ⟨ha, hXZ ha, hall⟩
  have hf : ∀ a ∈ X, a ∉ X₀ → 1 ≤ mIdx U₁ (centralizerMod Zz U₁ X) ∧
      1 ≤ mIdx U₂ (centralizerMod Zz U₂ X) := by
    intro a ha han
    obtain ⟨⟨w₁, hw₁, hn₁⟩, ⟨w₂, hw₂, hn₂⟩⟩ := hnt a ha han
    exact ⟨one_le_mIdx_centralizerMod hU₁p ha hw₁ hn₁,
      one_le_mIdx_centralizerMod hU₂p ha hw₂ hn₂⟩
  obtain ⟨x, hxX, hxX₀⟩ := IsConcreteLE.not_le_iff_exists.mp hn
  obtain ⟨hf₁, hf₂⟩ := hf x hxX hxX₀
  by_cases hr : mIdx X X₀ ≤ 1
  · omega
  have hrel : X₀.relIndex X = 2 ^ mIdx X X₀ :=
    HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hXab)
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => isElemAbelian_comm hXab ha hb
  obtain ⟨y, hyX, hyX₀, hxy⟩ : ∃ y ∈ X, y ∉ X₀ ∧ x⁻¹ * y ∉ X₀ := by
    by_contra hcon
    push Not at hcon
    have hcov : ∀ v ∈ X, ∃ r ∈ ({1, x⁻¹} : Finset G), v * r ∈ X₀ := by
      intro v hv
      by_cases hv₀ : v ∈ X₀
      · exact ⟨1, by simp, by simpa using hv₀⟩
      · refine ⟨x⁻¹, by simp, ?_⟩
        rw [hXcomm v hv x⁻¹ (X.inv_mem hxX)]
        exact hcon v hv hv₀
    have h1 := relIndex_le_card_of_cover (N := X₀) ({1, x⁻¹} : Finset G)
      (fun r hr => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact X.one_mem
        · exact X.inv_mem hxX) hcov
    have h2 : ({1, x⁻¹} : Finset G).card ≤ 2 := Finset.card_le_two
    rw [hrel] at h1
    have h3 : 2 ^ 2 ≤ 2 ^ mIdx X X₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hf₁y, hf₂y⟩ := hf y hyX hyX₀
  by_contra hcon
  have hf₁1 : mIdx U₁ (centralizerMod Zz U₁ X) = 1 := by omega
  have hf₂1 : mIdx U₂ (centralizerMod Zz U₂ X) = 1 := by omega
  have hx2 : x * x = 1 := by simpa [pow_two] using isElemAbelian_pow_eq_one hXab hxX
  have hy2 : y * y = 1 := by simpa [pow_two] using isElemAbelian_pow_eq_one hXab hyX
  obtain ⟨⟨wx₁, hwx₁, hnx₁⟩, ⟨wx₂, hwx₂, hnx₂⟩⟩ := hnt x hxX hxX₀
  obtain ⟨⟨wy₁, hwy₁, hny₁⟩, ⟨wy₂, hwy₂, hny₂⟩⟩ := hnt y hyX hyX₀
  have e₁x := centralizerMod_eq_zpowers hU₁p hxX hwx₁ hnx₁ hf₁1
  have e₁y := centralizerMod_eq_zpowers hU₁p hyX hwy₁ hny₁ hf₁1
  have e₂x := centralizerMod_eq_zpowers hU₂p hxX hwx₂ hnx₂ hf₂1
  have e₂y := centralizerMod_eq_zpowers hU₂p hyX hwy₂ hny₂ hf₂1
  have hA : ∀ u ∈ U₁, (x * u * x⁻¹ * u⁻¹ ∈ Zz ↔ y * u * y⁻¹ * u⁻¹ ∈ Zz) := by
    intro u hu
    have hN : u ∈ Subgroup.normalizer (Zz : Set G) := hUN (c.hU₁U hu)
    constructor
    · intro h
      have h1 : u ∈ centralizerMod Zz U₁ (Subgroup.zpowers x) :=
        (mem_centralizerMod_zpowers_iff hx2).mpr ⟨hu, hN, h⟩
      rw [← e₁x, e₁y] at h1
      exact ((mem_centralizerMod_zpowers_iff hy2).mp h1).2.2
    · intro h
      have h1 : u ∈ centralizerMod Zz U₁ (Subgroup.zpowers y) :=
        (mem_centralizerMod_zpowers_iff hy2).mpr ⟨hu, hN, h⟩
      rw [← e₁y, e₁x] at h1
      exact ((mem_centralizerMod_zpowers_iff hx2).mp h1).2.2
  have hB : ∀ u ∈ U₂, (x * u * x⁻¹ * u⁻¹ ∈ Zz ↔ y * u * y⁻¹ * u⁻¹ ∈ Zz) := by
    intro u hu
    have hN : u ∈ Subgroup.normalizer (Zz : Set G) := hUN (c.hU₂U hu)
    constructor
    · intro h
      have h1 : u ∈ centralizerMod Zz U₂ (Subgroup.zpowers x) :=
        (mem_centralizerMod_zpowers_iff hx2).mpr ⟨hu, hN, h⟩
      rw [← e₂x, e₂y] at h1
      exact ((mem_centralizerMod_zpowers_iff hy2).mp h1).2.2
    · intro h
      have h1 : u ∈ centralizerMod Zz U₂ (Subgroup.zpowers y) :=
        (mem_centralizerMod_zpowers_iff hy2).mpr ⟨hu, hN, h⟩
      rw [← e₂y, e₂x] at h1
      exact ((mem_centralizerMod_zpowers_iff hx2).mp h1).2.2
  have hact := c.act_eq_of_fix S (hXK hxX) (hXU hxX) (hXZ hxX) (hin x hxX) (hXK hyX) (hXU hyX)
    (hXZ hyX) (hin y hyX) hx2 hy2 ⟨wx₁, hwx₁, hnx₁⟩ ⟨wy₁, hwy₁, hny₁⟩ hA hB
  exact hxy ⟨X.mul_mem (X.inv_mem hxX) hyX,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXZ hxX)) (hXZ hyX), hact⟩

theorem CCtx.nff (S : Setting146 G T M) (c : CCtx T M K U₁ U₂ s) {X : Subgroup G}
    (hXH : X ≤ mcOf T) (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hXab : IsElemAbelian 2 X)
    (hn : ¬ X ≤ centralizerMod Zz X (U₁ ⊔ U₂)) :
    mIdx X (centralizerMod Zz X (U₁ ⊔ U₂)) + 1 ≤
      mIdx (U₁ ⊔ U₂) (centralizerMod Zz (U₁ ⊔ U₂) X) := by
  by_cases hsw : ∃ a ∈ X, conjSub a U₁ = U₂
  · obtain ⟨a, haX, hsw⟩ := hsw
    have h3 := c.swap_case S hXH hXab haX hsw
    have h2 := c.rank_le_two S hXH hXK hXab
    omega
  · push Not at hsw
    refine c.inner_case S hXH hXK hXab (fun a ha => ?_) hn
    have hXZ : a ∈ Subgroup.normalizer (Zz : Set G) := by rw [S.normalizer_Z]; exact hXH ha
    exact (c.normalizer_or S (hXK ha) (le_normalizer_conjClosure _ _ (hXH ha)) hXZ).resolve_right
      (hsw a ha)

end Inner

end CFSG.Quasithin.ThreeC

namespace CFSG.Quasithin

theorem input14624NonFF_proof : Input14624NonFF := by
  intro G _ _ T M S _ c19 K U₁ U₂ s hKc hL3 hdec X hXH hXK hXab hn
  have c := ThreeC.CCtx.ofDecomp S c19 hKc hL3 hdec
  have hsup := c.hsup
  rw [hsup] at hn ⊢
  exact c.nff S hXH hXK hXab hn

end CFSG.Quasithin
