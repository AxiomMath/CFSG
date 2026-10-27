module

public import CFSG.Quasithin.H13.A6S13827Gg
public import CFSG.Quasithin.H13.A6S13827Gh
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.A6S13827Gd

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem card_commV_le {F : Subgroup G} (hFH : F ≤ H) {Y : Subgroup G} (hYX : Y ≤ X)
    (hY : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ Y) :
    Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X))) ≤ W.relIndex Y := by
  have hle : commV (autSec (autOn F X) ⊤ (W.subgroupOf X)) ≤
      (Y.subgroupOf X).map (InternalSec.secMk (W.subgroupOf X)) := by
    refine G6.commV_le_iff.2 fun ψ hψ v => ?_
    obtain ⟨f, hfF, rfl⟩ := (hs.mem_autSec_iff hFH).1 hψ
    obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (W.subgroupOf X) v
    have hfx : (f : G) * x * (f : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hs.hHX f.2) x).mp x.2
    refine ⟨⟨(f : G) * x * (f : G)⁻¹ * (x : G)⁻¹, X.mul_mem hfx (X.inv_mem x.2)⟩,
      Subgroup.mem_subgroupOf.2 (hY f hfF x x.2), ?_⟩
    rw [act_secMk, ← map_inv, ← map_mul]
    congr 1
  have hker : (InternalSec.secMk (W.subgroupOf X)).ker = W.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, A6Mod.secMk_eq_one_iff, Subgroup.mem_subgroupOf]
  calc Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X)))
      ≤ Nat.card ((Y.subgroupOf X).map (InternalSec.secMk (W.subgroupOf X))) :=
        Subgroup.card_le_of_le hle
    _ = W.relIndex Y := by
        rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hYX]

theorem e4_of_fix
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) (h64 : W.relIndex X = 2 ^ 6) {F : Subgroup G}
    (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) (h4 : (F ⊓ pCoreOf 2 H).relIndex F ≤ 4)
    {x : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)} (hx : x ≠ 1)
    (hFx : x ∈ fixV (autSec (autOn F X) ⊤ (W.subgroupOf X)))
    (hn : ∀ k : ↥H, (k : G) ∈ K → hs.act k x = x →
      ∀ f ∈ F, (k : G) ^ 4 * f * ((k : G) ^ 4)⁻¹ ∈ F) :
    (F ⊓ pCoreOf 2 H).relIndex F = 4 ∧
      8 ≤ Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X))) := by
  obtain ⟨e, hKe, hHe⟩ := hs.exists_equiv_Q hU h64
  have hAH : autSec (autOn F X) ⊤ (W.subgroupOf X) ≤ autSec (autOn H X) ⊤ (W.subgroupOf X) :=
    hs.autSec_le hFH le_rfl
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hcard : Nat.card ((autSec (autOn F X) ⊤ (W.subgroupOf X)).map
      (MulAut.congr e).toMonoidHom) = Nat.card (autSec (autOn F X) ⊤ (W.subgroupOf X)) :=
    Subgroup.card_map_of_injective hinj
  have hAc := hs.card_autSec hFH
  have hZe := H13.isElemAbelian2_map_congr e (hs.isElemAbelian2_autSec hFH hFc hFs)
  have hex : e x ≠ 1 := fun h => hx (e.injective (h.trans (map_one e).symm))
  obtain ⟨h4', h8⟩ := A6G2.e4_of_fix hex (Z := (autSec (autOn F X) ⊤ (W.subgroupOf X)).map
      (MulAut.congr e).toMonoidHom)
    (by rintro _ ⟨ψ, hψ, rfl⟩; exact hHe ψ (hAH hψ))
    (fun h => hs.autSec_ne_bot hFH hF ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h))
    hZe.2 hZe.1 (by rw [hcard, hAc]; exact h4)
    (by
      rintro _ ⟨ψ, hψ, rfl⟩
      change MulAut.congr e ψ (e x) = e x
      rw [H13.congr_apply_eq, hFx ψ hψ])
    (by
      intro t ht htx z hz
      have htK : g2QAct (ZMod 2) t ∈ (autSec (autOn K X) ⊤ (W.subgroupOf X)).map
          (MulAut.congr e).toMonoidHom := by
        rw [hKe]
        exact ⟨t, ht, rfl⟩
      obtain ⟨ψ, hψ, hψt⟩ := htK
      obtain ⟨k, hkK, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
      have hkx : hs.act k x = x := by
        apply e.injective
        rw [← H13.congr_apply_eq]
        change (MulAut.congr e).toMonoidHom (hs.act k) (e x) = e x
        rw [hψt]
        exact htx
      obtain ⟨φ, hφ, rfl⟩ := hz
      obtain ⟨f, hfF, rfl⟩ := (hs.mem_autSec_iff hFH).1 hφ
      rw [← hψt]
      refine ⟨hs.act (k ^ 4 * f * (k ^ 4)⁻¹), (hs.mem_autSec_iff hFH).2 ⟨_, ?_, rfl⟩, ?_⟩
      · have := hn k hkK hkx f hfF
        simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] using this
      · simp only [map_mul, map_pow, map_inv])
  refine ⟨by rw [← hAc, ← hcard, h4'], ?_⟩
  rwa [H13.commV_map_congr, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    at h8

theorem card_le_four_of_not_le
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) {F F' : Subgroup G} (hFF' : F ≤ F') (hF'H : F' ≤ H)
    (hF'c : ∀ f ∈ F', ∀ f' ∈ F', f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hF's : ∀ f ∈ F', f * f ∈ pCoreOf 2 H) (hnot : ¬ F' ≤ F ⊔ pCoreOf 2 H) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ 4 := by
  have hAA' : autSec (autOn F X) ⊤ (W.subgroupOf X) ≤ autSec (autOn F' X) ⊤ (W.subgroupOf X) :=
    hs.autSec_le hFF' hF'H
  have hne : autSec (autOn F X) ⊤ (W.subgroupOf X) ≠ autSec (autOn F' X) ⊤ (W.subgroupOf X) := by
    intro h
    apply hnot
    intro v hv
    have h1 : hs.act ⟨v, hF'H hv⟩ ∈ autSec (autOn F X) ⊤ (W.subgroupOf X) :=
      h ▸ (hs.mem_autSec_iff hF'H).2 ⟨_, hv, rfl⟩
    obtain ⟨f, hfF, hf⟩ := (hs.mem_autSec_iff (hFF'.trans hF'H)).1 h1
    have h2 : hs.act (f⁻¹ * ⟨v, hF'H hv⟩) = 1 := by rw [map_mul, map_inv, hf, inv_mul_cancel]
    rw [hs.act_eq_one_iff] at h2
    have e : v = (f : G) * ((f⁻¹ * ⟨v, hF'H hv⟩ : ↥H) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hfF) (Subgroup.mem_sup_right h2)
  have h8 : Nat.card (autSec (autOn F' X) ⊤ (W.subgroupOf X)) ≤ 8 := by
    by_cases h1 : autSec (autOn F' X) ⊤ (W.subgroupOf X) = ⊥
    · rw [h1, Subgroup.card_bot]
      norm_num
    obtain ⟨r, -, hr, -, hr3, -⟩ := A6G2.short_generation (hs.autSec_le hs.hKH le_rfl)
      hs.autSec_le_normalizer hs.inf_centralizer_le (hs.b42TypeU33 hU) (hs.autSec_le hF'H le_rfl)
      h1 (hs.isElemAbelian2_autSec hF'H hF'c hF's)
    rw [hr]
    calc 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr3
      _ = 8 := by norm_num
  rw [← hs.card_autSec (hFF'.trans hF'H)]
  exact A6G2.card_le_four_of_lt hAA' hne h8

theorem eight_le_card_commV_of_large
    (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) (h12 : 2 ^ 12 < W.relIndex X) :
    8 ≤ Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X))) := by
  have hV : ∀ v : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs.sec_sq v
  have hAe := hs.isElemAbelian2_autSec hFH hFc hFs
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (hs.autSec_ne_bot hFH hF)
  have haA' : (a : MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) ∈
      autSec (autOn F X) ⊤ (W.subgroupOf X) := a.2
  set A₀ := Subgroup.zpowers (a : MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) with hA₀
  have hA₀A : A₀ ≤ autSec (autOn F X) ⊤ (W.subgroupOf X) := (Subgroup.zpowers_le).2 haA'
  have ha1' : (a : MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) ≠ 1 := fun h =>
    ha1 (Subtype.ext h)
  have hA₀1 : A₀ ≠ ⊥ := by
    intro h
    apply ha1'
    have : (a : MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) ∈ A₀ :=
      Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hA₀e : IsElemAbelian2 A₀ := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hAe.2 _ haA', one_zpow]
  obtain ⟨r, m, -, hr1, -, hmr, l, -, hle⟩ := A6G2.short_generation (hs.autSec_le hs.hKH le_rfl)
    hs.autSec_le_normalizer hs.inf_centralizer_le (hs.b42TypeU33 hU)
    (hA₀A.trans (hs.autSec_le hFH le_rfl)) hA₀1 hA₀e
  have hm6 : m ≤ 6 := by nlinarith
  have h1 := HatA6.card_le_pow_of_le_closure (hs.fixV_eq_bot hirr) l hle
  have hi0 : 0 < (fixV A₀).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hi : 4 < (fixV A₀).index := by
    by_contra hle4
    push Not at hle4
    have h2 : (fixV A₀).index ^ m ≤ 4 ^ 6 :=
      (Nat.pow_le_pow_left hle4 m).trans (Nat.pow_le_pow_right (by norm_num) hm6)
    rw [card_sec] at h1
    have : (4 : ℕ) ^ 6 = 2 ^ 12 := by norm_num
    omega
  have hc := card_commV_mul_card_fixV hV (a : MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))
  rw [← hA₀, ← (fixV A₀).card_mul_index] at hc
  have hpos : 0 < Nat.card (fixV A₀) := Nat.card_pos
  have hcA : Nat.card (commV A₀) = (fixV A₀).index :=
    Nat.eq_of_mul_eq_mul_right hpos (hc.trans (mul_comm _ _))
  obtain ⟨j, hj⟩ : ∃ j, Nat.card (commV A₀) = 2 ^ j :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one (fun v : ↥(commV A₀) =>
      Subtype.ext (by rw [Subgroup.coe_pow, hV, Subgroup.coe_one])))
  have hj3 : 3 ≤ j := by
    by_contra hj3
    push Not at hj3
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
    _ = Nat.card (commV A₀) := hj.symm
    _ ≤ Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X))) :=
        Subgroup.card_le_of_le (G6.commV_mono hA₀A)

@[expose] noncomputable def kHom : ↥K →* ↥(autSec (autOn K X) ⊤ (W.subgroupOf X)) :=
  (hs.act.comp (Subgroup.inclusion hs.hKH)).codRestrict _ fun k =>
    (hs.mem_autSec_iff hs.hKH).2 ⟨_, k.2, rfl⟩

theorem kHom_surjective : Function.Surjective hs.kHom := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
  exact ⟨⟨f, hf⟩, rfl⟩

theorem kHom_eq_one_iff (k : ↥K) : hs.kHom k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  rw [← Subtype.coe_inj]
  exact hs.act_eq_one_iff _

theorem exists_equivariant
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) {X₂ W₂ : Subgroup G} (hs₂ : S.SecHyp H K X₂ W₂)
    [IsMulCommutative ↥X₂] (h₁ : W.relIndex X = 2 ^ 6) (h₂ : W₂.relIndex X₂ = 2 ^ 6) :
    ∃ φ : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X) ≃* Sec (⊤ : Subgroup ↥X₂) (W₂.subgroupOf X₂),
      ∀ (h : ↥H) v, φ (hs.act h v) = hs₂.act h (φ v) := by
  have hker : hs.kHom.ker = hs₂.kHom.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hs.kHom_eq_one_iff, hs₂.kHom_eq_one_iff]
  let ψ : ↥(autSec (autOn K X) ⊤ (W.subgroupOf X)) ≃*
      ↥(autSec (autOn K X₂) ⊤ (W₂.subgroupOf X₂)) :=
    ((QuotientGroup.quotientKerEquivOfSurjective _ hs.kHom_surjective).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hs₂.kHom_surjective)
  have hψ : ∀ k : ↥K, ψ (hs.kHom k) = hs₂.kHom k := by
    intro k
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ hs.kHom_surjective).symm
        (hs.kHom k) = (k : ↥K ⧸ hs.kHom.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.quotientKerEquivOfSurjective _ hs₂.kHom_surjective)
      ((QuotientGroup.quotientMulEquivOfEq hker)
        ((QuotientGroup.quotientKerEquivOfSurjective _ hs.kHom_surjective).symm
          (hs.kHom k))) = hs₂.kHom k
    rw [h1]
    rfl
  set ρ₁ := (autSec (autOn K X) ⊤ (W.subgroupOf X)).subtype with hρ₁
  set ρ₂ := (autSec (autOn K X₂) ⊤ (W₂.subgroupOf X₂)).subtype.comp ψ.toMonoidHom with hρ₂
  have hi₁ : Function.Injective ρ₁ := Subgroup.subtype_injective _
  have hi₂ : Function.Injective ρ₂ := (Subgroup.subtype_injective _).comp ψ.injective
  have hr₁ : ρ₁.range = autSec (autOn K X) ⊤ (W.subgroupOf X) := Subgroup.range_subtype _
  have hr₂ : ρ₂.range = autSec (autOn K X₂) ⊤ (W₂.subgroupOf X₂) := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact (ψ l).2
    · intro hy
      obtain ⟨l, hl⟩ := ψ.surjective ⟨y, hy⟩
      exact ⟨l, by rw [hρ₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hl]; rfl⟩
  have hP₁ : B42TypeU33 ↥ρ₁.range :=
    A6G2.b42TypeU33_of_mulEquiv (MulEquiv.subgroupCongr hr₁.symm) (hs.b42TypeU33 hU)
  have hP₂ : B42TypeU33 ↥ρ₂.range :=
    A6G2.b42TypeU33_of_mulEquiv (MulEquiv.subgroupCongr hr₂.symm) (hs₂.b42TypeU33 hU)
  have hV₁ : ∀ v : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs.sec_sq v
  have hV₂ : ∀ v : Sec (⊤ : Subgroup ↥X₂) (W₂.subgroupOf X₂), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs₂.sec_sq v
  obtain ⟨φ, hφ⟩ := A6G2.exists_equivariant hV₁ hV₂ (by rw [card_sec, h₁])
    (by rw [card_sec, h₂]) hi₁ hi₂ hP₁ hP₂
  have hK : ∀ k : ↥H, (k : G) ∈ K → ∀ v, φ (hs.act k v) = hs₂.act k (φ v) := by
    intro k hk v
    have h1 := hφ (hs.kHom ⟨k, hk⟩) v
    have e1 : ρ₁ (hs.kHom ⟨k, hk⟩) = hs.act k := rfl
    have e2 : ρ₂ (hs.kHom ⟨k, hk⟩) = hs₂.act k := by
      rw [hρ₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ]
      rfl
    rw [e1, e2] at h1
    exact h1
  refine ⟨φ, fun h v => ?_⟩
  set φ' := ((hs.act h).trans φ).trans (hs₂.act h).symm with hφ'
  have hφ'K : ∀ l v, φ' (ρ₁ l v) = ρ₂ l (φ' v) := by
    intro l w
    obtain ⟨⟨k, hk⟩, rfl⟩ := hs.kHom_surjective l
    have e1 : ρ₁ (hs.kHom ⟨k, hk⟩) = hs.act (Subgroup.inclusion hs.hKH ⟨k, hk⟩) := rfl
    have e2 : ρ₂ (hs.kHom ⟨k, hk⟩) = hs₂.act (Subgroup.inclusion hs.hKH ⟨k, hk⟩) := by
      rw [hρ₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ]
      rfl
    rw [e1, e2]
    set k' : ↥H := Subgroup.inclusion hs.hKH ⟨k, hk⟩ with hk'
    have hk'K : ((h * k' * h⁻¹ : ↥H) : G) ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hs.hKn h.2) k).mp hk
      simpa [hk'] using this
    have e3 : hs.act h (hs.act k' w) = hs.act (h * k' * h⁻¹) (hs.act h w) := by
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
    have e4 : hs₂.act k' ((hs₂.act h).symm (φ (hs.act h w))) =
        (hs₂.act h).symm (hs₂.act (h * k' * h⁻¹) (φ (hs.act h w))) := by
      apply (hs₂.act h).injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv]
      rfl
    simp only [hφ', MulEquiv.trans_apply]
    rw [e3, hK _ hk'K, e4]
  have hU₁ := A6G2.equivariant_unique hV₁ (by rw [card_sec, h₁]) hP₁ hφ hφ'K
  have h1 : φ' v = φ v := by rw [hU₁]
  simp only [hφ', MulEquiv.trans_apply] at h1
  rw [← h1, MulEquiv.apply_symm_apply]

theorem card_commV_eq {X₂ W₂ : Subgroup G} (hs₂ : S.SecHyp H K X₂ W₂) [IsMulCommutative ↥X₂]
    {φ : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X) ≃* Sec (⊤ : Subgroup ↥X₂) (W₂.subgroupOf X₂)}
    (hφ : ∀ (h : ↥H) v, φ (hs.act h v) = hs₂.act h (φ v)) {F : Subgroup G} (hFH : F ≤ H) :
    Nat.card (commV (autSec (autOn F X₂) ⊤ (W₂.subgroupOf X₂))) =
      Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X))) := by
  have hmap : autSec (autOn F X₂) ⊤ (W₂.subgroupOf X₂) =
      (autSec (autOn F X) ⊤ (W.subgroupOf X)).map (MulAut.congr φ).toMonoidHom := by
    have hc : ∀ f : ↥H, MulAut.congr φ (hs.act f) = hs₂.act f := by
      intro f
      ext w
      rw [MulAut.congr_apply]
      change φ (hs.act f (φ.symm w)) = hs₂.act f w
      rw [hφ, MulEquiv.apply_symm_apply]
    ext ψ
    rw [hs₂.mem_autSec_iff hFH]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨hs.act f, (hs.mem_autSec_iff hFH).2 ⟨f, hf, rfl⟩, hc f⟩
    · rintro ⟨_, hψ', rfl⟩
      obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hFH).1 hψ'
      exact ⟨f, hf, (hc f).symm⟩
  rw [hmap, H13.commV_map_congr, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]

theorem eight_le_card_commV_of_chief
    (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) {X₀ W₀ : Subgroup G} (hs₀ : S.SecHyp H K X₀ W₀)
    [IsMulCommutative ↥X₀] (h64₀ : W₀.relIndex X₀ = 2 ^ 6)
    (h8₀ : 8 ≤ Nat.card (commV (autSec (autOn F X₀) ⊤ (W₀.subgroupOf X₀)))) :
    8 ≤ Nat.card (commV (autSec (autOn F X) ⊤ (W.subgroupOf X))) := by
  by_cases h12 : 2 ^ 12 < W.relIndex X
  · exact hs.eight_le_card_commV_of_large hU hirr hFH hF hFc hFs h12
  push Not at h12
  have hV : ∀ v : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs.sec_sq v
  have h64 : W.relIndex X = 2 ^ 6 := by
    rw [← card_sec]
    exact A6G2.card_eq_64_of_irr hV (hs.b42TypeU33 hU) (hs.isIrr_autSec_K hU hirr h12)
      (by rw [card_sec]; exact h12)
  obtain ⟨φ, hφ⟩ := hs₀.exists_equivariant hU hs h64₀ h64
  rw [hs₀.card_commV_eq hs hφ hFH]
  exact h8₀

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
