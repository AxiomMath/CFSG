module

public import CFSG.GroupTheory.CentreOfMassModulo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem inv_mul_conj_mem_of_commutator {V A X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ A) {v : G} (hvV : v ∈ V) {x : G}
    (hx : x ∈ X) : v⁻¹ * (x * v * x⁻¹) ∈ A := by
  have hxV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hXV hx) v).1 hvV
  have hcomm := congrArg Subtype.val (hV.1.is_comm.comm ⟨v⁻¹, V.inv_mem hvV⟩
    ⟨x * v * x⁻¹, hxV⟩)
  rw [show v⁻¹ * (x * v * x⁻¹) = x * v * x⁻¹ * v⁻¹ by
    simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using hcomm]
  exact hc x hx v hvV

private theorem inv_mul_conj_mem_bot {S X : Subgroup G} {v : G}
    (hvS : v ∈ Subgroup.centralizer (S : Set G)) :
    ∀ s ∈ S.subgroupOf X,
      v⁻¹ * (((s : ↥X) : G) * v * ((s : ↥X) : G)⁻¹) ∈ (⊥ : Subgroup G) := by
  intro s hs
  have hsS : ((s : ↥X) : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hsv : ((s : ↥X) : G) * v * ((s : ↥X) : G)⁻¹ = v := by
    have hcomm := hvS ((s : ↥X) : G) hsS
    rw [hcomm]
    group
  simp [hsv]

private theorem mul_mem_centralizer_of_fixed_mod_bot {X : Subgroup G} {w : G}
    (hfix : ∀ x ∈ X, w⁻¹ * (x * w * x⁻¹) ∈ (⊥ : Subgroup G)) :
    w ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : w⁻¹ * (x * w * x⁻¹) = 1 := by simpa using hfix x hx
  have h2 : x * w * x⁻¹ = w := by
    calc x * w * x⁻¹ = w * (w⁻¹ * (x * w * x⁻¹)) := by group
      _ = w * 1 := by rw [h1]
      _ = w := mul_one w
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [h2]

private theorem exists_mul_mem_centralizer {V A X S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hAV : A ≤ V)
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hodd : Odd (S.relIndex X))
    (hc : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ A) {v : G} (hvV : v ∈ V)
    (hvS : v ∈ Subgroup.centralizer (S : Set G)) :
    ∃ a ∈ A, v * a ∈ V ⊓ Subgroup.centralizer (X : Set G) := by
  classical
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    simpa [pow_two] using hV.2 a (hAV ha)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, hAV ha⟩ ⟨b, hAV hb⟩)
  have hXA' : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hx a ha
    exact (Subgroup.mem_normalizer_iff.mp (hXA hx) a).1 ha
  have hodd' : Odd (S.subgroupOf X).index := hodd
  obtain ⟨a, haA, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mod_of_odd_index hA2 hAc bot_le hXA'
      (by intro x _ c hc; rw [Subgroup.mem_bot.mp hc]; simp)
      (fun x hx => inv_mul_conj_mem_of_commutator hV hXV hc hvV hx)
      (inv_mul_conj_mem_bot hvS) hodd'
  exact ⟨a, haA, V.mul_mem hvV (hAV haA), mul_mem_centralizer_of_fixed_mod_bot hfix⟩

theorem fixed_le_of_odd_index {V A X S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hAV : A ≤ V)
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hSX : S ≤ X)
    (hodd : Odd (S.relIndex X)) (hc : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ A) :
    V ⊓ Subgroup.centralizer (S : Set G) ≤
      A ⊔ (V ⊓ Subgroup.centralizer (X : Set G)) := by
  intro v hv
  have hvV : v ∈ V := hv.1
  obtain ⟨a, haA, hva⟩ :=
    exists_mul_mem_centralizer hV hXV hAV hXA hodd hc hvV hv.2
  have hav : a * v = v * a :=
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, hAV haA⟩ ⟨v, hvV⟩)
  have hveq : v = a⁻¹ * (v * a) := by rw [← hav]; group
  rw [hveq]
  exact Subgroup.mul_mem_sup (A.inv_mem haA) hva

theorem Ctx23L.A_eq_V_of_commutator_le {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ⁅c.V, c.L⁆ ≤ A) : A = c.V := by
  have hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hXV : c.L ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (sup_le_normalizer_V D Ch c)
  have hcomm' : ⁅c.L, c.V⁆ ≤ A := by
    rwa [Subgroup.commutator_comm]
  have hXA : c.L ≤ Subgroup.normalizer (A : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 : l * a * l⁻¹ = ⁅l, a⁆ * a := by
        rw [commutatorElement_def]; group
      rw [h1]
      exact A.mul_mem (Subgroup.commutator_le.mp hcomm' l hl a (hAV ha)) ha
    · intro ha
      have hb : l * a * l⁻¹ ∈ c.V := hAV ha
      have h1 : l⁻¹ * (l * a * l⁻¹) * l = a := by group
      rw [← h1]
      have h2 : l⁻¹ * (l * a * l⁻¹) * l = ⁅l⁻¹, l * a * l⁻¹⁆ * (l * a * l⁻¹) := by
        rw [commutatorElement_def]; group
      rw [h2]
      exact A.mul_mem (Subgroup.commutator_le.mp hcomm' l⁻¹ (c.L.inv_mem hl) _ hb) ha
  have hSX : D.T ⊓ c.L ≤ c.L := inf_le_right
  have hodd : Odd ((D.T ⊓ c.L).relIndex c.L) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (isSylowIn_inf_of_le_normalizer c.hL.1.1).not_dvd_relIndex
  have hc : ∀ x ∈ c.L, ∀ v ∈ c.V, x * v * x⁻¹ * v⁻¹ ∈ A := fun x hx v hv =>
    Subgroup.commutator_le.mp hcomm' x hx v hv
  have haux := fixed_le_of_odd_index hV hXV hAV hXA hSX hodd hc
  rw [fixed_L_eq_bot c, sup_bot_eq] at haux
  have hZle : D.Z ≤ c.V ⊓ Subgroup.centralizer ((D.T ⊓ c.L : Subgroup G) : Set G) := by
    refine le_inf (uc22p22v_le_conjClosure c.N D.Z) ?_
    exact ((omegaOneCenterIn_le_inf_centralizer D.T).trans inf_le_right).trans
      (Subgroup.centralizer_le inf_le_left)
  have hZA : D.Z ≤ A := hZle.trans haux
  have hVA : c.V ≤ A := by
    simpa [Ctx23L.V] using uc22p22v_conjClosure_le hAN hZA
  exact le_antisymm hAV hVA

theorem rkIdx_fixV_zpowers_ge {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (σ : MulAut W) {A : Subgroup W} (hσA : σ ∈ stabSub A) :
    rkIdx (fixV (Subgroup.zpowers σ)) ≥
      rkIdx (fixV (autSub (Subgroup.zpowers σ) A)) +
        rkIdx (fixV (autQuot (Subgroup.zpowers σ) A)) := by
  classical
  let P : Subgroup (MulAut W) := Subgroup.zpowers σ
  change rkIdx (fixV P) ≥ rkIdx (fixV (autSub P A)) + rkIdx (fixV (autQuot P A))
  have hP : P ≤ stabSub A := Subgroup.zpowers_le.mpr hσA
  have hWA : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hW (a : W))
  have hWq : ∀ q : W ⧸ A, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow]; simp [hW w]
  have hcard := card_fixV_le_autQuot (V := W) (A := P) (U := A)
  have hcardA : Nat.card ↥(A ⊓ fixV P) = Nat.card (fixV (autSub P A)) := by
    rw [← map_subtype_fixV_autSub hP, Subgroup.card_map_of_injective A.subtype_injective]
  have h1 : Nat.card (fixV P) = 2 ^ rk (fixV P) := card_eq_two_pow hW _
  have h2 : Nat.card (fixV (autQuot P A)) = 2 ^ rk (fixV (autQuot P A)) :=
    card_eq_two_pow hWq _
  have h3 : Nat.card (fixV (autSub P A)) = 2 ^ rk (fixV (autSub P A)) :=
    card_eq_two_pow hWA _
  have hcard' : 2 ^ rk (fixV P) ≤
      2 ^ (rk (fixV (autQuot P A)) + rk (fixV (autSub P A))) := by
    rw [← h1, pow_add, ← h2, ← h3, ← hcardA]
    exact hcard
  have hrk : rk (fixV P) ≤ rk (fixV (autQuot P A)) + rk (fixV (autSub P A)) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard'
  have hrkq : rk (W ⧸ A) + rk A = rk W := by
    unfold rk
    rw [← padicValNat.mul (Nat.card_pos (α := W ⧸ A)).ne' (Nat.card_pos (α := A)).ne',
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup A]
  have e1 := rk_add_rkIdx (fixV P)
  have e2 := rk_add_rkIdx (fixV (autSub P A))
  have e3 := rk_add_rkIdx (fixV (autQuot P A))
  omega

theorem mem_stabTil_bot {s : G} {V : Subgroup G}
    (hsV : s ∈ Subgroup.normalizer (V : Set G)) : s ∈ stabTil (⊥ : Subgroup G) V :=
  ⟨hsV, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top s⟩

theorem Ctx23L.mParam_V_le {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1A : S23_1A D Ch) (h1930 : H1930 D) (hVne : c.V ≠ ⊥) :
    mBar c.N ⊥ c.V (isElemAbelian_V_basic c) ≤ c.n + 1 := by
  have hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have heq : c.V = conjClosure c.N (c.V ⊓ D.Z) := by
    rw [inf_eq_right.mpr hZleV]
    rfl
  obtain ⟨hW, h1, h2⟩ := h1A h1930 c c.V hV le_rfl heq hVne
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
