module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL28Facts
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.III.lemma_1_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.RightNearField.Linear

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixII PFAppendixIII MatrixGroups
open PFchapter1section2 PFchapter1section3
open scoped Pointwise commutatorElement

universe u v w

/-!
# Peterfalvi, Part II, Chapter II, Claim (15)
-/

/- The remaining declarations suffixed `_source_interface` mark same-file
boundaries for Claim (15). The current public inputs do not retain all local
model and index data used by the printed proof; the final conjunction is
assembled below without invoking any other numbered claim. -/

/- Claim (15): construct the concrete subgroup `L` in the `PSL(2,8)` copy,
prove `L ≤ R1`, and prove cyclicity/order `9`. -/
private theorem cyclic_order_nine_mulAut_eq_inv
    {C : Type*} [Group C] [Finite C] (hcard : Nat.card C = 9)
    (hcyc : IsCyclic C) (alpha : MulAut C)
    (halpha_sq : alpha ^ 2 = 1) (halpha_ne : alpha ≠ 1) :
    ∀ x : C, alpha x = x⁻¹ := by
  letI : IsCyclic C := hcyc
  let u : (ZMod (Nat.card C))ˣ := IsCyclic.mulAutMulEquiv C alpha
  have hu_sq : u ^ 2 = 1 := by
    dsimp [u]
    rw [← map_pow, halpha_sq, map_one]
  have hunit_cases :
      ∀ v : (ZMod (Nat.card C))ˣ, v ^ 2 = 1 → v = 1 ∨ v = -1 := by
    rw [hcard]
    decide
  have hu_cases : u = 1 ∨ u = -1 := hunit_cases u hu_sq
  have hu_ne : u ≠ 1 := by
    intro hu
    apply halpha_ne
    apply (IsCyclic.mulAutMulEquiv C).injective
    simpa [u] using hu
  have hu_neg : u = -1 := hu_cases.resolve_left hu_ne
  letI : IsMulCommutative C := IsCyclic.isMulCommutative
  let invAut : MulAut C :=
    { toFun := fun x ↦ x⁻¹
      invFun := fun x ↦ x⁻¹
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_mul' := by
        intro x y
        rw [mul_inv_rev]
        exact IsMulCommutative.is_comm.comm (y⁻¹) (x⁻¹) }
  have hinv_sq : invAut ^ 2 = 1 := by
    ext x
    simp [invAut, pow_two]
  have hinv_ne : invAut ≠ 1 := by
    intro hinv
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
    have hginv : g⁻¹ = g := by
      have h := DFunLike.congr_fun hinv g
      simpa [invAut] using h
    have hgpow : g ^ 2 = 1 := by
      simpa [pow_two] using (inv_eq_iff_mul_eq_one.mp hginv)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hgpow
    have hgtop : Subgroup.zpowers g = ⊤ :=
      top_unique (fun x _hx ↦ hg x)
    have horder : orderOf g = 9 :=
      (orderOf_eq_card_of_zpowers_eq_top hgtop).trans hcard
    rw [horder] at hdvd
    norm_num at hdvd
  let v : (ZMod (Nat.card C))ˣ := IsCyclic.mulAutMulEquiv C invAut
  have hv_sq : v ^ 2 = 1 := by
    dsimp [v]
    rw [← map_pow, hinv_sq, map_one]
  have hv_ne : v ≠ 1 := by
    intro hv
    apply hinv_ne
    apply (IsCyclic.mulAutMulEquiv C).injective
    simpa [v] using hv
  have hv_neg : v = -1 := (hunit_cases v hv_sq).resolve_left hv_ne
  have halpha_inv : alpha = invAut := by
    apply (IsCyclic.mulAutMulEquiv C).injective
    simpa [u, v] using hu_neg.trans hv_neg.symm
  intro x
  rw [halpha_inv]
  rfl

private theorem cyclic_order_nine_fixed_subgroup_eq
    {G : Type*} [Group G] [Finite G]
    (L Z : Subgroup G) (q : G)
    (hLcard : Nat.card L = 9) (hLcyc : IsCyclic L)
    (hZcard : Nat.card Z = 3) (hZ_le_L : Z ≤ L)
    (hq_norm_L : q ∈ Subgroup.normalizer (L : Set G))
    (hq_cent_Z : q ∈ Subgroup.centralizer (Z : Set G))
    (hq_not_cent_L : q ∉ Subgroup.centralizer (L : Set G)) :
    ∀ x : G, x ∈ L → q * x * q⁻¹ = x → x ∈ Z := by
  classical
  letI : CommGroup L := hLcyc.commGroup
  let qN : Subgroup.normalizer (L : Set G) := ⟨q, hq_norm_L⟩
  let alpha : MulAut L := L.normalizerMonoidHom qN
  let f : L →* L :=
    { toFun := fun x => alpha x * x⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hZsub_le_ker : Z.subgroupOf L ≤ f.ker := by
    intro z hzZ
    rw [MonoidHom.mem_ker]
    have hcomm : (z : G) * q = q * z :=
      Subgroup.mem_centralizer_iff.mp hq_cent_Z z hzZ
    apply Subtype.ext
    change ((alpha z : L) : G) * (z : G)⁻¹ = 1
    rw [show ((alpha z : L) : G) = q * (z : G) * q⁻¹ by
      simp [alpha, qN, Subgroup.normalizerMonoidHom_apply_apply_coe]]
    rw [← hcomm]
    simp [mul_assoc]
  have hker_ne_top : f.ker ≠ ⊤ := by
    intro htop
    apply hq_not_cent_L
    rw [Subgroup.mem_centralizer_iff]
    intro x hxL
    let xL : L := ⟨x, hxL⟩
    have hxker : xL ∈ f.ker := by rw [htop]; trivial
    have hfix : alpha xL = xL := by
      have hf := MonoidHom.mem_ker.mp hxker
      dsimp [f] at hf
      exact mul_inv_eq_one.mp hf
    have hfixG := congrArg Subtype.val hfix
    have hfixG' : q * x * q⁻¹ = x := by
      simpa [alpha, qN, xL,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using hfixG
    have hright := congrArg (fun z : G => z * q) hfixG'
    have hcomm : q * x = x * q := by simpa [mul_assoc] using hright
    exact hcomm.symm
  have hker_dvd : Nat.card f.ker ∣ 3 ^ 2 := by
    simpa [hLcard] using Subgroup.card_subgroup_dvd_card f.ker
  obtain ⟨k, hk_le, hker_card⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp hker_dvd
  have hker_ge : 3 ≤ Nat.card f.ker := by
    rw [← hZcard, ← natCard_subgroupOf_eq Z L hZ_le_L]
    exact Subgroup.card_le_of_le hZsub_le_ker
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hker_card_three : Nat.card f.ker = 3 := by
    rcases hk_cases with rfl | rfl | rfl
    · rw [hker_card] at hker_ge
      norm_num at hker_ge
    · simpa using hker_card
    · exfalso
      apply hker_ne_top
      apply Subgroup.eq_of_le_of_card_ge le_top
      simpa [hLcard] using (le_of_eq hker_card.symm)
  have hZsub_eq_ker : Z.subgroupOf L = f.ker :=
    Subgroup.eq_of_le_of_card_ge hZsub_le_ker
      (by rw [natCard_subgroupOf_eq Z L hZ_le_L, hZcard, hker_card_three])
  have hker_eq : f.ker = Z.subgroupOf L := hZsub_eq_ker.symm
  intro x hxL hfix
  let xL : L := ⟨x, hxL⟩
  have hxker : xL ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ((alpha xL : L) : G) * x⁻¹ = 1
    rw [show ((alpha xL : L) : G) = q * x * q⁻¹ by
      simp [alpha, qN, xL,
        Subgroup.normalizerMonoidHom_apply_apply_coe]]
    rw [hfix]
    simp
  rw [hker_eq] at hxker
  exact hxker

private theorem chapter2_claim15_cube_eq_one_iff_mem_cyclic_order_three_subgroup
    {G : Type*} [Group G] [Finite G]
    (A Z : Subgroup G) (hAcyc : IsCyclic A)
    (hAcard : Nat.card A = 3 ∨ Nat.card A = 9)
    (hZcard : Nat.card Z = 3) (hZ_le_A : Z ≤ A) :
    ∀ x : G, x ∈ A → (x ^ 3 = 1 ↔ x ∈ Z) := by
  letI : CommGroup A := hAcyc.commGroup
  let cubeKer : Subgroup A := (powMonoidHom 3 : A →* A).ker
  have hZsub_le : Z.subgroupOf A ≤ cubeKer := by
    intro z hzZ
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change (z : G) ^ 3 = 1
    have hzpow := pow_card_eq_one' (x := (⟨(z : G), hzZ⟩ : Z))
    rw [hZcard] at hzpow
    exact congrArg Subtype.val hzpow
  have hcubeCard : Nat.card cubeKer = 3 := by
    calc
      Nat.card cubeKer = (Nat.card A).gcd 3 :=
        IsCyclic.card_powMonoidHom_ker (G := A) 3
      _ = 3 := by rcases hAcard with hAcard | hAcard <;> simp [hAcard]
  have hZsub_eq : Z.subgroupOf A = cubeKer :=
    Subgroup.eq_of_le_of_card_ge hZsub_le (by
      rw [natCard_subgroupOf_eq Z A hZ_le_A, hZcard, hcubeCard])
  intro x hxA
  let xA : A := ⟨x, hxA⟩
  constructor
  · intro hx3
    have hxker : xA ∈ cubeKer := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hx3
    rw [← hZsub_eq] at hxker
    exact hxker
  · intro hxZ
    have hzpow := pow_card_eq_one' (x := (⟨x, hxZ⟩ : Z))
    rw [hZcard] at hzpow
    exact congrArg Subtype.val hzpow

private theorem chapter2_claim15_commutator_mem_cyclic_order_three_subgroup
    {G : Type*} [Group G] [Finite G]
    (A Z P : Subgroup G) (hAcyc : IsCyclic A)
    (hAcard : Nat.card A = 3 ∨ Nat.card A = 9)
    (hZcard : Nat.card Z = 3) (hZ_le_A : Z ≤ A)
    (hP_norm_A : P ≤ Subgroup.normalizer (A : Set G))
    (hZ_le_CP : Z ≤ Subgroup.centralizer (P : Set G)) :
    ∀ a : G, a ∈ A → ∀ q : G, q ∈ P → ⁅a, q⁆ ∈ Z := by
  classical
  letI : CommGroup A := hAcyc.commGroup
  intro a haA q hqP
  let qN : Subgroup.normalizer (A : Set G) := ⟨q, hP_norm_A hqP⟩
  let alpha : MulAut A := A.normalizerMonoidHom qN
  let f : A →* A :=
    { toFun := fun x => alpha x * x⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hZsub_le_ker : Z.subgroupOf A ≤ f.ker := by
    intro z hzZ
    rw [MonoidHom.mem_ker]
    have hcomm : (z : G) * q = q * z :=
      (Subgroup.mem_centralizer_iff.mp (hZ_le_CP hzZ) q hqP).symm
    apply Subtype.ext
    change ((alpha z : A) : G) * (z : G)⁻¹ = 1
    rw [show ((alpha z : A) : G) = q * (z : G) * q⁻¹ by
      simp [alpha, qN, Subgroup.normalizerMonoidHom_apply_apply_coe]]
    rw [← hcomm]
    simp [mul_assoc]
  have hker_ge : 3 ≤ Nat.card f.ker := by
    rw [← hZcard, ← natCard_subgroupOf_eq Z A hZ_le_A]
    exact Subgroup.card_le_of_le hZsub_le_ker
  have hcard_formula :
      Nat.card A = Nat.card f.range * Nat.card f.ker := by
    calc
      Nat.card A = Nat.card (A ⧸ f.ker) * Nat.card f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      _ = Nat.card f.range * Nat.card f.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hAcard_le : Nat.card A ≤ 9 := by
    rcases hAcard with hAcard | hAcard <;> omega
  have hrange_le : Nat.card f.range ≤ 3 := by
    nlinarith [Nat.card_pos (α := f.range)]
  have hA_dvd_nine : Nat.card A ∣ 3 ^ 2 := by
    rcases hAcard with hAcard | hAcard
    · rw [hAcard]
      norm_num
    · rw [hAcard]
      norm_num
  have hrange_dvd_nine : Nat.card f.range ∣ 3 ^ 2 :=
    (Subgroup.card_subgroup_dvd_card f.range).trans hA_dvd_nine
  obtain ⟨k, hk_le, hrange_card⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp hrange_dvd_nine
  have hk_one : k ≤ 1 := by
    by_contra hk
    have hk_two : k = 2 := by omega
    subst k
    norm_num at hrange_card hrange_le
    omega
  have hrange_dvd_three : Nat.card f.range ∣ 3 := by
    rw [hrange_card]
    exact Nat.pow_dvd_pow 3 hk_one
  let aInv : A := ⟨a⁻¹, A.inv_mem haA⟩
  have hf_mem_range : f aInv ∈ f.range := ⟨aInv, rfl⟩
  let faRange : f.range := ⟨f aInv, hf_mem_range⟩
  have horder_dvd_three : orderOf faRange ∣ 3 :=
    (orderOf_dvd_natCard faRange).trans hrange_dvd_three
  have hfa_cube_range : faRange ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp horder_dvd_three
  have hfa_cube : ((f aInv : A) : G) ^ 3 = 1 :=
    congrArg Subtype.val (congrArg Subtype.val hfa_cube_range)
  have hfa_Z : ((f aInv : A) : G) ∈ Z :=
    (chapter2_claim15_cube_eq_one_iff_mem_cyclic_order_three_subgroup
      A Z hAcyc hAcard hZcard hZ_le_A _ (f aInv).property).mp hfa_cube
  have hqainvA : q * a⁻¹ * q⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hP_norm_A hqP) a⁻¹).1 (A.inv_mem haA)
  have hcommute : Commute a (q * a⁻¹ * q⁻¹) := by
    exact congrArg Subtype.val
      (show (⟨a, haA⟩ : A) * ⟨q * a⁻¹ * q⁻¹, hqainvA⟩ =
        ⟨q * a⁻¹ * q⁻¹, hqainvA⟩ * ⟨a, haA⟩ from mul_comm _ _)
  have hcomm_eq : ⁅a, q⁆ = ((f aInv : A) : G) := by
    calc
      ⁅a, q⁆ = a * (q * a⁻¹ * q⁻¹) := by
        rw [commutatorElement_def]
        group
      _ = (q * a⁻¹ * q⁻¹) * a := hcommute.eq
      _ = ((f aInv : A) : G) := by
        simp [f, alpha, qN, aInv,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [hcomm_eq]
  exact hfa_Z

private theorem chapter2_claim15_commutator_mem_sup_cyclic_factors
    {G : Type*} [Group G] [Finite G]
    (L W Z Sigma P : Subgroup G)
    (hLcyc : IsCyclic L) (hWcyc : IsCyclic W)
    (hLcard : Nat.card L = 9)
    (hWcard : Nat.card W = 3 ∨ Nat.card W = 9)
    (hZcard : Nat.card Z = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hZ_le_L : Z ≤ L) (hSigma_le_W : Sigma ≤ W)
    (hP_norm_L : P ≤ Subgroup.normalizer (L : Set G))
    (hP_norm_W : P ≤ Subgroup.normalizer (W : Set G))
    (hZ_le_CP : Z ≤ Subgroup.centralizer (P : Set G))
    (hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G))
    (hW_le_CL : W ≤ Subgroup.centralizer (L : Set G)) :
    ∀ a : G, a ∈ L ⊔ W → ∀ q : G, q ∈ P →
      ⁅a, q⁆ ∈ Z ⊔ Sigma := by
  classical
  have hW_norm_L : W ≤ Subgroup.normalizer (L : Set G) :=
    hW_le_CL.trans (centralizer_le_normalizer (R := L))
  have hAcomm : IsMulCommutative (L ⊔ W : Subgroup G) := by
    rw [Subgroup.sup_eq_closure]
    let : IsCyclic L := hLcyc
    let : IsCyclic W := hWcyc
    exact Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with hxL | hxW
      · rcases hy with hyL | hyW
        · exact setLike_mul_comm hxL hyL
        · exact Subgroup.mem_centralizer_iff.mp (hW_le_CL hyW) x hxL
      · rcases hy with hyL | hyW
        · exact (Subgroup.mem_centralizer_iff.mp (hW_le_CL hxW) y hyL).symm
        · exact setLike_mul_comm hxW hyW)
  let A : Subgroup G := L ⊔ W
  let : IsMulCommutative A := by simpa [A] using hAcomm
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hP_norm_A : P ≤ Subgroup.normalizer (A : Set G) := by
    intro q hqP
    have hqL := hP_norm_L hqP
    have hqW := hP_norm_W hqP
    have hconj : ∀ g : G,
        g ∈ Subgroup.normalizer (L : Set G) →
        g ∈ Subgroup.normalizer (W : Set G) →
        ∀ y : G, y ∈ A → g * y * g⁻¹ ∈ A := by
      intro g hgL hgW y hy
      change y ∈ L ⊔ W at hy
      change g * y * g⁻¹ ∈ L ⊔ W
      rw [Subgroup.sup_eq_closure] at hy ⊢
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with hzL | hzW
        · exact Subgroup.subset_closure
            (Or.inl ((Subgroup.mem_normalizer_iff.mp hgL z).1 hzL))
        · exact Subgroup.subset_closure
            (Or.inr ((Subgroup.mem_normalizer_iff.mp hgW z).1 hzW))
      · simp
      · intro x y _hx _hy hcx hcy
        simpa [mul_assoc] using
          (Subgroup.closure ((L : Set G) ∪ (W : Set G))).mul_mem hcx hcy
      · intro x _hx hcx
        simpa [mul_assoc] using
          (Subgroup.closure ((L : Set G) ∪ (W : Set G))).inv_mem hcx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj q hqL hqW y
    · intro hy
      have h := hconj q⁻¹
        ((Subgroup.normalizer (L : Set G)).inv_mem hqL)
        ((Subgroup.normalizer (W : Set G)).inv_mem hqW)
        (q * y * q⁻¹) hy
      simpa [mul_assoc] using h
  intro a haA q hqP
  have haProd : a ∈ (L : Set G) * (W : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L W hW_norm_L]
    exact haA
  rcases haProd with ⟨l, hlL, w, hwW, hlw⟩
  change l * w = a at hlw
  have hcL : ⁅l, q⁆ ∈ Z :=
    chapter2_claim15_commutator_mem_cyclic_order_three_subgroup
      L Z P hLcyc (Or.inr hLcard) hZcard hZ_le_L hP_norm_L hZ_le_CP
        l hlL q hqP
  have hcW : ⁅w, q⁆ ∈ Sigma :=
    chapter2_claim15_commutator_mem_cyclic_order_three_subgroup
      W Sigma P hWcyc hWcard hSigmaCard hSigma_le_W hP_norm_W
        hSigma_le_CP w hwW q hqP
  have hqainvA : q * a⁻¹ * q⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hP_norm_A hqP) a⁻¹).1
      ((L ⊔ W).inv_mem haA)
  have hqlinvL : q * l⁻¹ * q⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hP_norm_L hqP) l⁻¹).1 (L.inv_mem hlL)
  have hqwinvW : q * w⁻¹ * q⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hP_norm_W hqP) w⁻¹).1 (W.inv_mem hwW)
  let aA : A := ⟨a, haA⟩
  let lA : A := ⟨l, Subgroup.mem_sup_left hlL⟩
  let wA : A := ⟨w, Subgroup.mem_sup_right hwW⟩
  let conjA : A := ⟨q * a⁻¹ * q⁻¹, hqainvA⟩
  let conjL : A := ⟨q * l⁻¹ * q⁻¹, Subgroup.mem_sup_left hqlinvL⟩
  let conjW : A := ⟨q * w⁻¹ * q⁻¹, Subgroup.mem_sup_right hqwinvW⟩
  let commA : A := ⟨⁅a, q⁆, by
    simpa [commutatorElement_def, mul_assoc] using A.mul_mem haA hqainvA⟩
  let commL : A := ⟨⁅l, q⁆, Subgroup.mem_sup_left (hZ_le_L hcL)⟩
  let commW : A := ⟨⁅w, q⁆, Subgroup.mem_sup_right (hSigma_le_W hcW)⟩
  have ha_decomp : aA = lA * wA := by
    apply Subtype.ext
    exact hlw.symm
  have hconj_decomp : conjA = conjW * conjL := by
    apply Subtype.ext
    change q * a⁻¹ * q⁻¹ =
      (q * w⁻¹ * q⁻¹) * (q * l⁻¹ * q⁻¹)
    rw [← hlw]
    group
  have hcommA_formula : commA = aA * conjA := by
    apply Subtype.ext
    dsimp [commA, aA, conjA]
    rw [commutatorElement_def]
    group
  have hcommL_formula : commL = lA * conjL := by
    apply Subtype.ext
    dsimp [commL, lA, conjL]
    rw [commutatorElement_def]
    group
  have hcommW_formula : commW = wA * conjW := by
    apply Subtype.ext
    dsimp [commW, wA, conjW]
    rw [commutatorElement_def]
    group
  have hcomm_eq : commA = commL * commW := by
    calc
      commA = aA * conjA := hcommA_formula
      _ = (lA * wA) * (conjW * conjL) := by rw [ha_decomp, hconj_decomp]
      _ = (lA * conjL) * (wA * conjW) := by ac_rfl
      _ = commL * commW := by rw [← hcommL_formula, ← hcommW_formula]
  have hcomm_eqG := congrArg Subtype.val hcomm_eq
  change ⁅a, q⁆ = ⁅l, q⁆ * ⁅w, q⁆ at hcomm_eqG
  rw [hcomm_eqG]
  exact Subgroup.mul_mem_sup hcL hcW

private theorem chapter2_claim15_s_inverts_cyclic_L
    {G : Type*} [Group G] [Finite G]
    (Q0 K L : Subgroup G) (t s : G)
    (hsQ0 : s ∈ Q0) (hsI : IsInvolution s) (htI : IsInvolution t)
    (hst_ne : s * t ≠ 1)
    (hL_constructed :
      L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (hL_order : Nat.card L = 9) (hL_cyclic : IsCyclic L) :
    ∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹ := by
  have hs_inv : s⁻¹ = s := hsI.inv_eq_self
  have hss : s * s = 1 := by simpa [pow_two] using hsI.sq_eq_one
  have hconj_st : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [hs_inv]
    calc
      s * (s * t) * s = t * s := by rw [← mul_assoc, hss]; simp
      _ = (s * t)⁻¹ := by simp [hs_inv, htI.inv_eq_self]
  have hs_norm_centralizer :
      s ∈ Subgroup.normalizer (Subgroup.centralizer ({s * t} : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    have hforward :
        ∀ x : G, x ∈ Subgroup.centralizer ({s * t} : Set G) →
          s * x * s⁻¹ ∈ Subgroup.centralizer ({s * t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hy_eq : y = s * t := by simpa using hy
      subst y
      have hcomm : Commute (s * t) x := hx (s * t) (by simp)
      have hcomm_inv : Commute ((s * t)⁻¹) (s * x * s⁻¹) := by
        rw [← hconj_st]
        exact hcomm.conj s
      exact (Commute.inv_left_iff.mp hcomm_inv).eq
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (s * x * s⁻¹) hx
      have hconj_twice : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hs_inv]
        calc
          s * (s * x * s) * s = (s * s) * x * (s * s) := by
            simp only [mul_assoc]
          _ = x := by rw [hss]; simp
      rw [hconj_twice] at hback
      exact hback
  let M : Subgroup G := psl2GeneratedSubgroup Q0 K t
  have hsM : s ∈ M :=
    Subgroup.subset_closure (Or.inl (Or.inl hsQ0))
  have hs_norm_M : s ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer hsM
  have hs_norm_L : s ∈ Subgroup.normalizer (L : Set G) := by
    rw [hL_constructed]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hs_norm_centralizer, hs_norm_M⟩
  let sn : Subgroup.normalizer (L : Set G) := ⟨s, hs_norm_L⟩
  let alpha : MulAut L := L.normalizerMonoidHom sn
  have hsn_sq : sn ^ 2 = 1 := by
    apply Subtype.ext
    exact hsI.sq_eq_one
  have halpha_sq : alpha ^ 2 = 1 := by
    dsimp [alpha]
    rw [← map_pow, hsn_sq, map_one]
  have htM : t ∈ M :=
    Subgroup.subset_closure (Or.inr rfl)
  have hstM : s * t ∈ M := M.mul_mem hsM htM
  have hstC : s * t ∈ Subgroup.centralizer ({s * t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy_eq : y = s * t := by simpa using hy
    subst y
    rfl
  have hstL : s * t ∈ L := by
    rw [hL_constructed]
    exact ⟨hstC, hstM⟩
  let stL : L := ⟨s * t, hstL⟩
  have hstL_ne : stL ≠ 1 := by
    intro h
    apply hst_ne
    exact congrArg Subtype.val h
  have hstL_ne_inv : stL ≠ stL⁻¹ := by
    intro hself
    have hsq : stL ^ 2 = 1 := by
      calc
        stL ^ 2 = stL * stL := by rw [pow_two]
        _ = stL * stL⁻¹ := congrArg (fun z => stL * z) hself
        _ = 1 := mul_inv_cancel _
    have hdvd2 : orderOf stL ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hdvd9 : orderOf stL ∣ 9 := by
      rw [← hL_order]
      exact orderOf_dvd_natCard stL
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with hone | htwo
    · exact hstL_ne (orderOf_eq_one_iff.mp hone)
    · have : ¬ 2 ∣ 9 := by norm_num
      exact this (htwo ▸ hdvd9)
  have halpha_stL : alpha stL = stL⁻¹ := by
    apply Subtype.ext
    exact hconj_st
  have halpha_ne : alpha ≠ 1 := by
    intro h
    have hfix : alpha stL = stL := by rw [h]; rfl
    apply hstL_ne_inv
    rw [← halpha_stL, hfix]
  have hinv := cyclic_order_nine_mulAut_eq_inv hL_order hL_cyclic alpha
    halpha_sq halpha_ne
  intro x hx
  have hsub := hinv ⟨x, hx⟩
  change s⁻¹ * x * s = x⁻¹
  simpa [alpha, sn, hs_inv, Subgroup.normalizerMonoidHom_apply_apply_coe] using
    congrArg Subtype.val hsub

private theorem chapter2_claim15_W_centralizes_generated_L
    {G : Type*} [Group G]
    (H D K V W Q0 L : Subgroup G) (t _s : G)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hV_eq : V = peterfalviV D t)
    (hW_eq : W = peterfalviW V (K : Set G))
    (hW_inv_cent :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x} : Set G))
    (hL_le_generated : L ≤ psl2GeneratedSubgroup Q0 K t) :
    W ≤ Subgroup.centralizer (L : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxM : x ∈ psl2GeneratedSubgroup Q0 K t := by
    exact hL_le_generated hx
  have hgen :
      (Q0 : Set G) ∪ (K : Set G) ∪ {t} ⊆
        Subgroup.centralizer ({w} : Set G) := by
    intro y hy
    rcases hy with (hyQ0 | hyK) | hyt
    · rcases (hQ0_def y).mp hyQ0 with rfl | hyI
      · exact (Subgroup.centralizer ({w} : Set G)).one_mem
      · apply (Subgroup.mem_centralizer_iff).2
        intro z hz
        have hz_eq : z = w := by simpa using hz
        subst z
        rw [hW_inv_cent] at hw
        exact (Subgroup.mem_centralizer_iff.mp hw.2 y hyI).symm
    · apply (Subgroup.mem_centralizer_iff).2
      intro z hz
      have hz_eq : z = w := by simpa using hz
      subst z
      rw [hW_eq] at hw
      exact (Subgroup.mem_centralizer_iff.mp hw.2 y hyK).symm
    · have hyt_eq : y = t := by simpa using hyt
      subst y
      apply (Subgroup.mem_centralizer_iff).2
      intro z hz
      have hz_eq : z = w := by simpa using hz
      subst z
      rw [hW_eq, hV_eq, peterfalviW, peterfalviV] at hw
      exact (Subgroup.mem_centralizer_iff.mp hw.1.2 t (by simp)).symm
  have hxcent :
      x ∈ Subgroup.centralizer ({w} : Set G) := by
    apply (show psl2GeneratedSubgroup Q0 K t ≤
        Subgroup.centralizer ({w} : Set G) by
      rw [psl2GeneratedSubgroup, Subgroup.closure_le]
      exact hgen)
    exact hxM
  exact (Subgroup.mem_centralizer_iff.mp hxcent w (by simp)).symm

private theorem chapter2_claim15_disjoint_L_W
    {G : Type*} [Group G]
    (H D K V W Q0 L : Subgroup G) (t s : G)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hV_eq : V = peterfalviV D t)
    (hW_eq : W = peterfalviW V (K : Set G))
    (hW_inv_cent :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x} : Set G))
    (hL_constructed :
      L = Subgroup.centralizer ({s * t} : Set G) ⊓
        psl2GeneratedSubgroup Q0 K t)
    (hM_center : Subgroup.center (psl2GeneratedSubgroup Q0 K t) = ⊥) :
    Disjoint L W := by
  have hW_le_CM :
      W ≤ Subgroup.centralizer (psl2GeneratedSubgroup Q0 K t : Set G) :=
    chapter2_claim15_W_centralizes_generated_L
      H D K V W Q0 (psl2GeneratedSubgroup Q0 K t) t s hQ0_def
      hV_eq hW_eq hW_inv_cent le_rfl
  rw [Subgroup.disjoint_def]
  intro x hxL hxW
  have hxM : x ∈ psl2GeneratedSubgroup Q0 K t := by
    rw [hL_constructed] at hxL
    exact hxL.2
  let xM : psl2GeneratedSubgroup Q0 K t := ⟨x, hxM⟩
  have hxCenter : xM ∈ Subgroup.center (psl2GeneratedSubgroup Q0 K t) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hW_le_CM hxW)) y y.property
  rw [hM_center] at hxCenter
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxCenter)

private theorem chapter2_claim15_exceptional_sylow_exponent_three
    {G F : Type*} [Group G] [Finite G]
    [RightNearField F]
    (T P Sigma Z1 R : Subgroup G)
    (addEquiv : Multiplicative F ≃* T)
    (hchar : addOrderOf (1 : F) = 3)
    (hPcard : Nat.card P = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hZ1card : Nat.card Z1 = 3)
    (hR : R = T ⊔ P)
    (hT_le_CP : T ≤ Subgroup.centralizer (P : Set G))
    (hSigma_norm_R : Sigma ≤ Subgroup.normalizer (R : Set G))
    (hcenter :
      (R ⊔ Sigma) ⊓
          Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
        Z1 ⊔ P)
    (hderived :
      ⁅(R ⊔ Sigma : Subgroup G), (R ⊔ Sigma : Subgroup G)⁆ = Z1) :
    ∀ x : G, x ∈ R ⊔ Sigma → x ^ 3 = 1 := by
  classical
  let X : Subgroup G := R ⊔ Sigma
  have hP_norm_T : P ≤ Subgroup.normalizer (T : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hforward : ∀ q : G, q ∈ P → ∀ z : G, z ∈ T →
        q * z * q⁻¹ ∈ T := by
      intro q hq z hz
      have hcomm : q * z = z * q :=
        (Subgroup.mem_centralizer_iff.mp (hT_le_CP hz)) q hq
      have hconj : q * z * q⁻¹ = z := by
        calc
          q * z * q⁻¹ = z * q * q⁻¹ := by rw [hcomm]
          _ = z := by simp [mul_assoc]
      simpa [hconj] using hz
    constructor
    · exact hforward p hp y
    · intro hyT
      have hpinvP : p⁻¹ ∈ P := P.inv_mem hp
      have := hforward p⁻¹ hpinvP (p * y * p⁻¹) hyT
      simpa [mul_assoc] using this
  have hTcube : ∀ a : G, a ∈ T → a ^ 3 = 1 := by
    intro a ha
    let aT : T := ⟨a, ha⟩
    obtain ⟨b, hb⟩ := addEquiv.surjective aT
    let bF : F := Multiplicative.toAdd b
    have hbAdd : 3 • bF = 0 := by
      rw [← hchar]
      exact rightNearField_addOrderOf_one_nsmul_eq_zero bF
    have hbPow : b ^ 3 = 1 := by
      change (Multiplicative.ofAdd bF) ^ 3 = 1
      rw [← ofAdd_nsmul, hbAdd, ofAdd_zero]
    have hmapPow : (addEquiv b) ^ 3 = 1 := by
      simpa using congrArg addEquiv hbPow
    have hmapPowG := congrArg Subtype.val hmapPow
    change a ^ 3 = 1
    rw [← show ((addEquiv b : T) : G) = a by
      exact congrArg Subtype.val hb]
    exact hmapPowG
  have hPcube : ∀ a : G, a ∈ P → a ^ 3 = 1 := by
    intro a ha
    have hpow := pow_card_eq_one' (x := (⟨a, ha⟩ : P))
    rw [hPcard] at hpow
    exact congrArg Subtype.val hpow
  have hSigmaCube : ∀ a : G, a ∈ Sigma → a ^ 3 = 1 := by
    intro a ha
    have hpow := pow_card_eq_one' (x := (⟨a, ha⟩ : Sigma))
    rw [hSigmaCard] at hpow
    exact congrArg Subtype.val hpow
  have hZ1cube : ∀ a : G, a ∈ Z1 → a ^ 3 = 1 := by
    intro a ha
    have hpow := pow_card_eq_one' (x := (⟨a, ha⟩ : Z1))
    rw [hZ1card] at hpow
    exact congrArg Subtype.val hpow
  have hZ1_le_CX : Z1 ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    have hzC0 : z ∈ Z1 ⊔ P := Subgroup.mem_sup_left hz
    have hzCenter : z ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
      simpa [X, hcenter] using hzC0
    exact hzCenter.2
  intro x hx
  have hxProd : x ∈ (R : Set G) * (Sigma : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left R Sigma hSigma_norm_R]
    exact hx
  rcases hxProd with ⟨r, hrR, z, hzSigma, hrz⟩
  have hrProd : r ∈ (T : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left T P hP_norm_T]
    rw [← hR]
    exact hrR
  rcases hrProd with ⟨a, haT, q, hqP, haq⟩
  let b : G := a * q
  have hbX : b ∈ X := by
    dsimp [b, X]
    apply Subgroup.mem_sup_left
    rw [hR]
    exact Subgroup.mul_mem_sup haT hqP
  have hzX : z ∈ X := by
    dsimp [X]
    exact Subgroup.mem_sup_right hzSigma
  have haqComm : Commute a q := by
    exact ((Subgroup.mem_centralizer_iff.mp (hT_le_CP haT)) q hqP).symm
  have hbCube : b ^ 3 = 1 := by
    dsimp [b]
    rw [haqComm.mul_pow, hTcube a haT, hPcube q hqP, one_mul]
  have hzCube : z ^ 3 = 1 := hSigmaCube z hzSigma
  have hcommZ1 : ⁅z, b⁆ ∈ Z1 := by
    rw [← hderived]
    exact Subgroup.commutator_mem_commutator hzX hbX
  have hcommCube : ⁅z, b⁆ ^ 3 = 1 := hZ1cube _ hcommZ1
  have hcommCentral : ⁅z, b⁆ ∈ Subgroup.centralizer (X : Set G) :=
    hZ1_le_CX hcommZ1
  have hcommBZ1 : ⁅b, z⁆ ∈ Z1 := by
    rw [← hderived]
    exact Subgroup.commutator_mem_commutator hbX hzX
  have hcommBCentral : ⁅b, z⁆ ∈ Subgroup.centralizer (X : Set G) :=
    hZ1_le_CX hcommBZ1
  have hcomm_b : Commute ⁅b, z⁆ b :=
    (Subgroup.mem_centralizer_iff.mp hcommBCentral b hbX).symm
  have hcomm_z : Commute ⁅b, z⁆ z :=
    (Subgroup.mem_centralizer_iff.mp hcommBCentral z hzX).symm
  have hformula := External.huppert_III_1_3_b b z hcomm_b hcomm_z 3
  rw [hbCube, hzCube] at hformula
  norm_num [Nat.choose] at hformula
  rw [hcommCube] at hformula
  rw [← hrz, ← haq]
  exact hformula

private noncomputable def chapter2_claim15_inf_centralizer_mulEquiv
    {G M : Type*} [Group G] [Group M]
    (A : Subgroup G) (x : G) (hx : x ∈ A) (e : A ≃* M) :
    ↥(Subgroup.centralizer ({x} : Set G) ⊓ A) ≃*
      ↥(Subgroup.centralizer ({e ⟨x, hx⟩} : Set M)) where
  toFun y := ⟨e ⟨y, y.property.2⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyC : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      y.property.1
    have hy := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hyA : (⟨y, y.property.2⟩ : A) * ⟨x, hx⟩ =
        ⟨x, hx⟩ * ⟨y, y.property.2⟩ := Subtype.ext hy
    calc
      e ⟨y, y.property.2⟩ * e ⟨x, hx⟩ =
          e (⟨y, y.property.2⟩ * ⟨x, hx⟩) :=
        (e.map_mul _ _).symm
      _ = e (⟨x, hx⟩ * ⟨y, y.property.2⟩) := congrArg e hyA
      _ = e ⟨x, hx⟩ * e ⟨y, y.property.2⟩ := e.map_mul _ _⟩
  invFun z := ⟨(e.symm z : A), by
    constructor
    · have hzC : (z : M) ∈
          Subgroup.centralizer ({e ⟨x, hx⟩} : Set M) := z.property
      have hz := congrArg e.symm
        (Subgroup.mem_centralizer_singleton_iff.mp hzC)
      have hzA : (e.symm z : A) * ⟨x, hx⟩ =
          ⟨x, hx⟩ * (e.symm z : A) := by
        calc
          (e.symm z : A) * ⟨x, hx⟩ =
              e.symm (z * e ⟨x, hx⟩) :=
            by simp
          _ = e.symm (e ⟨x, hx⟩ * z) := hz
          _ = ⟨x, hx⟩ * (e.symm z : A) := by
            simp
      show (e.symm z : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hzA
    · exact (e.symm z).property⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
  map_mul' y z := by
    apply Subtype.ext
    simpa using e.map_mul
      (⟨y, y.property.2⟩ : A) (⟨z, z.property.2⟩ : A)

private lemma chapter2_claim15_conj_mem_closure
    {G : Type*} [Group G] {S : Set G} (g y : G)
    (hy : y ∈ Subgroup.closure S)
    (hS : ∀ x : G, x ∈ S → g * x * g⁻¹ ∈ Subgroup.closure S) :
    g * y * g⁻¹ ∈ Subgroup.closure S := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · exact hS
  · simp
  · intro a b _ha _hb hca hcb
    simpa [mul_assoc] using (Subgroup.closure S).mul_mem hca hcb
  · intro a _ha hca
    simpa [mul_assoc] using (Subgroup.closure S).inv_mem hca

private lemma chapter2_claim15_mem_normalizer_closure
    {G : Type*} [Group G] {S : Set G} (g : G)
    (hforward : ∀ x : G, x ∈ S →
      g * x * g⁻¹ ∈ Subgroup.closure S)
    (hbackward : ∀ x : G, x ∈ S →
      g⁻¹ * x * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => chapter2_claim15_conj_mem_closure g y hy hforward
  · intro hy
    have h := chapter2_claim15_conj_mem_closure g⁻¹
      (g * y * g⁻¹) hy (by simpa using hbackward)
    simpa [mul_assoc] using h

private lemma chapter2_claim15_mem_normalizer_sup_of_normalizes
    {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [Subgroup.sup_eq_closure] at hy ⊢
    exact chapter2_claim15_conj_mem_closure x y hy (by
      intro z hz
      rcases hz with hzA | hzB
      · exact Subgroup.subset_closure
          (Or.inl ((Subgroup.mem_normalizer_iff.mp hA z).1 hzA))
      · exact Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp hB z).1 hzB)))
  · intro hy
    have hAinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hA
    have hBinv : x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hB
    rw [Subgroup.sup_eq_closure] at hy ⊢
    have h := chapter2_claim15_conj_mem_closure x⁻¹
      (x * y * x⁻¹) hy (by
        intro z hz
        rcases hz with hzA | hzB
        · exact Subgroup.subset_closure
            (Or.inl ((Subgroup.mem_normalizer_iff.mp hAinv z).1 hzA))
        · exact Subgroup.subset_closure
            (Or.inr ((Subgroup.mem_normalizer_iff.mp hBinv z).1 hzB)))
    simpa [mul_assoc] using h

private lemma chapter2_claim15_centralizer_le_normalizer
    {G : Type*} [Group G] (A : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hcomm : x * g = g * x :=
      (Subgroup.mem_centralizer_iff.mp hg) x hx
    have hconj : g * x * g⁻¹ = x := by
      calc
        g * x * g⁻¹ = (g * x) * g⁻¹ := by simp [mul_assoc]
        _ = (x * g) * g⁻¹ := by rw [hcomm.symm]
        _ = x := by simp [mul_assoc]
    simpa [hconj] using hx
  · intro hx
    have hginv : g⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.centralizer (A : Set G)).inv_mem hg
    have hcomm : (g * x * g⁻¹) * g⁻¹ =
        g⁻¹ * (g * x * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hginv) (g * x * g⁻¹) hx
    have hback_eq : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
      calc
        g⁻¹ * (g * x * g⁻¹) * g =
            (g⁻¹ * (g * x * g⁻¹)) * g := by simp [mul_assoc]
        _ = ((g * x * g⁻¹) * g⁻¹) * g := by rw [hcomm]
        _ = g * x * g⁻¹ := by simp [mul_assoc]
    have hback : g⁻¹ * (g * x * g⁻¹) * g ∈ A := by
      simpa [hback_eq] using hx
    simpa [mul_assoc] using hback

private lemma chapter2_claim15_mem_normalizer_centralizer_of_mem_normalizer
    {G : Type*} [Group G] (A : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    have ha_back : g⁻¹ * a * g ∈ A := by
      apply (hg (g⁻¹ * a * g)).mpr
      simpa [mul_assoc] using ha
    calc
      a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [hx _ ha_back]
      _ = (g * x * g⁻¹) * a := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    have hga : g * a * g⁻¹ ∈ A := (hg a).mp ha
    have hcomm := hx (g * a * g⁻¹) hga
    have h := congrArg (fun z : G => g⁻¹ * z * g) hcomm
    simpa [mul_assoc] using h

private theorem chapter2_claim15_centralizer_sup
    {G : Type*} [Group G] (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓
        Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf]
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_iff.mp hg a (Or.inl ha)
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_iff.mp hg b (Or.inr hb)
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hxA | hxB
    · exact Subgroup.mem_centralizer_iff.mp hg.1 x hxA
    · exact Subgroup.mem_centralizer_iff.mp hg.2 x hxB

private theorem chapter2_claim15_closure_involution_card
    {G : Type*} [Group G] (s : G) (hs : IsInvolution s) :
    Nat.card (Subgroup.closure ({s} : Set G)) = 2 := by
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers,
    orderOf_eq_prime hs.sq_eq_one hs.ne_one]

private theorem chapter2_claim15_sylow_card_from_factorization
    {G : Type*} [Group G] [Finite G] (S : Sylow 3 G)
    (k u : ℕ) (hk : Nat.card G = 3 ^ k * u) (hu : ¬ 3 ∣ u) :
    Nat.card (S : Subgroup G) = 3 ^ k := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    exact hu (dvd_zero 3)
  rw [Sylow.card_eq_multiplicity S, hk,
    Nat.factorization_mul (pow_ne_zero k (by norm_num)) hu0,
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_three]
  have hufac : u.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hu
  rw [hufac]
  simp

private theorem chapter2_claim15_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (A B : Subgroup G)
    (hnormal : B ≤ Subgroup.normalizer (A : Set G))
    (hdisjoint : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnormal]
      exact z.property
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem chapter2_claim15_normal_of_index_eq_prime_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hGp : IsPGroup p G) (A : Subgroup G) (hindex : A.index = p) :
    A.Normal := by
  rcases hGp.exists_card_eq with ⟨n, hGcard⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    have hcard_one : Nat.card G = 1 := by simpa [hn] using hGcard
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard_one).1
    have hAtop : A = ⊤ := by
      apply le_antisymm le_top
      intro x _hx
      have hxone : x = 1 := Subsingleton.elim x 1
      simp [hxone]
    have hp_one : p = 1 := by simpa [hAtop] using hindex.symm
    exact (Fact.out : Nat.Prime p).ne_one hp_one
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [hindex, hGcard]
  exact ((Fact.out : Nat.Prime p).pow_minFac hn_ne).symm

private theorem chapter2_claim15_pgroup_le_normal_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K L : Subgroup G) (hKp : IsPGroup p K) (hnot : ¬ p ∣ K.index)
    [K.Normal] (hLp : IsPGroup p L) :
    L ≤ K := by
  let Ks : Sylow p G := hKp.toSylow hnot
  have hInf := hLp.inf_normalizer_sylow Ks
  have hKs : (Ks : Subgroup G) = K := by
    simp [Ks]
  have hKsSet : (Ks : Set G) = (K : Set G) :=
    congrArg (fun H : Subgroup G ↦ (H : Set G)) hKs
  have hLnorm : L ≤ Subgroup.normalizer (Ks : Set G) := by
    rw [hKsSet, K.normalizer_eq_top]
    exact le_top
  have hleft : L ⊓ Subgroup.normalizer (Ks : Set G) = L :=
    inf_eq_left.mpr hLnorm
  rw [hleft] at hInf
  have hleKs : L ≤ (Ks : Subgroup G) := inf_eq_left.mp hInf.symm
  simpa [hKs] using hleKs


private theorem chapter2_claim15_P_normalizes_L
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P L : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
          V = peterfalviV D t ∧
            W ≤ V ∧
              W = peterfalviW V (K : Set G) ∧
                Q0 ≤ Q ∧
                  (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                    S ≤ Q ∧
                      Q1 ≤ Q ∧
                        (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                          Odd (Nat.card Q1) ∧
                            Disjoint S Q1 ∧
                              (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 →
                                s * q1 = q1 * s) ∧
                                S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hP_le_V : P ≤ V)
    (hL_constructed :
      L = Subgroup.centralizer ({s * t} : Set G) ⊓
        psl2GeneratedSubgroup Q0 K t) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  have hV_eq_Cs : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = peterfalviV D t := hsec.section2.V_eq
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (proposition_5 H D Q t s hsec.section2.hA.A1 hsec.s_mem_H
          hsec.s_involution hsec.s_conjugate).1
  have hKnormal : (K.subgroupOf D).Normal :=
    (proposition_2 H D Q K V W Q0 S Q1 t hsec.section2).2
  intro g hgP
  have hgV : g ∈ V := hP_le_V hgP
  have hgDt : g ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
    simpa [peterfalviV, hsec.section2.V_eq] using hgV
  have hgDs : g ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [← hV_eq_Cs]
    exact hgV
  have hgCst : g ∈ Subgroup.centralizer ({s * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsg : Commute s g :=
      (Subgroup.mem_centralizer_singleton_iff.mp hgDs.2).symm
    have htg : Commute t g :=
      (Subgroup.mem_centralizer_singleton_iff.mp hgDt.2).symm
    exact (hsg.mul_left htg).eq.symm
  have hg_norm_Cst :
      g ∈ Subgroup.normalizer
        (Subgroup.centralizer ({s * t} : Set G) : Set G) :=
    Subgroup.le_normalizer hgCst
  let gen : Set G := (Q0 : Set G) ∪ (K : Set G) ∪ {t}
  have hgen : ∀ a : G, a ∈ P → ∀ x : G, x ∈ gen →
      a * x * a⁻¹ ∈ Subgroup.closure gen := by
    intro a haP x hx
    have haV : a ∈ V := hP_le_V haP
    have haD : a ∈ D :=
      proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec.section2 haV
    let aD : D := ⟨a, haD⟩
    rcases hx with (hxQ0 | hxK) | hxt
    · let xQ0 : Q0 := ⟨x, hxQ0⟩
      have hx' := proposition_3_Q0_rightConjugate_mem_of_D
        H D Q K V W Q0 S Q1 t hsec.section2 aD xQ0
      apply Subgroup.subset_closure
      apply Or.inl
      apply Or.inl
      simpa [aD, xQ0, rightConjugateElem, mul_assoc] using hx'
    · let xD : D := ⟨x, hsec.section2.K_le_D hxK⟩
      have hxSub : xD ∈ K.subgroupOf D := hxK
      have hx' := hKnormal.conj_mem xD hxSub aD
      apply Subgroup.subset_closure
      apply Or.inl
      apply Or.inr
      exact hx'
    · have hx_eq : x = t := by simpa using hxt
      subst x
      have haDt : a ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
        simpa [peterfalviV, hsec.section2.V_eq] using haV
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp haDt.2
      have hconj : a * t * a⁻¹ = t := by
        calc
          a * t * a⁻¹ = t * a * a⁻¹ := by rw [hcomm]
          _ = t := by simp
      rw [hconj]
      exact Subgroup.subset_closure (Or.inr rfl)
  have hg_norm_M :
      g ∈ Subgroup.normalizer (psl2GeneratedSubgroup Q0 K t : Set G) := by
    change g ∈ Subgroup.normalizer (Subgroup.closure gen : Set G)
    exact chapter2_claim15_mem_normalizer_closure g
      (hgen g hgP) (by
        intro x hx
        simpa only [inv_inv] using hgen g⁻¹ (P.inv_mem hgP) x hx)
  rw [hL_constructed]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hg_norm_Cst, hg_norm_M⟩

private lemma chapter2_claim15_V_le_centralizer_zpowers
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
          V = peterfalviV D t ∧
            W ≤ V ∧
              W = peterfalviW V (K : Set G) ∧
                Q0 ≤ Q ∧
                  (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                    S ≤ Q ∧
                      Q1 ≤ Q ∧
                        (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                          Odd (Nat.card Q1) ∧
                            Disjoint S Q1 ∧
                              (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 →
                                s * q1 = q1 * s) ∧
                                S ⊔ Q1 = Q) ∧
      s ∈ H ∧ IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    V ≤ Subgroup.centralizer (Subgroup.zpowers (s * t) : Set G) := by
  have hV_eq_Cs : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = peterfalviV D t := hsec.section2.V_eq
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (proposition_5 H D Q t s hsec.section2.hA.A1 hsec.s_mem_H
          hsec.s_involution hsec.s_conjugate).1
  intro v hv
  have hvDt : v ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
    simpa [peterfalviV, hsec.section2.V_eq] using hv
  have hvDs : v ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [← hV_eq_Cs]
    exact hv
  have hvCst : v ∈ Subgroup.centralizer ({s * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsv : Commute s v :=
      (Subgroup.mem_centralizer_singleton_iff.mp hvDs.2).symm
    have htv : Commute t v :=
      (Subgroup.mem_centralizer_singleton_iff.mp hvDt.2).symm
    exact (hsv.mul_left htv).eq.symm
  simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hvCst

private theorem chapter2_claim15_L_construction_source_interface
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (A : Type u) [Group A] [Finite A],
        ∀ (ΩA : Type v) [MulAction A ΩA] [Finite ΩA]
          (HA DA QA : Subgroup A) (tA : A),
          Nat.card A < Nat.card G →
            HypothesisA A ΩA HA DA QA tA →
              suzukiConclusion A ΩA)
    (hst_order : orderOf (s * t) = 3)
    (hQ0card : Nat.card Q0 = 8)
    (_h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2) :
    ∃ L : Subgroup G,
      L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t ∧
        Nat.card L = 9 ∧ IsCyclic L ∧
          Subgroup.center (psl2GeneratedSubgroup Q0 K t) = ⊥ := by
  let L : Subgroup G :=
    Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t
  have hsQ0 : s ∈ Q0 :=
    (hch.section3.section2.Q0_def s).mpr
      (Or.inr ⟨hch.section3.s_mem_H, hch.section3.s_involution⟩)
  have hsM : s ∈ psl2GeneratedSubgroup Q0 K t :=
    Subgroup.subset_closure (Or.inl (Or.inl hsQ0))
  have htM : t ∈ psl2GeneratedSubgroup Q0 K t :=
    Subgroup.subset_closure (Or.inr rfl)
  have hstM : s * t ∈ psl2GeneratedSubgroup Q0 K t :=
    (psl2GeneratedSubgroup Q0 K t).mul_mem hsM htM
  have hV_ne : V ≠ ⊥ := by
    intro hV
    have hPbot : P = ⊥ := by
      apply le_antisymm
      · simpa [hV] using hch.B1.P_le_V
      · exact bot_le
    have hp_one : p = 1 := by
      calc
        p = Nat.card P := hch.B1.P_card.symm
        _ = 1 := by simp [hPbot]
    exact hch.B1.p_prime.ne_one hp_one
  obtain ⟨_hgenerated, m, hm_ne, hmQ0, he⟩ :=
    lemma_4 H D Q K V W Q0 S Q1 t s hch.section3 hind
      hst_order hV_ne
  have hm_three : m = 3 := by
    have hpow : 2 ^ m = 2 ^ 3 := by
      calc
        2 ^ m = Nat.card Q0 := hmQ0.symm
        _ = 8 := hQ0card
        _ = 2 ^ 3 := by norm_num
    exact Nat.pow_right_injective (by norm_num : 1 < 2) hpow
  subst m
  obtain ⟨e⟩ := he
  let stM : psl2GeneratedSubgroup Q0 K t := ⟨s * t, hstM⟩
  have hstM_order : orderOf stM = 3 := by
    simpa [stM] using hst_order
  have he_st_order : orderOf (e stM) = 3 := by
    simpa using hstM_order
  have hpsl := psl28_orderThree_centralizer_cyclic_order_nine
    (e stM) he_st_order
  let eL := chapter2_claim15_inf_centralizer_mulEquiv
    (psl2GeneratedSubgroup Q0 K t) (s * t) hstM e
  have hL_order : Nat.card L = 9 := by
    calc
      Nat.card L = Nat.card
          (Subgroup.centralizer
            ({e stM} : Set (PSL2BinaryMatrixGroup 3))) := by
        exact Nat.card_congr eL.toEquiv
      _ = 9 := hpsl.1
  have hL_cyclic : IsCyclic L := by
    exact eL.isCyclic.mpr hpsl.2
  have hM_center :
      Subgroup.center (psl2GeneratedSubgroup Q0 K t) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    calc
      Nat.card (Subgroup.center (psl2GeneratedSubgroup Q0 K t)) =
          Nat.card (Subgroup.center (PSL2BinaryMatrixGroup 3)) :=
        Nat.card_congr (Subgroup.centerCongr e).toEquiv
      _ = 1 := by rw [psl28_binary3_center_eq_bot]; simp
  exact ⟨L, rfl, hL_order, hL_cyclic, hM_center⟩

private theorem chapter2_claim15_s_inverts_L
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (_h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (_hL_le_R1 : L ≤ R1) (hL_order : Nat.card L = 9)
    (hL_cyclic : IsCyclic L) :
    ∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹ := by
  have hsQ0 : s ∈ Q0 :=
    (hch.section3.section2.Q0_def s).mpr
      (Or.inr ⟨hch.section3.s_mem_H, hch.section3.s_involution⟩)
  have hst_ne : s * t ≠ 1 := by
    intro hst
    apply hch.section3.section2.hA.A1.t_not_mem_H
    have ht_eq : t = s⁻¹ := by
      calc
        t = 1 * t := by simp
        _ = (s⁻¹ * s) * t := by simp
        _ = s⁻¹ * (s * t) := by rw [mul_assoc]
        _ = s⁻¹ := by rw [hst]; simp
    rw [ht_eq]
    exact H.inv_mem hch.section3.s_mem_H
  exact chapter2_claim15_s_inverts_cyclic_L Q0 K L t s hsQ0
    hch.section3.s_involution hch.section3.section2.hA.A1.involution_t
    hst_ne hL_constructed hL_order hL_cyclic

private theorem chapter2_claim15_V_normalizes_L_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hWP : W ⊔ P = V)
    (_h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (_hL_le_R1 : L ≤ R1) (_hL_order : Nat.card L = 9)
    (_hL_cyclic : IsCyclic L) :
    V ≤ Subgroup.normalizer (L : Set G) := by
  have hP_norm : P ≤ Subgroup.normalizer (L : Set G) :=
    chapter2_claim15_P_normalizes_L H D Q K V W Q0 S Q1 P L t s
      hch.section3 hch.B1.P_le_V hL_constructed
  have hW_inv_cent :
      W = D ⊓ Subgroup.centralizer
        ({x : G | x ∈ H ∧ IsInvolution x} : Set G) :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hch.section3.section2.hA.A1
        hch.section3.section2.K_def hch.section3.section2.V_eq
        hch.section3.section2.W_eq
  have hW_cent : W ≤ Subgroup.centralizer (L : Set G) :=
    chapter2_claim15_W_centralizes_generated_L
      H D K V W Q0 L t s hch.section3.section2.Q0_def
      hch.section3.section2.V_eq hch.section3.section2.W_eq
      hW_inv_cent (by rw [hL_constructed]; exact inf_le_right)
  have hW_norm : W ≤ Subgroup.normalizer (L : Set G) :=
    hW_cent.trans (chapter2_claim15_centralizer_le_normalizer L)
  rw [← hWP]
  exact sup_le hW_norm hP_norm

private theorem chapter2_claim15_W_centralizes_L
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (_h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (_hL_le_R1 : L ≤ R1) (_hL_order : Nat.card L = 9)
    (_hL_cyclic : IsCyclic L) :
    W ≤ Subgroup.centralizer (L : Set G) := by
  have hW_inv_cent :
      W = D ⊓ Subgroup.centralizer
        ({x : G | x ∈ H ∧ IsInvolution x} : Set G) :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hch.section3.section2.hA.A1
        hch.section3.section2.K_def hch.section3.section2.V_eq
        hch.section3.section2.W_eq
  exact chapter2_claim15_W_centralizes_generated_L
    H D K V W Q0 L t s hch.section3.section2.Q0_def
    hch.section3.section2.V_eq hch.section3.section2.W_eq
    hW_inv_cent (by rw [hL_constructed]; exact inf_le_right)

private theorem chapter2_claim15_P_not_centralizes_L_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (_hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hR2_inf_CP :
      R2 ⊓ Subgroup.centralizer (P : Set G) = R ⊔ Sigma)
    (hXcube : ∀ x : G, x ∈ R ⊔ Sigma → x ^ 3 = 1)
    (hL_order : Nat.card L = 9) (hL_cyclic : IsCyclic L) :
    ¬ P ≤ Subgroup.centralizer (L : Set G) := by
  intro hP_centralizes
  have hL_le_CP : L ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff.mpr hP_centralizes
  have hL_le_CZ1 : L ≤ Subgroup.centralizer (Z1 : Set G) := by
    rw [hZ1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro x hxL
    rw [hL_constructed] at hxL
    exact hxL.1
  have hL_le_R2 : L ≤ R2 := by
    rw [h14.2.2.2.2.2.2.2.1]
    exact hL_le_CZ1
  have hL_le_X : L ≤ R ⊔ Sigma := by
    intro x hxL
    have hxInf : x ∈ R2 ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hL_le_R2 hxL, hL_le_CP hxL⟩
    rw [hR2_inf_CP] at hxInf
    exact hxInf
  letI : IsCyclic L := hL_cyclic
  obtain ⟨g, hgorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := L)
  rw [hL_order] at hgorder
  have hgcube : (g : G) ^ 3 = 1 := hXcube g (hL_le_X g.property)
  have hgcubeL : g ^ 3 = 1 := by
    apply Subtype.ext
    exact hgcube
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hgcubeL
  rw [hgorder] at hdvd
  norm_num at hdvd

private theorem chapter2_claim15_LV_le_R2_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (_hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hL_le_R1 : L ≤ R1) (_hL_order : Nat.card L = 9)
    (_hL_cyclic : IsCyclic L) :
    L ⊔ V ≤ R2 := by
  have hL_le_R2 : L ≤ R2 := by
    exact hL_le_R1.trans h14.2.2.2.2.2.2.2.2
  have hV_le_R2 : V ≤ R2 := by
    rw [h14.2.2.2.2.2.2.2.1, hZ1]
    exact chapter2_claim15_V_le_centralizer_zpowers
      H D Q K V W Q0 S Q1 t s hch.section3
  exact sup_le hL_le_R2 hV_le_R2

private theorem chapter2_claim15_LV_index_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (_h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (_hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (_hL_le_R1 : L ≤ R1) (hL_order : Nat.card L = 9)
    (hL_cyclic : IsCyclic L)
    (hWP : W ⊔ P = V) (hPcard : Nat.card P = 3)
    (hV_norm : V ≤ Subgroup.normalizer (L : Set G))
    (hW_cent : W ≤ Subgroup.centralizer (L : Set G))
    (hP_not_cent : ¬ P ≤ Subgroup.centralizer (L : Set G))
    (hdisjoint_L_W : Disjoint L W)
    (hR2s : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2)
    (hGlobalCard : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u)
    (hLV_le_R2 : L ⊔ V ≤ R2) :
    ((L ⊔ V).subgroupOf R2).index = 3 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP_norm_W : P ≤ Subgroup.normalizer (W : Set G) := by
    rcases (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1 with
      ⟨_hW_le_V, hP_le_V, hW_norm, _hdisjoint, _hWP⟩
    intro x hxP
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hW_norm x w (hP_le_V hxP)
    · intro hxwx
      have hback := hW_norm x⁻¹ (x * w * x⁻¹)
        (V.inv_mem (hP_le_V hxP)) hxwx
      simpa [mul_assoc] using hback
  have hdisjoint_W_P : Disjoint W P :=
    (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1.2.2.2.1
  have hdisjoint_L_V : Disjoint L V := by
    rw [Subgroup.disjoint_def]
    intro x hxL hxV
    have hxProd : x ∈ (W : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left W P hP_norm_W, hWP]
      exact hxV
    rcases hxProd with ⟨w, hwW, q, hqP, hwq⟩
    letI : CommGroup L := hL_cyclic.commGroup
    have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyL
      have hcomm : (⟨y, hyL⟩ : L) * ⟨x, hxL⟩ =
          ⟨x, hxL⟩ * ⟨y, hyL⟩ := mul_comm _ _
      exact congrArg Subtype.val hcomm
    have hqCL : q ∈ Subgroup.centralizer (L : Set G) := by
      have hwCL := hW_cent hwW
      have hmem := (Subgroup.centralizer (L : Set G)).mul_mem
        ((Subgroup.centralizer (L : Set G)).inv_mem hwCL) hxCL
      have hqeq : w⁻¹ * x = q := by
        rw [← hwq]
        simp
      simpa [hqeq] using hmem
    have hq_one : q = 1 := by
      by_contra hq_ne
      apply hP_not_cent
      intro z hzP
      let qP : P := ⟨q, hqP⟩
      let zP : P := ⟨z, hzP⟩
      have hqP_ne : qP ≠ 1 := by
        intro h
        exact hq_ne (congrArg Subtype.val h)
      have hzpow : zP ∈ Subgroup.zpowers qP :=
        mem_zpowers_of_prime_card (G := P) (p := 3) hPcard hqP_ne
      rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hn⟩
      have hzEq : q ^ n = z := congrArg Subtype.val hn
      exact hzEq ▸ (Subgroup.centralizer (L : Set G)).zpow_mem hqCL n
    have hxW : x ∈ W := by
      rw [← hwq, hq_one]
      simpa using hwW
    exact Subgroup.disjoint_def.mp hdisjoint_L_W hxL hxW
  have hVcard : Nat.card V = Nat.card W * 3 := by
    rw [← hWP,
      chapter2_claim15_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        W P hP_norm_W hdisjoint_W_P, hPcard]
  have hLVcard : Nat.card (L ⊔ V : Subgroup G) = 27 * Nat.card W := by
    rw [chapter2_claim15_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
      L V hV_norm hdisjoint_L_V, hL_order, hVcard]
    ring
  rcases hR2s with ⟨R2s, hR2s⟩
  rcases hGlobalCard with ⟨k, u, hpart, hGcard, hu⟩
  have hGfactor : Nat.card G = 3 ^ k * u := by rw [← hpart, hGcard]
  have hR2card : Nat.card R2 = 81 * Nat.card W := by
    rw [← hR2s, chapter2_claim15_sylow_card_from_factorization R2s k u
      hGfactor hu, ← hpart]
    norm_num
  have hR2card' : Nat.card R2 = 3 * Nat.card (L ⊔ V : Subgroup G) := by
    rw [hR2card, hLVcard]
    ring
  have hmul := ((L ⊔ V).subgroupOf R2).index_mul_card
  rw [natCard_subgroupOf_eq (L ⊔ V) R2 hLV_le_R2, hR2card'] at hmul
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (L ⊔ V : Subgroup G)))
  simpa using hmul

private theorem chapter2_claim15_center_LV_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (_hL_le_R1 : L ≤ R1) (hL_order : Nat.card L = 9)
    (hL_cyclic : IsCyclic L)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hWP : W ⊔ P = V) (hPcard : Nat.card P = 3)
    (hZ1card : Nat.card Z1 = 3) (hW_cyclic : IsCyclic W)
    (hW_cent : W ≤ Subgroup.centralizer (L : Set G))
    (hP_not_cent : ¬ P ≤ Subgroup.centralizer (L : Set G))
    (hdisjoint_L_W : Disjoint L W) :
    (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
      Z1 ⊔ Sigma := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ1_le_L : Z1 ≤ L := by
    rw [hZ1]
    apply Subgroup.zpowers_le.mpr
    rw [hL_constructed]
    constructor
    · simp [Subgroup.mem_centralizer_iff]
    · apply (psl2GeneratedSubgroup Q0 K t).mul_mem
      · exact Subgroup.subset_closure
          (Or.inl (Or.inl ((hch.section3.section2.Q0_def s).mpr
            (Or.inr ⟨hch.section3.s_mem_H, hch.section3.s_involution⟩))))
      · exact Subgroup.subset_closure (Or.inr rfl)
  have hP_norm_L : P ≤ Subgroup.normalizer (L : Set G) :=
    chapter2_claim15_P_normalizes_L H D Q K V W Q0 S Q1 P L t s
      hch.section3 hch.B1.P_le_V hL_constructed
  have hP_norm_W : P ≤ Subgroup.normalizer (W : Set G) := by
    rcases (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1 with
      ⟨_hW_le_V, hP_le_V, hW_norm, _hdisjoint, _hWP⟩
    intro x hxP
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hW_norm x w (hP_le_V hxP)
    · intro hxwx
      have hback := hW_norm x⁻¹ (x * w * x⁻¹)
        (V.inv_mem (hP_le_V hxP)) hxwx
      simpa [mul_assoc] using hback
  have hW_norm_L : W ≤ Subgroup.normalizer (L : Set G) :=
    hW_cent.trans (chapter2_claim15_centralizer_le_normalizer L)
  have hZ1_le_CL : Z1 ≤ Subgroup.centralizer (L : Set G) := by
    letI : CommGroup L := hL_cyclic.commGroup
    intro z hzZ
    rw [Subgroup.mem_centralizer_iff]
    intro x hxL
    exact congrArg Subtype.val
      (show (⟨x, hxL⟩ : L) * ⟨z, hZ1_le_L hzZ⟩ =
        ⟨z, hZ1_le_L hzZ⟩ * ⟨x, hxL⟩ from mul_comm _ _)
  have hV_le_CZ1 : V ≤ Subgroup.centralizer (Z1 : Set G) := by
    rw [hZ1]
    exact chapter2_claim15_V_le_centralizer_zpowers
      H D Q K V W Q0 S Q1 t s hch.section3
  have hZ1_le_CV : Z1 ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mpr hV_le_CZ1
  have hSigma_le_W : Sigma ≤ W := by rw [hSigma]; exact inf_le_left
  have hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G) := by
    rw [hSigma]
    exact inf_le_right
  have hSigma_le_CW : Sigma ≤ Subgroup.centralizer (W : Set G) := by
    letI : CommGroup W := hW_cyclic.commGroup
    intro z hzSigma
    rw [Subgroup.mem_centralizer_iff]
    intro w hwW
    exact congrArg Subtype.val
      (show (⟨w, hwW⟩ : W) * ⟨z, hSigma_le_W hzSigma⟩ =
        ⟨z, hSigma_le_W hzSigma⟩ * ⟨w, hwW⟩ from mul_comm _ _)
  have hSigma_le_CV : Sigma ≤ Subgroup.centralizer (V : Set G) := by
    rw [← hWP, chapter2_claim15_centralizer_sup]
    intro z hzSigma
    exact ⟨hSigma_le_CW hzSigma, hSigma_le_CP hzSigma⟩
  have hZ1_le_center :
      Z1 ≤ (L ⊔ V) ⊓
        Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
    intro z hzZ
    constructor
    · exact Subgroup.mem_sup_left (hZ1_le_L hzZ)
    · rw [chapter2_claim15_centralizer_sup]
      exact ⟨hZ1_le_CL hzZ, hZ1_le_CV hzZ⟩
  have hSigma_le_center :
      Sigma ≤ (L ⊔ V) ⊓
        Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
    intro z hzSigma
    constructor
    · exact Subgroup.mem_sup_right (hch.section3.section2.W_le_V
        (hSigma_le_W hzSigma))
    · rw [chapter2_claim15_centralizer_sup]
      exact ⟨hW_cent (hSigma_le_W hzSigma), hSigma_le_CV hzSigma⟩
  apply le_antisymm
  · intro x hx
    let A : Subgroup G := L ⊔ W
    have hP_norm_A : P ≤ Subgroup.normalizer (A : Set G) := by
      intro q hqP
      exact chapter2_claim15_mem_normalizer_sup_of_normalizes
        (hP_norm_L hqP) (hP_norm_W hqP)
    have hxAP : x ∈ A ⊔ P := by
      have hxLV := hx.1
      rw [← hWP] at hxLV
      simpa [A, sup_assoc] using hxLV
    have hxProd : x ∈ (A : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A P hP_norm_A]
      exact hxAP
    rcases hxProd with ⟨a, haA, q, hqP, haq⟩
    have hA_le_CL : A ≤ Subgroup.centralizer (L : Set G) := by
      apply sup_le
      · letI : CommGroup L := hL_cyclic.commGroup
        intro z hzL
        rw [Subgroup.mem_centralizer_iff]
        intro y hyL
        exact congrArg Subtype.val
          (show (⟨y, hyL⟩ : L) * ⟨z, hzL⟩ =
            ⟨z, hzL⟩ * ⟨y, hyL⟩ from mul_comm _ _)
      · exact hW_cent
    have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyL
      exact Subgroup.mem_centralizer_iff.mp hx.2 y (Subgroup.mem_sup_left hyL)
    have hqCL : q ∈ Subgroup.centralizer (L : Set G) := by
      have haCL := hA_le_CL haA
      have hmem := (Subgroup.centralizer (L : Set G)).mul_mem
        ((Subgroup.centralizer (L : Set G)).inv_mem haCL) hxCL
      have hqeq : a⁻¹ * x = q := by rw [← haq]; simp
      simpa [hqeq] using hmem
    have hq_one : q = 1 := by
      by_contra hq_ne
      apply hP_not_cent
      intro z hzP
      let qP : P := ⟨q, hqP⟩
      let zP : P := ⟨z, hzP⟩
      have hqP_ne : qP ≠ 1 := by
        intro h
        exact hq_ne (congrArg Subtype.val h)
      have hzpow : zP ∈ Subgroup.zpowers qP :=
        mem_zpowers_of_prime_card (G := P) (p := 3) hPcard hqP_ne
      rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hn⟩
      have hzEq : q ^ n = z := congrArg Subtype.val hn
      exact hzEq ▸ (Subgroup.centralizer (L : Set G)).zpow_mem hqCL n
    have hxA : x ∈ A := by
      rw [← haq, hq_one]
      simpa using haA
    have hxCP : x ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      exact Subgroup.mem_centralizer_iff.mp hx.2 y
        (Subgroup.mem_sup_right (hch.B1.P_le_V hyP))
    have hxLWProd : x ∈ (L : Set G) * (W : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L W hW_norm_L]
      exact hxA
    rcases hxLWProd with ⟨l, hlL, w, hwW, hlw⟩
    change l * w = x at hlw
    have hparts : ∀ q : G, q ∈ P →
        q * l * q⁻¹ = l ∧ q * w * q⁻¹ = w := by
      intro q hqP
      have hqlL : q * l * q⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hP_norm_L hqP) l).1 hlL
      have hqwW : q * w * q⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hP_norm_W hqP) w).1 hwW
      have hqx : q * x * q⁻¹ = x := by
        have hcomm := Subgroup.mem_centralizer_iff.mp hxCP q hqP
        calc
          q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [hcomm]
          _ = x := by simp [mul_assoc]
      have hprodEq :
          (q * l * q⁻¹) * (q * w * q⁻¹) = l * w := by
        calc
          (q * l * q⁻¹) * (q * w * q⁻¹) =
              q * (l * w) * q⁻¹ := by group
          _ = q * x * q⁻¹ := by rw [hlw]
          _ = x := hqx
          _ = l * w := hlw.symm
      let leftPair : L × W :=
        (⟨q * l * q⁻¹, hqlL⟩, ⟨q * w * q⁻¹, hqwW⟩)
      let rightPair : L × W := (⟨l, hlL⟩, ⟨w, hwW⟩)
      have hpairs : leftPair = rightPair := by
        apply Subgroup.mul_injective_of_disjoint hdisjoint_L_W
        exact hprodEq
      constructor
      · exact congrArg (fun z : L × W => ((z.1 : L) : G)) hpairs
      · exact congrArg (fun z : L × W => ((z.2 : W) : G)) hpairs
    obtain ⟨q0, hq0P, hq0_not⟩ := SetLike.not_le_iff_exists.mp hP_not_cent
    have hq0_cent_Z1 : q0 ∈ Subgroup.centralizer (Z1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hzZ
      have hq0R : q0 ∈ R :=
        (h14.2.2.2.1 (Subgroup.mem_sup_right hq0P)).1
      have hzCR : z ∈ Subgroup.centralizer (R : Set G) :=
        (h14.2.2.2.1 (Subgroup.mem_sup_left hzZ)).2
      exact (Subgroup.mem_centralizer_iff.mp hzCR q0 hq0R).symm
    have hlZ1 : l ∈ Z1 :=
      cyclic_order_nine_fixed_subgroup_eq L Z1 q0 hL_order hL_cyclic
        hZ1card hZ1_le_L (hP_norm_L hq0P) hq0_cent_Z1 hq0_not l hlL
          (hparts q0 hq0P).1
    have hwCP : w ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hqP
      have hfix := (hparts q hqP).2
      have hright := congrArg (fun z : G => z * q) hfix
      have hcomm : q * w = w * q := by simpa [mul_assoc] using hright
      exact hcomm
    have hwSigma : w ∈ Sigma := by rw [hSigma]; exact ⟨hwW, hwCP⟩
    rw [← hlw]
    exact Subgroup.mul_mem_sup hlZ1 hwSigma
  · exact sup_le hZ1_le_center hSigma_le_center

-- The exponent-three step here cites Huppert III, Lemma 1.3(b).
private theorem chapter2_claim15_omega_one_LV_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hL_constructed : L = Subgroup.centralizer ({s * t} : Set G) ⊓ psl2GeneratedSubgroup Q0 K t)
    (_hL_le_R1 : L ≤ R1) (hL_order : Nat.card L = 9)
    (hL_cyclic : IsCyclic L)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hWP : W ⊔ P = V) (hPcard : Nat.card P = 3)
    (hZ1card : Nat.card Z1 = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hW_cyclic : IsCyclic W)
    (hWcard : Nat.card W = 3 ∨ Nat.card W = 9)
    (hW_cent : W ≤ Subgroup.centralizer (L : Set G))
    (hdisjoint_L_W : Disjoint L W)
    (hcenter :
      (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
        Z1 ⊔ Sigma)
    (hXcube : ∀ x : G, x ∈ R ⊔ Sigma → x ^ 3 = 1) :
    ∀ x : G, x ∈ L ⊔ V → (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ1_le_L : Z1 ≤ L := by
    rw [hZ1]
    apply Subgroup.zpowers_le.mpr
    rw [hL_constructed]
    constructor
    · simp [Subgroup.mem_centralizer_iff]
    · apply (psl2GeneratedSubgroup Q0 K t).mul_mem
      · exact Subgroup.subset_closure
          (Or.inl (Or.inl ((hch.section3.section2.Q0_def s).mpr
            (Or.inr ⟨hch.section3.s_mem_H, hch.section3.s_involution⟩))))
      · exact Subgroup.subset_closure (Or.inr rfl)
  have hSigma_le_W : Sigma ≤ W := by rw [hSigma]; exact inf_le_left
  have hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G) := by
    rw [hSigma]
    exact inf_le_right
  have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) := by
    intro z hzZ
    rw [Subgroup.mem_centralizer_iff]
    intro q hqP
    have hzCR : z ∈ Subgroup.centralizer (R : Set G) :=
      (h14.2.2.2.1 (Subgroup.mem_sup_left hzZ)).2
    have hqR : q ∈ R :=
      (h14.2.2.2.1 (Subgroup.mem_sup_right hqP)).1
    exact Subgroup.mem_centralizer_iff.mp hzCR q hqR
  have hP_norm_L : P ≤ Subgroup.normalizer (L : Set G) :=
    chapter2_claim15_P_normalizes_L H D Q K V W Q0 S Q1 P L t s
      hch.section3 hch.B1.P_le_V hL_constructed
  have hP_norm_W : P ≤ Subgroup.normalizer (W : Set G) := by
    rcases (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1 with
      ⟨_hW_le_V, hP_le_V, hW_norm, _hdisjoint, _hWP⟩
    intro q hqP
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hW_norm q w (hP_le_V hqP)
    · intro hq
      have hback := hW_norm q⁻¹ (q * w * q⁻¹)
        (V.inv_mem (hP_le_V hqP)) hq
      simpa [mul_assoc] using hback
  have hW_norm_L : W ≤ Subgroup.normalizer (L : Set G) :=
    hW_cent.trans (chapter2_claim15_centralizer_le_normalizer L)
  let A : Subgroup G := L ⊔ W
  have hP_norm_A : P ≤ Subgroup.normalizer (A : Set G) := by
    intro q hqP
    exact chapter2_claim15_mem_normalizer_sup_of_normalizes
      (hP_norm_L hqP) (hP_norm_W hqP)
  have hZS_le_X : Z1 ⊔ Sigma ≤ R ⊔ Sigma := by
    apply sup_le
    · exact (fun z hzZ => Subgroup.mem_sup_left
        ((h14.2.2.2.1 (Subgroup.mem_sup_left hzZ)).1))
    · exact le_sup_right
  have hK_le_X : Z1 ⊔ Sigma ⊔ P ≤ R ⊔ Sigma := by
    apply sup_le hZS_le_X
    intro q hqP
    exact Subgroup.mem_sup_left
      ((h14.2.2.2.1 (Subgroup.mem_sup_right hqP)).1)
  intro x hxLV
  constructor
  · intro hx_order
    have hxAP : x ∈ A ⊔ P := by
      rw [← hWP] at hxLV
      simpa [A, sup_assoc] using hxLV
    have hxProd : x ∈ (A : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A P hP_norm_A]
      exact hxAP
    rcases hxProd with ⟨a, haA, q, hqP, haq⟩
    change a * q = x at haq
    have hcomm_aq : ⁅a, q⁆ ∈ Z1 ⊔ Sigma :=
      chapter2_claim15_commutator_mem_sup_cyclic_factors
        L W Z1 Sigma P hL_cyclic hW_cyclic hL_order hWcard
          hZ1card hSigmaCard hZ1_le_L hSigma_le_W hP_norm_L hP_norm_W
          hZ1_le_CP hSigma_le_CP hW_cent a haA q hqP
    have hcomm_qa : ⁅q, a⁆ ∈ Z1 ⊔ Sigma := by
      rw [← commutatorElement_inv]
      exact (Z1 ⊔ Sigma).inv_mem hcomm_aq
    have haLV : a ∈ L ⊔ V := by
      exact (sup_le le_sup_left
        (hch.section3.section2.W_le_V.trans le_sup_right)) haA
    have hqLV : q ∈ L ⊔ V :=
      Subgroup.mem_sup_right (hch.B1.P_le_V hqP)
    have hcomm_aq_center :
        ⁅a, q⁆ ∈ (L ⊔ V) ⊓
          Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) := by
      rw [hcenter]
      exact hcomm_aq
    have hcomm_a : Commute ⁅a, q⁆ a :=
      (Subgroup.mem_centralizer_iff.mp hcomm_aq_center.2 a haLV).symm
    have hcomm_q : Commute ⁅a, q⁆ q :=
      (Subgroup.mem_centralizer_iff.mp hcomm_aq_center.2 q hqLV).symm
    have hqCube : q ^ 3 = 1 := by
      have hp := pow_card_eq_one' (x := (⟨q, hqP⟩ : P))
      rw [hPcard] at hp
      exact congrArg Subtype.val hp
    have hcommCube : ⁅q, a⁆ ^ 3 = 1 :=
      hXcube _ (hZS_le_X hcomm_qa)
    have hformula := External.huppert_III_1_3_b a q hcomm_a hcomm_q 3
    rw [hqCube] at hformula
    norm_num [Nat.choose] at hformula
    rw [hcommCube] at hformula
    have haCube : a ^ 3 = 1 := by
      have hformula' : (a * q) ^ 3 = a ^ 3 := by simpa using hformula
      calc
        a ^ 3 = (a * q) ^ 3 := hformula'.symm
        _ = x ^ 3 := by rw [haq]
        _ = 1 := hx_order
    have haLWProd : a ∈ (L : Set G) * (W : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L W hW_norm_L]
      exact haA
    rcases haLWProd with ⟨l, hlL, w, hwW, hlw⟩
    change l * w = a at hlw
    have hlwComm : Commute l w := by
      exact Subgroup.mem_centralizer_iff.mp (hW_cent hwW) l hlL
    have hlwCube : l ^ 3 * w ^ 3 = 1 := by
      rw [← hlwComm.mul_pow, hlw, haCube]
    have hcubes := Subgroup.disjoint_iff_mul_eq_one.mp hdisjoint_L_W
      (L.pow_mem hlL 3) (W.pow_mem hwW 3) hlwCube
    have hlZ1 : l ∈ Z1 :=
      (chapter2_claim15_cube_eq_one_iff_mem_cyclic_order_three_subgroup
        L Z1 hL_cyclic (Or.inr hL_order) hZ1card hZ1_le_L l hlL).mp hcubes.1
    have hwSigma : w ∈ Sigma :=
      (chapter2_claim15_cube_eq_one_iff_mem_cyclic_order_three_subgroup
        W Sigma hW_cyclic hWcard hSigmaCard hSigma_le_W w hwW).mp hcubes.2
    rw [← haq, ← hlw]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hlZ1 hwSigma) hqP
  · intro hx_mem
    exact hXcube x (hK_le_X hx_mem)

public theorem claim_15
    {G : Type u} {Ω : Type v} {F : Type w}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [RightNearField F] [Finite F]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (A : Type u) [Group A] [Finite A],
        ∀ (ΩA : Type v) [MulAction A ΩA] [Finite ΩA]
          (HA DA QA : Subgroup A) (tA : A),
          Nat.card A < Nat.card G →
            HypothesisA A ΩA HA DA QA tA →
              suzukiConclusion A ΩA)
    (hst_order : orderOf (s * t) = 3)
    (hQ0card : Nat.card Q0 = 8)
    (hWP : W ⊔ P = V)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (addEquiv : Multiplicative F ≃* T)
    (hchar : addOrderOf (1 : F) = 3)
    (hR_eq : R = T ⊔ P)
    (hT_le_CP : T ≤ Subgroup.centralizer (P : Set G))
    (hp_three : p = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hW_cyclic : IsCyclic W)
    (hWcard : Nat.card W = 3 ∨ Nat.card W = 9)
    (hGlobalCard : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u)
    (h14 : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2)
    (hR1p : IsPGroup 3 R1)
    (hR2s : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2)
    (hNormalizerSplit :
      Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) =
        R1 ⊔ Subgroup.closure ({s} : Set G))
    (hR1_disjoint_s :
      Disjoint R1 (Subgroup.closure ({s} : Set G)))
    (hNormalizerNormR1 :
      Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ≤
        Subgroup.normalizer (R1 : Set G))
    (_hcenterR2 : R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1)
    (hderived :
      ⁅(R ⊔ Sigma : Subgroup G), (R ⊔ Sigma : Subgroup G)⁆ = Z1)
    (hR2_inf_CP :
      R2 ⊓ Subgroup.centralizer (P : Set G) = R ⊔ Sigma) :
    ∃ L : Subgroup G, L ≤ R1 ∧
      (Nat.card L = 9 ∧ IsCyclic L) ∧
        (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
          V ≤ Subgroup.normalizer (L : Set G) ∧
            W ≤ Subgroup.centralizer (L : Set G) ∧
              ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
                L ⊔ V ≤ R2 ∧
                  Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
                  (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
                    Z1 ⊔ Sigma ∧
                    ∀ x : G, x ∈ L ⊔ V →
                      (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P) := by
  rcases
    chapter2_claim15_L_construction_source_interface (G := G) (Ω := Ω)
      H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 t s p hch hind
        hst_order hQ0card h14 with
    ⟨L, hL_constructed, hL_order, hL_cyclic, hM_center⟩
  have hPcard : Nat.card P = 3 := by
    rw [hch.B1.P_card, hp_three]
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, hst_order]
  have hXcube : ∀ x : G, x ∈ R ⊔ Sigma → x ^ 3 = 1 :=
    chapter2_claim15_exceptional_sylow_exponent_three
      T P Sigma Z1 R addEquiv hchar hPcard hSigmaCard hZ1card
        hR_eq hT_le_CP h14.1 h14.2.2.2.2.1 hderived
  have hP_not_cent : ¬ P ≤ Subgroup.centralizer (L : Set G) :=
    chapter2_claim15_P_not_centralizes_L_source_interface
      H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L t s p hch h14
        hL_constructed hZ1 hR2_inf_CP hXcube hL_order hL_cyclic
  have hL_le_R1 : L ≤ R1 := by
    classical
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hZ1_le_L : Z1 ≤ L := by
      rw [hZ1]
      apply Subgroup.zpowers_le.mpr
      rw [hL_constructed]
      constructor
      · simp [Subgroup.mem_centralizer_iff]
      · apply (psl2GeneratedSubgroup Q0 K t).mul_mem
        · exact Subgroup.subset_closure
            (Or.inl (Or.inl ((hch.section3.section2.Q0_def s).mpr
              (Or.inr ⟨hch.section3.s_mem_H, hch.section3.s_involution⟩))))
        · exact Subgroup.subset_closure (Or.inr rfl)
    have hPcard : Nat.card P = 3 := by
      rw [hch.B1.P_card, hp_three]
    have hdisjoint_L_P : Disjoint L P := by
      let LP : Subgroup P := L.comap P.subtype
      letI : Fact (Nat.card P).Prime := ⟨by simpa [hPcard] using Nat.prime_three⟩
      have hLP_bot : LP = ⊥ := by
        rcases LP.eq_bot_or_eq_top_of_prime_card with hbot | htop
        · exact hbot
        · exfalso
          apply hP_not_cent
          have hP_le_L : P ≤ L := by
            intro x hxP
            have hxLP : (⟨x, hxP⟩ : P) ∈ LP := by simp [LP, htop]
            exact hxLP
          letI : CommGroup L := hL_cyclic.commGroup
          intro x hxP
          rw [Subgroup.mem_centralizer_iff]
          intro y hyL
          have hcomm : (⟨y, hyL⟩ : L) * ⟨x, hP_le_L hxP⟩ =
              ⟨x, hP_le_L hxP⟩ * ⟨y, hyL⟩ := mul_comm _ _
          exact congrArg Subtype.val hcomm
      rw [Subgroup.disjoint_def]
      intro x hxL hxP
      have hxLP : (⟨x, hxP⟩ : P) ∈ LP := hxL
      rw [hLP_bot] at hxLP
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxLP)
    have hP_norm_L : P ≤ Subgroup.normalizer (L : Set G) :=
      chapter2_claim15_P_normalizes_L H D Q K V W Q0 S Q1 P L t s
        hch.section3 hch.B1.P_le_V hL_constructed
    have hLP_card : Nat.card (L ⊔ P : Subgroup G) = 27 := by
      rw [chapter2_claim15_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        L P hP_norm_L hdisjoint_L_P, hL_order, hPcard]
    have hZ1card : Nat.card Z1 = 3 := by
      rw [hZ1, Nat.card_zpowers, hst_order]
    have hdisjoint_Z1_P : Disjoint Z1 P :=
      hdisjoint_L_P.mono hZ1_le_L le_rfl
    have hP_le_CZ1 : P ≤ Subgroup.centralizer (Z1 : Set G) := by
      intro x hxP
      rw [Subgroup.mem_centralizer_iff]
      intro z hzZ1
      have hxR : x ∈ R := (h14.2.2.2.1 (Subgroup.mem_sup_right hxP)).1
      have hzCR : z ∈ Subgroup.centralizer (R : Set G) :=
        (h14.2.2.2.1 (Subgroup.mem_sup_left hzZ1)).2
      exact (Subgroup.mem_centralizer_iff.mp hzCR x hxR).symm
    have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) :=
      hP_le_CZ1.trans (chapter2_claim15_centralizer_le_normalizer Z1)
    have hZ1P_card : Nat.card (Z1 ⊔ P : Subgroup G) = 9 := by
      rw [chapter2_claim15_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        Z1 P hP_norm_Z1 hdisjoint_Z1_P, hZ1card, hPcard]
    have hZ1P_le_LP : Z1 ⊔ P ≤ L ⊔ P :=
      sup_le (hZ1_le_L.trans le_sup_left) le_sup_right
    have hZ1P_index :
        ((Z1 ⊔ P).subgroupOf (L ⊔ P : Subgroup G)).index = 3 := by
      have hmul :=
        ((Z1 ⊔ P).subgroupOf (L ⊔ P : Subgroup G)).index_mul_card
      rw [natCard_subgroupOf_eq (Z1 ⊔ P) (L ⊔ P) hZ1P_le_LP,
        hZ1P_card, hLP_card] at hmul
      omega
    have hLP_p : IsPGroup 3 (L ⊔ P : Subgroup G) :=
      IsPGroup.of_card (n := 3) (by norm_num [hLP_card])
    have hZ1P_normal :
        ((Z1 ⊔ P).subgroupOf (L ⊔ P : Subgroup G)).Normal :=
      chapter2_claim15_normal_of_index_eq_prime_of_isPGroup
        hLP_p ((Z1 ⊔ P).subgroupOf (L ⊔ P : Subgroup G)) hZ1P_index
    have hLP_le_NZ1P :
        L ⊔ P ≤ Subgroup.normalizer ((Z1 ⊔ P : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZ1P_le_LP).mp hZ1P_normal
    have hL_le_NZ1P :
        L ≤ Subgroup.normalizer ((Z1 ⊔ P : Subgroup G) : Set G) :=
      le_sup_left.trans hLP_le_NZ1P
    have hCZ1P :
        Subgroup.centralizer ((Z1 ⊔ P : Subgroup G) : Set G) = R ⊔ Sigma := by
      calc
        Subgroup.centralizer ((Z1 ⊔ P : Subgroup G) : Set G) =
            Subgroup.centralizer (Z1 : Set G) ⊓
              Subgroup.centralizer (P : Set G) :=
          chapter2_claim15_centralizer_sup Z1 P
        _ = R2 ⊓ Subgroup.centralizer (P : Set G) := by
          rw [h14.2.2.2.2.2.2.2.1]
        _ = R ⊔ Sigma := hR2_inf_CP
    have hL_le_NX :
        L ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) := by
      intro x hxL
      have hxNC := chapter2_claim15_mem_normalizer_centralizer_of_mem_normalizer
        (Z1 ⊔ P) (hL_le_NZ1P hxL)
      simpa [hCZ1P] using hxNC
    let N : Subgroup G :=
      Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)
    let C : Subgroup G := Subgroup.closure ({s} : Set G)
    have hN_eq : N = R1 ⊔ C := by
      simpa [N, C] using hNormalizerSplit
    have hR1_le_N : R1 ≤ N := by
      dsimp [N]
      exact h14.2.2.2.2.2.1
    have hC_le_N : C ≤ N := by
      rw [hN_eq]
      exact le_sup_right
    have hC_norm_R1 : C ≤ Subgroup.normalizer (R1 : Set G) :=
      hC_le_N.trans (by simpa [N] using hNormalizerNormR1)
    have hCcard : Nat.card C = 2 := by
      simpa [C] using chapter2_claim15_closure_involution_card s
        hch.section3.s_involution
    have hNcard : Nat.card N = Nat.card R1 * 2 := by
      rw [hN_eq,
        chapter2_claim15_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          R1 C hC_norm_R1 (by simpa [C] using hR1_disjoint_s),
        hCcard]
    have hR1_index_N : (R1.subgroupOf N).index = 2 := by
      have hmul := (R1.subgroupOf N).index_mul_card
      rw [natCard_subgroupOf_eq R1 N hR1_le_N, hNcard] at hmul
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := R1))
      simpa [Nat.mul_comm] using hmul
    have hR1sub_p : IsPGroup 3 (R1.subgroupOf N) :=
      hR1p.of_equiv (Subgroup.subgroupOfEquivOfLe hR1_le_N).symm
    have hL_le_N : L ≤ N := by simpa [N] using hL_le_NX
    have hL_p : IsPGroup 3 L :=
      IsPGroup.of_card (n := 2) (by norm_num [hL_order])
    have hLsub_p : IsPGroup 3 (L.subgroupOf N) :=
      hL_p.of_equiv (Subgroup.subgroupOfEquivOfLe hL_le_N).symm
    have hR1sub_normal : (R1.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hR1_le_N).mpr
        (by simpa [N] using hNormalizerNormR1)
    letI : (R1.subgroupOf N).Normal := hR1sub_normal
    have hLsub_le_R1sub : L.subgroupOf N ≤ R1.subgroupOf N :=
      chapter2_claim15_pgroup_le_normal_sylow
        (R1.subgroupOf N) (L.subgroupOf N) hR1sub_p
          (by rw [hR1_index_N]; norm_num) hLsub_p
    intro x hxL
    exact hLsub_le_R1sub (show (⟨x, hL_le_N hxL⟩ : N) ∈ L.subgroupOf N from hxL)
  have hcyc : Nat.card L = 9 ∧ IsCyclic L := ⟨hL_order, hL_cyclic⟩
  have hs_inv : ∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹ :=
    chapter2_claim15_s_inverts_L H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 hL_constructed hL_le_R1 hL_order hL_cyclic
  have hV_norm : V ≤ Subgroup.normalizer (L : Set G) :=
    chapter2_claim15_V_normalizes_L_source_interface H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch hWP h14 hL_constructed hL_le_R1 hL_order hL_cyclic
  have hW_cent : W ≤ Subgroup.centralizer (L : Set G) :=
    chapter2_claim15_W_centralizes_L H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 hL_constructed hL_le_R1 hL_order hL_cyclic
  have hdisjoint_L_W : Disjoint L W := by
    have hW_inv_cent :
        W = D ⊓ Subgroup.centralizer
          ({x : G | x ∈ H ∧ IsInvolution x} : Set G) :=
      peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hch.section3.section2.hA.A1
          hch.section3.section2.K_def hch.section3.section2.V_eq
          hch.section3.section2.W_eq
    exact chapter2_claim15_disjoint_L_W H D K V W Q0 L t s
      hch.section3.section2.Q0_def hch.section3.section2.V_eq
        hch.section3.section2.W_eq hW_inv_cent hL_constructed hM_center
  have hLV_le_R2 : L ⊔ V ≤ R2 :=
    chapter2_claim15_LV_le_R2_source_interface H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 hL_constructed hZ1 hL_le_R1 hL_order hL_cyclic
  have hLV_index : ((L ⊔ V).subgroupOf R2).index = 3 :=
    chapter2_claim15_LV_index_source_interface H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 hL_constructed hL_le_R1 hL_order hL_cyclic hWP hPcard
        hV_norm hW_cent hP_not_cent hdisjoint_L_W hR2s hGlobalCard hLV_le_R2
  have hindex : Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) := by
    calc
      Nat.card R2 = ((L ⊔ V).subgroupOf R2).index *
          Nat.card ((L ⊔ V).subgroupOf R2) :=
        ((L ⊔ V).subgroupOf R2).index_mul_card.symm
      _ = 3 * Nat.card ((L ⊔ V : Subgroup G)) := by
        rw [hLV_index, natCard_subgroupOf_eq (L ⊔ V) R2 hLV_le_R2]
  have hcenter :
      (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
        Z1 ⊔ Sigma :=
    chapter2_claim15_center_LV_source_interface H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 hL_constructed hL_le_R1 hL_order hL_cyclic hZ1
        hSigma hWP hPcard hZ1card hW_cyclic hW_cent hP_not_cent hdisjoint_L_W
  have homega : ∀ x : G, x ∈ L ⊔ V → (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P) :=
    chapter2_claim15_omega_one_LV_source_interface H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 hL_constructed hL_le_R1 hL_order hL_cyclic hZ1 hSigma
        hWP hPcard hZ1card hSigmaCard hW_cyclic hWcard hW_cent
        hdisjoint_L_W hcenter hXcube
  refine ⟨L, ?_⟩
  exact
    ⟨hL_le_R1, hcyc, hs_inv, hV_norm, hW_cent, hP_not_cent, hLV_le_R2, hindex,
      hcenter, homega⟩

end PFchapter2
end CFSG.BenderSuzuki
