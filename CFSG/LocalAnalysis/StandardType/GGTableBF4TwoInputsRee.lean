module

public import CFSG.LieType.Simplicity.TitsElements
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity CFSG.LieType.Simplicity.TitsBits CFSG.LieType.Simplicity.TitsBits.Letter

namespace TableBF4TwoInputs

section General

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem card_le_of_isPGroup_of_not_dvd {k : ℕ} (hG : ¬ p ^ (k + 1) ∣ Nat.card G)
    {S : Subgroup G} (hS : IsPGroup p S) : Nat.card S ≤ p ^ k := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  rw [hn]
  refine Nat.pow_le_pow_right hp.out.pos ?_
  by_contra hnk
  apply hG
  have h1 : p ^ (k + 1) ∣ p ^ n := Nat.pow_dvd_pow p (by omega)
  exact h1.trans (hn ▸ Subgroup.card_subgroup_dvd_card S)

theorem card_lt_of_isPGroup_of_not_comm {k : ℕ} (hG : ¬ p ^ (k + 1) ∣ Nat.card G)
    {H : Subgroup G} (hH : IsPGroup p H) {u v : G} (hu : u ∈ H) (hv : v ∈ H)
    (huv : u * v ≠ v * u) {E : Subgroup G} (hE : IsPGroup p E)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E < p ^ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  have hSk := card_le_of_isPGroup_of_not_dvd hG S.isPGroup'
  have hEeq : E = S :=
    Subgroup.eq_of_le_of_card_ge hES (hSk.trans hlt)
  obtain ⟨S', hHS'⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have hmem : ∀ z : G, z ∈ (S' : Subgroup G) → g⁻¹ * z * g ∈ (S : Subgroup G) := by
    intro z hz
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
    simpa [MulAut.conj_symm_apply] using hz
  have hu' := hmem u (hHS' hu)
  have hv' := hmem v (hHS' hv)
  rw [← hEeq] at hu' hv'
  have hc := hEc _ hu' _ hv'
  apply huv
  have e : u * v = g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ := by group
  have e' : v * u = g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
  rw [e, e', hc]

end General

@[expose] def reeAWord : List Letter := [x 0, x 3, n 0, n 3]

@[expose] def reeVWord : List Letter :=
  [x 0, x 3, n 1, n 2, n 1, n 2, n 0, n 3, n 1, n 2, n 1, n 2, x 0, x 3, n 0, n 3, n 2, n 1, n 2,
    n 1, n 3, n 0, n 2, n 1, n 2, n 1, x 3, x 0]

@[expose] def reeUWord : List Letter :=
  [x 0, x 3, x 2, x 1, n 2, x 1, n 2, x 2, x 1, n 2, x 1, n 2, x 2, x 1, n 2, x 1, n 2, n 1, n 2,
    n 1, n 2, n 1, n 2, n 1, n 2, n 1, n 2, n 1, n 2, x 0, x 3, n 0, n 3, n 0, n 3, x 2, x 1, n 2,
    x 1, n 2, x 2, x 1, n 2, x 1, n 2, x 2, x 1, n 2, x 1, n 2, n 0, n 3, n 1, n 2, n 1, n 2, n 0,
    n 3, n 0, n 3, n 0, n 3, n 1, n 2, n 1, n 2, x 0, x 3, n 1, n 2, n 1, n 2, x 0, x 3, n 1, n 2,
    n 1, n 2, x 0, x 3, x 2, x 1, n 2, x 1, n 2, x 0, x 3, n 0, n 3, x 0, x 3, n 0, n 3, n 0, n 3,
    n 1, n 2, n 1, n 2, n 0, n 3, n 1, n 2, n 1, n 2, n 0, n 3, x 0, x 3, n 1, n 2, n 1, n 2, x 2,
    x 1, n 2, x 1, n 2]

section Checks

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [CharP K 2]

theorem evalG_eq_one_of_evalB {w : List Letter} (h : evalB w % 2 ^ 2704 = evalB [] % 2 ^ 2704) :
    evalG K w = 1 := by
  rw [← evalG_nil (K := K)]
  exact (evalG_eq_evalG_iff w []).2 h

theorem evalG_pow_three (w : List Letter) : evalG K w ^ 3 = evalG K (w ++ w ++ w) := by
  rw [evalG_append, evalG_append, pow_three, mul_assoc]

theorem reeA_pow_three : evalG K reeAWord ^ 3 = 1 := by
  rw [evalG_pow_three]
  exact evalG_eq_one_of_evalB (by decide +kernel)

theorem reeV_pow_three : evalG K reeVWord ^ 3 = 1 := by
  rw [evalG_pow_three]
  exact evalG_eq_one_of_evalB (by decide +kernel)

theorem reeU_pow_three : evalG K reeUWord ^ 3 = 1 := by
  rw [evalG_pow_three]
  exact evalG_eq_one_of_evalB (by decide +kernel)

theorem reeA_ne_one : evalG K reeAWord ≠ 1 := by
  rw [← evalG_nil (K := K), Ne, evalG_eq_evalG_iff]
  decide +kernel

theorem reeA_mul_reeU :
    evalG K reeAWord * evalG K reeUWord = evalG K reeUWord * evalG K reeAWord := by
  rw [← evalG_append, ← evalG_append, evalG_eq_evalG_iff]
  decide +kernel

theorem reeA_mul_reeV :
    evalG K reeAWord * evalG K reeVWord = evalG K reeVWord * evalG K reeAWord := by
  rw [← evalG_append, ← evalG_append, evalG_eq_evalG_iff]
  decide +kernel

theorem reeU_conj_reeV :
    evalG K reeUWord * evalG K reeVWord * (evalG K reeUWord)⁻¹ =
      evalG K reeAWord * evalG K reeVWord := by
  rw [evalG_inv, ← evalG_append, ← evalG_append, ← evalG_append, evalG_eq_evalG_iff]
  decide +kernel

end Checks

section Fixed

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem reeA_mem : evalG K reeAWord ∈ reeFixed ReeTag.F4 K 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [mem_reeFixed, reeAut_evalG, evalG_eq_evalG_iff]
  decide +kernel

theorem reeV_mem : evalG K reeVWord ∈ reeFixed ReeTag.F4 K 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [mem_reeFixed, reeAut_evalG, evalG_eq_evalG_iff]
  decide +kernel

theorem reeU_mem : evalG K reeUWord ∈ reeFixed ReeTag.F4 K 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [mem_reeFixed, reeAut_evalG, evalG_eq_evalG_iff]
  decide +kernel

end Fixed

section Rank

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 3 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hg
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem exists_nonabelian_isPGroup_of_rel {G : Type*} [Group G] {a v u : G} (ha3 : a ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (hu3 : u ^ 3 = 1) (ha1 : a ≠ 1) (hau : a * u = u * a)
    (hav : a * v = v * a) (huv : u * v * u⁻¹ = a * v) :
    ∃ H : Subgroup G, IsPGroup 3 H ∧ ∃ u ∈ H, ∃ v ∈ H, u * v ≠ v * u := by
  have hvA : Subgroup.zpowers v ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left hav k)).eq
  set T : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers v with hT
  have hTp : IsPGroup 3 T := IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_three ha3)
    (isPGroup_zpowers_of_pow_three hv3) hvA
  have haT : a ∈ T := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hvT : v ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hconj : ∀ g ∈ T, u * g * u⁻¹ ∈ T := by
    have hle : T ≤ T.comap (MulAut.conj u).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        change u * a * u⁻¹ ∈ T
        rw [← hau, mul_inv_cancel_right]
        exact haT
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        change u * v * u⁻¹ ∈ T
        rw [huv]
        exact mul_mem haT hvT
    intro g hg
    exact hle hg
  have hconj' : ∀ g ∈ T, u⁻¹ * g * u ∈ T := by
    have hu2 : u⁻¹ = u * u := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hu3)
    intro g hg
    have e : u⁻¹ * g * u = u * (u * g * u⁻¹) * u⁻¹ := by
      calc u⁻¹ * g * u = u * u * g * (u * u)⁻¹ := by rw [← hu2, inv_inv]
        _ = u * (u * g * u⁻¹) * u⁻¹ := by group
    rw [e]
    exact hconj _ (hconj g hg)
  have huT : u ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj g hg, fun hg => ?_⟩
    have e : g = u⁻¹ * (u * g * u⁻¹) * u := by group
    rw [e]
    exact hconj' _ hg
  refine ⟨T ⊔ Subgroup.zpowers u, IsPGroup.to_sup_of_normal_left' hTp
    (isPGroup_zpowers_of_pow_three hu3) (Subgroup.zpowers_le.2 huT), u,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers u), v, Subgroup.mem_sup_left hvT,
    fun h => ha1 ?_⟩
  have e : u * v * u⁻¹ = v := by rw [h, mul_inv_cancel_right]
  rw [huv] at e
  exact mul_right_cancel (e.trans (one_mul v).symm)

theorem exists_nonabelian_isPGroup_reeFixed :
    ∃ H : Subgroup (reeFixed ReeTag.F4 K 0), IsPGroup 3 H ∧
      ∃ u ∈ H, ∃ v ∈ H, u * v ≠ v * u := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  refine exists_nonabelian_isPGroup_of_rel (a := ⟨evalG K reeAWord, reeA_mem⟩)
    (v := ⟨evalG K reeVWord, reeV_mem⟩) (u := ⟨evalG K reeUWord, reeU_mem⟩)
    (Subtype.ext ?_) (Subtype.ext ?_) (Subtype.ext ?_) ?_ (Subtype.ext reeA_mul_reeU)
    (Subtype.ext reeA_mul_reeV) (Subtype.ext ?_)
  · rw [Subgroup.coe_pow]
    exact reeA_pow_three
  · rw [Subgroup.coe_pow]
    exact reeV_pow_three
  · rw [Subgroup.coe_pow]
    exact reeU_pow_three
  · exact fun h => reeA_ne_one (K := K) (congrArg Subtype.val h)
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
    exact reeU_conj_reeV

theorem card_reeFixed_F4_zero (hK : Nat.card K = 2) :
    Nat.card (reeFixed ReeTag.F4 K 0) = 35942400 := by
  rw [Nat.card_congr (ReeTag.reeFixedEquivReeGamma K 0).toEquiv,
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion 0 K
      (by rw [hK]; norm_num)).1]
  norm_num

theorem card_lt_of_le_reeFixed (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup ReeTag.F4.tag K)} (hEΓ : E ≤ reeFixed ReeTag.F4 K 0)
    (hE : IsPGroup 3 E) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E < 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  set Γ := reeFixed ReeTag.F4 K 0
  obtain ⟨H, hH, u, hu, v, hv, huv⟩ := exists_nonabelian_isPGroup_reeFixed (K := K)
  have hG : ¬ 3 ^ (3 + 1) ∣ Nat.card Γ := by
    rw [card_reeFixed_F4_zero hK]
    norm_num
  set E' : Subgroup Γ := E.subgroupOf Γ with hE'
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv
  have hE'p : IsPGroup 3 E' := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEΓ).symm
  rw [← hcard]
  refine card_lt_of_isPGroup_of_not_comm hG hH hu hv huv hE'p fun x hx y hy => ?_
  exact Subtype.ext (hEc _ hx _ hy)

end Rank

end TableBF4TwoInputs

end CFSG.StandardType
