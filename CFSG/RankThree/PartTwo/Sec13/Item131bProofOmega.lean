module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item136
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofDefs
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem commutator_mem_inf (hD : Sec13Data G A c L) {e x : G} (heL : e ∈ L)
    (heW : e ∈ Subgroup.normalizer (A : Set G)) (hx : x ∈ A) :
    x * e * x⁻¹ * e⁻¹ ∈ A ⊓ L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : e * x⁻¹ * e⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp heW _).mp (inv_mem hx)
    have h2 : x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) := by group
    rw [h2]
    exact mul_mem hx h1
  · have h1 : x * e * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hx) e).mp heL
    exact mul_mem h1 (inv_mem heL)

theorem zpowers_mem_orbitIn (hD : Sec13Data G A c L) (hAL : A ⊓ L ≤ Subgroup.zpowers c)
    {e a : G} (heL : e ∈ L) (he3 : e ^ 3 = 1) (hec : e ∉ Subgroup.zpowers c)
    (heW : e ∈ Subgroup.normalizer (A : Set G)) (hce : c * e = e * c)
    (ha : a ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers c) (hac : a ∉ Subgroup.zpowers c) :
    Subgroup.zpowers a ∈ orbitIn A (Subgroup.zpowers e) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hD.toPartTwoStanding
  have hc3 : orderOf c = 3 := hD.orderOf_eq
  have hex : ∃ x₀ ∈ A, x₀ * e * x₀⁻¹ * e⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have heA : e ∈ A := Sec19.mem_of_le_centralizer hst hD.partTwoS_eq hD.mem_partTwoE he3
      fun x hx => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := hall x hx
        have h' : x * e * x⁻¹ = e := by
          calc x * e * x⁻¹ = x * e * x⁻¹ * e⁻¹ * e := by group
            _ = e := by rw [h, one_mul]
        calc x * e = x * e * x⁻¹ * x := by group
          _ = e * x := by rw [h']
    exact hec (hAL ⟨heA, heL⟩)
  obtain ⟨x₀, hx₀A, ht1⟩ := hex
  set t := x₀ * e * x₀⁻¹ * e⁻¹ with ht
  have htc : t ∈ Subgroup.zpowers c := hAL (commutator_mem_inf hD heL heW hx₀A)
  have htA : t ∈ A := (commutator_mem_inf hD heL heW hx₀A).1
  have ht3 : t ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hc3 ▸ orderOf_dvd_of_mem_zpowers htc)
  have hct : Subgroup.zpowers c = Subgroup.zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htc) ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hc3, orderOf_eq_prime ht3 ht1]
  have hx₀t : x₀ * t = t * x₀ := hD.commute hx₀A htA
  have hpow : ∀ n : ℕ, x₀ ^ n * e * (x₀ ^ n)⁻¹ = t ^ n * e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htn : x₀ * t ^ n = t ^ n * x₀ := (Commute.pow_right hx₀t n).eq
      calc x₀ ^ (n + 1) * e * (x₀ ^ (n + 1))⁻¹ = x₀ * (x₀ ^ n * e * (x₀ ^ n)⁻¹) * x₀⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = x₀ * t ^ n * e * x₀⁻¹ := by rw [ih]; group
        _ = t ^ n * (x₀ * e * x₀⁻¹) := by rw [htn]; group
        _ = t ^ n * (t * e) := by rw [ht]; group
        _ = t ^ (n + 1) * e := by rw [pow_succ]; group
  have horbit : ∀ n : ℕ, Subgroup.zpowers (t ^ n * e) ∈ orbitIn A (Subgroup.zpowers e) := by
    intro n
    refine ⟨x₀ ^ n, pow_mem hx₀A n, ?_⟩
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t ^ n * e) = Subgroup.zpowers (MulAut.conj (x₀ ^ n) e)
    rw [MulAut.conj_apply, hpow n]
  have hpowers : ∀ z ∈ Subgroup.zpowers c, ∃ n : ℕ, t ^ n = z := by
    intro z hz
    rw [hct, ← mem_powers_iff_mem_zpowers] at hz
    exact (Submonoid.mem_powers_iff _ _).mp hz
  have heN : Subgroup.zpowers e ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm : Commute e (c ^ k) := Commute.zpow_right (hce.symm : Commute e c) k
    rw [hcomm.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c k
  have ha' : a ∈ ((Subgroup.zpowers e ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ heN] at ha'
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp ha'
  have hez : Commute e z := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_right (hce.symm : Commute e c) k
  have hz3 : z ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hc3 ▸ orderOf_dvd_of_mem_zpowers hz)
  have heo : orderOf e = 3 := by
    refine orderOf_eq_prime he3 fun h => hec ?_
    rw [h]
    exact Subgroup.one_mem _
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : e ^ k = e ^ (k % 3) := by
    rw [← zpow_mod_orderOf, heo]
    norm_num
  set r := k % 3 with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg k (by norm_num)
  have hr3 : r < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk]
  interval_cases r
  · exfalso
    apply hac
    rw [hk, zpow_zero, one_mul]
    exact hz
  · obtain ⟨n, hn⟩ := hpowers z hz
    rw [zpow_one, hez.eq, ← hn]
    exact horbit n
  ·
    obtain ⟨n, hn⟩ := hpowers _ (pow_mem hz 2)
    rw [zpow_ofNat]
    set w := e ^ 2 * z with hw
    have hcomm : Commute (e ^ 2) z := hez.pow_left 2
    have hw2 : w ^ 2 = z ^ 2 * e := by
      rw [hw, hcomm.mul_pow, ← pow_mul]
      have h4 : e ^ (2 * 2) = e := by
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, he3, one_mul]
      rw [h4]
      exact (hez.pow_right 2).eq
    have hw3 : w ^ 3 = 1 := by
      rw [hw, hcomm.mul_pow, ← pow_mul, hz3, mul_one]
      rw [show 2 * 3 = 3 * 2 by norm_num, pow_mul, he3, one_pow]
    have hzw : Subgroup.zpowers w = Subgroup.zpowers (w ^ 2) := by
      apply le_antisymm
      · rw [Subgroup.zpowers_le]
        have h4 : (w ^ 2) ^ 2 = w := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hw3, one_mul]
        have h := pow_mem (Subgroup.mem_zpowers (w ^ 2)) 2
        rwa [h4] at h
      · rw [Subgroup.zpowers_le]
        exact pow_mem (Subgroup.mem_zpowers w) 2
    rw [hzw, hw2, ← hn]
    exact horbit n

theorem clauses_of_heis
    (h128 : Sec12.Item128BarAt) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hHE : Step131bHeisE) (hHK : Step131bHeisK) (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L)) {E : Subgroup G}
    (hEle : E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G))
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEC : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
    (hEL : ¬ IsCyclic (E ⊓ L : Subgroup G)) :
    E ∈ partTwoF G ∧ (E ∉ partTwoT G →
      Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
      (∃ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K ∧
        Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
      ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c ∧
        omegaA E = orbitIn A (Subgroup.zpowers e) ∧
        ∃ I : Subgroup G, lA E e = {I} ∧
          Nonempty (I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
  have hst := hD.toPartTwoStanding
  have hS := hD.partTwoS_eq
  have hFE : partTwoF G = partTwoE G := (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hcL := mem_of_isHeisCentral hD hH
  have hZ3 := card_center_eq_three hty
  have hAL := inf_le_zpowers hD hH hcL hZ3
  have hEW : E ≤ Subgroup.normalizer (A : Set G) := hEle.trans inf_le_right
  obtain ⟨hcE, hC9, -, hsup⟩ := e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hAN := le_normalizer_of_heis hD hAL hEW hcE hsup
  have hstd := sec12StdBar_of_heis hD hcL hEe hE27 hcE hC9 hsup hAN
  have hEE : E ∈ partTwoE G := hHE G A c L hD hH hty E hEle hstd hAN
  have hEF : E ∈ partTwoF G := hFE ▸ hEE
  refine ⟨hEF, fun hET => ⟨hH, ?_⟩⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rcases h128 G E c L hstd hEE (type122_of hty) with hT | hpt
  · exact absurd hT hET
  have halt : ∀ a : G, Subgroup.zpowers a ∈ omegaA E →
      a ∈ L ∧ E ⊓ L = Subgroup.zpowers a ⊔ Subgroup.zpowers c ∧
        ∃ L₀ ∈ thetaComponentsAt 3 c, L₀ ≠ L ∧
          Sec4.IsTripleCover (L₀ ⧸ aschbacherSolvableCore 3 L₀) (alternatingGroup (Fin 6)) ∧
          c ∈ L₀ ∧ a ∈ Sec4.thetaQuotCentralizer L₀ := by
    intro a ha
    rcases (hpt a ha).1 with ⟨-, hA6⟩ | h
    · exact (not_isTripleCover_six hty hA6).elim
    · exact h
  have hnotc : ∀ a : G, Subgroup.zpowers a ∈ omegaA E → a ∉ Subgroup.zpowers c := by
    intro a ha hac
    obtain ⟨-, hELe, -⟩ := halt a ha
    rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr hac)] at hELe
    rw [hELe] at hEL
    exact hEL inferInstance
  obtain ⟨F, hF⟩ := omegaA_nonempty hst hS hEF hET
  obtain ⟨-, -, e, rfl, -⟩ := id hF
  obtain ⟨heL, hELe, L₀, hL₀, hne, hA6, hcL₀, -⟩ := halt e hF
  have heE : e ∈ E := hF.1 (Subgroup.mem_zpowers e)
  have he3 : e ^ 3 = 1 := hEe.2 e heE
  have hec := hnotc e hF
  refine ⟨⟨L₀, hL₀, hHK G A c L hD hH hty L₀ hL₀ hne hA6 hcL₀, hA6⟩, e, ⟨heE, heL⟩, hec,
    ?_, ?_⟩
  ·
    ext F'
    constructor
    · intro hF'
      obtain ⟨hF'E, -, a, rfl, -⟩ := id hF'
      have haE : a ∈ E := hF'E (Subgroup.mem_zpowers a)
      obtain ⟨haL, -, -⟩ := halt a hF'
      have ha : a ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers c := hELe ▸ ⟨haE, haL⟩
      exact zpowers_mem_orbitIn hD hAL heL he3 hec (hEW heE) (hEcomm c hcE e heE) ha
        (hnotc a hF')
    · rintro ⟨x, hx, rfl⟩
      exact (map_conj_mem_omegaA_iff (hAN hx)).mpr hF
  ·
    obtain ⟨I, hI⟩ := Sec12.exists_mem_lA422 h422 h45 hst hEF hE27 hF
    obtain ⟨φ⟩ := (hpt e hF).2 I hI
    have hEe' : E ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx e heE)
    have hIlA : I ∈ lA E e := Sec12.mem_lA_of_mem_lA422 hEe' hI
    have hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
    have hJp : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
      (isPerfect_center_of_isSimpleGroup hJs (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
    have hθ := theta_eq_pCore_two hJs hJp φ
    have hJθ : Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans φ⟩
    have hDE : Sec13Data G E e I :=
      { hst with
        partTwoS_eq := hS
        mem_partTwoF := hEF
        not_mem_partTwoT := hET
        zpowers_mem_omegaA := hF
        mem_lA := hIlA }
    exact ⟨I, Sec14.lA_eq_singleton_of_j2_point hDE hJθ, ⟨φ⟩⟩

end CFSG.RankThree.PartTwo.Sec13.Item131bProof
