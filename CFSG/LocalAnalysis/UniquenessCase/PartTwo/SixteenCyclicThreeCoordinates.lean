module

public import CFSG.LinearAlgebra.OrderThreeSemilinearAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycBasic
public import CFSG.GroupTheory.PrimeOrderSubgroups
public import CFSG.Quasithin.Background.Asc81cPfTrans2
public import CFSG.Quasithin.Background.GoldschmidtD35CoreInv
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped commutatorElement Pointwise

theorem odd_centralizer_and_index_two_of_cyclic_three_mParam
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6)
    {A Lb : Subgroup (MulAut W)}
    (hLcard : Nat.card Lb = 3)
    (hLn : ∀ g ∈ A, Lb.map (MulAut.conj g).toMonoidHom = Lb)
    (hWL : commSub ⊤ Lb = ⊤)
    (hm : E3.mParam A = 3) :
    let C : Subgroup A :=
      (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A
    C.Normal ∧ Odd (Nat.card C) ∧ C.index = 2 := by
  classical
  haveI hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP OmegaField 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) OmegaField).injective 2
  haveI hfinField : Module.Finite (ZMod 2) OmegaField :=
    (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  haveI hfiniteField : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  have hcardField : Nat.card OmegaField = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
    norm_num
  have hcardW : Nat.card W = 64 := by rw [hcard]; norm_num
  obtain ⟨z, hzmem, hzord, hLbz⟩ :=
    CFSG.GroupTheory.exists_generator_of_card_prime (p := 3) (by norm_num) hLcard
  have hoddz : Odd (orderOf z) := by rw [hzord]; norm_num
  have hfpf : ∀ w : W, z w = w → w = 1 :=
    s168e3_cyc_fpf hW hLbz hoddz hWL
  obtain ⟨e, he⟩ :=
    exists_omega_coordinates_of_order_three_rank_six hW hcard z hzord hfpf
  have hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W)) := by
    intro g hg
    rw [← hLbz]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (hLn g hg)
  obtain ⟨ρ, hρinj, hact, hker⟩ :=
    exists_coordinate_semilinear_action_of_normalizes_three hW z hzord e he A hAN
  let C : Subgroup A :=
    (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A
  have hzcent : Subgroup.centralizer ({z} : Set (MulAut W)) =
      Subgroup.centralizer (Lb : Set (MulAut W)) := by
    rw [hLbz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hkerC : (SemidirectProduct.rightHom.comp ρ).ker = C := by
    rw [hker, hzcent]
  have hCnormal : C.Normal :=
    hkerC ▸ (SemidirectProduct.rightHom.comp ρ).normal_ker
  have hno_involution : ∀ t : A, t ∈ C → orderOf (t : MulAut W) = 2 → False := by
    intro t htC ht2
    have htker : t ∈ (SemidirectProduct.rightHom.comp ρ).ker := by
      rw [hkerC]
      exact htC
    have hright : (ρ t).right = 1 := by
      have := MonoidHom.mem_ker.mp htker
      simpa [MonoidHom.comp_apply] using this
    let M : GL (Fin 3) OmegaField := (ρ t).left
    have hpair : ρ t = SemidirectProduct.inl M := by
      rw [← SemidirectProduct.inl_left_mul_inr_right (ρ t), hright, map_one, mul_one]
    let s : (Fin 3 → OmegaField) ≃ₗ[OmegaField] (Fin 3 → OmegaField) :=
      matrixLinearEquiv M
    have hmap : (s : (Fin 3 → OmegaField) → (Fin 3 → OmegaField)) =
        (coordinateSemilinearMap (ρ t) :
          (Fin 3 → OmegaField) → (Fin 3 → OmegaField)) := by
      ext x
      rw [hpair, coordinateSemilinearMap_inl]
    have htA2 : orderOf t = 2 := by
      rw [← Subgroup.orderOf_coe t]
      exact ht2
    have htt : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [htA2, pow_two] at h
    have hρtt : ρ t * ρ t = 1 := by
      rw [← map_mul, htt, map_one]
    have hss : ∀ x, s (s x) = x := by
      intro x
      rw [hmap]
      rw [← coordinateSemilinearMap_mul, hρtt, coordinateSemilinearMap_one]
    have hs1 : s ≠ 1 := by
      intro hs
      have ht1 : (t : MulAut W) = 1 := by
        ext w
        have h := hact t w
        rw [← coordinateAddEquiv_ofMul e w, ← hmap] at h
        rw [hs] at h
        have h' : Multiplicative.toAdd (e ((t : MulAut W) w)) =
            Multiplicative.toAdd (e w) := by
          simpa using h
        exact e.injective (Multiplicative.toAdd.injective h')
      rw [ht1, orderOf_one] at ht2
      omega
    have hfin3 : Module.finrank OmegaField (Fin 3 → OmegaField) = 3 := by
      rw [Module.finrank_fin_fun]
    haveI hfinFun : FiniteDimensional OmegaField (Fin 3 → OmegaField) :=
      Module.Finite.of_finite
    have hfixcard : Nat.card {x : Fin 3 → OmegaField // s x = x} = 16 := by
      have h := CFSG.Quasithin.D35Core.card_fix_involution
        (K := OmegaField) (V := Fin 3 → OmegaField) (g := s) hfin3 hss hs1
      rw [h, hcardField]
      norm_num
    let eW : W ≃ (Fin 3 → OmegaField) :=
      (Additive.ofMul : W ≃ Additive W).trans (coordinateAddEquiv e).toEquiv
    have heW : ∀ w : W, eW w = coordinateAddEquiv e (Additive.ofMul w) := fun _ => rfl
    let eSub : {w : W // (t : MulAut W) w = w} ≃
        {x : Fin 3 → OmegaField // s x = x} :=
      eW.subtypeEquiv (fun w => by
        constructor
        · intro hw
          have h := hact t w
          rw [hw, ← hmap] at h
          simpa [heW, coordinateAddEquiv_ofMul] using h.symm
        · intro hx
          have h := hact t w
          have hx' : s (Multiplicative.toAdd (e w)) =
              Multiplicative.toAdd (e w) := by
            rw [← coordinateAddEquiv_ofMul e w, ← heW w]
            exact hx
          rw [← hmap, hx'] at h
          exact e.injective (Multiplicative.toAdd.injective h))
    have hfix16 : Nat.card (fixV (Subgroup.zpowers (t : MulAut W))) = 16 := by
      have h1 : Nat.card (fixV (Subgroup.zpowers (t : MulAut W))) =
          Nat.card {w : W // (t : MulAut W) w = w} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun w =>
          CFSG.Quasithin.mem_fixV_zpowers_iff_apply))
      rw [h1, Nat.card_congr eSub, hfixcard]
    have hindex : (fixV (Subgroup.zpowers (t : MulAut W))).index = 4 := by
      have h := Subgroup.card_mul_index (fixV (Subgroup.zpowers (t : MulAut W)))
      rw [hfix16, hcardW] at h
      omega
    have hrkIdx : rkIdx (fixV (Subgroup.zpowers (t : MulAut W))) = 2 := by
      rw [rkIdx, hindex]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have hle := CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two
      (G := A) (t := (t : MulAut W)) t.2 ht2
    rw [hrkIdx] at hle
    omega
  have hCodd : Odd (Nat.card C) := by
    by_contra hnotodd
    have heven : Even (Nat.card C) := Nat.not_odd_iff_even.mp hnotodd
    have h2dvd : 2 ∣ Nat.card C := even_iff_two_dvd.mp heven
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2dvd
    have ht2 : orderOf ((x : A) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe (x : A), Subgroup.orderOf_coe x]
      exact hx2
    exact hno_involution (x : A) x.2 ht2
  have hAeven : Even (Nat.card A) := by
    by_contra hnoteven
    have hmA : E3.mParam A = rk W := by
      simp [E3.mParam, hnoteven]
    have hrkW : rk W = 6 := by
      rw [rk, hcard]
      exact padicValNat.prime_pow 6
    have h36 : (3 : ℕ) = 6 := by
      calc (3 : ℕ) = E3.mParam A := hm.symm
        _ = rk W := hmA
        _ = 6 := hrkW
    omega
  have hdvd : Nat.card A ∣ 2 * Nat.card C := by
    have h := s168e3_cyc_card_dvd (W := W) (A := A) (L := Lb) (p := 3)
      (by norm_num) hLcard hLn
    have hCcard : Nat.card (A ⊓ (Subgroup.centralizer (Lb : Set (MulAut W))) :
          Subgroup (MulAut W)) = Nat.card C := by
      rw [show C = (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A from rfl]
      rw [← Subgroup.inf_subgroupOf_right]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]
    rw [show (3 - 1 : ℕ) = 2 by norm_num, hCcard] at h
    exact h
  have hidx_dvd : C.index ∣ 2 := by
    have hcardA : Nat.card A = Nat.card C * C.index := (Subgroup.card_mul_index C).symm
    have h := hdvd
    rw [hcardA] at h
    rw [mul_comm 2 (Nat.card C)] at h
    exact (Nat.mul_dvd_mul_iff_left (Nat.card_pos (α := C))).mp h
  have hidx_ne_one : C.index ≠ 1 := by
    intro hindex
    have htop : C = ⊤ := Subgroup.index_eq_one.mp hindex
    have hcardEq : Nat.card C = Nat.card A := by
      rw [htop]
      exact Subgroup.card_top
    have hAodd : Odd (Nat.card A) := by rwa [← hcardEq]
    exact (Nat.not_odd_iff_even.mpr hAeven) hAodd
  have hidx_two : C.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx_dvd with h1 | h2
    · exact absurd h1 hidx_ne_one
    · exact h2
  exact ⟨hCnormal, hCodd, hidx_two⟩

private theorem exists_cyclic_three_coordinates
    {G : Type} [Group G] [Finite G]
    (D : Data G)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    ∃ (z : MulAut (Vtil V₀ V hV))
      (e : Vtil V₀ V hV ≃* Multiplicative (Fin 3 → OmegaField)),
      z ∈ lBar V₀ V hV L ∧
      orderOf z = 3 ∧
      lBar V₀ V hV L = Subgroup.zpowers z ∧
      (∀ w : Vtil V₀ V hV,
        Multiplicative.toAdd (e (z w)) =
          CFSG.LinearAlgebra.omega • Multiplicative.toAdd (e w)) ∧
      Mbar D.M V₀ V hV ≤
        Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut (Vtil V₀ V hV))) := by
  classical
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have htop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hc hs
  have hrk' : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← htop]
    exact hrk
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top hW, hrk']
  obtain ⟨z, hzmem, hzord, hLbz⟩ :=
    CFSG.GroupTheory.exists_generator_of_card_prime (p := 3) (by norm_num) hcyc.2
  have hoddz : Odd (orderOf z) := by rw [hzord]; norm_num
  have hWL : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    simpa [wTil, lBar] using htop
  have hfpf : ∀ w : Vtil V₀ V hV, z w = w → w = 1 :=
    s168e3_cyc_fpf hW hLbz hoddz hWL
  obtain ⟨e, he⟩ :=
    exists_omega_coordinates_of_order_three_rank_six hW hcard z hzord hfpf
  have hAN : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    rw [← hLbz]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (lBar_conj_eq_of_s15_eq_one hs hg)
  exact ⟨z, e, hzmem, hzord, hLbz, he, hAN⟩

theorem exists_cyclic_three_rank_six_s1_coordinate_action
    {G : Type} [Group G] [Finite G]
    (D : Data G)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    ∃ (z : MulAut (Vtil V₀ V hV))
      (e : Vtil V₀ V hV ≃* Multiplicative (Fin 3 → OmegaField))
      (ρ : Mbar D.M V₀ V hV →* coordinateSemilinearGroup 3 OmegaField),
      z ∈ lBar V₀ V hV L ∧
      orderOf z = 3 ∧
      lBar V₀ V hV L = Subgroup.zpowers z ∧
      (∀ w : Vtil V₀ V hV,
        Multiplicative.toAdd (e (z w)) =
          CFSG.LinearAlgebra.omega • Multiplicative.toAdd (e w)) ∧
      Function.Injective ρ ∧
      (∀ (g : Mbar D.M V₀ V hV) (w : Vtil V₀ V hV),
        Multiplicative.toAdd (e ((g : MulAut (Vtil V₀ V hV)) w)) =
          coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w))) ∧
      (SemidirectProduct.rightHom.comp ρ).ker =
        (Subgroup.centralizer
          (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
            (Mbar D.M V₀ V hV) := by
  classical
  obtain ⟨z, e, hzmem, hzord, hLbz, he, hAN⟩ :=
    exists_cyclic_three_coordinates D hc hs hcyc hrk
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  obtain ⟨ρ, hρinj, hact, hker⟩ :=
    exists_coordinate_semilinear_action_of_normalizes_three
      hW z hzord e he (Mbar D.M V₀ V hV) hAN
  have hker' : (SemidirectProduct.rightHom.comp ρ).ker =
      (Subgroup.centralizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
          (Mbar D.M V₀ V hV) := by
    rw [hker]
    congr 1
    rw [hLbz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact ⟨z, e, ρ, hzmem, hzord, hLbz, he, hρinj, hact, hker'⟩

theorem cyclic_three_rank_six_s1_centralizer
    {G : Type} [Group G] [Finite G]
    (D : Data G)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Conc4_136 D V₀ V hV L)
    (hm : mBar D.M V₀ V hV = 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    let A := Mbar D.M V₀ V hV
    let C : Subgroup A :=
      (Subgroup.centralizer
        (lBar V₀ V hV L :
          Set (MulAut (Vtil V₀ V hV)))).subgroupOf A
    C.Normal ∧ Odd (Nat.card C) ∧ C.index = 2 := by
  classical
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have htop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hc hs
  have hrk' : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← htop]
    exact hrk
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top hW, hrk']
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  have hWL : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    simpa [wTil, lBar] using htop
  have hm' : E3.mParam (Mbar D.M V₀ V hV) = 3 := by
    simpa [mBar] using hm
  exact odd_centralizer_and_index_two_of_cyclic_three_mParam
    hW hcard hcyc.2 hLn hWL hm'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
