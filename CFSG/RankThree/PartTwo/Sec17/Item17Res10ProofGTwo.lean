module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res5ProofGTwo
public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofGTwoSL
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate2202
public import Certificates.Certificate8166
public import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

@[expose] def KS176GTwoChevThree : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K →
    ∀ Z : Subgroup ↥(adjointGroup .G2 K), Nat.card Z = 3 →
    (∀ g : ↥(adjointGroup .G2 K), Z.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Z : Set ↥(adjointGroup .G2 K)) →
      Z.map (MulAut.conj g).toMonoidHom = Z) →
    Proof176Steps.HasCommOfZ Z

namespace Proof17Res10

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem weaklyClosed_map (φ : X ≃* Y) {Z : Subgroup X}
    (hwc : ∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    ∀ g : Y, (Z.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Z.map φ.toMonoidHom : Subgroup Y) : Set Y) →
      (Z.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom = Z.map φ.toMonoidHom := by
  intro g hg
  have hcomp : (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom =
      φ.toMonoidHom.comp (MulAut.conj (φ.symm g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  have hmap : (Z.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (Z.map (MulAut.conj (φ.symm g)).toMonoidHom).map φ.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hmap] at hg ⊢
  rw [← Subgroup.map_equiv_normalizer_eq] at hg
  rw [hwc (φ.symm g) ((Subgroup.map_le_map_iff_of_injective φ.injective).mp hg)]

theorem hasCommOfZ_of_map (φ : X ≃* Y) {Z : Subgroup X}
    (h : Proof176Steps.HasCommOfZ (Z.map φ.toMonoidHom)) : Proof176Steps.HasCommOfZ Z := by
  obtain ⟨x, y, hx3, hy3, hxC, hyC, hxyZ, hxy1, hp⟩ := h
  refine ⟨φ.symm x, φ.symm y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hx3, map_one]
  · rw [← map_pow, hy3, map_one]
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp hxC (φ z) ⟨z, hz, rfl⟩
    apply φ.injective
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp hyC (φ z) ⟨z, hz, rfl⟩
    apply φ.injective
    simpa using this
  · obtain ⟨z, hz, hzxy⟩ := hxyZ
    rw [← map_commutatorElement, ← hzxy]
    simpa using hz
  · rw [← map_commutatorElement]
    intro h1
    apply hxy1
    simpa using congrArg φ h1
  · have e : Subgroup.closure ({φ.symm x, φ.symm y} : Set X) =
        (Subgroup.closure ({x, y} : Set Y)).map φ.symm.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [e]
    exact hp.map _

end Transport

theorem factorization_three_g2_sq {q : ℕ} (h3 : 3 ∣ q + 1) (hq : 2 ≤ q) :
    ((q ^ 2) ^ 6 * ((q ^ 2) ^ 6 - 1) * ((q ^ 2) ^ 2 - 1)).factorization 3 =
      (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 3 := by
  have hq3 : q % 3 = 2 := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ (q ^ 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2' : 2 ≤ q ^ 2 := by nlinarith
  have h6' : 2 ≤ q ^ 6 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  have hdecomp : (q ^ 2) ^ 6 * ((q ^ 2) ^ 6 - 1) * ((q ^ 2) ^ 2 - 1) =
      (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) * (q ^ 6 * (q ^ 6 + 1) * (q ^ 2 + 1)) := by
    zify [h2, h6, h12, h4]
    ring
  have hnd : ¬ 3 ∣ q ^ 6 * (q ^ 6 + 1) * (q ^ 2 + 1) := by
    have h6m : q ^ 6 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    have h2m : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod (q ^ 6), Nat.add_mod (q ^ 6),
      Nat.add_mod (q ^ 2), h6m, h2m]
    norm_num
  have hA : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≠ 0 := by
    have : 0 < q ^ 6 - 1 := by omega
    have : 0 < q ^ 2 - 1 := by omega
    positivity
  have hB : q ^ 6 * (q ^ 6 + 1) * (q ^ 2 + 1) ≠ 0 := by positivity
  rw [hdecomp, Nat.factorization_mul hA hB, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

section Certified

theorem exists_split_ext (K : Type) [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K')
      (f : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K')),
      Function.Injective f ∧ 3 ∣ Nat.card K' - 1 ∧
        (Nat.card ↥(adjointGroup .G2 K')).factorization 3 =
          (Nat.card ↥(adjointGroup .G2 K)).factorization 3 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases h1 : 3 ∣ Nat.card K - 1
  · exact ⟨K, inferInstance, inferInstance, MonoidHom.id _, fun _ _ h => h, h1, rfl⟩
  · have h2 : 3 ∣ Nat.card K + 1 := by omega
    obtain ⟨K₂, _, _, _, -, hdeg, -⟩ := Sec11.KS11Lie4Proof.exists_quadratic_ext' K
    have hK₂ : Nat.card K₂ = Nat.card K ^ 2 := Sec11.KS11Lie4Proof.natCard_quadratic hdeg
    refine ⟨K₂, inferInstance, inferInstance, Sec11.KS11Lie4Proof.bcG2 K K₂,
      Sec11.KS11Lie4Proof.bcG2_injective, ?_, ?_⟩
    · rw [hK₂]
      exact Sec11.KS11Lie4Proof.three_dvd_sq_sub_one h2
    · obtain ⟨-, hC, -⟩ := exact_G2_finite_order K rfl
      obtain ⟨-, hC₂, -⟩ := exact_G2_finite_order K₂ hK₂
      rw [hC, hC₂, factorization_three_g2_sq h2 hq]

open scoped MatrixGroups in
theorem exists_comm_sylow_g2_split
    {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (S : Sylow 3 ↥(adjointGroup .G2 K)) :
    ∃ x ∈ (S : Subgroup ↥(adjointGroup .G2 K)), ∃ y ∈ (S : Subgroup ↥(adjointGroup .G2 K)),
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ ⁅x, y⁆ ^ 3 = 1 ∧
        ∀ z ∈ (S : Subgroup ↥(adjointGroup .G2 K)),
          (∀ u ∈ (S : Subgroup ↥(adjointGroup .G2 K)), u * z = z * u) →
            z ∈ Subgroup.zpowers ⁅x, y⁆ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨ω, hω3, hω1⟩ : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    have hcard : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hcard
    refine ⟨(u : K), ?_, ?_⟩
    · have h := pow_orderOf_eq_one u
      rw [hu] at h
      have := congrArg Units.val h
      simpa using this
    · intro h
      have hu1 : u = 1 := Units.ext h
      rw [hu1, orderOf_one] at hu
      omega
  obtain ⟨ι, hι, -⟩ := GH74.GLS.Stage2.Bender.Thm1.exists_a2Hom_injective (K := K)
  set t : Matrix.SpecialLinearGroup (Fin 3) K := tSL hω3 with ht
  set w : Matrix.SpecialLinearGroup (Fin 3) K := LieType.SeitzGeneration.shiftSL with hw
  set s : Matrix.SpecialLinearGroup (Fin 3) K := sSL hω3 with hs
  obtain ⟨P₀, hEP⟩ := (isPGroup_closure_tSL_shiftSL hω3).exists_le_sylow
  have htP : t ∈ (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :=
    hEP (Subgroup.subset_closure (Set.mem_insert _ _))
  have hwP : w ∈ (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :=
    hEP (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨-, hC, -⟩ := exact_G2_finite_order K rfl
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
      show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  let Q₀ : Sylow 3 ↥(adjointGroup .G2 K) :=
    Sylow.ofCard ((P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map ι) (by
      rw [Subgroup.card_map_of_injective hι, Sylow.card_eq_multiplicity P₀, hC, hSL,
        GH74.GLS.Stage2.Bender.Thm1.factorization_three_g2_eq_sl3 h3 hq])
  have hQ₀ : (Q₀ : Subgroup ↥(adjointGroup .G2 K)) =
      (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map ι := Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(adjointGroup .G2 K) Q₀ S
  have hS : (S : Subgroup ↥(adjointGroup .G2 K)) =
      (Q₀ : Subgroup ↥(adjointGroup .G2 K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  set c := (MulAut.conj g).toMonoidHom.comp ι with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective.comp hι
  have hmemS : ∀ m ∈ (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)),
      c m ∈ (S : Subgroup ↥(adjointGroup .G2 K)) := fun m hm => by
    rw [hS, hQ₀]
    exact ⟨ι m, ⟨m, hm, rfl⟩, rfl⟩
  have hcomm : ⁅c t, c w⁆ = c s := by
    rw [← map_commutatorElement, ht, hw, hs, commutator_tSL_shiftSL]
  refine ⟨c t, hmemS t htP, c w, hmemS w hwP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ht, tSL_pow_three, map_one]
  · rw [← map_pow, hw, shiftSL_pow_three, map_one]
  · rw [hcomm]
    intro h1
    exact sSL_ne_one hω3 hω1 (hcinj (h1.trans (map_one c).symm))
  · rw [hcomm, ← map_pow, hs, sSL_pow_three, map_one]
  · intro z hz hzc
    rw [hS, hQ₀] at hz
    obtain ⟨_, ⟨m, hm, rfl⟩, rfl⟩ := hz
    have hcm : ∀ p ∈ (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)), p * m = m * p := by
      intro p hp
      apply hcinj
      rw [map_mul, map_mul]
      exact hzc (c p) (hmemS p hp)
    have hmz := mem_zpowers_sSL_of_commute hω3 hω1 (hcm t htP).symm (hcm w hwP).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmz
    rw [hcomm]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow, hs, hk]
    rfl

theorem hasCommOfZ_g2 {K : Type}
    [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    {Z : Subgroup ↥(adjointGroup .G2 K)} (hZ3 : Nat.card Z = 3)
    (hwc : ∀ g : ↥(adjointGroup .G2 K), Z.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Z : Set ↥(adjointGroup .G2 K)) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    Proof176Steps.HasCommOfZ Z := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hZS, hcen⟩ := exists_sylow_of_weaklyClosed hZ3 hwc
  obtain ⟨K', _, _, f, hf, h3', hord⟩ := exists_split_ext K hK3
  let S' : Sylow 3 ↥(adjointGroup .G2 K') :=
    Sylow.ofCard ((S : Subgroup ↥(adjointGroup .G2 K)).map f) (by
      rw [Subgroup.card_map_of_injective hf, Sylow.card_eq_multiplicity S, hord])
  have hS' : (S' : Subgroup ↥(adjointGroup .G2 K')) =
      (S : Subgroup ↥(adjointGroup .G2 K)).map f := Sylow.coe_ofCard _ _
  obtain ⟨x', hx', y', hy', hx3, hy3, hne, hc3, hcenter⟩ := exists_comm_sylow_g2_split h3' S'
  rw [hS'] at hx' hy'
  obtain ⟨x, hxS, rfl⟩ := hx'
  obtain ⟨y, hyS, rfl⟩ := hy'
  rw [← map_commutatorElement] at hne hc3 hcenter
  obtain ⟨z₀, hz₀, hz₀1⟩ := Proof176Steps.exists_ne_one_of_card_three hZ3
  have hZz : Z = Subgroup.zpowers z₀ := Proof176Steps.eq_zpowers_of_card_three hZ3 hz₀ hz₀1
  have hfz : f z₀ ∈ Subgroup.zpowers (f ⁅x, y⁆) := by
    refine hcenter (f z₀) (by rw [hS']; exact ⟨z₀, hZS hz₀, rfl⟩) fun u hu => ?_
    rw [hS'] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [← map_mul, ← map_mul, hcen z₀ hz₀ v hv]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfz
  have hz₀k : ⁅x, y⁆ ^ k = z₀ := hf (by rw [map_zpow, hk])
  have hxy1 : ⁅x, y⁆ ≠ 1 := fun h1 => hne (by rw [h1, map_one])
  have hxy3 : ⁅x, y⁆ ^ 3 = 1 := hf (by rw [map_pow, hc3, map_one])
  have hord3 : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime hxy3 hxy1
  have hZeq : Z = Subgroup.zpowers ⁅x, y⁆ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [hZz, Subgroup.zpowers_le]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hz₀k⟩
    · rw [Nat.card_zpowers, hord3, hZ3]
  refine ⟨x, y, hf (by rw [map_pow, hx3, map_one]), hf (by rw [map_pow, hy3, map_one]), ?_, ?_,
    ?_, hxy1, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hcen z hz x hxS).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hcen z hz y hyS).symm
  · rw [hZeq]
    exact Subgroup.mem_zpowers _
  · refine (S.isPGroup').to_le ?_
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | ha
    · exact hxS
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hyS

end Certified

end Proof17Res10

theorem ks176GTwoChev_of_three
    (h3 : KS176GTwoChevThree) : KS176GTwoChev := by
  intro X _ _ hX Z hZ3 hwc
  obtain ⟨p, f, -, K, _, _, -, ⟨e⟩⟩ := hX
  let iso : Blueprint.AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  let φ : X ≃* ↥(adjointGroup .G2 K) := e.trans iso
  have hZ3' : Nat.card (Z.map φ.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, hZ3]
  have hwc' := Proof17Res10.weaklyClosed_map φ hwc
  refine Proof17Res10.hasCommOfZ_of_map φ ?_
  by_cases hK3 : 3 ∣ Nat.card K
  · exact h3 K hK3 _ hZ3' hwc'
  · exact Proof17Res10.hasCommOfZ_g2 hK3 hZ3' hwc'

end CFSG.RankThree.PartTwo.Sec17
