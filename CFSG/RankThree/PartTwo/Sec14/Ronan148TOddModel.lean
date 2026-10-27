module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSinger
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.SubgroupLists.RationalFiveExclusions
import CFSG.RankThree.SubgroupLists.QuasisimpleRankTwo
import CFSG.RankThree.SubgroupLists.CommutatorScalarBound
import CFSG.RankThree.SubgroupLists.KleinFourCentralizer
import CFSG.RankThree.SubgroupLists.SL3Involutions
import CFSG.RankThree.SubgroupLists.UnitaryThreeFour
import CFSG.RankThree.SubgroupLists.CentralThreeLift
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.CharacterTheory.TwoRankLowerBound.RankTransport
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
public import Certificates.Certificate8169
import CFSG.RankThree.SubgroupLists.ExtraspecialNormal

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedScalars StatedProj StatedSU)
open CFSG.Assembly.RankThreeEven (projImage)

section Model

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mem_center_slPi_iff (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (z : slPi π 3 (p ^ f) K) :
    z ∈ Subgroup.center (slPi π 3 (p ^ f) K) ↔
      (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  constructor
  · intro hz
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx => ?_
    have := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm
  · intro hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_statedScalars hz (g : GL (Fin 3) K))

theorem center_slPi_eq_ker (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Subgroup.center (slPi π 3 (p ^ f) K) = (projOf (slPi π 3 (p ^ f) K)).ker := by
  ext z
  rw [mem_center_slPi_iff hK hq, mem_ker_projOf]

theorem det_eq_one_of_mem_slPi (hK : PiField π p f K) {x : GL (Fin 3) K}
    (hx : x ∈ slPi π 3 (p ^ f) K) : (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  exact ((mem_slPi_iff hπ).mp hx).2

theorem pow_three_eq_one_of_mem_center_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {z : slPi π 3 (p ^ f) K} (hz : z ∈ Subgroup.center (slPi π 3 (p ^ f) K)) : z ^ 3 = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨ζ, hζ⟩ := (mem_center_slPi_iff hK hq z).mp hz
  have hζL : GeneralLinearGroup.scalar (Fin 3) ζ ∈ slPi π 3 (p ^ f) K := by
    rw [hζ]
    exact z.2
  have h3 := pow_three_eq_one_of_scalar_mem_slPi hπ hζL
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hζ, ← map_pow, h3, map_one, Subgroup.coe_one]

theorem one_lt_card_center_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    1 < Nat.card (Subgroup.center (slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set t : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) with ht
  have htL : t ∈ slPi π 3 (p ^ f) K := scalar_mem_slPi_of_cube hK hq (by rw [Units.val_mk0]; exact hτ)
  have htZ : (⟨t, htL⟩ : slPi π 3 (p ^ f) K) ∈ Subgroup.center (slPi π 3 (p ^ f) K) :=
    (mem_center_slPi_iff hK hq _).mpr ⟨_, rfl⟩
  have ht1 : (⟨t, htL⟩ : slPi π 3 (p ^ f) K) ≠ 1 := by
    intro h
    apply hτ1
    have h1 := congrArg (fun s : slPi π 3 (p ^ f) K =>
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simpa [ht, GeneralLinearGroup.coe_scalar] using h1
  have hne : Subgroup.center (slPi π 3 (p ^ f) K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at htZ
    exact ht1 htZ
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne

theorem charP_of_piField (hK : PiField π p f K) : CharP K p := by
  have := hK.finite
  refine CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (n := cond π f (f * 2))
    hK.prime ?_
  rw [hK.card]
  cases π
  · change (p ^ f) ^ 2 = p ^ (f * 2)
    rw [pow_mul]
  · rfl

theorem odd_card_of_piField (hK : PiField π p f K) (hp2 : p ≠ 2) : Odd (Nat.card K) := by
  have hodd : Odd p := hK.prime.odd_of_ne_two hp2
  rw [hK.card]
  cases π
  · exact (hodd.pow).pow
  · exact hodd.pow

end Model

theorem exists_slPi_quotient {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) :
    ∃ (π : Bool) (F : Type) (_ : Field F), PiField π p e F ∧ ModThree π (p ^ e) ∧
      Nonempty (X ≃* ↥(slPi π 3 (p ^ e) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ e) F)) := by
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  refine ⟨π, F, inferInstance, hF, hq, ⟨φ.trans ?_⟩⟩
  exact (QuotientGroup.quotientKerEquivOfSurjective _ (projOf_surjective _)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq_ker hF hq).symm)

theorem oddFive : OddFive := by
  intro X _ _ p e _ he hiso x g hx5 hx1 hg
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := exists_slPi_quotient he hiso
  have hp : p.Prime := Fact.out
  have := charP_of_piField hF
  have h5 : (5 : F) = 0 := SubgroupLists.five_eq_zero_of_rational_five
    (H := slPi π 3 (p ^ e) F) (fun y hy => det_eq_one_of_mem_slPi hF hy)
    (fun z hz => pow_three_eq_one_of_mem_center_slPi hF hq hz) (s := φ x) (g := φ g)
    (by rw [← map_pow, hx5, map_one]) (fun h => hx1 (φ.injective (by rw [h, map_one])))
    (by rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow])
  have h5' : ((5 : ℕ) : F) = 0 := by exact_mod_cast h5
  have hdvd : p ∣ 5 := (CharP.cast_eq_zero_iff F p 5).mp h5'
  exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd

theorem oddTwoRank : OddTwoRank := by
  intro X _ _ p e _ hp2 he hiso K
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := exists_slPi_quotient he hiso
  have := hF.finite
  set H := slPi π 3 (p ^ e) F with hH
  have hN : ¬ 2 ∣ Nat.card (Subgroup.center H) := by
    intro h2
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hg3 : g ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_three_eq_one_of_mem_center_slPi hF hq g.2)
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    omega
  have h1 : CFSG.Assembly.twoRank K ≤ CFSG.Assembly.twoRank (H ⧸ Subgroup.center H) :=
    CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective
      (φ.toMonoidHom.comp K.subtype) (φ.injective.comp K.subtype_injective)
  have h2 : CFSG.Assembly.twoRank (H ⧸ Subgroup.center H) = CFSG.Assembly.twoRank H := by
    unfold CFSG.Assembly.twoRank
    exact CFSG.GroupTheory.PRankCoprimeQuotient.assembly_pRank_quotient_eq_of_not_dvd
      Nat.prime_two _ hN
  rw [h2] at h1
  exact h1.trans (SubgroupLists.twoRank_le_two_of_det_eq_one (odd_card_of_piField hF hp2)
    fun y hy => det_eq_one_of_mem_slPi hF hy)

theorem card_comap_mk' {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (Q : Subgroup (G ⧸ N)) :
    Nat.card (Q.comap (QuotientGroup.mk' N)) = Nat.card Q * Nat.card N := by
  have h1 := Subgroup.card_mul_index (Q.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index Q
  have h3 : (Q.comap (QuotientGroup.mk' N)).index = Q.index :=
    Subgroup.index_comap_of_surjective Q (QuotientGroup.mk'_surjective N)
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Q.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rw [h3] at h1
  have : Nat.card (Q.comap (QuotientGroup.mk' N)) * Q.index = Nat.card Q * Nat.card N * Q.index := by
    rw [h1, h4, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem oddThreeRank : OddThreeRank := by
  intro X _ _ p e _ he hiso P hP
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := exists_slPi_quotient he hiso
  have := hF.finite
  have := charP_of_piField hF
  have hp : p.Prime := Fact.out
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : (3 ^ e) % 3 = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      rw [pow_succ, Nat.mul_mod_left]
    cases π
    · change (3 ^ e) % 3 = 2 at hq
      omega
    · change (3 ^ e) % 3 = 1 at hq
      omega
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff F p 3).mp h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)
  set H := slPi π 3 (p ^ e) F with hH
  set Q : Subgroup (H ⧸ Subgroup.center H) := P.map φ.toMonoidHom with hQ
  set M : Subgroup H := Q.comap (QuotientGroup.mk' (Subgroup.center H)) with hM
  set R : Subgroup (GL (Fin 3) F) := M.map H.subtype with hR
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    change φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul]
    exact congrArg φ this
  have hQ3 : ∀ a ∈ Q, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    change (φ a) ^ 3 = 1
    rw [← map_pow, hP.2 a ha, map_one]
  have hscal : ∀ z : H, z ∈ Subgroup.center H →
      ∃ c : F, ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c := by
    intro z hz
    obtain ⟨ζ, hζ⟩ := (mem_center_slPi_iff hF hq z).mp hz
    exact ⟨ζ, by rw [← hζ, GeneralLinearGroup.coe_scalar]⟩
  have hRdet : ∀ x ∈ R, (x : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact det_eq_one_of_mem_slPi hF x.2
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, ∃ c : F,
      ((x * y * x⁻¹ * y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center H)]
      have hxy := hQc _ hx _ hy
      change QuotientGroup.mk' (Subgroup.center H) (x * y * x⁻¹ * y⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
      group
    exact hscal _ hz
  have hRcube : ∀ x ∈ R, ∃ c : F,
      ((x ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c := by
    rintro _ ⟨x, hx, rfl⟩
    have hz : x ^ 3 ∈ Subgroup.center H := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center H)]
      change QuotientGroup.mk' (Subgroup.center H) (x ^ 3) = 1
      rw [map_pow]
      exact hQ3 _ hx
    exact hscal _ hz
  have hR27 := SubgroupLists.card_le_twentyseven_of_scalar_commutators h3 R hRdet hRcomm hRcube
  have hRM : Nat.card R = Nat.card M := Subgroup.card_map_of_injective H.subtype_injective
  have hMQ : Nat.card M = Nat.card Q * Nat.card (Subgroup.center H) :=
    card_comap_mk' (Subgroup.center H) Q
  have hQP : Nat.card Q = Nat.card P := Subgroup.card_map_of_injective φ.injective
  have hZ := one_lt_card_center_slPi hF hq
  rw [hRM, hMQ, hQP] at hR27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := by
    intro x
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hP.2 x x.2, Subgroup.coe_one])⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  rw [hk] at hR27 ⊢
  have hk2 : k ≤ 2 := by
    by_contra hk
    push Not at hk
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    nlinarith
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem commute_of_centralize_four_group' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1) {a b x y : H ⧸ Subgroup.center H}
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (habc : a * b = b * a) (hxa : x * a = a * x) (hxb : x * b = b * x) (hya : y * a = a * y)
    (hyb : y * b = b * y) : x * y = y * x := by
  classical
  have hc2 : Nat.Coprime 2 3 := by norm_num
  obtain ⟨a', rfl, ha'2⟩ := SubgroupLists.exists_lift_pow_eq_one le_rfl hZ3 hc2 a ha2
  obtain ⟨b', rfl, hb'2⟩ := SubgroupLists.exists_lift_pow_eq_one le_rfl hZ3 hc2 b hb2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hb'a : b' * a' = a' * b' :=
    (SubgroupLists.commute_of_commute_mk le_rfl hZ3 hc2 ha'2 habc).symm
  have hx'a : x' * a' = a' * x' :=
    (SubgroupLists.commute_of_commute_mk le_rfl hZ3 hc2 ha'2 hxa.symm).symm
  have hy'a : y' * a' = a' * y' :=
    (SubgroupLists.commute_of_commute_mk le_rfl hZ3 hc2 ha'2 hya.symm).symm
  have hx'b : x' * b' = b' * x' :=
    (SubgroupLists.commute_of_commute_mk le_rfl hZ3 hc2 hb'2 hxb.symm).symm
  have hy'b : y' * b' = b' * y' :=
    (SubgroupLists.commute_of_commute_mk le_rfl hZ3 hc2 hb'2 hyb.symm).symm
  set C := (Subgroup.centralizer ({a'} : Set H)).map H.subtype with hC
  have hCc : ∀ g ∈ C, g * (a' : GL (Fin 3) K) = a' * g := by
    rintro _ ⟨g, hg, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact congrArg Subtype.val this
  have hCdet : ∀ g ∈ C, (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨g, -, rfl⟩
    exact hdet _ g.2
  have ha'1 : (a' : GL (Fin 3) K) ≠ 1 := fun h =>
    ha1 (by rw [show a' = 1 from Subtype.ext h, QuotientGroup.mk_one])
  obtain ⟨ρ, hρ, hρa⟩ := SubgroupLists.exists_injective_gl2_of_commute h2
    (by rw [← Subgroup.coe_mul, ← sq, ha'2, Subgroup.coe_one]) ha'1 (hdet _ a'.2) C hCc hCdet
  have hmem : ∀ g : H, g * a' = a' * g → (g : GL (Fin 3) K) ∈ C := fun g hg =>
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg, rfl⟩
  set A : C := ⟨a', hmem a' rfl⟩
  set B : C := ⟨b', hmem b' hb'a⟩
  set X : C := ⟨x', hmem x' hx'a⟩
  set Y : C := ⟨y', hmem y' hy'a⟩
  have hAm : ρ A = -1 := hρa A rfl
  set s := ((ρ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hBB : B * B = 1 := Subtype.ext (by
    change ((b' : GL (Fin 3) K)) * b' = 1
    rw [← Subgroup.coe_mul, ← sq, hb'2, Subgroup.coe_one])
  have hs : s * s = 1 := by
    change ((ρ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ B : GL _ _) = 1
    rw [← Units.val_mul, ← map_mul, hBB, map_one, Units.val_one]
  have hs1 : s ≠ 1 := by
    intro h
    have hB1 : ρ B = 1 := Units.ext h
    rw [← map_one ρ] at hB1
    have hB : B = 1 := hρ hB1
    apply hb1
    have hb'1 : b' = 1 := Subtype.ext (by simpa [B] using congrArg Subtype.val hB)
    rw [hb'1, QuotientGroup.mk_one]
  have hsn : s ≠ -1 := by
    intro h
    have hBA : ρ B = ρ A := by
      rw [hAm]
      exact Units.ext (by rw [Units.val_neg, Units.val_one]; exact h)
    have hBA' : B = A := hρ hBA
    apply hab
    have : b' = a' := Subtype.ext (by simpa [A, B] using congrArg Subtype.val hBA')
    rw [this]
  have hcomm : ∀ U : C, U * B = B * U →
      ((ρ U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * s =
        s * ((ρ U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro U hU
    change ((ρ U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ B : GL _ _) =
      ((ρ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ U : GL _ _)
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hU]
  have hXB : X * B = B * X := Subtype.ext (by
    change (x' : GL (Fin 3) K) * b' = b' * x'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hx'b])
  have hYB : Y * B = B * Y := Subtype.ext (by
    change (y' : GL (Fin 3) K) * b' = b' * y'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hy'b])
  have hXY := SubgroupLists.fin_two_commute_of_commute_involution h2 hs hs1 hsn (hcomm X hXB)
    (hcomm Y hYB)
  have hρXY : ρ (X * Y) = ρ (Y * X) := by
    rw [map_mul, map_mul]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hXY])
  have hXY' := congrArg Subtype.val (hρ hρXY)
  have hxy : x' * y' = y' * x' := Subtype.ext hXY'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem oddU34Excl : OddU34Excl := by
  intro X _ _ p e _ hp2 he hiso K hK
  obtain ⟨-, K', _, _, hK', ⟨ψ⟩⟩ := hK
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := exists_slPi_quotient he hiso
  have := hF.finite
  have hp : p.Prime := Fact.out
  have := charP_of_piField hF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K' 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two
    (by rw [hK', ← pow_mul])
  obtain ⟨a, b, x, y, ha2, hb2, ha1, hb1, hab, habc, hxa, hxb, hya, hyb, hxy⟩ :=
    SubgroupLists.exists_four_group_witness_psu34 hK'
  set ι : StatedProj (StatedSU 3 (2 ^ 2) K') →* ↥(slPi π 3 (p ^ e) F) ⧸
      Subgroup.center ↥(slPi π 3 (p ^ e) F) :=
    φ.toMonoidHom.comp (K.subtype.comp ψ.symm.toMonoidHom) with hι
  have hιi : Function.Injective ι :=
    φ.injective.comp (K.subtype_injective.comp ψ.symm.injective)
  apply hxy
  apply hιi
  have hne : ∀ c : StatedProj (StatedSU 3 (2 ^ 2) K'), c ≠ 1 → ι c ≠ 1 := fun c hc h =>
    hc (hιi (h.trans (map_one ι).symm))
  rw [map_mul, map_mul]
  exact commute_of_centralize_four_group' h2 (H := slPi π 3 (p ^ e) F)
    (fun z hz => det_eq_one_of_mem_slPi hF hz)
    (fun z hz => pow_three_eq_one_of_mem_center_slPi hF hq hz)
    (by rw [← map_pow, ha2, map_one]) (by rw [← map_pow, hb2, map_one]) (hne a ha1) (hne b hb1)
    (fun h => hab (hιi h)) (by rw [← map_mul, ← map_mul, habc])
    (by rw [← map_mul, ← map_mul, hxa]) (by rw [← map_mul, ← map_mul, hxb])
    (by rw [← map_mul, ← map_mul, hya]) (by rw [← map_mul, ← map_mul, hyb])

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
