module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofAfter
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import all CFSG.Timmesfeld.Orders.Distinct
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Open
open CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def KF83IndepGTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Odd n → Nat.card K = 2 ^ n →
    ∀ H : Subgroup (adjointGroup .G2 K), IsEmpty (H ≃* projSL 2 (GaloisField 2 (3 * n)))

section Profiles

variable {X : Type} [Group X]

theorem unitarySig_of_isoPGUThree {n : ℕ} (hn : 1 ≤ n) (h : IsoPGUThree X (2 ^ n)) :
    UnitarySig X n where
  profile := by
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    have hK' : Sec4.PiField false 2 n K := ⟨Nat.prime_two, hn, by rw [hK]; rfl⟩
    refine profile_of_eq (profile_card_SU3 hn) ?_
    rw [Nat.card_congr e.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hK',
      Sec13.card_slPi_three hK']
    rfl
  top := zU_two_six hn

theorem profile_projSL_two {g : ℕ} (hg : 1 ≤ g) (e : X ≃* projSL 2 (GaloisField 2 g)) :
    Profile (Nat.card X) g (zA 1 g) := by
  refine profile_of_eq (profile_congr (profile_ordA (n := 1) le_rfl hg) (by norm_num)) ?_
  have hgcd : Nat.gcd 2 (2 ^ g - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hg)
  rw [Nat.card_congr e.toEquiv, Sec21.card_projSL_two g hg]
  simp [ordA, hgcd]

theorem zA_one_self (g : ℕ) : zA 1 g g := ⟨2, by simp, ⟨2, by ring⟩⟩

theorem profile_of_isoReeF4
    {n : ℕ} (hn : 1 ≤ n)
    (h : IsoReeF4 X n) : Profile (Nat.card X) (n * 12) (z2F4 n) := by
  obtain ⟨k, K, _, _, _, hkn, hK, ⟨e⟩⟩ := h
  refine profile_of_eq (profile_ordTwistedF4 hn) ?_
  rw [card_of_mulEquiv_reeGamma k K (by rw [hK, hkn]) e, hkn]

theorem profile_of_projSp_two {n : ℕ} (hn : 1 ≤ n) (e : X ≃* projSp 2 (GaloisField 2 n)) :
    Profile (Nat.card X) (n * (2 * 2)) (zBC 2 n) := by
  refine profile_of_eq (profile_ordBC (n := 2) hn) ?_
  rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSp_two hn, ordBC_two_eq hn]

end Profiles

section Core

variable {G : Type} [Group G] [Finite G]

theorem false_of_profile_dvd {Y Z : Type} [Group Y] [Group Z] {N N' k : ℕ}
    {ZY ZZ : ℕ → Prop} (hY : Profile (Nat.card Y) N ZY) (hZ : Profile (Nat.card Z) N' ZZ)
    (hdvd : Nat.card Y ∣ Nat.card Z) (hk : 2 ≤ k) (hk6 : k ≠ 6) (hYk : ZY k) (hZk : ¬ ZZ k) :
    False := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk hk6
  have h1 := (hY.prim p k hp (by omega)).mpr hYk
  exact hZk ((hZ.prim p k hp (by omega)).mp (h1.trans hdvd))

theorem imageModTheta_le_barCentralizer {L K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hK : K ≤ Subgroup.centralizer ({a} : Set G)) :
    imageModTheta L K ≤ barCentralizer (Subgroup.zpowers a) L := by
  rintro _ ⟨k, hk, rfl⟩
  have hak : a * (k : G) = (k : G) * a :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hK (Subgroup.mem_subgroupOf.mp hk))).symm
  rw [KFacts.mem_barCentralizer_zpowers_iff ha, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  change a * (k : G) * a⁻¹ = k
  rw [hak, mul_inv_cancel_right]


theorem false_of_imageModTheta_le_barCentralizer (hG2 : KF83IndepGTwo) {c : G} {L : Subgroup G}
    {a : G} {A₀ : Subgroup G} {d : G} {n : ℕ} (hd : Data83 G c L a A₀ d n)
    (hle : imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≤
      barCentralizer (Subgroup.zpowers a) L) : False := by
  have hn := hd.odd
  have hn1 : 1 ≤ n := hn.pos
  set Kb := imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))
    with hKb
  set C := barCentralizer (Subgroup.zpowers a) L with hC
  have hdvd : Nat.card Kb ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  have h3n : 2 ≤ 3 * n := by omega
  have h3n6 : 3 * n ≠ 6 := by
    obtain ⟨t, rfl⟩ := hn
    omega
  have hU : ∀ eK : Kb ≃* projSL 2 (GaloisField 2 (3 * n)), UnitarySig C n → False :=
    fun eK hS => false_of_profile_dvd (profile_projSL_two (by omega) eK) hS.profile hdvd h3n
      h3n6 (zA_one_self _) (by
        have h := not_zU_mid (n := 2) (g := n) (t := 1) (Or.inl rfl) le_rfl (by omega)
        rwa [show n * (2 * 1 + 1) = 3 * n by ring] at h)
  rcases hd.cases with ⟨-, ⟨eK⟩, hC1 | ⟨-, hPGU, -⟩⟩ | ⟨-, hR, hSU⟩ | ⟨-, hS, ⟨eK⟩⟩ |
    ⟨-, hPGU, ⟨eK⟩⟩ | ⟨-, ⟨eC⟩, ⟨eK⟩⟩
  ·
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hC1
    have hH := hG2 F n hn hF ((Kb.subgroupOf C).map e.toMonoidHom)
    exact hH.false ((((Kb.subgroupOf C).equivMapOfInjective _ e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hle)).trans eK)
  · exact hU eK (unitarySig_of_isoPGUThree hn1 hPGU)
  ·
    have hKS := unitarySig_of_isoSUThree (g := 3 * n) (by omega) hSU
    refine false_of_profile_dvd hKS.profile (profile_of_isoReeF4 hn1 hR) hdvd (k := 18 * n)
      (by omega) (by omega) (by rw [show 18 * n = 6 * (3 * n) by ring]; exact hKS.top) ?_
    rintro (⟨h, -⟩ | h | ⟨h, -⟩ | h)
    · exact false_of_dvd_of_lt h (by omega) (by omega)
    · exact false_of_dvd_of_lt h (by omega) (by omega)
    · exact false_of_dvd_of_lt h (by omega) (by omega)
    · exact false_of_dvd_of_lt h (by omega) (by omega)
  · exact hU eK (unitarySig_of_isoSUThree hn1 hS)
  · exact hU eK (unitarySig_of_isoPGUThree hn1 hPGU)
  ·
    refine false_of_profile_dvd (profile_projSL_two (by omega) eK) (profile_of_projSp_two hn1 eC)
      hdvd h3n h3n6 (zA_one_self _) ?_
    rw [zBC_two_iff]
    intro h
    have h' : 3 * n ∣ n * 4 - 3 * n := Nat.dvd_sub h dvd_rfl
    exact false_of_dvd_of_lt h' (by omega) (by omega)

theorem kF83Indep_of
    (hG2 : KF83IndepGTwo) : KF83Indep := by
  intro G _ _ A c L a A₀ d n h hA hd hdca
  have hA₀e := hd.isElemAbelian
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA₀e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := hA₀e.2 c hd.c_mem
  have ha3 : a ^ 3 = 1 := hA₀e.2 a hd.a_mem
  have hca : c * a = a * c := hcomm c hd.c_mem a hd.a_mem
  have hcL := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  obtain ⟨i, j, -, hj, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hdca
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  ·
    refine false_of_isGammaIndex_of_centralizes (isGammaIndex_of_data83 hd)
      (Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt) (fun y hy => ?_)
    rw [pow_zero, mul_one, Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.pow_left (hcy y hy) i).eq).symm
  all_goals
    refine false_of_imageModTheta_le_barCentralizer hG2 hd
      (imageModTheta_le_barCentralizer h.a_mem_normalizer ?_)
    intro k hk
    obtain ⟨hkL, hkd⟩ := Subgroup.mem_inf.mp (Subgroup.map_subtype_le _ hk)
    have hkc : Commute c k := hcy k hkL
    rw [Subgroup.mem_centralizer_singleton_iff] at hkd ⊢
  ·
    have h1 : (c ^ i * a ^ 1) * k = k * (c ^ i * a ^ 1) := hkd.symm
    rw [pow_one] at h1
    have h2 : c ^ i * (a * k) = c ^ i * (k * a) := by
      rw [← mul_assoc, h1, ← mul_assoc, ← (Commute.pow_left hkc i).eq, mul_assoc]
    exact (mul_left_cancel h2).symm
  ·
    have h1 : (c ^ i * a ^ 2) * k = k * (c ^ i * a ^ 2) := hkd.symm
    have h2 : c ^ i * (a ^ 2 * k) = c ^ i * (k * a ^ 2) := by
      rw [← mul_assoc, h1, ← mul_assoc, ← (Commute.pow_left hkc i).eq, mul_assoc]
    have h3 : Commute (a ^ 2) k := mul_left_cancel h2
    have h4 : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
    rw [h4]
    exact ((h3.pow_left 2).eq).symm

end Core

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
