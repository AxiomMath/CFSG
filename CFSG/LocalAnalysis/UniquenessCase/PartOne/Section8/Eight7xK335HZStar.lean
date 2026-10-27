module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2CharThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65K332Inversion
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneBurnside
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CenterCentralizerP
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k335hz_weaklyClosed_zpowers {X : Type} [Group X] [Finite X] {a : X}
    (ha : orderOf a = 3)
    (hiso : ∀ g : X, g⁻¹ * a * g * a = a * (g⁻¹ * a * g) → g⁻¹ * a * g = a) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (Subgroup.zpowers a)
      (Subgroup.normalizer ((Subgroup.zpowers a : Subgroup X) : Set X)) := by
  intro g hg
  have hZ3 : IsPGroup 3 (Subgroup.zpowers a : Subgroup X) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hZcard : Nat.card ↥(Subgroup.zpowers a : Subgroup X) = 3 := by
    rw [Nat.card_zpowers, ha]
  have hA3 : IsPGroup 3 (CFSG.conjugate (Subgroup.zpowers a : Subgroup X) g) :=
    hZ3.map (MulAut.conj g⁻¹).toMonoidHom
  have hAc : CFSG.conjugate (Subgroup.zpowers a : Subgroup X) g ≤
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) :=
    le_centralizer_center_of_isPGroup hA3 hg hZcard
  have hzg : g⁻¹ * a * g ∈ CFSG.conjugate (Subgroup.zpowers a : Subgroup X) g := by
    simp [CFSG.conjugate]
  have hcomm := (Subgroup.mem_centralizer_iff.mp (hAc hzg)) a (Subgroup.mem_zpowers a)
  have hb : g⁻¹ * a * g = a := hiso g hcomm.symm
  rw [CFSG.conjugate, MonoidHom.map_zpowers]
  change Subgroup.zpowers ((MulAut.conj g⁻¹) a) = Subgroup.zpowers a
  rw [MulAut.conj_apply, inv_inv, hb]

private theorem k335hz_central_of_pRank_le_one {X : Type} [Group X] [Finite X] {a : X}
    (ha : orderOf a = 3)
    (hiso : ∀ g : X, g⁻¹ * a * g * a = a * (g⁻¹ * a * g) → g⁻¹ * a * g = a)
    (hcore : CFSG.pPrimeCore 3 X = ⊥)
    (hrank : CFSG.Open.pRank 3
      (Subgroup.normalClosure ((Subgroup.zpowers a : Subgroup X) : Set X)) ≤ 1) :
    ∀ y : X, a * y = y * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup X := Subgroup.normalClosure ((Subgroup.zpowers a : Subgroup X) : Set X)
  have hKnormal : K.Normal := Subgroup.normalClosure_normal
  have haK : a ∈ K := Subgroup.le_normalClosure (Subgroup.mem_zpowers a)
  have hrankK : CFSG.Open.pRank 3 K ≤ 1 := hrank
  have hcycK : ∀ S : Subgroup K, IsPGroup 3 S → IsCyclic ↥S := by
    intro S hS
    have hSm : IsPGroup 3 (S.map K.subtype) := hS.map K.subtype
    have hcycSm : IsCyclic ↥(S.map K.subtype) :=
      CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hSm
        (Subgroup.map_subtype_le S) hrankK
    exact ((Subgroup.equivMapOfInjective S K.subtype K.subtype_injective).isCyclic).mpr hcycSm
  have hNC : Subgroup.normalizer (Subgroup.zpowers (⟨a, haK⟩ : K) : Set K) ≤
      Subgroup.centralizer (Subgroup.zpowers (⟨a, haK⟩ : K) : Set K) := by
    intro g hg
    have hby : g⁻¹ * (⟨a, haK⟩ : K) * g ∈ Subgroup.zpowers (⟨a, haK⟩ : K) :=
      (Subgroup.mem_set_normalizer_iff''.mp hg (⟨a, haK⟩ : K)).mp (Subgroup.mem_zpowers _)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hby
    have hconj : (g : X)⁻¹ * a * (g : X) ∈ Subgroup.zpowers a := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      simpa using congrArg (fun z : K => (z : X)) hm
    have hprem : ((g : X)⁻¹ * a * (g : X)) * a = a * ((g : X)⁻¹ * a * (g : X)) := by
      have : IsMulCommutative ↥(Subgroup.zpowers a) := Subgroup.zpowers_isMulCommutative a
      have h := mul_comm' (⟨(g : X)⁻¹ * a * (g : X), hconj⟩ : Subgroup.zpowers a)
        (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a)
      simpa using congrArg Subtype.val h
    have hconj_eq : (g : X)⁻¹ * a * (g : X) = a := hiso (g : X) hprem
    have hgy : g * (⟨a, haK⟩ : K) = (⟨a, haK⟩ : K) * g := by
      apply Subtype.ext
      change (g : X) * a = a * (g : X)
      calc (g : X) * a = (g : X) * ((g : X)⁻¹ * a * (g : X)) := by rw [hconj_eq]
        _ = a * (g : X) := by group
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hgy
  have hyp : orderOf (⟨a, haK⟩ : K) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact ha
  obtain ⟨N, hNnormal, hNcop, hidx⟩ :=
    RankThreeTheoremC.RankOne.exists_normal_pComplement_of_normalizer_le_centralizer
      (Y := K) Nat.prime_three (y := (⟨a, haK⟩ : K)) hyp hNC hcycK
  have hNle : N ≤ CFSG.pPrimeCore 3 ↥K :=
    CFSG.le_pPrimeCore_of_normal_coprime hNnormal
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hNcop)
  have hpK : CFSG.pPrimeCore 3 ↥K = ⊥ := by
    have h := CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 3) hKnormal
    rw [hcore, inf_bot_eq,
      Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h
    exact h
  have hNbot : N = ⊥ := le_bot_iff.mp (hNle.trans (le_of_eq hpK))
  obtain ⟨n, hn⟩ := hidx
  have hcardK : Nat.card ↥K = 3 ^ n := by
    simpa [hNbot, Subgroup.index_bot] using hn
  have hKp : IsPGroup 3 ↥K := IsPGroup.of_card hcardK
  have hKrankTop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K]
    exact hrank
  have hcycKtop : IsCyclic ↥K :=
    CFSG.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) hKp hKrankTop
  have : IsMulCommutative ↥K := IsCyclic.isMulCommutative
  intro y
  have hcK : y⁻¹ * a * y ∈ K := by
    simpa using hKnormal.conj_mem a haK y⁻¹
  have hcommK : (y⁻¹ * a * y) * a = a * (y⁻¹ * a * y) := by
    have h := mul_comm' (⟨y⁻¹ * a * y, hcK⟩ : K) (⟨a, haK⟩ : K)
    simpa using congrArg Subtype.val h
  have hy : y⁻¹ * a * y = a := hiso y hcommK
  have h2 : y * a = a * y := by
    calc y * a = y * (y⁻¹ * a * y) := by rw [hy]
      _ = a * y := by group
  exact h2.symm

private theorem k335hz_central_of_K332
    (hK : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.K332Z3)
    (hJ2 : ∀ (Y : Type) [Group Y] [Finite Y], IsSpor Y .J2 → SylowCenterInverted Y)
    (hU33 : ∀ (Y : Type) [Group Y] [Finite Y],
      CFSG.Blueprint.LieModel Y .PSU 3 3 1 → SylowCenterInverted Y)
    (hG2 : ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime →
      CFSG.Blueprint.LieModel Y .G2 0 r f → SylowCenterInverted Y)
    {X : Type} [Group X] [Finite X] {a : X} (hXK : CFSG.Open.IsKGroup X)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) (hcore : CFSG.pPrimeCore 3 X = ⊥)
    (ha : orderOf a = 3)
    (hiso : ∀ g : X, g⁻¹ * a * g * a = a * (g⁻¹ * a * g) → g⁻¹ * a * g = a) :
    ∀ y : X, a * y = y * a := by
  have hwc := k335hz_weaklyClosed_zpowers ha hiso
  have hres := exists_inverts_or_pRank_one_of_K332 hK hJ2 hU33 hG2 hXK
    (by rw [Nat.card_zpowers, ha]) hwc hrank
  rcases hres with hinv | hrank1
  · exfalso
    obtain ⟨n, _hnN, hninv⟩ := hinv
    have hna : n * a * n⁻¹ = a⁻¹ := hninv a (Subgroup.mem_zpowers a)
    have hprem : (n⁻¹)⁻¹ * a * n⁻¹ * a = a * ((n⁻¹)⁻¹ * a * n⁻¹) := by
      rw [inv_inv, hna]; group
    have heq : n * a * n⁻¹ = a := by simpa [inv_inv] using hiso n⁻¹ hprem
    have hainv : a⁻¹ = a := hna.symm.trans heq
    have h2 : a ^ 2 = 1 := by
      have h := congrArg (fun t => t * a) hainv
      simpa [pow_two] using h.symm
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [ha] at hdvd
    exact absurd hdvd (by norm_num)
  · exact k335hz_central_of_pRank_le_one ha hiso hcore (le_of_eq hrank1)

theorem k335OddZStar_holds :
    K335OddZStar := by
  intro X _ _ hXK hrank hcore a ha hiso
  obtain ⟨hJ2, hU33, hG2⟩ := sylowCenterInverted_inputs g2CharThreeInversion_holds
  exact k335hz_central_of_K332
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.k332Z3_holds hJ2 hU33 hG2 hXK hrank
    hcore ha hiso

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
