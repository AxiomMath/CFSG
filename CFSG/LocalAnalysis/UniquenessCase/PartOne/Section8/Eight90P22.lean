module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveH2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63J2Tits
import CFSG.GroupTheory.AllPSubgroupsIsCyclicOfPRankLeOne
import CFSG.Quasithin.Vol2.F134Orders
import CFSG.LargeExtraspecial.S5Comp
import CFSG.Quasithin.Background.C2Eleven
import CFSG.Quasithin.H13.NQCatSubnormalCore
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

private theorem r890p22_two_le_pRank_centralizer {G : Type} [Group G] [Finite G] {D : Data G}
    {L : Subgroup G}
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2)
    (F : Subgroup G) (hFC : F ≤ PartTwo.S17.centSection D.M L (CFSG.Open.pCoreOf 2 L))
    (hF5 : IsPGroup 5 ↥F) :
    2 ≤ CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let CL : Subgroup G := L ⊓ Subgroup.centralizer (F : Set G)
  have hCLle : CL ≤ L := inf_le_left
  let K : Subgroup ↥L := CL.subgroupOf L
  let B : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' B
  have hKmap : K.map π = ⊤ := by
    simpa [CL, K, B, π] using
      PartTwo.S17.centralizer_map_bar2_eq_top (D := D) (L := L) hNL F hFC hF5
  have hsurj : Function.Surjective (π.comp K.subtype) := by
    intro y
    have hy : y ∈ K.map π := by rw [hKmap]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let φ : ↥K →* Bar2 L := π.comp K.subtype
  let N : Subgroup ↥K := B.subgroupOf K
  have hNker : φ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change π x.1 = 1 ↔ (x.1 : ↥L) ∈ B
    exact QuotientGroup.eq_one_iff (x.1 : ↥L)
  have hN2 : IsPGroup 2 ↥N := by
    let f : ↥N →* ↥B :=
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_injective f
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : ↥B => (z : ↥L)) h)))
  have hNcop : ¬ 5 ∣ Nat.card ↥N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    intro hd
    exact (by norm_num : ¬ (5 : ℕ) ∣ 2)
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
  have hquot : CFSG.Open.pRank 5 (⊤ : Subgroup (↥K ⧸ N)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_quotient_eq N hNcop
  have hbar : CFSG.Open.pRank 5 (⊤ : Subgroup (↥K ⧸ N)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := by
    let eQ : (↥K ⧸ N) ≃* Bar2 L :=
      (QuotientGroup.quotientMulEquivOfEq hNker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) eQ
  have hK : CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥CL) := by
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
      (Subgroup.subgroupOfEquivOfLe hCLle)
  have h2bar : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := by
    rw [pRank_five_eq_two_of_isSpor_J2 hJ2]
  have hCLtop : CFSG.Open.pRank 5 CL =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥CL) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup CL
  have hchain : CFSG.Open.pRank 5 CL =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := by
    calc CFSG.Open.pRank 5 CL
        = CFSG.Open.pRank 5 (⊤ : Subgroup ↥CL) := hCLtop
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) := hK.symm
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup (↥K ⧸ N)) := hquot.symm
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := hbar
  rw [hchain]
  exact h2bar

theorem r890p22_pRank_five_cent_le_one {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G}
    (hset : Set880 D L P) (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) (h885 : R885 D) :
    CFSG.Open.pRank 5 (F08.CentOverO2 D.M L) ≤ 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJ2, -, he3⟩ := h885 L P hset
  have hCeq : F08.CentOverO2 D.M L = PartTwo.S17.centSection D.M L (pCoreOf 2 L) :=
    PartTwo.S17.centOverO2_eq_centSection
  by_contra hnot
  have h2C : 2 ≤ CFSG.Open.pRank 5 (F08.CentOverO2 D.M L) := by omega
  have h2C' : 2 ≤ CFSG.Open.pRank 5
      (PartTwo.S17.centSection D.M L (pCoreOf 2 L)) := by rwa [hCeq] at h2C
  obtain ⟨F, hFC, hFel, hFcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five
      (PartTwo.S17.centSection D.M L (pCoreOf 2 L))
  have hF5 : IsPGroup 5 ↥F := hFel.isPGroup
  have h2CL : 2 ≤ CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G)) :=
    r890p22_two_le_pRank_centralizer (D := D) (L := L) hNL hJ2 F hFC hF5
  obtain ⟨E, hECL, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five
      (L ⊓ Subgroup.centralizer (F : Set G))
  have hEL : E ≤ L := hECL.trans inf_le_left
  have hECF : E ≤ Subgroup.centralizer (F : Set G) := hECL.trans inf_le_right
  have hE5 : IsPGroup 5 ↥E := hEel.isPGroup
  have hEinfF : E ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxF⟩ := Subgroup.mem_inf.mp hx
    have hxLC : x ∈ L ⊓ PartTwo.S17.centSection D.M L (pCoreOf 2 L) :=
      Subgroup.mem_inf.mpr ⟨hEL hxE, hFC hxF⟩
    have hxO2 : x ∈ pCoreOf 2 L := PartTwo.S17.inf_centSection_le_pCore (D := D) (L := L) hJ2 hxLC
    have hx2 : orderOf x ∣ Nat.card (pCoreOf 2 L) :=
      Subgroup.orderOf_dvd_natCard (pCoreOf 2 L) hxO2
    have hx5 : orderOf x ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hxE
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hE5
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    have h2 : Nat.card (pCoreOf 2 L) = 2 ^ b := by
      rw [show pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype from rfl,
        Subgroup.card_map_of_injective L.subtype_injective, hb]
    rw [ha] at hx5
    rw [h2] at hx2
    have hdvd : orderOf x ∣ Nat.gcd (5 ^ a) (2 ^ b) := Nat.dvd_gcd hx5 hx2
    have hgcd : Nat.gcd (5 ^ a) (2 ^ b) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow a b (by norm_num : Nat.Coprime 5 2))
    rw [hgcd] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e := by
    intro e he f hf
    exact (Subgroup.mem_centralizer_iff.mp (hECF he) f hf).symm
  have hEFel : IsElemAbelian 5 (E ⊔ F) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEel hFel hcomm
  have hFleCE : F ≤ Subgroup.centralizer (E : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hcomm e he f hf
  have hFnormE : F ≤ Subgroup.normalizer (E : Set G) :=
    hFleCE.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  have hcardEF : Nat.card ↥(E ⊔ F) = Nat.card E * Nat.card F :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E F hFnormE
      (disjoint_iff.mpr hEinfF)
  have hEFM : E ⊔ F ≤ D.M :=
    sup_le (hEL.trans (CFSG.Open.IsSubnormal.le hset.mem.1))
      (hFC.trans (PartTwo.S17.centSection_le _ _ _))
  have hcard5 : Nat.card ↥(E ⊔ F) = 5 ^
      (CFSG.Open.pRank 5 (PartTwo.S17.centSection D.M L (pCoreOf 2 L)) +
        CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G))) := by
    rw [hcardEF, hEcard, hFcard, ← pow_add, add_comm]
  have h4M : 4 ≤ CFSG.Open.pRank 5 D.M := by
    have hsum : 4 ≤ CFSG.Open.pRank 5 (PartTwo.S17.centSection D.M L (pCoreOf 2 L)) +
        CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G)) := by omega
    exact hsum.trans (CFSG.SectionRank.le_pRank (p := 5) (by norm_num) hEFM hEFel hcard5)
  have h4e : 4 ≤ CFSG.Open.evenRank G :=
    h4M.trans (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank
      5 Nat.prime_five (by norm_num) D.M D.maxLocal.1)
  omega

theorem r890p22_cent_normal {G : Type} [Group G] [Finite G] {D : Data G}
    {L : Subgroup G} (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) :
    D.M ≤ Subgroup.normalizer (F08.CentOverO2 D.M L : Set G) := by
  rw [PartTwo.S17.centOverO2_eq_centSection]
  exact PartTwo.S17.centSection_le_normalizer hNL

private theorem r890p22_pCoreOf_le_cent {G : Type} [Group G] [Finite G] {D : Data G}
    {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.Open.pCoreOf 2 L ≤ F08.CentOverO2 D.M L := by
  rw [PartTwo.S17.centOverO2_eq_centSection]
  intro x hx
  have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
  have hxM : x ∈ D.M := CFSG.Open.IsSubnormal.le hL.1 hxL
  have hxNL : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hxL
  refine PartTwo.S17.mem_centSection_iff.2 ⟨hxM, hxNL, ?_, ?_⟩
  · exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxNL
  · intro a ha
    have haNL : a ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ha
    have haNQ : a ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L haNL
    have hconj : a * x * a⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp haNQ x).mp hx
    have heq : x * a * x⁻¹ * a⁻¹ = x * (a * x * a⁻¹)⁻¹ := by group
    rw [heq]
    exact (CFSG.Open.pCoreOf 2 L).mul_mem hx ((CFSG.Open.pCoreOf 2 L).inv_mem hconj)

private theorem r890p22_inf_cent_eq_pCore {G : Type} [Group G] [Finite G] {D : Data G}
    {L : Subgroup G} (hL : L ∈ calC D.M)
    (hJ2 : IsSpor (Bar2 L) .J2) :
    L ⊓ F08.CentOverO2 D.M L = CFSG.Open.pCoreOf 2 L := by
  have h1 : L ⊓ F08.CentOverO2 D.M L ≤ CFSG.Open.pCoreOf 2 L := by
    rw [PartTwo.S17.centOverO2_eq_centSection]
    exact PartTwo.S17.inf_centSection_le_pCore (D := D) hJ2
  exact le_antisymm h1
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (r890p22_pCoreOf_le_cent hL))

theorem r890p22_three_not_dvd_cent {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G}
    (hL : L ∈ calC D.M) (hJ2 : IsSpor (Bar2 L) .J2)
    (hP : IsSylowOf 3 P D.M) (hPL : P ≤ L)
    (hNC : D.M ≤ Subgroup.normalizer (F08.CentOverO2 D.M L : Set G)) :
    ¬ 3 ∣ Nat.card ↥(F08.CentOverO2 D.M L) := by
  set C := F08.CentOverO2 D.M L with hCdef
  have hCM : C ≤ D.M := fun x hx => (PartTwo.mem_centOverO2_iff.mp hx).1
  have hCP : C ⊓ P = ⊥ := by
    have h1 : C ⊓ P ≤ CFSG.Open.pCoreOf 2 L := by
      calc C ⊓ P ≤ C ⊓ L := inf_le_inf le_rfl hPL
        _ = L ⊓ C := inf_comm C L
        _ = CFSG.Open.pCoreOf 2 L := r890p22_inf_cent_eq_pCore hL hJ2
    have h2 : IsPGroup 2 ↥(C ⊓ P) :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L).to_le h1
    have h3 : IsPGroup 3 ↥(C ⊓ P) := hP.isPGroup.to_le inf_le_right
    have hd := IsPGroup.disjoint_of_ne 2 3 (by norm_num) (C ⊓ P) (C ⊓ P) h2 h3
    simpa only [inf_idem] using hd.eq_bot
  have hSyl : IsSylowOf 3 (P ⊓ C) C := hP.inf_of_le_normalizer hCM hNC
  have hPC : P ⊓ C = ⊥ := by rw [inf_comm]; exact hCP
  have hcard := hSyl.card_eq
  rw [hPC, Subgroup.card_bot] at hcard
  have hk0 : (Nat.card C).factorization 3 = 0 := by
    have hpow : 3 ^ (Nat.card C).factorization 3 = 1 := hcard.symm
    by_contra hk
    have hk1 : 1 ≤ (Nat.card C).factorization 3 := Nat.one_le_iff_ne_zero.mpr hk
    have h3le : 3 ≤ 3 ^ (Nat.card C).factorization 3 := by
      calc 3 = 3 ^ 1 := by ring
        _ ≤ 3 ^ (Nat.card C).factorization 3 := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  rcases (Nat.factorization_eq_zero_iff (Nat.card C) 3).mp hk0 with h | h | h
  · exact absurd Nat.prime_three h
  · exact h
  · exact absurd h (Nat.card_pos (α := ↥C)).ne'

open CFSG.Blueprint (LieModel)

theorem r890p22_setup {G : Type} [Group G] [Finite G] {M C : Subgroup G} (hCM : C ≤ M)
    (hKM : CFSG.Open.IsKGroup ↥M) (hns : ¬ Group.IsSolvable ↥C) (h3 : ¬ 3 ∣ Nat.card ↥C)
    (h5 : CFSG.Open.pRank 5 C ≤ 1) (hr : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p M ≤ 3) :
    CFSG.Open.IsKGroup (Bar2 (CFSG.Quasithin.perfectCore C)) ∧
      commutator (Bar2 (CFSG.Quasithin.perfectCore C)) = ⊤ ∧
      ¬ Group.IsSolvable (Bar2 (CFSG.Quasithin.perfectCore C)) ∧
      CFSG.pCore 2 (Bar2 (CFSG.Quasithin.perfectCore C)) = ⊥ ∧
      ¬ 3 ∣ Nat.card (Bar2 (CFSG.Quasithin.perfectCore C)) ∧
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 (CFSG.Quasithin.perfectCore C))) ≤ 1 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (CFSG.Quasithin.perfectCore C))) ≤ 3 := by
  classical
  have key : ∀ Dp : Subgroup G, Dp ≤ C → ⁅Dp, Dp⁆ = Dp → ¬ Group.IsSolvable ↥Dp →
      CFSG.Open.IsKGroup (Bar2 Dp) ∧ commutator (Bar2 Dp) = ⊤ ∧ ¬ Group.IsSolvable (Bar2 Dp) ∧
        CFSG.pCore 2 (Bar2 Dp) = ⊥ ∧ ¬ 3 ∣ Nat.card (Bar2 Dp) ∧
        CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 Dp)) ≤ 1 ∧
        ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup (Bar2 Dp)) ≤ 3 := by
    intro Dp hDpC hperf hDpns
    have : Group.IsPerfect ↥Dp := Subgroup.isPerfect_iff.mpr hperf
    have : Group.IsNilpotent (CFSG.pCore 2 ↥Dp) := CFSG.pCore_isNilpotent
    have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ K : Subgroup G, Dp ≤ K →
        CFSG.Open.pRank p (⊤ : Subgroup (Bar2 Dp)) ≤ CFSG.Open.pRank p K := by
      intro p hp hp2 K hK
      have : Fact p.Prime := ⟨hp⟩
      have hcop : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥Dp) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Dp))
        rw [hk]
        intro hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
      rw [CFSG.SectionRank.pRank_quotient_eq _ hcop,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Dp]
      exact CFSG.SectionRank.pRank_mono hp.one_lt hK
    refine ⟨(hKM.of_le (hDpC.trans hCM)).quotient _, Group.isPerfect_def.mp inferInstance, ?_,
      CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2,
      fun hd => h3 (hd.trans ((Subgroup.card_quotient_dvd_card _).trans
        (Subgroup.card_dvd_of_le hDpC))),
      (hrank 5 Nat.prime_five (by norm_num) C hDpC).trans h5,
      fun p hp hp2 => (hrank p hp hp2 M (hDpC.trans hCM)).trans (hr p hp hp2)⟩
    intro hsolv
    exact hDpns (Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 ↥Dp))
  refine key _ (CFSG.Quasithin.perfectCore_le C) (CFSG.Quasithin.perfectCore_perfect C) ?_
  intro hs
  have h0 : CFSG.Quasithin.perfectCore (CFSG.Quasithin.perfectCore C) = ⊥ :=
    (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp hs
  rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect (CFSG.Quasithin.perfectCore_perfect C)] at h0
  exact hns ((CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot C).mpr h0)

theorem r890p22_pRank_quotient_le_one {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 1) (N : Subgroup H) [N.Normal] :
    CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt (H := ⊤) (k := 1) fun E _ hE => ?_
  have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; ext; exact hE.2 (g : H ⧸ N) g.2⟩
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) p P
  have hScyc : IsCyclic (S : Subgroup H) :=
    CFSG.all_pSubgroups_isCyclic_of_pRank_le_one hp hp2 h S le_top S.isPGroup'
  have hPmap : (P : Subgroup (H ⧸ N)) = (S : Subgroup H).map (QuotientGroup.mk' N) := by
    rw [← hS, Sylow.coe_mapSurjective]
  have : IsCyclic ((S : Subgroup H).map (QuotientGroup.mk' N)) :=
    isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap (S : Subgroup H))
      ((QuotientGroup.mk' N).subgroupMap_surjective (S : Subgroup H))
  have hEle : E ≤ (S : Subgroup H).map (QuotientGroup.mk' N) := hPmap ▸ hEP
  have : IsCyclic E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEle).surjective
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic E)
  have hcard : Nat.card E = orderOf g := (orderOf_eq_card_of_zpowers_eq_top hg).symm
  have hgp : g ^ p = 1 := by ext; exact hE.2 (g : H ⧸ N) g.2
  have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
  rw [hcard]
  simpa only [pow_one] using Nat.le_of_dvd hp.pos hdvd

theorem r890p22_unique_sz_component (hCat : PartTwo.Inputs1719.K_CatalogueThreePrimeSz)
    {Q : Type} [Group Q] [Finite Q] [Nontrivial Q] (hK : CFSG.Open.IsKGroup Q)
    (hrad : CFSG.solvableRadical Q = ⊥) (h3 : ¬ 3 ∣ Nat.card Q)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Q) ≤ 1) :
    ∃ (S : Subgroup Q) (n : ℕ), S.Normal ∧ IsSz ↥S n ∧ Subgroup.centralizer (S : Set Q) = ⊥ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2 : CFSG.pCore 2 Q = ⊥ := by
    have : Group.IsNilpotent (CFSG.pCore 2 Q) := CFSG.pCore_isNilpotent
    rw [eq_bot_iff, ← hrad]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical CFSG.pCore_normal
      inferInstance
  have hcomp : ∀ J : Subgroup Q, IsComponentOf J ⊤ → ∃ n : ℕ, IsSz ↥J n := by
    intro J hJ
    have hJsn : J.IsSubnormal := CFSG.Open.IsSubnormal.mathlib hJ.2.1 Subgroup.IsSubnormal.top
    have h3J : 3 ∉ piSet (⊤ : Subgroup ↥J) := by
      intro h
      simp only [piSet, Set.mem_setOf_eq] at h
      obtain ⟨-, hdvd⟩ := h
      rw [Subgroup.card_top] at hdvd
      exact h3 (hdvd.trans (Subgroup.card_subgroup_dvd_card J))
    obtain ⟨n, hn⟩ := hCat ↥J (hK.subgroup J) hJ.2.2 h3J
    have hbot : CFSG.pCore 2 ↥J = ⊥ := by
      have hle := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2) hJsn
      rw [h2, le_bot_iff] at hle
      exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥J) J.subtype_injective).1 hle
    exact ⟨n, CFSG.Blueprint.LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hn⟩
  have hfacts : ∀ J : Subgroup Q, IsComponentOf J ⊤ →
      ∃ x : Q, x ∈ J ∧ orderOf x = 5 ∧ x ∉ CFSG.Quasithin.centerOf J := by
    intro J hJ
    obtain ⟨n, hn⟩ := hcomp J hJ
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5
      (PartTwo.Inputs1719.FourteenEight.five_dvd_card_of_isSz hn)
    have hc := PartTwo.Inputs1719.FourteenEight.center_eq_bot_of_isSz hn
    refine ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx], fun h => ?_⟩
    have hxcent : x ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp h.2 (z : Q) z.2
    rw [hc, Subgroup.mem_bot] at hxcent
    rw [hxcent, orderOf_one] at hx
    omega
  have hunique : ∀ J₁ J₂ : Subgroup Q, IsComponentOf J₁ ⊤ → IsComponentOf J₂ ⊤ → J₁ = J₂ := by
    intro J₁ J₂ h₁ h₂
    by_contra hne
    obtain ⟨x₁, hx₁, ho₁, hc₁⟩ := hfacts J₁ h₁
    obtain ⟨x₂, hx₂, ho₂, hc₂⟩ := hfacts J₂ h₂
    have c12 : J₁ ≤ Subgroup.centralizer (J₂ : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h₁ h₂ hne)
    obtain ⟨hE1, hc1⟩ := CFSG.Quasithin.C2Eleven.elemAbelian_step Nat.prime_five
      (CFSG.SectionRank.isElemAbelian_bot 5) (L := ⊥) le_rfl bot_le hx₁ ho₁ hc₁
    have hE1K : (⊥ : Subgroup Q) ⊔ Subgroup.zpowers x₁ ≤ J₁ :=
      sup_le bot_le (Subgroup.zpowers_le.mpr hx₁)
    obtain ⟨hE2, hc2⟩ := CFSG.Quasithin.C2Eleven.elemAbelian_step Nat.prime_five hE1 hE1K c12
      hx₂ ho₂ hc₂
    have h2le := CFSG.SectionRank.le_pRank Nat.prime_five.one_lt
      (le_top : (⊥ ⊔ Subgroup.zpowers x₁) ⊔ Subgroup.zpowers x₂ ≤ (⊤ : Subgroup Q)) hE2
      (k := 2) (by rw [hc2, hc1, Subgroup.card_bot]; ring)
    omega
  have hex : ∃ J : Subgroup Q, IsComponentOf J ⊤ := by
    by_contra hne
    push Not at hne
    have hl : CFSG.layer Q = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall fun K hK' =>
      hne K ((CFSG.isComponent_iff_open K).mp hK')
    have hcb := CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot hrad
    rw [hl] at hcb
    obtain ⟨g, hg⟩ := exists_ne (1 : Q)
    apply hg
    have hmem : g ∈ Subgroup.centralizer (((⊥ : Subgroup Q) : Set Q)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
    rw [hcb, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨J, hJ⟩ := hex
  obtain ⟨n, hn⟩ := hcomp J hJ
  have hset : {K : Subgroup Q | CFSG.IsComponent K} = {J} := by
    ext K
    constructor
    · intro hK'
      exact hunique K J ((CFSG.isComponent_iff_open K).mp hK') hJ
    · intro hK'
      rw [Set.mem_singleton_iff] at hK'
      subst hK'
      exact (CFSG.isComponent_iff_open _).mpr hJ
  have hlayer : CFSG.layer Q = J := by
    rw [CFSG.layer.eq_sSup, hset, sSup_singleton]
  have hchar := CFSG.LocalCores.layer_characteristic (G := Q)
  rw [hlayer] at hchar
  refine ⟨J, n, inferInstance, hn, ?_⟩
  have hcb := CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot hrad
  rwa [hlayer] at hcb

theorem r890p22_eq_top_of_sz {Q : Type} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) {S : Subgroup Q} [S.Normal] {n : ℕ} (hS : IsSz ↥S n)
    (hcent : Subgroup.centralizer (S : Set Q) = ⊥) : S = ⊤ := by
  have : Group.IsPerfect Q := Group.isPerfect_def.mpr hperf
  have hs : CFSG.Blueprint.SuzukiModel ↥S 2 n := (CFSG.Blueprint.LieModel.suzukiModel hS).2
  have : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥S 2 n hs).1.1
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨s, hsq⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (MulAut.conjNormal : Q →* MulAut ↥S) q
  have hmem : (s : Q)⁻¹ * q ∈ Subgroup.centralizer (S : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥S => ((φ ⟨x, hx⟩ : ↥S) : Q)) hsq
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((s : Q)⁻¹ * q) = (s : Q)⁻¹ * (s * x * (s : Q)⁻¹) * q := by group
      _ = (s : Q)⁻¹ * (q * x * q⁻¹) * q := by rw [h1]
      _ = (s : Q)⁻¹ * q * x := by group
  rw [hcent, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem]
  exact s.2

theorem r890p22_three_dvd_of_K318 {S : Type} [Group S] [Finite S]
    (h : (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel S .PSL 2 p 1 ∨ LieModel S .PSL 3 p 1)) ∨
      IsAlt S 6 ∨ IsAlt S 7 ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel S .PSp 2 p 1 ∨ LieModel S .PSL 2 p 2)) :
    3 ∣ Nat.card S := by
  have hBC : ∀ q : ℕ, 3 ∣ CFSG.Open.ordBC 2 q := by
    intro q
    unfold CFSG.Open.ordBC
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
    have h1 : Nat.gcd 2 (q - 1) ∣ q ^ (2 * 1) - 1 :=
      (Nat.gcd_dvd_right 2 (q - 1)).trans (by simpa using Nat.sub_one_dvd_pow_sub_one q 2)
    have h3 : 3 ∣ q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) := by
      refine (CFSG.Quasithin.F134.three_dvd_mul_sq_sub_one q).trans ⟨q ^ 3 * (q ^ (2 * 2) - 1), ?_⟩
      norm_num
      ring
    exact CFSG.Quasithin.F134.dvd_div_of_dvd_of_coprime
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right h1 _) _) h3
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num))
  rcases h with ⟨p, -, hp2, h | h⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨p, -, hp2, h | h⟩
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_two
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_three
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))).2.2.1 rfl
    rw [hc]
    exact hBC _
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_two
      (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem r890p22_sz_cover {H : Type} [Group H] [Finite H] (hperf : commutator H = ⊤)
    (h2 : CFSG.pCore 2 H = ⊥) {n : ℕ} (hn : IsSz (H ⧸ CFSG.solvableRadical H) n)
    (hcent : ¬ Subgroup.centralizer ((CFSG.solvableRadical H : Subgroup H) : Set H) ≤
      CFSG.solvableRadical H) : IsSz H n := by
  have : Group.IsPerfect H := Group.isPerfect_def.mpr hperf
  have hXs : Group.IsSolvable (CFSG.solvableRadical H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have : IsSimpleGroup (H ⧸ CFSG.solvableRadical H) :=
    (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n
      (CFSG.Blueprint.LieModel.suzukiModel hn).2).2
  have hsup : Subgroup.centralizer ((CFSG.solvableRadical H : Subgroup H) : Set H) ⊔
      CFSG.solvableRadical H = ⊤ := by
    have hKn : (Subgroup.centralizer ((CFSG.solvableRadical H : Subgroup H) : Set H)).Normal :=
      inferInstance
    rcases (hKn.map (QuotientGroup.mk' (CFSG.solvableRadical H))
      (QuotientGroup.mk'_surjective _)).eq_bot_or_eq_top with h | h
    · exfalso
      apply hcent
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.solvableRadical H))
        (Subgroup.centralizer ((CFSG.solvableRadical H : Subgroup H) : Set H))
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
  have hKtop : Subgroup.centralizer ((CFSG.solvableRadical H : Subgroup H) : Set H) = ⊤ :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.eq_top_of_isSubnormal_of_sup_eq_top
      (Subgroup.Normal.isSubnormal inferInstance) inferInstance hXs hsup
  have hXc : CFSG.solvableRadical H ≤ Subgroup.center H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ((CFSG.solvableRadical H : Subgroup H) : Set H) := by
      rw [hKtop]
      exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have hX2 : IsPGroup 2 (CFSG.solvableRadical H) :=
    CFSG.Quasithin.isPGroup_two_of_isSz (CFSG.solvableRadical H) hXc
      (CFSG.Blueprint.LieModel.suzukiModel hn).2
  have hXbot : CFSG.solvableRadical H = ⊥ := by
    have hle : CFSG.solvableRadical H ≤ CFSG.pCore 2 H := le_sSup ⟨inferInstance, hX2⟩
    rwa [h2, le_bot_iff] at hle
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hXbot).trans QuotientGroup.quotientBot) hn

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
