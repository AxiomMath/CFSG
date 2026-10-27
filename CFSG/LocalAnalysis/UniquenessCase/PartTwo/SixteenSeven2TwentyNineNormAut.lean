module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormCount
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3Simple
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2Y13
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F918C12
public import CFSG.Quasithin.Background.F918C6
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate8026Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_isSimpleGroup_mulAut_eight {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 8) :
    IsSimpleGroup (MulAut W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm
    hsq (n := 3) (by rw [hcard]; norm_num)
  haveI :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
  exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).isSimpleGroup

private theorem s16c167_norm_exists_ne_one_mem_inf_fixV (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L) {P : Subgroup (MulAut W)}
    (hPL : P ≤ L) (hP : Nat.card ↥P = 8) {V : Subgroup W} (hV : XMod.IsIrr ↥L V)
    (hc : Nat.card ↥V = 8) : ∃ m ∈ V ⊓ fixV P, m ≠ 1 := by
  have hVinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hV.1 ⟨x, hx⟩ v hv
  have hnt := s16c167_norm_irr_nontrivial hV hc
  have hPV : ∀ g ∈ P, ∀ v ∈ V, g v ∈ V := fun g hg v hv => hVinv g (hPL hg) v hv
  have hfaith : ∀ g ∈ P, (∀ v ∈ V, g v = v) → g = 1 :=
    fun g hg hfix => rank3_inj hL hVinv hnt g (hPL hg) hfix
  have hcard : Nat.card ↥(V ⊓ fixV P) = 2 :=
    s16c167_norm_card_inf_fixV_eq_two hW hc hP hPV hfaith
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' (G := ↥(V ⊓ fixV P)) 2
    (by change 2 ∣ Nat.card ↥(V ⊓ fixV P); exact ⟨1, hcard⟩)
  refine ⟨(m : W), m.2, ?_⟩
  intro h1
  have h2 : m = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hm
  norm_num at hm

theorem s16c167_norm_two_element_fixes_of_normalizes_seven (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup W} (hA : Nat.card ↥A = 8) {Z : Subgroup (MulAut W)} (hZ : Nat.card ↥Z = 7)
    (hZA : ∀ z ∈ Z, ∀ a ∈ A, z a ∈ A) (hZf : ∀ z ∈ Z, (∀ a ∈ A, z a = a) → z = 1)
    {c : MulAut W} {k : ℕ} (hck : c ^ 2 ^ k = 1)
    (hcZ : Z.map (MulAut.conj c).toMonoidHom = Z) (hcA : c ∈ stabSub A) :
    ∀ a ∈ A, c a = a := by
  haveI : Finite ↥A := Subtype.finite
  have hZS : Z ≤ stabSub A := by
    intro z hz
    rw [mem_stabSub]
    intro u
    exact ⟨fun hzu => by
      have h1 : z⁻¹ (z u) ∈ A := hZA z⁻¹ (Z.inv_mem hz) (z u) hzu
      rwa [mulAut_inv_apply_apply] at h1,
      fun hu => hZA z hz u hu⟩
  let ψ : ↥Z →* MulAut ↥A := (resHom A).comp (Subgroup.inclusion hZS)
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have h1 : ∀ a ∈ A, (z : MulAut W) a = a := by
      intro a ha
      have h2 := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : W)) hz
      simpa [ψ, resHom_apply] using h2
    exact Subgroup.mem_bot.mpr (Subtype.ext (hZf z z.2 h1))
  let Q : Subgroup (MulAut ↥A) := ψ.range
  have hQcard : Nat.card ↥Q = 7 := by
    have h1 : Nat.card ↥Z = Nat.card ↥Q := Nat.card_congr (MonoidHom.ofInjective hψ_inj).toEquiv
    rw [hZ] at h1
    exact h1.symm
  have hcommA : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (mul_comm _ _)
  have hsqA : ∀ a : ↥A, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hW (a : W))
  have hcardAut : Nat.card (MulAut ↥A) = 168 :=
    card_mulAut_of_card_eight hcommA hsqA hA
  haveI : IsSimpleGroup (MulAut ↥A) :=
    s16c167_isSimpleGroup_mulAut_eight hcommA hsqA hA
  have hcardNorm : Nat.card ↥(Subgroup.normalizer (Q : Set (MulAut ↥A))) = 21 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.card_normalizer_of_card_seven_simple168 hcardAut Q hQcard
  have hmapZ : ∀ z ∈ Z, c * (z : MulAut W) * c⁻¹ ∈ Z := by
    intro z hz
    have hmem : (MulAut.conj c).toMonoidHom z ∈ Z.map (MulAut.conj c).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rw [hcZ] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hmapZinv : ∀ z ∈ Z, c⁻¹ * (z : MulAut W) * c ∈ Z := by
    intro z hz
    have hzZ : c * (c⁻¹ * (z : MulAut W) * c) * c⁻¹ ∈ Z := by
      have h1 : c * (c⁻¹ * (z : MulAut W) * c) * c⁻¹ = z := by group
      rw [h1]; exact hz
    have h2 : c * (c⁻¹ * (z : MulAut W) * c) * c⁻¹ ∈ Z.map (MulAut.conj c).toMonoidHom := by
      rw [hcZ]; exact hzZ
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h2
    have h3 : y = c⁻¹ * (z : MulAut W) * c := by
      have h4 : c * y * c⁻¹ = c * (c⁻¹ * (z : MulAut W) * c) * c⁻¹ := by
        simpa [MulAut.conj_apply] using hyeq
      exact mul_left_cancel (mul_right_cancel h4)
    rw [← h3]; exact hy
  have hcAinv : c⁻¹ ∈ stabSub A := (stabSub A).inv_mem hcA
  have hconjQ : ∀ q ∈ Q, (resHom A ⟨c, hcA⟩) * q * (resHom A ⟨c, hcA⟩)⁻¹ ∈ Q := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨c * (z : MulAut W) * c⁻¹, hmapZ z z.2⟩, ?_⟩
    have hconj_eq : (Subgroup.inclusion hZS ⟨c * (z : MulAut W) * c⁻¹, hmapZ z z.2⟩
          : ↥(stabSub A)) =
        (⟨c, hcA⟩ : ↥(stabSub A)) * (Subgroup.inclusion hZS z)
          * (⟨c, hcA⟩ : ↥(stabSub A))⁻¹ := rfl
    calc ψ ⟨c * (z : MulAut W) * c⁻¹, hmapZ z z.2⟩
        = resHom A (Subgroup.inclusion hZS ⟨c * (z : MulAut W) * c⁻¹, hmapZ z z.2⟩) := rfl
      _ = resHom A ((⟨c, hcA⟩ : ↥(stabSub A)) * (Subgroup.inclusion hZS z)
            * (⟨c, hcA⟩ : ↥(stabSub A))⁻¹) := by rw [hconj_eq]
      _ = resHom A ⟨c, hcA⟩ * resHom A (Subgroup.inclusion hZS z)
            * (resHom A ⟨c, hcA⟩)⁻¹ := by rw [map_mul, map_mul, map_inv]
  have hconjQinv : ∀ q ∈ Q,
      (resHom A ⟨c⁻¹, hcAinv⟩) * q * (resHom A ⟨c⁻¹, hcAinv⟩)⁻¹ ∈ Q := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨c⁻¹ * (z : MulAut W) * c, hmapZinv z z.2⟩, ?_⟩
    have hconj_eq : (Subgroup.inclusion hZS ⟨c⁻¹ * (z : MulAut W) * c, hmapZinv z z.2⟩
          : ↥(stabSub A)) =
        (⟨c⁻¹, hcAinv⟩ : ↥(stabSub A)) * (Subgroup.inclusion hZS z)
          * (⟨c⁻¹, hcAinv⟩ : ↥(stabSub A))⁻¹ := rfl
    calc ψ ⟨c⁻¹ * (z : MulAut W) * c, hmapZinv z z.2⟩
        = resHom A (Subgroup.inclusion hZS ⟨c⁻¹ * (z : MulAut W) * c, hmapZinv z z.2⟩) := rfl
      _ = resHom A ((⟨c⁻¹, hcAinv⟩ : ↥(stabSub A)) * (Subgroup.inclusion hZS z)
            * (⟨c⁻¹, hcAinv⟩ : ↥(stabSub A))⁻¹) := by rw [hconj_eq]
      _ = resHom A ⟨c⁻¹, hcAinv⟩ * resHom A (Subgroup.inclusion hZS z)
            * (resHom A ⟨c⁻¹, hcAinv⟩)⁻¹ := by rw [map_mul, map_mul, map_inv]
  have hc'normalizer : (resHom A ⟨c, hcA⟩) ∈ Subgroup.normalizer (Q : Set (MulAut ↥A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hconjQ q
    · intro hq
      have h1 : (resHom A ⟨c⁻¹, hcAinv⟩)
          * ((resHom A ⟨c, hcA⟩) * q * (resHom A ⟨c, hcA⟩)⁻¹)
          * (resHom A ⟨c⁻¹, hcAinv⟩)⁻¹ ∈ Q := hconjQinv _ hq
      have h3 : (resHom A ⟨c⁻¹, hcAinv⟩ : MulAut ↥A) = (resHom A ⟨c, hcA⟩)⁻¹ := by
        have h4 : (⟨c⁻¹, hcAinv⟩ : ↥(stabSub A)) = (⟨c, hcA⟩ : ↥(stabSub A))⁻¹ :=
          Subtype.ext rfl
        rw [h4, map_inv]
      have h2 : (resHom A ⟨c⁻¹, hcAinv⟩)
          * ((resHom A ⟨c, hcA⟩) * q * (resHom A ⟨c, hcA⟩)⁻¹)
          * (resHom A ⟨c⁻¹, hcAinv⟩)⁻¹ = q := by
        rw [h3]; group
      rwa [h2] at h1
  have horder21 : orderOf (resHom A ⟨c, hcA⟩) ∣ 21 := by
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.normalizer (Q : Set (MulAut ↥A)))
      hc'normalizer
    rwa [hcardNorm] at h1
  have hc'pow : (resHom A ⟨c, hcA⟩) ^ 2 ^ k = 1 := by
    have h1 : (⟨c, hcA⟩ : ↥(stabSub A)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      show c ^ 2 ^ k = 1
      exact hck
    calc (resHom A ⟨c, hcA⟩) ^ 2 ^ k
        = resHom A ((⟨c, hcA⟩ : ↥(stabSub A)) ^ 2 ^ k) := (map_pow _ _ _).symm
      _ = resHom A 1 := by rw [h1]
      _ = 1 := map_one _
  have horder2 : orderOf (resHom A ⟨c, hcA⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc'pow
  have hcop : Nat.Coprime 21 (2 ^ k) := (by norm_num : Nat.Coprime 21 2).pow_right k
  have hone : orderOf (resHom A ⟨c, hcA⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder21 horder2
  have hc'1 : (resHom A ⟨c, hcA⟩) = 1 := orderOf_eq_one_iff.mp hone
  intro a ha
  have h1 := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : W)) hc'1
  simpa [resHom_apply] using h1

theorem s16c167_norm_natSum3_centralizer_two_trivial (hW : ∀ w : W, w ^ 2 = 1)
    {L Z : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L) {J : Subgroup W} (hJ : NatSum3 L J)
    (hZ : Nat.card ↥Z = 7) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J) (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w)
    {c : MulAut W} {k : ℕ} (hck : c ^ 2 ^ k = 1) (hcL : ∀ y ∈ L, c * y = y * c)
    (hcJ : J.map c.toMonoidHom = J) (hcZ : Z.map (MulAut.conj c).toMonoidHom = Z) :
    ∀ w ∈ J, c w = w := by
  obtain ⟨P, hPL, hP⟩ := s16c167_norm_exists_subgroup_card_eight hL
  have hAcard : Nat.card ↥(J ⊓ fixV P) = 8 :=
    (s16c167_norm_card_irr_natSum3 hW hL hJ hZ hZL hZJ hZf hPL hP).1
  have hfixirr : ∀ V : Subgroup W, V ≤ J → XMod.IsIrr ↥L V → Nat.card ↥V = 8 →
      ∃ m ∈ V ⊓ fixV P, m ≠ 1 := fun V _ hV hcV =>
    s16c167_norm_exists_ne_one_mem_inf_fixV hW hL hPL hP hV hcV
  have hZA : ∀ z ∈ Z, ∀ a ∈ J ⊓ fixV P, z a ∈ J ⊓ fixV P := by
    intro z hz a ha
    refine ⟨hZJ z hz a ha.1, mem_fixV.mpr ?_⟩
    intro p hp
    have hcomm := congrArg (fun φ : MulAut W => φ a) (hZL z hz p (hPL hp))
    simp only [MulAut.mul_apply] at hcomm
    rw [← hcomm, mem_fixV.mp ha.2 p hp]
  have hZfA : ∀ z ∈ Z, (∀ a ∈ J ⊓ fixV P, z a = a) → z = 1 := by
    intro z hz hzA
    by_contra hz1
    have hfixJ : ∀ w ∈ J, z w = w :=
      s16c167_norm_fixes_natSum3_of_fixes_irr hJ (hZL z hz) (fun V hVJ hV hcV => by
        obtain ⟨m, hm, hm1⟩ := hfixirr V hVJ hV hcV
        exact ⟨m, hm.1, hm1, hzA m ⟨hVJ hm.1, hm.2⟩⟩)
    obtain ⟨w, hw, hzw⟩ := hZf z hz hz1
    exact hzw (hfixJ w hw)
  have hcA : c ∈ stabSub (J ⊓ fixV P) := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hcu
      refine ⟨?_, ?_⟩
      · have hmem : c u ∈ J.map c.toMonoidHom := by rw [hcJ]; exact hcu.1
        obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp hmem
        have h1 : u' = u := c.injective hu'eq
        rw [← h1]; exact hu'
      · refine mem_fixV.mpr ?_
        intro p hp
        have hcomm := congrArg (fun φ : MulAut W => φ (c u))
          ((Commute.inv_left (hcL p (hPL hp))).eq)
        simp only [MulAut.mul_apply] at hcomm
        have h1 : p (c u) = c u := mem_fixV.mp hcu.2 p hp
        calc p u = p (c⁻¹ (c u)) := by rw [mulAut_inv_apply_apply]
          _ = c⁻¹ (p (c u)) := hcomm.symm
          _ = c⁻¹ (c u) := by rw [h1]
          _ = u := mulAut_inv_apply_apply c u
    · intro hu
      refine ⟨?_, ?_⟩
      · have hmem : c u ∈ J.map c.toMonoidHom := Subgroup.mem_map_of_mem _ hu.1
        rwa [hcJ] at hmem
      · refine mem_fixV.mpr ?_
        intro p hp
        have hcomm := congrArg (fun φ : MulAut W => φ u) (hcL p (hPL hp))
        simp only [MulAut.mul_apply] at hcomm
        rw [← hcomm, mem_fixV.mp hu.2 p hp]
  have hfixA : ∀ a ∈ J ⊓ fixV P, c a = a :=
    s16c167_norm_two_element_fixes_of_normalizes_seven hW hAcard hZ hZA hZfA hck hcZ hcA
  exact s16c167_norm_fixes_natSum3_of_fixes_irr hJ hcL (fun V hVJ hV hcV => by
    obtain ⟨m, hm, hm1⟩ := hfixirr V hVJ hV hcV
    exact ⟨m, hm.1, hm1, hfixA m ⟨hVJ hm.1, hm.2⟩⟩)

theorem s16c167_norm_natSum3_two_element_inner (hW : ∀ w : W, w ^ 2 = 1)
    {L Z : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L) {J : Subgroup W} (hJ : NatSum3 L J)
    (hZ : Nat.card ↥Z = 7) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J) (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w)
    {x : MulAut W} {k : ℕ} (hx : x ^ 2 ^ k = 1) (hxZ : Z.map (MulAut.conj x).toMonoidHom = Z)
    (hxJ : J.map x.toMonoidHom = J) {l₀ : MulAut W} (hl₀ : l₀ ∈ L)
    (hcent : ∀ y ∈ L, (x * l₀⁻¹) * y = y * (x * l₀⁻¹)) :
    ∀ w ∈ J, x w = l₀ w := by
  have hcomml : Commute (x * l₀⁻¹) l₀ := hcent l₀ hl₀
  have hxsplit : x = (x * l₀⁻¹) * l₀ := by group
  have hcpow : (x * l₀⁻¹) ^ 2 ^ k = (l₀ ^ 2 ^ k)⁻¹ := by
    have h1 : ((x * l₀⁻¹) * l₀) ^ 2 ^ k = (x * l₀⁻¹) ^ 2 ^ k * l₀ ^ 2 ^ k :=
      hcomml.mul_pow (2 ^ k)
    rw [← hxsplit, hx] at h1
    exact mul_eq_one_iff_eq_inv.mp h1.symm
  have hmemL : (x * l₀⁻¹) ^ 2 ^ k ∈ L := by
    rw [hcpow]; exact L.inv_mem (L.pow_mem hl₀ (2 ^ k))
  have hcommL : ∀ y ∈ L, ((x * l₀⁻¹) ^ 2 ^ k) * y = y * ((x * l₀⁻¹) ^ 2 ^ k) := by
    intro y hy
    have hc : Commute (x * l₀⁻¹) y := hcent y hy
    exact (hc.pow_left (2 ^ k)).eq
  have hcpow1 : (x * l₀⁻¹) ^ 2 ^ k = 1 :=
    s16c167_norm_eq_one_of_commute hL hmemL hcommL
  have hconjZ : ∀ z ∈ Z, MulAut.conj (x * l₀⁻¹) z = MulAut.conj x z := by
    intro z hz
    have hcomm : l₀⁻¹ * (z : MulAut W) * l₀ = z := by
      have h1 : (z : MulAut W) * l₀ = l₀ * (z : MulAut W) := hZL z hz l₀ hl₀
      calc l₀⁻¹ * (z : MulAut W) * l₀ = l₀⁻¹ * ((z : MulAut W) * l₀) := by group
        _ = l₀⁻¹ * (l₀ * (z : MulAut W)) := by rw [h1]
        _ = z := by group
    simp only [MulAut.conj_apply]
    calc (x * l₀⁻¹) * (z : MulAut W) * (x * l₀⁻¹)⁻¹
        = x * (l₀⁻¹ * (z : MulAut W) * l₀) * x⁻¹ := by group
      _ = x * (z : MulAut W) * x⁻¹ := by rw [hcomm]
  have hmapZ : Z.map (MulAut.conj (x * l₀⁻¹)).toMonoidHom
      = Z.map (MulAut.conj x).toMonoidHom := by
    ext v
    constructor
    · intro hv
      obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hv
      refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
      rw [← hzv]
      change MulAut.conj x z = MulAut.conj (x * l₀⁻¹) z
      exact (hconjZ z hz).symm
    · intro hv
      obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hv
      refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
      rw [← hzv]
      change MulAut.conj (x * l₀⁻¹) z = MulAut.conj x z
      exact hconjZ z hz
  have hcZ' : Z.map (MulAut.conj (x * l₀⁻¹)).toMonoidHom = Z := by rw [hmapZ, hxZ]
  have hxJmem : ∀ w ∈ J, x w ∈ J := fun w hw => by
    have hmem : x w ∈ J.map x.toMonoidHom := Subgroup.mem_map_of_mem _ hw
    rwa [hxJ] at hmem
  have hxJinv : ∀ v ∈ J, x⁻¹ v ∈ J := by
    intro v hv
    have hmem : v ∈ J.map x.toMonoidHom := by rw [hxJ]; exact hv
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hmem
    have h1 : x⁻¹ v = u := by rw [← hux]; exact mulAut_inv_apply_apply x u
    rw [h1]; exact hu
  have hlJinv : ∀ w ∈ J, (l₀⁻¹ : MulAut W) w ∈ J :=
    s16c167_norm_natSum3_invariant hJ l₀⁻¹ (L.inv_mem hl₀)
  have hlJ : ∀ w ∈ J, l₀ w ∈ J := s16c167_norm_natSum3_invariant hJ l₀ hl₀
  have hcJ' : J.map (x * l₀⁻¹).toMonoidHom = J := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hv
      rw [← hwv]
      change x ((l₀⁻¹ : MulAut W) w) ∈ J
      exact hxJmem _ (hlJinv w hw)
    · intro hv
      refine Subgroup.mem_map.mpr ⟨l₀ (x⁻¹ v), hlJ _ (hxJinv v hv), ?_⟩
      change x ((l₀⁻¹ : MulAut W) (l₀ (x⁻¹ v))) = v
      rw [mulAut_inv_apply_apply, mulAut_apply_inv_apply]
  have hcfix : ∀ w ∈ J, (x * l₀⁻¹) w = w :=
    s16c167_norm_natSum3_centralizer_two_trivial hW hL hJ hZ hZL hZJ hZf
      hcpow1 hcent hcJ' hcZ'
  intro w hw
  have hxeq : x = (x * l₀⁻¹) * l₀ := by group
  rw [hxeq, MulAut.mul_apply]
  exact hcfix (l₀ w) (hlJ w hw)

theorem s16c167_norm_commute_of_agree {L Z : Subgroup (MulAut W)} {J : Subgroup W}
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) {x : MulAut W}
    (hxZ : Z.map (MulAut.conj x).toMonoidHom = Z) (hxJ : J.map x.toMonoidHom = J)
    {l : MulAut W} (hl : l ∈ L) (hxl : ∀ w ∈ J, x w = l w) : ∀ z ∈ Z, x * z = z * x := by
  intro z hz
  have hxJinv : ∀ v ∈ J, x⁻¹ v ∈ J := by
    intro v hv
    have hmem : v ∈ J.map x.toMonoidHom := by rw [hxJ]; exact hv
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hmem
    have h1 : x⁻¹ v = u := by rw [← hux]; exact mulAut_inv_apply_apply x u
    rw [h1]; exact hu
  have huZ : x * z * x⁻¹ ∈ Z := by
    have hmem : (MulAut.conj x).toMonoidHom z ∈ Z.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rw [hxZ] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hkey : ∀ w ∈ J, (x * z * x⁻¹) w = z w := by
    intro w hw
    have hvJ : x⁻¹ w ∈ J := hxJinv w hw
    have hzvJ : z (x⁻¹ w) ∈ J := hZJ z hz _ hvJ
    have h1 : x (z (x⁻¹ w)) = l (z (x⁻¹ w)) := hxl _ hzvJ
    have h2 : l (z (x⁻¹ w)) = z (l (x⁻¹ w)) := by
      have hc := congrArg (fun φ : MulAut W => φ (x⁻¹ w)) (hZL z hz l hl)
      simpa only [MulAut.mul_apply] using hc.symm
    have h3 : l (x⁻¹ w) = x (x⁻¹ w) := (hxl _ hvJ).symm
    calc (x * z * x⁻¹) w = x (z (x⁻¹ w)) := by simp only [MulAut.mul_apply]
      _ = l (z (x⁻¹ w)) := h1
      _ = z (l (x⁻¹ w)) := h2
      _ = z (x (x⁻¹ w)) := by rw [h3]
      _ = z w := by rw [mulAut_apply_inv_apply]
  have huz1 : (x * z * x⁻¹) * z⁻¹ = 1 := by
    by_contra hne
    obtain ⟨w, hw, hwne⟩ := hZf _ (Z.mul_mem huZ (Z.inv_mem hz)) hne
    apply hwne
    have hzwJ : z⁻¹ w ∈ J := hZJ z⁻¹ (Z.inv_mem hz) w hw
    calc ((x * z * x⁻¹) * z⁻¹) w = (x * z * x⁻¹) (z⁻¹ w) := by simp only [MulAut.mul_apply]
      _ = z (z⁻¹ w) := hkey _ hzwJ
      _ = w := mulAut_apply_inv_apply z w
  have hux : x * z * x⁻¹ = z := mul_inv_eq_one.mp huz1
  have hxzx : (x * z * x⁻¹) * x = z * x := congrArg (fun φ : MulAut W => φ * x) hux
  simpa [mul_assoc] using hxzx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
