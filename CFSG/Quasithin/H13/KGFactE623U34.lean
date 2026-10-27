module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.Goldschmidt.Steps.G36TypeI
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate113
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin.H13.KGE623

open CFSG.Assembly.LowTwoRank

theorem eq_one_of_psu34
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (hnab : ∃ x y : L, x * y ≠ y * x)
    (h : StatedClassicalModel L .PSU 3 2 2) {a b : L} (ha : a ^ 3 = 1) (hb : b ^ 2 = 1)
    (hb1 : b ≠ 1) (hab : a * b = b * a) : a = 1 := by
  classical
  by_contra ha1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * 2) := by rw [hK]; norm_num
  let eC : StatedProj (StatedSU 3 (2 ^ 2) K) ≃*
      CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ 2)) := MulEquiv.refl _
  let e : L ≃* CFSG.Open.PSU3 2 2 :=
    (e₀.trans eC).trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative 2 le_rfl hK')
  have hL : Nat.card L = 62400 := by
    have hc := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd (p := 2)
      (by norm_num)
    rw [Nat.card_congr e.toEquiv]
    norm_num at hc
    exact hc
  have hZ : Subgroup.center L = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot L hnab
  have hI : CFSG.Goldschmidt.IsGoldTypeI L :=
    Or.inr (Or.inr ⟨2, le_rfl,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩⟩)
  have hob : orderOf b = 2 := orderOf_eq_prime hb hb1
  have hbp : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hob, pow_one])
  obtain ⟨T, hT⟩ := hbp.exists_le_sylow
  have hbT : b ∈ (T : Subgroup L) := hT (Subgroup.mem_zpowers b)
  obtain ⟨D, hDN, -, -, -, -, -, -, hΩ, htr, -, -, -, hU, hTI, -, -, -, -⟩ :=
    CFSG.Goldschmidt.G32 L hI T
  obtain ⟨hZc, -, -⟩ := hU 2 le_rfl ⟨e⟩
  set Z := (T : Subgroup L) ⊓ Subgroup.centralizer ((T : Subgroup L) : Set L) with hZdef
  set N := Subgroup.normalizer ((T : Subgroup L) : Set L) with hNdef
  have hΩmem : ∀ z ∈ Z, z ∈ CFSG.Goldschmidt.Omega1 (T : Subgroup L) := fun z hz => by
    rw [hΩ]
    exact hz
  have hbZ : b ∈ Z := by
    rw [← hΩ]
    exact Subgroup.subset_closure ⟨hbT, hb⟩
  have haT : CFSG.Goldschmidt.conjSub a (T : Subgroup L) = T := by
    apply hTI a
    intro hbot
    have hmem : b ∈ (T : Subgroup L) ⊓ CFSG.Goldschmidt.conjSub a (T : Subgroup L) := by
      refine ⟨hbT, CFSG.Goldschmidt.mem_conjSub.mpr ?_⟩
      have hb' : a * b * a⁻¹ = b := by rw [hab]; group
      rw [hb']
      exact hbT
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hb1 hmem
  have haN : a ∈ N := by
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have h1 : t ∈ CFSG.Goldschmidt.conjSub a (T : Subgroup L) := by rw [haT]; exact ht
      exact CFSG.Goldschmidt.mem_conjSub.mp h1
    · intro ht
      rw [← haT]
      exact CFSG.Goldschmidt.mem_conjSub.mpr ht
  have hZN : Z ≤ N := fun z hz => Subgroup.le_normalizer hz.1
  have hNZ : N ≤ Subgroup.normalizer (Z : Set L) :=
    CFSG.Goldschmidt.normalizer_le_normalizer_inf_centralizer (T : Subgroup L)
  set b' : N := ⟨b, hZN hbZ⟩ with hb'
  have hto : ∀ s : N, IsConj s b' → (s : L) ∈ Z ∧ (s : L) ≠ 1 := by
    intro s hs
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_comm.mp hs)
    have hs' : (s : L) = (c : L) * b * (c : L)⁻¹ := by rw [← hc]; rfl
    refine ⟨?_, ?_⟩
    · rw [hs']
      exact (Subgroup.mem_normalizer_iff.mp (hNZ c.2) b).mp hbZ
    · rw [hs']
      intro h1
      apply hb1
      calc b = (c : L)⁻¹ * ((c : L) * b * (c : L)⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
  have hfrom : ∀ z : Z, z ≠ 1 → IsConj (⟨z, hZN z.2⟩ : N) b' := by
    intro z hz1
    have hz1' : (z : L) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
    obtain ⟨d, hd, hdz⟩ := htr b (hΩmem b hbZ) z (hΩmem z z.2) hb1 hz1'
    refine isConj_iff.mpr ⟨⟨d, hDN hd⟩, Subtype.ext ?_⟩
    show d * (z : L) * d⁻¹ = b
    rw [← hdz]
    group
  let f : {s : N // IsConj s b'} → {z : Z // z ≠ 1} := fun s =>
    ⟨⟨s.1, (hto s.1 s.2).1⟩, fun h1 => (hto s.1 s.2).2 (congrArg Subtype.val h1)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s s' hss' => ?_, fun z => ⟨⟨⟨z.1, hZN z.1.2⟩, hfrom z.1 z.2⟩, rfl⟩⟩
    have h1 : ((s.1 : N) : L) = ((s'.1 : N) : L) := congrArg (fun w : {z : Z // z ≠ 1} =>
      ((w.1 : Z) : L)) hss'
    exact Subtype.ext (Subtype.ext h1)
  have hZ3 : Nat.card {z : Z // z ≠ 1} = 3 := by
    have : Fintype Z := Fintype.ofFinite Z
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hZc]
    norm_num
  have hclass : Nat.card {s : N // IsConj s b'} = 3 := by
    rw [Nat.card_eq_of_bijective f hf, hZ3]
  have hceq : Nat.card (ConjClasses.mk b').carrier *
      Nat.card (Subgroup.centralizer ({b'} : Set N)) = Nat.card N := by
    rw [← ConjAct.orbit_eq_carrier_conjClasses, Subgroup.nat_card_centralizer_nat_card_stabilizer,
      Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
    exact Nat.card_congr ConjAct.ofConjAct.toEquiv
  have hcar : Nat.card (ConjClasses.mk b').carrier = Nat.card {s : N // IsConj s b'} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj])
  rw [hcar, hclass] at hceq
  have hoa : orderOf a = 3 := orderOf_eq_prime ha ha1
  have haC : (⟨a, haN⟩ : N) ∈ Subgroup.centralizer ({b'} : Set N) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hab
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({b'} : Set N)) := by
    have h1 := orderOf_dvd_natCard (⟨⟨a, haN⟩, haC⟩ : Subgroup.centralizer ({b'} : Set N))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hoa] at h1
  obtain ⟨m, hm⟩ := h3
  have h9 : 9 ∣ Nat.card L := by
    have h1 : Nat.card N ∣ Nat.card L := Subgroup.card_subgroup_dvd_card N
    rw [← hceq, hm] at h1
    exact (Dvd.intro m (by ring)).trans h1
  rw [hL] at h9
  norm_num at h9

end CFSG.Quasithin.H13.KGE623
