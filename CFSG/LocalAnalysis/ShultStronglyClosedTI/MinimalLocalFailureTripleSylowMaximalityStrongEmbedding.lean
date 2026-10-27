module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityActions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Lemma73
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem2

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {G : Type u} [Group G]

theorem sylow_conj [Finite G] {p : ℕ} (hp : p.Prime)
    {P D : Subgroup G} (hP : theorem4bIsSylowSubgroupOf p P D) (g : G) :
    theorem4bIsSylowSubgroupOf p (P.conjBy g) (D.conjBy g) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨PD, hPD⟩ := hP
  let e : D ≃* D.conjBy g := MulEquiv.subgroupMap (MulAut.conj g) D
  let Q : Sylow p (D.conjBy g) := PD.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q, ?_⟩
  rw [hPD]
  change ((PD : Subgroup D).map D.subtype).map (MulAut.conj g).toMonoidHom =
    ((PD : Subgroup D).map e.toMonoidHom).map (D.conjBy g).subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem ambient_sylows_conjugate [Finite G] {p : ℕ} (hp : p.Prime)
    {P Q D : Subgroup G} (hP : theorem4bIsSylowSubgroupOf p P D)
    (hQ : theorem4bIsSylowSubgroupOf p Q D) :
    ∃ d : D, P.conjBy (d : G) = Q := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨PD, hPD⟩ := hP
  obtain ⟨QD, hQD⟩ := hQ
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D PD QD
  refine ⟨d, ?_⟩
  rw [hPD, hQD, ← hd]
  change ((PD : Subgroup D).map D.subtype).map (MulAut.conj (d : G)).toMonoidHom =
    ((PD : Subgroup D).map (MulAut.conj d).toMonoidHom).map D.subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem three_le_fixed_card {Ω : Type v} [MulAction G Ω] [Finite Ω]
    (P : Subgroup G) {a b c : Ω}
    (ha : P ≤ MulAction.stabilizer G a) (hb : P ≤ MulAction.stabilizer G b)
    (hc : P ≤ MulAction.stabilizer G c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} := by
  let A : {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} :=
    ⟨a, fun x hx => MulAction.mem_stabilizer_iff.mp (ha hx)⟩
  let B : {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} :=
    ⟨b, fun x hx => MulAction.mem_stabilizer_iff.mp (hb hx)⟩
  let C : {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} :=
    ⟨c, fun x hx => MulAction.mem_stabilizer_iff.mp (hc hx)⟩
  let := Fintype.ofFinite {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P}
  rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
  exact ⟨A, B, C, fun h => hab (congrArg Subtype.val h),
    fun h => hac (congrArg Subtype.val h), fun h => hbc (congrArg Subtype.val h)⟩

variable [Finite G]

theorem stronglyEmbedded_triple_sylow_three_fixed
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {z : G}
    (hzH : z ∈ H) (hz : IsInvolution z)
    {beta : conjugateCosetSpace H}
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace H))
    {p : ℕ} {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P (theorem4bSection7E H z beta)) :
    2 < Nat.card (theorem4bFixedPoints H P) := by
  let alpha : conjugateCosetSpace H := QuotientGroup.mk 1
  have hzalpha : z • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [alpha, baseCoset_stabilizer] using hzH
  have hPE := theorem4bIsSylowSubgroupOf_le_section7 hP
  have hPa : P ≤ MulAction.stabilizer G alpha := by
    simpa [alpha, baseCoset_stabilizer] using hPE.trans
      (show theorem4bSection7E H z beta ≤ H from inf_le_left.trans inf_le_left)
  have hPb : P ≤ MulAction.stabilizer G beta := hPE.trans
    (show theorem4bSection7E H z beta ≤ MulAction.stabilizer G beta from
      inf_le_left.trans inf_le_right)
  have hPc : P ≤ MulAction.stabilizer G (z • beta) := hPE.trans inf_le_right
  have hbc : beta ≠ z • beta := by
    intro h
    exact hbeta ((hH.involution_fixed_coset_unique hz).unique h.symm hzalpha)
  have hac : alpha ≠ z • beta := by
    intro h
    exact hbeta ((MulAction.injective z) (h.symm.trans hzalpha.symm))
  exact three_le_fixed_card P hPa hPb hPc hbeta.symm hac hbc

theorem stronglyEmbedded_maximal_three_fixed_conjugate_to_triple_sylow
    {H : Subgroup G} (hH : IsStronglyEmbedded H)
    (htwo : MulAction.IsMultiplyPretransitive G (conjugateCosetSpace H) 2)
    {z : G} (hzH : z ∈ H) (hz : IsInvolution z)
    {beta : conjugateCosetSpace H}
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace H))
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {P Q : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P (theorem4bSection7E H z beta))
    (hQ : Maximal (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card (theorem4bFixedPoints H R)) Q) :
    ∃ g : G, Q.conjBy g = P := by
  classical
  let := Fintype.ofFinite (theorem4bFixedPoints H Q)
  obtain ⟨a, b, _c, hab, _hac, _hbc⟩ :=
    (Fintype.two_lt_card_iff (α := theorem4bFixedPoints H Q)).mp
      (by simpa only [Nat.card_eq_fintype_card] using hQ.1.2)
  let gamma : conjugateCosetSpace H := a
  let delta : conjugateCosetSpace H := b
  have hgd : gamma ≠ delta := fun h => hab (Subtype.ext h)
  obtain ⟨s, _hsset, hs, hsN, hsgamma⟩ :=
    proposition_5_3_normalizer_involution hH hp hpodd htwo hQ a.property
  let T : Subgroup G :=
    (MulAction.stabilizer G gamma ⊓ MulAction.stabilizer G delta) ⊓
      MulAction.stabilizer G (s • delta)
  have hQT : Q ≤ T := by
    intro q hq
    exact ⟨⟨MulAction.mem_stabilizer_iff.mpr (a.property q hq),
      MulAction.mem_stabilizer_iff.mpr (b.property q hq)⟩,
      MulAction.mem_stabilizer_iff.mpr
        (fixedPoints_smul_of_mem_normalizer hsN b.property q hq)⟩
  have hsdelta : delta ≠ s • delta := by
    intro h
    exact hgd ((hH.involution_fixed_coset_unique hs).unique hsgamma h.symm)
  have hgsdelta : gamma ≠ s • delta := by
    intro h
    exact hgd (MulAction.injective s (hsgamma.trans h))
  have hQTsyl : theorem4bIsSylowSubgroupOf p Q T := by
    refine ⟨{ toSubgroup := Q.subgroupOf T
              isPGroup' := hQ.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQT).symm
              is_maximal' := ?_ }, ?_⟩
    · intro R hRp hQR
      let V : Subgroup G := R.map T.subtype
      have hQV : Q ≤ V := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hQT]
        exact Subgroup.map_mono hQR
      have hVT : V ≤ T := Subgroup.map_subtype_le R
      have hVthree : 2 < Nat.card (theorem4bFixedPoints H V) :=
        three_le_fixed_card V (hVT.trans (inf_le_left.trans inf_le_left))
          (hVT.trans (inf_le_left.trans inf_le_right)) (hVT.trans inf_le_right)
          hgd hgsdelta hsdelta
      have hVQ : V ≤ Q := hQ.2 ⟨hRp.map T.subtype, hVthree⟩ hQV
      apply le_antisymm
      · intro x hx
        exact hVQ (Subgroup.mem_map_of_mem T.subtype hx)
      · exact hQR
    · exact (Subgroup.map_subgroupOf_eq_of_le hQT).symm
  obtain ⟨g, hggamma, hgdelta, hsg⟩ :=
    lemma73_triple_transport hH htwo hzH hz hs hsgamma hgd hbeta
  have hTE : T.conjBy g = theorem4bSection7E H z beta :=
    lemma73_tripleStabilizer_conjBy_eq_E hggamma hgdelta hsg
  have hQg : theorem4bIsSylowSubgroupOf p (Q.conjBy g)
      (theorem4bSection7E H z beta) := by
    rw [← hTE]
    exact sylow_conj hp hQTsyl g
  obtain ⟨d, hd⟩ := ambient_sylows_conjugate hp hQg hP
  exact ⟨(d : G) * g, by rw [← Subgroup.conjBy_conjBy, hd]⟩

theorem stronglyEmbedded_base_triple_sylow_maximality_and_conjugacy
    {H : Subgroup G} (hH : IsStronglyEmbedded H)
    (htwo : MulAction.IsMultiplyPretransitive G (conjugateCosetSpace H) 2)
    {z : G} (hzH : z ∈ H) (hz : IsInvolution z)
    {beta : conjugateCosetSpace H}
    (hbeta : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace H))
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P (theorem4bSection7E H z beta)) :
    Maximal (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card (theorem4bFixedPoints H R)) P ∧
      ∀ Q : Subgroup G, Maximal (fun R : Subgroup G => IsPGroup p R ∧
        2 < Nat.card (theorem4bFixedPoints H R)) Q → ∃ g : G, Q.conjBy g = P := by
  have hPp : IsPGroup p P := by
    obtain ⟨S, hS⟩ := hP
    rw [hS]
    exact S.isPGroup'.map _
  have hPthree := stronglyEmbedded_triple_sylow_three_fixed hH hzH hz hbeta hP
  obtain ⟨Q, _hPQ, hQ⟩ := exists_maximal_three_fixed_overgroup
    (Ω := conjugateCosetSpace H) p P hPp hPthree
  obtain ⟨g, hg⟩ := stronglyEmbedded_maximal_three_fixed_conjugate_to_triple_sylow
    hH htwo hzH hz hbeta hp hpodd hP hQ
  refine ⟨?_, fun Q hQ =>
    stronglyEmbedded_maximal_three_fixed_conjugate_to_triple_sylow
      hH htwo hzH hz hbeta hp hpodd hP hQ⟩
  rw [← hg]
  exact maximal_three_fixed_conj (Ω := conjugateCosetSpace H) p Q g hQ

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
