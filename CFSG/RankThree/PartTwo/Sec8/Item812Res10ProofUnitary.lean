module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofBNotCent
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofCent
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU projSL)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace Item812Res10

theorem false_of_dvd_unitary {q k : ℕ} (hq : 4 ≤ q) (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (h : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ∣ k * (q ^ 3 * ((q ^ 3) ^ 2 - 1))) : False := by
  have hq1 : 1 ≤ q := by omega
  have e1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [Nat.one_le_pow 2 q hq1, hq1]
    ring
  have e2 : (q ^ 3) ^ 2 - 1 = (q - 1) * (q ^ 2 + q + 1) * (q ^ 3 + 1) := by
    have : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    zify [this, hq1]
    ring
  rw [e1, e2] at h
  have hA : 0 < q ^ 3 * (q - 1) * (q ^ 3 + 1) := by
    have : 0 < q - 1 := by omega
    positivity
  have h' : q ^ 3 * (q - 1) * (q ^ 3 + 1) * (q + 1) ∣
      q ^ 3 * (q - 1) * (q ^ 3 + 1) * (k * (q ^ 2 + q + 1)) := by
    have e3 : q ^ 3 * ((q - 1) * (q + 1)) * (q ^ 3 + 1) =
        q ^ 3 * (q - 1) * (q ^ 3 + 1) * (q + 1) := by ring
    have e4 : k * (q ^ 3 * ((q - 1) * (q ^ 2 + q + 1) * (q ^ 3 + 1))) =
        q ^ 3 * (q - 1) * (q ^ 3 + 1) * (k * (q ^ 2 + q + 1)) := by ring
    rw [← e3, ← e4]
    exact h
  have h2 := Nat.dvd_of_mul_dvd_mul_left hA h'
  have hcop : Nat.Coprime (q + 1) (q ^ 2 + q + 1) := by
    have e5 : q ^ 2 + q + 1 = 1 + q * (q + 1) := by ring
    rw [e5, Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right _
  have h3 : q + 1 ∣ k := (Nat.Coprime.dvd_mul_right hcop).mp h2
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem noThetaNormal_of_isSimpleGroup_of_isPerfect {S : Type*} [Group S] [IsSimpleGroup S]
    (hP : Group.IsPerfect S) : NoThetaNormal S := by
  intro N hN hNs _
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    subst h
    have hs : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup S).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    have : Nontrivial S := IsSimpleGroup.toNontrivial
    exact Group.IsPerfect.not_isSolvable S hs

variable {X : Type} [Group X]

theorem noThetaNormal_perfectResidual_of_isoPGUThree {m : ℕ} (hm : 2 ≤ m)
    (h : IsoPGUThree X (2 ^ m)) : NoThetaNormal (perfectResidual X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hPi : Sec4.PiField false 2 m K := ⟨Nat.prime_two, by omega, hK⟩
  have hq2 : 2 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hU := hPi.unitary
  have hSP : projImage (Sec4.slPi false 3 (2 ^ m) K) ≤ projImage (Sec4.glPi false 3 (2 ^ m) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hU))
  have hs := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hPi hq2
  have hperf : Group.IsPerfect (projImage (Sec4.slPi false 3 (2 ^ m) K)) :=
    Sec13.isPerfect_projImage_slPi hPi hq2
  have hθ := noThetaNormal_of_isSimpleGroup_of_isPerfect hperf
  refine Item87Proof.NoThetaNormal.of_mulEquiv
    ((Item8KFacts2Proof.perfectResidualEquivOfMulEquiv e).trans
      ((MulEquiv.subgroupCongr (Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hPi hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP))) hθ

theorem exists_card_eq_mul_card_perfectResidual {m : ℕ} (hm : 2 ≤ m)
    (h : IsoPGUThree X (2 ^ m)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ Nat.card X = k * Nat.card (perfectResidual X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hPi : Sec4.PiField false 2 m K := ⟨Nat.prime_two, by omega, hK⟩
  have hq2 : 2 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hU := hPi.unitary
  have hSP : projImage (Sec4.slPi false 3 (2 ^ m) K) ≤ projImage (Sec4.glPi false 3 (2 ^ m) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hU))
  have e1 : perfectResidual X ≃* projImage (Sec4.slPi false 3 (2 ^ m) K) :=
    (Item8KFacts2Proof.perfectResidualEquivOfMulEquiv e).trans
      ((MulEquiv.subgroupCongr (Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hPi hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP))
  have hX : Nat.card X = Nat.card (Sec4.slPi false 3 (2 ^ m) K) := by
    rw [Nat.card_congr e.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hPi]
  have hmul := KFacts.card_slPi_eq_mul (Sec4.slPi false 3 (2 ^ m) K)
  have hle := KFacts.card_ker_mk_slPi_le hU
  refine ⟨Nat.card ((Matrix.ProjGenLinGroup.mk.comp (Sec4.slPi false 3 (2 ^ m) K).subtype).ker),
    Nat.card_pos, hle, ?_⟩
  rw [hX, hmul, Nat.card_congr e1.toEquiv]

theorem eq_of_isUnitaryTwo {Y : Type} [Group Y] {g g' : ℕ} (hg : 1 ≤ g) (hg' : 1 ≤ g')
    (h : IsUnitaryTwo Y g) (h' : IsUnitaryTwo Y g') : g = g' := by
  have hs : ∀ {k : ℕ}, 1 ≤ k → IsUnitaryTwo Y k → Item86ResProof.UnitarySig Y k := by
    intro k hk hY
    rcases hY with ⟨⟨e⟩⟩ | hS
    · exact Item86ResProof.unitarySig_of_projSU hk e
    · exact Item86ResProof.unitarySig_of_isoSUThree hk hS
  have := ((hs hg h).profile.transfer (hs hg' h').profile).1
  omega

end Item812Res10


@[expose] def KF89BNotCentIU38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 →
    ∃ i ∈ sec8I L a, b * i * b⁻¹ * i⁻¹ ∉
      ((aschbacherSolvableCore 3 ↥(sec8I L a)).map (sec8I L a).subtype : Subgroup G)

namespace Item812Res10

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}

theorem isoPGUThree_barCentralizer_of_projSU {m : ℕ} (hm : 2 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * m)) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    IsoPGUThree (barCentralizer (Subgroup.zpowers x) L) (2 ^ m) := by
  have hout : InducesOuterTheta x L := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
  have h3m : 1 ≤ 3 * m := by omega
  have hU := unitaryFieldData_galoisField 2 (3 * m) h3m
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  rcases Nat.even_or_odd m with hme | hmo
  · have hme3 : Even (3 * m) := hme.mul_left 3
    have hq := Item82OneProof.two_pow_mod_three_of_even hme3
    set E := e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)
    rcases KFacts.inducesKindPSU3_diagonal_or_field (h := hU) L hq2 hx3 hout E with hd | hf
    · exact (false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd hx3).elim
    · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq2 hx3 ⟨E, hf⟩
      obtain rfl : f₀ = m := by omega
      exact hC
  · have hmo3 : Odd (3 * m) := Nat.odd_mul.mpr ⟨by decide, hmo⟩
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd (e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)).symm
        (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
        CFSG.Open.ordTwistedA 2 (2 ^ (3 * m)) :=
      (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
    have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * m) e₁
    rcases hk with hk | hk
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
        ⟨K, _, hK, hq, hkK⟩ | hO
      · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq hx3 hkK
        obtain rfl : f₀ = m := by omega
        exact hC
      · exact (hodd hO).elim
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
        ⟨K, _, hK, -, hkK⟩ | hO
      · exact (KFacts.not_inducesKindPSU3_graphField hK hkK).elim
      · exact (hodd hO).elim

theorem barCentralizer_of_isUnitaryTwo {m : ℕ} (hm : 2 ≤ m)
    (hL : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * m)) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    IsoPGUThree (barCentralizer (Subgroup.zpowers x) L) (2 ^ m) ∨
      IsoSUThree (barCentralizer (Subgroup.zpowers x) L) (2 ^ m) := by
  rcases hL with ⟨⟨e₁⟩⟩ | hS
  · exact Or.inl (isoPGUThree_barCentralizer_of_projSU hm e₁ hx3 hk)
  · rcases Nat.even_or_odd m with hme | hmo
    · obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hS
      obtain ⟨e₂⟩ := Item82OneProof.nonempty_statedSU_mulEquiv_projSU (by omega : 1 ≤ 3 * m)
        (Item82OneProof.two_pow_mod_three_of_even (hme.mul_left 3)) hK
      exact Or.inl (isoPGUThree_barCentralizer_of_projSU hm (e₁.trans e₂) hx3 hk)
    · rcases hk with hk | hk
      · exact Or.inr (KFacts.isoSUThree_barCentralizer_of_inducesStdKind hmo hS hx3 hk)
      · exact (KFacts.not_inducesStdKind_graphField_of_isoSUThree (by omega)
          (KFacts.three_dvd_two_pow_three_mul_add_one hmo) hS hk).elim

end Item812Res10

open Item812Res10


theorem kF89BNotCentIUnitary_of
    (h45 : Sec4.Item4_5) (hU38 : KF89BNotCentIU38) :
    KF89BNotCentIUnitary := by
  intro G _ _ A c L a b X n h hun
  classical
  by_cases h3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3
  · exact hU38 G A c L a b X n h h3
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, h3, ↓reduceIte]
  by_contra hall
  push Not at hall
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAab.2 c hcA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAcC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 hc1 hAp hAcC L
      h.mem_thetaComponentsAt
  have haN := hAL haA
  have hbN := hAL hbA
  have hIL : sec8I L a ≤ L := (Item812Res7.sec8I_le L a).trans inf_le_left
  have hIimg : imageModTheta L (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) := by
    rw [hIdef]
    exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩
  have hn1 : 1 ≤ n := h.isGammaIndex.2.2.1
  obtain ⟨m, hm⟩ := hun
  have hU3n := isUnitaryTwo_three_mul_of_isGammaIndex h.isGammaIndex hm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    exact h3 (by rwa [show n = 1 by omega] at hU3n)
  obtain ⟨ι⟩ := Item86ResProof.projSL_of_isGammaIndex_of_isUnitaryTwo h.isGammaIndex hm
  have hN : Nat.card (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) =
      2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) :=
    (Nat.card_congr ι.toEquiv).trans (Item87Proof.card_projSL_two_three hn1)
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have h3n : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm, pow_mul]
  rcases barCentralizer_of_isUnitaryTwo hn2 hU3n ha3 h.inducesStdKind with hP | hS
  ·
    refine Item812Res8.false_of_trivial_of_card hIL hbN hb3 hIimg
      (noThetaNormal_perfectResidual_of_isoPGUThree hn2 hP) hall hN ?_
    intro hd
    obtain ⟨k, hk1, hk3, hk⟩ := exists_card_eq_mul_card_perfectResidual hn2 hP
    have hC := Item812Res8.card_of_isoPGUThree hn1 hP
    refine false_of_dvd_unitary hq4 hk1 hk3 ?_
    rw [← hC, hk, ← h3n]
    exact Nat.mul_dvd_mul_left k hd
  ·
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hS
    obtain ⟨hq, -⟩ := Item87Proof.isQuasisimple_statedSU_three hK hn2
    have := hq.1
    have hperf : Group.IsPerfect (barCentralizer (Subgroup.zpowers a) L) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have htop := KFacts.perfectResidual_eq_top_of_isPerfect hperf
    have eP : perfectResidual (barCentralizer (Subgroup.zpowers a) L) ≃*
        CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K :=
      (MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans e)
    refine Item812Res8.false_of_trivial_of_card hIL hbN hb3 hIimg
      (Item87Proof.NoThetaNormal.of_mulEquiv eP (Item87Proof.noThetaNormal_statedSU hK hn2))
      hall hN ?_
    intro hd
    have hC := Item812Res8.card_of_isoSUThree ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩
    have hCP : Nat.card (barCentralizer (Subgroup.zpowers a) L) =
        Nat.card (perfectResidual (barCentralizer (Subgroup.zpowers a) L)) := by
      rw [htop, Subgroup.card_top]
    refine false_of_dvd_unitary hq4 le_rfl (by norm_num) ?_
    rw [one_mul, ← hC, hCP, ← h3n]
    exact hd

end CFSG.RankThree.PartTwo.Sec8
