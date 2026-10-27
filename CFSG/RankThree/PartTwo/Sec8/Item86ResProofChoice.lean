module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofKinds
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofAfter

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Elementary

variable {G : Type} [Group G]

theorem not_mem_zpowers_symm [Finite G] {b c : G} (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hb1 : b ≠ 1)
    (hc1 : c ≠ 1) (hbc : b ∉ Subgroup.zpowers c) : c ∉ Subgroup.zpowers b := by
  intro hcb
  apply hbc
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hle : Subgroup.zpowers c ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hcb
  have heq : Subgroup.zpowers c = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hob, hoc])
  rw [heq]
  exact Subgroup.mem_zpowers b

theorem zpowers_subset_sectionCentralizer {A X : Subgroup G} {b : G} (hbA : b ∈ A)
    (hX : X ≤ Subgroup.centralizer ({b} : Set G)) :
    (Subgroup.zpowers b : Set G) ⊆
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) := by
  rintro _ ⟨k, rfl⟩
  refine ⟨A.zpow_mem hbA k, fun y hy => ?_⟩
  have hby : b * y = y * b := (Subgroup.mem_centralizer_singleton_iff.mp (hX hy)).symm
  have hc : (fun j : ℤ => b ^ j) k * y = y * (fun j : ℤ => b ^ j) k :=
    (Commute.zpow_left hby k).eq
  rw [hc, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem sq_two_pow_mod_five {f : ℕ} (hf : Odd f) : (2 ^ f) ^ 2 % 5 = 4 := by
  obtain ⟨k, rfl⟩ := hf
  have h1 : (2 ^ (2 * k + 1)) ^ 2 = 4 * 16 ^ k := by
    rw [← pow_mul, show (2 * k + 1) * 2 = 2 + 4 * k by ring, pow_add, pow_mul]
    norm_num
  rw [h1, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_five_dvd_ordTrialityD4_ordG2 {q : ℕ} (hq : q ^ 2 % 5 = 4) :
    ¬ 5 ∣ Open.ordTrialityD4 q ∧ ¬ 5 ∣ Open.ordG2 q := by
  have h5 : Nat.Prime 5 := by norm_num
  have hpow : ∀ j : ℕ, q ^ (2 * j) % 5 = 4 ^ j % 5 := fun j => by rw [pow_mul, Nat.pow_mod, hq]
  have h4 : q ^ 4 % 5 = 1 := hpow 2
  have h6 : q ^ 6 % 5 = 4 := hpow 3
  have h8 : q ^ 8 % 5 = 1 := hpow 4
  have h12 : q ^ 12 % 5 = 1 := hpow 6
  have hq1 : ¬ 5 ∣ q ^ 2 - 1 := by omega
  have hq6 : ¬ 5 ∣ q ^ 6 - 1 := by omega
  have hq6' : ¬ 5 ∣ q ^ 6 := by omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Open.ordTrialityD4] at h
    rcases (Nat.Prime.dvd_mul h5).mp h with h | h
    · rcases (Nat.Prime.dvd_mul h5).mp h with h | h
      · rcases (Nat.Prime.dvd_mul h5).mp h with h | h
        · omega
        · omega
      · exact hq6 h
    · exact hq1 h
  · rw [Open.ordG2] at h
    rcases (Nat.Prime.dvd_mul h5).mp h with h | h
    · rcases (Nat.Prime.dvd_mul h5).mp h with h | h
      · exact hq6' h
      · exact hq6 h
    · exact hq1 h

end Elementary

@[expose] def Pair86Center : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) →
      PairRel A c L b X → (∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
      (∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
        Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) ⊆
          (Subgroup.zpowers b : Set G)

variable {G : Type} [Group G] [Finite G]

theorem not_isUnitaryTwo_of_isList86
    {X : Type} [Group X] {n : ℕ}
    (hn : 1 ≤ n) (h : IsList86 X n) (m : ℕ) : ¬ IsUnitaryTwo X m := by
  rcases h with hD | hG | hSp
  · exact (sigD4_of_isoTrialityD4 hn hD).not_isUnitaryTwo hn m
  · exact (sigG2_of_isoGTwo hn (isoGTwo_of_isoGTwoEven (by omega) hG)).not_isUnitaryTwo hn m
  · obtain ⟨e⟩ := hSp
    exact (sigSp4_of_projSp hn e).not_isUnitaryTwo hn m

theorem sec8PairGTwo_of_isUnitaryTwo
    {L : Subgroup G} {x : G}
    {n k : ℕ} (hn : 1 ≤ n) (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) k) :
    Sec8PairGTwo L x n := by
  rintro (hD | hG)
  · exact ((sigD4_of_isoTrialityD4 hn hD).not_isUnitaryTwo hn k hU).elim
  · exact ((sigG2_of_isoGTwo hn (isoGTwo_of_isoGTwoEven (by omega) hG)).not_isUnitaryTwo hn k
      hU).elim

theorem not_mem_zpowers_of_isGammaIndex
    {A L : Subgroup G} {c x : G} {m : ℕ}
    (hL : L ∈ thetaComponentsAt 3 c) (h : IsGammaIndex A L x m) : x ∉ Subgroup.zpowers c := by
  intro hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine false_of_isGammaIndex_of_centralizes h (Sec6.isPerfect_of_mem_thetaComponentsAt hL)
    (fun y hy => ?_)
  have hcy : c * y = y * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hL hy)).symm
  exact Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.zpow_left hcy k).eq).symm

theorem a_not_mem_zpowers {A L : Subgroup G} {c a : G} (h : Hyp81 G A c L a) :
    a ∉ Subgroup.zpowers c := by
  have ha := h.a_mem_normalizer
  have hcy := hyp81_commute_of_mem h
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcy y hy).symm)
  intro h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  apply h.not_isInnerAut_induced
  have hk' : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ k :=
    Subtype.ext (by simp [hk])
  rw [hk', map_zpow, map_zpow, KFacts.thetaQuotMulAut_compAction_eq_one hcN hcy, one_zpow]
  exact ⟨1, map_one _⟩

theorem mul_zpow_ne_one {A L : Subgroup G} {c a : G} (h : Hyp81 G A c L a) (k : ℤ) :
    a * c ^ k ≠ 1 := by
  intro h1
  apply a_not_mem_zpowers h
  rw [mul_eq_one_iff_eq_inv.mp h1, ← zpow_neg]
  exact Subgroup.zpow_mem_zpowers c (-k)

theorem exists_partTwoE_of_mem_pairOmega {A X : Subgroup G} {b : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA81 : Nat.card A = 81) (h : (b, X) ∈ pairOmega A) :
    ∃ E ∈ partTwoE G, E ≤ A ∧ ∃ U ∈ invariantPiSubgroups X E (piOf 2), U ≠ ⊥ := by
  obtain ⟨-, -, -, -, ⟨E₁, hE₁A, hcard, U, hU, hU1⟩, -⟩ := h
  refine ⟨E₁, ⟨isElemAbelian_of_le hA hE₁A, by omega, U, hU1,
    (isPiSubgroup_piOf_iff Nat.prime_two U).mp hU.2.1, hU.2.2⟩, hE₁A, U, hU, hU1⟩

theorem hyp81_of_partner {A L X : Subgroup G} {c a b : G} (h : Hyp81 G A c L a)
    (hA81 : Nat.card A = 81) (hbA : b ∈ A) (hb1 : b ≠ 1) (hX : X ∈ thetaComponentsAt 3 b)
    (hΩ : (b, X) ∈ pairOmega A)
    (hkind : KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField)
    (hC : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) ⊆
      (Subgroup.zpowers b : Set G)) : Hyp81 G A b X a where
  toPartTwoStanding := h.toPartTwoStanding
  mem_partTwoF := h.mem_partTwoF
  mem_A := hbA
  ne_one := hb1
  mem_thetaComponentsAt := hX
  sectionCentralizer_eq := subset_antisymm hC
    (zpowers_subset_sectionCentralizer hbA (Sec6.le_centralizer_of_mem_thetaComponentsAt hX))
  a_mem := h.a_mem
  a_ne_one := h.a_ne_one
  inducesStdKind := hkind
  exists_invariant_two := fun _ => exists_partTwoE_of_mem_pairOmega h.mem_partTwoF.1 hA81 hΩ
  partTwoE_eq := fun h27 => absurd (h27.symm.trans hA81) (by norm_num)

theorem isoSUThree_of_isGammaIndex_of_sigF4 {A L : Subgroup G} {b : G} {n : ℕ}
    (h : IsGammaIndex A L b n) (hF : SigF4 (L ⧸ aschbacherSolvableCore 3 L) n) :
    IsoSUThree (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) (2 ^ (3 * n)) := by
  have hn : 1 ≤ n := one_le_of_isGammaIndex h
  obtain ⟨-, -, -, ⟨-, -, -, -, hSU⟩ | ⟨htype, -⟩⟩ := h
  · exact hSU
  · exfalso
    rcases htype with hD | hG | hU | hS | hSp
    · exact hF.false_of_sigD4 (sigD4_of_isoTrialityD4 hn hD) hn
    · exact hF.false_of_sigG2 (sigG2_of_isoGTwo hn hG) hn
    · obtain ⟨e⟩ := hU
      exact hF.false_of_sigU (sigU_of_unitarySig (unitarySig_of_projSU (by omega) e)) hn
    · exact hF.false_of_sigU (sigU_of_unitarySig (unitarySig_of_isoSUThree (by omega) hS)) hn
    · obtain ⟨e⟩ := hSp
      exact hF.false_of_sigSp4 (sigSp4_of_projSp hn e) hn

theorem isGammaType_of_isList86 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (h : IsList86 X n) :
    IsGammaType X n := by
  rcases h with hD | hG | hSp
  · exact Or.inr (Or.inl hD)
  · exact Or.inr (Or.inr (Or.inl (isoGTwo_of_isoGTwoEven (by omega) hG)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSp))))

theorem one_le_of_isoTrialityD4_or_isoGTwoEven {X : Type} [Group X] {m : ℕ}
    (h : IsoTrialityD4 X m ∨ IsoGTwoEven X (3 * m)) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    rcases h with ⟨q, -, -, hqe, -⟩ | ⟨K, _, _, hK, -⟩
    · exact absurd hqe q.exponent_pos.ne'
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
  · exact hm

theorem isGammaType_of_isoTrialityD4_or_isoGTwoEven {X : Type} [Group X] {m : ℕ}
    (h : IsoTrialityD4 X m ∨ IsoGTwoEven X (3 * m)) : IsGammaType X m := by
  have hm := one_le_of_isoTrialityD4_or_isoGTwoEven h
  rcases h with hD | hG
  · exact Or.inr (Or.inl hD)
  · exact Or.inr (Or.inr (Or.inl (isoGTwo_of_isoGTwoEven (by omega) hG)))

theorem sec8PairGTwo_forall {X : Subgroup G} {x : G} {n : ℕ} (hn : 1 ≤ n)
    (ht : IsGammaType (X ⧸ aschbacherSolvableCore 3 X) n) (h : Sec8PairGTwo X x n) :
    ∀ m : ℕ, Sec8PairGTwo X x m := by
  intro m hm
  have hmn : m = n := eq_of_isGammaType (one_le_of_isoTrialityD4_or_isoGTwoEven hm) hn
    (isGammaType_of_isoTrialityD4_or_isoGTwoEven hm) ht
  subst hmn
  exact h hm

theorem sec8PairGTwo_forall_of_isList86 {X : Subgroup G} {x : G} {n : ℕ} (hn : 1 ≤ n)
    (hl : IsList86 (X ⧸ aschbacherSolvableCore 3 X) n)
    (hC : IsoGTwoEven (barCentralizer (Subgroup.zpowers x) X) n) :
    ∀ m : ℕ, Sec8PairGTwo X x m :=
  sec8PairGTwo_forall hn (isGammaType_of_isList86 hn hl) fun _ => hC

theorem false_of_projSp_barCentralizer {X : Subgroup G} {x : G} {n : ℕ} (hn : Odd n)
    (hX : IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) n ∨
      IsoGTwoEven (X ⧸ aschbacherSolvableCore 3 X) (3 * n))
    (hC : Nonempty (barCentralizer (Subgroup.zpowers x) X ≃* projSp 2 (GaloisField 2 n))) :
    False := by
  obtain ⟨e⟩ := hC
  have hn1 : 1 ≤ n := hn.pos
  have h16 : (2 ^ n) ^ 4 % 5 = 1 := by
    rw [← pow_mul, mul_comm n 4, pow_mul, Nat.pow_mod]
    norm_num
  have h5 : 5 ∣ (2 ^ n) ^ 4 - 1 := by omega
  have h5C : 5 ∣ Nat.card (barCentralizer (Subgroup.zpowers x) X) := by
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSp_two hn1]
    exact (h5.mul_left _).mul_left _
  have h5X : 5 ∣ Nat.card (X ⧸ aschbacherSolvableCore 3 X) :=
    h5C.trans (Subgroup.card_subgroup_dvd_card _)
  rcases hX with ⟨q, hv, hq2, hqe, ⟨eX⟩⟩ | hG
  · have hcard : Nat.card (X ⧸ aschbacherSolvableCore 3 X) = Open.ordTrialityD4 (2 ^ n) := by
      rw [Nat.card_congr eX.toEquiv, Sec11.KSListsProof.card_trialityD4_carrier,
        TauCeti.PrimePower.card_def, hq2, hqe]
    rw [hcard] at h5X
    exact (not_five_dvd_ordTrialityD4_ordG2 (sq_two_pow_mod_five hn)).1 h5X
  · have hcard := (sigG2_of_isoGTwo hn1 (isoGTwo_of_isoGTwoEven (by omega) hG)).card
    rw [hcard] at h5X
    exact (not_five_dvd_ordTrialityD4_ordG2
      (sq_two_pow_mod_five ((show Odd 3 by decide).mul hn))).2 h5X

theorem sec8PairGTwo_forall_of_projSp {X : Subgroup G} {x : G} {n : ℕ} (hn : Odd n)
    (hl : IsList86 (X ⧸ aschbacherSolvableCore 3 X) n)
    (hC : Nonempty (barCentralizer (Subgroup.zpowers x) X ≃* projSp 2 (GaloisField 2 n))) :
    ∀ m : ℕ, Sec8PairGTwo X x m := by
  intro m hm
  have hmn : m = n := eq_of_isGammaType (one_le_of_isoTrialityD4_or_isoGTwoEven hm) hn.pos
    (isGammaType_of_isoTrialityD4_or_isoGTwoEven hm) (isGammaType_of_isList86 hn.pos hl)
  subst hmn
  exact (false_of_projSp_barCentralizer hn hm hC).elim

theorem barCentralizer_zpowers_mul_zpow {L : Subgroup G} {x c : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hcL : ∀ y ∈ L, c * y = y * c) (k : ℤ) :
    barCentralizer (Subgroup.zpowers (x * c ^ k)) L = barCentralizer (Subgroup.zpowers x) L := by
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcL y hy).symm)
  have hxc : x * c ^ k ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hx (Subgroup.zpow_mem _ hcN k)
  ext y
  rw [KFacts.mem_barCentralizer_zpowers_iff hxc, KFacts.mem_barCentralizer_zpowers_iff hx,
    thetaQuotMulAut_mul_zpow_eq hx hcL k hxc]

theorem sec8PairGTwo_mul_zpow {A L : Subgroup G} {c a : G} {n : ℕ} (h : Hyp81 G A c L a)
    (hg : Sec8PairGTwo L a n) (k : ℤ) : Sec8PairGTwo L (a * c ^ k) n := by
  intro hL
  rw [barCentralizer_zpowers_mul_zpow h.a_mem_normalizer (hyp81_commute_of_mem h) k]
  exact hg hL

theorem projSL_of_isGammaIndex_of_isUnitaryTwo {A X : Subgroup G} {c : G} {n m : ℕ}
    (h : IsGammaIndex A X c n) (hU : IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) :
    Nonempty (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))) ≃*
        projSL 2 (GaloisField 2 (3 * n))) := by
  have hn : 1 ≤ n := one_le_of_isGammaIndex h
  obtain ⟨-, -, -, ⟨k, hk, hkn, he, -⟩ | ⟨-, hL2⟩⟩ := h
  · exact ((sigF4_of_reeF4 hn ⟨k, hk, hkn, he⟩).false_of_isUnitaryTwo hn hU).elim
  · exact hL2

@[expose] def Pair85Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → (∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
      ∃ b ∈ Subgroup.closure ({c, d} : Set G), b ≠ 1 ∧ ∃ X : Subgroup G, PairRel A c L b X

@[expose] def Pair86Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      ∃ b ∈ Subgroup.closure ({c, d} : Set G), b ∉ Subgroup.zpowers c ∧ ∃ X : Subgroup G,
        PairRel A c L b X ∧ IsList86 (X ⧸ aschbacherSolvableCore 3 X) n ∧
          (IsoGTwoEven (barCentralizer (Subgroup.zpowers a) X) n ∨
            (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
              IsoGTwoEven (barCentralizer (Subgroup.zpowers (a * c ^ ε)) X) n) ∨
            Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* projSp 2 (GaloisField 2 n)))

@[expose] def Pair86GTwoN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → (∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
      ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) → PairRel A c L b X →
        (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
          ∃ k : ℤ, ∀ m : ℕ, Sec8PairGTwo X (a * c ^ k) m

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
