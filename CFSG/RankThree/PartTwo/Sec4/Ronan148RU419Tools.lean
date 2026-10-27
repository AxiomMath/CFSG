module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Transfer
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieType
public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofUnitary
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)

variable {X : Type} [Group X]

theorem exists_e9_of_cfg [Finite X] {α : MulAut X} {Y : Subgroup X} {m : ℕ}
    (hc : CfgU419 X α Y m) :
    ∃ E : Subgroup X, E ≤ Y ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 3 = 1) ∧
      Nat.card E = 9 ∧ ∀ z ∈ E, (∀ k ∈ Y, z * k = k * z) → z = 1 := by
  obtain ⟨π, hπ, hker⟩ := hc.cover
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN3 : ¬ 3 ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hker.symm
  set eQ : Y ⧸ π.ker ≃* projSU 3 2 m := QuotientGroup.quotientKerEquivOfSurjective π hπ
  obtain ⟨E', hE', h9'⟩ := Sec15.exists_e9_of_isLThreePi (X := Y ⧸ π.ker)
    ⟨2, m, inferInstance, by have := hc.one_lt; omega,
      Or.inr ⟨two_pow_mod_three_of_odd hc.odd, ⟨eQ⟩⟩⟩
  obtain ⟨P, -, hP9, hPN, hP⟩ := RonanK429Lie.exists_e9_lift π.ker hN3 hE' h9'
  refine ⟨P.map Y.subtype, Subgroup.map_subtype_le P, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val)
  · rintro _ ⟨a, ha, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, hP.2 a ha, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hP9]
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have hx1 : π x = 1 := eq_one_of_central π hπ (center_projSU_three_two hc.odd hc.one_lt)
      (fun k => Subtype.ext (hcomm k k.2))
    have hxN : x ∈ P ⊓ π.ker := ⟨hx, hx1⟩
    rw [hPN, Subgroup.mem_bot] at hxN
    rw [hxN]
    rfl

theorem card_le_nine_of_noE27 {T : Type*} [Group T] [Finite T]
    (hN : ∀ E : Subgroup T, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27) {B : Subgroup T}
    (h3 : ∀ b ∈ B, b ^ 3 = 1) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  have hp : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using h3 _ x.2)⟩
  obtain ⟨j, hj⟩ := hp.exists_card_eq
  have hj3 : 3 ≤ j := by
    by_contra hj3
    push Not at hj3
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 3 ∣ Nat.card B from hj ▸ Nat.pow_dvd_pow 3 hj3)
  refine hN (E₀.map B.subtype) ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩ ?_
  · obtain ⟨_, ⟨a, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨b, -, rfl⟩⟩ := b
    exact hc _ a.2 _ b.2
  · rintro _ ⟨a, -, rfl⟩
    exact h3 _ a.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective B), hE₀]
    norm_num

theorem card_dvd_of_cfg [Finite X] {α : MulAut X} {Y : Subgroup X} {m : ℕ}
    (hc : CfgU419 X α Y m) : Nat.card (projSU 3 2 m) ∣ Nat.card X := by
  obtain ⟨π, hπ, -⟩ := hc.cover
  refine Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card Y)
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem dvd_facts_of_card {m M : ℕ} (hm : Odd m) (hm1 : 1 < m)
    (hM : Nat.card (projSU 3 2 m) ∣ M) :
    2 ^ 9 ∣ M ∧ (19 ∣ M ∨ 2 ^ 15 ∣ M) ∧ (19 ∣ M ∨ 11 ∣ M ∨ 2 ^ 21 ∣ M) := by
  have h2 := (Item419Res3.two_pow_dvd_card_projSU_three_two hm).trans hM
  have hm3 : 3 ≤ m := by obtain ⟨j, rfl⟩ := hm; omega
  refine ⟨(pow_dvd_pow 2 (by omega)).trans h2, ?_, ?_⟩
  · rcases (show m = 3 ∨ 5 ≤ m by obtain ⟨j, rfl⟩ := hm; omega) with rfl | h5
    · left
      rw [Item419Res3.card_projSU_three_two_three] at hM
      exact (show (19 : ℕ) ∣ 5515776 by norm_num).trans hM
    · exact Or.inr ((pow_dvd_pow 2 (by omega)).trans h2)
  · rcases (show m = 3 ∨ m = 5 ∨ 7 ≤ m by obtain ⟨j, rfl⟩ := hm; omega) with rfl | rfl | h7
    · left
      rw [Item419Res3.card_projSU_three_two_three] at hM
      exact (show (19 : ℕ) ∣ 5515776 by norm_num).trans hM
    · exact Or.inr (Or.inl (Item419Res3.eleven_dvd_card_projSU_three_two_five.trans hM))
    · exact Or.inr (Or.inr ((pow_dvd_pow 2 (by omega)).trans h2))

theorem noCfgU419_of_two_pow_nine [Finite X] {M : ℕ} (hM : Nat.card X ∣ M) (h9 : ¬ 2 ^ 9 ∣ M) :
    NoCfgU419 X := fun _ _ _ hc =>
  h9 (dvd_facts_of_card hc.odd hc.one_lt ((card_dvd_of_cfg hc).trans hM)).1

theorem noCfgU419_of_two_pow_fifteen [Finite X] {M : ℕ} (hM : Nat.card X ∣ M)
    (h19 : ¬ 19 ∣ M) (h15 : ¬ 2 ^ 15 ∣ M) : NoCfgU419 X := fun _ _ _ hc => by
  rcases (dvd_facts_of_card hc.odd hc.one_lt ((card_dvd_of_cfg hc).trans hM)).2.1 with h | h
  · exact h19 h
  · exact h15 h

theorem noCfgU419_of_two_pow_twentyone [Finite X] {M : ℕ} (hM : Nat.card X ∣ M)
    (h19 : ¬ 19 ∣ M) (h11 : ¬ 11 ∣ M) (h21 : ¬ 2 ^ 21 ∣ M) : NoCfgU419 X := fun _ _ _ hc => by
  rcases (dvd_facts_of_card hc.odd hc.one_lt ((card_dvd_of_cfg hc).trans hM)).2.2 with
    h | h | h
  · exact h19 h
  · exact h11 h
  · exact h21 h

theorem CfgU419.map_mulEquiv {X' : Type} [Group X'] [Finite X] (e : X ≃* X') {α : MulAut X}
    {Y : Subgroup X} {m : ℕ} (hc : CfgU419 X α Y m) :
    CfgU419 X' (MulAut.congr e α) (Y.map e.toMonoidHom) m := by
  haveI := hc.isPerfect
  obtain ⟨π, hπ, hker⟩ := hc.cover
  have hfix := autFix_congr e α
  set eY : Y ≃* Y.map e.toMonoidHom := Y.equivMapOfInjective e.toMonoidHom e.injective with heY
  refine ⟨by rw [← map_pow, hc.pow_three, map_one], fun h => hc.ne_one ?_, ?_, ?_, ?_, hc.odd,
    hc.one_lt, ?_⟩
  · exact (MulAut.congr e).injective (by rw [h, map_one])
  · rw [hfix]
    exact Subgroup.map_mono hc.le_autFix
  · rw [hfix]
    set ψ : autFix α →* (autFix α).map e.toMonoidHom :=
      e.toMonoidHom.subgroupMap (autFix α) with hψ
    have hψs : Function.Surjective ψ := e.toMonoidHom.subgroupMap_surjective _
    have heq : (Y.subgroupOf (autFix α)).map ψ =
        (Y.map e.toMonoidHom).subgroupOf ((autFix α).map e.toMonoidHom) := by
      ext ⟨y, hy⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨⟨x, hx⟩, hxY, hxy⟩
        refine ⟨x, hxY, ?_⟩
        exact congrArg Subtype.val hxy
      · rintro ⟨x, hxY, rfl⟩
        exact ⟨⟨x, hc.le_autFix hxY⟩, hxY, rfl⟩
    rw [← heq]
    exact hc.isSubnormal.map hψs
  · exact Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  · have hle : (eY.toMonoidHom).ker ≤ π.ker := by
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have : y = 1 := eY.injective (by rw [map_one]; exact hy)
      rw [this]
      exact one_mem _
    obtain ⟨π', hπ', hdvd⟩ := exists_surj_factor eY.toMonoidHom eY.surjective π hπ hle
    exact ⟨π', hπ', Nat.Coprime.coprime_dvd_left hdvd hker⟩

theorem NoCfgU419.of_mulEquiv {X' : Type} [Group X'] [Finite X] (e : X ≃* X')
    (h : NoCfgU419 X') : NoCfgU419 X := fun α Y m hc => h _ _ m (hc.map_mulEquiv e)

theorem nonempty_quot_center_of_isExtOf {Q B : Type*} [Group Q] [Group B] [Nontrivial Q]
    (hq : IsQuasisimple X) (h : IsExtOf X Q B) (hQ : Subgroup.center Q = ⊥) :
    Nonempty (X ⧸ Subgroup.center X ≃* Q) := by
  obtain ⟨K, hK, -, ⟨eQ⟩⟩ := h
  have hKZ : K ≤ Subgroup.center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hK with h | h
    · exfalso
      obtain ⟨u, v, huv⟩ := exists_pair_ne Q
      apply huv
      obtain ⟨a, rfl⟩ := eQ.surjective u
      obtain ⟨b, rfl⟩ := eQ.surjective v
      congr 1
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [QuotientGroup.eq]
          rw [h]
          exact Subgroup.mem_top _
    · exact h
  have hZK : Subgroup.center X ≤ K := by
    intro z hz
    have hc : eQ (z : X ⧸ K) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨a, rfl⟩ := eQ.surjective u
      induction a using QuotientGroup.induction_on with
      | H a =>
        rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (Subgroup.mem_center_iff.mp hz a)]
    rw [hQ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hc
    exact hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (le_antisymm hZK hKZ)).trans eQ⟩

theorem cfgU419_center [Finite X] (hq : IsQuasisimple X) {α : MulAut X} {Y : Subgroup X} {m : ℕ}
    (hc : CfgU419 X α Y m) :
    CfgU419 (X ⧸ Subgroup.center X) (centerDescend X α)
      (Y.map (QuotientGroup.mk' (Subgroup.center X))) m := by
  haveI : Group.IsPerfect X := hq.1
  exact cfgU419_map le_rfl (fun h => centerDescend_mk X α h) hc

theorem noCfgU419_of_isExtOf [Finite X] {Q B : Type} [Group Q] [Group B] [Nontrivial Q]
    (hq : IsQuasisimple X) (h : IsExtOf X Q B) (hQ : Subgroup.center Q = ⊥)
    (hQc : NoCfgU419 Q) : NoCfgU419 X := by
  obtain ⟨e⟩ := nonempty_quot_center_of_isExtOf hq h hQ
  intro α Y m hc
  exact NoCfgU419.of_mulEquiv e hQc _ _ m (cfgU419_center hq hc)

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
