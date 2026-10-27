module

public import CFSG.RankThree.GF2n.Smith81.OrthSetup
public import CFSG.RankThree.GF2n.Smith81.Sec117
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Smith81.Lanes
public import CFSG.RankThree.GF2n.Smith81.Sec216
public import CFSG.RankThree.GF2n.Smith81.Sec2Assembly
public import CFSG.RankThree.GF2n.Smith81.Sec2Consequences

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def OrthTacitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B'

@[expose] def Smith25OrthStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ V = A ⊔ Z} =
      {V : Subgroup G | ∃ m ∈ M, V = conjSubgroup m B ⊔ Z}

section Two5

variable [Finite G]

theorem smith25Orth_of_inputs (h34 : Stroth34Statement) (hT : OrthTacitStatement) :
    Smith25OrthStatement := by
  intro G _ _ M Q Z B hc
  obtain ⟨n, hw, -, h4⟩ := hc.orth.exists_width
  have hno : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') :=
    fun B' hB' => (hT G M Q Z B hc B' hB').1
  have h15c : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G) := fun B' hB' =>
    (stroth_3_5 h34 hB' hw (by omega) (hT G M Q Z B hc B' hB').1
      (hT G M Q Z B hc B' hB').2).2.1
  exact smith25_of_117 smith117Statement_holds hc.ctx hw (by omega) hno h15c

end Two5

@[expose] def Smith28OrthStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

section Nine

variable [Finite G]

theorem smith29_of_exists {M Q Z X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hex : ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ A ≤ QB X ∧ A ≠ X ∧
      X ≤ LB M Q A := by
  obtain ⟨v, hxv, hvQ, hvX⟩ := hex
  have H := hs.hyp
  have h12 := smith_1_12 hs
  have hv1 : v ≠ 1 := ne_one_of_isConj_Z hs.ne_one hxv
  obtain ⟨g, hg⟩ := hs.conj
  have hzx : g⁻¹ * x * g ∈ Z := mem_conjSubgroup.mp (hg ▸ hs.mem)
  have hzv : IsConj (g⁻¹ * x * g) v :=
    IsConj.trans (isConj_iff.mpr ⟨g, by group⟩) hxv
  obtain ⟨A, hA, hvA⟩ := exists_isZConjugate_mem hzx hzv
  have hXc : IsZConjugate Z X := hs.conj
  have hZc : IsZConjugate Z Z := IsZConjugate.self Z
  have hAQ : A ≤ Q := by
    have := hZc.le_QB_of_mem H hA hv1 hvA (by rw [H.QB_Z]; exact hvQ)
    rwa [H.QB_Z] at this
  have hAX : A ≤ QB X := hXc.le_QB_of_mem H hA hv1 hvA hvX
  have hAZ : A ≠ Z := by
    intro h
    rw [h] at hAX
    have h1 : Z ⊓ QB X = Z := inf_eq_left.mpr hAX
    have h2 := Z_inf_QB_eq_bot hs h12
    rw [h1] at h2
    have h4 := H.q4
    rw [h2, Subgroup.card_bot] at h4
    omega
  have hAXne : A ≠ X := by
    intro h
    rw [h] at hAQ
    have h1 := hs.X_inf_Q
    rw [inf_eq_left.mpr hAQ] at h1
    have : x ∈ (⊥ : Subgroup G) := h1 ▸ hs.mem
    exact hs.ne_one (Subgroup.mem_bot.mp this)
  refine ⟨A, hA, hAQ, hAZ, hAX, hAXne, ?_⟩
  have hXA : X ≤ QB A := (hA.le_QB_iff H hXc).mpr hAX
  have hXM : X ≤ M := fun y hy => (h12.1 hy).1
  exact (le_inf hXA hXM).trans (le_sup_right (a := Q))

end Nine

section Fusion

variable [Finite G]

theorem Jx_le_Q {M Q Z X : Subgroup G} {x : G} (hs : Sit M Q Z X x) : Jx Q X x ≤ Q := by
  intro b hb
  have hbD : b ∈ ⁅Q, Subgroup.zpowers x⁆ := (Subgroup.mem_inf.mp hb).1
  have hcomm : ⁅Q, Subgroup.zpowers x⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    have hyM : y ∈ M := (Subgroup.zpowers_le.mpr hs.memM) hy
    have h1 := conj_mem_Q hs.hyp hyM (Q.inv_mem hq)
    have e : ⁅q, y⁆ = q * (y * q⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hq h1
  exact hcomm hbD

theorem smith28_of_fused {M Q Z X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hJ : Jx Q X x ≠ ⊥) (hfus : ∀ z ∈ Z, IsConj x (x * z)) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJ
  have hbJ : (b : G) ∈ Jx Q X x := b.2
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨g, z, hz, hbg⟩ := smith_1_16 hs hbJ hb1'
  refine ⟨b, ?_, Jx_le_Q hs hbJ, (Subgroup.mem_inf.mp hbJ).2⟩
  rw [hbg]
  exact IsConj.trans (hfus z hz) (isConj_iff.mpr ⟨g, rfl⟩)

end Fusion

@[expose] def Smith28aOrthStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥

@[expose] def Smith212OrthCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q → IsConj z x →
      (conjClassSet z ∩ cosetSet x Z = {x}) ∧
      ({g : G | IsConj x g} ∩ {g : G | ∃ q ∈ Q, g = x * q} = conjOrbit Q x) ∧
      (∀ X : Subgroup G, IsZConjugate Z X → x ∈ X →
        (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z)

@[expose] def Smith213OrthStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))

@[expose] def Smith216OrthCountStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ A C : Subgroup G, IsZConjugate Z A → IsZConjugate Z C → A ≠ C →
      C ≤ QB A → ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧ (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧
        Nat.card Z ^ 2 < Nat.card S

@[expose] def Smith216OrthOddStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ z ∈ Z, z ≠ 1 → ∀ x z' w y : G, IsConj z x → IsConj z z' → IsConj z w → IsConj z y →
      Commute x z' → Commute z' w → Commute w y → ¬ Commute x w → ¬ Commute z' y →
      Odd (orderOf (x * w)) → Odd (orderOf (z' * y)) →
        ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y

section Sixteen

variable [Finite G]

theorem smith216Orth_of_statements (h212 : Smith212OrthCoreStatement)
    (h213 : Smith213OrthStatement) (hCount : Smith216OrthCountStatement)
    (hOdd : Smith216OrthOddStatement) : Smith216OrthStatement := by
  intro G _ _ M Q Z B IH hc hcase z hz hz1 x z' w y hx hz' hw hy hxz hzw hwy
  have hOC : SmithOrthCfg M Q Z B := ⟨hc.toCfg, hcase⟩
  refine smith_2_16 hc.ctx.hyp hz hz1 ?_ (h213 G M Q Z B hOC z hz hz1) ?_ ?_ hx hz' hw hy
    hxz hzw hwy
  · intro x' hxM hxQ hxc y' hy'cos hy'c
    have h1 := (h212 G M Q Z B hOC z hz hz1 x' hxM hxQ hxc).1
    have hmem : y' ∈ conjClassSet z ∩ cosetSet x' Z := ⟨hy'c, hy'cos⟩
    rw [h1] at hmem
    exact hmem
  · exact fun A C hA hC hAC hCA => hCount G M Q Z B hOC z hz hz1 A C hA hC hAC hCA
  · exact fun x' z'' w' y' hx' hz'' hw' hy' hxz' hzw' hwy' hxw hzy ho1 ho2 =>
      hOdd G M Q Z B hOC z hz hz1 x' z'' w' y' hx' hz'' hw' hy' hxz' hzw' hwy' hxw hzy ho1 ho2

end Sixteen

@[expose] def Smith219OrthInspectionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
      Timmesfeld.Outcome (FStar G) → SmithLaneOrth M Q Z B

end CFSG.RankThree.GF2n.Smith81
