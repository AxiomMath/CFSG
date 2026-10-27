module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusGenHomocyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section

open CFSG.Open

private abbrev FrameAction (p : ℕ) (R : Type*) [Group R]
    (t : Multiplicative (Fin 6 → ZMod p) →* R) (m : WeylGroup TwistTag.E6.tag →* R) : Prop :=
  ∀ (v : WeylGroup TwistTag.E6.tag) (s : Fin 6 → ZMod p),
    m v * t (Multiplicative.ofAdd s) * (m v)⁻¹ =
      t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p v s))

private theorem card_range {p : ℕ} [NeZero p] {R : Type*} [Group R]
    {t : Multiplicative (Fin 6 → ZMod p) →* R} (hinj : Function.Injective t) :
    Nat.card ↥t.range = p ^ 6 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma conj_range_mem {p : ℕ} {R : Type*} [Group R]
    {t : Multiplicative (Fin 6 → ZMod p) →* R} {m : WeylGroup TwistTag.E6.tag →* R}
    (hact : FrameAction p R t m)
    {v : WeylGroup TwistTag.E6.tag} {a : R} (ha : a ∈ t.range) :
    m v * a * (m v)⁻¹ ∈ t.range := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ha
  rw [← hx]
  refine ⟨Multiplicative.ofAdd
    (TableBExc.torusAct TwistTag.E6.tag p v (Multiplicative.toAdd x)), ?_⟩
  exact (hact v (Multiplicative.toAdd x)).symm

private theorem torusAct_simple_local (τ : Tag) {p : ℕ} [NeZero p] (i : Fin τ.rank)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (simple τ i) x =
      x - (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * x j) • Pi.single i 1 := by
  funext k
  simp only [TableBExc.torusAct, simple_smul, reflect, TableBExc.redMod, TableBExc.liftMod,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  congr 2
  by_cases h : k = i
  · subst h; simp
  · simp [h]

private theorem torusAct_simple_E6_local {p : ℕ} [NeZero p] (i : Fin 6) (s : Fin 6 → ZMod p) :
    TableBExc.torusAct Tag.E6 p (simple Tag.E6 i) s = TwE6TB.reflE6 p i s := by
  refine (torusAct_simple_local Tag.E6 i s).trans ?_
  show (s - (∑ j : Fin 6, ((Tag.E6.cartan i j : ℤ) : ZMod p) * s j) •
      (Pi.single i 1 : Fin 6 → ZMod p) : Fin 6 → ZMod p) = _
  rw [TwE6TB.reflE6]
  congr 2
  unfold TwE6TB.pairE6
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 2
  fin_cases i <;> fin_cases j <;> rfl

private theorem normalized_eq_bot_or_eq_range {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp5 : 5 ≤ p) {R : Type*} [Group R]
    {t : Multiplicative (Fin 6 → ZMod p) →* R} {m : WeylGroup TwistTag.E6.tag →* R}
    (hact : FrameAction p R t m)
    {Q : Subgroup R} (hQ : Q ≤ t.range)
    (hnormQ : ∀ v, ∀ q ∈ Q, m v * q * (m v)⁻¹ ∈ Q) :
    Q = ⊥ ∨ Q = t.range := by
  let G : AddSubgroup (Fin 6 → ZMod p) :=
    { carrier := {s | t (Multiplicative.ofAdd s) ∈ Q}
      zero_mem' := by simp
      add_mem' := by
        intro s w hs hw
        show t (Multiplicative.ofAdd (s + w)) ∈ Q
        rw [show t (Multiplicative.ofAdd (s + w)) =
            t (Multiplicative.ofAdd s) * t (Multiplicative.ofAdd w) from
          map_mul t (Multiplicative.ofAdd s) (Multiplicative.ofAdd w)]
        exact Q.mul_mem hs hw
      neg_mem' := by
        intro s hs
        show t (Multiplicative.ofAdd (-s)) ∈ Q
        rw [show t (Multiplicative.ofAdd (-s)) = (t (Multiplicative.ofAdd s))⁻¹ from
          map_inv t (Multiplicative.ofAdd s)]
        exact Q.inv_mem hs }
  have hG : ∀ i : Fin 6, ∀ v ∈ G, TwE6TB.reflE6 p i v ∈ G := by
    intro i v hv
    have h1 : t (Multiplicative.ofAdd
        (TableBExc.torusAct Tag.E6 p (simple Tag.E6 i) v)) ∈ Q := by
      change t (Multiplicative.ofAdd
        (TableBExc.torusAct TwistTag.E6.tag p (simple Tag.E6 i) v)) ∈ Q
      rw [← hact (simple Tag.E6 i) v]
      exact hnormQ _ _ hv
    rwa [torusAct_simple_E6_local] at h1
  rcases TwE6TB.eq_bot_or_eq_top_of_reflE6 hp5 G hG with hbot | htop
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hQ hq)
    have hxG : Multiplicative.toAdd x ∈ G := by
      show t (Multiplicative.ofAdd (Multiplicative.toAdd x)) ∈ Q
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd x) = x from rfl, hx]
      exact hq
    rw [hbot, AddSubgroup.mem_bot] at hxG
    have hx1 : x = 1 := by simpa using congrArg Multiplicative.ofAdd hxG
    rw [← hx, hx1, map_one]
  · right
    apply le_antisymm hQ
    intro a ha
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ha
    have hxG : Multiplicative.toAdd x ∈ G := htop ▸ AddSubgroup.mem_top _
    have hxQ : t (Multiplicative.ofAdd (Multiplicative.toAdd x)) ∈ Q := hxG
    rwa [show Multiplicative.ofAdd (Multiplicative.toAdd x) = x from rfl, hx] at hxQ

end

theorem ggTorusGenR_twE6
    {n p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTorusGenR p 4 (TwE6Delta.RecipeR K n) := by
  have : NeZero p := ⟨by omega⟩
  obtain ⟨t, m, T, e, hframe⟩ := TwE6TB.ggTwE6TorusFramePackage_recipeR hp5 hn hK hpq
  obtain ⟨hinj, hact, hU, hTab, hrangeT, hcent, htors, hcount, hcomp⟩ := hframe
  have hA : Nat.card ↥t.range = p ^ 6 := card_range hinj
  have hNA : m.range ≤ Subgroup.normalizer (t.range : Set (TwE6Delta.RecipeR K n)) := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact conj_range_mem hact
    · intro ha
      have h := conj_range_mem (m := m) hact (v := v⁻¹) ha
      have hcalc : m v⁻¹ * (m v * a * (m v)⁻¹) * (m v⁻¹)⁻¹ = a := by
        rw [map_inv]; group
      rwa [hcalc] at h
  have hcent' : Subgroup.centralizer (t.range : Set (TwE6Delta.RecipeR K n)) ≤ T := by
    intro c hc
    exact hcent c (fun x hx => ((Subgroup.mem_centralizer_iff.mp hc) x hx).symm)
  have hirr : ∀ Q : Subgroup (TwE6Delta.RecipeR K n), Q ≤ t.range →
      m.range ≤ Subgroup.normalizer (Q : Set (TwE6Delta.RecipeR K n)) →
        Q = ⊥ ∨ Q = t.range := by
    intro Q hQ hNQ
    refine normalized_eq_bot_or_eq_range hp5 hact hQ ?_
    intro v q hq
    exact (Subgroup.mem_normalizer_iff.mp (hNQ ⟨v, rfl⟩) q).mp hq
  have hexp : (∃ s ∈ T, orderOf s = p ^ e) → ∀ y ∈ T,
      (∃ k : ℕ, y ^ p ^ k = 1) → y ^ p ^ e = 1 := by
    rintro ⟨s, hsT, hse⟩
    exact pow_eq_one_of_card_torusPPart hTab hrangeT hcent' hNA htors hirr hA hcount hsT hse
  have hcomp' : ∀ x ∈ t.range, x ≠ 1 → ∀ J : Subgroup (TwE6Delta.RecipeR K n),
      IsComponentOf J (Subgroup.centralizer {x}) → ∃ s ∈ J, s ∈ T ∧ orderOf s = p ^ e := by
    intro x hx hx1 J hJ
    exact hcomp x hx hx1 J ((CFSG.Assembly.isComponentOf_iff_open).1 hJ)
  exact ggTorusGenR_of_torusIrred (A := t.range) (N := m.range) (n := 6) hTab hrangeT
    hcent' hNA htors hirr hA hexp hU hcomp'

end CFSG.StandardType
