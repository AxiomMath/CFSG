module

public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrWA
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6aR_fix_closure {E : Type*} [Group E] {S : Set (MulAut E)} {b : E}
    (hb : ∀ ψ ∈ S, ψ b = b) : ∀ ψ ∈ Subgroup.closure S, ψ b = b := by
  intro ψ hψ
  have hle : Subgroup.closure S ≤ MulAction.stabilizer (MulAut E) b := by
    rw [Subgroup.closure_le]
    exact hb
  exact hle hψ

private theorem l6aR_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]


private theorem l6aR_disj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {x y : G}
    {D : Subgroup G}
    (hDcard : Nat.card D = p ^ 2) (hDp : ∀ z ∈ D, z ^ p = 1) (hxD : x ∈ D)
    (hDgen : D = Subgroup.closure ({x, y} : Set G)) :
    ∀ z : G, z ∈ Subgroup.zpowers x → z ∈ Subgroup.zpowers y → z = 1 := by
  have hp : p.Prime := Fact.out
  intro z hzx hzy
  by_contra hz
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hxp : x ^ p = 1 := hDp x hxD
  have hyp : y ^ p = 1 := hDp y hyD
  have hzD : z ∈ D := (Subgroup.zpowers_le.mpr hxD) hzx
  have hzp : z ^ p = 1 := hDp z hzD
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz
  have hxle : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one hp.pos hxp
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have heqx : Subgroup.zpowers z = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzx)
      (by rw [hzcard]; exact hxle)
  have hzyle : Subgroup.zpowers z ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hzy
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one hp.pos hyp
  have heqy : Subgroup.zpowers z = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hzyle (by rw [hzcard]; exact hyle)
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hDgen]
    refine (Subgroup.closure_le (Subgroup.zpowers x)).mpr ?_
    intro a ha
    have ha' : a = x ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.mem_zpowers x
    · rw [h, ← heqx, heqy]; exact Subgroup.mem_zpowers y
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
      _ ≤ p := hxle
  nlinarith [hcon, hp.two_le]



private theorem l6aR_y_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : y ≠ 1 := by
  intro hy1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hDea.2 x hxD
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hDgen, hy1, Subgroup.closure_le]
    intro a ha
    have ha' : a = x ∨ a = 1 := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.mem_zpowers x
    · rw [h]; exact Subgroup.one_mem _
  have hxle : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hxp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
      _ ≤ p := hxle
  nlinarith [hcon, hp.two_le]

private theorem l6aR_moving {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hA : GGReflGenerated p A) {z : G} (hz : z ∈ Bs) {w : G}
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → (b : G) ∈ Subgroup.zpowers w)
    (hdisj : ∀ g : G, g ∈ Subgroup.zpowers z → g ∈ Subgroup.zpowers w → g = 1) (hz1 : z ≠ 1) :
    ∃ t ∈ A, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩ := by
  by_contra hcon
  push Not at hcon
  have hA' : A = Subgroup.closure {φ | φ ∈ A ∧ GGIsReflection p φ} := hA
  have hall : ∀ ψ ∈ A, ψ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    intro ψ hψ
    have hψ' : ψ ∈ Subgroup.closure {φ | φ ∈ A ∧ GGIsReflection p φ} := by
      rw [← hA']
      exact hψ
    exact l6aR_fix_closure (fun φ hφ => hcon φ hφ.1 hφ.2) ψ hψ'
  have hmem : z ∈ Subgroup.zpowers w := by
    have := hfix ⟨z, hz⟩ hall
    simpa using this
  exact hz1 (hdisj z (Subgroup.mem_zpowers z) hmem)

private theorem l6aR_moving_wA {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hA : GGReflGenerated p A) {z : G} (hz : z ∈ Bs)
    (hfix : ∀ b : ↥Bs, (b : G) ∈ Subgroup.zpowers z → (∀ ψ ∈ A, ψ b = b) → (b : G) = 1)
    (hz1 : z ≠ 1) : ∃ t ∈ A, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩ := by
  by_contra hcon
  push Not at hcon
  have hA' : A = Subgroup.closure {φ | φ ∈ A ∧ GGIsReflection p φ} := hA
  have hall : ∀ ψ ∈ A, ψ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    intro ψ hψ
    have hψ' : ψ ∈ Subgroup.closure {φ | φ ∈ A ∧ GGIsReflection p φ} := by
      rw [← hA']
      exact hψ
    exact l6aR_fix_closure (fun φ hφ => hcon φ hφ.1 hφ.2) ψ hψ'
  exact hz1 (by simpa using hfix ⟨z, hz⟩ (Subgroup.mem_zpowers z) hall)

theorem ggIndep_moving_K (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) :
    ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩ :=
  l6aR_moving_wA hH.2.2.2.2.2.1 hx (fun b hbx hb =>
    ggTBFixNbrInput_wA hFixK G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 b hbx hb) (l6aR_x_ne_one hH)

theorem ggIndep_moving_K_of_fixedLine {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    (hfixK : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y) :
    ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩ := by
  have hpre := hH.1.2.2.1
  refine l6aR_moving hH.2.2.2.2.2.1 hx (w := y) hfixK ?_ (l6aR_x_ne_one hH)
  intro g hgx hgy
  exact l6aR_disj hpre.2.2.1 hpre.2.1.2 hpre.2.2.2.1 hH.2.2.2.2.1.2.1 g hgx hgy

theorem ggIndep_moving_L (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs)) :
    ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩ := by
  have hpre := hH.1.2.2.1
  refine l6aR_moving hLrefl hy (w := x) (fun b hb => ?_) ?_ (l6aR_y_ne_one hH)
  · exact hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 b hb
  · intro g hgy hgx
    exact l6aR_disj hpre.2.2.1 hpre.2.1.2 hpre.2.2.2.1 hH.2.2.2.2.1.2.1 g hgx hgy


end CFSG.StandardType

end
