module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmRank
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB
open CFSG.StandardType.NoOffOm CFSG.StandardType.OrdPNsOm CFSG.StandardType.OrdPNsGen
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.KCOrthComm CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.T173S

private theorem twomsc_genMax_le {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {p : ℕ} (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) {E₀ : Subgroup (GL (Fin d) K)}
    (hE₀Γ : E₀ ≤ matrixDerived Q) (hE₀p : ∀ a ∈ E₀, a ^ p = 1)
    (hE₀c : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a) :
    ∃ E : Subgroup (GL (Fin d) K), GenMax (polB Q) (matrixDerived Q) p E ∧ E₀ ≤ E := by
  classical
  set Γ := matrixDerived Q with hΓ
  set P : Subgroup (GL (Fin d) K) → Prop := fun E =>
    E ≤ Γ ∧ E₀ ≤ E ∧ (∀ a ∈ E, a ^ p = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hP
  set R : ℕ → Prop := fun k => ∃ E, P E ∧ Nat.card E = k with hR
  have hP0 : P E₀ := ⟨hE₀Γ, le_rfl, hE₀p, hE₀c⟩
  have hbound : ∀ k, R k → k ≤ Nat.card (GL (Fin d) K) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hR0 : R (Nat.card E₀) := ⟨_, hP0, rfl⟩
  set N := Nat.findGreatest R (Nat.card (GL (Fin d) K)) with hN
  obtain ⟨E, hE, hEN⟩ : R N := Nat.findGreatest_spec (hbound _ hR0) hR0
  refine ⟨E, ⟨polB_isSymm, hnd.1, hp, hp2, hE.1, hE.2.2.1, hE.2.2.2, fun g hg hgp hgE => ?_,
    fun g hg v w => polB_glin_of_mem_isometries (matrixDerived_le_isometries Q (hE.1 hg)) v w,
    fun c hc W hW hWA => ?_⟩, hE.2.1⟩
  · set E' := Subgroup.closure ((E : Set (GL (Fin d) K)) ∪ {g}) with hE'
    have h1 := closure_comm_pow (S := (E : Set (GL (Fin d) K)) ∪ {g}) (p := p)
      (by
        rintro x (hx | hx) y (hy | hy)
        · exact hE.2.2.2 x hx y hy
        · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
        · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
        · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
      (by
        rintro x (hx | hx)
        · exact hE.2.2.1 x hx
        · rw [Set.mem_singleton_iff.mp hx]; exact hgp)
    have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hE'Γ : E' ≤ Γ := by
      rw [hE', Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hE.1 hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg
    have hP' : P E' := ⟨hE'Γ, fun x hx => hEE' (hE.2.1 hx), h1.2, h1.1⟩
    have hcard : Nat.card E' ≤ Nat.card E := by
      rw [hEN]
      exact Nat.le_findGreatest (hbound _ ⟨E', hP', rfl⟩) ⟨E', hP', rfl⟩
    have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
    rw [heq]
    exact Subgroup.subset_closure (Or.inr rfl)
  · exact exists_restrict_mem_omega hnd hT hp hp2 (hE.1 hc) (hE.2.2.1 c hc) hW (hWA c hc)

private theorem twomsc_selfCent_map {p : ℕ} {R S : Type} [Group R] [Group S] (e : R ≃* S)
    {E : Subgroup R}
    (hsc : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∀ g : S, (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
  intro g hg hgp
  obtain ⟨g₀, rfl⟩ := e.surjective g
  rw [Subgroup.mem_map]
  refine ⟨g₀, ?_, rfl⟩
  refine hsc g₀ (fun x hx => ?_) ?_
  · have h1 := hg (e x) (Subgroup.mem_map_of_mem _ hx)
    exact e.injective (by rw [map_mul, map_mul]; exact h1)
  · apply e.injective
    rw [map_pow, hgp, map_one]

private theorem twomsc_isHypFamily_qMinus {K : Type} [Field K] (m : ℕ) (b c : K) :
    TableBOrth.IsHypFamily (TableBOrth.qMinusForm K m b c)
      (fun i => Pi.single (Sum.inl (Sum.inl i)) (1 : K))
      (fun i => Pi.single (Sum.inl (Sum.inr i)) (1 : K)) where
  map_e i := (TableBOrth.isHypCoord_qMinusForm b c i).map_left
  map_f i := (TableBOrth.isHypCoord_qMinusForm b c i).map_right
  polar_ee i j := by
    have h := (TableBOrth.isHypCoord_qMinusForm b c i).polar_left
      (Pi.single (Sum.inl (Sum.inl j)) (1 : K))
    rw [h]
    exact Pi.single_eq_of_ne (by simp) 1
  polar_ff i j := by
    have h := (TableBOrth.isHypCoord_qMinusForm b c i).polar_right
      (Pi.single (Sum.inl (Sum.inr j)) (1 : K))
    rw [h]
    exact Pi.single_eq_of_ne (by simp) 1
  polar_ef i j := by
    have h := (TableBOrth.isHypCoord_qMinusForm b c i).polar_left
      (Pi.single (Sum.inl (Sum.inr j)) (1 : K))
    rw [h, Pi.single_apply]
    simp [Sum.inl_injective.eq_iff]

theorem ggTwOm_scRank_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n m r : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ n) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) (hmr : m = r)
    (h3 : 3 ∣ 2 ^ n - 1 ∨ (Odd r ∧ 3 ∣ 2 ^ n + 1)) :
    GGSelfCentRankGE 3 r (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
  subst hmr
  intro E hE hsc
  have hn1 : 1 ≤ m + 1 := by omega
  have hn4 : 4 ≤ m + 1 := by omega
  set Q : QuadraticForm K (Fin (2 * (m + 1)) → K) :=
    coordinateQuadMinus (m + 1) K hn1 b c with hQ
  have hnd : Q.polarBilin.Nondegenerate :=
    (regular_coordinateQuadMinus (m + 1) K b c hn4 hbc).1
  have hT : ∃ T : Submodule K (Fin (2 * (m + 1)) → K),
      Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 :=
    (regular_coordinateQuadMinus (m + 1) K b c hn4 hbc).2
  let eIso : (TableBOrth.qMinusForm K m b c).IsometryEquiv Q :=
    (TableBOrth.qMinusIsometry m b c).trans (coordinateMinusIsometry (m + 1) K hn1 b c)
  let eOrth : orthDerived (TableBOrth.qMinusForm K m b c) ≃* matrixDerived Q :=
    (CFSG.RankThree.PartOne.orthDerivedEquiv eIso).trans (matrixDerivedEquiv Q).symm
  let eR : OrthRest.RMinus K m b c ≃* matrixDerived Q :=
    (OrthTorus.rMinusEquiv K m b c).trans eOrth
  set E' : Subgroup (matrixDerived Q) := E.map eR.toMonoidHom with hE'
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective eR.injective
  have hE'ab : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE eR.toMonoidHom
  have hE'sc : ∀ g : matrixDerived Q, (∀ x ∈ E', g * x = x * g) → g ^ 3 = 1 → g ∈ E' :=
    twomsc_selfCent_map eR hsc
  obtain ⟨E₀, hE₀ab, hE₀card⟩ :
      ∃ E₀ : Subgroup (matrixDerived Q), IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ m := by
    rcases h3 with h1 | ⟨hodd, hpn⟩
    ·
      have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h1
      obtain ⟨A₀, hA₀ab, hA₀card, -⟩ :=
        exists_subgroup_eq_torsionTorus (Q := TableBOrth.qMinusForm K m b c)
          (TableBOrth.nondegenerate_qMinusForm m hbc) Nat.prime_three (by norm_num) hpq
          (twomsc_isHypFamily_qMinus m b c)
      exact ⟨A₀.map eOrth.toMonoidHom,
        TableB.isElemAbelian_map hA₀ab eOrth.toMonoidHom,
        by rw [Subgroup.card_map_of_injective eOrth.injective, hA₀card]⟩
    ·
      obtain ⟨-, E₁, -, -, -, hE₁ab, hE₁card⟩ :=
        OrthRestTail.torus_minus (K := K) (m := m) (n := n) b c hK hr
          Nat.prime_three (by norm_num) hpn hbc
      exact ⟨E₁.map eR.toMonoidHom, TableB.isElemAbelian_map hE₁ab eR.toMonoidHom,
        by rw [Subgroup.card_map_of_injective eR.injective, hE₁card]⟩
  set E₀g : Subgroup (GL (Fin (2 * (m + 1))) K) := E₀.map (matrixDerived Q).subtype with hE₀g
  set E'g : Subgroup (GL (Fin (2 * (m + 1))) K) := E'.map (matrixDerived Q).subtype with hE'g
  have hE₀gΓ : E₀g ≤ matrixDerived Q := Subgroup.map_subtype_le _
  have hE'gΓ : E'g ≤ matrixDerived Q := Subgroup.map_subtype_le _
  have hE₀gab : IsElemAbelian 3 E₀g := TableB.isElemAbelian_map hE₀ab _
  have hE'gab : IsElemAbelian 3 E'g := TableB.isElemAbelian_map hE'ab _
  have hE₀gcard : Nat.card E₀g = 3 ^ m := by
    rw [Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective, hE₀card]
  have hE'gcard : Nat.card E'g = Nat.card E' :=
    Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective
  obtain ⟨A₀, hA₀, hE₀gA₀⟩ := twomsc_genMax_le (E₀ := E₀g) hnd hT Nat.prime_three (by norm_num)
    hE₀gΓ hE₀gab.2 (fun a ha b hb => TableB.IsElemAbelian.comm hE₀gab ha hb)
  obtain ⟨A_E, hA_E, hE'gA_E⟩ := twomsc_genMax_le (E₀ := E'g) hnd hT Nat.prime_three (by norm_num)
    hE'gΓ hE'gab.2 (fun a ha b hb => TableB.IsElemAbelian.comm hE'gab ha hb)
  have hA_E_le : A_E ≤ E'g := by
    intro a ha
    have haΓ : a ∈ matrixDerived Q := hA_E.le ha
    have ha' : (⟨a, haΓ⟩ : matrixDerived Q) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hA_E.pow a ha
    have hcomm' : ∀ x ∈ E',
        (⟨a, haΓ⟩ : matrixDerived Q) * x = x * (⟨a, haΓ⟩ : matrixDerived Q) := by
      intro x hx
      apply Subtype.ext
      exact hA_E.comm a ha (↑x) (hE'gA_E (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    have hmem : (⟨a, haΓ⟩ : matrixDerived Q) ∈ E' := hE'sc _ hcomm' ha'
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hA_E_eq : A_E = E'g := le_antisymm hA_E_le hE'gA_E
  have hcard := card_le_card_of_genMax hnd hT hA₀ hA_E
  calc 3 ^ m = Nat.card E₀g := hE₀gcard.symm
    _ ≤ Nat.card A₀ := Nat.card_le_card_of_injective (Subgroup.inclusion hE₀gA₀)
        (Subgroup.inclusion_injective hE₀gA₀)
    _ ≤ Nat.card A_E := hcard
    _ = Nat.card E'g := by rw [hA_E_eq]
    _ = Nat.card E' := hE'gcard
    _ = Nat.card E := hE'card

end CFSG.StandardType

end
