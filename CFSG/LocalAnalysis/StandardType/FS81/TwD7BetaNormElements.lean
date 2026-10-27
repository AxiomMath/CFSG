module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthP
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaCoordinates

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Assembly
open scoped commutatorElement

theorem realized_eq_evenFix0_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    B.realized K = evenFix0 7 := by
  classical
  have hstd₀ := hstd
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, hKN, -, -, -, -, -⟩ := hA
  have hsub : B.realized K ⊆ evenFix0 7 := fun A hA =>
    realized_centralizer_subset_evenFix0_of_recOutTwD7 hB hKC hKN hCanon.2.1 hrec
      (realized_mono B hKC hA)
  obtain ⟨B₀, hB₀, -, heven⟩ := exists_basis_localOrth_even_twD7 hstd₀
  have hcard := Basis3.card_realized_eq_of_span_eq (hB.1.trans hB₀.1.symm) K
  let incl : evenFix0 7 → B₀.realized K := fun x => ⟨x.val, heven x.2⟩
  have hinj : Function.Injective incl := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : B₀.realized K => z.val) h)
  have hle : Nat.card (evenFix0 7) ≤ Nat.card (B.realized K) :=
    (Nat.card_le_card_of_injective incl hinj).trans hcard.symm.le
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hle
  exact Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)

theorem exists_even_sign_action_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (T : Finset (Fin 8)) (hT0 : (0 : Fin 8) ∉ T) (hT : Even T.card) :
    ∃ g ∈ K, g ∈ normalizer (E : Set G) ∧
      ∀ j : Fin 8, g * B.b j * g⁻¹ = if j ∈ T then (B.b j)⁻¹ else B.b j := by
  let s : Fin 8 → ZMod 3 := sgnOn T
  have hmat : spMat 1 s ∈ evenFix0 7 := sgnOn_mem_evenFix0 T hT0 hT
  have hr : spMat 1 s ∈ B.realized K :=
    (realized_eq_evenFix0_of_std_twD7 hstd B hB hrec).symm ▸ hmat
  obtain ⟨g, hg, hact⟩ := hr
  refine ⟨g, hg, hB.1 ▸ B.mem_normalizer_of_acts hact, ?_⟩
  intro j
  have hcol : (fun i => spMat 1 s i j) = Pi.single j (s j) := by
    ext i
    simp [spMat, Pi.single_apply, eq_comm]
  rw [hact j, hcol]
  by_cases hj : j ∈ T
  · have hs : s j = -1 := by simp [s, sgnOn, hj]
    rw [hs, if_pos hj]
    have hv : (Pi.single j (-1) : Coords 8) = -(Pi.single j (1 : ZMod 3) : Coords 8) := by
      ext i
      by_cases hij : i = j <;> simp [hij]
    rw [hv]
    exact (B.vec_neg (Pi.single j (1 : ZMod 3))).trans (congrArg Inv.inv (B.vec_single j))
  · have hs : s j = 1 := by simp [s, sgnOn, hj]
    rw [hs, B.vec_single, if_neg hj]

theorem exists_even_inverter_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    ∃ g ∈ K, g ∈ normalizer (E : Set G) ∧
      ∀ j : Fin 8, g * B.b j * g⁻¹ = if j = 1 ∨ j = 2 then (B.b j)⁻¹ else B.b j := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    exists_even_sign_action_of_std_twD7 hstd B hB hrec {1, 2} (by decide) (by decide)

private theorem normalizes_derived_centralizer_of_inv
    {G : Type} [Group G] [Finite G] (K : Subgroup G) (b g : G) (hg : g ∈ K)
    (hgb : g * b * g⁻¹ = b⁻¹) :
    g ∈ normalizer ((⁅centralizer ({b} : Set G) ⊓ K,
      centralizer ({b} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := by
  let C : Subgroup G := centralizer ({b} : Set G) ⊓ K
  have hmap : C.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, K.mul_mem (K.mul_mem hg hx.2) (K.inv_mem hg)⟩
    change g * x * g⁻¹ ∈ centralizer ({b} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hc : Commute x b := (mem_centralizer_iff.mp hx.1 b (Set.mem_singleton b)).symm
    have hm := hc.map (MulAut.conj g).toMonoidHom
    change Commute (g * x * g⁻¹) (g * b * g⁻¹) at hm
    rw [hgb] at hm
    have hm' : Commute (g * x * g⁻¹) b := by simpa only [inv_inv] using hm.inv_right
    exact hm'.eq.symm
  have heq : C.map (MulAut.conj g).toMonoidHom = C :=
    Subgroup.eq_of_le_of_card_ge hmap (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅C, C⁆).map (MulAut.conj g).toMonoidHom = ⁅C, C⁆
  rw [Subgroup.map_commutator, heq]

theorem exists_beta_line_swap_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    ∃ g ∈ K, g ∈ normalizer (E : Set G) ∧
      g ∈ normalizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
        centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ∧
      g * (b₀ * B.b 1) * g⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ ∧
      g * (b₀⁻¹ * B.b 1) * g⁻¹ = (b₀ * B.b 1)⁻¹ ∧
      g * B.b 2 * g⁻¹ = (B.b 2)⁻¹ := by
  obtain ⟨g, hg, hgE, hact⟩ := exists_even_inverter_of_std_twD7 hstd B hB hrec
  have h0 : g * b₀ * g⁻¹ = b₀ := by simpa [hB.2.1] using hact 0
  have h1 : g * B.b 1 * g⁻¹ = (B.b 1)⁻¹ := by simpa using hact 1
  have h2 : g * B.b 2 * g⁻¹ = (B.b 2)⁻¹ := by simpa using hact 2
  have hcomm : Commute b₀ (B.b 1) := by simpa only [hB.2.1] using B.comm 0 1
  refine ⟨g, hg, hgE, normalizes_derived_centralizer_of_inv K (B.b 1) g hg h1, ?_, ?_, h2⟩
  · change (MulAut.conj g) (b₀ * B.b 1) = _
    rw [map_mul]
    change (g * b₀ * g⁻¹) * (g * B.b 1 * g⁻¹) = _
    rw [h0, h1, mul_inv_rev, inv_inv]
    exact hcomm.inv_right.eq
  · change (MulAut.conj g) (b₀⁻¹ * B.b 1) = _
    rw [map_mul, map_inv]
    change (g * b₀ * g⁻¹)⁻¹ * (g * B.b 1 * g⁻¹) = _
    rw [h0, h1, mul_inv_rev]
    exact hcomm.inv_left.inv_right.eq

theorem tail_mem_commutator_centralizer_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) (i : Fin 6) :
    B.b i.succ.succ ∈ ⁅centralizer ({B.b 1} : Set G) ⊓ K,
      centralizer ({B.b 1} : Set G) ⊓ K⁆ := by
  let j : Fin 8 := if i = 0 then 3 else 2
  let T : Finset (Fin 8) := {i.succ.succ, j}
  have hT0 : (0 : Fin 8) ∉ T := by fin_cases i <;> decide
  have hT1 : (1 : Fin 8) ∉ T := by fin_cases i <;> decide
  have hTE : Even T.card := by fin_cases i <;> decide
  obtain ⟨g, hg, -, hact⟩ := exists_even_sign_action_of_std_twD7 hstd B hB hrec T hT0 hTE
  let C : Subgroup G := centralizer ({B.b 1} : Set G) ⊓ K
  have hgfix : g * B.b 1 * g⁻¹ = B.b 1 := by simpa only [if_neg hT1] using hact 1
  have hgC : g ∈ C := by
    refine ⟨?_, hg⟩
    change g ∈ centralizer ({B.b 1} : Set G)
    rw [mem_centralizer_iff]
    rintro x rfl
    have h := congrArg (fun x : G => x * g) hgfix
    simpa only [inv_mul_cancel_right] using h.symm
  have hbC : B.b i.succ.succ ∈ C := by
    refine ⟨?_, hB.2.2 _ (by fin_cases i <;> decide)⟩
    change B.b i.succ.succ ∈ centralizer ({B.b 1} : Set G)
    rw [mem_centralizer_iff]
    rintro x rfl
    exact (B.comm 1 i.succ.succ).eq
  have hbinv : g * B.b i.succ.succ * g⁻¹ = (B.b i.succ.succ)⁻¹ := by
    simpa [T] using hact i.succ.succ
  have hb3 : B.b i.succ.succ ^ 3 = 1 := by
    simpa only [B.ord i.succ.succ] using pow_orderOf_eq_one (B.b i.succ.succ)
  have hb2 : B.b i.succ.succ * B.b i.succ.succ = (B.b i.succ.succ)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [pow_succ, pow_zero, one_mul] using hb3)
  have hmem := Subgroup.commutator_mem_commutator hgC hbC
  rwa [commutatorElement_def, hbinv, ← mul_inv_rev, hb2, inv_inv] at hmem

theorem commutator_centralizer_le_beta_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8) :
    ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ K ∧
      ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤
        centralizer ({b₀ * B.b 1} : Set G) := by
  let C : Subgroup G := centralizer ({B.b 1} : Set G) ⊓ K
  have hDC : ⁅C, C⁆ ≤ C := commutator_le_self C
  refine ⟨hDC.trans inf_le_right, hDC.trans ?_⟩
  intro c hc
  rw [mem_centralizer_iff]
  rintro x rfl
  have hb₀c : b₀ * c = c * b₀ :=
    mem_centralizer_iff.mp (hstd.2.1.1.2.1 hc.2) b₀ (Set.mem_singleton b₀)
  have hb₁c : B.b 1 * c = c * B.b 1 :=
    mem_centralizer_iff.mp hc.1 (B.b 1) (Set.mem_singleton (B.b 1))
  calc (b₀ * B.b 1) * c = b₀ * (B.b 1 * c) := mul_assoc _ _ _
    _ = b₀ * (c * B.b 1) := by rw [hb₁c]
    _ = (b₀ * c) * B.b 1 := (mul_assoc _ _ _).symm
    _ = (c * b₀) * B.b 1 := by rw [hb₀c]
    _ = c * (b₀ * B.b 1) := mul_assoc _ _ _

end CFSG.StandardType.FrameRoute.FS81
