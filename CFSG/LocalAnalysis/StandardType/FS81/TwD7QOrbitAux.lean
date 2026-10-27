module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCent
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutTwD7
public import CFSG.LocalAnalysis.StandardType.FS81.D6Refl
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Open CFSG.Assembly
open scoped Matrix

open TwD7Q

@[expose] def twD7VBeta : Coords 8 := Pi.single 0 1 + Pi.single 1 1

private def qIdx (j : Fin 7) : Fin 8 := if j = 0 then 0 else j.succ

private theorem qIdx_zero : qIdx 0 = 0 := by simp [qIdx]

private theorem qIdx_succ (i : Fin 6) : qIdx i.succ = i.succ.succ := by simp [qIdx]

private theorem qIdx_ne_one (j : Fin 7) : qIdx j ≠ 1 := by
  fin_cases j <;> decide

private theorem qIdx_injective : Function.Injective qIdx := by
  decide +kernel

private theorem qIdx_exists_of_ne_one : ∀ k : Fin 8, k ≠ 1 → ∃ j : Fin 7, qIdx j = k := by
  decide +kernel

private theorem quotCoords_single_qIdx (c : ZMod 3) (i : Fin 7) :
    Basis3.quotCoords (Pi.single (qIdx i) c : Coords 8) = (Pi.single i c : Coords 7) := by
  ext k
  revert c
  fin_cases i <;> fin_cases k <;> decide

private theorem isD6Root_quotCoords_check :
    ∀ (a b : ZMod 3) (g : Fin 6 → ZMod 3),
      let f : Coords 8 := Fin.cons a (Fin.cons b g)
      (wt f = 1 ∨ wt f = 4 ∨ wt f = 7) →
      (wt (twD7VBeta - f) = 1 ∨ wt (twD7VBeta - f) = 4 ∨ wt (twD7VBeta - f) = 7) →
      (wt (twD7VBeta + f) = 2 ∨ (wt (twD7VBeta + f) = 8 ∧
        ∏ i : Fin 8, (twD7VBeta + f) i = -1)) →
      IsD6Root (Basis3.quotCoords f) := by
  intro a b
  rcases (show a = 0 ∨ a = 1 ∨ a = -1 by decide +revert) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = -1 by decide +revert) with rfl | rfl | rfl <;>
    decide +kernel

theorem isD6Root_quotCoords_of_wt {f : Coords 8}
    (h1 : wt f = 1 ∨ wt f = 4 ∨ wt f = 7)
    (h2 : wt (twD7VBeta - f) = 1 ∨ wt (twD7VBeta - f) = 4 ∨ wt (twD7VBeta - f) = 7)
    (h3 : wt (twD7VBeta + f) = 2 ∨ (wt (twD7VBeta + f) = 8 ∧
      ∏ i : Fin 8, (twD7VBeta + f) i = -1)) :
    IsD6Root (Basis3.quotCoords f) := by
  have hf : f = Fin.cons (f 0) (Fin.cons (f 1) fun i : Fin 6 => f i.succ.succ) := by
    funext i
    fin_cases i <;> rfl
  rw [hf] at h1 h2 h3 ⊢
  exact isD6Root_quotCoords_check (f 0) (f 1) (fun i => f i.succ.succ) h1 h2 h3

private theorem mem_evenFix0_six_of_mulVec_quotCoords
    {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} {x : Matrix (Fin 7) (Fin 7) (ZMod 3)}
    (hM : M ∈ evenFix0 7)
    (hMe1 : M *ᵥ (Pi.single (1 : Fin 8) 1 : Coords 8) = Pi.single 1 1)
    (hx : ∀ j : Fin 7, x *ᵥ (Pi.single j 1 : Coords 7) =
      Basis3.quotCoords (M *ᵥ (Pi.single (qIdx j) 1 : Coords 8))) :
    x ∈ evenFix0 6 := by
  classical
  obtain ⟨σ, s, hs, ⟨hσ0, hs0, hprod⟩, rfl⟩ := hM
  have hcol1 : (Pi.single (σ 1) (s 1 * 1) : Coords 8) = Pi.single (1 : Fin 8) 1 := by
    rwa [spMat_mulVec_single] at hMe1
  have hσ1 : σ 1 = 1 := by
    by_contra h
    have h2 := congrFun hcol1 1
    rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_same] at h2
    exact zero_ne_one h2
  have hs1 : s 1 = 1 := by
    have h2 := congrFun hcol1 (σ 1)
    rw [Pi.single_eq_same, hσ1, Pi.single_eq_same] at h2
    simpa using h2
  have hσq_ne : ∀ j : Fin 7, σ (qIdx j) ≠ 1 := by
    intro j h
    exact qIdx_ne_one j (σ.injective (h.trans hσ1.symm))
  choose τ hτ using fun j => qIdx_exists_of_ne_one (σ (qIdx j)) (hσq_ne j)
  have hτinj : Function.Injective τ := by
    intro i j hij
    have h : qIdx (τ i) = qIdx (τ j) := by rw [hij]
    rw [hτ i, hτ j] at h
    exact qIdx_injective (σ.injective h)
  let σ' : Equiv.Perm (Fin 7) := Equiv.ofBijective τ hτinj.bijective_of_finite
  have hσ' : ∀ j, qIdx (σ' j) = σ (qIdx j) := fun j => hτ j
  let s' : Fin 7 → ZMod 3 := fun j => s (qIdx j)
  have hs' : IsSign s' := fun j => hs (qIdx j)
  have hxsp : x = spMat σ' s' := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [hx j, spMat_mulVec_single σ s (qIdx j),
      show σ (qIdx j) = qIdx (σ' j) from (hσ' j).symm, quotCoords_single_qIdx,
      spMat_mulVec_single σ' s' j, mul_one]
  rw [evenFix0, spSet]
  refine ⟨σ', s', hs', ⟨?_, ?_, ?_⟩, hxsp⟩
  · apply qIdx_injective
    rw [hσ' 0, qIdx_zero, hσ0]
  · show s (qIdx 0) = 1
    rw [qIdx_zero]
    exact hs0
  · show ∏ i : Fin 6, s (qIdx i.succ) = 1
    have hstep : (∏ i : Fin 7, s i.succ) = s 1 * ∏ i : Fin 6, s i.succ.succ := by
      rw [Fin.prod_univ_succ]
      rfl
    have hstep' : (∏ i : Fin 7, s i.succ) = ∏ i : Fin 6, s i.succ.succ := by
      rw [hstep, hs1, one_mul]
    calc ∏ i : Fin 6, s (qIdx i.succ) = ∏ i : Fin 6, s i.succ.succ := by
          apply Finset.prod_congr rfl
          intro i _
          rw [qIdx_succ i]
      _ = 1 := by rw [← hstep', hprod]

theorem mem_evenFix0_six_of_acts_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) {n : Q (B.b 0 * B.b 1)}
    {A : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hA : B.twD7Quot.Acts n A)
    (hAe : A *ᵥ Pi.single (0 : Fin 7) 1 = Pi.single 0 1) : A ∈ evenFix0 6 := by
  classical
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hA', -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, hKn, -, -, -, -⟩ := hA'
  obtain ⟨-, hdisj, -⟩ := hCanon
  have hrec' : RecOutTwD7 B (B.b 0) := by rw [hB.2.1]; exact hrec
  have hvecβ : B.vec twD7VBeta = B.b 0 * B.b 1 := by
    rw [twD7VBeta, B.vec_add, B.vec_single, B.vec_single]
  have hβmem : B.b 0 * B.b 1 ∈ B.span := by
    rw [← hvecβ]
    exact B.vec_mem_span twD7VBeta
  have hspanCen : B.span ≤ cen (B.b 0 * B.b 1) := by
    intro y hy
    obtain ⟨v, rfl⟩ := B.exists_vec_eq hy
    exact B.vec_mem_cen_twD7 v
  have hcol : ∀ j : Fin 7,
      n * B.twD7Quot.b j * n⁻¹ = B.twD7Quot.vec (A *ᵥ Pi.single j 1) := by
    intro j
    rw [← B.twD7Quot.vec_single j, B.twD7Quot.acts_vec hA]
  obtain ⟨c, hc⟩ := pr_surjective (B.b 0 * B.b 1) n
  have hcN : (c : G) ∈ normalizer (B.span : Set G) := by
    refine (pr_mem_normalizer_img_iff hβmem hspanCen).mp ?_
    rw [← B.twD7Quot_span, hc]
    exact B.twD7Quot.mem_normalizer_of_acts hA
  have hcent : n ∈ centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))) := by
    rw [mem_centralizer_singleton_iff]
    have h : n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.b 0 := by
      rw [hcol 0, hAe, B.twD7Quot.vec_single]
    calc n * B.twD7Quot.b 0 = (n * B.twD7Quot.b 0 * n⁻¹) * n := by group
      _ = B.twD7Quot.b 0 * n := by rw [h]
  rw [← hc] at hcent
  have hcCent0 : (c : G) ∈ centralizer ({B.b 0} : Set G) :=
    (B.pr_mem_centralizer_twD7Quot_b_zero_iff hrec' c).mp hcent
  have hb0comm : (c : G) * B.b 0 = B.b 0 * c := mem_centralizer_singleton_iff.mp hcCent0
  have hcCent : (c : G) ∈ centralizer ({b₀} : Set G) := by
    have hset : ({b₀} : Set G) = {B.b 0} := by rw [hB.2.1]
    exact hset.symm ▸ hcCent0
  have hβcen : (c : G) * (B.b 0 * B.b 1) = (B.b 0 * B.b 1) * c := mem_cen_iff.mp c.2
  have hconj_b1 : (c : G) * B.b 1 * (c : G)⁻¹ = B.b 1 := by
    have hβconj : (c : G) * (B.b 0 * B.b 1) * (c : G)⁻¹ = B.b 0 * B.b 1 := by
      rw [hβcen]; group
    calc (c : G) * B.b 1 * (c : G)⁻¹
        = ((c : G) * B.b 0 * (c : G)⁻¹)⁻¹ *
            ((c : G) * (B.b 0 * B.b 1) * (c : G)⁻¹) := by group
      _ = B.b 1 := by
            rw [show (c : G) * B.b 0 * (c : G)⁻¹ = B.b 0 from by rw [hb0comm]; group,
              hβconj]
            group
  obtain ⟨M, hMacts⟩ := B.exists_acts hcN
  have hMeven : M ∈ evenFix0 7 :=
    (realized_centralizer_subset_evenFix0_of_recOutTwD7 hB hKC hKn hdisj hrec)
      ⟨c, hcCent, hMacts⟩
  have hMe1 : M *ᵥ (Pi.single (1 : Fin 8) 1 : Coords 8) = Pi.single 1 1 := by
    apply B.vec_injective
    have h := B.acts_vec hMacts (Pi.single (1 : Fin 8) 1)
    rw [B.vec_single, hconj_b1] at h
    rw [← h, B.vec_single]
  have hquot : ∀ j : Fin 7, B.twD7Quot.b j =
      pr (B.b 0 * B.b 1) ⟨B.b (qIdx j), B.b_mem_cen_twD7 _⟩ := by
    intro j
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ j
    · rw [qIdx_zero]
      exact (B.pr_b_zero_twD7Quot).symm
    · rw [qIdx_succ]
      exact (B.pr_b_succ_succ_twD7Quot k).symm
  have hxcol : ∀ j : Fin 7, A *ᵥ (Pi.single j 1 : Coords 7) =
      Basis3.quotCoords (M *ᵥ (Pi.single (qIdx j) 1 : Coords 8)) := by
    intro j
    apply B.twD7Quot.vec_injective
    rw [← hcol j]
    calc n * B.twD7Quot.b j * n⁻¹
        = pr (B.b 0 * B.b 1) (c * ⟨B.b (qIdx j), B.b_mem_cen_twD7 _⟩ * c⁻¹) := by
          rw [hquot, ← hc]
          rw [← map_inv, ← map_mul, ← map_mul]
      _ = pr (B.b 0 * B.b 1) ⟨B.vec (M *ᵥ (Pi.single (qIdx j) 1 : Coords 8)),
            B.vec_mem_cen_twD7 _⟩ := by
          congr 1
          apply Subtype.ext
          show (c : G) * B.b (qIdx j) * (c : G)⁻¹ =
            B.vec (M *ᵥ (Pi.single (qIdx j) 1 : Coords 8))
          have hb : B.b (qIdx j) = B.vec (Pi.single (qIdx j) 1 : Coords 8) :=
            (B.vec_single (qIdx j)).symm
          rw [hb, B.acts_vec hMacts]
      _ = B.twD7Quot.vec (Basis3.quotCoords (M *ᵥ (Pi.single (qIdx j) 1 : Coords 8))) :=
          B.pr_vec_twD7Quot _ _
  exact mem_evenFix0_six_of_mulVec_quotCoords hMeven hMe1 hxcol

theorem card_twD7Quot_stabilizer_le {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    Nat.card {A : ↥((ggAutomizer ⊤ B.twD7Quot.span).map B.twD7Quot.glHom) //
      (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single (0 : Fin 7) 1 =
        Pi.single 0 1} ≤ 23040 := by
  classical
  have key : ∀ A : ↥((ggAutomizer ⊤ B.twD7Quot.span).map B.twD7Quot.glHom),
      (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single (0 : Fin 7) 1 = Pi.single 0 1 →
      (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenFix0 6 := by
    intro A hAe
    obtain ⟨φ, n, -, hnact, hxeq⟩ := B.twD7Quot.exists_of_mem_xg A.2
    rw [← hxeq, Basis3.coe_glHom] at hAe ⊢
    exact mem_evenFix0_six_of_acts_twD7Quot hstd hB hrec (B.twD7Quot.acts_matOf hnact) hAe
  calc Nat.card {A : ↥((ggAutomizer ⊤ B.twD7Quot.span).map B.twD7Quot.glHom) //
        (A.1 : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single (0 : Fin 7) 1 = Pi.single 0 1}
      ≤ Nat.card ↥(evenFix0 6) :=
        Nat.card_le_card_of_injective
          (fun A => (⟨A.1.1, key A.1 A.2⟩ : ↥(evenFix0 6)))
          (fun a b h => by
            apply Subtype.ext
            apply Subtype.ext
            exact Units.ext (congrArg Subtype.val h))
    _ ≤ 23040 := card_evenFix0_le

end CFSG.StandardType.FrameRoute.FS81

end
