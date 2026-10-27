module

public import CFSG.LocalAnalysis.StandardType.PhanEResSL
public import CFSG.LocalAnalysis.StandardType.PhanELeviA3

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open Matrix CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

namespace Res

open CFSG.LieType.Steinberg.CentralExt.SLClosed

private lemma p9uRC_tv_eq {m : ℕ} (p q : Fin (m + 1)) (hpq : p ≠ q) (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld p q c = CFSG.Timmesfeld.tv p q c := by
  rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne hpq,
    CFSG.Timmesfeld.tv_of_ne hpq]

private lemma p9uRC_pathRoot_one_01 (e : Fin 1 → Fin D.rank) :
    pathRoot e (0 : Fin 2) (1 : Fin 2) = Pi.single (e 0) 1 := by
  simp [pathRoot, Fin.sum_univ_one]

private lemma p9uRC_pathRoot_one_10 (e : Fin 1 → Fin D.rank) :
    pathRoot e (1 : Fin 2) (0 : Fin 2) = -Pi.single (e 0) 1 := by
  simp [pathRoot, Fin.sum_univ_one]

private lemma p9uRC_pathRoot_two_01 (e : Fin 2 → Fin D.rank) :
    pathRoot e (0 : Fin 3) (1 : Fin 3) = Pi.single (e 0) 1 := by
  simp [pathRoot, Fin.sum_univ_two]

private lemma p9uRC_pathRoot_two_10 (e : Fin 2 → Fin D.rank) :
    pathRoot e (1 : Fin 3) (0 : Fin 3) = -Pi.single (e 0) 1 := by
  simp [pathRoot, Fin.sum_univ_two]

private lemma p9uRC_pathRoot_two_12 (e : Fin 2 → Fin D.rank) :
    pathRoot e (1 : Fin 3) (2 : Fin 3) = Pi.single (e 1) 1 := by
  simp [pathRoot, Fin.sum_univ_two]

private lemma p9uRC_pathRoot_two_21 (e : Fin 2 → Fin D.rank) :
    pathRoot e (2 : Fin 3) (1 : Fin 3) = -Pi.single (e 1) 1 := by
  simp [pathRoot, Fin.sum_univ_two]

private lemma p9uRC_pathRoot_two_02 (e : Fin 2 → Fin D.rank) :
    pathRoot e (0 : Fin 3) (2 : Fin 3) = Pi.single (e 0) 1 + Pi.single (e 1) 1 := by
  simp [pathRoot, Fin.sum_univ_two]

private lemma p9uRC_pathRoot_two_20 (e : Fin 2 → Fin D.rank) :
    pathRoot e (2 : Fin 3) (0 : Fin 3) = -(Pi.single (e 0) 1 + Pi.single (e 1) 1) := by
  simp [pathRoot, Fin.sum_univ_two]

theorem a3Root_eq_pathRoot (e : Fin 3 → Fin D.rank) (p q : Fin 4) :
    a3Root e p q = pathRoot e p q := by
  rfl

variable (M : ChevModel2 D n H Fld)

theorem isA2Chart_of_slPath (L : SLPath M 2) : IsA2Chart M L.ε (L.e 0) (L.e 1) := by
  intro c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← p9uRC_tv_eq (0 : Fin 3) (1 : Fin 3) (by decide) c,
      L.tv_eq (0 : Fin 3) (1 : Fin 3) (by decide) c, p9uRC_pathRoot_two_01 L.e]
  · rw [← p9uRC_tv_eq (1 : Fin 3) (0 : Fin 3) (by decide) c,
      L.tv_eq (1 : Fin 3) (0 : Fin 3) (by decide) c, p9uRC_pathRoot_two_10 L.e]
  · rw [← p9uRC_tv_eq (1 : Fin 3) (2 : Fin 3) (by decide) c,
      L.tv_eq (1 : Fin 3) (2 : Fin 3) (by decide) c, p9uRC_pathRoot_two_12 L.e]
  · rw [← p9uRC_tv_eq (2 : Fin 3) (1 : Fin 3) (by decide) c,
      L.tv_eq (2 : Fin 3) (1 : Fin 3) (by decide) c, p9uRC_pathRoot_two_21 L.e]
  · rw [← p9uRC_tv_eq (0 : Fin 3) (2 : Fin 3) (by decide) c,
      L.tv_eq (0 : Fin 3) (2 : Fin 3) (by decide) c, p9uRC_pathRoot_two_02 L.e]
  · rw [← p9uRC_tv_eq (2 : Fin 3) (0 : Fin 3) (by decide) c,
      L.tv_eq (2 : Fin 3) (0 : Fin 3) (by decide) c, p9uRC_pathRoot_two_20 L.e]

theorem exists_slPath_two_of_isA2Chart (e : Fin 2 → Fin D.rank) (he : Function.Injective e)
    (hc : ∀ k l : Fin 2, D.cartan (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0)
    {l : SL(3, Fld) →* K} (hl : IsA2Chart M l (e 0) (e 1)) : ∃ L : SLPath M 2, L.e = e := by
  refine ⟨⟨e, he, hc, l, ?_⟩, rfl⟩
  intro p q hpq c
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · change l (tv Fld (0 : Fin 3) (1 : Fin 3) c) =
      M.x (pathRoot e (0 : Fin 3) (1 : Fin 3)) c
    rw [p9uRC_tv_eq (0 : Fin 3) (1 : Fin 3) (by decide) c, (hl c).1,
      p9uRC_pathRoot_two_01 e]
  · change l (tv Fld (0 : Fin 3) (2 : Fin 3) c) =
      M.x (pathRoot e (0 : Fin 3) (2 : Fin 3)) c
    rw [p9uRC_tv_eq (0 : Fin 3) (2 : Fin 3) (by decide) c, (hl c).2.2.2.2.1,
      p9uRC_pathRoot_two_02 e]
  · change l (tv Fld (1 : Fin 3) (0 : Fin 3) c) =
      M.x (pathRoot e (1 : Fin 3) (0 : Fin 3)) c
    rw [p9uRC_tv_eq (1 : Fin 3) (0 : Fin 3) (by decide) c, (hl c).2.1,
      p9uRC_pathRoot_two_10 e]
  · exact absurd rfl hpq
  · change l (tv Fld (1 : Fin 3) (2 : Fin 3) c) =
      M.x (pathRoot e (1 : Fin 3) (2 : Fin 3)) c
    rw [p9uRC_tv_eq (1 : Fin 3) (2 : Fin 3) (by decide) c, (hl c).2.2.1,
      p9uRC_pathRoot_two_12 e]
  · change l (tv Fld (2 : Fin 3) (0 : Fin 3) c) =
      M.x (pathRoot e (2 : Fin 3) (0 : Fin 3)) c
    rw [p9uRC_tv_eq (2 : Fin 3) (0 : Fin 3) (by decide) c, (hl c).2.2.2.2.2,
      p9uRC_pathRoot_two_20 e]
  · change l (tv Fld (2 : Fin 3) (1 : Fin 3) c) =
      M.x (pathRoot e (2 : Fin 3) (1 : Fin 3)) c
    rw [p9uRC_tv_eq (2 : Fin 3) (1 : Fin 3) (by decide) c, (hl c).2.2.2.1,
      p9uRC_pathRoot_two_21 e]
  · exact absurd rfl hpq

variable {adj : Fin D.rank → Fin D.rank → Prop}
  (hD : CFSG.Timmesfeld.SimplyLacedLevis D Fld adj M.x)

include hD in
theorem exists_slPath_one (e : Fin 1 → Fin D.rank)
    (hc : ∀ k l : Fin 1, D.cartan (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) :
    ∃ L : SLPath M 1, L.e = e := by
  obtain ⟨l, -, hl⟩ := hD.sl2 (e 0)
  refine ⟨⟨e, fun a b _ => Subsingleton.elim a b, hc, l, ?_⟩, rfl⟩
  intro p q hpq c
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · change l (tv Fld (0 : Fin 2) (1 : Fin 2) c) =
      M.x (pathRoot e (0 : Fin 2) (1 : Fin 2)) c
    rw [p9uRC_tv_eq (0 : Fin 2) (1 : Fin 2) (by decide) c, (hl c).1,
      p9uRC_pathRoot_one_01 e]
  · change l (tv Fld (1 : Fin 2) (0 : Fin 2) c) =
      M.x (pathRoot e (1 : Fin 2) (0 : Fin 2)) c
    rw [p9uRC_tv_eq (1 : Fin 2) (0 : Fin 2) (by decide) c, (hl c).2,
      p9uRC_pathRoot_one_10 e]
  · exact absurd rfl hpq

include hD in
theorem exists_slPath_two [CharP Fld 2] (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a)
    (e : Fin 2 → Fin D.rank) (he : Function.Injective e)
    (hc : ∀ k l : Fin 2, D.cartan (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) :
    ∃ L : SLPath M 2, L.e = e := by
  have h01 : D.cartan (e 0) (e 1) = -1 := by simpa using hc (0 : Fin 2) (1 : Fin 2)
  rcases hadj (e 0) (e 1) h01 with h | h
  · obtain ⟨l, -, hl⟩ := hD.sl3 (e 0) (e 1) h
    exact exists_slPath_two_of_isA2Chart M e he hc (fun c => hl c)
  · obtain ⟨l, -, hl⟩ := hD.sl3 (e 1) (e 0) h
    let e' : Fin 2 → Fin D.rank := ![e 1, e 0]
    have he' : Function.Injective e' := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        first
          | rfl
          | exact absurd (he (by simpa [e'] using hab)) (by decide)
    have hc' : ∀ k l : Fin 2, D.cartan (e' k) (e' l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0 := by
      intro k l
      fin_cases k <;> fin_cases l
      · simpa [e'] using hc (1 : Fin 2) (1 : Fin 2)
      · simpa [e'] using hc (1 : Fin 2) (0 : Fin 2)
      · simpa [e'] using hc (0 : Fin 2) (1 : Fin 2)
      · simpa [e'] using hc (0 : Fin 2) (0 : Fin 2)
    have hl' : IsA2Chart M l (e' 0) (e' 1) := by
      intro c
      simpa [e'] using hl c
    obtain ⟨L', hL'e⟩ := exists_slPath_two_of_isA2Chart M e' he' hc' hl'
    refine ⟨L'.reverse, ?_⟩
    funext k
    rw [SLPath.reverse_e L' k, hL'e]
    fin_cases k <;> simp [e']

include hD in
theorem commute_blk_of_levis (hnadj : ∀ a b, D.cartan a b = 0 → ¬ adj a b) {a b c : Fin D.rank}
    (hac : a ≠ c) (hac0 : D.cartan a c = 0) (hca0 : D.cartan c a = 0)
    {θ₀ θ₁ : SL(3, Fld) →* K} (h₀ : IsA2Chart M θ₀ a b) (h₁ : IsA2Chart M θ₁ b c) :
    ∀ A B : SL(2, Fld), Commute (θ₀ (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 A))
      (θ₁ (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 B)) := by
  intro A B
  obtain ⟨l, -, hl⟩ := hD.sl2sl2 a c hac (hnadj a c hac0) (hnadj c a hca0)
  have hθ0 : θ₀.comp (CFSG.ClassicalInvolution.WeakCT.blk Fld 0) =
      l.comp (MonoidHom.inl (SL(2, Fld)) (SL(2, Fld))) := by
    refine MonoidHom.eq_of_eqOn_dense (CFSG.Timmesfeld.closure_tv_two (F := Fld)) ?_
    rintro x (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · show θ₀ (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 (CFSG.Timmesfeld.tv 0 1 d)) =
        l ((MonoidHom.inl (SL(2, Fld)) (SL(2, Fld))) (CFSG.Timmesfeld.tv 0 1 d))
      rw [CFSG.ClassicalInvolution.WeakCT.blk_zero_tv01, MonoidHom.inl_apply, (h₀ d).1,
        (hl d).1]
    · show θ₀ (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 (CFSG.Timmesfeld.tv 1 0 d)) =
        l ((MonoidHom.inl (SL(2, Fld)) (SL(2, Fld))) (CFSG.Timmesfeld.tv 1 0 d))
      rw [CFSG.ClassicalInvolution.WeakCT.blk_zero_tv10, MonoidHom.inl_apply, (h₀ d).2.1,
        (hl d).2.1]
  have hθ1 : θ₁.comp (CFSG.ClassicalInvolution.WeakCT.blk Fld 1) =
      l.comp (MonoidHom.inr (SL(2, Fld)) (SL(2, Fld))) := by
    refine MonoidHom.eq_of_eqOn_dense (CFSG.Timmesfeld.closure_tv_two (F := Fld)) ?_
    rintro x (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · show θ₁ (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 (CFSG.Timmesfeld.tv 0 1 d)) =
        l ((MonoidHom.inr (SL(2, Fld)) (SL(2, Fld))) (CFSG.Timmesfeld.tv 0 1 d))
      rw [CFSG.ClassicalInvolution.WeakCT.blk_one_tv01, MonoidHom.inr_apply, (h₁ d).2.2.1,
        (hl d).2.2.1]
    · show θ₁ (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 (CFSG.Timmesfeld.tv 1 0 d)) =
        l ((MonoidHom.inr (SL(2, Fld)) (SL(2, Fld))) (CFSG.Timmesfeld.tv 1 0 d))
      rw [CFSG.ClassicalInvolution.WeakCT.blk_one_tv10, MonoidHom.inr_apply, (h₁ d).2.2.2.1,
        (hl d).2.2.2]
  show θ₀ (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 A) *
      θ₁ (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 B) =
    θ₁ (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 B) *
      θ₀ (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 A)
  have hA : θ₀ (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 A) =
      l ((MonoidHom.inl (SL(2, Fld)) (SL(2, Fld))) A) := DFunLike.congr_fun hθ0 A
  have hB : θ₁ (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 B) =
      l ((MonoidHom.inr (SL(2, Fld)) (SL(2, Fld))) B) := DFunLike.congr_fun hθ1 B
  rw [hA, hB, ← map_mul, ← map_mul]
  congr 1
  simp [Prod.mk_mul_mk]

include hD in
theorem exists_slPath_three [CharP Fld 2] (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a)
    (hnadj : ∀ a b, D.cartan a b = 0 → ¬ adj a b) (e : Fin 3 → Fin D.rank)
    (he : Function.Injective e)
    (hc : ∀ k l : Fin 3, D.cartan (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) :
    ∃ L : SLPath M 3, L.e = e := by
  have h01 : D.cartan (e 0) (e 1) = -1 := by simpa using hc (0 : Fin 3) (1 : Fin 3)
  have h12 : D.cartan (e 1) (e 2) = -1 := by simpa using hc (1 : Fin 3) (2 : Fin 3)
  have h02 : D.cartan (e 0) (e 2) = 0 := by simpa using hc (0 : Fin 3) (2 : Fin 3)
  have h20 : D.cartan (e 2) (e 0) = 0 := by simpa using hc (2 : Fin 3) (0 : Fin 3)
  have he02 : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (he h)
  let e₀ : Fin 2 → Fin D.rank := ![e 0, e 1]
  let e₁ : Fin 2 → Fin D.rank := ![e 1, e 2]
  have he₀ : Function.Injective e₀ := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact absurd (he (by simpa [e₀] using hab)) (by decide)
  have he₁ : Function.Injective e₁ := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact absurd (he (by simpa [e₁] using hab)) (by decide)
  have hc₀ : ∀ k l : Fin 2, D.cartan (e₀ k) (e₀ l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0 := by
    intro k l
    fin_cases k <;> fin_cases l
    · simpa [e₀] using hc (0 : Fin 3) (0 : Fin 3)
    · simpa [e₀] using hc (0 : Fin 3) (1 : Fin 3)
    · simpa [e₀] using hc (1 : Fin 3) (0 : Fin 3)
    · simpa [e₀] using hc (1 : Fin 3) (1 : Fin 3)
  have hc₁ : ∀ k l : Fin 2, D.cartan (e₁ k) (e₁ l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0 := by
    intro k l
    fin_cases k <;> fin_cases l
    · simpa [e₁] using hc (1 : Fin 3) (1 : Fin 3)
    · simpa [e₁] using hc (1 : Fin 3) (2 : Fin 3)
    · simpa [e₁] using hc (2 : Fin 3) (1 : Fin 3)
    · simpa [e₁] using hc (2 : Fin 3) (2 : Fin 3)
  obtain ⟨L₀, hL₀e⟩ := exists_slPath_two M hD hadj e₀ he₀ hc₀
  obtain ⟨L₁, hL₁e⟩ := exists_slPath_two M hD hadj e₁ he₁ hc₁
  have h₀ : IsA2Chart M L₀.ε (e 0) (e 1) := by
    simpa [hL₀e, e₀] using isA2Chart_of_slPath M L₀
  have h₁ : IsA2Chart M L₁.ε (e 1) (e 2) := by
    simpa [hL₁e, e₁] using isA2Chart_of_slPath M L₁
  have hcomm : ∀ A B : SL(2, Fld),
      Commute (L₀.ε (CFSG.ClassicalInvolution.WeakCT.blk Fld 0 A))
        (L₁.ε (CFSG.ClassicalInvolution.WeakCT.blk Fld 1 B)) :=
    commute_blk_of_levis M hD hnadj he02 h02 h20 h₀ h₁
  obtain ⟨ε, hε⟩ := exists_leviA3 e hc h₀ h₁ hcomm
  refine ⟨⟨e, he, hc, ε, ?_⟩, rfl⟩
  intro p q hpq c
  rw [← a3Root_eq_pathRoot e p q]
  exact hε p q hpq c

include hD in
theorem exists_slPath_of_levis [CharP Fld 2]
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a)
    (hnadj : ∀ a b, D.cartan a b = 0 → ¬ adj a b) :
    ∀ (m : ℕ) (e : Fin m → Fin D.rank), 1 ≤ m → m ≤ 3 → Function.Injective e →
      (∀ k l : Fin m, D.cartan (e k) (e l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) →
      ∃ L : SLPath M m, L.e = e := by
  intro m e h1 h3 he hc
  interval_cases m
  · exact exists_slPath_one M hD e hc
  · exact exists_slPath_two M hD hadj e he hc
  · exact exists_slPath_three M hD hadj hnadj e he hc

end Res

end CFSG.ClassicalInvolution.Phan.PhanE

end
