module

public import CFSG.Timmesfeld.Transvection.PresSURel

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F}

open Classical in
@[expose] noncomputable def commData (σ : F ≃+* F) (a b c d : Fin r ⊕ Fin r) (s t : F) :
    Option ((Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) ×
      Option ((Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) ×
      Option ((Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) × F) :=
  if b = a then
    if d = c then (none, none, none)
    else if c = Sum.swap a then (some (a, d, s * t), none, some (d, d, s * σ t * t))
    else if d = Sum.swap a then (some (a, c, s * σ t), none, some (c, c, s * t * σ t))
    else (none, none, none)
  else if d = c then
    if c = Sum.swap b then (some (a, Sum.swap b, s * t), some (a, a, σ s * s * t), none)
    else if c = Sum.swap a then (some (b, Sum.swap a, σ s * t), some (b, b, s * σ s * t), none)
    else (none, none, none)
  else if c = Sum.swap a then
    if d = b then (some (b, b, σ s * t + s * σ t), none, none)
    else (some (b, d, σ s * t), none, none)
  else if c = Sum.swap b then
    if d = a then (some (a, a, s * t + σ s * σ t), none, none)
    else (some (a, d, s * t), none, none)
  else if d = Sum.swap a then
    if c = b then (some (b, b, σ s * σ t + s * t), none, none)
    else (some (b, c, σ s * σ t), none, none)
  else if d = Sum.swap b then
    if c = a then (some (a, a, s * σ t + σ s * t), none, none)
    else (some (a, c, s * σ t), none, none)
  else (none, none, none)

theorem rt_add_rt_swap (a b d : Fin r ⊕ Fin r) :
    rt a b + rt (Sum.swap a) d = rt b d := by
  simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel

theorem swap_ne_of_idx_ne' {a b : Fin r ⊕ Fin r} (h : idx a ≠ idx b) : Sum.swap b ≠ a :=
  fun e => h (by rw [← e, idx_swap])

theorem relValid_short {a b : Fin r ⊕ Fin r} (h : idx a ≠ idx b) (c : F) :
    RElValid σ (a, b, c) :=
  ⟨ne_swap_of_idx_ne h, fun e => absurd e (ne_of_idx_ne h)⟩

theorem relValid_long (a : Fin r ⊕ Fin r) {c : F} (h : σ c = c) : RElValid σ (a, a, c) :=
  ⟨(swap_ne_self a).symm, fun _ => h⟩

namespace SURelations

variable {G : Type*} [Group G] (R : SURelations r σ G) [CharP F 2] (hσ : ∀ c, σ (σ c) = c)

include hσ in
theorem comm_eval {a b c d : Fin r ⊕ Fin r} {s t : F} (hu : RElValid σ (a, b, s))
    (hv : RElValid σ (c, d, t)) (hne : rt a b + rt c d ≠ 0) :
    (∀ e ∈ (commData σ a b c d s t).1, RElValid σ e ∧ rt e.1 e.2.1 = rt a b + rt c d) ∧
    (∀ e ∈ (commData σ a b c d s t).2.1, RElValid σ e ∧ rt e.1 e.2.1 = 2 • rt a b + rt c d) ∧
    (∀ e ∈ (commData σ a b c d s t).2.2, RElValid σ e ∧ rt e.1 e.2.1 = rt a b + 2 • rt c d) ∧
    ⁅R.eval (a, b, s), R.eval (c, d, t)⁆ = R.evalO (commData σ a b c d s t).1 *
      R.evalO (commData σ a b c d s t).2.1 * R.evalO (commData σ a b c d s t).2.2 := by
  obtain ⟨hab, hsf⟩ := hu
  obtain ⟨hcd, htf⟩ := hv
  simp only at hab hsf hcd htf
  have sw : ∀ x : Fin r ⊕ Fin r, Sum.swap x ≠ x := swap_ne_self
  have sw' : ∀ x : Fin r ⊕ Fin r, x ≠ Sum.swap x := fun x => (swap_ne_self x).symm
  have hopp : ∀ x y : Fin r ⊕ Fin r, rt x y + rt (Sum.swap x) (Sum.swap y) = 0 := fun x y => by
    rw [rt_swap_swap, add_neg_cancel]
  have hopp' : ∀ x y : Fin r ⊕ Fin r, rt x y + rt (Sum.swap y) (Sum.swap x) = 0 := fun x y => by
    rw [rt_comm (Sum.swap y), rt_swap_swap, add_neg_cancel]
  by_cases hba : b = a
  ·
    subst hba
    have hs := hsf rfl
    rw [R.eval_long]
    by_cases hdc : d = c
    ·
      subst hdc
      have ht := htf rfl
      have hcb : d ≠ Sum.swap b := fun h => hne (by rw [h]; exact hopp b b)
      simp only [commData, ite_true]
      refine ⟨by simp, by simp, by simp, ?_⟩
      rw [R.eval_long, R.commLL b d hcb s t hs ht, evalO_none, mul_one, mul_one]
    · have hidx : idx c ≠ idx d := idx_ne_of_ne hdc hcd
      rw [R.eval_short hdc]
      by_cases hcb : c = Sum.swap b
      ·
        subst hcb
        have hbd : idx b ≠ idx d := by rwa [idx_swap] at hidx
        simp only [commData, ite_true, hdc, ite_false]
        refine ⟨?_, by simp, ?_, ?_⟩
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          exact ⟨⟨ne_swap_of_idx_ne hbd, fun h => absurd h (ne_of_idx_ne hbd)⟩,
            (rt_add_rt_swap b b d).symm⟩
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨⟨sw' d, fun _ => ?_⟩, ?_⟩
          · simp only [map_mul, hσ, hs]
            ring
          · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; module
        · rw [evalO_some, evalO_none, evalO_some, R.eval_short (ne_of_idx_ne hbd), R.eval_long,
            mul_one, R.longShort hσ hbd hs t]
      by_cases hdb : d = Sum.swap b
      ·
        subst hdb
        have hbc : idx b ≠ idx c := by rw [← idx_swap b]; exact hidx.symm
        simp only [commData, ite_true, hdc, hcb, ite_false]
        refine ⟨?_, by simp, ?_, ?_⟩
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨⟨ne_swap_of_idx_ne hbc, fun h => absurd h (ne_of_idx_ne hbc)⟩, ?_⟩
          rw [rt_comm c]
          exact (rt_add_rt_swap b b c).symm
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨⟨sw' c, fun _ => ?_⟩, ?_⟩
          · simp only [map_mul, hσ, hs]
            ring
          · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; module
        · rw [evalO_some, evalO_none, evalO_some, R.eval_short (ne_of_idx_ne hbc), R.eval_long,
            mul_one, R.swap (Sum.swap b) c hidx.symm, R.longShort hσ hbc hs (σ t), hσ]
      ·
        simp only [commData, ite_true, hdc, hcb, hdb, ite_false]
        refine ⟨by simp, by simp, by simp, ?_⟩
        rw [R.commLS b c d hidx hcb hdb s t hs, evalO_none, mul_one, mul_one]
  ·
    have hidx₁ : idx a ≠ idx b := idx_ne_of_ne hba hab
    have hba' : idx b ≠ idx a := hidx₁.symm
    rw [R.eval_short hba]
    have hrt : ∀ x y z : Fin r ⊕ Fin r, rt x y = rt z (Sum.swap z) + rt x y := fun x y z => by
      simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
    by_cases hdc : d = c
    ·
      subst hdc
      have ht := htf rfl
      rw [R.eval_long]
      by_cases hcb : d = Sum.swap b
      · subst hcb
        simp only [commData, hba, ite_false, ite_true]
        refine ⟨?_, ?_, by simp, ?_⟩
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨relValid_short (by rwa [idx_swap]) _, ?_⟩
          simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨relValid_long a ?_, ?_⟩
          · simp only [map_mul, hσ, ht]
            ring
          · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; module
        · rw [evalO_some, evalO_some, evalO_none, mul_one,
            R.eval_short (swap_ne_of_idx_ne' hidx₁), R.eval_long, R.shortLong a b hidx₁ s t ht]
      by_cases hca : d = Sum.swap a
      · subst hca
        simp only [commData, hba, hcb, ite_false, ite_true]
        refine ⟨?_, ?_, by simp, ?_⟩
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨relValid_short (by rwa [idx_swap]) _, ?_⟩
          simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
        · simp only [Option.mem_def, Option.some.injEq, forall_eq']
          refine ⟨relValid_long b ?_, ?_⟩
          · simp only [map_mul, hσ, ht]
            ring
          · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; module
        · rw [evalO_some, evalO_some, evalO_none, mul_one, R.eval_short (swap_ne_of_idx_ne' hba'),
            R.eval_long, R.swap b a hba', R.shortLong b a hba' (σ s) t ht, hσ]
      · simp only [commData, hba, hcb, hca, ite_false, ite_true]
        refine ⟨by simp, by simp, by simp, ?_⟩
        have h1 : a ≠ Sum.swap d := fun h => hca (by rw [h, Sum.swap_swap])
        have h2 : b ≠ Sum.swap d := fun h => hcb (by rw [h, Sum.swap_swap])
        rw [← commutatorElement_inv, R.commLS d a b hidx₁ h1 h2 t s ht, inv_one, evalO_none,
          mul_one, mul_one]
    ·
      have hidx₂ : idx c ≠ idx d := idx_ne_of_ne hdc hcd
      have hdc' : idx d ≠ idx c := hidx₂.symm
      rw [R.eval_short hdc]
      by_cases hca : c = Sum.swap a
      · subst hca
        by_cases hdb : d = b
        · subst hdb
          simp only [commData, hba, hdc, ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_long d ?_, ?_⟩
            · simp only [map_add, map_mul, hσ]
              ring
            · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_long, R.swap d a hba', R.swap d (Sum.swap a) (by rwa [idx_swap]),
              R.trace d a hba' (σ s) (σ t), hσ, hσ]
        ·
          have hdb' : d ≠ Sum.swap b := fun h => hne (by rw [h]; exact hopp a b)
          have had : idx a ≠ idx d := idx_ne_of_ne (by rwa [Sum.swap_swap] at hcd) hdc
          have hbd : idx b ≠ idx d := idx_ne_of_ne hdb hdb'
          simp only [commData, hba, hdc, hdb, ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            exact ⟨relValid_short hbd _, (rt_add_rt_swap a b d).symm⟩
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_short (ne_of_idx_ne hbd), R.swap b a hba', R.short b a d hba' had hbd]
      by_cases hcb : c = Sum.swap b
      · subst hcb
        by_cases hda : d = a
        · subst hda
          simp only [commData, hba, hdc, hca, ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_long d ?_, ?_⟩
            · simp only [map_add, map_mul, hσ]
              ring
            · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_long, R.swap d (Sum.swap b) (by rwa [idx_swap]), R.trace d b hidx₁ s (σ t),
              hσ]
        · have hda' : d ≠ Sum.swap a := fun h => hne (by rw [h]; exact hopp' a b)
          have hdb : d ≠ b := by rwa [Sum.swap_swap] at hcd
          have had : idx a ≠ idx d := idx_ne_of_ne hda hda'
          have hbd : idx b ≠ idx d := idx_ne_of_ne hdb hdc
          simp only [commData, hba, hdc, hca, hda, ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_short had _, ?_⟩
            rw [rt_comm a b]
            exact (rt_add_rt_swap b a d).symm
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_short (ne_of_idx_ne had), R.short a b d hidx₁ hbd had]
      by_cases hda : d = Sum.swap a
      · subst hda
        by_cases hcb' : c = b
        · subst hcb'
          simp only [commData, hba, hdc, hca, hcb, ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_long c ?_, ?_⟩
            · simp only [map_add, map_mul, hσ]
              ring
            · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_long, R.swap c a hba', R.trace c a hba' (σ s) t, hσ]
        · have hca' : c ≠ a := fun h => hcd (by rw [h])
          have hac : idx a ≠ idx c := idx_ne_of_ne hca' hca
          have hbc : idx b ≠ idx c := idx_ne_of_ne hcb' hcb
          simp only [commData, hba, hdc, hca, hcb, hcb', ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_short hbc _, ?_⟩
            rw [rt_comm c]
            exact (rt_add_rt_swap a b c).symm
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_short (ne_of_idx_ne hbc), R.swap b a hba',
              R.swap (Sum.swap a) c (by rwa [idx_swap]), R.short b a c hba' hac hbc]
      by_cases hdb : d = Sum.swap b
      · subst hdb
        by_cases hca' : c = a
        · subst hca'
          simp only [commData, hba, hdc, hca, hcb, hda, ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_long c ?_, ?_⟩
            · simp only [map_add, map_mul, hσ]
              ring
            · simp only [rt, CFSG.LieType.Steinberg.Sp.wt_swap]; abel
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_long, R.trace c b hidx₁ s t]
        · have hcb' : c ≠ b := fun h => hcd (by rw [h])
          have hac : idx a ≠ idx c := idx_ne_of_ne hca' hca
          have hbc : idx b ≠ idx c := idx_ne_of_ne hcb' hcb
          simp only [commData, hba, hdc, hca, hcb, hda, hca', ite_false, ite_true]
          refine ⟨?_, by simp, by simp, ?_⟩
          · simp only [Option.mem_def, Option.some.injEq, forall_eq']
            refine ⟨relValid_short hac _, ?_⟩
            rw [rt_comm c, rt_comm a b]
            exact (rt_add_rt_swap b a c).symm
          · simp only [evalO_some, evalO_none, mul_one]
            rw [R.eval_short (ne_of_idx_ne hac), R.swap (Sum.swap b) c (by rwa [idx_swap]),
              R.short a b c hidx₁ hbc hac]
      ·
        simp only [commData, hba, hdc, hca, hcb, hda, hdb, ite_false]
        refine ⟨by simp, by simp, by simp, ?_⟩
        rw [R.commSS a b c d hidx₁ hidx₂ hca hcb hda hdb s t, evalO_none, mul_one, mul_one]

end SURelations

end CFSG.Timmesfeld.Transvection
