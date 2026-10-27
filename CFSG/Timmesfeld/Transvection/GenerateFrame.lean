module

public import CFSG.Timmesfeld.Transvection.GenerateFrameBasic
public import CFSG.Timmesfeld.Transvection.GenerateRel
public import CFSG.Timmesfeld.Transvection.RelBuildSp
public import CFSG.Timmesfeld.Transvection.RelBuildFamily
public import CFSG.Timmesfeld.Transvection.ShortRootCommSL2
public import CFSG.Timmesfeld.Transvection.ShortRootField

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {H : Type*} [Group H] {r : ℕ}

theorem shortRootGroup_comm {Δ : Set (Subgroup H)} (P Q P' Q' : Subgroup H) :
    shortRootGroup Δ P Q P' Q' = shortRootGroup Δ P' Q' P Q := by
  rw [shortRootGroup, shortRootGroup, lineGroup_comm, lineStab_comm Q P', lineStab_comm P Q',
    inf_right_comm]

structure FrameCoords (K : Type*) [Field K] (P Q : Fin r → Subgroup H) where
  p : Fin r → K → H
  q : Fin r → K → H
  w : Fin r → H
  h : Fin r → Kˣ → H
  mem_P : ∀ i g, g ∈ P i ↔ ∃ t, p i t = g
  mem_Q : ∀ i g, g ∈ Q i ↔ ∃ t, q i t = g
  add_p : ∀ i s t, p i (s + t) = p i s * p i t
  inj_p : ∀ i, Function.Injective (p i)
  w_mem : ∀ i, w i ∈ P i ⊔ Q i
  w_mul_self : ∀ i, w i * w i = 1
  w_conj : ∀ i t, w i * p i t * (w i)⁻¹ = q i t
  h_mem : ∀ i c, h i c ∈ P i ⊔ Q i
  w_conj_h : ∀ i c, w i * h i c * (w i)⁻¹ = h i c⁻¹

namespace FrameCoords

variable {K : Type*} [Field K] {P Q : Fin r → Subgroup H} (C : FrameCoords K P Q)

@[expose] def long : Fin r ⊕ Fin r → K → H := Sum.elim C.p C.q

@[simp] theorem long_inl (i : Fin r) : C.long (Sum.inl i) = C.p i := rfl

@[simp] theorem long_inr (i : Fin r) : C.long (Sum.inr i) = C.q i := rfl

theorem w_inv (i : Fin r) : (C.w i)⁻¹ = C.w i :=
  inv_eq_of_mul_eq_one_right (C.w_mul_self i)

theorem w_conj_q (i : Fin r) (t : K) : C.w i * C.q i t * (C.w i)⁻¹ = C.p i t := by
  rw [← C.w_conj, C.w_inv]
  calc C.w i * (C.w i * C.p i t * C.w i) * C.w i =
        (C.w i * C.w i) * C.p i t * (C.w i * C.w i) := by group
    _ = C.p i t := by rw [C.w_mul_self, one_mul, mul_one]

theorem add_q (i : Fin r) (s t : K) : C.q i (s + t) = C.q i s * C.q i t := by
  rw [← C.w_conj, ← C.w_conj, ← C.w_conj, C.add_p]
  group

theorem long_add (a : Fin r ⊕ Fin r) (s t : K) : C.long a (s + t) = C.long a s * C.long a t := by
  rcases a with i | i
  · exact C.add_p i s t
  · exact C.add_q i s t

theorem mem_framePt_iff (a : Fin r ⊕ Fin r) (g : H) :
    g ∈ framePt P Q a ↔ ∃ t, C.long a t = g := by
  rcases a with i | i
  · exact C.mem_P i g
  · exact C.mem_Q i g

theorem long_mem (a : Fin r ⊕ Fin r) (t : K) : C.long a t ∈ framePt P Q a :=
  (C.mem_framePt_iff a _).2 ⟨t, rfl⟩

theorem long_zero (a : Fin r ⊕ Fin r) : C.long a 0 = 1 := by
  have h := C.long_add a 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem long_injective (a : Fin r ⊕ Fin r) : Function.Injective (C.long a) := by
  rcases a with i | i
  · exact C.inj_p i
  · intro s t h
    refine C.inj_p i ?_
    simp only [long_inr, ← C.w_conj] at h
    simpa using h

variable {Δ : Set (Subgroup H)} (hF : IsFrame Δ P Q) (hΔ : IsRootClass Δ)
include hF hΔ

theorem conjSub_framePt (k : Fin r) (c : Fin r ⊕ Fin r) :
    conjSub (framePt P Q c) (C.w k) = framePt P Q (RelBuild.flip k c) := by
  by_cases hck : idx c = k
  · rw [RelBuild.flip_of_idx_eq hck]
    have hle : ∀ d : Fin r ⊕ Fin r, idx d = k →
        conjSub (framePt P Q d) (C.w k) ≤ framePt P Q (Sum.swap d) := by
      intro d hd
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨t, rfl⟩ := (C.mem_framePt_iff d g).1 hg
      rcases d with i | i <;> simp only [idx_inl, idx_inr] at hd <;> subst hd
      · exact (C.mem_framePt_iff (Sum.inr _) _).2 ⟨t, (C.w_conj _ t).symm⟩
      · exact (C.mem_framePt_iff (Sum.inl _) _).2 ⟨t, (C.w_conj_q _ t).symm⟩
    refine le_antisymm (hle c hck) ?_
    have h2 := conjSub_le_conjSub (hle (Sum.swap c) (by rwa [idx_swap])) (C.w k)
    rwa [← conjSub_mul, C.w_mul_self, conjSub_one, Sum.swap_swap] at h2
  · rw [RelBuild.flip_of_idx_ne hck]
    exact conjSub_of_forall_commute fun g hg =>
      (hF.commuting_sup_framePt hΔ hck) _ (C.w_mem k) g hg
where
  conjSub_le_conjSub {A B : Subgroup H} (h : A ≤ B) (g : H) : conjSub A g ≤ conjSub B g :=
    Subgroup.map_mono h

omit hΔ in
theorem w_commute (i j : Fin r) : C.w i * C.w j = C.w j * C.w i := by
  by_cases hij : i = j
  · rw [hij]
  · exact (hF.commuting i j hij _ (C.w_mem i) _ (C.w_mem j)).eq

theorem long_conj (k : Fin r) (a : Fin r ⊕ Fin r) (t : K) :
    C.w k * C.long a t * (C.w k)⁻¹ = C.long (RelBuild.flip k a) t := by
  by_cases hak : idx a = k
  · rw [RelBuild.flip_of_idx_eq hak]
    rcases a with i | i <;> simp only [idx_inl, idx_inr] at hak <;> subst hak
    · exact C.w_conj _ t
    · exact C.w_conj_q _ t
  · rw [RelBuild.flip_of_idx_ne hak,
      (hF.commuting_sup_framePt hΔ hak _ (C.w_mem k) _ (C.long_mem a t)).eq, mul_inv_cancel_right]

variable {F : Type*} [Field F] {σ : F ≃+* F} {β : Fin r → Fin r → F → H}
  (hβ : ∀ i j : Fin r, i < j → ∀ g,
    g ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j) ↔ ∃ c, β i j c = g)
include hβ

omit [Field F] in
theorem w_commute_base (i j k : Fin r) (hij : i < j) (hki : k ≠ i) (hkj : k ≠ j) (c : F) :
    C.w k * β i j c = β i j c * C.w k :=
  (hF.commuting_sup_shortRootGroup hΔ (a := Sum.inr i) (b := Sum.inl j) (i := k)
    (fun h => hki h.symm) (fun h => hkj h.symm) _ (C.w_mem k) _
    ((hβ i j hij _).2 ⟨c, rfl⟩)).eq

theorem mem_shortRootGroup_iff_family_of_lt {a b : Fin r ⊕ Fin r} (hab : idx a < idx b)
    (g : H) :
    g ∈ shortRootGroup Δ (framePt P Q a) (framePt P Q (Sum.swap a)) (framePt P Q b)
        (framePt P Q (Sum.swap b)) ↔ ∃ c, RelBuild.family σ β C.w a b c = g := by
  have key := RelBuild.of_flip (fun T : Fin 2 → Fin r ⊕ Fin r => idx (T 0) < idx (T 1) →
      ∀ g, g ∈ shortRootGroup Δ (framePt P Q (T 0)) (framePt P Q (Sum.swap (T 0)))
        (framePt P Q (T 1)) (framePt P Q (Sum.swap (T 1))) ↔
          ∃ c, RelBuild.family σ β C.w (T 0) (T 1) c = g)
    (fun k T hT hlt g => by
      simp only [Function.comp_apply, RelBuild.idx_flip] at hlt ⊢
      rw [← RelBuild.flip_swap, ← RelBuild.flip_swap, ← C.conjSub_framePt hF hΔ,
        ← C.conjSub_framePt hF hΔ, ← C.conjSub_framePt hF hΔ, ← C.conjSub_framePt hF hΔ,
        shortRootGroup_conjSub hΔ, mem_conjSub, hT hlt]
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [← RelBuild.family_weyl (C.w_mul_self) (C.w_commute hF)
          (C.w_commute_base hF hΔ hβ) hlt.ne, hc]
        group
      · rintro ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        rw [← RelBuild.family_weyl (C.w_mul_self) (C.w_commute hF)
          (C.w_commute_base hF hΔ hβ) hlt.ne]
        group)
    (P := ![Sum.inr (idx a), Sum.inl (idx b)]) (P' := ![a, b])
    (fun x => by fin_cases x <;> simp)
    (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all [hab.ne, hab.ne'])
    (fun hlt g => by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Sum.swap_inr,
        Sum.swap_inl, framePt_inl, framePt_inr, idx_inl, idx_inr] at hlt ⊢
      rw [hβ _ _ hlt]
      constructor
      · rintro ⟨c, rfl⟩
        refine ⟨σ.symm c, ?_⟩
        rw [RelBuild.family_of_gt (by simpa using hlt)]
        simp [RelBuild.familyLT, RelBuild.wPos, RelBuild.wNeg]
      · rintro ⟨c, rfl⟩
        refine ⟨σ c, ?_⟩
        rw [RelBuild.family_of_gt (by simpa using hlt)]
        simp [RelBuild.familyLT, RelBuild.wPos, RelBuild.wNeg])
  simpa using key hab g

theorem mem_shortRootGroup_iff_family (hσ : ∀ c, σ (σ c) = c) {a b : Fin r ⊕ Fin r}
    (hab : idx a ≠ idx b) (g : H) :
    g ∈ shortRootGroup Δ (framePt P Q a) (framePt P Q (Sum.swap a)) (framePt P Q b)
        (framePt P Q (Sum.swap b)) ↔ ∃ c, RelBuild.family σ β C.w a b c = g := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact C.mem_shortRootGroup_iff_family_of_lt hF hΔ hβ h g
  · rw [shortRootGroup_comm, C.mem_shortRootGroup_iff_family_of_lt hF hΔ hβ (σ := σ) h g]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, (RelBuild.family_swap hσ hab c).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨σ.symm c, ?_⟩
      rw [RelBuild.family_swap hσ hab, RingEquiv.apply_symm_apply]

end FrameCoords

namespace RelBuild

variable {F G : Type*} [Field F] [Group G] {σ : F ≃+* F} {β : Fin r → Fin r → F → G}
  {w : Fin r → G}

theorem family_inl_inr_of_gt {i j : Fin r} (h : j < i) (c : F) :
    family σ β w (.inl j) (.inr i) c = w i * w j * β j i (σ c) * (w i * w j)⁻¹ := by
  rw [family_of_gt (by simpa using h)]
  simp [familyLT, wPos, wNeg]

theorem family_inl_inl_of_gt {i j : Fin r} (h : j < i) (c : F) :
    family σ β w (.inl j) (.inl i) c = w j * β j i (σ c) * (w j)⁻¹ := by
  rw [family_of_gt (by simpa using h)]
  simp [familyLT, wPos, wNeg]

end RelBuild

namespace FrameCoords

variable {K : Type*} [Field K] {P Q : Fin r → Subgroup H} (C : FrameCoords K P Q)
  {Δ : Set (Subgroup H)} (hF : IsFrame Δ P Q) (hΔ : IsRootClass Δ)
  {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {ι : K →+* F}
  (hι : ∀ c, σ c = c ↔ ∃ n, ι n = c) {L : Fin r ⊕ Fin r → F → H}
  (hL : ∀ a n, L a (ι n) = C.long a n) {β : Fin r → Fin r → F → H}
  (hpair : ∀ i j : Fin r, i < j →
    PairRelations σ ι Δ (P i) (Q i) (P j) (Q j) (C.p i) (C.p j) (C.w i) (C.w j) (C.h i) (C.h j)
      (β i j))

section Long

include hι hL

theorem L_mem (a : Fin r ⊕ Fin r) {c : F} (hc : σ c = c) : L a c ∈ framePt P Q a := by
  obtain ⟨n, rfl⟩ := (hι c).1 hc
  rw [hL]
  exact C.long_mem a n

theorem L_add (a : Fin r ⊕ Fin r) {s t : F} (hs : σ s = s) (ht : σ t = t) :
    L a (s + t) = L a s * L a t := by
  obtain ⟨m, rfl⟩ := (hι s).1 hs
  obtain ⟨n, rfl⟩ := (hι t).1 ht
  rw [← map_add, hL, hL, hL, C.long_add]

include hF hΔ in
theorem L_conj (k : Fin r) (a : Fin r ⊕ Fin r) {c : F} (hc : σ c = c) :
    C.w k * L a c * (C.w k)⁻¹ = L (RelBuild.flip k a) c := by
  obtain ⟨n, rfl⟩ := (hι c).1 hc
  rw [hL, hL, C.long_conj hF hΔ]

end Long

include hσ hι hL hpair

theorem shortLong_family {i j : Fin r} (hij : i ≠ j) (s t : F) (ht : σ t = t) :
    ⁅RelBuild.family σ β C.w (.inl j) (.inr i) s, L (.inl i) t⁆ =
      RelBuild.family σ β C.w (.inl j) (.inl i) (s * t) * L (.inl j) (σ s * s * t) := by
  obtain ⟨t, rfl⟩ := (hι t).1 ht
  obtain ⟨n, hn⟩ := (hι (σ s * s * ι t)).1 (RelBuild.fixed_norm_mul hσ s ht)
  rw [← hn, hL, hL]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [RelBuild.family_inl_inr h, RelBuild.family_inl_inl h]
    exact (hpair i j h).shortLong s t n hn
  · rw [RelBuild.family_inl_inr_of_gt h, RelBuild.family_inl_inl_of_gt h]
    exact (hpair j i h).shortLong' s t n hn

theorem trace_family {i j : Fin r} (hij : i ≠ j) (s t : F) :
    ⁅RelBuild.family σ β C.w (.inl j) (.inr i) s, RelBuild.family σ β C.w (.inl j) (.inl i) t⁆ =
      L (.inl j) (s * σ t + σ s * t) := by
  obtain ⟨n, hn⟩ := (hι (s * σ t + σ s * t)).1 (RelBuild.fixed_trace hσ s t)
  rw [← hn, hL]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [RelBuild.family_inl_inr h, RelBuild.family_inl_inl h]
    exact (hpair i j h).trace s t n hn
  · rw [RelBuild.family_inl_inr_of_gt h, RelBuild.family_inl_inl_of_gt h]
    exact (hpair j i h).trace' s t n hn

omit hσ hι hL hpair in
theorem w_inv_conj_h (i : Fin r) (c : Kˣ) : (C.w i)⁻¹ * C.h i c * C.w i = C.h i c⁻¹ := by
  have h := C.w_conj_h i c
  rw [C.w_inv] at h ⊢
  exact h

include hF in
omit hσ hι hL hpair in
theorem h_commute_w {i j : Fin r} (hij : i ≠ j) (c : Kˣ) : C.h i c * C.w j = C.w j * C.h i c :=
  (hF.commuting i j hij _ (C.h_mem i c) _ (C.w_mem j)).eq

include hF in
omit hσ hL in
theorem torus_family_left {i j : Fin r} (hij : i ≠ j) (c : Kˣ) (s : F) :
    C.h i c * RelBuild.family σ β C.w (.inl j) (.inr i) s * (C.h i c)⁻¹ =
      RelBuild.family σ β C.w (.inl j) (.inr i) (ι (c : K) * s) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [RelBuild.family_inl_inr h, RelBuild.family_inl_inr h]
    exact (hpair i j h).torusA c s
  · have hfix : σ (ι (c : K)) = ι (c : K) := (hι _).2 ⟨_, rfl⟩
    rw [RelBuild.family_inl_inr_of_gt h, RelBuild.family_inl_inr_of_gt h, map_mul, hfix]
    have hc : (C.w i * C.w j)⁻¹ * C.h i c * (C.w i * C.w j) = C.h i c⁻¹ := by
      have h1 := C.h_commute_w hF h.ne' c⁻¹
      calc (C.w i * C.w j)⁻¹ * C.h i c * (C.w i * C.w j) =
            (C.w j)⁻¹ * ((C.w i)⁻¹ * C.h i c * C.w i) * C.w j := by group
        _ = (C.w j)⁻¹ * (C.h i c⁻¹ * C.w j) := by rw [C.w_inv_conj_h, mul_assoc]
        _ = C.h i c⁻¹ := by rw [h1, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 := (hpair j i h).torusD c⁻¹ (σ s)
    rw [inv_inv] at h2
    calc C.h i c * (C.w i * C.w j * β j i (σ s) * (C.w i * C.w j)⁻¹) * (C.h i c)⁻¹ =
          C.w i * C.w j * ((C.w i * C.w j)⁻¹ * C.h i c * (C.w i * C.w j) * β j i (σ s) *
            ((C.w i * C.w j)⁻¹ * C.h i c * (C.w i * C.w j))⁻¹) * (C.w i * C.w j)⁻¹ := by group
      _ = _ := by rw [hc, h2]

include hF in
omit hσ hL in
theorem torus_family_right {i j : Fin r} (hij : i ≠ j) (c : Kˣ) (s : F) :
    C.h j c * RelBuild.family σ β C.w (.inl j) (.inr i) s * (C.h j c)⁻¹ =
      RelBuild.family σ β C.w (.inl j) (.inr i) (ι ((c⁻¹ : Kˣ) : K) * s) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [RelBuild.family_inl_inr h, RelBuild.family_inl_inr h]
    exact (hpair i j h).torusD c s
  · have hfix : σ (ι ((c⁻¹ : Kˣ) : K)) = ι ((c⁻¹ : Kˣ) : K) := (hι _).2 ⟨_, rfl⟩
    rw [RelBuild.family_inl_inr_of_gt h, RelBuild.family_inl_inr_of_gt h, map_mul, hfix]
    have hc : (C.w i * C.w j)⁻¹ * C.h j c * (C.w i * C.w j) = C.h j c⁻¹ := by
      have h1 := C.h_commute_w hF h.ne c
      calc (C.w i * C.w j)⁻¹ * C.h j c * (C.w i * C.w j) =
            (C.w j)⁻¹ * ((C.w i)⁻¹ * (C.h j c * C.w i)) * C.w j := by group
        _ = C.h j c⁻¹ := by rw [h1, inv_mul_cancel_left, C.w_inv_conj_h]
    calc C.h j c * (C.w i * C.w j * β j i (σ s) * (C.w i * C.w j)⁻¹) * (C.h j c)⁻¹ =
          C.w i * C.w j * ((C.w i * C.w j)⁻¹ * C.h j c * (C.w i * C.w j) * β j i (σ s) *
            ((C.w i * C.w j)⁻¹ * C.h j c * (C.w i * C.w j))⁻¹) * (C.w i * C.w j)⁻¹ := by group
      _ = _ := by rw [hc, (hpair j i h).torusA c⁻¹ (σ s)]

include hF hΔ

omit hι hL in
theorem family_mem {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (c : F) :
    RelBuild.family σ β C.w a b c ∈ shortRootGroup Δ (framePt P Q a) (framePt P Q (Sum.swap a))
      (framePt P Q b) (framePt P Q (Sum.swap b)) :=
  (C.mem_shortRootGroup_iff_family hF hΔ (fun i j h => (hpair i j h).mem_iff) hσ hab _).2
    ⟨c, rfl⟩

omit hι hL in
theorem torus_family_other {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) {k : Fin r}
    (hka : idx a ≠ k) (hkb : idx b ≠ k) (c : Kˣ) (s : F) :
    C.h k c * RelBuild.family σ β C.w a b s = RelBuild.family σ β C.w a b s * C.h k c :=
  (hF.commuting_sup_shortRootGroup hΔ hka hkb _ (C.h_mem k c) _
    (C.family_mem hF hΔ hσ hpair hab s)).eq

@[expose] noncomputable def toPreRelations : PreRelations r σ H where
  ξ := RelBuild.family σ β C.w
  ξL := L
  w := C.w
  swap _ _ hab c := RelBuild.family_swap hσ hab c
  add _ _ hab s t := RelBuild.family_add (fun i j h => (hpair i j h).add) hab s t
  addL a _ _ hs ht := C.L_add hι hL a hs ht
  weyl k _ _ hab c := RelBuild.family_weyl C.w_mul_self (C.w_commute hF)
    (C.w_commute_base hF hΔ fun i j h => (hpair i j h).mem_iff) hab k c
  weylL k a _ hc := C.L_conj hF hΔ hι hL k a hc
  shortLong _ _ hij s t ht := C.shortLong_family hσ hι hL hpair hij s t ht
  trace _ _ hij s t := C.trace_family hσ hι hL hpair hij s t
  commLL i j hij s t hs ht := commutatorElement_eq_one_iff_mul_comm.2
    (hF.commuting_PP hij _ (C.L_mem hι hL (.inl i) hs) _ (C.L_mem hι hL (.inl j) ht)).eq
  commLS i j hij s t hs := commutatorElement_eq_one_iff_mul_comm.2
    ((hF.commuting_framePt_shortRootGroup hΔ (a := .inl j) (c := .inl j) (d := .inr i)
      (by simp) (by simp [hij])) _ (C.L_mem hι hL (.inl j) hs) _
      (C.family_mem hF hΔ hσ hpair (by simpa using hij.symm) t)).eq
  commLS₃ i j k hij hik hjk s t hs := commutatorElement_eq_one_iff_mul_comm.2
    ((hF.commuting_framePt_shortRootGroup hΔ (a := .inl k) (c := .inl j) (d := .inr i)
      (by simp) (by simp [hik])) _ (C.L_mem hι hL (.inl k) hs) _
      (C.family_mem hF hΔ hσ hpair (by simpa using hij.symm) t)).eq
  commSS₃ i j k hij hik hjk s t := commutatorElement_eq_one_iff_mul_comm.2
    ((hF.commuting_shortRootGroup hΔ (a := .inl j) (b := .inr i) (c := .inl k) (d := .inr i)
      (by simp) (by simp [hik.symm]) (by simp [hij]) (by simp)) _
      (C.family_mem hF hΔ hσ hpair (by simpa using hij.symm) s) _
      (C.family_mem hF hΔ hσ hpair (by simpa using hik.symm) t)).eq
  commSS₄ i j k l hij hkl hik hil hjk hjl s t := commutatorElement_eq_one_iff_mul_comm.2
    ((hF.commuting_shortRootGroup hΔ (a := .inl j) (b := .inr i) (c := .inl l) (d := .inr k)
      (by simp) (by simp [hil.symm]) (by simp [hjk.symm]) (by simp)) _
      (C.family_mem hF hΔ hσ hpair (by simpa using hij.symm) s) _
      (C.family_mem hF hΔ hσ hpair (by simpa using hkl.symm) t)).eq

@[simp] theorem toPreRelations_ξ :
    (C.toPreRelations hF hΔ hσ hι hL hpair).ξ = RelBuild.family σ β C.w := rfl

@[simp] theorem toPreRelations_ξL : (C.toPreRelations hF hΔ hσ hι hL hpair).ξL = L := rfl

@[simp] theorem toPreRelations_w : (C.toPreRelations hF hΔ hσ hι hL hpair).w = C.w := rfl

theorem hasFrameImages_of_eq (R : SURelations r σ H) (hRL : R.ξL = L)
    (hRξ : ∀ a b, idx a ≠ idx b →
      ∃ θ : F ≃+ F, ∀ c, R.ξ a b c = RelBuild.family σ β C.w a b (θ c)) :
    R.HasFrameImages Δ P Q := by
  refine ⟨fun a g => ?_, fun a b hab g => ?_⟩
  · rw [hRL]
    constructor
    · intro hg
      obtain ⟨n, rfl⟩ := (C.mem_framePt_iff a g).1 hg
      exact ⟨ι n, (hι _).2 ⟨n, rfl⟩, hL a n⟩
    · rintro ⟨c, hc, rfl⟩
      exact C.L_mem hι hL a hc
  · obtain ⟨θ, hθ⟩ := hRξ a b hab
    rw [C.mem_shortRootGroup_iff_family hF hΔ (fun i j h => (hpair i j h).mem_iff) hσ hab]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨θ.symm c, by rw [hθ, AddEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨θ c, (hθ c).symm⟩

end FrameCoords

namespace FrameCoords

variable {K : Type} [Field K] {P Q : Fin r → Subgroup H} (C : FrameCoords K P Q)
  {Δ : Set (Subgroup H)} (hF : IsFrame Δ P Q) (hΔ : IsRootClass Δ) {β : Fin r → Fin r → K → H}
  (hpair : ∀ i j : Fin r, i < j → PairRelations (RingEquiv.refl K) (RingHom.id K) Δ (P i) (Q i)
    (P j) (Q j) (C.p i) (C.p j) (C.w i) (C.w j) (C.h i) (C.h j) (β i j))

@[expose] noncomputable def toPreRelationsId : PreRelations r (RingEquiv.refl K) H :=
  C.toPreRelations hF hΔ (fun _ => rfl) (ι := RingHom.id K)
    (fun c => ⟨fun _ => ⟨c, rfl⟩, fun _ => rfl⟩) (L := C.long) (fun _ _ => rfl) hpair

variable [CharP K 2]
  (hshort : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ s t, ∃ u,
    ⁅RelBuild.family (RingEquiv.refl K) β C.w (.inl j) (.inr i) s,
      RelBuild.family (RingEquiv.refl K) β C.w (.inl k) (.inr j) t⁆ =
      RelBuild.family (RingEquiv.refl K) β C.w (.inl k) (.inr i) u ∧ u ^ 2 = s ^ 2 * t ^ 2)

@[expose] noncomputable def toPreSpRelations : PreSpRelations r K H where
  ξ := RelBuild.family (RingEquiv.refl K) β C.w
  ξL := C.long
  w := C.w
  symm _ _ hab c := RelBuild.family_swap (fun _ => rfl) hab c
  add := (C.toPreRelationsId hF hΔ hpair).add
  addL := C.long_add
  weyl := (C.toPreRelationsId hF hΔ hpair).weyl
  weylL k a c := C.long_conj hF hΔ k a c
  shortLong i j hij s t := by
    have h := (C.toPreRelationsId hF hΔ hpair).shortLong i j hij s t rfl
    rwa [RingEquiv.refl_apply, ← sq] at h
  commLong i j hij s t := by
    have h := (C.toPreRelationsId hF hΔ hpair).trace i j hij s t
    rw [RingEquiv.refl_apply, RingEquiv.refl_apply, CharTwo.add_self_eq_zero] at h
    exact h.trans (C.long_zero (Sum.inl j) : C.long (Sum.inl j) 0 = 1)
  commLL i j hij s t := (C.toPreRelationsId hF hΔ hpair).commLL i j hij s t rfl rfl
  commLS i j hij s t := (C.toPreRelationsId hF hΔ hpair).commLS i j hij s t rfl
  commLS₃ i j k h₁ h₂ h₃ s t := (C.toPreRelationsId hF hΔ hpair).commLS₃ i j k h₁ h₂ h₃ s t rfl
  commSS₃ := (C.toPreRelationsId hF hΔ hpair).commSS₃
  commSS₄ := (C.toPreRelationsId hF hΔ hpair).commSS₄
  short := hshort

theorem hasFrameImages_toSpRelations :
    (C.toPreSpRelations hF hΔ hpair hshort).toSpRelations.HasFrameImages Δ P Q := by
  refine ⟨fun a g => ?_, fun a b hab g => ?_⟩
  · simp only [PreSpRelations.toSpRelations_ξ_self]
    exact C.mem_framePt_iff a g
  · simp only [PreSpRelations.toSpRelations_ξ_of_ne _ (ne_of_idx_ne hab)]
    exact C.mem_shortRootGroup_iff_family hF hΔ (fun i j h => (hpair i j h).mem_iff)
      (fun _ => rfl) hab g

include hF hΔ hpair hshort in
theorem exists_spRelations_hasFrameImages : ∃ R : SpRelations r K H, R.HasFrameImages Δ P Q :=
  ⟨_, C.hasFrameImages_toSpRelations hF hΔ hpair hshort⟩

end FrameCoords

open CFSG.Timmesfeld.ARS.NaturalModule in
private theorem torusElt_eq_elt_diagElt {A E : Subgroup H} {k : ℕ} (φ : SL2Coords A E k)
    (c : (GaloisField 2 k)ˣ) : φ.torusElt c = φ.elt (diagElt c) := by
  rw [← φ.mat_torusElt c, φ.elt_mat (φ.torusElt_mem c)]

open CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne in
@[expose] noncomputable def FrameCoords.ofSL2Coords {P Q : Fin r → Subgroup H} {k : ℕ}
    (φ : ∀ i, SL2Coords (P i) (Q i) k) : FrameCoords (GaloisField 2 k) P Q where
  p i t := (φ i).elt (lowerElt _ t)
  q i t := (φ i).elt (upperElt _ t)
  w i := (φ i).elt (weylElt _)
  h i := (φ i).torusElt
  mem_P i g := ⟨fun hg => by
      obtain ⟨t, ht⟩ := (φ i).exists_eq_elt_lowerElt hg
      exact ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ht ▸ (φ i).elt_lowerElt_mem t⟩
  mem_Q i g := ⟨fun hg => by
      obtain ⟨t, ht⟩ := (φ i).exists_eq_elt_upperElt hg
      exact ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ht ▸ (φ i).elt_upperElt_mem t⟩
  add_p i s t := (φ i).elt_lowerElt_add s t
  inj_p i := (φ i).elt_lowerElt_injective
  w_mem i := (φ i).elt_mem _
  w_mul_self i := (φ i).elt_weylElt_mul_self
  w_conj i t := (φ i).elt_weylElt_conj_lowerElt t
  h_mem i c := (φ i).torusElt_mem c
  w_conj_h i c := by
    rw [torusElt_eq_elt_diagElt, torusElt_eq_elt_diagElt]
    exact (φ i).elt_weylElt_conj_diagElt c

end CFSG.Timmesfeld.Transvection
