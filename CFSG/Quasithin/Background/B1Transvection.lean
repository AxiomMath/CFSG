module

import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def IsTransvectionWith (t : MulAut V) (w : V) : Prop :=
  w ≠ 1 ∧ ∀ v : V, t v = v ∨ t v = v * w

@[expose] def IsTransvection (t : MulAut V) : Prop :=
  t ≠ 1 ∧ ∃ w : V, IsTransvectionWith t w

@[expose] def transvectionsIn (J : Subgroup (MulAut V)) : Set (MulAut V) :=
  {t | t ∈ J ∧ IsTransvection t}

namespace B1

theorem exists_moved_of_ne_one {t : MulAut V} (ht : t ≠ 1) : ∃ v : V, t v ≠ v := by
  by_contra hcon
  push Not at hcon
  exact ht (MulEquiv.ext hcon)

theorem tv_fix {t : MulAut V} {w : V} (h : IsTransvectionWith t w) (ht : t ≠ 1) : t w = w := by
  obtain ⟨v, hv⟩ := exists_moved_of_ne_one ht
  have h1 : t v = v * w := (h.2 v).resolve_left hv
  have h2 : t (t v) = t v * w := by
    rcases h.2 (t v) with h3 | h3
    · exact absurd (t.injective h3) hv
    · exact h3
  have hw : w = t v * v⁻¹ := by rw [h1, mul_comm v w, mul_inv_cancel_right]
  calc t w = t (t v * v⁻¹) := by rw [← hw]
    _ = t (t v) * (t v)⁻¹ := by rw [map_mul, map_inv]
    _ = (t v * w) * (t v)⁻¹ := by rw [h2]
    _ = w := by rw [mul_comm, inv_mul_cancel_left]

theorem tv_sq (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} {w : V} (h : IsTransvectionWith t w)
    (ht : t ≠ 1) : t * t = 1 := by
  refine MulEquiv.ext fun u => ?_
  rcases h.2 u with h1 | h1
  · show t (t u) = u
    rw [h1, h1]
  · show t (t u) = u
    rw [h1, map_mul, tv_fix h ht, h1, mul_assoc, ← sq, hV w, mul_one]

theorem tv_conj {t : MulAut V} {w : V} (h : IsTransvectionWith t w) (g : MulAut V) :
    IsTransvectionWith (g * t * g⁻¹) (g w) := by
  refine ⟨fun h1 => h.1 (g.injective (by rw [h1, map_one])), fun v => ?_⟩
  show g (t (g⁻¹ v)) = v ∨ g (t (g⁻¹ v)) = v * g w
  rcases h.2 (g⁻¹ v) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1, map_mul]
    simp

theorem tv_conj_ne_one {t : MulAut V} (ht : t ≠ 1) (g : MulAut V) : g * t * g⁻¹ ≠ 1 := by
  intro h
  apply ht
  have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
  rw [this, h]
  group

theorem isTransvection_conj {t : MulAut V} (h : IsTransvection t) (g : MulAut V) :
    IsTransvection (g * t * g⁻¹) := by
  obtain ⟨ht, w, hw⟩ := h
  exact ⟨tv_conj_ne_one ht g, g w, tv_conj hw g⟩

theorem tv_comm_centre {t : MulAut V} {w : V} (h : IsTransvectionWith t w) (ht : t ≠ 1)
    {g : MulAut V} (hg : g * t = t * g) : g w = w := by
  obtain ⟨v, hv⟩ := exists_moved_of_ne_one ht
  have h1 : t v = v * w := (h.2 v).resolve_left hv
  have h2 : t (g v) = g v * g w := by
    have := congrArg (fun s : MulAut V => s v) hg
    simp only [MulAut.mul_apply] at this
    rw [← this, h1, map_mul]
  rcases h.2 (g v) with h3 | h3
  · exfalso
    rw [h3] at h2
    have : g w = 1 := by
      have h4 : g v * 1 = g v * g w := by rw [mul_one]; exact h2
      exact (mul_left_cancel h4).symm
    exact h.1 (g.injective (by rw [this, map_one]))
  · rw [h3] at h2
    exact (mul_left_cancel h2).symm

theorem tv_commute {t t' : MulAut V} {w w' : V} (h : IsTransvectionWith t w)
    (h' : IsTransvectionWith t' w') (htw' : t w' = w') (ht'w : t' w = w) : t * t' = t' * t := by
  refine MulEquiv.ext fun u => ?_
  show t (t' u) = t' (t u)
  rcases h.2 u with h1 | h1 <;> rcases h'.2 u with h2 | h2
  · simp only [h1, h2]
  · simp only [h2, map_mul, htw', h1]
  · simp only [h1, map_mul, ht'w, h2]
  · simp only [h1, h2, map_mul, htw', ht'w]
    exact mul_right_comm _ _ _

theorem tv_split {t : MulAut V} {w : V} (h : IsTransvectionWith t w)
    (ht : t ≠ 1) {C W : Subgroup V} (hinf : C ⊓ W = ⊥) (hsup : C ⊔ W = ⊤)
    (hC : ∀ c ∈ C, t c ∈ C) (hW : ∀ m ∈ W, t m ∈ W) :
    (w ∈ W ∧ ∀ c ∈ C, t c = c) ∨ (w ∈ C ∧ ∀ m ∈ W, t m = m) := by
  have hδ : ∀ z : V, t z * z⁻¹ = 1 ∨ t z * z⁻¹ = w := by
    intro z
    rcases h.2 z with h1 | h1
    · left
      rw [h1, mul_inv_cancel]
    · right
      rw [h1, mul_comm z w, mul_inv_cancel_right]
  have hdelC : ∀ c ∈ C, t c * c⁻¹ = 1 ∨ (t c * c⁻¹ = w ∧ w ∈ C) := by
    intro c hc
    rcases hδ c with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      rw [← h1]
      exact C.mul_mem (hC c hc) (C.inv_mem hc)
  have hdelW : ∀ m ∈ W, t m * m⁻¹ = 1 ∨ (t m * m⁻¹ = w ∧ w ∈ W) := by
    intro m hm
    rcases hδ m with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      rw [← h1]
      exact W.mul_mem (hW m hm) (W.inv_mem hm)
  have hwbot : w ∈ C → w ∈ W → False := fun h1 h2 => by
    have : w ∈ C ⊓ W := ⟨h1, h2⟩
    rw [hinf] at this
    exact h.1 this
  obtain ⟨u, hu⟩ := exists_moved_of_ne_one ht
  have hu' : u ∈ C ⊔ W := by rw [hsup]; trivial
  obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hu'
  have hprod : t (c * m) * (c * m)⁻¹ = (t c * c⁻¹) * (t m * m⁻¹) := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hne : t (c * m) * (c * m)⁻¹ = w := by
    rcases hδ (c * m) with h1 | h1
    · exfalso
      exact hu (mul_inv_eq_one.1 h1)
    · exact h1
  rw [hprod] at hne
  rcases hdelC c hc with h1 | ⟨h1, hwC⟩
  · rcases hdelW m hm with h2 | ⟨h2, hwW⟩
    · rw [h1, h2, mul_one] at hne
      exact absurd hne.symm h.1
    · left
      refine ⟨hwW, fun c' hc' => ?_⟩
      rcases hdelC c' hc' with h3 | ⟨-, hwC'⟩
      · exact mul_inv_eq_one.1 h3
      · exact (hwbot hwC' hwW).elim
  · rcases hdelW m hm with h2 | ⟨h2, hwW⟩
    · right
      refine ⟨hwC, fun m' hm' => ?_⟩
      rcases hdelW m' hm' with h3 | ⟨-, hwW'⟩
      · exact mul_inv_eq_one.1 h3
      · exact (hwbot hwC hwW').elim
    · exact (hwbot hwC hwW).elim

theorem commSub_smul_mem {Y Y' : Subgroup (MulAut V)} {M M' : Subgroup V} (b : MulAut V)
    (hY : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y') (hM : ∀ m ∈ M, b m ∈ M') :
    ∀ c ∈ commSub M Y, b c ∈ commSub M' Y' := by
  intro c hc
  refine Subgroup.closure_induction (p := fun c _ => b c ∈ commSub M' Y') ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨y, hy, w, hw, rfl⟩
    have h1 : b (y w * w⁻¹) = (b * y * b⁻¹) (b w) * (b w)⁻¹ := by
      simp [map_mul, map_inv, MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨b * y * b⁻¹, hY y hy, b w, hM w hw, rfl⟩
  · rw [map_one]
    exact (commSub M' Y').one_mem
  · intro a a' _ _ ha ha'
    rw [map_mul]
    exact (commSub M' Y').mul_mem ha ha'
  · intro a _ ha
    rw [map_inv]
    exact (commSub M' Y').inv_mem ha

theorem fixV_smul_mem {Y : Subgroup (MulAut V)} (b : MulAut V)
    (hY : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y) {c : V} (hc : c ∈ fixV Y) : b c ∈ fixV Y := by
  intro y hy
  have h1 := hc _ (hY y hy)
  simp only [MulAut.mul_apply] at h1
  have h2 := congrArg b h1
  simpa using h2

theorem zpowers_fix {x : MulAut V} {m : V} (h : x m = m) : ∀ y ∈ Subgroup.zpowers x, y m = m := by
  intro y hy
  have hs : Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut V) m :=
    Subgroup.zpowers_le.2 (by
      rw [MulAction.mem_stabilizer_iff]
      exact h)
  have := hs hy
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem fix_of_sq_fix {x : MulAut V} {r : ℕ} (hr : Odd r) (hxr : x ^ r = 1) {m : V}
    (h : (x ^ 2) m = m) : x m = m := by
  obtain ⟨k, rfl⟩ := hr
  have hs : x ^ 2 ∈ MulAction.stabilizer (MulAut V) m := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have h1 : x ^ (2 * k) ∈ MulAction.stabilizer (MulAut V) m := by
    rw [pow_mul]
    exact Subgroup.pow_mem _ hs k
  have h2 : x = x ^ (2 * k + 1) * (x ^ (2 * k))⁻¹ := by
    rw [pow_succ]
    group
  have h3 : x ∈ MulAction.stabilizer (MulAut V) m := by
    rw [h2, hxr]
    exact Subgroup.mul_mem _ (Subgroup.one_mem _) (Subgroup.inv_mem _ h1)
  rwa [MulAction.mem_stabilizer_iff] at h3

theorem commSub_top_ne_bot {x : MulAut V} (hx : x ≠ 1) :
    commSub (⊤ : Subgroup V) (Subgroup.zpowers x) ≠ ⊥ := by
  intro h
  have := commSub_eq_bot_iff.1 h
  exact hx (MulEquiv.ext fun v => this (Subgroup.mem_top v) x (Subgroup.mem_zpowers x))

theorem card_le_of_finset_subset [Finite V] {M : Subgroup V} (F : Finset V)
    (hF : ∀ f ∈ F, f ∈ M) : F.card ≤ Nat.card M := by
  classical
  let g : ↥F → ↥M := fun f => ⟨f.1, hF f.1 f.2⟩
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (congrArg (fun s : ↥M => (s : V)) h)
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card ↥F = F.card := by simp
  rw [h2] at h1
  exact h1

theorem card_le_of_injOn {M : Subgroup V} (f : V → V) (S : Finset V) (hf : ∀ m ∈ M, f m ∈ S)
    (hinj : ∀ m ∈ M, ∀ m' ∈ M, f m = f m' → m = m') : Nat.card M ≤ S.card := by
  classical
  let g : ↥M → ↥S := fun m => ⟨f m.1, hf m.1 m.2⟩
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg (fun s : ↥S => (s : V)) h))
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card ↥S = S.card := by simp
  rw [h2] at h1
  exact h1

theorem inverted_by_transvection [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} {w : V}
    (ht : IsTransvectionWith t w) (ht1 : t ≠ 1) {x : MulAut V} {r : ℕ} (hr : Odd r)
    (hxr : x ^ r = 1) (hx1 : x ≠ 1) (htx : t * x * t⁻¹ = x⁻¹) :
    w ∈ commSub ⊤ (Subgroup.zpowers x) ∧ (∀ c ∈ fixV (Subgroup.zpowers x), t c = c) ∧
      Nat.card (commSub ⊤ (Subgroup.zpowers x)) = 4 ∧ x ^ 3 = 1 := by
  classical
  set Y := Subgroup.zpowers x with hYdef
  have hYodd : Odd (Nat.card Y) := by
    rw [hYdef, Nat.card_zpowers]
    exact Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one hxr)
  have hMYtop : ∀ y ∈ Y, ∀ m ∈ (⊤ : Subgroup V), y m ∈ (⊤ : Subgroup V) :=
    fun _ _ _ _ => trivial
  obtain ⟨hsup0, hinf0⟩ := coprime_decomp hV hYodd hMYtop
  have hsup : fixV Y ⊔ commSub ⊤ Y = ⊤ := by simpa using hsup0
  have hinf : fixV Y ⊓ commSub ⊤ Y = ⊥ := by simpa using hinf0
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (tv_sq hV ht ht1)
  have hxY : x ∈ Y := Subgroup.mem_zpowers x
  have hconj : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : t * x ^ k * t⁻¹ = (x⁻¹) ^ k := by
      have := map_zpow (MulAut.conj t) x k
      simpa [MulAut.conj_apply, htx] using this
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ hxY) k
  have hconj' : ∀ y ∈ Y, t⁻¹ * y * t ∈ Y := by
    intro y hy
    have := hconj y hy
    rw [htinv] at this ⊢
    exact this
  have hCt : ∀ c ∈ fixV Y, t c ∈ fixV Y := fun c hc => fixV_smul_mem t hconj' hc
  have hMt : ∀ m ∈ commSub ⊤ Y, t m ∈ commSub ⊤ Y :=
    commSub_smul_mem t hconj (fun _ _ => trivial)
  have hxn : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun y hy =>
    Y.mul_mem (Y.mul_mem hxY hy) (Y.inv_mem hxY)
  have hMx : ∀ m ∈ commSub ⊤ Y, x m ∈ commSub ⊤ Y :=
    commSub_smul_mem x hxn (fun _ _ => trivial)
  have hfpf : ∀ m ∈ commSub ⊤ Y, x m = m → m = 1 := by
    intro m hm hxm
    have hfix : m ∈ fixV Y := fun y hy => zpowers_fix hxm y hy
    have : m ∈ fixV Y ⊓ commSub ⊤ Y := ⟨hfix, hm⟩
    rw [hinf] at this
    exact this
  have hfpf2 : ∀ m ∈ commSub ⊤ Y, (x ^ 2) m = m → m = 1 := fun m hm h2 =>
    hfpf m hm (fix_of_sq_fix hr hxr h2)
  have hMne : commSub ⊤ Y ≠ ⊥ := commSub_top_ne_bot hx1
  have hrel : t * x = x⁻¹ * t := by
    have := congrArg (· * t) htx
    simpa [mul_assoc] using this
  rcases tv_split ht ht1 hinf hsup hCt hMt with ⟨hwM, hCfix⟩ | ⟨hwC, hMfix⟩
  swap
  · exfalso
    have hx2 : ∀ m ∈ commSub ⊤ Y, (x ^ 2) m = m := by
      intro m hm
      have h1 : x⁻¹ m = x m := by
        have h2 := congrArg (fun s : MulAut V => s m) hrel
        simp only [MulAut.mul_apply] at h2
        rw [hMfix (x m) (hMx m hm), hMfix m hm] at h2
        exact h2.symm
      calc (x ^ 2) m = x (x m) := by rw [pow_two]; rfl
        _ = x (x⁻¹ m) := by rw [h1]
        _ = m := by simp
    exact hMne ((Subgroup.eq_bot_iff_forall _).2 fun m hm => hfpf2 m hm (hx2 m hm))
  refine ⟨hwM, hCfix, ?_⟩
  have hw2 : w * w = 1 := by rw [← sq]; exact hV w
  have hz2 : (x⁻¹ w) * (x⁻¹ w) = 1 := by rw [← sq]; exact hV _
  have hzinv : (x⁻¹ w)⁻¹ = x⁻¹ w := inv_eq_of_mul_eq_one_right hz2
  let S : Finset V := {1, w, x⁻¹ w, w * x⁻¹ w}
  have hθS : ∀ m ∈ commSub ⊤ Y, x⁻¹ m * (x m)⁻¹ ∈ S := by
    intro m hm
    have hrelm : t (x m) = x⁻¹ (t m) := by
      have h2 := congrArg (fun s : MulAut V => s m) hrel
      simpa only [MulAut.mul_apply] using h2
    rcases ht.2 m with h1 | h1
    · rw [h1] at hrelm
      rcases ht.2 (x m) with h2 | h2
      · rw [h2] at hrelm
        have : x⁻¹ m * (x m)⁻¹ = 1 := by rw [← hrelm, mul_inv_cancel]
        rw [this]
        simp [S]
      · rw [h2] at hrelm
        have : x⁻¹ m * (x m)⁻¹ = w := by
          rw [← hrelm, mul_comm (x m) w, mul_inv_cancel_right]
        rw [this]
        simp [S]
    · rw [h1, map_mul] at hrelm
      rcases ht.2 (x m) with h2 | h2
      · rw [h2] at hrelm
        have : x⁻¹ m * (x m)⁻¹ = x⁻¹ w := by
          rw [hrelm, mul_inv, mul_inv_cancel_left, hzinv]
        rw [this]
        simp [S]
      · rw [h2] at hrelm
        have : x⁻¹ m * (x m)⁻¹ = w * x⁻¹ w := by
          rw [mul_inv_eq_iff_eq_mul]
          calc x⁻¹ m = x⁻¹ m * x⁻¹ w * (x⁻¹ w)⁻¹ := by rw [mul_inv_cancel_right]
            _ = x m * w * (x⁻¹ w)⁻¹ := by rw [← hrelm]
            _ = w * x⁻¹ w * x m := by rw [hzinv, mul_assoc, mul_comm]
        rw [this]
        simp [S]
  have hθinj : ∀ m ∈ commSub ⊤ Y, ∀ m' ∈ commSub ⊤ Y,
      x⁻¹ m * (x m)⁻¹ = x⁻¹ m' * (x m')⁻¹ → m = m' := by
    intro m hm m' hm' h
    have hn : m * m'⁻¹ ∈ commSub ⊤ Y :=
      (commSub ⊤ Y).mul_mem hm ((commSub ⊤ Y).inv_mem hm')
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at h
    have h1 : x⁻¹ (m * m'⁻¹) = x (m * m'⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
        div_eq_div_iff_mul_eq_mul]
      rw [h, mul_comm]
    have h2 : (x ^ 2) (m * m'⁻¹) = m * m'⁻¹ := by
      calc (x ^ 2) (m * m'⁻¹) = x (x (m * m'⁻¹)) := by rw [pow_two]; rfl
        _ = x (x⁻¹ (m * m'⁻¹)) := by rw [h1]
        _ = m * m'⁻¹ := by simp
    exact mul_inv_eq_one.1 (hfpf2 _ hn h2)
  have hcard4 : Nat.card (commSub ⊤ Y) ≤ 4 :=
    (card_le_of_injOn (fun m => x⁻¹ m * (x m)⁻¹) S hθS hθinj).trans Finset.card_le_four
  obtain ⟨m₀, hm₀M, hm₀1⟩ : ∃ m ∈ commSub ⊤ Y, m ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hMne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hm₁M : x m₀ ∈ commSub ⊤ Y := hMx m₀ hm₀M
  have hm₂M : x (x m₀) ∈ commSub ⊤ Y := hMx _ hm₁M
  have hm₃M : x (x (x m₀)) ∈ commSub ⊤ Y := hMx _ hm₂M
  have h1ne1 : x m₀ ≠ 1 := fun h => hm₀1 (x.injective (by rw [map_one]; exact h))
  have h2ne1 : x (x m₀) ≠ 1 := fun h => h1ne1 (x.injective (by rw [map_one]; exact h))
  have hne01 : m₀ ≠ x m₀ := fun h => hm₀1 (hfpf m₀ hm₀M h.symm)
  have hx2 : ∀ m, (x ^ 2) m = x (x m) := fun m => by rw [pow_two]; rfl
  have hne02 : m₀ ≠ x (x m₀) := fun h => hm₀1 (hfpf2 m₀ hm₀M (by rw [hx2]; exact h.symm))
  have hne12 : x m₀ ≠ x (x m₀) := fun h => h1ne1 (hfpf _ hm₁M h.symm)
  have hcardF : ({1, m₀, x m₀, x (x m₀)} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne12]
    · simp [hne01, hne02]
    · simp [hm₀1.symm, h1ne1.symm, h2ne1.symm]
  have hFM : ∀ f ∈ ({1, m₀, x m₀, x (x m₀)} : Finset V), f ∈ commSub ⊤ Y := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact (commSub ⊤ Y).one_mem
    · exact hm₀M
    · exact hm₁M
    · exact hm₂M
  have hcardM : Nat.card (commSub ⊤ Y) = 4 :=
    le_antisymm hcard4 (hcardF ▸ card_le_of_finset_subset _ hFM)
  refine ⟨hcardM, ?_⟩
  have hexh : ∀ m ∈ commSub ⊤ Y, m ∈ ({1, m₀, x m₀, x (x m₀)} : Finset V) := by
    intro m hm
    by_contra hnot
    have hcard5 : (insert m ({1, m₀, x m₀, x (x m₀)} : Finset V)).card = 5 := by
      rw [Finset.card_insert_of_notMem hnot, hcardF]
    have := card_le_of_finset_subset (insert m ({1, m₀, x m₀, x (x m₀)} : Finset V)) (by
      intro f hf
      rw [Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact hm
      · exact hFM f hf)
    rw [hcard5, hcardM] at this
    omega
  have hx3 : ∀ m, (x ^ 3) m = x (x (x m)) := fun m => by rw [pow_succ, pow_two]; rfl
  have hx3m₀ : x (x (x m₀)) = m₀ := by
    have hmem := hexh (x (x (x m₀))) hm₃M
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd (x.injective (by rw [map_one]; exact h)) h2ne1
    · exact h
    · exact absurd (x.injective h).symm hne02
    · exact absurd (x.injective (x.injective h)).symm hne01
  have hx3fix : ∀ m ∈ commSub ⊤ Y, x (x (x m)) = m := by
    intro m hm
    have hmem := hexh m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · simp
    · exact hx3m₀
    · rw [hx3m₀]
    · rw [hx3m₀]
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ fixV Y ⊔ commSub ⊤ Y := by rw [hsup]; trivial
  obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
  show (x ^ 3) (c * m) = c * m
  rw [map_mul, hc (x ^ 3) (Subgroup.pow_mem _ hxY 3), hx3, hx3fix m hm]

theorem zpowers_decomp [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} {r : ℕ} (hr : Odd r)
    (hxr : x ^ r = 1) :
    fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) = ⊤ ∧
      fixV (Subgroup.zpowers x) ⊓ commSub ⊤ (Subgroup.zpowers x) = ⊥ ∧
      (∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), x m ∈ commSub ⊤ (Subgroup.zpowers x)) ∧
      (∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), x m = m → m = 1) := by
  have hYodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one hxr)
  obtain ⟨hsup0, hinf0⟩ := coprime_decomp hV hYodd (M := ⊤) (fun _ _ _ _ => trivial)
  have hsup : fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) = ⊤ := by
    simpa using hsup0
  have hinf : fixV (Subgroup.zpowers x) ⊓ commSub ⊤ (Subgroup.zpowers x) = ⊥ := by
    simpa using hinf0
  have hxY : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  refine ⟨hsup, hinf, ?_, ?_⟩
  · exact commSub_smul_mem x (fun y hy => Subgroup.mul_mem _ (Subgroup.mul_mem _ hxY hy)
      (Subgroup.inv_mem _ hxY)) (fun _ _ => trivial)
  · intro m hm hxm
    have hfix : m ∈ fixV (Subgroup.zpowers x) := fun y hy => zpowers_fix hxm y hy
    have : m ∈ fixV (Subgroup.zpowers x) ⊓ commSub ⊤ (Subgroup.zpowers x) := ⟨hfix, hm⟩
    rw [hinf] at this
    exact this

theorem four_elements [Finite V] {M : Subgroup V} {x : MulAut V} (hMx : ∀ m ∈ M, x m ∈ M)
    (hfpf : ∀ m ∈ M, x m = m → m = 1) (hfpf2 : ∀ m ∈ M, x (x m) = m → m = 1)
    (hcard : Nat.card M ≤ 4) {m₀ : V} (hm₀ : m₀ ∈ M) (hm₀1 : m₀ ≠ 1) :
    ∀ m ∈ M, m = 1 ∨ m = m₀ ∨ m = x m₀ ∨ m = x (x m₀) := by
  classical
  have hm₁M : x m₀ ∈ M := hMx m₀ hm₀
  have hm₂M : x (x m₀) ∈ M := hMx _ hm₁M
  have h1ne1 : x m₀ ≠ 1 := fun h => hm₀1 (x.injective (by rw [map_one]; exact h))
  have h2ne1 : x (x m₀) ≠ 1 := fun h => h1ne1 (x.injective (by rw [map_one]; exact h))
  have hne01 : m₀ ≠ x m₀ := fun h => hm₀1 (hfpf m₀ hm₀ h.symm)
  have hne02 : m₀ ≠ x (x m₀) := fun h => hm₀1 (hfpf2 m₀ hm₀ h.symm)
  have hne12 : x m₀ ≠ x (x m₀) := fun h => h1ne1 (hfpf _ hm₁M h.symm)
  have hcardF : ({1, m₀, x m₀, x (x m₀)} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne12]
    · simp [hne01, hne02]
    · simp [hm₀1.symm, h1ne1.symm, h2ne1.symm]
  have hFM : ∀ f ∈ ({1, m₀, x m₀, x (x m₀)} : Finset V), f ∈ M := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact M.one_mem
    · exact hm₀
    · exact hm₁M
    · exact hm₂M
  intro m hm
  by_contra hnot
  have hnot' : m ∉ ({1, m₀, x m₀, x (x m₀)} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hnot
  have hcard5 : (insert m ({1, m₀, x m₀, x (x m₀)} : Finset V)).card = 5 := by
    rw [Finset.card_insert_of_notMem hnot', hcardF]
  have := card_le_of_finset_subset (M := M) (insert m ({1, m₀, x m₀, x (x m₀)} : Finset V)) (by
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact hm
    · exact hFM f hf)
  rw [hcard5] at this
  omega

theorem fix_or_pow_on_M [Finite V] {M : Subgroup V} {x z : MulAut V} (hMx : ∀ m ∈ M, x m ∈ M)
    (hMz : ∀ m ∈ M, z m ∈ M) (hxz : x * z = z * x) (hfpf : ∀ m ∈ M, x m = m → m = 1)
    (hfpf2 : ∀ m ∈ M, x (x m) = m → m = 1) (hcard : Nat.card M ≤ 4) (hM1 : M ≠ ⊥) :
    (∀ m ∈ M, z m = m) ∨ (∀ m ∈ M, z m = x m) ∨ (∀ m ∈ M, z m = x (x m)) := by
  obtain ⟨m₀, hm₀M, hm₀1⟩ : ∃ m ∈ M, m ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hM1 ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hcommx : ∀ m, z (x m) = x (z m) := fun m => by
    have := congrArg (fun s : MulAut V => s m) hxz
    simp only [MulAut.mul_apply] at this
    exact this.symm
  have hexh := four_elements hMx hfpf hfpf2 hcard hm₀M hm₀1
  have hzm₀ : z m₀ = m₀ ∨ z m₀ = x m₀ ∨ z m₀ = x (x m₀) := by
    have hmem := hexh (z m₀) (hMz m₀ hm₀M)
    rcases hmem with h | h | h | h
    · exact absurd (z.injective (by rw [map_one]; exact h)) hm₀1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hzm₀ with h | h | h
  · left
    intro m hm
    rcases hexh m hm with rfl | rfl | rfl | rfl
    · simp
    · exact h
    · rw [hcommx, h]
    · rw [hcommx, hcommx, h]
  · right; left
    intro m hm
    rcases hexh m hm with rfl | rfl | rfl | rfl
    · simp
    · exact h
    · rw [hcommx, h]
    · rw [hcommx, hcommx, h]
  · right; right
    intro m hm
    rcases hexh m hm with rfl | rfl | rfl | rfl
    · simp
    · exact h
    · rw [hcommx, h]
    · rw [hcommx, hcommx, h]

theorem z_mem_of_eq_on_M [Finite V] {x z q : MulAut V}
    (hsup : fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) = ⊤)
    (hinf : fixV (Subgroup.zpowers x) ⊓ commSub ⊤ (Subgroup.zpowers x) = ⊥)
    (hMx : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = 4)
    (hMz : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers z)) = 4)
    (hq : q ∈ Subgroup.zpowers x)
    (hqM : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
      q m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x))
    (hqfpf : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), q m = m → m = 1)
    (hz : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), z m = q m)
    (hzn' : ∀ y ∈ Subgroup.zpowers x, z⁻¹ * y * z ∈ Subgroup.zpowers x) :
    z ∈ Subgroup.zpowers x := by
  set M := commSub (⊤ : Subgroup V) (Subgroup.zpowers x) with hMdef
  have hzM : ∀ m ∈ M, z m * m⁻¹ ∈ M := by
    intro m hm
    rw [hz m hm]
    exact M.mul_mem (hqM m hm) (M.inv_mem hm)
  have hinj : ∀ m ∈ M, ∀ m' ∈ M, z m * m⁻¹ = z m' * m'⁻¹ → m = m' := by
    intro m hm m' hm' hmm
    have hn : m * m'⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hm')
    have hmm' : z m * m' = z m' * m := by
      have := hmm
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at this
      exact this
    have htarget : z m * (z m')⁻¹ = m * m'⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, mul_comm m (z m')]
      exact hmm'
    have h1 : q (m * m'⁻¹) = m * m'⁻¹ := by
      rw [map_mul, map_inv, ← hz m hm, ← hz m' hm']
      exact htarget
    exact mul_inv_eq_one.1 (hqfpf _ hn h1)
  let g : ↥M → ↥M := fun m => ⟨z m.1 * m.1⁻¹, hzM m.1 m.2⟩
  have hginj : Function.Injective g := fun a b h =>
    Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg (fun s : ↥M => (s : V)) h))
  have hgsurj : Function.Surjective g := Finite.surjective_of_injective hginj
  have hMle : M ≤ commSub ⊤ (Subgroup.zpowers z) := by
    intro m hm
    obtain ⟨⟨m', hm'⟩, hm'eq⟩ := hgsurj ⟨m, hm⟩
    have : z m' * m'⁻¹ = m := congrArg (fun s : ↥M => (s : V)) hm'eq
    rw [← this]
    exact Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, m', trivial, rfl⟩
  have hMeq : M = commSub ⊤ (Subgroup.zpowers z) :=
    Subgroup.eq_of_le_of_card_ge hMle (by rw [hMz, hMx])
  have hCz : ∀ c ∈ fixV (Subgroup.zpowers x), z c = c := by
    intro c hc
    have hzc : z c ∈ fixV (Subgroup.zpowers x) := fixV_smul_mem z hzn' hc
    have hd1 : z c * c⁻¹ ∈ fixV (Subgroup.zpowers x) :=
      Subgroup.mul_mem _ hzc (Subgroup.inv_mem _ hc)
    have hd2 : z c * c⁻¹ ∈ M := by
      rw [hMeq]
      exact Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, c, trivial, rfl⟩
    have : z c * c⁻¹ ∈ fixV (Subgroup.zpowers x) ⊓ M := ⟨hd1, hd2⟩
    rw [hinf] at this
    exact mul_inv_eq_one.1 this
  have hzq : z = q := by
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ M := by rw [hsup]; trivial
    obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul, map_mul, hCz c hc, hc q hq, hz m hm]
  rw [hzq]
  exact hq

theorem commuting_fixes_aux [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x z : MulAut V}
    (hxz : x * z = z * x) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hMx : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = 4)
    (hMz : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers z)) = 4)
    (hnot : z ∉ Subgroup.zpowers x) :
    ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), z m = m := by
  obtain ⟨hsup, hinf, hMxinv, hfpf⟩ := zpowers_decomp hV (r := 3) (by decide) hx3
  have hfpf2 : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), x (x m) = m → m = 1 :=
    fun m hm h => hfpf m hm (fix_of_sq_fix (r := 3) (by decide) hx3 (by rw [pow_two]; exact h))
  have hxY : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  have hzcomm : ∀ y ∈ Subgroup.zpowers x, z * y = y * z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_right (show Commute z x from hxz.symm) k).eq)
  have hzn : ∀ y ∈ Subgroup.zpowers x, z * y * z⁻¹ ∈ Subgroup.zpowers x := by
    intro y hy
    rw [hzcomm y hy]
    simpa using hy
  have hzn' : ∀ y ∈ Subgroup.zpowers x, z⁻¹ * y * z ∈ Subgroup.zpowers x := by
    intro y hy
    have : z⁻¹ * y * z = y := by
      calc z⁻¹ * y * z = z⁻¹ * (y * z) := by rw [mul_assoc]
        _ = z⁻¹ * (z * y) := by rw [hzcomm y hy]
        _ = y := by rw [inv_mul_cancel_left]
    rw [this]
    exact hy
  have hMzM : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
      z m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) :=
    commSub_smul_mem z hzn (fun _ _ => trivial)
  have hMne : commSub (⊤ : Subgroup V) (Subgroup.zpowers x) ≠ ⊥ := commSub_top_ne_bot hx1
  rcases fix_or_pow_on_M hMxinv hMzM hxz hfpf hfpf2 hMx.le hMne with h | h | h
  · exact h
  · exact absurd (z_mem_of_eq_on_M hsup hinf hMx hMz hxY hMxinv hfpf h hzn') hnot
  · refine absurd (z_mem_of_eq_on_M (q := x * x) hsup hinf hMx hMz
      (Subgroup.mul_mem _ hxY hxY) (fun m hm => hMxinv _ (hMxinv m hm))
      (fun m hm hh => hfpf2 m hm hh) (fun m hm => by rw [h m hm]; rfl) hzn') hnot

theorem commuting_fixes [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x z : MulAut V}
    (hxz : x * z = z * x) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1) (hz1 : z ≠ 1)
    (hMx : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = 4)
    (hMz : Nat.card (commSub (⊤ : Subgroup V) (Subgroup.zpowers z)) = 4)
    (hnot : z ∉ Subgroup.zpowers x) :
    (∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), z m = m) ∧
      ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers z), x m = m := by
  refine ⟨commuting_fixes_aux hV hxz hx3 hx1 hMx hMz hnot, ?_⟩
  refine commuting_fixes_aux hV hxz.symm hz3 hz1 hMz hMx ?_
  intro hxz'
  apply hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers z := Subgroup.zpowers_le.2 hxz'
  have heq : Subgroup.zpowers x = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoz])
  rw [heq]
  exact Subgroup.mem_zpowers z

theorem conj_mem_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t t' : MulAut V} {w w' : V}
    (ht : IsTransvectionWith t w) (ht1 : t ≠ 1) (ht' : IsTransvectionWith t' w')
    {x : MulAut V} {r : ℕ} (hr : Odd r) (hxr : x ^ r = 1) (hx1 : x ≠ 1)
    (htx : t * x * t⁻¹ = x⁻¹) (hxz : x * (t' * x * t'⁻¹) = (t' * x * t'⁻¹) * x) :
    t' * x * t'⁻¹ ∈ Subgroup.zpowers x := by
  by_contra hnot
  set z : MulAut V := t' * x * t'⁻¹ with hzdef
  have ht'1 : t' ≠ 1 := by
    intro h
    apply hnot
    rw [hzdef, h]
    simp
  obtain ⟨hwM, hCfix, hMx4, hx3⟩ := inverted_by_transvection hV ht ht1 hr hxr hx1 htx
  have hzr : z ^ r = 1 := by
    have := map_pow (MulAut.conj t') x r
    simp only [MulAut.conj_apply] at this
    rw [hzdef, ← this, hxr]
    simp
  have hz1 : z ≠ 1 := tv_conj_ne_one hx1 t'
  have ht'' : IsTransvectionWith (t' * t * t'⁻¹) (t' w) := tv_conj ht t'
  have ht''1 : t' * t * t'⁻¹ ≠ 1 := tv_conj_ne_one ht1 t'
  have ht''z : (t' * t * t'⁻¹) * z * (t' * t * t'⁻¹)⁻¹ = z⁻¹ := by
    have : (t' * t * t'⁻¹) * z * (t' * t * t'⁻¹)⁻¹ = t' * (t * x * t⁻¹) * t'⁻¹ := by
      rw [hzdef]
      group
    rw [this, htx, hzdef]
    group
  obtain ⟨hwM', hCfix', hMz4, hz3⟩ := inverted_by_transvection hV ht'' ht''1 hr hzr hz1 ht''z
  obtain ⟨hfixz, hfixx⟩ := commuting_fixes hV hxz hx3 hz3 hx1 hz1 hMx4 hMz4 hnot
  obtain ⟨-, hinfz, -, -⟩ := zpowers_decomp hV (r := r) hr hzr
  have hdisj : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
      m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers z) → m = 1 := by
    intro m hmx hmz
    have hfix : m ∈ fixV (Subgroup.zpowers z) := fun y hy => zpowers_fix (hfixz m hmx) y hy
    have : m ∈ fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) := ⟨hfix, hmz⟩
    rw [hinfz] at this
    exact this
  have hmap : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
      t' m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers z) := by
    refine commSub_smul_mem t' (fun y hy => ?_) (fun _ _ => trivial)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have := map_zpow (MulAut.conj t') x k
    simp only [MulAut.conj_apply] at this
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  obtain ⟨hsupx, hinfx, hMxinv, hfpf⟩ := zpowers_decomp hV hr hxr
  have hMne : commSub (⊤ : Subgroup V) (Subgroup.zpowers x) ≠ ⊥ := commSub_top_ne_bot hx1
  obtain ⟨m₀, hm₀M, hm₀1⟩ : ∃ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), m ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hMne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hmoved : ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), m ≠ 1 → t' m = m * w' := by
    intro m hm hm1
    rcases ht'.2 m with h | h
    · exact absurd (hdisj m hm (h ▸ hmap m hm)) hm1
    · exact h
  have hm₁M : x m₀ ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) := hMxinv m₀ hm₀M
  have h1ne1 : x m₀ ≠ 1 := fun h => hm₀1 (x.injective (by rw [map_one]; exact h))
  have hne01 : m₀ ≠ x m₀ := fun h => hm₀1 (hfpf m₀ hm₀M h.symm)
  have hn : m₀ * (x m₀)⁻¹ ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) :=
    Subgroup.mul_mem _ hm₀M (Subgroup.inv_mem _ hm₁M)
  have hnfix : t' (m₀ * (x m₀)⁻¹) = m₀ * (x m₀)⁻¹ := by
    rw [map_mul, map_inv, hmoved m₀ hm₀M hm₀1, hmoved (x m₀) hm₁M h1ne1, mul_inv,
      mul_mul_mul_comm, mul_inv_cancel, mul_one]
  have hnz : m₀ * (x m₀)⁻¹ ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers z) :=
    hnfix ▸ hmap _ hn
  exact hne01 (mul_inv_eq_one.1 (hdisj _ hn hnz))

open scoped commutatorElement in
theorem exists_normal_elem_abelian_odd {G : Type*} [Group G] [Finite G]
    (hG : Group.IsSolvable G) (hne : Nontrivial G)
    (hO : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 Q → Q = ⊥) :
    ∃ (r : ℕ) (N : Subgroup G), r.Prime ∧ Odd r ∧ N.Normal ∧ N ≠ ⊥ ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ ∀ n ∈ N, n ^ r = 1 := by
  classical
  obtain ⟨D, hDn, hDc, hD1⟩ : ∃ D : Subgroup G, D.Normal ∧
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∧ D ≠ ⊥ := by
    let p : ℕ → Prop := fun n => derivedSeries G n = ⊥
    have h : ∃ n, p n := hG.solvable
    let i := Nat.find h
    have hi : i ≠ 0 := by
      have : ¬ p 0 := by
        simp [p, derivedSeries_zero]
      exact (Nat.find_eq_zero h).not.mpr this
    refine ⟨derivedSeries G (i - 1), derivedSeries_normal _ _, ?_, Nat.find_min h (Nat.sub_one_lt hi)⟩
    intro a ha b hb
    have hcomm : ⁅derivedSeries G (i - 1), derivedSeries G (i - 1)⁆ = ⊥ := by
      rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
      exact Nat.find_spec h
    have hc : ⁅a, b⁆ ∈ ⁅derivedSeries G (i - 1), derivedSeries G (i - 1)⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hDcard : 1 < Nat.card D := (Subgroup.one_lt_card_iff_ne_bot D).2 hD1
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hDcard)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) r hrdvd
  let N : Subgroup G :=
    { carrier := {g | g ∈ D ∧ g ^ r = 1}
      mul_mem' := fun {a b} ha hb => ⟨D.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (show Commute a b from hDc a ha.1 b hb.1)), ha.2, hb.2, mul_one]⟩
      one_mem' := ⟨D.one_mem, one_pow r⟩
      inv_mem' := fun {a} ha => ⟨D.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hNn : N.Normal := ⟨fun n hn g => ⟨hDn.conj_mem n hn.1 g, by
    have : (g * n * g⁻¹) ^ r = g * n ^ r * g⁻¹ := by
      simp
    rw [this, hn.2]
    simp⟩⟩
  have hdN : (d : G) ∈ N := ⟨d.2, by
    have := pow_orderOf_eq_one d
    rw [hd] at this
    exact congrArg Subtype.val this⟩
  have hd1 : (d : G) ≠ 1 := by
    intro h
    have : d = 1 := Subtype.ext h
    rw [this, orderOf_one] at hd
    exact hr.one_lt.ne hd
  have hN1 : N ≠ ⊥ := fun h => hd1 (by
    have := hdN
    rw [h, Subgroup.mem_bot] at this
    exact this)
  refine ⟨r, N, hr, ?_, hNn, hN1, fun a ha b hb => hDc a ha.1 b hb.1, fun n hn => hn.2⟩
  rcases hr.eq_two_or_odd' with h2 | hodd
  · exfalso
    apply hN1
    refine hO N hNn ?_
    intro n
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := n.2.2
    rw [h2] at this
    simpa using this
  · exact hodd

theorem exists_normal_elem_abelian_odd_sub [Finite V] {J : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥J) (hJ1 : J ≠ ⊥)
    (hO : ∀ Q : Subgroup (MulAut V), Q ≤ J → (Q.subgroupOf J).Normal → IsPGroup 2 Q → Q = ⊥) :
    ∃ (r : ℕ) (N : Subgroup (MulAut V)), r.Prime ∧ Odd r ∧ N ≤ J ∧
      (∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N) ∧ N ≠ ⊥ ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      ∀ n ∈ N, n ^ r = 1 := by
  have hne : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 hJ1
  obtain ⟨r, N, hr, hodd, hNn, hN1, hNc, hNr⟩ := exists_normal_elem_abelian_odd hsolv hne (by
    intro Q hQ hQp
    have : Q.map J.subtype = ⊥ := by
      refine hO _ (Subgroup.map_subtype_le Q) ?_ (hQp.map J.subtype)
      have hsub : (Q.map J.subtype).subgroupOf J = Q :=
        Subgroup.comap_map_eq_self_of_injective J.subtype_injective Q
      rw [hsub]
      exact hQ
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 this)
  refine ⟨r, N.map J.subtype, hr, hodd, Subgroup.map_subtype_le N, ?_, ?_, ?_, ?_⟩
  · rintro j hj _ ⟨n, hn, rfl⟩
    exact ⟨⟨j, hj⟩ * n * ⟨j, hj⟩⁻¹, hNn.conj_mem n hn ⟨j, hj⟩, rfl⟩
  · intro h
    exact hN1 ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hNc a ha b hb)
  · rintro _ ⟨n, hn, rfl⟩
    exact congrArg Subtype.val (hNr n hn)

theorem exists_transvection_not_central [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {J N : Subgroup (MulAut V)} (hJ : Subgroup.closure (transvectionsIn J) = J) (hNJ : N ≤ J)
    {r : ℕ} (hr : Odd r) (hNr : ∀ n ∈ N, n ^ r = 1) (hN1 : N ≠ ⊥) :
    ∃ t ∈ transvectionsIn J, ∃ n ∈ N, t * n ≠ n * t := by
  by_contra hall
  push Not at hall
  let U : Subgroup V := Subgroup.closure {w | ∃ t ∈ transvectionsIn J, IsTransvectionWith t w}
  have hUfix : ∀ n ∈ N, ∀ u ∈ U, n u = u := by
    intro n hn
    have hle : U ≤ fixV (Subgroup.zpowers n) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro w ⟨t, htT, hw⟩ y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hcomm : n ^ k * t = t * n ^ k :=
        (hall t htT (n ^ k) (Subgroup.zpow_mem _ hn k)).symm
      exact tv_comm_centre hw htT.2.1 hcomm
    intro u hu
    exact hle hu n (Subgroup.mem_zpowers n)
  let K : Subgroup (MulAut V) :=
    { carrier := {j | ∀ v : V, j v * v⁻¹ ∈ U}
      mul_mem' := fun {a b} ha hb v => by
        have h1 : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
          show a (b v) * v⁻¹ = _
          rw [mul_assoc (a (b v)), ← mul_assoc ((b v)⁻¹) (b v) v⁻¹, inv_mul_cancel, one_mul]
        rw [h1]
        exact U.mul_mem (ha (b v)) (hb v)
      one_mem' := fun v => by simp
      inv_mem' := fun {a} ha v => by
        have h1 : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
          simp
        rw [h1]
        exact U.inv_mem (ha (a⁻¹ v)) }
  have hTK : transvectionsIn J ⊆ K := by
    intro t ht v
    obtain ⟨-, w, hw⟩ := ht.2
    rcases hw.2 v with h | h
    · rw [h, mul_inv_cancel]
      exact U.one_mem
    · rw [h, mul_comm v w, mul_inv_cancel_right]
      exact Subgroup.subset_closure ⟨t, ht, hw⟩
  have hJK : J ≤ K := by
    rw [← hJ]
    exact (Subgroup.closure_le _).2 hTK
  apply hN1
  refine (Subgroup.eq_bot_iff_forall _).2 fun n hn => ?_
  by_contra hn1
  have hnodd : n ^ r = 1 := hNr n hn
  obtain ⟨-, hinf, -, -⟩ := zpowers_decomp hV hr hnodd
  have hle : commSub (⊤ : Subgroup V) (Subgroup.zpowers n) ≤ fixV (Subgroup.zpowers n) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨y, hy, v, -, rfl⟩
    have hyN : y ∈ N := (Subgroup.zpowers_le.2 hn) hy
    have hyU : y v * v⁻¹ ∈ U := hJK (hNJ hyN) v
    intro y' hy'
    exact hUfix y' ((Subgroup.zpowers_le.2 hn) hy') _ hyU
  have hbot : commSub (⊤ : Subgroup V) (Subgroup.zpowers n) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun m hm => ?_
    have : m ∈ fixV (Subgroup.zpowers n) ⊓ commSub ⊤ (Subgroup.zpowers n) := ⟨hle hm, hm⟩
    rw [hinf] at this
    exact this
  exact commSub_top_ne_bot hn1 hbot

theorem exists_normal_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {J N : Subgroup (MulAut V)}
    (hJ : Subgroup.closure (transvectionsIn J) = J) (hNJ : N ≤ J)
    (hNn : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N) (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {r : ℕ}
    (hr : Odd r) (hNr : ∀ n ∈ N, n ^ r = 1) (hN1 : N ≠ ⊥) :
    ∃ x t : MulAut V, x ∈ J ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧ t ∈ transvectionsIn J ∧
      t * x * t⁻¹ = x⁻¹ ∧ ∀ j ∈ J, j * x * j⁻¹ ∈ Subgroup.zpowers x := by
  obtain ⟨t, htT, n, hnN, hne⟩ := exists_transvection_not_central hV hJ hNJ hr hNr hN1
  obtain ⟨ht1, w, htw⟩ := htT.2
  have hsq : t * t = 1 := tv_sq hV htw ht1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  have htnN : t * n * t⁻¹ ∈ N := hNn t htT.1 n hnN
  set x : MulAut V := n * (t * n * t⁻¹)⁻¹ with hxdef
  have hxN : x ∈ N := N.mul_mem hnN (N.inv_mem htnN)
  have htx : t * x * t⁻¹ = x⁻¹ := by
    have h1 : t * (t * n * t⁻¹) * t⁻¹ = n := by
      rw [htinv]
      calc t * (t * n * t) * t = (t * t) * n * (t * t) := by group
        _ = n := by rw [hsq]; group
    calc t * x * t⁻¹ = (t * n * t⁻¹) * (t * (t * n * t⁻¹) * t⁻¹)⁻¹ := by rw [hxdef]; group
      _ = (t * n * t⁻¹) * n⁻¹ := by rw [h1]
      _ = x⁻¹ := by rw [hxdef]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    have h2 : n = t * n * t⁻¹ := by
      have : n * (t * n * t⁻¹)⁻¹ = 1 := by rw [← hxdef]; exact h
      exact mul_inv_eq_one.1 this
    calc t * n = (t * n * t⁻¹) * t := by group
      _ = n * t := by rw [← h2]
  obtain ⟨hwM, hCfix, hMx4, hx3⟩ := inverted_by_transvection hV htw ht1 hr (hNr x hxN) hx1 htx
  refine ⟨x, t, hNJ hxN, hx1, hx3, htT, htx, ?_⟩
  have hT : ∀ t' ∈ transvectionsIn J, t' ∈ Subgroup.normalizer (Subgroup.zpowers x : Set (MulAut V)) := by
    intro t' ht'
    obtain ⟨ht'1, w', ht'w⟩ := ht'.2
    have hz : t' * x * t'⁻¹ ∈ Subgroup.zpowers x := by
      refine conj_mem_zpowers hV htw ht1 ht'w hr (hNr x hxN) hx1 htx ?_
      exact hNc x hxN _ (hNn t' ht'.1 x hxN)
    have hfwd : ∀ h ∈ Subgroup.zpowers x, t' * h * t'⁻¹ ∈ Subgroup.zpowers x := by
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      have := map_zpow (MulAut.conj t') x k
      simp only [MulAut.conj_apply] at this
      rw [this]
      exact Subgroup.zpow_mem _ hz k
    have hsq' : t' * t' = 1 := tv_sq hV ⟨ht'w.1, ht'w.2⟩ ht'1
    have hinv' : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right hsq'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have := hfwd _ hh
    have h2 : t' * (t' * h * t'⁻¹) * t'⁻¹ = h := by
      rw [hinv']
      calc t' * (t' * h * t') * t' = (t' * t') * h * (t' * t') := by group
        _ = h := by rw [hsq']; group
    rwa [h2] at this
  have hJle : J ≤ Subgroup.normalizer (Subgroup.zpowers x : Set (MulAut V)) := by
    rw [← hJ]
    exact (Subgroup.closure_le _).2 fun t' ht' => hT t' ht'
  intro j hj
  exact (Subgroup.mem_normalizer_iff.1 (hJle hj) x).1 (Subgroup.mem_zpowers x)

theorem isKleinFour_of_card_four (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V}
    (h4 : Nat.card W = 4) : IsKleinFour W := by
  have hexp : Monoid.exponent W = 2 := by
    have hdvd : Monoid.exponent W ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun w =>
      Subtype.ext (by simpa using hV w)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exfalso
      have hsub : Subsingleton W := ⟨fun a b => by
        have ha := Monoid.pow_exponent_eq_one a
        have hb := Monoid.pow_exponent_eq_one b
        rw [h, pow_one] at ha hb
        rw [ha, hb]⟩
      have := Finite.card_le_one_iff_subsingleton.2 hsub
      omega
    · exact h
  exact ⟨h4, hexp⟩

theorem card_mulAut_of_card_four (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V}
    (h4 : Nat.card W = 4) : Nat.card (MulAut W) = 6 := by
  have := isKleinFour_of_card_four hV h4
  exact CFSG.kleinFour_automorphism_card W

theorem solvable_of_le {J J' : Subgroup (MulAut V)} (h : J' ≤ J) (hJ : Group.IsSolvable ↥J) :
    Group.IsSolvable ↥J' :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)

theorem sup_le_normalizer_of_commute {G : Type*} [Group G] {A B Q : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hQB : Q ≤ B) (hQ : (Q.subgroupOf B).Normal) :
    A ⊔ B ≤ Subgroup.normalizer (Q : Set G) := by
  refine sup_le (fun a ha => ?_) (fun b hb => ?_)
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ k ∈ B, a * k * a⁻¹ = k := fun k hk => by rw [hcomm a ha k hk]; group
    have hc' : ∀ k ∈ B, a⁻¹ * k * a = k := fun k hk => by
      rw [hcomm a⁻¹ (A.inv_mem ha) k hk]; group
    constructor
    · intro hh
      rw [hc h (hQB hh)]
      exact hh
    · intro hh
      have h1 := hc' _ (hQB hh)
      have h2 : a⁻¹ * (a * h * a⁻¹) * a = h := by group
      rw [h2] at h1
      rw [h1]
      exact hh
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have hn := (Subgroup.normal_subgroupOf_iff hQB).1 hQ
    constructor
    · intro hh
      exact hn h b hh hb
    · intro hh
      have h1 := hn _ b⁻¹ hh (B.inv_mem hb)
      have h2 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rwa [h2] at h1

theorem transvection_structure_aux [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (n : ℕ) :
    ∀ J : Subgroup (MulAut V), Nat.card J ≤ n → Group.IsSolvable ↥J →
      (∀ Q : Subgroup (MulAut V), Q ≤ J → (Q.subgroupOf J).Normal → IsPGroup 2 Q → Q = ⊥) →
      Subgroup.closure (transvectionsIn J) = J →
      ∃ 𝓗 : Finset (Subgroup (MulAut V)),
        (⨆ H ∈ 𝓗, H) = J ∧
        (∀ H ∈ 𝓗, Nat.card H = 6 ∧ Nat.card (commSub (⊤ : Subgroup V) H) = 4 ∧
          Subgroup.closure (transvectionsIn H) = H ∧
          (∀ h ∈ H, ∀ m ∈ commSub (⊤ : Subgroup V) H, h m ∈ commSub (⊤ : Subgroup V) H) ∧
          autSub H (commSub (⊤ : Subgroup V) H) = ⊤ ∧
          ∃ C : Subgroup V, C ⊓ commSub ⊤ H = ⊥ ∧ C ⊔ commSub ⊤ H = ⊤ ∧
            ∀ h ∈ H, ∀ c ∈ C, h c = c) ∧
        (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' →
          (∀ a ∈ H, ∀ b ∈ H', a * b = b * a) ∧
            ∀ a ∈ H, ∀ u ∈ commSub (⊤ : Subgroup V) H', a u = u) ∧
        (∀ t ∈ transvectionsIn J, ∃ H ∈ 𝓗, t ∈ H) := by
  classical
  induction n with
  | zero =>
    intro J hcard
    have : 0 < Nat.card J := Nat.card_pos
    omega
  | succ n ih =>
    intro J hcard hsolv hO hJ
    by_cases hJ0 : J = ⊥
    · refine ⟨∅, ?_, by simp, by simp, ?_⟩
      · simp [hJ0]
      · intro t ht
        exfalso
        have : t = 1 := by
          have := ht.1
          rw [hJ0, Subgroup.mem_bot] at this
          exact this
        exact ht.2.1 this
    · obtain ⟨r, N, hr, hodd, hNJ, hNn, hN1, hNc, hNr⟩ :=
        exists_normal_elem_abelian_odd_sub hsolv hJ0 hO
      obtain ⟨x, t, hxJ, hx1, hx3, htT, htx, hnormx⟩ :=
        exists_normal_zpowers hV hJ hNJ hNn hNc hodd hNr hN1
      obtain ⟨ht1, w, htw⟩ := htT.2
      have hsq : t * t = 1 := tv_sq hV htw ht1
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
      obtain ⟨hwM, hCfix, hM4, -⟩ :=
        inverted_by_transvection hV htw ht1 (r := 3) (by decide) hx3 hx1 htx
      obtain ⟨hsup, hinf, hWx, hfpf⟩ := zpowers_decomp hV (r := 3) (by decide) hx3
      have hxY : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      have hJn : ∀ j ∈ J, ∀ y ∈ Subgroup.zpowers x, j * y * j⁻¹ ∈ Subgroup.zpowers x := by
        intro j hj y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have := map_zpow (MulAut.conj j) x k
        simp only [MulAut.conj_apply] at this
        rw [this]
        exact Subgroup.zpow_mem _ (hnormx j hj) k
      have hJC : ∀ j ∈ J, ∀ c ∈ fixV (Subgroup.zpowers x), j c ∈ fixV (Subgroup.zpowers x) :=
        fun j hj c hc => fixV_smul_mem j
          (fun y hy => by simpa using hJn j⁻¹ (J.inv_mem hj) y hy) hc
      have hJW : ∀ j ∈ J, ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
          j m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) :=
        fun j hj => commSub_smul_mem j (hJn j hj) (fun _ _ => trivial)
      let T1 : Set (MulAut V) :=
        {s | s ∈ transvectionsIn J ∧ ∀ c ∈ fixV (Subgroup.zpowers x), s c = c}
      let T0 : Set (MulAut V) :=
        {s | s ∈ transvectionsIn J ∧ ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), s m = m}
      have hTsplit : ∀ s ∈ transvectionsIn J, s ∈ T1 ∨ s ∈ T0 := by
        intro s hs
        obtain ⟨hs1, w', hsw⟩ := hs.2
        rcases tv_split hsw hs1 hinf hsup (hJC s hs.1) (hJW s hs.1) with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr ⟨hs, h⟩
      let J1 : Subgroup (MulAut V) := Subgroup.closure T1
      let J0 : Subgroup (MulAut V) := Subgroup.closure T0
      have hJ1J : J1 ≤ J := (Subgroup.closure_le _).2 fun s hs => hs.1.1
      have hJ0J : J0 ≤ J := (Subgroup.closure_le _).2 fun s hs => hs.1.1
      have hJeq : J = J1 ⊔ J0 := by
        refine le_antisymm ?_ (sup_le hJ1J hJ0J)
        conv_lhs => rw [← hJ]
        refine (Subgroup.closure_le _).2 fun s hs => ?_
        rcases hTsplit s hs with h | h
        · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
        · exact Subgroup.mem_sup_right (Subgroup.subset_closure h)
      have hJ1C : ∀ g ∈ J1, ∀ c ∈ fixV (Subgroup.zpowers x), g c = c := fun g hg c hc =>
        ((Subgroup.closure_le (centSub (fixV (Subgroup.zpowers x)))).2
          (fun s hs => (fun c hc => hs.2 c hc : s ∈ centSub (fixV (Subgroup.zpowers x)))) hg) c hc
      have hJ0W : ∀ g ∈ J0, ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), g m = m :=
        fun g hg m hm =>
        ((Subgroup.closure_le (centSub (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)))).2
          (fun s hs => (fun m hm => hs.2 m hm :
            s ∈ centSub (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)))) hg) m hm
      have htT1 : t ∈ T1 := ⟨htT, hCfix⟩
      have htJ1 : t ∈ J1 := Subgroup.subset_closure htT1
      have hxfixC : ∀ c ∈ fixV (Subgroup.zpowers x), x c = c := fun c hc => hc x hxY
      have hconj : x⁻¹ * t * x ∈ T1 := by
        refine ⟨⟨J.mul_mem (J.mul_mem (J.inv_mem hxJ) htT.1) hxJ, ?_⟩, ?_⟩
        · have := isTransvection_conj ⟨ht1, w, htw⟩ x⁻¹
          simpa using this
        · intro c hc
          show x⁻¹ (t (x c)) = c
          rw [hxfixC c hc, hCfix c hc]
          calc x⁻¹ c = x⁻¹ (x c) := by rw [hxfixC c hc]
            _ = c := by simp
      have hxJ1 : x ∈ J1 := by
        have h2 : t * x * t = x⁻¹ := by
          have := htx
          rwa [htinv] at this
        have h3 : x * x * x = 1 := by
          have := hx3
          rwa [pow_succ, pow_two] at this
        have h1 : x = (x⁻¹ * t * x) * t := by
          calc x = (x * x)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
            _ = x⁻¹ * x⁻¹ := mul_inv_rev x x
            _ = x⁻¹ * (t * x * t) := by rw [h2]
            _ = (x⁻¹ * t * x) * t := by group
        rw [h1]
        exact J1.mul_mem (Subgroup.subset_closure hconj) htJ1
      have hJ1st : J1 ≤ stabSub (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) :=
        le_stabSub_of_invariant fun g hg m hm => hJW g (hJ1J hg) m hm
      have hJ1faith : J1 ⊓ centSub (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => MulEquiv.ext fun v => ?_
        have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
          rw [hsup]; trivial
        obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
        show g (c * m) = c * m
        rw [map_mul, hJ1C g hg.1 c hc, hg.2 m hm]
      have hcard6 : Nat.card J1 = 6 := by
        have h1 := card_autSub_mul hJ1st
        rw [hJ1faith, Subgroup.card_bot, mul_one] at h1
        have hle : Nat.card (autSub J1 (commSub (⊤ : Subgroup V) (Subgroup.zpowers x))) ≤ 6 :=
          (Subgroup.card_le_card_group _).trans (card_mulAut_of_card_four hV hM4).le
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
        have hot : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) ht1
        have h3 : 3 ∣ Nat.card J1 := by
          have := orderOf_dvd_natCard (⟨x, hxJ1⟩ : ↥J1)
          rwa [Subgroup.orderOf_mk, hox] at this
        have h2 : 2 ∣ Nat.card J1 := by
          have := orderOf_dvd_natCard (⟨t, htJ1⟩ : ↥J1)
          rwa [Subgroup.orderOf_mk, hot] at this
        have hpos : 0 < Nat.card J1 := Nat.card_pos
        omega
      have hVJ1 : commSub (⊤ : Subgroup V) J1 = commSub ⊤ (Subgroup.zpowers x) := by
        refine le_antisymm ?_ (commSub_mono le_rfl (Subgroup.zpowers_le.2 hxJ1))
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, hg, v, -, rfl⟩
        have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
          rw [hsup]; trivial
        obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
        have h1 : g (c * m) * (c * m)⁻¹ = g m * m⁻¹ := by
          rw [map_mul, hJ1C g hg c hc, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
        rw [SetLike.mem_coe, h1]
        exact Subgroup.mul_mem _ (hJW g (hJ1J hg) m hm) (Subgroup.inv_mem _ hm)
      have hinv1 : ∀ g ∈ J1, ∀ m ∈ commSub (⊤ : Subgroup V) J1, g m ∈ commSub (⊤ : Subgroup V) J1 := by
        rw [hVJ1]
        exact fun g hg m hm => hJW g (hJ1J hg) m hm
      have hautJ1 : autSub J1 (commSub (⊤ : Subgroup V) J1) = ⊤ := by
        rw [hVJ1]
        apply Subgroup.eq_top_of_card_eq
        have h1 := card_autSub_mul hJ1st
        rw [hJ1faith, Subgroup.card_bot, mul_one] at h1
        rw [h1, hcard6, card_mulAut_of_card_four hV hM4]
      have hcomm : ∀ a ∈ J1, ∀ b ∈ J0, a * b = b * a := by
        intro a ha b hb
        refine MulEquiv.ext fun v => ?_
        have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
          rw [hsup]; trivial
        obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
        have hbc := hJC b (hJ0J hb) c hc
        have ham := hJW a (hJ1J ha) m hm
        show a (b (c * m)) = b (a (c * m))
        simp only [map_mul, hJ0W b hb m hm, hJ1C a ha c hc, hJ1C a ha (b c) hbc,
          hJ0W b hb (a m) ham]
      have hO0 : ∀ Q : Subgroup (MulAut V), Q ≤ J0 → (Q.subgroupOf J0).Normal →
          IsPGroup 2 Q → Q = ⊥ := by
        intro Q hQ hQn hQ2
        refine hO Q (hQ.trans hJ0J) ?_ hQ2
        rw [Subgroup.normal_subgroupOf_iff (hQ.trans hJ0J)]
        intro h k hh hk
        have hk' : k ∈ J1 ⊔ J0 := by rw [← hJeq]; exact hk
        exact (Subgroup.mem_normalizer_iff.1
          (sup_le_normalizer_of_commute hcomm hQ hQn hk') h).1 hh
      have hcl0 : Subgroup.closure (transvectionsIn J0) = J0 := by
        refine le_antisymm ((Subgroup.closure_le _).2 fun s hs => hs.1) ?_
        refine Subgroup.closure_mono ?_
        intro s hs
        exact ⟨Subgroup.subset_closure hs, hs.1.2⟩
      have hcl1 : Subgroup.closure (transvectionsIn J1) = J1 := by
        refine le_antisymm ((Subgroup.closure_le _).2 fun s hs => hs.1) ?_
        refine Subgroup.closure_mono ?_
        intro s hs
        exact ⟨Subgroup.subset_closure hs, hs.1.2⟩
      have hxJ0 : x ∉ J0 := by
        intro hx0
        have h0 : commSub (⊤ : Subgroup V) (Subgroup.zpowers x) = ⊥ :=
          (Subgroup.eq_bot_iff_forall _).2 fun m hm => hfpf m hm (hJ0W x hx0 m hm)
        rw [h0, Subgroup.card_bot] at hM4
        omega
      have hlt : Nat.card J0 < Nat.card J := by
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hJ0J) fun h => hxJ0 ?_
        have := Subgroup.eq_of_le_of_card_ge hJ0J h.ge
        rw [this]
        exact hxJ
      obtain ⟨𝓗₀, hU0, hH0, hP0, hT0'⟩ :=
        ih J0 (by omega) (solvable_of_le hJ0J hsolv) hO0 hcl0
      have hle0 : ∀ K ∈ 𝓗₀, K ≤ J0 := fun K hK => by
        rw [← hU0]
        exact le_iSup₂ (f := fun (H : Subgroup (MulAut V)) (_ : H ∈ 𝓗₀) => H) K hK
      have hcommJ0 : commSub (⊤ : Subgroup V) J0 ≤ fixV (Subgroup.zpowers x) := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, hg, v, -, rfl⟩
        have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
          rw [hsup]; trivial
        obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
        have h1 : g (c * m) * (c * m)⁻¹ = g c * c⁻¹ := by
          rw [map_mul, hJ0W g hg m hm, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
        rw [SetLike.mem_coe, h1]
        exact Subgroup.mul_mem _ (hJC g (hJ0J hg) c hc) (Subgroup.inv_mem _ hc)
      refine ⟨insert J1 𝓗₀, ?_, ?_, ?_, ?_⟩
      · rw [Finset.iSup_insert, hU0, ← hJeq]
      · intro H hH
        rcases Finset.mem_insert.1 hH with rfl | hH
        · refine ⟨hcard6, by rw [hVJ1]; exact hM4, hcl1, hinv1, hautJ1, fixV (Subgroup.zpowers x),
            ?_, ?_, hJ1C⟩
          · rw [hVJ1]; exact hinf
          · rw [hVJ1]; exact hsup
        · exact hH0 H hH
      · intro H hH H' hH' hne
        rcases Finset.mem_insert.1 hH with rfl | hH
        · rcases Finset.mem_insert.1 hH' with rfl | hH'
          · exact absurd rfl hne
          · refine ⟨fun a ha b hb => hcomm a ha b (hle0 H' hH' hb), fun a ha u hu => ?_⟩
            exact hJ1C a ha u (hcommJ0 (commSub_mono le_rfl (hle0 H' hH') hu))
        · rcases Finset.mem_insert.1 hH' with rfl | hH'
          · refine ⟨fun a ha b hb => (hcomm b hb a (hle0 H hH ha)).symm, fun a ha u hu => ?_⟩
            rw [hVJ1] at hu
            exact hJ0W a (hle0 H hH ha) u hu
          · exact hP0 H hH H' hH' hne
      · intro s hs
        rcases hTsplit s hs with h | h
        · exact ⟨J1, Finset.mem_insert_self _ _, Subgroup.subset_closure h⟩
        · obtain ⟨H, hH, hsH⟩ := hT0' s ⟨Subgroup.subset_closure h, h.1.2⟩
          exact ⟨H, Finset.mem_insert_of_mem hH, hsH⟩

end B1

structure IsTransvectionBlocks (J : Subgroup (MulAut V)) (𝓗 : Finset (Subgroup (MulAut V))) :
    Prop where
  iSup_eq : (⨆ H ∈ 𝓗, H) = J
  card_eq : ∀ H ∈ 𝓗, Nat.card H = 6
  card_comm : ∀ H ∈ 𝓗, Nat.card (commSub (⊤ : Subgroup V) H) = 4
  closure_eq : ∀ H ∈ 𝓗, Subgroup.closure (transvectionsIn H) = H
  stab : ∀ H ∈ 𝓗, ∀ h ∈ H, ∀ m ∈ commSub (⊤ : Subgroup V) H, h m ∈ commSub (⊤ : Subgroup V) H
  autSub_eq_top : ∀ H ∈ 𝓗, autSub H (commSub (⊤ : Subgroup V) H) = ⊤
  exists_compl : ∀ H ∈ 𝓗, ∃ C : Subgroup V, C ⊓ commSub ⊤ H = ⊥ ∧ C ⊔ commSub ⊤ H = ⊤ ∧
    ∀ h ∈ H, ∀ c ∈ C, h c = c
  comm : ∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a
  triv : ∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → ∀ a ∈ H, ∀ u ∈ commSub (⊤ : Subgroup V) H', a u = u
  cover : ∀ t ∈ transvectionsIn J, ∃ H ∈ 𝓗, t ∈ H

theorem transvection_structure [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {J : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥J)
    (hO : ∀ Q : Subgroup (MulAut V), Q ≤ J → (Q.subgroupOf J).Normal → IsPGroup 2 Q → Q = ⊥)
    (hJ : Subgroup.closure (transvectionsIn J) = J) :
    ∃ 𝓗 : Finset (Subgroup (MulAut V)), IsTransvectionBlocks J 𝓗 := by
  obtain ⟨𝓗, h1, h2, h3, h4⟩ := B1.transvection_structure_aux hV (Nat.card J) J le_rfl hsolv hO hJ
  exact ⟨𝓗, ⟨h1, fun H hH => (h2 H hH).1, fun H hH => (h2 H hH).2.1,
    fun H hH => (h2 H hH).2.2.1, fun H hH => (h2 H hH).2.2.2.1,
    fun H hH => (h2 H hH).2.2.2.2.1, fun H hH => (h2 H hH).2.2.2.2.2,
    fun H hH H' hH' hne => (h3 H hH H' hH' hne).1,
    fun H hH H' hH' hne => (h3 H hH H' hH' hne).2, h4⟩⟩

end CFSG.Quasithin
