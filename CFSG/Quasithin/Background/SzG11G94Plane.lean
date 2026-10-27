module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Pre
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzG11G94

open CFSG.Quasithin.G11 CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def pl (w : GLV V) (v : V) : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {v, w v}

section Lines

variable {w : GLV V} (hw : ∀ v, w (w v) + w v + v = 0)

omit hw in
theorem mem_pl {v x : V} : x ∈ pl w v ↔ x = 0 ∨ x = v ∨ x = w v ∨ x = v + w v := by
  unfold pl
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

include hw in
theorem w_w (v : V) : w (w v) = w v + v := by
  have := hw v
  calc w (w v) = -(w v + v) := eq_neg_of_add_eq_zero_left (by rwa [add_assoc] at this)
    _ = w v + v := zmod2_neg _

include hw in
theorem eq_zero_of_w_fix {v : V} (h : w v = v) : v = 0 := by
  have h1 := hw v
  have h2 : w (w v) = v := by rw [h, h]
  rw [h2, h] at h1
  have h3 : v + v = 0 := zmod2_add_self v
  rw [h3, zero_add] at h1
  exact h1

theorem w_ne_zero {v : V} (hv : v ≠ 0) : w v ≠ 0 := by
  intro h
  apply hv
  exact w.injective (by simpa using h)

omit hw in
theorem pl_carrier {v : V} : (pl w v : Set V) = {0, v, w v, v + w v} := by
  ext x
  simp only [SetLike.mem_coe, mem_pl, Set.mem_insert_iff, Set.mem_singleton_iff]

include hw in
theorem ncard_pl {v : V} (hv : v ≠ 0) : (pl w v : Set V).ncard = 4 := by
  rw [pl_carrier]
  have h1 : w v ≠ v := fun h => hv (eq_zero_of_w_fix hw h)
  have h2 : w v ≠ 0 := w_ne_zero hv
  have h3 : v + w v ≠ 0 := by
    intro h
    apply h1
    have : w v = -v := eq_neg_of_add_eq_zero_right h
    rw [this, zmod2_neg]
  have h4 : v + w v ≠ v := by
    intro h
    apply h2
    have := congrArg (fun x => x - v) h
    simpa using this
  have h5 : v + w v ≠ w v := by
    intro h
    apply hv
    have := congrArg (fun x => x - w v) h
    simpa using this
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
  · exact h5.symm
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1.symm, h4.symm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hv.symm, h2.symm, h3.symm⟩

include hw in
theorem w_mem_pl {v x : V} (hx : x ∈ pl w v) : w x ∈ pl w v := by
  rw [mem_pl] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · left
    simp
  · right
    right
    left
    rfl
  · right
    right
    right
    rw [w_w hw, add_comm]
  · right
    left
    rw [map_add, w_w hw, ← add_assoc, zmod2_add_self, zero_add]

include hw in
theorem pl_eq_of_mem {v z : V} (hv : v ≠ 0) (hz : z ∈ pl w v) (hz0 : z ≠ 0) :
    pl w z = pl w v := by
  have hle : pl w z ≤ pl w v := by
    unfold pl
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hz
    · exact w_mem_pl hw hz
  have hcard : (pl w v : Set V).ncard ≤ (pl w z : Set V).ncard := by
    rw [ncard_pl hw hv, ncard_pl hw hz0]
  exact SetLike.coe_injective (Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.2 hle) hcard
    (Set.finite_of_ncard_pos (by rw [ncard_pl hw hv]; norm_num)))

include hw in
theorem pl_inf_eq_bot {v u : V} (hv : v ≠ 0) (hu : u ∉ pl w v) : pl w v ⊓ pl w u = ⊥ := by
  have hu0 : u ≠ 0 := fun h => hu (by rw [h]; exact Submodule.zero_mem _)
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  by_contra hz0
  have h1 := pl_eq_of_mem hw hv hz.1 hz0
  have h2 := pl_eq_of_mem hw hu0 hz.2 hz0
  apply hu
  rw [← h1, h2]
  exact Submodule.subset_span (by simp)

variable [Finite V]

include hw in
theorem finrank_pl {v : V} (hv : v ≠ 0) : Module.finrank (ZMod 2) (pl w v) = 2 := by
  have : Module.Finite (ZMod 2) (pl w v) := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := pl w v)
  rw [Nat.card_zmod] at h1
  have h2 : Nat.card (pl w v) = 4 := by
    rw [show Nat.card (pl w v) = (pl w v : Set V).ncard from (Nat.card_coe_set_eq _)]
    exact ncard_pl hw hv
  rw [h2] at h1
  exact (Nat.pow_right_injective (le_refl 2) (by simpa using h1.symm : 2 ^ _ = 2 ^ 2))

include hw in
theorem sup_pl_eq_top (hV : Module.finrank (ZMod 2) V = 4) {v u : V} (hv : v ≠ 0)
    (hu : u ∉ pl w v) : pl w v ⊔ pl w u = ⊤ := by
  have hu0 : u ≠ 0 := fun h => hu (by rw [h]; exact Submodule.zero_mem _)
  have : Module.Finite (ZMod 2) (pl w v) := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) (pl w u) := Module.Finite.of_finite
  have h := Submodule.finrank_sup_add_finrank_inf_eq (pl w v) (pl w u)
  rw [pl_inf_eq_bot hw hv hu, finrank_bot, finrank_pl hw hv, finrank_pl hw hu0] at h
  apply Submodule.eq_top_of_finrank_eq
  rw [hV]
  omega

end Lines

section Centralizer

variable [Finite V] {w : GLV V} (hw : ∀ v, w (w v) + w v + v = 0)
  (hV : Module.finrank (ZMod 2) V = 4)

include hw hV in
theorem card_frames : Nat.card {p : V × V // p.1 ≠ 0 ∧ p.2 ∉ pl w p.1} = 180 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hV16 : Nat.card V = 16 := card_eq_sixteen hV
  have e : {p : V × V // p.1 ≠ 0 ∧ p.2 ∉ pl w p.1} ≃
      Σ v : {v : V // v ≠ 0}, {u : V // u ∉ pl w v} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun s => rfl }
  have hfib : ∀ v : {v : V // v ≠ 0}, Nat.card {u : V // u ∉ pl w v} = 12 := by
    intro v
    have h1 : Nat.card {u : V // u ∉ pl w v} = ((pl w v : Set V)ᶜ).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [h1, Set.ncard_compl, ncard_pl hw v.2, hV16]
  have hnz : Nat.card {v : V // v ≠ 0} = 15 := by
    have h1 : Nat.card {v : V // v ≠ 0} = (({0} : Set V)ᶜ).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [h1, Set.ncard_compl, Set.ncard_singleton, hV16]
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hnz]
  rfl

omit [Finite V] hV in
theorem mem_pl_of_apply_mem {g : GLV V} (hg : ∀ x, g (w x) = w (g x)) {v u : V}
    (h : g u ∈ pl w (g v)) : u ∈ pl w v := by
  rw [mem_pl] at h ⊢
  rcases h with h | h | h | h
  · left
    exact g.injective (by simpa using h)
  · right
    left
    exact g.injective h
  · right
    right
    left
    exact g.injective (by rw [hg]; exact h)
  · right
    right
    right
    exact g.injective (by rw [map_add, hg]; exact h)

omit [Finite V] hV in
theorem agree_on_pl {g g' : GLV V} (hg : ∀ x, g (w x) = w (g x))
    (hg' : ∀ x, g' (w x) = w (g' x)) {v : V} (hgv : g v = g' v) :
    ∀ x ∈ pl w v, g x = g' x := by
  intro x hx
  rw [mem_pl] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · exact hgv
  · rw [hg, hg', hgv]
  · rw [map_add, map_add, hg, hg', hgv]

include hw hV in
theorem card_centralizer_le : Nat.card (Subgroup.centralizer ({w} : Set (GLV V))) ≤ 180 := by
  classical
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hV]; norm_num)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hex : ∃ u₀ : V, u₀ ∉ pl w v₀ := by
    by_contra h
    push Not at h
    have hle : (Set.univ : Set V) ⊆ (pl w v₀ : Set V) := fun x _ => h x
    have h1 := Set.ncard_le_ncard hle
      (Set.finite_of_ncard_pos (by rw [ncard_pl hw hv₀]; norm_num))
    rw [Set.ncard_univ, ncard_pl hw hv₀, card_eq_sixteen hV] at h1
    omega
  obtain ⟨u₀, hu₀⟩ := hex
  have hmem : ∀ g : Subgroup.centralizer ({w} : Set (GLV V)), ∀ x,
      (g : GLV V) (w x) = w ((g : GLV V) x) := by
    intro g x
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact congrArg (fun f : GLV V => f x) this
  let Φ : Subgroup.centralizer ({w} : Set (GLV V)) →
      {p : V × V // p.1 ≠ 0 ∧ p.2 ∉ pl w p.1} := fun g =>
    ⟨((g : GLV V) v₀, (g : GLV V) u₀), by
      refine ⟨fun h => hv₀ ?_, fun h => hu₀ ?_⟩
      · exact (g : GLV V).injective (by simpa using h)
      · exact mem_pl_of_apply_mem (hmem g) h⟩
  have hinj : Function.Injective Φ := by
    intro g g' hgg
    have h1 : (g : GLV V) v₀ = (g' : GLV V) v₀ := congrArg (fun p => p.1.1) hgg
    have h2 : (g : GLV V) u₀ = (g' : GLV V) u₀ := congrArg (fun p => p.1.2) hgg
    apply Subtype.ext
    refine LinearEquiv.ext fun x => ?_
    have hx : x ∈ pl w v₀ ⊔ pl w u₀ := by rw [sup_pl_eq_top hw hV hv₀ hu₀]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, agree_on_pl (hmem g) (hmem g') h1 a ha,
      agree_on_pl (hmem g) (hmem g') h2 b hb]
  calc Nat.card (Subgroup.centralizer ({w} : Set (GLV V)))
      ≤ Nat.card {p : V × V // p.1 ≠ 0 ∧ p.2 ∉ pl w p.1} := Nat.card_le_card_of_injective Φ hinj
    _ = 180 := card_frames hw hV

end Centralizer

end CFSG.Quasithin.SzG11G94
