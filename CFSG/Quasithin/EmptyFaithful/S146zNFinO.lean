module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinN
public import CFSG.Quasithin.EmptyFaithful.S146zNFinM
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

theorem card_A6 : Nat.card A6 = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

instance : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)

theorem no_index_small (H : Subgroup A6) (h1 : H.index ≠ 1) (h5 : H.index ≤ 5) : False := by
  classical
  let f : A6 →* Perm (A6 ⧸ H) := MulAction.toPermHom A6 (A6 ⧸ H)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hk | hk
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
    have hfin : Finite (A6 ⧸ H) := by
      have : H.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
      infer_instance
    have hle := Nat.card_le_card_of_injective f hinj
    rw [card_A6, Nat.card_eq_fintype_card (α := Perm (A6 ⧸ H))] at hle
    rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, ← Subgroup.index] at hle
    have h120 : H.index.factorial ≤ Nat.factorial 5 := Nat.factorial_le h5
    have : Nat.factorial 5 = 120 := by decide
    omega
  · apply h1
    have hH : H = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ f.ker := by rw [hk]; exact Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hg
      have := congrArg (fun π : Perm (A6 ⧸ H) => π ((1 : A6) : A6 ⧸ H)) hg
      simp only [f, MulAction.toPermHom_apply, Perm.coe_one, id_eq] at this
      have h2 : ((g : A6) : A6 ⧸ H) = ((1 : A6) : A6 ⧸ H) := by
        simpa using this
      exact QuotientGroup.eq.mp h2 |> fun h => by simpa using h
    rw [hH, Subgroup.index_top]


section Orbit

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def orb (ρ : A6 →* MulAut W) (u : W) : Set W := Set.range fun g : A6 => ρ g u

@[expose] def c5A6 : A6 := x0A6 * y0A6

theorem c5A6_ne_one : c5A6 ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  unfold c5A6 x0A6 y0A6 x0P y0P
  decide

theorem c5A6_pow : c5A6 ^ 5 = 1 := by
  apply Subtype.ext
  have := rel_x0y0.2.2.1
  simpa [c5A6, x0A6, y0A6, pow_succ, mul_assoc] using this

omit [Finite W] in
theorem Setup.orb_ne_one {ρ : A6 →* MulAut W} {u : W} (hu : u ≠ 1) {v : W} (hv : v ∈ orb ρ u) :
    v ≠ 1 := by
  obtain ⟨g, rfl⟩ := hv
  intro h
  apply hu
  have h' : ρ g u = 1 := h
  have : ρ g u = ρ g 1 := by rw [h', map_one]
  exact (ρ g).injective this

theorem Setup.orb_ncard_ge_ten {ρ : A6 →* MulAut W} (h : Setup ρ) {u : W} (hu : u ≠ 1) :
    10 ≤ (orb ρ u).ncard := by
  classical
  let _ : MulAction A6 W := MulAction.compHom W ρ
  have hO : orb ρ u = MulAction.orbit A6 u := rfl
  have : Fintype W := Fintype.ofFinite W
  have hfc : fc ρ c5A6 = 1 := h.fc_five c5A6_ne_one c5A6_pow
  have hbot : fixSub (ρ c5A6) = ⊥ := Subgroup.eq_bot_of_card_eq _ hfc
  have h5 : 5 ∣ (orb ρ u).ncard := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let π : Perm W := (ρ c5A6).toEquiv
    have hπ : π ^ 5 = 1 := by
      ext x
      have h5' : ρ c5A6 ^ 5 = 1 := by rw [← map_pow, c5A6_pow, map_one]
      have := congrArg (fun f : MulAut W => f x) h5'
      simpa [π, pow_succ, Perm.mul_apply] using this
    have hP : ∀ x : W, (fun w : W => w ∈ orb ρ u) (π x) ↔ (fun w : W => w ∈ orb ρ u) x := by
      intro x
      constructor
      · rintro ⟨g, hg⟩
        have hg' : ρ g u = π x := hg
        refine ⟨c5A6⁻¹ * g, ?_⟩
        show ρ (c5A6⁻¹ * g) u = x
        rw [map_mul, MulAut.mul_apply, hg', map_inv]
        exact MulAut.inv_apply_self W (ρ c5A6) x
      · rintro ⟨g, hg⟩
        have hg' : ρ g u = x := hg
        exact ⟨c5A6 * g, by simp [map_mul, hg', π]⟩
    have h1 := card_modEq_perm_inv π 5 hπ (fun w : W => w ∈ orb ρ u) hP
    have h2 : Fintype.card {a : W // a ∈ orb ρ u ∧ π a = a} = 0 := by
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨a, ha, hfix⟩ => ?_⟩
      have : a ∈ fixSub (ρ c5A6) := hfix
      rw [hbot] at this
      exact Setup.orb_ne_one hu ha (Subgroup.mem_bot.mp this)
    rw [h2] at h1
    have h3 : Fintype.card {a : W // a ∈ orb ρ u} = (orb ρ u).ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [h3] at h1
    exact (Nat.modEq_zero_iff_dvd.mp h1)
  have h15 : (orb ρ u).ncard ≤ 15 := by
    have hsub : orb ρ u ⊆ ↑(Finset.univ.erase (1 : W)) := by
      intro v hv
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
        true_and]
      exact Setup.orb_ne_one hu hv
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)] at this
    have hc : (Finset.univ : Finset W).card = 16 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card]
    omega
  have hpos : 0 < (orb ρ u).ncard := by
    apply Set.ncard_pos (Set.toFinite _) |>.mpr
    exact ⟨u, 1, by simp⟩
  have hne5 : (orb ρ u).ncard ≠ 5 := by
    intro h5'
    have hidx := MulAction.index_stabilizer A6 u
    rw [← hO, h5'] at hidx
    exact no_index_small (MulAction.stabilizer A6 u) (by rw [hidx]; omega) (by rw [hidx])
  omega

end Orbit

end CFSG.Quasithin.A6Fin
