module

public import CFSG.Quasithin.H13.U3S134Co

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem fix_c012_of_fixDA : ∀ x : G6.PermMod 6,
    G6.permAct 6 (swap 0 1 * swap 2 3) x = x → G6.permAct 6 (swap 0 2 * swap 1 3) x = x →
    G6.permAct 6 (swap 0 1 * swap 4 5) x = x → G6.permAct 6 (swap 0 1 * swap 1 2) x = x := by
  decide +kernel

theorem act4f_c012_e0123 : act4f (swap 0 1 * swap 1 2) e0123 = e0123 := by decide +kernel

theorem exists_moved_core : ∃ x : G6.PermMod 6, x ∈ G6.coreMod 6 ∧
    G6.permAct 6 (swap 0 1 * swap 1 2) x ≠ x :=
  ⟨Multiplicative.ofAdd ![1, 0, 0, 1, 0, 0], by decide, by decide⟩

theorem exists_moved_W4 : ∃ x : G6.PermMod 6, InW4 x ∧
    act4f (swap 0 1 * swap 1 2) x ≠ x :=
  ⟨Multiplicative.ofAdd ![1, 0, 0, 1, 0, 0], by decide, by decide⟩

theorem c012_props : swap (0 : Fin 6) 1 * swap 1 2 ∈ alternatingGroup (Fin 6) ∧
    (swap (0 : Fin 6) 1 * swap 1 2) ^ 3 = 1 ∧ swap (0 : Fin 6) 1 * swap 1 2 ≠ 1 :=
  ⟨Perm.mem_alternatingGroup.2 (by decide), by decide, by decide⟩

theorem da_props : (InD6 (swap (0 : Fin 6) 1 * swap 2 3) ∧
      swap (0 : Fin 6) 1 * swap 2 3 ∈ alternatingGroup (Fin 6)) ∧
    (InD6 (swap (0 : Fin 6) 2 * swap 1 3) ∧
      swap (0 : Fin 6) 2 * swap 1 3 ∈ alternatingGroup (Fin 6)) ∧
    (InD6 (swap (0 : Fin 6) 1 * swap 4 5) ∧
      swap (0 : Fin 6) 1 * swap 4 5 ∈ alternatingGroup (Fin 6)) :=
  ⟨⟨by decide, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨by decide, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨by decide, Perm.mem_alternatingGroup.2 (by decide)⟩⟩

theorem exists_odd_part {N : Subgroup G} {X : Type*} [Group X] (ρ : ↥N →* X) (g : ↥N)
    (h3 : ρ g ^ 3 = 1) :
    ∃ y : ↥N, (∃ m : ℕ, Odd m ∧ (y : G) ^ m = 1) ∧ ρ y = ρ g ∧
      ∃ k : ℕ, (y : G) = (g : G) ^ k := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ 4 ^ a, ⟨m, hm, ?_⟩, ?_, 4 ^ a, by simp⟩
  · have h1 : (g ^ 4 ^ a) ^ m = (g ^ (2 ^ a * m)) ^ 2 ^ a := by
      rw [← pow_mul, ← pow_mul, show (4 : ℕ) ^ a = 2 ^ a * 2 ^ a by
        rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]]
      ring_nf
    have h2 : (g ^ 4 ^ a) ^ m = 1 := by rw [h1, ← hn, pow_orderOf_eq_one, one_pow]
    simpa using congrArg Subtype.val h2
  · rw [map_pow]
    obtain ⟨k, hk⟩ : ∃ k, 4 ^ a = 3 * k + 1 := ⟨4 ^ a / 3, by
      have := Nat.div_add_mod (4 ^ a) 3
      rw [U3.four_pow_mod_three] at this
      omega⟩
    rw [hk, pow_succ, pow_mul, h3, one_pow, one_mul]

theorem exists_three_of_a5Frame {T K W : Subgroup G} (F : A5.Frame T K W) :
    ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
  obtain ⟨g, hgK, hg⟩ := (F.image_L A5Model.c3p).2 A5.c3p_sign
  obtain ⟨y, hodd, hρy, k, hyk⟩ := exists_odd_part F.ρ g (by rw [hg]; exact A5.c3p_cube)
  rw [hg] at hρy
  refine ⟨(y : G), by rw [hyk]; exact pow_mem hgK k, hodd, ?_, ?_, ?_⟩
  · intro hyC
    have h1 := A5.Frame.rho_eq_one_of_mem F y hyC
    rw [hρy] at h1
    exact absurd h1 (by decide)
  · have h3 : F.ρ (y ^ 3) = 1 := by rw [map_pow, hρy, A5.c3p_cube]
    simpa using A5.Frame.mem_centralizer_of_rho F (y ^ 3) h3
  · intro w hwW hwT
    have hfix : ∀ σ : Perm (Fin 5), A5.InK4 σ →
        A5Model.pact σ (F.ψ ⟨w, hwW⟩) = F.ψ ⟨w, hwW⟩ := by
      intro σ hσ
      obtain ⟨t, htT, rfl⟩ := F.K4_T σ hσ
      rw [← F.equiv t ⟨w, hwW⟩]
      congr 1
      apply Subtype.ext
      rw [A5.conjAct_val]
      have := mem_centralizer_iff.mp hwT (t : G) htT
      calc (t : G) * w * (t : G)⁻¹ = w * t * (t : G)⁻¹ := by rw [this]
        _ = w := by group
    have hy : A5Model.pact (F.ρ y) (F.ψ ⟨w, hwW⟩) = F.ψ ⟨w, hwW⟩ := by
      rw [hρy]
      rcases A5.fixed_K4 _ hfix with h1 | h4
      · rw [h1, map_one]
      · rw [h4]
        exact A5Model.pact_W4 A5.c3p_four
    rw [← F.equiv y ⟨w, hwW⟩] at hy
    have h2 := congrArg Subtype.val (F.ψ.injective hy)
    rw [A5.conjAct_val] at h2
    calc (y : G) * w = (y : G) * w * (y : G)⁻¹ * y := by group
      _ = w * y := by rw [h2]

theorem exists_three_of_frame4 {T K W : Subgroup G} (F : Frame4 T K W) :
    ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
  obtain ⟨hcA, hc3, hc1⟩ := c012_props
  obtain ⟨g, hgK, hg⟩ := (F.image_L _).2 hcA
  obtain ⟨y, hodd, hρy, k, hyk⟩ := exists_odd_part F.ρ g (by rw [hg]; exact hc3)
  rw [hg] at hρy
  have hconj : ∀ (h : ↥(normalizer (W : Set G))) (w : G) (hwW : w ∈ W),
      ((F.ψ ⟨(h : G) * w * (h : G)⁻¹, (mem_normalizer_iff.mp h.2 w).mp hwW⟩ : ↥W4) : P6) =
        act4f (F.ρ h) (F.ψ ⟨w, hwW⟩ : P6) := by
    intro h w hwW
    have e : (conjAct W h ⟨w, hwW⟩ : ↥W) = ⟨(h : G) * w * (h : G)⁻¹,
        (mem_normalizer_iff.mp h.2 w).mp hwW⟩ := Subtype.ext (A5.conjAct_val W h ⟨w, hwW⟩)
    rw [← e]
    have := congrArg Subtype.val (F.equiv h ⟨w, hwW⟩)
    rw [act4_coe] at this
    exact this
  refine ⟨(y : G), by rw [hyk]; exact pow_mem hgK k, hodd, ?_, ?_, ?_⟩
  · intro hyC
    obtain ⟨x, hxW, hx⟩ := exists_moved_W4
    obtain ⟨v, hv⟩ := F.ψ.surjective ⟨x, hxW⟩
    have h1 := hconj y v v.2
    have hc : (y : G) * v * (y : G)⁻¹ = v := by
      rw [← mem_centralizer_iff.mp hyC v v.2, mul_inv_cancel_right]
    simp only [hc, Subtype.coe_eta, hv, hρy] at h1
    exact hx h1.symm
  · have h3 : F.ρ (y ^ 3) = 1 := by rw [map_pow, hρy, hc3]
    rw [mem_centralizer_iff]
    intro w hwW
    have h1 := hconj (y ^ 3) w hwW
    rw [h3, show act4f 1 (F.ψ ⟨w, hwW⟩ : P6) = F.ψ ⟨w, hwW⟩ from
      act4f_one _ (F.ψ ⟨w, hwW⟩).2] at h1
    have h2 : ((y ^ 3 : ↥(normalizer (W : Set G))) : G) * w *
        ((y ^ 3 : ↥(normalizer (W : Set G))) : G)⁻¹ = w :=
      congrArg Subtype.val (F.ψ.injective (Subtype.ext h1))
    simp only [Subgroup.coe_pow] at h2
    calc w * (y : G) ^ 3 = (y : G) ^ 3 * w * ((y : G) ^ 3)⁻¹ * (y : G) ^ 3 := by rw [h2]
      _ = (y : G) ^ 3 * w := by group
  · intro w hwW hwT
    have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
        act4f σ (F.ψ ⟨w, hwW⟩ : P6) = F.ψ ⟨w, hwW⟩ := by
      intro σ hσD hσA
      obtain ⟨t, htT, rfl⟩ := F.DA_T σ hσD hσA
      rw [← hconj t w hwW]
      congr 2
      apply Subtype.ext
      show (t : G) * w * (t : G)⁻¹ = w
      rw [mem_centralizer_iff.mp hwT (t : G) htT, mul_inv_cancel_right]
    obtain ⟨⟨h1D, h1A⟩, ⟨h2D, h2A⟩, ⟨h3D, h3A⟩⟩ := da_props
    have hcase := fixedW4_cases _ (F.ψ ⟨w, hwW⟩).2 (hfix _ h1D h1A) (hfix _ h2D h2A)
      (hfix _ h3D h3A)
    have hy : act4f (F.ρ y) (F.ψ ⟨w, hwW⟩ : P6) = F.ψ ⟨w, hwW⟩ := by
      rw [hρy]
      rcases hcase with h1 | h4
      · rw [h1]
        decide
      · rw [h4]
        exact act4f_c012_e0123
    rw [← hconj y w hwW] at hy
    have h2 : (y : G) * w * (y : G)⁻¹ = w :=
      congrArg Subtype.val (F.ψ.injective (Subtype.ext hy))
    calc (y : G) * w = (y : G) * w * (y : G)⁻¹ * y := by group
      _ = w * y := by rw [h2]

theorem exists_three_of_frame5 {T K W : Subgroup G} (F : Frame5 T K W) :
    ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
  obtain ⟨hcA, hc3, hc1⟩ := c012_props
  obtain ⟨g, hgK, hg⟩ := (F.image_L _).2 hcA
  obtain ⟨y, hodd, hρy, k, hyk⟩ := exists_odd_part F.ρ g (by rw [hg]; exact hc3)
  rw [hg] at hρy
  have hconj : ∀ (h : ↥(normalizer (W : Set G))) (w : G) (hwW : w ∈ W),
      ((F.ψ ⟨(h : G) * w * (h : G)⁻¹, (mem_normalizer_iff.mp h.2 w).mp hwW⟩ :
          ↥(G6.coreMod 6)) : G6.PermMod 6) =
        G6.permAct 6 (F.ρ h) (F.ψ ⟨w, hwW⟩ : G6.PermMod 6) := by
    intro h w hwW
    have e : (conjAct W h ⟨w, hwW⟩ : ↥W) = ⟨(h : G) * w * (h : G)⁻¹,
        (mem_normalizer_iff.mp h.2 w).mp hwW⟩ := Subtype.ext (A5.conjAct_val W h ⟨w, hwW⟩)
    rw [← e]
    have := congrArg Subtype.val (F.equiv h ⟨w, hwW⟩)
    rw [G6.coreAct_coe] at this
    exact this
  refine ⟨(y : G), by rw [hyk]; exact pow_mem hgK k, hodd, ?_, ?_, ?_⟩
  · intro hyC
    obtain ⟨x, hxU, hx⟩ := exists_moved_core
    obtain ⟨v, hv⟩ := F.ψ.surjective ⟨x, hxU⟩
    have h1 := hconj y v v.2
    have hc : (y : G) * v * (y : G)⁻¹ = v := by
      rw [← mem_centralizer_iff.mp hyC v v.2, mul_inv_cancel_right]
    simp only [hc, Subtype.coe_eta, hv, hρy] at h1
    exact hx h1.symm
  · have h3 : F.ρ (y ^ 3) = 1 := by rw [map_pow, hρy, hc3]
    rw [mem_centralizer_iff]
    intro w hwW
    have h1 := hconj (y ^ 3) w hwW
    rw [h3, map_one, MulAut.one_apply] at h1
    have h2 : ((y ^ 3 : ↥(normalizer (W : Set G))) : G) * w *
        ((y ^ 3 : ↥(normalizer (W : Set G))) : G)⁻¹ = w :=
      congrArg Subtype.val (F.ψ.injective (Subtype.ext h1))
    simp only [Subgroup.coe_pow] at h2
    calc w * (y : G) ^ 3 = (y : G) ^ 3 * w * ((y : G) ^ 3)⁻¹ * (y : G) ^ 3 := by rw [h2]
      _ = (y : G) ^ 3 * w := by group
  · intro w hwW hwT
    have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
        G6.permAct 6 σ (F.ψ ⟨w, hwW⟩ : G6.PermMod 6) = F.ψ ⟨w, hwW⟩ := by
      intro σ hσD hσA
      obtain ⟨t, htT, rfl⟩ := F.DA_T σ hσD hσA
      rw [← hconj t w hwW]
      congr 2
      apply Subtype.ext
      show (t : G) * w * (t : G)⁻¹ = w
      rw [mem_centralizer_iff.mp hwT (t : G) htT, mul_inv_cancel_right]
    obtain ⟨⟨h1D, h1A⟩, ⟨h2D, h2A⟩, ⟨h3D, h3A⟩⟩ := da_props
    have hy : G6.permAct 6 (F.ρ y) (F.ψ ⟨w, hwW⟩ : G6.PermMod 6) = F.ψ ⟨w, hwW⟩ := by
      rw [hρy]
      exact fix_c012_of_fixDA _ (hfix _ h1D h1A) (hfix _ h2D h2A) (hfix _ h3D h3A)
    rw [← hconj y w hwW] at hy
    have h2 : (y : G) * w * (y : G)⁻¹ = w :=
      congrArg Subtype.val (F.ψ.injective (Subtype.ext hy))
    calc (y : G) * w = (y : G) * w * (y : G)⁻¹ * y := by group
      _ = w * y := by rw [h2]

theorem card_le_of_maps_to {α β : Type*} [Finite α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (t : Finset β) (ht : ∀ a, f a ∈ t) : Nat.card α ≤ t.card := by
  have h := Nat.card_le_card_of_injective (fun a => (⟨f a, ht a⟩ : ↥t))
    (fun a b hab => hf (congrArg Subtype.val hab))
  rwa [Nat.card_eq_fintype_card (α := ↥t), Fintype.card_coe] at h

theorem fixDA_cases : ∀ x : G6.PermMod 6,
    G6.permAct 6 (swap 0 1 * swap 2 3) x = x → G6.permAct 6 (swap 0 2 * swap 1 3) x = x →
    G6.permAct 6 (swap 0 1 * swap 4 5) x = x →
    x = 1 ∨ x = Multiplicative.ofAdd ![1, 1, 1, 1, 0, 0] ∨
      x = Multiplicative.ofAdd ![0, 0, 0, 0, 1, 1] ∨ x = Multiplicative.ofAdd ![1, 1, 1, 1, 1, 1] := by
  decide +kernel

theorem card_cT_le_of_frame4 {T K W : Subgroup G} (F : Frame4 T K W) :
    Nat.card ↥(W ⊓ centralizer (T : Set G)) ≤ 2 := by
  classical
  refine (card_le_of_maps_to (fun x : ↥(W ⊓ centralizer (T : Set G)) =>
    ((F.ψ ⟨x, (mem_inf.1 x.2).1⟩ : ↥W4) : P6)) (fun a b hab => Subtype.ext
      (congrArg (fun y : ↥W => (y : G)) (F.ψ.injective (Subtype.ext hab)))) {1, e0123}
      fun x => ?_).trans (Finset.card_le_two)
  obtain ⟨hxW, hxT⟩ := mem_inf.1 x.2
  have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      act4f σ (F.ψ ⟨x, hxW⟩ : P6) = F.ψ ⟨x, hxW⟩ := by
    intro σ hσD hσA
    obtain ⟨t, htT, rfl⟩ := F.DA_T σ hσD hσA
    have h1 := congrArg Subtype.val (F.equiv t ⟨x, hxW⟩)
    rw [act4_coe] at h1
    rw [show act4f (F.ρ t) (F.ψ ⟨x, hxW⟩ : P6) = nrm (G6.permAct 6 (F.ρ t) (F.ψ ⟨x, hxW⟩))
      from rfl, ← h1]
    congr 2
    apply Subtype.ext
    rw [A5.conjAct_val]
    show (t : G) * x * (t : G)⁻¹ = x
    rw [mem_centralizer_iff.mp hxT (t : G) htT, mul_inv_cancel_right]
  obtain ⟨⟨h1D, h1A⟩, ⟨h2D, h2A⟩, ⟨h3D, h3A⟩⟩ := da_props
  rcases fixedW4_cases _ (F.ψ ⟨x, hxW⟩).2 (hfix _ h1D h1A) (hfix _ h2D h2A) (hfix _ h3D h3A)
    with h | h <;> simp [h]

theorem card_cT_le_of_frame5 {T K W : Subgroup G} (F : Frame5 T K W) :
    Nat.card ↥(W ⊓ centralizer (T : Set G)) ≤ 4 := by
  classical
  refine (card_le_of_maps_to (fun x : ↥(W ⊓ centralizer (T : Set G)) =>
    ((F.ψ ⟨x, (mem_inf.1 x.2).1⟩ : ↥(G6.coreMod 6)) : G6.PermMod 6))
    (fun a b hab => Subtype.ext (congrArg (fun y : ↥W => (y : G))
      (F.ψ.injective (Subtype.ext hab))))
    {1, Multiplicative.ofAdd ![1, 1, 1, 1, 0, 0], Multiplicative.ofAdd ![0, 0, 0, 0, 1, 1],
      Multiplicative.ofAdd ![1, 1, 1, 1, 1, 1]} fun x => ?_).trans ?_
  · obtain ⟨hxW, hxT⟩ := mem_inf.1 x.2
    have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
        G6.permAct 6 σ (F.ψ ⟨x, hxW⟩ : G6.PermMod 6) = F.ψ ⟨x, hxW⟩ := by
      intro σ hσD hσA
      obtain ⟨t, htT, rfl⟩ := F.DA_T σ hσD hσA
      have h1 := congrArg Subtype.val (F.equiv t ⟨x, hxW⟩)
      rw [G6.coreAct_coe] at h1
      rw [← h1]
      congr 2
      apply Subtype.ext
      rw [A5.conjAct_val]
      show (t : G) * x * (t : G)⁻¹ = x
      rw [mem_centralizer_iff.mp hxT (t : G) htT, mul_inv_cancel_right]
    obtain ⟨⟨h1D, h1A⟩, ⟨h2D, h2A⟩, ⟨h3D, h3A⟩⟩ := da_props
    rcases fixDA_cases _ (hfix _ h1D h1A) (hfix _ h2D h2A) (hfix _ h3D h3A)
      with h | h | h | h <;> simp [h]
  · exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ (Finset.card_le_two))))

theorem l3_two_fixed : ∀ u v : L3.Vec, u ≠ 0 → v ≠ 0 → u ≠ v →
    (Finset.univ.filter fun g : L3.Γ => L3.act g u = u ∧ L3.act g v = v).card ≤ 4 := by
  decide +kernel

theorem l3_three_fix : ∀ p : L3.Vec, ∃ g : L3.Γ, g ^ 3 = 1 ∧ g ≠ 1 ∧ L3.act g p = p := by
  decide +kernel

@[expose] noncomputable def l3coord {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    (D : L3Data H ⊤ ⊥) (w : W) : L3.Vec :=
  Multiplicative.toAdd (D.β ⟨w, mem_top w⟩)

omit [Finite G] in
theorem l3coord_rho {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} (D : L3Data H ⊤ ⊥)
    (γ : L3.Γ) (w : W) : l3coord D (D.rho γ w) = L3.act γ (l3coord D w) := by
  have := D.β_rho γ w (mem_top w) (mem_top _)
  simp only [l3coord, this, toAdd_ofAdd]

omit [Finite G] in
theorem l3coord_injective {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    (D : L3Data H ⊤ ⊥) : Function.Injective (l3coord D) := by
  intro w₁ w₂ h
  have h1 : D.β ⟨w₁ * w₂⁻¹, mem_top _⟩ = 1 := by
    have e1 : (⟨w₁ * w₂⁻¹, mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨w₁, mem_top _⟩ * (⟨w₂, mem_top _⟩)⁻¹ := rfl
    rw [e1, map_mul, map_inv]
    have h2 : D.β ⟨w₁, mem_top _⟩ = D.β ⟨w₂, mem_top _⟩ := Multiplicative.toAdd.injective h
    rw [h2]
    exact mul_inv_cancel _
  have h3 := (D.ker_β _).1 h1
  rw [mem_bot] at h3
  exact mul_inv_eq_one.1 h3

theorem l32_coord_unique {T K W : Subgroup G} [IsMulCommutative ↥W]
    (hKW : K ≤ normalizer (W : Set G)) (hsyl : IsSylowTwoOf (T ⊓ K) K)
    (D : L3Data (autOn K W) ⊤ ⊥) (w₁ w₂ : ↥W) (hw₁ : (w₁ : G) ∈ centralizer (T : Set G))
    (hw₂ : (w₂ : G) ∈ centralizer (T : Set G)) (h₁ : l3coord D w₁ ≠ 0)
    (h₂ : l3coord D w₂ ≠ 0) : l3coord D w₁ = l3coord D w₂ := by
  classical
  by_contra hne
  set φ := A6.autOnHom hKW with hφ
  let e : L3.Γ ≃* ↥(autOn K W) := MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩
  have he : ∀ γ, (e γ : MulAut ↥W) = D.rho γ := fun γ => rfl
  set P₀ := ((T ⊓ K).subgroupOf K).map φ with hP₀
  have hcard : Nat.card ↥(autOn K W) = 168 := by
    rw [← Nat.card_congr e.toEquiv]
    exact HSType.card_SL_three_two
  have hidx : ¬ 2 ∣ P₀.index := fun h =>
    hsyl.2.2 (h.trans (Subgroup.index_map_dvd _ (A6.autOnHom_surjective hKW)))
  have h8 : 8 ∣ Nat.card ↥P₀ := by
    have h1 := P₀.index_mul_card
    rw [hcard] at h1
    have hcop : Nat.Coprime 8 P₀.index :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hidx)))
    exact hcop.dvd_of_dvd_mul_left ⟨21, by omega⟩
  have hpos : 0 < Nat.card ↥P₀ := Nat.card_pos
  have hfixW : ∀ a ∈ P₀, ∀ w : ↥W, (w : G) ∈ centralizer (T : Set G) →
      (a : MulAut ↥W) w = w := by
    rintro a ⟨k, hk, rfl⟩ w hw
    apply Subtype.ext
    rw [A6.autOnHom_apply, A5.conjAct_val]
    have hkT : (k : G) ∈ T := (mem_inf.1 (mem_subgroupOf.1 hk)).1
    show (k : G) * w * (k : G)⁻¹ = w
    rw [mem_centralizer_iff.mp hw (k : G) hkT, mul_inv_cancel_right]
  have hle := l3_two_fixed (l3coord D w₁) (l3coord D w₂) h₁ h₂ hne
  have hsub : ((P₀.map e.symm.toMonoidHom : Subgroup L3.Γ) : Set L3.Γ) ⊆
      ↑(Finset.univ.filter fun g : L3.Γ =>
        L3.act g (l3coord D w₁) = l3coord D w₁ ∧ L3.act g (l3coord D w₂) = l3coord D w₂) := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have hea : D.rho (e.symm a) = (a : MulAut ↥W) := by
      rw [← he, MulEquiv.apply_symm_apply]
    change L3.act (e.symm a) (l3coord D w₁) = l3coord D w₁ ∧
      L3.act (e.symm a) (l3coord D w₂) = l3coord D w₂
    constructor
    · rw [← l3coord_rho, hea, hfixW a ha w₁ hw₁]
    · rw [← l3coord_rho, hea, hfixW a ha w₂ hw₂]
  have hc1 : Nat.card ↥(P₀.map e.symm.toMonoidHom) = Nat.card ↥P₀ :=
    Subgroup.card_map_of_injective e.symm.injective
  have hc2 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at hc2
  have : Nat.card ↥P₀ ≤ 4 := by
    rw [← hc1]
    exact hc2.trans hle
  obtain ⟨c, hc⟩ := h8
  rcases c with _ | c
  · omega
  · omega

theorem card_cT_le_of_l32 {T K W : Subgroup G} [IsMulCommutative ↥W]
    (hKW : K ≤ normalizer (W : Set G))
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hsyl : IsSylowTwoOf (T ⊓ K) K) :
    Nat.card ↥(W ⊓ centralizer (T : Set G)) ≤ 2 := by
  classical
  obtain ⟨D⟩ := hnat.toL3Coord
  let f : ↥(W ⊓ centralizer (T : Set G)) → L3.Vec := fun x => l3coord D ⟨x, (mem_inf.1 x.2).1⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext
    (congrArg (fun y : ↥W => (y : G)) (l3coord_injective D hab))
  by_cases hex : ∃ x : ↥(W ⊓ centralizer (T : Set G)), f x ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hex
    refine (card_le_of_maps_to f hf {0, f x₀} fun x => ?_).trans Finset.card_le_two
    by_cases hx : f x = 0
    · simp [hx]
    · have := l32_coord_unique hKW hsyl D _ _ (mem_inf.1 x.2).2 (mem_inf.1 x₀.2).2 hx hx₀
      simp [f, this]
  · push Not at hex
    refine (card_le_of_maps_to f hf {0} fun x => by simp [hex x]).trans (by simp)

theorem exists_three_of_l32 {T K W : Subgroup G} [IsMulCommutative ↥W]
    (hKW : K ≤ normalizer (W : Set G))
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hsyl : IsSylowTwoOf (T ⊓ K) K) :
    ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
  classical
  obtain ⟨D⟩ := hnat.toL3Coord
  let e : L3.Γ ≃* ↥(autOn K W) := MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩
  have he : ∀ γ, (e γ : MulAut ↥W) = D.rho γ := fun γ => rfl
  have key : ∃ g : L3.Γ, g ^ 3 = 1 ∧ g ≠ 1 ∧ ∀ w : ↥W, (w : G) ∈ centralizer (T : Set G) →
      L3.act g (l3coord D w) = l3coord D w := by
    by_cases hex : ∃ w : ↥W, (w : G) ∈ centralizer (T : Set G) ∧ l3coord D w ≠ 0
    · obtain ⟨w₀, hw₀T, hw₀⟩ := hex
      obtain ⟨g, hg3, hg1, hgp⟩ := l3_three_fix (l3coord D w₀)
      refine ⟨g, hg3, hg1, fun w hw => ?_⟩
      by_cases hz : l3coord D w = 0
      · rw [hz]
        exact L3.act_zero g
      rw [l32_coord_unique hKW hsyl D w w₀ hw hw₀T hz hw₀]
      exact hgp
    · push Not at hex
      obtain ⟨g, hg3, hg1, -⟩ := l3_three_fix 0
      exact ⟨g, hg3, hg1, fun w hw => by rw [hex w hw]; exact L3.act_zero g⟩
  obtain ⟨g, hg3, hg1, hgfix⟩ := key
  obtain ⟨k, hk⟩ := A6.autOnHom_surjective hKW (e g)
  set k' : ↥(normalizer (W : Set G)) := ⟨k, hKW k.2⟩ with hk'
  have hk'ρ : conjAct W k' = (e g : MulAut ↥W) := by
    rw [← hk, A6.autOnHom_apply]
  obtain ⟨y, hodd, hρy, j, hyj⟩ := exists_odd_part (conjAct W) k' (by
    rw [hk'ρ, ← Subgroup.coe_pow, ← map_pow, hg3, map_one, Subgroup.coe_one])
  rw [hk'ρ] at hρy
  refine ⟨(y : G), by rw [hyj]; exact pow_mem k.2 j, hodd, ?_, ?_, ?_⟩
  · intro hyC
    apply hg1
    apply e.injective
    apply Subtype.ext
    rw [map_one, ← hρy]
    exact A4.conjAct_eq_one_iff.2 hyC
  · have h3 : conjAct W (y ^ 3) = 1 := by
      rw [map_pow, hρy, ← Subgroup.coe_pow, ← map_pow, hg3, map_one, Subgroup.coe_one]
    simpa using A4.conjAct_eq_one_iff.1 h3
  · intro w hwW hwT
    have h1 : (conjAct W y ⟨w, hwW⟩ : ↥W) = ⟨w, hwW⟩ := by
      rw [hρy, he]
      apply l3coord_injective D
      rw [l3coord_rho]
      exact hgfix ⟨w, hwW⟩ hwT
    have h2 := congrArg Subtype.val h1
    rw [A5.conjAct_val] at h2
    calc (y : G) * w = (y : G) * w * (y : G)⁻¹ * y := by group
      _ = w * y := by rw [h2]

end CFSG.Quasithin.H13.NQS134
