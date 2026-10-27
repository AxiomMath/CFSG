module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7A
public import CFSG.Quasithin.EmptyFaithful.ModCModel7B
public import CFSG.Quasithin.EmptyFaithful.ModCModel7C
public import CFSG.Quasithin.EmptyFaithful.ModCModel7D
public import CFSG.Quasithin.EmptyFaithful.ModCModel7E

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

theorem modelOut (D : Subgroup (Perm (Fin 7))) (hDe : ∀ d ∈ D, sign d = 1) (hD8 : Nat.card D = 8)
    (z v : PermMod 7) (hz : ∑ i, Multiplicative.toAdd z i = 0) (hz1 : z ≠ 1)
    (hv : ∑ i, Multiplicative.toAdd v i = 0) (hv1 : v ≠ 1) (hvz : v ≠ z)
    (hDV : ∀ d ∈ D, permAct 7 d z = z ∧ (permAct 7 d v = v ∨ permAct 7 d v = z * v))
    (hwt : wt v = wt z ∨ wt (z * v) = wt z)
    (g : Perm (Fin 7)) (hg3 : g ^ 3 = 1) (hgz : permAct 7 g z = z)
    (hgv1 : permAct 7 g v ≠ v) (hgv2 : permAct 7 g v ≠ z * v)
    (hne : (join3F z v g).card ≠ 8)
    (h5 : ¬ 5 ∣ Nat.card ↥(Subgroup.closure ((D : Set (Perm (Fin 7))) ∪ {g}))) :
    ∃ y : PermMod 7, y ∈ join3F z v g ∧ (∑ i, Multiplicative.toAdd y i = 0) ∧ y ≠ 1 ∧ y ≠ z ∧
      (∀ d ∈ D, permAct 7 d y = y) ∧
      (∀ u : PermMod 7, (∑ i, Multiplicative.toAdd u i = 0) → (∀ d ∈ D, permAct 7 d u = u) →
        u = 1 ∨ u = z ∨ u = y ∨ u = z * y) ∧
      (∃ j : Perm (Fin 7), sign j = 1 ∧ permAct 7 j y = y ∧ permAct 7 j z ≠ z) ∧
      (∃ j' : Perm (Fin 7), sign j' = 1 ∧ permAct 7 j' y = y ∧ permAct 7 j' v ≠ v ∧
        permAct 7 j' v ≠ z * v ∧ permAct 7 j' v ≠ z) ∧
      (∃ L : List (Perm (Fin 7)), L.length = 8 ∧ (∀ σ ∈ L, sign σ = 1) ∧
        (L.map (fun σ => permAct 7 σ (z * y))).Nodup) ∧
      ((Finset.univ.filter fun u : PermMod 7 =>
        (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt y).card ≤ 7) := by
  have hD0le : D0 ≤ alternatingGroup (Fin 7) := fun s hs => Perm.mem_alternatingGroup.mpr (D0_even s hs)
  have hDle : D ≤ alternatingGroup (Fin 7) := fun d hd => Perm.mem_alternatingGroup.mpr (hDe d hd)
  obtain ⟨τ, hτ⟩ := exists_conj_sylow fac_alt7 hDle hD0le hD8 D0_card
  have hgens : ∀ s ∈ gens, τ⁻¹ * s * τ ∈ D := fun s hs => (hτ s).1 (Subgroup.subset_closure hs)
  have hconj : ∀ (s : Perm (Fin 7)) (y : PermMod 7),
      permAct 7 s (permAct 7 τ y) = permAct 7 τ (permAct 7 (τ⁻¹ * s * τ) y) := by
    intro s y
    rw [permAct_conj_inv_apply, permAct_inv_apply_self']
  have hinj := (permAct 7 τ).injective
  have hz' : CondZ (permAct 7 τ z) := by
    refine ⟨by rw [sum_permAct]; exact hz, fun h => hz1 (hinj (by rw [h, map_one])), fun s hs => ?_⟩
    rw [hconj, (hDV _ (hgens s hs)).1]
  have hv' : CondV (permAct 7 τ z) (permAct 7 τ v) := by
    refine ⟨by rw [sum_permAct]; exact hv, fun h => hv1 (hinj (by rw [h, map_one])),
      fun h => hvz (hinj h), fun s hs => ?_, ?_⟩
    · rw [hconj, ← map_mul]
      rcases (hDV _ (hgens s hs)).2 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · rw [wt_permAct, wt_permAct, ← map_mul, wt_permAct]
      exact hwt
  have hcl := classify _ hz' _ hv'
  have hΛ : permAct 7 τ z = a ∧ (permAct 7 τ v = w ∨ permAct 7 τ v = a * w) := (by
    rcases hcl with h | ⟨hzb, hv'⟩
    · exact h
    · exfalso
      have hg'b : permAct 7 (τ * g * τ⁻¹) b = b := by rw [← hzb, permAct_conj_apply, hgz]
      have hg'3 : (τ * g * τ⁻¹) ^ 3 = 1 := by rw [conj_pow, hg3]; group
      have hgv1' : permAct 7 (τ * g * τ⁻¹) (permAct 7 τ v) ≠ permAct 7 τ v := by
        rw [permAct_conj_apply]; exact fun h => hgv1 (hinj h)
      have hgv2' : permAct 7 (τ * g * τ⁻¹) (permAct 7 τ v) ≠ b * permAct 7 τ v := by
        rw [permAct_conj_apply, ← hzb, ← map_mul]; exact fun h => hgv2 (hinj h)
      have hvmem' : permAct 7 τ v ∈ [t1, t2] := by
        rcases hv' with h | h
        · simp [h]
        · simp [h]
      have h6 := g_tri _ ⟨hg'b, hg'3, _, hvmem', hgv1', hgv2'⟩
      have h5' := orbit5 _ (mem_stab45_of_fix hg'b) h6
      rw [card_closure_conj τ D D0 g hτ] at h5'
      exact h5 h5')
  obtain ⟨hza, hvw⟩ := hΛ
  have hg'z : permAct 7 (τ * g * τ⁻¹) a = a := by
    rw [← hza, permAct_conj_apply, hgz]
  have hg'3 : (τ * g * τ⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hg3]; group
  have hgv1' : permAct 7 (τ * g * τ⁻¹) (permAct 7 τ v) ≠ permAct 7 τ v := by
    rw [permAct_conj_apply]; exact fun h => hgv1 (hinj h)
  have hgv2' : permAct 7 (τ * g * τ⁻¹) (permAct 7 τ v) ≠ a * permAct 7 τ v := by
    rw [permAct_conj_apply, ← hza, ← map_mul]; exact fun h => hgv2 (hinj h)
  have hvmem : permAct 7 τ v ∈ [w, a * w] := by
    rcases hvw with h | h
    · simp [h]
    · simp [h]
  have hga := g_analysis _ hg'z hg'3 _ hvmem hgv1' hgv2'
  have hcard := card_join3F_conj τ g z v
  rw [hza] at hcard
  have hxmem : x ∈ join3F a (permAct 7 τ v) (τ * g * τ⁻¹) := by
    rcases hga with h | h
    · exact (hne (hcard.symm.trans h)).elim
    · exact h
  rw [← hza, join3F_conj] at hxmem
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxmem
  have hyx' : permAct 7 τ y = x := hyx
  have hDfix : ∀ (u : PermMod 7), (∀ s ∈ D0, permAct 7 s (permAct 7 τ u) = permAct 7 τ u) →
      ∀ d ∈ D, permAct 7 d u = u := by
    intro u hu d hd
    have hs : τ * d * τ⁻¹ ∈ D0 := (hτ _).2 (by
      have : τ⁻¹ * (τ * d * τ⁻¹) * τ = d := by group
      rw [this]; exact hd)
    have h := hu _ hs
    rw [hconj, show τ⁻¹ * (τ * d * τ⁻¹) * τ = d by group] at h
    exact hinj h
  have hxD0 : ∀ s ∈ D0, permAct 7 s x = x :=
    fix_of_closure (S := {s | s ∈ gens}) x_fix
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← sum_permAct τ y, hyx']; exact x_core
  · intro h; rw [h, map_one] at hyx'; exact x_ne_one hyx'.symm
  · intro h; apply x_ne_a; rw [← hyx', h]; exact hza
  · exact hDfix y (fun s hs => by rw [hyx']; exact hxD0 s hs)
  · intro u hu hDu
    have hfix : ∀ s ∈ gens, permAct 7 s (permAct 7 τ u) = permAct 7 τ u := by
      intro s hs
      rw [hconj, hDu _ (hgens s hs)]
    rcases fixed_vectors _ (by rw [sum_permAct]; exact hu) hfix with h | h | h | h
    · left; exact hinj (by rw [h, map_one])
    · right; left; exact hinj (by rw [h, hza])
    · right; right; right
      apply hinj
      rw [map_mul, hza, hyx', ab_eq, h]
    · right; right; left; exact hinj (by rw [h, hyx'])
  · obtain ⟨j₀, j₀', hj₀s, hj₀s', hj₀x, hj₀a, hj₀'x, hj₀'v⟩ := exists_jj
    have hτy : permAct 7 τ⁻¹ x = y := by rw [← hyx']; exact permAct_inv_apply_self τ y
    refine ⟨τ⁻¹ * j₀ * τ, by rw [sign_conj]; exact hj₀s, ?_, ?_⟩
    · rw [permAct_conj_inv_apply, hyx', hj₀x, hτy]
    · intro h
      apply hj₀a
      rw [permAct_conj_inv_apply, hza] at h
      have := congrArg (permAct 7 τ) h
      rw [permAct_inv_apply_self', hza] at this
      exact this
  · obtain ⟨j₀, j₀', hj₀s, hj₀s', hj₀x, hj₀a, hj₀'x, hj₀'v⟩ := exists_jj
    have hτy : permAct 7 τ⁻¹ x = y := by rw [← hyx']; exact permAct_inv_apply_self τ y
    refine ⟨τ⁻¹ * j₀' * τ, by rw [sign_conj]; exact hj₀s', ?_, ?_, ?_, ?_⟩
    · rw [permAct_conj_inv_apply, hyx', hj₀'x, hτy]
    · intro h
      apply (hj₀'v _ hvmem).1
      rw [permAct_conj_inv_apply] at h
      have := congrArg (permAct 7 τ) h
      rw [permAct_inv_apply_self'] at this
      exact this
    · intro h
      apply (hj₀'v _ hvmem).2.1
      rw [permAct_conj_inv_apply] at h
      have := congrArg (permAct 7 τ) h
      rw [permAct_inv_apply_self', map_mul, hza] at this
      exact this
    · intro h
      apply (hj₀'v _ hvmem).2.2
      rw [permAct_conj_inv_apply] at h
      have := congrArg (permAct 7 τ) h
      rw [permAct_inv_apply_self', hza] at this
      exact this
  · obtain ⟨L, hL8, hLs, hLn⟩ := pigeon_list
    refine ⟨L.map (fun σ => τ⁻¹ * σ * τ), by simpa using hL8, ?_, ?_⟩
    · intro σ hσ
      rw [List.mem_map] at hσ
      obtain ⟨σ', hσ', rfl⟩ := hσ
      rw [sign_conj]
      exact hLs σ' hσ'
    · have hzy : permAct 7 τ (z * y) = b := by rw [map_mul, hza, hyx', ab_eq]
      have : (List.map (fun σ => permAct 7 σ (z * y)) (L.map fun σ => τ⁻¹ * σ * τ)) =
          (L.map (fun σ => permAct 7 σ b)).map (permAct 7 τ⁻¹) := by
        rw [List.map_map, List.map_map]
        refine List.map_congr_left fun σ _ => ?_
        simp only [Function.comp]
        rw [permAct_conj_inv_apply, hzy]
      rw [this]
      exact hLn.map (permAct 7 τ⁻¹).injective
  · have hwy : wt y = wt x := by rw [← hyx', wt_permAct]
    rw [hwy]
    exact wt_count

end M7

theorem modelOut7 : ModelOut 7 := M7.modelOut

end CFSG.Quasithin.ModC
