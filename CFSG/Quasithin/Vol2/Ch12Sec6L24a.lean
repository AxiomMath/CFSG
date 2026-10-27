module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L19 S126L19a S126L20a Equiv

namespace S126L24

abbrev vx (m : ↥(coreMod 8)) : Fin 8 → ZMod 2 := Multiplicative.toAdd (m : PermMod 8)

theorem vx_mul (m m' : ↥(coreMod 8)) : vx (m * m') = vx m + vx m' := rfl

theorem vx_inv (m : ↥(coreMod 8)) : vx m⁻¹ = -vx m := rfl

theorem vx_one : vx 1 = 0 := rfl

theorem vx_coreAct (σ : Perm (Fin 8)) (m : ↥(coreMod 8)) :
    vx (coreAct 8 σ m) = fun i => vx m (σ⁻¹ i) := rfl

theorem vx_injective : Function.Injective vx := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem vx_eOm : vx eOm = fun _ => 1 := rfl

theorem vx_pe (a b : Fin 8) : vx (pe a b) = B5FinS8.pv a b := rfl

@[expose] def E0123 : ↥(coreMod 8) := ⟨eset {0, 1, 2, 3}, e0123_mem⟩

theorem mk_E0123 : (QuotientGroup.mk E0123 : D8) = e0123 := rfl

abbrev e0v : Fin 8 → ZMod 2 := Multiplicative.toAdd (eset {0, 1, 2, 3})

theorem vx_E0123 : vx E0123 = e0v := rfl

theorem sum8 (m : ↥(coreMod 8)) :
    vx m 0 + vx m 1 + vx m 2 + vx m 3 + vx m 4 + vx m 5 + vx m 6 + vx m 7 = 0 := by
  have h := mem_coreMod.1 m.2
  rw [Fin.sum_univ_eight] at h
  exact h

abbrev Ev (x : Fin 8 → ZMod 2) : Prop := x 0 + x 1 + x 2 + x 3 = 0

abbrev BC (x : Fin 8 → ZMod 2) : Prop :=
  x 1 = x 0 ∧ x 2 = x 0 ∧ x 3 = x 0 ∧ x 5 = x 4 ∧ x 6 = x 4 ∧ x 7 = x 4

theorem ev_add_ones : ∀ x : Fin 8 → ZMod 2, Ev (x + fun _ => 1) ↔ Ev x := by
  decide +kernel

theorem bc_cases : ∀ x : Fin 8 → ZMod 2, BC x →
    x = 0 ∨ x = (fun _ => 1) ∨ x = e0v ∨ x = e0v + fun _ => 1 := by
  decide +kernel

theorem bc_zero : BC 0 := by decide

theorem bc_ones : BC fun _ => 1 := by decide

theorem bc_e0v : BC e0v := by decide

theorem bc_e0v_ones : BC (e0v + fun _ => 1) := by decide

theorem mem_W5_iff (m : ↥(coreMod 8)) : (QuotientGroup.mk m : D8) ∈ W5 ↔ Ev (vx m) := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := Subgroup.mem_map.1 h
    rw [QuotientGroup.mk'_apply] at he
    have hm'' : Ev (vx m') := hm'
    rcases (mk_eq_iff m' m).1 he with h1 | h1
    · rwa [show m' = m from Subtype.ext h1] at hm''
    · have h2 : vx m' = vx m + fun _ => 1 := by
        show Multiplicative.toAdd (m' : PermMod 8) = _
        rw [h1]
        rfl
      rwa [h2, ev_add_ones] at hm''
  · intro h
    exact Subgroup.mem_map.2 ⟨m, h, rfl⟩

theorem mem_W1_iff (m : ↥(coreMod 8)) : (QuotientGroup.mk m : D8) ∈ W1 ↔ BC (vx m) := by
  constructor
  · intro h
    rcases mem_W1 h with h1 | h1
    · rcases (mk_eq_one_iff m).1 h1 with rfl | rfl
      · exact bc_zero
      · exact bc_ones
    · rw [e0123] at h1
      rcases (mk_eq_iff m _).1 h1 with h2 | h2
      · have h3 : vx m = e0v := by
          show Multiplicative.toAdd (m : PermMod 8) = _
          rw [h2]
        rw [h3]
        exact bc_e0v
      · have h3 : vx m = e0v + fun _ => 1 := by
          show Multiplicative.toAdd (m : PermMod 8) = _
          rw [h2]
          rfl
        rw [h3]
        exact bc_e0v_ones
  · intro h
    have hO : (QuotientGroup.mk eOm : D8) = 1 := (mk_eq_one_iff eOm).2 (Or.inr rfl)
    rcases bc_cases _ h with h1 | h1 | h1 | h1
    · rw [show m = 1 from vx_injective h1, QuotientGroup.mk_one]
      exact W1.one_mem
    · rw [show m = eOm from vx_injective h1, hO]
      exact W1.one_mem
    · rw [show m = E0123 from vx_injective h1, mk_E0123]
      exact e0123_mem_W1
    · rw [show m = E0123 * eOm from vx_injective h1, QuotientGroup.mk_mul, hO, mul_one, mk_E0123]
      exact e0123_mem_W1

theorem ev_add_pv04 : ∀ x : Fin 8 → ZMod 2, Ev (x + B5FinS8.pv 0 4) ↔ ¬ Ev x := by
  decide +kernel

theorem index_W5 : W5.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨QuotientGroup.mk (pe 0 4), fun b => ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, mem_W5_iff, mem_W5_iff, vx_mul, vx_pe, ev_add_pv04]
  by_cases h : Ev (vx m)
  · exact Or.inr ⟨h, fun h' => h' h⟩
  · exact Or.inl ⟨h, h⟩

theorem card_W5 : Nat.card W5 = 32 := by
  have h := Subgroup.card_mul_index W5
  rw [index_W5, S126L20.card_D8_eq] at h
  omega

theorem W1_le_W5 : W1 ≤ W5 := by
  intro y hy
  rcases mem_W1 hy with rfl | rfl
  · exact W5.one_mem
  · rw [← mk_E0123, mem_W5_iff]
    decide

theorem ev_iff_sum (x : Fin 8 → ZMod 2) :
    Ev x ↔ ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => i.val < 4), x i = 0 := by
  have : ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => i.val < 4), x i = x 0 + x 1 + x 2 + x 3 := by
    rw [Finset.sum_filter, Fin.sum_univ_eight]
    simp
  rw [this]

theorem ev_coreAct {σ : Perm (Fin 8)}
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)))
    {m : ↥(coreMod 8)} (hm : Ev (vx m)) : Ev (vx (coreAct 8 σ m)) := by
  rw [ev_iff_sum] at hm ⊢
  rw [vx_coreAct]
  set B := Finset.univ.filter (fun i : Fin 8 => i.val < 4) with hB
  have h1 : ∑ i ∈ B, vx m (σ⁻¹ i) = ∑ j ∈ B.map (σ⁻¹ : Perm (Fin 8)).toEmbedding, vx m j := by
    rw [Finset.sum_map]
    rfl
  rw [h1]
  rcases hb with hb | hb
  · have h2 : B.map (σ⁻¹ : Perm (Fin 8)).toEmbedding = B := by
      ext j
      rw [Finset.mem_map_equiv, hB, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      exact (hb j).symm
    rw [h2]
    exact hm
  · have h2 : B.map (σ⁻¹ : Perm (Fin 8)).toEmbedding =
        Finset.univ.filter (fun i : Fin 8 => ¬ i.val < 4) := by
      ext j
      rw [Finset.mem_map_equiv, hB, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      rw [hb j]
      change (σ j).val < 4 ↔ ¬ 4 ≤ (σ j).val
      omega
    rw [h2]
    have htot := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin 8 => i.val < 4)
      (vx m)
    have hs : ∑ i, vx m i = 0 := mem_coreMod.1 m.2
    rw [hs, ← hB, hm, zero_add] at htot
    exact htot

theorem dAct_mem_W5 {σ : Perm (Fin 8)}
    (hb : (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) ∨ (∀ i : Fin 8, (i.val < 4 ↔ 4 ≤ (σ i).val)))
    {y : D8} (hy : y ∈ W5) : dAct σ y ∈ W5 := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [dAct_mk, mem_W5_iff]
  exact ev_coreAct hb ((mem_W5_iff m).1 hy)

theorem key_c1 : ∀ x : Fin 8 → ZMod 2, Ev x → ¬ (x 0 = x 1 ∧ x 1 = x 2) →
    (fun i => x i + x (c1⁻¹ i)) = B5FinS8.pv 0 1 ∨ (fun i => x i + x (c1⁻¹ i)) = B5FinS8.pv 1 2 ∨
      (fun i => x i + x (c1⁻¹ i)) = B5FinS8.pv 0 2 := by
  decide +kernel

theorem key_bsw : ∀ x : Fin 8 → ZMod 2,
    x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 = 0 → Ev x → ¬ BC x →
    ¬ (x 0 = x 1 ∧ x 1 = x 2) ∨
      ¬ (x (S126L1c.bsw⁻¹ 0) = x (S126L1c.bsw⁻¹ 1) ∧
        x (S126L1c.bsw⁻¹ 1) = x (S126L1c.bsw⁻¹ 2)) := by
  decide +kernel

theorem decomp_chk : ∀ x : Fin 8 → ZMod 2,
    x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 = 0 → Ev x →
    x = ((if x 1 + x 3 = 0 then 0 else B5FinS8.pv 0 1) +
      (if x 2 + x 3 = 0 then 0 else B5FinS8.pv 0 2) +
      (if x 5 + x 7 = 0 then 0 else B5FinS8.pv 4 5) +
      (if x 6 + x 7 = 0 then 0 else B5FinS8.pv 4 6) +
      (if x 3 + x 7 = 0 then 0 else e0v) + (if x 7 = 0 then 0 else fun _ => 1)) := by
  decide +kernel

theorem c1_vals : c1 0 = 1 ∧ c1 1 = 2 ∧ c1 2 = 0 := by
  decide

theorem bsw_vals : S126L1c.bsw 0 = 4 ∧ S126L1c.bsw 1 = 5 ∧ S126L1c.bsw 2 = 6 := by
  decide

@[expose] def pw (E : ↥(coreMod 8)) (a : ZMod 2) : ↥(coreMod 8) := if a = 0 then 1 else E

theorem vx_pw (E : ↥(coreMod 8)) (a : ZMod 2) : vx (pw E a) = if a = 0 then 0 else vx E := by
  unfold pw
  split_ifs
  · rfl
  · rfl

theorem mk_pw_mem {Ŵ : Subgroup D8} {E : ↥(coreMod 8)} (hE : (QuotientGroup.mk E : D8) ∈ Ŵ)
    (a : ZMod 2) : (QuotientGroup.mk (pw E a) : D8) ∈ Ŵ := by
  unfold pw
  split_ifs
  · rw [QuotientGroup.mk_one]
    exact Ŵ.one_mem
  · exact hE

theorem irred_W {Ŵ : Subgroup D8} (h1 : W1 ≤ Ŵ) (h5 : Ŵ ≤ W5)
    (hc : ∀ y ∈ Ŵ, dAct c1 y ∈ Ŵ) (hb : ∀ y ∈ Ŵ, dAct S126L1c.bsw y ∈ Ŵ) :
    Ŵ = W1 ∨ Ŵ = W5 := by
  by_cases hle : Ŵ ≤ W1
  · exact Or.inl (le_antisymm hle h1)
  right
  obtain ⟨y, hyW, hy1⟩ := Set.not_subset.1 hle
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  have hev : ∀ m' : ↥(coreMod 8), (QuotientGroup.mk m' : D8) ∈ Ŵ → Ev (vx m') := fun m' h =>
    (mem_W5_iff m').1 (h5 h)
  have hpe : ∀ a b : Fin 8, (QuotientGroup.mk (pe a b) : D8) ∈ Ŵ →
      (QuotientGroup.mk (pe (c1 a) (c1 b)) : D8) ∈ Ŵ := fun a b h => by
    rw [← dAct_pe]
    exact hc _ h
  obtain ⟨hc0, hc1, hc2⟩ := c1_vals
  have step : ∀ m' : ↥(coreMod 8), (QuotientGroup.mk m' : D8) ∈ Ŵ →
      ¬ (vx m' 0 = vx m' 1 ∧ vx m' 1 = vx m' 2) →
      (QuotientGroup.mk (pe 0 1) : D8) ∈ Ŵ ∧ (QuotientGroup.mk (pe 0 2) : D8) ∈ Ŵ := by
    intro m' hm' hnc
    have hu : (QuotientGroup.mk (m' * coreAct 8 c1 m') : D8) ∈ Ŵ := by
      rw [QuotientGroup.mk_mul, ← dAct_mk]
      exact Ŵ.mul_mem hm' (hc _ hm')
    rcases key_c1 (vx m') (hev m' hm') hnc with h | h | h
    · rw [show m' * coreAct 8 c1 m' = pe 0 1 from vx_injective h] at hu
      have h2 := hpe _ _ (hpe _ _ hu)
      rw [hc0, hc1, hc2, pe_comm] at h2
      exact ⟨hu, h2⟩
    · rw [show m' * coreAct 8 c1 m' = pe 1 2 from vx_injective h] at hu
      have h2 := hpe _ _ hu
      rw [hc1, hc2, pe_comm] at h2
      have h3 := hpe _ _ h2
      rw [hc0, hc2, pe_comm] at h3
      exact ⟨h3, h2⟩
    · rw [show m' * coreAct 8 c1 m' = pe 0 2 from vx_injective h] at hu
      have h2 := hpe _ _ hu
      rw [hc0, hc2, pe_comm] at h2
      exact ⟨h2, hu⟩
  have hbc : ¬ BC (vx m) := fun h => hy1 ((mem_W1_iff m).2 h)
  obtain ⟨h01, h02⟩ : (QuotientGroup.mk (pe 0 1) : D8) ∈ Ŵ ∧
      (QuotientGroup.mk (pe 0 2) : D8) ∈ Ŵ := by
    rcases key_bsw (vx m) (sum8 m) (hev m hyW) hbc with h | h
    · exact step m hyW h
    · refine step (coreAct 8 S126L1c.bsw m) (by rw [← dAct_mk]; exact hb _ hyW) ?_
      rw [vx_coreAct]
      exact h
  obtain ⟨hb0, hb1, hb2⟩ := bsw_vals
  have h45 : (QuotientGroup.mk (pe 4 5) : D8) ∈ Ŵ := by
    have := hb _ h01
    rwa [dAct_pe, hb0, hb1] at this
  have h46 : (QuotientGroup.mk (pe 4 6) : D8) ∈ Ŵ := by
    have := hb _ h02
    rwa [dAct_pe, hb0, hb2] at this
  have hE : (QuotientGroup.mk E0123 : D8) ∈ Ŵ := h1 (by rw [mk_E0123]; exact e0123_mem_W1)
  have hO : (QuotientGroup.mk eOm : D8) ∈ Ŵ := by
    rw [(mk_eq_one_iff eOm).2 (Or.inr rfl)]
    exact Ŵ.one_mem
  refine le_antisymm h5 fun z hz => ?_
  obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.1 hz
  rw [QuotientGroup.mk'_apply]
  set x := vx m' with hx
  have hd := decomp_chk x (sum8 m') hm'
  have he : m' = pw (pe 0 1) (x 1 + x 3) * pw (pe 0 2) (x 2 + x 3) * pw (pe 4 5) (x 5 + x 7) *
      pw (pe 4 6) (x 6 + x 7) * pw E0123 (x 3 + x 7) * pw eOm (x 7) := by
    apply vx_injective
    rw [vx_mul, vx_mul, vx_mul, vx_mul, vx_mul, vx_pw, vx_pw, vx_pw, vx_pw, vx_pw, vx_pw, vx_pe,
      vx_pe, vx_pe, vx_pe, vx_E0123, vx_eOm, ← hx]
    exact hd
  rw [he]
  simp only [QuotientGroup.mk_mul]
  exact Ŵ.mul_mem (Ŵ.mul_mem (Ŵ.mul_mem (Ŵ.mul_mem (Ŵ.mul_mem (mk_pw_mem h01 _) (mk_pw_mem h02 _))
    (mk_pw_mem h45 _)) (mk_pw_mem h46 _)) (mk_pw_mem hE _)) (mk_pw_mem hO _)

theorem bc_pair1 : ∀ a b j : Fin 8, 0 < j.val → j.val < 4 → a ≠ b →
    BC (B5FinS8.pv a b - B5FinS8.pv 0 j) →
      a.val < 4 ∧ b = tf ⟨a.val % 4, Nat.mod_lt _ (by norm_num)⟩ 0 j := by
  decide +kernel

theorem bc_pair2 : ∀ a b j : Fin 8, 4 < j.val → a ≠ b →
    BC (B5FinS8.pv a b - B5FinS8.pv 4 j) →
      4 ≤ a.val ∧ b = tf 0 ⟨a.val % 4, Nat.mod_lt _ (by norm_num)⟩ j := by
  decide +kernel

theorem tf_left : ∀ u v v' : Fin 4, ∀ j : Fin 8, j.val < 4 → tf u v j = tf u v' j := by
  decide

theorem tf_right : ∀ u u' v : Fin 4, ∀ j : Fin 8, 4 ≤ j.val → tf u v j = tf u' v j := by
  decide

theorem tf_base0 : ∀ a : Fin 8, a.val < 4 → ∀ v : Fin 4,
    tf ⟨a.val % 4, Nat.mod_lt _ (by norm_num)⟩ v 0 = a := by
  decide

theorem tf_base4 : ∀ a : Fin 8, 4 ≤ a.val → ∀ u : Fin 4,
    tf u ⟨a.val % 4, Nat.mod_lt _ (by norm_num)⟩ 4 = a := by
  decide

theorem ev_pv0 : ∀ j : Fin 8, j.val < 4 → Ev (B5FinS8.pv 0 j) := by
  decide

theorem ev_pv4 : ∀ j : Fin 8, 4 ≤ j.val → Ev (B5FinS8.pv 4 j) := by
  decide

theorem bc_of_cent {σ : Perm (Fin 8)} (h : ∀ y ∈ W5, dAct σ y * y⁻¹ ∈ W1) {i k : Fin 8}
    (hik : Ev (B5FinS8.pv i k)) : BC (B5FinS8.pv (σ i) (σ k) - B5FinS8.pv i k) := by
  have hy : (QuotientGroup.mk (pe i k) : D8) ∈ W5 := (mem_W5_iff _).2 hik
  have h1 := h _ hy
  rw [dAct_pe, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul, vx_inv,
    vx_pe, vx_pe, ← sub_eq_add_neg] at h1
  exact h1

theorem mem_E16_of_cent {σ : Perm (Fin 8)} (h : ∀ y ∈ W5, dAct σ y * y⁻¹ ∈ W1) : σ ∈ E16 := by
  have h01 := bc_pair1 (σ 0) (σ 1) 1 (by decide) (by decide) (σ.injective.ne (by decide))
    (bc_of_cent h (ev_pv0 1 (by decide)))
  have h45 := bc_pair2 (σ 4) (σ 5) 5 (by decide) (σ.injective.ne (by decide))
    (bc_of_cent h (ev_pv4 5 (by decide)))
  refine ⟨⟨(σ 0).val % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨(σ 4).val % 4, Nat.mod_lt _ (by norm_num)⟩,
    Equiv.ext fun j => ?_⟩
  rw [tau_apply]
  by_cases hj : j.val < 4
  · by_cases hj0 : j = 0
    · subst hj0
      exact (tf_base0 (σ 0) h01.1 _).symm
    · have hj1 : 0 < j.val := by
        rcases Nat.eq_zero_or_pos j.val with h0 | h0
        · exact absurd (Fin.ext h0) hj0
        · exact h0
      have h2 := bc_pair1 (σ 0) (σ j) j hj1 hj (σ.injective.ne (Ne.symm hj0))
        (bc_of_cent h (ev_pv0 j hj))
      rw [h2.2]
      exact tf_left _ _ _ j hj
  · have hj' : 4 ≤ j.val := by omega
    by_cases hj4 : j = 4
    · subst hj4
      exact (tf_base4 (σ 4) h45.1 _).symm
    · have hj5 : 4 < j.val := by
        rcases Nat.lt_or_eq_of_le hj' with h0 | h0
        · exact h0
        · exact absurd (Fin.ext h0.symm) hj4
      have h2 := bc_pair2 (σ 4) (σ j) j hj5 (σ.injective.ne (Ne.symm hj4))
        (bc_of_cent h (ev_pv4 j hj'))
      rw [h2.2]
      exact tf_right _ _ _ j hj'

theorem bc_tau : ∀ u v : Fin 4, ∀ x : Fin 8 → ZMod 2,
    x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 = 0 → Ev x →
    BC (fun i => x (tf u v i) - x i) := by
  decide +kernel

theorem cent_of_mem_E16 {σ : Perm (Fin 8)} (hσ : σ ∈ E16) {y : D8} (hy : y ∈ W5) :
    dAct σ y * y⁻¹ ∈ W1 := by
  obtain ⟨u, v, rfl⟩ := hσ
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul, vx_inv,
    vx_coreAct]
  have e : ((fun i => vx m ((tau u v)⁻¹ i)) + -vx m) = fun i => vx m (tf u v i) - vx m i := by
    funext i
    rw [Pi.add_apply, Pi.neg_apply, tau_inv_apply, ← sub_eq_add_neg]
  rw [e]
  exact bc_tau u v (vx m) (sum8 m) ((mem_W5_iff m).1 hy)

theorem tau_fix_chk : ∀ u v : Fin 4,
    (B5FinS8.pv (tf u v 0) (tf u v 1) = B5FinS8.pv 0 1 ∨
      B5FinS8.pv (tf u v 0) (tf u v 1) = B5FinS8.pv 0 1 + fun _ => 1) →
    (B5FinS8.pv (tf u v 0) (tf u v 2) = B5FinS8.pv 0 2 ∨
      B5FinS8.pv (tf u v 0) (tf u v 2) = B5FinS8.pv 0 2 + fun _ => 1) →
    (B5FinS8.pv (tf u v 4) (tf u v 5) = B5FinS8.pv 4 5 ∨
      B5FinS8.pv (tf u v 4) (tf u v 5) = B5FinS8.pv 4 5 + fun _ => 1) →
    (B5FinS8.pv (tf u v 4) (tf u v 6) = B5FinS8.pv 4 6 ∨
      B5FinS8.pv (tf u v 4) (tf u v 6) = B5FinS8.pv 4 6 + fun _ => 1) →
    u = 0 ∧ v = 0 := by
  decide +kernel

theorem eq_one_of_fix {σ : Perm (Fin 8)} (h : ∀ y ∈ W5, dAct σ y = y) : σ = 1 := by
  obtain ⟨u, v, rfl⟩ := mem_E16_of_cent fun y hy => by
    rw [h y hy, mul_inv_cancel]
    exact W1.one_mem
  have key : ∀ i k : Fin 8, Ev (B5FinS8.pv i k) →
      (B5FinS8.pv (tf u v i) (tf u v k) = B5FinS8.pv i k ∨
        B5FinS8.pv (tf u v i) (tf u v k) = B5FinS8.pv i k + fun _ => 1) := by
    intro i k hik
    have h1 := h _ ((mem_W5_iff (pe i k)).2 hik)
    rw [dAct_pe, mk_eq_iff] at h1
    rcases h1 with h1 | h1
    · left
      have := congrArg Multiplicative.toAdd h1
      exact this
    · right
      have := congrArg Multiplicative.toAdd h1
      exact this
  have := tau_fix_chk u v (key 0 1 (by decide)) (key 0 2 (by decide)) (key 4 5 (by decide))
    (key 4 6 (by decide))
  rw [this.1, this.2, tau_zero]

theorem tau_decomp : ∀ u v : Fin 4, tau u v = tau 1 0 ^ (u.val % 2) * tau 2 0 ^ (u.val / 2) *
    (tau 0 1 ^ (v.val % 2) * tau 0 2 ^ (v.val / 2)) := by
  decide

theorem E16_le_Q8 : E16 ≤ S126L1c.Q8 := by
  rintro _ ⟨u, v, rfl⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := S126L1c.mem_Q8
  rw [tau_decomp u v]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 _) (Subgroup.pow_mem _ h2 _))
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ h3 _) (Subgroup.pow_mem _ h4 _))

abbrev wt8 (x : Fin 8 → ZMod 2) : ℕ := (Finset.univ.filter fun i => x i ≠ 0).card

@[expose] def za (x : Fin 8 → ZMod 2) : Fin 8 := if x 0 = 0 then 0 else if x 1 = 0 then 1 else 2

@[expose] def zb (x : Fin 8 → ZMod 2) : Fin 8 := if x 3 = 0 then 3 else if x 2 = 0 then 2 else 1

@[expose] def oc (x : Fin 8 → ZMod 2) : Fin 8 := if x 4 = 1 then 4 else if x 5 = 1 then 5 else 6

@[expose] def od (x : Fin 8 → ZMod 2) : Fin 8 := if x 7 = 1 then 7 else if x 6 = 1 then 6 else 5

@[expose] def oa (x : Fin 8 → ZMod 2) : Fin 8 := if x 0 = 1 then 0 else if x 1 = 1 then 1 else 2

@[expose] def sw (x : Fin 8 → ZMod 2) : Perm (Fin 8) := swap (za x) (oc x) * swap (zb x) (od x)

theorem swap_chk : ∀ x : Fin 8 → ZMod 2, wt8 x = 4 →
    (wt8 (x + e0v) = 4 ∨ wt8 (x + e0v + fun _ => 1) = 4) →
    (fun i => e0v ((sw x)⁻¹ i)) = x ∧ (fun i => x ((sw x)⁻¹ i)) = e0v ∧ za x ≠ oc x ∧
      zb x ≠ od x ∧ (∀ i, sw x (sw x i) = i) ∧ Ev (B5FinS8.pv (oa x) (za x)) ∧
      ¬ Ev (fun i => B5FinS8.pv (oa x) (za x) ((sw x)⁻¹ i)) := by
  decide +kernel

theorem exists_swap {y : D8} (h4 : HasWt 4 y) (h4' : HasWt 4 (y * e0123)) :
    ∃ σ : Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) ∧ σ * σ = 1 ∧ dAct σ e0123 = y ∧
      dAct σ y = e0123 ∧ ∃ z ∈ W5, dAct σ z ∉ W5 := by
  obtain ⟨m, rfl, hm⟩ := h4
  obtain ⟨m', hm', hm'4⟩ := h4'
  have hx4 : wt8 (vx m) = 4 := hm
  have hx4' : wt8 (vx m + e0v) = 4 ∨ wt8 (vx m + e0v + fun _ => 1) = 4 := by
    rw [← mk_E0123, ← QuotientGroup.mk_mul, mk_eq_iff] at hm'
    rcases hm' with h | h
    · left
      have e : vx m' = vx m + e0v := by
        show Multiplicative.toAdd (m' : PermMod 8) = _
        rw [h]
        rfl
      rw [← e]
      exact hm'4
    · right
      have e : vx m' = vx m + e0v + fun _ => 1 := by
        show Multiplicative.toAdd (m' : PermMod 8) = _
        rw [h]
        rfl
      rw [← e]
      exact hm'4
  obtain ⟨hσe, hσx, hac, hbd, hinv, hev, hnev⟩ := swap_chk (vx m) hx4 hx4'
  refine ⟨sw (vx m), ?_, Equiv.ext fun i => hinv i, ?_, ?_,
    ⟨QuotientGroup.mk (pe (oa (vx m)) (za (vx m))), (mem_W5_iff _).2 hev, ?_⟩⟩
  · rw [Equiv.Perm.mem_alternatingGroup, sw, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hac,
      Equiv.Perm.sign_swap hbd]
    rfl
  · rw [← mk_E0123, dAct_mk]
    congr 1
    apply vx_injective
    rw [vx_coreAct]
    exact hσe
  · rw [← mk_E0123, dAct_mk]
    congr 1
    apply vx_injective
    rw [vx_coreAct]
    exact hσx
  · rw [dAct_mk, mem_W5_iff, vx_coreAct, vx_pe]
    exact hnev

theorem e0145_mem : eset {0, 1, 4, 5} ∈ coreMod 8 := by
  rw [mem_coreMod]
  decide

@[expose] def E0145 : ↥(coreMod 8) := ⟨eset {0, 1, 4, 5}, e0145_mem⟩

@[expose] noncomputable def e0145 : D8 := QuotientGroup.mk E0145

theorem W2_eq : W2 = Subgroup.closure {e0123, e0145} := by
  rw [W2, X2, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm | hm, rfl⟩
    · left
      rw [QuotientGroup.mk'_apply, ← mk_E0123]
      congr 1
      exact Subtype.ext hm
    · right
      rw [QuotientGroup.mk'_apply, e0145]
      congr 1
      exact Subtype.ext hm
  · rintro (rfl | rfl)
    · exact ⟨E0123, Or.inl rfl, rfl⟩
    · exact ⟨E0145, Or.inr rfl, rfl⟩

theorem hasWt_e0145 : HasWt 4 e0145 := ⟨E0145, rfl, by decide⟩

theorem hasWt_e0145_mul : HasWt 4 (e0145 * e0123) :=
  ⟨E0145 * E0123, by rw [QuotientGroup.mk_mul, mk_E0123]; rfl, by decide⟩

end S126L24

end CFSG.Quasithin.H13
