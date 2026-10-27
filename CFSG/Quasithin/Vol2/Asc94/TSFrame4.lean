module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame3
public import CFSG.Quasithin.Vol2.Asc94.TS40d
public import CFSG.Quasithin.Vol2.Asc94.TSModel10

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

@[expose] noncomputable def frame4 [Finite G] (hz : orderOf z = 2) (hF6 : L52.F6Model) : Frame4 G z :=
  have spec := Classical.choose_spec L52.B_orbits
  have specΔ := Classical.choose_spec L52.A1_orbits
  { toFrame3 := frame3 e hz hF6
    z_mem_A' := by
      have h := emb_mem_tr e L52.zt_mem_A2
      rwa [emb_zt e hz] at h
    Γ := fun i => emb e '' (Classical.choose L52.B_orbits i)
    Γ_disj := by
      obtain ⟨hd, -⟩ := spec
      intro i j hij
      exact (Set.disjoint_image_iff (emb_injective e)).2 (hd i j hij)
    Γ_union := by
      obtain ⟨-, hu, -⟩ := spec
      show (⋃ i, emb e '' (Classical.choose L52.B_orbits i)) =
        ((tr e L52.A1 ⊓ tr e L52.A2 : Subgroup G) : Set G) \ {1}
      rw [← Set.image_iUnion, hu, Set.image_diff (emb_injective e), Set.image_singleton, map_one,
        ← tr_inf]
      rfl
    Γ_inv := by
      obtain ⟨-, -, hinv, -⟩ := spec
      rintro i _ ⟨a', ha', rfl⟩ x ⟨x', hx', rfl⟩
      exact ⟨x'⁻¹ * a' * x', hinv i a' ha' x' hx', by rw [emb_conj]⟩
    Γ_trans := by
      obtain ⟨-, -, -, htr, -⟩ := spec
      rintro i _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
      obtain ⟨x', hx', hb⟩ := htr i a' ha' b' hb'
      exact ⟨emb e x', emb_mem_tr e hx', by rw [hb, emb_conj]⟩
    Γ_card := by
      obtain ⟨-, -, -, -, hc, -⟩ := spec
      intro i
      rw [Set.ncard_image_of_injective _ (emb_injective e), hc i]
      rfl
    Γ0 := by
      obtain ⟨-, -, -, -, -, h0, -⟩ := spec
      show emb e '' (Classical.choose L52.B_orbits 0) = {z}
      rw [h0, Set.image_singleton, emb_zt e hz]
    Γ1 := by
      obtain ⟨-, -, -, -, -, -, h1, -⟩ := spec
      show emb e '' (Classical.choose L52.B_orbits 1) =
        ((tr e L52.A1 ⊓ tr e L52.A2 ⊓ tr e L52.U1 : Subgroup G) : Set G) \ {1, z}
      rw [h1, Set.image_diff (emb_injective e), Set.image_pair, map_one, emb_zt e hz, ← tr_inf,
        ← tr_inf]
      rfl
    Γ2 := by
      obtain ⟨-, -, -, -, -, -, -, h2, -⟩ := spec
      show emb e '' (Classical.choose L52.B_orbits 2) =
        ((tr e L52.A1 ⊓ tr e L52.A2 ⊓ tr e L52.U2 : Subgroup G) : Set G) \ {1, z}
      rw [h2, Set.image_diff (emb_injective e), Set.image_pair, map_one, emb_zt e hz, ← tr_inf,
        ← tr_inf]
      rfl
    Γ3 := by
      obtain ⟨-, -, -, -, -, -, -, -, h3⟩ := spec
      show emb e '' (Classical.choose L52.B_orbits 3) =
        {a | a ∈ tr e L52.A1 ∧ a ∈ tr e L52.A2 ∧ a ∈ tr e L52.Qh ∧ a ≠ 1 ∧ a ∉ tr e L52.U1 ∧
          a ∉ tr e L52.U2}
      rw [h3]
      ext a
      constructor
      · rintro ⟨a', ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩
        refine ⟨emb_mem_tr e h1, emb_mem_tr e h2, emb_mem_tr e h3,
          fun h => h4 (emb_injective e (by rw [h, map_one])), ?_, ?_⟩
        · rw [emb_mem_tr_iff]
          exact h5
        · rw [emb_mem_tr_iff]
          exact h6
      · rintro ⟨⟨a', h1, rfl⟩, ⟨a'', h2, h2'⟩, ⟨a''', h3, h3'⟩, h4, h5, h6⟩
        have e2 : a'' = a' := emb_injective e h2'
        have e3 : a''' = a' := emb_injective e h3'
        rw [e2] at h2
        rw [e3] at h3
        refine ⟨a', ⟨h1, h2, h3, fun h => h4 (by rw [h, map_one]), ?_, ?_⟩, rfl⟩
        · intro h
          exact h5 (emb_mem_tr e h)
        · intro h
          exact h6 (emb_mem_tr e h)
    card_B := by
      show Nat.card ↥(tr e L52.A1 ⊓ tr e L52.A2) = 16
      rw [← tr_inf, card_tr, L52.card_A1_inf_A2]
      norm_num
    NH_J := by
      intro x hxz hxN
      obtain ⟨x', rfl⟩ := exists_emb e hxz
      have hJ : (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) = tr e L52.Jm := (tr_sup e _ _).symm
      have hxN' : emb e x' ∈ Subgroup.normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G) :=
        hxN
      rw [hJ] at hxN'
      have := (emb_mem_normalizer_tr e).1 hxN'
      rw [L52.normalizer_Jm_eq] at this
      exact emb_mem_tr e this
    Bsub := tr e L52.Bs
    card_Bsub := by
      rw [card_tr, L52.card_Bs]
      norm_num
    Γ012_le_Bsub := by
      obtain ⟨-, -, -, -, -, h0, h1, h2, -⟩ := spec
      intro i hi a ha
      obtain ⟨a', ha', rfl⟩ := ha
      exact emb_mem_tr e (L52.Gamma012_le_Bs h0 h1 h2 i hi a' ha')
    Δ_Q := by
      obtain ⟨-, -, -, -, -, h0, h1, h2, h3⟩ := specΔ
      intro i hi a ha
      obtain ⟨a', ha', rfl⟩ := ha
      exact emb_mem_tr e (L52.Delta_le_Qh h0 h1 h2 h3 i hi a' ha')
    TQ_not_U := by
      rintro _ ⟨t', ⟨hq, -, -, h1, h2⟩, rfl⟩
      refine ⟨?_, ?_, emb_mem_tr e hq⟩
      · intro h
        exact h1 ((emb_mem_tr_iff e).1 h)
      · intro h
        exact h2 ((emb_mem_tr_iff e).1 h) }

end CFSG.Quasithin.A94
