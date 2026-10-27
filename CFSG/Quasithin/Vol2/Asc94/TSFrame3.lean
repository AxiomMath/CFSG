module

public import CFSG.Quasithin.Vol2.Asc94.TSFrame2
public import CFSG.Quasithin.Vol2.Asc94.TS39g
public import CFSG.Quasithin.Vol2.Asc94.TSModel7

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem tr_cj (x' : L52.Hc) (X : Subgroup L52.Hc) :
    tr e (cjS x' X) = cjS (emb e x') (tr e X) := by
  show (X.map (MulAut.conj x').toMonoidHom).map (emb e) =
    (X.map (emb e)).map (MulAut.conj (emb e x')).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem emb_mem_normalizer_tr {X : Subgroup L52.Hc} {x' : L52.Hc} :
    emb e x' ∈ Subgroup.normalizer ((tr e X : Subgroup G) : Set G) ↔
      x' ∈ Subgroup.normalizer (X : Set L52.Hc) := by
  rw [Gen.mem_normalizer_iff_cj, Gen.mem_normalizer_iff_cj, ← tr_cj]
  exact (Subgroup.map_injective (emb_injective e)).eq_iff

@[expose] noncomputable def frame3 [Finite G] (hz : orderOf z = 2) (hF6 : L52.F6Model) : Frame3 G z :=
  have spec := Classical.choose_spec L52.A1_orbits
  { toFrame2 := frame2 e hz hF6
    Δ := fun i => emb e '' (Classical.choose L52.A1_orbits i)
    Δ_disj := by
      obtain ⟨hd, -⟩ := spec
      intro i j hij
      exact (Set.disjoint_image_iff (emb_injective e)).2 (hd i j hij)
    Δ_union := by
      obtain ⟨-, hu, -⟩ := spec
      show (⋃ i, emb e '' (Classical.choose L52.A1_orbits i)) =
        ((tr e L52.A1 : Subgroup G) : Set G) \ {1}
      rw [← Set.image_iUnion, hu, Set.image_diff (emb_injective e), Set.image_singleton, map_one]
      rfl
    Δ_inv := by
      obtain ⟨-, -, hinv, -⟩ := spec
      rintro i _ ⟨a', ha', rfl⟩ x ⟨hxz, hxN⟩
      obtain ⟨x', rfl⟩ := exists_emb e hxz
      have hx' : x' ∈ L52.NH1 := by
        rw [← L52.normalizer_A1_eq]
        exact (emb_mem_normalizer_tr e).1 hxN
      exact ⟨x'⁻¹ * a' * x', hinv i a' ha' x' hx', by rw [emb_conj]⟩
    Δ_trans := by
      obtain ⟨-, -, -, htr, -⟩ := spec
      rintro i _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
      obtain ⟨x', hx', hb⟩ := htr i a' ha' b' hb'
      refine ⟨emb e x', ⟨emb_mem_Cz e x', ?_⟩, ?_⟩
      · apply (emb_mem_normalizer_tr e (X := L52.A1)).2
        rw [L52.normalizer_A1_eq]
        exact hx'
      · rw [hb, emb_conj]
    Δ_card := by
      obtain ⟨-, -, -, -, hc, -⟩ := spec
      intro i
      rw [Set.ncard_image_of_injective _ (emb_injective e), hc i]
      rfl
    Δ0 := by
      obtain ⟨-, -, -, -, -, h0, -⟩ := spec
      show emb e '' (Classical.choose L52.A1_orbits 0) = {z}
      rw [h0, Set.image_singleton, emb_zt e hz]
    Δ1 := by
      obtain ⟨-, -, -, -, -, -, h1, -⟩ := spec
      show emb e '' (Classical.choose L52.A1_orbits 1) =
        ((tr e L52.A1 ⊓ tr e L52.U1 : Subgroup G) : Set G) \ {1, z}
      rw [h1, Set.image_diff (emb_injective e), Set.image_pair, map_one, emb_zt e hz, ← tr_inf]
      rfl
    Δ2_sub := by
      obtain ⟨-, -, -, -, -, -, -, h2, -⟩ := spec
      rintro _ ⟨a', ha', rfl⟩
      rw [h2] at ha'
      obtain ⟨ha1, ha2⟩ := ha'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ha2
      refine ⟨emb_mem_tr e (Subgroup.mem_inf.1 ha1).2,
        fun h => ha2.1 (emb_injective e (by rw [h, map_one])),
        fun h => ha2.2 (emb_injective e (by rw [h, emb_zt e hz]))⟩
    Δ3_sub := by
      obtain ⟨-, -, -, -, -, -, -, -, h3⟩ := spec
      rintro _ ⟨a', ha', rfl⟩
      rw [h3] at ha'
      obtain ⟨haA, haQ, ha1, haU1, haU2⟩ := ha'
      refine ⟨a', ⟨haQ, ?_, ha1, haU1, haU2⟩, rfl⟩
      rw [← sq]
      exact L52.isElemAbelian_A1.2 a' haA }

end CFSG.Quasithin.A94
