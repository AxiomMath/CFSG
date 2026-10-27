module

public import CFSG.Quasithin.Recognition.J2RecEndgame
public import CFSG.Timmesfeld.Moufang.J2

public section

namespace CFSG.Quasithin

open CFSG.Timmesfeld.Moufang

theorem j2LineEndgame :
    J2LineEndgame := by
  intro H _ d c x h1 h2
  have hd : d ∈ Subgroup.closure (insert d (insert c (Set.range x))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hc : c ∈ Subgroup.closure (insert d (insert c (Set.range x))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hx : ∀ i, x i ∈ Subgroup.closure (insert d (insert c (Set.range x))) := fun i =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  have hcfg : LineConfig (G := Subgroup.closure (insert d (insert c (Set.range x))))
      ⟨d, hd⟩ ⟨c, hc⟩ (fun i => ⟨x i, hx i⟩) := by
    refine ⟨Subtype.ext h1.d_sq, Subtype.ext h2.c_sq, fun i => Subtype.ext (h1.x_sq i),
      Subtype.ext (by simpa using h2.dc_pow), fun i => Subtype.ext (h1.d_comm i).eq,
      fun i j hij => Subtype.ext (by simpa using h1.sq_eq i j hij),
      fun i => Subtype.ext (by simpa using h2.cx_pow i),
      fun i => Subtype.ext (by simpa using h2.cdx_pow i)⟩
  have hprod : (⟨x 0, hx 0⟩ : Subgroup.closure (insert d (insert c (Set.range x)))) *
      ⟨x 1, hx 1⟩ * ⟨x 2, hx 2⟩ * ⟨x 3, hx 3⟩ * ⟨x 4, hx 4⟩ = 1 := Subtype.ext h1.prod_eq
  have hdc : (⟨d, hd⟩ : Subgroup.closure (insert d (insert c (Set.range x)))) * ⟨c, hc⟩ ≠ 1 :=
    fun h => h2.dc_ne (congrArg Subtype.val h)
  have hgen : Subgroup.closure (insert (⟨d, hd⟩ : Subgroup.closure (insert d (insert c
      (Set.range x)))) (insert ⟨c, hc⟩ (Set.range fun i => ⟨x i, hx i⟩))) = ⊤ := by
    rw [← Subgroup.closure_closure_coe_preimage (k := insert d (insert c (Set.range x)))]
    congr 1
    ext y
    simp only [Set.mem_insert_iff, Set.mem_range, Set.mem_preimage]
    constructor
    · rintro (h | h | ⟨i, h⟩)
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr ⟨i, by rw [← h]⟩)
    · rintro (h | h | ⟨i, h⟩)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr ⟨i, Subtype.ext h⟩)
  obtain ⟨-, ⟨e⟩⟩ := j2Endgame _ _ _ _ hcfg hprod hdc hgen
  exact ⟨e⟩

end CFSG.Quasithin
