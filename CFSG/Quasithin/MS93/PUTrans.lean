module

public import CFSG.Quasithin.MS93.PUEquiv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] noncomputable def transN (N : Subgroup A) : Vtx X → Subgroup X.Universal
  | .inl q => (N.map X.ofA).map (MulAut.conj q.out).toMonoidHom
  | .inr _ => ⊥

theorem PU.map_ofA_map_conj_ofA (N : Subgroup A) [hN : N.Normal] (a : A) :
    (N.map X.ofA).map (MulAut.conj (X.ofA a)).toMonoidHom = N.map X.ofA := by
  ext x
  rw [PU.mem_map_conj]
  constructor
  · rintro ⟨n, hn, hx⟩
    refine ⟨a * n * a⁻¹, hN.conj_mem n hn a, ?_⟩
    rw [map_mul, map_mul, map_inv, hx]
    group
  · rintro ⟨n, hn, rfl⟩
    exact ⟨a⁻¹ * n * a, by simpa using hN.conj_mem n hn a⁻¹, by simp [map_mul, map_inv]⟩

theorem transN_smul_baseA (N : Subgroup A) [N.Normal] (g : X.Universal) :
    transN X N (g • baseA X) = (N.map X.ofA).map (MulAut.conj g).toMonoidHom := by
  rw [smul_baseA]
  show (N.map X.ofA).map
    (MulAut.conj (Quotient.out (g : X.Universal ⧸ X.ofA.range))).toMonoidHom = _
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := QuotientGroup.mk_out_eq_mul X.ofA.range g
  rw [ha, PU.map_conj_mul, PU.map_ofA_map_conj_ofA]

theorem transN_smul_baseB (N : Subgroup A) (g : X.Universal) : transN X N (g • baseB X) = ⊥ := by
  rw [smul_baseB]
  rfl

theorem transN_baseA (N : Subgroup A) [N.Normal] : transN X N (baseA X) = N.map X.ofA := by
  have := transN_smul_baseA X N 1
  rwa [one_smul, PU.map_conj_one] at this

theorem transN_smul (N : Subgroup A) [N.Normal] (h : X.Universal) (α : Vtx X) :
    transN X N (h • α) = (transN X N α).map (MulAut.conj h).toMonoidHom := by
  by_cases hα : IsMVtx X α
  · obtain ⟨g, rfl⟩ := (PU.isMVtx_iff X).1 hα
    rw [smul_smul, transN_smul_baseA, transN_smul_baseA, PU.map_conj_mul]
  · obtain ⟨g, rfl⟩ := (PU.not_isMVtx_iff X).1 hα
    rw [smul_smul, transN_smul_baseB, transN_smul_baseB, Subgroup.map_bot]

theorem transN_le_stab (N : Subgroup A) (α : Vtx X) : transN X N α ≤ stab X α := by
  rcases α with q | q
  · have hq : (Sum.inl q : Vtx X) = q.out • baseA X := by
      rw [smul_baseA]
      exact congrArg Sum.inl (QuotientGroup.out_eq' q).symm
    show (N.map X.ofA).map (MulAut.conj q.out).toMonoidHom ≤ stab X (Sum.inl q)
    rw [hq, PU.stab_smul, stab, stabilizer_baseA]
    exact Subgroup.map_mono (Subgroup.map_le_range _ _)
  · exact bot_le

theorem stab_le_normalizer_transN (N : Subgroup A) [N.Normal] (α : Vtx X) :
    stab X α ≤ Subgroup.normalizer (transN X N α : Set X.Universal) :=
  PU.stab_le_normalizer_of_smul X (transN_smul X N) α

theorem transN_normal (N : Subgroup A) [N.Normal] (α : Vtx X) :
    ((transN X N α).subgroupOf (stab X α)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (transN_le_stab X N α)).2
    (stab_le_normalizer_transN X N α)

theorem transN_top {α : Vtx X} (hα : IsMVtx X α) : transN X ⊤ α = stab X α := by
  obtain ⟨g, rfl⟩ := (PU.isMVtx_iff X).1 hα
  rw [transN_smul_baseA, PU.stab_smul, stab, stabilizer_baseA, MonoidHom.range_eq_map]

theorem transN_mono {N N' : Subgroup A} (h : N ≤ N') (α : Vtx X) :
    transN X N α ≤ transN X N' α := by
  rcases α with q | q
  · exact Subgroup.map_mono (Subgroup.map_mono h)
  · exact le_rfl

theorem transN_inf (N N' : Subgroup A) (α : Vtx X) :
    transN X (N ⊓ N') α = transN X N α ⊓ transN X N' α := by
  rcases α with q | q
  · show ((N ⊓ N').map X.ofA).map (MulAut.conj q.out).toMonoidHom =
      (N.map X.ofA).map (MulAut.conj q.out).toMonoidHom ⊓
        (N'.map X.ofA).map (MulAut.conj q.out).toMonoidHom
    rw [Subgroup.map_inf _ _ _ X.ofA_injective,
      Subgroup.map_inf _ _ _ (MulAut.conj q.out).injective]
  · exact (inf_idem _).symm

theorem transN_bot (α : Vtx X) : transN X ⊥ α = ⊥ := by
  rcases α with q | q
  · show ((⊥ : Subgroup A).map X.ofA).map (MulAut.conj q.out).toMonoidHom = ⊥
    rw [Subgroup.map_bot, Subgroup.map_bot]
  · rfl

end CFSG.Quasithin.MS93
