module

public import CFSG.Quasithin.Recognition.RuRank3Defs

public section

namespace CFSG.Quasithin.RuRank3

open MulAction

section Invariance

variable {X Y : Type*} [Group X] [Group Y]

theorem IsL225Plus.of_mulEquiv (e : X ≃* Y) (h : IsL225Plus X) : IsL225Plus Y := by
  obtain ⟨K, hK, hidx, ⟨f⟩, hC, hS⟩ := h
  refine ⟨K.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact hK.map _ e.surjective
  · exact (Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective K).trans hidx
  · exact ⟨(Subgroup.equivMapOfInjective K e.toMonoidHom e.injective).symm.trans f⟩
  · rw [eq_bot_iff]
    intro y hy
    have hy' : e.symm y ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := (Subgroup.mem_centralizer_iff.1 hy) (e k) ⟨k, hk, rfl⟩
      apply e.injective
      simpa [map_mul] using this
    rw [hC, Subgroup.mem_bot] at hy'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hy'
  · intro S
    have hle : (S : Subgroup Y) ≤ e.toMonoidHom.range := by
      rw [MonoidHom.range_eq_top_of_surjective _ e.surjective]
      exact le_top
    have hinj : Function.Injective e.toMonoidHom := fun a b h => e.injective h
    obtain ⟨f⟩ := hS (S.comapOfInjective e.toMonoidHom hinj hle)
    have hmap : ((S.comapOfInjective e.toMonoidHom hinj hle : Sylow 2 X) :
        Subgroup X).map e.toMonoidHom = S := by
      change ((S : Subgroup Y).comap e.toMonoidHom).map e.toMonoidHom = S
      exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
    exact ⟨f.trans ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap))⟩

theorem IsSylowTwoParabolic.map_mulEquiv (e : X ≃* Y) {P : Subgroup X}
    (h : IsSylowTwoParabolic P) : IsSylowTwoParabolic (P.map e.toMonoidHom) := by
  obtain ⟨S, hS⟩ := h
  have hle : (S : Subgroup X) ≤ e.symm.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top_of_surjective _ e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := fun a b h => e.symm.injective h
  refine ⟨S.comapOfInjective e.symm.toMonoidHom hinj hle, ?_⟩
  intro y hy
  refine ⟨e.symm y, ?_, by simp⟩
  apply hS
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro s
  have hmem : ∀ x : X, x ∈ (S : Subgroup X) ↔
      e x ∈ ((S.comapOfInjective e.symm.toMonoidHom hinj hle : Sylow 2 Y) :
        Subgroup Y) := by
    intro x
    change x ∈ (S : Subgroup X) ↔ e x ∈ (S : Subgroup X).comap e.symm.toMonoidHom
    rw [Subgroup.mem_comap]
    simp
  have key := hy (e s)
  rw [hmem s, hmem (e.symm y * s * (e.symm y)⁻¹)]
  simpa [map_mul, map_inv] using key

end Invariance

section Conj

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] noncomputable def stabilizerConj (g : G) (ω : Ω) :
    stabilizer G ω ≃* stabilizer G (g • ω) :=
  stabilizerEquivStabilizer rfl

theorem stabilizerConj_apply (g : G) (ω : Ω) (f : stabilizer G ω) :
    ((stabilizerConj g ω f : stabilizer G (g • ω)) : G) = g * f * g⁻¹ := by
  rfl

theorem stabilizerConj_smul (g : G) (ω : Ω) (f : stabilizer G ω) (x : Ω) :
    stabilizerConj g ω f • (g • x) = g • (f • x) := by
  show ((stabilizerConj g ω f : stabilizer G (g • ω)) : G) • (g • x) = g • ((f : G) • x)
  rw [stabilizerConj_apply, smul_smul, smul_smul, inv_mul_cancel_right]

theorem map_stabilizerConj_stabilizer (g : G) (ω : Ω) (x : Ω) :
    (stabilizer (stabilizer G ω) x).map (stabilizerConj g ω).toMonoidHom =
      stabilizer (stabilizer G (g • ω)) (g • x) := by
  ext f'
  rw [Subgroup.mem_map, mem_stabilizer_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_stabilizer_iff] at hf
    rw [MulEquiv.coe_toMonoidHom, stabilizerConj_smul, hf]
  · intro hf'
    refine ⟨(stabilizerConj g ω).symm f', ?_, by simp⟩
    rw [mem_stabilizer_iff]
    have h := stabilizerConj_smul g ω ((stabilizerConj g ω).symm f') x
    rw [MulEquiv.apply_symm_apply, hf'] at h
    exact (smul_left_cancel g h).symm

theorem orbitRel_stabilizer_smul_iff (g : G) (ω : Ω) (x y : Ω) :
    orbitRel (stabilizer G (g • ω)) Ω (g • x) (g • y) ↔ orbitRel (stabilizer G ω) Ω x y := by
  rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨f', hf'⟩
    refine ⟨(stabilizerConj g ω).symm f', ?_⟩
    have h := stabilizerConj_smul g ω ((stabilizerConj g ω).symm f') y
    rw [MulEquiv.apply_symm_apply, hf'] at h
    exact (smul_left_cancel g h).symm
  · rintro ⟨f, hf⟩
    exact ⟨stabilizerConj g ω f, by rw [stabilizerConj_smul, hf]⟩

noncomputable def orbitRelQuotientSmulEquiv (g : G) (ω : Ω) :
    orbitRel.Quotient (stabilizer G ω) Ω ≃ orbitRel.Quotient (stabilizer G (g • ω)) Ω :=
  Quotient.congr (MulAction.toPerm g) fun x y => (orbitRel_stabilizer_smul_iff g ω x y).symm

theorem card_orbitRel_quotient_stabilizer_smul (g : G) (ω : Ω) :
    Nat.card (orbitRel.Quotient (stabilizer G (g • ω)) Ω) =
      Nat.card (orbitRel.Quotient (stabilizer G ω) Ω) :=
  (Nat.card_congr (orbitRelQuotientSmulEquiv g ω)).symm

end Conj

theorem IsRudvalisRank3.of_point {G Ω : Type*} [Group G] [MulAction G Ω]
    (hfaith : FaithfulSMul G Ω) (htrans : IsPretransitive G Ω) (ω : Ω)
    (hrank : Nat.card (orbitRel.Quotient (stabilizer G ω) Ω) = 3)
    (htwoF4 : Nonempty (stabilizer G ω ≃* CFSG.Sporadic.Schreier.Tits.titsA))
    (hpar : ∃ δ : Ω, Nat.card (stabilizer (stabilizer G ω) δ) = 2 ^ 12 * 5 ∧
      IsSylowTwoParabolic (stabilizer (stabilizer G ω) δ))
    (hl : ∃ γ : Ω, IsL225Plus (stabilizer (stabilizer G ω) γ)) : IsRudvalisRank3 G Ω := by
  have key : ∀ ω' : Ω, ∃ g : G, g • ω = ω' := fun ω' => exists_smul_eq G ω ω'
  refine ⟨hfaith, ⟨ω⟩, htrans, fun ω' => ?_, fun ω' => ?_, fun ω' => ?_, fun ω' => ?_⟩
  · obtain ⟨g, rfl⟩ := key ω'
    rw [card_orbitRel_quotient_stabilizer_smul, hrank]
  · obtain ⟨g, rfl⟩ := key ω'
    obtain ⟨e⟩ := htwoF4
    exact ⟨(stabilizerConj g ω).symm.trans e⟩
  · obtain ⟨g, rfl⟩ := key ω'
    obtain ⟨δ, hcard, hP⟩ := hpar
    refine ⟨g • δ, ?_, ?_⟩
    · rw [← map_stabilizerConj_stabilizer, ← hcard]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (stabilizerConj g ω).injective).toEquiv.symm
    · rw [← map_stabilizerConj_stabilizer]
      exact hP.map_mulEquiv (stabilizerConj g ω)
  · obtain ⟨g, rfl⟩ := key ω'
    obtain ⟨γ, hγ⟩ := hl
    refine ⟨g • γ, ?_⟩
    rw [← map_stabilizerConj_stabilizer]
    exact hγ.of_mulEquiv (Subgroup.equivMapOfInjective _ _ (stabilizerConj g ω).injective)

end CFSG.Quasithin.RuRank3
