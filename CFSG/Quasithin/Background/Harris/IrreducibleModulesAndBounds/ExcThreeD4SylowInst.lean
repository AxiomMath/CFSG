module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4SylowRank
public import CFSG.Quasithin.Background.SmithB42D4Rel
public import CFSG.LieType.Chevalley.EvenTrialityOrbitParametrization
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators

public section

open scoped commutatorElement

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.B42D4
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

theorem commute_of_coe {G : Type*} [Group G] {H : Subgroup G} {a b : H}
    (h : (a : G) * b = b * a) : Commute a b :=
  Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact h)

theorem subgroup_coe_comm {G : Type*} [Group G] {H : Subgroup G} (a b : H) :
    ((⁅a, b⁆ : H) : G) = ⁅(a : G), (b : G)⁆ := by
  simp [commutatorElement_def]


theorem exists_d4Syl (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : σ.toRingHom ^ 3 = 1) :
    Nonempty (D4Syl K σ (trialityFixedField K σ.toRingHom)
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) := by
  obtain ⟨⟨f1, hi1, hf1⟩, ⟨f2, hi2, hf2⟩, ⟨f3, hi3, hf3⟩, ⟨f4, hi4, hf4⟩, ⟨f5, hi5, hf5⟩,
    ⟨f6, hi6, hf6⟩, hbij, -, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨t14, t34, t25, c15, c16, c23, c24, c26, c35, c36, c45, c46, c56, -, -⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  have hσ3' := sigma_sigma_sigma σ hσ3
  have hcomm : ∀ {a b : adjointGroup TwistTag.D4.tag K}, a * b = b * a →
      (a : ModGL TwistTag.D4.tag K) * b = b * a := fun h => congrArg Subtype.val h
  refine ⟨{
    Tr := trialityTrace K σ.toRingHom hσ3
    Nm := nrm σ hσ3
    x1 := fun a => f1 (Multiplicative.ofAdd a)
    x2 := fun a => f2 (Multiplicative.ofAdd a)
    x3 := fun a => f3 (Multiplicative.ofAdd a)
    x4 := fun a => f4 (Multiplicative.ofAdd a)
    x5 := fun a => f5 (Multiplicative.ofAdd a)
    x6 := fun a => f6 (Multiplicative.ofAdd a)
    two_eq_zero := by simpa using CharP.cast_eq_zero K 2
    hσ3 := hσ3'
    hk := fun c => Iff.rfl
    hTr := fun s => rfl
    hNm := fun s => rfl
    x1_add := fun a b => by rw [ofAdd_add, map_mul]
    x2_add := fun a b => by rw [ofAdd_add, map_mul]
    x3_add := fun a b => by rw [ofAdd_add, map_mul]
    x4_add := fun a b => by rw [ofAdd_add, map_mul]
    x5_add := fun a b => by rw [ofAdd_add, map_mul]
    x6_add := fun a b => by rw [ofAdd_add, map_mul]
    bij := ?_
    c15 := fun a b => ?_
    c16 := fun a b => ?_
    c23 := fun a b => ?_
    c24 := fun a b => ?_
    c26 := fun a b => ?_
    c35 := fun a b => ?_
    c36 := fun a b => ?_
    c45 := fun a b => ?_
    c46 := fun a b => ?_
    c56 := fun a b => ?_
    r14 := fun s t => ?_
    r34 := fun s t => ?_
    r25 := fun b e => ?_
    r21 := fun β s => ?_
    r13 := fun s t => ?_ }⟩
  ·
    have hGF : ∀ p : K × trialityFixedField K σ.toRingHom × K × K × trialityFixedField K σ.toRingHom ×
        trialityFixedField K σ.toRingHom,
        (((f1 (Multiplicative.ofAdd p.1) * (f2 (Multiplicative.ofAdd p.2.1) *
          (f3 (Multiplicative.ofAdd p.2.2.1) * (f4 (Multiplicative.ofAdd p.2.2.2.1) *
          (f5 (Multiplicative.ofAdd p.2.2.2.2.1) * f6 (Multiplicative.ofAdd p.2.2.2.2.2)))))) :
          graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        ((trialityX₁ K σ.toRingHom p.1 * trialityX₂ K σ.toRingHom p.2.1 *
        trialityX₃ K σ.toRingHom p.2.2.1 * trialityX₄ K σ.toRingHom p.2.2.2.1 *
        trialityX₅ K σ.toRingHom p.2.2.2.2.1 * trialityX₆ K σ.toRingHom p.2.2.2.2.2 :
          adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) := by
      intro p
      simp only [Subgroup.coe_mul, hf1, hf2, hf3, hf4, hf5, hf6, mul_assoc]
    refine ⟨fun p q hpq => hbij.injOn (Set.mem_univ p) (Set.mem_univ q) ?_, fun g => ?_⟩
    · have := congrArg Subtype.val hpq
      simp only at this
      rwa [hGF, hGF] at this
    · obtain ⟨p, -, hp⟩ := hbij.surjOn g.2
      exact ⟨p, Subtype.ext (by simp only; rw [hGF]; exact hp)⟩
  · exact commute_of_coe (by rw [hf1, hf5]; exact hcomm (c15 a b).eq)
  · exact commute_of_coe (by rw [hf1, hf6]; exact hcomm (c16 a b).eq)
  · exact commute_of_coe (by rw [hf2, hf3]; exact hcomm (c23 a b).eq)
  · exact commute_of_coe (by rw [hf2, hf4]; exact hcomm (c24 a b).eq)
  · exact commute_of_coe (by rw [hf2, hf6]; exact hcomm (c26 a b).eq)
  · exact commute_of_coe (by rw [hf3, hf5]; exact hcomm (c35 a b).eq)
  · exact commute_of_coe (by rw [hf3, hf6]; exact hcomm (c36 a b).eq)
  · exact commute_of_coe (by rw [hf4, hf5]; exact hcomm (c45 a b).eq)
  · exact commute_of_coe (by rw [hf4, hf6]; exact hcomm (c46 a b).eq)
  · exact commute_of_coe (by rw [hf5, hf6]; exact hcomm (c56 a b).eq)
  · refine Subtype.ext ?_
    rw [subgroup_coe_comm, hf1, hf4, hf5]
    have := congrArg Subtype.val (t14 s t)
    rwa [subgroup_coe_comm] at this
  · refine Subtype.ext ?_
    rw [subgroup_coe_comm, hf3, hf4, hf6]
    have := congrArg Subtype.val (t34 s t)
    rwa [subgroup_coe_comm] at this
  · refine Subtype.ext ?_
    rw [subgroup_coe_comm, hf2, hf5, hf6]
    have := congrArg Subtype.val (t25 b e)
    rwa [subgroup_coe_comm] at this
  · refine Subtype.ext ?_
    rw [subgroup_coe_comm, hf2, hf1]
    simp only [Subgroup.coe_mul, hf3, hf4, hf5, hf6]
    exact ox₂_comm_ox₁_gen σ hσ3 β s
  · refine Subtype.ext ?_
    rw [subgroup_coe_comm, hf1, hf3]
    simp only [Subgroup.coe_mul, hf4, hf5, hf6]
    exact ox₁_comm_ox₃ σ hσ3 s t

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
