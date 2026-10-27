module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.Quasithin.H13.NQCatLieCartan
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs

public section

namespace CFSG.Quasithin.H13.NQCat.D4Center

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open scoped commutatorElement

section Center

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_ox₆_of_mem_center_a0
    (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    {z : ModGL TwistTag.D4.tag K}
    (hz : z ∈ Q0 σ ⊓ Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K))) :
    ∃ f : trialityFixedField K σ.toRingHom, z = ox₆ σ f := by
  obtain ⟨hzQ, hzC⟩ := hz
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_radical_a0_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q0 σ,
      ⁅ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hb : b = 0 := by
    have h1 := hcent _ (ox₅_mem_Q0 σ hσ3 (1 : trialityFixedField K σ.toRingHom))
    have e1 : ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₂ σ b * (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₅ σ 1) :=
      (((comm35 σ hσ3 c 1).mul_left (comm45 σ hσ3 d 1)).mul_left
        (commute_of_add (ox₅ σ) (ox₅_add σ hσ3) e 1)).mul_left (comm56 σ hσ3 1 f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), rel25 σ hσ3] at h1
    have := ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
    exact (mul_one b).symm.trans this
  subst hb
  have hc : c = 0 := by
    apply trace_nondeg σ hσ3
    intro t
    have h1 := hcent _ (ox₄_mem_Q0 σ hσ3 t)
    have e1 : ox₂ σ 0 * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        ox₂ σ 0 * ox₃ σ c * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0) (ox₄ σ t) := comm24 σ hσ3 0 t
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    have hAy : Commute (ox₂ σ 0) ⁅ox₃ σ c, ox₄ σ t⁆ := by
      rw [rel34 σ hσ3]; exact comm26 σ hσ3 0 _
    rw [e1, comm_sandwich hA hB hAy, rel34 σ hσ3] at h1
    exact ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₃_mem_Q0 σ hσ3 s)
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0) * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0) (ox₃ σ s) :=
      (comm23 σ hσ3 0 s).mul_left (commute_of_add (ox₃ σ) (ox₃_add σ hσ3) 0 s)
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₃ σ s) :=
      (comm35 σ hσ3 s e).symm.mul_left (comm36 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₃ σ s⁆ =
        (ox₆ σ (trialityTrace K σ.toRingHom hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel34 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0) ⁅ox₄ σ d, ox₃ σ s⁆ := by
      rw [hinv]
      exact ((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (trialityTrace K σ.toRingHom hσ3 (s * d)) = 1 := inv_eq_one.1 h1
    exact ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
  subst hd
  have he : e = 0 := by
    have h1 := hcent _ (ox₂_mem_Q0 σ hσ3 (1 : trialityFixedField K σ.toRingHom))
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) * ox₅ σ e * ox₆ σ f := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) (ox₂ σ 1) :=
      (((commute_of_add (ox₂ σ) (ox₂_add σ hσ3) 0 1).mul_left (comm23 σ hσ3 1 0).symm).mul_left
        (comm24 σ hσ3 1 0).symm)
    have hB : Commute (ox₆ σ f) (ox₂ σ 1) := (comm26 σ hσ3 1 f).symm
    have hinv : ⁅ox₅ σ e, ox₂ σ 1⁆ = (ox₆ σ (1 * e))⁻¹ := by
      rw [← commutatorElement_inv, rel25 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) ⁅ox₅ σ e, ox₂ σ 1⁆ := by
      rw [hinv]
      exact (((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).mul_left
        (comm46 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (1 * e) = 1 := inv_eq_one.1 h1
    have := ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
    exact (one_mul e).symm.trans this
  subst he
  refine ⟨f, ?_⟩
  rw [ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3]
  simp

theorem card_le_of_le_centralizer_graphFixedPosUnipotent
    (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hEU : E ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hEC : E ≤ Subgroup.centralizer
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K))) :
    Nat.card E ≤ Nat.card (trialityFixedField K σ.toRingHom) := by
  obtain ⟨-, -, -, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hUP : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ P0 σ :=
    graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hQU : Q0 σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedPosUnipotent _
  have hb : ∀ x : E, ∃ f : trialityFixedField K σ.toRingHom,
      (x : ModGL TwistTag.D4.tag K) = ox₆ σ f := fun x => by
    have hxC : (x : ModGL TwistTag.D4.tag K) ∈
        Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) :=
      Subgroup.centralizer_le hQU (hEC x.2)
    exact eq_ox₆_of_mem_center_a0 σ hσ3 ⟨hsc ⟨hUP (hEU x.2), hxC⟩, hxC⟩
  choose β hβ using hb
  exact Nat.card_le_card_of_injective β fun x y hxy => Subtype.ext (by rw [hβ x, hβ y, hxy])

end Center

theorem isCyclic_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    IsCyclic G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2) with h1 | h2
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2

theorem isCyclic_center_sylow_of_triality_two :
    ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .trialityD4 2 1 →
      ∀ T : Sylow 2 X, IsCyclic (Subgroup.center ↥(T : Subgroup X)) := by
  intro X _ _ hX T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hm⟩ := hX
  obtain ⟨K, _, _, _, σ, hσ3, -, -, hk, ⟨e⟩⟩ := TrialityCover.triality_model le_rfl hm
  have hσ3' : σ.toRingHom ^ 3 = 1 := by
    ext c
    have h := DFunLike.congr_fun hσ3 c
    simpa [pow_succ] using h
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : U ≤ C := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf U C := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hT' : IsSylowTwoOf ((T : Subgroup X).map e.toMonoidHom) ⊤ :=
    LieCartan.isSylowTwoOf_top_map_equiv e (isSylowTwoOf_top_of_sylow T)
  obtain ⟨g, -, hg⟩ := hU₀.exists_conj hT'
  let φ : ↥(T : Subgroup X) ≃* ↥(U.subgroupOf C) :=
    (((T : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hg)).trans
      ((U.subgroupOf C).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  apply isCyclic_of_card_le_two
  rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv]
  set Z := ((Subgroup.center ↥(U.subgroupOf C)).map (U.subgroupOf C).subtype).map C.subtype
    with hZ
  have hZcard : Nat.card Z = Nat.card (Subgroup.center ↥(U.subgroupOf C)) := by
    rw [hZ, Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective (U.subgroupOf C).subtype_injective]
  have hZU : Z ≤ U := by
    rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
    exact z.2
  have hZC : Z ≤ Subgroup.centralizer (U : Set (ModGL TwistTag.D4.tag K)) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := Subgroup.mem_center_iff.mp hz ⟨⟨u, hUC hu⟩, hu⟩
    exact congrArg (fun w : ↥(U.subgroupOf C) => ((w : C) : ModGL TwistTag.D4.tag K)) h1
  have h1 := card_le_of_le_centralizer_graphFixedPosUnipotent σ hσ3' hZU hZC
  rw [hZcard, hk, pow_one] at h1
  exact h1

end CFSG.Quasithin.H13.NQCat.D4Center
