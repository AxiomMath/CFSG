module

public import CFSG.Milestones.ASVolI.F411.KeyGen
public import CFSG.Milestones.ASVolI.F411.SpOddT
public import CFSG.Milestones.ASVolI.F411.Main
import all CFSG.Milestones.ASVolI.F4
import all CFSG.RankThree.PartOne.AUTSL.SpTwoCenter

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.AUTSL.SpTwo

section Model

variable {K : Type} [Field K]

theorem burnsideF411_projStab_inf :
    projStabilizer 2 K (flag 2 K 1) ⊓ projStabilizer 2 K (flag 2 K 2) = projBorel 2 K := by
  rw [projStabilizer, projStabilizer, ← burnsideF4h_cl_map_inf_of_ker_le _ (by
    rw [ker_proj]; exact spScalars_le_stabilizer _), burnsideF4h_cl_sp_stab_inf]
  rfl

theorem burnsideF411_projUnipotent_le_projBorel : projUnipotent 2 K ≤ projBorel 2 K :=
  Subgroup.map_mono unipotent_le_borelSubgroup

theorem burnsideF411_projBorel_le_normalizer :
    projBorel 2 K ≤ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
  have hn := (unipotent_subgroupOf_borelSubgroup_normal (r := 2) (K := K))
  refine burnsideF411_le_normalizer ?_
  rintro _ ⟨b, hb, rfl⟩ _ ⟨u, hu, rfl⟩
  have h1 : (⟨b, hb⟩ : borelSubgroup 2 K) * ⟨u, unipotent_le_borelSubgroup hu⟩ *
      (⟨b, hb⟩ : borelSubgroup 2 K)⁻¹ ∈ (unipotent 2 K).subgroupOf (borelSubgroup 2 K) :=
    hn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hu) _
  refine ⟨b * u * b⁻¹, Subgroup.mem_subgroupOf.mp h1, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem burnsideF411_pCoreOf_projBorel [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    pCoreOf p (projBorel 2 K) = projUnipotent 2 K := by
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnipotent (K := K) p (r := 2) (by norm_num)
  apply le_antisymm
  ·
    have hSB : (SU : Subgroup (StatedProj (StatedSp 2 K))) ≤ projBorel 2 K :=
      hSU ▸ burnsideF411_projUnipotent_le_projBorel
    haveI := CFSG.LieType.BorelTits.pCore_normal p (G := ↥(projBorel 2 K))
    have hle := (CFSG.LieType.BorelTits.pCore_isPGroup p (G := ↥(projBorel 2 K))).le_sylow_of_normal
      (SU.subtype hSB)
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hle hx
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, hSU] at hx'
    exact hx'
  · refine burnsideF411_le_pCoreOf burnsideF411_projUnipotent_le_projBorel
      burnsideF411_projBorel_le_normalizer ?_
    rw [← hSU]
    exact SU.isPGroup'

theorem burnsideF411_proj_dt_mem (t : Kˣ) : proj 2 K (burnsideF411_dt t) ∈ projBorel 2 K :=
  ⟨_, torus_le_borelSubgroup ⟨_, rfl⟩, rfl⟩

private theorem burnsideF411_ctr_projUnipotent : burnsideF411_ctr (projUnipotent 2 K) = Z0 K := rfl

end Model

section Transport

variable {G H : Type} [Group G] [Group H]

theorem burnsideF411_pCoreOf_map_injective {f : G →* H} (hf : Function.Injective f) (p : ℕ)
    (X : Subgroup G) : pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem burnsideF411_ctr_map_injective {f : G →* H} (hf : Function.Injective f) (X : Subgroup G) :
    burnsideF411_ctr (X.map f) = (burnsideF411_ctr X).map f := by
  ext y
  rw [burnsideF411_mem_ctr]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, burnsideF411_mem_ctr.mpr ⟨hx, fun h hh => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc (f h) ⟨h, hh, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxX, hxc⟩ := burnsideF411_mem_ctr.mp hx
    refine ⟨⟨x, hxX, rfl⟩, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hxc h hh]

theorem burnsideF411_map_conj_eq {X : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (X : Set G)) : X.map (MulAut.conj r).toMonoidHom = X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hr y).mp hy
  · intro hx
    refine ⟨r⁻¹ * x * r, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr) x).mp hx
    simpa using this

end Transport

private theorem burnsideF411_sp4_marking_parabolic {p f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .Sp4 p f H) (b : Bool) :
    marking.parabolic b =
      (projStabilizer 2 marking.field (flag 2 marking.field (if b then 2 else 1))).map
        (marking.identification : StatedProj (StatedSp 2 marking.field) ≃* H).toMonoidHom := by
  set K := marking.field
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have keym : ∀ (b : Bool) (x : StatedSp 2 K),
      x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ f) K marking.basis b ↔
        x ∈ stabilizer 2 K (flag 2 K (if b then 2 else 1)) := by
    intro b x
    rw [hbasis]
    have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ f) K 1 b ↔
        (x : GL (ChF.ClassicalRoots.Coord .Sp4) K) ∈ ChF.ClassicalRoots.rawStabilizer
          ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .Sp4) K) :
            Matrix (ChF.ClassicalRoots.Coord .Sp4) (ChF.ClassicalRoots.Coord .Sp4) K).mulVec
              vector) ''
            ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .Sp4
              else ChF.ClassicalRoots.flagOne .Sp4)) :=
      Iff.rfl
    rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
      burnsideF4h_cl_map_eq_iff _
        (C := (((x⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        (by rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one])
        (by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one])]
    simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
    cases b
    · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sp_coordinateSpace _).1, (burnsideF4h_cl_sp_coordinateSpace _).1]
    · simp only [if_true, ChF.ClassicalRoots.flagTwo]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sp_coordinateSpace _).2, (burnsideF4h_cl_sp_coordinateSpace _).2]
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨proj 2 K x, ⟨x, (keym b x).1 hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, (keym b x).2 hx, rfl⟩

theorem burnsideF411_sp4_chart {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 p f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : StatedProj (StatedSp 2 K) ≃* ↥Gp),
      Nat.card K = p ^ f ∧
      Gp ⊓ M₁ = (projStabilizer 2 K (flag 2 K 1)).map (Gp.subtype.comp e.toMonoidHom) ∧
      Gp ⊓ M₂ = (projStabilizer 2 K (flag 2 K 2)).map (Gp.subtype.comp e.toMonoidHom) ∧
      IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨chart, hB, hP1, hP2⟩ := hyp.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  rotate_left
  iterate 5 exact absurd hk (by decide)
  have hc : c = .Sp4 := by cases c <;> first | rfl | exact absurd hk (by decide)
  subst hc
  haveI : Fact p.Prime := ⟨marking.prime⟩
  set K := marking.field
  have hK : Nat.card K = p ^ f := by simpa using marking.field_card
  let e : StatedProj (StatedSp 2 K) ≃* ↥Gp := marking.identification
  have hcl := (burnsideF4h_cl_Sp4 p f ↥Gp marking).1
  have hmap := burnsideF4h_isLieParabolics_map Gp.subtype Gp.subtype_injective hcl
  rw [burnsideF4h_map_subtype_top, ← h1, ← h2, ← h3, ← hB, ← hP1, ← hP2] at hmap
  have hpar := burnsideF411_sp4_marking_parabolic marking
  refine ⟨K, inferInstance, inferInstance, e, hK, ?_, ?_, hmap⟩
  · rw [hP1, h2, hpar false]
    exact Subgroup.map_map _ _ _
  · rw [hP2, h3, hpar true]
    exact Subgroup.map_map _ _ _

theorem burnsideF411_key_Sp4_odd {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 p f Gp M₁ M₂) (hp2 : p ≠ 2) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ (p ^ k) = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hrk hcomm
  haveI : Finite E := hyp.finite
  haveI := hyp.normal
  have hp : p.Prime := hyp.model.1
  have hf : 1 ≤ f := hyp.model.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, e, hK, hG1, hG2, hP⟩ := burnsideF411_sp4_chart hyp
  haveI : CharP K p := burnsideF4h_cl_charP hK
  set Ψ : StatedProj (StatedSp 2 K) →* E := Gp.subtype.comp e.toMonoidHom with hΨdef
  have hΨ : Function.Injective Ψ := Gp.subtype_injective.comp e.injective
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (projBorel 2 K).map Ψ := by
    rw [← hP.2.2.1, hG1, hG2, ← Subgroup.map_inf_eq _ _ Ψ hΨ, burnsideF411_projStab_inf]
  have hU : pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) = (projUnipotent 2 K).map Ψ := by
    rw [hGB, burnsideF411_pCoreOf_map_injective hΨ, burnsideF411_pCoreOf_projBorel]
  let β : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr e.symm (MulAut.conjNormal r)
  have hβΨ : ∀ x, Ψ (β x) = r * Ψ x * r⁻¹ := by
    intro x
    show ((e (e.symm (MulAut.conjNormal r (e x))) : ↥Gp) : E) = r * ((e x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
  have hβcomp : Ψ.comp β.toMonoidHom = (MulAut.conj r).toMonoidHom.comp Ψ :=
    MonoidHom.ext fun x => (hβΨ x).trans (by rw [MonoidHom.comp_apply]; rfl)
  have hβk : β ^ (p ^ k) = 1 := by
    have h1 : (MulAut.conjNormal r : MulAut ↥Gp) ^ (p ^ k) = 1 := by
      rw [← map_pow, hrk, map_one]
    show (MulAut.congr e.symm (MulAut.conjNormal r)) ^ (p ^ k) = 1
    rw [← map_pow, h1, map_one]
  have hmapβ : ∀ X : Subgroup (StatedProj (StatedSp 2 K)), r ∈ Subgroup.normalizer
      ((X.map Ψ : Subgroup E) : Set E) → X.map β.toMonoidHom = X := by
    intro X hX
    apply Subgroup.map_injective hΨ
    rw [Subgroup.map_map, hβcomp, ← Subgroup.map_map, burnsideF411_map_conj_eq hX]
  have hr1 : r ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) := by
    rw [inf_comm]
    exact burnsideF411_le_normalizer_inf hyp.normal M₁ hr.1
  have hr2 : r ∈ Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) := by
    rw [inf_comm]
    exact burnsideF411_le_normalizer_inf hyp.normal M₂ hr.2
  have h1 : (projStabilizer 2 K (flag 2 K 1)).map β.toMonoidHom =
      projStabilizer 2 K (flag 2 K 1) := by
    refine hmapβ _ ?_
    rw [← hG1]
    exact hr1
  have h2 : (projStabilizer 2 K (flag 2 K 2)).map β.toMonoidHom =
      projStabilizer 2 K (flag 2 K 2) := by
    refine hmapβ _ ?_
    rw [← hG2]
    exact hr2
  have hT : ∀ t : Kˣ, β (proj 2 K (burnsideF411_dt t)) * (proj 2 K (burnsideF411_dt t))⁻¹ ∈
      projUnipotent 2 K := by
    intro t
    set h := proj 2 K (burnsideF411_dt t) with hh
    have hb : Ψ h ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hGB]
      exact ⟨h, burnsideF411_proj_dt_mem t, rfl⟩
    have hc := hcomm (Ψ h) hb
    rw [hU] at hc
    have e1 : Ψ (β h * h⁻¹) = r * Ψ h * r⁻¹ * (Ψ h)⁻¹ := by rw [map_mul, map_inv, hβΨ]
    rw [← e1] at hc
    exact (Subgroup.mem_map_iff_mem hΨ).mp hc
  obtain ⟨g, hg⟩ := burnsideF411_sp4_inner_of_torus hp hp2 hf hK β k hβk h1 h2 hT
  have hcent : (Ψ g)⁻¹ * r ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    have hyx : y = Ψ x := by
      show y = ((e x : ↥Gp) : E)
      rw [hx]
    have h3 : Ψ (β x) = Ψ (g * x * g⁻¹) := by rw [hg]; rfl
    rw [hβΨ, map_mul, map_mul, map_inv] at h3
    rw [hyx]
    calc Ψ x * ((Ψ g)⁻¹ * r) = (Ψ g)⁻¹ * (Ψ g * Ψ x * (Ψ g)⁻¹) * r := by group
      _ = (Ψ g)⁻¹ * (r * Ψ x * r⁻¹) * r := by rw [← h3]
      _ = (Ψ g)⁻¹ * r * Ψ x := by group
  rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcent
  have hrg : r = Ψ g := by
    have := congrArg (fun z => Ψ g * z) hcent
    simpa using this
  rw [hrg]
  exact (e g).2

theorem burnsideF411_swap_Sp4_odd {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 p f Gp M₁ M₂) (hp2 : p ≠ 2) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  have hp : p.Prime := hyp.model.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, e, hK, hG1, hG2, hP⟩ := burnsideF411_sp4_chart hyp
  haveI : CharP K p := burnsideF4h_cl_charP hK
  have h2K : (2 : K) ≠ 0 := by
    intro h0
    have h1' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h1'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1')
  set Ψ : StatedProj (StatedSp 2 K) →* E := Gp.subtype.comp e.toMonoidHom with hΨdef
  have hΨ : Function.Injective Ψ := Gp.subtype_injective.comp e.injective
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (projBorel 2 K).map Ψ := by
    rw [← hP.2.2.1, hG1, hG2, ← Subgroup.map_inf_eq _ _ Ψ hΨ, burnsideF411_projStab_inf]
  have hU : pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) = (projUnipotent 2 K).map Ψ := by
    rw [hGB, burnsideF411_pCoreOf_map_injective hΨ, burnsideF411_pCoreOf_projBorel]
  obtain ⟨T, hTp, hTi, hT⟩ := burnsideF411_exists_sylow_inf hyp.normal hyp.split hP
  have hB := burnsideF411_pCoreOf_eq_of_key hyp.normal hTp hTi hT
    (burnsideF411_key_Sp4_odd hyp hp2) le_rfl
  have hBT : burnsideF411_BorelTitsIn p Gp := burnsideF411_borelTitsIn_of_holds
    ((CFSG.LieType.BorelTits.holds_statedProj_statedSp (n := 2) (K := K) p).of_mulEquiv e)
  refine burnsideF411_swap_of_center hyp.normal hyp.split hP hBT hB ?_
  rw [hU, burnsideF411_ctr_map_injective hΨ, burnsideF411_ctr_projUnipotent, hG1]
  exact (Subgroup.map_mono (normalizer_Z0 h2K).ge).trans (Subgroup.le_normalizer_map _)

end CFSG.ASVolI
