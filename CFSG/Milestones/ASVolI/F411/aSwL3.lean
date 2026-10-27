module

public import CFSG.Milestones.ASVolI.F411.aSwCore
public import CFSG.Milestones.ASVolI.F411.aSwL3Aut
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

theorem burnsideF411a_swap_of_comm {E : Type} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp M₁ M₂ : Subgroup E} (hN : Gp.Normal) (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    (ζ : MulAut ↥Gp) (hcomm : ∀ α : MulAut ↥Gp, ∃ y : ↥Gp, ζ * α * ζ⁻¹ = MulAut.conj y * α)
    (hζ1 : ((Gp ⊓ M₁).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₂).subgroupOf Gp)
    (hζ2 : ((Gp ⊓ M₂).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₁).subgroupOf Gp) :
    burnsideF411_Swap M₁ M₂ := by
  haveI := hN
  have hM₁ := burnsideF411_eq_normalizer hN hsplit hP
  have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₂ ⊓ M₁, e = n * h := fun e => by
    obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
    exact ⟨n, hn, h, ⟨hh.2, hh.1⟩, rfl⟩
  have hM₂ := burnsideF411_eq_normalizer hN hsplit' (burnsideF411a_isLieParabolics_symm hP)
  refine burnsideF411_swap_of_aut hC hM₁ hM₂ ζ (fun e => ?_) hζ1 hζ2
  obtain ⟨y, hy⟩ := hcomm (MulAut.conjNormal e)
  refine ⟨(y : E) * e, ?_⟩
  rw [map_mul, MulAut.conjNormal_val, hy]

theorem burnsideF411a_comm_congr {G H : Type*} [Group G] [Group H] (χ : G ≃* H)
    (ζ₀ : MulAut G) (h : ∀ α : MulAut G, ∃ g : G, ζ₀ * α * ζ₀⁻¹ = MulAut.conj g * α) :
    ∀ α : MulAut H, ∃ y : H,
      MulAut.congr χ ζ₀ * α * (MulAut.congr χ ζ₀)⁻¹ = MulAut.conj y * α := by
  intro α
  obtain ⟨g, hg⟩ := h ((MulAut.congr χ).symm α)
  refine ⟨χ g, ?_⟩
  have h1 := congrArg (MulAut.congr χ) hg
  rw [map_mul, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply] at h1
  rw [h1]
  congr 1
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem burnsideF411a_L3_map_map_congr {G H : Type*} [Group G] [Group H] (χ : G ≃* H)
    (φ : MulAut G) (L : Subgroup G) :
    (L.map χ.toMonoidHom).map (MulAut.congr χ φ).toMonoidHom =
      (L.map φ.toMonoidHom).map χ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun x => by simp [MulAut.congr_apply]

theorem burnsideF411a_L3_chart {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : projectiveSL 3 K ≃* ↥Gp),
      p.Prime ∧ Nat.card K = p ^ f ∧
      Gp ⊓ M₁ = (projStabilizer (flagSpace 3 K 1)).map (Gp.subtype.comp e.toMonoidHom) ∧
      Gp ⊓ M₂ = (projStabilizer (flagSpace 3 K 2)).map (Gp.subtype.comp e.toMonoidHom) ∧
      IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨chart, hB, hP1, hP2⟩ := hyp.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  rotate_left
  iterate 5 exact absurd hk (by decide)
  have hc : c = .L3 := by cases c <;> first | rfl | exact absurd hk (by decide)
  subst hc
  haveI : Fact p.Prime := ⟨marking.prime⟩
  set K := marking.field
  have hK : Nat.card K = p ^ f := by simpa using marking.field_card
  haveI : CharP K p := burnsideF4h_cl_charP hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let s : Matrix.SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
    specialLinearGroupEquivStatedSL 3 K
  have keym : ∀ (b : Bool) (x : StatedSL 3 K),
      x ∈ ChF.ClassicalRoots.nativeParabolic .L3 (p ^ f) K marking.basis b ↔
        s.symm x ∈ stabilizer (flagSpace 3 K (if b then 2 else 1)) := by
    intro b x
    rw [hbasis]
    have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .L3 (p ^ f) K 1 b ↔
        (x : GL (ChF.ClassicalRoots.Coord .L3) K) ∈ ChF.ClassicalRoots.rawStabilizer
          ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .L3) K) :
            Matrix (ChF.ClassicalRoots.Coord .L3) (ChF.ClassicalRoots.Coord .L3) K).mulVec
              vector) ''
            ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .L3
              else ChF.ClassicalRoots.flagOne .L3)) :=
      Iff.rfl
    have hxu : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((s.symm x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      conv_lhs => rw [← s.apply_symm_apply x]
      rfl
    rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
      burnsideF4h_cl_map_eq_iff _
        (C := (((s.symm x)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (coe_inv_mul_coe _)
        (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one])]
    simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
    rw [hxu]
    cases b
    · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sl_coordinateSpace _).1, (burnsideF4h_cl_sl_coordinateSpace _).1]
    · simp only [if_true, ChF.ClassicalRoots.flagTwo]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sl_coordinateSpace _).2, (burnsideF4h_cl_sl_coordinateSpace _).2]
  let φ : projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    QuotientGroup.congr (scalars 3 K) ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) s
      (by rw [scalars_eq_center]; exact map_center_eq_statedScalars 3 K)
  let e : projectiveSL 3 K ≃* ↥Gp := φ.trans marking.identification
  have he : ∀ x : StatedSL 3 K, e (proj 3 K (s.symm x)) = marking.transport x := fun x =>
    congrArg marking.transport (s.apply_symm_apply x)
  have hpar : ∀ b : Bool, marking.parabolic b =
      (projStabilizer (flagSpace 3 K (if b then 2 else 1))).map e.toMonoidHom := by
    intro b
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨proj 3 K (s.symm x), ⟨s.symm x, (keym b x).1 hx, rfl⟩, he x⟩
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨s u, (keym b (s u)).2 (by rwa [MulEquiv.symm_apply_apply]), ?_⟩
      have := he (s u)
      rw [MulEquiv.symm_apply_apply] at this
      exact this.symm
  have hcl := burnsideF4h_cl_L3 p f ↥Gp marking
  have hmap := burnsideF4h_isLieParabolics_map Gp.subtype Gp.subtype_injective hcl
  rw [burnsideF4h_map_subtype_top, ← h1, ← h2, ← h3, ← hB, ← hP1, ← hP2] at hmap
  refine ⟨K, inferInstance, inferInstance, e, marking.prime, hK, ?_, ?_, hmap⟩
  · rw [hP1, h2, hpar false]
    exact Subgroup.map_map _ _ _
  · rw [hP2, h3, hpar true]
    exact Subgroup.map_map _ _ _

theorem burnsideF411a_swap_L3_of_mod {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hp : p % 3 ≠ 1) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  obtain ⟨K, fK, finK, e, hpr, hK, hP1, hP2, hP⟩ := burnsideF411a_L3_chart hyp
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI : CharP K p := burnsideF4h_cl_charP hK
  have hQ : ∀ (X : Subgroup E) (L : Subgroup (projectiveSL 3 K)),
      Gp ⊓ X = L.map (Gp.subtype.comp e.toMonoidHom) →
        (Gp ⊓ X).subgroupOf Gp = L.map e.toMonoidHom := by
    intro X L hX
    rw [hX, ← Subgroup.map_map]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hQ1 := hQ _ _ hP1
  have hQ2 := hQ _ _ hP2
  have hz1 := burnsideF411a_L3zeta_map_flag_one (K := K) (frobeniusEquiv K p)
  have hz2 := burnsideF411a_L3zeta_map_flag_two (K := K) (frobeniusEquiv K p)
  refine burnsideF411a_swap_of_comm hyp.normal hyp.centralizer_trivial hyp.split hP
    (MulAut.congr e (burnsideF411a_L3zeta K (frobeniusEquiv K p)))
    (burnsideF411a_comm_congr e _ (burnsideF411a_L3zeta_comm hp)) ?_ ?_
  · rw [hQ1, hQ2, burnsideF411a_L3_map_map_congr]
    exact congrArg (fun L => L.map e.toMonoidHom) hz1
  · rw [hQ1, hQ2, burnsideF411a_L3_map_map_congr]
    exact congrArg (fun L => L.map e.toMonoidHom) hz2


theorem burnsideF411a_swap_of_normalizing {E : Type} [Group E] [Finite E] {p : ℕ}
    [Fact p.Prime] {Gp M₁ M₂ : Subgroup E} (hN : Gp.Normal)
    (hC : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) (ζ : MulAut ↥Gp)
    (hζE : ∀ x : E, ∃ x' : E, (MulAut.conjNormal x' : MulAut ↥Gp) =
      ζ * MulAut.conjNormal x * ζ⁻¹)
    (hζ1 : ((Gp ⊓ M₁).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₂).subgroupOf Gp)
    (hζ2 : ((Gp ⊓ M₂).subgroupOf Gp).map ζ.toMonoidHom = (Gp ⊓ M₁).subgroupOf Gp) :
    burnsideF411_Swap M₁ M₂ := by
  haveI := hN
  have hM₁ := burnsideF411_eq_normalizer hN hsplit hP
  have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₂ ⊓ M₁, e = n * h := fun e => by
    obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
    exact ⟨n, hn, h, ⟨hh.2, hh.1⟩, rfl⟩
  have hM₂ := burnsideF411_eq_normalizer hN hsplit' (burnsideF411a_isLieParabolics_symm hP)
  exact burnsideF411_swap_of_aut hC hM₁ hM₂ ζ hζE hζ1 hζ2

theorem burnsideF411a_swap_L3_of_normalizes {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .L3 p f Gp M₁ M₂)
    (hnorm : ∀ (K : Type) [Field K] [Finite K] [Fact p.Prime] [CharP K p]
      (e : projectiveSL 3 K ≃* ↥Gp),
      Gp ⊓ M₁ = (projStabilizer (flagSpace 3 K 1)).map (Gp.subtype.comp e.toMonoidHom) →
      Gp ⊓ M₂ = (projStabilizer (flagSpace 3 K 2)).map (Gp.subtype.comp e.toMonoidHom) →
      ∀ x : E, ∃ x' : E, @MulAut.conjNormal E _ Gp hyp.normal x' =
        MulAut.congr e (burnsideF411a_L3zeta K (frobeniusEquiv K p)) *
          @MulAut.conjNormal E _ Gp hyp.normal x *
          (MulAut.congr e (burnsideF411a_L3zeta K (frobeniusEquiv K p)))⁻¹) :
    burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, fK, finK, e, hpr, hK, hP1, hP2, hP⟩ := burnsideF411a_L3_chart hyp
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI : CharP K p := burnsideF4h_cl_charP hK
  have hQ : ∀ (X : Subgroup E) (L : Subgroup (projectiveSL 3 K)),
      Gp ⊓ X = L.map (Gp.subtype.comp e.toMonoidHom) →
        (Gp ⊓ X).subgroupOf Gp = L.map e.toMonoidHom := by
    intro X L hX
    rw [hX, ← Subgroup.map_map]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hQ1 := hQ _ _ hP1
  have hQ2 := hQ _ _ hP2
  have hz1 := burnsideF411a_L3zeta_map_flag_one (K := K) (frobeniusEquiv K p)
  have hz2 := burnsideF411a_L3zeta_map_flag_two (K := K) (frobeniusEquiv K p)
  refine burnsideF411a_swap_of_normalizing hyp.normal hyp.centralizer_trivial hyp.split hP
    (MulAut.congr e (burnsideF411a_L3zeta K (frobeniusEquiv K p))) (hnorm K e hP1 hP2) ?_ ?_
  · rw [hQ1, hQ2, burnsideF411a_L3_map_map_congr]
    exact congrArg (fun L => L.map e.toMonoidHom) hz1
  · rw [hQ1, hQ2, burnsideF411a_L3_map_map_congr]
    exact congrArg (fun L => L.map e.toMonoidHom) hz2

end CFSG.ASVolI
