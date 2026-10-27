module

public import CFSG.Timmesfeld.ARS.CaseHG2
public import CFSG.Timmesfeld.RankTwo.ModelG2Rank
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.ARS.CaseHClass
public import CFSG.Timmesfeld.ARS.CaseHFeitHigman
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field
open CFSG.Timmesfeld.RankTwo CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CaseH

section Block

variable (F : Type) [Field F]

@[expose] def sl2to3Mat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1]

theorem det_sl2to3Mat (g : Matrix (Fin 2) (Fin 2) F) : (sl2to3Mat F g).det = g.det := by
  simp [sl2to3Mat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem sl2to3Mat_mul (g h : Matrix (Fin 2) (Fin 2) F) :
    sl2to3Mat F (g * h) = sl2to3Mat F g * sl2to3Mat F h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2to3Mat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem sl2to3Mat_one : sl2to3Mat F 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2to3Mat]

@[expose] def sl2to3 : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun g := ⟨sl2to3Mat F g.1, by rw [det_sl2to3Mat]; exact g.2⟩
  map_one' := Subtype.ext (sl2to3Mat_one F)
  map_mul' g h := Subtype.ext (sl2to3Mat_mul F g.1 h.1)

variable {F}

theorem sl2to3_upper (t : F) :
    sl2to3 F (sl2Upper t) = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  change sl2to3Mat F (sl2Upper t).1 = _
  rw [val_tv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2to3Mat, sl2Upper]

theorem sl2to3_lower (t : F) :
    sl2to3 F (sl2Lower t) = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  change sl2to3Mat F (sl2Lower t).1 = _
  rw [val_tv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2to3Mat, sl2Lower]

end Block

theorem g2_root_cases {γ : Fin 2 → ℤ} (hγ : IsRoot .G2 γ) :
    ∃ j, γ = hexRoot j ∨ γ = -hexRoot j := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  interval_cases k <;>
    first
    | (refine ⟨0, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨1, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨2, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨3, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨4, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨5, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨0, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨1, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨2, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨3, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨4, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨5, Or.inr ?_⟩; funext k; fin_cases k <;> decide)

theorem hexRoot_ne_neg (i j : Fin 6) : hexRoot i ≠ -hexRoot j := by
  have hpos : ∀ k : Fin 6, 0 ≤ hexRoot k 0 ∧ 0 ≤ hexRoot k 1 ∧ 0 < hexRoot k 0 + hexRoot k 1 := by
    intro k
    fin_cases k <;> decide
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.neg_apply] at h0 h1
  have := hpos i
  have := hpos j
  omega

abbrev g2Refl (i : Fin 2) (v : Fin 2 → ℤ) : Fin 2 → ℤ :=
  CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) i v

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

open Classical in
@[expose] noncomputable def g2Psi (e : F →+* E) (τ : F) (γ : Fin 2 → ℤ) (t : F) : G :=
  if h : ∃ i, hexRoot i = γ then c.g2Pos e τ h.choose t
  else if h' : ∃ i, -hexRoot i = γ then c.g2Neg e h'.choose t else 1

theorem g2Psi_pos (e : F →+* E) (τ : F) (j : Fin 6) (t : F) :
    c.g2Psi e τ (hexRoot j) t = c.g2Pos e τ j t := by
  classical
  have h : ∃ i, hexRoot i = hexRoot j := ⟨j, rfl⟩
  rw [g2Psi, dite_eq_left h]
  rw [hexRoot_injective h.choose_spec]

theorem g2Psi_neg (e : F →+* E) (τ : F) (j : Fin 6) (t : F) :
    c.g2Psi e τ (-hexRoot j) t = c.g2Neg e j t := by
  classical
  have h1 : ¬ ∃ i, hexRoot i = -hexRoot j := fun ⟨i, hi⟩ => hexRoot_ne_neg i j hi
  have h2 : ∃ i, -hexRoot i = -hexRoot j := ⟨j, rfl⟩
  rw [g2Psi, dite_eq_right h1, dite_eq_left h2]
  rw [hexRoot_injective (neg_injective h2.choose_spec)]

@[expose] noncomputable def g2Weyl : Fin 2 → G
  | 0 => c.nb
  | 1 => c.m

variable [CharP F 2] (e : F →+* E) {τ : F} (hτ0 : τ ≠ 0)
  (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))

include hτ0 hτ in
theorem g2_weyl_pos (hβ : ∀ s, c.beta s = s) :
    ∀ (i : Fin 2) (j : Fin 6) (t : F),
      c.g2Weyl i * c.g2Pos e τ j t * (c.g2Weyl i)⁻¹ = c.g2Psi e τ (g2Refl i (hexRoot j)) t
  | 0, 0, t => by
    rw [show g2Refl 0 (hexRoot 0) = hexRoot 4 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.nb_conj_x1 hβ (e t)
  | 0, 1, t => by
    rw [show g2Refl 0 (hexRoot 1) = hexRoot 3 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.nb_conj_x2 (τ * t)
  | 0, 2, t => by
    rw [show g2Refl 0 (hexRoot 2) = hexRoot 2 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.nb_conj_x3 (e t)
  | 0, 3, t => by
    rw [show g2Refl 0 (hexRoot 3) = hexRoot 1 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.nb_conj_x4 (τ * t)
  | 0, 4, t => by
    rw [show g2Refl 0 (hexRoot 4) = hexRoot 0 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.nb_conj_x5 hβ (e t)
  | 0, 5, t => by
    rw [show g2Refl 0 (hexRoot 5) = -hexRoot 5 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.nb_conj_x6 t
  | 1, 0, t => by
    rw [show g2Refl 1 (hexRoot 0) = -hexRoot 0 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.m_conj_x1 (e t)
  | 1, 1, t => by
    rw [show g2Refl 1 (hexRoot 1) = hexRoot 5 by funext k; fin_cases k <;> decide, g2Psi_pos]
    change c.m * c.x2 (τ * t) * c.m⁻¹ = c.x6 t
    rw [c.m_conj_x2 hτ0 hτ, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]
  | 1, 2, t => by
    rw [show g2Refl 1 (hexRoot 2) = hexRoot 4 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.m_conj_x3 (e t)
  | 1, 3, t => by
    rw [show g2Refl 1 (hexRoot 3) = hexRoot 3 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.m_conj_x4 (τ * t)
  | 1, 4, t => by
    rw [show g2Refl 1 (hexRoot 4) = hexRoot 2 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact c.m_conj_x5 (e t)
  | 1, 5, t => by
    rw [show g2Refl 1 (hexRoot 5) = hexRoot 1 by funext k; fin_cases k <;> decide, g2Psi_pos]
    exact hτ t

omit [CharP F 2] in
theorem g2_weyl_neg [CharP F 2] :
    ∀ (i : Fin 2) (j : Fin 6) (t : F),
      c.g2Weyl i * c.g2Neg e j t * (c.g2Weyl i)⁻¹ = c.g2Psi e τ (-g2Refl i (hexRoot j)) t
  | 0, 0, t => by
    rw [show g2Refl 0 (hexRoot 0) = hexRoot 4 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.nb_conj_xm1 (e t)
  | 0, 1, t => by
    rw [show g2Refl 0 (hexRoot 1) = hexRoot 3 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.nb_conj_xm2 t
  | 0, 2, t => by
    rw [show g2Refl 0 (hexRoot 2) = hexRoot 2 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.nb_conj_xm3 (e t)
  | 0, 3, t => by
    rw [show g2Refl 0 (hexRoot 3) = hexRoot 1 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.nb_conj_xm4 t
  | 0, 4, t => by
    rw [show g2Refl 0 (hexRoot 4) = hexRoot 0 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.nb_conj_xm5 (e t)
  | 0, 5, t => by
    rw [show g2Refl 0 (hexRoot 5) = -hexRoot 5 by decide, neg_neg, g2Psi_pos]
    exact c.nb_conj_xmb t
  | 1, 0, t => by
    rw [show g2Refl 1 (hexRoot 0) = -hexRoot 0 by decide, neg_neg, g2Psi_pos]
    exact c.m_conj_xm1 (e t)
  | 1, 1, t => by
    rw [show g2Refl 1 (hexRoot 1) = hexRoot 5 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.m_conj_xm2 t
  | 1, 2, t => by
    rw [show g2Refl 1 (hexRoot 2) = hexRoot 4 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.m_conj_xm3 (e t)
  | 1, 3, t => by
    rw [show g2Refl 1 (hexRoot 3) = hexRoot 3 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.m_conj_xm4 t
  | 1, 4, t => by
    rw [show g2Refl 1 (hexRoot 4) = hexRoot 2 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.m_conj_xm5 (e t)
  | 1, 5, t => by
    rw [show g2Refl 1 (hexRoot 5) = hexRoot 1 by funext k; fin_cases k <;> decide, g2Psi_neg]
    exact c.m_conj_xmb t

include hτ0 hτ in
theorem g2_hW (hβ : ∀ s, c.beta s = s) :
    ∀ i γ, IsRoot .G2 γ → ∀ t, c.g2Weyl i * c.g2Psi e τ γ t * (c.g2Weyl i)⁻¹ =
      c.g2Psi e τ ((RootSystem.ofCartan (g2Datum F).isFiniteType (g2Datum F).divisible).refl i γ)
        t := by
  intro i γ hγ t
  change c.g2Weyl i * c.g2Psi e τ γ t * (c.g2Weyl i)⁻¹ = c.g2Psi e τ (g2Refl i γ) t
  obtain ⟨j, rfl | rfl⟩ := g2_root_cases hγ
  · rw [c.g2Psi_pos]
    exact c.g2_weyl_pos e hτ0 hτ hβ i j t
  · rw [c.g2Psi_neg, show g2Refl i (-hexRoot j) = -g2Refl i (hexRoot j) from
      _root_.map_neg (CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) i) (hexRoot j)]
    exact c.g2_weyl_neg e i j t

omit [CharP E 2] [CharP F 2] in
@[expose] noncomputable def rankOneB : SpecialLinearGroup (Fin 2) F →* G := c.ψ.comp (sl2to3 F)

omit [CharP E 2] [CharP F 2] in
theorem rankOneB_upper (t : F) : c.rankOneB (sl2Upper t) = c.x6 t := by
  rw [rankOneB, MonoidHom.comp_apply, sl2to3_upper]
  rfl

omit [CharP E 2] [CharP F 2] in
theorem rankOneB_lower (t : F) : c.rankOneB (sl2Lower t) = c.xmb t := by
  rw [rankOneB, MonoidHom.comp_apply, sl2to3_lower]
  rfl

omit [CharP E 2] [CharP F 2] in
@[expose] noncomputable def rankOneA : SpecialLinearGroup (Fin 2) F →* G :=
  (Subgroup.subtype _).comp (c.φ.symm.toMonoidHom.comp (SpecialLinearGroup.map e))

omit [CharP E 2] [CharP F 2] in
theorem rankOneA_upper (t : F) : c.rankOneA e (sl2Upper t) = c.x1 (e t) := by
  have h : SpecialLinearGroup.map e (sl2Upper t) = upperElt E (e t) := by
    apply Subtype.ext
    change e.mapMatrix !![1, t; 0, 1] = !![1, e t; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp only [rankOneA, MonoidHom.comp_apply, h]
  rfl

omit [CharP E 2] [CharP F 2] in
theorem rankOneA_lower (t : F) : c.rankOneA e (sl2Lower t) = c.xm1 (e t) := by
  have h : SpecialLinearGroup.map e (sl2Lower t) = lowerElt E (e t) := by
    apply Subtype.ext
    change e.mapMatrix !![1, 0; t, 1] = !![1, 0; e t, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp only [rankOneA, MonoidHom.comp_apply, h]
  rfl

theorem single_zero_eq : (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) = hexRoot 5 := by
  funext k
  fin_cases k <;> decide

theorem single_one_eq : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) = hexRoot 0 := by
  funext k
  fin_cases k <;> decide

omit [CharP F 2] in
theorem g2_hrank [Finite F] :
    ∀ i : Fin 2, ExtendsToHom (g2Datum F).rootGroup {Pi.single i 1, -Pi.single i 1}
      (g2PhiOf (c.g2Psi e τ))
  | 0 => g2_extendsToHom_rankOne (c.g2Psi e τ) (0 : Fin 2) c.rankOneB
      (fun t => (c.rankOneB_upper t).trans ((c.g2Psi_pos e τ 5 t).symm.trans
        (congrArg (fun γ => c.g2Psi e τ γ t) single_zero_eq.symm)))
      (fun t => (c.rankOneB_lower t).trans ((c.g2Psi_neg e τ 5 t).symm.trans
        (congrArg (fun γ => c.g2Psi e τ (-γ) t) single_zero_eq.symm)))
  | 1 => g2_extendsToHom_rankOne (c.g2Psi e τ) (1 : Fin 2) (c.rankOneA e)
      (fun t => (c.rankOneA_upper e t).trans ((c.g2Psi_pos e τ 0 t).symm.trans
        (congrArg (fun γ => c.g2Psi e τ γ t) single_one_eq.symm)))
      (fun t => (c.rankOneA_lower e t).trans ((c.g2Psi_neg e τ 0 t).symm.trans
        (congrArg (fun γ => c.g2Psi e τ (-γ) t) single_one_eq.symm)))

include hτ0 in
theorem g2_hgen (hesurj : Function.Surjective e) :
    Subgroup.closure (⋃ γ ∈ (g2Datum F).roots, Set.range (g2PhiOf (c.g2Psi e τ) γ)) = ⊤ := by
  refine (congrArg Subgroup.closure (iUnion_range_g2PhiOf (c.g2Psi e τ))).trans ?_
  set H := Subgroup.closure (⋃ γ ∈ (g2Datum F).roots, Set.range (c.g2Psi e τ γ)) with hH
  have hmem : ∀ γ, IsRoot .G2 γ → ∀ t, c.g2Psi e τ γ t ∈ H := fun γ hγ t =>
    Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨γ, mem_adjDatum_roots.2 hγ, t, rfl⟩)
  have hpos : ∀ j t, c.g2Pos e τ j t ∈ H := fun j t => by
    rw [← c.g2Psi_pos e τ j t]
    exact hmem _ (isRoot_hexRoot j) t
  have hneg : ∀ j t, c.g2Neg e j t ∈ H := fun j t => by
    rw [← c.g2Psi_neg e τ j t]
    exact hmem _ (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_hexRoot j)) t
  have hτ' : ∀ v : F, τ * (τ⁻¹ * v) = v := fun v => by
    rw [← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
  have hP : P ≤ H := fun p hp => by
    obtain ⟨u, rfl⟩ := c.x6_surjective hp
    exact hpos 5 u
  have hP' : P' ≤ H := fun p hp => by
    obtain ⟨v, rfl⟩ := c.x2_surjective hp
    have := hpos 1 (τ⁻¹ * v)
    rwa [show c.g2Pos e τ 1 (τ⁻¹ * v) = c.x2 v from congrArg c.x2 (hτ' v)] at this
  have hA : A ≤ H := fun a ha => by
    obtain ⟨z, rfl⟩ := c.x4_surjective ha
    have := hpos 3 (τ⁻¹ * z)
    rwa [show c.g2Pos e τ 3 (τ⁻¹ * z) = c.x4 z from congrArg c.x4 (hτ' z)] at this
  have hU5 : shortRoot R P' ⁅A₀, P⁆ A ≤ H := fun u hu => by
    obtain ⟨w, rfl⟩ := c.x5_surjective hu
    obtain ⟨t, rfl⟩ := hesurj w
    exact hpos 4 t
  have hU3 : shortRoot R P ⁅A₀, P'⁆ A ≤ H := fun u hu => by
    obtain ⟨r, rfl⟩ := c.x3_surjective hu
    obtain ⟨t, rfl⟩ := hesurj r
    exact hpos 2 t
  have hQ' : ⁅A₀, P'⁆ ≤ H := fun q hq => by
    obtain ⟨u, rfl⟩ := exists_psi_tv_eq _ c.hψQ' hq
    exact hneg 5 u
  have hm : c.m ∈ H := by
    have h := c.x1_mul_xm1_mul_x1 (one_ne_zero (α := E))
    rw [show Units.mk0 (1 : E) one_ne_zero = 1 from Units.ext rfl, c.k_one, one_mul, inv_one] at h
    rw [← h]
    have h1 := hpos 0 1
    have h2 := hneg 0 1
    simp only [g2Pos, g2Neg, map_one] at h1 h2
    exact H.mul_mem (H.mul_mem h1 h2) h1
  have hnb : c.nb ∈ H := by
    have e1 : c.nb = c.x6 1 * c.xmb 1 * c.x6 1 := by
      rw [nb, w01, map_mul, map_mul]
      rfl
    rw [e1]
    exact H.mul_mem (H.mul_mem (hpos 5 1) (hneg 5 1)) (hpos 5 1)
  have hM : M R A ≤ H := fun g hg => by
    obtain ⟨a, ha, hga⟩ := S.exists_eq_mul ⟨g, hg⟩
    have hga' : g = _ := hga
    rw [hga']
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hP (S.proj ⟨g, hg⟩).1.2)
      (hU5 (S.proj ⟨g, hg⟩).2.1.2)) (hU3 (S.proj ⟨g, hg⟩).2.2.1.2))
      (hP' (S.proj ⟨g, hg⟩).2.2.2.2)) (hA ha)
  have hA₀ : A₀ ≤ H := fun a ha => by
    rw [← c.conjSub_Q_nb, ← c.conjSub_Q'_m] at ha
    obtain ⟨b, ⟨q, hq, rfl⟩, rfl⟩ := ha
    change c.nb * (c.m * q * c.m⁻¹) * c.nb⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem hnb (H.mul_mem (H.mul_mem hm (hQ' hq)) (H.inv_mem hm)))
      (H.inv_mem hnb)
  rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top S.hyp S.hA S.hA₀]
  exact sup_le (le_trans le_sup_right hM) hA₀

omit [CharP F 2] in
theorem g2_hnt : ∃ γ ∈ (g2Datum F).roots, ∃ x, g2PhiOf (c.g2Psi e τ) γ x ≠ 1 := by
  have := S.hyp.finite
  refine ⟨hexRoot 5, mem_adjDatum_roots.2 (isRoot_hexRoot 5),
    ⟨xPar (rootOperatorFamily .G2) (hexRoot 5) 1, xPar_mem (isRoot_hexRoot 5) 1⟩, ?_⟩
  intro h
  have h2 : c.g2Psi e τ (hexRoot 5) 1 = 1 :=
    (g2PhiOf_xPar (c.g2Psi e τ) (isRoot_hexRoot 5) 1).symm.trans h
  rw [c.g2Psi_pos] at h2
  exact one_ne_zero (c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1) (h2.trans c.x6_zero.symm))

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
