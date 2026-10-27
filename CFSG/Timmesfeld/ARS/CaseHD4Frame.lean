module

public import CFSG.Timmesfeld.ARS.CaseHD4
public import CFSG.Timmesfeld.ARS.CaseHG2Frame
public import CFSG.Timmesfeld.RankTwo.ModelD43Rank
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field
open CFSG.Timmesfeld.RankTwo CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedD4

namespace CaseH

theorem d43Long_neg_iff (v : Fin (Tag.rank .G2) → ℤ) : d43Long (-v) ↔ d43Long v := by
  change (3 : ℤ) ∣ (-v) (ng 1) ↔ (3 : ℤ) ∣ v (ng 1)
  rw [Pi.neg_apply, dvd_neg]

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]
  {σ : E →+* E}

open Classical in
@[expose] noncomputable def d4PsiS (γ : Fin 2 → ℤ) (t : E) : G :=
  if h : ∃ i, hexRoot i = γ then c.d4PosS h.choose t
  else if h' : ∃ i, -hexRoot i = γ then c.d4NegS h'.choose t else 1

open Classical in
@[expose] noncomputable def d4PsiL (ι : fixedField σ →+* F) (τ : F) (γ : Fin 2 → ℤ)
    (t : fixedField σ) : G :=
  if h : ∃ i, hexRoot i = γ then c.d4PosL ι τ h.choose t
  else if h' : ∃ i, -hexRoot i = γ then c.d4NegL ι h'.choose t else 1

theorem d4PsiS_pos (j : Fin 6) (t : E) : c.d4PsiS (hexRoot j) t = c.d4PosS j t := by
  classical
  have h : ∃ i, hexRoot i = hexRoot j := ⟨j, rfl⟩
  rw [d4PsiS, dite_eq_left h]
  rw [hexRoot_injective h.choose_spec]

theorem d4PsiS_neg (j : Fin 6) (t : E) : c.d4PsiS (-hexRoot j) t = c.d4NegS j t := by
  classical
  have h1 : ¬ ∃ i, hexRoot i = -hexRoot j := fun ⟨i, hi⟩ => hexRoot_ne_neg i j hi
  have h2 : ∃ i, -hexRoot i = -hexRoot j := ⟨j, rfl⟩
  rw [d4PsiS, dite_eq_right h1, dite_eq_left h2]
  rw [hexRoot_injective (neg_injective h2.choose_spec)]

theorem d4PsiL_pos (ι : fixedField σ →+* F) (τ : F) (j : Fin 6) (t : fixedField σ) :
    c.d4PsiL ι τ (hexRoot j) t = c.d4PosL ι τ j t := by
  classical
  have h : ∃ i, hexRoot i = hexRoot j := ⟨j, rfl⟩
  rw [d4PsiL, dite_eq_left h]
  rw [hexRoot_injective h.choose_spec]

theorem d4PsiL_neg (ι : fixedField σ →+* F) (τ : F) (j : Fin 6) (t : fixedField σ) :
    c.d4PsiL ι τ (-hexRoot j) t = c.d4NegL ι j t := by
  classical
  have h1 : ¬ ∃ i, hexRoot i = -hexRoot j := fun ⟨i, hi⟩ => hexRoot_ne_neg i j hi
  have h2 : ∃ i, -hexRoot i = -hexRoot j := ⟨j, rfl⟩
  rw [d4PsiL, dite_eq_right h1, dite_eq_left h2]
  rw [hexRoot_injective (neg_injective h2.choose_spec)]

theorem d43PsiPos_eq (ι : fixedField σ →+* F) (τ : F) :
    d43PsiPos (G := G) (σ := σ) c.d4PsiS (c.d4PsiL ι τ) = c.d4Pos ι τ := by
  funext ⟨i, t⟩
  fin_cases i
  exacts [c.d4PsiS_pos 0 t, c.d4PsiL_pos ι τ 1 t, c.d4PsiS_pos 2 t, c.d4PsiL_pos ι τ 3 t,
    c.d4PsiS_pos 4 t, c.d4PsiL_pos ι τ 5 t]

variable [CharP F 2] (ι : fixedField σ →+* F) {τ : F} (hτ0 : τ ≠ 0)
  (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))

theorem d4_weyl_posS (hβ : ∀ s, c.beta s = s) (i : Fin 2) (j : Fin 6)
    (hj : ¬ d43Long (hexRoot j)) (t : E) :
    c.g2Weyl i * c.d4PosS j t * (c.g2Weyl i)⁻¹ = c.d4PsiS (g2Refl i (hexRoot j)) t := by
  match i, j with
  | 0, 0 =>
    rw [show g2Refl 0 (hexRoot 0) = hexRoot 4 by funext k; fin_cases k <;> decide, d4PsiS_pos]
    exact c.nb_conj_x1 hβ t
  | 0, 2 =>
    rw [show g2Refl 0 (hexRoot 2) = hexRoot 2 by funext k; fin_cases k <;> decide, d4PsiS_pos]
    exact c.nb_conj_x3 t
  | 0, 4 =>
    rw [show g2Refl 0 (hexRoot 4) = hexRoot 0 by funext k; fin_cases k <;> decide, d4PsiS_pos]
    exact c.nb_conj_x5 hβ t
  | 1, 0 =>
    rw [show g2Refl 1 (hexRoot 0) = -hexRoot 0 by funext k; fin_cases k <;> decide, d4PsiS_neg]
    exact c.m_conj_x1 t
  | 1, 2 =>
    rw [show g2Refl 1 (hexRoot 2) = hexRoot 4 by funext k; fin_cases k <;> decide, d4PsiS_pos]
    exact c.m_conj_x3 t
  | 1, 4 =>
    rw [show g2Refl 1 (hexRoot 4) = hexRoot 2 by funext k; fin_cases k <;> decide, d4PsiS_pos]
    exact c.m_conj_x5 t
  | 0, 1 => exact absurd long_hexRoot_one hj
  | 1, 1 => exact absurd long_hexRoot_one hj
  | 0, 3 => exact absurd long_hexRoot_three hj
  | 1, 3 => exact absurd long_hexRoot_three hj
  | 0, 5 => exact absurd long_hexRoot_five hj
  | 1, 5 => exact absurd long_hexRoot_five hj

omit [CharP F 2] in
theorem d4_weyl_negS [CharP F 2] (i : Fin 2) (j : Fin 6) (hj : ¬ d43Long (hexRoot j)) (t : E) :
    c.g2Weyl i * c.d4NegS j t * (c.g2Weyl i)⁻¹ = c.d4PsiS (-g2Refl i (hexRoot j)) t := by
  match i, j with
  | 0, 0 =>
    rw [show g2Refl 0 (hexRoot 0) = hexRoot 4 by funext k; fin_cases k <;> decide, d4PsiS_neg]
    exact c.nb_conj_xm1 t
  | 0, 2 =>
    rw [show g2Refl 0 (hexRoot 2) = hexRoot 2 by funext k; fin_cases k <;> decide, d4PsiS_neg]
    exact c.nb_conj_xm3 t
  | 0, 4 =>
    rw [show g2Refl 0 (hexRoot 4) = hexRoot 0 by funext k; fin_cases k <;> decide, d4PsiS_neg]
    exact c.nb_conj_xm5 t
  | 1, 0 =>
    rw [show g2Refl 1 (hexRoot 0) = -hexRoot 0 by funext k; fin_cases k <;> decide, neg_neg,
      d4PsiS_pos]
    exact c.m_conj_xm1 t
  | 1, 2 =>
    rw [show g2Refl 1 (hexRoot 2) = hexRoot 4 by funext k; fin_cases k <;> decide, d4PsiS_neg]
    exact c.m_conj_xm3 t
  | 1, 4 =>
    rw [show g2Refl 1 (hexRoot 4) = hexRoot 2 by funext k; fin_cases k <;> decide, d4PsiS_neg]
    exact c.m_conj_xm5 t
  | 0, 1 => exact absurd long_hexRoot_one hj
  | 1, 1 => exact absurd long_hexRoot_one hj
  | 0, 3 => exact absurd long_hexRoot_three hj
  | 1, 3 => exact absurd long_hexRoot_three hj
  | 0, 5 => exact absurd long_hexRoot_five hj
  | 1, 5 => exact absurd long_hexRoot_five hj

include hτ0 hτ in
theorem d4_weyl_posL (i : Fin 2) (j : Fin 6) (hj : d43Long (hexRoot j)) (t : fixedField σ) :
    c.g2Weyl i * c.d4PosL ι τ j t * (c.g2Weyl i)⁻¹ = c.d4PsiL ι τ (g2Refl i (hexRoot j)) t := by
  match i, j with
  | 0, 1 =>
    rw [show g2Refl 0 (hexRoot 1) = hexRoot 3 by funext k; fin_cases k <;> decide, d4PsiL_pos]
    exact c.nb_conj_x2 (τ * ι t)
  | 0, 3 =>
    rw [show g2Refl 0 (hexRoot 3) = hexRoot 1 by funext k; fin_cases k <;> decide, d4PsiL_pos]
    exact c.nb_conj_x4 (τ * ι t)
  | 0, 5 =>
    rw [show g2Refl 0 (hexRoot 5) = -hexRoot 5 by funext k; fin_cases k <;> decide, d4PsiL_neg]
    exact c.nb_conj_x6 (ι t)
  | 1, 1 =>
    rw [show g2Refl 1 (hexRoot 1) = hexRoot 5 by funext k; fin_cases k <;> decide, d4PsiL_pos]
    change c.m * c.x2 (τ * ι t) * c.m⁻¹ = c.x6 (ι t)
    rw [c.m_conj_x2 hτ0 hτ, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]
  | 1, 3 =>
    rw [show g2Refl 1 (hexRoot 3) = hexRoot 3 by funext k; fin_cases k <;> decide, d4PsiL_pos]
    exact c.m_conj_x4 (τ * ι t)
  | 1, 5 =>
    rw [show g2Refl 1 (hexRoot 5) = hexRoot 1 by funext k; fin_cases k <;> decide, d4PsiL_pos]
    exact hτ (ι t)
  | 0, 0 => exact absurd hj short_hexRoot_zero
  | 1, 0 => exact absurd hj short_hexRoot_zero
  | 0, 2 => exact absurd hj short_hexRoot_two
  | 1, 2 => exact absurd hj short_hexRoot_two
  | 0, 4 => exact absurd hj short_hexRoot_four
  | 1, 4 => exact absurd hj short_hexRoot_four

omit [CharP F 2] in
theorem d4_weyl_negL [CharP F 2] (i : Fin 2) (j : Fin 6) (hj : d43Long (hexRoot j))
    (t : fixedField σ) :
    c.g2Weyl i * c.d4NegL ι j t * (c.g2Weyl i)⁻¹ = c.d4PsiL ι τ (-g2Refl i (hexRoot j)) t := by
  match i, j with
  | 0, 1 =>
    rw [show g2Refl 0 (hexRoot 1) = hexRoot 3 by funext k; fin_cases k <;> decide, d4PsiL_neg]
    exact c.nb_conj_xm2 (ι t)
  | 0, 3 =>
    rw [show g2Refl 0 (hexRoot 3) = hexRoot 1 by funext k; fin_cases k <;> decide, d4PsiL_neg]
    exact c.nb_conj_xm4 (ι t)
  | 0, 5 =>
    rw [show g2Refl 0 (hexRoot 5) = -hexRoot 5 by funext k; fin_cases k <;> decide, neg_neg,
      d4PsiL_pos]
    exact c.nb_conj_xmb (ι t)
  | 1, 1 =>
    rw [show g2Refl 1 (hexRoot 1) = hexRoot 5 by funext k; fin_cases k <;> decide, d4PsiL_neg]
    exact c.m_conj_xm2 (ι t)
  | 1, 3 =>
    rw [show g2Refl 1 (hexRoot 3) = hexRoot 3 by funext k; fin_cases k <;> decide, d4PsiL_neg]
    exact c.m_conj_xm4 (ι t)
  | 1, 5 =>
    rw [show g2Refl 1 (hexRoot 5) = hexRoot 1 by funext k; fin_cases k <;> decide, d4PsiL_neg]
    exact c.m_conj_xmb (ι t)
  | 0, 0 => exact absurd hj short_hexRoot_zero
  | 1, 0 => exact absurd hj short_hexRoot_zero
  | 0, 2 => exact absurd hj short_hexRoot_two
  | 1, 2 => exact absurd hj short_hexRoot_two
  | 0, 4 => exact absurd hj short_hexRoot_four
  | 1, 4 => exact absurd hj short_hexRoot_four

theorem d4_hWS (hβ : ∀ s, c.beta s = s) :
    ∀ i γ, IsRoot .G2 γ → ¬d43Long γ → ∀ t : E, c.g2Weyl i * c.d4PsiS γ t * (c.g2Weyl i)⁻¹ =
      c.d4PsiS ((RootSystem.ofCartan (twistedDatum σ).isFiniteType
        (twistedDatum σ).divisible).refl i γ) t := by
  intro i γ hγ hs t
  change c.g2Weyl i * c.d4PsiS γ t * (c.g2Weyl i)⁻¹ = c.d4PsiS (g2Refl i γ) t
  obtain ⟨j, rfl | rfl⟩ := g2_root_cases hγ
  · rw [c.d4PsiS_pos]
    exact c.d4_weyl_posS hβ i j hs t
  · have hs' : ¬ d43Long (hexRoot j) := fun h => hs ((d43Long_neg_iff _).2 h)
    rw [c.d4PsiS_neg, show g2Refl i (-hexRoot j) = -g2Refl i (hexRoot j) from
      _root_.map_neg (CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) i) (hexRoot j)]
    exact c.d4_weyl_negS i j hs' t

include hτ0 hτ in
theorem d4_hWL :
    ∀ i γ, IsRoot .G2 γ → d43Long γ → ∀ t : fixedField σ,
      c.g2Weyl i * c.d4PsiL ι τ γ t * (c.g2Weyl i)⁻¹ =
        c.d4PsiL ι τ ((RootSystem.ofCartan (twistedDatum σ).isFiniteType
          (twistedDatum σ).divisible).refl i γ) t := by
  intro i γ hγ hl t
  change c.g2Weyl i * c.d4PsiL ι τ γ t * (c.g2Weyl i)⁻¹ = c.d4PsiL ι τ (g2Refl i γ) t
  obtain ⟨j, rfl | rfl⟩ := g2_root_cases hγ
  · rw [c.d4PsiL_pos]
    exact c.d4_weyl_posL ι hτ0 hτ i j hl t
  · have hl' : d43Long (hexRoot j) := (d43Long_neg_iff _).1 hl
    rw [c.d4PsiL_neg, show g2Refl i (-hexRoot j) = -g2Refl i (hexRoot j) from
      _root_.map_neg (CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) i) (hexRoot j)]
    exact c.d4_weyl_negL ι i j hl' t

omit [CharP E 2] [CharP F 2] in
theorem map_sl2Upper {K L : Type} [Field K] [Field L] (f : K →+* L) (t : K) :
    SpecialLinearGroup.map f (sl2Upper t) = sl2Upper (f t) := by
  apply Subtype.ext
  change f.mapMatrix !![1, t; 0, 1] = !![1, f t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP E 2] [CharP F 2] in
theorem map_sl2Lower {K L : Type} [Field K] [Field L] (f : K →+* L) (t : K) :
    SpecialLinearGroup.map f (sl2Lower t) = sl2Lower (f t) := by
  apply Subtype.ext
  change f.mapMatrix !![1, 0; t, 1] = !![1, 0; f t, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem single_ng_zero : (Pi.single (ng 0) 1 : Fin (Tag.rank .G2) → ℤ) = hexRoot 5 := by
  funext k
  obtain ⟨k, hk⟩ := k
  have hk' : k < 2 := hk
  interval_cases k <;> decide +revert

theorem single_ng_one : (Pi.single (ng 1) 1 : Fin (Tag.rank .G2) → ℤ) = hexRoot 0 := by
  funext k
  obtain ⟨k, hk⟩ := k
  have hk' : k < 2 := hk
  interval_cases k <;> decide +revert

omit [CharP F 2] in
theorem d4_hrank (hσ3 : ∀ x, σ (σ (σ x)) = x) :
    ∀ i, ExtendsToHom (twistedDatum σ).rootGroup {Pi.single i 1, -Pi.single i 1}
      (d43PhiOf hσ3 c.d4PsiS (c.d4PsiL ι τ)) :=
  d43_extendsToHom_rankOne hσ3 c.d4PsiS (c.d4PsiL ι τ) (c.rankOneB.comp (SpecialLinearGroup.map ι))
    (fun t => by
      rw [MonoidHom.comp_apply, map_sl2Upper, c.rankOneB_upper]
      exact ((c.d4PsiL_pos ι τ 5 t).symm.trans
        (congrArg (fun γ => c.d4PsiL ι τ γ t) single_ng_zero.symm)))
    (fun t => by
      rw [MonoidHom.comp_apply, map_sl2Lower, c.rankOneB_lower]
      exact ((c.d4PsiL_neg ι τ 5 t).symm.trans
        (congrArg (fun γ => c.d4PsiL ι τ (-γ) t) single_ng_zero.symm)))
    ((Subgroup.subtype _).comp c.φ.symm.toMonoidHom)
    (fun t => ((c.d4PsiS_pos 0 t).symm.trans
      (congrArg (fun γ => c.d4PsiS γ t) single_ng_one.symm)))
    (fun t => ((c.d4PsiS_neg 0 t).symm.trans
      (congrArg (fun γ => c.d4PsiS (-γ) t) single_ng_one.symm)))

theorem eq_top_of_le {H : Subgroup G} (hP : P ≤ H) (hP' : P' ≤ H) (hA : A ≤ H)
    (hU5 : shortRoot R P' ⁅A₀, P⁆ A ≤ H) (hU3 : shortRoot R P ⁅A₀, P'⁆ A ≤ H)
    (hQ' : ⁅A₀, P'⁆ ≤ H) (hm : c.m ∈ H) (hnb : c.nb ∈ H) : H = ⊤ := by
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

include hτ0 in
theorem d4_hgen (hσ3 : ∀ x, σ (σ (σ x)) = x) (hι : Function.Surjective ι) :
    Subgroup.closure (⋃ γ ∈ (twistedDatum σ).roots,
      Set.range (d43PhiOf hσ3 c.d4PsiS (c.d4PsiL ι τ) γ)) = ⊤ := by
  refine (congrArg Subgroup.closure (iUnion_range_d43PhiOf hσ3 c.d4PsiS (c.d4PsiL ι τ))).trans ?_
  set H := Subgroup.closure
    ((⋃ γ ∈ {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ ¬d43Long γ}, Set.range (c.d4PsiS γ)) ∪
      ⋃ γ ∈ {γ : Fin (Tag.rank .G2) → ℤ | IsRoot .G2 γ ∧ d43Long γ},
        Set.range (c.d4PsiL ι τ γ)) with hH
  have hmemS : ∀ γ, IsRoot .G2 γ → ¬d43Long γ → ∀ t, c.d4PsiS γ t ∈ H := fun γ hγ hs t =>
    Subgroup.subset_closure (Or.inl (Set.mem_iUnion₂.2 ⟨γ, ⟨hγ, hs⟩, t, rfl⟩))
  have hmemL : ∀ γ, IsRoot .G2 γ → d43Long γ → ∀ t, c.d4PsiL ι τ γ t ∈ H := fun γ hγ hl t =>
    Subgroup.subset_closure (Or.inr (Set.mem_iUnion₂.2 ⟨γ, ⟨hγ, hl⟩, t, rfl⟩))
  have hS : ∀ j, ¬d43Long (hexRoot j) → ∀ t, c.d4PosS j t ∈ H ∧ c.d4NegS j t ∈ H :=
    fun j hj t => ⟨c.d4PsiS_pos j t ▸ hmemS _ (isRoot_hexRoot j) hj t,
      c.d4PsiS_neg j t ▸ hmemS _ (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_hexRoot j))
        (fun h => hj ((d43Long_neg_iff _).1 h)) t⟩
  have hL : ∀ j, d43Long (hexRoot j) → ∀ t, c.d4PosL ι τ j t ∈ H ∧ c.d4NegL ι j t ∈ H :=
    fun j hj t => ⟨c.d4PsiL_pos ι τ j t ▸ hmemL _ (isRoot_hexRoot j) hj t,
      c.d4PsiL_neg ι τ j t ▸ hmemL _ (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_hexRoot j))
        ((d43Long_neg_iff _).2 hj) t⟩
  have hτ' : ∀ v : F, τ * (τ⁻¹ * v) = v := fun v => by
    rw [← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
  refine c.eq_top_of_le (fun p hp => ?_) (fun p hp => ?_) (fun a ha => ?_) (fun u hu => ?_)
    (fun u hu => ?_) (fun q hq => ?_) ?_ ?_
  · obtain ⟨u, rfl⟩ := c.x6_surjective hp
    obtain ⟨t, rfl⟩ := hι u
    exact (hL 5 long_hexRoot_five t).1
  · obtain ⟨v, rfl⟩ := c.x2_surjective hp
    obtain ⟨t, ht⟩ := hι (τ⁻¹ * v)
    have := (hL 1 long_hexRoot_one t).1
    change c.x2 (τ * ι t) ∈ H at this
    rwa [ht, hτ'] at this
  · obtain ⟨z, rfl⟩ := c.x4_surjective ha
    obtain ⟨t, ht⟩ := hι (τ⁻¹ * z)
    have := (hL 3 long_hexRoot_three t).1
    change c.x4 (τ * ι t) ∈ H at this
    rwa [ht, hτ'] at this
  · obtain ⟨w, rfl⟩ := c.x5_surjective hu
    exact (hS 4 short_hexRoot_four w).1
  · obtain ⟨r, rfl⟩ := c.x3_surjective hu
    exact (hS 2 short_hexRoot_two r).1
  · obtain ⟨u, rfl⟩ := exists_psi_tv_eq _ c.hψQ' hq
    obtain ⟨t, rfl⟩ := hι u
    exact (hL 5 long_hexRoot_five t).2
  · have h := c.x1_mul_xm1_mul_x1 (one_ne_zero (α := E))
    rw [show Units.mk0 (1 : E) one_ne_zero = 1 from Units.ext rfl, c.k_one, one_mul, inv_one] at h
    rw [← h]
    obtain ⟨h1, h2⟩ := hS 0 short_hexRoot_zero 1
    exact H.mul_mem (H.mul_mem h1 h2) h1
  · have e1 : c.nb = c.x6 1 * c.xmb 1 * c.x6 1 := by
      rw [nb, w01, map_mul, map_mul]
      rfl
    obtain ⟨h1, h2⟩ := hL 5 long_hexRoot_five 1
    change c.x6 (ι 1) ∈ H at h1
    change c.xmb (ι 1) ∈ H at h2
    rw [map_one] at h1 h2
    rw [e1]
    exact H.mul_mem (H.mul_mem h1 h2) h1

omit [CharP F 2] in
theorem d4_hnt (hσ3 : ∀ x, σ (σ (σ x)) = x) :
    ∃ γ ∈ (twistedDatum σ).roots, ∃ x, d43PhiOf hσ3 c.d4PsiS (c.d4PsiL ι τ) γ x ≠ 1 := by
  have := S.hyp.finite
  have hr := range_d43PhiOf_long hσ3 c.d4PsiS (c.d4PsiL ι τ) (isRoot_hexRoot 5) long_hexRoot_five
  have hmem : c.d4PsiL ι τ (hexRoot 5) 1 ∈ Set.range (d43PhiOf hσ3 c.d4PsiS (c.d4PsiL ι τ)
      (hexRoot 5)) := by
    rw [hr]
    exact ⟨1, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨hexRoot 5, by rw [twistedDatum_roots]; exact isRoot_hexRoot 5, x, ?_⟩
  rw [hx, c.d4PsiL_pos]
  change c.x6 (ι 1) ≠ 1
  rw [map_one]
  intro h
  exact one_ne_zero (c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1) (h.trans c.x6_zero.symm))

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
