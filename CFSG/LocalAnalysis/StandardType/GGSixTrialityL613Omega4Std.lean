module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusFour
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGClass

public section

namespace CFSG.StandardType

namespace L613O4

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  CFSG.StandardType.Triality CFSG.StandardType.D4Rank CFSG.StandardType.L613KG
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical2 (orthDerived)

section Scale

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_leviFix_of_scale {H : Subgroup (V ≃ₗ[K] V)} {P₁ P₂ : HypPair Q} {L : V ≃ₗ[K] V}
    (hLH : L ∈ H) (hLO : L ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (c : Kˣ)
    (h1e : L P₁.e = (c : K) • P₁.e) (h1f : L P₁.f = ((c⁻¹ : Kˣ) : K) • P₁.f)
    (h2e : L P₂.e = ((c⁻¹ : Kˣ) : K) • P₂.e) (h2f : L P₂.f = (c : K) • P₂.f)
    (hW : ∀ x, InW P₁ P₂ x → L x = x) : L ∈ leviFix H P₁ P₂ := by
  have key : ∀ {u w : V} {a b : Kˣ}, a * b = 1 → L u = (a : K) • u → L w = (b : K) • w →
      L ∈ centralizer {eichler Q u w} := by
    intro u w a b hab hu hw
    rw [mem_centralizer_singleton_iff]
    have h := eichler_conj hLO u w
    rw [hu, hw, eichler_smul_left, smul_smul, ← Units.val_mul, hab, Units.val_one, one_smul] at h
    calc L * eichler Q u w = L * eichler Q u w * L⁻¹ * L := by group
      _ = eichler Q u w * L := by rw [h]
  refine mem_leviFix.mpr ⟨hLH, ⟨⟨hLO, key (mul_inv_cancel c) h1e h2e⟩,
    key (inv_mul_cancel c) h1f h2f⟩, hW⟩

end Scale

variable {K : Type} [Field K]

section Proj

noncomputable abbrev proj : Om8 K →* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
  matrixProjectiveProjection (coordinateQuadPlus 4 K)

theorem projHom_derivedEquiv (x : Om8 K) :
    projHom (coordinateQuadPlus 4 K) (derivedEquiv (coordinateQuadPlus 4 K) x) = proj x := by
  simp only [projHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

theorem derivedEquiv_apply (x : Om8 K) (v : Fin (2 * 4) → K) :
    ((derivedEquiv (coordinateQuadPlus 4 K) x : orthDerived (coordinateQuadPlus 4 K)) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) v = act x v := by
  rw [coe_derivedEquiv, matrixLinearIso_apply_eq, matrixLinearEquiv_apply]

theorem proj_injective [CharP K 2] : Function.Injective (proj (K := K)) := by
  intro x y hxy
  have hQ' : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  apply (derivedEquiv (coordinateQuadPlus 4 K)).injective
  apply projHom_injective hQ'
  rw [projHom_derivedEquiv, projHom_derivedEquiv, hxy]

end Proj

section Roots

variable [Finite K] [CharP K 2]

@[expose] noncomputable def rootPlus (k l : Fin 4) : Subgroup (Om8 K) :=
  (leviFixBar (plusPair K k) (flipPair (plusPair K l))).comap proj

@[expose] noncomputable def rootMinus (k l : Fin 4) : Subgroup (Om8 K) :=
  (leviFixBar (plusPair K k) (plusPair K l)).comap proj

theorem rootMinus_commute {k l : Fin 4} (hkl : k ≠ l) {x y : Om8 K} (hx : x ∈ rootMinus k l)
    (hy : y ∈ rootPlus k l) : x * y = y * x := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  apply proj_injective
  rw [map_mul, map_mul]
  exact (mem_centralizer_iff.mp (leviFixBar_le_centralizer_flip (plusPair_orth hkl) hQ hT hx) _
    hy).symm

theorem conj_mem_rootPlus (hq : 4 ≤ Nat.card K) {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) {n : Om8 K}
    (hni : ∀ r, act n (AutOm.pvec i r) = AutOm.pvec i r)
    (hnj : ∀ r, act n (AutOm.pvec j r) = AutOm.pvec j r) {y : Om8 K} (hy : y ∈ rootPlus k l) :
    n * y * n⁻¹ ∈ rootPlus k l := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hfix : ∀ (m : Fin 4) (r : Bool), act n (AutOm.pvec m r) = AutOm.pvec m r →
      ((derivedEquiv (coordinateQuadPlus 4 K) n : orthDerived (coordinateQuadPlus 4 K)) :
        (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (AutOm.pvec m r) = AutOm.pvec m r :=
    fun m r h => by rw [derivedEquiv_apply, h]
  have hstab : proj n ∈ stabTwoBar K i j := by
    refine ⟨derivedEquiv (coordinateQuadPlus 4 K) n, mem_subgroupOf.mpr ?_,
      projHom_derivedEquiv n⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← AutOm.pvec_true]
      exact hfix i true (hni true)
    · rw [← AutOm.pvec_false]
      exact hfix i false (hni false)
    · rw [← AutOm.pvec_true]
      exact hfix j true (hnj true)
    · rw [← AutOm.pvec_false]
      exact hfix j false (hnj false)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_stabTwoBar hq hij hkl hik hil hjk hjl hstab
  have hy' : proj y ∈ leviFixBar (plusPair K k) (flipPair (plusPair K l)) := hy
  have hby : b * proj y * b⁻¹ ∈ leviFixBar (plusPair K k) (flipPair (plusPair K l)) :=
    mul_mem (mul_mem hb hy') (inv_mem hb)
  have hc := mem_centralizer_iff.mp
    (leviFixBar_le_centralizer_flip (plusPair_orth hkl) hQ hT ha) _ hby
  show proj (n * y * n⁻¹) ∈ leviFixBar (plusPair K k) (flipPair (plusPair K l))
  have e : proj (n * y * n⁻¹) = b * proj y * b⁻¹ := by
    rw [map_mul, map_mul, map_inv, hab]
    calc a * b * proj y * (a * b)⁻¹ = a * (b * proj y * b⁻¹) * a⁻¹ := by group
      _ = b * proj y * b⁻¹ * a * a⁻¹ := by rw [← hc]
      _ = b * proj y * b⁻¹ := by group
  rw [e]
  exact hby

end Roots

section Torus

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem mulSingle_two_of_ne {k l m : Fin 4} (hmk : m ≠ k) (hml : m ≠ l) (c d : Kˣ) :
    (Pi.mulSingle k c * Pi.mulSingle l d : Fin 4 → Kˣ) m = 1 := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hmk, Pi.mulSingle_eq_of_ne hml, one_mul]

omit [Finite K] [CharP K 2] in
theorem mulSingle_two_left {k l : Fin 4} (hkl : k ≠ l) (c d : Kˣ) :
    (Pi.mulSingle k c * Pi.mulSingle l d : Fin 4 → Kˣ) k = c := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hkl, mul_one]

omit [Finite K] [CharP K 2] in
theorem mulSingle_two_right {k l : Fin 4} (hkl : k ≠ l) (c d : Kˣ) :
    (Pi.mulSingle k c * Pi.mulSingle l d : Fin 4 → Kˣ) l = d := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hkl.symm, Pi.mulSingle_eq_same, one_mul]

theorem act_dg_two_of_coord {k l : Fin 4} (c d : Kˣ) {x : Fin (2 * 4) → K} (hek : x (ie k) = 0)
    (hfk : x (jf k) = 0) (hel : x (ie l) = 0) (hfl : x (jf l) = 0) :
    act (dg (Pi.mulSingle k c * Pi.mulSingle l d)) x = x := by
  rw [act_dg]
  funext a
  rcases ie_or_jf a with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · by_cases hmk : m = k
    · subst hmk
      rw [hek, mul_zero]
    · by_cases hml : m = l
      · subst hml
        rw [hel, mul_zero]
      · rw [twHom_ie, mulSingle_two_of_ne hmk hml, Units.val_one, one_mul]
  · by_cases hmk : m = k
    · subst hmk
      rw [hfk, mul_zero]
    · by_cases hml : m = l
      · subst hml
        rw [hfl, mul_zero]
      · rw [twHom_jf, mulSingle_two_of_ne hmk hml, inv_one, Units.val_one, one_mul]

theorem dg_mem_leviFix {k l : Fin 4} (hkl : k ≠ l) {c d : Kˣ}
    {P₂ : HypPair (coordinateQuadPlus 4 K)}
    (h2e : act (dg (Pi.mulSingle k c * Pi.mulSingle l d)) P₂.e = ((c⁻¹ : Kˣ) : K) • P₂.e)
    (h2f : act (dg (Pi.mulSingle k c * Pi.mulSingle l d)) P₂.f = (c : K) • P₂.f)
    (hW2 : ∀ x, polar (coordinateQuadPlus 4 K) P₂.e x = 0 →
      polar (coordinateQuadPlus 4 K) P₂.f x = 0 → x (ie l) = 0 ∧ x (jf l) = 0) :
    ((derivedEquiv (coordinateQuadPlus 4 K) (dg (Pi.mulSingle k c * Pi.mulSingle l d)) :
      orthDerived (coordinateQuadPlus 4 K)) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
      leviFix (orthDerived (coordinateQuadPlus 4 K)) (plusPair K k) P₂ := by
  set L := ((derivedEquiv (coordinateQuadPlus 4 K) (dg (Pi.mulSingle k c * Pi.mulSingle l d)) :
    orthDerived (coordinateQuadPlus 4 K)) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) with hL
  have hLa : ∀ v, L v = act (dg (Pi.mulSingle k c * Pi.mulSingle l d)) v :=
    fun v => derivedEquiv_apply _ v
  have hk := isHypCoord_coordinateQuadPlus (K := K) (n := 4) k
  refine mem_leviFix_of_scale (derivedEquiv (coordinateQuadPlus 4 K) _).2
    (Subgroup.commutator_le_self _ (derivedEquiv (coordinateQuadPlus 4 K) _).2) c ?_ ?_
    (by rw [hLa]; exact h2e) (by rw [hLa]; exact h2f) ?_
  · rw [hLa]
    change act _ (Pi.single (ie k) 1) = _
    rw [act_dg_single, twHom_ie, mulSingle_two_left hkl]
    rfl
  · rw [hLa]
    change act _ (Pi.single (jf k) 1) = _
    rw [act_dg_single, twHom_jf, mulSingle_two_left hkl]
    rfl
  · rintro x ⟨h1, h2, h3, h4⟩
    rw [hLa]
    have hjk : x (jf k) = 0 := by rw [← hk.polar_left x]; exact h1
    have hik : x (ie k) = 0 := by rw [← hk.polar_right x]; exact h2
    obtain ⟨hil, hjl⟩ := hW2 x h3 h4
    exact act_dg_two_of_coord c d hik hjk hil hjl

theorem dg_mem_rootPlus {k l : Fin 4} (hkl : k ≠ l) (c : Kˣ) :
    dg (Pi.mulSingle k c * Pi.mulSingle l c) ∈ rootPlus (K := K) k l := by
  have hl := isHypCoord_coordinateQuadPlus (K := K) (n := 4) l
  show proj _ ∈ leviFixBar (plusPair K k) (flipPair (plusPair K l))
  rw [← projHom_derivedEquiv]
  refine projHom_mem_leviFixBar (dg_mem_leviFix hkl ?_ ?_ ?_)
  · change act _ (Pi.single (jf l) 1) = _
    rw [act_dg_single, twHom_jf, mulSingle_two_right hkl]
    rfl
  · change act _ (Pi.single (ie l) 1) = _
    rw [act_dg_single, twHom_ie, mulSingle_two_right hkl]
    rfl
  · intro x h1 h2
    exact ⟨by rw [← hl.polar_right x]; exact h1, by rw [← hl.polar_left x]; exact h2⟩

theorem dg_mem_rootMinus {k l : Fin 4} (hkl : k ≠ l) (c : Kˣ) :
    dg (Pi.mulSingle k c * Pi.mulSingle l c⁻¹) ∈ rootMinus (K := K) k l := by
  have hl := isHypCoord_coordinateQuadPlus (K := K) (n := 4) l
  show proj _ ∈ leviFixBar (plusPair K k) (plusPair K l)
  rw [← projHom_derivedEquiv]
  refine projHom_mem_leviFixBar (dg_mem_leviFix hkl ?_ ?_ ?_)
  · change act _ (Pi.single (ie l) 1) = _
    rw [act_dg_single, twHom_ie, mulSingle_two_right hkl]
    rfl
  · change act _ (Pi.single (jf l) 1) = _
    rw [act_dg_single, twHom_jf, mulSingle_two_right hkl, inv_inv]
    rfl
  · intro x h1 h2
    exact ⟨by rw [← hl.polar_right x]; exact h2, by rw [← hl.polar_left x]; exact h1⟩

end Torus

end L613O4

end CFSG.StandardType
