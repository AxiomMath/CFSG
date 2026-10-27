module

public import CFSG.Milestones.ASVolI.F431.BCoreGen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ASVolI.ChF.ClassicalRoots
open scoped Pointwise

section Transport

variable {K : Type} [Field K] {r ε : ℕ}

@[expose] noncomputable def burnsideF4m_hypR (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    Matrix (Fin (2 * r + ε)) (HypIndex r ε) K :=
  B.submatrix id fullPosEquiv

theorem burnsideF4m_hypR_mulVec (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (w : HypIndex r ε → K) :
    burnsideF4m_hypR B *ᵥ w = B *ᵥ (w ∘ fullPosEquiv.symm) :=
  submatrix_mulVec_equiv B w id fullPosEquiv

theorem burnsideF4m_isHypTransport {p f : ℕ} (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hB : ∀ i j : Fin (2 * r + ε),
      ((B.map h.bar)ᵀ * B) i j = if i.val + j.val + 1 = 2 * r + ε then 1 else 0) :
    IsHypTransport h (burnsideF4m_hypR B) := by
  ext a b
  have h1 : (((burnsideF4m_hypR B).map h.bar)ᵀ * burnsideF4m_hypR B) a b =
      ((B.map h.bar)ᵀ * B) (fullPosEquiv a) (fullPosEquiv b) := by
    simp [Matrix.mul_apply, burnsideF4m_hypR]
  show (((burnsideF4m_hypR B).map h.bar)ᵀ * burnsideF4m_hypR B) a b = hypGram r ε K a b
  rw [h1, hB, hypGram_apply, fullPosEquiv_apply, fullPosEquiv_apply]
  have hpa := fullPos_hypPartner (r := r) hε a
  have hla := fullPos_lt a
  have hlb := fullPos_lt b
  by_cases hb : b = hypPartner a
  · subst hb
    rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg hb, if_neg]
    intro hab
    apply hb
    apply fullPos_injective
    omega

variable {p f : ℕ} (h : UnitaryFieldData p f K) {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem burnsideF4m_mem_image_iff (hR : IsHypTransport h R) (W : Set (HypIndex r ε → K))
    (v : Fin (2 * r + ε) → K) :
    v ∈ (fun w => R *ᵥ w) '' W ↔ transportInv h R *ᵥ v ∈ W := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mulVec_mulVec, transportInv_mul hR, one_mulVec]
    exact hw
  · intro hv
    exact ⟨_, hv, by
      show R *ᵥ (transportInv h R *ᵥ v) = v
      rw [mulVec_mulVec, mul_transportInv hR, one_mulVec]⟩

theorem burnsideF4m_transportInv_mulVec (hR : IsHypTransport h R) (g : hypSU h r ε)
    (v : Fin (2 * r + ε) → K) :
    transportInv h R *ᵥ (((hypTransport h hR g : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v) =
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        (transportInv h R *ᵥ v) := by
  rw [coe_hypTransport, mulVec_mulVec, mulVec_mulVec]
  congr 1
  rw [show transportInv h R * (R * ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R) =
    (transportInv h R * R) * ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R by
    simp only [Matrix.mul_assoc], transportInv_mul hR, Matrix.one_mul]

theorem burnsideF4m_stab_iff (hR : IsHypTransport h R) (W : Set (HypIndex r ε → K))
    (g : hypSU h r ε) :
    (∀ v, ((hypTransport h hR g : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈ (fun w => R *ᵥ w) '' W ↔
          v ∈ (fun w => R *ᵥ w) '' W) ↔
      ∀ w, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W ↔
        w ∈ W := by
  simp only [burnsideF4m_mem_image_iff h hR, burnsideF4m_transportInv_mulVec h hR]
  constructor
  · intro H w
    have e : transportInv h R *ᵥ (R *ᵥ w) = w := by
      rw [mulVec_mulVec, transportInv_mul hR, one_mulVec]
    have := H (R *ᵥ w)
    rwa [e] at this
  · intro H v
    exact H _

theorem burnsideF4m_image_posFlag (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) (i : ℕ)
    (S : Set (Fin (2 * r + ε))) (hS : ∀ j : Fin (2 * r + ε), j ∉ S ↔ i ≤ (j : ℕ))
    (v : Fin (2 * r + ε) → K) :
    v ∈ (fun w => burnsideF4m_hypR B *ᵥ w) ''
        ((posFlag r ε K i : Submodule K (HypIndex r ε → K)) : Set (HypIndex r ε → K)) ↔
      v ∈ (fun u => B *ᵥ u) '' {u : Fin (2 * r + ε) → K | ∀ j, j ∉ S → u j = 0} := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w ∘ fullPosEquiv.symm, fun j hj => ?_, (burnsideF4m_hypR_mulVec B w).symm⟩
    exact hw (fullPosEquiv.symm j) (by rw [fullPos_fullPosEquiv_symm]; exact (hS j).1 hj)
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u ∘ fullPosEquiv, fun a ha => ?_, ?_⟩
    · exact hu _ ((hS _).2 (by rw [fullPosEquiv_apply]; exact ha))
    · show burnsideF4m_hypR B *ᵥ (u ∘ fullPosEquiv) = B *ᵥ u
      rw [burnsideF4m_hypR_mulVec]
      congr 1
      ext j
      simp

theorem burnsideF4m_mem_isoStabilizer_iff (hε : ε ≤ 1)
    (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hR : IsHypTransport h (burnsideF4m_hypR B)) (i : ℕ) (hi : i ≤ 2 * r + ε)
    (S : Set (Fin (2 * r + ε))) (hS : ∀ j : Fin (2 * r + ε), j ∉ S ↔ i ≤ (j : ℕ))
    (g : hypSU h r ε) :
    g ∈ UnitaryHigher.isoStabilizer h r ε (hypFlag h r ε i) ↔
      ∀ v : Fin (2 * r + ε) → K, ((hypTransport h hR g : GL (Fin (2 * r + ε)) K) :
          Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈
            (fun u => B *ᵥ u) '' {u : Fin (2 * r + ε) → K | ∀ j, j ∉ S → u j = 0} ↔
          v ∈ (fun u => B *ᵥ u) '' {u : Fin (2 * r + ε) → K | ∀ j, j ∉ S → u j = 0} := by
  rw [UnitaryHigher.mem_isoStabilizer, hypFlag_eq_posFlag h hε hi,
    Subgroup.smul_def, burnsideF4gU4_smul_eq_iff]
  have := burnsideF4m_stab_iff h hR
    ((posFlag r ε K i : Submodule K (HypIndex r ε → K)) : Set (HypIndex r ε → K)) g
  simp only [burnsideF4m_image_posFlag B i S hS, SetLike.mem_coe] at this
  exact this.symm

end Transport

section U5Marking

variable {f : ℕ} {H : Type} [Group H] (marking : Marking .U5 2 f H)

theorem burnsideF4m_U5_fieldData : UnitaryFieldData 2 f marking.field :=
  ⟨Nat.prime_two, marking.exponent_pos, by
    have := marking.field_card
    simp only [or_true, if_true] at this
    rw [this, ← pow_mul, mul_comm]⟩

theorem burnsideF4m_U5_basis_gram (i j : Fin (2 * 2 + 1)) :
    (((marking.basis : Matrix (Fin 5) (Fin 5) marking.field).map
        (burnsideF4m_U5_fieldData marking).bar)ᵀ *
      (marking.basis : Matrix (Fin 5) (Fin 5) marking.field)) i j =
      if i.val + j.val + 1 = 2 * 2 + 1 then 1 else 0 := by
  have h1 := congrFun (congrFun marking.basis_compatible i) j
  have hbar : (⇑(burnsideF4m_U5_fieldData marking).bar : marking.field → marking.field) =
      fun e => e ^ 2 ^ f := funext (burnsideF4m_U5_fieldData marking).bar_apply
  rw [hbar]
  exact h1

theorem burnsideF4m_U5_isHypTransport :
    IsHypTransport (burnsideF4m_U5_fieldData marking)
      (burnsideF4m_hypR (r := 2) (ε := 1)
        (marking.basis : Matrix (Fin 5) (Fin 5) marking.field)) :=
  burnsideF4m_isHypTransport _ (by norm_num) _ (burnsideF4m_U5_basis_gram marking)

noncomputable def burnsideF4m_U5_T :
    hypSU (burnsideF4m_U5_fieldData marking) 2 1 ≃* nativeGroup .U5 (2 ^ f) marking.field :=
  hypTransport (burnsideF4m_U5_fieldData marking) (burnsideF4m_U5_isHypTransport marking)

theorem burnsideF4m_U5_parabolic_false :
    nativeParabolic .U5 (2 ^ f) marking.field marking.basis false =
      (UnitaryHigher.isoStabilizer (burnsideF4m_U5_fieldData marking) 2 1
        (hypFlag (burnsideF4m_U5_fieldData marking) 2 1 1)).map
        (burnsideF4m_U5_T marking).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have key := burnsideF4m_mem_isoStabilizer_iff (r := 2) (ε := 1)
    (burnsideF4m_U5_fieldData marking) (by norm_num)
    (marking.basis : Matrix (Fin 5) (Fin 5) marking.field)
    (burnsideF4m_U5_isHypTransport marking) 1 (by norm_num) {0}
    (by intro j; fin_cases j <;> simp) ((burnsideF4m_U5_T marking).symm x)
  have e : hypTransport (burnsideF4m_U5_fieldData marking)
      (burnsideF4m_U5_isHypTransport marking)
      ((burnsideF4m_U5_T marking).symm x) = x := (burnsideF4m_U5_T marking).apply_symm_apply x
  rw [e] at key
  show (x : GL (Coord .U5) marking.field) ∈ rawStabilizer _ ↔ _
  rw [burnsideF4f_mem_rawStabilizer]
  exact key.symm

theorem burnsideF4m_U5_parabolic_true :
    nativeParabolic .U5 (2 ^ f) marking.field marking.basis true =
      (UnitaryHigher.isoStabilizer (burnsideF4m_U5_fieldData marking) 2 1
        (hypFlag (burnsideF4m_U5_fieldData marking) 2 1 2)).map
        (burnsideF4m_U5_T marking).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have key := burnsideF4m_mem_isoStabilizer_iff (r := 2) (ε := 1)
    (burnsideF4m_U5_fieldData marking) (by norm_num)
    (marking.basis : Matrix (Fin 5) (Fin 5) marking.field)
    (burnsideF4m_U5_isHypTransport marking) 2 (by norm_num) {0, 1}
    (by intro j; fin_cases j <;> simp) ((burnsideF4m_U5_T marking).symm x)
  have e : hypTransport (burnsideF4m_U5_fieldData marking)
      (burnsideF4m_U5_isHypTransport marking)
      ((burnsideF4m_U5_T marking).symm x) = x := (burnsideF4m_U5_T marking).apply_symm_apply x
  rw [e] at key
  show (x : GL (Coord .U5) marking.field) ∈ rawStabilizer _ ↔ _
  rw [burnsideF4f_mem_rawStabilizer]
  exact key.symm

theorem burnsideF4m_U5_equiv :
    ∃ Ψ : CFSG.ClassicalGroups.UnitaryFlag.hypPSU (burnsideF4m_U5_fieldData marking) 2 1 ≃* H,
      marking.parabolic false =
        (H13.Sec53F.Unit.u5PtP (burnsideF4m_U5_fieldData marking)).map Ψ.toMonoidHom ∧
      marking.parabolic true =
        (H13.Sec53F.Unit.u5LnP (burnsideF4m_U5_fieldData marking)).map Ψ.toMonoidHom := by
  set hK := burnsideF4m_U5_fieldData marking
  set hR := burnsideF4m_U5_isHypTransport marking
  let Ψ : hypPSU hK 2 1 ≃* H := (hypPSUEquivStatedProj hK hR (by norm_num)).trans
    marking.identification
  have hcomp : Ψ.toMonoidHom.comp (hypProj hK 2 1) =
      marking.transport.comp (burnsideF4m_U5_T marking).toMonoidHom := by
    refine MonoidHom.ext fun g => ?_
    show marking.identification (hypPSUEquivStatedProj hK hR (by norm_num) (hypProj hK 2 1 g)) = _
    rw [hypPSUEquivStatedProj_hypProj]
    rfl
  refine ⟨Ψ, ?_, ?_⟩
  · rw [H13.Sec53F.Unit.u5PtP, projIsoStabilizer, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      ← burnsideF4m_U5_parabolic_false]
    rfl
  · rw [H13.Sec53F.Unit.u5LnP, projIsoStabilizer, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      ← burnsideF4m_U5_parabolic_true]
    rfl

end U5Marking

theorem burnsideF4m_U5_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U5 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K)
      (Ψ : CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1 ≃* ↥Gp),
      Gp ⊓ M₁ = (H13.Sec53F.Unit.u5PtP h).map (Gp.subtype.comp Ψ.toMonoidHom) ∧
      Gp ⊓ M₂ = (H13.Sec53F.Unit.u5LnP h).map (Gp.subtype.comp Ψ.toMonoidHom) := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp
  obtain ⟨Ψ, e1, e2⟩ := burnsideF4m_U5_equiv marking
  refine ⟨marking.field, inferInstance, burnsideF4m_U5_fieldData marking, Ψ, ?_, ?_⟩
  · rw [burnsideF4m_inf_eq_map Ψ (h1.trans e1)]
  · rw [burnsideF4m_inf_eq_map Ψ (h2.trans e2)]

end CFSG.ASVolI
