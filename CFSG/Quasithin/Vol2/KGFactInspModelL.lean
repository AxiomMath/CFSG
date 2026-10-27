module

public import CFSG.Quasithin.Vol2.KGFactInspSchur

public section

namespace CFSG.Quasithin.H13.KGInspOdd

open Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

@[expose] def InvCentModel (P : Type*) [Group P] (F₀ : Type*) [Field F₀] : Prop :=
  ∀ z : P, orderOf z = 2 → ∃ ι : SL(2, F₀) →* P, Function.Injective ι ∧
    ι.range ≤ centralizer ({z} : Set P) ∧
    ⁅centralizer ({z} : Set P), centralizer ({z} : Set P)⁆ ≤ ι.range ∧
    ∀ Hs : Subgroup SL(2, F₀), (∃ a ∈ Hs, ∃ b ∈ Hs, a * b ≠ b * a) →
      ∀ g ∈ centralizer ({z} : Set P), (∀ h ∈ Hs, g * ι h = ι h * g) →
        ∀ c ∈ centralizer ({z} : Set P), g * c = c * g

theorem model_of_param {S X H : Type*} [Group S] [Group X] [Group H] {F₀ : Type*} [Field F₀]
    (ρ : S →* X) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center S)
    (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1) (φ : H →* S)
    (hrange : φ.range = centralizer ({a} : Set S)) (T : Subgroup H) (hT : T.Normal)
    (hinj : ∀ t ∈ T, ρ (φ t) = 1 → t = 1) (hHT : ∀ A B : H, A * B * A⁻¹ * B⁻¹ ∈ T)
    (hschur : ∀ H₀ : Subgroup H, H₀ ≤ T → (∃ b ∈ H₀, ∃ c ∈ H₀, b * c ≠ c * b) →
      ∀ A : H, (∀ h ∈ H₀, A * h = h * A) → ∀ B : H, A * B = B * A)
    (eT : SL(2, F₀) ≃* ↥T) :
    ∃ ι : SL(2, F₀) →* X, Function.Injective ι ∧ ι.range ≤ centralizer ({ρ a} : Set X) ∧
      ⁅centralizer ({ρ a} : Set X), centralizer ({ρ a} : Set X)⁆ ≤ ι.range ∧
      ∀ Hs : Subgroup SL(2, F₀), (∃ a ∈ Hs, ∃ b ∈ Hs, a * b ≠ b * a) →
        ∀ g ∈ centralizer ({ρ a} : Set X), (∀ h ∈ Hs, g * ι h = ι h * g) →
          ∀ c ∈ centralizer ({ρ a} : Set X), g * c = c * g := by
  let ι : SL(2, F₀) →* X := (ρ.comp φ).comp (T.subtype.comp eT.toMonoidHom)
  have hι : ∀ s, ι s = ρ (φ (eT s)) := fun _ => rfl
  refine ⟨ι, (injective_iff_map_eq_one ι).mpr fun s hs => ?_, ?_, ?_, ?_⟩
  · have h1 : ((eT s : ↥T) : H) = 1 := hinj _ (eT s).2 hs
    exact eT.injective ((Subtype.ext h1).trans (map_one eT).symm)
  · rintro _ ⟨s, rfl⟩
    exact mem_centralizer_of_param ρ φ hrange _
  · refine (commutator_le_of_param ρ hρ hker h3 ha φ hrange T hHT).trans ?_
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := eT.surjective ⟨t, ht⟩
    exact ⟨s, by rw [hι, hs]⟩
  · rintro Hs ⟨b, hb, c, hc, hbc⟩ g hg hgH
    have hH₀ : (Hs.map eT.toMonoidHom).map T.subtype ≤ T := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    refine central_of_param ρ hρ hker h3 ha φ hrange T hT hinj hH₀
      (hschur _ hH₀ ⟨(eT b : H), ⟨eT b, ⟨b, hb, rfl⟩, rfl⟩, (eT c : H),
        ⟨eT c, ⟨c, hc, rfl⟩, rfl⟩, ?_⟩) hg ?_
    · intro h
      apply hbc
      apply eT.injective
      rw [map_mul, map_mul]
      exact Subtype.ext h
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact hgH s hs

variable {F : Type} [Field F]

theorem invCentModel_psl (h2 : (2 : F) ≠ 0) : InvCentModel (StatedProj (StatedSL 3 F)) F := by
  intro w hw
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSL 3 F))
    (statedProjMk_surjective _) (fun z hz => linConj_ker_pow_three z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  obtain ⟨φ, hφ, hrange⟩ := Lemma41aL3.exists_phi h2 (StatedSL 3 F)
    (fun A => linConj_mem_statedSL A) ha ha1
  have hdet : ∀ A : GL (Fin 2) F, A ∈ StatedSL 2 F ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
    fun A => linConj_mem_statedSL A
  have hinj : ∀ t ∈ StatedSL 2 F, statedProjMk (StatedSL 3 F) (φ t) = 1 → t = 1 := by
    intro t ht htk
    have htk' : φ t ∈ (statedProjMk (StatedSL 3 F)).ker := htk
    have htc := mem_center_iff.mp (ker_statedProjMk_le_center _ htk')
    have hc : t ∈ center (GL (Fin 2) F) := by
      rw [mem_center_iff]
      intro B
      apply hφ
      rw [map_mul, map_mul, htc (φ B)]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨d, rfl⟩ := hc
    have hd2 : (d : F) ^ 2 = 1 := by
      have := (hdet _).mp ht
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_fin_two] at this
      simpa [sq] using this
    have ht3 : Matrix.GeneralLinearGroup.scalar (Fin 2) d ^ 3 = 1 :=
      hφ (by rw [map_pow, linConj_ker_pow_three _ htk', map_one])
    have hd3 : (d : F) ^ 3 = 1 := by
      rw [← map_pow] at ht3
      have h1 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) ht3
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h1
      rw [Units.val_pow_eq_pow_val] at h1
      exact h1
    have hd1 : d = 1 := by
      have h1 : (d : F) ^ 3 = (d : F) ^ 2 * d := by ring
      rw [hd3, hd2, one_mul] at h1
      exact Units.ext h1.symm
    rw [hd1, map_one]
  refine model_of_param (statedProjMk (StatedSL 3 F)) (statedProjMk_surjective _)
    (ker_statedProjMk_le_center _) (fun z hz => linConj_ker_pow_three z hz) ha φ hrange
    (StatedSL 2 F) ⟨fun n hn g => ?_⟩ hinj (fun A B => ?_) ?_
    (specialLinearGroupEquivStatedSL 2 F)
  · rw [hdet] at hn ⊢
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, hn]
  · rw [hdet, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_units_conj,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · rintro H₀ - ⟨b, hb, c, hc, hbc⟩ A hA B
    exact commute_of_commute_gl (hA b hb) (hA c hc) hbc B

end CFSG.Quasithin.H13.KGInspOdd
