module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Cmp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem conj_mul_inv_mem_fix_iff (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) (ℓ : ↥L)
    (v : ↥V) :
    (ℓ : G) * v * (ℓ : G)⁻¹ * (v : G)⁻¹ ∈ V ⊓ Subgroup.centralizer ({t} : Set G) ↔
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩
          (((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
            Matrix (Fin 2) (Fin 2) h.data.K).mulVec (Multiplicative.toAdd (h.data.E v)) -
            Multiplicative.toAdd (h.data.E v)) =
        ((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
            Matrix (Fin 2) (Fin 2) h.data.K).mulVec (Multiplicative.toAdd (h.data.E v)) -
          Multiplicative.toAdd (h.data.E v) := by
  have hℓN : (ℓ : G) ∈ Subgroup.normalizer (V : Set G) := h.data.le_normalizer ℓ.2
  have hv' : (ℓ : G) * v * (ℓ : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hℓN v).mp v.2
  have hw : (ℓ : G) * v * (ℓ : G)⁻¹ * (v : G)⁻¹ ∈ V := V.mul_mem hv' (V.inv_mem v.2)
  have hE : Multiplicative.toAdd (h.data.E ⟨(ℓ : G) * v * (ℓ : G)⁻¹ * (v : G)⁻¹, hw⟩) =
      ((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec (Multiplicative.toAdd (h.data.E v)) -
        Multiplicative.toAdd (h.data.E v) := by
    have e : (⟨(ℓ : G) * v * (ℓ : G)⁻¹ * (v : G)⁻¹, hw⟩ : ↥V) = ⟨_, hv'⟩ * v⁻¹ := rfl
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg,
      h.toAdd_E_conj_rho ℓ v.2 hv']
  rw [← h.mem_addSub_fix_iff htT, ← hE]
  exact (h.data.toAdd_mem_addSub (U := V ⊓ Subgroup.centralizer ({t} : Set G))
    ⟨(ℓ : G) * v * (ℓ : G)⁻¹ * (v : G)⁻¹, hw⟩).symm

theorem exists_unipotent_pair (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) (hn4 : 4 ≤ n) :
    ∃ x₁ ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
      ∃ x₂ ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
        x₁ * x₁ ∈ Subgroup.centralizer (V : Set G) ∧ x₂ * x₂ ∈ Subgroup.centralizer (V : Set G) ∧
        x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
        (∃ v ∈ V, x₁ * v * x₁⁻¹ * v⁻¹ ∉ V ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        (∃ v ∈ V, x₂ * v * x₂⁻¹ * v⁻¹ ∉ V ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        (∃ v ∈ V, x₁ * x₂ * v * (x₁ * x₂)⁻¹ * v⁻¹ ∉ V ⊓ Subgroup.centralizer ({t} : Set G)) := by
  classical
  have : CharP h.data.K 2 := charP_two_of_two_dvd h.two_dvd_card_K
  have h2K : (2 : h.data.K) = 0 := CharTwo.two_eq_zero
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  obtain ⟨σ, u₁, u₂, hσ, hu₁, hu₂, hdet, hc⟩ := h.exists_fieldAut_data htT ht
  obtain ⟨θ, hθ⟩ := h.exists_ne_of_fieldAut htT ht hσ
  have h4 := four_le_card_fixField h hc hn4
  obtain ⟨ω, hωσ, hω0, hω1⟩ : ∃ ω : h.data.K, σ ω = ω ∧ ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ x : ↥(stabFixField σ), x = 0 ∨ x = 1 := by
      intro x
      by_cases hx0 : (x : h.data.K) = 0
      · exact Or.inl (Subtype.ext hx0)
      · exact Or.inr (Subtype.ext (hcon x (mem_stabFixField.mp x.2) hx0))
    have : Nat.card ↥(stabFixField σ) ≤ 2 := by
      have hsurj : Function.Surjective (![0, 1] : Fin 2 → ↥(stabFixField σ)) := by
        intro x
        rcases hsub x with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      have := Nat.card_le_card_of_surjective _ hsurj
      rwa [Nat.card_fin] at this
    omega
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    simp [det2] at hdet
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu₁0
  simp only [Pi.zero_apply] at hi
  have hdet₁ : det2 u₁ (u₂ + u₁) = det2 u₁ u₂ := by
    simp only [det2, Pi.add_apply]
    ring
  have hdet₂ : det2 u₁ (u₂ + ω • u₁) = det2 u₁ u₂ := by
    simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨B₁, hB₁1, hB₁2⟩ := exists_sl2_basis hdet (by rw [hdet₁] : det2 u₁ (u₂ + u₁) = _)
  obtain ⟨B₂, hB₂1, hB₂2⟩ := exists_sl2_basis hdet (by rw [hdet₂] : det2 u₁ (u₂ + ω • u₁) = _)
  have hB₁S : B₁ ∈ stabSub (h.data.conj tt) := mem_stabSub_of_basis hσ hu₁ hu₂ hdet
    (by rw [hB₁1, hu₁]) (by rw [hB₁2, map_add, hu₂, hu₁])
  have hB₂S : B₂ ∈ stabSub (h.data.conj tt) := mem_stabSub_of_basis hσ hu₁ hu₂ hdet
    (by rw [hB₂1, hu₁]) (by rw [hB₂2, map_add, hu₂, hσ, hu₁, hωσ])
  have hB₁sq : B₁ * B₁ = 1 := eq_one_of_basis hdet
    (by rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB₁1, hB₁1])
    (by
      rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB₁2, Matrix.mulVec_add,
        hB₁2, hB₁1]
      funext k
      simp only [Pi.add_apply]
      linear_combination (u₁ k) * h2K)
  have hB₂sq : B₂ * B₂ = 1 := eq_one_of_basis hdet
    (by rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB₂1, hB₂1])
    (by
      rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB₂2, Matrix.mulVec_add,
        Matrix.mulVec_smul, hB₂2, hB₂1]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (ω * u₁ k) * h2K)
  have hB₁₂ : B₁ * B₂ = B₂ * B₁ := by
    apply Subtype.ext
    apply matrix_eq_of_mulVec_eq
    intro w
    rw [eq_add_of_det2_ne_zero hdet w]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_smul, hB₁1, hB₁2, hB₂1, hB₂2]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hS := h.map_lOne_fix_eq htT ht hn4
  rw [← hS] at hB₁S hB₂S
  obtain ⟨x₁, hx₁, hρ₁⟩ := Subgroup.mem_map.mp hB₁S
  obtain ⟨x₂, hx₂, hρ₂⟩ := Subgroup.mem_map.mp hB₂S
  have hcen : ∀ y : ↥L, h.data.rho y = 1 → (y : G) ∈ Subgroup.centralizer (V : Set G) :=
    fun y hy => (h.data.mem_ker_rho_iff y).mp hy
  set v : ↥V := h.data.E.symm (Multiplicative.ofAdd (θ • u₂)) with hvdef
  have hEv : Multiplicative.toAdd (h.data.E v) = θ • u₂ := by simp [hvdef]
  have hmove : ∀ (y : ↥L) (c : h.data.K), σ c = c → c ≠ 0 →
      ((h.data.rho y : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₂ = u₂ + c • u₁ →
      ((h.data.rho y : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec u₁ = u₁ →
      (y : G) * v * (y : G)⁻¹ * (v : G)⁻¹ ∉ V ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro y c hcσ hc0 hy2 hy1 hmem
    rw [h.conj_mul_inv_mem_fix_iff htT y v] at hmem
    rw [hEv, Matrix.mulVec_smul, hy2, smul_add, add_sub_cancel_left, smul_smul, hσ,
      hu₁] at hmem
    have := congrFun hmem i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hcσ] at this
    apply hθ
    have h3 : (σ θ - θ) * (c * u₁ i) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 (mul_ne_zero hc0 hi)
  refine ⟨x₁, Subgroup.mem_subgroupOf.mp hx₁, x₂, Subgroup.mem_subgroupOf.mp hx₂, ?_, ?_, ?_,
    ⟨v, v.2, ?_⟩, ⟨v, v.2, ?_⟩, ⟨v, v.2, ?_⟩⟩
  · exact hcen (x₁ * x₁) (by rw [map_mul, hρ₁, hB₁sq])
  · exact hcen (x₂ * x₂) (by rw [map_mul, hρ₂, hB₂sq])
  · exact hcen (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ₁, hρ₂, hB₁₂]
      group)
  · exact hmove x₁ 1 (map_one σ) one_ne_zero (by rw [hρ₁, hB₁2, one_smul])
      (by rw [hρ₁, hB₁1])
  · exact hmove x₂ ω hωσ hω0 (by rw [hρ₂, hB₂2]) (by rw [hρ₂, hB₂1])
  · have := hmove (x₁ * x₂) (1 + ω) (by rw [map_add, map_one, hωσ])
      (fun h0 => hω1 (by linear_combination h0 - h2K))
      (by
        rw [map_mul, hρ₁, hρ₂, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB₂2,
          Matrix.mulVec_add, Matrix.mulVec_smul, hB₁2, hB₁1, add_smul, one_smul]
        abel)
      (by rw [map_mul, hρ₁, hρ₂, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
        hB₂1, hB₁1])
    simpa [mul_assoc] using this

theorem commutator_mem_centralizer_of_le (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)))
    (hn4 : 4 ≤ n) {g : G}
    (hA : conjSubgroup V g ≤
      Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G)) :
    ∀ a ∈ conjSubgroup V g, ∀ x ∈ lOne L (V ⊓ Subgroup.centralizer ({t} : Set G)),
      a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set LU := lOne L U with hLU
  set A := conjSubgroup V g with hAdef
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have h1 := h.lemma_6_1_14_one h432 htT ht hSyl
  have hAN : A ≤ Subgroup.normalizer (LU : Set G) :=
    hA.trans (h.centralizer_le_normalizer_lOne_fix h432 h6110 h37 h39 htT ht hSyl hn4)
  have hRTU : R ≤ T ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf (sup_le inf_le_left (Subgroup.zpowers_le.mpr htT))
      (h1.1.le.trans (Subgroup.centralizer_le_normalizer _))
  have hRX : R ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.normalizer (LU : Set G) :=
    le_inf h1.1.le (hRTU.trans h.le_normalizer_lOne_fix)
  have hRsyl : IsSylowTwoOf R (Subgroup.centralizer (U : Set G) ⊓
      Subgroup.normalizer (LU : Set G)) := E6.isSylowIn_of_le h1.1 hRX inf_le_left
  have hA2 : IsPGroup 2 A :=
    isPGroup_conjSubgroup (F7.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian) g
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_isSylowTwoOf hRsyl (le_inf hA hAN) hA2
  have heq : cjSub y A = conjSubgroup V (g * y⁻¹) := by
    ext x
    rw [mem_cjSub, hAdef, mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    constructor <;> intro hx <;> simpa [mul_assoc] using hx
  have hyAQ : cjSub y A ≤ ch6Q T V := by
    have hmem : cjSub y A ∈ gammaSet V 0 R :=
      ⟨hyA, g * y⁻¹, heq.le, by rw [heq, mQuot_self]⟩
    exact (le_wClos hmem).trans (h.lemma_6_1_14_three h6110 htT ht).1
  have hQ := h.toHyp611.centralizer_eq
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLUL : LU ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hLUQ : LU ≤ Subgroup.normalizer (ch6Q T V : Set G) := hLUL.trans (le_sup_left.trans hLTQ)
  have hQLU : ch6Q T V ⊓ LU ≤ pCoreOf 2 LU := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hLUQ hx, Subgroup.le_normalizer hx⟩)
      ((h.sylow.1.to_le inf_le_left).to_le inf_le_left)
  have hQN : ch6Q T V ≤ Subgroup.normalizer (LU : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans ((Subgroup.centralizer_le inf_le_left).trans
      (Subgroup.centralizer_le_normalizer _)))).trans h.le_normalizer_lOne_fix
  have hO := h.pCoreOf_lOne_fix_le htT ht hn4
  intro a ha x hx
  have hq : y * a * y⁻¹ ∈ ch6Q T V := hyAQ (mem_cjSub.mpr (by simpa [mul_assoc] using ha))
  have hx' : y * x * y⁻¹ ∈ LU := (Subgroup.mem_normalizer_iff.mp hy.2 x).mp hx
  have hc : (y * a * y⁻¹) * (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ ∈
      ch6Q T V ⊓ LU := by
    refine ⟨?_, ?_⟩
    · have h2 : (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ ∈ ch6Q T V :=
        (Subgroup.mem_normalizer_iff.mp (hLUQ hx') _).mp (Subgroup.inv_mem _ hq)
      have e : (y * a * y⁻¹) * (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ =
          (y * a * y⁻¹) * ((y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hq h2
    · exact LU.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN hq) _).mp hx') (LU.inv_mem hx')
  have hc' := hQLU hc
  have hyO : y⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 LU : Subgroup G) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 LU (Subgroup.inv_mem _ hy.2)
  have e : a * x * a⁻¹ * x⁻¹ = y⁻¹ * ((y * a * y⁻¹) * (y * x * y⁻¹) * (y * a * y⁻¹)⁻¹ *
      (y * x * y⁻¹)⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact hO ((Subgroup.mem_normalizer_iff.mp hyO _).mp hc')

end Hyp611Nat

end CFSG.Quasithin.H13
