module

public import CFSG.Quasithin.H13.GoldschmidtU43DInv
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.Quasithin.H13.GoldschmidtU43DMat

public section

namespace CFSG.Quasithin.H13.U43

open Matrix CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6
open CFSG.ComponentClassification.PresentationLocal (sympFour antidiagGram omegaPerm
  mem_sympFour_iff omegaPerm_injective omegaPerm_surjective commutator_sympFour)

variable {G : Type} [Group G]

theorem gram_eq (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j : Fin 4) :
    (Mᵀ * antidiagGram * M) i j = Fvb (M.mulVec (idc i)) (M.mulVec (idc j)) := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, antidiagGram, Fvb, Matrix.mulVec, dotProduct,
      idc] <;> ring

theorem antidiag_eq (i j : Fin 4) : antidiagGram i j = Fvb (idc i) (idc j) := by
  fin_cases i <;> fin_cases j <;> simp [antidiagGram, Fvb, idc]

theorem mem_sympFour_of_Fvb (A : GL (Fin 4) (ZMod 2))
    (h : ∀ i j, Fvb ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (idc i))
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (idc j)) = Fvb (idc i) (idc j)) :
    A ∈ sympFour := by
  rw [mem_sympFour_iff]
  ext i j
  rw [gram_eq, h i j, antidiag_eq]

@[expose] def Cgl (l : ZMod 2) : GL (Fin 4) (ZMod 2) :=
  ⟨Cmat l, Cmat l, Cmat_mul_self l, Cmat_mul_self l⟩

theorem commutator_le_of_index_two {S : Type} [Group S] (R : Subgroup S) (h : R.index = 2) :
    commutator S ≤ R := by
  have hN := Subgroup.normal_of_index_eq_two h
  have hcard : Nat.card (S ⧸ R) = 2 := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (S ⧸ R) := isCyclic_of_prime_card (p := 2) hcard
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact (IsCyclic.isMulCommutative (α := S ⧸ R)).is_comm.comm _ _

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

@[expose] noncomputable def lam (z t w a : G) : ZMod 2 := Fv z t w a (idc 2) (idc 3)

theorem Fv_Cmat' (u v : V4) :
    Fv z t w a ((Cmat (lam z t w a)).mulVec u) ((Cmat (lam z t w a)).mulVec v) = Fvb u v :=
  s.Fv_Cmat ha u v

theorem conj_mem_sympFour (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) :
    Cgl (lam z t w a) * s.rho ha k * (Cgl (lam z t w a))⁻¹ ∈ sympFour := by
  have hPP : ∀ x : V4, (Cmat (lam z t w a)).mulVec ((Cmat (lam z t w a)).mulVec x) = x :=
    fun x => by rw [Matrix.mulVec_mulVec, Cmat_mul_self, Matrix.one_mulVec]
  have hA : ((Cgl (lam z t w a) * s.rho ha k * (Cgl (lam z t w a))⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = Cmat (lam z t w a) * s.Mat ha k * Cmat (lam z t w a) :=
    rfl
  apply mem_sympFour_of_Fvb
  intro i j
  rw [hA]
  simp only [← Matrix.mulVec_mulVec]
  rw [← s.Fv_Cmat' ha, ← s.Fv_Cmat' ha (idc i) (idc j), hPP, hPP, s.Fv_rho ha k]

@[expose] noncomputable def rhoS :
    ↥(Subgroup.normalizer (Eg z t w a : Set G)) →* ↥sympFour :=
  ((MulAut.conj (Cgl (lam z t w a))).toMonoidHom.comp (s.rho ha)).codRestrict sympFour
    (fun k => s.conj_mem_sympFour ha k)

theorem rhoS_eq_one_iff (k : ↥(Subgroup.normalizer (Eg z t w a : Set G))) :
    s.rhoS ha k = 1 ↔ (k : G) ∈ Eg z t w a := by
  rw [← s.rho_eq_one_iff ha]
  constructor
  · intro h1
    have h2 : Cgl (lam z t w a) * s.rho ha k * (Cgl (lam z t w a))⁻¹ = 1 :=
      congrArg Subtype.val h1
    have : s.rho ha k = 1 := by
      have := congrArg (fun g => (Cgl (lam z t w a))⁻¹ * g * Cgl (lam z t w a)) h2
      simpa [mul_assoc] using this
    exact this
  · intro h1
    apply Subtype.ext
    show Cgl (lam z t w a) * s.rho ha k * (Cgl (lam z t w a))⁻¹ = 1
    rw [h1]
    group

end Swap

theorem card_sympFour : Nat.card ↥sympFour = 720 := by
  have e : ↥sympFour ≃ Equiv.Perm (Fin 6) :=
    Equiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩
  rw [Nat.card_congr e, Nat.card_perm]
  simp [Nat.factorial]

theorem card_commutator_sympFour : Nat.card ↥(commutator ↥sympFour) = 360 := by
  have hbij : Function.Bijective omegaPerm := ⟨omegaPerm_injective, omegaPerm_surjective⟩
  have h1 : (alternatingGroup (Fin 6)).comap omegaPerm =
      (alternatingGroup (Fin 6)).map (MulEquiv.ofBijective omegaPerm hbij).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm (MulEquiv.ofBijective omegaPerm hbij) _
  rw [commutator_sympFour, h1, Subgroup.card_map_of_injective
    (MulEquiv.ofBijective omegaPerm hbij).symm.injective]
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  have h6 : Nat.card (Fin 6) = 6 := by simp
  rw [Nat.card_perm, h6, show Nat.factorial 6 = 720 by decide] at h
  omega

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

theorem ker_rhoS : (s.rhoS ha).ker = (Eg z t w a).subgroupOf
    (Subgroup.normalizer (Eg z t w a : Set G)) := by
  ext k
  rw [MonoidHom.mem_ker, s.rhoS_eq_one_iff ha]
  rfl

theorem range_rhoS : (s.rhoS ha).range = commutator ↥sympFour := by
  have h1 := Subgroup.card_mul_index (s.rhoS ha).ker
  rw [Subgroup.index_ker, s.ker_rhoS ha] at h1
  have hcardE : Nat.card ↥((Eg z t w a).subgroupOf
      (Subgroup.normalizer (Eg z t w a : Set G))) = 16 := by
    rw [← s.card_Eg ha]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  rw [hcardE, s.card_normalizer_Eg ha] at h1
  have hR : Nat.card (s.rhoS ha).range = 360 := by omega
  have hidx : (s.rhoS ha).range.index = 2 := by
    have := Subgroup.card_mul_index (s.rhoS ha).range
    rw [hR, card_sympFour] at this
    omega
  have hle : commutator ↥sympFour ≤ (s.rhoS ha).range :=
    commutator_le_of_index_two _ hidx
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hR, card_commutator_sympFour])).symm

theorem exists_hom_A6 : ∃ φ : ↥(Subgroup.normalizer (Eg z t w a : Set G)) →* Equiv.Perm (Fin 6),
    φ.ker = (Eg z t w a).subgroupOf (Subgroup.normalizer (Eg z t w a : Set G)) ∧
      φ.range = alternatingGroup (Fin 6) := by
  refine ⟨omegaPerm.comp (s.rhoS ha), ?_, ?_⟩
  · ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_eq_one_iff _ omegaPerm_injective,
      s.rhoS_eq_one_iff ha]
    rfl
  · ext σ
    constructor
    · rintro ⟨k, rfl⟩
      have hk : s.rhoS ha k ∈ commutator ↥sympFour := by
        rw [← s.range_rhoS ha]
        exact ⟨k, rfl⟩
      rw [commutator_sympFour] at hk
      exact hk
    · intro hσ
      obtain ⟨g, rfl⟩ := omegaPerm_surjective σ
      have hg : g ∈ commutator ↥sympFour := by
        rw [commutator_sympFour]
        exact hσ
      rw [← s.range_rhoS ha] at hg
      obtain ⟨k, rfl⟩ := hg
      exact ⟨k, rfl⟩

end Swap

end CFSG.Quasithin.H13.U43
