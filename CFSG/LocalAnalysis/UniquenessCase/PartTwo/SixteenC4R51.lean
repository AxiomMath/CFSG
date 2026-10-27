module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R50
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16QModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

theorem s16c4_le_lBar_of_calABar (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L)
    {A : Subgroup (MulAut (Vtil V₀ V hV))} (hA : A ∈ calABar 2 D.M V₀ V hV) :
    A ≤ lBar V₀ V hV L := by
  obtain ⟨hAM, hA1, hAab, hAfix⟩ := hA
  let ρ : ↥A →* Equiv.Perm (Fin 4 → F.K) :=
    { toFun := fun φ => (F.rho (φ : MulAut (Vtil V₀ V hV))).toEquiv
      map_one' := Equiv.ext fun x => by simp [UFrame.rho]
      map_mul' := fun φ ψ => Equiv.ext fun x => by
        rw [Equiv.Perm.mul_apply]
        exact F.rho_mul (φ : MulAut (Vtil V₀ V hV)) (ψ : MulAut (Vtil V₀ V hV)) x }
  have hH2 : ∀ h : ↥A, h * h = 1 := by
    intro h
    apply Subtype.ext
    show (h : MulAut (Vtil V₀ V hV)) * (h : MulAut (Vtil V₀ V hV)) = 1
    simpa [pow_two] using hAab.2 (h : MulAut (Vtil V₀ V hV)) h.2
  have hadd : ∀ (h : ↥A) (x y : Fin 4 → F.K), ρ h (x + y) = ρ h x + ρ h y :=
    fun h x y => (F.rho (h : MulAut (Vtil V₀ V hV))).map_add x y
  have hN : ∀ h : ↥A, ∀ g ∈ StatedSU 4 (2 ^ 1) F.K, ∃ g' ∈ StatedSU 4 (2 ^ 1) F.K,
      ∀ x : Fin 4 → F.K,
        ρ h⁻¹ (((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x) =
          ((g' : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ ρ h⁻¹ x := by
    intro h g hg
    have hgSU : g ∈ SUid F.σ 4 := by rw [F.suid_eq_statedSU]; exact hg
    let γ : ↥(SUid F.σ 4) := ⟨g, hgSU⟩
    let φ : MulAut (Vtil V₀ V hV) := ((h⁻¹ : ↥A) : MulAut (Vtil V₀ V hV))
    have hφN : φ ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
      F.Mbar_le_normalizer hS (hAM (h⁻¹).2)
    have hmem : φ * (F.π γ) * φ⁻¹ ∈ lBar V₀ V hV L :=
      (Subgroup.mem_set_normalizer_iff.1 hφN (F.π γ)).1 (F.π γ).2
    let γ' : ↥(SUid F.σ 4) := F.π.symm ⟨φ * (F.π γ) * φ⁻¹, hmem⟩
    have hπγ' : (F.π γ' : MulAut (Vtil V₀ V hV)) = φ * (F.π γ) * φ⁻¹ := by
      simp [γ']
    refine ⟨(γ' : GL (Fin 4) F.K), ?_, ?_⟩
    · rw [← F.suid_eq_statedSU]; exact γ'.2
    · intro x
      have hx1 : F.ofVec (g *ᵥ x) = (F.π γ : MulAut (Vtil V₀ V hV)) (F.ofVec x) := by
        apply F.vec_injective
        rw [F.vec_ofVec, F.vec_action, CFSG.ClassicalGroups.Unitary.smul_def]
        simp [γ]
      have hrho : ∀ y : Fin 4 → F.K, F.rho φ y = F.vec (φ (F.ofVec y)) := fun y => rfl
      show F.rho φ (g *ᵥ x) =
        ((γ' : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ F.rho φ x
      rw [← F.vec_ofVec (g *ᵥ x), F.rho_vec, hrho]
      rw [← CFSG.ClassicalGroups.Unitary.smul_def, ← F.vec_action γ' (φ (F.ofVec x))]
      rw [F.vec_injective.eq_iff]
      rw [hx1, hπγ']
      simp [MulAut.mul_apply]
  have hQ : ∀ K : Subgroup ↥A, K.index < Nat.card F.K → ∀ x : Fin 4 → F.K,
      (∀ k ∈ K, ρ k x = x) → ∀ h : ↥A, ρ h x = x := by
    intro K hK x hx h
    let K' : Subgroup (MulAut (Vtil V₀ V hV)) := K.map A.subtype
    have hK'le : K' ≤ A := Subgroup.map_subtype_le K
    have hrel : K'.relIndex A = K.index := by
      have h := Subgroup.relIndex_map_map_of_injective (f := A.subtype) K ⊤ A.subtype_injective
      rwa [Subgroup.map_top, A.range_subtype, Subgroup.relIndex_top_right] at h
    have hmq : E3.mQuot A K' < 2 := by
      have hdvd : K.index ∣ Nat.card ↥A := Subgroup.index_dvd_card K
      have hcard : Nat.card ↥A = 2 ^ rk ↥A :=
        card_eq_two_pow_of_isPGroup (IsElemAbelian2.isPGroup hAab)
      have hdvd' : K.index ∣ 2 ^ rk ↥A := by rwa [← hcard]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
      have hjlt : j < 2 := by
        have h2 : (2 : ℕ) ^ j < 2 ^ 2 := by
          rw [← hj]
          rw [show Nat.card F.K = 2 ^ 2 by rw [F.card_K]; norm_num] at hK
          exact hK
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h2
      show padicValNat 2 (K'.relIndex A) < 2
      rw [hrel, hj, padicValNat.prime_pow]
      omega
    have hfixA : fixV K' = fixV A := hAfix K' hK'le hmq
    have hfixK : F.ofVec x ∈ fixV K' := by
      rw [mem_fixV]
      intro k hk
      obtain ⟨k₀, hk₀K, rfl⟩ := Subgroup.mem_map.1 hk
      apply F.vec_injective
      change F.vec (((k₀ : ↥A) : MulAut (Vtil V₀ V hV)) (F.ofVec x)) = F.vec (F.ofVec x)
      rw [← F.rho_vec (k₀ : ↥A) (F.ofVec x), F.vec_ofVec]
      exact hx k₀ hk₀K
    have hfixA' : F.ofVec x ∈ fixV A := hfixA ▸ hfixK
    rw [mem_fixV] at hfixA'
    show F.rho h x = x
    rw [← F.vec_ofVec x]
    exact (F.rho_vec h (F.ofVec x)).trans (congrArg F.vec (hfixA' h h.2))
  have hMQ := model_Q (n := 1) (by rw [F.card_K]; norm_num) le_rfl hH2 ρ hadd hN hQ
  intro a ha
  obtain ⟨g, hg, hgx⟩ := hMQ ⟨a, ha⟩
  have hgSU : g ∈ SUid F.σ 4 := by rw [F.suid_eq_statedSU]; exact hg
  let γ : ↥(SUid F.σ 4) := ⟨g, hgSU⟩
  have haeq : a = (F.π γ : MulAut (Vtil V₀ V hV)) := by
    apply MulEquiv.ext
    intro w
    apply F.vec_injective
    rw [← F.rho_vec (⟨a, ha⟩ : ↥A) w, F.vec_action,
      CFSG.ClassicalGroups.Unitary.smul_def]
    exact hgx (F.vec w)
  rw [haeq]
  exact (F.π γ).2

theorem r16_51_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hV1 : Case167_4_V1Eq D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_4 D V₀ V hV L →
        ∀ A ∈ E3.gammaSet V 0 D.M, barSub V₀ V hV A ≠ ⊥ →
          barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV ∧ barSub V₀ V hV A ≤ lBar V₀ V hV L := by
  intro V₀ V L hV hS h4 A hA hA1
  have hcal := sixteen_fiftyOne_calABar D hSg h1219 h21 h22 (r16_50_holds D h61 hV1)
    V₀ V L hV hS h4 hA hA1
  obtain ⟨F⟩ := exists_uFrame D h4 (hV1.v1Sub_eq hS h4)
  exact ⟨hcal, s16c4_le_lBar_of_calABar D hS F hcal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
