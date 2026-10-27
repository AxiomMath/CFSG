module

public import CFSG.Quasithin.H13.L32NLem14411e

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

theorem Ctx.JH (C : Ctx G T L V V₂ g D e) (k : ℕ) :
    lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T ≤ l32nH T V :=
  sup_le (sup_le L1H (xk_le_H k)) C.TH


theorem M12_eq : M12 = O7 1 ⊔ O7 2 ⊔ P7 := by
  rw [← sup_M7, ← O7_sup_P7 (Or.inl rfl), ← O7_sup_P7 (Or.inr rfl)]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_right)

namespace Ctx

variable (C : Ctx G T L V V₂ g D e)
include C

theorem img_J {j k : ℕ} (hj : j = 1 ∨ j = 2) (hjk : (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1))
    (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = M7 j) :
    img8 D e (lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T) = M12 := by
  have hk3 : k < 3 := by omega
  rw [img8_sup D e (sup_le L1H (xk_le_H k) |>.trans HN) (C.TH.trans HN),
    img8_sup D e (L1H.trans HN) ((xk_le_H k).trans HN), C.img_L1 hj hjeq, C.img_xk hk3,
    C.imgT, M12_eq]
  rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [sup_comm (O7 2)]

theorem nonempty_quot {j k : ℕ} (hj : j = 1 ∨ j = 2) (hjk : (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1))
    (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = M7 j) :
    Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    (C.JH k).trans HN
  have himg := C.img_J hj hjk hjeq
  let φ : ↥(lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T) →* ↥M12 :=
    (hom8 D e hJN).codRestrict M12 fun x => by
      rw [← himg, ← range_hom8 D e hJN]
      exact ⟨x, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨γ, hγ⟩
    rw [← himg, ← range_hom8 D e hJN] at hγ
    obtain ⟨x, rfl⟩ := hγ
    exact ⟨x, rfl⟩
  have hk : IsPGroup 2 (chi.comp φ).ker := by
    rintro ⟨x, hx⟩
    have hsq := sq_eq_one_of_chi (MonoidHom.mem_ker.mp hx)
    have hxx : hom8 D e hJN (x * x) = 1 := by
      rw [map_mul]
      exact hsq
    have hxQ : ((x * x : ↥(lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T)) : G) ∈ pCoreOf 2 (l32nH T V) :=
      (C.matOf_eq_one_iff (C.JH k (x * x).2)).mp hxx
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨_, hxQ⟩
    refine ⟨n + 1, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : ((x : G) * x) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, sq, h1]
  exact nonempty_quot_equiv_of_surj (chi.comp φ) (chi_surjective.comp hφ) hk s33_normal_two

end Ctx

theorem y1444Claim_of_ctx (C : Ctx G T L V V₂ g D e) : Y1444Claim T L V V₂ g := by
  obtain ⟨j, hj, hjeq⟩ := C.exists_j
  obtain ⟨k, hk, hjk⟩ : ∃ k, (k = 1 ∨ k = 2) ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) := by
    rcases hj with rfl | rfl
    · exact ⟨2, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inl rfl, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨xk D e k, ⟨xk_le_H k, C.T_le_normalizer_xk k, oTwoUpper_xk k, C.relIndex_xk hk,
    C.card_commutator hk, C.commutator_le_E hk⟩, fun h => ?_, C.nonempty_quot hj hjk hjeq⟩
  have h1 := C.img_xk (k := k) (by omega)
  rw [h, C.img_L1 hj hjeq] at h1
  rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact O7_ne h1
  · exact O7_ne h1.symm

theorem y1444Claim_of_case4 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11) (h12812 : Lemma12_8_12_two)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) (h4 : Case1442Four T V V₂ g D) :
    Y1444Claim T L V V₂ g := by
  obtain ⟨e, C⟩ := exists_ctx h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP
    hgH h4
  exact y1444Claim_of_ctx C

end CFSG.Quasithin.H13.L14411
