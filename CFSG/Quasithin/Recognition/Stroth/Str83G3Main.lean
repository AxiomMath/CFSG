module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexM6
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_disp_z2_ge_of_c_eq_two
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hser : IsChiefSeriesFrom (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) 2) :
    ∀ t ∈ S, t * t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
      t ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
      (2 ^ (2 * a + 1)) ^ 2 ≤
        (Z2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hL2sup : IsL2Quot (2 * a + 1) (oTwoQuot ↥(L2 ⊔ S)) := by
    obtain ⟨eL⟩ := hL2
    rw [hsup2]
    have hsupQ : L2 ⊔ Q2 L1 L2 S = L2 ⊔ Q1 L2 L1 S := by
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hsupQ]
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
  have hQ2S : Q2 L1 L2 S ≤ S :=
    (le_sup_right : Q2 L1 L2 S ≤ (S ⊓ L2) ⊔ Q2 L1 L2 S).trans hS2.symm.le
  have hZ2H : Z2 L1 L2 S ≤ L2 ⊔ S :=
    (omegaOneCenterOf_le (Q2 L1 L2 S)).trans (hQ2S.trans le_sup_right)
  have hZ2p : IsPGroup 2 (Z2 L1 L2 S) :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le (omegaOneCenterOf_le (Q2 L1 L2 S))
  have hSQ2 : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.2.2.1
  intro t htS htC htNC
  have htQ2 : t * t ∈ Q2 L1 L2 S := by
    rw [← hSQ2]
    exact ⟨S.mul_mem htS htS, htC⟩
  have htNQ2 : t ∉ Q2 L1 L2 S := fun hmem =>
    htNC (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hmem)
  have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) htS
  have ht : t * t ∈ pCoreOf 2 (L2 ⊔ S) := by rwa [hpCore2]
  have htO : t ∉ pCoreOf 2 (L2 ⊔ S) := by rwa [hpCore2]
  have h := l2_pow_sq_le_relIndex_centralizer (H := L2 ⊔ S) (U := Z2 L1 L2 S)
    (m := 2 * a + 1) (c := 2) (by omega) hL2sup hZ2p hZ2H hser htH ht htO
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  simpa [hcent, Subgroup.inf_relIndex_left] using h

theorem str83_relIndex_quadratic_le
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ∀ A : Subgroup G, A ≤ S → (∀ x ∈ A, ∀ y ∈ A,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) ∧
        x * x ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G)) →
    (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A ≤ 2 ^ (2 * a + 1) := by
  have hSQ2 : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.2.2.1
  intro A hAS hAq
  have hArel : (A ⊓ Q2 L1 L2 S).relIndex A ≤ 2 ^ (2 * a + 1) := by
    rw [Subgroup.inf_relIndex_left]
    calc (Q2 L1 L2 S).relIndex A ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hAS (D15Proof.relIndex_ne_zero _ _)
      _ = 2 ^ (2 * a + 1) := by
          have h := str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
          simpa using h
  refine (Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)).trans hArel
  refine le_inf inf_le_left ?_
  intro x hx
  exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hx.2

end CFSG.Quasithin.Stroth

end
