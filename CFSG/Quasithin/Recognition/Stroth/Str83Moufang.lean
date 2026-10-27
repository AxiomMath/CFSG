module

public import CFSG.Quasithin.Recognition.Stroth.F112Moufang
public import CFSG.Quasithin.Recognition.Stroth.WeissStrothLeaves
public import CFSG.Quasithin.Recognition.Stroth.F112U3Vertex
public import CFSG.Quasithin.Recognition.Stroth.Y9TwistedF4
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSt84HypA

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

theorem f112_relIndex_left_sz {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ (2 * (2 * a + 1)) + 1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hrel : (borelOf L1 S).relIndex L1 = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    have h' := index_borelOf_of_sz ha hF.1.h1.sylow (Classical.choice hSz)
    simpa [Subgroup.relIndex] using h'
  rw [F112W.relIndex_sup_eq_relIndex_inf (N := L1) (B := bigB L1 L2 S)
    ((F1.bigB_le_normalizer_left hR).1), F1.inf_bigB_eq_borelOf hR, hrel, ← pow_mul]
  congr 1
  ring

theorem f112_relIndex_right_l2 {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {f : ℕ} (hf : f ≠ 0)
    (hm : IsL2Quot f (oTwoQuot ↥L2)) :
    (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 2 ^ f + 1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hrel : (borelOf L2 S).relIndex L2 = 2 ^ f + 1 := by
    have h' := CFSG.Quasithin.F112R.St84.index_borelOf_of_psl2 (f := f) hf hF.1.h2.sylow hm
    simpa [Subgroup.relIndex] using h'
  have hinf : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
    have h := F1.inf_bigB_eq_borelOf hR.symm
    rwa [bigB_comm] at h
  rw [F112W.relIndex_sup_eq_relIndex_inf (N := L2) (B := bigB L1 L2 S)
    ((F1.bigB_le_normalizer_left hR).2), hinf]
  exact hrel

theorem f112_relIndex_left_u3 {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {k : ℕ} (hk : 2 ≤ k)
    {F : Type} [Field F] [Finite F] (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ (3 * k) + 1 := by
  rw [f112_relIndex_bigB_of_u3 hF hk hFc hU3, ← pow_mul]
  congr 1
  ring

theorem str83Moufang_of_leaves (hT : Str83LocTrans9)
    (hO : Str83Orders) : Str83Moufang := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨hm, hQ1, hQ2, hS⟩ := hO G L1 L2 S a hF ha hSz hBig hL2
  have hv1 := f112_relIndex_left_sz hF ha hSz
  have hv2 := f112_relIndex_right_l2 hF (by omega) hm
  have hQ1' : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) * 2 ^ (2 * (2 * a + 1)) =
      Nat.card S := by
    have h2 : 2 ^ (2 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 2 := by
      rw [show 2 * (2 * a + 1) = (2 * a + 1) * 2 by ring, pow_mul]
    rw [hQ1, hS, h2]
    exact (pow_add (2 ^ (2 * a + 1)) 10 2).symm
  have hQ2' : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) * 2 ^ (2 * a + 1) =
      Nat.card S := by
    rw [hQ2, hS]
    exact (pow_succ (2 ^ (2 * a + 1)) 11).symm
  have hS' : Nat.card S = 2 ^ ((2 * (2 * a + 1) + (2 * a + 1)) * 4) := by
    rw [hS, ← pow_mul]
    congr 1
    ring
  have hK1 : ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1 := by
    obtain ⟨e⟩ := hSz
    haveI : IsSimpleGroup ↥(Sz a) :=
      CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup ha
    exact f112_kernel_centralizes_of_isSimpleGroup hF e.isSimpleGroup
  have hK2 : ∀ t ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L2 := by
    obtain ⟨e⟩ := hm
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 (2 * a + 1))) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [GaloisField.card 2 (2 * a + 1) (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    exact f112_kernel_centralizes_of_isSimpleGroup_right hF e.isSimpleGroup
  exact f112_weissMoufangHat hF (j := 4) (e₁ := 2 * (2 * a + 1)) (e₂ := 2 * a + 1)
    (by norm_num) (hT G L1 L2 S a hF ha hSz hBig hL2) hv1 hv2 hQ1' hQ2' hS' hK1 hK2

theorem str86Moufang_of_leaves (hT : Str86LocTrans5)
    (hO : Str86Orders) : Str86Moufang := by
  intro G _ _ L1 L2 S hF hU3 hBig hL2
  obtain ⟨k, hk, F, hField, hFin, hFc, hU3'⟩ := hU3
  letI : Field F := hField
  haveI : Finite F := hFin
  have hU3 : VU3Big L1 := ⟨k, hk, F, hField, hFin, hFc, hU3'⟩
  obtain ⟨hm, hQ1, hQ2, hS⟩ := hO G L1 L2 S k F hF hk hFc hU3' hBig hL2
  have hv1 := f112_relIndex_left_u3 hF hk hFc hU3'
  have hv2 := f112_relIndex_right_l2 hF.toW (by omega) hm
  have hQ1' : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) * 2 ^ (3 * k) = Nat.card S := by
    rw [hQ1, hS, show 3 * k = k * 3 by ring, pow_mul]
    exact (pow_add (2 ^ k) 7 3).symm
  have hQ2' : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) * 2 ^ (2 * k) = Nat.card S := by
    rw [hQ2, hS, show 2 * k = k * 2 by ring, pow_mul]
    exact (pow_add (2 ^ k) 8 2).symm
  have hS' : Nat.card S = 2 ^ ((3 * k + 2 * k) * 2) := by
    rw [hS, ← pow_mul]
    congr 1
    ring
  have hK1 : ∀ t ∈ (f112K1 L1 L2 S).map (L1 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L1,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L1 :=
    f112_kernel_centralizes_of_u3 hF hU3
  have hK2 : ∀ t ∈ (f112K2 L1 L2 S).map (L2 ⊔ bigB L1 L2 S).subtype, ∀ l ∈ L2,
      l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L2 := by
    obtain ⟨e⟩ := hm
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 (2 * k))) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [GaloisField.card 2 (2 * k) (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega))
    exact f112_kernel_centralizes_of_isSimpleGroup_right hF.toW e.isSimpleGroup
  exact f112_weissMoufangHat hF.toW (j := 2) (e₁ := 3 * k) (e₂ := 2 * k)
    (by norm_num) (hT G L1 L2 S hF hU3 hBig hL2) hv1 hv2 hQ1' hQ2' hS' hK1 hK2

end CFSG.Quasithin.Stroth
