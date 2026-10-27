module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9

import CFSG.Quasithin.Recognition.St84.Gen.D4qModelData
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalVertexOne
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalVertexTwoIso
import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Uniq
import CFSG.Quasithin.Recognition.CertF6Bridge

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LocalAnalysis.EvenBN.TrialityD4 CFSG.Quasithin.H13.F431.D4q
open CFSG.Quasithin.H13.F431.D4q.Struct
open CFSG.Quasithin.F6 CFSG.Quasithin.F6.GoldAmL4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley


theorem isAmalgamOfGroup_d4_of_d4qLocalData {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {f : ℕ} (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hD : D4qLocalData L1 L2 S f) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f) := by
  classical
  let K := GaloisField 2 (3 * f)
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 f
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hf1 : 1 ≤ f := by omega
  have hK : Nat.card K = (2 ^ f) ^ 3 := by
    rw [GaloisField.card (p := 2) (n := 3 * f) (by omega), Nat.mul_comm 3 f, pow_mul]
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := fun c => iterateFrobeniusEquiv_def K 2 f c
  let d : TrialityD4Data (Struct.Cm σ) (2 ^ f) := d4ModelData σ hf1 hK hσ
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  have hdS : d.S = Struct.Ust σ := d4ModelData_S σ hf1 hK hσ
  have hNV : Subgroup.normalizer (d.V : Set (Struct.Cm σ)) = Struct.Pst0 σ :=
    normalizer_d4ModelData_V σ hf1 hK hσ
  have hNY : Subgroup.normalizer (d.Y : Set (Struct.Cm σ)) = Struct.Pst1 σ :=
    normalizer_d4ModelData_Y σ hf1 hK hσ
  obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hD.exists_hall_bigB hH h1
  obtain ⟨ψ₁, hψ₁S, hψ₁N, hψ₁H⟩ :=
    hD.exists_mulEquiv_vertexOne hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm d
  obtain ⟨ψ₂, hψ₂agree⟩ :=
    hD.exists_mulEquiv_vertexTwo hf hH h1 hHB hSH hSinfH hHcard hHcomm d ψ₁ hψ₁S hψ₁H
  let φ₁ : ↥P1 ≃* ↥(Struct.Pst0 σ) := ψ₁.trans (MulEquiv.subgroupCongr hNV)
  let φ₂ : ↥P2 ≃* ↥(Struct.Pst1 σ) := ψ₂.trans (MulEquiv.subgroupCongr hNY)
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 3 * f) (n := f) (by omega) (by omega) hH h1 h2
  have hInf : P1 ⊓ P2 = bigB L1 L2 S := by
    simpa [P1, P2] using parabolic_inf_parabolic hR
  have hbigB1 : bigB L1 L2 S = P1 ⊓ Subgroup.normalizer (S : Set G) := by
    simpa [P1] using hD.bigB_eq_inf_normalizer_left hH h1 h2
  have hN : Subgroup.normalizer (d.S : Set (Struct.Cm σ)) = Struct.Pst0 σ ⊓ Struct.Pst1 σ := by
    rw [hdS]
    exact normalizer_Ust_eq_inf σ
  have hφ₁coe : ∀ (x : G) (hx : x ∈ P1),
      ((φ₁ ⟨x, hx⟩ : ↥(Struct.Pst0 σ)) : Struct.Cm σ) = (ψ₁ ⟨x, hx⟩ : Struct.Cm σ) := by
    intro x hx
    simp only [φ₁, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  have hφ₂coe : ∀ (x : G) (hx : x ∈ P2),
      ((φ₂ ⟨x, hx⟩ : ↥(Struct.Pst1 σ)) : Struct.Cm σ) = (ψ₂ ⟨x, hx⟩ : Struct.Cm σ) := by
    intro x hx
    simp only [φ₂, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  have hag : ∀ (x : G) (hx₁ : x ∈ P1) (hx₂ : x ∈ P2),
      ((φ₁ ⟨x, hx₁⟩ : ↥(Struct.Pst0 σ)) : Struct.Cm σ) =
        ((φ₂ ⟨x, hx₂⟩ : ↥(Struct.Pst1 σ)) : Struct.Cm σ) := by
    intro x hx₁ hx₂
    have hxB : x ∈ bigB L1 L2 S := by
      have hx : x ∈ P1 ⊓ P2 := ⟨hx₁, hx₂⟩
      rwa [hInf] at hx
    have h1' : (⟨x, Subgroup.mem_sup_right hxB⟩ : ↥P1) = ⟨x, hx₁⟩ := Subtype.ext rfl
    have h2' : (⟨x, Subgroup.mem_sup_right hxB⟩ : ↥P2) = ⟨x, hx₂⟩ := Subtype.ext rfl
    calc ((φ₁ ⟨x, hx₁⟩ : ↥(Struct.Pst0 σ)) : Struct.Cm σ)
        = (ψ₁ ⟨x, hx₁⟩ : Struct.Cm σ) := hφ₁coe x hx₁
      _ = (ψ₁ ⟨x, Subgroup.mem_sup_right hxB⟩ : Struct.Cm σ) := by rw [h1']
      _ = (ψ₂ ⟨x, Subgroup.mem_sup_right hxB⟩ : Struct.Cm σ) := (hψ₂agree x hxB).symm
      _ = (ψ₂ ⟨x, hx₂⟩ : Struct.Cm σ) := by rw [h2']
      _ = ((φ₂ ⟨x, hx₂⟩ : ↥(Struct.Pst1 σ)) : Struct.Cm σ) := (hφ₂coe x hx₂).symm
  have hsurj : ∀ y : Struct.Cm σ, y ∈ Struct.Pst0 σ → y ∈ Struct.Pst1 σ →
      ∃ (x : G) (hx₁ : x ∈ P1), x ∈ P2 ∧
        ((φ₁ ⟨x, hx₁⟩ : ↥(Struct.Pst0 σ)) : Struct.Cm σ) = y := by
    intro y hy0 hy1
    have hyN : y ∈ Subgroup.normalizer (d.S : Set (Struct.Cm σ)) := by
      rw [hN]
      exact ⟨hy0, hy1⟩
    let x : ↥P1 := φ₁.symm ⟨y, hy0⟩
    have hxval : ((φ₁ x : ↥(Struct.Pst0 σ)) : Struct.Cm σ) = y := by
      simp [x]
    have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
      refine (hψ₁N x).mpr ?_
      have hxφ : (ψ₁ x : Struct.Cm σ) = ((φ₁ x : ↥(Struct.Pst0 σ)) : Struct.Cm σ) :=
        hφ₁coe (x : G) x.2
      rw [hxφ, hxval]
      exact hyN
    have hxB : (x : G) ∈ bigB L1 L2 S := by
      rw [hbigB1]
      exact ⟨x.2, hxN⟩
    exact ⟨(x : G), x.2, Subgroup.mem_sup_right hxB, hxval⟩
  have hiso : IsAmalgamIso P1 P2 (Struct.Pst0 σ) (Struct.Pst1 σ) :=
    isAmalgamIso_of_agree φ₁ φ₂ hag hsurj
  refine ⟨Struct.Cm σ, inferInstance, isLieOverTwo_d4 σ hf1 hK hσ, Struct.Ust σ, ?_⟩
  refine ⟨Struct.Pst0 σ, Struct.Pst1 σ, isYAmalgamPair_d4 σ hf1 hK hσ, ?_⟩
  simpa [f112Amalgam, P1, P2] using nonempty_iso_ofSubgroups_of_isAmalgamIso hiso

end CFSG.Quasithin.F112R.St84

end
