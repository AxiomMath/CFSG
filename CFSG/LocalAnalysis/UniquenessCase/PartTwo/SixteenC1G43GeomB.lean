module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Defs
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_primGeom {M V : Subgroup G} {g : G} (hV : IsElemAbelian 2 V)
    (hM : normalizer (V : Set G) = M) (hV64 : Nat.card V = 64)
    (hnot : ¬ V ≤ conjSubgroup M g)
    (hmB : E3.mQuot (conjSubgroup V g) (BOf M V g) = 1)
    (hker : (BOf M V g ⊓ centralizer (V : Set G)).relIndex (BOf M V g) = 16)
    {z : G} {P : Subgroup G} (hE : E16Lift V (BOf M V g) z P)
    (hfix : ∀ b ∈ BOf M V g, b ∉ centralizer (V : Set G) → ∀ v ∈ V,
      b * v * b⁻¹ = v → v ∈ conjSubgroup M g) :
    PrimGeom M V g := by
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup' hV g
  have hcardVg : Nat.card (conjSubgroup V g) = 64 := by
    rw [card_conjSubgroup' g V, hV64]
  have hNOf : NOf M V g = V ⊓ conjSubgroup V g := NOf_eq M V g hVM
  have hU_le_V : UOf M V g ≤ V := by
    intro x hx
    exact (Subgroup.mem_inf.mp (by simpa [UOf] using hx)).1
  have hU_le_conjM : UOf M V g ≤ conjSubgroup M g := by
    intro x hx
    exact (Subgroup.mem_inf.mp (by simpa [UOf] using hx)).2
  have hB_le_conjVg : BOf M V g ≤ conjSubgroup V g := by
    intro x hx
    exact (Subgroup.mem_inf.mp (by simpa [BOf] using hx)).1
  have hSU : {v : G | v ∈ V ∧ ∃ b ∈ BOf M V g,
      b ∉ centralizer (V : Set G) ∧ b * v * b⁻¹ = v} ⊆ (UOf M V g : Set G) := by
    rintro v ⟨hvV, b, hbB, hbcent, hbv⟩
    exact ⟨hvV, hfix b hbB hbcent v hvV hbv⟩
  have hP_le_U : P ≤ UOf M V g :=
    hE.le_closure.trans ((Subgroup.closure_le (UOf M V g)).mpr hSU)
  have hprod : P.relIndex (UOf M V g) * (UOf M V g).relIndex V = 2 := by
    rw [Subgroup.relIndex_mul_relIndex P (UOf M V g) V hP_le_U hU_le_V]
    exact hE.relIndex_eq
  have hUrel_ne_one : (UOf M V g).relIndex V ≠ 1 := by
    intro h1
    exact hnot ((Subgroup.relIndex_eq_one.mp h1).trans hU_le_conjM)
  have hPrel_one : P.relIndex (UOf M V g) = 1 := by
    have hdvd : P.relIndex (UOf M V g) ∣ 2 := ⟨(UOf M V g).relIndex V, hprod.symm⟩
    rcases Nat.prime_two.eq_one_or_self_of_dvd (P.relIndex (UOf M V g)) hdvd with h | h
    · exact h
    · exfalso
      have h2 : (UOf M V g).relIndex V = 1 := by
        rw [h] at hprod
        omega
      exact hUrel_ne_one h2
  have hU_eq_P : UOf M V g = P :=
    le_antisymm (Subgroup.relIndex_eq_one.mp hPrel_one) hP_le_U
  have hrelU : (UOf M V g).relIndex V = 2 := by
    rw [hU_eq_P]; exact hE.relIndex_eq
  have hcardU : Nat.card ↥(UOf M V g) = 32 := by
    have h := Subgroup.relIndex_mul_card (H := UOf M V g) (K := V)
    rw [inf_eq_left.mpr hU_le_V] at h
    rw [hrelU, hV64] at h
    omega
  obtain ⟨b, hbB, v, hvP, hmove⟩ := hE.exists_move
  have hbVg : b ∈ conjSubgroup V g := hB_le_conjVg hbB
  have hvU : v ∈ UOf M V g := hP_le_U hvP
  have hvV : v ∈ V := hU_le_V hvU
  have hvMg : v ∈ conjSubgroup M g := hU_le_conjM hvU
  have hbveq : b * v * b⁻¹ = v * z := by
    rcases hE.act_of_mem b hbB v hvP with h | h
    · exact absurd h hmove
    · exact h
  have hMnorm : conjSubgroup M g = Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [← hM]; exact conjSubgroup_normalizer V g
  have hv_norm_inv : v⁻¹ ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
    (Subgroup.normalizer (conjSubgroup V g : Set G)).inv_mem (hMnorm ▸ hvMg)
  have hvbv : v⁻¹ * b * v ∈ conjSubgroup V g := by
    have h := (Subgroup.mem_normalizer_iff.mp hv_norm_inv b).1 hbVg
    simpa using h
  have hzconj : z ∈ conjSubgroup V g := by
    have hzb : v⁻¹ * b * v * b⁻¹ ∈ conjSubgroup V g :=
      mul_mem hvbv ((conjSubgroup V g).inv_mem hbVg)
    have hz_eq : z = v⁻¹ * b * v * b⁻¹ := by
      have h1 : v⁻¹ * b * v * b⁻¹ = v⁻¹ * (b * v * b⁻¹) := by simp only [mul_assoc]
      rw [h1, hbveq]
      exact (inv_mul_cancel_left v z).symm
    rw [hz_eq]; exact hzb
  have hN'_cases : ∀ n ∈ V ⊓ conjSubgroup V g, n = 1 ∨ n = z := by
    intro n hn
    obtain ⟨hnV, hnVg⟩ := Subgroup.mem_inf.mp hn
    refine (hE.fixed_iff n hnV).mp ?_
    intro b hbB
    have hcomm := hVg.comm (hB_le_conjVg hbB) hnVg
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hzN' : z ∈ V ⊓ conjSubgroup V g := ⟨hE.mem_z, hzconj⟩
  have hN'_eq : V ⊓ conjSubgroup V g = Subgroup.zpowers z := by
    apply le_antisymm
    · intro n hn
      rcases hN'_cases n hn with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    · exact Subgroup.zpowers_le.mpr hzN'
  have horder : orderOf z = 2 := by
    have hz2 : z ^ 2 = 1 := hV.2 z hE.mem_z
    exact orderOf_eq_prime hz2 hE.ne_one
  have hcardN' : Nat.card ↥(V ⊓ conjSubgroup V g) = 2 := by
    rw [hN'_eq, Nat.card_zpowers, horder]
  have hcardB : Nat.card ↥(BOf M V g) = 32 := by
    have h := E3.card_eq_two_pow_mul (V := conjSubgroup V g) (U := BOf M V g)
      hVg.isPGroup hB_le_conjVg
    rw [hcardVg, hmB] at h
    norm_num at h
    omega
  have hcardC : Nat.card ↥(BOf M V g ⊓ centralizer (V : Set G)) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := BOf M V g ⊓ centralizer (V : Set G))
      (K := BOf M V g)
    rw [inf_eq_left.mpr (inf_le_left : BOf M V g ⊓ centralizer (V : Set G) ≤
      BOf M V g)] at h
    rw [hker, hcardB] at h
    omega
  have hN'_le_C : V ⊓ conjSubgroup V g ≤ BOf M V g ⊓ centralizer (V : Set G) := by
    intro n hn
    obtain ⟨hnV, hnVg⟩ := Subgroup.mem_inf.mp hn
    refine ⟨Subgroup.mem_inf.mpr ⟨hnVg, hVM hnV⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun w hw => hV.comm hw hnV)
  have hC_eq : BOf M V g ⊓ centralizer (V : Set G) = V ⊓ conjSubgroup V g := by
    have hcardle : Nat.card ↥(BOf M V g ⊓ centralizer (V : Set G)) ≤
        Nat.card ↥(V ⊓ conjSubgroup V g) := by omega
    exact (Subgroup.eq_of_le_of_card_ge hN'_le_C hcardle).symm
  have hcardN : Nat.card ↥(NOf M V g) = 2 := by
    rw [hNOf]; exact hcardN'
  have hhalf1 : V ⊓ centralizer ((BOf M V g : Subgroup G) : Set G) ≤ conjSubgroup V g := by
    intro v hv
    obtain ⟨hvV, hvcent⟩ := Subgroup.mem_inf.mp hv
    have hfix' : ∀ b ∈ BOf M V g, b * v * b⁻¹ = v := by
      intro b hbB
      have hb' : b * v = v * b := (Subgroup.mem_centralizer_iff.mp hvcent) b hbB
      rw [hb', mul_assoc, mul_inv_cancel, mul_one]
    rcases (hE.fixed_iff v hvV).mp hfix' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hzconj
  have hhalf2 : ∀ b ∈ BOf M V g, b ∉ V → ∀ v ∈ V,
      ⁅v, b⁆ ∈ V ⊓ conjSubgroup V g → v ∈ conjSubgroup M g := by
    intro b hbB hbV' v hvV hcomm
    have hbcent : b ∉ centralizer (V : Set G) := by
      intro hbc
      apply hbV'
      have hbc' : b ∈ BOf M V g ⊓ centralizer (V : Set G) := ⟨hbB, hbc⟩
      rw [hC_eq] at hbc'
      exact hbc'.1
    rcases hN'_cases ⁅v, b⁆ hcomm with hc | hc
    · have hvb : v * b = b * v := commutatorElement_eq_one_iff_mul_comm.mp hc
      have hconj : b * v * b⁻¹ = v := by
        rw [← hvb, mul_assoc, mul_inv_cancel, mul_one]
      exact hU_le_conjM (hP_le_U (hE.mem_of_act b hbB hbcent v hvV (Or.inl hconj)))
    · have hzinv : z⁻¹ = z := by
        have hz2 : z * z = 1 := by simpa [pow_two] using hV.2 z hE.mem_z
        exact inv_eq_of_mul_eq_one_right hz2
      have hzv : z * v = v * z := hV.comm hE.mem_z hvV
      have hconj : b * v * b⁻¹ = v * z := by
        have hstep : b * v * b⁻¹ = ⁅b, v⁆ * v := by
          simpa [MulAut.conj_apply] using conj_eq_commutatorElement_mul (g₁ := b) (g₂ := v)
        rw [hstep, ← commutatorElement_inv, hc, hzinv, hzv]
      exact hU_le_conjM (hP_le_U (hE.mem_of_act b hbB hbcent v hvV (Or.inr hconj)))
  exact ⟨⟨hhalf1, hhalf2⟩, hrelU, hcardU, hcardB, hcardN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
