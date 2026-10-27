
module

public import CFSG.Monster.GMS.S365CosetSpecBase

public import Certificates.Certificate10042

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

theorem cosetFacts_ok :
    (cosetRowsT.all fun Mt => isFixedN Mt 2 && isFixedN Mt 4) = true ∧
    pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 cosetBase =
      true ∧
    countBelow (pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4)
      16777216 0 = 1995840 ∧
    ∃ R : Finset ℕ, R.card = 498960 ∧ ∀ r ∈ R, r < 2 ^ 24 ∧ ∃ w : List ℕ, (∀ l ∈ w, l < 3) ∧
      canon4 2 4 (applyPath cosetRowsT w cosetBase) = r :=
  Certificates.certificate10042

theorem co1FourT_ref :
    ∀ v v' : Fin 24 → ZMod 2,
    FourPattern (toVecD 24 2) (toVecD 24 4) v → FourPattern (toVecD 24 2) (toVecD 24 4) v' →
      ∃ g : Co1, g • toVecD 24 2 = toVecD 24 2 ∧ g • toVecD 24 4 = toVecD 24 4 ∧
        CosetEq (toVecD 24 2) (toVecD 24 4) (g • v) v' := by
  obtain ⟨hfix, h40, hcnt, R, hR, hRm⟩ := cosetFacts_ok
  obtain ⟨gl, hgl⟩ := exists_cosetElems
  have h3 : cosetRowsT.size = 3 := by decide
  have hstab : ∀ l < cosetRowsT.size, gl l • toVecD 24 2 = toVecD 24 2 ∧
      gl l • toVecD 24 4 = toVecD 24 4 := by
    intro l hl
    have hf := Array.all_eq_true.1 hfix l hl
    simp only [Bool.and_eq_true] at hf
    have e2 : vecMulN 24 cosetRowsT[l]! 2 = 2 := by
      rw [getElem!_pos cosetRowsT l hl]; exact beq_iff_eq.1 hf.1
    have e4 : vecMulN 24 cosetRowsT[l]! 4 = 4 := by
      rw [getElem!_pos cosetRowsT l hl]; exact beq_iff_eq.1 hf.2
    exact ⟨by rw [hgl l hl, e2], by rw [hgl l hl, e4]⟩
  have hfix2 := pathElem_fix (fun l hl => (hstab l hl).1)
  have hfix4 := pathElem_fix (fun l hl => (hstab l hl).2)
  have hw3 : ∀ w : List ℕ, (∀ l ∈ w, l < 3) → ∀ l ∈ w, l < cosetRowsT.size := by
    intro w hw l hl
    rw [h3]
    exact hw l hl
  have h40' : toVecD 24 cosetBase ∈ PatSet (toVecD 24 2) (toVecD 24 4) :=
    (pat4_iff (by decide)).1 h40
  have hcos : ∀ {u c : ℕ}, CosetEq (toVecD 24 2) (toVecD 24 4) (toVecD 24 c) (toVecD 24 u) →
      toVecD 24 u ∈ PatSet (toVecD 24 2) (toVecD 24 4) →
      toVecD 24 c ∈ PatSet (toVecD 24 2) (toVecD 24 4) := by
    intro u c he hu
    have := PatSet.add_klein he hu
    rwa [add_comm (toVecD 24 c), ← add_assoc, vec_add_self, zero_add] at this
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have hRC : R ⊆ canonPatSet (pat4 qRows (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 2 4) 16777216 := by
    intro r hr
    obtain ⟨hr24, w, hw, hwr⟩ := hRm r hr
    refine (mem_canonPatSet _ _ _).2 ⟨lt_of_lt_of_eq hr24 h24, (pat4_iff hr24).2 ?_,
      by rw [← hwr, canon4_idem]⟩
    have hu : toVecD 24 (applyPath cosetRowsT w cosetBase) ∈
        PatSet (toVecD 24 2) (toVecD 24 4) := by
      rw [← pathElem_smul hgl w (hw3 w hw)]
      exact PatSet.smul_mem (hfix2 w (hw3 w hw)) (hfix4 w (hw3 w hw)) h40'
    rw [← hwr]
    exact hcos (coset_canon4 2 4 _) hu
  have hCle := card_canonPatSet_le (pat4 qRows (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 2 4) 16777216 (fun c k hk hc hpc => by
    have hc' : c < 2 ^ 24 := lt_of_lt_of_eq hc h24.symm
    have hk24 : k < 2 ^ 24 := by rcases hk with h | h | h | h <;> rw [h] <;> norm_num
    have hlt : c ^^^ k < 2 ^ 24 := Nat.xor_lt_two_pow hc' hk24
    refine ⟨lt_of_lt_of_eq hlt h24, (pat4_iff hlt).2 ?_⟩
    rw [toVecD_xor]
    exact PatSet.add_klein (inK_of_mem hk) ((pat4_iff hc').1 hpc))
  have hP := countBelow_eq
    (pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4) 16777216 0
  rewrite [hcnt] at hP
  have hRC' := Finset.eq_of_subset_of_card_le hRC (by omega)
  have hreach : ∀ v : Fin 24 → ZMod 2, FourPattern (toVecD 24 2) (toVecD 24 4) v →
      ∃ g : Co1, g • toVecD 24 2 = toVecD 24 2 ∧ g • toVecD 24 4 = toVecD 24 4 ∧
        CosetEq (toVecD 24 2) (toVecD 24 4) (g • toVecD 24 cosetBase) v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ : v ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
      rw [toVecD_image_Iio]; trivial
    have hu' : u < 2 ^ 24 := hu
    have hcu : canon4 2 4 u < 2 ^ 24 := lt_of_le_of_lt (canon4_le u) hu'
    have hmem : canon4 2 4 u ∈ canonPatSet (pat4 qRows (orbitOf 2 98280).pts
        (posTable 24 (orbitOf 2 98280).pts) 98280 2 4) 16777216 :=
      (mem_canonPatSet _ _ _).2 ⟨lt_of_lt_of_eq hcu h24,
        (pat4_iff hcu).2 (hcos (coset_canon4 2 4 u) hv.2.2.2), canon4_idem u⟩
    rw [← hRC'] at hmem
    obtain ⟨-, w, hw, hwr⟩ := hRm _ hmem
    refine ⟨pathElem gl w, hfix2 w (hw3 w hw), hfix4 w (hw3 w hw), ?_⟩
    rw [pathElem_smul hgl w (hw3 w hw)]
    have e1 := (coset_canon4 2 4 (applyPath cosetRowsT w cosetBase)).symm
    rw [hwr] at e1
    exact e1.trans (coset_canon4 2 4 u)
  intro v v' hv hv'
  obtain ⟨g₁, h1x, h1y, hg₁⟩ := hreach v hv
  obtain ⟨g₂, h2x, h2y, hg₂⟩ := hreach v' hv'
  have hix : g₁⁻¹ • toVecD 24 2 = toVecD 24 2 := inv_smul_eq_iff.2 h1x.symm
  have hiy : g₁⁻¹ • toVecD 24 4 = toVecD 24 4 := inv_smul_eq_iff.2 h1y.symm
  refine ⟨g₂ * g₁⁻¹, by rw [mul_smul, hix, h2x], by rw [mul_smul, hiy, h2y], ?_⟩
  have e1 := hg₁.symm.smul hix hiy
  rw [inv_smul_smul] at e1
  have e2 := e1.smul h2x h2y
  rw [mul_smul]
  exact e2.trans hg₂

theorem co1FourT :
    Co1FourT := by
  intro a b ω a' b' ω' hP hP'
  obtain ⟨hx₀, hy₀, hxy₀⟩ := refPair
  obtain ⟨g₁, hg₁a, hg₁b⟩ := exists_co1Act_pair hP.1 hP.2.1 hP.2.2.1 hx₀ hy₀ hxy₀
  obtain ⟨g₂, hg₂a, hg₂b⟩ := exists_co1Act_pair hP'.1 hP'.2.1 hP'.2.2.1 hx₀ hy₀ hxy₀
  have hg₁a' : g₁ • a = toVecD 24 2 := hg₁a
  have hg₁b' : g₁ • b = toVecD 24 4 := hg₁b
  have hg₂a' : g₂ • a' = toVecD 24 2 := hg₂a
  have hg₂b' : g₂ • b' = toVecD 24 4 := hg₂b
  have hω₁ : FourPattern (toVecD 24 2) (toVecD 24 4) (g₁ • ω) := by
    have := hP.map g₁
    rwa [hg₁a', hg₁b'] at this
  have hω₂ : FourPattern (toVecD 24 2) (toVecD 24 4) (g₂ • ω') := by
    have := hP'.map g₂
    rwa [hg₂a', hg₂b'] at this
  obtain ⟨h, hh2, hh4, hhc⟩ := co1FourT_ref _ _ hω₁ hω₂
  refine ⟨g₂⁻¹ * h * g₁, ?_, ?_, ?_⟩
  · show (g₂⁻¹ * h * g₁) • a = a'
    rw [mul_smul, mul_smul, hg₁a', hh2, ← hg₂a', inv_smul_smul]
  · show (g₂⁻¹ * h * g₁) • b = b'
    rw [mul_smul, mul_smul, hg₁b', hh4, ← hg₂b', inv_smul_smul]
  · have e1 := hhc.map g₂⁻¹
    have ex : g₂⁻¹ • toVecD 24 2 = a' := by rw [← hg₂a', inv_smul_smul]
    have ey : g₂⁻¹ • toVecD 24 4 = b' := by rw [← hg₂b', inv_smul_smul]
    have eg : (g₂⁻¹ * h * g₁) • ω = g₂⁻¹ • (h • (g₁ • ω)) := by rw [mul_assoc, mul_smul, mul_smul]
    rw [ex, ey, inv_smul_smul, ← eg] at e1
    exact e1.cases

end S365

end CFSG.Monster.GMS
