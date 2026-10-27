module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section

private theorem e6_prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G] (s : Finset ι)
    (f : ι → ℤ) (x : G) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private theorem e6_rootChar_eq_pow_sum {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (ω : Kˣ) (e : Fin τ.rank → ℕ) (ha : ∀ i, a i = ω ^ e i) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = ω ^ (∑ i, (e i : ℤ) * γ i) := by
  simp only [rootChar]
  calc ∏ i, a i ^ γ i
      = ∏ i, (ω ^ (e i : ℤ)) ^ γ i := by
        apply Finset.prod_congr rfl
        intro i _
        rw [ha i, zpow_natCast]
    _ = ∏ i, ω ^ ((e i : ℤ) * γ i) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [zpow_mul]
    _ = ω ^ (∑ i, (e i : ℤ) * γ i) := by
        simpa using e6_prod_zpow_eq_zpow_sum Finset.univ (fun i => (e i : ℤ) * γ i) ω

private theorem e6_rootChar_single {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (i : Fin τ.rank) : rootChar a (Pi.single i 1) = a i := by
  simpa using rootChar_nsmul_single a i 1

private theorem e6_natPow_eq_zpow_mul {G : Type*} [CommGroup G] (x : G) (m n : ℕ) :
    (x ^ m) ^ n = x ^ ((m : ℤ) * (n : ℤ)) := by
  calc (x ^ m) ^ n = (x ^ (m : ℤ)) ^ (n : ℤ) := by rw [zpow_natCast, zpow_natCast]
    _ = x ^ ((m : ℤ) * (n : ℤ)) := by rw [zpow_mul]

private theorem e6_zmod_eq_of_zpow_eq {G : Type*} [CommGroup G] {x : G} (hx : IsPrimitiveRoot x 3)
    {A B : ℤ} (h : x ^ A = x ^ B) : (A : ZMod 3) = (B : ZMod 3) := by
  have hdvd : (3 : ℤ) ∣ A - B := by
    apply (hx.zpow_eq_one_iff_dvd (A - B)).1
    rw [zpow_sub, h, mul_inv_cancel]
  have h0 : ((A - B : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (A - B) 3).2 hdvd
  rw [Int.cast_sub, sub_eq_zero] at h0
  exact h0

private theorem e6_zmod_sum_val {n : ℕ} (v : Fin n → ZMod 3) (γ : Fin n → ℤ) :
    ((∑ k, ((v k).val : ℤ) * γ k : ℤ) : ZMod 3) =
      ∑ k, ((γ k : ℤ) : ZMod 3) * v k := by
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [ZMod.natCast_zmod_val]
  exact mul_comm _ _

private theorem e6_zmod_mul_val {n : ℕ} (v : Fin n → ZMod 3) (q : ℕ) (i : Fin n) :
    ((((v i).val : ℤ) * (q : ℤ) : ℤ) : ZMod 3) = ((q : ℕ) : ZMod 3) * v i := by
  push_cast
  rw [ZMod.natCast_zmod_val, mul_comm]

end

theorem frobRootMap_e6_admissible
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E6 L 3) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (ω : L) (hω : IsPrimitiveRoot ω 3)
    (v : Fin Tag.E6.rank → ZMod 3) (hv : ∀ i, ((a i : Lˣ) : L) = ω ^ (v i).val) :
    E6Admissible (fun i => S.ρ (Pi.single i 1)) v ((S.D.q : ℕ) : ZMod 3) ∧
      kernelRoots (rootCharHom a) =
        {γ | IsRoot Tag.E6 γ ∧ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0} := by
  classical
  set ω₀ : Lˣ := Units.mk0 ω (hω.ne_zero (by norm_num)) with hω₀def
  have hω₀ : IsPrimitiveRoot ω₀ 3 := by
    rw [hω₀def]
    exact IsPrimitiveRoot.coe_units_iff.1 (by simpa only [Units.val_mk0] using hω)
  have hae : ∀ i, a i = ω₀ ^ (v i).val := by
    intro i
    rw [hω₀def]
    exact Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hv i)
  have hrootChar : ∀ γ : Fin Tag.E6.rank → ℤ,
      rootChar a γ = ω₀ ^ (∑ k, ((v k).val : ℤ) * γ k) :=
    fun γ => e6_rootChar_eq_pow_sum a ω₀ (fun k => (v k).val) hae γ
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (S.frob.isRoot_iff (Pi.single i 1)).2 (IsRoot.basis i)
    · intro i j
      exact S.frob.iform_eq (Pi.single i 1) (Pi.single j 1)
    · intro i
      have hroot := S.frob.rootChar_eq a hT (Pi.single i 1) (IsRoot.basis i)
      have hB : rootChar a (Pi.single i 1) ^ S.D.q =
          ω₀ ^ (((v i).val : ℤ) * (S.D.q : ℤ)) := by
        rw [e6_rootChar_single a i, hae i, e6_natPow_eq_zpow_mul]
      have hAB : ω₀ ^ (∑ k, ((v k).val : ℤ) * (S.ρ (Pi.single i 1)) k) =
          ω₀ ^ (((v i).val : ℤ) * (S.D.q : ℤ)) := by
        rw [← hrootChar (S.ρ (Pi.single i 1)), hroot, hB]
      have hz := e6_zmod_eq_of_zpow_eq hω₀ hAB
      rw [e6_zmod_sum_val v (S.ρ (Pi.single i 1)), e6_zmod_mul_val v S.D.q i] at hz
      exact hz
  · ext γ
    rw [kernelRoots_rootCharHom]
    simp only [Set.mem_setOf_eq]
    refine and_congr_right fun _ => ?_
    rw [hrootChar γ, hω₀.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      ← e6_zmod_sum_val v γ]

end CFSG.StandardType.TablePThreeKG

end
