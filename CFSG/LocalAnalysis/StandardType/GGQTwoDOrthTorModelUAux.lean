module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelV
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorSU
import CFSG.ClassicalInvolution.Phan.PhanDn.KLinearIsometry

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open TauCeti.QuadraticMap CFSG.Assembly.LowTwoRank
open Matrix

section ModelU

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

theorem qtwoStdWin_injective (m a len : ℕ) (h : a + len ≤ m + 1) :
    Function.Injective (qtwoStdWin (F := F) (K := K) m a len h) := by
  intro x y hxy
  simp only [qtwoStdWin, MonoidHom.comp_apply] at hxy
  exact blockEmb_injective h (suEndN_injective _ _ hxy)

theorem qtwoStdWin_range_mono (m a : ℕ) {len₁ len₂ : ℕ} (hl : len₁ ≤ len₂)
    (h₂ : a + len₂ ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a len₁ (by omega)).range ≤
      (qtwoStdWin (F := F) (K := K) m a len₂ h₂).range := by
  rintro _ ⟨x, rfl⟩
  refine ⟨blockEmb K 2 1 len₂ len₁ 0 (by omega) x, ?_⟩
  simp only [qtwoStdWin, MonoidHom.comp_apply, blockEmb_comp_apply, Nat.add_zero]

theorem qtwoStdWin_range_equiv_statedSU (hK : Nat.card K = 4) (m a len : ℕ)
    (h : a + len ≤ m + 1) :
    Nonempty (↥(qtwoStdWin (F := F) (K := K) m a len h).range ≃*
      ↥(StatedSU len (2 ^ 1) K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  refine ⟨(MulEquiv.ofBijective
    (qtwoStdWin (F := F) (K := K) m a len h).rangeRestrict
    ⟨(MonoidHom.rangeRestrict_injective_iff (f :=
        qtwoStdWin (F := F) (K := K) m a len h)).mpr
      (qtwoStdWin_injective m a len h),
     (qtwoStdWin (F := F) (K := K) m a len h).rangeRestrict_surjective⟩).symm.trans ?_⟩
  exact MulEquiv.subgroupCongr (SUid_eq_statedSU (F := K) (p := 2) (f := 1) hK' len)

theorem plh_pmoc_eq_zero_or_one (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (α := F) (by rw [hF]; norm_num)
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F ≤ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have h : (Finset.univ : Finset F) = {0, 1} := Finset.univ_of_card_le_two hcard
  have ha : a ∈ (Finset.univ : Finset F) := Finset.mem_univ a
  rw [h] at ha
  simpa using ha

theorem plh_torStdM_apply (ζ : normOne (unitaryInvolution K 2 1)) (m a : ℕ)
    (x : Fin (m + 1) → K) (i : Fin (m + 1)) :
    torStdM (F := F) ζ m a x i =
      (if i.val < a then (1 : K) else ((ζ : Kˣ) : K)) * x i := by
  simp only [torStdM, diagHom_apply]
  by_cases hi : i.val < a <;> simp [hi]

theorem plh_torStdM_eq_smul_of_mem_V₁ (ζ : normOne (unitaryInvolution K 2 1)) (m a : ℕ)
    {x : Fin (m + 1) → K} (hx : x ∈ torStdV₁ (F := F) m a) :
    torStdM (F := F) ζ m a x = ((ζ : Kˣ) : K) • x := by
  funext i
  rw [plh_torStdM_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.val < a
  · simp [hi, hx i hi]
  · simp [hi]

theorem plh_torE₁_isKLinear (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1)
    (m a : ℕ) (ha : a ≤ m + 1)
    {g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    (hg : g ∈ torE₁ (Qn E (m + 1)) (torStdM ζ m a)) :
    ∀ (c : K) (x : Fin (m + 1) → K), g (c • x) = c • g x := by
  classical
  set ζ' : K := (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) with hζ'def
  have hV₀ : torV₀ (torStdM (F := F) ζ m a) = torStdV₀ (F := F) m a := torV₀_torStdM hζ m a
  have hV₁ : torV₁ (torStdM (F := F) ζ m a) = torStdV₁ (F := F) m a := torV₁_torStdM hζ m a
  have hfix : ∀ v ∈ torStdV₀ (F := F) m a, g v = v := fun v hv => hg.1.2 v (by rw [hV₀]; exact hv)
  have hcomm : torStdM (F := F) ζ m a * g = g * torStdM (F := F) ζ m a :=
    (Subgroup.mem_centralizer_iff.mp hg.2) _ (Set.mem_singleton _)
  have htg : ∀ z : Fin (m + 1) → K, (↑(torStdM (F := F) ζ m a) :
      (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) (g z) =
      g ((torStdM (F := F) ζ m a) z) := by
    intro z
    have h := congrArg
      (fun e : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) => e z) hcomm
    simpa [LinearEquiv.mul_apply] using h
  have hpres : ∀ v ∈ torStdV₁ (F := F) m a, g v ∈ torStdV₁ (F := F) m a := by
    intro v hv
    rw [← hV₁] at hv ⊢
    rw [torV₁, LinearMap.mem_range] at hv ⊢
    obtain ⟨z, hz⟩ := hv
    refine ⟨g z, ?_⟩
    have hz' : torStdM (F := F) ζ m a z - z = v := by
      simpa [LinearMap.sub_apply, LinearMap.id_apply] using hz
    rw [LinearMap.sub_apply, LinearMap.id_apply, htg z, ← map_sub, hz']
  have hz : ∀ x : Fin (m + 1) → K, g (ζ' • x) = ζ' • g x := by
    intro x
    rw [hζ'def]
    set x₀ : Fin (m + 1) → K := fun i => if i.val < a then x i else 0 with hx₀
    set x₁ : Fin (m + 1) → K := fun i => if i.val < a then 0 else x i with hx₁
    have hxsum : x₀ + x₁ = x := by
      funext i; rw [Pi.add_apply, hx₀, hx₁]; by_cases hi : i.val < a <;> simp [hi]
    have hx₀mem : x₀ ∈ torStdV₀ (F := F) m a := by
      intro i hi; rw [hx₀]; simp [not_lt.mpr hi]
    have hx₁mem : x₁ ∈ torStdV₁ (F := F) m a := by
      intro i hi; rw [hx₁]; simp [hi]
    have hx₀smem : ((ζ : Kˣ) : K) • x₀ ∈ torStdV₀ (F := F) m a := by
      intro i hi
      rw [Pi.smul_apply, smul_eq_mul, hx₀mem i hi, mul_zero]
    have hx₁smem : ((ζ : Kˣ) : K) • x₁ ∈ torStdV₁ (F := F) m a := by
      intro i hi
      rw [Pi.smul_apply, smul_eq_mul, hx₁mem i hi, mul_zero]
    have h₁ : g (((ζ : Kˣ) : K) • x₀) = ((ζ : Kˣ) : K) • g x₀ := by
      rw [hfix _ hx₀smem, hfix _ hx₀mem]
    have h₂ : g (((ζ : Kˣ) : K) • x₁) = ((ζ : Kˣ) : K) • g x₁ := by
      rw [← plh_torStdM_eq_smul_of_mem_V₁ ζ m a hx₁mem,
        ← plh_torStdM_eq_smul_of_mem_V₁ ζ m a (hpres x₁ hx₁mem)]
      exact (htg x₁).symm
    have hsmul : ((ζ : Kˣ) : K) • x = ((ζ : Kˣ) : K) • x₀ + ((ζ : Kˣ) : K) • x₁ := by
      rw [← hxsum, smul_add]
    rw [hsmul, map_add, h₁, h₂, ← smul_add, ← map_add, hxsum]
  have hζ'_ne_zero : ζ' ≠ 0 := by
    rw [hζ'def]; exact Units.ne_zero (ζ : Kˣ)
  have hζ'_ne_one : ζ' ≠ 1 := by
    intro hone
    rw [hζ'def] at hone
    exact hζ (Subtype.ext (Units.ext hone))
  have hζ'_not_range : ∀ c : F, algebraMap F K c ≠ ζ' := by
    intro c hc
    rcases plh_pmoc_eq_zero_or_one hF c with rfl | rfl
    · rw [map_zero] at hc; exact hζ'_ne_zero hc.symm
    · rw [map_one] at hc; exact hζ'_ne_one hc.symm
  let b : Module.Basis (Fin 2) F K := E.basisOneR hζ'_not_range
  have hb0 : b 0 = 1 := by simp only [b, QuadExt.basisOneR_apply]; simp
  have hb1 : b 1 = ζ' := by simp only [b, QuadExt.basisOneR_apply]; simp
  let S : Submodule F K :=
    { carrier := {c : K | ∀ x, g (c • x) = c • g x}
      zero_mem' := by intro x; simp
      add_mem' := by
        intro c d hc hd x
        rw [add_smul, map_add, hc x, hd x, add_smul]
      smul_mem' := by
        intro e c hc x
        rw [smul_assoc, map_smul, hc x, smul_assoc] }
  have hspan : Submodule.span F ({1, ζ'} : Set K) ≤ S := by
    rw [Submodule.span_le]
    intro c hc
    rcases hc with rfl | rfl
    · intro x; simp
    · intro x; exact hz x
  have hrange : (Set.range b : Set K) = {1, ζ'} := by
    ext c
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [hb0, hb1]
    · intro hc
      rcases hc with rfl | rfl
      · exact ⟨0, hb0⟩
      · exact ⟨1, hb1⟩
  have htop : Submodule.span F ({1, ζ'} : Set K) = ⊤ := by rw [← hrange, b.span_eq]
  intro c x
  exact hspan (by rw [htop]; exact Submodule.mem_top) x

theorem plh_diagHom_conj_suEndN (n : ℕ) (t : Fin n → normOne (unitaryInvolution K 2 1))
    (s : SUid (unitaryInvolution K 2 1) n) :
    ∃ s' : SUid (unitaryInvolution K 2 1) n,
      diagHom F (unitaryInvolution K 2 1) n t * suEndN (F := F) (unitaryInvolution K 2 1) n s *
        (diagHom F (unitaryInvolution K 2 1) n t)⁻¹ =
      suEndN (F := F) (unitaryInvolution K 2 1) n s' := by
  classical
  set D : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => ((t i : Kˣ) : K) with hD
  set Dinv : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal fun i => (((t i : Kˣ) : K))⁻¹ with hDinv
  have hDuni : conjTr (unitaryInvolution K 2 1) D * D = 1 := by
    rw [hD, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    exact (mem_normOne (unitaryInvolution K 2 1)).mp (t i).2
  have hDinvuni : conjTr (unitaryInvolution K 2 1) Dinv * Dinv = 1 := by
    rw [hDinv, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    have h0 : (unitaryInvolution K 2 1) ((t i : Kˣ) : K) * ((t i : Kˣ) : K) = 1 :=
      (mem_normOne (unitaryInvolution K 2 1)).mp (t i).2
    rw [map_inv₀, ← mul_inv, h0, inv_one]
  have hDinvD : Dinv * D = 1 := by
    rw [hDinv, hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (Units.ne_zero (t i : Kˣ))
  have hDDinv : D * Dinv = 1 := by
    rw [hD, hDinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (Units.ne_zero (t i : Kˣ))
  set M : Matrix (Fin n) (Fin n) K :=
    (((s : SUid (unitaryInvolution K 2 1) n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hM
  set S : Matrix (Fin n) (Fin n) K := D * M * Dinv with hS
  have hMuni : conjTr (unitaryInvolution K 2 1) M * M = 1 := (mem_SUid.mp s.2).2
  have hMdet : M.det = 1 := (mem_SUid.mp s.2).1
  have hSdet : S.det = 1 := by
    rw [hS, Matrix.det_mul, Matrix.det_mul, hMdet, mul_one]
    have h := congrArg Matrix.det hDDinv
    rwa [Matrix.det_mul, Matrix.det_one] at h
  have hSuni : conjTr (unitaryInvolution K 2 1) S * S = 1 := by
    have key : conjTr (unitaryInvolution K 2 1) S * S =
        conjTr (unitaryInvolution K 2 1) Dinv *
          (conjTr (unitaryInvolution K 2 1) M *
            (conjTr (unitaryInvolution K 2 1) D * D) * M) * Dinv := by
      rw [hS, conjTr_mul, conjTr_mul]; simp only [Matrix.mul_assoc]
    rw [key, hDuni, Matrix.mul_one, hMuni, Matrix.mul_one, hDinvuni]
  have hSiso : ∀ x y : Fin n → K,
      herm (unitaryInvolution K 2 1) (S *ᵥ x) (S *ᵥ y) =
        herm (unitaryInvolution K 2 1) x y := by
    intro x y; rw [herm_mulVec, hSuni, Matrix.one_mulVec]
  have hdiag : ∀ v : Fin n → K,
      diagHom F (unitaryInvolution K 2 1) n t v = D *ᵥ v := by
    intro v; funext i; rw [diagHom_apply, hD, Matrix.mulVec_diagonal]
  have hdiaginv : ∀ v : Fin n → K,
      (diagHom F (unitaryInvolution K 2 1) n t)⁻¹ v = Dinv *ᵥ v := by
    intro v
    rw [← map_inv]
    funext i
    rw [diagHom_apply, hDinv, Matrix.mulVec_diagonal]
    simp [Pi.inv_apply]
  refine ⟨mkSU (unitaryInvolution K 2 1) S hSdet hSiso, ?_⟩
  apply LinearEquiv.ext
  intro v
  show diagHom F (unitaryInvolution K 2 1) n t
      (suEndN (F := F) (unitaryInvolution K 2 1) n s
        ((diagHom F (unitaryInvolution K 2 1) n t)⁻¹ v)) = S *ᵥ v
  rw [hdiaginv, hdiag, suEndN_apply, smul_def, ← hM, hS]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem plh_torE₁_le_sup (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ)
    (ha : a ≤ m + 1) :
    torE₁ (Qn E (m + 1)) (torStdM ζ m a) ≤
      (diagHom F (unitaryInvolution K 2 1) (m + 1)).range ⊔
        (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).range := by
  intro g hg
  have hgO : g ∈ orthogonalGroup (Qn E (m + 1)) := hg.1.1
  have hKlin := plh_torE₁_isKLinear E hF hζ m a ha hg
  obtain ⟨t, s, hts⟩ := exists_diagHom_mul_suEndN_eq E (by omega : 1 ≤ m + 1) hgO hKlin
  rw [← hts]
  exact Subgroup.mul_mem_sup ⟨t, rfl⟩ ⟨s, rfl⟩

theorem plh_qtwoStdWin_apply_window (m k d : ℕ) (h : k + d ≤ m + 1)
    (s : Su K 2 1 d) (v : Fin (m + 1) → K) (x : Fin d) :
    (qtwoStdWin (F := F) (K := K) m k d h s) v (blockIdx k h x) =
      ((((s : Su K 2 1 d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec
        (fun y => v (blockIdx k h y))) x := by
  change (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
    (blockEmb K 2 1 (m + 1) d k h s)) v (blockIdx k h x) = _
  rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb]
  exact blockMat_mulVec_blockIdx h _ _ x

theorem plh_qtwoStdWin_apply_not_mem (m k d : ℕ) (h : k + d ≤ m + 1)
    (s : Su K 2 1 d) (v : Fin (m + 1) → K) (i : Fin (m + 1))
    (hi : ¬ (k ≤ i.val ∧ i.val < k + d)) :
    (qtwoStdWin (F := F) (K := K) m k d h s) v i = v i := by
  change (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
    (blockEmb K 2 1 (m + 1) d k h s)) v i = _
  rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb]
  exact blockMat_mulVec_of_not_mem _ _ hi

theorem plh_diagHom_comm_qtwoStdWin (m k d : ℕ) (h : k + d ≤ m + 1)
    (u : Fin (m + 1) → normOne (unitaryInvolution K 2 1))
    (hu : ∀ a b : Fin (m + 1), k ≤ a.val → a.val < k + d → k ≤ b.val → b.val < k + d →
      u a = u b)
    (s : Su K 2 1 d) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) u *
        qtwoStdWin (F := F) (K := K) m k d h s =
      qtwoStdWin (F := F) (K := K) m k d h s *
        diagHom F (unitaryInvolution K 2 1) (m + 1) u := by
  apply LinearEquiv.ext; intro v; funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagHom_apply]
  by_cases hi : k ≤ i.val ∧ i.val < k + d
  · have hix : i = blockIdx k h ⟨i.val - k, by omega⟩ := by
      ext; simp only [blockIdx_val]; omega
    rw [hix, plh_qtwoStdWin_apply_window, plh_qtwoStdWin_apply_window]
    simp only [diagHom_apply]
    have hv : (fun y : Fin d =>
          (((u (blockIdx k h y) : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) *
            v (blockIdx k h y)) =
        ((((u (blockIdx k h ⟨i.val - k, by omega⟩) :
              normOne (unitaryInvolution K 2 1)) : Kˣ) : K)) •
          (fun y => v (blockIdx k h y)) := by
      funext y
      rw [Pi.smul_apply]
      congr 1
      exact congrArg (fun z : normOne (unitaryInvolution K 2 1) => ((z : Kˣ) : K))
        (hu (blockIdx k h y) (blockIdx k h ⟨i.val - k, by omega⟩)
          (by simp only [blockIdx_val]; omega) (by simp only [blockIdx_val]; omega)
          (by simp only [blockIdx_val]; omega) (by simp only [blockIdx_val]; omega))
    rw [hv, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  · rw [plh_qtwoStdWin_apply_not_mem m k d h s v i hi,
      plh_qtwoStdWin_apply_not_mem m k d h s
        (diagHom F (unitaryInvolution K 2 1) (m + 1) u v) i hi,
      diagHom_apply]

theorem plh_suEndN_mem_win_of_fix (m a : ℕ) (ha : a ≤ m + 1)
    {s : SUid (unitaryInvolution K 2 1) (m + 1)}
    (hfix : ∀ v ∈ torStdV₀ (F := F) m a,
      suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s v = v) :
    suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s ∈
      (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range := by
  classical
  let b := m + 1 - a
  have hb' : a + b ≤ m + 1 := by omega
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    (((s : SUid (unitaryInvolution K 2 1) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  have hM_apply : ∀ v : Fin (m + 1) → K,
      M *ᵥ v = suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s v := by
    intro v; rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def]
  have hcol : ∀ j : Fin (m + 1), j.val < a → ∀ i : Fin (m + 1),
      M i j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j := by
    intro j hj i
    have hmem : Pi.single j (1 : K) ∈ torStdV₀ (F := F) m a := by
      intro k hk
      rw [Pi.single_eq_of_ne]
      intro hkj; rw [hkj] at hk; omega
    have h := congrFun ((hM_apply (Pi.single j 1)).trans (hfix _ hmem)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    simpa [Pi.single_apply, Matrix.one_apply] using h
  have huni : conjTr (unitaryInvolution K 2 1) M * M = 1 := (mem_SUid.mp s.2).2
  have hrow : ∀ i : Fin (m + 1), i.val < a → ∀ j : Fin (m + 1),
      M i j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j := by
    intro i hi j
    have h := congrFun (congrFun huni i) j
    rw [Matrix.mul_apply] at h
    rw [Finset.sum_eq_single i] at h
    · rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, hcol i hi i, Matrix.one_apply_eq,
        map_one, one_mul] at h
      exact h
    · intro k _ hk
      rw [conjTr, Matrix.transpose_apply, Matrix.map_apply, hcol i hi k, Matrix.one_apply_ne hk,
        map_zero, zero_mul]
    · simp
  let A : Matrix (Fin b) (Fin b) K := fun x y => M (blockIdx a hb' x) (blockIdx a hb' y)
  have hMeq : M = blockMat (m + 1) a A := by
    ext i j
    have hi_lt : i.val < a + b := by omega
    have hj_lt : j.val < a + b := by omega
    by_cases hi : a ≤ i.val
    · have hi_in : a ≤ i.val ∧ i.val < a + b := ⟨hi, hi_lt⟩
      by_cases hj : a ≤ j.val
      · have hj_in : a ≤ j.val ∧ j.val < a + b := ⟨hj, hj_lt⟩
        have hi' : i = blockIdx a hb' ⟨i.val - a, by omega⟩ :=
          Fin.ext (by simp only [blockIdx_val]; omega)
        have hj' : j = blockIdx a hb' ⟨j.val - a, by omega⟩ :=
          Fin.ext (by simp only [blockIdx_val]; omega)
        rw [hi', hj', blockMat_apply_blockIdx]
      · have hj_out : ¬ (a ≤ j.val ∧ j.val < a + b) := by omega
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [blockMat_apply_of_not_mem_right A i hj_out, hcol j (by omega) i, Matrix.one_apply,
          if_neg hij]
    · have hi_out : ¬ (a ≤ i.val ∧ i.val < a + b) := by omega
      by_cases hj : a ≤ j.val
      · have hj_in : a ≤ j.val ∧ j.val < a + b := ⟨hj, hj_lt⟩
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        rw [blockMat_apply_of_not_mem_left A hi_out j, hrow i (by omega) j, Matrix.one_apply,
          if_neg hij]
      · by_cases hij : i = j
        · subst hij
          rw [blockMat_apply_of_not_mem_left A hi_out i, hrow i (by omega) i, Matrix.one_apply,
            if_pos rfl]
        · rw [blockMat_apply_of_not_mem_left A hi_out j, hrow i (by omega) j, Matrix.one_apply,
            if_neg hij]
  have huniA : conjTr (unitaryInvolution K 2 1) A * A = 1 := by
    refine blockMat_injective hb' ?_
    rw [blockMat_mul hb', ← conjTr_blockMat, ← hMeq, huni, blockMat_one]
  have hisoA : ∀ x y : Fin b → K,
      herm (unitaryInvolution K 2 1) (A *ᵥ x) (A *ᵥ y) =
        herm (unitaryInvolution K 2 1) x y := by
    intro x y; rw [herm_mulVec, huniA, Matrix.one_mulVec]
  have hdetA : A.det = 1 := by
    rw [← det_blockMat hb' A, ← hMeq]
    exact (mem_SUid.mp s.2).1
  let A' : Su K 2 1 b := mkSU (unitaryInvolution K 2 1) A hdetA hisoA
  have hA'_mat : (((A' : Su K 2 1 b) : GL (Fin b) K) : Matrix (Fin b) (Fin b) K) = A := rfl
  refine ⟨A', ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [qtwoStdWin, MonoidHom.comp_apply, suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
    coe_coe_blockEmb, hA'_mat, ← hMeq]
  exact (hM_apply v).symm

theorem plh_commutator_le_range_suEndN (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ)
    (ha : a ≤ m + 1) :
    ⁅torE₁ (Qn E (m + 1)) (torStdM ζ m a), torE₁ (Qn E (m + 1)) (torStdM ζ m a)⁆ ≤
      (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).range := by
  let D : Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
    (diagHom F (unitaryInvolution K 2 1) (m + 1)).range
  let U : Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
    (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).range
  have hE1 : torE₁ (Qn E (m + 1)) (torStdM ζ m a) ≤ D ⊔ U := plh_torE₁_le_sup E hF hζ m a ha
  have hDnorm : D ≤ Subgroup.normalizer U := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd u hu
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp
      (show d ∈ (diagHom F (unitaryInvolution K 2 1) (m + 1)).range from hd)
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp
      (show u ∈ (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).range from hu)
    rw [← ht, ← hs]
    obtain ⟨s', hs'⟩ := plh_diagHom_conj_suEndN (F := F) (K := K) (m + 1) t s
    rw [hs']
    exact MonoidHom.mem_range.mpr ⟨s', rfl⟩
  have hUnorm : (U.subgroupOf (D ⊔ U)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hDnorm (Subgroup.le_normalizer))
  have hHN : (U.subgroupOf (D ⊔ U)) ⊔ (D.subgroupOf (D ⊔ U)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_right : U ≤ D ⊔ U) (le_sup_left : D ≤ D ⊔ U)]
    simpa [sup_comm] using Subgroup.subgroupOf_self (U ⊔ D)
  have hHcomm : IsMulCommutative (D.subgroupOf (D ⊔ U)) := by
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨tx, htx⟩ := MonoidHom.mem_range.mp
      (show (x : ↥(D ⊔ U)).1 ∈ (diagHom F (unitaryInvolution K 2 1) (m + 1)).range from x.2)
    obtain ⟨ty, hty⟩ := MonoidHom.mem_range.mp
      (show (y : ↥(D ⊔ U)).1 ∈ (diagHom F (unitaryInvolution K 2 1) (m + 1)).range from y.2)
    show (x : ↥(D ⊔ U)).1 * (y : ↥(D ⊔ U)).1 =
      (y : ↥(D ⊔ U)).1 * (x : ↥(D ⊔ U)).1
    rw [← htx, ← hty, ← map_mul, ← map_mul, mul_comm]
  haveI := hUnorm
  have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (N := U.subgroupOf (D ⊔ U)) hHN hHcomm
  have hmap : ⁅D ⊔ U, D ⊔ U⁆ ≤ U := by
    have h1 := Subgroup.map_mono (f := (D ⊔ U).subtype) hcomm
    simpa only [commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right : U ≤ D ⊔ U)] using h1
  exact (Subgroup.commutator_mono hE1 hE1).trans hmap

end ModelU

end CFSG.StandardType.QTwo

end
