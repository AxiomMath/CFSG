module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.StandardType.GGQTwoDRigidSU3
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.ClassicalGroups.Unitary
open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private lemma su_diagonal_mem {n : ℕ} (d : Fin n → K)
    (h : ∀ i, CFSG.LieType.BorelTits.unitaryInvolution K 2 1 (d i) * d i = 1)
    (hdet : (∏ i, d i) = 1) :
    ∃ g : Su K 2 1 n, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal d := by
  classical
  have hMdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    exact hdet
  let A : GL (Fin n) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
      (by rw [hMdet]; exact one_ne_zero)
  have hA : A ∈ SUid (CFSG.LieType.BorelTits.unitaryInvolution K 2 1) n := by
    rw [mem_SUid]
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hMdet
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [conjTr, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact h i
  exact ⟨⟨A, hA⟩, Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩

private lemma ker_eq_bot_of_coordBlocks (hK : Nat.card K = 4) {X : Type} [Group X]
    {U V : Subgroup X} {θ : Su K 2 1 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K 2 1 3))
    (hU : (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map θ = U)
    (hV : (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map θ = V)
    (hUV : ∀ g ∈ U, g ∈ V → g ^ 3 = 1 → g = 1) :
    θ.ker = ⊥ := by
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [hK]
    norm_num
  have hσ : IsUnitaryInvolution (CFSG.LieType.BorelTits.unitaryInvolution K 2 1) :=
    isUnitaryInvolution_unitaryInvolution hK'
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hxc : x ∈ Subgroup.center (Su K 2 1 3) := hker hx
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 3) hxc
  have hu3 : (u : K) ^ 3 = 1 := by
    have hxdet : (((x : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).det = 1 := x.2.1
    rw [hu, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at hxdet
    simpa using hxdet
  have hu1 : (u : K) ≠ 1 := by
    intro h1
    apply hxne
    apply Subtype.ext
    apply Units.ext
    rw [hu, h1]
    simp
  have hinv3 : ((u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu3, inv_one]
  let d : Fin 3 → K := ![((u⁻¹ : Kˣ) : K), (u : K), 1]
  have hd : ∀ i, CFSG.LieType.BorelTits.unitaryInvolution K 2 1 (d i) * d i = 1 := by
    intro i
    fin_cases i <;>
      simp [d, frobenius_def, ← Units.val_inv_eq_inv_val, ← inv_pow, ← pow_succ, hu3, hinv3]
  have hdet : (∏ i, d i) = 1 := by
    simp [d, Fin.prod_univ_three, Units.val_inv_eq_inv_val]
  obtain ⟨s, hs⟩ := su_diagonal_mem d hd hdet
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    fin_cases i <;> simp [d, hu3]
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hs]
    have hpow3 : (Matrix.diagonal d : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        Matrix.diagonal (fun i => d i ^ 3) := by
      rw [pow_succ, pow_succ, pow_one, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    rw [hpow3, show (fun i => d i ^ 3) = fun _ => (1 : K) by funext i; exact hd3 i,
      Matrix.diagonal_one]
    simp
  have hsx : (((s * x : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, (u : K) ^ 2, (u : K)] := by
    rw [Subgroup.coe_mul, Units.val_mul, hs, hu, Matrix.scalar_apply,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;>
      simp [d, Units.val_inv_eq_inv_val, pow_two]
  have hs01 : s ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
    rw [mem_coordBlockSU_iff]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hsx12 : s * x ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
    rw [mem_coordBlockSU_iff]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hxθ : θ x = 1 := (MonoidHom.mem_ker).mp hx
  have hgsU : θ s ∈ U := by
    rw [← hU]
    exact Subgroup.mem_map_of_mem θ hs01
  have hgsV : θ s ∈ V := by
    have hsame : θ s = θ (s * x) := by
      rw [map_mul, hxθ, mul_one]
    rw [hsame, ← hV]
    exact Subgroup.mem_map_of_mem θ hsx12
  have hgs3 : (θ s) ^ 3 = 1 := by
    rw [← map_pow, hs3, map_one]
  have hgs1 : θ s = 1 := hUV (θ s) hgsU hgsV hgs3
  have hsker : s ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    exact hgs1
  have hsc : s ∈ Subgroup.center (Su K 2 1 3) := hker hsker
  obtain ⟨v, hv⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 3) hsc
  have hmat : Matrix.diagonal d = Matrix.scalar (Fin 3) (v : K) := hs.symm.trans hv
  have h1 : d 1 = (v : K) := by
    have := congrFun (congrFun hmat 1) 1
    simpa [Matrix.scalar_apply] using this
  have h2 : d 2 = (v : K) := by
    have := congrFun (congrFun hmat 2) 2
    simpa [Matrix.scalar_apply] using this
  have h12 : d 1 = d 2 := by rw [h1, h2]
  exact hu1 (by simpa [d] using h12)

private lemma commute_of_coordBlocks (hK : Nat.card K = 4) {X : Type} [Group X]
    {W U V : Subgroup X} {θ : Su K 2 1 3 →* X} (hrange : θ.range = W)
    (hker : θ.ker ≤ Subgroup.center (Su K 2 1 3))
    (hU : (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map θ = U)
    (hV : (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map θ = V)
    (hUV : ∀ g ∈ U, g ∈ V → g ^ 3 = 1 → g = 1) {u : X} {k : ℕ} (hu : u ^ 2 ^ k = 1)
    (huW : u ∈ Subgroup.normalizer (W : Set X))
    (hcU : ∀ g ∈ U, g ^ 3 = 1 → u * g = g * u)
    (hcV : ∀ g ∈ V, g ^ 3 = 1 → u * g = g * u) :
    ∀ y ∈ W, u * y = y * u := by
  classical
  have hkerbot : θ.ker = ⊥ :=
    ker_eq_bot_of_coordBlocks hK hker hU hV hUV
  have hθinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hkerbot
  let e : Su K 2 1 3 ≃* W :=
    (MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ g : Su K 2 1 3, ((e g : W) : X) = θ g := by
    intro g
    simp [e, MonoidHom.ofInjective_apply]
  have hmapW : W.map (MulAut.conj u).toMonoidHom = W := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp huW w).mp hw
    · intro w hw
      refine ⟨u⁻¹ * w * u, ?_, ?_⟩
      · have hinv : u⁻¹ ∈ Subgroup.normalizer (W : Set X) := Subgroup.inv_mem _ huW
        simpa using (Subgroup.mem_normalizer_iff.mp hinv w).mp hw
      · change u * (u⁻¹ * w * u) * u⁻¹ = w
        group
  let cW : MulAut W :=
    (W.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective).trans
      (MulEquiv.subgroupCongr hmapW)
  have hcW : ∀ w : W, ((cW w : W) : X) = u * (w : X) * u⁻¹ := by
    intro w
    rfl
  let α : MulAut (Su K 2 1 3) := e.trans (cW.trans e.symm)
  have hα : ∀ g : Su K 2 1 3, θ (α g) = u * θ g * u⁻¹ := by
    intro g
    have h1 : ((e (α g) : W) : X) = u * ((e g : W) : X) * u⁻¹ := by
      simp [α, hcW]
    rw [he, he] at h1
    exact h1
  have hpow : ∀ n : ℕ, ∀ g : Su K 2 1 3,
      θ ((α ^ n) g) = u ^ n * θ g * (u ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
        intro g
        simp
    | succ n ih =>
        intro g
        calc θ ((α ^ (n + 1)) g) = θ ((α ^ n * α) g) := by rw [pow_succ]
          _ = θ ((α ^ n) (α g)) := by rw [MulAut.mul_apply]
          _ = u ^ n * θ (α g) * (u ^ n)⁻¹ := ih (α g)
          _ = u ^ n * (u * θ g * u⁻¹) * (u ^ n)⁻¹ := by rw [hα g]
          _ = u ^ (n + 1) * θ g * (u ^ (n + 1))⁻¹ := by
                rw [pow_succ]
                group
  have hk : α ^ 2 ^ k = 1 := by
    apply MulEquiv.ext
    intro g
    apply hθinj
    rw [hpow (2 ^ k) g, hu]
    simp
  have h01 : ∀ g ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)), g ^ 3 = 1 → α g = g := by
    intro g hg hg3
    apply hθinj
    have hmem : θ g ∈ U := by
      rw [← hU]
      exact Subgroup.mem_map_of_mem θ hg
    have hcube : (θ g) ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    have hcomm := hcU (θ g) hmem hcube
    rw [hα g, hcomm]
    group
  have h12 : ∀ g ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)), g ^ 3 = 1 → α g = g := by
    intro g hg hg3
    apply hθinj
    have hmem : θ g ∈ V := by
      rw [← hV]
      exact Subgroup.mem_map_of_mem θ hg
    have hcube : (θ g) ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    have hcomm := hcV (θ g) hmem hcube
    rw [hα g, hcomm]
    group
  have hα1 : α = 1 := mulAut_su3_eq_one hK α hk h01 h12
  intro y hy
  have hy' : y ∈ θ.range := by rwa [hrange]
  obtain ⟨g, hg⟩ := hy'
  subst hg
  have h := hα g
  rw [hα1] at h
  simp only [MulAut.one_apply] at h
  calc u * θ g = u * θ g * u⁻¹ * u := by group
    _ = θ g * u := by rw [h.symm]

theorem commute_of_unitaryBlockStandardPair (hK : Nat.card K = 4) {X : Type} [Group X]
    {W U V : Subgroup X} (hP : UnitaryBlockStandardPair K 2 1 W U V)
    (hUV : ∀ g ∈ U, g ∈ V → g ^ 3 = 1 → g = 1) {u : X} {k : ℕ} (hu : u ^ 2 ^ k = 1)
    (huW : u ∈ Subgroup.normalizer (W : Set X))
    (hcU : ∀ g ∈ U, g ^ 3 = 1 → u * g = g * u) (hcV : ∀ g ∈ V, g ^ 3 = 1 → u * g = g * u) :
    ∀ y ∈ W, u * y = y * u := by
  classical
  obtain ⟨θ, c, hrange, hker, hblocks⟩ := hP
  let θ' : Su K 2 1 3 →* X := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hrange' : θ'.range = W := by
    have hsurj : Function.Surjective (MulAut.conj c⁻¹).toMonoidHom :=
      (MulAut.conj c⁻¹).surjective
    have htop : (MulAut.conj c⁻¹).toMonoidHom.range = ⊤ := by
      rw [← Subgroup.map_top, Subgroup.map_top_of_surjective _ hsurj]
    rw [show θ' = θ.comp (MulAut.conj c⁻¹).toMonoidHom from rfl, MonoidHom.range_comp,
      htop, Subgroup.map_top, hrange]
  have hker' : θ'.ker ≤ Subgroup.center (Su K 2 1 3) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxc : (MulAut.conj c⁻¹) x ∈ Subgroup.center (Su K 2 1 3) := by
      apply hker
      exact hx
    have h := (Subgroup.mem_center_iff.mp hxc) ((MulAut.conj c⁻¹) y)
    simp only [MulAut.conj_apply, inv_inv] at h
    calc y * x = c * (c⁻¹ * y * c) * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = x * y := by group
  rcases hblocks with ⟨h12, h23⟩ | ⟨h12, h23⟩
  · exact commute_of_coordBlocks hK hrange' hker'
      (by rw [← B12_eq_coordBlockSU, ← h12, Subgroup.map_map])
      (by rw [← B23_eq_coordBlockSU, ← h23, Subgroup.map_map])
      hUV hu huW hcU hcV
  · exact commute_of_coordBlocks hK hrange' hker'
      (by rw [← B12_eq_coordBlockSU, ← h12, Subgroup.map_map])
      (by rw [← B23_eq_coordBlockSU, ← h23, Subgroup.map_map])
      (fun g hgU hgV hg3 => hUV g hgV hgU hg3) hu huW hcV hcU

end CFSG.StandardType.QTwo

end
