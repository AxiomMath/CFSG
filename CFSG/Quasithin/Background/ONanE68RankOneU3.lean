module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import CFSG.Open.Catalog
import CFSG.StronglyEmbedded.BenderBinaryHermitian
import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.Quasithin.E6.E68Proof

namespace RankOne

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization

@[expose] def OTB {S : Type*} [Group S] (P : Subgroup S) (q : ℕ) : Prop :=
  ∀ c ∈ Subgroup.normalizer (P : Set S), orderOf c = 3 →
    Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set S)) ≤ q

theorem OTB.of_equiv {S T : Type*} [Group S] [Group T] [Finite S] (φ : S ≃* T)
    {P : Subgroup S} {Q : Subgroup T} (hPQ : ∀ x, x ∈ Q ↔ φ.symm x ∈ P) {q : ℕ}
    (h : OTB P q) : OTB Q q := by
  intro c' hc' hc3
  have hc : φ.symm c' ∈ Subgroup.normalizer (P : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : x ∈ P ↔ φ x ∈ Q := by rw [hPQ]; simp
    have h2 := Subgroup.mem_normalizer_iff.mp hc' (φ x)
    have h3 : c' * φ x * c'⁻¹ ∈ Q ↔ φ.symm c' * x * (φ.symm c')⁻¹ ∈ P := by
      rw [hPQ]; simp
    rw [h1, h2, h3]
  have h3 : orderOf (φ.symm c') = 3 := by rw [MulEquiv.orderOf_eq]; exact hc3
  have hmem : ∀ x : ↥(Q ⊓ Subgroup.centralizer ({c'} : Set T)),
      φ.symm x ∈ P ⊓ Subgroup.centralizer ({φ.symm c'} : Set S) := by
    intro x
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp x.2
    refine Subgroup.mem_inf.mpr ⟨(hPQ _).mp hxQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
    have := congrArg φ.symm hxc
    simpa using this
  exact le_trans (Nat.card_le_card_of_injective
    (fun x : ↥(Q ⊓ Subgroup.centralizer ({c'} : Set T)) =>
      (⟨φ.symm x, hmem x⟩ : ↥(P ⊓ Subgroup.centralizer ({φ.symm c'} : Set S))))
    (fun x y hxy => Subtype.ext (φ.symm.injective (congrArg Subtype.val hxy))))
    (h _ hc h3)

theorem exists_map_conj_eq {G : Type*} [Group G] [Finite G] (Q Q' : Sylow 2 G) :
    ∃ g : G, (Q' : Subgroup G) = (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G Q Q'
  refine ⟨g, ?_⟩
  rw [Sylow.coe_subgroup_smul]
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map, MulAut.smul_def,
    MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, by simpa using h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

section Heisenberg

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem pgl_entries {A B : GL (Fin 3) K}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    ∃ u : Kˣ, ∀ i j, (A : Matrix (Fin 3) (Fin 3) K) i j * u =
      (B : Matrix (Fin 3) (Fin 3) K) i j := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  refine ⟨u, fun i j => ?_⟩
  have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) i j) hu
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.diagonal_apply] using this

@[expose] def uMat (z : K × K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, z.1, z.2; 0, 1, -σ z.1; 0, 0, 1]

@[expose] def dMat (k : K) : Matrix (Fin 3) (Fin 3) K :=
  !![(σ k)⁻¹, 0, 0; 0, σ k * k⁻¹, 0; 0, 0, k]

theorem uMat_mul_00 {M1 M2 : Matrix (Fin 3) (Fin 3) K} {z1 z2 : K × K}
    (h1 : M1 = uMat σ z1) (h2 : M2 = uMat σ z2) : (M1 * M2) 0 0 = 1 := by
  subst h1 h2
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem uMat_mul_01 {M1 M2 : Matrix (Fin 3) (Fin 3) K} {z1 z2 : K × K}
    (h1 : M1 = uMat σ z1) (h2 : M2 = uMat σ z2) : (M1 * M2) 0 1 = z1.1 + z2.1 := by
  subst h1 h2
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem dMat_uMat_00 {M1 M2 : Matrix (Fin 3) (Fin 3) K} {z : K × K} {k : K}
    (h1 : M1 = dMat σ k) (h2 : M2 = uMat σ z) : (M1 * M2) 0 0 = (σ k)⁻¹ := by
  subst h1 h2
  simp [uMat, dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem dMat_uMat_01 {M1 M2 : Matrix (Fin 3) (Fin 3) K} {z : K × K} {k : K}
    (h1 : M1 = dMat σ k) (h2 : M2 = uMat σ z) : (M1 * M2) 0 1 = (σ k)⁻¹ * z.1 := by
  subst h1 h2
  simp [uMat, dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem uMat_dMat_00 {M1 M2 : Matrix (Fin 3) (Fin 3) K} {z : K × K} {k : K}
    (h1 : M1 = uMat σ z) (h2 : M2 = dMat σ k) : (M1 * M2) 0 0 = (σ k)⁻¹ := by
  subst h1 h2
  simp [uMat, dMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem uMat_dMat_01 {M1 M2 : Matrix (Fin 3) (Fin 3) K} {z : K × K} {k : K}
    (h1 : M1 = uMat σ z) (h2 : M2 = dMat σ k) : (M1 * M2) 0 1 = z.1 * (σ k * k⁻¹) := by
  subst h1 h2
  simp [uMat, dMat, Matrix.mul_apply, Fin.sum_univ_three]

omit [Field K] in
private theorem exists_mul_of_mem_sup' {G : Type*} [Group G] {Q D : Subgroup G}
    (hD : D ≤ Subgroup.normalizer (Q : Set G)) {a : G} (ha : a ∈ Q ⊔ D) :
    ∃ p ∈ Q, ∃ d ∈ D, a = p * d := by
  open scoped Pointwise in
  have h := Subgroup.coe_mul_of_right_le_normalizer_left Q D hD
  have ha' : a ∈ (Q : Set G) * (D : Set G) := h ▸ ha
  obtain ⟨p, hp, d, hd, rfl⟩ := ha'
  exact ⟨p, hp, d, hd, rfl⟩

variable [Finite K] [CharP K 2]

theorem card_inf_centralizer_le
    (hσ : ∀ x, σ (σ x) = x)
    (G : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K)) (R H : Subgroup G)
    (coord : {z : K × K // z.2 + σ z.2 + z.1 * σ z.1 = 0} ≃ R)
    (hcoord : ∀ z, ∃ M : GL (Fin 3) K, (M : Matrix (Fin 3) (Fin 3) K) = uMat σ z.1 ∧
      (((coord z : R) : G) : Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M)
    (hH : ∀ h : H, ∃ k : Kˣ, ∃ M : GL (Fin 3) K, (M : Matrix (Fin 3) (Fin 3) K) = dMat σ k ∧
      ((h : G) : Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M)
    (hHN : H ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R) {q : ℕ}
    (hfixed : Nat.card {x : K // σ x = x} ≤ q)
    {c : G} (hc : c ∈ R ⊔ H) (hc3 : orderOf c = 3) :
    Nat.card ↥(R ⊓ Subgroup.centralizer ({c} : Set G)) ≤ q := by
  classical
  let A : G → K := fun g => if hg : g ∈ R then (coord.symm ⟨g, hg⟩).1.1 else 0
  have hA : ∀ (g : G) (hg : g ∈ R), A g = (coord.symm ⟨g, hg⟩).1.1 := fun g hg => by
    simp [A, hg]
  have hlift : ∀ (g : G) (hg : g ∈ R), ∃ M : GL (Fin 3) K,
      (M : Matrix (Fin 3) (Fin 3) K) = uMat σ (coord.symm ⟨g, hg⟩).1 ∧
      (g : Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M := by
    intro g hg
    obtain ⟨M, hM, hMk⟩ := hcoord (coord.symm ⟨g, hg⟩)
    rw [Equiv.apply_symm_apply] at hMk
    exact ⟨M, hM, hMk⟩
  have hAmul : ∀ (g1 g2 : G) (h1 : g1 ∈ R) (h2 : g2 ∈ R), A (g1 * g2) = A g1 + A g2 := by
    intro g1 g2 h1 h2
    have h12 : g1 * g2 ∈ R := R.mul_mem h1 h2
    obtain ⟨M1, hM1, hk1⟩ := hlift g1 h1
    obtain ⟨M2, hM2, hk2⟩ := hlift g2 h2
    obtain ⟨M3, hM3, hk3⟩ := hlift (g1 * g2) h12
    have hmk : Matrix.ProjGenLinGroup.mk (M1 * M2) = Matrix.ProjGenLinGroup.mk M3 := by
      rw [map_mul, ← hk1, ← hk2, ← hk3]
      rfl
    obtain ⟨u, hu⟩ := pgl_entries hmk
    have e00 := hu 0 0
    have e01 := hu 0 1
    rw [Units.val_mul, uMat_mul_00 σ hM1 hM2, hM3] at e00
    rw [Units.val_mul, uMat_mul_01 σ hM1 hM2, hM3] at e01
    simp only [uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01
    have hu1 : (u : K) = 1 := by simpa using e00
    rw [hu1, mul_one] at e01
    rw [hA _ h12, hA _ h1, hA _ h2, ← e01]
  have hAconj : ∀ h : G, h ∈ H → ∃ μ : K, (h = 1 ∨ μ ≠ 1) ∧
      ∀ (r : G) (hr : r ∈ R), A (h * r * h⁻¹) = μ * A r := by
    intro h hh
    obtain ⟨k, Mh, hMh, hk⟩ := hH ⟨h, hh⟩
    have hk0 : (k : K) ≠ 0 := k.ne_zero
    have hσk0 : σ k ≠ 0 := by
      intro h0
      exact hk0 (σ.injective (by rw [h0, map_zero]))
    refine ⟨(σ k)⁻¹ * (σ k * (k : K)⁻¹)⁻¹, ?_, ?_⟩
    · by_cases hμ : (σ k)⁻¹ * (σ k * (k : K)⁻¹)⁻¹ = 1
      · left
        have h1 : (σ k)⁻¹ = σ k * (k : K)⁻¹ := by
          have : (σ k * (k : K)⁻¹)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσk0 (inv_ne_zero hk0))
          field_simp at hμ ⊢
          linear_combination hμ
        have h2 : (k : K) = σ k * σ k := by
          field_simp at h1
          linear_combination h1
        have h3 : σ k = (k : K) * k := by
          have := congrArg σ h2
          rw [map_mul, hσ] at this
          rw [this]
        have h4 : (k : K) * k * k = 1 := by
          have : (k : K) = (k * k) * (k * k) := by
            calc (k : K) = σ k * σ k := h2
              _ = (k * k) * (k * k) := by rw [h3]
          apply mul_left_cancel₀ hk0
          linear_combination -this
        have hMs : Mh = Matrix.GeneralLinearGroup.scalar (Fin 3) k := by
          apply Units.ext
          have hd1 : (σ k)⁻¹ = (k : K) := by
            rw [h3]; field_simp; first | linear_combination h4 | linear_combination -h4
          have hd2 : σ k * (k : K)⁻¹ = (k : K) := by
            rw [h3]; field_simp
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [hMh, dMat, Matrix.GeneralLinearGroup.coe_scalar, hd1, hd2]
        have h1' : ((h : G) : Matrix.ProjGenLinGroup (Fin 3) K) = 1 := by
          rw [hk, hMs, Matrix.ProjGenLinGroup.mk_scalar]
        exact Subtype.ext h1'
      · right
        exact hμ
    · intro r hr
      have hr' : h * r * h⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hHN hh) r).mp hr
      obtain ⟨M, hM, hkM⟩ := hlift r hr
      obtain ⟨M', hM', hkM'⟩ := hlift (h * r * h⁻¹) hr'
      have hmk : Matrix.ProjGenLinGroup.mk (M' * Mh) = Matrix.ProjGenLinGroup.mk (Mh * M) := by
        rw [map_mul, map_mul, ← hkM', ← hkM, ← hk]
        have : h * r * h⁻¹ * h = h * r := by group
        exact congrArg (fun g : G => (g : Matrix.ProjGenLinGroup (Fin 3) K)) this
      obtain ⟨u, hu⟩ := pgl_entries hmk
      have e00 := hu 0 0
      have e01 := hu 0 1
      rw [Units.val_mul, uMat_dMat_00 σ hM' hMh, Units.val_mul, dMat_uMat_00 σ hMh hM] at e00
      rw [Units.val_mul, uMat_dMat_01 σ hM' hMh, Units.val_mul, dMat_uMat_01 σ hMh hM] at e01
      have hu1 : (u : K) = 1 := by
        have : (σ k)⁻¹ * (u - 1) = 0 := by linear_combination e00
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd (inv_eq_zero.mp h0) hσk0
        · exact sub_eq_zero.mp h0
      rw [hu1, mul_one] at e01
      rw [hA _ hr', hA _ hr]
      field_simp at e01 ⊢
      linear_combination e01
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r0, hr0, h, hh, rfl⟩ := exists_mul_of_mem_sup' hHN hc
  obtain ⟨μ, hμ, hconj⟩ := hAconj h hh
  have hh1 : h ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc3
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hR2 ⟨r0, hr0⟩
    rw [Subgroup.orderOf_mk, hc3] at hm
    cases m with
    | zero => omega
    | succ m => rw [pow_succ] at hm; omega
  have hμ1 : μ ≠ 1 := hμ.resolve_left hh1
  have hA1 : A 1 = 0 := by
    have := hAmul 1 1 R.one_mem R.one_mem
    rw [mul_one] at this
    linear_combination -this
  have hAinv : ∀ g ∈ R, A g⁻¹ = - A g := by
    intro g hg
    have := hAmul g g⁻¹ hg (R.inv_mem hg)
    rw [mul_inv_cancel, hA1] at this
    linear_combination -this
  have hzero : ∀ x : G, x ∈ R → x * (r0 * h) = (r0 * h) * x → A x = 0 := by
    intro x hxR hxc
    have hy : h * x * h⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hHN hh) x).mp hxR
    have hx : x = r0 * (h * x * h⁻¹) * r0⁻¹ := by
      calc x = (r0 * h) * x * (r0 * h)⁻¹ := by rw [← hxc]; group
        _ = r0 * (h * x * h⁻¹) * r0⁻¹ := by group
    have h1 : A x = A r0 + A (h * x * h⁻¹) + A r0⁻¹ := by
      conv_lhs => rw [hx]
      rw [hAmul _ _ (R.mul_mem hr0 hy) (R.inv_mem hr0), hAmul _ _ hr0 hy]
    rw [hconj x hxR, hAinv r0 hr0] at h1
    have h2 : (1 - μ) * A x = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hμ1
    · exact h0
  have memR : ∀ x : ↥(R ⊓ Subgroup.centralizer ({r0 * h} : Set G)), (x : G) ∈ R :=
    fun x => (Subgroup.mem_inf.mp x.2).1
  have hz0 : ∀ x : ↥(R ⊓ Subgroup.centralizer ({r0 * h} : Set G)),
      (coord.symm ⟨x, memR x⟩).1.1 = 0 := fun x => by
    rw [← hA _ (memR x)]
    exact hzero x (memR x) (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2)
  have hfix : ∀ x : ↥(R ⊓ Subgroup.centralizer ({r0 * h} : Set G)),
      σ (coord.symm ⟨x, memR x⟩).1.2 = (coord.symm ⟨x, memR x⟩).1.2 := by
    intro x
    have h0 := (coord.symm ⟨x, memR x⟩).2
    rw [hz0 x, zero_mul, add_zero] at h0
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination h0 - (coord.symm ⟨x, memR x⟩).1.2 * h2
  let f : ↥(R ⊓ Subgroup.centralizer ({r0 * h} : Set G)) → {x : K // σ x = x} :=
    fun x => ⟨(coord.symm ⟨x, memR x⟩).1.2, hfix x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : coord.symm ⟨x, memR x⟩ = coord.symm ⟨y, memR y⟩ :=
      Subtype.ext (Prod.ext (by rw [hz0 x, hz0 y]) (congrArg Subtype.val hxy))
    exact Subtype.ext (congrArg Subtype.val (coord.symm.injective h1) : _)
  exact (Nat.card_le_card_of_injective f hinj).trans hfixed

end Heisenberg

theorem exists_sylow_bound {K : Type} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      OTB (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (2 ^ f) := by
  let q := 2 ^ f
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  rcases huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, a, _hinj, _hnatural, _hUcard,
      ⟨R, D, hRle, hDle, hN, hinf, hsup, hcyc, hRcard,
        hcomm, hcommcard, hDcard, hreg, ⟨coord, hcoord⟩,
        hDcoord, _hDsurj⟩, htwo, _hGcard, _hthree⟩
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hstab : (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho =
      MulAction.stabilizer G a := by
    ext g
    rfl
  have hRle' : R ≤ MulAction.stabilizer G a := hstab ▸ hRle
  have hDle' : D ≤ MulAction.stabilizer G a := hstab ▸ hDle
  have hN' : MulAction.stabilizer G a ≤ Subgroup.normalizer (R : Set G) :=
    hstab ▸ hN
  have hsup' : R ⊔ D = MulAction.stabilizer G a := hsup.trans hstab
  have hqpos : 0 < q := by positivity
  have hqeven : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    have hdiv : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
      rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq q 1]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
    exact Odd.of_dvd_nat
      (Nat.Even.sub_odd (pow_pos hqpos 2)
        (hqeven.pow_of_ne_zero (by norm_num)) odd_one)
      (Nat.div_dvd_of_dvd hdiv)
  have hRp : IsPGroup 2 R :=
    IsPGroup.of_card (n := f * 3) (by simpa only [q, ← pow_mul] using hRcard)
  have hRne : R ≠ ⊥ := by
    intro h
    have hcard : Nat.card R = 1 := by rw [h]; simp
    rw [hcard] at hRcard
    have : (1 : ℕ) = q ^ 3 := hRcard
    have h4 : 4 ≤ q := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h5 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h4 3
    omega
  have hreg' : ∀ b c : Ω, b ≠ a → c ≠ a → ∃! r : R, (r : G) • b = c := hreg
  have hnormalizer : Subgroup.normalizer (R : Set G) = MulAction.stabilizer G a :=
    normalizer_eq_stabilizer_of_regular_compl R a hRle' hRne hreg' hN'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P0, hP0⟩ := exists_sylow_map_eq_of_normal_complement
    hRle' hDle' hN' hinf hsup' hRp hDodd.not_two_dvd_nat
  obtain ⟨S0, hS0⟩ := exists_sylow_map_eq_of_normalizer_le P0 (by
    rw [hP0, hnormalizer])
  have hSR : (S0 : Subgroup G) = R := hS0.trans hP0
  refine ⟨S0, fun c hc hc3 => ?_⟩
  rw [hSR] at hc ⊢
  have hcU : c ∈ R ⊔ D := by
    rw [hsup', ← hnormalizer]
    exact hc
  have hHN : D ≤ Subgroup.normalizer (R : Set G) := fun d hd => hN' (hDle' hd)
  refine card_inf_centralizer_le J.conj J.conj_involutive G R D coord ?_ ?_ hHN hRp
    (le_of_eq hfixed) hcU hc3
  · intro z
    obtain ⟨M, hM, hMk⟩ := hcoord z
    exact ⟨M, hM, hMk⟩
  · intro h
    obtain ⟨k, M, hM, hMk⟩ := hDcoord h
    exact ⟨k, M, hM, hMk⟩

theorem orderThreeBound_psu {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (e : S ≃* PSU3 2 f) (P : Sylow 2 S) : OTB (P : Subgroup S) (2 ^ f) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective
    (fun x : ProjectiveSpecialUnitaryMatrixGroup J => (x : Matrix.ProjGenLinGroup (Fin 3) K))
    Subtype.coe_injective
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f :=
    CFSG.Models.benderPSU3Model_eq_psu3 f
  let ψ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some.trans
      (MulEquiv.subgroupCongr hmodel)
  let Φ : S ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans ψ.symm
  obtain ⟨Q0, hQ0⟩ := exists_sylow_bound J f hf hKcard hfixed hJ
  let P' : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    P.mapSurjective (f := Φ.toMonoidHom) Φ.surjective
  obtain ⟨g, hg⟩ := exists_map_conj_eq Q0 P'
  have h1 : OTB (P' : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (2 ^ f) := by
    refine OTB.of_equiv (MulAut.conj g) (P := (Q0 : Subgroup _)) (fun x => ?_) hQ0
    rw [hg, Subgroup.mem_map_equiv]
  have hP' : (P' : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (P : Subgroup S).map Φ.toMonoidHom := Sylow.coe_mapSurjective _ P
  refine OTB.of_equiv Φ.symm (P := (P' : Subgroup _)) (fun x => ?_) h1
  rw [MulEquiv.symm_symm, hP', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end RankOne

end CFSG.Quasithin.E6.E68Proof
