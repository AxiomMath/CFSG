module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
import CFSG.RankThree.PartTwo.Sec21.FF81P51Eleven
import CFSG.LocalAnalysis.StandardType.GGFFP51

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec21.FF81 (autOrder)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open CFSG.RankThree.PartTwo.Sec21.FF81 CFSG.RankThree.PartTwo.Sec21.FF81.P51T
  CFSG.RankThree.PartTwo.Sec21.FF81.P51
open Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

private theorem cvG_conj {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {n : G} (hn : n ∈ Nor B) {x : G}
    (hx : x ∈ B) : cvG β (n * x * n⁻¹) = ρM β ⟨n, hn⟩ *ᵥ cvG β x := by
  have hmem : n * x * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  rw [cvG_of_mem β hmem, cvG_of_mem β hx, ρM_mulVec]
  exact congrArg (cv β) (Subtype.ext rfl)

private theorem conj_eq_of_cv {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {n x y : G} (hn : n ∈ Nor B)
    (hx : x ∈ B) (hy : y ∈ B) (h : ρM β ⟨n, hn⟩ *ᵥ cvG β x = cvG β y) : n * x * n⁻¹ = y :=
  cvG_inj β ((Subgroup.mem_normalizer_iff.mp hn x).mp hx) hy ((cvG_conj β hn hx).trans h)

private theorem conj_eq_of_cv_inv {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {n x y : G} (hn : n ∈ Nor B)
    (hx : x ∈ B) (hy : y ∈ B) (h : ρM β ⟨n⁻¹, (Nor B).inv_mem hn⟩ *ᵥ cvG β x = cvG β y) :
    n⁻¹ * x * n = y := by
  have h1 := cvG_conj β ((Nor B).inv_mem hn) hx
  rw [inv_inv] at h1
  have hmem : n⁻¹ * x * n ∈ B := by
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp ((Nor B).inv_mem hn) x).mp hx
  exact cvG_inj β hmem hy (h1.trans h)

omit [Finite G] in
private theorem ρM_mul3 {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {m₁ m₂ m₃ : G} (h₁ : m₁ ∈ Nor B)
    (h₂ : m₂ ∈ Nor B) (h₃ : m₃ ∈ Nor B) :
    ρM β ⟨m₁ * m₂ * m₃, (Nor B).mul_mem ((Nor B).mul_mem h₁ h₂) h₃⟩ =
      ρM β ⟨m₁, h₁⟩ * ρM β ⟨m₂, h₂⟩ * ρM β ⟨m₃, h₃⟩ := by
  change ρ β ⟨m₁ * m₂ * m₃, (Nor B).mul_mem ((Nor B).mul_mem h₁ h₂) h₃⟩ =
    ρ β ⟨m₁, h₁⟩ * ρ β ⟨m₂, h₂⟩ * ρ β ⟨m₃, h₃⟩
  rw [show (⟨m₁ * m₂ * m₃, (Nor B).mul_mem ((Nor B).mul_mem h₁ h₂) h₃⟩ : Nor B) =
    ⟨m₁, h₁⟩ * ⟨m₂, h₂⟩ * ⟨m₃, h₃⟩ from Subtype.ext rfl, map_mul, map_mul]

omit [Finite G] in
private theorem ρM_mul4 {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {m₁ m₂ m₃ m₄ : G} (h₁ : m₁ ∈ Nor B)
    (h₂ : m₂ ∈ Nor B) (h₃ : m₃ ∈ Nor B) (h₄ : m₄ ∈ Nor B) :
    ρM β ⟨m₁ * m₂ * m₃ * m₄, (Nor B).mul_mem ((Nor B).mul_mem ((Nor B).mul_mem h₁ h₂) h₃) h₄⟩ =
      ρM β ⟨m₁, h₁⟩ * ρM β ⟨m₂, h₂⟩ * ρM β ⟨m₃, h₃⟩ * ρM β ⟨m₄, h₄⟩ := by
  change ρ β ⟨m₁ * m₂ * m₃ * m₄,
      (Nor B).mul_mem ((Nor B).mul_mem ((Nor B).mul_mem h₁ h₂) h₃) h₄⟩ =
    ρ β ⟨m₁, h₁⟩ * ρ β ⟨m₂, h₂⟩ * ρ β ⟨m₃, h₃⟩ * ρ β ⟨m₄, h₄⟩
  rw [show (⟨m₁ * m₂ * m₃ * m₄,
      (Nor B).mul_mem ((Nor B).mul_mem ((Nor B).mul_mem h₁ h₂) h₃) h₄⟩ : Nor B) =
    ⟨m₁, h₁⟩ * ⟨m₂, h₂⟩ * ⟨m₃, h₃⟩ * ⟨m₄, h₄⟩ from Subtype.ext rfl, map_mul, map_mul, map_mul]

private theorem ρM_inv {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {m : G} (hm : m ∈ Nor B) {A : Mat}
    (hA : ρM β ⟨m, hm⟩ = A) (hAA : A * A = 1) :
    ρM β ⟨m⁻¹, (Nor B).inv_mem hm⟩ = A := by
  have hu : (ρU β ⟨m, hm⟩ : GL4) = ⟨A, A, hAA, hAA⟩ := by
    ext
    rw [coe_ρU, hA]
  have hu2 : (ρU β ⟨m, hm⟩) * (ρU β ⟨m, hm⟩) = 1 := by
    apply Units.ext
    rw [Units.val_mul, hu, hAA, Units.val_one]
  have hinv : (ρU β ⟨m, hm⟩)⁻¹ = ρU β ⟨m, hm⟩ := inv_eq_of_mul_eq_one_right hu2
  rw [← coe_ρU, show (⟨m⁻¹, (Nor B).inv_mem hm⟩ : Nor B) = (⟨m, hm⟩)⁻¹ from Subtype.ext rfl,
    map_inv, hinv, coe_ρU, hA]

omit [Finite G] in
private theorem ρM_eq_of_cols
    {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {m : G} (hm : m ∈ Nor B) {A : Mat}
    (h : ∀ i, ρM β ⟨m, hm⟩ *ᵥ e i = A *ᵥ e i) : ρM β ⟨m, hm⟩ = A := by
  rw [← ofCols_cols (ρM β ⟨m, hm⟩), ← ofCols_cols A]
  congr 1
  funext i
  fin_cases i
  exacts [h 0, h 1, h 2, h 3]

private theorem cvG_basis {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) (i : Fin 4) :
    cvG β (((Additive.toMul (β i) : B) : G)) = e i := by
  rw [cvG_of_mem β (Additive.toMul (β i)).2]
  exact cv_basis β i

private theorem cvG_of_bs {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {bs : Fin 4 → G}
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = bs i) (i : Fin 4) : cvG β (bs i) = e i := by
  rw [← hβ i]
  exact cvG_basis β i

private theorem cvG_pow' {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {g : G} (hg : g ∈ B) (k : ℕ) :
    cvG β (g ^ k) = k • cvG β g := by
  induction k with
  | zero => rw [pow_zero, zero_smul, cvG_one]
  | succ k ih => rw [pow_succ, cvG_mul β (B.pow_mem hg k) hg, ih, succ_nsmul]

private theorem cvG_vecElt {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))
    (h0 : cvG β (zs z 0) = e 1) (h1 : cvG β (zs z 1) = e 2) (h2 : cvG β (zs z 2) = e 3)
    (hm0 : zs z 0 ∈ B) (hm1 : zs z 1 ∈ B) (hm2 : zs z 2 ∈ B) (w : Fin 3 → ZMod 3) :
    cvG β (vecElt (zs z) w) =
      (w 0).val • e 1 + (w 1).val • e 2 + (w 2).val • e 3 := by
  rw [vecElt, cvG_mul β (B.mul_mem (B.pow_mem hm0 _) (B.pow_mem hm1 _)) (B.pow_mem hm2 _),
    cvG_mul β (B.pow_mem hm0 _) (B.pow_mem hm1 _), cvG_pow' β hm0, cvG_pow' β hm1,
    cvG_pow' β hm2, h0, h1, h2]

private theorem mem_cenS_of_ρM_one {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {m : G} (hm : m ∈ Nor B)
    (h : ρM β ⟨m, hm⟩ = 1) : m ∈ CenS B := by
  have h1 : ρU β ⟨m, hm⟩ = 1 := by
    ext
    rw [coe_ρU, h, Units.val_one]
  have h2 : ⟨m, hm⟩ ∈ (ρU β).ker := by
    rw [MonoidHom.mem_ker]
    exact h1
  rw [ker_ρU] at h2
  exact Subgroup.mem_subgroupOf.mp h2

private theorem hbarM_mulVec_a : hbarM *ᵥ (e 1 + -e 2) = e 0 + (e 1 + e 2 + e 3) := by
  decide +kernel

private theorem hbarM_mulVec_z : hbarM *ᵥ (e 1 + e 2 + e 3) = e 1 + e 2 + e 3 := by
  decide +kernel

private theorem hbarM_mulVec_w :
    ∀ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 →
      hbarM *ᵥ ((w 0).val • e 1 + (w 1).val • e 2 + (w 2).val • e 3) =
        (w 1 - w 0).val • e 0 + (w 0).val • (e 1 + e 2 + e 3) := by
  decide +kernel

private theorem T0_mulVec : T0 *ᵥ e 1 = e 1 ∧ T0 *ᵥ e 2 = e 2 ∧ T0 *ᵥ e 3 = e 3 := by
  decide +kernel

private theorem Cyc_mulVec : Cyc *ᵥ e 0 = e 0 ∧ Cyc *ᵥ e 1 = e 2 ∧ Cyc *ᵥ e 2 = e 3 ∧
    Cyc *ᵥ e 3 = e 1 := by
  decide +kernel

private theorem rhoM_mulVec_a : rhoM *ᵥ e 0 = e 0 + 2 • (e 1 + e 2 + e 3) := by
  decide +kernel

private theorem rhoM_mulVec_z : rhoM *ᵥ (e 1 + e 2 + e 3) = e 1 + e 2 + e 3 := by
  decide +kernel

private theorem rhoM_mulVec_zs : ∀ i : Fin 3,
    rhoM *ᵥ e i.succ = e i.succ + -(e 0 + (e 1 + e 2 + e 3)) := by
  decide +kernel

private theorem T0_mul_self : T0 * T0 = 1 := by
  rw [← mm_eq]
  exact T0_sq

private theorem ρM_eq_T0
    {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {bs : Fin 4 → G}
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = bs i)
    (h0 : bs 0 = b) (h1 : bs 1 = zs z 0) (h2 : bs 2 = zs z 1) (h3 : bs 3 = zs z 2)
    (hbB : b ∈ B) {x : G} (hx : x ∈ Nor B) (hxb : x * b * x⁻¹ = b⁻¹)
    (hx0 : x * zs z 0 * x⁻¹ = zs z 0) (hx1 : x * zs z 1 * x⁻¹ = zs z 1)
    (hx2 : x * zs z 2 * x⁻¹ = zs z 2) : ρM β ⟨x, hx⟩ = T0 := by
  have hb : cvG β b = e 0 := by rw [← h0]; exact cvG_of_bs β hβ 0
  have hz0 : cvG β (zs z 0) = e 1 := by rw [← h1]; exact cvG_of_bs β hβ 1
  have hz1 : cvG β (zs z 1) = e 2 := by rw [← h2]; exact cvG_of_bs β hβ 2
  have hz2 : cvG β (zs z 2) = e 3 := by rw [← h3]; exact cvG_of_bs β hβ 3
  have hcol0 : ρM β ⟨x, hx⟩ *ᵥ e 0 = T0 *ᵥ e 0 := by
    rw [ρM_col, hβ 0, h0, hxb, cvG_inv β hbB, hb, T0_e0]
  have hcol1 : ρM β ⟨x, hx⟩ *ᵥ e 1 = T0 *ᵥ e 1 := by
    rw [ρM_col, hβ 1, h1, hx0, hz0, T0_mulVec.1]
  have hcol2 : ρM β ⟨x, hx⟩ *ᵥ e 2 = T0 *ᵥ e 2 := by
    rw [ρM_col, hβ 2, h2, hx1, hz1, T0_mulVec.2.1]
  have hcol3 : ρM β ⟨x, hx⟩ *ᵥ e 3 = T0 *ᵥ e 3 := by
    rw [ρM_col, hβ 3, h3, hx2, hz2, T0_mulVec.2.2]
  refine ρM_eq_of_cols β hx (fun i => ?_)
  fin_cases i
  exacts [hcol0, hcol1, hcol2, hcol3]

private theorem ρM_eq_Cyc
    {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {bs : Fin 4 → G}
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = bs i)
    (h0 : bs 0 = b) (h1 : bs 1 = zs z 0) (h2 : bs 2 = zs z 1) (h3 : bs 3 = zs z 2)
    {π : G} (hπ : π ∈ Nor B) (hπb : π * b * π⁻¹ = b)
    (hπ0 : π * zs z 0 * π⁻¹ = zs z 1) (hπ1 : π * zs z 1 * π⁻¹ = zs z 2)
    (hπ2 : π * zs z 2 * π⁻¹ = zs z 0) : ρM β ⟨π, hπ⟩ = Cyc := by
  have hb : cvG β b = e 0 := by rw [← h0]; exact cvG_of_bs β hβ 0
  have hz0 : cvG β (zs z 0) = e 1 := by rw [← h1]; exact cvG_of_bs β hβ 1
  have hz1 : cvG β (zs z 1) = e 2 := by rw [← h2]; exact cvG_of_bs β hβ 2
  have hz2 : cvG β (zs z 2) = e 3 := by rw [← h3]; exact cvG_of_bs β hβ 3
  have hcol0 : ρM β ⟨π, hπ⟩ *ᵥ e 0 = Cyc *ᵥ e 0 := by
    rw [ρM_col, hβ 0, h0, hπb, hb, Cyc_mulVec.1]
  have hcol1 : ρM β ⟨π, hπ⟩ *ᵥ e 1 = Cyc *ᵥ e 1 := by
    rw [ρM_col, hβ 1, h1, hπ0, hz1, Cyc_mulVec.2.1]
  have hcol2 : ρM β ⟨π, hπ⟩ *ᵥ e 2 = Cyc *ᵥ e 2 := by
    rw [ρM_col, hβ 2, h2, hπ1, hz2, Cyc_mulVec.2.2.1]
  have hcol3 : ρM β ⟨π, hπ⟩ *ᵥ e 3 = Cyc *ᵥ e 3 := by
    rw [ρM_col, hβ 3, h3, hπ2, hz0, Cyc_mulVec.2.2.2]
  refine ρM_eq_of_cols β hπ (fun i => ?_)
  fin_cases i
  exacts [hcol0, hcol1, hcol2, hcol3]

private theorem cfgOf_eq_mD (h : Setting b K z)
    [IsElementaryAbelian 3 (Bt b z)] (h1440 : autOrder (Bt b z) = 1440) :
    ∃ (β : Module.Basis (Fin 4) (ZMod 3) (Additive (Bt b z))),
      (∀ i, ((Additive.toMul (β i) : Bt b z) : G) = ![b, zs z 0, zs z 1, zs z 2] i) ∧
      Hyp (ρU β).range ∧ (cfgOf (ρU β).range).1 = mD := by
  have hH0 := h.hasH0
  obtain ⟨β, hβ⟩ := exists_basis (B := Bt b z) hH0.1.2 hH0.2.1
  have hyp := P51T.hyp_of hH0 h.stab h.meetB β hβ
  set Γ := (ρU β).range with hΓdef
  have haut : autOrder (Bt b z) = Nat.card Γ := autOrder_eq β
  have hcard := card_eq hyp
  have hOm : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m →
      Om Γ = ↑((nonzeroL.filter fun v => m (tab v).1).toFinset) := by
    intro m hm
    ext v
    rw [om_iff hyp, hm]
    simp
  have hautm : ∀ m : Fin 7 → Bool, (m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) →
      (cfgOf Γ).1 = m → autOrder (Bt b z) = 96 * lineCount m := by
    intro m hm hcm
    rw [haut, hcard, hOm m hcm, Set.ncard_coe_finset, vecCount m hm]
    ring
  have key : ∀ m : Fin 7 → Bool, (m = mA ∨ m = mB ∨ m = mC ∨ m = mE) →
      (cfgOf Γ).1 = m → False := by
    intro m hm hcm
    have h1 := hautm m (by rcases hm with h | h | h | h <;> simp [h]) hcm
    rw [h1] at h1440
    rcases hm with rfl | rfl | rfl | rfl
    · rw [lineCount_mA] at h1440; norm_num at h1440
    · rw [lineCount_mB] at h1440; norm_num at h1440
    · rw [lineCount_mC] at h1440; norm_num at h1440
    · rw [lineCount_mE] at h1440; norm_num at h1440
  have hD : (cfgOf Γ).1 = mD := by
    rcases cfgOf_good hyp with hA | ⟨hB, -⟩ | ⟨hC, -⟩ | hD | hE
    · exact (key mA (Or.inl rfl) hA).elim
    · exact (key mB (Or.inr (Or.inl rfl)) hB).elim
    · exact (key mC (Or.inr (Or.inr (Or.inl rfl))) hC).elim
    · exact hD
    · exact (key mE (Or.inr (Or.inr (Or.inr rfl))) hE).elim
  exact ⟨β, hβ, hyp, hD⟩

private theorem exists_n
    {B : Subgroup G} [IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))
    (hyp : Hyp (ρU β).range) (hD : (cfgOf (ρU β).range).1 = mD) :
    ∃ (n : G) (hn : n ∈ Nor B), ρM β ⟨n, hn⟩ = hbarM ∧
      ρM β ⟨n⁻¹, (Nor B).inv_mem hn⟩ = hbarM := by
  obtain ⟨g, hgΓ, hgM⟩ := mem_GM.1 (hbar_mem hyp hD)
  obtain ⟨m, rfl⟩ := hgΓ
  have hm : ρM β m = hbarM := by
    rw [← coe_ρU]
    exact hgM
  exact ⟨(m : G), m.2, by simpa using hm, ρM_inv β m.2 hm hbar_sq⟩

theorem exists_hbar (h : Setting b K z)
    (h1440 : autOrder (Bt b z) = 1440) :
    ∃ n ∈ Nor (Bt b z),
      n⁻¹ * (zs z 0 * (zs z 1)⁻¹) * n = b * zetaOf (zs z) ∧
      n⁻¹ * zetaOf (zs z) * n = zetaOf (zs z) ∧
      (∀ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 → ∀ c : G, c * b = b * c →
        c * zetaOf (zs z) = zetaOf (zs z) * c →
        c * (n⁻¹ * vecElt (zs z) w * n) = n⁻¹ * vecElt (zs z) w * n * c) ∧
      (∀ x ∈ Nor (Bt b z), x * b * x⁻¹ = b⁻¹ → (∀ i, x * zs z i * x⁻¹ = zs z i) →
        n * x * n⁻¹ * b * (n * x * n⁻¹)⁻¹ = b ∧
        n * x * n⁻¹ * zs z 0 * (n * x * n⁻¹)⁻¹ = zs z 0 ∧
        n * x * n⁻¹ * zs z 1 * (n * x * n⁻¹)⁻¹ = zs z 2 ∧
        n * x * n⁻¹ * zs z 2 * (n * x * n⁻¹)⁻¹ = zs z 1) ∧
      ∀ π ∈ Nor (Bt b z), π * b * π⁻¹ = b → (∀ i, π * zs z i * π⁻¹ = zs z (finRotate 3 i)) →
        n⁻¹ * π * n * b * (n⁻¹ * π * n)⁻¹ = b * zetaOf (zs z) ^ 2 ∧
        n⁻¹ * π * n * zetaOf (zs z) * (n⁻¹ * π * n)⁻¹ = zetaOf (zs z) ∧
        (∀ i, n⁻¹ * π * n * zs z i * (n⁻¹ * π * n)⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹) ∧
        ∀ x ∈ Nor (Bt b z), x * b * x⁻¹ = b⁻¹ → (∀ i, x * zs z i * x⁻¹ = zs z i) →
          x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n) ∈ CenS (Bt b z) := by
  classical
  have hEA : IsElementaryAbelian 3 (Bt b z) := h.hasH0.1.1
  obtain ⟨β, hβ, hyp, hD⟩ := cfgOf_eq_mD h h1440
  obtain ⟨n, hn, hnM, hnMinv⟩ := exists_n β hyp hD
  have hb : cvG β b = e 0 := cvG_of_bs β hβ 0
  have hz0 : cvG β (zs z 0) = e 1 := cvG_of_bs β hβ 1
  have hz1 : cvG β (zs z 1) = e 2 := cvG_of_bs β hβ 2
  have hz2 : cvG β (zs z 2) = e 3 := cvG_of_bs β hβ 3
  have hbB : b ∈ Bt b z := b_mem_Bt b z
  have hz0B : zs z 0 ∈ Bt b z := zs_mem_Bt b z 0
  have hz1B : zs z 1 ∈ Bt b z := zs_mem_Bt b z 1
  have hz2B : zs z 2 ∈ Bt b z := zs_mem_Bt b z 2
  have hζB : zetaOf (zs z) ∈ Bt b z := by
    rw [show zetaOf (zs z) = zs z 0 * zs z 1 * zs z 2 from rfl]
    exact (Bt b z).mul_mem ((Bt b z).mul_mem hz0B hz1B) hz2B
  have hζcv : cvG β (zetaOf (zs z)) = e 1 + e 2 + e 3 := by
    rw [show zetaOf (zs z) = zs z 0 * zs z 1 * zs z 2 from rfl,
      cvG_mul β ((Bt b z).mul_mem hz0B hz1B) hz2B, cvG_mul β hz0B hz1B, hz0, hz1, hz2]
  have hζ2 : cvG β (zetaOf (zs z) ^ 2) = 2 • (e 1 + e 2 + e 3) := by
    rw [pow_two, cvG_mul β hζB hζB, hζcv, two_nsmul]
  have hnin : n⁻¹ ∈ Nor (Bt b z) := (Nor (Bt b z)).inv_mem hn
  have hzs : ∀ i : Fin 3, cvG β (zs z i) = e i.succ := by
    intro i
    fin_cases i
    exacts [hz0, hz1, hz2]
  refine ⟨n, hn, ?_, ?_, ?_, ?_, ?_⟩
  · refine conj_eq_of_cv_inv β hn ((Bt b z).mul_mem hz0B ((Bt b z).inv_mem hz1B))
      ((Bt b z).mul_mem hbB hζB) ?_
    rw [hnMinv, cvG_mul β hz0B ((Bt b z).inv_mem hz1B), hz0, cvG_inv β hz1B, hz1,
      hbarM_mulVec_a, cvG_mul β hbB hζB, hb, hζcv]
  · refine conj_eq_of_cv_inv β hn hζB hζB ?_
    rw [hnMinv, hζcv, hbarM_mulVec_z]
  · intro w hw c hcb hcz
    have hvec : cvG β (vecElt (zs z) w) =
        (w 0).val • e 1 + (w 1).val • e 2 + (w 2).val • e 3 :=
      cvG_vecElt β hz0 hz1 hz2 hz0B hz1B hz2B w
    have hweB : vecElt (zs z) w ∈ Bt b z := tor_le_Bt b z (vecElt_mem_tor (zs z) w)
    have hwe : n⁻¹ * vecElt (zs z) w * n =
        b ^ (w 1 - w 0).val * zetaOf (zs z) ^ (w 0).val := by
      refine conj_eq_of_cv_inv β hn hweB
        ((Bt b z).mul_mem ((Bt b z).pow_mem hbB _) ((Bt b z).pow_mem hζB _)) ?_
      rw [hnMinv, hvec, hbarM_mulVec_w w hw,
        cvG_mul β ((Bt b z).pow_mem hbB _) ((Bt b z).pow_mem hζB _),
        cvG_pow' β hbB, cvG_pow' β hζB, hb, hζcv]
    rw [hwe]
    exact ((show Commute c b from hcb).pow_right _).mul_right
      ((show Commute c (zetaOf (zs z)) from hcz).pow_right _) |>.eq
  · intro x hx hxb hxz
    have hxT0 : ρM β ⟨x, hx⟩ = T0 :=
      ρM_eq_T0 β hβ rfl rfl rfl rfl hbB hx hxb (hxz 0) (hxz 1) (hxz 2)
    have hxinvT0 : ρM β ⟨x⁻¹, (Nor (Bt b z)).inv_mem hx⟩ = T0 :=
      ρM_inv β hx hxT0 T0_mul_self
    have hy : n * x * n⁻¹ ∈ Nor (Bt b z) :=
      (Nor (Bt b z)).mul_mem ((Nor (Bt b z)).mul_mem hn hx) hnin
    have hyM : ρM β ⟨n * x * n⁻¹, hy⟩ = Swap23 := by
      rw [ρM_mul3 β hn hx hnin, hnM, hxT0, hnMinv, hbar_T0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine conj_eq_of_cv β hy hbB hbB ?_
      rw [hyM, hb, swap23_cols.1]
    · refine conj_eq_of_cv β hy hz0B hz0B ?_
      rw [hyM, hz0, swap23_cols.2.1]
    · refine conj_eq_of_cv β hy hz1B hz2B ?_
      rw [hyM, hz1, swap23_cols.2.2.1, hz2]
    · refine conj_eq_of_cv β hy hz2B hz1B ?_
      rw [hyM, hz2, swap23_cols.2.2.2, hz1]
  · intro π hπ hπb hπz
    have hπCyc : ρM β ⟨π, hπ⟩ = Cyc :=
      ρM_eq_Cyc β hβ rfl rfl rfl rfl hπ hπb (by simpa using hπz 0) (by simpa using hπz 1)
        (by simpa using hπz 2)
    have hr2 : n⁻¹ * π * n ∈ Nor (Bt b z) :=
      (Nor (Bt b z)).mul_mem ((Nor (Bt b z)).mul_mem hnin hπ) hn
    have hr2M : ρM β ⟨n⁻¹ * π * n, hr2⟩ = rhoM := by
      rw [ρM_mul3 β hnin hπ hn, hnMinv, hπCyc, hnM, hbar_Cyc]
    have hbζB : b * zetaOf (zs z) ∈ Bt b z := (Bt b z).mul_mem hbB hζB
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine conj_eq_of_cv β hr2 hbB ((Bt b z).mul_mem hbB ((Bt b z).pow_mem hζB 2)) ?_
      rw [hr2M, hb, rhoM_mulVec_a, cvG_mul β hbB ((Bt b z).pow_mem hζB 2), hb, hζ2]
    · refine conj_eq_of_cv β hr2 hζB hζB ?_
      rw [hr2M, hζcv, rhoM_mulVec_z]
    · intro i
      have hzsiB : zs z i ∈ Bt b z := zs_mem_Bt b z i
      refine conj_eq_of_cv β hr2 hzsiB
        ((Bt b z).mul_mem hzsiB ((Bt b z).inv_mem hbζB)) ?_
      rw [hr2M, hzs i, rhoM_mulVec_zs i,
        cvG_mul β hzsiB ((Bt b z).inv_mem hbζB), hzs i, cvG_inv β hbζB,
        cvG_mul β hbB hζB, hb, hζcv]
    · intro x hx hxb hxz
      have hxT0 : ρM β ⟨x, hx⟩ = T0 :=
        ρM_eq_T0 β hβ rfl rfl rfl rfl hbB hx hxb (hxz 0) (hxz 1) (hxz 2)
      have hxinvT0 : ρM β ⟨x⁻¹, (Nor (Bt b z)).inv_mem hx⟩ = T0 :=
        ρM_inv β hx hxT0 T0_mul_self
      have hm : x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n) ∈ Nor (Bt b z) :=
        (Nor (Bt b z)).mul_mem
          ((Nor (Bt b z)).mul_mem ((Nor (Bt b z)).mul_mem hx hr2) ((Nor (Bt b z)).inv_mem hx))
          hr2
      refine mem_cenS_of_ρM_one β hm ?_
      rw [ρM_mul4 β hx hr2 ((Nor (Bt b z)).inv_mem hx) hr2, hxT0, hr2M, hxinvT0, T0_rho]

theorem exists_e23 (h : Setting b K z)
    (h1440 : autOrder (Bt b z) = 1440) :
    ∃ g ∈ Nor (Bt b z), g * b * g⁻¹ = zs z 1 * zs z 2 ∧
      ∀ x ∈ Nor (Bt b z), x * b * x⁻¹ = b⁻¹ → (∀ i, x * zs z i * x⁻¹ = zs z i) →
        g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ = b := by
  classical
  have hEA : IsElementaryAbelian 3 (Bt b z) := h.hasH0.1.1
  obtain ⟨β, hβ, hyp, hD⟩ := cfgOf_eq_mD h h1440
  have hb : cvG β b = e 0 := cvG_of_bs β hβ 0
  have hz0 : cvG β (zs z 0) = e 1 := cvG_of_bs β hβ 1
  have hz1 : cvG β (zs z 1) = e 2 := cvG_of_bs β hβ 2
  have hz2 : cvG β (zs z 2) = e 3 := cvG_of_bs β hβ 3
  have hbB : b ∈ Bt b z := b_mem_Bt b z
  have hz0B : zs z 0 ∈ Bt b z := zs_mem_Bt b z 0
  have hz1B : zs z 1 ∈ Bt b z := zs_mem_Bt b z 1
  have hz2B : zs z 2 ∈ Bt b z := zs_mem_Bt b z 2
  obtain ⟨γ, hγΓ, hγe0, hγψ⟩ := real_e23 hyp hD
  obtain ⟨m, rfl⟩ := hγΓ
  have hmM : ρM β m = ((ρU β m : GL4) : Mat) := (coe_ρU β m).symm
  have hminv : ρM β ⟨(↑m : G)⁻¹, (Nor (Bt b z)).inv_mem m.2⟩ =
      (((ρU β m)⁻¹ : GL4) : Mat) := by
    rw [← coe_ρU, show (⟨(↑m : G)⁻¹, (Nor (Bt b z)).inv_mem m.2⟩ : Nor (Bt b z)) = m⁻¹ from
      Subtype.ext rfl, map_inv]
  have hgb : (↑m : G) * b * (↑m)⁻¹ = zs z 1 * zs z 2 := by
    refine conj_eq_of_cv β m.2 hbB ((Bt b z).mul_mem hz1B hz2B) ?_
    rw [hb, hmM, hγe0, cvG_mul β hz1B hz2B, hz1, hz2]
  refine ⟨(↑m : G), m.2, hgb, ?_⟩
  intro x hx hxb hxz
  have hxT0 : ρM β ⟨x, hx⟩ = T0 :=
    ρM_eq_T0 β hβ rfl rfl rfl rfl hbB hx hxb (hxz 0) (hxz 1) (hxz 2)
  have hxinvT0 : ρM β ⟨x⁻¹, (Nor (Bt b z)).inv_mem hx⟩ = T0 :=
    ρM_inv β hx hxT0 T0_mul_self
  have hy : (↑m : G) * x * (↑m)⁻¹ ∈ Nor (Bt b z) :=
    (Nor (Bt b z)).mul_mem ((Nor (Bt b z)).mul_mem m.2 hx) ((Nor (Bt b z)).inv_mem m.2)
  have hyM : ρM β ⟨(↑m : G) * x * (↑m)⁻¹, hy⟩ =
      1 + vecMulVec (e 2 + e 3) ![0, 0, 2, 2] := by
    rw [ρM_mul3 β m.2 hx ((Nor (Bt b z)).inv_mem m.2), hmM, hxT0, hminv, conj_T0, hγe0, hγψ]
  refine conj_eq_of_cv β hy hbB hbB ?_
  rw [hyM, hb, refl_e23_cols.1]

end CFSG.StandardType.GGFF.Setting

end
