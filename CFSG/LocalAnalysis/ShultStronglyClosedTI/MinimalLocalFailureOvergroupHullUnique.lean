module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHullKernel

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OvergroupHull

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.FixedPointModel
open scoped MatrixGroups commutatorElement

section Group

variable {L : Type*} [Group L]

theorem commutatorElement_mul_center_left {a b c : L} (hc : c ∈ Subgroup.center L) :
    ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have hcb : c * b = b * c := ((Subgroup.mem_center_iff.mp hc) b).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
    show a * c * b * (c⁻¹ * a⁻¹) * b⁻¹ = a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ by group, hcb]
  group

theorem commutatorElement_mul_center_right {a b c : L} (hc : c ∈ Subgroup.center L) :
    ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have hca : c * a⁻¹ = a⁻¹ * c := ((Subgroup.mem_center_iff.mp hc) a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
    show a * (b * c) * a⁻¹ * (c⁻¹ * b⁻¹) = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ by group, hca]
  group

theorem eq_top_of_map_mk_eq_top [Group.IsPerfect L] {R : Subgroup L} [R.Normal]
    (hR : R ≤ Subgroup.center L) {W : Subgroup L} (hW : W.map (QuotientGroup.mk' R) = ⊤) :
    W = ⊤ := by
  have hlift : ∀ l : L, ∃ w ∈ W, ∃ c ∈ Subgroup.center L, l = w * c := by
    intro l
    have hl : QuotientGroup.mk' R l ∈ W.map (QuotientGroup.mk' R) := hW ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwl⟩ := hl
    refine ⟨w, hw, w⁻¹ * l, hR ?_, by group⟩
    exact QuotientGroup.eq.mp hwl
  have hcomm : commutator L ≤ W := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    obtain ⟨w₁, hw₁, c₁, hc₁, rfl⟩ := hlift a
    obtain ⟨w₂, hw₂, c₂, hc₂, rfl⟩ := hlift b
    rw [commutatorElement_mul_center_left hc₁, commutatorElement_mul_center_right hc₂,
      commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)) (W.inv_mem hw₂)
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := L)]
  exact hcomm

theorem normal_le_ker_of_odd {P : Type*} [Group P] [IsSimpleGroup P] (ρ : L →* P)
    (hρ : Function.Surjective ρ) {w : P} (hw : orderOf w = 2) (N : Subgroup L) [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ ρ.ker := by
  have : (N.map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ρ) with hbot | htop
  · exact (Subgroup.map_eq_bot_iff _).mp hbot
  · exfalso
    have hwN : w ∈ N.map ρ := htop ▸ Subgroup.mem_top w
    obtain ⟨n, hn, rfl⟩ := hwN
    have h1 : orderOf (ρ n) ∣ orderOf n := orderOf_map_dvd ρ n
    have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    rw [hw] at h1
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (h1.trans h2))

variable [Finite L]

theorem card_le_card_map_mk {P : Type*} [Group P] [Finite P] [IsSimpleGroup P]
    {R : Subgroup L} [R.Normal] (hR : Odd (Nat.card R)) (W : Subgroup L) (ρ : W →* P)
    (hρ : Function.Surjective ρ) {w : P} (hw : orderOf w = 2) :
    Nat.card P ≤ Nat.card (W.map (QuotientGroup.mk' R)) := by
  let N : Subgroup W := R.subgroupOf W
  have hNodd : Odd (Nat.card N) := by
    have hcard : Nat.card N = Nat.card (R ⊓ W : Subgroup L) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective W.subtype_injective]
    rw [hcard]
    exact Odd.of_dvd_nat hR (Subgroup.card_dvd_of_le inf_le_left)
  have hNker : N ≤ ρ.ker := normal_le_ker_of_odd ρ hρ hw N hNodd
  let φ : W →* L ⧸ R := (QuotientGroup.mk' R).comp W.subtype
  have hφker : φ.ker = N := by
    ext x
    simp [φ, N, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = W.map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card N * Nat.card (W.map (QuotientGroup.mk' R)) = Nat.card W := by
    rw [← hφrange, ← Subgroup.index_ker, hφker, Subgroup.card_mul_index]
  have h2 : Nat.card ρ.ker * Nat.card P = Nat.card W := by
    rw [← Subgroup.card_top (G := P), ← MonoidHom.range_eq_top.mpr hρ, ← Subgroup.index_ker,
      Subgroup.card_mul_index]
  have h3 : Nat.card N * Nat.card P ≤ Nat.card ρ.ker * Nat.card P :=
    Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hNker)
  exact Nat.le_of_mul_le_mul_left (h3.trans (h2.trans h1.symm).le) Nat.card_pos

end Group

theorem card_psl2_le (F : Type*) [Field F] [Finite F] :
    Nat.card PSL(2, F) ≤ Nat.card F ^ 4 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h1 : Nat.card PSL(2, F) ≤ Nat.card SL(2, F) :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have h2 : Nat.card SL(2, F) ≤ Nat.card (Matrix (Fin 2) (Fin 2) F) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h3 : Nat.card (Matrix (Fin 2) (Fin 2) F) = Nat.card F ^ 4 := by
    change Nat.card (Fin 2 → Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]
  omega

theorem lt_unitary_order {q n : ℕ} (hq : 4 ≤ q) (hn : n ≤ q ^ 5 + q ^ 4) :
    n < (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q + 1))
  have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h16 : 16 ≤ q ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 = m + 16 := ⟨q ^ 2 - 16, by omega⟩
  have hsub : q ^ 2 - 1 = m + 15 := by omega
  have hq5 : q ^ 5 * 4 ≤ q ^ 6 := by
    rw [show q ^ 6 = q ^ 5 * q by ring]
    exact Nat.mul_le_mul_left _ hq
  have hq4 : q ^ 4 * 4 ≤ q ^ 5 := by
    rw [show q ^ 5 = q ^ 4 * q by ring]
    exact Nat.mul_le_mul_left _ hq
  have hq1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  calc n < (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / 3 := by
        rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by norm_num), hsub]
        have h6 : q ^ 6 * (m + 15) ≤ (q ^ 3 + 1) * q ^ 3 * (m + 15) := by
          apply Nat.mul_le_mul_right
          nlinarith
        nlinarith
    _ ≤ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := Nat.div_le_div_left hg hgpos

variable {L : Type*} [Group L]

theorem model_unitary_of_le_card {M : Subgroup L} {q i : ℕ}
    (h : IsModelCosetAction L M q i)
    (hle : (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ≤
      Nat.card (L ⧸ CFSG.oddCore L)) :
    i = 3 ∧ Nat.card (L ⧸ CFSG.oddCore L) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  rcases h with ⟨rfl, f, hf, hq, e, -⟩ | ⟨rfl, a, ha, hq, -, K, _, _, hK, e, -⟩ |
    ⟨rfl, f, hf, hq, -, k, _, _, J, hJ, hk, hfix, e, -⟩
  · exfalso
    have hq4 : 4 ≤ q := hq ▸ (show 2 ^ 2 ≤ 2 ^ f from Nat.pow_le_pow_right (by norm_num) hf)
    have hcard : Nat.card (L ⧸ CFSG.oddCore L) ≤ q ^ 4 := by
      rw [Nat.card_congr e.toEquiv, hq, ← GaloisField.card 2 f (by omega)]
      exact card_psl2_le _
    have hlt := lt_unitary_order hq4 (n := Nat.card (L ⧸ CFSG.oddCore L))
      (hcard.trans (Nat.le_add_left _ _))
    omega
  · exfalso
    have hq8 : 4 ≤ q := hq ▸ (show 2 ^ 2 ≤ 2 ^ (2 * a + 1) from
      Nat.pow_le_pow_right (by norm_num) (by omega))
    have hcard : Nat.card (L ⧸ CFSG.oddCore L) = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK, hq]
    have hbound : q ^ 2 * (q - 1) * (q ^ 2 + 1) ≤ q ^ 5 + q ^ 4 := by
      have hq1 : q - 1 ≤ q := Nat.sub_le q 1
      calc q ^ 2 * (q - 1) * (q ^ 2 + 1) ≤ q ^ 2 * q * (q ^ 2 + 1) := by
            apply Nat.mul_le_mul_right
            exact Nat.mul_le_mul_left _ hq1
        _ = q ^ 5 + q ^ 3 := by ring
        _ ≤ q ^ 5 + q ^ 4 := Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _
    have hlt := lt_unitary_order hq8 (hcard ▸ hbound)
    omega
  · refine ⟨rfl, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨-, -, -, -, -, -, -, -, hG, -⟩ :=
      CFSG.BenderSuzuki.External.huppert_II_10_12 J q hk hfix hJ
    exact hG

variable [Finite L]

theorem eq_top_of_unitary_scalar_quotient [Group.IsPerfect L]
    (hZ : CFSG.oddCore L ≤ Subgroup.center L) {M : Subgroup L} {q i : ℕ}
    (hmodel : IsModelCosetAction L M q i)
    {k₀ : Type} [Field k₀] [Finite k₀] {J₀ : HermitianForm 3 k₀}
    (hJ₀ : J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hk₀ : Nat.card k₀ = q ^ 2)
    (hfix₀ : Nat.card {x : k₀ // J₀.conj x = x} = q)
    {C₀ : Subgroup J₀.specialSubgroup} [C₀.Normal]
    (hC₀ : C₀ ≤ (PerfectOddCover.unitaryProj J₀).ker)
    {W : Subgroup L} (e₀ : J₀.specialSubgroup ⧸ C₀ ≃* W) : W = ⊤ ∧ i = 3 := by
  obtain ⟨f, hf, hq⟩ := model_parameter_two_pow hmodel
  have hq4 : 4 ≤ q := hq ▸ (show 2 ^ 2 ≤ 2 ^ f from Nat.pow_le_pow_right (by norm_num) hf)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) k₀) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J₀ =>
      (x : Matrix.ProjGenLinGroup (Fin 3) k₀)) Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    CFSG.BenderSuzuki.External.huppert_II_10_13 J₀ q (by omega) hk₀ hfix₀
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨w, hw, -⟩, -⟩ := UnitaryModel.unitary_three_point_structure J₀ f hf (hq ▸ hk₀)
      (hq ▸ hfix₀) hJ₀
  let ρ : W →* ProjectiveSpecialUnitaryMatrixGroup J₀ :=
    (QuotientGroup.lift C₀ (PerfectOddCover.unitaryProj J₀) hC₀).comp e₀.symm.toMonoidHom
  have hρ : Function.Surjective ρ := by
    intro p
    obtain ⟨A, rfl⟩ := PerfectOddCover.unitaryProj_surjective J₀ p
    refine ⟨e₀ (QuotientGroup.mk A), ?_⟩
    simp [ρ]
  have hle : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J₀) ≤
      Nat.card (W.map (QuotientGroup.mk' (CFSG.oddCore L))) :=
    card_le_card_map_mk (CFSG.ComponentClassification.OddCore.odd_card L) W ρ hρ hw
  have hPcard : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J₀) =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
    obtain ⟨-, -, -, -, -, -, -, -, hG, -⟩ :=
      CFSG.BenderSuzuki.External.huppert_II_10_12 J₀ q hk₀ hfix₀ hJ₀
    exact hG
  have hWL : Nat.card (W.map (QuotientGroup.mk' (CFSG.oddCore L))) ≤
      Nat.card (L ⧸ CFSG.oddCore L) := Subgroup.card_le_card_group _
  obtain ⟨hi, hcard⟩ := model_unitary_of_le_card hmodel (hPcard ▸ hle.trans hWL)
  have htop : W.map (QuotientGroup.mk' (CFSG.oddCore L)) = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    refine le_antisymm hWL ?_
    rw [hcard, ← hPcard]
    exact hle
  exact ⟨eq_top_of_map_mk_eq_top hZ htop, hi⟩

@[expose] def IsUnitaryScalarQuotient (q : ℕ) (V : Type*) [Group V] : Prop :=
  ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀) (J₀ : HermitianForm 3 k₀)
    (_ : J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
    Nat.card k₀ = q ^ 2 ∧ Nat.card {x : k₀ // J₀.conj x = x} = q ∧
    ∃ (C₀ : Subgroup J₀.specialSubgroup) (_ : C₀.Normal),
      (∀ A ∈ C₀, ∃ c : k₀, ((A : GL (Fin 3) k₀) : Matrix (Fin 3) (Fin 3) k₀) =
        Matrix.scalar (Fin 3) c ∧ c ^ (q + 1) = 1 ∧ c ^ 3 = 1) ∧
      Nonempty (J₀.specialSubgroup ⧸ C₀ ≃* V)

omit [Finite L] in
theorem IsUnitaryScalarQuotient.of_mulEquiv {q : ℕ} {V : Type*} [Group V]
    (h : IsUnitaryScalarQuotient q V) (e : V ≃* L) : IsUnitaryScalarQuotient q L := by
  obtain ⟨k₀, _, _, J₀, hJ₀, hk₀, hfix₀, C₀, _, hC₀, ⟨e₀⟩⟩ := h
  exact ⟨k₀, inferInstance, inferInstance, J₀, hJ₀, hk₀, hfix₀, C₀, inferInstance, hC₀,
    ⟨e₀.trans e⟩⟩

theorem eq_top_of_isUnitaryScalarQuotient [Group.IsPerfect L]
    (hZ : CFSG.oddCore L ≤ Subgroup.center L) {M : Subgroup L} {q i : ℕ}
    (hmodel : IsModelCosetAction L M q i) {W : Subgroup L} (hW : IsUnitaryScalarQuotient q W) :
    W = ⊤ ∧ i = 3 := by
  obtain ⟨k₀, _, _, J₀, hJ₀, hk₀, hfix₀, C₀, _, hC₀, ⟨e₀⟩⟩ := hW
  have hconj := CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J₀ q hk₀ hfix₀
  have hC₀' : C₀ ≤ (PerfectOddCover.unitaryProj J₀).ker := by
    intro A hA
    obtain ⟨c, hc, hc1, hc3⟩ := hC₀ A hA
    rw [PerfectOddCover.mem_ker_unitaryProj_iff J₀ hJ₀]
    refine ⟨c, hc, ?_, hc3⟩
    rw [hconj c, ← pow_succ']
    exact hc1
  exact eq_top_of_unitary_scalar_quotient hZ hmodel hJ₀ hk₀ hfix₀ hC₀' e₀

end CFSG.ShultStronglyClosedTI.OvergroupHull
