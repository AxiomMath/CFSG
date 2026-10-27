module

public import CFSG.Quasithin.Vol2.Ch10SecDXI2
public import CFSG.Quasithin.Vol2.Ch10SecDFactX

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_normalizer_V12_of_mem_Xz (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥)
    {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) {y : G} (hy : y ∈ Xz T L (v₁ * v₂)) :
    y ∈ Subgroup.normalizer (fsuUL T L I : Set G) ∧ y * v₁ = v₁ * y ∧
      y ∈ Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) ∧
      y * v₂ = v₂ * y := by
  have hy' := oTwoUpper_le _ hy
  have hE := fsuL0_inf_centralizer_z_le h37 h38 h hc hd hy'
  obtain ⟨ht, htn, -, -, -, -⟩ := hd
  obtain ⟨hN1, hN2⟩ := fsuL0_le_normalizer_V12 h37 h38 h ht htn
  refine ⟨hN1 hy'.1, ((Subgroup.mem_centralizer_iff.mp hE) v₁
    (Subgroup.subset_closure (Set.mem_insert _ _))).symm, hN2 hy'.1,
    ((Subgroup.mem_centralizer_iff.mp hE) v₂
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))).symm⟩

omit [Finite G] in
theorem pow_mul_comm {x v : G} (hxv : x * v = v * x) (n : ℕ) : x ^ n * v = v * x ^ n :=
  ((Commute.pow_left (show Commute x v from hxv) n)).eq

theorem exists_pow_mul_mem_kOf
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {x : G} (hxX : x ∈ Xz T L (v₁ * v₂))
    (hxo : Odd (orderOf x)) (hxC : x ∉ Subgroup.centralizer (fsuUL T L I : Set G)) {y : G}
    (hy : y ∈ Xz T L (v₁ * v₂)) : ∃ i : ℕ, x ^ i * y ∈ kOf (fsuUL T L I) v₁ := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hv1 : v₁ ∈ fsuUL T L I := hd.2.2.1.1
  have hv11 : v₁ ≠ 1 := hd.2.2.2.1
  have hrho : ∀ g (hg : g ∈ Subgroup.normalizer (fsuUL T L I : Set G)),
      ∃ γ, D.rho γ = conjAct (fsuUL T L I) ⟨g, hg⟩ := fun g hg =>
    D.exists_rho (by rw [autOn_L_V1_eq_top h3 hc]; trivial)
  have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_mem h37 h38 h h3 hc hd (oTwoUpper_le _ hxX) hxo
  obtain ⟨hxN, hxv, -, -⟩ := mem_normalizer_V12_of_mem_Xz h37 h38 h hc hd hxX
  obtain ⟨δ, hδ⟩ := hrho x hxN
  have hc0 : coord D ⟨v₁, hv1⟩ ≠ 0 := fun h0 =>
    hv11 (congrArg Subtype.val (coord_injective D (h0.trans (coord_one D).symm)))
  refine Subgroup.closure_induction (p := fun y _ => ∃ i : ℕ, x ^ i * y ∈ kOf (fsuUL T L I) v₁)
    (fun g hg => ?_) ⟨0, by simp⟩ (fun a b ha hb iha ihb => ?_)
    (fun a ha iha => ?_) hy
  ·
    obtain ⟨hg, hgo⟩ := hg
    obtain ⟨hgN, hgv, -, -⟩ :=
      mem_normalizer_V12_of_mem_Xz h37 h38 h hc hd (mem_oTwoUpper_of_odd hg hgo)
    obtain ⟨γ, hγ⟩ := hrho g hgN
    obtain ⟨i, hi⟩ := L3.exists_pow_mul_mem_AS _ hc0 δ (act_coord_of_rho D hxN hv1 hxv hδ)
      (pow_eq_one_of_rho D hxN hδ hx3) (ne_one_of_rho D hxN hδ hxC) γ
      (act_coord_of_rho D hgN hv1 hgv hγ)
      (pow_eq_one_of_rho D hgN hγ (pow_three_eq_one_of_mem h37 h38 h h3 hc hd hg hgo))
    refine ⟨i, mem_kOf_of_rho D (Subgroup.mul_mem _ (Subgroup.pow_mem _ hxN _) hgN) hv1 ?_
      (rho_mul_of D _ hgN (rho_pow_of D hxN hδ i) hγ) hi⟩
    rw [mul_assoc, hgv, ← mul_assoc, pow_mul_comm hxv, mul_assoc]
  ·
    obtain ⟨i, hi⟩ := iha
    obtain ⟨j, hj⟩ := ihb
    refine ⟨i + j, ?_⟩
    have e : x ^ (i + j) * (a * b) = (x ^ j * (x ^ i * a) * (x ^ j)⁻¹) * (x ^ j * b) := by
      rw [pow_add]
      group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_kOf (Subgroup.pow_mem _ hxN j) (pow_mul_comm hxv j) hi) hj
  ·
    obtain ⟨i, hi⟩ := iha
    refine ⟨2 * i, ?_⟩
    have hx2 : x ^ (2 * i) = (x ^ i)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, show 2 * i + i = 3 * i by ring, pow_mul, hx3,
        one_pow]
    have e : x ^ (2 * i) * a⁻¹ = (x ^ i)⁻¹ * (x ^ i * a)⁻¹ * ((x ^ i)⁻¹)⁻¹ := by
      rw [hx2]
      group
    rw [e]
    have hv' : (x ^ i)⁻¹ * v₁ = v₁ * (x ^ i)⁻¹ := by
      calc (x ^ i)⁻¹ * v₁ = (x ^ i)⁻¹ * (v₁ * x ^ i) * (x ^ i)⁻¹ := by group
        _ = v₁ * (x ^ i)⁻¹ := by rw [← pow_mul_comm hxv i]; group
    exact conj_mem_kOf (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxN i)) hv'
      (Subgroup.inv_mem _ hi)

end CFSG.Quasithin.Vol2.Ch10.SecD
