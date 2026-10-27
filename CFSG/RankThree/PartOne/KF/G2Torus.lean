module

public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

variable {K : Type} [Field K]

theorem cartan_g2_sum (i : Fin Tag.G2.rank) (v : Fin Tag.G2.rank → ℤ) :
    ∑ x, Tag.G2.cartan i x * v x =
      Tag.G2.cartan i g2ia * v g2ia + Tag.G2.cartan i g2ir * v g2ir :=
  Fin.sum_univ_two (fun x => Tag.G2.cartan i x * v x)

theorem reflect_ia_apply (v : Fin Tag.G2.rank → ℤ) :
    reflect .G2 g2ia v g2ia = -v g2ia + v g2ir ∧ reflect .G2 g2ia v g2ir = v g2ir := by
  have h0 : g2ia ≠ g2ir := by decide
  have e1 : Tag.G2.cartan g2ia g2ia = 2 := by decide
  have e2 : Tag.G2.cartan g2ia g2ir = -1 := by decide
  simp [reflect, h0.symm, cartan_g2_sum, e1, e2]
  ring

theorem reflect_ir_apply (v : Fin Tag.G2.rank → ℤ) :
    reflect .G2 g2ir v g2ia = v g2ia ∧ reflect .G2 g2ir v g2ir = 3 * v g2ia - v g2ir := by
  have h0 : g2ia ≠ g2ir := by decide
  have e1 : Tag.G2.cartan g2ir g2ia = -3 := by decide
  have e2 : Tag.G2.cartan g2ir g2ir = 2 := by decide
  simp [reflect, h0, cartan_g2_sum, e1, e2]
  ring

theorem rootChar_g2 (c : Fin Tag.G2.rank → Kˣ) (v : Fin Tag.G2.rank → ℤ) :
    rootChar c v = c g2ia ^ v g2ia * c g2ir ^ v g2ir :=
  Fin.prod_univ_two (fun i => c i ^ v i)

theorem zpow_calc1 {G : Type*} [CommGroup G] (x y : G) (m n : ℤ) :
    x⁻¹ ^ (-m + n) * (y * x) ^ n = x ^ m * y ^ n := by
  rw [inv_zpow', mul_zpow, mul_comm (y ^ n) (x ^ n), ← mul_assoc, ← zpow_add,
    show -(-m + n) + n = m by ring]

theorem zpow_calc2 {G : Type*} [CommGroup G] (x y : G) (m n : ℤ) :
    (x * y ^ 3) ^ m * y⁻¹ ^ (3 * m - n) = x ^ m * y ^ n := by
  rw [inv_zpow', mul_zpow, ← zpow_natCast y 3, ← zpow_mul, mul_assoc, ← zpow_add,
    show (↑(3 : ℕ) : ℤ) * m + -(3 * m - n) = n by push_cast; ring]

@[expose] def g2Tuple (x y : Kˣ) : Fin Tag.G2.rank → Kˣ := fun j => if j = g2ia then x else y

theorem g2Tuple_ia (x y : Kˣ) : g2Tuple x y g2ia = x := by simp [g2Tuple]

theorem g2Tuple_ir (x y : Kˣ) : g2Tuple x y g2ir = y := by
  have h0 : g2ir ≠ g2ia := by decide
  simp [g2Tuple, h0]

theorem weylElt_ia_conj_rootDiagUnit
    (a : Fin Tag.G2.rank → Kˣ) :
    weylElt .G2 K g2ia 1 * rootDiagUnit .G2 a * (weylElt .G2 K g2ia 1)⁻¹ =
      rootDiagUnit .G2 (g2Tuple (a g2ia)⁻¹ (a g2ir * a g2ia)) := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := K)
    (g2Tuple (a g2ia)⁻¹ (a g2ir * a g2ia)) a (simple .G2 g2ia)).2 (fun v => by
      rw [simple_smul, rootChar_g2, rootChar_g2, (reflect_ia_apply v).1, (reflect_ia_apply v).2,
        g2Tuple_ia, g2Tuple_ir]
      exact zpow_calc1 _ _ _ _)
  rw [canonicalRep_simple] at h
  exact h.symm

theorem weylElt_ir_conj_rootDiagUnit
    (a : Fin Tag.G2.rank → Kˣ) :
    weylElt .G2 K g2ir 1 * rootDiagUnit .G2 a * (weylElt .G2 K g2ir 1)⁻¹ =
      rootDiagUnit .G2 (g2Tuple (a g2ia * a g2ir ^ 3) (a g2ir)⁻¹) := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := K)
    (g2Tuple (a g2ia * a g2ir ^ 3) (a g2ir)⁻¹) a (simple .G2 g2ir)).2 (fun v => by
      rw [simple_smul, rootChar_g2, rootChar_g2, (reflect_ir_apply v).1, (reflect_ir_apply v).2,
        g2Tuple_ia, g2Tuple_ir]
      exact zpow_calc2 _ _ _ _)
  rw [canonicalRep_simple] at h
  exact h.symm

theorem rootDiagUnit_mem_torusGroup_g2
    (a : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit .G2 a ∈ torusGroup .G2 K := by
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).1
  exact ((G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).2 B hB a).2.1

theorem rootDiagUnit_mem_adjointGroup_g2
    (a : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit .G2 a ∈ adjointGroup .G2 K := by
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).1
  exact ((G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).2 B hB a).2.2.1

theorem exists_eq_rootDiagUnit_of_mem_torusGroup
    {τ : Tag} {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) : ∃ a : Fin τ.rank → Kˣ, t = rootDiagUnit τ a := by
  have hrange : torusGroup τ K ≤ (rootDiagUnitHom τ K).range := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩
  obtain ⟨a, ha⟩ := hrange ht
  exact ⟨a, ha.symm⟩

theorem rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell_of_mem_torus
    {τ : Tag}
    (a b : Fin τ.rank → Kˣ) (hTa : rootDiagUnit τ a ∈ torusGroup τ K)
    (hTb : rootDiagUnit τ b ∈ torusGroup τ K) {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ bruhatCell τ K w) (hconj : g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ a) :
    rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set da := rootDiagUnit τ a with hda
  set db := rootDiagUnit τ b with hdb
  obtain ⟨⟨bb, v⟩, ⟨hbb, hv⟩, hbv⟩ := ((bruhat_cell_factorization τ K).1 w).2.2 hg
  have hbb' : bb ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hTB.2.2.2.2.1]
    exact hbb
  obtain ⟨h, hh, u, hu, rfl⟩ := hbb'
  simp only at hbv
  subst hbv
  have hconj' : h * u * n * v * db * (h * u * n * v)⁻¹ = da := hconj
  set s := n * db * n⁻¹ with hs
  have hsT : s ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) db).1 hTb
  set t := da * s⁻¹ with ht
  have htT : t ∈ torusGroup τ K := mul_mem hTa (inv_mem hsT)
  have hdu : da * u * da⁻¹ ∈ posUnipotent τ K := by
    have := ((chevalley_root_character_and_field_conjugation τ K).2.2.2.1 a).2.1
    rw [← this]
    exact ⟨u, hu, rfl⟩
  have hdv : db * v * db⁻¹ ∈ rootSpan τ K (inversionSet w) := by
    have : (rootSpan τ K (inversionSet w)).map (MulAut.conj db).toMonoidHom =
        rootSpan τ K (inversionSet w) :=
      map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup b hα.1
    rw [← this]
    exact ⟨v, hv, rfl⟩
  have hu' : t⁻¹ * (da * u * da⁻¹) * t ∈ posUnipotent τ K := by
    have hN := hTB.2.2.1 (inv_mem htT)
    have := (Subgroup.mem_normalizer_iff.1 hN (da * u * da⁻¹)).1 hdu
    simpa using this
  have hg' : da * (h * u * n * v) * db⁻¹ = h * u * n * v := by
    rw [← hconj']
    group
  have heq : h * t * (t⁻¹ * (da * u * da⁻¹) * t) * n * (db * v * db⁻¹) = h * u * n * v := by
    calc h * t * (t⁻¹ * (da * u * da⁻¹) * t) * n * (db * v * db⁻¹) =
        (h * da) * u * n * v * db⁻¹ := by
          simp only [ht, hs]
          group
      _ = da * (h * u * n * v) * db⁻¹ := by
          have hcomm : da * h = h * da := rootDiagUnit_mul_comm_of_mem_torusGroup a hh
          rw [← hcomm]
          group
      _ = h * u * n * v := hg'
  obtain ⟨-, h1, -⟩ := (Chevalley_toral_centralizer_Bruhat_factors τ K a).2.1 w w (h * t) h _ u _ v
    (mul_mem hh htT) hh hu' hu hdv hv heq
  have ht1 : t = 1 := by
    rwa [mul_eq_left] at h1
  rw [ht, mul_inv_eq_one] at ht1
  exact ht1

theorem exists_weyl_conj_of_mem_adjointGroup
    {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K) :
    ∃ w : WeylGroup .G2, ∀ a b : Fin Tag.G2.rank → Kˣ,
      g * rootDiagUnit .G2 b * g⁻¹ = rootDiagUnit .G2 a →
        rootDiagUnit .G2 a = canonicalRep (coxeterSystem .G2) K w * rootDiagUnit .G2 b *
          (canonicalRep (coxeterSystem .G2) K w)⁻¹ := by
  have hg' : g ∈ (adjointGroup .G2 K : Set (ModGL .G2 K)) := hg
  rw [adjointGroup_eq_iUnion_bruhatCell, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  exact ⟨w, fun a b h =>
    rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell_of_mem_torus a b
      (rootDiagUnit_mem_torusGroup_g2 a) (rootDiagUnit_mem_torusGroup_g2 b) hw h⟩

theorem exists_list_canonicalRep_eq
    (w : WeylGroup .G2) :
    ∃ ω : List (Fin Tag.G2.rank),
      canonicalRep (coxeterSystem .G2) K w = (ω.map fun i => weylElt .G2 K i 1).prod := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem .G2).exists_isReduced w
  exact ⟨ω, canonicalRep_wordProd hω⟩

end CFSG.RankThree.PartOne.KFU
