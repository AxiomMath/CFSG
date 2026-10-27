module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem iSup_inf_centralizer_eq_of_card_27 {G : Type} [Group G] [Finite G] {A Q : Subgroup G}
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQ : ¬ 3 ∣ Nat.card Q) :
    ⨆ (F : Subgroup G) (_ : F ≤ A) (_ : Nat.card F = 9), Q ⊓ Subgroup.centralizer (F : Set G) =
      Q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElementaryAbelian 3 ↥A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
        Subtype.ext (by simpa using hA.2 (x : G) x.2) }
  have : Nontrivial ↥A :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hAcard]; norm_num)
  let act : MulDistribMulAction ↥A ↥Q :=
    MulDistribMulAction.compHom Q (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := ↥A) (H := ↥Q) hQ
  have hmap : (⨆ (B : Subgroup ↥A) (_ : B.index = 3),
      (fixedPointSubgroup B ↥Q).map Q.subtype) = Q := by
    have h1 : (⨆ (B : Subgroup ↥A) (_ : B.index = 3),
        (fixedPointSubgroup B ↥Q).map Q.subtype)
        = ((⨆ (B : Subgroup ↥A) (_ : B.index = 3),
        fixedPointSubgroup B ↥Q).map Q.subtype) := by
      simp only [Subgroup.map_iSup]
    rw [h1, hgen, Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm ?_ ?_
  · exact iSup_le fun F => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · refine le_trans (le_of_eq hmap.symm) ?_
    refine iSup_le fun B => iSup_le fun hB => ?_
    have hF : (B.map A.subtype : Subgroup G) ≤ A := Subgroup.map_subtype_le B
    have hBcard : Nat.card B = 9 := by
      have h := B.card_mul_index
      rw [hB, hAcard] at h
      omega
    have hcard : Nat.card (B.map A.subtype : Subgroup G) = 9 := by
      rw [Subgroup.card_subtype, hBcard]
    have heq : (fixedPointSubgroup B ↥Q).map Q.subtype =
        Q ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
      apply le_antisymm
      · rintro x ⟨q, hq, rfl⟩
        refine ⟨q.2, ?_⟩
        change Q.subtype q ∈ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        rcases Subgroup.mem_map.mp hf with ⟨b, hb, rfl⟩
        have h := hq ⟨b, hb⟩
        have h2 := congrArg Subtype.val h
        simp only [Subgroup.mk_smul] at h2
        change (b : G) * (q : G) * (b : G)⁻¹ = (q : G) at h2
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2
      · rintro x ⟨hxQ, hxC⟩
        refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
        intro b'
        apply Subtype.ext
        have hmem : (A.subtype b'.1 : G) ∈ (B.map A.subtype : Subgroup G) :=
          Subgroup.mem_map.mpr ⟨b'.1, b'.2, rfl⟩
        have hc := (Subgroup.mem_centralizer_iff.mp hxC) (A.subtype b'.1) hmem
        change (b'.1 : G) * (x : G) = (x : G) * (b'.1 : G) at hc
        change (b'.1 : G) * (x : G) * (b'.1 : G)⁻¹ = (x : G)
        rw [hc]
        group
    rw [heq]
    exact le_iSup_of_le (B.map A.subtype) (le_iSup_of_le hF (le_iSup_of_le hcard le_rfl))

theorem le_of_hyperplane_conj {G : Type} [Group G] [Finite G] {Y A Q : Subgroup G} {b₀ : G}
    (hCY : Subgroup.centralizer ({b₀} : Set G) ≤ Y)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hAF : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQ : ¬ 3 ∣ Nat.card Q) : Q ≤ Y := by
  rw [← iSup_inf_centralizer_eq_of_card_27 hA hAcard hAQ hQ]
  refine iSup_le fun F => iSup_le fun hF => iSup_le fun hc => ?_
  obtain ⟨y, hyY, hyb⟩ := hAF F hF hc
  intro x hx
  have hxF : x ∈ Subgroup.centralizer (F : Set G) := hx.2
  have hcomm : (y * b₀ * y⁻¹) * x = x * (y * b₀ * y⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hxF) (y * b₀ * y⁻¹) hyb
  have hyx : y⁻¹ * x * y ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc
      b₀ * (y⁻¹ * x * y) = y⁻¹ * ((y * b₀ * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * b₀ * y⁻¹)) * y := by rw [hcomm]
      _ = (y⁻¹ * x * y) * b₀ := by group
  have hY := hCY hyx
  have hxeq : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [hxeq]
  exact Y.mul_mem (Y.mul_mem hyY hY) (Y.inv_mem hyY)

end CFSG.StandardType.FrameRoute.FS81
