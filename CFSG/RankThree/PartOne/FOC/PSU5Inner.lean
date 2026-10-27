module

public import CFSG.RankThree.PartOne.FOC.SU5Cen
public import CFSG.RankThree.PartOne.FOC.CompGroup
public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.S11c.Sec66PSUFrame

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.Sec66T (psu5 proj5)

section Inner

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem commutator_mem_normOneScalars {B g : ↥(gamma5 h)}
    (hg : (QuotientGroup.mk g : psu5 h) ∈ Subgroup.centralizer ({(QuotientGroup.mk B : psu5 h)} :
      Set (psu5 h))) :
    g * B * g⁻¹ * B⁻¹ ∈ normOneScalars h (gamma5 h) 5 := by
  rw [← QuotientGroup.eq_one_iff]
  have := Subgroup.mem_centralizer_singleton_iff.mp hg
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [this]
  group

theorem innerComp_psu_five (h5 : 5 ∣ 2 ^ f + 1) [Finite (psu5 h)] [IsSimpleGroup (psu5 h)]
    (hnab : ∃ a b : psu5 h, a * b ≠ b * a) : InnerComp 5 (psu5 h) := by
  classical
  have hfin : Finite K := h.finite
  have hZc : normOneScalars h (gamma5 h) 5 ≤ Subgroup.center (gamma5 h) :=
    normOneScalars_le_center h _ 5
  have hker : (proj5 h).ker ≤ Subgroup.center (gamma5 h) := by
    rw [proj5, QuotientGroup.ker_mk']
    exact hZc
  intro _ b y hb5 hy5 hby E hE
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
  have hB5 : B ^ 5 ∈ normOneScalars h (gamma5 h) 5 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hb5
  obtain ⟨c, hcn, hc5, hBc⟩ := hB5
  have hP5 : (B : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
    rw [← Subgroup.coe_pow]
    exact hBc
  have hc : c ^ (2 ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hcn
  have hBU : (B : GL (Fin 5) K) ∈ unit5 h := ((mem_gramSU_iff_unitary h).mp B.2).1
  let P : unit5 h := ⟨(B : GL (Fin 5) K), hBU⟩
  have hPB : (P : GL (Fin 5) K) = (B : GL (Fin 5) K) := rfl
  have hP5' : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c := hP5
  by_cases hsc : ∃ μ : Kˣ, (B : GL (Fin 5) K) = Matrix.GeneralLinearGroup.scalar (Fin 5) μ
  ·
    obtain ⟨μ, hμ⟩ := hsc
    have hb1 : (QuotientGroup.mk B : psu5 h) = 1 := by
      have hcen : (QuotientGroup.mk B : psu5 h) ∈ Subgroup.center (psu5 h) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hμ]
        exact (commute_scalar (ι := Fin 5) μ _).eq
      rw [center_eq_bot_of_nonab inferInstance hnab, Subgroup.mem_bot] at hcen
      exact hcen
    have htop : Subgroup.centralizer ({(QuotientGroup.mk B : psu5 h)} : Set (psu5 h)) = ⊤ := by
      rw [hb1]
      ext x
      simp [Subgroup.mem_centralizer_iff]
    rw [htop] at hE
    have : IsSimpleGroup ↥(⊤ : Subgroup (psu5 h)) := Subgroup.topEquiv.isSimpleGroup
    have hEtop := eq_of_isComponentOf_simple (F := (⊤ : Subgroup (psu5 h))) hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top _)
  · have hns : ∀ μ : Kˣ, (P : GL (Fin 5) K) ≠
        Matrix.GeneralLinearGroup.scalar (Fin 5) μ := fun μ hμ => hsc ⟨μ, hμ⟩
    by_cases hsh : ∃ (g : ↥(gamma5 h)) (w : Kˣ), w ^ 5 = 1 ∧ w ≠ 1 ∧
        (g : GL (Fin 5) K) * (B : GL (Fin 5) K) * (g : GL (Fin 5) K)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 5) w * (B : GL (Fin 5) K)
    ·
      exfalso
      obtain ⟨g, w, hw5, hw1, hg⟩ := hsh
      have hcomm := su5_comm_of_shift (h := h) (P := P) h5 hc hP5' (g := g) hw5 hw1 hg
      refine false_of_isComponentOf_of_comm (A := (cenSU h 5 (B : GL (Fin 5) K)).map (proj5 h))
        ?_ ?_ hE
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
        rw [← map_mul, ← map_mul, hcomm a a' ha ha']
      · intro x hx y hy
        obtain ⟨gx, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨gy, rfl⟩ := QuotientGroup.mk_surjective y
        have hux := commutator_mem_normOneScalars hx
        have huy := commutator_mem_normOneScalars hy
        have hc' := commutator_mem_of_central_conj (B := B) (g₁ := gx) (g₂ := gy)
          (u₁ := gx * B * gx⁻¹ * B⁻¹) (u₂ := gy * B * gy⁻¹ * B⁻¹)
          (fun z => (Subgroup.mem_center_iff.mp (hZc hux) z).symm)
          (fun z => (Subgroup.mem_center_iff.mp (hZc huy) z).symm) (by group) (by group)
        refine ⟨gx * gy * gx⁻¹ * gy⁻¹, mem_cenSU.mpr ?_, ?_⟩
        · have := congrArg Subtype.val hc'
          simpa using this
        · rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          rfl
    · push Not at hsh
      have hC : Subgroup.centralizer ({(QuotientGroup.mk B : psu5 h)} : Set (psu5 h)) =
          (cenSU h 5 (B : GL (Fin 5) K)).map (proj5 h) := by
        ext x
        constructor
        · intro hx
          obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
          obtain ⟨w, -, hw5, huw⟩ := commutator_mem_normOneScalars hx
          refine ⟨g, mem_cenSU.mpr ?_, rfl⟩
          have hgl : (g : GL (Fin 5) K) * (B : GL (Fin 5) K) * (g : GL (Fin 5) K)⁻¹ *
              (B : GL (Fin 5) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 5) w := by
            simpa using huw
          by_cases hw1 : w = 1
          · rw [hw1, map_one] at hgl
            exact commutatorElement_eq_one_iff_mul_comm.mp hgl
          · exfalso
            apply hsh g w hw5 hw1
            rw [← hgl]
            group
        · rintro ⟨g, hg, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          show (QuotientGroup.mk g : psu5 h) * QuotientGroup.mk B = QuotientGroup.mk B * QuotientGroup.mk g
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact mem_cenSU.mp hg
      have hQ := su5_quasiFactored (h := h) (P := P) h5 hc hP5' hns
      obtain ⟨ι, F, hFq, hFC, hFn, hfac⟩ := hQ
      have hYc : (QuotientGroup.mk Y : psu5 h) ∈
          Subgroup.centralizer ({(QuotientGroup.mk B : psu5 h)} : Set (psu5 h)) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hby.symm
      rw [hC] at hYc
      obtain ⟨g, hg, hgY⟩ := hYc
      obtain ⟨z, k, hgzk, hzc, hk⟩ := hfac g hg
      have hFC' : ∀ i, F i ≤ Subgroup.centralizer ({B} : Set ↥(gamma5 h)) := by
        intro i g' hg'
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact mem_cenSU.mp (hFC i hg')
      have hFn' : ∀ i, ∀ g' ∈ Subgroup.centralizer ({B} : Set ↥(gamma5 h)), ∀ f' ∈ F i,
          g' * f' * g'⁻¹ ∈ F i := by
        intro i g' hg' f' hf'
        refine hFn i g' (mem_cenSU.mpr ?_) f' hf'
        have := Subgroup.mem_centralizer_singleton_iff.mp hg'
        have h2 := congrArg Subtype.val this
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
        exact h2
      have hJ : ∀ i, (F i).map (proj5 h) = ⊥ ∨ IsComponentOf
          (Subgroup.centralizer ({(QuotientGroup.mk B : psu5 h)} : Set (psu5 h)))
          ((F i).map (proj5 h)) := fun i =>
        Or.inr (isComponentOf_map_block (proj5 h) (QuotientGroup.mk'_surjective _) hker B (F i)
          (hFq i) (hFC' i) (hFn' i))
      rw [← hgY]
      refine mem_sup_centralizer_of_factorization (fun i => (F i).map (proj5 h)) hJ
        (z := proj5 h z) (k := proj5 h k) (by rw [hgzk, map_mul]) ?_ ?_ hE
      · intro n hn
        rw [hC] at hn
        obtain ⟨g', hg', rfl⟩ := hn
        rw [← map_mul, ← map_mul, hzc g' hg']
      · rw [← Subgroup.map_iSup]
        exact ⟨k, hk, rfl⟩

end Inner

end CFSG.RankThree.PartOne.FOC
