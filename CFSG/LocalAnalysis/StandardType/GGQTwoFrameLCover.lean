module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxCover
public import CFSG.GH74.Uniqueness.Section14Primary
public import CFSG.GroupTheory.PerfectCoverProduct
public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.StandardType.QTwo
open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

theorem qTwoCover_mem_primaryComponent_of_sq_mem
    {G : Type} [Group G] {B : Subgroup G} (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    {z : G} (hz : z ∈ B)
    (hz2 : z ^ 2 ∈ CFSG.GH74.Uniqueness.primaryComponent B hB 2) :
    z ∈ CFSG.GH74.Uniqueness.primaryComponent B hB 2 := by
  obtain ⟨-, k, hk⟩ := CFSG.GH74.Uniqueness.mem_primaryComponent.mp hz2
  refine CFSG.GH74.Uniqueness.mem_primaryComponent.mpr ⟨hz, k + 1, ?_⟩
  have h : z ^ (2 ^ (k + 1)) = (z ^ 2) ^ (2 ^ k) := by
    rw [pow_succ', ← pow_mul]
  rw [h, hk]

private theorem qTwoCover_quotient_perfect
    {L : Type} [Group L] {Δ : Subgroup L} [Δ.Normal] (hperf : commutator L = ⊤) :
    commutator (L ⧸ Δ) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Δ y
  have hl : l ∈ commutator L := by rw [hperf]; exact Subgroup.mem_top l
  have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' Δ) hl
  rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Δ), ← commutator_def] at h1

private theorem qTwoCover_piZ_ker
    {L : Type} [Group L] {Δ Z : Subgroup L} [Δ.Normal] [Z.Normal] (hΔZ : Δ ≤ Z)
    (πZ : L ⧸ Δ →* L ⧸ Z) (hπZ : ∀ l, πZ (QuotientGroup.mk' Δ l) = QuotientGroup.mk' Z l) :
    πZ.ker = Z.map (QuotientGroup.mk' Δ) := by
  ext y
  constructor
  · intro hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Δ y
    have hl : l ∈ Z := by
      have h1 : πZ (QuotientGroup.mk' Δ l) = 1 := hy
      rw [hπZ l] at h1
      change ((l : L ⧸ Z) = 1) at h1
      rwa [QuotientGroup.eq_one_iff] at h1
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rw [MonoidHom.mem_ker, hπZ l]
    change ((l : L ⧸ Z) = 1)
    rw [QuotientGroup.eq_one_iff]
    exact hl

private theorem qTwoCover_ker_projS_le_center
    {m : ℕ} {F0 : Type} [Field F0] :
    (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1))).ker ≤
      Subgroup.center (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) := by
  rw [LargeEvenProjMk, QuotientGroup.ker_mk']
  exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem qTwoFrameL_cover
    {L : Type} [Group L] [Finite L] {m : ℕ} (hm : 5 ≤ m) (hperf : commutator L = ⊤)
    {F0 : Type} [Field F0] [Finite F0] (hcard : Nat.card F0 = 4)
    (e : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F0 (2 ^ 1))) :
    ∃ (Δ : Subgroup L) (_ : Δ.Normal), Δ ≤ Subgroup.center L ∧ IsPGroup 2 Δ ∧
      (∀ z ∈ Subgroup.center L, (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ Δ) ∧
      ∃ ψ : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) →* L ⧸ Δ,
        Function.Surjective ψ ∧
          ψ.ker ≤ Subgroup.center ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) ∧
          ∀ (u : ↥(LargeEvenSUGroup (Fin m) F0 (2 ^ 1))) (l : L),
            ψ u = (QuotientGroup.mk l : L ⧸ Δ) →
              e (QuotientGroup.mk l : L ⧸ Subgroup.center L) =
                LargeEvenProjMk (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)) u := by
  classical
  let S : Subgroup (GL (Fin m) F0) := LargeEvenSUGroup (Fin m) F0 (2 ^ 1)
  let Z : Subgroup L := Subgroup.center L
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_center_iff.mp ha b).symm
  let Δ : Subgroup L := CFSG.GH74.Uniqueness.primaryComponent Z hZcomm 2
  have hΔleZ : Δ ≤ Z := CFSG.GH74.Uniqueness.primaryComponent_le
  have hΔleCenter : Δ ≤ Subgroup.center L := hΔleZ
  have hΔnormal : Δ.Normal := Subgroup.normal_of_le_center hΔleCenter
  haveI : Δ.Normal := hΔnormal
  haveI : Z.Normal := inferInstance
  have hΔp : IsPGroup 2 Δ := CFSG.GH74.Uniqueness.isPGroup_primaryComponent Nat.prime_two
  have hΔmem : ∀ z ∈ Z, (∃ k : ℕ, z ^ (2 ^ k) = 1) → z ∈ Δ := by
    intro z hz h
    exact CFSG.GH74.Uniqueness.mem_primaryComponent.mpr ⟨hz, h⟩
  have hperfΔ : commutator (L ⧸ Δ) = ⊤ := qTwoCover_quotient_perfect hperf
  have hΔZ_ker : Δ ≤ (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    exact hΔleZ
  let πZ : L ⧸ Δ →* L ⧸ Z := QuotientGroup.lift Δ (QuotientGroup.mk' Z) hΔZ_ker
  have hπZ : ∀ l, πZ (QuotientGroup.mk' Δ l) = QuotientGroup.mk' Z l := by
    intro l
    exact QuotientGroup.lift_mk Δ hΔZ_ker l
  have hπZ_ker : πZ.ker = Z.map (QuotientGroup.mk' Δ) :=
    qTwoCover_piZ_ker hΔleZ πZ hπZ
  have hZbar_central : Z.map (QuotientGroup.mk' Δ) ≤ Subgroup.center (L ⧸ Δ) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Δ w
    rw [← map_mul (QuotientGroup.mk' Δ) l z, ← map_mul (QuotientGroup.mk' Δ) z l]
    rw [(Subgroup.mem_center_iff.mp hz l).symm]
  haveI : (Z.map (QuotientGroup.mk' Δ)).Normal := Subgroup.normal_of_le_center hZbar_central
  let projS : S →* LargeEvenProj S := LargeEvenProjMk S
  have hprojS_surj : Function.Surjective projS := by
    change Function.Surjective (QuotientGroup.mk' _)
    exact QuotientGroup.mk'_surjective _
  let P : Subgroup ((L ⧸ Δ) × S) :=
    { carrier := {x | e (πZ x.1) = projS x.2}
      mul_mem' := by
        intro x y hx hy
        change e (πZ x.1) = projS x.2 at hx
        change e (πZ y.1) = projS y.2 at hy
        change e (πZ (x.1 * y.1)) = projS (x.2 * y.2)
        simp only [map_mul, hx, hy]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        change e (πZ x.1) = projS x.2 at hx
        change e (πZ (x.1)⁻¹) = projS (x.2)⁻¹
        simp only [map_inv, hx] }
  let pr₁ : P →* L ⧸ Δ := (MonoidHom.fst _ _).comp P.subtype
  let pr₂ : P →* S := (MonoidHom.snd _ _).comp P.subtype
  have hpr₂_surj : Function.Surjective pr₂ := by
    intro u
    obtain ⟨y, hy⟩ : ∃ y : L ⧸ Z, e y = projS u := ⟨e.symm (projS u), e.apply_symm_apply _⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Z y
    refine ⟨⟨(QuotientGroup.mk' Δ l, u), ?_⟩, rfl⟩
    change e (πZ (QuotientGroup.mk' Δ l)) = projS u
    rw [hπZ l, hl, hy]
  have hpr₂_ker_le_center : pr₂.ker ≤ Subgroup.center P := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx2 : pr₂ x = 1 := MonoidHom.mem_ker.mp hx
    have hx1_mem : pr₁ x ∈ Z.map (QuotientGroup.mk' Δ) := by
      have hx_e : e (πZ (pr₁ x)) = 1 := by
        have hmem := x.2
        change e (πZ (pr₁ x)) = projS (pr₂ x) at hmem
        rw [hmem, hx2, map_one]
      have hx_pi : πZ (pr₁ x) = 1 := by
        apply e.injective
        rw [hx_e, map_one]
      rw [← hπZ_ker]
      exact MonoidHom.mem_ker.mpr hx_pi
    have hcomm : pr₁ x * pr₁ y = pr₁ y * pr₁ x :=
      (Subgroup.mem_center_iff.mp (hZbar_central hx1_mem) (pr₁ y)).symm
    apply Subtype.ext
    apply Prod.ext
    · change pr₁ (y * x) = pr₁ (x * y)
      rw [map_mul, map_mul]
      exact hcomm.symm
    · change pr₂ (y * x) = pr₂ (x * y)
      rw [map_mul, map_mul, hx2, mul_one, one_mul]
  have hpr₂_ker_odd : Nat.Coprime 2 (Nat.card pr₂.ker) := by
    refine CFSG.StandardType.TableBU.coprime_two_card_of_sq ?_
    intro g hg2
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change pr₁ g = 1
      have hg2' : pr₂ g = 1 := MonoidHom.mem_ker.mp g.2
      have hg1_mem : pr₁ g ∈ Z.map (QuotientGroup.mk' Δ) := by
        have hg_e : e (πZ (pr₁ g)) = 1 := by
          have hmem := (g : P).2
          change e (πZ (pr₁ g)) = projS (pr₂ g) at hmem
          rw [hmem, hg2', map_one]
        have hg_pi : πZ (pr₁ g) = 1 := by
          apply e.injective
          rw [hg_e, map_one]
        rw [← hπZ_ker]
        exact MonoidHom.mem_ker.mpr hg_pi
      obtain ⟨z, hz, hz_eq⟩ := hg1_mem
      have hg1_sq : z ^ 2 ∈ Δ := by
        have h1 : pr₁ g ^ 2 = 1 := by
          have hg2P : (g : P) ^ 2 = 1 := by
            simpa using congrArg Subtype.val hg2
          have := congrArg pr₁ hg2P
          simpa using this
        rw [← hz_eq] at h1
        have h2 : QuotientGroup.mk' Δ (z ^ 2) = 1 := by
          rw [map_pow]
          exact h1
        exact (QuotientGroup.eq_one_iff (z ^ 2)).mp h2
      have hzΔ : z ∈ Δ := qTwoCover_mem_primaryComponent_of_sq_mem hZcomm hz hg1_sq
      rw [← hz_eq]
      exact (QuotientGroup.eq_one_iff z).mpr hzΔ
    · change pr₂ g = 1
      exact MonoidHom.mem_ker.mp g.2
  obtain ⟨s, hs⟩ := qTwoNbrRec_hsplit (F := F0) (n := 1) (d := m)
    (by rw [hcard]; norm_num) (by norm_num) (by omega)
    (by rintro ⟨h1, -⟩; omega)
    P pr₂ hpr₂_surj hpr₂_ker_le_center hpr₂_ker_odd
  let ψ : S →* L ⧸ Δ := (MonoidHom.fst _ _).comp (P.subtype.comp s)
  have hpr₁_range : pr₁.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨u, hu⟩ := hprojS_surj (e (πZ y))
    exact ⟨⟨(y, u), hu.symm⟩, rfl⟩
  have htop : (⊤ : Subgroup (L ⧸ Δ)) = Z.map (QuotientGroup.mk' Δ) ⊔ ψ.range := by
    apply le_antisymm
    · intro y _
      have hy : y ∈ pr₁.range := by rw [hpr₁_range]; exact Subgroup.mem_top y
      obtain ⟨p, hp⟩ := hy
      let q : P := p * (s (pr₂ p))⁻¹
      have hq_ker : q ∈ pr₂.ker := by
        change pr₂ (p * (s (pr₂ p))⁻¹) = 1
        rw [map_mul, map_inv, hs, mul_inv_cancel]
      have hq2 : pr₂ q = 1 := MonoidHom.mem_ker.mp hq_ker
      have hq1_mem : pr₁ q ∈ Z.map (QuotientGroup.mk' Δ) := by
        have hq_e : e (πZ (pr₁ q)) = 1 := by
          have hmem := (q : P).2
          change e (πZ (pr₁ q)) = projS (pr₂ q) at hmem
          rw [hmem, hq2, map_one]
        have hq_pi : πZ (pr₁ q) = 1 := by
          apply e.injective
          rw [hq_e, map_one]
        rw [← hπZ_ker]
        exact MonoidHom.mem_ker.mpr hq_pi
      have hq1_eq : pr₁ q = y * (ψ (pr₂ p))⁻¹ := by
        change pr₁ (p * (s (pr₂ p))⁻¹) = y * (ψ (pr₂ p))⁻¹
        rw [map_mul, map_inv]
        rw [show pr₁ p = y from hp]
        rfl
      have hy_eq : y = pr₁ q * ψ (pr₂ p) := by
        rw [hq1_eq]; group
      exact Subgroup.mem_sup_of_normal_left.mpr
        ⟨pr₁ q, hq1_mem, ψ (pr₂ p), MonoidHom.mem_range.mpr ⟨pr₂ p, rfl⟩, hy_eq.symm⟩
    · exact le_top
  have hcomm_eq :
      ⁅Z.map (QuotientGroup.mk' Δ) ⊔ ψ.range, Z.map (QuotientGroup.mk' Δ) ⊔ ψ.range⁆ =
        ⁅ψ.range, ψ.range⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rcases Subgroup.mem_sup_of_normal_left.mp hx with ⟨z1, hz1, h1, hh1, rfl⟩
      rcases Subgroup.mem_sup_of_normal_left.mp hy with ⟨z2, hz2, h2, hh2, rfl⟩
      have hz1c : z1 ∈ Subgroup.center (L ⧸ Δ) := hZbar_central hz1
      have hz2c : z2 ∈ Subgroup.center (L ⧸ Δ) := hZbar_central hz2
      rw [(Subgroup.mem_center_iff.mp hz1c h1).symm, (Subgroup.mem_center_iff.mp hz2c h2).symm]
      rw [CFSG.GroupTheory.PerfectCover.commutatorElement_mul_mul_of_mem_center hz1c hz2c]
      exact Subgroup.commutator_mem_commutator hh1 hh2
    · exact Subgroup.commutator_mono le_sup_right le_sup_right
  have hψ_range_top : ψ.range = ⊤ := by
    have h1 : ⁅ψ.range, ψ.range⁆ = ⊤ := by
      rw [← hcomm_eq, ← htop]
      change commutator (L ⧸ Δ) = ⊤
      exact hperfΔ
    have h2 : ⁅ψ.range, ψ.range⁆ ≤ ψ.range := Subgroup.commutator_le_self _
    rw [h1] at h2
    exact le_antisymm le_top h2
  have hψ_surj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hψ_range_top
  have hψ_ker : ψ.ker ≤ Subgroup.center S := by
    intro u hu
    have h1 : ψ u = 1 := hu
    have hs1 : pr₁ (s u) = 1 := h1
    have hs2 : pr₂ (s u) = u := hs u
    have hsP : e (πZ (pr₁ (s u))) = projS (pr₂ (s u)) := (s u).2
    rw [hs1, hs2] at hsP
    simp only [map_one] at hsP
    have hproj : projS u = 1 := hsP.symm
    have hu_ker : u ∈ projS.ker := hproj
    exact qTwoCover_ker_projS_le_center hu_ker
  refine ⟨Δ, hΔnormal, hΔleCenter, hΔp, hΔmem, ψ, hψ_surj, hψ_ker, ?_⟩
  intro u l hul
  have hP : e (πZ (ψ u)) = projS u := by
    have hmem := (s u).2
    change e (πZ (pr₁ (s u))) = projS (pr₂ (s u)) at hmem
    rwa [show pr₁ (s u) = ψ u from rfl, show pr₂ (s u) = u from hs u] at hmem
  rw [hul] at hP
  change e (πZ (QuotientGroup.mk' Δ l)) = projS u at hP
  rw [hπZ l] at hP
  exact hP

end CFSG.StandardType.QTwo

end
