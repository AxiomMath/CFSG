module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryLift
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryTorus
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankU3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem two_mul_le_modCommRank_of_isUnitaryTransvectionIn
    {X : Type} [Group X] [Finite X] {m n : ℕ} (hm : 4 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hcard : Nat.card F₀ = (2 ^ n) ^ 2)
    (e : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSU m (2 ^ n) F₀))
    (hodd : Odd (Nat.card (Subgroup.center X)))
    {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Finite F]
    (σ : ↥(commutator X) →* LGL 2 F)
    (hσ : ∀ y : ↥(commutator X), (y : X) ∉ Subgroup.center X → σ y ≠ 1)
    {w : ↥(commutator X)} (hw : (w : X) * (w : X) = 1)
    (hwt : IsUnitaryTransvectionIn m n (e (QuotientGroup.mk (w : X)))) :
    2 * n ≤ modCommRank (σ w) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hc := hcard
    rw [hn0, pow_zero, one_pow] at hc
    have h1 := Finite.one_lt_card (α := F₀)
    omega
  haveI : CharP F₀ 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hcard
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F₀ :=
    ⟨Nat.prime_two, hn, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨g, hge, hgrank⟩ := hwt
  let P : ↥(StatedSU 3 (2 ^ n) F₀) := permSU n F₀ (Equiv.swap 0 1)
  have hPP : P * P = 1 := by
    dsimp [P]
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have h3 : 0 + 3 ≤ m := by omega
  let g' : ↥(StatedSU m (2 ^ n) F₀) :=
    CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 h3 P
  have hg'rank :
      Matrix.rank (((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) = 1 := by
    dsimp [g', P]
    rw [CFSG.OddStandard.GH71.S55.C5U.coe_blkSU,
      CFSG.ClassicalInvolution.Phan.coe_blockGL, rank_blockMat_sub_one h3,
      rank_permSU_swap_sub_one]
  obtain ⟨α, hαe, hαX⟩ := exists_blkSU_lift hm hU e hodd
  obtain ⟨a, ha⟩ :=
    exists_mul_mul_inv_eq_of_rank_sub_one_eq_one hcard (by omega : 3 ≤ m) hgrank hg'rank
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm (QuotientGroup.mk a))
  have hxe : e (QuotientGroup.mk x) = QuotientGroup.mk a := by
    rw [hx, MulEquiv.apply_symm_apply]
  let y : X := x⁻¹ * α P * x
  have hye : e (QuotientGroup.mk y) = e (QuotientGroup.mk (w : X)) := by
    have hga : g = a⁻¹ * g' * a := by
      rw [← ha]
      group
    calc
      e (QuotientGroup.mk y) =
          (e (QuotientGroup.mk x))⁻¹ * e (QuotientGroup.mk (α P)) *
            e (QuotientGroup.mk x) := by
        simp [y, map_mul, map_inv]
      _ = (QuotientGroup.mk a)⁻¹ * QuotientGroup.mk g' * QuotientGroup.mk a := by
        rw [hxe, hαe P]
      _ = QuotientGroup.mk (a⁻¹ * g' * a) := by
        simp [map_mul, map_inv]
      _ = QuotientGroup.mk g := by rw [← hga]
      _ = e (QuotientGroup.mk (w : X)) := hge
  have hmyw : (QuotientGroup.mk y : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (w : X) := e.injective hye
  have hyy : y * y = 1 := by
    dsimp [y]
    calc
      (x⁻¹ * α P * x) * (x⁻¹ * α P * x) = x⁻¹ * (α P * α P) * x := by group
      _ = x⁻¹ * α (P * P) * x := by rw [← map_mul]
      _ = x⁻¹ * α 1 * x := by rw [hPP]
      _ = 1 := by rw [map_one]; group
  have hyw : y = (w : X) := eq_of_mul_self_eq_one_of_mk_eq hodd hyy hw hmyw
  let α' : ↥(StatedSU 3 (2 ^ n) F₀) →* ↥(commutator X) :=
    ((MulAut.conj x⁻¹).toMonoidHom.comp α).codRestrict (commutator X) fun h => by
      change (MulAut.conj x⁻¹) (α h) ∈ commutator X
      have hmem : (MulAut.conj x⁻¹) (α h) = x⁻¹ * α h * x := by
        rw [MulAut.conj_apply, inv_inv]
      rw [hmem, commutator_def]
      simpa [inv_inv] using
        (Subgroup.commutator_normal (⊤ : Subgroup X) (⊤ : Subgroup X)).conj_mem
          (α h) (hαX h) x⁻¹
  have hα'P : α' P = w := by
    apply Subtype.ext
    change (MulAut.conj x⁻¹) (α P) = (w : X)
    rw [MulAut.conj_apply, inv_inv]
    exact hyw
  have hinj : Function.Injective (σ.comp α') := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have hcenter : (α' h : X) ∈ Subgroup.center X := by
      by_contra hc
      exact (hσ (α' h) hc) hh
    have hαc : α h ∈ Subgroup.center X := by
      have hconj : (α' h : X) = x⁻¹ * α h * x := by
        change (MulAut.conj x⁻¹) (α h) = x⁻¹ * α h * x
        rw [MulAut.conj_apply, inv_inv]
      have hxconj : x * (α' h : X) * x⁻¹ = α h := by
        rw [hconj]
        group
      rw [← hxconj]
      exact (inferInstance : (Subgroup.center X).Normal).conj_mem
        (α' h : X) hcenter x
    have hblk : CFSG.ComponentClassification.Burgoyne.Proj.projH
        (StatedSU m (2 ^ n) F₀)
        (CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 h3 h) = 1 := by
      have h1 : (QuotientGroup.mk (α h) : X ⧸ Subgroup.center X) = 1 :=
        (QuotientGroup.eq_one_iff (α h)).2 hαc
      have h2 : (QuotientGroup.mk
          (CFSG.OddStandard.GH71.S55.C5U.blkSU hU 0 h3 h) :
            StatedProj (StatedSU m (2 ^ n) F₀)) = 1 := by
        rw [← hαe h, h1, map_one]
      simpa [CFSG.ComponentClassification.Burgoyne.Proj.projH,
        QuotientGroup.mk'_apply] using h2
    apply CFSG.OddStandard.GH71.S55.C5U.proj_blkSU_injective hU h3 (by omega : 3 < m)
    simpa [MonoidHom.comp_apply, hblk]
  have hbound :=
    two_mul_le_modCommRank_permSU_swap_of_injective (n := n) (F₀ := F₀) hn hcard
      (σ.comp α') hinj
  rw [MonoidHom.comp_apply] at hbound
  change 2 * n ≤ modCommRank (σ (α' P)) at hbound
  rw [hα'P] at hbound
  exact hbound

theorem unitaryRootCommutatorRankAt_of_four_le
    {m : ℕ} (hm : 4 ≤ m) : UnitaryRootCommutatorRankAt m := by
  intro G _ _ K I n hI hK hC X _ φ hφ hX v hv hvt
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hvtX : IsUnitaryTransvection X m n (φ v) := hvt
  obtain ⟨F₀, _, _, hcard, e, hvt'⟩ := hvt
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hc := hcard
    rw [hn0, pow_zero, one_pow] at hc
    have h1 := Finite.one_lt_card (α := F₀)
    omega
  have hnq : (m, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (StatedProj (StatedSU m (2 ^ n) F₀)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F₀ 2 n hcard m
      (by omega) hnq
  haveI : Group.IsPerfect (StatedSU m (2 ^ n) F₀) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard (by omega) hnq
  haveI : Group.IsPerfect (StatedProj (StatedSU m (2 ^ n) F₀)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hS : IsSimpleGroup (X ⧸ Subgroup.center X) := e.isSimpleGroup
  have hperf : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hvc : φ v ∉ Subgroup.center X :=
    isUnitaryTransvection_not_mem_center_of_two_le (by omega : 2 ≤ m) hvtX
  obtain ⟨hvX, F, _, _, _, σ, _, hσ1, hrank⟩ :=
    exists_irreducible_section_of_bar hI hK hC hφ hS hperf hv hvc
  have hσ' : ∀ y : ↥(commutator X), (y : X) ∉ Subgroup.center X → σ y ≠ 1 :=
    fun y hy => sigma_ne_one_of_not_mem_center hS hperf σ ⟨⟨φ v, hvX⟩, hσ1⟩ y.2 hy
  have hvv : φ v * φ v = 1 := by
    rw [← map_mul]
    have hvv' : v * v = 1 := Subtype.ext hv
    rw [hvv', map_one]
  have hmain :=
    two_mul_le_modCommRank_of_isUnitaryTransvectionIn hm hcard e
      (bar_odd_card_center hφ) σ hσ' (w := ⟨φ v, hvX⟩) hvv hvt'
  exact hmain.trans hrank

end CFSG.LocalAnalysis.WeakClosure81

end
