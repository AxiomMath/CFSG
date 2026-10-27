module

public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryPieces1615
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerDiag
public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryBlockShape

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

private theorem ltrcu2a_not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  haveI : Group.IsPerfect Q := hperf
  exact Group.IsPerfect.not_isSolvable Q

private theorem ltrcu2_n_ge_two
    {d n : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hψker : ψ.ker ≤ Subgroup.center L')
    {J : Subgroup L'} (hJ : CFSG.IsQuasisimple J)
    {I : Finset (Fin d)} (hI : I.card = 2)
    (hmap : J.map ψ =
      (TableBUE.blockSU (K := K) (n := n) I).map (LargeEvenProjMk (unitarySU 2 n K d))) :
    2 ≤ n := by
  by_contra hlt
  have hn1 : n = 1 := by have := h.one_le; omega
  subst hn1
  haveI : Group.IsSolvable ↥(unitarySU 2 1 K I.card) :=
    WitSU.isSolvable_unitarySU_two_one h (k := I.card) (by omega) (by omega)
  have hsolvImg : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) I).map
      (LargeEvenProjMk (unitarySU 2 1 K d))) :=
    WitSU.isSolvable_map_blockSU_two_one h (LargeEvenProjMk (unitarySU 2 1 K d))
      (S := I) (by omega) (by omega)
  have hsolvJ : Group.IsSolvable ↥(J.map ψ) := by
    rw [hmap]
    exact hsolvImg
  have hqJ : CFSG.IsQuasisimple ↥(J.map ψ) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      (SURepair.isQuasisimple_map_of_isQuasisimple hψker hJ)
  exact ltrcu2a_not_isSolvable_of_isQuasisimple hqJ hsolvJ

private theorem ltrcu2_block_perfect
    {d n : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    {I : Finset (Fin d)} (hI : I.card = 2) :
    ⁅TableBUE.blockSU (K := K) (n := n) I, TableBUE.blockSU (K := K) (n := n) I⁆ =
      TableBUE.blockSU (K := K) (n := n) I := by
  have hq := SURepair.isQuasisimple_blockSU_of_two_le (f := n) (n := d) h hn (S := I) (by omega)
  exact Subgroup.isPerfect_iff.1 hq.1

private theorem ltrcu2b_commutator_mul_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x y : G) :
    (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzy : z * y = y * z := (Subgroup.mem_center_iff.mp hz y).symm
  rw [mul_inv_rev, mul_assoc x z y, hzy]
  group

private theorem ltrcu2b_commutator_mul_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x y : G) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzx : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.mp hz x⁻¹).symm
  rw [mul_inv_rev, ← mul_assoc x y z, mul_assoc (x * y) z x⁻¹, hzx]
  group

private theorem ltrcu2b_commutator_mul_center {G : Type*} [Group G] {z z' : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) (x y : G) :
    (x * z) * (y * z') * (x * z)⁻¹ * (y * z')⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  rw [ltrcu2b_commutator_mul_center_right hz' (x * z) y,
    ltrcu2b_commutator_mul_center_left hz x y]

private theorem ltrcu2_conj_block
    {d n : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    {J : Subgroup L'} {a : MulAut L'} (haJ : ∀ j ∈ J, a j ∈ J)
    {N : GL (Fin d) K}
    (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {I : Finset (Fin d)}
    (hperf : ⁅TableBUE.blockSU (K := K) (n := n) I, TableBUE.blockSU (K := K) (n := n) I⁆ =
      TableBUE.blockSU (K := K) (n := n) I)
    (hmap : J.map ψ =
      (TableBUE.blockSU (K := K) (n := n) I).map (LargeEvenProjMk (unitarySU 2 n K d)))
    (hact : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ (ψ l) = ψ (a l)) :
    ∀ b : ↥(unitarySU 2 n K d), b ∈ TableBUE.blockSU (K := K) (n := n) I →
      (unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b ∈
        TableBUE.blockSU (K := K) (n := n) I := by
  let c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d) :=
    ((unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩).toMonoidHom
  have hstep : ∀ x ∈ TableBUE.blockSU (K := K) (n := n) I,
      ∃ x' ∈ TableBUE.blockSU (K := K) (n := n) I,
        ∃ z ∈ Subgroup.center ↥(unitarySU 2 n K d), c x = x' * z := by
    intro x hx
    have hxπ : LargeEvenProjMk (unitarySU 2 n K d) x ∈
        (TableBUE.blockSU (K := K) (n := n) I).map
          (LargeEvenProjMk (unitarySU 2 n K d)) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxJ : LargeEvenProjMk (unitarySU 2 n K d) x ∈ J.map ψ := by
      rw [hmap]; exact hxπ
    obtain ⟨j, hjJ, hjx⟩ := Subgroup.mem_map.mp hxJ
    have hproj : TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩
        (LargeEvenProjMk (unitarySU 2 n K d) x) =
        LargeEvenProjMk (unitarySU 2 n K d) (c x) :=
      CFSG.StandardType.TableBUD.projConj_mk_coe ⟨N, hNnorm⟩ x
    have hcx : LargeEvenProjMk (unitarySU 2 n K d) (c x) = ψ (a j) := by
      rw [← hproj, ← hjx, hact j]
    have hmem : LargeEvenProjMk (unitarySU 2 n K d) (c x) ∈
        (TableBUE.blockSU (K := K) (n := n) I).map
          (LargeEvenProjMk (unitarySU 2 n K d)) := by
      rw [hcx, ← hmap]
      exact Subgroup.mem_map.mpr ⟨a j, haJ j hjJ, rfl⟩
    obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp hmem
    have hzker : x'⁻¹ * c x ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx'eq, inv_mul_cancel]
    have hzcen : x'⁻¹ * c x ∈ Subgroup.center ↥(unitarySU 2 n K d) :=
      TableBUE.ker_projMk_le_center hzker
    exact ⟨x', hx', x'⁻¹ * c x, hzcen, by group⟩
  have hle : (TableBUE.blockSU (K := K) (n := n) I).map c ≤
      TableBUE.blockSU (K := K) (n := n) I := by
    have hperf' : (TableBUE.blockSU (K := K) (n := n) I).map c =
        ⁅(TableBUE.blockSU (K := K) (n := n) I).map c,
          (TableBUE.blockSU (K := K) (n := n) I).map c⁆ :=
      (congrArg (Subgroup.map c) hperf.symm).trans
        (Subgroup.map_commutator (TableBUE.blockSU (K := K) (n := n) I)
          (TableBUE.blockSU (K := K) (n := n) I) c)
    rw [hperf', Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x', hx', z, hz, hxeq⟩ := hstep x₀ hx₀
    obtain ⟨y', hy', z', hz', hyeq⟩ := hstep y₀ hy₀
    rw [hxeq, hyeq, commutatorElement_def,
      ltrcu2b_commutator_mul_center hz hz' x' y', ← commutatorElement_def]
    exact hperf ▸ Subgroup.commutator_mem_commutator hx' hy'
  intro b hb
  exact hle (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)

private theorem ltrcu2_block_conj_inner
    {d n : ℕ} [NeZero d] {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hdvd : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hψsurj : Function.Surjective ψ) (hψker : ψ.ker ≤ Subgroup.center L')
    {J : Subgroup L'} (hJ : CFSG.IsQuasisimple J)
    {a : MulAut L'} (haJ : ∀ j ∈ J, a j ∈ J)
    {τ : Fin d → Kˣ} (hτ : ∀ i, τ i ^ 3 = 1)
    {N : GL (Fin d) K}
    (hNnorm : N ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hNgu : N ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hND : N * diagHom d τ * N⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ)
    {I : Finset (Fin d)} (hI : I.card = 2)
    (hclass : ∀ i ∈ I, ∀ j, τ j = τ i → j ∈ I)
    (hconst : ∀ i ∈ I, ∀ j ∈ I, τ i = τ j)
    (hmap : J.map ψ =
      (TableBUE.blockSU (K := K) (n := n) I).map (LargeEvenProjMk (unitarySU 2 n K d)))
    (hact : ∀ l : L', TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ (ψ l) = ψ (a l)) :
    ∃ s : ↥(unitarySU 2 n K d), s ∈ TableBUE.blockSU (K := K) (n := n) I ∧
      ∀ b : ↥(unitarySU 2 n K d), b ∈ TableBUE.blockSU (K := K) (n := n) I →
        LargeEvenProjMk (unitarySU 2 n K d)
            ((unitarySU 2 n K d).normalizerMonoidHom ⟨N, hNnorm⟩ b) =
          LargeEvenProjMk (unitarySU 2 n K d) (s * b * s⁻¹) := by
  have hn := ltrcu2_n_ge_two h hψker hJ hI hmap
  have hperf := ltrcu2_block_perfect h hn hI
  have hconj := ltrcu2_conj_block haJ hNnorm hperf hmap hact
  have hshape := unitaryBlock_entry_zero h hn hdvd hNnorm hI hconj
  obtain ⟨s, hsB, hs⟩ := unitaryBlock_conj_inner_of_shape h hn hNnorm hNgu hI hshape hconj
  exact ⟨s, hsB, fun b hb => congrArg (LargeEvenProjMk (unitarySU 2 n K d)) (hs b hb)⟩

theorem unitaryBlockAction_holds : UnitaryBlockAction := by
  intro d n hd_ne K hK hKfin h hdvd L' hL' hL'fin ψ hψsurj hψker J hJ a haJ τ hτ
    D N hDnorm hNnorm hNgu hD ζ hζ hND I hI hclass hconst hmap hact
  have hND' : N * diagHom d τ * N⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) ζ * diagHom d τ := by
    rw [hD] at hND
    exact hND
  obtain ⟨s, hsB, hinner⟩ :=
    ltrcu2_block_conj_inner h hdvd hψsurj hψker hJ haJ hτ hNnorm hNgu hζ hND' hI hclass
      hconst hmap hact
  have hπs_mem : LargeEvenProjMk (unitarySU 2 n K d) s ∈ J.map ψ := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨s, hsB, rfl⟩
  obtain ⟨j₀raw, hj₀J, hj₀eq⟩ := Subgroup.mem_map.mp hπs_mem
  let j₀ : ↥J := ⟨j₀raw, hj₀J⟩
  have hj₀eq' : ψ (j₀ : L') = LargeEvenProjMk (unitarySU 2 n K d) s := hj₀eq
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥J) j₀, ?_⟩
  intro j j' hajj'
  have hψj : ψ j ∈ (TableBUE.blockSU (K := K) (n := n) I).map
      (LargeEvenProjMk (unitarySU 2 n K d)) := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨j, j.2, rfl⟩
  obtain ⟨b, hbB, hbψ⟩ := Subgroup.mem_map.mp hψj
  have hproj : TableB.projConj (unitarySU 2 n K d) ⟨N, hNnorm⟩ (ψ j) =
      LargeEvenProjMk (unitarySU 2 n K d) (s * b * s⁻¹) := by
    rw [← hbψ]
    rw [CFSG.StandardType.TableBUD.projConj_mk_coe]
    exact hinner b hbB
  have key : ψ ((j₀ * j * j₀⁻¹ : ↥J) : L') = ψ (j' : L') := by
    have hmid : LargeEvenProjMk (unitarySU 2 n K d) (s * b * s⁻¹) = ψ (j' : L') := by
      rw [← hproj, hact (j : L'), hajj']
    calc ψ ((j₀ * j * j₀⁻¹ : ↥J) : L')
        = ψ (j₀ : L') * ψ (j : L') * (ψ (j₀ : L'))⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
      _ = LargeEvenProjMk (unitarySU 2 n K d) (s * b * s⁻¹) := by
          rw [hj₀eq', ← hbψ, map_mul, map_mul, map_inv]
      _ = ψ (j' : L') := hmid
  set d' : ↥J := (j₀ * j * j₀⁻¹)⁻¹ * j' with hd'def
  have hdker : (d' : L') ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    have hcoeeq : (d' : L') =
        ((j₀ * j * j₀⁻¹ : ↥J) : L')⁻¹ * (j' : L') := by
      rw [hd'def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoeeq, map_mul, map_inv, key, inv_mul_cancel]
  have hdcenter : d' ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hψker hdker) (g : L')
  have hd1 : QuotientGroup.mk' (Subgroup.center ↥J) d' = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hdcenter
  have hjeq : j' = (j₀ * j * j₀⁻¹) * d' := by
    rw [hd'def]
    group
  show QuotientGroup.mk' (Subgroup.center ↥J) j' =
    QuotientGroup.mk' (Subgroup.center ↥J) j₀ *
      QuotientGroup.mk' (Subgroup.center ↥J) j *
      (QuotientGroup.mk' (Subgroup.center ↥J) j₀)⁻¹
  rw [hjeq, map_mul, hd1, mul_one, map_mul, map_mul, map_inv]

end CFSG.StandardType.KD2Pieces1615

end
