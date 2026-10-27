module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover

private theorem nbcb_ggIsUnitaryMat_mem_GUSet {K : Type} [Field K]
    [CharP K 2] [Finite K] {m f : ℕ} {g : GL (Fin m) K}
    (hg : ggIsUnitaryMat (p := 2) (f := f) g) :
    g ∈ LargeEvenGUSet (Fin m) K (2 ^ f) := by
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul]
  have hmap : ((g : Matrix (Fin m) (Fin m) K).map (· ^ 2 ^ f)) =
      (g : Matrix (Fin m) (Fin m) K).map
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 f) := by
    ext i j
    simp [iterateFrobenius_def]
  rw [hmap]
  exact hg

private theorem nbcb_not_solvable_of_isQuasisimple {Q : Type} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hsol
  obtain ⟨hperf, hsimple⟩ := hQ
  obtain ⟨n, hn⟩ := hsol.solvable
  have htop : ∀ m, derivedSeries Q m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [derivedSeries_succ, ih]
      exact hperf
  rw [htop] at hn
  have hall : ∀ x : Q, x = 1 := fun x => Subgroup.mem_bot.1 (hn ▸ Subgroup.mem_top x)
  haveI : Subsingleton Q := ⟨fun a b => by rw [hall a, hall b]⟩
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hsimple
  haveI : Subsingleton (Q ⧸ Subgroup.center Q) := inferInstance
  exact not_subsingleton (Q ⧸ Subgroup.center Q) inferInstance


theorem exists_isComponent_block_iso {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {G : Type} [Group G] [Finite G] {ψ : Su K 2 f n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {e : G} {g : GL (Fin n) K}
    (hg : ggIsDiagMat g) (he : GGInducesUnitary (p := 2) (f := f) ψ e g) {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer ({e} : Set G))) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ n ∧ (f = 1 → 4 ≤ a) ∧
      (a = n → ψ.range ≤ Subgroup.centralizer ({e} : Set G)) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* Su K 2 f a ⧸ Subgroup.center (Su K 2 f a)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by
    intro h0
    subst n
    have hrange : ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨y, rfl⟩
      have hy1 : y = 1 := by
        apply Subtype.ext
        apply Units.ext
        ext i j
        exact i.elim0
      rw [hy1, map_one]
      exact Subgroup.one_mem ⊥
    have hJle : J ≤ ⊥ := by
      have h := hJ.1.trans inf_le_left
      rwa [hrange] at h
    have hJbot : J = ⊥ := le_bot_iff.mp hJle
    exact commutator_ne_bot_of_isQuasisimple hJ.2.2
      (by rw [hJbot, Subgroup.commutator_bot_left])
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hK, hf0]; norm_num
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hfpos
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  let ee : Su K 2 f (m + 1) ≃* ↥(unitarySU 2 f K (m + 1)) :=
    MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK (m + 1))
  let ψ' : ↥(unitarySU 2 f K (m + 1)) →* G := ψ.comp ee.symm.toMonoidHom
  have hrange : ψ'.range = ψ.range := by
    change (ψ.comp ee.symm.toMonoidHom).range = ψ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ee.symm.surjective,
      Subgroup.map_top]
  have hker' : ψ'.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)) := by
    intro x hx
    have hx' : ee.symm x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : ψ' x = 1 := hx
      simpa only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h1
    have hcent : ee.symm x ∈ Subgroup.center (Su K 2 f (m + 1)) := hker hx'
    have hxcent : ∀ y : ↥(unitarySU 2 f K (m + 1)), y * x = x * y := by
      intro y
      apply ee.symm.injective
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp hcent) (ee.symm y)
    rw [Subgroup.mem_center_iff]
    exact hxcent
  have hdiag : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).IsDiag := by
    obtain ⟨d, hd⟩ := hg
    intro i j hij
    rw [hd, Matrix.diagonal_apply_ne _ hij]
  obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag hdiag
  let δ : G → Fin (m + 1) → Kˣ := fun _ => σ
  have hgU : g ∈ LargeEvenGUSet (Fin (m + 1)) K (2 ^ f) :=
    nbcb_ggIsUnitaryMat_mem_GUSet he.1
  have hgnorm : g ∈ Subgroup.normalizer
      ((unitarySU 2 f K (m + 1) : Set (GL (Fin (m + 1)) K))) :=
    TableBUE.gu_subset_normalizer hUF hgU
  have hdiagHomNorm : CFSG.SectionRank.OddCover.diagHom (m + 1) σ ∈
      Subgroup.normalizer ((unitarySU 2 f K (m + 1) : Set (GL (Fin (m + 1)) K))) := by
    rw [← hσ]
    exact hgnorm
  have hpair : (e, CFSG.SectionRank.OddCover.diagHom (m + 1) σ) ∈ SUTorus.suPairs ψ' := by
    refine (SUTorus.mem_suPairs).mpr ⟨hdiagHomNorm, ?_⟩
    intro u v huv
    obtain ⟨y, hy1, hy2⟩ := he.2 (ee.symm u)
    have hyv : y = ee.symm v := by
      apply Subtype.ext
      rw [hy1, hσ]
      change (CFSG.SectionRank.OddCover.diagHom (m + 1) σ : GL (Fin (m + 1)) K) *
          (u : GL (Fin (m + 1)) K) *
          (CFSG.SectionRank.OddCover.diagHom (m + 1) σ : GL (Fin (m + 1)) K)⁻¹ =
        (v : GL (Fin (m + 1)) K)
      rw [← huv]
    change e * ψ (ee.symm u) * e⁻¹ = ψ (ee.symm v)
    rw [hy2, hyv]
  have hδ : ∀ b ∈ ({e} : Set G),
      (b, CFSG.SectionRank.OddCover.diagHom (m + 1) (δ b)) ∈ SUTorus.suPairs ψ' := by
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact hpair
  have hJ' : CFSG.Assembly.IsComponentOf J
      (ψ'.range ⊓ Subgroup.centralizer ({e} : Set G)) := by
    have h := hJ
    rwa [← hrange] at h
  obtain ⟨i, hJI⟩ := SUTorus.exists_le_map_blockSU (f := f) (m := m) (G := G)
    (ψ := ψ') (S := ({e} : Set G)) (δ := δ) (J := J) hUF hp hpq hker' hδ hJ'
  let I : Finset (Fin (m + 1)) := LinTorus.diagClass ({e} : Set G) δ i
  have hJI' : J ≤ (TableBUE.blockSU (K := K) (n := f) I).map ψ' := hJI
  have hI2 : 2 ≤ I.card := by
    by_contra hlt
    push Not at hlt
    have h1 : 1 ≤ I.card :=
      Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass _ δ i⟩
    obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp (show I.card = 1 by omega)
    rw [hi0, SUTorus.blockSU_singleton hUF, Subgroup.map_bot] at hJI'
    exact commutator_ne_bot_of_isQuasisimple hJ.2.2
      (by rw [le_bot_iff.mp hJI', Subgroup.commutator_bot_left])
  have hKle : (TableBUE.blockSU (K := K) (n := f) I).map ψ' ≤
      Subgroup.centralizer ({e} : Set G) := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconst : ∀ p ∈ I, ∀ q ∈ I, σ p = σ q :=
      fun p hp q hq => LinTorus.eq_of_mem_diagClass hp hq (Set.mem_singleton e)
    have hcomm : (g : GL (Fin (m + 1)) K) * (w : GL (Fin (m + 1)) K) =
        (w : GL (Fin (m + 1)) K) * g := by
      rw [hσ]
      exact TableBUE.diagHom_mul_comm_of_isBlockOn hconst hw
    obtain ⟨y, hy1, hy2⟩ := he.2 (ee.symm w)
    have hyw : y = ee.symm w := by
      apply Subtype.ext
      rw [hy1]
      change (g : GL (Fin (m + 1)) K) *
          ((ee.symm w : Su K 2 f (m + 1)) : GL (Fin (m + 1)) K) * g⁻¹ =
        ((ee.symm w : Su K 2 f (m + 1)) : GL (Fin (m + 1)) K)
      have hcoe : ((ee.symm w : Su K 2 f (m + 1)) : GL (Fin (m + 1)) K) =
          (w : GL (Fin (m + 1)) K) := rfl
      rw [hcoe]
      calc g * (w : GL (Fin (m + 1)) K) * g⁻¹ =
          (w : GL (Fin (m + 1)) K) * g * g⁻¹ := by rw [hcomm]
        _ = (w : GL (Fin (m + 1)) K) := by group
    have hconj : e * ψ' w * e⁻¹ = ψ' w := by
      change e * ψ (ee.symm w) * e⁻¹ = ψ (ee.symm w)
      rw [hy2, hyw]
    have hcommE : e * ψ' w = ψ' w * e := by
      calc e * ψ' w = (e * ψ' w * e⁻¹) * e := by group
        _ = ψ' w * e := by rw [hconj]
    exact hcommE.symm
  have ha4 : f = 1 → 4 ≤ I.card := by
    intro hf1'
    subst f
    by_contra hlt
    have hI1 : 1 ≤ I.card := by omega
    have hI3 : I.card ≤ 3 := by omega
    have hsol : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) I).map ψ') :=
      WitSU.isSolvable_map_blockSU_two_one hUF ψ' hI1 hI3
    haveI : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) I).map ψ') := hsol
    have hsolJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJI')
        (fun x y hxy => Subtype.ext (congrArg
          (fun z : ↥((TableBUE.blockSU (K := K) (n := 1) I).map ψ') => (z : G)) hxy))
    exact nbcb_not_solvable_of_isQuasisimple hJ.2.2 hsolJ
  have hKq : CFSG.Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := K) (n := f) I).map ψ') := by
    by_cases hf2 : 2 ≤ f
    · exact SURepair.isQuasisimple_map_blockSU_of_two_le hUF hf2 hker' hI2
    · have hf1' : f = 1 := by omega
      have h4 : 4 ≤ I.card := ha4 hf1'
      have hblock : CFSG.IsQuasisimple ↥(TableBUE.blockSU (K := K) (n := f) I) :=
        TableBUE.isQuasisimple_blockSU I hUF hUF.card_eq_sq (by omega)
          (by intro h'; exact absurd (Prod.mk.inj h').1 (by omega))
      exact SURepair.isQuasisimple_map_of_isQuasisimple hker' hblock
  have hKleH : (TableBUE.blockSU (K := K) (n := f) I).map ψ' ≤
      ψ'.range ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_inf (Subgroup.map_le_range ψ' _) hKle
  have hLeq : J = (TableBUE.blockSU (K := K) (n := f) I).map ψ' :=
    LinTypeAk.eq_of_isComponentOf_of_le hJ' hJI' hKleH hKq
  have hanej : I.card = m + 1 → ψ.range ≤ Subgroup.centralizer ({e} : Set G) := by
    intro hcard
    have hIuniv : I = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      exact hcard
    have htop : (TableBUE.blockSU (K := K) (n := f) I).map ψ' = ψ'.range := by
      rw [hIuniv, SUTorus.blockSU_univ, Subgroup.map_top]
    have hJC : J ≤ Subgroup.centralizer ({e} : Set G) := hJ.1.trans inf_le_right
    have hJr : ψ'.range = J := by
      rw [hLeq]
      exact htop.symm
    rw [← hrange, hJr]
    exact hJC
  have hQ : CFSG.IsQuasisimple ↥(TableBUE.blockSU (K := K) (n := f) I) := by
    by_cases hf2 : 2 ≤ f
    · exact SURepair.isQuasisimple_blockSU_of_two_le hUF hf2 hI2
    · have h4 : 4 ≤ I.card := ha4 (by omega)
      exact TableBUE.isQuasisimple_blockSU I hUF hUF.card_eq_sq (by omega)
        (by intro h'; exact absurd (Prod.mk.inj h').1 (by omega))
  let φ : ↥(TableBUE.blockSU (K := K) (n := f) I) →* ↥J :=
    (ψ'.comp (TableBUE.blockSU (K := K) (n := f) I).subtype).codRestrict J
      (fun q => by
        rw [hLeq]
        exact Subgroup.mem_map.mpr ⟨q, q.2, rfl⟩)
  have hsurj : Function.Surjective φ := by
    intro z
    have hz : (z : G) ∈ (TableBUE.blockSU (K := K) (n := f) I).map ψ' := by
      rw [← hLeq]
      exact z.2
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  have hkerφ : φ.ker ≤ Subgroup.center ↥(TableBUE.blockSU (K := K) (n := f) I) := by
    intro q hq
    have hq1 : ψ' (q : ↥(unitarySU 2 f K (m + 1))) = 1 := by
      have h1 : ((φ q : ↥J) : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
      exact h1
    have hcent : (q : ↥(unitarySU 2 f K (m + 1))) ∈
        Subgroup.center ↥(unitarySU 2 f K (m + 1)) :=
      hker' (MonoidHom.mem_ker.mpr hq1)
    rw [Subgroup.mem_center_iff] at hcent ⊢
    intro g
    apply Subtype.ext
    exact hcent (g : ↥(unitarySU 2 f K (m + 1)))
  obtain ⟨hcen⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective
    hQ φ hsurj hkerφ
  let eeB : Su K 2 f I.card ≃* ↥(TableBUE.blockSU (K := K) (n := f) I) :=
    (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK I.card)).trans
      (TableBUE.blockSUEquiv (K := K) (n := f) I hUF)
  exact ⟨I.card, hI2, by simpa using Finset.card_le_univ I, ha4, hanej,
    ⟨((QuotientGroup.congr (Subgroup.center (Su K 2 f I.card))
      (Subgroup.center ↥(TableBUE.blockSU (K := K) (n := f) I)) eeB
      (Subgroup.map_center_eq eeB)).trans hcen).symm⟩⟩

end CFSG.StandardType

end
