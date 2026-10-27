module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeFieldBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeReduce
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace TableBU63

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  TableBUD TableBUE TableBUR TableBUDT

section Layer

variable {G : Type*} [Group G]

theorem layer_eq_of_derived_le {H D : Subgroup G} (hD : CFSG.IsQuasisimple D) (hDH : D ≤ H)
    (hder : ⁅⁅H, H⁆, ⁅H, H⁆⁆ ≤ D) : LargeEvenLayer H = D ∧ IsComponentOf D H := by
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hD.1
  have hDeq : D = ⁅⁅H, H⁆, ⁅H, H⁆⁆ := by
    refine le_antisymm ?_ hder
    calc D = ⁅⁅D, D⁆, ⁅D, D⁆⁆ := by rw [hDperf, hDperf]
      _ ≤ ⁅⁅H, H⁆, ⁅H, H⁆⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono hDH hDH)
          (Subgroup.commutator_mono hDH hDH)
  have hconj : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    intro h hh d hd
    have hHc : H.map (MulAut.conj h).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      exact H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)
    have hle : (⁅⁅H, H⁆, ⁅H, H⁆⁆).map (MulAut.conj h).toMonoidHom ≤ ⁅⁅H, H⁆, ⁅H, H⁆⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
      exact Subgroup.commutator_mono (Subgroup.commutator_mono hHc hHc)
        (Subgroup.commutator_mono hHc hHc)
    rw [hDeq] at hd ⊢
    exact hle ⟨d, hd, rfl⟩
  have hcompD : IsComponentOf D H := by
    refine ⟨hDH, IsSubnormal.step hDH ?_ (IsSubnormal.refl H),
      (TableBSymp.isQuasisimple_iff _).mpr hD⟩
    rw [Subgroup.normal_subgroupOf_iff hDH]
    intro d g hd hg
    exact hconj g hg d hd
  have hle : ∀ K' : Subgroup G, IsComponentOf K' H → K' ≤ D := by
    intro K' hK'
    have hK'q : CFSG.IsQuasisimple K' := (TableBSymp.isQuasisimple_iff _).mp hK'.2.2
    have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 hK'q.1
    calc K' = ⁅⁅K', K'⁆, ⁅K', K'⁆⁆ := by rw [hK'perf, hK'perf]
      _ ≤ ⁅⁅H, H⁆, ⁅H, H⁆⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono hK'.1 hK'.1)
          (Subgroup.commutator_mono hK'.1 hK'.1)
      _ ≤ D := hder
  exact ⟨le_antisymm (sSup_le fun K' hK' => hle K' hK') (le_sSup hcompD), hcompD⟩

end Layer

theorem fieldTypeEndNodeInput_holds : FieldTypeEndNodeInput := by
  intro n K _ _ hK hpq Ab hAb hAbI M hMN l hMu hM3 hl hMA
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num at hpq
    · exact hn
  have h := TableBU.unitaryFieldData_of_card hK hn
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hN := gu_subset_normalizer (d := 6) h
  set NN := Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) with hNN
  have hMuU : M ∈ primeFormUnitary h (idGram K 6) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [← map_pow_eq_map_bar h]
    exact hMu
  obtain ⟨J, hJq, hJdet, hJM, hJcomm, hJcent⟩ :=
    exists_fieldBlock h hpq (M := ⟨M, hMuU⟩) hM3 hl
  set π := LargeEvenProjMk (unitarySU 2 n K 6) with hπ
  set a := TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ with ha
  have hJSU : ∀ g ∈ J, (g : GL (Fin 6) K) ∈ unitarySU 2 n K 6 := fun g hg =>
    (mem_unitarySU_iff h).mpr ⟨hJdet g hg, by
      have := mem_primeFormUnitary.mp g.2
      simpa only [idGram, Units.val_one, Matrix.mul_one] using this⟩
  set JG := J.map (primeFormUnitary h (idGram K 6)).subtype with hJG
  have hJGq : CFSG.IsQuasisimple JG := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (J.equivMapOfInjective _ (Subgroup.subtype_injective _)) hJq
  have hJGle : JG ≤ unitarySU 2 n K 6 := by
    rintro _ ⟨g, hg, rfl⟩
    exact hJSU g hg
  set JS := JG.comap (unitarySU 2 n K 6).subtype with hJS
  have hJSmap : JS.map (unitarySU 2 n K 6).subtype = JG := by
    rw [hJS, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_of_le_right hJGle
  have hJSq : CFSG.IsQuasisimple JS := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((JS.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr hJSmap)).symm hJGq
  have hJScomm : ∀ s ∈ JS, (s : GL (Fin 6) K) * M = M * s := by
    rintro s ⟨g, hg, hgs⟩
    have hgs' : (g : GL (Fin 6) K) = (s : GL (Fin 6) K) := hgs
    have e := congrArg Subtype.val (hJM g hg)
    rw [← hgs']
    exact e
  set D := JS.map π with hD
  have hDq : CFSG.IsQuasisimple D := by
    have hker : (π.comp JS.subtype).ker ≤ Subgroup.center JS := by
      intro s hs
      have hs' : (s : ↥(unitarySU 2 n K 6)) ∈ Subgroup.center ↥(unitarySU 2 n K 6) :=
        ker_projMk_le_center hs
      rw [Subgroup.mem_center_iff] at hs' ⊢
      intro s'
      exact Subtype.ext (hs' s')
    have hR := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hJSq (π.comp JS.subtype) hker
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hR
  set H := ggFix a with hH
  set Nf := H.comap π with hNf
  have hHN : Nf.map π = H := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) H
  set αM := (unitarySU 2 n K 6).normalizerMonoidHom ⟨M, hMN⟩ with hαM
  have hαM_apply : ∀ s : ↥(unitarySU 2 n K 6), ((αM s : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) =
      M * s * M⁻¹ := fun s => rfl
  have hfixM : ∀ s : ↥(unitarySU 2 n K 6), s ∈ ggFix αM ↔ (s : GL (Fin 6) K) * M = M * s := by
    intro s
    rw [mem_ggFix]
    constructor
    · intro hs
      have e : M * (s : GL (Fin 6) K) * M⁻¹ = s := by
        rw [← hαM_apply]
        exact congrArg Subtype.val hs
      calc (s : GL (Fin 6) K) * M = M * s * M⁻¹ * M := by rw [e]
        _ = M * s := by group
    · intro hs
      apply Subtype.ext
      rw [hαM_apply, ← hs]
      group
  have hNsc : ∀ s ∈ Nf, αM s * s⁻¹ ∈ Subgroup.center ↥(unitarySU 2 n K 6) := by
    intro s hs
    have hs' : a (π s) = π s := hs
    rw [ha, projConj_mk_coe] at hs'
    apply ker_projMk_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact mul_inv_eq_one.mpr hs'
  have hNN' : ⁅Nf, Nf⁆ ≤ ggFix αM := commutator_le_ggFix αM hNsc
  have hCC : ⁅ggFix αM, ggFix αM⁆ ≤ JS := by
    rw [Subgroup.commutator_le]
    intro c hc c' hc'
    have hcM := (hfixM c).mp hc
    have hc'M := (hfixM c').mp hc'
    have hcu : (c : GL (Fin 6) K) ∈ primeFormUnitary h (idGram K 6) :=
      unitarySU_le_primeFormUnitary h c.2
    have hc'u : (c' : GL (Fin 6) K) ∈ primeFormUnitary h (idGram K 6) :=
      unitarySU_le_primeFormUnitary h c'.2
    have hmem := hJcomm ⟨c, hcu⟩ ⟨c', hc'u⟩ (Subtype.ext hcM) (Subtype.ext hc'M)
    exact ⟨_, hmem, rfl⟩
  have hder : ⁅⁅H, H⁆, ⁅H, H⁆⁆ ≤ D := by
    rw [← hHN, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hD]
    exact Subgroup.map_mono ((Subgroup.commutator_mono hNN' hNN').trans hCC)
  have hDH : D ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    show a (π s) = π s
    rw [ha, projConj_mk_coe]
    congr 1
    exact (hfixM s).mpr (hJScomm s hs)
  obtain ⟨hlayer, hcomp⟩ := layer_eq_of_derived_le hDq hDH hder
  refine ⟨a, hMA, ?_, hlayer ▸ hcomp, fun a' ha' => ?_⟩
  ·
    intro ha1
    obtain ⟨c, hc⟩ := mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq ha1
    apply hl c
    have hc' : GeneralLinearGroup.scalar (Fin 6) c = M := hc
    have e := hM3
    rw [← hc', ← map_pow] at e
    exact TypeA.PGLTor.scalar_injective e
  show (∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a
  rw [← hH, hlayer]
  constructor
  · intro hfix
    obtain ⟨M', hM'gu, hM'eq⟩ := TableB.exists_eq_projConj hN (hAbI a' ha')
    obtain ⟨u, hu⟩ := exists_unitary_of_gu h hM'gu
    set Y := GeneralLinearGroup.scalar (Fin 6) u * M' with hY
    have hsN : GeneralLinearGroup.scalar (Fin 6) u ∈ NN :=
      TableB.scalar_mem_normalizer _ ⟨u, rfl⟩
    have hYN : Y ∈ NN := NN.mul_mem hsN (hN hM'gu)
    have hYa : a' = TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩ := by
      have e : (⟨Y, hYN⟩ : NN) = ⟨_, hsN⟩ * ⟨M', hN hM'gu⟩ := rfl
      rw [e, map_mul, TableB.projConj_of_scalar _ ⟨u, rfl⟩, one_mul]
      exact hM'eq
    have hYJ : ∀ g ∈ J, (⟨Y, hu⟩ : primeFormUnitary h (idGram K 6)) * g = g * ⟨Y, hu⟩ := by
      set αY := (unitarySU 2 n K 6).normalizerMonoidHom ⟨Y, hYN⟩ with hαY
      have hperf : Group.IsPerfect JS := hJSq.1
      have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq π ker_projMk_le_center
        hperf (αY.toMonoidHom.comp JS.subtype) JS.subtype (fun w => by
          have hw : π w ∈ D := ⟨w, w.2, rfl⟩
          have e : TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩ (π w) = π w := by
            have e0 := hfix (π w) hw
            rw [hYa] at e0
            exact e0
          rw [projConj_mk_coe] at e
          exact e)
      intro g hg
      have e := congrArg Subtype.val (key ⟨⟨g, hJSU g hg⟩, ⟨g, hg, rfl⟩⟩)
      change Y * (g : GL (Fin 6) K) * Y⁻¹ = g at e
      apply Subtype.ext
      change Y * (g : GL (Fin 6) K) = g * Y
      calc Y * (g : GL (Fin 6) K) = Y * g * Y⁻¹ * Y := by group
        _ = g * Y := by rw [e]
    obtain ⟨t, ht⟩ : ∃ t : Kˣ, Y * M = GeneralLinearGroup.scalar (Fin 6) t * (M * Y) := by
      have hcomm : TableB.projConj (unitarySU 2 n K 6) (⟨Y, hYN⟩ * ⟨M, hMN⟩) =
          TableB.projConj (unitarySU 2 n K 6) (⟨M, hMN⟩ * ⟨Y, hYN⟩) := by
        rw [map_mul, map_mul]
        have e := TableB.IsElemAbelian.comm hAb ha' hMA
        rw [hYa] at e
        exact e
      have h1 : TableB.projConj (unitarySU 2 n K 6) ((⟨Y, hYN⟩ * ⟨M, hMN⟩) *
          (⟨M, hMN⟩ * ⟨Y, hYN⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, hcomm, mul_inv_cancel]
      obtain ⟨t, ht⟩ := mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq h1
      refine ⟨t, ?_⟩
      have e : (((⟨Y, hYN⟩ * ⟨M, hMN⟩) * (⟨M, hMN⟩ * ⟨Y, hYN⟩)⁻¹ : NN) : GL (Fin 6) K) =
          Y * M * (M * Y)⁻¹ := rfl
      rw [e] at ht
      calc Y * M = Y * M * (M * Y)⁻¹ * (M * Y) := by group
        _ = GeneralLinearGroup.scalar (Fin 6) t * (M * Y) := by rw [← ht]
    obtain ⟨k, hk⟩ : ∃ k : Kˣ, Y ^ 3 = GeneralLinearGroup.scalar (Fin 6) k := by
      have h3 : (TableB.projConj (unitarySU 2 n K 6) ⟨Y, hYN⟩) ^ 3 = 1 := by
        have e := hAb.2 a' ha'
        rw [hYa] at e
        exact e
      rw [← map_pow] at h3
      obtain ⟨k, hk⟩ := mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq h3
      exact ⟨k, hk.symm⟩
    obtain ⟨d, j, hdj⟩ := hJcent ⟨Y, hu⟩ hYJ t ht ⟨k, hk⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), ?_⟩
    show a ^ (j : ℤ) = a'
    have hdN : GeneralLinearGroup.scalar (Fin 6) d ∈ NN := TableB.scalar_mem_normalizer _ ⟨d, rfl⟩
    have e : (⟨Y, hYN⟩ : NN) = ⟨_, hdN⟩ * ⟨M, hMN⟩ ^ j := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
      exact hdj
    rw [zpow_natCast, hYa, e, map_mul, TableB.projConj_of_scalar _ ⟨d, rfl⟩, one_mul, map_pow]
  · intro hmem j hj
    exact apply_eq_of_mem_zpowers hmem (mem_ggFix.mp (hDH hj))

end TableBU63

end CFSG.StandardType
