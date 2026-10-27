module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Class
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Cover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Marking
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Setup
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Outer
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.LineU CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

theorem ggLAut_eq_projConj_of_actsAs {G : Type} [Group G] {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    {φ : ↥(unitarySU 2 n K 6) →* G} (hφL : ∀ s, φ s ∈ L)
    (hψ : ∀ (s : ↥(unitarySU 2 n K 6)) (h : φ s ∈ L),
      θ ((⟨φ s, h⟩ : ↥L) : L ⧸ Subgroup.center L) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) {M : GL (Fin 6) K}
    (hM : ActsAs φ b M)
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) :
    ggLAut L θ ⟨b, hb⟩ = TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ := by
  obtain ⟨hMN', hact⟩ := hM
  ext r
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective r
  have h1 : (LargeEvenProjMk (unitarySU 2 n K 6) s) =
      θ ((⟨φ s, hφL s⟩ : ↥L) : L ⧸ Subgroup.center L) := (hψ s (hφL s)).symm
  have h2 : ((L.normalizerMonoidHom ⟨b, hb⟩ ⟨φ s, hφL s⟩ : ↥L) : G) = φ (conjN M hMN' s) := by
    rw [normalizerMonoidHom_coe]
    exact hact s
  have h3 : (L.normalizerMonoidHom ⟨b, hb⟩ ⟨φ s, hφL s⟩ : ↥L) =
      ⟨φ (conjN M hMN' s), hφL _⟩ := Subtype.ext h2
  have hL1 : ggLAut L θ ⟨b, hb⟩ (LargeEvenProjMk (unitarySU 2 n K 6) s) =
      LargeEvenProjMk (unitarySU 2 n K 6) (conjN M hMN' s) := by
    conv_lhs => rw [h1]
    rw [ggLAut_apply, h3, hψ _ (hφL _)]
  have hR1 : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩
      (LargeEvenProjMk (unitarySU 2 n K 6) s) =
      LargeEvenProjMk (unitarySU 2 n K 6) (conjN M hMN s) := projConj_mk_eq M hMN s
  exact hL1.trans hR1.symm

theorem all_inner_of_marking
    [Finite K] {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hlt : Nat.card Bs < 3 ^ 5)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1) :
    ∃ φ : ↥(unitarySU 2 n K 6) →* G, (∀ s, φ s ∈ L) ∧ (∀ l ∈ L, ∃ s, φ s = l) ∧
      (∀ s, (∀ l ∈ L, φ s * l = l * φ s) ↔ LargeEvenProjMk (unitarySU 2 n K 6) s = 1) ∧
      (∀ (s : ↥(unitarySU 2 n K 6)) (h : φ s ∈ L),
        θ ((⟨φ s, h⟩ : ↥L) : L ⧸ Subgroup.center L) = LargeEvenProjMk (unitarySU 2 n K 6) s) ∧
      (∀ z : ↥L, z ∈ Subgroup.center ↥L → z = 1) ∧
      ∀ b ∈ Bs, ∃ M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n), ActsAs φ b M ∧ IsInner n M := by
  classical
  have hKd : UnitaryFieldData 2 n K := CFSG.StandardType.TableBU.unitaryFieldData_of_card hK
    (by omega)
  have hcov : UnitaryCoverAt n 6 K :=
    unitaryUniversalCover_holds n 6 K hK (by norm_num) (by
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega)
  obtain ⟨φ, hφL, hφs, hφZ, hψ, hact⟩ := exists_cover_actsAs hKd hcov hL θ hBN hBI
  have hZ1 : ∀ z : ↥L, z ∈ Subgroup.center ↥L → z = 1 := by
    intro z hz'
    obtain ⟨s, hs⟩ := hφs z z.2
    have hcomm : ∀ l ∈ L, φ s * l = l * φ s := by
      intro l hl
      rw [hs]
      have := Subgroup.mem_center_iff.mp hz' ⟨l, hl⟩
      exact congrArg Subtype.val this.symm
    obtain ⟨c, hc3, hc⟩ := exists_scalar_of_proj_eq_one hKd hpq ((hφZ s).mp hcomm)
    have hφ3 : (φ s) ^ 3 = 1 := by
      rw [← map_pow]
      have : s ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
        rfl
      rw [this, map_one]
    have := hz (φ s) (hφL s) hcomm hφ3
    exact Subtype.ext (by rw [← hs]; exact this)
  refine ⟨φ, hφL, hφs, hφZ, hψ, hZ1, fun b hb => ?_⟩
  obtain ⟨M, hMgu, hMact⟩ := hact b hb
  refine ⟨M, hMgu, hMact, ?_⟩
  by_contra hMn
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨-, hrank⟩ := config_card_rank hcfg hlt
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) := fun z => ⟨0, by
    have := hZ1 z z.2
    exact Subtype.ext (by simpa using congrArg Subtype.val this)⟩
  obtain ⟨u, hu⟩ := CFSG.StandardType.TableBU63.exists_unitary_of_gu hKd hMgu
  have hgn : ¬ IsInner n (GeneralLinearGroup.scalar (Fin 6) u * M) :=
    fun h => hMn ((isInner_scalar_mul_iff u M).mp h)
  have hgN : GeneralLinearGroup.scalar (Fin 6) u * M ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer (d := 6) hKd
      (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hu)
  have hac : ggLAut L θ ⟨b, hBN hb⟩ = TableB.projConj (unitarySU 2 n K 6)
      ⟨GeneralLinearGroup.scalar (Fin 6) u * M, hgN⟩ := by
    have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
      TableBUE.gu_subset_normalizer (d := 6) hKd hMgu
    rw [ggLAut_eq_projConj_of_actsAs θ hφL hψ (hBN hb) hMact hMN]
    have hu' : GeneralLinearGroup.scalar (Fin 6) u ∈ LargeEvenScalars (Fin 6) K := ⟨u, rfl⟩
    have : (⟨GeneralLinearGroup.scalar (Fin 6) u * M, hgN⟩ :
        ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) =
        ⟨GeneralLinearGroup.scalar (Fin 6) u, TableB.scalar_mem_normalizer _ hu'⟩ * ⟨M, hMN⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, TableB.projConj_of_scalar _ hu', one_mul]
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hxC : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)).symm
  have hxL : x ∉ L := fun hxL => hS.2.2.1 (hz x hxL hxC hx3)
  have hxa : x * b = b * x := CFSG.StandardType.TableB.IsElemAbelian.comm hBs hxBs hb
  have h5 := five_le_twoLocalRank_of_outer hKd hpq hL θ hZ2 (hBN hb) (hBs.2 b hb) hu hgn hac hx3
    hS.2.2.1 hxC hxa hxL
  omega

end CFSG.StandardType.Line63.H5

end
