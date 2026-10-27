module

public import CFSG.Quasithin.Vol2.Ch11SecOE7M
public import CFSG.Quasithin.Vol2.Ch11SecOE7N
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.Quasithin.EmptyFaithful.S153MDiag
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_levi_proj3 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (ι : projectiveSL 3 K →* G)
    (hι : Function.Injective ι) (j : Fin 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (φ : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι) →* SL(2, F)),
      Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧ Nat.card F = 2 ^ n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set eN := perfectCoreMapEquiv (proj 3 K) (Q3 K j) (Rk2.proj3_injOn_perfectCore j) with heN
  set eX := (perfectCore ((Q3 K j).map (proj 3 K))).equivMapOfInjective ι hι with heX
  set φ : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι) →* SL(2, K) :=
    (blk3 j).comp (eN.symm.toMonoidHom.comp eX.symm.toMonoidHom) with hφ
  refine ⟨K, inferInstance, inferInstance, inferInstance, φ, ?_, ?_, hK⟩
  · exact (blk3_surjective hK4 j).comp (eN.symm.surjective.comp eX.symm.surjective)
  · intro x
    have hx : eN.symm (eX.symm x) ∈ (blk3 (K := K) j).ker := x.2
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup ⟨n, hK⟩ j ⟨_, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (eN.symm (eX.symm x)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : eN.symm (eX.symm ((x : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι)) ^ 2 ^ k)) =
        1 := by rw [map_pow, map_pow]; exact h1
    have h3 : (x : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι)) ^ 2 ^ k = 1 := by
      have := congrArg (fun y => eX (eN y)) h2
      simpa using this
    exact h3

theorem nParam_le_of_psl3_of_untwisted {L T : Subgroup G} [hLn : L.Normal]
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* projectiveSL 3 K)
    (hun : ¬ E2.IsDiagramNontrivial T L (T ⊓ L)) : E1.nParam (⊤ : Subgroup G) ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ : Fin 2 → Subgroup (projectiveSL 3 K) := fun j => (Q3 K j).map (proj 3 K) with hP₀
  have pkg₀ := Rk2.rank2Pkg_proj3 hK hn
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hS ▸ isSylowTwoOf_top_of_sylow S
  set U := (T ⊓ L).subgroupOf L with hUdef
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hU : IsSylowTwoOf U ⊤ := S153M.isSylowTwoOf_subgroupOf_top' hTL
  have hU₁ := B113Lie.isSylowTwoOf_map_top e.symm hU₀
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : ((projUnitriangular 3 K).map e.symm.toMonoidHom).map
      (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  obtain ⟨α, hα⟩ : ∃ α : projectiveSL 3 K ≃* ↥L, α = e.symm.trans (MulAut.conj k) := ⟨_, rfl⟩
  have hPL : ∀ j, ((P₀ j).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom =
      (P₀ j).map α.toMonoidHom := fun j => by
    rw [Subgroup.map_map, hα]
    rfl
  have pkg : Rk2.Rank2Pkg ↥L U (fun j => (P₀ j).map α.toMonoidHom) := by
    have h1 := (pkg₀.map e.symm).map (MulAut.conj k)
    rw [show (unitriangular 3 K).map (proj 3 K) = projUnitriangular 3 K from rfl, hconj] at h1
    convert h1 using 1
    funext j
    exact (hPL j).symm
  set ι : projectiveSL 3 K →* G := L.subtype.comp α.toMonoidHom with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp α.injective
  set X : Fin 2 → Subgroup G := fun j => (perfectCore (P₀ j)).map ι with hX
  have hXc : ∀ j, X j = (perfectCore ((P₀ j).map α.toMonoidHom)).map L.subtype := fun j => by
    rw [← map_perfectCore, Subgroup.map_map]
  have hTX : ∀ j, T ≤ Subgroup.normalizer (X j : Set G) := by
    intro j
    have h1 := le_normalizer_parabolic_of_not_isDiagramNontrivial hT pkg.res pkg.norm hun j
    have h2 : X j = perfectCore (((P₀ j).map α.toMonoidHom).map L.subtype) := by
      rw [hXc, map_perfectCore]
    rw [h2]
    exact h1.trans (normalizer_le_normalizer_perfectCore _)
  have hgen : (⨆ j, X j) ⊔ T = ⊤ := by
    have h1 := pkg.sup_perfectCore_eq_top
    have h2 := congrArg (Subgroup.map L.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_sup, ← hXc, ← hXc, hUdef,
      Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      inf_assoc, inf_idem] at h2
    have hX01 : X 0 ⊔ X 1 ≤ ⨆ j, X j := sup_le (le_iSup X 0) (le_iSup X 1)
    have hLle : L ≤ (⨆ j, X j) ⊔ T :=
      calc L = X 0 ⊔ X 1 ⊔ (T ⊓ L) := h2.symm
        _ ≤ (⨆ j, X j) ⊔ T := sup_le (hX01.trans le_sup_left) (inf_le_left.trans le_sup_right)
    exact eq_top_iff.mpr (hLT.symm.trans_le (sup_le hLle le_sup_right))
  have h := inEFor_top_of_quot_sl2_family X hT hn hTX
    (fun j => exists_levi_proj3 hK hn ι hι j) hgen
  exact (E1.nParam_le_iff (by omega)).mpr ((E1.inE_iff_inEFor hT).mpr h)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
