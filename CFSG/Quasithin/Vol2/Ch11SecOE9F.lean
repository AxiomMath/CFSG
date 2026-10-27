module

public import CFSG.Quasithin.Vol2.Ch11SecOE9E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParSp4
public import CFSG.Quasithin.Vol2.Ch11SecOE7M
public import CFSG.Quasithin.Vol2.Ch11SecOE7N
public import CFSG.Quasithin.Vol2.Ch11SecOE9D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj projUnipotent)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkN blkN_surjective blkN_ker_isPGroup)

variable {G : Type} [Group G] [Finite G]

open Sp4 in
theorem nParam_le_of_isPSp4_of_untwisted {T : Subgroup G} {n : ℕ}
    (hS : IsPSp4 2 n ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hun : ¬ E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
      (T ⊓ CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := two_le_of_isPSp4 hS
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set L := CFSG.generalizedFitting G with hLdef
  have hLn : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hTsyl : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_projUnipotent
    (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P
  have hU₀' := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal
      (⟨hTsyl.1, hTsyl.2.1, hTsyl.2.2⟩ : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
    refine ⟨le_top, hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL.1).symm, ?_⟩
    show ¬ 2 ∣ ((T ⊓ L).subgroupOf L).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hTL.2.2
  obtain ⟨k, -, hk⟩ :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₀').exists_mem_conj
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : ((projUnipotent 2 K).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom =
      (T ⊓ L).subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have hpkg := ((CFSG.Quasithin.Rk2.rank2Pkg_sp4 hK hn).map e.symm).map (MulAut.conj k)
  rw [hconj] at hpkg
  set Pj : Fin 2 → Subgroup ↥L := fun j =>
    (((Q2 K j).map (proj 2 K)).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom
    with hPjdef
  have := hLn
  have hTP : ∀ j, T ≤ Subgroup.normalizer (((Pj j).map L.subtype : Subgroup G) : Set G) :=
    fun j => le_normalizer_parabolic_of_not_isDiagramNontrivial hTsyl hpkg.res hpkg.norm hun j
  set ι : ↥(StatedSp 2 K) →* G := L.subtype.comp ((MulAut.conj k).toMonoidHom.comp
    (e.symm.toMonoidHom.comp (proj 2 K))) with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp ((MulAut.conj k).injective.comp
    (e.symm.injective.comp CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo))
  set X : Fin 2 → Subgroup G := fun j => (perfectCore (Q2 K j)).map ι with hXdef
  have hX : ∀ j, X j = perfectCore ((Pj j).map L.subtype) := by
    intro j
    show (perfectCore (Q2 K j)).map ι = _
    rw [map_perfectCore, hPjdef]
    simp only [Subgroup.map_map]
    rfl
  have hTX : ∀ j, T ≤ Subgroup.normalizer (X j : Set G) := fun j => by
    rw [hX j]
    exact le_normalizer_perfectCore (hTP j)
  have hφ : ∀ j, ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (φ : ↥(X j) →* Matrix.SpecialLinearGroup (Fin 2) F),
      Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧ Nat.card F = 2 ^ n := by
    intro j
    set eq := (perfectCore (Q2 K j)).equivMapOfInjective ι hι
    refine ⟨K, inferInstance, inferInstance, inferInstance, (blkN j).comp eq.symm.toMonoidHom,
      (blkN_surjective (exists_finset_card_four' h4) j).comp eq.symm.surjective,
      isPGroup_ker_comp (blkN j) eq.symm (blkN_ker_isPGroup ⟨n, hK⟩ j), hK⟩
  have hgen : (⨆ j, X j) ⊔ T = ⊤ := by
    have h2 := congrArg (Subgroup.map L.subtype) hpkg.sup_perfectCore_eq_top
    rw [Subgroup.map_sup, Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, map_perfectCore, map_perfectCore, ← hX 0, ← hX 1] at h2
    rw [eq_top_iff, ← hFT, ← h2]
    refine sup_le (sup_le (sup_le ((le_iSup X 0).trans le_sup_left)
      ((le_iSup X 1).trans le_sup_left)) ((inf_le_left.trans inf_le_left).trans le_sup_right))
      le_sup_right
  exact (E1.nParam_le_iff (by omega)).mpr ((E1.inE_iff_inEFor hTsyl).mpr
    (inEFor_top_of_quot_sl2_family X hTsyl hn hTX hφ hgen))

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
