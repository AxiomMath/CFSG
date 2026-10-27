module

public import CFSG.Quasithin.Vol2.Ch11SecOE9G
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParSp4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem le_normalizer_dInf {X : Type*} [Group X] [Finite X] (M : Subgroup X) :
    M ≤ Subgroup.normalizer (dInf M : Set X) := by
  intro g hg
  rw [← A1b.conjSub_eq_iff_mem_normalizer, A1b.conjSub, ← dInf_map_equiv (MulAut.conj g),
    ← A1b.conjSub, A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)]

theorem normalizer_parC_le (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    Subgroup.normalizer (parC K i : Set (antiSp K)) ≤
      Subgroup.normalizer (rootA K i : Set (antiSp K)) := by
  have hS := even_symplectic_four_root_axis_centralizer_structure hK hn i
  have hA : (CFSG.pCore 2 ↥(parC K i)).map (parC K i).subtype = rootA K i := by
    rw [hS.C_pCore, Subgroup.map_subgroupOf_eq_of_le hS.A_le_C]
  intro g hg
  have hC : (parC K i).map (MulAut.conj g).toMonoidHom = parC K i :=
    A1b.conjSub_eq_iff_mem_normalizer.mpr hg
  set φ : ↥(parC K i) ≃* ↥(parC K i) :=
    ((parC K i).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hC) with hφ
  have hcomp : (MulAut.conj g).toMonoidHom.comp (parC K i).subtype =
      (parC K i).subtype.comp φ.toMonoidHom := MonoidHom.ext fun _ => rfl
  rw [← A1b.conjSub_eq_iff_mem_normalizer, A1b.conjSub]
  calc (rootA K i).map (MulAut.conj g).toMonoidHom
      = ((CFSG.pCore 2 ↥(parC K i)).map (parC K i).subtype).map
          (MulAut.conj g).toMonoidHom := by rw [hA]
    _ = ((CFSG.pCore 2 ↥(parC K i)).map φ.toMonoidHom).map (parC K i).subtype := by
        rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    _ = rootA K i := by rw [CFSG.pCore_map_iso 2 φ, hA]

theorem exists_rank2Pkg (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    ∃ P : Fin 2 → Subgroup (antiSp K), Rk2.Rank2Pkg (antiSp K) (antiUnipotent K) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_projUnipotent
    (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P
  have hU₀' := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top (antiProjEquiv K).symm hU₀
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀').exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 (card_and_isSylowTwoOf_antiUnipotent (K := K)).2)
  have hconj : ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent 2 K).map
      (antiProjEquiv K).symm.toMonoidHom).map (MulAut.conj k).toMonoidHom = antiUnipotent K := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have h := ((Rk2.rank2Pkg_sp4 hK hn).map (antiProjEquiv K).symm).map (MulAut.conj k)
  rw [hconj] at h
  exact ⟨_, h⟩

theorem exists_eq_parN (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {P : Fin 2 → Subgroup (antiSp K)}
    (h : Rk2.Rank2Pkg (antiSp K) (antiUnipotent K) P) (i : Axis) : ∃ j, P j = parN K i := by
  obtain ⟨-, -, -, -, hC2, -⟩ := h.res
  obtain ⟨j, hj, hd⟩ := hC2 (parN K i) (le_parN hK hn i) (parN_ne_top hK hn i)
    (not_isSolvable_parN hK hn i)
  refine ⟨j, le_antisymm ?_ ((hj j).mpr rfl)⟩
  calc P j ≤ Subgroup.normalizer (dInf (P j) : Set (antiSp K)) := le_normalizer_dInf _
    _ = Subgroup.normalizer (parC K i : Set (antiSp K)) := by rw [← hd, dInf_parN hK hn i]
    _ ≤ Subgroup.normalizer (rootA K i : Set (antiSp K)) := normalizer_parC_le hK hn i
    _ = parN K i := (parN_eq hK hn i).symm

theorem parN_one_ne_two (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) : parN K .one ≠ parN K .two := by
  intro h
  rw [parN_eq hK hn, parN_eq hK hn] at h
  have h' : Subgroup.normalizer (radA1 K : Set (antiSp K)) =
      Subgroup.normalizer (radA2 K : Set (antiSp K)) := h
  apply CFSG.QuasithinUnique.Fin257.Sp4.wT_not_mem_normalizer_radA1 (K := K)
  rw [h']
  exact CFSG.QuasithinUnique.Fin257.Sp4.wT_mem_normalizer_radA2

theorem eq_parN_of_rank2Pkg (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {P : Fin 2 → Subgroup (antiSp K)} (h : Rk2.Rank2Pkg (antiSp K) (antiUnipotent K) P)
    (j : Fin 2) : P j = parN K .one ∨ P j = parN K .two := by
  obtain ⟨j₁, h₁⟩ := exists_eq_parN hK hn h .one
  obtain ⟨j₂, h₂⟩ := exists_eq_parN hK hn h .two
  have hne : j₁ ≠ j₂ := fun e => parN_one_ne_two hK hn (h₁.symm.trans (e ▸ h₂))
  have key : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b := by decide
  rcases key j₁ j₂ j hne with rfl | rfl
  · exact Or.inl h₁
  · exact Or.inr h₂

theorem coatom_iff (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {M : Subgroup (antiSp K)}
    (hUM : antiUnipotent K ≤ M) : IsCoatom M ↔ M = parN K .one ∨ M = parN K .two := by
  obtain ⟨P, hP⟩ := exists_rank2Pkg hK hn
  obtain ⟨-, -, hmax, -, -, -⟩ := hP.res
  rw [← covBy_top_iff, hmax M hUM]
  constructor
  · rintro ⟨j, rfl⟩
    exact eq_parN_of_rank2Pkg hK hn hP j
  · rintro (rfl | rfl)
    · obtain ⟨j, hj⟩ := exists_eq_parN hK hn hP .one
      exact ⟨j, hj.symm⟩
    · obtain ⟨j, hj⟩ := exists_eq_parN hK hn hP .two
      exact ⟨j, hj.symm⟩

theorem isSolvable_normalizer_U (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    Group.IsSolvable ↥(Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) := by
  obtain ⟨P, hP⟩ := exists_rank2Pkg hK hn
  obtain ⟨hne, -, -, hsolv, -, -⟩ := hP.res
  have h : P 0 ⊓ P 1 = parN K .one ⊓ parN K .two := by
    rcases eq_parN_of_rank2Pkg hK hn hP 0 with h0 | h0 <;>
      rcases eq_parN_of_rank2Pkg hK hn hP 1 with h1 | h1 <;> rw [h0, h1] at hne ⊢ <;>
      first | exact absurd rfl hne | exact inf_comm _ _
  rw [← parN_inf_eq hK hn, ← h]
  exact hsolv

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
