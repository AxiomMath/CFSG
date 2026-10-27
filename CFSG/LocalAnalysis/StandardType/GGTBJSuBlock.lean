module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)
open CFSG.RankThree.Classical (permGL)

theorem ggTBJ_su_blockData {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    {G : Type} [Group G] [Finite G] (ψ : ↥(unitarySU 2 n K d) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 n K d))
    (t : Fin d → Kˣ) (hDt : diagHom d t ∈ unitarySU 2 n K d) {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J
      (ψ.range ⊓ Subgroup.centralizer ({ψ ⟨diagHom d t, hDt⟩} : Set G))) :
    ∃ I : Finset (Fin d),
      (∀ i ∈ I, ∀ j ∈ I, t i = t j) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∃ z : ↥(unitarySU 2 n K d),
        (z : GL (Fin d) K) = permGL (Equiv.swap i j) ∧ ψ z ∈ J) ∧
      (∀ x : Fin d → Kˣ, (∀ i ∈ I, ∀ j ∈ I, x i = x j) →
        ∀ hx : diagHom d x ∈ unitarySU 2 n K d,
          ∀ j ∈ J, ψ ⟨diagHom d x, hx⟩ * j = j * ψ ⟨diagHom d x, hx⟩) := by
  classical
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK (by omega)
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n + 1) (by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega)
  cases d with
  | zero =>
    exfalso
    have hrange : ψ.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨y, rfl⟩
      rw [show y = 1 from Subsingleton.elim y 1, map_one]
    have hJbot : J ≤ ⊥ := hJ.1.trans (le_trans inf_le_left (le_of_eq hrange))
    exact commutator_ne_bot_of_isQuasisimple hJ.2.2
      (by rw [le_bot_iff.mp hJbot, Subgroup.commutator_bot_left])
  | succ m =>
    have suPairs_diag : ∀ (u : Fin (m + 1) → Kˣ)
        (hu : diagHom (m + 1) u ∈ unitarySU 2 n K (m + 1)),
        (ψ ⟨diagHom (m + 1) u, hu⟩, diagHom (m + 1) u) ∈ SUTorus.suPairs ψ := by
      intro u hu
      refine ⟨Subgroup.le_normalizer hu, fun a b hb => ?_⟩
      have hb' : (⟨diagHom (m + 1) u, hu⟩ : ↥(unitarySU 2 n K (m + 1))) * a *
          ⟨diagHom (m + 1) u, hu⟩⁻¹ = b :=
        Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
          exact hb.symm)
      calc ψ ⟨diagHom (m + 1) u, hu⟩ * ψ a * (ψ ⟨diagHom (m + 1) u, hu⟩)⁻¹
          = ψ ((⟨diagHom (m + 1) u, hu⟩ : ↥(unitarySU 2 n K (m + 1))) * a *
              ⟨diagHom (m + 1) u, hu⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = ψ b := by rw [hb']
    set S : Set G := {ψ ⟨diagHom (m + 1) t, hDt⟩} with hSdef
    have hδ : ∀ e ∈ S, (e, diagHom (m + 1) ((fun _ => t) e)) ∈ SUTorus.suPairs ψ := by
      intro e he
      have he' : e = ψ ⟨diagHom (m + 1) t, hDt⟩ := by
        rw [hSdef] at he
        simpa using he
      rw [he']
      exact suPairs_diag t hDt
    obtain ⟨i, hJi⟩ := SUTorus.exists_le_map_blockSU h hp hpq hker hδ hJ
    set I : Finset (Fin (m + 1)) := LinTorus.diagClass S (fun _ => t) i with hIdef
    have hI2 : 2 ≤ I.card := by
      by_contra hlt
      have hI1 : I = {i} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨LinTorus.self_mem_diagClass S (fun _ => t) i,
          fun j hj => Finset.card_le_one.mp (by omega) j hj i
            (LinTorus.self_mem_diagClass S (fun _ => t) i)⟩
      rw [hI1, SUTorus.blockSU_singleton h, Subgroup.map_bot] at hJi
      exact commutator_ne_bot_of_isQuasisimple hJ.2.2
        (by rw [le_bot_iff.mp hJi, Subgroup.commutator_bot_left])
    have hsubI : IsSubnormal ((TableBUE.blockSU (K := K) (n := n) I).map ψ)
        (ψ.range ⊓ Subgroup.centralizer S) :=
      SUTorus.isSubnormal_map_blockSU hker hδ i
    have hcI : IsComponentOf ((TableBUE.blockSU (K := K) (n := n) I).map ψ)
        (ψ.range ⊓ Subgroup.centralizer S) :=
      ⟨isSubnormal_le_of_assembly hsubI, hsubI,
        SURepair.isQuasisimple_map_blockSU_of_two_le h hn hker hI2⟩
    have hJI_eq : J = (TableBUE.blockSU (K := K) (n := n) I).map ψ := by
      refine le_antisymm hJi ?_
      rcases isComponentOf_le_or_commutator_eq_bot hcI hJ.2.1 with h1 | h1
      · exact h1
      · exfalso
        have h2 : ⁅J, J⁆ ≤ ⁅(TableBUE.blockSU (K := K) (n := n) I).map ψ, J⁆ :=
          Subgroup.commutator_mono hJi le_rfl
        rw [h1, le_bot_iff] at h2
        exact commutator_ne_bot_of_isQuasisimple hJ.2.2 h2
    refine ⟨I, ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [hIdef] at ha hb
      have hmem : ψ ⟨diagHom (m + 1) t, hDt⟩ ∈ S := by
        rw [hSdef]
        exact Set.mem_singleton _
      have h1 := (LinTorus.mem_diagClass.mp ha) _ hmem
      have h2 := (LinTorus.mem_diagClass.mp hb) _ hmem
      simpa using h1.trans h2.symm
    · intro a ha b hb hab
      rw [hIdef] at ha hb
      refine ⟨⟨permGL (Equiv.swap a b), TableBUE.permGL_swap_mem h a b⟩, rfl, ?_⟩
      rw [hJI_eq]
      exact Subgroup.mem_map_of_mem ψ (TableBUE.isBlockOn_permGL_swap ha hb)
    · intro x hxconst hx j hj
      have hxpair : (ψ ⟨diagHom (m + 1) x, hx⟩, diagHom (m + 1) x) ∈ SUTorus.suPairs ψ :=
        suPairs_diag x hx
      have hcent := SUTorus.mem_centralizer_map_blockSU (ψ := ψ) hxpair hxconst
      rw [hJI_eq] at hj
      exact ((Subgroup.mem_centralizer_iff.mp hcent) j hj).symm

end CFSG.StandardType

end
