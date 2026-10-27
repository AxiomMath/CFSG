module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Par

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.L436
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)

variable {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F] [CharP F 2]
  {ι : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) →* Q}

private theorem Q2_zero_inf_Q2_one_le :
    Q2 F 0 ⊓ Q2 F 1 ≤ CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 2 F := by
  intro g hg
  rw [CFSG.QuasithinUnique.Setup.X7a.borelSubgroup_eq_flagStabilizer, mem_flagStabilizer]
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  have h0 : g ∈ flagStabilizer 2 F ({1} : Set ℕ) := by
    simpa using (CFSG.QuasithinUnique.Setup.X7a.Q2_eq (K := F) 0 ▸ hg.1)
  have h1 : g ∈ flagStabilizer 2 F ({2} : Set ℕ) := by
    simpa using (CFSG.QuasithinUnique.Setup.X7a.Q2_eq (K := F) 1 ▸ hg.2)
  rcases hi with rfl | rfl
  · exact mem_flagStabilizer.mp h0 1 (by simp)
  · exact mem_flagStabilizer.mp h1 2 (by simp)

private theorem Q2_injective : Function.Injective (Q2 F) := by
  intro i j hij
  rcases CFSG.QuasithinUnique.Vol2Native.A312L.fin_two_cases i with rfl | rfl <;>
    rcases CFSG.QuasithinUnique.Vol2Native.A312L.fin_two_cases j with rfl | rfl
  · rfl
  · exact absurd hij CFSG.QuasithinUnique.Setup.X7a.Q2_ne
  · exact absurd hij.symm CFSG.QuasithinUnique.Setup.X7a.Q2_ne
  · rfl

private theorem not_Q2_le_of_ne {i j : Fin 2} (hij : i ≠ j) : ¬ Q2 F i ≤ Q2 F j := by
  intro h
  exact (CFSG.QuasithinUnique.Setup.X7a.covBy_Q2 j).2
    (CFSG.QuasithinUnique.Setup.X7a.covBy_Q2 i).lt
    (lt_of_le_of_ne h fun he => hij (Q2_injective he))

private theorem Q2_le_Q2_iff {i j : Fin 2} : Q2 F i ≤ Q2 F j ↔ i = j :=
  ⟨fun h => by
    by_contra hij
    exact not_Q2_le_of_ne hij h, fun h => h ▸ le_rfl⟩

private theorem map_tauEquiv_Q2_zero :
    (Q2 F 0).map (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).toMonoidHom = Q2 F 1 := by
  refine Subgroup.eq_of_le_of_card_ge CFSG.Quasithin.H13.Ch4.Sp4M.tau_map_Q0_le ?_
  rw [Subgroup.card_map_of_injective
    (f := (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).toMonoidHom)
    (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).injective]
  calc Nat.card ↥(Q2 F 1) =
        Nat.card ↥((Q2 F 1).map
          (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).toMonoidHom) :=
        (Subgroup.card_map_of_injective
          (f := (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).toMonoidHom)
          (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).injective).symm
    _ ≤ Nat.card ↥(Q2 F 0) := Subgroup.card_le_of_le
        CFSG.Quasithin.H13.Ch4.Sp4M.tau_map_Q1_le

private theorem sp4K₂_Q2_zero {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    sp4K₂ ⊤ (Q2 F 0) (unipotent 2 F) (pCoreOf 2 (perfectCore (Q2 F 0))) =
      perfectCore (Q2 F 1) := by
  have h := CFSG.Quasithin.H13.Ch4.L436.map_sp4K₂
    (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).toMonoidHom
    (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).injective
    (K := ⊤) (P := Q2 F 1) (S := unipotent 2 F)
    (V := pCoreOf 2 (perfectCore (Q2 F 1)))
  rw [CFSG.Quasithin.H13.Ch4.Sp4M.sp4K₂_eq hn hF, CFSG.Quasithin.map_perfectCore,
    map_tauEquiv_Q2_zero,
    Subgroup.map_top_of_surjective
      (f := (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).toMonoidHom)
      (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := F)).surjective,
    CFSG.Quasithin.H13.Ch4.Sp4M.map_tau_Q1,
    CFSG.Quasithin.F134.Sp4.map_tauEquiv_unipotent,
    CFSG.Quasithin.H13.Ch4.Sp4M.map_tau_R1] at h
  exact h.symm

theorem isMaxParabolicOver_map_Q2 (hι : Function.Injective ι) (j : Fin 2) :
    IsMaxParabolicOver ι.range ((unipotent 2 F).map ι) ((Q2 F j).map ι) := by
  refine ⟨Subgroup.map_le_range ι _, ?_, ?_, ?_⟩
  · rintro x ⟨hxr, hxN⟩
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxr
    have hyN : y ∈ Subgroup.normalizer ((unipotent 2 F : Subgroup _) : Set _) := by
      have h := Subgroup.le_normalizer_comap (f := ι) (H := (unipotent 2 F).map ι) hxN
      rwa [Subgroup.comap_map_eq_self_of_injective hι] at h
    rw [normalizer_unipotent] at hyN
    exact Subgroup.mem_map_of_mem ι ((CFSG.QuasithinUnique.Setup.X7a.covBy_Q2 j).lt.le hyN)
  · intro h
    exact CFSG.Quasithin.H13.Ch4.Sp4M.Q2_ne_top j
      (Subgroup.map_injective hι (by rw [h, MonoidHom.range_eq_map]))
  · intro Y hPY hYX
    have hYmap : (Y.comap ι).map ι = Y := Subgroup.map_comap_eq_self hYX
    have hQY : Q2 F j ≤ Y.comap ι := by
      rw [← Subgroup.map_le_map_iff_of_injective hι, hYmap]
      exact hPY
    have hUY : unipotent 2 F ≤ Y.comap ι :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent_le_borelSubgroup.trans
        ((CFSG.QuasithinUnique.Setup.X7a.covBy_Q2 j).lt.le.trans hQY)
    by_cases htop : Y.comap ι = ⊤
    · right
      rw [← hYmap, htop, MonoidHom.range_eq_map]
    · rcases CFSG.QuasithinUnique.Setup.X7a.contained_in_Q2 hUY htop with h0 | h1
      · left
        have hj : j = 0 := Q2_le_Q2_iff.mp (hQY.trans h0)
        subst j
        rw [← hYmap, le_antisymm h0 hQY]
      · left
        have hj : j = 1 := Q2_le_Q2_iff.mp (hQY.trans h1)
        subst j
        rw [← hYmap, le_antisymm h1 hQY]

theorem map_Q2_zero_ne_one (hι : Function.Injective ι) : (Q2 F 0).map ι ≠ (Q2 F 1).map ι := by
  intro h
  exact CFSG.QuasithinUnique.Setup.X7a.Q2_ne (Subgroup.map_injective hι h)

theorem le_or_le_map_Q2 (hι : Function.Injective ι) {Y : Subgroup Q}
    (hUY : (unipotent 2 F).map ι ≤ Y) (hY : Y < ι.range) :
    Y ≤ (Q2 F 0).map ι ∨ Y ≤ (Q2 F 1).map ι := by
  have hYmap : (Y.comap ι).map ι = Y := Subgroup.map_comap_eq_self hY.le
  have hU : unipotent 2 F ≤ Y.comap ι := by
    intro u hu
    exact hUY (Subgroup.mem_map_of_mem ι hu)
  have hne : Y.comap ι ≠ ⊤ := by
    intro htop
    apply hY.ne
    rw [← hYmap, htop, MonoidHom.range_eq_map]
  rcases CFSG.QuasithinUnique.Setup.X7a.contained_in_Q2 hU hne with h | h
  · left
    rw [← hYmap]
    exact Subgroup.map_mono h
  · right
    rw [← hYmap]
    exact Subgroup.map_mono h

theorem map_Q2_inf_le (hι : Function.Injective ι) :
    (Q2 F 0).map ι ⊓ (Q2 F 1).map ι ≤
      normalizer (((unipotent 2 F).map ι : Subgroup Q) : Set Q) := by
  rw [← Subgroup.map_inf_eq (Q2 F 0) (Q2 F 1) ι hι]
  refine CFSG.Quasithin.H13.Ch4.L436.map_le_normalizer ι hι ?_
  rw [normalizer_unipotent]
  exact Q2_zero_inf_Q2_one_le

theorem sp4ParConcl_map_Q2 {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hι : Function.Injective ι) (j : Fin 2) :
    Sp4ParConcl n ι.range ((Q2 F j).map ι) ((unipotent 2 F).map ι)
      (pCoreOf 2 (perfectCore ((Q2 F j).map ι))) := by
  rcases CFSG.QuasithinUnique.Vol2Native.A312L.fin_two_cases j with rfl | rfl
  · have h := (CFSG.Quasithin.H13.Ch4.Sp4M.sp4ParConcl_Q0 hn hF).map ι hι
    rwa [← MonoidHom.range_eq_map,
      ← CFSG.Quasithin.Lie2Parabolic.pCoreOf_map_of_injective ι hι,
      CFSG.Quasithin.map_perfectCore] at h
  · have h := (CFSG.Quasithin.H13.Ch4.Sp4M.sp4ParConcl_Q1 hn hF).map ι hι
    rwa [← MonoidHom.range_eq_map,
      ← CFSG.Quasithin.Lie2Parabolic.pCoreOf_map_of_injective ι hι,
      CFSG.Quasithin.map_perfectCore] at h

theorem sp4K₂_map_Q2_zero {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hι : Function.Injective ι) :
    sp4K₂ ι.range ((Q2 F 0).map ι) ((unipotent 2 F).map ι)
        (pCoreOf 2 (perfectCore ((Q2 F 0).map ι))) = perfectCore ((Q2 F 1).map ι) := by
  have h := CFSG.Quasithin.H13.Ch4.L436.map_sp4K₂ ι hι (K := ⊤) (P := Q2 F 0)
    (S := unipotent 2 F) (V := pCoreOf 2 (perfectCore (Q2 F 0)))
  rw [sp4K₂_Q2_zero hn hF, CFSG.Quasithin.map_perfectCore,
    ← MonoidHom.range_eq_map,
    ← CFSG.Quasithin.Lie2Parabolic.pCoreOf_map_of_injective ι hι,
    CFSG.Quasithin.map_perfectCore] at h
  exact h.symm

theorem sp4K₂_map_Q2_one {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hι : Function.Injective ι) :
    sp4K₂ ι.range ((Q2 F 1).map ι) ((unipotent 2 F).map ι)
        (pCoreOf 2 (perfectCore ((Q2 F 1).map ι))) = perfectCore ((Q2 F 0).map ι) := by
  have h := CFSG.Quasithin.H13.Ch4.L436.map_sp4K₂ ι hι (K := ⊤) (P := Q2 F 1)
    (S := unipotent 2 F) (V := pCoreOf 2 (perfectCore (Q2 F 1)))
  rw [CFSG.Quasithin.H13.Ch4.Sp4M.sp4K₂_eq hn hF, CFSG.Quasithin.map_perfectCore,
    ← MonoidHom.range_eq_map,
    ← CFSG.Quasithin.Lie2Parabolic.pCoreOf_map_of_injective ι hι,
    CFSG.Quasithin.map_perfectCore] at h
  exact h.symm

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model
