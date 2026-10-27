module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSettingW
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCoreO2
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.Universal.Spin.Generation

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Cores

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.HighestRoot CFSG.LieType.Steinberg CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

private theorem cop_ht_le {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n} {s t : ℤ}
    (hij : i ≠ j) (hs : s = 1 ∨ s = -1) (hts : t = 1 ∨ t = -1)
    (h : Spin.toStdD n γ = Pi.single i s + Pi.single j t) :
    ht γ ≤ 2 * (n : ℤ) - 3 := by
  rw [Spin.ht_of_toStdD_eq_add n (by omega) h]
  have hi : (i : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
  have hj : (j : ℤ) < (n : ℤ) := by exact_mod_cast j.isLt
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i.val
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j.val
  have hijz : (i : ℤ) ≠ (j : ℤ) := by
    intro hh; exact hij (Fin.ext (by exact_mod_cast hh))
  rcases lt_or_gt_of_ne hijz with hlt | hgt
  · rcases hs with rfl | rfl <;> rcases hts with rfl | rfl <;> omega
  · rcases hs with rfl | rfl <;> rcases hts with rfl | rfl <;> omega

private theorem cop_eq_std_of_ht {n : ℕ} (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n} {s t : ℤ}
    (hij : i ≠ j) (hs : s = 1 ∨ s = -1) (hts : t = 1 ∨ t = -1)
    (h : Spin.toStdD n γ = Pi.single i s + Pi.single j t)
    (hht : ht γ = 2 * (n : ℤ) - 3) :
    Spin.toStdD n γ = Pi.single (⟨0, by omega⟩ : Fin n) (1:ℤ) +
      Pi.single (⟨1, by omega⟩ : Fin n) (1:ℤ) := by
  rw [Spin.ht_of_toStdD_eq_add n (by omega) h] at hht
  have hi : (i : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
  have hj : (j : ℤ) < (n : ℤ) := by exact_mod_cast j.isLt
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i.val
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j.val
  have hijz : (i : ℤ) ≠ (j : ℤ) := by
    intro hh; exact hij (Fin.ext (by exact_mod_cast hh))
  rw [h]
  rcases hs with rfl | rfl
  · rcases hts with rfl | rfl
    · have hsum : ((i:ℤ) + (j:ℤ)) = 1 := by omega
      by_cases hi0' : i.val = 0
      · have hieq : i = (⟨0, by omega⟩ : Fin n) := by
          apply Fin.ext
          show (i:ℕ) = 0
          omega
        have hjeq : j = (⟨1, by omega⟩ : Fin n) := by
          apply Fin.ext
          show (j:ℕ) = 1
          omega
        rw [hieq, hjeq]
      · have hival : (i:ℤ) = 1 := by
          have : (i:ℤ) ≠ 0 := by
            intro hh; exact hi0' (by exact_mod_cast hh)
          omega
        have hjval : (j:ℤ) = 0 := by omega
        have hieq : i = (⟨1, by omega⟩ : Fin n) := by
          apply Fin.ext
          show (i:ℕ) = 1
          omega
        have hjeq : j = (⟨0, by omega⟩ : Fin n) := by
          apply Fin.ext
          show (j:ℕ) = 0
          omega
        rw [hieq, hjeq, add_comm]
    · exfalso; omega
  · rcases hts with rfl | rfl <;> (exfalso; omega)

theorem spinPlus_highest {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] :
    (Spin.plusDatum n F hn).divisible = ∅ ∧ IsIrreducible (Spin.plusDatum n F hn).cartan ∧
      ∃ r : Fin (Spin.plusDatum n F hn).rank → ℤ, IsHighestRoot (Spin.plusDatum n F hn) r ∧
        ∀ γ₀ ∈ (Spin.plusDatum n F hn).roots,
          (∀ δ ∈ (Spin.plusDatum n F hn).roots, ht δ ≤ ht γ₀) → γ₀ = r := by
  obtain ⟨r, hr⟩ := exists_isHighestRoot (Spin.plusDatum n F hn)
    (isIrreducible_cartanD hn) rfl (by show 0 < n; omega)
  refine ⟨rfl, isIrreducible_cartanD hn, r, hr, ?_⟩
  intro γ₀ hγ₀ hmax₀
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
    intro h'; exact absurd (congrArg Fin.val h') (by simp)
  obtain ⟨θ, hθmem, hθstd⟩ := Spin.exists_mem_rootsD_toStdD_eq n
    (i := (⟨0, by omega⟩ : Fin n)) (j := (⟨1, by omega⟩ : Fin n))
    (s := 1) (t := 1) h01 (Or.inl rfl) (Or.inl rfl)
  have hθht : ht θ = 2 * (n : ℤ) - 3 := by
    rw [Spin.ht_of_toStdD_eq_add n (by omega) hθstd]
    simp only [Fin.val_mk, one_mul]
    ring
  have hroot_le : ∀ {γ : Fin n → ℤ}, γ ∈ roots (Spin.isFiniteType_cartanD n) ∅ →
      ht γ ≤ 2 * (n:ℤ) - 3 := by
    intro γ hγ
    rw [Spin.rootsD_eq n (by omega), Set.mem_setOf_eq] at hγ
    obtain ⟨i, j, s, t, hij, hs, hts, hstd⟩ := hγ
    exact cop_ht_le hn hij hs hts hstd
  have hstd_of_max : ∀ {γ : Fin n → ℤ}, γ ∈ roots (Spin.isFiniteType_cartanD n) ∅ →
      (∀ δ ∈ roots (Spin.isFiniteType_cartanD n) ∅, ht δ ≤ ht γ) →
      Spin.toStdD n γ = Pi.single (⟨0, by omega⟩ : Fin n) (1:ℤ) +
        Pi.single (⟨1, by omega⟩ : Fin n) (1:ℤ) := by
    intro γ hγ hmax
    have hγht : ht γ = 2 * (n:ℤ) - 3 :=
      le_antisymm (hroot_le hγ) (by rw [← hθht]; exact hmax θ hθmem)
    rw [Spin.rootsD_eq n (by omega), Set.mem_setOf_eq] at hγ
    obtain ⟨i, j, s, t, hij, hs, hts, hstd⟩ := hγ
    exact cop_eq_std_of_ht hn hij hs hts hstd hγht
  have hγ₀std := hstd_of_max hγ₀ hmax₀
  have hrstd := hstd_of_max hr.mem_roots hr.height_le
  exact Spin.toStdD_injective n (hγ₀std.trans hrstd.symm)


theorem spinPlus_coreOne {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hl : GGLongRoot (Spin.plusDatum n F (by omega)) β)
    (u : ↥(spinGroup (Spin.quadPlus n F)))
    {Rr Rm Q : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    (hRr : Rr = ggRootSub (Spin.plusDatum n F (by omega)) (MonoidHom.id _) β u)
    (hRm : Rm = ggRootSub (Spin.plusDatum n F (by omega)) (MonoidHom.id _) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set ↥(spinGroup (Spin.quadPlus n F))))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hdiv, hirr, r, hr, hmax⟩ := spinPlus_highest (n := n) hn3 (F := F)
  exact coreOne_long_of
    (K := ↥(spinGroup (Spin.quadPlus n F)))
    (D := Spin.plusDatum n F hn3)
    (Spin.plusDatum_isCTGroupDatum (n := n) (K := F) hn3
      (Spin.plusDatum_iSup_eq_top n F hn3))
    (Spin.plusDatum_steinbergExtras (n := n) (K := F) hn3)
    hdiv hirr
    (fun γ hγ => by
      obtain ⟨i, j, hij, s, t, hstd, hgrp⟩ :=
        Spin.exists_plusRootGroup_eq (K := F) (n := n) hn3 hγ
      change IsPGroup 2 (Spin.plusRootGroup n F hn3 γ)
      haveI : Fintype F := Fintype.ofFinite F
      obtain ⟨k, -, hk⟩ := FiniteField.card F 2
      have hf : Function.Injective ((Spin.plusFrame n F hn3).longRoot hij s t) :=
        Spin.HypFrame.longRoot_injective _ hij s t
      have hcard : Nat.card ((Spin.plusFrame n F hn3).longRoot hij s t).range = 2 ^ (k : ℕ) := by
        rw [(Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm]
        rw [show Nat.card (Multiplicative F) = Nat.card F from rfl,
          Nat.card_eq_fintype_card, hk]
      rw [hgrp]
      exact IsPGroup.of_card hcard)
    hr hmax hl u hRr hRm hQ

theorem spinPlus_coreFour {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hl : GGLongRoot (Spin.plusDatum n F (by omega)) β)
    (u : ↥(spinGroup (Spin.quadPlus n F)))
    {Rr Q : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    (hRr : Rr = ggRootSub (Spin.plusDatum n F (by omega)) (MonoidHom.id _) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set ↥(spinGroup (Spin.quadPlus n F))))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set ↥(spinGroup (Spin.quadPlus n F))) := by
  have hn3 : 3 ≤ n := by omega
  have hS : Radical.SpinOmegaData (Spin.quadPlus n F) :=
    Radical.spinOmegaData_quadPlus (n := n) (F := F) hn3
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ := hl
  have hβ : β ∈ (Spin.plusDatum n F hn3).roots := by
    rw [hβeq]
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀mem w
  obtain ⟨P, P', horth, hRmap, hW⟩ :=
    Radical.exists_frame_hW_of_root_plus hn hS hβ u
  have hRr' : Rr = Radical.siegelRoot (Spin.quadPlus n F) P.e P'.e := by
    rw [hRr, ggRootSub, Subgroup.map_id]
    exact hRmap
  have hQ' : Q = pCoreOf 2 (Subgroup.normalizer
      (Radical.siegelRoot (Spin.quadPlus n F) P.e P'.e : Set _)) := by
    rw [hQ, hRr']
  have hV : 6 ≤ Module.finrank F (Fin n ⊕ Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hle : Q ≤ Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e := by
    rw [hQ']
    exact Radical.siegelO2_le_orthSiegelCore hS horth hV hW
  have hcf : ⁅Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e,
      Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e⁆ ≤
      Radical.siegelRoot (Spin.quadPlus n F) P.e P'.e :=
    Radical.orthSiegelCore_commutator_le horth hS.nondeg hV
  have hcen : Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e ≤
      Subgroup.centralizer (Radical.siegelRoot (Spin.quadPlus n F) P.e P'.e : Set _) :=
    Radical.orthSiegelCore_le_centralizer hS horth
  refine ⟨?_, ?_⟩
  · calc ⁅Q, Q⁆ ≤ ⁅Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e,
        Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e⁆ :=
        Subgroup.commutator_mono hle hle
      _ ≤ Radical.siegelRoot (Spin.quadPlus n F) P.e P'.e := hcf
      _ = Rr := hRr'.symm
  · calc Q ≤ Radical.orthSiegelCore (Spin.quadPlus n F) P.e P'.e := hle
      _ ≤ Subgroup.centralizer (Radical.siegelRoot (Spin.quadPlus n F) P.e P'.e : Set _) := hcen
      _ = Subgroup.centralizer (Rr : Set _) := by rw [hRr']

end CFSG.StandardType.LieKnownR2.POmega.Cores
