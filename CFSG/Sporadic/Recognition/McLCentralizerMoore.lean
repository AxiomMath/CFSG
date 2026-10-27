module

public import CFSG.Sporadic.Recognition.McLCentralizerLift
public import CFSG.Sporadic.SchreierLemmas.MoorePresentation

public noncomputable section

namespace CFSG.Sporadic.Recognition.McLCentralizer

open Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SchreierLemmas

@[expose] def mooreX
    (i : ℕ) : Equiv.Perm (Fin 35) :=
  mclRho (mooreLift i)

theorem tabRep_mooreX
    (i : ℕ) :
    TabRep (mooreTab i) (mooreX i) := by
  have h := tabRep_wordTabS tabRep_mclXGens (mooreWord i)
    (fun j hj => by rw [mclX_basic.2.1]; exact mooreWord_lt i j hj)
  have e : mooreX i = ((mooreWord i).map mclXPerm).prod := by
    rw [mooreX, mooreLift, map_list_prod, List.map_map]
    rfl
  rw [e]
  exact h

theorem mooreCheck_spec (h : mooreCheck = true) :
    cubeTab 35 (mooreTab 1) = idTab 35 ∧
    (∀ j, 2 ≤ j → j ≤ 6 → sqTab 35 (mooreTab j) = idTab 35 ∧
      cubeTab 35 (comp 35 (mooreTab (j - 1)) (mooreTab j)) = idTab 35) ∧
    ∀ i j, 1 ≤ i → i + 2 ≤ j → j ≤ 6 →
      sqTab 35 (comp 35 (mooreTab i) (mooreTab j)) = idTab 35 := by
  simp only [mooreCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range'_1] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun j hj1 hj2 => h2 j ⟨hj1, by omega⟩, fun i j hi hij hj => ?_⟩
  exact h3 i ⟨hi, by omega⟩ j ⟨hij, by omega⟩

theorem isMooreFamily_mooreX
    (h : mooreCheck = true) :
    IsMooreFamily (8 - 2) mooreX := by
  obtain ⟨h1, h2, h3⟩ := mooreCheck_spec h
  have hid : TabRep (idTab 35) (1 : Equiv.Perm (Fin 35)) := TabRep.idTab
  refine ⟨?_, fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, fun i j hi hij hj => ?_⟩
  · have e := (((tabRep_mooreX 1).comp ((tabRep_mooreX 1).comp (tabRep_mooreX 1))).eq_iff hid).1 h1
    rw [pow_three]
    exact e
  · have e := (((tabRep_mooreX j).comp (tabRep_mooreX j)).eq_iff hid).1
      (h2 j hj1 (by omega)).1
    rw [pow_two]
    exact e
  · have hA := (tabRep_mooreX (j - 1)).comp (tabRep_mooreX j)
    have e := ((hA.comp (hA.comp hA)).eq_iff hid).1 (h2 j hj1 (by omega)).2
    rw [pow_three]
    exact e
  · have hA := (tabRep_mooreX i).comp (tabRep_mooreX j)
    have e := ((hA.comp hA).eq_iff hid).1 (h3 i j hi hij (by omega))
    rw [pow_two]
    exact e

theorem mooreX_four_ne_one
    (hL : liftCheck = true) :
    mooreX 4 ≠ 1 := by
  intro h
  have hk : mooreLift 4 ∈ mclRho.ker := by
    rw [MonoidHom.mem_ker]
    exact h
  rw [mclRho_ker_eq, mem_zpowers_iff] at hk
  obtain ⟨n, hn⟩ := hk
  have hsq : ∀ m : ℤ, ((⟨mclT0, mclT0_mem_Ct⟩ : mclCt) ^ m) ^ 2 = 1 := fun m => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, mclT0_sq, one_zpow]
  have h1 : mooreLift 4 ^ 2 = 1 := by
    rw [← hn]
    exact hsq n
  rw [mooreLift_sq hL] at h1
  have h2 := mclT0_facts.2.1
  have h3 : mclT0 = 1 := congrArg Subtype.val h1
  rw [h3, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem nonempty_range_mulEquiv_alt8
    (hM : mooreCheck = true)
    (hL : liftCheck = true) : Nonempty (mclRho.range ≃* alternatingGroup (Fin 8)) := by
  have hx : IsMooreFamily (8 - 2) mooreX := isMooreFamily_mooreX hM
  have hne : ∃ i ∈ Set.Icc 1 (8 - 2), mooreX i ≠ 1 :=
    ⟨4, ⟨by norm_num, by norm_num⟩, mooreX_four_ne_one hL⟩
  obtain ⟨e₀⟩ :=
    ((moore_alternating_presentation (by norm_num : 3 ≤ 8) mooreX hx).2.2.2.2.2 (by norm_num)
      hne).2
  have hle : closure (mooreX '' Set.Icc 1 (8 - 2)) ≤ mclRho.range := by
    rw [closure_le]
    rintro _ ⟨i, -, rfl⟩
    exact ⟨mooreLift i, rfl⟩
  have hcard : Nat.card mclRho.range ≤ Nat.card (closure (mooreX '' Set.Icc 1 (8 - 2))) := by
    rw [← Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup, Nat.card_fin, mclRho_range.1,
      card_mclX]
    norm_num [Nat.factorial]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e₀.symm⟩

end CFSG.Sporadic.Recognition.McLCentralizer
