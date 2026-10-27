module

public import CFSG.Quasithin.AppendixH.H14.H141Engine
public import CFSG.Quasithin.AppendixH.H14.H141S1
public import CFSG.Quasithin.AppendixH.H14.H141SChecks

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

theorem smul_stdS_of_arr {g : S24} {a : Array ℕ} (hg : HasArr g a)
    (h : ∀ m ∈ stdMasks, permM a m ∈ stdMasks) : g • stdS = stdS := by
  apply Finset.eq_of_subset_of_card_le
  · intro T hT
    rw [Finset.mem_smul_finset] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    rw [stdS_eq_stdMasks, List.mem_toFinset, List.mem_map] at hT₀
    obtain ⟨m, hm, rfl⟩ := hT₀
    rw [smul_maskSetOf hg, stdS_eq_stdMasks, List.mem_toFinset, List.mem_map]
    exact ⟨permM a m, h m hm, rfl⟩
  · rw [Finset.card_smul_finset]

theorem tabS_le_MS : tab64Sub tabS tabS_ok ≤ MY M24g stdS := by
  intro x hx
  rw [mem_tab64Sub tabS_ok] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  have harr := hasArr_tab64Perm tabS_ok hn
  have hmask : ∀ m ∈ stdMasks, permM tabS[n]! m ∈ stdMasks := by
    intro m hm
    have h1 := List.all_eq_true.mp tabS_stab n (List.mem_range.mpr hn)
    have h2 := List.all_eq_true.mp h1 m hm
    exact List.contains_iff_mem.mp h2
  rw [MY, Subgroup.mem_inf]
  exact ⟨tab64Perm_mem_M24g tabS_ok hn,
    MulAction.mem_stabilizer_iff.mpr (smul_stdS_of_arr harr hmask)⟩

theorem gensS_mem : ∀ a ∈ gensS, inAutOK a = true ∧ ∃ σ ∈ MY M24g stdS, HasArr σ a := by
  intro a ha
  have h := List.all_eq_true.mp gensS_stab a ha
  rw [Bool.and_eq_true] at h
  obtain ⟨hok, hmask'⟩ := h
  have hmask : ∀ m ∈ stdMasks, permM a m ∈ stdMasks := fun m hm =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hmask' m hm)
  refine ⟨hok, permOfArrD a, ?_, hasArr_permOfArrD hok⟩
  rw [MY, Subgroup.mem_inf]
  exact ⟨permOfArrD_mem_M24g hok,
    MulAction.mem_stabilizer_iff.mpr (smul_stdS_of_arr (hasArr_permOfArrD hok) hmask)⟩

theorem engine_S :
    EngineHyp tabS tabS_ok (MY M24g stdS) gensS gmS bfsS where
  le := tabS_le_MS
  gens_mem := gensS_mem
  len := by decide
  act := by
    intro j hj n hn
    have hj2 : j < 2 := by simpa [gensS] using hj
    have h1 := List.all_eq_true.mp cmapS_gens j (List.mem_range.mpr hj2)
    have h2 := List.all_eq_true.mp h1 n (List.mem_range.mpr hn)
    exact beq_iff_eq.mp h2
  bfs := bfsS_ok
  card := by
    have h := card_MS_le (S := stdS) isSextet_stdS
    rw [bfsS_length]
    omega

theorem pCore_S : KY M24g stdS = tab64Sub tabS tabS_ok :=
  engine_S.pCore vbS1_ok vbS2_ok vbS_cover derS1_ok vbS_link

end CFSG.Quasithin.AppendixH.H14
