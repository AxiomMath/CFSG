module

public import CFSG.Quasithin.AppendixH.H14.H141Engine
public import CFSG.Quasithin.AppendixH.H14.H141T1
public import CFSG.Quasithin.AppendixH.H14.H141TChecks

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H158T CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

theorem labTrio_eq_trioMasks : labTrio = (trioMasks.map maskSetOf).toFinset := by
  rw [labTrio, o0F_eq_mask, o1F_eq_mask, o2F_eq_mask]
  simp [trioMasks]

theorem smul_labTrio_of_arr {g : S24} {a : Array ℕ} (hg : HasArr g a)
    (h : ∀ m ∈ trioMasks, permM a m ∈ trioMasks) : g • labTrio = labTrio := by
  apply Finset.eq_of_subset_of_card_le
  · intro T hT
    rw [Finset.mem_smul_finset] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    rw [labTrio_eq_trioMasks, List.mem_toFinset, List.mem_map] at hT₀
    obtain ⟨m, hm, rfl⟩ := hT₀
    rw [smul_maskSetOf hg, labTrio_eq_trioMasks, List.mem_toFinset, List.mem_map]
    exact ⟨permM a m, h m hm, rfl⟩
  · rw [Finset.card_smul_finset]

theorem tabT_le_MT : tab64Sub tabT tabT_ok ≤ MY M24g labTrio := by
  intro x hx
  rw [mem_tab64Sub tabT_ok] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  have harr := hasArr_tab64Perm tabT_ok hn
  have hmask : ∀ m ∈ trioMasks, permM tabT[n]! m ∈ trioMasks := by
    intro m hm
    have h1 := List.all_eq_true.mp tabT_stab n (List.mem_range.mpr hn)
    have h2 := List.all_eq_true.mp h1 m hm
    exact List.contains_iff_mem.mp h2
  rw [MY, Subgroup.mem_inf]
  exact ⟨tab64Perm_mem_M24g tabT_ok hn,
    MulAction.mem_stabilizer_iff.mpr (smul_labTrio_of_arr harr hmask)⟩

theorem gensT_mem : ∀ a ∈ gensT, inAutOK a = true ∧ ∃ σ ∈ MY M24g labTrio, HasArr σ a := by
  intro a ha
  have h := List.all_eq_true.mp gensT_stab a ha
  rw [Bool.and_eq_true] at h
  obtain ⟨hok, hmask'⟩ := h
  have hmask : ∀ m ∈ trioMasks, permM a m ∈ trioMasks := fun m hm =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hmask' m hm)
  refine ⟨hok, permOfArrD a, ?_, hasArr_permOfArrD hok⟩
  rw [MY, Subgroup.mem_inf]
  exact ⟨permOfArrD_mem_M24g hok,
    MulAction.mem_stabilizer_iff.mpr (smul_labTrio_of_arr (hasArr_permOfArrD hok) hmask)⟩

theorem engine_T :
    EngineHyp tabT tabT_ok (MY M24g labTrio) gensT gmT bfsT where
  le := tabT_le_MT
  gens_mem := gensT_mem
  len := by decide
  act := by
    intro j hj n hn
    have hj2 : j < 2 := by simpa [gensT] using hj
    have h1 := List.all_eq_true.mp cmapT_gens j (List.mem_range.mpr hj2)
    have h2 := List.all_eq_true.mp h1 n (List.mem_range.mpr hn)
    exact beq_iff_eq.mp h2
  bfs := bfsT_ok
  card := by
    have h := card_MT_le
    rw [bfsT_length]
    omega

theorem pCore_T : KY M24g labTrio = tab64Sub tabT tabT_ok :=
  engine_T.pCore vbT1_ok vbT2_ok vbT_cover derT1_ok vbT_link

end CFSG.Quasithin.AppendixH.H14
