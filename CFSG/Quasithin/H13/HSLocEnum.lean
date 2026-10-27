module

public import CFSG.Quasithin.H13.HSLocTab
public import CFSG.Quasithin.H13.OverSylowEnum

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.Quasithin.H13.LocDbl (enum_spec)

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 100)] [FaithfulSMul Γ (Fin 100)]

theorem T_getElem (g : Γ) {i : ℕ} (hi : i < (T g).size) : (T g)[i] = act 100 g i := by
  have h := img_T g i
  simpa [img, Array.getD_eq_getD_getElem?, hi] using h

theorem rows_eq_T (g : Γ) : (List.range 100).map (act 100 g) = (T g).toList := by
  apply List.ext_getElem
  · simp [T_size]
  · intro i h1 h2
    have hi : i < 100 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact (T_getElem g (by rw [T_size]; exact hi)).symm

theorem enumTabs_getD {G : Array (Array ℕ)} {L : List Γ}
    (hG : ∀ t < G.size, ∀ p < 100, img (G.getD t #[]) p = act 100 (L.getD t 1) p)
    {par lab : Array ℕ} {N : ℕ} (hok : enumOK N G par lab = true) {k : ℕ} (hk : k < N) :
    (enumTabs G (par, lab) N).getD k #[] = T (enumElt L par lab k) := by
  have hget : (enumTabs G (par, lab) N).getD k #[] =
      ((Array.range 100).map (ptsArr G par lab N)).map (fun A => A.getD k 0) := by
    unfold enumTabs
    simp [Array.getD_eq_getD_getElem?, hk]
  rw [hget]
  apply eq_T_of_img
  · simp
  · intro q hq
    simp only [img, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hq,
      if_true, Option.map_some, Option.getD_some]
    have := (ptsArr_spec G L par lab N q hq hG hok).2 k hk
    simpa only [Array.getD_eq_getD_getElem?] using this

theorem mem_enumTabs {G : Array (Array ℕ)} {L : List Γ}
    (hG : ∀ t < G.size, ∀ p < 100, img (G.getD t #[]) p = act 100 (L.getD t 1) p)
    {par lab : Array ℕ} {N : ℕ} (hok : enumOK N G par lab = true) (g : Γ) :
    T g ∈ (enumTabs G (par, lab) N).toList ↔ ∃ k < N, T (enumElt L par lab k) = T g := by
  have hsize : (enumTabs G (par, lab) N).size = N := by simp [enumTabs]
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i < N := by rwa [hsize] at hi
    refine ⟨i, hi', ?_⟩
    rw [← enumTabs_getD hG hok hi', ← h]
    simp [Array.getD_eq_getD_getElem?, hi]
  · rintro ⟨k, hk, h⟩
    refine ⟨k, by rw [hsize]; exact hk, ?_⟩
    rw [← h, ← enumTabs_getD hG hok hk]
    simp [Array.getD_eq_getD_getElem?, hsize, hk]

structure SubSpec (H : Subgroup Γ) (X : Array (Array ℕ)) (N : ℕ) : Prop where
  card : Nat.card H = N
  mem_iff : ∀ g : Γ, g ∈ H ↔ T g ∈ X.toList
  exists_of_mem : ∀ t ∈ X.toList, ∃ g ∈ H, T g = t

theorem subSpec_of_enum [Finite Γ] {G : Array (Array ℕ)} {L : List Γ} (hlen : L.length = G.size)
    (hG : ∀ t < G.size, ∀ p < 100, img (G.getD t #[]) p = act 100 (L.getD t 1) p) {cap N : ℕ}
    (h : subEnumOK 100 B100 N cap G = true) :
    SubSpec (Subgroup.closure {x | x ∈ L}) (enumTabs G (bfsEnumL 100 B100 G cap) N) N := by
  simp only [subEnumOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hd⟩, hcl⟩, hN⟩ := h
  have hB : ∀ b ∈ B100, b < 100 := fun b hb => List.mem_range.mp hb
  obtain ⟨hcard, hmem⟩ := enum_spec hB base_of_faithful G L hlen hG _ _ N hok hd hcl hN
  have hmem' : ∀ g : Γ, g ∈ Subgroup.closure {x | x ∈ L} ↔
      ∃ k < N, T (enumElt L (bfsEnumL 100 B100 G cap).1 (bfsEnumL 100 B100 G cap).2 k) = T g := by
    intro g
    rw [hmem g]
    refine exists_congr fun k => and_congr_right fun hk => ?_
    rw [rows_spec hB G L _ _ N hG hok hk]
    change (List.range 100).map _ = (List.range 100).map _ ↔ _
    rw [rows_eq_T, rows_eq_T, Array.toList_inj]
  refine ⟨hcard, fun g => ?_, fun t ht => ?_⟩
  · rw [hmem' g]
    exact (mem_enumTabs hG hok g).symm
  · have hsize : (enumTabs G (bfsEnumL 100 B100 G cap) N).size = N := by simp [enumTabs]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have hi' : i < N := by simpa [hsize] using hi
    refine ⟨enumElt L (bfsEnumL 100 B100 G cap).1 (bfsEnumL 100 B100 G cap).2 i,
      enumElt_mem _ _ _ _, ?_⟩
    rw [← enumTabs_getD hG hok hi']
    simp [Array.getD_eq_getD_getElem?, hsize, hi']

end CFSG.Quasithin.H13.LocDbl.HSLoc
