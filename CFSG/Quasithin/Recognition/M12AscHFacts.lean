module

public import CFSG.Quasithin.Recognition.M12AscHModel

public section

namespace CFSG.Quasithin

@[expose] def tmul (a b : List (Fin 12)) : List (Fin 12) := b.map fun i => a.getD i.val 0

@[expose] def tid : List (Fin 12) := List.finRange 12

theorem tabOf_mul' (p q : Equiv.Perm (Fin 12)) : tabOf (p * q) = tmul (tabOf p) (tabOf q) := by
  simp [tabOf, tmul, List.map_map, Function.comp_def]

theorem tabOf_one' : tabOf (1 : Equiv.Perm (Fin 12)) = tid := by simp [tabOf, tid]

@[expose] def zTab : List (Fin 12) := [4, 6, 2, 3, 0, 5, 1, 7, 11, 10, 9, 8]

@[expose] def qTabs : List (List (Fin 12)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
   [9, 8, 3, 2, 10, 7, 11, 5, 6, 4, 0, 1],
   [9, 11, 2, 3, 10, 5, 8, 7, 1, 4, 0, 6],
   [10, 8, 2, 3, 9, 5, 11, 7, 6, 0, 4, 1],
   [10, 11, 3, 2, 9, 7, 8, 5, 1, 0, 4, 6],
   [0, 6, 3, 2, 4, 7, 1, 5, 11, 9, 10, 8],
   [4, 1, 3, 2, 0, 7, 6, 5, 8, 10, 9, 11],
   [4, 6, 2, 3, 0, 5, 1, 7, 11, 10, 9, 8],
   [1, 4, 2, 3, 6, 5, 0, 7, 10, 8, 11, 9],
   [1, 4, 7, 5, 6, 3, 0, 2, 9, 11, 8, 10],
   [6, 0, 2, 3, 1, 5, 4, 7, 9, 11, 8, 10],
   [6, 0, 7, 5, 1, 3, 4, 2, 10, 8, 11, 9],
   [8, 9, 2, 3, 11, 5, 10, 7, 4, 6, 1, 0],
   [8, 10, 5, 7, 11, 2, 9, 3, 4, 1, 6, 0],
   [11, 9, 5, 7, 8, 2, 10, 3, 0, 6, 1, 4],
   [11, 10, 2, 3, 8, 5, 9, 7, 0, 1, 6, 4],
   [0, 1, 7, 5, 4, 3, 6, 2, 11, 10, 9, 8],
   [0, 6, 5, 7, 4, 2, 1, 3, 8, 10, 9, 11],
   [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10],
   [1, 0, 5, 7, 6, 2, 4, 3, 10, 11, 8, 9],
   [4, 1, 5, 7, 0, 2, 6, 3, 11, 9, 10, 8],
   [4, 6, 7, 5, 0, 3, 1, 2, 8, 9, 10, 11],
   [6, 4, 3, 2, 1, 7, 0, 5, 10, 11, 8, 9],
   [6, 4, 5, 7, 1, 2, 0, 3, 9, 8, 11, 10],
   [8, 9, 7, 5, 11, 3, 10, 2, 0, 1, 6, 4],
   [8, 10, 3, 2, 11, 7, 9, 5, 0, 6, 1, 4],
   [11, 9, 3, 2, 8, 7, 10, 5, 4, 1, 6, 0],
   [11, 10, 7, 5, 8, 3, 9, 2, 4, 6, 1, 0],
   [9, 8, 5, 7, 10, 2, 11, 3, 1, 0, 4, 6],
   [9, 11, 7, 5, 10, 3, 8, 2, 6, 0, 4, 1],
   [10, 8, 7, 5, 9, 3, 11, 2, 1, 4, 0, 6],
   [10, 11, 5, 7, 9, 2, 8, 3, 6, 4, 0, 1]]

@[expose] def FTabs : List (List (Fin 12)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
   [0, 6, 3, 2, 4, 7, 1, 5, 11, 9, 10, 8],
   [4, 1, 3, 2, 0, 7, 6, 5, 8, 10, 9, 11],
   [4, 6, 2, 3, 0, 5, 1, 7, 11, 10, 9, 8],
   [0, 1, 7, 5, 4, 3, 6, 2, 11, 10, 9, 8],
   [0, 6, 5, 7, 4, 2, 1, 3, 8, 10, 9, 11],
   [4, 1, 5, 7, 0, 2, 6, 3, 11, 9, 10, 8],
   [4, 6, 7, 5, 0, 3, 1, 2, 8, 9, 10, 11]]

@[expose] def tTabs : List (List (Fin 12)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
   [0, 10, 5, 3, 4, 2, 9, 7, 11, 6, 1, 8],
   [9, 8, 3, 2, 10, 7, 11, 5, 6, 4, 0, 1],
   [9, 11, 2, 3, 10, 5, 8, 7, 1, 4, 0, 6],
   [10, 8, 2, 3, 9, 5, 11, 7, 6, 0, 4, 1],
   [10, 11, 3, 2, 9, 7, 8, 5, 1, 0, 4, 6],
   [0, 6, 3, 2, 4, 7, 1, 5, 11, 9, 10, 8],
   [1, 8, 3, 5, 6, 7, 11, 2, 10, 0, 4, 9],
   [1, 11, 5, 3, 6, 2, 8, 7, 9, 0, 4, 10],
   [4, 1, 3, 2, 0, 7, 6, 5, 8, 10, 9, 11],
   [4, 6, 2, 3, 0, 5, 1, 7, 11, 10, 9, 8],
   [6, 8, 5, 3, 1, 2, 11, 7, 10, 4, 0, 9],
   [6, 11, 3, 5, 1, 7, 8, 2, 9, 4, 0, 10],
   [9, 0, 5, 3, 10, 2, 4, 7, 6, 8, 11, 1],
   [9, 0, 7, 2, 10, 3, 4, 5, 1, 11, 8, 6],
   [10, 4, 5, 3, 9, 2, 0, 7, 1, 11, 8, 6],
   [10, 4, 7, 2, 9, 3, 0, 5, 6, 8, 11, 1],
   [0, 9, 3, 5, 4, 7, 10, 2, 8, 6, 1, 11],
   [0, 10, 7, 2, 4, 3, 9, 5, 8, 1, 6, 11],
   [1, 4, 2, 3, 6, 5, 0, 7, 10, 8, 11, 9],
   [1, 4, 7, 5, 6, 3, 0, 2, 9, 11, 8, 10],
   [4, 9, 5, 3, 0, 2, 10, 7, 8, 1, 6, 11],
   [4, 9, 7, 2, 0, 3, 10, 5, 11, 6, 1, 8],
   [4, 10, 3, 5, 0, 7, 9, 2, 11, 1, 6, 8],
   [6, 0, 2, 3, 1, 5, 4, 7, 9, 11, 8, 10],
   [6, 0, 7, 5, 1, 3, 4, 2, 10, 8, 11, 9],
   [8, 1, 5, 3, 11, 2, 6, 7, 0, 10, 9, 4],
   [8, 1, 7, 2, 11, 3, 6, 5, 4, 9, 10, 0],
   [8, 6, 2, 7, 11, 5, 1, 3, 0, 9, 10, 4],
   [8, 6, 3, 5, 11, 7, 1, 2, 4, 10, 9, 0],
   [8, 9, 2, 3, 11, 5, 10, 7, 4, 6, 1, 0],
   [8, 10, 5, 7, 11, 2, 9, 3, 4, 1, 6, 0],
   [11, 1, 2, 7, 8, 5, 6, 3, 4, 10, 9, 0],
   [11, 1, 3, 5, 8, 7, 6, 2, 0, 9, 10, 4],
   [11, 6, 5, 3, 8, 2, 1, 7, 4, 9, 10, 0],
   [11, 6, 7, 2, 8, 3, 1, 5, 0, 10, 9, 4],
   [11, 9, 5, 7, 8, 2, 10, 3, 0, 6, 1, 4],
   [11, 10, 2, 3, 8, 5, 9, 7, 0, 1, 6, 4],
   [0, 1, 7, 5, 4, 3, 6, 2, 11, 10, 9, 8],
   [0, 6, 5, 7, 4, 2, 1, 3, 8, 10, 9, 11],
   [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10],
   [1, 0, 5, 7, 6, 2, 4, 3, 10, 11, 8, 9],
   [1, 8, 2, 7, 6, 5, 11, 3, 9, 4, 0, 10],
   [1, 11, 7, 2, 6, 3, 8, 5, 10, 4, 0, 9],
   [4, 1, 5, 7, 0, 2, 6, 3, 11, 9, 10, 8],
   [4, 6, 7, 5, 0, 3, 1, 2, 8, 9, 10, 11],
   [6, 4, 3, 2, 1, 7, 0, 5, 10, 11, 8, 9],
   [6, 4, 5, 7, 1, 2, 0, 3, 9, 8, 11, 10],
   [6, 8, 7, 2, 1, 3, 11, 5, 9, 0, 4, 10],
   [6, 11, 2, 7, 1, 5, 8, 3, 10, 0, 4, 9],
   [8, 9, 7, 5, 11, 3, 10, 2, 0, 1, 6, 4],
   [8, 10, 3, 2, 11, 7, 9, 5, 0, 6, 1, 4],
   [9, 4, 2, 7, 10, 5, 0, 3, 6, 11, 8, 1],
   [9, 4, 3, 5, 10, 7, 0, 2, 1, 8, 11, 6],
   [10, 0, 2, 7, 9, 5, 4, 3, 1, 8, 11, 6],
   [10, 0, 3, 5, 9, 7, 4, 2, 6, 11, 8, 1],
   [11, 9, 3, 2, 8, 7, 10, 5, 4, 1, 6, 0],
   [11, 10, 7, 5, 8, 3, 9, 2, 4, 6, 1, 0],
   [0, 9, 2, 7, 4, 5, 10, 3, 11, 1, 6, 8],
   [4, 10, 2, 7, 0, 5, 9, 3, 8, 6, 1, 11],
   [9, 8, 5, 7, 10, 2, 11, 3, 1, 0, 4, 6],
   [9, 11, 7, 5, 10, 3, 8, 2, 6, 0, 4, 1],
   [10, 8, 7, 5, 9, 3, 11, 2, 1, 4, 0, 6],
   [10, 11, 5, 7, 9, 2, 8, 3, 6, 4, 0, 1]]

theorem zTab_eval : tabOf (ascHImg 0 * ascHImg 0) = zTab := by decide +kernel

theorem qTabs_sub : ∀ t ∈ qTabs, t ∈ ascHTabs := by decide +kernel
theorem tid_mem_q : tid ∈ qTabs := by decide +kernel
theorem qTabs_mul : ∀ s ∈ qTabs, ∀ t ∈ qTabs, tmul s t ∈ qTabs := by decide +kernel
theorem qTabs_inv : ∀ t ∈ qTabs, ∃ s ∈ qTabs, tmul t s = tid := by decide +kernel
theorem qTabs_normal :
    ∀ h ∈ ascHTabs, ∀ q ∈ qTabs, ∃ q' ∈ qTabs, tmul h q = tmul q' h := by decide +kernel
theorem qTabs_length : qTabs.length = 32 := by decide +kernel
theorem qTabs_nodup : qTabs.Nodup := by decide +kernel

theorem FTabs_sub : ∀ t ∈ FTabs, t ∈ qTabs := by decide +kernel
theorem tid_mem_F : tid ∈ FTabs := by decide +kernel
theorem zTab_mem_F : zTab ∈ FTabs := by decide +kernel
theorem FTabs_mul : ∀ s ∈ FTabs, ∀ t ∈ FTabs, tmul s t ∈ FTabs := by decide +kernel
theorem FTabs_elab :
    ∀ s ∈ FTabs, ∀ t ∈ FTabs, tmul s s = tid ∧ tmul s t = tmul t s := by decide +kernel
theorem FTabs_normal :
    ∀ h ∈ ascHTabs, ∀ f ∈ FTabs, ∃ f' ∈ FTabs, tmul h f = tmul f' h := by decide +kernel
theorem FTabs_length : FTabs.length = 8 := by decide +kernel
theorem FTabs_nodup : FTabs.Nodup := by decide +kernel
theorem CH_F : ∀ h ∈ ascHTabs, (∀ f ∈ FTabs, tmul h f = tmul f h) → h ∈ FTabs := by decide +kernel

set_option synthInstance.maxSize 2048 in
theorem commuting_involution_mem_F :
    ∀ v ∈ ascHTabs, v ∉ qTabs → tmul v v = tid → ∀ s ∈ qTabs, s ≠ tid → s ≠ zTab →
      tmul s s = tid → tmul v s = tmul s v → s ∈ FTabs := by decide +kernel

theorem F_orbit : ∀ s ∈ FTabs, s ≠ tid → s ≠ zTab → ∀ s' ∈ FTabs, s' ≠ tid → s' ≠ zTab →
    ∃ h ∈ ascHTabs, tmul h s = tmul s' h := by decide +kernel

theorem O12_orbit : ∀ s ∈ qTabs, s ∉ FTabs → tmul s s = tid → ∀ s' ∈ qTabs, s' ∉ FTabs →
    tmul s' s' = tid → ∃ h ∈ ascHTabs, tmul h s = tmul s' h := by decide +kernel

theorem outInv_orbit : ∀ v ∈ ascHTabs, v ∉ qTabs → tmul v v = tid → ∀ w ∈ ascHTabs, w ∉ qTabs →
    tmul w w = tid → ∃ h ∈ ascHTabs, tmul h v = tmul w h := by decide +kernel

theorem O12_exists : ∃ s ∈ qTabs, s ∉ FTabs ∧ tmul s s = tid := by decide +kernel

set_option synthInstance.maxSize 2048 in
theorem involutions_outside_F_one_coset :
    ∀ s ∈ FTabs, s ≠ tid → s ≠ zTab →
      ∀ y ∈ qTabs, y ∉ FTabs → tmul y y = tid → tmul y s = tmul s y →
        ∀ y' ∈ qTabs, y' ∉ FTabs → tmul y' y' = tid → tmul y' s = tmul s y' →
          (tmul y y' = tid ∨ tmul y y' = zTab ∨ tmul y y' = s ∨ tmul y y' = tmul zTab s) := by
  decide +kernel

theorem tTabs_sub : ∀ t ∈ tTabs, t ∈ ascHTabs := by decide +kernel
theorem tid_mem_t : tid ∈ tTabs := by decide +kernel
theorem zTab_mem_t : zTab ∈ tTabs := by decide +kernel
theorem tTabs_mul : ∀ s ∈ tTabs, ∀ t ∈ tTabs, tmul s t ∈ tTabs := by decide +kernel
theorem tTabs_inv : ∀ t ∈ tTabs, ∃ s ∈ tTabs, tmul t s = tid := by decide +kernel
theorem tTabs_length : tTabs.length = 64 := by decide +kernel
theorem tTabs_nodup : tTabs.Nodup := by decide +kernel
theorem tTabs_center :
    ∀ t ∈ tTabs, (∀ t' ∈ tTabs, tmul t t' = tmul t' t) → t = tid ∨ t = zTab := by decide +kernel

end CFSG.Quasithin
