module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44PackK

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

@[expose] def encE (x : El) : Nat := Nat.add (Nat.mul x.1 4) x.2

@[expose] def wfCodesK (T : List El) : Bool :=
  T.all fun x => Nat.blt x.2 4 && Nat.blt (encE x) 68719476736

@[expose] def outerKeyK (x : El) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul (encE x) 71999863749) 20) 16383

@[expose] noncomputable def posTabK (key : El → Nat) (T : List El) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 10 (key x))) (ih (Nat.succ i))) T

@[expose] def memHashK (TT PT n : Nat) (key : El → Nat) (y : El) : Bool :=
  let i := laneK 10 PT (key y)
  Nat.blt 0 i && Nat.ble i n && (decEl (laneK 36 TT (i - 1)) == y)

theorem decEl_encE (x : El) (hx : x.2 < 4) : decEl (encE x) = x := by
  unfold decEl encE
  ext <;> simp only [Nat.add_eq, Nat.mul_eq] <;> omega

theorem memHashK_sound (T : List El) (hT : wfCodesK T = true) (PT : Nat) (key : El → Nat)
    (y : El) (h : memHashK (packLK 36 (T.map encE)) PT T.length key y = true) :
    memK T y = true := by
  unfold memHashK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hw : ∀ x ∈ T, x.2 < 4 ∧ encE x < 2 ^ 36 := fun x hx => by
    have := List.all_eq_true.mp hT x hx
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, by simpa using this.2⟩
  have hb : ∀ v ∈ T.map encE, v < 2 ^ 36 := fun v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact (hw x hx).2
  have hj : laneK 10 PT (key y) - 1 < T.length := by omega
  have hl := getD_eq_laneK 36 (T.map encE) hb (laneK 10 PT (key y) - 1)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at hl
  simp only [Option.map_some, Option.getD_some] at hl
  rw [← hl, decEl_encE _ (hw _ (List.getElem_mem hj)).1] at h2
  unfold memK
  exact List.any_eq_true.mpr ⟨_, List.getElem_mem hj, by rw [h2]; exact beq_self_eq_true _⟩

@[expose] noncomputable def closureFastK (T G : List El) (f : El → El → El) (key : El → Nat) :
    Bool :=
  wfCodesK T && forceK (packLK 36 (T.map encE)) fun TT => forceK (posTabK key T 0) fun PT =>
    T.all fun x => G.all fun g => memHashK TT PT T.length key (f x g)

@[expose] noncomputable def closureK (T G : List El) (f : El → El → El) (key : El → Nat) :
    Bool :=
  Bool.rec (T.all fun x => G.all fun g => memK T (f x g)) true (closureFastK T G f key)

theorem closureK_eq (T G : List El) (f : El → El → El) (key : El → Nat) :
    closureK T G f key = (T.all fun x => G.all fun g => memK T (f x g)) := by
  unfold closureK
  cases h : closureFastK T G f key
  · rfl
  · unfold closureFastK at h
    rw [forceK_apply, forceK_apply, Bool.and_eq_true] at h
    obtain ⟨hw, hf⟩ := h
    symm
    exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun g hg =>
      memHashK_sound T hw _ key _ (List.all_eq_true.mp (List.all_eq_true.mp hf x hx) g hg)

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
