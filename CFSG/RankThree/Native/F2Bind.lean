module

public import CFSG.RankThree.Native.F2Ops

public section

namespace CFSG.RankThree.Native.F2

variable {d : ℕ} {V : Array ℕ}

theorem nodup_of_lk {LK : ℕ → ℕ} (h : ∀ i < V.size, LK V[i]! = i) : V.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi' : i.val < V.size := by simp
  have hj' : j.val < V.size := by simp
  have e1 := h i hi'
  have e2 := h j hj'
  rw [getElem!_pos V _ hi'] at e1
  rw [getElem!_pos V _ hj'] at e2
  simp only [List.get_eq_getElem, Array.getElem_toList] at hij
  apply Fin.ext
  rw [← e1, ← e2, hij]

theorem inv_of_images (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {a : Array ℕ} (hs : a.size = V.size) {M M' : ℕ}
    (h : ∀ i < V.size, a[i]! < V.size ∧ V[a[i]!]! = vmul d V[i]! M)
    (h1 : mmul d M M' = idM d) (h2 : mmul d M' M = idM d) :
    Inv d V M M' ∧ a = permOfMat d V M := by
  have hmem : ∀ v ∈ V, ∃ i < V.size, V[i]! = v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hv
    exact ⟨i, hi, getElem!_pos V i hi⟩
  have hback : ∀ i < V.size, vmul d (vmul d V[i]! M) M' = V[i]! := by
    intro i hi
    rw [← vmul_mmul, h1, vmul_idM hd (hVd _ (mem_of_lt hi))]
  let f : Fin V.size → Fin V.size := fun i => ⟨a[i.val]!, (h i i.2).1⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have e := congrArg (fun x : Fin V.size => V[x.val]!) hij
    change V[a[i.val]!]! = V[a[j.val]!]! at e
    rw [(h i i.2).2, (h j j.2).2] at e
    have e2 : vmul d (vmul d V[i.val]! M) M' = vmul d (vmul d V[j.val]! M) M' := by rw [e]
    rw [hback i i.2, hback j j.2] at e2
    exact Fin.ext (by rw [← vidx_get hV i.2, e2, vidx_get hV j.2])
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨⟨fun v hv => ?_, fun v hv => ?_, h1, h2⟩, eq_permOfMat hV hs h⟩
  · obtain ⟨i, hi, rfl⟩ := hmem v hv
    rw [← (h i hi).2]
    exact mem_of_lt (h i hi).1
  · obtain ⟨i, hi, rfl⟩ := hmem v hv
    obtain ⟨j, hj⟩ := hsurj ⟨i, hi⟩
    have e : a[j.val]! = i := congrArg Fin.val hj
    rw [← e, (h j j.2).2, hback j j.2]
    exact mem_of_lt j.2

@[expose] noncomputable def mpowW (mm : ℕ → ℕ → ℕ) (I A e : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) I (fun _ acc => mm acc A) e

theorem mpowW_eq {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d)
    (A : ℕ) : ∀ e, mpowW mm I A e = mpow d A e
  | 0 => hI
  | e + 1 => by
    change mm (mpowW mm I A e) A = _
    rw [hmm, mpowW_eq hmm hI A e]
    rfl

end CFSG.RankThree.Native.F2

end
