module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverPair
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem zmod3_injOn_affine :
    ∀ (S : Finset (ZMod 3)) (f : ZMod 3 → ZMod 3),
      (∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) → ∃ κ c : ZMod 3, ∀ z ∈ S, f z = κ * z + c := by
  decide

private def l6p2_tail (m : ℕ) (u : ℕ → ZMod 3) (n : ℕ) : ZMod 3 :=
  ∑ k ∈ Finset.Ico n m, u k

private lemma l6p2_tail_sub (m : ℕ) (u : ℕ → ZMod 3) {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) :
    l6p2_tail m u i - l6p2_tail m u j = ∑ k ∈ Finset.Ico i j, u k := by
  unfold l6p2_tail
  rw [Finset.sum_Ico_eq_sub u hjm, Finset.sum_Ico_eq_sub u hij,
    Finset.sum_Ico_eq_sub u (hij.trans hjm)]
  abel

private lemma l6p2_tail_sub_succ (m : ℕ) (u : ℕ → ZMod 3) {n : ℕ} (hn : n < m) :
    l6p2_tail m u n - l6p2_tail m u (n + 1) = u n := by
  rw [l6p2_tail_sub m u (Nat.le_succ n) (Nat.succ_le_of_lt hn)]
  have hIco : Finset.Ico n (n + 1) = {n} := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hIco, Finset.sum_singleton]

private lemma l6p2_filter_sum_eq_tail (m : ℕ) (f : Fin m → ZMod 3) (u : ℕ → ZMod 3)
    (hu : ∀ k (hk : k < m), u k = f ⟨k, hk⟩) {i j : ℕ} (hjm : j ≤ m) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), f l)
      = ∑ k ∈ Finset.Ico i j, u k := by
  have hcongr :
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), f l)
        = ∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), u l.val := by
    refine Finset.sum_congr rfl ?_
    intro l _
    exact (hu l.val l.isLt).symm
  rw [hcongr, Finset.sum_filter]
  have hfin :
      (∑ l : Fin m, (if i ≤ l.val ∧ l.val < j then u l.val else 0))
        = ∑ k ∈ Finset.range m, (if i ≤ k ∧ k < j then u k else 0) :=
    Fin.sum_univ_eq_sum_range (fun k => if i ≤ k ∧ k < j then u k else 0) m
  rw [hfin]
  have hset : (Finset.range m).filter (fun k => i ≤ k ∧ k < j) = Finset.Ico i j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, hik, hkj⟩
      exact ⟨hik, hkj⟩
    · rintro ⟨hik, hkj⟩
      exact ⟨lt_of_lt_of_le hkj hjm, hik, hkj⟩
  rw [← Finset.sum_filter, hset]

theorem ggIndep_p3_refl_affine {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod 3) V) (ht : V) (αt : Module.Dual (ZMod 3) V)
    (hCLL : ∀ i j : ℕ, i < j → j ≤ m →
      ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), αv l) ht = 0 ↔
        αt (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), hv l) = 0)) :
    ∃ κ : ZMod 3, ∀ l, αt (hv l) = κ * αv l ht := by
  let u : ℕ → ZMod 3 := fun n => if h : n < m then αv ⟨n, h⟩ ht else 0
  let w : ℕ → ZMod 3 := fun n => if h : n < m then αt (hv ⟨n, h⟩) else 0
  have hA : ∀ i j : ℕ, i < j → j ≤ m →
      (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), αv l) ht
        = l6p2_tail m u i - l6p2_tail m u j := by
    intro i j hij hjm
    rw [LinearMap.sum_apply]
    rw [l6p2_filter_sum_eq_tail m (fun l => αv l ht) u
      (fun k hk => by dsimp only [u]; exact dif_pos hk) hjm]
    exact (l6p2_tail_sub m u hij.le hjm).symm
  have hB : ∀ i j : ℕ, i < j → j ≤ m →
      αt (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), hv l)
        = l6p2_tail m w i - l6p2_tail m w j := by
    intro i j hij hjm
    rw [map_sum]
    rw [l6p2_filter_sum_eq_tail m (fun l => αt (hv l)) w
      (fun k hk => by dsimp only [w]; exact dif_pos hk) hjm]
    exact (l6p2_tail_sub m w hij.le hjm).symm
  have hiff_sub : ∀ i j : ℕ, i < j → j ≤ m →
      (l6p2_tail m u i = l6p2_tail m u j ↔ l6p2_tail m w i = l6p2_tail m w j) := by
    intro i j hij hjm
    have h := hCLL i j hij hjm
    rw [hA i j hij hjm, hB i j hij hjm] at h
    rw [sub_eq_zero, sub_eq_zero] at h
    exact h
  have hiff : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      (l6p2_tail m u i = l6p2_tail m u j ↔ l6p2_tail m w i = l6p2_tail m w j) := by
    intro i hi j hj
    have him : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have hjm : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact hiff_sub i j hlt hjm
    · subst heq
      simp
    · have h := hiff_sub j i hgt him
      exact ⟨fun hab => (h.mp hab.symm).symm, fun hcd => (h.mpr hcd.symm).symm⟩
  let S : Finset (ZMod 3) := (Finset.range (m + 1)).image (l6p2_tail m u)
  let ψ : ZMod 3 → ZMod 3 := fun z =>
    if h : z ∈ S then l6p2_tail m w (Classical.choose (Finset.mem_image.mp h)) else 0
  have hψg : ∀ i ∈ Finset.range (m + 1), ψ (l6p2_tail m u i) = l6p2_tail m w i := by
    intro i hi
    have hmem : l6p2_tail m u i ∈ S := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hspec := Classical.choose_spec (Finset.mem_image.mp hmem)
    dsimp only [ψ]
    rw [dif_pos hmem]
    exact (hiff (Classical.choose (Finset.mem_image.mp hmem)) hspec.1 i hi).mp hspec.2
  have hψinj : ∀ a ∈ S, ∀ b ∈ S, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    obtain ⟨ia, hia, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨ib, hib, rfl⟩ := Finset.mem_image.mp hb
    have h1 := hψg ia hia
    have h2 := hψg ib hib
    rw [h1, h2] at hab
    exact (hiff ia hia ib hib).mpr hab
  obtain ⟨κ, cc, haff⟩ := zmod3_injOn_affine S ψ hψinj
  have hφaff : ∀ i ∈ Finset.range (m + 1),
      l6p2_tail m w i = κ * l6p2_tail m u i + cc := by
    intro i hi
    have hmem : l6p2_tail m u i ∈ S := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have h := haff (l6p2_tail m u i) hmem
    rw [hψg i hi] at h
    exact h
  have hw_eq : ∀ l : Fin m, αt (hv l) = κ * (αv l ht) := by
    intro l
    have hmem1 : l.val ∈ Finset.range (m + 1) := by
      simp only [Finset.mem_range]
      omega
    have hmem2 : l.val + 1 ∈ Finset.range (m + 1) := by
      simp only [Finset.mem_range]
      omega
    have h1 := hφaff l.val hmem1
    have h2 := hφaff (l.val + 1) hmem2
    have hwt := l6p2_tail_sub_succ m w l.isLt
    have hut := l6p2_tail_sub_succ m u l.isLt
    have hwv : w l.val = αt (hv l) := by
      dsimp only [w]
      exact dif_pos l.isLt
    have huv : u l.val = αv l ht := by
      dsimp only [u]
      exact dif_pos l.isLt
    calc αt (hv l) = w l.val := hwv.symm
      _ = l6p2_tail m w l.val - l6p2_tail m w (l.val + 1) := hwt.symm
      _ = (κ * l6p2_tail m u l.val + cc) - (κ * l6p2_tail m u (l.val + 1) + cc) := by
            rw [h1, h2]
      _ = κ * (l6p2_tail m u l.val - l6p2_tail m u (l.val + 1)) := by ring
      _ = κ * u l.val := by rw [hut]
      _ = κ * (αv l ht) := by rw [huv]
  exact ⟨κ, hw_eq⟩

theorem ggIndep_p3_refl_fixes_x {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod 3) V) (c : Fin m → ZMod 3)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod 3))
    (ht : V) (αt : Module.Dual (ZMod 3) V) (hcα : (∑ i, c i • αv i) ht = 0)
    (hCLL : ∀ i j : ℕ, i < j → j ≤ m →
      ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), αv l) ht = 0 ↔
        αt (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), hv l) = 0)) :
    αt (∑ i, c i • hv i) = 0 := by
  obtain ⟨κ, hw_eq⟩ := ggIndep_p3_refl_affine hv αv ht αt hCLL
  have hfinal1 : αt (∑ i, c i • hv i) = ∑ i, c i * (κ * (αv i ht)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, hw_eq i]
    simp
  have hfinal2 : (∑ i, c i * (κ * (αv i ht))) = κ * ((∑ i, c i • αv i) ht) := by
    rw [LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hfinal1, hfinal2, hcα]
  simp

end CFSG.StandardType

end
