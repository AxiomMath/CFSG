module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Link
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory
public import CFSG.RankThree.PartOne.KE.SLnShape

public section

namespace CFSG.StandardType.LieKnownR2.LinkF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.StandardType.LieKnownR2.Q2 CFSG.StandardType.LieKnownR2.Link

structure LinkDataF4 (d : ℕ) (L1 Γ : List (Fin Tag.F4.rank → ℤ)) (gens : List (List ℕ)) :
    Prop where
  len : L1.length = d
  nodup : L1.Nodup
  deg1 : ∀ α, α ∈ L1 ↔ α ∈ Deg1 Tag.F4
  gam : ∀ γ ∈ Γ, IsRoot Tag.F4 γ ∧ γ (iθ Tag.F4) = 0
  glen : gens.length = Γ.length
  bits : ∀ k < Γ.length, ∀ i j : Fin d, bit ((gens.getD k []).getD j 0) i =
    (if i = j then 1 else 0) +
      (if L1.getD i 0 = Γ.getD k 0 + L1.getD j 0 ∧
          L1.getD j 0 - Γ.getD k 0 ∉ rootFinset Tag.F4 then 1 else 0) +
      (if L1.getD i 0 = 2 • Γ.getD k 0 + L1.getD j 0 then 1 else 0)

private theorem getD_mem_of_lt {α : Type*} {l : List α} {k : ℕ} (hk : k < l.length) (a : α) :
    l.getD k a ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

private theorem getD_eq_getElem' {α : Type*} {l : List α} {k : ℕ} (hk : k < l.length) (a : α) :
    l.getD k a = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

private theorem deg1_sub_deg1Roots
    {β : Fin Tag.F4.rank → ℤ} (h : β ∈ Deg1 Tag.F4) : β ∈ deg1Roots := by
  have h1 : ∀ β ∈ rootFinset .F4, β 0 = 1 → β ∈ deg1Roots := by decide +kernel
  exact h1 β (mem_rootFinset.2 h.1) h.2

private theorem intCast_of_abs_eq_two {K : Type} [Field K] [CharP K 2] {z : ℤ} (h : |z| = 2) :
    (z : K) = 0 := by
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).1 h with rfl | rfl <;> simp [CharTwo.two_eq_zero]

private theorem intCast_of_abs_eq_one {K : Type} [Field K] [CharP K 2] {z : ℤ} (h : |z| = 1) :
    (z : K) = 1 := by
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 h with rfl | rfl <;> simp [CharTwo.neg_eq]

private theorem sum_pick {K : Type} [Field K] {d : ℕ} {L1 : List (Fin Tag.F4.rank → ℤ)}
    (hlen : L1.length = d) (hnd : L1.Nodup) (c : (Fin Tag.F4.rank → ℤ) → K)
    (ν s : Fin Tag.F4.rank → ℤ) (P : (Fin Tag.F4.rank → ℤ) → Prop) [DecidablePred P] :
    ∑ j : Fin d, (if ν = s + L1.getD j 0 ∧ P (L1.getD j 0) then c (L1.getD j 0) else 0) =
      if ν - s ∈ L1 ∧ P (ν - s) then c (ν - s) else 0 := by
  classical
  by_cases hm : ν - s ∈ L1
  · obtain ⟨n, hn, hjn⟩ := List.mem_iff_getElem.1 hm
    let j0 : Fin d := ⟨n, hlen ▸ hn⟩
    have hj0 : L1.getD j0 0 = ν - s := by rw [getD_eq_getElem' hn, hjn]
    rw [Finset.sum_eq_single j0]
    · rw [hj0]
      have e : ν = s + (ν - s) := by abel
      by_cases hP : P (ν - s)
      · rw [if_pos ⟨e, hP⟩, if_pos ⟨hm, hP⟩]
      · rw [if_neg (fun h => hP h.2), if_neg (fun h => hP h.2)]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨he, -⟩
      apply hj
      have e1 : L1.getD j 0 = L1.getD j0 0 := by rw [hj0, he]; abel
      rw [getD_eq_getElem' (hlen ▸ j.2), getD_eq_getElem' hn] at e1
      exact Fin.ext ((hnd.getElem_inj_iff).1 e1)
    · simp
  · rw [if_neg (fun h => hm h.1)]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    rintro ⟨he, -⟩
    apply hm
    have : L1.getD j 0 = ν - s := by rw [he]; abel
    rw [← this]
    exact getD_mem_of_lt (hlen ▸ j.2) 0

theorem cvec_conj_genF4
    {K : Type} [Field K] [CharP K 2] {d : ℕ} {L1 Γ : List (Fin Tag.F4.rank → ℤ)}
    {gens : List (List ℕ)} (D : LinkDataF4 d L1 Γ gens) {k : ℕ} (hk : k < Γ.length)
    {q : ModGL Tag.F4 K} (hq : q ∈ Qθ Tag.F4 K) :
    cvec L1 d (pinnedX Tag.F4 K (Γ.getD k 0) 1 * q * (pinnedX Tag.F4 K (Γ.getD k 0) 1)⁻¹) =
      ((toMat d (gens.getD k [])).map (φ2 (K := K))).mulVec (cvec L1 d q) := by
  classical
  obtain ⟨a1, a2, h1, h2, hact⟩ := exists_action_data K
  have hγ := D.gam _ (getD_mem_of_lt hk 0)
  set γ := Γ.getD k 0 with hγdef
  have hs := heisCoord_spec Tag.F4 K
  have hmem : ∀ j : Fin d, L1.getD j 0 ∈ L1 := fun j => getD_mem_of_lt (D.len ▸ j.2) 0
  have hact' := hact γ (mem_rootFinset.2 hγ.1) hγ.2 1 q hq
  funext i
  set ν := L1.getD i 0 with hν
  have hνD : ν ∈ Deg1 Tag.F4 := (D.deg1 ν).1 (hmem i)
  have hνΦ : ν ∈ rootFinset Tag.F4 := mem_rootFinset.2 hνD.1
  simp only [cvec, Matrix.mulVec, dotProduct, Matrix.map_apply, toMat, Matrix.of_apply,
    D.bits k hk, map_add, apply_ite (φ2 (K := K)), map_one, map_zero, add_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hact', actFun]
  simp only [one_mul, one_pow]
  rw [← hν]
  have hsA := sum_pick (K := K) D.len D.nodup (heisCoord Tag.F4 K q) ν γ
    (fun μ => μ - γ ∉ rootFinset Tag.F4)
  have hsB := sum_pick (K := K) D.len D.nodup (heisCoord Tag.F4 K q) ν (2 • γ) (fun _ => True)
  simp only [and_true] at hsB
  rw [hsA, hsB]
  congr 1
  congr 1
  ·
    by_cases hm : ν - γ ∈ L1
    · have hμ : ν - γ ∈ Deg1 Tag.F4 := (D.deg1 _).1 hm
      have hμR := deg1_sub_deg1Roots hμ
      have hA := (h1 γ (mem_rootFinset.2 hγ.1) hγ.2 (ν - γ) hμR).1
        (by rw [add_sub_cancel]; exact hνΦ)
      by_cases hr : ν - γ - γ ∈ rootFinset Tag.F4
      · rw [if_pos hr] at hA
        rw [intCast_of_abs_eq_two hA, if_neg (fun h => h.2 hr)]
        simp
      · rw [if_neg hr] at hA
        rw [intCast_of_abs_eq_one hA, if_pos ⟨hm, hr⟩]
        simp
    · have h0 : heisCoord Tag.F4 K q (ν - γ) = 0 := by
        apply hs.support q hq
        exact fun h => hm ((D.deg1 _).2 h)
      rw [h0, if_neg (fun h => hm h.1)]
      simp
  ·
    by_cases hm : ν - 2 • γ ∈ L1
    · have hμ : ν - 2 • γ ∈ Deg1 Tag.F4 := (D.deg1 _).1 hm
      have hμR := deg1_sub_deg1Roots hμ
      have hB := (h2 γ (mem_rootFinset.2 hγ.1) hγ.2 (ν - 2 • γ) hμR).1
        (by rw [add_sub_cancel]; exact hνΦ)
      rw [intCast_of_abs_eq_one hB, if_pos hm]
      simp
    · have h0 : heisCoord Tag.F4 K q (ν - 2 • γ) = 0 := by
        apply hs.support q hq
        exact fun h => hm ((D.deg1 _).2 h)
      rw [h0, if_neg hm]
      simp

theorem LinkDataF4.core
    {d : ℕ} {L1 Γ : List (Fin Tag.F4.rank → ℤ)} {gens : List (List ℕ)}
    (D : LinkDataF4 d L1 Γ gens) : LinkCore Tag.F4 d L1 Γ gens :=
  ⟨D.len, D.deg1, D.gam, D.glen, fun _ _ _ _ hk _ hq => cvec_conj_genF4 D hk hq⟩

def L1F4 : List (Fin Tag.F4.rank → ℤ) :=
  [![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 0], ![1, 1, 2, 1],
    ![1, 1, 2, 2], ![1, 2, 2, 0], ![1, 2, 2, 1], ![1, 2, 2, 2], ![1, 2, 3, 1], ![1, 2, 3, 2],
    ![1, 2, 4, 2], ![1, 3, 4, 2]]

def gamF4 : List (Fin Tag.F4.rank → ℤ) :=
  [![0, 1, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0], ![0, 0, -1, 0], ![0, 0, 0, 1], ![0, 0, 0, -1]]

theorem linkF4 :
    LinkDataF4 14 L1F4 gamF4 gensF4 where
  len := by decide
  nodup := by decide +kernel
  deg1 := deg1_of_filter (by decide +kernel)
  gam := gam_of_check (by decide +kernel)
  glen := by decide
  bits := by decide +kernel

theorem F4_exists_odd_fpf
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ h ∈ Pθ .F4 K, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .F4 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .F4 K → q ∈ Uθ .F4 K :=
  exists_odd_fpf linkF4.core (by decide) certF4

end CFSG.StandardType.LieKnownR2.LinkF4
