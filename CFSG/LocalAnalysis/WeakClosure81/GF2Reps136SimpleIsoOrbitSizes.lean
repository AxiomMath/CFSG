module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoRanks
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoThirdPoint

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q]

def w1369_ta_orb (N : Subgroup (MulAut Q)) (S : Subgroup Q) : Set (Subgroup Q) :=
  {T | ∃ n : N, T = S.map (n : MulAut Q).toMonoidHom}

lemma w1369_ta_mem_orb_iff {N : Subgroup (MulAut Q)} {S T : Subgroup Q} :
    T ∈ w1369_ta_orb N S ↔ ∃ n : N, T = S.map (n : MulAut Q).toMonoidHom :=
  Iff.rfl

lemma w1369_ta_mem_orb_self (N : Subgroup (MulAut Q)) (S : Subgroup Q) :
    S ∈ w1369_ta_orb N S :=
  ⟨1, by rw [Subgroup.coe_one]; exact (Subgroup.map_id S).symm⟩

lemma w1369_ta_orb_subset {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ) {S : Subgroup Q}
    (hS : w1369_ta_IsSimple Λ S) : w1369_ta_orb N S ⊆ {T | w1369_ta_IsSimple Λ T} := by
  rintro T ⟨n, rfl⟩
  exact w1369_simple_map hnorm hS n.2

lemma w1369_ta_orb_mem_of_mem {N : Subgroup (MulAut Q)} {S T : Subgroup Q}
    (hT : T ∈ w1369_ta_orb N S) (n : N) :
    T.map (n : MulAut Q).toMonoidHom ∈ w1369_ta_orb N S := by
  obtain ⟨m, rfl⟩ := hT
  exact ⟨n * m, by rw [Subgroup.map_map]; rfl⟩

lemma w1369_ta_simple_iso {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {A B : Subgroup Q} (hA : w1369_ta_IsSimple Λ A) (hB : w1369_ta_IsSimple Λ B) :
    SecIsoOn Λ A ⊥ B ⊥ := by
  obtain ⟨i, hi⟩ := w1369_ta_simple_iso_some P hstab hIsimple hA
  obtain ⟨j, hj⟩ := w1369_ta_simple_iso_some P hstab hIsimple hB
  have hij : SecIsoOn Λ (I i) ⊥ (I j) ⊥ := by
    by_cases h : i = j
    · subst h
      exact secIsoOn_refl (hstab i) (fun g hg x hx => by simpa using hx) bot_le
    · exact hisoAll i j h
  exact secIsoOn_trans (secIsoOn_trans (w1369_ta_SecIsoOn_symm hi) hij) hj

lemma w1369_ta_third_triple (hQ : ∀ x : Q, x ^ 2 = 1) {A B C : Subgroup Q}
    (α : ↥A ≃* ↥B) (β : ↥B ≃* ↥C) :
    w1369_ta_third (β.symm.trans α.symm) ≤ w1369_ta_third α ⊔ w1369_ta_third β := by
  rintro y ⟨c, rfl⟩
  have hb : (β.symm c : Q) * (β.symm c : Q) = 1 := by
    simpa [pow_two] using hQ (β.symm c : Q)
  have heq : (w1369_ta_graphHom (β.symm.trans α.symm) c : Q) =
      (w1369_ta_graphHom α (α.symm (β.symm c)) : Q) *
        (w1369_ta_graphHom β (β.symm c) : Q) := by
    change (c : Q) * ((β.symm.trans α.symm) c : Q) =
      ((α.symm (β.symm c) : ↥A) : Q) * (α (α.symm (β.symm c)) : Q) *
        (((β.symm c : ↥B) : Q) * (β (β.symm c) : Q))
    rw [show (β.symm.trans α.symm) c = α.symm (β.symm c) from rfl,
      MulEquiv.apply_symm_apply α (β.symm c), MulEquiv.apply_symm_apply β c]
    calc (c : Q) * (α.symm (β.symm c) : Q)
        = (α.symm (β.symm c) : Q) * (c : Q) := mul_comm _ _
      _ = (α.symm (β.symm c) : Q) * ((β.symm c : Q) * (β.symm c : Q)) * (c : Q) := by
          rw [hb, mul_one]
      _ = ((α.symm (β.symm c) : Q) * (β.symm c : Q)) *
            ((β.symm c : Q) * (c : Q)) := by group
  rw [heq]
  exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

lemma w1369_ta_rk_simple_eq {Λ : Subgroup (MulAut Q)} {k : ℕ} [NeZero k] {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥) {X : Subgroup Q}
    (hX : w1369_ta_IsSimple Λ X) : rk ↥X = rk ↥(I 0) :=
  w1369_ta_rk_eq_of_secIsoOn (w1369_ta_simple_iso P hstab hIsimple hisoAll hX (hIsimple 0))

lemma w1369_ta_orb_ne_one {Λ N : Subgroup (MulAut Q)} {k : ℕ} (hk2 : 2 ≤ k)
    {I : Fin k → Subgroup Q} (hstab : ∀ i, StableUnder Λ (I i))
    (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) {S : Subgroup Q}
    (hS : w1369_ta_IsSimple Λ S) (h1 : (w1369_ta_orb N S).ncard = 1) : False := by
  obtain ⟨T, hT⟩ := Set.ncard_eq_one.mp h1
  have hmem : S ∈ w1369_ta_orb N S := w1369_ta_mem_orb_self N S
  rw [hT] at hmem
  have hTS : T = S := hmem.symm
  have hstabN : StableUnder N S := by
    intro n hn x hx
    have hmem' : S.map (n.toMonoidHom) ∈ w1369_ta_orb N S := by
      have := w1369_ta_orb_mem_of_mem (w1369_ta_mem_orb_self N S) (⟨n, hn⟩ : N)
      simpa using this
    rw [hT, hTS] at hmem'
    have heq : S.map (n.toMonoidHom) = S := by simpa using hmem'
    rw [← heq]
    exact Subgroup.mem_map_of_mem n.toMonoidHom hx
  rcases hirr S hstabN with h | h
  · exact hS.1 h
  · exact w1369_ta_top_not_simple hk2 hstab hIsimple hind (h ▸ hS)

lemma w1369_ta_orb_ne_two [Finite Q] {Λ N : Subgroup (MulAut Q)}
    (hQ : ∀ x : Q, x ^ 2 = 1) (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} (hk3 : k = 3) {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i)) (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hspan : ⨆ i, I i = ⊤)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) {S : Subgroup Q}
    (hS : w1369_ta_IsSimple Λ S) (h2 : (w1369_ta_orb N S).ncard = 2) : False := by
  subst hk3
  obtain ⟨A, B, hAB, hABeq⟩ := Set.ncard_eq_two.mp h2
  have hAmem : A ∈ w1369_ta_orb N S := by rw [hABeq]; simp
  have hBmem : B ∈ w1369_ta_orb N S := by rw [hABeq]; simp
  have hA : w1369_ta_IsSimple Λ A := w1369_ta_orb_subset hnorm hS hAmem
  have hB : w1369_ta_IsSimple Λ B := w1369_ta_orb_subset hnorm hS hBmem
  have hABinf : A ⊓ B = ⊥ := w1369_ta_inf_eq_bot hA hB hAB
  have hstabN : StableUnder N (A ⊔ B) := by
    intro n hn x hx
    have hAn : A.map (n.toMonoidHom) ∈ w1369_ta_orb N S := by
      have := w1369_ta_orb_mem_of_mem hAmem (⟨n, hn⟩ : N)
      simpa using this
    have hBn : B.map (n.toMonoidHom) ∈ w1369_ta_orb N S := by
      have := w1369_ta_orb_mem_of_mem hBmem (⟨n, hn⟩ : N)
      simpa using this
    rw [hABeq] at hAn hBn
    have hAle : A.map (n.toMonoidHom) ≤ A ⊔ B := by
      rcases (by simpa using hAn : A.map (n.toMonoidHom) = A ∨ A.map (n.toMonoidHom) = B)
        with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    have hBle : B.map (n.toMonoidHom) ≤ A ⊔ B := by
      rcases (by simpa using hBn : B.map (n.toMonoidHom) = A ∨ B.map (n.toMonoidHom) = B)
        with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    have hle : (A ⊔ B).map n.toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      exact sup_le hAle hBle
    exact hle (Subgroup.mem_map_of_mem n.toMonoidHom hx)
  have hproper : A ⊔ B ≠ ⊤ := by
    intro htop
    have hAd : rk ↥A = rk ↥(I 0) := w1369_ta_rk_simple_eq P hstab hIsimple hisoAll hA
    have hBd : rk ↥B = rk ↥(I 0) := w1369_ta_rk_simple_eq P hstab hIsimple hisoAll hB
    have h1 : rk ↥(A ⊔ B) = rk ↥A + rk ↥B := by
      have h := rk_sup_add_rk_inf A B
      rw [hABinf, rk_bot, add_zero] at h
      exact h
    have h2 : rk ↥(A ⊔ B) = rk ↥(⊤ : Subgroup Q) := by rw [htop]
    have h1d : rk ↥(I 1) = rk ↥(I 0) :=
      w1369_ta_rk_eq_of_secIsoOn (hisoAll 1 0 (by decide))
    have h2d : rk ↥(I 2) = rk ↥(I 0) :=
      w1369_ta_rk_eq_of_secIsoOn (hisoAll 2 0 (by decide))
    have h3 : rk ↥(⊤ : Subgroup Q) = rk ↥(I 0) + rk ↥(I 1) + rk ↥(I 2) :=
      w1369_ta_rk_sup_three hspan hind
    rw [h1d, h2d] at h3
    rw [hAd, hBd] at h1
    have hd : rk ↥(I 0) ≠ 0 := by
      intro h0
      exact (hIsimple 0).1 ((rk_eq_zero_iff hQ (H := I 0)).mp h0)
    omega
  rcases hirr (A ⊔ B) hstabN with h | h
  · exact hA.1 (le_bot_iff.mp (le_sup_left.trans (le_of_eq h)))
  · exact hproper h

lemma w1369_ta_exists_equiv {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (hA : StableUnder Λ A) (hB : StableUnder Λ B) (h : SecIsoOn Λ A ⊥ B ⊥) :
    ∃ e : ↥A ≃* ↥B, w1369_ta_Equiv hA hB e := by
  obtain ⟨e, he⟩ := w1369_ta_exists_mulEquiv_of_secIsoOn h
  refine ⟨e, ?_⟩
  intro g hg x
  convert he g hg x using 2

lemma w1369_ta_third_mem_triple {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hpart : ∀ i : Fin k, ∃ j : Fin k, j ≠ i)
    {A B C : Subgroup Q} (hA : w1369_ta_IsSimple Λ A) (hB : w1369_ta_IsSimple Λ B)
    (hC : w1369_ta_IsSimple Λ C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {α : ↥A ≃* ↥B} (hα : w1369_ta_Equiv hA.2.1 hB.2.1 α)
    {β : ↥B ≃* ↥C} (hβ : w1369_ta_Equiv hB.2.1 hC.2.1 β)
    {γ : ↥C ≃* ↥A} (hγ : w1369_ta_Equiv hC.2.1 hA.2.1 γ)
    {X Y : Subgroup Q} (hX : w1369_ta_IsSimple Λ X) (hY : w1369_ta_IsSimple Λ Y)
    (hXY : X ≠ Y) (hXm : X ∈ ({A, B, C} : Set (Subgroup Q)))
    (hYm : Y ∈ ({A, B, C} : Set (Subgroup Q))) (e : ↥X ≃* ↥Y)
    (he : w1369_ta_Equiv hX.2.1 hY.2.1 e) :
    w1369_ta_third e ∈ ({w1369_ta_third α, w1369_ta_third β, w1369_ta_third γ} :
      Set (Subgroup Q)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hXm hYm
  rcases hXm with hXm | hXm | hXm <;> subst X <;>
    rcases hYm with hYm | hYm | hYm <;> subst Y
  · exact absurd rfl hXY
  · have h := w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart (X := A) (Y := B)
      hX hY (w1369_ta_inf_eq_bot hX hY hXY) (e := α) hα
      (w1369_ta_third_isSimple hX hY (w1369_ta_inf_eq_bot hX hY hXY) e he)
      (w1369_ta_third_le_sup e)
      (w1369_ta_third_ne_left hX (w1369_ta_inf_eq_bot hX hY hXY) e)
      (w1369_ta_third_ne_right hX (w1369_ta_inf_eq_bot hX hY hXY) e)
    rw [h]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · have h := w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart (X := C) (Y := A)
      hC hA (by rw [inf_comm]; exact w1369_ta_inf_eq_bot hA hC hAC) (e := γ) hγ
      (w1369_ta_third_isSimple hX hY (w1369_ta_inf_eq_bot hX hY hXY) e he)
      (by rw [sup_comm]; exact w1369_ta_third_le_sup e)
      (w1369_ta_third_ne_right hX (w1369_ta_inf_eq_bot hX hY hXY) e)
      (w1369_ta_third_ne_left hX (w1369_ta_inf_eq_bot hX hY hXY) e)
    rw [h]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr
      (Set.mem_singleton_iff.mpr rfl))))
  · have h := w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart (X := A) (Y := B)
      hA hB (w1369_ta_inf_eq_bot hA hB hAB) (e := α) hα
      (w1369_ta_third_isSimple hX hY (w1369_ta_inf_eq_bot hX hY hXY) e he)
      (by rw [sup_comm]; exact w1369_ta_third_le_sup e)
      (w1369_ta_third_ne_right hX (w1369_ta_inf_eq_bot hX hY hXY) e)
      (w1369_ta_third_ne_left hX (w1369_ta_inf_eq_bot hX hY hXY) e)
    rw [h]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · exact absurd rfl hXY
  · have h := w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart (X := B) (Y := C)
      hX hY (w1369_ta_inf_eq_bot hX hY hXY) (e := β) hβ
      (w1369_ta_third_isSimple hX hY (w1369_ta_inf_eq_bot hX hY hXY) e he)
      (w1369_ta_third_le_sup e)
      (w1369_ta_third_ne_left hX (w1369_ta_inf_eq_bot hX hY hXY) e)
      (w1369_ta_third_ne_right hX (w1369_ta_inf_eq_bot hX hY hXY) e)
    rw [h]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl)))
  · have h := w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart (X := C) (Y := A)
      hC hA (by rw [inf_comm]; exact w1369_ta_inf_eq_bot hA hC hAC) (e := γ) hγ
      (w1369_ta_third_isSimple hX hY (w1369_ta_inf_eq_bot hX hY hXY) e he)
      (w1369_ta_third_le_sup e)
      (w1369_ta_third_ne_left hX (w1369_ta_inf_eq_bot hX hY hXY) e)
      (w1369_ta_third_ne_right hX (w1369_ta_inf_eq_bot hX hY hXY) e)
    rw [h]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr
      (Set.mem_singleton_iff.mpr rfl))))
  · have h := w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart (X := B) (Y := C)
      hB hC (w1369_ta_inf_eq_bot hB hC hBC) (e := β) hβ
      (w1369_ta_third_isSimple hX hY (w1369_ta_inf_eq_bot hX hY hXY) e he)
      (by rw [sup_comm]; exact w1369_ta_third_le_sup e)
      (w1369_ta_third_ne_right hX (w1369_ta_inf_eq_bot hX hY hXY) e)
      (w1369_ta_third_ne_left hX (w1369_ta_inf_eq_bot hX hY hXY) e)
    rw [h]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl)))
  · exact absurd rfl hXY

lemma w1369_ta_orb_ne_three [Finite Q] {Λ N : Subgroup (MulAut Q)}
    (hQ : ∀ x : Q, x ^ 2 = 1) (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {I : Fin 3 → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i)) (hIsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hpart : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), I j) = ⊥)
    (hspan : ⨆ i, I i = ⊤)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) {S : Subgroup Q}
    (hS : w1369_ta_IsSimple Λ S) (h3 : (w1369_ta_orb N S).ncard = 3) : False := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hABC⟩ := Set.ncard_eq_three.mp h3
  have hAmem : A ∈ w1369_ta_orb N S := by rw [hABC]; simp
  have hBmem : B ∈ w1369_ta_orb N S := by rw [hABC]; simp
  have hCmem : C ∈ w1369_ta_orb N S := by rw [hABC]; simp
  have hA : w1369_ta_IsSimple Λ A := w1369_ta_orb_subset hnorm hS hAmem
  have hB : w1369_ta_IsSimple Λ B := w1369_ta_orb_subset hnorm hS hBmem
  have hC : w1369_ta_IsSimple Λ C := w1369_ta_orb_subset hnorm hS hCmem
  have hinfAB : A ⊓ B = ⊥ := w1369_ta_inf_eq_bot hA hB hAB
  have hinfBC : B ⊓ C = ⊥ := w1369_ta_inf_eq_bot hB hC hBC
  have hinfAC : A ⊓ C = ⊥ := w1369_ta_inf_eq_bot hA hC hAC
  have hinfCA : C ⊓ A = ⊥ := by rw [inf_comm]; exact hinfAC
  obtain ⟨α, hα⟩ := w1369_ta_exists_equiv hA.2.1 hB.2.1
    (w1369_ta_simple_iso P hstab hIsimple hisoAll hA hB)
  obtain ⟨β, hβ⟩ := w1369_ta_exists_equiv hB.2.1 hC.2.1
    (w1369_ta_simple_iso P hstab hIsimple hisoAll hB hC)
  obtain ⟨γ, hγ⟩ := w1369_ta_exists_equiv hC.2.1 hA.2.1
    (w1369_ta_simple_iso P hstab hIsimple hisoAll hC hA)
  have hthirdA : w1369_ta_IsSimple Λ (w1369_ta_third α) :=
    w1369_ta_third_isSimple hA hB hinfAB α hα
  have hthirdB : w1369_ta_IsSimple Λ (w1369_ta_third β) :=
    w1369_ta_third_isSimple hB hC hinfBC β hβ
  have hthirdCA : w1369_ta_third γ = w1369_ta_third (β.symm.trans α.symm) :=
    w1369_ta_third_eq P hstab hIsimple hend hisoAll hpart hC hA hinfCA
      (e := β.symm.trans α.symm)
      (w1369_ta_Equiv.trans hC.2.1 hB.2.1 hA.2.1
        (w1369_ta_Equiv.symm hβ) (w1369_ta_Equiv.symm hα))
      (w1369_ta_third_isSimple hC hA hinfCA γ hγ)
      (w1369_ta_third_le_sup γ)
      (w1369_ta_third_ne_left hC hinfCA γ)
      (w1369_ta_third_ne_right hC hinfCA γ)
  have hT3le : w1369_ta_third γ ≤ w1369_ta_third α ⊔ w1369_ta_third β := by
    rw [hthirdCA]
    exact w1369_ta_third_triple hQ α β
  set W : Subgroup Q := w1369_ta_third α ⊔ w1369_ta_third β ⊔ w1369_ta_third γ with hW
  have hWeq : W = w1369_ta_third α ⊔ w1369_ta_third β := by
    rw [hW]
    exact sup_eq_left.mpr hT3le
  have hmemW : ∀ R : Subgroup Q,
      R ∈ ({w1369_ta_third α, w1369_ta_third β, w1369_ta_third γ} : Set (Subgroup Q)) →
      R ≤ W := by
    intro R hR
    rw [hW]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with h | h | h
    · rw [h]; exact le_sup_of_le_left le_sup_left
    · rw [h]; exact le_sup_of_le_left le_sup_right
    · rw [h]; exact le_sup_right
  have hmem_orbit_three : ∀ {X : Subgroup Q}, X ∈ w1369_ta_orb N S →
      ∀ {n : MulAut Q}, n ∈ N → X.map n.toMonoidHom ∈ ({A, B, C} : Set (Subgroup Q)) := by
    intro X hX n hn
    have h1 := w1369_ta_orb_mem_of_mem hX (⟨n, hn⟩ : N)
    rw [hABC] at h1
    simpa using h1
  have hstabW : StableUnder N W := by
    intro n hn x hx
    have hmapW : W.map n.toMonoidHom ≤ W := by
      rw [hW, Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · obtain ⟨e', he'⟩ := w1369_ta_exists_equiv
          (w1369_simple_map hnorm hA hn).2.1 (w1369_simple_map hnorm hB hn).2.1
          (w1369_ta_simple_iso P hstab hIsimple hisoAll
            (w1369_simple_map hnorm hA hn) (w1369_simple_map hnorm hB hn))
        have hmap := w1369_ta_third_map hnorm P hstab hIsimple hend hisoAll hpart
          hA hB hinfAB hα hn he'
        rw [hmap]
        exact hmemW _ (w1369_ta_third_mem_triple P hstab hIsimple hend hisoAll hpart
          hA hB hC hAB hAC hBC hα hβ hγ
          (w1369_simple_map hnorm hA hn) (w1369_simple_map hnorm hB hn)
          (fun h => hAB (w1369_ta_map_injective n h))
          (hmem_orbit_three hAmem hn) (hmem_orbit_three hBmem hn) e' he')
      · obtain ⟨e', he'⟩ := w1369_ta_exists_equiv
          (w1369_simple_map hnorm hB hn).2.1 (w1369_simple_map hnorm hC hn).2.1
          (w1369_ta_simple_iso P hstab hIsimple hisoAll
            (w1369_simple_map hnorm hB hn) (w1369_simple_map hnorm hC hn))
        have hmap := w1369_ta_third_map hnorm P hstab hIsimple hend hisoAll hpart
          hB hC hinfBC hβ hn he'
        rw [hmap]
        exact hmemW _ (w1369_ta_third_mem_triple P hstab hIsimple hend hisoAll hpart
          hA hB hC hAB hAC hBC hα hβ hγ
          (w1369_simple_map hnorm hB hn) (w1369_simple_map hnorm hC hn)
          (fun h => hBC (w1369_ta_map_injective n h))
          (hmem_orbit_three hBmem hn) (hmem_orbit_three hCmem hn) e' he')
      · obtain ⟨e', he'⟩ := w1369_ta_exists_equiv
          (w1369_simple_map hnorm hC hn).2.1 (w1369_simple_map hnorm hA hn).2.1
          (w1369_ta_simple_iso P hstab hIsimple hisoAll
            (w1369_simple_map hnorm hC hn) (w1369_simple_map hnorm hA hn))
        have hmap := w1369_ta_third_map hnorm P hstab hIsimple hend hisoAll hpart
          hC hA hinfCA hγ hn he'
        rw [hmap]
        exact hmemW _ (w1369_ta_third_mem_triple P hstab hIsimple hend hisoAll hpart
          hA hB hC hAB hAC hBC hα hβ hγ
          (w1369_simple_map hnorm hC hn) (w1369_simple_map hnorm hA hn)
          (fun h => hAC (w1369_ta_map_injective n h).symm)
          (hmem_orbit_three hCmem hn) (hmem_orbit_three hAmem hn) e' he')
    exact hmapW (Subgroup.mem_map_of_mem n.toMonoidHom hx)
  have hrkA : rk ↥(w1369_ta_third α) = rk ↥(I 0) :=
    w1369_ta_rk_simple_eq P hstab hIsimple hisoAll hthirdA
  have hrkB : rk ↥(w1369_ta_third β) = rk ↥(I 0) :=
    w1369_ta_rk_simple_eq P hstab hIsimple hisoAll hthirdB
  have hrkW : rk ↥W ≤ 2 * rk ↥(I 0) := by
    rw [hWeq]
    have h := rk_sup_add_rk_inf (w1369_ta_third α) (w1369_ta_third β)
    rw [hrkA, hrkB] at h
    omega
  have hrk1 : rk ↥(I 1) = rk ↥(I 0) := w1369_ta_rk_eq_of_secIsoOn (hisoAll 1 0 (by decide))
  have hrk2 : rk ↥(I 2) = rk ↥(I 0) := w1369_ta_rk_eq_of_secIsoOn (hisoAll 2 0 (by decide))
  have hrtop : rk ↥(⊤ : Subgroup Q) = 3 * rk ↥(I 0) := by
    have h := w1369_ta_rk_sup_three hspan hind
    rw [hrk1, hrk2] at h
    omega
  have hdne : rk ↥(I 0) ≠ 0 := by
    intro h0
    exact (hIsimple 0).1 ((rk_eq_zero_iff hQ (H := I 0)).mp h0)
  have hWtop : W ≠ ⊤ := by
    intro htop
    have h1 : rk ↥W = rk ↥(⊤ : Subgroup Q) := by rw [htop]
    rw [hrtop] at h1
    omega
  have hWbot : W ≠ ⊥ := by
    intro hbot
    have hle : w1369_ta_third α ≤ W := by
      rw [hW]
      exact le_sup_of_le_left le_sup_left
    rw [hbot] at hle
    exact hthirdA.1 (le_bot_iff.mp hle)
  rcases hirr W hstabW with h | h
  · exact hWbot h
  · exact hWtop h

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
