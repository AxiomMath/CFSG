module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4A6S6
import CFSG.Goldschmidt.Steps.G63Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

private def w183finG4A6_isInvC (c : List Nat) : Bool :=
  A6Facts.Core.cmul c c == A6Facts.Core.cid && c != A6Facts.Core.cid

private def w183finG4A6_comm (a b : List Nat) : Bool :=
  A6Facts.Core.cmul a b == A6Facts.Core.cmul b a

private def w183finG4A6_e8free (iv : List (List Nat)) (b : List Nat) : Bool :=
  let cb := iv.filter (fun c => c != b && w183finG4A6_comm b c)
  cb.all fun c => cb.all fun d =>
    !(d != c && d != A6Facts.Core.cmul b c && w183finG4A6_comm c d)

private def w183finG4A6_outerE8free : Bool :=
  let iv := A6Facts.Core.autL.filter w183finG4A6_isInvC
  iv.all fun b => A6Facts.Core.inS6 b || w183finG4A6_e8free iv b

private def w183finG4A6_pE8free : Bool :=
  let iv := A6Facts.Core.pslLit.filter w183finG4A6_isInvC
  iv.all fun b => w183finG4A6_e8free iv b

private theorem w183finG4A6_outerE8free_eq_true : w183finG4A6_outerE8free = true := by
  decide +kernel

private theorem w183finG4A6_pE8free_eq_true : w183finG4A6_pE8free = true := by
  decide +kernel

private theorem w183finG4A6_code_comm (x y : P10) :
    w183finG4A6_comm (code x) (code y) = true ↔ x * y = y * x := by
  unfold w183finG4A6_comm
  rw [← code_mul, ← code_mul, beq_iff_eq]
  exact ⟨fun h => code_injective h, fun h => by rw [h]⟩

private theorem w183finG4A6_code_isInv (x : P10) :
    w183finG4A6_isInvC (code x) = true ↔ x * x = 1 ∧ x ≠ 1 := by
  unfold w183finG4A6_isInvC
  rw [← code_mul, ← code_one, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  exact ⟨fun ⟨h1, h2⟩ => ⟨code_injective h1, fun h => h2 (by rw [h])⟩,
    fun ⟨h1, h2⟩ => ⟨by rw [h1], fun h => h2 (code_injective h)⟩⟩

private theorem w183finG4A6_not_e8free {iv : List (List Nat)} {b c d : List Nat}
    (hc : c ∈ iv) (hd : d ∈ iv)
    (hbc : w183finG4A6_comm b c = true) (hbd : w183finG4A6_comm b d = true)
    (hcd : w183finG4A6_comm c d = true)
    (hcb : c ≠ b) (hdb : d ≠ b) (hdc : d ≠ c) (hbdc : d ≠ A6Facts.Core.cmul b c)
    (h : w183finG4A6_e8free iv b = true) : False := by
  unfold w183finG4A6_e8free at h
  rw [List.all_eq_true] at h
  have hcv : c ∈ iv.filter (fun c => c != b && w183finG4A6_comm b c) := by
    refine List.mem_filter.2 ⟨hc, ?_⟩
    rw [Bool.and_eq_true, bne_iff_ne]
    exact ⟨hcb, hbc⟩
  have hdv : d ∈ iv.filter (fun c => c != b && w183finG4A6_comm b c) := by
    refine List.mem_filter.2 ⟨hd, ?_⟩
    rw [Bool.and_eq_true, bne_iff_ne]
    exact ⟨hdb, hbd⟩
  have h1 := h c hcv
  rw [List.all_eq_true] at h1
  have h2 := h1 d hdv
  have hconj : (d != c && d != A6Facts.Core.cmul b c && w183finG4A6_comm c d) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne]
    exact ⟨⟨hdc, hbdc⟩, hcd⟩
  rw [hconj] at h2
  exact Bool.false_ne_true h2

private theorem w183finG4A6_exists_ne_one_of_card_eight {X : Type} [Group X] [Finite X]
    {B : Subgroup X} (h8 : 8 ≤ Nat.card B) : ∃ x ∈ B, x ≠ 1 := by
  haveI : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : B)
  exact ⟨(x : X), x.2, fun h => hx (Subtype.ext h)⟩

private theorem w183finG4A6_exists_three {X : Type} [Group X] [Finite X] {B : Subgroup X}
    (hel : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B) {x : X} (hxB : x ∈ B) (hx1 : x ≠ 1) :
    ∃ y z : X, y ∈ B ∧ z ∈ B ∧ y * y = 1 ∧ y ≠ 1 ∧ z * z = 1 ∧ z ≠ 1 ∧
      x * y = y * x ∧ x * z = z * x ∧ y * z = z * y ∧
      y ≠ x ∧ z ≠ x ∧ z ≠ y ∧ z ≠ x * y := by
  have hx2 : x ^ 2 = 1 := hel.2 x hxB
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hcardx : Nat.card (Subgroup.zpowers x) = 2 := by rw [Nat.card_zpowers, hxo]
  have hnotle : ¬ B ≤ Subgroup.zpowers x := by
    intro hle
    have hle2 := Subgroup.card_le_of_le hle
    rw [hcardx] at hle2
    omega
  have hnotsub : ¬ (B : Set X) ⊆ (Subgroup.zpowers x : Set X) := fun h => hnotle h
  obtain ⟨y, hyB, hyNot⟩ := Set.not_subset.mp hnotsub
  have hy1 : y ≠ 1 := fun h => hyNot (by rw [h]; exact Subgroup.one_mem _)
  have hy2 : y ^ 2 = 1 := hel.2 y hyB
  have hcommxy : x * y = y * x := hel.comm hxB hyB
  obtain ⟨-, hAcard⟩ :=
    CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian (p := 2) Nat.prime_two hy2 hx2 hx1 hyNot
      hcommxy.symm
  have hxA : x ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hyA : y ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hxyA : x * y ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x :=
    (Subgroup.zpowers y ⊔ Subgroup.zpowers x).mul_mem hxA hyA
  have hnotsub2 : ¬ (B : Set X) ⊆
      ((Subgroup.zpowers y ⊔ Subgroup.zpowers x : Subgroup X) : Set X) := by
    intro hsub
    have hcard := Subgroup.card_le_of_le hsub
    have h4 : Nat.card B ≤ 4 := by
      calc Nat.card B ≤ Nat.card (Subgroup.zpowers y ⊔ Subgroup.zpowers x : Subgroup X) := hcard
        _ = 2 ^ 2 := hAcard
        _ = 4 := by norm_num
    omega
  obtain ⟨z, hzB, hzNot⟩ := Set.not_subset.mp hnotsub2
  refine ⟨y, z, hyB, hzB, by rw [← pow_two]; exact hy2, hy1,
    by rw [← pow_two]; exact hel.2 z hzB, ?_, hcommxy, hel.comm hxB hzB,
    hel.comm hyB hzB, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hzNot (by rw [h]; exact Subgroup.one_mem _)
  · intro h
    exact hyNot (by rw [h]; exact Subgroup.mem_zpowers x)
  · intro h
    exact hzNot (by rw [h]; exact hxA)
  · intro h
    exact hzNot (by rw [h]; exact hyA)
  · intro h
    exact hzNot (by rw [h]; exact hxyA)

theorem w183finG4A6_model_e8_le_s6 (B : Subgroup P10) (hB : B ≤ A6Models.autA6)
    (hab : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B) : B ≤ A6Facts.s6 := by
  by_contra hnot
  have hnot' : ∃ x : P10, x ∈ B ∧ x ∉ A6Facts.s6 := by
    by_contra h
    apply hnot
    intro x hx
    by_contra hx6
    exact h ⟨x, hx, hx6⟩
  obtain ⟨x, hxB, hxs6⟩ := hnot'
  have hx1 : x ≠ 1 := fun h => hxs6 (by rw [h]; exact A6Facts.s6.one_mem)
  have hx2 : x * x = 1 := by simpa [pow_two] using hab.2 x hxB
  obtain ⟨y, z, hyB, hzB, hy2, hy1, hz2, hz1, hxy, hxz, hyz, hyx, hzx, hzy, hzxy⟩ :=
    w183finG4A6_exists_three hab h8 hxB hx1
  have hchk := w183finG4A6_outerE8free_eq_true
  unfold w183finG4A6_outerE8free at hchk
  rw [List.all_eq_true] at hchk
  have hxiv : code x ∈ A6Facts.Core.autL.filter w183finG4A6_isInvC :=
    List.mem_filter.2 ⟨A6Facts.code_mem_autL (hB hxB),
      (w183finG4A6_code_isInv x).2 ⟨hx2, hx1⟩⟩
  have h1 := hchk (code x) hxiv
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact hxs6 ((A6Facts.mem_s6_iff x).2 h1)
  · have hyiv : code y ∈ A6Facts.Core.autL.filter w183finG4A6_isInvC :=
      List.mem_filter.2 ⟨A6Facts.code_mem_autL (hB hyB),
        (w183finG4A6_code_isInv y).2 ⟨hy2, hy1⟩⟩
    have hziv : code z ∈ A6Facts.Core.autL.filter w183finG4A6_isInvC :=
      List.mem_filter.2 ⟨A6Facts.code_mem_autL (hB hzB),
        (w183finG4A6_code_isInv z).2 ⟨hz2, hz1⟩⟩
    exact w183finG4A6_not_e8free hyiv hziv
      ((w183finG4A6_code_comm x y).2 hxy) ((w183finG4A6_code_comm x z).2 hxz)
      ((w183finG4A6_code_comm y z).2 hyz)
      (fun h => hyx (code_injective h)) (fun h => hzx (code_injective h))
      (fun h => hzy (code_injective h))
      (fun h => hzxy (code_injective (h.trans (A6Facts.code_mul x y).symm))) h1

theorem w183finG4A6_model_psl_sup (B : Subgroup P10) (hB : B ≤ A6Facts.s6)
    (hab : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B) : A6Models.psl29 ⊔ B = A6Facts.s6 := by
  have hpsl_le : A6Models.psl29 ≤ A6Facts.s6 := A6Facts.psl29_le_s6
  have hsup_le : A6Models.psl29 ⊔ B ≤ A6Facts.s6 := sup_le hpsl_le hB
  have hBnotpsl : ¬ B ≤ A6Models.psl29 := by
    intro hBpsl
    obtain ⟨x, hxB, hx1⟩ := w183finG4A6_exists_ne_one_of_card_eight (B := B) h8
    have hx2 : x * x = 1 := by simpa [pow_two] using hab.2 x hxB
    obtain ⟨y, z, hyB, hzB, hy2, hy1, hz2, hz1, hxy, hxz, hyz, hyx, hzx, hzy, hzxy⟩ :=
      w183finG4A6_exists_three hab h8 hxB hx1
    have hchk := w183finG4A6_pE8free_eq_true
    unfold w183finG4A6_pE8free at hchk
    rw [List.all_eq_true] at hchk
    have hxL : code x ∈ A6Facts.Core.pslLit.filter w183finG4A6_isInvC :=
      List.mem_filter.2 ⟨(A6Facts.mem_psl29_iff x).1 (hBpsl hxB),
        (w183finG4A6_code_isInv x).2 ⟨hx2, hx1⟩⟩
    have hyL : code y ∈ A6Facts.Core.pslLit.filter w183finG4A6_isInvC :=
      List.mem_filter.2 ⟨(A6Facts.mem_psl29_iff y).1 (hBpsl hyB),
        (w183finG4A6_code_isInv y).2 ⟨hy2, hy1⟩⟩
    have hzL : code z ∈ A6Facts.Core.pslLit.filter w183finG4A6_isInvC :=
      List.mem_filter.2 ⟨(A6Facts.mem_psl29_iff z).1 (hBpsl hzB),
        (w183finG4A6_code_isInv z).2 ⟨hz2, hz1⟩⟩
    have h1 := hchk (code x) hxL
    exact w183finG4A6_not_e8free hyL hzL
      ((w183finG4A6_code_comm x y).2 hxy) ((w183finG4A6_code_comm x z).2 hxz)
      ((w183finG4A6_code_comm y z).2 hyz)
      (fun h => hyx (code_injective h)) (fun h => hzx (code_injective h))
      (fun h => hzy (code_injective h))
      (fun h => hzxy (code_injective (h.trans (A6Facts.code_mul x y).symm))) h1
  have hne : A6Models.psl29 ⊔ B ≠ A6Models.psl29 := by
    intro h
    exact hBnotpsl (le_sup_right.trans (le_of_eq h))
  have hrel : A6Models.psl29.relIndex (A6Models.psl29 ⊔ B) *
      (A6Models.psl29 ⊔ B).relIndex A6Facts.s6 = 2 := by
    rw [Subgroup.relIndex_mul_relIndex A6Models.psl29 (A6Models.psl29 ⊔ B) A6Facts.s6
      le_sup_left hsup_le, w183finG4A6_model_psl_s6.2]
  have hne1 : A6Models.psl29.relIndex (A6Models.psl29 ⊔ B) ≠ 1 := by
    intro h1
    exact hne (le_antisymm ((Subgroup.relIndex_eq_one).mp h1) le_sup_left)
  have h2 : A6Models.psl29.relIndex (A6Models.psl29 ⊔ B) = 2 := by
    have hdvd : A6Models.psl29.relIndex (A6Models.psl29 ⊔ B) ∣ 2 := ⟨_, hrel.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hb1 : (A6Models.psl29 ⊔ B).relIndex A6Facts.s6 = 1 := by
    rw [h2] at hrel
    omega
  exact le_antisymm hsup_le ((Subgroup.relIndex_eq_one).mp hb1)

end CFSG.LocalAnalysis.WeakClosure81

end
