module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_false {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X)
    (h21 : Nat.card (autI hd.setting.isElemAbelian M) = 21)
    (h3 : Nat.card (autI hd.setting.isElemAbelian X) = 3) (h8 : Nat.card V = 8) : False := by
  obtain ⟨A, L', X', hfam, hdist⟩ := eleven11_exists_family hd h21 h3 h8
  choose hd' h3' using hfam
  let D : Fin 7 → Subgroup G := fun i => Q ⊓ centralizerModCore (L' i)
  have hD32 : ∀ i, Nat.card (D i) = 32 := fun i =>
    (eleven11_card_D (hd' i) h21 (h3' i) h8).1
  have hVD : ∀ i, V ≤ D i := fun i => eleven11_V_le_D (hd' i) h21 (h3' i) h8
  have hinf : ∀ i j, i ≠ j → D i ⊓ D j = V := fun i j hij =>
    eleven11_D_inf_D (hd' i) (hd' j) h21 (h3' i) (h3' j) h8 (hdist i j hij)
  have hcount := card_add_mul_le_of_inf_eq (B := V) (Q := Q) (K := D) (b := 8) (k := 32) h8
    hD32 hd.setting.V_le_Q hVD (fun i => inf_le_left) hinf
  rw [(eleven11_card_D hd h21 h3 h8).2] at hcount
  simp at hcount

theorem eleven11Closing_holds {M V Q : Subgroup G} :
    Eleven11Closing M V Q := fun _ _ _ hd h21 h3 h8 => eleven11_false hd h21 h3 h8

end CFSG.LocalAnalysis.WeakClosure81
