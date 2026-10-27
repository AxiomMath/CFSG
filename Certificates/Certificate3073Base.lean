
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Certificates.Kernel.MonsterB.Sp8RowSpan
public import Certificates.Kernel.MonsterB.Sp8Rows3073
public import Certificates.Kernel.MonsterB.Sp8Xi3073

@[expose] public section

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Co2Inv
open CFSG.KC.KDense CFSG.KC.Rep4371Row CFSG.KC.Sp8Span

namespace CertificateChecks.Batch3073

open CertificateChecks.Sp8Rows3073 CertificateChecks.Sp8Xi3073

theorem forall₂_eYT : ∀ as : List ℕ, List.Forall₂ Twin (as.map eYT) (as.map Model.eYN)
  | [] => .nil
  | a :: as => .cons (twin_eYT a) (forall₂_eYT as)

theorem perm_case {j : ℕ} (hj : j < 9) {P BT : ℕ} (hP : ∀ i < 24, pe P i = (fPerms[j]!)[i]!)
    (hBT : betaTabT P = BT) (s : Bool) (a d : ℕ) (hq : gDiff (23 + j) = (s, a, d))
    (hchk : spanEqT [eYT 3, ePermT P BT 0, ePauliT 0 0 0]
      [ePermT P BT 0, ePauliT 0 0 0, ePauliT s.toNat a d, eYT 3] = true) :
    Native.Sp8.rowChainEq (Model.eYN 3 :: permFs Model.ePermN Model.ePauliN Model.kappaN j)
      (permFs Model.ePermN Model.ePauliN Model.kappaN j ++
        [Model.ePauliN (gDiff (23 + j)), Model.eYN 3]) = true := by
  have hk := kappa63 j hj
  have e : permFs Model.ePermN Model.ePauliN Model.kappaN j =
      [Model.ePermN fPerms[j]!, Model.ePauliN (false, 0, 0)] := by
    unfold permFs
    rw [hk]
    rfl
  have hK : (Model.kappaN fPerms[j]! 63).toNat = 0 := by rw [hk]; rfl
  rw [e, hq]
  refine rowChainEq_of_spanEqT
    (.cons (twin_eYT 3) (.cons (twin_ePermT hP hBT hK) (.cons (twin_ePauliT false 0 0) .nil)))
    (.cons (twin_ePermT hP hBT hK) (.cons (twin_ePauliT false 0 0)
      (.cons (twin_ePauliT s a d) (.cons (twin_eYT 3) .nil)))) ?_ ?_ hchk
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact sAff_eYN 3
    · exact sAff_ePermN _
    · exact sAff_ePauliN _
  · intro f hf
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact sAff_ePermN _
    · exact sAff_ePauliN _
    · exact sAff_ePauliN _
    · exact sAff_eYN 3

theorem sign_case {j : ℕ} (as : List ℕ) (has : signCodesOf j = as) (s : Bool) (a d : ℕ)
    (hq : gDiff (32 + j) = (s, a, d))
    (hchk : spanEqT (eYT 3 :: as.map eYT) (as.map eYT ++ [ePauliT s.toNat a d, eYT 3]) = true) :
    Native.Sp8.rowChainEq (Model.eYN 3 :: signFs Model.eYN j)
      (signFs Model.eYN j ++ [Model.ePauliN (gDiff (32 + j)), Model.eYN 3]) = true := by
  rw [signFs, has, hq]
  refine rowChainEq_of_spanEqT (.cons (twin_eYT 3) (forall₂_eYT as))
    (List.rel_append (forall₂_eYT as) (.cons (twin_ePauliT s a d) (.cons (twin_eYT 3) .nil)))
    ?_ ?_ hchk
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact sAff_eYN 3
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hf
      exact sAff_eYN b
  · intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hf
      exact sAff_eYN b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact sAff_ePauliN _
      · exact sAff_eYN 3

theorem pauliDiff_check_0 :
    ∀ k < 23,
    Model.conjYN 3 (pauliGen k) = Model.Pauli.mul (pauliGen k) (gDiff k) :=
  pauli_check

theorem permRows_1 :
    ∀ j < 9,
    Native.Sp8.rowChainEq (Native.eYN 3 :: permFs Native.ePermN Native.ePauliN Native.kappaN j)
      (permFs Native.ePermN Native.ePauliN Native.kappaN j ++
        [Native.ePauliN (gDiff (23 + j)), Native.eYN 3]) = true := by
  intro j hj
  rw [native_eYN, native_ePermN, native_ePauliN, native_kappaN]
  match j, hj with
  | 0, hj => exact perm_case hj pe0 bt0 false 0 0 rfl perm0
  | 1, hj => exact perm_case hj pe1 bt1 false 0 0 rfl perm1
  | 2, hj => exact perm_case hj pe2 bt2 false 0 0 rfl perm2
  | 3, hj => exact perm_case hj pe3 bt3 false 0 0 rfl perm3
  | 4, hj => exact perm_case hj pe4 bt4 false 0 0 rfl perm4
  | 5, hj => exact perm_case hj pe5 bt5 true 63 0 rfl perm5
  | 6, hj => exact perm_case hj pe6 bt6 false 0 0 rfl perm6
  | 7, hj => exact perm_case hj pe7 bt7 false 0 0 rfl perm7
  | 8, hj => exact perm_case hj pe8 bt8 true 63 0 rfl perm8

theorem signRows_2 :
    ∀ j < 11,
    Native.Sp8.rowChainEq (Native.eYN 3 :: signFs Native.eYN j)
      (signFs Native.eYN j ++ [Native.ePauliN (gDiff (32 + j)), Native.eYN 3]) = true := by
  intro j hj
  rw [native_eYN, native_ePauliN]
  match j, hj with
  | 0, _ => exact sign_case [2, 1] rfl false 0 0 rfl sign0
  | 1, _ => exact sign_case [4, 1] rfl true 63 0 rfl sign1
  | 2, _ => exact sign_case [8, 1] rfl true 63 0 rfl sign2
  | 3, _ => exact sign_case [16, 1] rfl true 63 0 rfl sign3
  | 4, _ => exact sign_case [32, 1] rfl true 63 0 rfl sign4
  | 5, _ => exact sign_case [64] rfl true 63 0 rfl sign5
  | 6, _ => exact sign_case [128, 1] rfl true 63 0 rfl sign6
  | 7, _ => exact sign_case [256] rfl true 63 0 rfl sign7
  | 8, _ => exact sign_case [512] rfl true 63 0 rfl sign8
  | 9, _ => exact sign_case [1024] rfl false 0 0 rfl sign9
  | 10, _ => exact sign_case [2048] rfl false 0 0 rfl sign10

end CertificateChecks.Batch3073

namespace Certificates

end Certificates
