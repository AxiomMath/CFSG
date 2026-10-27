module

public import Certificates.Kernel.Co2Census.CCXGlue
public import CFSG.Sporadic.Co2Smith.CCFacts

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem mem_DCi_iff {i er nr : ℕ} (hi : cR i = cE er nr) (her : er < 512) {d : Cz} :
    d ∈ DCi i ↔ ∃ e ∈ dlK QKt (mulV (SK nr) (QKt er)), d = qE e := by
  have hr := repK_cE QK_eq her nr
  constructor
  · rintro ⟨hdX, hdQ⟩
    obtain ⟨e, he, -, -, hq⟩ := exists_qE ⟨d, hdQ⟩
    have hq' : (qE e : Cz) = d := congrArg Subtype.val hq
    refine ⟨e, (mem_dlK hr).2 ⟨he, ?_⟩, hq'.symm⟩
    rw [hq']
    have := Subgroup.mem_centralizer_singleton_iff.1 hdX
    rwa [hi] at this
  · rintro ⟨e, he, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (qE e).2⟩
    rw [hi]
    exact ((mem_dlK hr).1 he).2

theorem qE0 : (qE 0 : Cz) = 1 :=
  (cz_eq_iff (repK_qE (by norm_num)) repK_one').2 F1_misc_spec.2.2.2.2.2.1

theorem natCard_DCi' (i : ℕ) : Nat.card (DCi i) = ceInv (cR i) := by
  unfold ceInv
  exact Nat.card_congr
    { toFun := fun d => ⟨⟨d.1, d.2.2⟩, (Subgroup.mem_centralizer_singleton_iff.mp d.2.1)⟩
      invFun := fun q => ⟨q.1.1, Subgroup.mem_centralizer_singleton_iff.mpr q.2, q.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def certXE (o c m : ℕ) : Cz := cE (fld21 c (o + 4 * m)) (fld21 c (o + 4 * m + 1))

noncomputable def certXIE (o c m : ℕ) : Cz :=
  cE (fld21 c (o + 4 * m + 2)) (fld21 c (o + 4 * m + 3))

noncomputable def certEltL (o c : ℕ) (d : Cz) (l : List ℕ) : Cz :=
  l.foldr (fun m acc => certXE o c m * d * certXIE o c m * acc) 1

theorem certElt_facts {o c : ℕ} {r : Cz} {R : ℕ} (hr : repK (r : K) R) {d : Cz} {Dr : ℕ}
    (hd : repK (d : K) Dr) (l : List ℕ)
    (hl : ∀ m ∈ l, fld21 c (o + 4 * m) < 512 ∧ fld21 c (o + 4 * m + 2) < 512 ∧
      commK (certX QKt o c m) R = true ∧ mulV (certX QKt o c m) (certXI QKt o c m) = IDP) :
    repK ((certEltL o c d l : Cz) : K) (l.foldr (fun m acc =>
        mulV (mulV (mulV (certX QKt o c m) Dr) (certXI QKt o c m)) acc) IDP) ∧
      ∀ N : Subgroup Cz, d ∈ N → (∀ x : Cz, x * r = r * x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
        certEltL o c d l ∈ N := by
  induction l with
  | nil => exact ⟨repK_one', fun N _ _ => N.one_mem⟩
  | cons m l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun m' hm' => hl m' (List.mem_cons_of_mem _ hm')
    obtain ⟨h1, h2, h3, h4⟩ := hl m List.mem_cons_self
    have hx : repK ((certXE o c m : Cz) : K) (certX QKt o c m) := repK_cE QK_eq h1 _
    have hxi : repK ((certXIE o c m : Cz) : K) (certXI QKt o c m) := repK_cE QK_eq h2 _
    have hinv : certXIE o c m = (certXE o c m)⁻¹ := by
      refine (eq_inv_of_mul_eq_one_right ?_)
      exact (cz_eq_iff (repK_czmul hx hxi) repK_one').2 h4
    refine ⟨repK_czmul (repK_czmul (repK_czmul hx hd) hxi) ih1, fun N hdN hN => ?_⟩
    show certXE o c m * d * certXIE o c m * certEltL o c d l ∈ N
    refine N.mul_mem ?_ (ih2 N hdN hN)
    rw [hinv]
    refine hN _ ?_ d hdN
    unfold commK at h3
    exact (cz_eq_iff (repK_czmul hx hr) (repK_czmul hr hx)).2 (Nat.eq_of_beq_eq_true h3)

theorem certXOK_spec {o c R len : ℕ} (h : certXOK QKt o c R len = true) :
    ∀ m ∈ List.range len, fld21 c (o + 4 * m) < 512 ∧ fld21 c (o + 4 * m + 2) < 512 ∧
      commK (certX QKt o c m) R = true ∧ mulV (certX QKt o c m) (certXI QKt o c m) = IDP := by
  intro m hm
  have := List.all_eq_true.1 h m hm
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

end CC

end CertificateChecks.KernelCo2Census

end
