module

public import CFSG.Quasithin.Vol2.KGFact1296Ct

public section

namespace CFSG.Quasithin.H13.KG1296

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.SLnTwo

local notation "SL₅" => SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M₅" => Matrix (Fin 5) (Fin 5) (ZMod 2)

@[expose] def rMat (a b : Fin 3 → ZMod 2) (c : ZMod 2) : M₅ :=
  !![1, a 0, a 1, a 2, c;
     0, 1, 0, 0, b 0;
     0, 0, 1, 0, b 1;
     0, 0, 0, 1, b 2;
     0, 0, 0, 0, 1]

theorem rMat_mul (a b a' b' : Fin 3 → ZMod 2) (c c' : ZMod 2) :
    rMat a b c * rMat a' b' c' = rMat (a + a') (b + b') (c + c' + a ⬝ᵥ b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rMat, Matrix.mul_apply, Fin.sum_univ_five, dotProduct, Fin.sum_univ_three] <;> ring

theorem rMat_det (a b : Fin 3 → ZMod 2) (c : ZMod 2) : (rMat a b c).det = 1 := by
  have h : (rMat a b c).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rMat] at hij ⊢
  rw [Matrix.det_of_isUpperTriangular h, Fin.prod_univ_five]
  simp [rMat]

@[expose] def rElt (a b : Fin 3 → ZMod 2) (c : ZMod 2) : SL₅ := ⟨rMat a b c, rMat_det a b c⟩

theorem coe_rElt (a b : Fin 3 → ZMod 2) (c : ZMod 2) : ((rElt a b c : SL₅) : M₅) = rMat a b c :=
  rfl

theorem rElt_mul (a b a' b' : Fin 3 → ZMod 2) (c c' : ZMod 2) :
    rElt a b c * rElt a' b' c' = rElt (a + a') (b + b') (c + c' + a ⬝ᵥ b') :=
  Subtype.ext (rMat_mul a b a' b' c c')

theorem rElt_zero : rElt 0 0 0 = 1 := by
  apply Subtype.ext
  rw [coe_rElt, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat]

theorem rElt_inv (a b : Fin 3 → ZMod 2) (c : ZMod 2) :
    (rElt a b c)⁻¹ = rElt a b (c + a ⬝ᵥ b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [rElt_mul, ← rElt_zero, CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b]
  congr 1
  ring_nf
  reduce_mod_char

theorem rElt_inj {a b a' b' : Fin 3 → ZMod 2} {c c' : ZMod 2}
    (h : rElt a b c = rElt a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have e : ∀ i j, rMat a b c i j = rMat a' b' c' i j := fun i j =>
    congrFun (congrFun (congrArg Subtype.val h) i) j
  refine ⟨funext fun k => ?_, funext fun k => ?_, ?_⟩
  · fin_cases k
    · simpa [rMat] using e 0 1
    · simpa [rMat] using e 0 2
    · simpa [rMat] using e 0 3
  · fin_cases k
    · simpa [rMat] using e 1 4
    · simpa [rMat] using e 2 4
    · simpa [rMat] using e 3 4
  · simpa [rMat] using e 0 4

theorem rElt_commutator (a b a' b' : Fin 3 → ZMod 2) (c c' : ZMod 2) :
    rElt a' b' c' * rElt a b c * (rElt a' b' c')⁻¹ * (rElt a b c)⁻¹ =
      rElt 0 0 (a' ⬝ᵥ b + a ⬝ᵥ b') := by
  rw [rElt_inv, rElt_inv, rElt_mul, rElt_mul, rElt_mul]
  congr 1
  · rw [add_comm a' a, add_assoc, add_assoc, ← add_assoc a' a', CharTwo.add_self_eq_zero,
      zero_add, CharTwo.add_self_eq_zero]
  · rw [add_comm b' b, add_assoc, add_assoc, ← add_assoc b' b', CharTwo.add_self_eq_zero,
      zero_add, CharTwo.add_self_eq_zero]
  · simp only [add_dotProduct]
    ring_nf
    reduce_mod_char

theorem rElt_pow_four (a b : Fin 3 → ZMod 2) (c : ZMod 2) : rElt a b c ^ 4 = 1 := by
  have h2 : rElt a b c ^ 2 = rElt 0 0 (a ⬝ᵥ b) := by
    rw [sq, rElt_mul, CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b,
      CharTwo.add_self_eq_zero c, zero_add]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq, rElt_mul, add_zero, ← rElt_zero,
    dotProduct_zero, add_zero, CharTwo.add_self_eq_zero]

theorem rElt_mem_Ct (a b : Fin 3 → ZMod 2) (c : ZMod 2) : rElt a b c ∈ Ct := by
  refine mem_Ct_iff.2 ⟨funext fun i => ?_, funext fun j => ?_⟩
  · fin_cases i <;> simp [rElt, rMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  · fin_cases j <;> simp [rElt, rMat, Matrix.vecMul, dotProduct, Fin.sum_univ_five]

theorem qCt_rElt (a b : Fin 3 → ZMod 2) (c : ZMod 2) :
    qCt ⟨rElt a b c, rElt_mem_Ct a b c⟩ = 1 := by
  apply Subtype.ext
  ext p q
  rw [qCt_apply]
  fin_cases p <;> fin_cases q <;> simp [rElt, rMat]

theorem eq_rElt_of_qCt {x : SL₅} (hx : x ∈ Ct) (hq : qCt ⟨x, hx⟩ = 1) :
    x = rElt ![(x : M₅) 0 1, (x : M₅) 0 2, (x : M₅) 0 3]
      ![(x : M₅) 1 4, (x : M₅) 2 4, (x : M₅) 3 4] ((x : M₅) 0 4) := by
  obtain ⟨h1, h2⟩ := mem_Ct_iff.1 hx
  have hc : ∀ i, (x : M₅) i 0 = (Pi.single 0 1 : Fin 5 → ZMod 2) i := fun i => by
    have := congrFun h1 i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  have hr : ∀ j, (x : M₅) 4 j = (Pi.single 4 1 : Fin 5 → ZMod 2) j := fun j => by
    have := congrFun h2 j
    rwa [Matrix.single_one_vecMul, Matrix.row_apply] at this
  have hm : ∀ p q : Fin 3, (x : M₅) ⟨1 + p, by omega⟩ ⟨1 + q, by omega⟩ =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) p q := fun p q => by
    rw [← qCt_apply ⟨x, hx⟩, hq]
    rfl
  have h11 := hm 0 0
  have h12 := hm 0 1
  have h13 := hm 0 2
  have h21 := hm 1 0
  have h22 := hm 1 1
  have h23 := hm 1 2
  have h31 := hm 2 0
  have h32 := hm 2 1
  have h33 := hm 2 2
  simp at h11 h12 h13 h21 h22 h23 h31 h32 h33
  apply Subtype.ext
  rw [coe_rElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rMat, hc, hr, h11, h12, h13, h21, h22, h23, h31, h32, h33]

theorem map_ker_qCt_le : qCt.ker.map Ct.subtype ≤ pCoreOf 2 Ct := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 qCt.ker := by
    intro y
    refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
    have hx := eq_rElt_of_qCt (y : ↥Ct).2 y.2
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one, hx]
    exact rElt_pow_four _ _ _
  have hle := le_pCore_of_normal (MonoidHom.normal_ker qCt) h2
  exact Subgroup.map_mono hle

theorem mem_pCoreOf_Ct_iff {x : SL₅} : x ∈ pCoreOf 2 Ct ↔ ∃ a b c, x = rElt a b c := by
  constructor
  · intro hx
    exact ⟨_, _, _, eq_rElt_of_qCt (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
      (qCt_eq_one_of_mem_pCoreOf hx)⟩
  · rintro ⟨a, b, c, rfl⟩
    exact map_ker_qCt_le ⟨⟨rElt a b c, rElt_mem_Ct a b c⟩, qCt_rElt a b c, rfl⟩

theorem mem_radOne_four_iff {x : SL₅} : x ∈ radOne 4 ↔ ∃ a c, x = rElt a 0 c := by
  constructor
  · rintro ⟨φ, hφ, hx⟩
    refine ⟨![φ 1, φ 2, φ 3], φ 4, Subtype.ext ?_⟩
    rw [hx, coe_rElt]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rMat, vecMulVec_apply, hφ]
  · rintro ⟨a, c, rfl⟩
    refine ⟨![0, a 0, a 1, a 2, c], rfl, ?_⟩
    rw [coe_rElt]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rMat]

theorem graphFun_rElt_left (a : Fin 3 → ZMod 2) (c : ZMod 2) :
    BinaryParabolic.graphFun (rElt a 0 c) = rElt 0 ![a 2, a 1, a 0] c := by
  have hinv : (rElt a 0 c)⁻¹ = rElt a 0 c := by rw [rElt_inv, dotProduct_zero, add_zero]
  apply Subtype.ext
  rw [BinaryParabolic.coe_graphFun, hinv, coe_rElt, coe_rElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rMat, Fin.rev]

theorem graphFun_rElt_right (b : Fin 3 → ZMod 2) (c : ZMod 2) :
    BinaryParabolic.graphFun (rElt 0 b c) = rElt ![b 2, b 1, b 0] 0 c := by
  have h := graphFun_rElt_left ![b 2, b 1, b 0] c
  have hb : (![(![b 2, b 1, b 0] : Fin 3 → ZMod 2) 2, ![b 2, b 1, b 0] 1, ![b 2, b 1, b 0] 0] :
      Fin 3 → ZMod 2) = b := by
    funext k
    fin_cases k <;> rfl
  rw [hb] at h
  rw [← h, BinaryParabolic.graphFun_graphFun]

theorem mem_radFour_iff {x : SL₅} :
    x ∈ (radOne 4).map (BinaryParabolic.graphAut 5).toMonoidHom ↔ ∃ b c, x = rElt 0 b c := by
  rw [Subgroup.mem_map_equiv]
  show BinaryParabolic.graphFun x ∈ radOne 4 ↔ _
  rw [mem_radOne_four_iff]
  constructor
  · rintro ⟨a, c, h⟩
    refine ⟨![a 2, a 1, a 0], c, ?_⟩
    rw [← BinaryParabolic.graphFun_graphFun x, h, graphFun_rElt_left]
  · rintro ⟨b, c, rfl⟩
    exact ⟨_, _, graphFun_rElt_right b c⟩

@[expose] noncomputable def leviT {p q : Fin 3} (hpq : p ≠ q) : SL₅ :=
  SpecialLinearGroup.transvection (i := ⟨1 + p, by omega⟩) (j := ⟨1 + q, by omega⟩)
    (fun e => hpq (Fin.ext (by have := congrArg Fin.val e; simp at this; omega))) (1 : ZMod 2)

theorem leviT_mem_Ct {p q : Fin 3} (hpq : p ≠ q) : leviT hpq ∈ Ct :=
  transvection_mem_Ct _ (fun e => by have := congrArg Fin.val e; simp at this)
    (fun e => by have := congrArg Fin.val e; simp at this; omega)

theorem leviT_conj {p q : Fin 3} (hpq : p ≠ q) (a b : Fin 3 → ZMod 2) (c : ZMod 2) :
    leviT hpq * rElt a b c * (leviT hpq)⁻¹ =
      rElt (a + Pi.single q (a p)) (b + Pi.single p (b q)) c := by
  have hinv : (leviT hpq)⁻¹ = leviT hpq :=
    inv_eq_of_mul_eq_one_right (transvection_mul_self _)
  rw [hinv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rElt, coe_rElt,
    leviT, SpecialLinearGroup.transvection_coe]
  fin_cases p <;> fin_cases q <;> (try exact absurd rfl hpq) <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [rMat, Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply]
        <;> first | ring1 | decide)

theorem leviT_commutator {p q : Fin 3} (hpq : p ≠ q) (a b : Fin 3 → ZMod 2) (c : ZMod 2) :
    ∃ c', leviT hpq * rElt a b c * (leviT hpq)⁻¹ * (rElt a b c)⁻¹ =
      rElt (Pi.single q (a p)) (Pi.single p (b q)) c' := by
  rw [leviT_conj, rElt_inv, rElt_mul]
  refine ⟨c + (c + a ⬝ᵥ b) + (a + Pi.single q (a p)) ⬝ᵥ b, ?_⟩
  congr 1
  · rw [add_comm a, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [add_comm b, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem forall_of_closed {S : (Fin 3 → ZMod 2) → Prop} (h0 : S 0)
    (hadd : ∀ a a', S a → S a' → S (a + a'))
    (htv : ∀ a (p q : Fin 3), p ≠ q → S a → S (a + Pi.single q (a p)))
    (hex : ∃ a, a ≠ 0 ∧ S a) : ∀ a, S a := by
  obtain ⟨a, ha, hSa⟩ := hex
  obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero ha
  have hq : ∀ q, q ≠ k → S (Pi.single q 1) := by
    intro q hqk
    have h1 := htv a k q (Ne.symm hqk) hSa
    rw [hk] at h1
    have h2 := hadd _ _ h1 hSa
    rwa [add_comm a, add_assoc, CharTwo.add_self_eq_zero, add_zero] at h2
  have hk' : S (Pi.single k 1) := by
    obtain ⟨q, hqk⟩ : ∃ q : Fin 3, q ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
    have h1 := htv _ q k hqk (hq q hqk)
    rw [Pi.single_eq_same] at h1
    have h2 := hadd _ _ h1 (hq q hqk)
    rwa [add_comm (Pi.single q 1), add_assoc, CharTwo.add_self_eq_zero, add_zero] at h2
  have he : ∀ q, S (Pi.single q 1) := fun q => by
    by_cases hqk : q = k
    · rw [hqk]
      exact hk'
    · exact hq q hqk
  have hsm : ∀ (r : ZMod 2) q, S (r • Pi.single q 1) := fun r q => by
    rcases zmod_two_cases r with rfl | rfl
    · rw [zero_smul]
      exact h0
    · rw [one_smul]
      exact he q
  intro b
  have hb : b = (b 0 • Pi.single 0 1 + b 1 • Pi.single 1 1) + b 2 • Pi.single 2 1 := by
    funext i
    fin_cases i <;> simp
  rw [hb]
  exact hadd _ _ (hadd _ _ (hsm _ _) (hsm _ _)) (hsm _ _)

theorem eq_of_invariant {Q : Subgroup SL₅} (hQR : Q ≤ pCoreOf 2 Ct)
    (hQN : Ct ≤ Subgroup.normalizer (Q : Set SL₅)) (hQ : Q ≠ ⊥) (hQne : Q ≠ pCoreOf 2 Ct)
    (hcard : Nat.card ↥(pCoreOf 2 Ct) ≤ 2 ^ 3 * Nat.card Q) :
    Q = radOne 4 ∨ Q = (radOne 4).map (BinaryParabolic.graphAut 5).toMonoidHom := by
  classical
  have hconj : ∀ g ∈ Ct, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hQN hg) x).1 hx
  have hcomm : ∀ g ∈ Ct, ∀ x ∈ Q, g * x * g⁻¹ * x⁻¹ ∈ Q := fun g hg x hx =>
    Q.mul_mem (hconj g hg x hx) (Q.inv_mem hx)
  have hform : ∀ x ∈ Q, ∃ a b c, x = rElt a b c := fun x hx => mem_pCoreOf_Ct_iff.1 (hQR hx)
  have ht : rElt 0 0 1 ∈ Q := by
    obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
      by_contra h
      push Not at h
      exact hQ (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
    obtain ⟨a, b, c, rfl⟩ := hform _ hxQ
    by_cases hab : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := hab
      rcases zmod_two_cases c with rfl | rfl
      · exact absurd rElt_zero hx1
      · exact hxQ
    · by_cases ha : a = 0
      · have hb : b ≠ 0 := fun hb => hab ⟨ha, hb⟩
        obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero hb
        have := hcomm _ (rElt_mem_Ct (Pi.single k 1) 0 0) _ hxQ
        rwa [rElt_commutator, single_dotProduct, hk, one_mul, dotProduct_zero, add_zero] at this
      · obtain ⟨k, hk⟩ := exists_eq_one_of_ne_zero ha
        have := hcomm _ (rElt_mem_Ct 0 (Pi.single k 1) 0) _ hxQ
        rwa [rElt_commutator, zero_dotProduct, zero_add, dotProduct_single, hk, mul_one] at this
  have htmul : ∀ a b c, rElt a b c ∈ Q → ∀ c', rElt a b c' ∈ Q := by
    intro a b c h c'
    by_cases hne : c' = c
    · rw [hne]
      exact h
    · have hc : c' = c + 1 := by
        rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl <;>
          first | exact absurd rfl hne | decide
      have := Q.mul_mem h ht
      rwa [rElt_mul, add_zero, add_zero, dotProduct_zero, add_zero, ← hc] at this
  have hA : (∃ a, a ≠ 0 ∧ ∃ c, rElt a 0 c ∈ Q) → radOne 4 ≤ Q := by
    intro hex x hx
    obtain ⟨a, c, rfl⟩ := mem_radOne_four_iff.1 hx
    have hall := forall_of_closed (S := fun a => ∃ c, rElt a 0 c ∈ Q) ⟨1, ht⟩
      (fun a a' ⟨c, h⟩ ⟨c', h'⟩ => ⟨c + c' + a ⬝ᵥ 0, by
        have := Q.mul_mem h h'
        rwa [rElt_mul, add_zero] at this⟩)
      (fun a p q hpq ⟨c, h⟩ => ⟨c, by
        have := hconj _ (leviT_mem_Ct hpq) _ h
        rwa [leviT_conj, Pi.zero_apply, Pi.single_zero, add_zero] at this⟩) hex a
    obtain ⟨c', hc'⟩ := hall
    exact htmul _ _ _ hc' c
  have hB : (∃ b, b ≠ 0 ∧ ∃ c, rElt 0 b c ∈ Q) →
      (radOne 4).map (BinaryParabolic.graphAut 5).toMonoidHom ≤ Q := by
    intro hex x hx
    obtain ⟨b, c, rfl⟩ := mem_radFour_iff.1 hx
    have hall := forall_of_closed (S := fun b => ∃ c, rElt 0 b c ∈ Q) ⟨1, ht⟩
      (fun b b' ⟨c, h⟩ ⟨c', h'⟩ => ⟨c + c' + 0 ⬝ᵥ b', by
        have := Q.mul_mem h h'
        rwa [rElt_mul, add_zero] at this⟩)
      (fun b p q hpq ⟨c, h⟩ => ⟨c, by
        have := hconj _ (leviT_mem_Ct hpq.symm) _ h
        rwa [leviT_conj, Pi.zero_apply, Pi.single_zero, add_zero] at this⟩) hex b
    obtain ⟨c', hc'⟩ := hall
    exact htmul _ _ _ hc' c
  by_cases hexA : ∃ a, a ≠ 0 ∧ ∃ c, rElt a 0 c ∈ Q <;>
    by_cases hexB : ∃ b, b ≠ 0 ∧ ∃ c, rElt 0 b c ∈ Q
  ·
    exfalso
    apply hQne
    refine le_antisymm hQR fun x hx => ?_
    obtain ⟨a, b, c, rfl⟩ := mem_pCoreOf_Ct_iff.1 hx
    have h1 : rElt a 0 (c + a ⬝ᵥ b) ∈ Q := hA hexA (mem_radOne_four_iff.2 ⟨a, _, rfl⟩)
    have h2 : rElt 0 b 0 ∈ Q := hB hexB (mem_radFour_iff.2 ⟨b, 0, rfl⟩)
    have := Q.mul_mem h1 h2
    rw [rElt_mul, add_zero, zero_add, add_zero, add_assoc, CharTwo.add_self_eq_zero,
      add_zero] at this
    exact this
  ·
    left
    refine le_antisymm (fun x hx => ?_) (hA hexA)
    obtain ⟨a, b, c, rfl⟩ := hform x hx
    have h1 : rElt a 0 0 ∈ Q := hA hexA (mem_radOne_four_iff.2 ⟨a, 0, rfl⟩)
    have := Q.mul_mem h1 hx
    rw [rElt_mul, CharTwo.add_self_eq_zero, zero_add, zero_add] at this
    have hb : b = 0 := by
      by_contra hb
      exact hexB ⟨b, hb, _, this⟩
    rw [hb]
    exact mem_radOne_four_iff.2 ⟨a, c, rfl⟩
  ·
    right
    refine le_antisymm (fun x hx => ?_) (hB hexB)
    obtain ⟨a, b, c, rfl⟩ := hform x hx
    have h1 : rElt 0 b 0 ∈ Q := hB hexB (mem_radFour_iff.2 ⟨b, 0, rfl⟩)
    have := Q.mul_mem hx h1
    rw [rElt_mul, add_zero, CharTwo.add_self_eq_zero, add_zero] at this
    have ha : a = 0 := by
      by_contra ha
      exact hexA ⟨a, ha, _, this⟩
    rw [ha]
    exact mem_radFour_iff.2 ⟨b, c, rfl⟩
  ·
    exfalso
    have hrel : ∀ a b c, rElt a b c ∈ Q → ∀ p q : Fin 3, p ≠ q → a p = b q := by
      intro a b c hx p q hpq
      obtain ⟨c', hc'⟩ := leviT_commutator hpq a b c
      have hmem := hcomm _ (leviT_mem_Ct hpq) _ hx
      rw [hc'] at hmem
      rcases zmod_two_cases (a p) with hap | hap <;> rcases zmod_two_cases (b q) with hbq | hbq
      · rw [hap, hbq]
      · exfalso
        rw [hap, hbq, Pi.single_zero] at hmem
        exact hexB ⟨Pi.single p 1, fun h => by simpa using congrFun h p, c', hmem⟩
      · exfalso
        rw [hap, hbq, Pi.single_zero] at hmem
        exact hexA ⟨Pi.single q 1, fun h => by simpa using congrFun h q, c', hmem⟩
      · rw [hap, hbq]
    have hall : ∀ a b c, rElt a b c ∈ Q → (∀ k, a k = a 0) ∧ ∀ k, b k = a 0 := by
      intro a b c hx
      have e1 := hrel a b c hx 0 1 (by decide)
      have e2 := hrel a b c hx 2 1 (by decide)
      have e3 := hrel a b c hx 2 0 (by decide)
      have e4 := hrel a b c hx 1 0 (by decide)
      have e6 := hrel a b c hx 0 2 (by decide)
      refine ⟨fun k => ?_, fun k => ?_⟩
      · fin_cases k
        · rfl
        · exact e4.trans (e3.symm.trans (e2.trans e1.symm))
        · exact e2.trans e1.symm
      · fin_cases k
        · exact e3.symm.trans (e2.trans e1.symm)
        · exact e1.symm
        · exact e6.symm
    have hQ4 : Nat.card Q ≤ 4 := by
      have hinj : Function.Injective
          (fun x : ↥Q => (((x : SL₅) : M₅) 0 1, ((x : SL₅) : M₅) 0 4)) := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        obtain ⟨a, b, c, rfl⟩ := hform x hx
        obtain ⟨a', b', c', rfl⟩ := hform y hy
        simp only [Prod.mk.injEq, coe_rElt] at hxy
        have h01 : a 0 = a' 0 := by simpa [rMat] using hxy.1
        have h04 : c = c' := by simpa [rMat] using hxy.2
        obtain ⟨ha, hb⟩ := hall a b c hx
        obtain ⟨ha', hb'⟩ := hall a' b' c' hy
        have e1 : a = a' := funext fun k => by rw [ha k, ha' k, h01]
        have e2 : b = b' := funext fun k => by rw [hb k, hb' k, h01]
        exact Subtype.ext (show rElt a b c = rElt a' b' c' by rw [e1, e2, h04])
      have h := Nat.card_le_card_of_injective _ hinj
      rwa [Nat.card_prod, Nat.card_zmod] at h
    have hR : 128 ≤ Nat.card ↥(pCoreOf 2 Ct) := by
      have hinj : Function.Injective (fun v : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × ZMod 2 =>
          (⟨rElt v.1 v.2.1 v.2.2, mem_pCoreOf_Ct_iff.2 ⟨_, _, _, rfl⟩⟩ : ↥(pCoreOf 2 Ct))) := by
        rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
        obtain ⟨h1, h2, h3⟩ := rElt_inj (congrArg Subtype.val h)
        exact Prod.ext h1 (Prod.ext h2 h3)
      have h128 : Nat.card ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × ZMod 2) = 128 := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
        norm_num
      have h := Nat.card_le_card_of_injective _ hinj
      rwa [h128] at h
    omega

theorem parConclusion_Ct : ParConclusion Ct 3 := by
  intro Q hQ hQne hQbot hQN hcard
  rcases eq_of_invariant hQ hQN hQbot hQne hcard with rfl | rfl
  · exact ⟨Pone 5, Ct_le_Pone, Pone_le_normalizer_radOne, not_Pone_le_normalizer_Ct⟩
  · exact ⟨_, Ct_le_graph_Pone, map_le_normalizer_map _ Pone_le_normalizer_radOne,
      not_graph_Pone_le_normalizer_Ct⟩

end CFSG.Quasithin.H13.KG1296
