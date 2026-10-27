module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2Off
public import CFSG.Quasithin.Vol2.Ch12Sec4G2Syl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Orbit

section Codes

theorem mem_o0Codes {c : ℕ} : c ∈ o0Codes ↔ c < 256 ∧ c.testBit 0 = c.testBit 7 := by
  simp [o0Codes]

theorem o0Codes_nodup : o0Codes.Nodup := by
  decide +kernel

theorem trace_decodeZ_iff : ∀ c < 256,
    ((decodeZ c).1 + (decodeZ c).2.2.2 = 0 ↔ c.testBit 0 = c.testBit 7) := by
  decide +kernel

theorem decodeZ_mem_zornO0 {c : ℕ} (hc : c ∈ o0Codes) :
    Multiplicative.ofAdd (decodeZ c) ∈ zornO0 (ZMod 2) :=
  (trace_decodeZ_iff c (mem_o0Codes.1 hc).1).2 (mem_o0Codes.1 hc).2

abbrev O0C : Type := {c : ℕ // c ∈ o0Codes}

@[expose] def o0Elt (c : O0C) : ↥(zornO0 (ZMod 2)) :=
  ⟨Multiplicative.ofAdd (decodeZ c.1), decodeZ_mem_zornO0 c.2⟩

theorem o0Elt_injective : Function.Injective o0Elt := by
  intro a b h
  have h1 : decodeZ a.1 = decodeZ b.1 :=
    congrArg (fun m : ↥(zornO0 (ZMod 2)) => Multiplicative.toAdd m.1) h
  exact Subtype.ext (decodeZ_injective (mem_o0Codes.1 a.2).1 (mem_o0Codes.1 b.2).1 h1)

theorem o0Elt_surjective : Function.Surjective o0Elt := by
  rintro ⟨m, hm⟩
  obtain ⟨c, hc, hcm⟩ := decodeZ_surjective (Multiplicative.toAdd m)
  have hmem : c ∈ o0Codes := by
    refine mem_o0Codes.2 ⟨hc, (trace_decodeZ_iff c hc).1 ?_⟩
    rw [hcm]
    exact hm
  refine ⟨⟨c, hmem⟩, Subtype.ext ?_⟩
  change Multiplicative.ofAdd (decodeZ c) = m
  rw [hcm, ofAdd_toAdd]

theorem xor_lt_256 {c d : ℕ} (hc : c < 256) (hd : d < 256) : c ^^^ d < 256 := by
  have h := Nat.xor_lt_two_pow (n := 8) (by norm_num; exact hc) (by norm_num; exact hd)
  norm_num at h
  exact h

theorem xor_mem_o0Codes {c d : ℕ} (hc : c ∈ o0Codes) (hd : d ∈ o0Codes) : c ^^^ d ∈ o0Codes := by
  rw [mem_o0Codes] at hc hd ⊢
  exact ⟨xor_lt_256 hc.1 hd.1, by rw [Nat.testBit_xor, Nat.testBit_xor, hc.2, hd.2]⟩

@[expose] def o0Xor (c d : O0C) : O0C := ⟨c.1 ^^^ d.1, xor_mem_o0Codes c.2 d.2⟩

theorem zero_mem_o0Codes : (0 : ℕ) ∈ o0Codes := by
  decide

@[expose] def o0Zero : O0C := ⟨0, zero_mem_o0Codes⟩

theorem o0Elt_xor (c d : O0C) : o0Elt (o0Xor c d) = o0Elt c * o0Elt d := by
  apply Subtype.ext
  change Multiplicative.ofAdd (decodeZ (c.1 ^^^ d.1)) =
    Multiplicative.ofAdd (decodeZ c.1) * Multiplicative.ofAdd (decodeZ d.1)
  rw [decodeZ_xor, ofAdd_add]

theorem o0Elt_zero : o0Elt o0Zero = 1 := by
  apply Subtype.ext
  change Multiplicative.ofAdd (decodeZ 0) = 1
  rw [decodeZ_zero, ofAdd_zero]

theorem o0Xor_self (c : O0C) : o0Xor c c = o0Zero :=
  Subtype.ext (Nat.xor_self c.1)

theorem mact_mem_o0Codes {g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)}
    (hg : g ∈ quasithinG2 (ZMod 2)) {c : ℕ} (hc : c ∈ o0Codes) :
    mact (matCode g) c ∈ o0Codes := by
  have hlt := mact_lt' g c
  refine mem_o0Codes.2 ⟨hlt, (trace_decodeZ_iff _ hlt).1 ?_⟩
  rw [decodeZ_mact' g (mem_o0Codes.1 hc).1]
  exact (mem_quasithinG2_isZornAuto hg).trace_zero
    ((trace_decodeZ_iff c (mem_o0Codes.1 hc).1).2 (mem_o0Codes.1 hc).2)

@[expose] def o0Act (g : ↥(quasithinG2 (ZMod 2))) (c : O0C) : O0C :=
  ⟨mact (matCode g.1) c.1, mact_mem_o0Codes g.2 c.2⟩

theorem o0Elt_act (g : ↥(quasithinG2 (ZMod 2))) (c : O0C) :
    ((o0Elt (o0Act g c) : ↥(zornO0 (ZMod 2))) : Multiplicative (quasithinZorn (ZMod 2))) =
      Multiplicative.ofAdd (g.1 (Multiplicative.toAdd (o0Elt c).1)) := by
  change Multiplicative.ofAdd (decodeZ (mact (matCode g.1) c.1)) =
    Multiplicative.ofAdd (g.1 (decodeZ c.1))
  rw [decodeZ_mact' g.1 (mem_o0Codes.1 c.2).1]

theorem card_o0C_filter (P : ℕ → Bool) :
    Nat.card {c : O0C // P c.1 = true} = (o0Codes.filter P).length := by
  have e : {c : O0C // P c.1 = true} ≃ {c : ℕ // c ∈ o0Codes.filter P} :=
    { toFun := fun c => ⟨c.1.1, List.mem_filter.2 ⟨c.1.2, c.2⟩⟩
      invFun := fun c => ⟨⟨c.1, (List.mem_filter.1 c.2).1⟩, (List.mem_filter.1 c.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e' : {c : ℕ // c ∈ o0Codes.filter P} ≃ ↥((o0Codes.filter P).toFinset) :=
    Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e, Nat.card_congr e', Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (o0Codes_nodup.filter _)]

end Codes

section ModelsTwo

abbrev ModO : Type := (zornO0Model (quasithinG2 (ZMod 2))).Mod

abbrev ModQ : Type := (FFModel.zornQ (quasithinG2 (ZMod 2))).Mod

@[expose] def codeO (c : O0C) : ModO := QuotientGroup.mk (o0Elt c)

@[expose] def codeQ (c : O0C) : ModQ := QuotientGroup.mk (o0Elt c)

theorem codeO_injective : Function.Injective codeO := by
  intro a b h
  apply o0Elt_injective
  have h1 := QuotientGroup.eq.1 h
  have h2 : (o0Elt a)⁻¹ * o0Elt b = 1 :=
    Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1))
  exact inv_mul_eq_one.1 h2

theorem codeO_surjective : Function.Surjective codeO := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨c, rfl⟩ := o0Elt_surjective m
  exact ⟨c, rfl⟩

theorem codeQ_surjective : Function.Surjective codeQ := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨c, rfl⟩ := o0Elt_surjective m
  exact ⟨c, rfl⟩

theorem codeO_xor (c d : O0C) : codeO (o0Xor c d) = codeO c * codeO d := by
  rw [codeO, codeO, codeO, o0Elt_xor]
  rfl

theorem codeQ_xor (c d : O0C) : codeQ (o0Xor c d) = codeQ c * codeQ d := by
  rw [codeQ, codeQ, codeQ, o0Elt_xor]
  rfl

theorem codeO_zero : codeO o0Zero = 1 := by
  rw [codeO, o0Elt_zero]
  rfl

theorem codeQ_zero : codeQ o0Zero = 1 := by
  rw [codeQ, o0Elt_zero]
  rfl

theorem codeO_inv (c : O0C) : (codeO c)⁻¹ = codeO c := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← codeO_xor, o0Xor_self, codeO_zero]

theorem codeQ_inv (c : O0C) : (codeQ c)⁻¹ = codeQ c := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← codeQ_xor, o0Xor_self, codeQ_zero]

theorem g2OAct_codeO (g : ↥(quasithinG2 (ZMod 2))) (c : O0C) :
    g2OAct (ZMod 2) g (codeO c) = codeO (o0Act g c) := by
  change (QuotientGroup.mk _ : ModO) = QuotientGroup.mk _
  congr 1
  apply Subtype.ext
  exact (o0Elt_act g c).symm

theorem g2QAct_codeQ (g : ↥(quasithinG2 (ZMod 2))) (c : O0C) :
    g2QAct (ZMod 2) g (codeQ c) = codeQ (o0Act g c) := by
  change (QuotientGroup.mk _ : ModQ) = QuotientGroup.mk _
  congr 1
  apply Subtype.ext
  exact (o0Elt_act g c).symm

theorem zornR_code : ∀ x < 256, ((∃ t : ZMod 2, decodeZ x = (t, 0, 0, t)) ↔ x = 0 ∨ x = 129) := by
  decide +kernel

theorem neg_decodeZ (c : ℕ) : -decodeZ c = decodeZ c := by
  have h : decodeZ c + decodeZ c = 0 := by rw [← decodeZ_xor, Nat.xor_self, decodeZ_zero]
  exact neg_eq_of_add_eq_zero_left h

theorem xor_eq_iff {c d e : ℕ} : c ^^^ d = e ↔ d = c ^^^ e := by
  constructor
  · rintro rfl
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rintro rfl
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem codeQ_eq_iff (c d : O0C) : codeQ c = codeQ d ↔ d.1 = c.1 ∨ d.1 = c.1 ^^^ 129 := by
  have e : codeQ c = codeQ d ↔ (((o0Elt c)⁻¹ * o0Elt d : ↥(zornO0 (ZMod 2))) :
      Multiplicative (quasithinZorn (ZMod 2))) ∈ zornR (ZMod 2) :=
    QuotientGroup.eq.trans Subgroup.mem_subgroupOf
  rw [e]
  have h : (((o0Elt c)⁻¹ * o0Elt d : ↥(zornO0 (ZMod 2))) :
      Multiplicative (quasithinZorn (ZMod 2))) = Multiplicative.ofAdd (decodeZ (c.1 ^^^ d.1)) := by
    change (Multiplicative.ofAdd (decodeZ c.1))⁻¹ * Multiplicative.ofAdd (decodeZ d.1) = _
    rw [decodeZ_xor, ofAdd_add, ← ofAdd_neg, neg_decodeZ]
  rw [h]
  change (∃ t : ZMod 2, decodeZ (c.1 ^^^ d.1) = (t, 0, 0, t)) ↔ _
  rw [zornR_code _ (xor_lt_256 (mem_o0Codes.1 c.2).1 (mem_o0Codes.1 d.2).1), xor_eq_iff,
    xor_eq_iff, Nat.xor_zero]

theorem xor_eq_iff' {a c e : ℕ} : a ^^^ c = e ↔ a = c ^^^ e := by
  rw [Nat.xor_comm]
  exact xor_eq_iff

theorem fixQB_iff (m : List ℕ) {c : ℕ} (hc : c ∈ o0Codes) (hm : mact m c ∈ o0Codes) :
    fixQB m c = true ↔ mact m c = c ∨ mact m c = c ^^^ 129 := by
  have key : ∀ x < 256, x.testBit 0 = x.testBit 7 →
      ((x ||| 129 == 129) = true ↔ x = 0 ∨ x = 129) := by
    decide +kernel
  have hx := mem_o0Codes.1 (xor_mem_o0Codes hm hc)
  unfold fixQB
  rw [key _ hx.1 hx.2, xor_eq_iff', xor_eq_iff', Nat.xor_zero]

theorem testBit_xor_129 (c : ℕ) : (c ^^^ 129).testBit 0 = !c.testBit 0 := by
  rw [Nat.testBit_xor]
  have : (129 : ℕ).testBit 0 = true := by decide
  rw [this]
  cases c.testBit 0 <;> rfl

end ModelsTwo

section Sub

@[expose] def sEltG (i : ℕ) : ↥(quasithinG2 (ZMod 2)) := ⟨sElt i, sElt_mem_G i⟩

theorem matCode_sEltG {i : ℕ} (hi : i < 64) : matCode (sEltG i).1 = sM i := matCode_sElt hi

theorem mem_sSubG {g : ↥(quasithinG2 (ZMod 2))} : g ∈ sSubG ↔ ∃ i < 64, sEltG i = g := by
  rw [sSubG, Subgroup.mem_subgroupOf, mem_sSub]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, Subtype.ext h⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem sEltG_injective {i k : ℕ} (hi : i < 64) (hk : k < 64) (h : sEltG i = sEltG k) : i = k :=
  sElt_injective hi hk (congrArg Subtype.val h)

variable (B : Subgroup ↥(quasithinG2 (ZMod 2)))

open Classical in
@[expose] noncomputable def idx : Finset ℕ := (Finset.range 64).filter fun i => sEltG i ∈ B

variable {B}

theorem mem_idx {i : ℕ} : i ∈ idx B ↔ i < 64 ∧ sEltG i ∈ B := by
  classical
  simp [idx]

theorem card_eq_idx (hB : B ≤ sSubG) : Nat.card B = (idx B).card := by
  have hbij : Function.Bijective fun i : ↥(idx B) =>
      (⟨sEltG i.1, (mem_idx.1 i.2).2⟩ : ↥B) := by
    constructor
    · intro a b h
      exact Subtype.ext (sEltG_injective (mem_idx.1 a.2).1 (mem_idx.1 b.2).1
        (congrArg Subtype.val h))
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hB hg)
      exact ⟨⟨i, mem_idx.2 ⟨hi, hg⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem mem_map_iff_O (hB : B ≤ sSubG) {x : MulAut ModO} :
    x ∈ B.map (g2OAct (ZMod 2)) ↔ ∃ i ∈ idx B, g2OAct (ZMod 2) (sEltG i) = x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hB hb)
    exact ⟨i, mem_idx.2 ⟨hi, hb⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, (mem_idx.1 hi).2, rfl⟩

theorem mem_map_iff_Q (hB : B ≤ sSubG) {x : MulAut ModQ} :
    x ∈ B.map (g2QAct (ZMod 2)) ↔ ∃ i ∈ idx B, g2QAct (ZMod 2) (sEltG i) = x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hB hb)
    exact ⟨i, mem_idx.2 ⟨hi, hb⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, (mem_idx.1 hi).2, rfl⟩

theorem o0Act_sEltG {i : ℕ} (hi : i < 64) (c : O0C) :
    (o0Act (sEltG i) c).1 = mact (sM i) c.1 := by
  change mact (matCode (sEltG i).1) c.1 = _
  rw [matCode_sEltG hi]

theorem mem_fixV_codeO (hB : B ≤ sSubG) (c : O0C) :
    codeO c ∈ fixV (B.map (g2OAct (ZMod 2))) ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true := by
  constructor
  · intro h i hi
    have h1 := h _ ((mem_map_iff_O hB).2 ⟨i, hi, rfl⟩)
    rw [g2OAct_codeO] at h1
    have h2 := congrArg Subtype.val (codeO_injective h1)
    rw [o0Act_sEltG (mem_idx.1 hi).1] at h2
    simp [fixOB, h2]
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := (mem_map_iff_O hB).1 hx
    rw [g2OAct_codeO]
    congr 1
    apply Subtype.ext
    rw [o0Act_sEltG (mem_idx.1 hi).1]
    simpa [fixOB] using h i hi

theorem mem_fixV_codeQ (hB : B ≤ sSubG) (c : O0C) :
    codeQ c ∈ fixV (B.map (g2QAct (ZMod 2))) ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := by
  have hiff : ∀ i ∈ idx B, (g2QAct (ZMod 2) (sEltG i) (codeQ c) = codeQ c ↔
      fixQB (sM i) c.1 = true) := by
    intro i hi
    have hi' := (mem_idx.1 hi).1
    rw [g2QAct_codeQ, eq_comm, codeQ_eq_iff, o0Act_sEltG hi']
    have hm : mact (sM i) c.1 ∈ o0Codes := by
      rw [← o0Act_sEltG hi']
      exact (o0Act (sEltG i) c).2
    exact (fixQB_iff (sM i) c.2 hm).symm
  constructor
  · intro h i hi
    exact (hiff i hi).1 (h _ ((mem_map_iff_Q hB).2 ⟨i, hi, rfl⟩))
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := (mem_map_iff_Q hB).1 hx
    exact (hiff i hi).2 (h i hi)

theorem card_fixV_O (hB : B ≤ sSubG) (P : ℕ → Bool)
    (hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true) :
    Nat.card (fixV (B.map (g2OAct (ZMod 2)))) = (o0Codes.filter P).length := by
  rw [← card_o0C_filter P]
  refine (Nat.card_congr ?_).symm
  refine (Equiv.ofBijective (fun c : {c : O0C // P c.1 = true} =>
    (⟨codeO c.1, (mem_fixV_codeO hB c.1).2 ((hP c.1).1 c.2)⟩ :
      ↥(fixV (B.map (g2OAct (ZMod 2)))))) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (codeO_injective (congrArg Subtype.val h))
  · rintro ⟨v, hv⟩
    obtain ⟨c, rfl⟩ := codeO_surjective v
    exact ⟨⟨c, (hP c).2 ((mem_fixV_codeO hB c).1 hv)⟩, rfl⟩

theorem card_fixV_Q (hB : B ≤ sSubG) (P : ℕ → Bool)
    (hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true) :
    Nat.card (fixV (B.map (g2QAct (ZMod 2)))) =
      (o0Codes.filter fun c => !c.testBit 0 && P c).length := by
  rw [← card_o0C_filter]
  refine (Nat.card_congr ?_).symm
  have hsub : ∀ c : {c : O0C // (!c.1.testBit 0 && P c.1) = true}, P c.1.1 = true := fun c => by
    have := c.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.2
  refine (Equiv.ofBijective (fun c : {c : O0C // (!c.1.testBit 0 && P c.1) = true} =>
    (⟨codeQ c.1, (mem_fixV_codeQ hB c.1).2 ((hP c.1).1 (hsub c))⟩ :
      ↥(fixV (B.map (g2QAct (ZMod 2)))))) ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have h1 := (codeQ_eq_iff a b).1 (congrArg Subtype.val h)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha hb
    rcases h1 with h1 | h1
    · exact Subtype.ext (Subtype.ext h1.symm)
    · exfalso
      have h2 := testBit_xor_129 a.1
      rw [← h1, hb.1, ha.1] at h2
      exact Bool.false_ne_true h2
  · rintro ⟨v, hv⟩
    obtain ⟨c, rfl⟩ := codeQ_surjective v
    have hPc : P c.1 = true := (hP c).2 ((mem_fixV_codeQ hB c).1 hv)
    cases hc0 : c.1.testBit 0
    · exact ⟨⟨c, by simp [hc0, hPc]⟩, rfl⟩
    · have h129 : (129 : ℕ) ∈ o0Codes := by decide
      let c' : O0C := o0Xor c ⟨129, h129⟩
      have hcc : codeQ c = codeQ c' := (codeQ_eq_iff c c').2 (Or.inr rfl)
      have hPc' : P c'.1 = true := (hP c').2 ((mem_fixV_codeQ hB c').1 (hcc ▸ hv))
      have hc0' : c'.1.testBit 0 = false := by
        change (c.1 ^^^ 129).testBit 0 = false
        rw [testBit_xor_129, hc0]
        rfl
      exact ⟨⟨c', by simp [hc0', hPc']⟩, Subtype.ext hcc.symm⟩

theorem codeO_comm (i : ℕ) (c : O0C) :
    g2OAct (ZMod 2) (sEltG i) (codeO c) * (codeO c)⁻¹ =
      codeO (o0Xor (o0Act (sEltG i) c) c) := by
  rw [codeO_inv, codeO_xor, g2OAct_codeO]

theorem codeQ_comm (i : ℕ) (c : O0C) :
    g2QAct (ZMod 2) (sEltG i) (codeQ c) * (codeQ c)⁻¹ =
      codeQ (o0Xor (o0Act (sEltG i) c) c) := by
  rw [codeQ_inv, codeQ_xor, g2QAct_codeQ]

theorem commV_eq_fixV_O (hB : B ≤ sSubG) {E F : List ℕ} (hE : ∀ i, i ∈ idx B ↔ i ∈ E)
    (hF : ∀ c : O0C, c.1 ∈ F ↔ ∀ i ∈ E, fixOB (sM i) c.1 = true)
    (h1 : ∀ i ∈ E, ∀ c ∈ o0Codes, mact (sM i) c ^^^ c ∈ F)
    (h2 : ∀ f ∈ F, ∃ w : ℕ × ℕ × ℕ × ℕ × ℕ, w.1 = f ∧ w.2.1 ∈ E ∧ w.2.2.1 ∈ o0Codes ∧
      w.2.2.2.1 ∈ E ∧ w.2.2.2.2 ∈ o0Codes ∧
      f = mact (sM w.2.1) w.2.2.1 ^^^ w.2.2.1 ^^^ (mact (sM w.2.2.2.1) w.2.2.2.2 ^^^ w.2.2.2.2)) :
    commV (B.map (g2OAct (ZMod 2))) = fixV (B.map (g2OAct (ZMod 2))) := by
  have hfix : ∀ c : O0C, codeO c ∈ fixV (B.map (g2OAct (ZMod 2))) ↔ c.1 ∈ F := by
    intro c
    rw [mem_fixV_codeO hB, hF]
    exact forall_congr' fun i => imp_congr (hE i) Iff.rfl
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_map_iff_O hB).1 hx
    obtain ⟨c, rfl⟩ := codeO_surjective v
    have hi64 := (mem_idx.1 hi).1
    rw [SetLike.mem_coe, codeO_comm i c, hfix]
    change mact (matCode (sEltG i).1) c.1 ^^^ c.1 ∈ F
    rw [matCode_sEltG hi64]
    exact h1 i ((hE i).1 hi) c.1 c.2
  · intro v hv
    obtain ⟨f, rfl⟩ := codeO_surjective v
    obtain ⟨⟨f', i, c, j, d⟩, hf', hi, hc, hj, hd, hfe⟩ := h2 f.1 ((hfix f).1 hv)
    have hi' := (hE i).2 hi
    have hj' := (hE j).2 hj
    have hi64 := (mem_idx.1 hi').1
    have hj64 := (mem_idx.1 hj').1
    have hmem : ∀ k ∈ idx B, ∀ e : O0C, g2OAct (ZMod 2) (sEltG k) (codeO e) * (codeO e)⁻¹ ∈
        commV (B.map (g2OAct (ZMod 2))) := fun k hk e =>
      Subgroup.subset_closure ⟨_, (mem_map_iff_O hB).2 ⟨k, hk, rfl⟩, codeO e, rfl⟩
    have key : f = o0Xor (o0Xor (o0Act (sEltG i) ⟨c, hc⟩) ⟨c, hc⟩)
        (o0Xor (o0Act (sEltG j) ⟨d, hd⟩) ⟨d, hd⟩) := by
      apply Subtype.ext
      change f.1 = mact (matCode (sEltG i).1) c ^^^ c ^^^ (mact (matCode (sEltG j).1) d ^^^ d)
      rw [matCode_sEltG hi64, matCode_sEltG hj64]
      exact hfe
    rw [key, codeO_xor, ← codeO_comm i, ← codeO_comm j]
    exact mul_mem (hmem i hi' _) (hmem j hj' _)

theorem commV_eq_fixV_Q (hB : B ≤ sSubG) {E F : List ℕ} (hE : ∀ i, i ∈ idx B ↔ i ∈ E)
    (hF : ∀ c : O0C, c.1 ∈ F ↔ ∀ i ∈ E, fixQB (sM i) c.1 = true)
    (h1 : ∀ i ∈ E, ∀ c ∈ o0Codes, mact (sM i) c ^^^ c ∈ F)
    (h2 : ∀ f ∈ F, ∃ w : ℕ × ℕ × ℕ, w.1 = f ∧ w.2.1 ∈ E ∧ w.2.2 ∈ o0Codes ∧
      (f = mact (sM w.2.1) w.2.2 ^^^ w.2.2 ∨ f = mact (sM w.2.1) w.2.2 ^^^ w.2.2 ^^^ 129)) :
    commV (B.map (g2QAct (ZMod 2))) = fixV (B.map (g2QAct (ZMod 2))) := by
  have hfix : ∀ c : O0C, codeQ c ∈ fixV (B.map (g2QAct (ZMod 2))) ↔ c.1 ∈ F := by
    intro c
    rw [mem_fixV_codeQ hB, hF]
    exact forall_congr' fun i => imp_congr (hE i) Iff.rfl
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_map_iff_Q hB).1 hx
    obtain ⟨c, rfl⟩ := codeQ_surjective v
    have hi64 := (mem_idx.1 hi).1
    rw [SetLike.mem_coe, codeQ_comm i c, hfix]
    change mact (matCode (sEltG i).1) c.1 ^^^ c.1 ∈ F
    rw [matCode_sEltG hi64]
    exact h1 i ((hE i).1 hi) c.1 c.2
  · intro v hv
    obtain ⟨f, rfl⟩ := codeQ_surjective v
    obtain ⟨⟨f', i, c⟩, hf', hi, hc, hfe⟩ := h2 f.1 ((hfix f).1 hv)
    have hi' := (hE i).2 hi
    have hi64 := (mem_idx.1 hi').1
    have hmem : g2QAct (ZMod 2) (sEltG i) (codeQ ⟨c, hc⟩) * (codeQ ⟨c, hc⟩)⁻¹ ∈
        commV (B.map (g2QAct (ZMod 2))) :=
      Subgroup.subset_closure ⟨_, (mem_map_iff_Q hB).2 ⟨i, hi', rfl⟩, _, rfl⟩
    rw [codeQ_comm i] at hmem
    have hval : (o0Xor (o0Act (sEltG i) ⟨c, hc⟩) ⟨c, hc⟩).1 = mact (sM i) c ^^^ c := by
      change mact (matCode (sEltG i).1) c ^^^ c = _
      rw [matCode_sEltG hi64]
    have heq : codeQ f = codeQ (o0Xor (o0Act (sEltG i) ⟨c, hc⟩) ⟨c, hc⟩) := by
      rw [codeQ_eq_iff, hval]
      rcases hfe with h | h
      · exact Or.inl h.symm
      · right
        rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [heq]
    exact hmem

end Sub

end CFSG.Quasithin.H13
