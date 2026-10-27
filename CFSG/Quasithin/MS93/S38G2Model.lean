module

public import CFSG.Quasithin.Background.SmithB42U33Off

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
open scoped Pointwise commutatorElement

@[expose] def qlB (i : ℕ) : Bool := i < 16 || (32 ≤ i && i < 48)

theorem off_idx : ∀ e < 8, 8 ≤ (o0Codes.filter fun c =>
      !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length →
    e = 1 ∨ e = 2 ∨ e = 6 := by
  decide +kernel

theorem cent_off : ∀ e ∈ [1, 2, 6], ∀ i < 64,
    (∀ j ∈ sE8.getD e [], mmul (sM i) (sM j) = mmul (sM j) (sM i)) → i ∈ sE8.getD e [] := by
  decide +kernel

theorem ptw_off : ∀ e ∈ [1, 2, 6], ∀ i < 64,
    (∀ c ∈ sFixQ.getD e [], fixQB (sM i) c = true) → i ∈ sE8.getD e [] := by
  decide +kernel

theorem ql_off : ∀ e ∈ [1, 2, 6], ∀ i ∈ sE8.getD e [], qlB i = true := by
  decide +kernel

theorem ql_mul : ∀ i ∈ (List.range 64).filter qlB, ∀ j ∈ (List.range 64).filter qlB,
    ∀ k ∈ List.range 64, mmul (sM i) (sM j) = sM k → qlB k = true := by
  decide +kernel

theorem ql_comm : ∀ i < 64, ∀ j < 64, qlB i = true → qlB j = true →
    mmul (sM i) (sM j) = mmul (sM j) (sM i) ∨
      mmul (sM i) (sM j) = mmul (sM 4) (mmul (sM j) (sM i)) := by
  decide +kernel

theorem ql_inv : ∀ i ∈ (List.range 64).filter qlB, ∀ k ∈ List.range 64,
    mmul (sM i) (sM k) = idMat → qlB k = true := by
  decide +kernel

@[expose] def IsOffG2 (B : Subgroup ↥(quasithinG2 (ZMod 2))) : Prop :=
  B ≠ ⊥ ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ (∀ b ∈ B, b ^ 2 = 1) ∧
    Nat.card ModQ ≤ Nat.card B * Nat.card (fixV (B.map (g2QAct (ZMod 2))))

theorem exists_sE8_of_isOffG2 {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (hoff : IsOffG2 B) : ∃ e ∈ [1, 2, 6], ∀ l, l ∈ idx B ↔ l ∈ sE8.getD e [] := by
  classical
  obtain ⟨hB1, hBc, hB2, hff⟩ := hoff
  have hff' : 64 ≤ (idx B).card * Nat.card (fixV (B.map (g2QAct (ZMod 2)))) := by
    rw [← card_eq_idx hB, ← card_ModQ]
    exact hff
  obtain ⟨h8, hfix8⟩ := B42U33.offender_exact_sylow hB hB1 hBc hB2 hff'
  obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8.ge
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_Q hB P hP
  have hfilter : (o0Codes.filter fun c => !c.testBit 0 && P c) =
      o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c := by
    refine List.filter_congr fun c _ => ?_
    congr 1
    simp only [P]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
    exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
  have hcount : 8 ≤ (o0Codes.filter fun c =>
      !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length := by
    rw [← hfilter, ← hC, hfix8]
  rcases off_idx e he hcount with rfl | rfl | rfl
  · exact ⟨1, by simp, hiff⟩
  · exact ⟨2, by simp, hiff⟩
  · exact ⟨6, by simp, hiff⟩

theorem matCode_sEltG_mul {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    matCode ⇑(sEltG i * sEltG j).1 = mmul (sM i) (sM j) :=
  matCode_mul_sElt hi hj

theorem mem_of_commute_sylow {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (hoff : IsOffG2 B) {y : ↥(quasithinG2 (ZMod 2))} (hy : y ∈ sSubG)
    (hyc : ∀ b ∈ B, y * b = b * y) : y ∈ B := by
  obtain ⟨e, he, hiff⟩ := exists_sE8_of_isOffG2 hB hoff
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hy
  have hmem : i ∈ sE8.getD e [] := by
    refine cent_off e he i hi fun j hj => ?_
    have hj' := (hiff j).2 hj
    have hj64 := (mem_idx.1 hj').1
    have hc := hyc _ (mem_idx.1 hj').2
    rw [← matCode_sEltG_mul hi hj64, ← matCode_sEltG_mul hj64 hi, hc]
  exact (mem_idx.1 ((hiff i).2 hmem)).2

theorem mem_of_fix_sylow {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (hoff : IsOffG2 B) {y : ↥(quasithinG2 (ZMod 2))} (hy : y ∈ sSubG)
    (hyf : ∀ v ∈ fixV (B.map (g2QAct (ZMod 2))), g2QAct (ZMod 2) y v = v) : y ∈ B := by
  obtain ⟨e, he, hiff⟩ := exists_sE8_of_isOffG2 hB hoff
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hy
  have he8 : e < 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    omega
  have hmem : i ∈ sE8.getD e [] := by
    refine ptw_off e he i hi fun c hc => ?_
    rw [sFixQ_spec e he8, List.mem_filter, List.all_eq_true] at hc
    obtain ⟨hc0, hcall⟩ := hc
    let c' : O0C := ⟨c, hc0⟩
    have hfix : codeQ c' ∈ fixV (B.map (g2QAct (ZMod 2))) :=
      (mem_fixV_codeQ hB c').2 fun i' hi' => hcall i' ((hiff i').1 hi')
    have h1 := hyf _ hfix
    have hm : mact (sM i) c ∈ o0Codes := by
      rw [← o0Act_sEltG hi c']
      exact (o0Act (sEltG i) c').2
    rw [g2QAct_codeQ, eq_comm, codeQ_eq_iff, o0Act_sEltG hi] at h1
    exact (fixQB_iff (sM i) hc0 hm).2 h1
  exact (mem_idx.1 ((hiff i).2 hmem)).2

@[expose] def qlSub : Subgroup ↥(quasithinG2 (ZMod 2)) where
  carrier := {g | ∃ i < 64, qlB i = true ∧ sEltG i = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, hqi, rfl⟩ ⟨j, hj, hqj, rfl⟩
    obtain ⟨k, hk, hke⟩ := sElt_mul hi hj
    refine ⟨k, hk, ?_, Subtype.ext hke.symm⟩
    refine ql_mul i (List.mem_filter.2 ⟨List.mem_range.2 hi, hqi⟩) j
      (List.mem_filter.2 ⟨List.mem_range.2 hj, hqj⟩) k (List.mem_range.2 hk) ?_
    rw [← matCode_mul_sElt hi hj, hke, matCode_sElt hk]
  one_mem' := ⟨0, by norm_num, by decide, sEltG_zero⟩
  inv_mem' := by
    rintro _ ⟨i, hi, hqi, rfl⟩
    obtain ⟨k, hk, hke⟩ := sElt_inv hi
    refine ⟨k, hk, ?_, Subtype.ext hke.symm⟩
    refine ql_inv i (List.mem_filter.2 ⟨List.mem_range.2 hi, hqi⟩) k (List.mem_range.2 hk) ?_
    rw [← matCode_mul_sElt hi hk, ← hke, mul_inv_cancel, ← sElt_zero, matCode_sElt (by norm_num),
      sM_zero]

theorem le_qlSub {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG) (hoff : IsOffG2 B) :
    B ≤ qlSub := by
  obtain ⟨e, he, hiff⟩ := exists_sE8_of_isOffG2 hB hoff
  intro b hb
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 (hB hb)
  exact ⟨i, hi, ql_off e he i ((hiff i).1 (mem_idx.2 ⟨hi, hb⟩)), rfl⟩

theorem comm_qlSub {x y : ↥(quasithinG2 (ZMod 2))} (hx : x ∈ qlSub) (hy : y ∈ qlSub) :
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = sEltG 4 := by
  obtain ⟨i, hi, hqi, rfl⟩ := hx
  obtain ⟨j, hj, hqj, rfl⟩ := hy
  have hcode : ∀ g h : ↥(quasithinG2 (ZMod 2)), matCode ⇑g.1 = matCode ⇑h.1 → g = h :=
    fun g h e => Subtype.ext (LinearEquiv.toLinearMap_injective (matCode_injective e))
  rcases ql_comm i hi j hj hqi hqj with h | h
  · left
    have : sEltG i * sEltG j = sEltG j * sEltG i := by
      apply hcode
      rw [matCode_sEltG_mul hi hj, matCode_sEltG_mul hj hi, h]
    rw [commutatorElement_def, this]
    group
  · right
    have : sEltG i * sEltG j = sEltG 4 * (sEltG j * sEltG i) := by
      apply hcode
      have h4 : (4 : ℕ) < 64 := by norm_num
      rw [matCode_sEltG_mul hi hj, Subgroup.coe_mul, matCode_mul, matCode_sEltG h4,
        matCode_sEltG_mul hj hi, h]
    rw [commutatorElement_def, this]
    group

theorem exists_conj_le_sSubG {P : Subgroup ↥(quasithinG2 (ZMod 2))} (hP : IsPGroup 2 ↥P) :
    ∃ g : ↥(quasithinG2 (ZMod 2)), P.map (MulAut.conj g).toMonoidHom ≤ sSubG := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) S sylowSub
  refine ⟨g, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have h1 : MulAut.conj g • b ∈ MulAut.conj g • (S : Subgroup ↥(quasithinG2 (ZMod 2))) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hS hb)
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

theorem map_conj_map_g2QAct (B : Subgroup ↥(quasithinG2 (ZMod 2))) (g : ↥(quasithinG2 (ZMod 2))) :
    (B.map (MulAut.conj g).toMonoidHom).map (g2QAct (ZMod 2)) =
      (B.map (g2QAct (ZMod 2))).map (MulAut.congr (g2QAct (ZMod 2) g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun b => ?_
  change g2QAct (ZMod 2) (g * b * g⁻¹) = MulAut.congr (g2QAct (ZMod 2) g) (g2QAct (ZMod 2) b)
  rw [congr_eq_conj, map_mul, map_mul, map_inv]

theorem IsOffG2.map_conj {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : IsOffG2 B)
    (g : ↥(quasithinG2 (ZMod 2))) : IsOffG2 (B.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hB1, hBc, hB2, hff⟩ := hB
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨fun h => hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  · rw [Subgroup.card_map_of_injective hinj, map_conj_map_g2QAct, fixV_map_congr,
      Subgroup.card_map_of_injective (f := (g2QAct (ZMod 2) g).toMonoidHom)
        (g2QAct (ZMod 2) g).injective]
    exact hff

theorem mem_of_commute_off {P B : Subgroup ↥(quasithinG2 (ZMod 2))} (hP : IsPGroup 2 ↥P)
    (hBP : B ≤ P) (hB : IsOffG2 B) {y : ↥(quasithinG2 (ZMod 2))} (hy : y ∈ P)
    (hyc : ∀ b ∈ B, y * b = b * y) : y ∈ B := by
  obtain ⟨g, hg⟩ := exists_conj_le_sSubG hP
  have h := mem_of_commute_sylow ((Subgroup.map_mono hBP).trans hg) (hB.map_conj g)
    (hg ⟨y, hy, rfl⟩) (fun b' hb' => by
      obtain ⟨b, hb, rfl⟩ := hb'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * y * g⁻¹ * (g * b * g⁻¹) = g * (y * b) * g⁻¹ by group, hyc b hb]
      group)
  obtain ⟨b, hb, hb'⟩ := h
  rw [(MulAut.conj g).injective hb'] at hb
  exact hb

theorem mem_of_fix_off {P B : Subgroup ↥(quasithinG2 (ZMod 2))} (hP : IsPGroup 2 ↥P)
    (hBP : B ≤ P) (hB : IsOffG2 B) {y : ↥(quasithinG2 (ZMod 2))} (hy : y ∈ P)
    (hyf : ∀ v ∈ fixV (B.map (g2QAct (ZMod 2))), g2QAct (ZMod 2) y v = v) : y ∈ B := by
  obtain ⟨g, hg⟩ := exists_conj_le_sSubG hP
  have h := mem_of_fix_sylow ((Subgroup.map_mono hBP).trans hg) (hB.map_conj g)
    (hg ⟨y, hy, rfl⟩) (fun v hv => by
      rw [map_conj_map_g2QAct, fixV_map_congr] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      change g2QAct (ZMod 2) (g * y * g⁻¹) (g2QAct (ZMod 2) g w) = g2QAct (ZMod 2) g w
      rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
        hyf w hw])
  obtain ⟨b, hb, hb'⟩ := h
  rw [(MulAut.conj g).injective hb'] at hb
  exact hb

theorem exists_comm_off {P : Subgroup ↥(quasithinG2 (ZMod 2))} (hP : IsPGroup 2 ↥P) :
    ∃ (X : Subgroup ↥(quasithinG2 (ZMod 2))) (z : ↥(quasithinG2 (ZMod 2))),
      (∀ B, IsOffG2 B → B ≤ P → B ≤ X) ∧ ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := by
  obtain ⟨g, hg⟩ := exists_conj_le_sSubG hP
  refine ⟨qlSub.map (MulAut.conj g⁻¹).toMonoidHom, g⁻¹ * sEltG 4 * g, fun B hB hBP => ?_,
    ?_⟩
  · have h := le_qlSub ((Subgroup.map_mono hBP).trans hg) (hB.map_conj g)
    intro b hb
    refine ⟨g * b * g⁻¹, h ⟨b, hb, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases comm_qlSub hx hy with h | h
    · left
      rw [← map_commutatorElement, h, map_one]
    · right
      rw [← map_commutatorElement, h]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem card_mul_card_fixV_le {B : Subgroup ↥(quasithinG2 (ZMod 2))}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    Nat.card B * Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤ Nat.card ModQ := by
  by_contra hlt
  push Not at hlt
  have hB1 : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.map_bot, B1.fixV_bot, Subgroup.card_bot, Subgroup.card_top, one_mul] at hlt
    exact lt_irrefl _ hlt
  have hinj : Function.Injective (g2QAct (ZMod 2)) := g2QAct_injective
  have hle : B.map (g2QAct (ZMod 2)) ≤ (g2QAct (ZMod 2)).range := Subgroup.map_le_range _ _
  have hne : B.map (g2QAct (ZMod 2)) ≠ ⊥ := fun h =>
    hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h)
  have hea : IsElemAbelian2 (B.map (g2QAct (ZMod 2))) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBc a ha b hb]
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hB2 b hb, map_one]
  have hcard : Nat.card (B.map (g2QAct (ZMod 2))) = Nat.card B :=
    Subgroup.card_map_of_injective hinj
  obtain ⟨h1, h2⟩ := B42U33.offender_exact hle hne hea (by rw [hcard]; exact hlt.le)
  rw [hcard] at h1
  rw [h1, h2, card_ModQ] at hlt
  norm_num at hlt

end CFSG.Quasithin.MS93.S38G
