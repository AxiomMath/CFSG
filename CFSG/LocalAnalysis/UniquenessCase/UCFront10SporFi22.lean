module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporDc2
public import Certificates.Certificate10505
public import CFSG.Monster.B.Fischer.Fi22Local
public import CFSG.Sporadic.Schreier.PairChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi22Dc2

open CFSG.KD.Fi22Dc2 CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Certificates
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

theorem perm_facts {p : ℕ} (hp : p < 3510) :
    P p < 3510 ∧ Q p < 3510 ∧ P (Q p) = p ∧ Q (P p) = p := by
  have h0 := (Certificates.certificate10505).2.1
  unfold permOK at h0
  have h := List.all_eq_true.1 h0 p (List.mem_range.2 hp)
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1.1.1, Nat.blt_eq.mp h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

theorem P_inj {a b : ℕ} (ha : a < 3510) (hb : b < 3510)
    (h : P a = P b) : a = b := by
  rw [← (perm_facts ha).2.2.2, ← (perm_facts hb).2.2.2, h]

noncomputable def sigma : Equiv.Perm (Fin 3510) where
  toFun i := ⟨P i, (perm_facts i.2).1⟩
  invFun i := ⟨Q i, (perm_facts i.2).2.1⟩
  left_inv i := Fin.ext (perm_facts i.2).2.2.2
  right_inv i := Fin.ext (perm_facts i.2).2.2.1

@[instance_reducible]
noncomputable def act2 : MulAction fi22P (Fin 3510) :=
  MulAction.compHom (Fin 3510) ((MulAut.conj sigma).toMonoidHom.comp fi22P.subtype)

theorem act_conj (g : fi22P) {p : ℕ} (hp : p < 3510) :
    @act fi22P _ 3510 act2 g p = P (g.1 ⟨Q p, (perm_facts hp).2.1⟩).val :=
  @act_eq fi22P _ 3510 act2 g ⟨p, hp⟩

@[expose] def tj (l : ℕ) : ℕ := [1, 2, 3, 5].getD l 0

theorem tj_lt {l : ℕ} (hl : l < 4) : tj l < 9 := by
  obtain rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  all_goals decide

theorem tw_lt {j : ℕ} (hj : j < 9) : ∀ l ∈ tw j, l < 4 := by
  interval_cases j <;> decide

theorem t_mem {j : ℕ} (hj : j < 9) : permOfArr 3510 (fi22OuterStrong3510 4)[j]! ∈ fi22OuterT := by
  rw [fi22OuterT, RawSchreierDatum.originalSubgroup]
  apply Subgroup.subset_closure
  rw [Set.mem_ofPred_eq, fi22OuterChainT, RawSchreierDatum.mem_ofArrays_original]
  exact ⟨j, hj, rfl⟩

theorem s_mem {k : ℕ} (hk : k < 19) : fi22StrongPerm k ∈ fi22P := by
  have h := fi22Chain_strong_mem ⟨k, hk⟩
  rwa [fi22Chain_strong_get] at h

noncomputable def gen
    (l : ℕ) : fi22P :=
  if h : l < 4 then ⟨permOfArr 3510 (fi22OuterStrong3510 4)[tj l]!, fi22OuterT_le (t_mem (tj_lt h))⟩
  else if l = 5 then ⟨fi22StrongPerm 0, s_mem (by norm_num)⟩
  else if l = 6 then ⟨fi22StrongPerm 1, s_mem (by norm_num)⟩
  else 1

theorem gen_lt
    {l : ℕ} (h : l < 4) :
    (gen l).1 = permOfArr 3510 (fi22OuterStrong3510 4)[tj l]! := by
  rw [gen, dif_pos h]

noncomputable def els :
    List fi22P :=
  [gen 0, gen 1, gen 2, gen 3, (hw.map gen).prod, gen 5, gen 6]

theorem act_gen
    {l : ℕ} (hl : l < 7)
    (h4 : l ≠ 4) {p : ℕ} (hp : p < 3510) : @act fi22P _ 3510 act2 (gen l) p = L l p := by
  rw [act_conj (gen l) hp]
  by_cases h : l < 4
  · have h3 := (Certificates.certificate10505).2.2.1 (tj l) (tj_lt h) p hp
    rw [gen_lt h, ← rep_fi22OuterTStrong (k := tj l) (by have := tj_lt h; omega)
      ⟨Q p, (perm_facts hp).2.1⟩]
    refine h3.trans ?_
    obtain rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
    all_goals rfl
  · obtain rfl | rfl : l = 5 ∨ l = 6 := by omega
    · have e : (gen 5).1 = fi22StrongPerm 0 := by simp [gen]
      rw [e, ← rep_fi22Strong (j := 0) (by norm_num) ⟨Q p, (perm_facts hp).2.1⟩]
      exact ((Certificates.certificate10505).2.2.2.1 0 (by norm_num) p hp).symm
    · have e : (gen 6).1 = fi22StrongPerm 1 := by simp [gen]
      rw [e, ← rep_fi22Strong (j := 1) (by norm_num) ⟨Q p, (perm_facts hp).2.1⟩]
      exact ((Certificates.certificate10505).2.2.2.1 1 (by norm_num) p hp).symm

theorem act_word :
    ∀ w : List ℕ, (∀ l ∈ w, l < 7 ∧ l ≠ 4) → ∀ {p : ℕ}, p < 3510 →
      @act fi22P _ 3510 act2 (w.map gen).prod p = wordF L w p
  | [], _, p, hp => @act_one fi22P _ 3510 act2 p hp
  | l :: w, hw, p, hp => by
    have hl := hw l List.mem_cons_self
    have ih := act_word w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hp
    have hlt := @act_lt fi22P _ 3510 act2 (w.map gen).prod p hp
    rw [ih] at hlt
    rw [List.map_cons, List.prod_cons, @act_mul fi22P _ 3510 act2 _ _ p hp, ih]
    exact act_gen hl.1 hl.2 hlt

theorem good_els :
    ∀ l < C.nl, Good 3510 (@tab fi22P _ 3510 act2 (els.getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl7 : l < 7 := hl
  have hact : ∀ p < 3510, @act fi22P _ 3510 act2 (els.getD l 1) p = L l p := by
    intro p hp
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 := by omega
    · exact act_gen (l := 0) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 1) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 2) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 3) (by norm_num) (by norm_num) hp
    · have e : els.getD 4 1 = (hw.map gen).prod := rfl
      have hw4 : ∀ x ∈ hw, x < 7 ∧ x ≠ 4 := by decide
      have h0 := (Certificates.certificate10505).2.2.2.2.1
      unfold hwOK at h0
      rw [e, act_word hw hw4 hp]
      exact (Nat.eq_of_beq_eq_true (List.all_eq_true.1 h0 p (List.mem_range.2 hp))).symm
    · exact act_gen (l := 5) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 6) (by norm_num) (by norm_num) hp
  refine ⟨?_, fun p hp => ?_⟩
  · rw [tab, List.size_toArray, List.length_map, List.length_finRange]
  have e1 : (@tab fi22P _ 3510 act2 (els.getD l 1)).toArray.getD p 0 =
      @act fi22P _ 3510 act2 (els.getD l 1) p := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
    rfl
  have e2 : C.L l p = L l p := rfl
  have h := @act_lt fi22P _ 3510 act2 (els.getD l 1) p hp
  rw [hact p hp] at h
  rw [e1, e2, hact p hp]
  exact ⟨rfl, h⟩

theorem t_eq
    {j : ℕ} (hj : j < 9) :
    (((tw j).map gen).prod : fi22P).1 = permOfArr 3510 (fi22OuterStrong3510 4)[j]! := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hp : P x.val < 3510 := (perm_facts x.2).1
  have hy : (⟨Q (P x.val), (perm_facts hp).2.1⟩ : Fin 3510) = x := Fin.ext (perm_facts x.2).2.2.2
  have h1 := act_word (tw j) (fun l hl => ⟨by have := tw_lt hj l hl; omega,
    by have := tw_lt hj l hl; omega⟩) hp
  rw [act_conj _ hp, hy] at h1
  have h2 := (Certificates.certificate10505).2.2.1 j hj (P x.val) hp
  rw [(perm_facts x.2).2.2.2, rep_fi22OuterTStrong (k := j) (by omega) x] at h2
  exact P_inj (Fin.isLt _) (Fin.isLt _) (h1.trans h2.symm)

theorem card_S :
    Nat.card (Subgroup.closure {x | x ∈ els.take 4}) = 2 ^ 17 := by
  have htake : els.take 4 = [gen 0, gen 1, gen 2, gen 3] := rfl
  have hgen : ∀ x ∈ els.take 4, ∃ l < 4, x = gen l := by
    intro x hx
    rw [htake] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩]
  have hmem : ∀ l < 4, gen l ∈ Subgroup.closure {x | x ∈ els.take 4} := by
    intro l hl
    apply Subgroup.subset_closure
    rw [Set.mem_ofPred_eq, htake]
    obtain rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
    all_goals simp
  have hT : (Subgroup.closure {x | x ∈ els.take 4}).map fi22P.subtype = fi22OuterT := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      intro x hx
      obtain ⟨l, hl, rfl⟩ := hgen x hx
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype, gen_lt hl]
      exact t_mem (tj_lt hl)
    · rw [fi22OuterT, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
      intro g hg
      rw [Set.mem_ofPred_eq, fi22OuterChainT, RawSchreierDatum.mem_ofArrays_original] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj9 : j < 9 := hj
      rw [SetLike.mem_coe, Subgroup.mem_map]
      refine ⟨((tw j).map gen).prod, Subgroup.list_prod_mem _ fun x hx => ?_, t_eq hj9⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact hmem l (tw_lt hj9 l hl)
  rw [← Subgroup.card_subtype fi22P, hT, card_fi22OuterT]
  norm_num

theorem sep_ok :
    ∀ g : fi22P, (∀ p ∈ D.sep, @act fi22P _ 3510 act2 g p = p) → g = 1 := by
  intro g hg
  have hB : CFSG.Sporadic.Schreier.BaseFaithful fi22P [0, 1, 2, 3, 6, 4] := by
    have h := CFSG.Sporadic.Schreier.baseFaithful_of_valid fi22Chain_valid.1
    rw [fi22Chain_base] at h
    exact h
  apply Subtype.ext
  refine hB g.1 g.2 fun x hx => Fin.ext ?_
  have hxP : P x.val ∈ D.sep := by
    rw [(Certificates.certificate10505).2.2.2.2.2]
    exact List.mem_map_of_mem hx
  have h1 := hg _ hxP
  rw [act_conj g (perm_facts x.2).1] at h1
  have hQP : Q (P x.val) = x.val := (perm_facts x.2).2.2.2
  have e : (⟨Q (P x.val), (perm_facts (perm_facts x.2).1).2.1⟩ : Fin 3510) = x := Fin.ext hQP
  rw [e] at h1
  have h2 := congrArg Q h1
  rwa [(perm_facts (g.1 x).2).2.2.2, hQP] at h2

end Fi22Dc2

open Fi22Dc2 CFSG.KD.Fi22Dc2 CFSG.Monster.B.Fischer in
theorem k105SporAt_Fi22 :
    K105SporAt .Fi22 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃* ↥fi22P := fi22PermEquiv
  have hN : Nat.card ↥fi22P = C.N1 * C.N2 * 2 ^ C.k := by
    rw [card_fi22P]
    show 64561751654400 = 142155 * 3465 * 2 ^ 17
    norm_num
  have hodd : ¬ 2 ∣ C.N1 * C.N2 := by
    show ¬ 2 ∣ 142155 * 3465
    norm_num
  exact @k105SporAt_of_dc2 .Fi22 fi22P _ _ 3510 act2 C rfl D els rfl good_els card_S hN hodd
    sep_ok (Certificates.certificate10505).1 e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
