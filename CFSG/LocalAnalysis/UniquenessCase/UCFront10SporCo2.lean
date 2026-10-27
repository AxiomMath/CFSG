module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporDc2
public import Certificates.Certificate10503
public import CFSG.Sporadic.Co2Inv
public import CFSG.Sporadic.Schreier.PairChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Co2Dc2

open CFSG.KD.Co2Dc2 CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Inv CFSG.Monster.B.Co2
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

theorem perm_facts {p : ℕ} (hp : p < 2300) :
    P p < 2300 ∧ Q p < 2300 ∧ P (Q p) = p ∧ Q (P p) = p := by
  have h0 := (Certificates.certificate10503).2.1
  unfold permOK at h0
  have h := List.all_eq_true.1 h0 p (List.mem_range.2 hp)
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1.1.1, Nat.blt_eq.mp h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

noncomputable def sigma : Equiv.Perm (Fin 2300) where
  toFun i := ⟨P i, (perm_facts i.2).1⟩
  invFun i := ⟨Q i, (perm_facts i.2).2.1⟩
  left_inv i := Fin.ext (perm_facts i.2).2.2.2
  right_inv i := Fin.ext (perm_facts i.2).2.2.1

@[instance_reducible]
noncomputable def act2 : MulAction co2P (Fin 2300) :=
  MulAction.compHom (Fin 2300) ((MulAut.conj sigma).toMonoidHom.comp co2P.subtype)

theorem act_conj (g : co2P) {p : ℕ} (hp : p < 2300) :
    @act co2P _ 2300 act2 g p = P (g.1 ⟨Q p, (perm_facts hp).2.1⟩).val :=
  @act_eq co2P _ 2300 act2 g ⟨p, hp⟩

noncomputable def gen
    (l : ℕ) : co2P :=
  if h : l < 5 then ⟨permOfArr 2300 (genPerm l), genPerm_mem h⟩
  else if l = 6 then ⟨co2Gen 0, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  else if l = 7 then ⟨co2Gen 1, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  else 1

noncomputable def els :
    List co2P :=
  [gen 0, gen 1, gen 2, gen 3, gen 4, (hw.map gen).prod, gen 6, gen 7]

theorem act_gen
    {l : ℕ} (hl : l < 8)
    (h5 : l ≠ 5) {p : ℕ} (hp : p < 2300) : @act co2P _ 2300 act2 (gen l) p = L l p := by
  rw [act_conj (gen l) hp]
  by_cases h : l < 5
  · have e : (gen l).1 = permOfArr 2300 (genPerm l) := by rw [gen, dif_pos h]
    rw [e, ← rep_genPerm h ⟨Q p, (perm_facts hp).2.1⟩]
    exact ((Certificates.certificate10503).2.2.1 l h p hp).symm
  · obtain rfl | rfl : l = 6 ∨ l = 7 := by omega
    · have e : (gen 6).1 = co2Gen 0 := by simp [gen]
      rw [e, ← rep_co2Gen (k := 0) (by norm_num) ⟨Q p, (perm_facts hp).2.1⟩]
      exact ((Certificates.certificate10503).2.2.2.1 0 (by norm_num) p hp).symm
    · have e : (gen 7).1 = co2Gen 1 := by simp [gen]
      rw [e, ← rep_co2Gen (k := 1) (by norm_num) ⟨Q p, (perm_facts hp).2.1⟩]
      exact ((Certificates.certificate10503).2.2.2.1 1 (by norm_num) p hp).symm

theorem act_word :
    ∀ w : List ℕ, (∀ l ∈ w, l < 8 ∧ l ≠ 5) → ∀ {p : ℕ}, p < 2300 →
      @act co2P _ 2300 act2 (w.map gen).prod p = wordF L w p
  | [], _, p, hp => @act_one co2P _ 2300 act2 p hp
  | l :: w, hw, p, hp => by
    have hl := hw l List.mem_cons_self
    have ih := act_word w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hp
    have hlt := @act_lt co2P _ 2300 act2 (w.map gen).prod p hp
    rw [ih] at hlt
    rw [List.map_cons, List.prod_cons, @act_mul co2P _ 2300 act2 _ _ p hp, ih]
    exact act_gen hl.1 hl.2 hlt

theorem good_els :
    ∀ l < C.nl, Good 2300 (@tab co2P _ 2300 act2 (els.getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl8 : l < 8 := hl
  have hact : ∀ p < 2300, @act co2P _ 2300 act2 (els.getD l 1) p = L l p := by
    intro p hp
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 := by omega
    · exact act_gen (l := 0) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 1) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 2) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 3) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 4) (by norm_num) (by norm_num) hp
    · have e : els.getD 5 1 = (hw.map gen).prod := rfl
      have hw5 : ∀ x ∈ hw, x < 8 ∧ x ≠ 5 := by decide
      have h0 := (Certificates.certificate10503).2.2.2.2.1
      unfold hwOK at h0
      rw [e, act_word hw hw5 hp]
      exact (Nat.eq_of_beq_eq_true (List.all_eq_true.1 h0 p (List.mem_range.2 hp))).symm
    · exact act_gen (l := 6) (by norm_num) (by norm_num) hp
    · exact act_gen (l := 7) (by norm_num) (by norm_num) hp
  refine ⟨?_, fun p hp => ?_⟩
  · rw [tab, List.size_toArray, List.length_map, List.length_finRange]
  have e1 : (@tab co2P _ 2300 act2 (els.getD l 1)).toArray.getD p 0 =
      @act co2P _ 2300 act2 (els.getD l 1) p := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
    rfl
  have e2 : C.L l p = L l p := rfl
  have h := @act_lt co2P _ 2300 act2 (els.getD l 1) p hp
  rw [hact p hp] at h
  rw [e1, e2, hact p hp]
  exact ⟨rfl, h⟩

@[expose] noncomputable def phi :
    CFSG.Blueprint.NativeSporadic.Co2 →* co2P := by
  with_reducible_and_instances exact co2PermEquiv.toMonoidHom

theorem phi_apply
    (u : CFSG.Blueprint.NativeSporadic.Co2) : phi u = co2PermEquiv u :=
  rfl

theorem card_S :
    Nat.card (Subgroup.closure {x | x ∈ els.take 5}) = 2 ^ 18 := by
  have hj : ∀ j : Fin 5, phi (genCo2 j) = gen j := fun j => by
    rw [phi_apply, genCo2, dif_pos j.2, MulEquiv.apply_symm_apply, gen, dif_pos j.2]
  have htake : els.take 5 = [gen 0, gen 1, gen 2, gen 3, gen 4] := rfl
  have hmem : ∀ j : Fin 5, gen j ∈ els.take 5 := by
    intro j
    rw [htake]
    fin_cases j
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h1 : Subgroup.closure {x | x ∈ els.take 5} ≤ sylowS.map phi := by
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : x ∈ els.take 5 := hx
    rw [htake] at hx'
    obtain ⟨j, rfl⟩ : ∃ j : Fin 5, gen j = x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    exact Subgroup.mem_map.2 ⟨genCo2 j, Subgroup.subset_closure ⟨j, rfl⟩, hj j⟩
  have h2 : sylowS.map phi ≤ Subgroup.closure {x | x ∈ els.take 5} := by
    rw [Subgroup.map_le_iff_le_comap, sylowS, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, hj j]
    exact Subgroup.subset_closure (hmem j)
  have hinj : Function.Injective phi := fun u v h => by
    rw [phi_apply, phi_apply] at h
    exact co2PermEquiv.injective h
  rw [le_antisymm h1 h2, Subgroup.card_map_of_injective hinj, card_sylowS]
  norm_num

theorem sep_ok :
    ∀ g : co2P, (∀ p ∈ D.sep, @act co2P _ 2300 act2 g p = p) → g = 1 := by
  intro g hg
  have hB : CFSG.Sporadic.Schreier.BaseFaithful co2P [0, 1, 2, 3, 5, 4] := by
    have h := CFSG.Sporadic.Schreier.baseFaithful_of_valid co2Q_valid.1
    rwa [co2Q_originalSubgroup, co2Q_base] at h
  apply Subtype.ext
  refine hB g.1 g.2 fun x hx => Fin.ext ?_
  have hxP : P x.val ∈ D.sep := by
    rw [(Certificates.certificate10503).2.2.2.2.2]
    exact List.mem_map_of_mem hx
  have h1 := hg _ hxP
  rw [act_conj g (perm_facts x.2).1] at h1
  have hQP : Q (P x.val) = x.val := (perm_facts x.2).2.2.2
  have e : (⟨Q (P x.val), (perm_facts (perm_facts x.2).1).2.1⟩ : Fin 2300) = x := Fin.ext hQP
  rw [e] at h1
  have h2 := congrArg Q h1
  rwa [(perm_facts (g.1 x).2).2.2.2, hQP] at h2

end Co2Dc2

open Co2Dc2 CFSG.KD.Co2Dc2 CFSG.Sporadic.Co2Cert in
theorem k105SporAt_Co2 :
    K105SporAt .Co2 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Co2 ≃* ↥co2P := co2PermEquiv
  have hN : Nat.card ↥co2P = C.N1 * C.N2 * 2 ^ C.k := by
    rw [card_co2P]
    show 42305421312000 = 46575 * 3465 * 2 ^ 18
    norm_num
  have hodd : ¬ 2 ∣ C.N1 * C.N2 := by
    show ¬ 2 ∣ 46575 * 3465
    norm_num
  exact @k105SporAt_of_dc2 .Co2 co2P _ _ 2300 act2 C rfl D els rfl good_els card_S hN hodd
    sep_ok (Certificates.certificate10503).1 e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
