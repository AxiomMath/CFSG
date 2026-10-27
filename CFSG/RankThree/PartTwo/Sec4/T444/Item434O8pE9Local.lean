module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434O8pE9

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord wordPerm wordPerm_mem getElem!_map'
  letters_of_all mapWord_rep dPair_facts isElemAbelian_subgroupOf card_subgroupOf_of_le)

theorem covRow_get {n : ℕ} {cD cQ : ArrCert} {h : Array ℕ} {a : ℕ} (ha : a < cQ.pts.size) :
    (covRow n cD h cQ)[a]! = cD.pts.toList.any (eqA n (conjA n h cQ.pts[a]!)) :=
  getElem!_map' cQ.pts _ ha

theorem e9_sound (X : E9Data) (h : e9Check X = true)
    (P : Subgroup (Equiv.Perm (Fin X.n))) (hP : ∀ l < X.pg.size, permOfArr X.n X.pg[l]! ∈ P) :
    ∃ Q : Subgroup (Equiv.Perm (Fin X.n)), Q ≤ P ∧ Nat.card Q = X.qOrd ∧
      ∀ x y : Equiv.Perm (Fin X.n), x ∈ Q → y ∈ Q → x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x →
        x ≠ 1 → y ∉ Subgroup.zpowers x →
        ∃ E : Subgroup (Equiv.Perm (Fin X.n)), E ≤ P ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
          x ∈ E ∧ y ∈ E := by
  unfold e9Check e9Check' at h
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hpg, hkeys, hqW, hhW, hdW, hQenum, hQcard, hDenum, hD81, hDab, hhv, hpairs⟩ := h
  have hpgv : ∀ l < X.pg.size, validA X.n X.pg[l]! = true := fun l hl => allLt_spec hpg hl
  have hk3 : ∀ p ∈ X.qKeys ++ X.dKeys, p < X.n := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  have hqk : ∀ p ∈ X.qKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hdk : ∀ p ∈ X.dKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hqWl := letters_of_all hqW
  have hhWl := letters_of_all hhW
  have hdWl := letters_of_all hdW
  set qg := qGens X with hqg
  have hqgv : ∀ l < qg.size, validA X.n qg[l]! = true := fun l hl => enumOK_gens_valid hQenum hl
  have hqsize : qg.size = X.qW.size := by simp [hqg, qGens]
  have hqgP : ∀ k < qg.size, permOfArr X.n qg[k]! ∈ P := by
    intro k hk
    have hk' : k < X.qW.size := hqsize ▸ hk
    show permOfArr X.n (X.qW.map (posWord X.n X.pg))[k]! ∈ P
    rw [permOfArr_eq_of_rep (mapWord_rep hpgv hqWl hk')]
    exact wordPerm_mem hP (hqWl k hk')
  set Q := Subgroup.closure (permsA X.n qg) with hQdef
  have hQgen : ∀ k < qg.size, permOfArr X.n qg[k]! ∈ Q := fun k hk =>
    Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hQP : Q ≤ P := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hqgP k hk
  have hQcard' : Nat.card Q = X.qOrd := (enumOK_spec hqk hQenum).2.1.trans hQcard
  obtain ⟨D, hDQ, hDe, hD81', hDmem⟩ := dPair_facts hqgv hQgen hdk hdWl hDenum hD81 hDab
  refine ⟨Q, hQP, hQcard', ?_⟩
  intro x y hxQ hyQ hx3 hy3 hxy hx1 hyx
  obtain ⟨a, ha, hrx⟩ := enumOK_exists_rep hqk hQenum hxQ
  obtain ⟨b, hb, hry⟩ := enumOK_exists_rep hqk hQenum hyQ
  have hpair := allLt_spec (allLt_spec hpairs ha) hb
  simp only [pairOK, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true,
    List.mem_range] at hpair
  have hcb : ∀ {c : ℕ}, c < (qCert X).pts.size → (cubeOne X.n (qCert X))[c]! =
      eqA X.n (compA X.n (qCert X).pts[c]! (compA X.n (qCert X).pts[c]! (qCert X).pts[c]!))
        (idA X.n) := fun hc => getElem!_map' (qCert X).pts _ hc
  rcases hpair with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | ⟨i, hi, hia, hib⟩
  · exfalso
    have h5 := (eqA_iff (rep_compA hrx (rep_compA hrx hrx)) rep_idA).2
      (by rw [← pow_three]; exact hx3)
    rw [hcb ha, h5] at h1
    exact absurd h1 (by simp)
  · exfalso
    have h5 := (eqA_iff (rep_compA hry (rep_compA hry hry)) rep_idA).2
      (by rw [← pow_three]; exact hy3)
    rw [hcb hb, h5] at h2
    exact absurd h2 (by simp)
  · exact absurd ((eqA_iff hrx rep_idA).1 h3) hx1
  · exact absurd (by rw [(eqA_iff hry rep_idA).1 h4]; exact Subgroup.one_mem _) hyx
  · exact absurd (by rw [(eqA_iff hry hrx).1 h5]; exact Subgroup.mem_zpowers _) hyx
  · exfalso
    have h5 := (eqA_iff (rep_compA hrx hry) (rep_compA hry hrx)).2 hxy
    rw [h5] at h6
    exact absurd h6 (by simp)
  · exact absurd (by
      rw [(eqA_iff hry (rep_compA hrx hrx)).1 h7]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x)) hyx
  ·
    have hsz : ((hArrs X).map fun h => covRow X.n (dCert X) h (qCert X)).size = X.hW.size := by
      simp [hArrs]
    have hi' : i < (hArrs X).size := by
      have : i < X.hW.size := hsz ▸ hi
      simpa [hArrs] using this
    have hi'' : i < X.hW.size := by simpa [hArrs] using hi'
    have hrow : (((hArrs X).map fun h => covRow X.n (dCert X) h (qCert X))[i]!) =
        covRow X.n (dCert X) (hArrs X)[i]! (qCert X) := getElem!_map' (hArrs X) _ hi'
    rw [hrow, covRow_get ha] at hia
    rw [hrow, covRow_get hb] at hib
    obtain ⟨t1, ht1, he1⟩ := List.any_eq_true.1 hia
    obtain ⟨t2, ht2, he2⟩ := List.any_eq_true.1 hib
    have hv : validA X.n (hArrs X)[i]! = true := allLt_spec hhv hi'
    have hHrep : Rep X.n (hArrs X)[i]! (wordPerm X.n X.pg X.hW[i]!) :=
      mapWord_rep hpgv hhWl hi''
    have hHP : wordPerm X.n X.pg X.hW[i]! ∈ P := wordPerm_mem hP (hhWl i hi'')
    set H := wordPerm X.n X.pg X.hW[i]! with hH
    have hcx := rep_conjA hv hrx
    have hcy := rep_conjA hv hry
    rw [permOfArr_eq_of_rep hHrep] at hcx hcy
    have hxD : H * x * H⁻¹ ∈ D := hDmem t1 _ (rep_of_eqA hcx he1) ht1
    have hyD : H * y * H⁻¹ ∈ D := hDmem t2 _ (rep_of_eqA hcy he2) ht2
    have hmemE : ∀ z, H * z * H⁻¹ ∈ D → z ∈ D.map (MulAut.conj H⁻¹).toMonoidHom := fun z hz =>
      ⟨H * z * H⁻¹, hz, by simp [mul_assoc]⟩
    refine ⟨D.map (MulAut.conj H⁻¹).toMonoidHom, ?_, ?_, ?_, hmemE x hxD, hmemE y hyD⟩
    · rintro _ ⟨d, hd, rfl⟩
      show H⁻¹ * d * H⁻¹⁻¹ ∈ P
      rw [inv_inv]
      exact P.mul_mem (P.mul_mem (P.inv_mem hHP) (hQP (hDQ hd))) hHP
    · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ D hDe
    · rw [Subgroup.card_map_of_injective (MulAut.conj H⁻¹).injective]
      exact hD81'

theorem exists_e81_of_e9 {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : Nat.card Q = 3 ^ (Nat.card G).factorization 3)
    (hgood : ∀ x ∈ Q, ∀ y ∈ Q, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 →
      y ∉ Subgroup.zpowers x →
      ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ x ∈ E ∧ y ∈ E)
    {P : Subgroup G} (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ P ≤ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hQ hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'e : IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP'9 : Nat.card P' = 9 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]
  have hP'Q : P' ≤ Q := Item434AltPerm.map_conj_inv_le hg
  have hab : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP'e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x, hxP', hx1⟩ : ∃ x ∈ P', x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : P' ≤ ⊥ := fun a ha => Subgroup.mem_bot.2 (hall a ha)
    have := Subgroup.card_le_of_le this
    rw [Subgroup.card_bot] at this
    omega
  have hx3 := hP'e.2 x hxP'
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨y, hyP', hyx⟩ : ∃ y ∈ P', y ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show P' ≤ Subgroup.zpowers x from hall)
    rw [Nat.card_zpowers, hx] at this
    omega
  have hy3 := hP'e.2 y hyP'
  obtain ⟨E, hEe, hE81, hxE, hyE⟩ :=
    hgood x (hP'Q hxP') y (hP'Q hyP') hx3 hy3 (hab x hxP' y hyP') hx1 hyx
  have hP'E : P' ≤ E := by
    have hcl : Subgroup.closure ({x, y} : Set G) ≤ P' := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hxP'
      · exact hyP'
    have h9 := Asc83Table.card_closure_pair_eq_nine hx3 hy3 (hab x hxP' y hyP') hx1 hyx
    have heq : Subgroup.closure ({x, y} : Set G) = P' :=
      Subgroup.eq_of_le_of_card_ge hcl (by rw [h9, hP'9])
    rw [← heq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxE
    · exact hyE
  refine ⟨E.map (MulAut.conj g).toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hEe, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE81
  · rw [← Item434AltPerm.map_conj_map_conj_inv P g]
    exact Subgroup.map_mono hP'E

theorem exists_e81_of_e9_ambient {W : Type*} [Group W] {J : Subgroup W} [Finite J]
    {Q : Subgroup W} (hQJ : Q ≤ J) (hQ : Nat.card Q = 3 ^ (Nat.card J).factorization 3)
    (hgood : ∀ x y : W, x ∈ Q → y ∈ Q → x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 →
      y ∉ Subgroup.zpowers x →
      ∃ E : Subgroup W, E ≤ J ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ x ∈ E ∧ y ∈ E)
    {P : Subgroup J} (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    ∃ E : Subgroup J, IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ P ≤ E := by
  refine exists_e81_of_e9 (Q := Q.subgroupOf J) ?_ ?_ hP hP9
  · rw [card_subgroupOf_of_le hQJ]
    exact hQ
  · intro x hxQ y hyQ hx3 hy3 hxy hx1 hyx
    have hx3' : (x : W) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    have hy3' : (y : W) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    have hxy' : (x : W) * y = y * x := congrArg Subtype.val hxy
    have hx1' : (x : W) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hyx' : (y : W) ∉ Subgroup.zpowers (x : W) := by
      rintro ⟨k, hk⟩
      exact hyx ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨E, hEJ, hEe, hE81, hxE, hyE⟩ :=
      hgood x y (Subgroup.mem_subgroupOf.mp hxQ) (Subgroup.mem_subgroupOf.mp hyQ) hx3' hy3' hxy'
        hx1' hyx'
    refine ⟨E.subgroupOf J, isElemAbelian_subgroupOf J hEe, ?_, Subgroup.mem_subgroupOf.mpr hxE,
      Subgroup.mem_subgroupOf.mpr hyE⟩
    rw [card_subgroupOf_of_le hEJ]
    exact hE81

end CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
