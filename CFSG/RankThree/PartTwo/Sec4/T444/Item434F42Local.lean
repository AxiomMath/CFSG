module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Enum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434F42

open CFSG.Assembly (IsElemAbelian)
open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes codeBits)

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {k : ℕ} (hk : k < A.size) : (A.map f)[k]! = f A[k]! := by
  rw [getElem!_pos (A.map f) k (by simpa using hk), getElem!_pos A k hk]
  simp

theorem getElem!_mem_toList {α : Type*} [Inhabited α] (A : Array α) {k : ℕ} (hk : k < A.size) :
    A[k]! ∈ A.toList := by
  rw [getElem!_pos A k hk]
  exact Array.getElem_mem_toList hk

theorem distinctB_spec : ∀ l : List ℕ, distinctB l = true →
    l.Pairwise fun a b => eqB a b = false
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [distinctB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    exact List.Pairwise.cons h.1 (distinctB_spec l (by simpa [distinctB] using h.2))

theorem bothAny_spec {la lb : List Bool} (h : bothAny la lb = true) :
    ∃ i : ℕ, la[i]? = some true ∧ lb[i]? = some true := by
  simp only [bothAny, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨p, hp, h1, h2⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
  rw [List.getElem?_zip_eq_some] at hi
  refine ⟨i, ?_, ?_⟩
  · rw [hi.1, h1]
  · rw [hi.2, h2]

theorem enumOK_letters {gb : Array ℕ} {L : List (List ℕ)} {vals : List ℕ}
    (h : enumOK gb L vals = true) : ∀ w ∈ L, ∀ l ∈ w, l < gb.size := by
  simp only [enumOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

section Bits

noncomputable def jGen (K : Type) [Field K]
    (D : F42Data) (l : ℕ) : adjointGroup ReeTag.F4.tag K :=
  evalG K (wordOfCodes D.gW[l]!)

noncomputable def qGen (K : Type) [Field K]
    (D : F42Data) (k : ℕ) : adjointGroup ReeTag.F4.tag K :=
  wordElt (jGen K D) D.qW[k]!

noncomputable def dGen (K : Type) [Field K]
    (D : F42Data) (k : ℕ) : adjointGroup ReeTag.F4.tag K :=
  wordElt (qGen K D) D.dW[k]!

variable {K : Type} [Field K]

theorem hasBits_wordElt [CharP K 2]
    {g : ℕ → adjointGroup ReeTag.F4.tag K} {gb : Array ℕ}
    (hg : ∀ l < gb.size, HasBits K (g l) gb[l]!) (w : List ℕ) (hw : ∀ l ∈ w, l < gb.size) :
    HasBits K (wordElt g w) (wordB gb w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, l < gb.size) → ∀ (acc : ℕ)
      (a : adjointGroup ReeTag.F4.tag K), HasBits K a acc →
      HasBits K (a * wordElt g w) (w.foldl (fun acc l => mul acc gb[l]!) acc) := by
    intro w
    induction w with
    | nil => intro _ acc a h; simpa using h
    | cons l w ih =>
      intro hw acc a h
      rw [List.foldl_cons, wordElt_cons, ← mul_assoc]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
        (h.mul (hg l (hw l (List.mem_cons_self ..))))
  have := key w hw oneBits 1 hasBits_one
  rwa [one_mul] at this

theorem eqB_iff
    {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBits K g A)
    (hh : HasBits K h B) : eqB A B = true ↔ g = h := by
  rw [eqB, beq_iff_eq]
  exact (hg.eq_iff hh).symm

theorem enum_sound [CharP K 2]
    [Finite (adjointGroup ReeTag.F4.tag K)] {g : ℕ → adjointGroup ReeTag.F4.tag K}
    {gb : Array ℕ} (hg : ∀ l < gb.size, HasBits K (g l) gb[l]!) {L : List (List ℕ)}
    (h : enumOK gb L (L.map (wordB gb)) = true) :
    (∀ x, x ∈ Subgroup.closure (g '' {k | k < gb.size}) ↔ ∃ w ∈ L, wordElt g w = x) ∧
      Nat.card (Subgroup.closure (g '' {k | k < gb.size})) = L.length := by
  simp only [enumOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.any_eq_true, and_assoc] at h
  obtain ⟨hL, h1, hcl, hnd⟩ := h
  have hL' : ∀ w ∈ L, ∀ l ∈ w, l < gb.size := hL
  have hbits : ∀ w ∈ L, HasBits K (wordElt g w) (wordB gb w) := fun w hw =>
    hasBits_wordElt hg w (hL' w hw)
  refine enum_spec hL' h1 ?_ ?_
  · intro w hw k hk
    obtain ⟨x, hx, hxe⟩ := hcl _ (List.mem_map_of_mem hw) k hk
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hx
    refine ⟨w', hw', ?_⟩
    exact ((eqB_iff ((hbits w hw).mul (hg k hk)) (hbits w' hw')).1 hxe).symm
  · have hp := distinctB_spec _ hnd
    rw [List.pairwise_map] at hp
    rw [List.Nodup, List.pairwise_map]
    refine hp.imp_of_mem fun {a b} ha hb hab hE => ?_
    have := (eqB_iff (hbits a ha) (hbits b hb)).2 hE
    rw [hab] at this
    exact Bool.false_ne_true this

theorem elemAbOK_sound [CharP K 2]
    {dg : ℕ → adjointGroup ReeTag.F4.tag K} {dgb : Array ℕ}
    (hg : ∀ k < dgb.size, HasBits K (dg k) dgb[k]!) (h : elemAbOK dgb = true) :
    ∀ k < dgb.size, dg k ^ 3 = 1 ∧ ∀ k' < dgb.size, dg k * dg k' = dg k' * dg k := by
  simp only [elemAbOK, List.all_eq_true, Bool.and_eq_true, List.mem_range] at h
  intro k hk
  obtain ⟨h3, hc⟩ := h k hk
  refine ⟨?_, fun k' hk' => ?_⟩
  · rw [pow_three]
    exact (eqB_iff ((hg k hk).mul ((hg k hk).mul (hg k hk))) hasBits_one).1 h3
  · exact (eqB_iff ((hg k hk).mul (hg k' hk')) ((hg k' hk').mul (hg k hk))).1 (hc k' hk')

theorem f42_sound [CharP K 2]
    [Finite (adjointGroup ReeTag.F4.tag K)] (D : F42Data) (h : f42Check D = true) :
    ∃ Q : Subgroup (adjointGroup ReeTag.F4.tag K), Nat.card Q = D.qOrd ∧
      ∀ x y : adjointGroup ReeTag.F4.tag K, x ∈ Q → y ∈ Q → x ^ 3 = 1 → y ^ 3 = 1 →
        x * y = y * x → x ≠ 1 → y ∉ Subgroup.zpowers x →
        ∃ E : Subgroup (adjointGroup ReeTag.F4.tag K),
          IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ x ∈ E ∧ y ∈ E := by
  unfold f42Check f42Check' at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hinv, hqW, hhW, hdW, hQenum, hQcard, hDenum, hD81, hDab, hpairs⟩ := h
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_range] at hinv hqW hhW hdW hQcard hD81
  have hgb : ∀ l < (gB D).size, HasBits K (jGen K D l) (gB D)[l]! := by
    intro l hl
    have hl' : l < D.gW.size := by simpa [gB] using hl
    rw [gB, getElem!_map' D.gW codeBits hl']
    exact hasBits_evalG (wordOfCodes D.gW[l]!)
  have hgg : ∀ l < (gB D).size, jGen K D l * jGen K D l = 1 := fun l hl =>
    (eqB_iff ((hgb l hl).mul (hgb l hl)) hasBits_one).1 (hinv l hl)
  have hqb : ∀ k < (qgB D).size, HasBits K (qGen K D k) (qgB D)[k]! := by
    intro k hk
    have hk' : k < D.qW.size := by simpa [qgB] using hk
    rw [qgB, getElem!_map' D.qW (wordB (gB D)) hk']
    exact hasBits_wordElt hgb D.qW[k]! (hqW _ (getElem!_mem_toList D.qW hk'))
  have hdb : ∀ k < (dgB D).size, HasBits K (dGen K D k) (dgB D)[k]! := by
    intro k hk
    have hk' : k < D.dW.size := by simpa [dgB] using hk
    rw [dgB, getElem!_map' D.dW (wordB (qgB D)) hk']
    exact hasBits_wordElt hqb D.dW[k]! (hdW _ (getElem!_mem_toList D.dW hk'))
  obtain ⟨hQmem, hQc⟩ := enum_sound hqb
    (show enumOK (qgB D) (qL D) ((qL D).map (wordB (qgB D))) = true from hQenum)
  obtain ⟨hDmem, hDc⟩ := enum_sound hdb
    (show enumOK (dgB D) (dL D) ((dL D).map (wordB (dgB D))) = true from hDenum)
  have hqL := enumOK_letters hQenum
  set Dsub := Subgroup.closure (dGen K D '' {k | k < (dgB D).size}) with hDsub
  have hDe : IsElemAbelian 3 Dsub := by
    have hab := elemAbOK_sound hdb hDab
    refine isElemAbelian_closure ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
      exact (hab k hk).2 k' hk'
    · rintro _ ⟨k, hk, rfl⟩
      exact (hab k hk).1
  have hD81' : 81 ≤ Nat.card Dsub := by rw [hDc]; exact hD81
  refine ⟨Subgroup.closure (qGen K D '' {k | k < (qgB D).size}), by rw [hQc]; exact hQcard, ?_⟩
  intro x y hxQ hyQ hx3 hy3 hxy hx1 hyx
  obtain ⟨wa, hwa, rfl⟩ := (hQmem x).1 hxQ
  obtain ⟨wb, hwb, rfl⟩ := (hQmem y).1 hyQ
  have hbx := hasBits_wordElt hqb wa (hqL wa hwa)
  have hby := hasBits_wordElt hqb wb (hqL wb hwb)
  have hamem : elemInfo (dV D) (hps D) (wordB (qgB D) wa) ∈ (qV D).map (elemInfo (dV D) (hps D)) :=
    List.mem_map_of_mem (List.mem_map_of_mem hwa)
  have hbmem : elemInfo (dV D) (hps D) (wordB (qgB D) wb) ∈ (qV D).map (elemInfo (dV D) (hps D)) :=
    List.mem_map_of_mem (List.mem_map_of_mem hwb)
  have hp := List.all_eq_true.1 (List.all_eq_true.1 hpairs _ hamem) _ hbmem
  simp only [pairOK, elemInfo, Bool.or_eq_true, Bool.not_eq_true'] at hp
  have hx3' : eqB (mul (wordB (qgB D) wa) (mul (wordB (qgB D) wa) (wordB (qgB D) wa))) oneBits
      = true :=
    (eqB_iff (hbx.mul (hbx.mul hbx)) hasBits_one).2 (by rw [← pow_three]; exact hx3)
  have hy3' : eqB (mul (wordB (qgB D) wb) (mul (wordB (qgB D) wb) (wordB (qgB D) wb))) oneBits
      = true :=
    (eqB_iff (hby.mul (hby.mul hby)) hasBits_one).2 (by rw [← pow_three]; exact hy3)
  rcases hp with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8
  · exact absurd hx3' (by simp [h1])
  · exact absurd hy3' (by simp [h2])
  · exact absurd ((eqB_iff hbx hasBits_one).1 h3) hx1
  · exact absurd (by rw [(eqB_iff hby hasBits_one).1 h4]; exact Subgroup.one_mem _) hyx
  · exact absurd (by rw [(eqB_iff hby hbx).1 h5]; exact Subgroup.mem_zpowers _) hyx
  · exact absurd ((eqB_iff (hbx.mul hby) (hby.mul hbx)).2 hxy) (by simp [h6])
  · exact absurd (by
      rw [(eqB_iff hby (hbx.mul hbx)).1 h7]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)) hyx
  ·
    obtain ⟨i, hia, hib⟩ := bothAny_spec h8
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hia hib
    obtain ⟨p, hp1, hpa⟩ := hia
    obtain ⟨p', hp2, hpb⟩ := hib
    rw [hp1, Option.some.injEq] at hp2
    subst hp2
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hp1)
    have hwl : ∀ l ∈ w, l < (gB D).size := hhW w hw
    have hhb := hasBits_wordElt hgb w hwl
    have hib' := hasBits_wordElt hgb w.reverse (fun l hl => hwl l (List.mem_reverse.1 hl))
    have hhinv : (wordElt (jGen K D) w)⁻¹ = wordElt (jGen K D) w.reverse :=
      wordElt_reverse hgg w hwl
    obtain ⟨da, hda, hdae⟩ := List.any_eq_true.1 hpa
    obtain ⟨db, hdb', hdbe⟩ := List.any_eq_true.1 hpb
    obtain ⟨wda, hwda, rfl⟩ := List.mem_map.1 hda
    obtain ⟨wdb, hwdb, rfl⟩ := List.mem_map.1 hdb'
    have hlda := enumOK_letters hDenum
    have hzda := hasBits_wordElt hdb wda (hlda wda hwda)
    have hzdb := hasBits_wordElt hdb wdb (hlda wdb hwdb)
    have hxD : wordElt (jGen K D) w * wordElt (qGen K D) wa * (wordElt (jGen K D) w)⁻¹ ∈ Dsub := by
      rw [hhinv]
      have := (eqB_iff ((hhb.mul hbx).mul hib') hzda).1 hdae
      rw [this]
      exact (hDmem _).2 ⟨wda, hwda, rfl⟩
    have hyD : wordElt (jGen K D) w * wordElt (qGen K D) wb * (wordElt (jGen K D) w)⁻¹ ∈ Dsub := by
      rw [hhinv]
      have := (eqB_iff ((hhb.mul hby).mul hib') hzdb).1 hdbe
      rw [this]
      exact (hDmem _).2 ⟨wdb, hwdb, rfl⟩
    have hmemE : ∀ z, wordElt (jGen K D) w * z * (wordElt (jGen K D) w)⁻¹ ∈ Dsub →
        z ∈ Dsub.map (MulAut.conj (wordElt (jGen K D) w)⁻¹).toMonoidHom := fun z hz =>
      ⟨_, hz, by simp [mul_assoc]⟩
    refine ⟨Dsub.map (MulAut.conj (wordElt (jGen K D) w)⁻¹).toMonoidHom,
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ Dsub hDe, ?_, hmemE _ hxD,
      hmemE _ hyD⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hD81'

end Bits

end CFSG.RankThree.PartTwo.Sec4.Item434F42
