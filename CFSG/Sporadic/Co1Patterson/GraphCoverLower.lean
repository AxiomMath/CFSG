module

public import CFSG.Sporadic.Co1Patterson.GraphSuborbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

theorem ncard_filter_range (p : ℕ → Bool) (n : ℕ) :
    {i | i < n ∧ p i = true}.ncard = ((List.range n).filter p).length := by
  classical
  have hset : {i | i < n ∧ p i = true} = ↑(((List.range n).filter p).toFinset) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup ((List.nodup_range).filter _)]


@[expose] noncomputable def gensElt (L : List ℕ) (l : ℕ) : NativeSporadic.Co1 := gElt (L.getD l 0)

theorem gensArr_size (L : List ℕ) : (gensArr L).size = L.length := by
  simp [gensArr]

theorem gensArr_get (L : List ℕ) {l : ℕ} (hl : l < L.length) :
    (gensArr L)[l]! = gEl (L.getD l 0) := by
  rw [getElem!_pos (gensArr L) l (by rw [gensArr_size]; exact hl)]
  simp [gensArr, List.getElem?_eq_getElem hl]

theorem nrep_gensArr (hdag : dagOK = true) (L : List ℕ) {l : ℕ} (hl : l < (gensArr L).size) :
    NRep (gensArr L)[l]! (gensElt L l) := by
  rw [gensArr_size] at hl
  rw [gensArr_get L hl]
  exact nrep_gEl (dagOK_parts hdag).1 _

theorem mem_of_centOK {G : Array Native.Rows} {zR : Native.Rows} (h : centOK G zR = true)
    {k : ℕ → NativeSporadic.Co1} (hk : ∀ l < G.size, NRep G[l]! (k l))
    {z : NativeSporadic.Co1} (hz : NRep zR z) (l : ℕ) (hl : l < G.size) :
    k l ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ⊓
      centralizer ({z} : Set NativeSporadic.Co1) := by
  unfold centOK at h
  rw [Array.all_eq_true] at h
  have h' := h l hl
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  have hkl := hk l hl
  rw [getElem!_pos G l hl] at hkl
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
  · exact NRep.unique (nrep_aNC.mul hkl) (h'.1 ▸ hkl.mul nrep_aNC) |>.symm
  · exact NRep.unique (hz.mul hkl) (h'.2 ▸ hkl.mul hz) |>.symm

theorem fibre_le (hdag : dagOK = true) {gens : List ℕ} {zR root : Native.Rows} {n : ℕ}
    {T : Array ℕ × Array ℕ} (h : fibreOK gens zR root n T = true) {z : NativeSporadic.Co1} (hz : NRep zR z) {b : Vt}
    (hb : NRep root b) :
    n ≤ {v : Vt | ∃ g ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ⊓
      centralizer ({z} : Set NativeSporadic.Co1), v = g • b}.ncard := by
  unfold fibreOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hok⟩, hn⟩ := h
  rw [← hn]
  exact le_ncard_of_orbOK hok _ (gensElt gens) (fun l hl => nrep_gensArr hdag gens hl)
    (fun l hl => mem_of_centOK hc (fun l hl => nrep_gensArr hdag gens hl) hz l hl) b hb

theorem exists_point_of_exactOK {o : Orb} {X Xi : Native.Rows} {n : ℕ}
    (h : exactOK o (conjA X Xi) n = true) {x : NativeSporadic.Co1} (hX : NRep X x)
    (hXi : NRep Xi x⁻¹) {u : Vt} (hu : u ∈ cOrb (x • vA)) :
    ∃ i < o.c.pts.size, ∃ g : NativeSporadic.Co1, u = (g * x) • vA ∧ NRep o.hs[i]! g ∧
      NRep o.his[i]! g⁻¹ := by
  have hroot : NRep (conjA X Xi) ((x • vA : Vt) : NativeSporadic.Co1) := nrep_conjA hX hXi
  obtain ⟨i, hi, hiu⟩ := (mem_cOrb_iff_of_exactOK h (x • vA) hroot u).1 hu
  have hok : orbOK brayArr brayInvArr (conjA X Xi) o = true := by
    unfold exactOK at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨g, -, hg, hgi, hp⟩ := orbOK_sound matHom hok brayNC (fun l hl => nrep_brayArr l hl)
    _ hroot i hi
  refine ⟨i, hi, g, Subtype.ext ?_, hg, hgi⟩
  rw [NRep.unique hiu hp, mul_smul]
  rfl

theorem nrep_conjPt (o : Orb) {X Xi B : Native.Rows} {x g b : NativeSporadic.Co1}
    (hX : NRep X x) (hXi : NRep Xi x⁻¹) (i : ℕ) (hg : NRep o.hs[i]! g)
    (hgi : NRep o.his[i]! g⁻¹) (hb : NRep B b) :
    NRep (conjPt o X Xi i B) ((g * x)⁻¹ * b * (g * x)) := by
  unfold conjPt
  rw [mul_inv_rev]
  have := (((hXi.mul hgi).mul hb).mul (hg.mul hX))
  simpa [mul_assoc] using this

theorem ncard_rel_le_countN {o ot : Orb} {X Xi Rt B : Native.Rows} {n nt : ℕ}
    (h : exactOK o (conjA X Xi) n = true) (ht : exactOK ot Rt nt = true)
    (hv : conjValid o X Xi B = true) {x : NativeSporadic.Co1} (hX : NRep X x)
    (hXi : NRep Xi x⁻¹) {t b : Vt} (hRt : NRep Rt t) (hB : NRep B b) :
    {u | u ∈ cOrb (x • vA) ∧ orbRel t u b}.ncard ≤ countN o X Xi (ptSet ot) B := by
  have hok : orbOK brayArr brayInvArr (conjA X Xi) o = true := by
    unfold exactOK at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hokt : orbOK brayArr brayInvArr Rt ot = true := by
    unfold exactOK at ht
    simp only [Bool.and_eq_true] at ht
    exact ht.1.1
  have hroot : NRep (conjA X Xi) ((x • vA : Vt) : NativeSporadic.Co1) := nrep_conjA hX hXi
  have hsound := orbOK_sound matHom hok brayNC (fun l hl => nrep_brayArr l hl) _ hroot
  choose! g _ hg hgi _ using hsound
  let w : ℕ → Vt := fun i => (g i * x) • vA
  have hsub : {u | u ∈ cOrb (x • vA) ∧ orbRel t u b} ⊆
      w '' {i | i < o.c.pts.size ∧ (ptSet ot).contains (conjPt o X Xi i B) = true} := by
    rintro u ⟨hu, hR⟩
    obtain ⟨i, hi, g', rfl, hg', hgi'⟩ := exists_point_of_exactOK h hX hXi hu
    have hgg : g' = g i := NRep.unique hg' (hg i hi)
    subst hgg
    refine ⟨i, ⟨hi, ?_⟩, rfl⟩
    rw [orbRel_smul_iff_mem] at hR
    obtain ⟨j, hj, hjv⟩ := (mem_cOrb_iff_of_exactOK ht t hRt _).1 hR
    have hc := nrep_conjPt o hX hXi i hg' hgi' hB
    have hval : CFSG.Sporadic.Co1.InvNative.validRows (conjPt o X Xi i B) = true := by
      unfold conjValid at hv
      simp only [List.all_eq_true, List.mem_range] at hv
      exact hv i hi
    have hjval : CFSG.Sporadic.Co1.InvNative.validRows ot.c.pts[j]! = true :=
      ((orbOK_parts hokt).2.2.2.2.2.2.2.1 j hj).1
    refine ptSet_contains_iff.2 ⟨j, hj, NRep.rows_eq hjv ?_ hjval hval⟩
    simpa [coe_smul_conjVert, mul_assoc] using hc
  calc {u | u ∈ cOrb (x • vA) ∧ orbRel t u b}.ncard
      ≤ (w '' {i | i < o.c.pts.size ∧ (ptSet ot).contains (conjPt o X Xi i B) = true}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {i | i < o.c.pts.size ∧ (ptSet ot).contains (conjPt o X Xi i B) = true}.ncard :=
        Set.ncard_image_le ((Set.finite_lt_nat o.c.pts.size).subset fun i hi => hi.1)
    _ = countN o X Xi (ptSet ot) B := ncard_filter_range _ _

end CFSG.Sporadic.Co1Patterson
