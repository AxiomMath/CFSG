module

public import CFSG.Quasithin.Recognition.SzVBA5Loc
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Perm

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Pair

variable {H : Type*} [Group H] {z : H}

theorem pair_mul_of_sq (hzz : z * z = 1) {a b : H} (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) :
    a * b = 1 ∨ a * b = z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, hzz]

theorem pair_inv_of_sq (hzz : z * z = 1) {a : H} (ha : a = 1 ∨ a = z) :
    a⁻¹ = 1 ∨ a⁻¹ = z := by
  rcases ha with ha | ha
  · simp [ha]
  · exact Or.inr (by rw [ha]; exact inv_eq_of_mul_eq_one_right hzz)

theorem not_mem_pair_mul {p e : H} (hzz : z * z = 1) (hp1 : p ≠ 1) (hpz : p ≠ z)
    (he : e = 1 ∨ e = z) : p * e ≠ 1 ∧ p * e ≠ z := by
  have hp : p = p * e * e⁻¹ := (mul_inv_cancel_right p e).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases pair_mul_of_sq hzz (Or.inl h) (pair_inv_of_sq hzz he) with h' | h'
    · exact hp1 (hp.trans h')
    · exact hpz (hp.trans h')
  · rcases pair_mul_of_sq hzz (Or.inr h) (pair_inv_of_sq hzz he) with h' | h'
    · exact hp1 (hp.trans h')
    · exact hpz (hp.trans h')

theorem inv_mul_mem_pair_of_mem_four {x u v : H} (hzz : z * z = 1)
    (hu : u ∈ ({1, x, z, x * z} : Set H)) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hv : v ∈ ({1, x, z, x * z} : Set H)) (hv1 : v ≠ 1) (hvz : v ≠ z) :
    u⁻¹ * v = 1 ∨ u⁻¹ * v = z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with hu | hu | hu | hu
  · exact absurd hu hu1
  · rcases hv with hv | hv | hv | hv
    · exact absurd hv hv1
    · exact Or.inl (by rw [hu, hv, inv_mul_cancel])
    · exact absurd hv hvz
    · exact Or.inr (by rw [hu, hv, inv_mul_cancel_left])
  · exact absurd hu huz
  · rcases hv with hv | hv | hv | hv
    · exact absurd hv hv1
    · exact Or.inr (by rw [hu, hv, mul_inv_rev, inv_mul_cancel_right, hzi])
    · exact absurd hv hvz
    · exact Or.inl (by rw [hu, hv, inv_mul_cancel])

end Pair

section Algebra

variable {A : Type*} [CommGroup A] {z ta tya tb tyb ea eb : A}

theorem four_mem_pair_comm (hzz : z * z = 1) (hta : ta * ta = 1) (htya : tya * tya = 1)
    (hea : ea = 1 ∨ ea = z) (heb : eb = 1 ∨ eb = z)
    (h : (tya * ta * ea)⁻¹ * (tyb * tb * eb) = 1 ∨ (tya * ta * ea)⁻¹ * (tyb * tb * eb) = z) :
    ta * tya * tb * tyb = 1 ∨ ta * tya * tb * tyb = z := by
  have hsq : ∀ e : A, (e = 1 ∨ e = z) → e * e = 1 := fun e he => by
    rcases he with he | he
    · rw [he, mul_one]
    · rw [he]
      exact hzz
  have hea2 := hsq ea hea
  have heb2 := hsq eb heb
  have hinv : (tya * ta * ea)⁻¹ = tya * ta * ea := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc tya * ta * ea * (tya * ta * ea) = (tya * tya) * (ta * ta) * (ea * ea) := by ac_rfl
      _ = 1 := by rw [htya, hta, hea2]; simp
  have e : (tya * ta * ea)⁻¹ * (tyb * tb * eb) * (ea * eb) = ta * tya * tb * tyb :=
    calc (tya * ta * ea)⁻¹ * (tyb * tb * eb) * (ea * eb)
        = ta * tya * tb * tyb * ((ea * ea) * (eb * eb)) := by rw [hinv]; ac_rfl
      _ = ta * tya * tb * tyb := by rw [hea2, heb2]; simp
  rw [← e]
  exact pair_mul_of_sq hzz h (pair_mul_of_sq hzz hea heb)

end Algebra

section Elementary

variable {G : Type*} [Group G]

theorem four_mem_pair {W : Subgroup G} (hW : IsElemAbelian 2 W)
    {z ta tya tb tyb ea eb : G} (hz : z ∈ W) (hta : ta ∈ W) (htya : tya ∈ W) (htb : tb ∈ W)
    (htyb : tyb ∈ W) (hzz : z * z = 1) (hta2 : ta * ta = 1) (htya2 : tya * tya = 1)
    (hea : ea = 1 ∨ ea = z) (heb : eb = 1 ∨ eb = z)
    (h : (tya * ta * ea)⁻¹ * (tyb * tb * eb) = 1 ∨ (tya * ta * ea)⁻¹ * (tyb * tb * eb) = z) :
    ta * tya * tb * tyb = 1 ∨ ta * tya * tb * tyb = z := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  have hmemE : ∀ e : G, (e = 1 ∨ e = z) → e ∈ W := fun e he => by
    rcases he with he | he
    · rw [he]
      exact W.one_mem
    · rw [he]
      exact hz
  have key := four_mem_pair_comm (A := ↥W) (z := ⟨z, hz⟩) (ta := ⟨ta, hta⟩)
    (tya := ⟨tya, htya⟩) (tb := ⟨tb, htb⟩) (tyb := ⟨tyb, htyb⟩) (ea := ⟨ea, hmemE ea hea⟩)
    (eb := ⟨eb, hmemE eb heb⟩) (Subtype.ext hzz) (Subtype.ext hta2) (Subtype.ext htya2)
    (by
      rcases hea with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext he))
    (by
      rcases heb with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext he))
    (by
      rcases h with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h))
  rcases key with k | k
  · exact Or.inl (congrArg Subtype.val k)
  · exact Or.inr (congrArg Subtype.val k)

end Elementary

variable {G : Type} [Group G] [Finite G] {P T V : Subgroup G} {z : G}

theorem four_ne_of_tDataG {W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hPN : P ≤ Subgroup.normalizer (W : Set G)) {t : ConjSet P V → G} (ht : TDataG P W t z)
    (hl : L24Facts P T V) (p1 p2 p3 p4 : ConjSet P V) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3)
    (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4) :
    t p1 * t p2 * t p3 * t p4 ≠ 1 ∧ t p1 * t p2 * t p3 * t p4 ≠ z := by
  classical
  have : Fintype (ConjSet P V) := Fintype.ofFinite _
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  have hmul : ∀ a b : ↥W, ((a * b : ↥W) : G) = (a : G) * (b : G) := fun a b => rfl
  have honeW : ((1 : ↥W) : G) = 1 := rfl
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥P →* MulAut ↥W,
      ∀ (x : ↥P) (a : ↥W), ((ρ x a : ↥W) : G) = x * a * (x : G)⁻¹ :=
    ⟨(conjAct W).comp (Subgroup.inclusion hPN),
      fun x a => OddAux.conjAct_coe W (Subgroup.inclusion hPN x) a⟩
  obtain ⟨tW, htW⟩ : ∃ tW : ConjSet P V → ↥W, ∀ a, ((tW a : ↥W) : G) = t a :=
    ⟨fun a => ⟨t a, ht.t_mem a⟩, fun a => rfl⟩
  obtain ⟨zW, hzW⟩ : ∃ zW : ↥W, (zW : G) = z := ⟨⟨z, ht.z_mem⟩, rfl⟩
  have hT : TData ρ tW zW := by
    refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, fun h => ht.z_ne_one ?_,
      fun x => Subtype.ext ?_, fun x a => ?_, fun a b hab => ?_⟩
    · rw [hmul, htW, honeW]
      exact ht.t_sq a
    · rw [hmul, hzW, honeW]
      exact ht.z_sq
    · rw [← hzW, h, honeW]
    · rw [hρ, hzW]
      calc (x : G) * z * (x : G)⁻¹ = z * x * (x : G)⁻¹ := by rw [ht.z_cent x x.2]
        _ = z := mul_inv_cancel_right _ _
    · rcases ht.act x a with h | h
      · refine Or.inl (Subtype.ext ?_)
        rw [hρ, htW, htW]
        exact h
      · refine Or.inr (Subtype.ext ?_)
        rw [hρ, hmul, htW, htW, hzW]
        exact h
    · refine ⟨fun h => (ht.distinct a b hab).1 ?_, fun h => (ht.distinct a b hab).2 ?_⟩
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, honeW] at this
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, hzW] at this
  have hcard : Fintype.card (ConjSet P V) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact hl.card_five
  have hΩodd : Odd (Fintype.card (ConjSet P V)) := by
    rw [hcard]
    decide
  have hker : KerProp tW zW := by
    refine kerProp_of_tData hT (OddAux.conjSet_isPretransitive P V) (T.subgroupOf P)
      (hl.S_pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hl.S_le).symm) (ConjSet.base P V)
      ?_ ?_ hΩodd
    · intro r hr
      exact Subtype.ext
        (OddAux.conjSub_eq_of_mem_normalizer'
          (hl.S_le_normalizer (Subgroup.mem_subgroupOf.mp hr)))
    · intro a b ha hb
      obtain ⟨s, hs, h⟩ := hl.S_transitive a b ha hb
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, h⟩
  have key : ¬ ((tW p1 * tW p2 * tW p3 * tW p4 = 1) ∨ (tW p1 * tW p2 * tW p3 * tW p4 = zW)) := by
    intro hc
    have hn1 : p1 ∉ ({p2, p3, p4} : Finset (ConjSet P V)) := by simp [h12, h13, h14]
    have hn2 : p2 ∉ ({p3, p4} : Finset (ConjSet P V)) := by simp [h23, h24]
    have hn3 : p3 ∉ ({p4} : Finset (ConjSet P V)) := by simp [h34]
    have hprod : (∏ a ∈ ({p1, p2, p3, p4} : Finset (ConjSet P V)), tW a) =
        tW p1 * tW p2 * tW p3 * tW p4 := by
      rw [Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_insert hn3,
        Finset.prod_singleton]
      simp only [mul_assoc]
    rcases hker {p1, p2, p3, p4} (by rw [hprod]; exact hc) with hI | hI
    · exact Finset.insert_ne_empty _ _ hI
    · have hc4 := Finset.card_le_four (a := p1) (b := p2) (c := p3) (d := p4)
      rw [hI, Finset.card_univ] at hc4
      omega
  refine ⟨fun h => key (Or.inl ?_), fun h => key (Or.inr ?_)⟩
  · apply Subtype.ext
    simp only [hmul, htW, honeW]
    exact h
  · apply Subtype.ext
    simp only [hmul, htW, hzW]
    exact h

theorem exists_tDataG_four (F : A5Facts P T V z) : ∃ t : ConjSet P V → G,
    TDataG P (conjClosure V P) t z ∧ (∀ U, t U ∈ U.1 ∧ t U ≠ 1 ∧ t U ≠ z) ∧
    ∀ p1 p2 p3 p4 : ConjSet P V, p1 ≠ p2 → p1 ≠ p3 → p1 ≠ p4 → p2 ≠ p3 → p2 ≠ p4 → p3 ≠ p4 →
      t p1 * t p2 * t p3 * t p4 ≠ 1 ∧ t p1 * t p2 * t p3 * t p4 ≠ z := by
  obtain ⟨t, ht, htmem⟩ := exists_tDataG_mem F.klein
  exact ⟨t, ht, htmem, fun p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 =>
    four_ne_of_tDataG F.abel (le_normalizer_conjClosure V P) ht F.l24 p1 p2 p3 p4 h12 h13 h14
      h23 h24 h34⟩

theorem exists_comm_not_mem (F : A5Facts P T V z) {w : G} (hw : w ∈ P) (hw2 : w * w = 1)
    (hwQ : w ∉ pCoreOf 2 P) (x : G) :
    ∃ a ∈ conjClosure V P, w * a * w⁻¹ * a⁻¹ ∉ ({1, x, z, x * z} : Set G) := by
  obtain ⟨t, ht, -, h4⟩ := exists_tDataG_four F
  set y : ↥P := ⟨w, hw⟩
  have hyy : y * y = 1 := Subtype.ext hw2
  have hy : y ∉ kerAct P V := fun h => hwQ (F.ker_le y h)
  obtain ⟨ω, hω, hu⟩ := F.inv_one_fixed y hyy hy
  obtain ⟨a, b, ha, hb, hba, hbma⟩ :=
    CFSG.Quasithin.Kleidman.VBOdd.perm_two_cycles_of_one_fixed F.l24.card_five
      (MulAction.toPermHom ↥P (ConjSet P V) y) (by rw [← map_mul, hyy, map_one])
      ⟨ω, hω, fun U hU => hu U hU⟩
  have hya : y • a ≠ a := ha
  have hyb : y • b ≠ b := hb
  have hbya : b ≠ y • a := hbma
  have hyyb : y • y • b = b := by rw [← mul_smul, hyy, one_smul]
  have hay : a ≠ y • b := fun h => hbya (hyyb.symm.trans (congrArg (fun u => y • u) h.symm))
  have hyayb : y • a ≠ y • b := fun h => hba (MulAction.injective y h).symm
  obtain ⟨h4a, h4b⟩ := h4 a (y • a) b (y • b) hya.symm hba.symm hay hbya.symm hyayb hyb.symm
  have hzz : z * z = 1 := ht.z_sq
  have htt : ∀ c, t c * t c = 1 := ht.t_sq
  have hact : ∀ c : ConjSet P V, w * t c * w⁻¹ = t (y • c) ∨ w * t c * w⁻¹ = t (y • c) * z :=
    fun c => ht.act y c
  have hcommz : ∀ c, z * t c = t c * z := fun c =>
    F7.isElemAbelian_comm F.abel ht.z_mem (ht.t_mem c)
  have hcomm_aux : ∀ c : ConjSet P V, ∃ e : G, (e = 1 ∨ e = z) ∧
      w * t c * w⁻¹ * (t c)⁻¹ = t (y • c) * t c * e := by
    intro c
    have hinv : (t c)⁻¹ = t c := inv_eq_of_mul_eq_one_right (htt c)
    rcases hact c with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, hinv, mul_one]⟩
    · refine ⟨z, Or.inr rfl, ?_⟩
      rw [h, hinv]
      calc t (y • c) * z * t c = t (y • c) * (z * t c) := mul_assoc _ _ _
        _ = t (y • c) * (t c * z) := by rw [hcommz c]
        _ = t (y • c) * t c * z := (mul_assoc _ _ _).symm
  obtain ⟨ea, hea, hua⟩ := hcomm_aux a
  obtain ⟨eb, heb, hub⟩ := hcomm_aux b
  by_contra hcon
  have hmemS : ∀ c ∈ conjClosure V P, w * c * w⁻¹ * c⁻¹ ∈ ({1, x, z, x * z} : Set G) :=
    fun c hc => by
      by_contra hnot
      exact hcon ⟨c, hc, hnot⟩
  have hSa : t (y • a) * t a * ea ∈ ({1, x, z, x * z} : Set G) := by
    rw [← hua]
    exact hmemS _ (ht.t_mem a)
  have hSb : t (y • b) * t b * eb ∈ ({1, x, z, x * z} : Set G) := by
    rw [← hub]
    exact hmemS _ (ht.t_mem b)
  have hda := ht.distinct (y • a) a hya
  have hdb := ht.distinct (y • b) b hyb
  have hnA := not_mem_pair_mul hzz hda.1 hda.2 hea
  have hnB := not_mem_pair_mul hzz hdb.1 hdb.2 heb
  have hpair := inv_mul_mem_pair_of_mem_four hzz hSa hnA.1 hnA.2 hSb hnB.1 hnB.2
  rcases four_mem_pair F.abel ht.z_mem (ht.t_mem a) (ht.t_mem (y • a)) (ht.t_mem b)
      (ht.t_mem (y • b)) hzz (htt a) (htt (y • a)) hea heb hpair with h | h
  · exact h4a h
  · exact h4b h

end CFSG.Quasithin.SzVB
