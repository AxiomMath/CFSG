module

public import CFSG.Quasithin.H13.L32NMatNGen
public import Certificates.Certificate7189

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert L1442M

theorem m22Check_eq : m22Check = true :=
  Certificates.certificate7189

theorem m22Check_parts :
    gG.all (validB 12) = true ∧ orbB = true ∧ s0B = true ∧ schB = true ∧ pB = true ∧
      e0B = true ∧ witB = true ∧ ovB = true ∧ oB = true ∧ m12B = true := by
  have h := m22Check_eq
  simp only [m22Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem gG_cols : gG = [colsN (m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)),
    colsN (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2))] := by
  decide +kernel

theorem validN_gG : ∀ g ∈ gG, ValidN 12 g := by
  rw [gG_cols]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact validN_colsN _

@[expose] def gU (i : ℕ) : GL (Fin 12) (ZMod 2) :=
  if i = 0 then m22a else if i = 1 then m22b else 1

@[expose] def tU (w : List ℕ) : GL (Fin 12) (ZMod 2) := (w.map gU).prod

theorem gU_val (i : ℕ) : ((gU i : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
    decN 12 (gG.getD i one12) := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i <;> rw [gG_cols] <;> simp [gU, decN_colsN]
  · rw [List.getD_eq_default _ _ (by simp [gG]; omega), decN_oneN]
    simp [gU, show i ≠ 0 by omega, show i ≠ 1 by omega]

theorem tU_cons (i : ℕ) (w : List ℕ) : tU (i :: w) = gU i * tU w := by
  simp only [tU, List.map_cons, List.prod_cons]

theorem tU_val (w : List ℕ) :
    ((tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 (tW w) := by
  induction w with
  | nil =>
    simp only [tU, List.map_nil, List.prod_nil, Units.val_one]
    exact decN_oneN.symm
  | cons i w ih =>
    rw [tU_cons, Units.val_mul, ih, gU_val]
    show _ = decN 12 (evalW 12 gG (i :: w))
    rw [evalW_cons, decN_mulN (validN_getD validN_gG i).1 (length_evalW gG w)]

theorem gU_mem (i : ℕ) : gU i ∈ m22 := by
  unfold gU
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact one_mem _

theorem tU_mem (w : List ℕ) : tU w ∈ m22 := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    rw [tU_cons]
    exact mul_mem (gU_mem i) ih

theorem orbB_spec :
    orbL.head? = some (v0, []) ∧ orbL.length = 693 ∧ (orbL.map Prod.fst).Nodup ∧
      ∀ uw ∈ orbL, mvN (tW uw.2) v0 = uw.1 := by
  have h := m22Check_parts.2.1
  simp only [orbB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  have h5 : ((orbL.map Prod.fst).mergeSort).Nodup :=
    (List.isChain_iff_pairwise.mp h3).imp (fun hab => ne_of_lt hab)
  exact (List.mergeSort_perm _ _).nodup_iff.mp h5

theorem v0_mem : (v0, ([] : List ℕ)) ∈ orbL :=
  List.mem_of_mem_head? (by rw [orbB_spec.1]; rfl)

theorem orbL_lt {uw : ℕ × List ℕ} (huw : uw ∈ orbL) :
    uw.1 < 2 ^ 12 := by
  rw [← orbB_spec.2.2.2 uw huw]
  exact mvN_lt (validN_evalW gG validN_gG _).2 _

theorem orbL_ext {uw uw' : ℕ × List ℕ} (huw : uw ∈ orbL)
    (huw' : uw' ∈ orbL) (h : uw.1 = uw'.1) : uw = uw' :=
  List.inj_on_of_nodup_map orbB_spec.2.2.1 huw huw' h

theorem schB_spec :
    ∀ uw ∈ orbL, ∀ g ∈ gG, ∃ uw' ∈ orbL, uw'.1 = mvN g uw.1 ∧
      ∃ s ∈ s0E, mulN (tW uw'.2) s = mulN g (tW uw.2) := by
  have h := m22Check_parts.2.2.2.1
  simp only [schB, List.all_eq_true] at h
  intro uw huw g hg
  have h1 := h uw huw g hg
  cases hf : orbL.find? (fun p => p.1 == mvN g uw.1) with
  | none =>
    rw [hf] at h1
    exact absurd h1 Bool.false_ne_true
  | some uw' =>
    rw [hf] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, Std.HashSet.contains_ofList,
      List.contains_iff_mem] at h1
    refine ⟨uw', List.mem_of_find?_eq_some hf, ?_, _, h1.1, h1.2⟩
    have := List.find?_some hf
    simpa using this

@[expose] def S0 : Subgroup (GL (Fin 12) (ZMod 2)) := genSubN 12 s0G

theorem s0B_spec :
    subB 12 s0G s0E = true ∧ s0E.length = 3840 ∧ ∀ s ∈ s0E, mvN s v0 = v0 := by
  have h := m22Check_parts.2.2.1
  simp only [s0B, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem s0G_unit : ∀ g ∈ s0G, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨tU w, tU_val w⟩

theorem mem_S0_iff (u : GL (Fin 12) (ZMod 2)) :
    u ∈ S0 ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ s0E :=
  mem_genSubN_iff_of s0B_spec.1 s0G_unit u

theorem card_S0 : Nat.card S0 = 3840 := by
  rw [S0, card_genSubN_of s0B_spec.1 s0G_unit]
  exact s0B_spec.2.1

theorem exists_mem_S0 {c : List ℕ} (hc : c ∈ s0E) :
    ∃ u ∈ S0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 c :=
  exists_mem_of_elemsOf s0B_spec.1 s0G_unit hc

theorem S0_le : S0 ≤ m22 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨w, -, hw⟩ := List.mem_map.mp (show colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈
    s0G from hu)
  have : u = tU w := by
    apply Units.ext
    rw [tU_val, hw, decN_colsN]
  rw [this]
  exact tU_mem w

theorem S0_fix {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    (s : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0 := by
  rw [mulVec_vecN, s0B_spec.2.2 _ ((mem_S0_iff s).mp hs)]

theorem tU_mulVec {uw : ℕ × List ℕ} (huw : uw ∈ orbL) :
    ((tU uw.2 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = vecN 12 uw.1 := by
  rw [tU_val, decN_mulVec (length_evalW gG _), orbB_spec.2.2.2 uw huw]

theorem decomp {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ m22) :
    ∃ uw ∈ orbL, ∃ s ∈ S0, x = tU uw.2 * s := by
  have hstep : ∀ i < 2, ∀ y : GL (Fin 12) (ZMod 2), (∃ uw ∈ orbL, ∃ s ∈ S0, y = tU uw.2 * s) →
      ∃ uw ∈ orbL, ∃ s ∈ S0, gU i * y = tU uw.2 * s := by
    rintro i hi y ⟨uw, huw, s, hs, rfl⟩
    have hg : gG.getD i one12 ∈ gG := by
      rw [List.getD_eq_getElem _ _ (by simp [gG]; omega)]
      exact List.getElem_mem _
    obtain ⟨uw', huw', -, σ, hσ, hσeq⟩ := schB_spec uw huw _ hg
    obtain ⟨σU, hσU, hσU'⟩ := exists_mem_S0 hσ
    refine ⟨uw', huw', σU * s, S0.mul_mem hσU hs, ?_⟩
    have hvσ : ValidN 12 σ := (subB_spec s0B_spec.1).1 σ hσ
    have key : gU i * tU uw.2 = tU uw'.2 * σU := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, gU_val, tU_val, tU_val, hσU',
        ← decN_mulN (validN_getD validN_gG i).1 (length_evalW gG _),
        ← decN_mulN (length_evalW gG _) hvσ.1, hσeq]
    rw [← mul_assoc, key, mul_assoc]
  have hpow : ∀ i < 2, ∀ m : ℕ, ∀ y : GL (Fin 12) (ZMod 2),
      (∃ uw ∈ orbL, ∃ s ∈ S0, y = tU uw.2 * s) →
      ∃ uw ∈ orbL, ∃ s ∈ S0, gU i ^ m * y = tU uw.2 * s := by
    intro i hi m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_mul]
    | succ m ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hstep i hi _ (ih y hy)
  have hgen : ∀ x ∈ ({m22a, m22b} : Set (GL (Fin 12) (ZMod 2))), ∃ i < 2, x = gU i := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, by norm_num, by simp [gU]⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨1, by norm_num, by simp [gU, hx]⟩
  refine Subgroup.closure_induction_left
    (p := fun x _ => ∃ uw ∈ orbL, ∃ s ∈ S0, x = tU uw.2 * s) ?_ ?_ ?_ hx
  · exact ⟨_, v0_mem, 1, one_mem _, by simp [tU]⟩
  · intro x hx y _ hy
    obtain ⟨i, hi, rfl⟩ := hgen x hx
    exact hstep i hi y hy
  · intro x hx y _ hy
    obtain ⟨i, hi, rfl⟩ := hgen x hx
    have hfin : IsOfFinOrder (gU i) := isOfFinOrder_of_finite _
    have hinv : (gU i)⁻¹ = gU i ^ (orderOf (gU i) - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow i hi _ y hy

theorem mulVec_decomp {uw : ℕ × List ℕ} (huw : uw ∈ orbL)
    {s : GL (Fin 12) (ZMod 2)} (hs : s ∈ S0) :
    ((tU uw.2 * s : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
      (vecN 12 v0) = vecN 12 uw.1 := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, S0_fix hs, tU_mulVec huw]

theorem mem_S0_of_fix {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ m22)
    (hfix : (x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (vecN 12 v0) = vecN 12 v0) :
    x ∈ S0 := by
  obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hx
  have h1 := mulVec_decomp huw hs
  rw [hfix] at h1
  have hu : uw.1 = v0 := (vecN_inj (by decide) (orbL_lt huw) h1).symm
  have he : uw = (v0, []) := orbL_ext huw v0_mem hu
  rw [he]
  simpa [tU] using hs

theorem card_m22 : Nat.card m22 = 2661120 := by
  let f : {uw // uw ∈ orbL} × S0 → m22 := fun p =>
    ⟨tU p.1.1.2 * p.2, m22.mul_mem (tU_mem _) (S0_le p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · have h1 : tU p.1.1.2 * p.2 = tU q.1.1.2 * q.2 := congrArg Subtype.val h
      have h2 := mulVec_decomp p.1.2 p.2.2
      rw [h1, mulVec_decomp q.1.2 q.2.2] at h2
      have hpq : p.1 = q.1 := Subtype.ext (orbL_ext p.1.2 q.1.2
        (vecN_inj (orbL_lt p.1.2) (orbL_lt q.1.2) h2.symm))
      rw [hpq] at h1
      exact Prod.ext hpq (Subtype.ext (mul_left_cancel h1))
    · obtain ⟨uw, huw, s, hs, rfl⟩ := decomp hx
      exact ⟨(⟨uw, huw⟩, ⟨s, hs⟩), rfl⟩
  have hnd : orbL.Nodup := List.Nodup.of_map _ orbB_spec.2.2.1
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, card_S0,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := orbL) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, orbB_spec.2.1]

end CFSG.Quasithin.H13.M22Cert
