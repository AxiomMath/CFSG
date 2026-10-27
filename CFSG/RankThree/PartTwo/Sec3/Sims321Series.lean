module

public import CFSG.RankThree.PartTwo.Sec3.Sims321Module

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

section Series

variable {V : Type*} [CommGroup V]

private def stabSub (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {γ | ∀ w, w ∈ W ↔ γ w ∈ W}
  one_mem' _ := Iff.rfl
  mul_mem' {a b} ha hb w := (hb w).trans (ha (b w))
  inv_mem' {a} ha w := by
    have := ha (a⁻¹ w)
    rwa [MulAut.apply_inv_self, iff_comm] at this

private def restrictAut (W : Subgroup V) : stabSub W →* MulAut W where
  toFun γ :=
    { toFun := fun w => ⟨γ.1 w, (γ.2 w.1).1 w.2⟩
      invFun := fun w => ⟨γ.1⁻¹ w, ((stabSub W).inv_mem γ.2 w.1).1 w.2⟩
      left_inv := fun w => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun w => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun a b => Subtype.ext (map_mul γ.1 (a : V) (b : V)) }
  map_one' := rfl
  map_mul' _ _ := rfl

private def commHom (α : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => v⁻¹ * α v) (fun a b => by
    rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm])

private theorem commHom_apply (α : MulAut V) (v : V) : commHom α v = v⁻¹ * α v := rfl

private theorem apply_commHom (α : MulAut V) (v : V) : α (commHom α v) = commHom α (α v) := by
  simp [commHom_apply, map_mul, map_inv]

end Series

private theorem card_map_commHom {V : Type*} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : orderOf (2 : ZMod r) = k)
    {α : MulAut V} (hα : α ^ r = 1) {W : Subgroup V} (hW : ∀ v, v ∈ W ↔ α v ∈ W) :
    ∃ a, k ∣ a ∧ Nat.card (W.map (commHom α)) = 2 ^ a := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  set A : Subgroup V := W.map (commHom α)
  have hA : ∀ x, x ∈ A ↔ α x ∈ A := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨α w, (hW w).1 hw, (apply_commHom α w).symm⟩
    · rintro ⟨w, hw, hwx⟩
      refine ⟨α⁻¹ w, (hW _).2 (by simpa using hw), α.injective ?_⟩
      rw [apply_commHom, MulAut.apply_inv_self, hwx]
  have hαS : α ∈ stabSub A := hA
  have hφ' : restrictAut A ⟨α, hαS⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨α, hαS⟩ : stabSub A) ^ r = 1 := Subtype.ext (by simpa using hα)
    rw [this, map_one]
  have hfix : ∀ w : A, restrictAut A ⟨α, hαS⟩ w = w → w = 1 := by
    intro w hw
    have hαw : α (w : V) = w := congrArg Subtype.val hw
    obtain ⟨v, -, hv⟩ := Subgroup.mem_map.1 w.2
    have hv' : α v = v * w := by
      rw [← hv, commHom_apply]
      simp
    have h1 : ∀ i : ℕ, (α ^ i) v = v * (w : V) ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαw, hv', pow_succ]
        rw [mul_assoc, mul_comm (w : V) ((w : V) ^ i)]
    have h2 : (w : V) ^ r = 1 := by
      have := h1 r
      rw [hα, MulAut.one_apply] at this
      exact mul_left_cancel (a := v) (by rw [mul_one]; exact this.symm)
    obtain ⟨a, ha⟩ := hodd
    have h3 : (w : V) ^ r = w := by
      rw [ha, pow_succ, pow_mul, hV2, one_pow, one_mul]
    exact Subtype.ext (h3.symm.trans h2)
  have h1 := card_mod_eq_one_of_fpf hr (restrictAut A ⟨α, hαS⟩) hφ' hfix
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hV2 x)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hp2
  refine ⟨a, ?_, ha⟩
  have hmod : (2 : ZMod r) ^ a = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (2 ^ a) 1 r).2 (by rw [← ha]; exact h1)
    simpa using this
  exact hk ▸ orderOf_dvd_of_pow_eq_one hmod

private theorem card_map_commHom_step {V : Type*} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hk : orderOf (2 : ZMod r) = k) {α : MulAut V} (hα : α ^ r = 1) {U W : Subgroup V}
    (hU : ∀ v, v ∈ U ↔ α v ∈ U) (hW : ∀ v, v ∈ W ↔ α v ∈ W) (hUW : U ≤ W)
    (hne : ∃ v ∈ W, α v * v⁻¹ ∉ U) :
    Nat.card (U.map (commHom α)) * 2 ^ k ≤ Nat.card (W.map (commHom α)) := by
  obtain ⟨c, hkc, hc⟩ := card_map_commHom hV2 hr hr2 hk hα hU
  obtain ⟨a, hka, ha⟩ := card_map_commHom hV2 hr hr2 hk hα hW
  have hlt : U.map (commHom α) < W.map (commHom α) := by
    refine lt_of_le_of_ne (Subgroup.map_mono hUW) ?_
    obtain ⟨v, hv, hvU⟩ := hne
    intro heq
    have h1 : commHom α v ∈ W.map (commHom α) := ⟨v, hv, rfl⟩
    rw [← heq] at h1
    obtain ⟨u, hu, hux⟩ := h1
    apply hvU
    have h2 : commHom α u ∈ U := by
      rw [commHom_apply]
      exact U.mul_mem (U.inv_mem hu) ((hU u).1 hu)
    rw [hux, commHom_apply, mul_comm] at h2
    exact h2
  have hlt' := Subgroup.card_lt_of_lt hlt
  rw [hc, ha] at hlt'
  have hca : c < a := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
  have hdvd : k ∣ a - c := Nat.dvd_sub hka hkc
  have hk' : k ≤ a - c := Nat.le_of_dvd (by omega) hdvd
  rw [hc, ha, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem series_core {V : Type*} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : orderOf (2 : ZMod r) = k)
    {α : MulAut V} (hα : α ^ r = 1) {m : ℕ} (Ws : Fin (m + 1) → Subgroup V)
    (hlast : Ws (Fin.last m) = ⊤) (hmono : ∀ i : Fin m, Ws i.castSucc ≤ Ws i.succ)
    (hnorm : ∀ i (v : V), v ∈ Ws i ↔ α v ∈ Ws i) (I : Finset (Fin m))
    (hI : ∀ i ∈ I, ∃ v ∈ Ws i.succ, α v * v⁻¹ ∉ Ws i.castSucc) :
    2 ^ (k * I.card) ≤ (fixSubgroup α).index := by
  have key : ∀ j : Fin (m + 1),
      2 ^ (k * (I.filter (fun i => i.val < j.val)).card) ≤
        Nat.card ((Ws j).map (commHom α)) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      have : I.filter (fun i => i.val < (0 : Fin (m + 1)).val) = ∅ := by
        simp
      rw [this, Finset.card_empty, mul_zero, pow_zero]
      exact Nat.card_pos
    | succ i ih =>
      have hmon : Nat.card ((Ws i.castSucc).map (commHom α)) ≤
          Nat.card ((Ws i.succ).map (commHom α)) :=
        Subgroup.card_le_of_le (Subgroup.map_mono (hmono i))
      by_cases hi : i ∈ I
      · have hstep := card_map_commHom_step hV2 hr hr2 hk hα (hnorm _) (hnorm _) (hmono i)
          (hI i hi)
        have hsub : I.filter (fun i' => i'.val < i.succ.val) ⊆
            insert i (I.filter (fun i' => i'.val < i.castSucc.val)) := by
          intro i' hi'
          rw [Finset.mem_filter] at hi'
          rw [Finset.mem_insert, Finset.mem_filter]
          by_cases h : i' = i
          · exact Or.inl h
          · refine Or.inr ⟨hi'.1, ?_⟩
            have h1 := hi'.2
            have h2 : i'.val ≠ i.val := fun h' => h (Fin.ext h')
            simp only [Fin.val_succ, Fin.coe_castSucc] at h1 ⊢
            omega
        have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        calc 2 ^ (k * (I.filter (fun i' => i'.val < i.succ.val)).card)
            ≤ 2 ^ (k * ((I.filter (fun i' => i'.val < i.castSucc.val)).card + 1)) :=
              Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hcard)
          _ = 2 ^ (k * (I.filter (fun i' => i'.val < i.castSucc.val)).card) * 2 ^ k := by
              rw [Nat.mul_add, pow_add, mul_one]
          _ ≤ Nat.card ((Ws i.castSucc).map (commHom α)) * 2 ^ k :=
              Nat.mul_le_mul_right _ ih
          _ ≤ _ := hstep
      · have hsub : I.filter (fun i' => i'.val < i.succ.val) ⊆
            I.filter (fun i' => i'.val < i.castSucc.val) := by
          intro i' hi'
          rw [Finset.mem_filter] at hi' ⊢
          refine ⟨hi'.1, ?_⟩
          have h1 := hi'.2
          have h2 : i'.val ≠ i.val := fun h' => hi (Fin.ext h' ▸ hi'.1)
          simp only [Fin.val_succ, Fin.coe_castSucc] at h1 ⊢
          omega
        exact (Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))).trans (ih.trans hmon)
  have h := key (Fin.last m)
  have hfilter : I.filter (fun i => i.val < (Fin.last m).val) = I :=
    Finset.filter_true_of_mem (fun i _ => i.is_lt)
  rw [hfilter, hlast] at h
  have hker : (commHom α).ker = fixSubgroup α := by
    ext v
    simp only [MonoidHom.mem_ker, commHom_apply, mem_fixSubgroup, inv_mul_eq_one]
    exact eq_comm
  rw [Subgroup.map_top] at h
  rw [← hker, Subgroup.index_ker]
  exact h

private theorem coe_normalizerMonoidHom_pow {G : Type*} [Group G] (V : Subgroup G)
    (g : Subgroup.normalizer (V : Set G)) (n : ℕ) (v : V) :
    (((V.normalizerMonoidHom g ^ n) v : V) : G) = (g : G) ^ n * v * ((g : G) ^ n)⁻¹ := by
  rw [← map_pow]
  rfl

theorem two_pow_mul_le_relIndex_of_series {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1) {y : G}
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : orderOf (2 : ZMod r) = k) (hyr : y ^ r = 1)
    {m : ℕ} (Vs : Fin (m + 1) → Subgroup G) (h0 : Vs 0 = ⊥) (hlast : Vs (Fin.last m) = V)
    (hmono : ∀ i : Fin m, Vs i.castSucc ≤ Vs i.succ)
    (hnorm : ∀ i, y ∈ Subgroup.normalizer (Vs i : Set G)) (I : Finset (Fin m))
    (hI : ∀ i ∈ I, ∃ v ∈ Vs i.succ, y * v * y⁻¹ * v⁻¹ ∉ Vs i.castSucc) :
    2 ^ (k * I.card) ≤ (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V := by
  have _ := h0
  have hVs_le : ∀ j, Vs j ≤ V := fun j => by
    rw [← hlast]
    exact (Fin.monotone_iff_le_succ.2 hmono) (Fin.le_last j)
  have hy : y ∈ Subgroup.normalizer (V : Set G) := hlast ▸ hnorm (Fin.last m)
  letI : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  have hrel : (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V =
      (fixSubgroup (V.normalizerMonoidHom ⟨y, hy⟩)).index := by
    show ((V ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf V).index = _
    congr 1
    ext v
    rw [Subgroup.mem_subgroupOf, mem_fixSubgroup, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show y * v * y⁻¹ = v
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
    · intro h
      refine ⟨v.2, ?_⟩
      have : y * v * y⁻¹ = v := congrArg Subtype.val h
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  have hαr : V.normalizerMonoidHom ⟨y, hy⟩ ^ r = 1 := by
    ext v
    rw [coe_normalizerMonoidHom_pow]
    simp [hyr]
  have hV2' : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (by
    show (v : G) ^ 2 = 1
    rw [sq]
    exact hV2 v v.2)
  rw [hrel]
  refine series_core hV2' hr hr2 hk hαr (fun i => (Vs i).subgroupOf V) ?_ ?_ ?_ I ?_
  · rw [hlast]
    exact Subgroup.subgroupOf_self V
  · intro i v hv
    exact hmono i hv
  · intro i v
    show (v : G) ∈ Vs i ↔ y * v * y⁻¹ ∈ Vs i
    exact hnorm i v
  · intro i hi
    obtain ⟨v, hv, hvn⟩ := hI i hi
    exact ⟨⟨v, hVs_le _ hv⟩, hv, hvn⟩

end CFSG.RankThree.PartTwo.Sec3.Sims321
