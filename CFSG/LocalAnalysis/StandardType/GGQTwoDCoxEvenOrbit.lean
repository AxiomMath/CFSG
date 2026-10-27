module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset

theorem dPerm_apply_apply (d : ℕ) (σ : Equiv.Perm (Fin d)) (v : DVec d) (j : Fin d) :
    dPerm d σ v j = v (σ.symm j) := by
  have h : dPerm d σ = LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) σ.symm := by
    refine (dBasis d).ext' fun i => ?_
    rw [dPerm_apply]
    funext j
    simp only [Pi.basisFun_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Pi.single_apply, Equiv.symm_apply_eq]
  rw [h]
  rfl

@[expose] noncomputable def dFlip (d : ℕ) (A : Finset (Fin d)) : DVec d ≃ₗ[ZMod 3] DVec d :=
  LinearEquiv.piCongrRight fun i =>
    if i ∈ A then LinearEquiv.neg (ZMod 3) else LinearEquiv.refl (ZMod 3) (ZMod 3)

theorem dFlip_apply (d : ℕ) (A : Finset (Fin d)) (v : DVec d) (j : Fin d) :
    dFlip d A v j = (if j ∈ A then (-1 : ZMod 3) else 1) * v j := by
  by_cases hj : j ∈ A <;> simp [dFlip, hj]

theorem dFlip_mem_dEven (d : ℕ) {A : Finset (Fin d)} (hA : Even A.card) :
    dFlip d A ∈ dEven d := by
  refine ⟨1, fun i => if i ∈ A then -1 else 1, fun i => ?_, ?_, fun i => ?_⟩
  · by_cases hi : i ∈ A <;> simp [hi]
  · rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hA.neg_one_pow]
  · funext j
    rw [dFlip_apply]
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.basisFun_apply, hji]

theorem le_choose_of_pos_of_lt : ∀ {d k : ℕ}, 1 ≤ k → k < d → d ≤ d.choose k
  | d, k, hk, hkd => by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ']
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · subst h0
      simp
    · rcases Nat.lt_or_ge (k' + 1) d' with h1 | h1
      · have h2 := le_choose_of_pos_of_lt (d := d') (k := k') h0 (by omega)
        have h3 := le_choose_of_pos_of_lt (d := d') (k := k' + 1) (by omega) h1
        omega
      · obtain rfl : d' = k' + 1 := by omega
        simp [Nat.choose_succ_self_right]

theorem card_le_card_orbit {d : ℕ} {v : DVec d} {X : Finset (DVec d)}
    (hX : ∀ w ∈ X, w ∈ MulAction.orbit (dEven d) v) :
    X.card ≤ Nat.card (MulAction.orbit (dEven d) v) := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hX (Set.toFinite _)

theorem mem_orbit_of_mem_dEven {d : ℕ} {g : DVec d ≃ₗ[ZMod 3] DVec d} (hg : g ∈ dEven d)
    {v w : DVec d} (hw : w ∈ MulAction.orbit (dEven d) v) :
    g w ∈ MulAction.orbit (dEven d) v := by
  obtain ⟨h, rfl⟩ := hw
  refine ⟨⟨g, hg⟩ * h, ?_⟩
  show (⟨g, hg⟩ * h : dEven d) • v = g (h • v)
  rw [mul_smul]
  rfl

private lemma neg_ne_self_zmod3 : ∀ x : ZMod 3, x ≠ 0 → -x ≠ x := by decide

theorem two_pow_le_card_orbit_of_full {d : ℕ} (hd : 1 ≤ d) {v : DVec d} (hv : ∀ i, v i ≠ 0) :
    2 ^ (d - 1) ≤ Nat.card (MulAction.orbit (dEven d) v) := by
  classical
  set z : Fin d := ⟨0, by omega⟩
  let ev : Finset (Fin d) → Finset (Fin d) := fun A => if Even A.card then A else insert z A
  have hev : ∀ A ∈ (univ.erase z).powerset, Even (ev A).card := by
    intro A hA
    have hzA : z ∉ A := fun h => by simpa using mem_powerset.1 hA h
    simp only [ev]
    split_ifs with he
    · exact he
    · rw [card_insert_of_notMem hzA]
      exact (Nat.not_even_iff_odd.1 he).add_one
  have hinj : Set.InjOn (fun A => dFlip d (ev A) v) ((univ.erase z).powerset : Set _) := by
    intro A hA B hB hAB
    have hzA : z ∉ A := fun h => by simpa using mem_powerset.1 hA h
    have hzB : z ∉ B := fun h => by simpa using mem_powerset.1 hB h
    have key : ∀ j, j ∈ ev A ↔ j ∈ ev B := by
      intro j
      have h := congrFun hAB j
      simp only [dFlip_apply] at h
      by_cases h1 : j ∈ ev A <;> by_cases h2 : j ∈ ev B <;> simp only [h1, h2, if_true, if_false,
        neg_mul, one_mul] at h ⊢
      · exact (neg_ne_self_zmod3 _ (hv j) h).elim
      · exact (neg_ne_self_zmod3 _ (hv j) h.symm).elim
    ext j
    by_cases hjz : j = z
    · subst hjz
      simp [hzA, hzB]
    · have h := key j
      simp only [ev] at h
      split_ifs at h <;> simpa [mem_insert, hjz] using h
  have hcard : ((univ.erase z).powerset.image fun A => dFlip d (ev A) v).card = 2 ^ (d - 1) := by
    rw [card_image_of_injOn hinj, card_powerset, card_erase_of_mem (mem_univ z), card_univ,
      Fintype.card_fin]
  rw [← hcard]
  refine card_le_card_orbit fun w hw => ?_
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hw
  exact mem_orbit_of_mem_dEven (dFlip_mem_dEven d (hev A hA)) (MulAction.mem_orbit_self v)

@[expose] def dVecSupp {d : ℕ} (w : DVec d) : Finset (Fin d) :=
  univ.filter fun i => w i ≠ 0

theorem mem_dVecSupp {d : ℕ} {w : DVec d} {i : Fin d} : i ∈ dVecSupp w ↔ w i ≠ 0 := by
  simp [dVecSupp]

theorem dVecSupp_dFlip {d : ℕ} (A : Finset (Fin d)) (w : DVec d) :
    dVecSupp (dFlip d A w) = dVecSupp w := by
  ext i
  rw [mem_dVecSupp, mem_dVecSupp, dFlip_apply]
  by_cases hi : i ∈ A <;> simp [hi]

theorem four_mul_choose_le_card_orbit {d : ℕ} {v : DVec d} (hk2 : 2 ≤ (dVecSupp v).card)
    (hkd : (dVecSupp v).card < d) :
    4 * d.choose (dVecSupp v).card ≤ Nat.card (MulAction.orbit (dEven d) v) := by
  classical
  set k := (dVecSupp v).card with hk
  set O : Finset (DVec d) := (Set.toFinite (MulAction.orbit (dEven d) v)).toFinset with hO
  have hmemO : ∀ w, w ∈ O ↔ w ∈ MulAction.orbit (dEven d) v := fun w => Set.Finite.mem_toFinset _
  have hfib : ∀ T ∈ powersetCard k (univ : Finset (Fin d)),
      4 ≤ (O.filter fun w => dVecSupp w = T).card := by
    intro T hT
    have hTk : T.card = k := (mem_powersetCard.1 hT).2
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq (dVecSupp v) T hTk.symm
    set w := dPerm d σ v with hw
    have hwT : dVecSupp w = T := by
      ext j
      rw [mem_dVecSupp, hw, dPerm_apply_apply, ← hσ, Finset.mem_map_equiv, mem_dVecSupp]
    have hwO : w ∈ MulAction.orbit (dEven d) v :=
      mem_orbit_of_mem_dEven (dPerm_mem_dEven d σ) (MulAction.mem_orbit_self v)
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < T.card)
    obtain ⟨z, hz⟩ : ∃ z, z ∉ T := by
      by_contra hcon
      push Not at hcon
      have hT' : T = univ := eq_univ_of_forall hcon
      rw [hT', card_univ, Fintype.card_fin] at hTk
      omega
    have haz : a ≠ z := fun h => hz (h ▸ ha)
    have hbz : b ≠ z := fun h => hz (h ▸ hb)
    have hwa : w a ≠ 0 := mem_dVecSupp.1 (hwT ▸ ha)
    have hwb : w b ≠ 0 := mem_dVecSupp.1 (hwT ▸ hb)
    have hwz : w z = 0 := by
      by_contra h
      exact hz (hwT ▸ mem_dVecSupp.2 h)
    have hflip : ∀ {x y : Fin d}, x ≠ y → dFlip d {x, y} w ∈ O := fun {x y} hxy =>
      (hmemO _).2 (mem_orbit_of_mem_dEven (dFlip_mem_dEven d (by rw [card_pair hxy]; decide)) hwO)
    have hfa : ∀ (A : Finset (Fin d)) (i : Fin d), dFlip d A w i =
        (if i ∈ A then -w i else w i) := fun A i => by
      rw [dFlip_apply]
      split_ifs <;> ring
    have hne : ∀ {x : ZMod 3}, x ≠ 0 → -x ≠ x := fun {x} hx => neg_ne_self_zmod3 x hx
    let X : Finset (DVec d) := {w, dFlip d {a, z} w, dFlip d {b, z} w, dFlip d {a, b} w}
    have hX4 : X.card = 4 := by
      have h1 : w ≠ dFlip d {a, z} w := fun h => hne hwa (by
        have := congrFun h a; rw [hfa] at this; simpa using this.symm)
      have h2 : w ≠ dFlip d {b, z} w := fun h => hne hwb (by
        have := congrFun h b; rw [hfa] at this; simpa using this.symm)
      have h3 : w ≠ dFlip d {a, b} w := fun h => hne hwa (by
        have := congrFun h a; rw [hfa] at this; simpa using this.symm)
      have h4 : dFlip d {a, z} w ≠ dFlip d {b, z} w := fun h => hne hwa (by
        have := congrFun h a; rw [hfa, hfa] at this; simpa [hab, haz] using this)
      have h5 : dFlip d {a, z} w ≠ dFlip d {a, b} w := fun h => hne hwb (by
        have := congrFun h b; rw [hfa, hfa] at this; simpa [hab.symm, hbz] using this.symm)
      have h6 : dFlip d {b, z} w ≠ dFlip d {a, b} w := fun h => hne hwa (by
        have := congrFun h a; rw [hfa, hfa] at this; simpa [hab, haz] using this.symm)
      rw [card_insert_of_notMem (by simp [h1, h2, h3]), card_insert_of_notMem (by simp [h4, h5]),
        card_insert_of_notMem (by simp [h6]), card_singleton]
    have hXsub : X ⊆ O.filter fun u => dVecSupp u = T := by
      intro u hu
      rw [mem_filter]
      simp only [X, mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact ⟨(hmemO _).2 hwO, hwT⟩
      · exact ⟨hflip haz, by rw [dVecSupp_dFlip, hwT]⟩
      · exact ⟨hflip hbz, by rw [dVecSupp_dFlip, hwT]⟩
      · exact ⟨hflip hab, by rw [dVecSupp_dFlip, hwT]⟩
    calc 4 = X.card := hX4.symm
      _ ≤ _ := card_le_card hXsub
  have hdisj : ((powersetCard k (univ : Finset (Fin d)) : Set (Finset (Fin d)))).PairwiseDisjoint
      (fun T => O.filter fun w => dVecSupp w = T) := by
    intro T _ T' _ hTT'
    refine disjoint_filter.2 fun w _ h h' => hTT' (h.symm.trans h')
  have hU : (powersetCard k (univ : Finset (Fin d))).biUnion
      (fun T => O.filter fun w => dVecSupp w = T) ⊆ O := by
    intro w hw
    obtain ⟨T, -, hwT⟩ := mem_biUnion.1 hw
    exact (mem_filter.1 hwT).1
  have hOcard : O.card = Nat.card (MulAction.orbit (dEven d) v) := by
    rw [hO, Set.Finite.card_toFinset, Nat.card_eq_fintype_card]
  calc 4 * d.choose k = ∑ _T ∈ powersetCard k (univ : Finset (Fin d)), 4 := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    _ ≤ ∑ T ∈ powersetCard k (univ : Finset (Fin d)), (O.filter fun w => dVecSupp w = T).card :=
        sum_le_sum hfib
    _ = ((powersetCard k (univ : Finset (Fin d))).biUnion
          (fun T => O.filter fun w => dVecSupp w = T)).card := (card_biUnion hdisj).symm
    _ ≤ O.card := card_le_card hU
    _ = Nat.card (MulAction.orbit (dEven d) v) := hOcard

end CFSG.StandardType.QTwo

end
