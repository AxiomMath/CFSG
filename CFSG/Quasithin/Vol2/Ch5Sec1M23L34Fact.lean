module

public import CFSG.Quasithin.Vol2.Ch5Sec1M23L34Two
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.M23.M23Group

namespace M23Perm

theorem all_inner_H0 :
    ∀ α : MulAut ↥H0, α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H0 := by
  have h := CFSG.QuasithinUnique.Ch1.m23_all_inner
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq] at h
  exact h

theorem exists_intertwiner
    {Γ : Type} [Group Γ] {L : Subgroup Γ} (e : ↥L ≃* ↥H0) {r : Γ}
    (hrL : r ∈ Subgroup.normalizer (L : Set Γ)) :
    ∃ m : ↥H0, ∀ l l' : ↥L, (l' : Γ) = r * l * r⁻¹ → e l' = m * e l * m⁻¹ := by
  set α : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨r, hrL⟩ with hα
  have hαv : ∀ l : ↥L, ((α l : ↥L) : Γ) = r * l * r⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L _ l
  obtain ⟨m, hm⟩ := all_inner_H0 (e.symm.trans (α.trans e))
  refine ⟨m, fun l l' hl' => ?_⟩
  have hl : l' = α l := Subtype.ext (by rw [hl', hαv])
  have h1 := congrArg (fun φ : MulAut ↥H0 => φ (e l)) hm
  simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [hl, ← h1]

open Classical in
theorem card_fixedPoints_modEq {K : Subgroup ↥H0} {p : ℕ} [Fact p.Prime] (hK : IsPGroup p K)
    (Y : Finset (Fin 23)) (hY : ∀ k ∈ K, ∀ q ∈ Y, k • q ∈ Y) :
    (Y.filter fun q => ∀ k ∈ K, k • q = q).card ≡ Y.card [MOD p] := by
  classical
  let Ys : SubMulAction ↥K (Fin 23) :=
    { carrier := Y
      smul_mem' := fun k q hq => hY k k.2 q hq }
  have h := hK.card_modEq_card_fixedPoints ↥Ys
  have hYc : Nat.card ↥Ys = Y.card := by
    have : Nat.card ↥Ys = Nat.card ↥((Y : Set (Fin 23))) := rfl
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  let eq : ↑(MulAction.fixedPoints ↥K ↥Ys) ≃
      {q // q ∈ Y.filter fun q => ∀ k ∈ K, k • q = q} :=
    { toFun := fun w => ⟨(w.1 : Fin 23), Finset.mem_filter.mpr ⟨w.1.2,
        fun k hk => congrArg Subtype.val (w.2 ⟨k, hk⟩)⟩⟩
      invFun := fun q => ⟨⟨q.1, (Finset.mem_filter.mp q.2).1⟩, fun k => Subtype.ext
        ((Finset.mem_filter.mp q.2).2 k k.2)⟩
      left_inv := fun w => rfl
      right_inv := fun q => rfl }
  have hfc : Nat.card ↑(MulAction.fixedPoints ↥K ↥Ys) =
      (Y.filter fun q => ∀ k ∈ K, k • q = q).card := by
    rw [Nat.card_congr eq, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hYc, hfc] at h
  exact h.symm

theorem exists_unique_fixed
    {x y : Fin 23} (hxy : x ≠ y) {K : Subgroup ↥H0}
    (hK : ∀ k ∈ K, k • x = x ∧ k • y = y) (h2 : IsPGroup 2 K) (h48 : ¬ Nat.card K ∣ 48) :
    ∃ z : Fin 23, z ≠ x ∧ z ≠ y ∧ (∀ k ∈ K, k • z = z) ∧
      ∀ w : Fin 23, w ≠ x → w ≠ y → (∀ k ∈ K, k • w = w) → w = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ω : Finset (Fin 23) := Finset.univ \ {x, y} with hΩ
  have hΩc : Ω.card = 21 := by
    rw [hΩ, Finset.card_univ_sdiff, Fintype.card_fin, Finset.card_pair hxy]
  have hmemΩ : ∀ q, q ∈ Ω ↔ q ≠ x ∧ q ≠ y := fun q => by
    simp [hΩ]
  have hinv : ∀ k ∈ K, ∀ q ∈ Ω, k • q ∈ Ω := by
    intro k hk q hq
    rw [hmemΩ] at hq ⊢
    obtain ⟨hkx, hky⟩ := hK k hk
    refine ⟨fun h => hq.1 ?_, fun h => hq.2 ?_⟩
    · exact MulAction.injective k (h.trans hkx.symm)
    · exact MulAction.injective k (h.trans hky.symm)
  have hmod := card_fixedPoints_modEq h2 Ω hinv
  rw [hΩc] at hmod
  have hne : (Ω.filter fun q => ∀ k ∈ K, k • q = q).Nonempty := by
    rw [← Finset.card_pos]
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hzΩ, hzK⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzx, hzy⟩ := (hmemΩ z).mp hzΩ
  refine ⟨z, hzx, hzy, hzK, fun w hwx hwy hwK => ?_⟩
  by_contra hwz
  apply h48
  refine card_dvd_of_fixes_four (s := {x, y, z, w}) ?_ ?_
  · have h1 : x ∉ ({y, z, w} : Finset (Fin 23)) := by simp [hxy, Ne.symm hzx, Ne.symm hwx]
    have h2 : y ∉ ({z, w} : Finset (Fin 23)) := by simp [Ne.symm hzy, Ne.symm hwy]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_pair (Ne.symm hwz)]
  · intro k hk p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (hK k hk).1
    · exact (hK k hk).2
    · exact hzK k hk
    · exact hwK k hk

theorem eq_of_stab_three_le
    {x y z : Fin 23} (hxy : x ≠ y)
    (hzx : z ≠ x) (hzy : z ≠ y) {Q : Subgroup ↥H0}
    (hPQ : MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y ⊓
      MulAction.stabilizer ↥H0 z ≤ Q)
    (hQA : Q ≤ MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y)
    (hQP : Q ≠ MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y ⊓
      MulAction.stabilizer ↥H0 z) :
    Q = MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y := by
  obtain ⟨q, hqQ, hqP⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hPQ (Ne.symm hQP))
  obtain ⟨hqx, hqy⟩ := Subgroup.mem_inf.mp (hQA hqQ)
  have hqx' : q • x = x := hqx
  have hqy' : q • y = y := hqy
  have hqz : q • z ≠ z := fun h => hqP (Subgroup.mem_inf.mpr ⟨hQA hqQ, h⟩)
  have hwx : q • z ≠ x := fun h => hzx (MulAction.injective q (h.trans hqx'.symm))
  have hwy : q • z ≠ y := fun h => hzy (MulAction.injective q (h.trans hqy'.symm))
  refine le_antisymm hQA fun a ha => ?_
  obtain ⟨hax, hay⟩ := Subgroup.mem_inf.mp ha
  have hax' : a • x = x := hax
  have hay' : a • y = y := hay
  by_cases haz : a • z = z
  · exact hPQ (Subgroup.mem_inf.mpr ⟨ha, haz⟩)
  · have hvx : a • z ≠ x := fun h => hzx (MulAction.injective a (h.trans hax'.symm))
    have hvy : a • z ≠ y := fun h => hzy (MulAction.injective a (h.trans hay'.symm))
    obtain ⟨k, hkx, hky, hkz, hkw⟩ := exists_smul_eq_of_three (x := x) (y := y) (z := z)
      (u := q • z) (v := a • z)
      (nodup_four hxy (Ne.symm hzx) (Ne.symm hwx) (Ne.symm hzy) (Ne.symm hwy) (Ne.symm hqz))
      (nodup_four hxy (Ne.symm hzx) (Ne.symm hvx) (Ne.symm hzy) (Ne.symm hvy) (Ne.symm haz))
    have hkQ : k ∈ Q := hPQ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hkx, hky⟩, hkz⟩)
    have hkq : (k * q) • z = a • z := by rw [mul_smul, hkw]
    have hb : (k * q)⁻¹ * a ∈ Q := by
      refine hPQ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩)
      · show ((k * q)⁻¹ * a) • x = x
        rw [mul_smul, hax', inv_smul_eq_iff, mul_smul, hqx', hkx]
      · show ((k * q)⁻¹ * a) • y = y
        rw [mul_smul, hay', inv_smul_eq_iff, mul_smul, hqy', hky]
      · show ((k * q)⁻¹ * a) • z = z
        rw [mul_smul, inv_smul_eq_iff, hkq]
    have := Q.mul_mem (Q.mul_mem hkQ hqQ) hb
    rwa [mul_inv_cancel_left] at this

theorem smul_eq_of_mem_normalizer
    {x y z : Fin 23} (hxy : x ≠ y)
    {K : Subgroup ↥H0} {m : ↥H0}
    (hm : m ∈ Subgroup.normalizer ((MulAction.stabilizer ↥H0 x ⊓
      MulAction.stabilizer ↥H0 y : Subgroup ↥H0) : Set ↥H0))
    (hmK : m ∈ Subgroup.normalizer (K : Set ↥H0)) (hzx : z ≠ x) (hzy : z ≠ y)
    (hzK : ∀ k ∈ K, k • z = z)
    (hzu : ∀ w : Fin 23, w ≠ x → w ≠ y → (∀ k ∈ K, k • w = w) → w = z) : m • z = z := by
  have hp := fix_or_swap_of_mem_normalizer hxy hm
  apply hzu
  · intro h
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hzx (MulAction.injective m (h.trans h1.symm))
    · exact hzy (MulAction.injective m (h.trans h2.symm))
  · intro h
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hzy (MulAction.injective m (h.trans h2.symm))
    · exact hzx (MulAction.injective m (h.trans h1.symm))
  · intro k hk
    have h1 : m⁻¹ * k * m ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hmK) k).mp hk
      rwa [inv_inv] at this
    have h2 := hzK _ h1
    rw [mul_smul, mul_smul] at h2
    have h3 := congrArg (m • ·) h2
    simp only [smul_inv_smul] at h3
    exact h3

end M23Perm

open M23Perm in
theorem factM23L34_holds :
    FactM23L34 := by
  intro Γ _ _ L A S R hL hAL hA hS hRL hRA hRS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, x, y, hxy, hAe⟩ := exists_two_point_stabilizer hL hAL hA
  have hAc : Nat.card A = 20160 := (l34_facts e hAL hA).2.1
  set A₂ : Subgroup ↥H0 := MulAction.stabilizer ↥H0 x ⊓ MulAction.stabilizer ↥H0 y with hA₂
  have hAA : ∀ l : ↥L, (l : Γ) ∈ A ↔ e l ∈ A₂ := fun l => by
    rw [hAe l, hA₂, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have hSA : S ≤ A := hS.1
  have hSL : S ≤ L := hSA.trans hAL
  set S' : Subgroup ↥H0 := (S.subgroupOf L).map e.toMonoidHom with hS'
  have hSS : ∀ l : ↥L, (l : Γ) ∈ S ↔ e l ∈ S' := fun l => by
    rw [hS', Subgroup.mem_map_equiv, e.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hS'A : ∀ s ∈ S', s • x = x ∧ s • y = y := by
    intro s hs
    have h1 := (hSS (e.symm s)).mpr (by rwa [e.apply_symm_apply])
    have h2 := (hAe (e.symm s)).mp (hSA h1)
    rwa [e.apply_symm_apply] at h2
  let ιS : ↥S ≃* ↥S' := (Subgroup.subgroupOfEquivOfLe hSL).symm.trans
    ((S.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have hS2 : IsPGroup 2 S' := hS.2.1.of_equiv ιS
  have hS64 : Nat.card S = 64 := by
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    have hmul := Subgroup.card_mul_index (S.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv, hk, hAc] at hmul
    have hodd := hS.2.2
    have hk14 : k ≤ 14 := by
      by_contra h
      push Not at h
      have h1 : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      have h2 : 2 ^ k ≤ 20160 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
      norm_num at h1
      omega
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega
  have hS'c : Nat.card S' = 64 := by rw [← Nat.card_congr ιS.toEquiv, hS64]
  obtain ⟨z, hzx, hzy, hzS, hzu⟩ :=
    exists_unique_fixed hxy hS'A hS2 (by rw [hS'c]; norm_num)
  set P' : Subgroup ↥H0 := A₂ ⊓ MulAction.stabilizer ↥H0 z with hP'
  set P : Subgroup Γ := (P'.comap e.toMonoidHom).map L.subtype with hP
  have hPL : P ≤ L := by
    rintro _ ⟨l, -, rfl⟩
    exact l.2
  have hPP : ∀ l : ↥L, (l : Γ) ∈ P ↔ e l ∈ P' := fun l => by
    constructor
    · rintro ⟨l', hl', hll'⟩
      have : l' = l := Subtype.ext hll'
      rw [← this]
      exact hl'
    · intro h
      exact ⟨l, h, rfl⟩
  have hcorr : ∀ {Q₁ Q₂ : Subgroup Γ} {Q₁' Q₂' : Subgroup ↥H0},
      (∀ l : ↥L, (l : Γ) ∈ Q₁ ↔ e l ∈ Q₁') → (∀ l : ↥L, (l : Γ) ∈ Q₂ ↔ e l ∈ Q₂') →
      (Q₁ ≤ L → Q₁' ≤ Q₂' → Q₁ ≤ Q₂) ∧ (Q₁ ≤ Q₂ → Q₁' ≤ Q₂') := by
    intro Q₁ Q₂ Q₁' Q₂' h1 h2
    refine ⟨fun hL1 hle g hg => (h2 ⟨g, hL1 hg⟩).mpr (hle ((h1 ⟨g, hL1 hg⟩).mp hg)),
      fun hle g hg => ?_⟩
    have h3 := (h1 (e.symm g)).mpr (by rwa [e.apply_symm_apply])
    have h4 := (h2 (e.symm g)).mp (hle h3)
    rwa [e.apply_symm_apply] at h4
  have hB : A ⊓ Subgroup.normalizer (S : Set Γ) ≤ P := by
    intro g hg
    obtain ⟨hgA, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgL := hAL hgA
    have hmN := (mem_normalizer_iff_of_corr e hSL hSS (Subgroup.le_normalizer hgL)
      (intertwine_self e ⟨g, hgL⟩)).mp hgN
    have hmA : e ⟨g, hgL⟩ ∈ A₂ := (hAA ⟨g, hgL⟩).mp hgA
    have hz := smul_eq_of_mem_normalizer hxy (Subgroup.le_normalizer hmA) hmN hzx hzy hzS hzu
    exact (hPP ⟨g, hgL⟩).mpr (Subgroup.mem_inf.mpr ⟨hmA, hz⟩)
  have hPA : P ≤ A := (hcorr hPP hAA).1 hPL inf_le_left
  refine ⟨P, ⟨⟨hPA, S, hS, hB⟩, ?_, ?_⟩, hB, ?_⟩
  ·
    intro hPA'
    obtain ⟨g, hgx, hgy, hgz⟩ := exists_fix_two_move hxy hzx hzy
    have hle := (hcorr hAA hPP).2 hPA'.symm.le
    exact hgz (Subgroup.mem_inf.mp (hle (Subgroup.mem_inf.mpr ⟨hgx, hgy⟩))).2
  ·
    intro Q hQ hQA hPQ
    obtain ⟨hQA', -⟩ := hQ
    have hQL : Q ≤ L := hQA'.trans hAL
    set Q' : Subgroup ↥H0 := (Q.subgroupOf L).map e.toMonoidHom with hQ'
    have hQQ : ∀ l : ↥L, (l : Γ) ∈ Q ↔ e l ∈ Q' := fun l => by
      rw [hQ', Subgroup.mem_map_equiv, e.symm_apply_apply, Subgroup.mem_subgroupOf]
    by_contra hne
    have hne' : Q' ≠ P' := fun h => hne (le_antisymm ((hcorr hQQ hPP).1 hQL h.le) hPQ)
    have h1 := eq_of_stab_three_le hxy hzx hzy ((hcorr hPP hQQ).2 hPQ)
      ((hcorr hQQ hAA).2 hQA') hne'
    exact hQA (le_antisymm hQA' ((hcorr hAA hQQ).1 hAL h1.symm.le))
  ·
    intro r hr
    obtain ⟨m, hm⟩ := exists_intertwiner e (hRL hr)
    have hmA := (mem_normalizer_iff_of_corr e hAL hAA (hRL hr) hm).mp (hRA hr)
    have hmS := (mem_normalizer_iff_of_corr e hSL hSS (hRL hr) hm).mp (hRS hr)
    have hmz := smul_eq_of_mem_normalizer hxy hmA hmS hzx hzy hzS hzu
    exact (mem_normalizer_iff_of_corr e hPL hPP (hRL hr) hm).mpr
      (mem_normalizer_stab_of_perm (fix_or_swap_of_mem_normalizer hxy hmA) hmz)

end CFSG.Quasithin.H13
