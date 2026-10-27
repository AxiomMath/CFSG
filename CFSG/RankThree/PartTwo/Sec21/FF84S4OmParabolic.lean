module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmPair
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP1

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_inv eichler_conj
  eichler_zero_right eichler_add_smul_self eichler_apply_eq_of_polar_eq)

theorem polarMinus_add_left (u v w : F6) :
    polarMinus (u + v) w = polarMinus u w + polarMinus v w := by
  simp only [polarMinus, Pi.add_apply]
  ring

theorem polarMinus_add_right (u v w : F6) :
    polarMinus u (v + w) = polarMinus u v + polarMinus u w := by
  simp only [polarMinus, Pi.add_apply]
  ring

theorem polarMinus_smul_left (c : ZMod 2) (u w : F6) :
    polarMinus (c • u) w = c * polarMinus u w := by
  simp only [polarMinus, Pi.smul_apply, smul_eq_mul]
  ring

theorem polarMinus_zero_right (u : F6) : polarMinus u 0 = 0 := by
  simp [polarMinus]

theorem add_self_F6 (w : F6) : w + w = 0 := by
  funext k
  exact CharTwo.add_self_eq_zero (w k)

theorem omq (g : OmG) (v : F6) : qMinus ((g : F6 ≃ₗ[ZMod 2] F6) v) = qMinus v :=
  qMinus_apply_of_mem g.2 v

theorem omp (g : OmG) (u v : F6) :
    polarMinus ((g : F6 ≃ₗ[ZMod 2] F6) u) ((g : F6 ≃ₗ[ZMod 2] F6) v) = polarMinus u v :=
  polarMinus_apply_of_mem g.2 u v

theorem mem_stabilizer_vec {t : F6} {g : OmG} :
    g ∈ stabilizer OmG t ↔ (g : F6 ≃ₗ[ZMod 2] F6) t = t := by
  rw [mem_stabilizer_iff]
  rfl

@[expose] noncomputable def eichG (t w : F6) : OmG :=
  ⟨eichler qMinusForm t w, eichler_mem_timmesfeldOmega t w⟩

theorem eichG_apply {t w : F6} (ht : qMinus t = 0) (hw : polarMinus t w = 0) (x : F6) :
    (eichG t w : F6 ≃ₗ[ZMod 2] F6) x =
      x + polarMinus x t • w + (polarMinus x w + qMinus w * polarMinus x t) • t :=
  eichler_apply_qMinus ht hw x

theorem eichG_mul {t w w' : F6} (hw : polarMinus t w = 0) (hw' : polarMinus t w' = 0) :
    eichG t w * eichG t w' = eichG t (w + w') :=
  Subtype.ext (eichler_mul (by rwa [polar_qMinusForm]) (by rwa [polar_qMinusForm]))

theorem eichG_zero (t : F6) : eichG t 0 = 1 :=
  Subtype.ext (eichler_zero_right qMinusForm t)

theorem eichG_self {t : F6} (ht : qMinus t = 0) : eichG t t = 1 := by
  have h := eichler_add_smul_self (Q := qMinusForm) (u := t) (by rwa [qMinusForm_apply]) 0 1
  have h2 : eichler qMinusForm t t = 1 := by simpa [eichler_zero_right] using h
  exact Subtype.ext h2

theorem eichG_conj (g : OmG) (t w : F6) :
    g * eichG t w * g⁻¹ =
      eichG ((g : F6 ≃ₗ[ZMod 2] F6) t) ((g : F6 ≃ₗ[ZMod 2] F6) w) :=
  Subtype.ext (eichler_conj (timmesfeldOmega_le_orthogonalGroup g.2) t w)

theorem eichG_sq {t w : F6} (hw : polarMinus t w = 0) : eichG t w * eichG t w = 1 := by
  rw [eichG_mul hw hw, add_self_F6, eichG_zero]

@[expose] def Et (t : F6) : Subgroup OmG where
  carrier := {g | ∃ w, polarMinus t w = 0 ∧ g = eichG t w}
  mul_mem' := by
    rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
    exact ⟨w + w', by rw [polarMinus_add_right, hw, hw', add_zero], eichG_mul hw hw'⟩
  one_mem' := ⟨0, polarMinus_zero_right t, (eichG_zero t).symm⟩
  inv_mem' := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hw, inv_eq_of_mul_eq_one_right (eichG_sq hw)⟩

theorem Et_comm {t : F6} {a b : OmG} (ha : a ∈ Et t) (hb : b ∈ Et t) : a * b = b * a := by
  obtain ⟨w, hw, rfl⟩ := ha
  obtain ⟨w', hw', rfl⟩ := hb
  rw [eichG_mul hw hw', eichG_mul hw' hw, add_comm]

theorem Et_sq {t : F6} {a : OmG} (ha : a ∈ Et t) : a * a = 1 := by
  obtain ⟨w, hw, rfl⟩ := ha
  exact eichG_sq hw

theorem Et_normalized {t : F6} :
    ∀ g ∈ stabilizer OmG t, ∀ x ∈ Et t, g * x * g⁻¹ ∈ Et t := by
  intro g hg x hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hgt : (g : F6 ≃ₗ[ZMod 2] F6) t = t := mem_stabilizer_vec.1 hg
  refine ⟨(g : F6 ≃ₗ[ZMod 2] F6) w, ?_, ?_⟩
  · have := omp g t w
    rw [hgt] at this
    rw [this, hw]
  · rw [eichG_conj, hgt]

theorem Et_le_stabilizer {t : F6} (ht : qMinus t = 0) : Et t ≤ stabilizer OmG t := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_stabilizer_vec, eichG_apply ht hw, polarMinus_self, hw]
  simp

theorem Et_isPGroup {t : F6} : IsPGroup 2 ↥(Et t) := by
  intro x
  refine ⟨1, ?_⟩
  have h := Et_sq x.2
  apply Subtype.ext
  simpa [pow_two] using h

instance instFiniteOmG : Finite OmG :=
  Nat.finite_of_card_ne_zero (by rw [card_timmesfeldOmega]; norm_num)

private theorem omY_card : ∀ t : F6, qMinus t = 0 → t ≠ 0 →
    (Finset.univ.filter fun y : F6 => qMinus y = 0 ∧ polarMinus t y = 1).card = 16 := by
  decide +kernel

private theorem omY_exists : ∀ t : F6, qMinus t = 0 → t ≠ 0 →
    ∃ y : F6, qMinus y = 0 ∧ polarMinus t y = 1 := by
  decide +kernel

private theorem two_pow_ne_sixty (n : ℕ) : 2 ^ n ≠ 60 := by
  intro h
  have h3 : 3 ∣ 2 ^ n := by rw [h]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem fix_of_mem_Op {t : F6} {g : OmG} (hg : g ∈ Op 2 (stabilizer OmG t)) :
    (g : F6 ≃ₗ[ZMod 2] F6) t = t :=
  mem_stabilizer_vec.1 (L41.Op_le (p := 2) _ hg)

theorem card_Op_le {t y : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) (hy : qMinus y = 0)
    (hty : polarMinus t y = 1) : Nat.card ↥(Op 2 (stabilizer OmG t)) ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyt : polarMinus y t = 1 := by rw [polarMinus_comm]; exact hty
  have hs : qMinus (y + t) = 1 := by rw [qMinus_add, hy, ht, hyt]; rfl
  have hst : qMinus (y + t + t) = 0 := by
    rw [add_assoc, add_self_F6, add_zero]; exact hy
  obtain ⟨e⟩ := Om_pair hs ht hst h0
  set K : Subgroup OmG := stabilizer OmG (y + t) ⊓ stabilizer OmG t with hK
  haveI : IsSimpleGroup ↥K := e.isSimpleGroup
  have hKS : K ≤ stabilizer OmG t := inf_le_right
  have hM : ((Op 2 (stabilizer OmG t)).subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := L41.Op_conj_mem (p := 2) (hKS k.2) hn
    simpa using this
  have hKcard : Nat.card ↥K = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hbot : (Op 2 (stabilizer OmG t)).subgroupOf K = ⊥ := by
    haveI := hM
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Op 2 (stabilizer OmG t)).subgroupOf K) with h | h
    · exact h
    · exfalso
      have hle : K ≤ Op 2 (stabilizer OmG t) := by
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ (Op 2 (stabilizer OmG t)).subgroupOf K := by rw [h]; trivial
        exact this
      obtain ⟨n, hn⟩ := (IsPGroup.to_le (L41.Op_isPGroup (p := 2) (stabilizer OmG t)) hle).exists_card_eq
      rw [hKcard] at hn
      exact two_pow_ne_sixty n hn.symm
  have hmem : ∀ g : ↥(Op 2 (stabilizer OmG t)),
      qMinus (((g : OmG) : F6 ≃ₗ[ZMod 2] F6) y) = 0 ∧
        polarMinus t (((g : OmG) : F6 ≃ₗ[ZMod 2] F6) y) = 1 := by
    intro g
    have hgt := fix_of_mem_Op g.2
    refine ⟨by rw [omq, hy], ?_⟩
    have := omp g.1 t y
    rw [hgt] at this
    rw [this, hty]
  let f : ↥(Op 2 (stabilizer OmG t)) →
      {y' : F6 // qMinus y' = 0 ∧ polarMinus t y' = 1} :=
    fun g => ⟨((g : OmG) : F6 ≃ₗ[ZMod 2] F6) y, hmem g⟩
  have hinj : Function.Injective f := by
    intro g g' hgg
    have h1 : ((g : OmG) : F6 ≃ₗ[ZMod 2] F6) y = ((g' : OmG) : F6 ≃ₗ[ZMod 2] F6) y :=
      congrArg Subtype.val hgg
    have hgt := fix_of_mem_Op g.2
    have hgt' := fix_of_mem_Op g'.2
    have hk : (g : OmG)⁻¹ * (g' : OmG) ∈ K := by
      have hfix : ∀ v, ((g : OmG) : F6 ≃ₗ[ZMod 2] F6) v = ((g' : OmG) : F6 ≃ₗ[ZMod 2] F6) v →
          (((g : OmG)⁻¹ * (g' : OmG) : OmG) : F6 ≃ₗ[ZMod 2] F6) v = v := by
        intro v hv
        show (((g : OmG)⁻¹ : OmG) : F6 ≃ₗ[ZMod 2] F6) (((g' : OmG) : F6 ≃ₗ[ZMod 2] F6) v) = v
        rw [← hv]
        exact ((g : OmG) : F6 ≃ₗ[ZMod 2] F6).symm_apply_apply v
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_stabilizer_vec]
        apply hfix
        rw [map_add, map_add, hgt, hgt', h1]
      · rw [mem_stabilizer_vec]
        apply hfix
        rw [hgt, hgt']
    have hkO : (g : OmG)⁻¹ * (g' : OmG) ∈ Op 2 (stabilizer OmG t) :=
      mul_mem (inv_mem g.2) g'.2
    have : (⟨(g : OmG)⁻¹ * (g' : OmG), hk⟩ : ↥K) ∈
        (Op 2 (stabilizer OmG t)).subgroupOf K := hkO
    rw [hbot, Subgroup.mem_bot] at this
    have h2 : (g : OmG)⁻¹ * (g' : OmG) = 1 := congrArg Subtype.val this
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hY : Nat.card {y' : F6 // qMinus y' = 0 ∧ polarMinus t y' = 1} = 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact omY_card t ht h0
  calc Nat.card ↥(Op 2 (stabilizer OmG t)) ≤
      Nat.card {y' : F6 // qMinus y' = 0 ∧ polarMinus t y' = 1} :=
        Nat.card_le_card_of_injective f hinj
    _ = 16 := hY

theorem card_Et_ge {t y : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) (hy : qMinus y = 0)
    (hty : polarMinus t y = 1) : 16 ≤ Nat.card ↥(Et t) := by
  let f : ↥(Et t) → F6 := fun g => ((g : OmG) : F6 ≃ₗ[ZMod 2] F6) y
  have hsub : {y' : F6 | qMinus y' = 0 ∧ polarMinus t y' = 1} ⊆ Set.range f := by
    rintro y' ⟨hy', hty'⟩
    have hw : polarMinus t (y' - y) = 0 := by
      have h := QuadraticMap.polar_sub_right qMinusForm t y' y
      rw [polar_qMinusForm, polar_qMinusForm, polar_qMinusForm, hty', hty, sub_self] at h
      exact h
    refine ⟨⟨eichG t (y' - y), y' - y, hw, rfl⟩, ?_⟩
    show eichler qMinusForm t (y' - y) y = y'
    have h := eichler_apply_eq_of_polar_eq (Q := qMinusForm) (u := t) (x := y) (y := y')
      (t := 1) (by rwa [qMinusForm_apply]) (by rw [qMinusForm_apply, qMinusForm_apply, hy, hy'])
      (by rw [polar_qMinusForm]; exact hty) (by rw [polar_qMinusForm]; exact hty') one_ne_zero
    simpa using h
  have hfin : (Set.range f).Finite := Set.finite_range f
  have h1 : {y' : F6 | qMinus y' = 0 ∧ polarMinus t y' = 1}.ncard ≤ (Set.range f).ncard :=
    Set.ncard_le_ncard hsub hfin
  have h2 : (Set.range f).ncard ≤ Nat.card ↥(Et t) := by
    rw [← Set.image_univ, ← Set.ncard_univ]
    exact Set.ncard_image_le Set.finite_univ
  have h3 : {y' : F6 | qMinus y' = 0 ∧ polarMinus t y' = 1}.ncard = 16 := by
    have e : {y' : F6 | qMinus y' = 0 ∧ polarMinus t y' = 1} =
        ↑(Finset.univ.filter fun y' : F6 => qMinus y' = 0 ∧ polarMinus t y' = 1) := by
      ext; simp
    rw [e, Set.ncard_coe_finset]
    exact omY_card t ht h0
  omega

theorem Op_eq_Et {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) :
    Op 2 (stabilizer OmG t) = Et t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, hty⟩ := omY_exists t ht h0
  have hle : Et t ≤ Op 2 (stabilizer OmG t) :=
    L41.le_Op_of_normalized (Et_le_stabilizer ht) Et_normalized Et_isPGroup
  have h1 := card_Op_le ht h0 hy hty
  have h2 := card_Et_ge ht h0 hy hty
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem card_Et {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) : Nat.card ↥(Et t) = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, hty⟩ := omY_exists t ht h0
  have h1 := card_Op_le ht h0 hy hty
  have h2 := card_Et_ge ht h0 hy hty
  rw [Op_eq_Et ht h0] at h1
  omega

private theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem Om_parabolic_elemAb {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) :
    IsElemAb 2 4 (Op 2 (stabilizer OmG t)) := by
  rw [Op_eq_Et ht h0]
  refine ⟨?_, by rw [card_Et ht h0]; norm_num⟩
  refine CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (Et_comm a.2 b.2)
  · rw [pow_two]
    exact Et_sq hx

private theorem omPerp_check : ∀ t z : F6, qMinus t = 0 → t ≠ 0 →
    (∀ v : F6, polarMinus v t = 0 → polarMinus z v = 0) → z = 0 ∨ z = t := by
  decide +kernel

theorem Om_parabolic_fix {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) (g : OmG)
    (hg : ∀ x : F6, polarMinus x t = 0 → (g : F6 ≃ₗ[ZMod 2] F6) x = x) : g = 1 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  show (g : F6 ≃ₗ[ZMod 2] F6) v = v
  by_cases hv : polarMinus v t = 0
  · exact hg v hv
  · have hv1 : polarMinus v t = 1 := by
      revert hv
      generalize polarMinus v t = a
      revert a
      decide
    have hz : ∀ x : F6, polarMinus x t = 0 →
        polarMinus ((g : F6 ≃ₗ[ZMod 2] F6) v + v) x = 0 := by
      intro x hx
      rw [polarMinus_add_left]
      have := omp g v x
      rw [hg x hx] at this
      rw [this]
      exact CharTwo.add_self_eq_zero _
    have hgv : (g : F6 ≃ₗ[ZMod 2] F6) v = (g : F6 ≃ₗ[ZMod 2] F6) v + v + v := by
      rw [add_assoc, add_self_F6, add_zero]
    rcases omPerp_check t _ ht h0 hz with h | h
    · rw [hgv, h, zero_add]
    · exfalso
      have h1 : (g : F6 ≃ₗ[ZMod 2] F6) v = v + t := by
        rw [hgv, h, add_comm]
      have h2 := omq g v
      rw [h1, qMinus_add, ht, hv1] at h2
      revert h2
      generalize qMinus v = a
      revert a
      decide

private theorem omPerp_ex : ∀ t : F6, qMinus t = 0 → t ≠ 0 →
    ∃ x w : F6, polarMinus x t = 0 ∧ polarMinus w t = 0 ∧ polarMinus x w = 1 := by
  decide +kernel

theorem Om_parabolic_closure {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) :
    AddSubgroup.closure {y : F6 | ∃ g ∈ Op 2 (stabilizer OmG t), ∃ x : F6,
      y = (g : F6 ≃ₗ[ZMod 2] F6) x - x} =
      AddSubgroup.closure {x : F6 | polarMinus x t = 0} := by
  rw [Op_eq_Et ht h0]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro y ⟨g, ⟨w, hw, rfl⟩, x, rfl⟩
    apply AddSubgroup.subset_closure
    show polarMinus ((eichG t w : F6 ≃ₗ[ZMod 2] F6) x - x) t = 0
    rw [eichG_apply ht hw]
    have e : x + polarMinus x t • w + (polarMinus x w + qMinus w * polarMinus x t) • t - x =
        polarMinus x t • w + (polarMinus x w + qMinus w * polarMinus x t) • t := by abel
    rw [e, polarMinus_add_left, polarMinus_smul_left, polarMinus_smul_left, polarMinus_comm w t,
      hw, polarMinus_self]
    simp
  · rw [AddSubgroup.closure_le]
    set D := AddSubgroup.closure {y : F6 | ∃ g ∈ Et t, ∃ x : F6,
      y = (g : F6 ≃ₗ[ZMod 2] F6) x - x} with hD
    have hmem : ∀ w x : F6, polarMinus t w = 0 →
        (eichG t w : F6 ≃ₗ[ZMod 2] F6) x - x ∈ D := fun w x hw =>
      AddSubgroup.subset_closure ⟨eichG t w, ⟨w, hw, rfl⟩, x, rfl⟩
    have htD : t ∈ D := by
      obtain ⟨x', w', hx', hw', hxw⟩ := omPerp_ex t ht h0
      have hw'' : polarMinus t w' = 0 := by rw [polarMinus_comm]; exact hw'
      have h := hmem w' x' hw''
      rw [eichG_apply ht hw'', hx', hxw] at h
      have e : x' + (0 : ZMod 2) • w' + (1 + qMinus w' * 0) • t - x' = t := by simp
      rw [e] at h
      exact h
    have hc : ∀ c : ZMod 2, c • t ∈ D := by
      intro c
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using htD
    intro x hx
    obtain ⟨y, hy, hty⟩ := omY_exists t ht h0
    have hx' : polarMinus t x = 0 := by rw [polarMinus_comm]; exact hx
    have hyt : polarMinus y t = 1 := by rw [polarMinus_comm]; exact hty
    have h := hmem x y hx'
    rw [eichG_apply ht hx', hyt] at h
    have e : y + (1 : ZMod 2) • x + (polarMinus y x + qMinus x * 1) • t - y =
        x + (polarMinus y x + qMinus x * 1) • t := by
      rw [one_smul]; abel
    rw [e] at h
    have : x = x + (polarMinus y x + qMinus x * 1) • t - (polarMinus y x + qMinus x * 1) • t := by
      abel
    rw [this]
    exact sub_mem h (hc _)

@[expose] def omMove (u v x : F6) : F6 :=
  x + polarMinus x u • v + (polarMinus x v + qMinus v * polarMinus x u) • u

@[expose] def omTp : Finset F6 := Finset.univ.filter fun x : F6 => polarMinus omT0 x = 0

@[expose] def omLs : Finset F6 := omTp.filter fun x : F6 => qMinus x = 0 ∧ x ≠ 0 ∧ x ≠ omT0

@[expose] def omLn : Finset F6 := omTp.filter fun x : F6 => qMinus x = 1

private theorem omTrans_s : ∀ w ∈ omLs, ∀ w' ∈ omLs, ∃ u ∈ omTp, ∃ v ∈ omTp,
    qMinus u = 0 ∧ polarMinus u v = 0 ∧ (omMove u v w = w' ∨ omMove u v w = w' + omT0) := by
  decide +kernel

private theorem omTrans_n : ∀ w ∈ omLn, ∀ w' ∈ omLn, ∃ u ∈ omTp, ∃ v ∈ omTp,
    qMinus u = 0 ∧ polarMinus u v = 0 ∧ (omMove u v w = w' ∨ omMove u v w = w' + omT0) := by
  decide +kernel

private theorem omSpan_s : ∀ x ∈ omTp, ∃ a ∈ omTp, (a = 0 ∨ a = omT0 ∨ a ∈ omLs) ∧
    ∃ b ∈ omTp, (b = 0 ∨ b = omT0 ∨ b ∈ omLs) ∧ x = a + b := by
  decide +kernel

private theorem omSpan_n : ∀ x ∈ omTp, ∃ a ∈ omTp, (a = 0 ∨ a = omT0 ∨ a ∈ omLn) ∧
    ∃ b ∈ omTp, (b = 0 ∨ b = omT0 ∨ b ∈ omLn) ∧ x = a + b := by
  decide +kernel

private theorem mem_omTp {x : F6} : x ∈ omTp ↔ polarMinus omT0 x = 0 := by
  simp [omTp]

theorem omIrr0 (S : Set F6) (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (h0 : (0 : F6) ∈ S)
    (ht : omT0 ∈ S)
    (hmov : ∀ u v : F6, polarMinus omT0 u = 0 → polarMinus omT0 v = 0 → qMinus u = 0 →
      polarMinus u v = 0 → ∀ x ∈ S, omMove u v x ∈ S)
    {w : F6} (hw : w ∈ S) (hwp : polarMinus omT0 w = 0) (hw0 : w ≠ 0) (hwt : w ≠ omT0) :
    ∀ x : F6, polarMinus omT0 x = 0 → x ∈ S := by
  have hwT : w ∈ omTp := mem_omTp.2 hwp
  have hfix : ∀ w' m : F6, m ∈ S → (m = w' ∨ m = w' + omT0) → w' ∈ S := by
    intro w' m hm h
    rcases h with rfl | rfl
    · exact hm
    · have : w' = (w' + omT0) + omT0 := by rw [add_assoc, add_self_F6, add_zero]
      rw [this]
      exact hadd _ hm _ ht
  rcases zmod2_cases (qMinus w) with hq | hq
  · have hwL : w ∈ omLs := by simp [omLs, mem_omTp, hwp, hq, hw0, hwt]
    have hL : ∀ w' ∈ omLs, w' ∈ S := by
      intro w' hw'
      obtain ⟨u, hu, v, hv, hqu, hpuv, hm⟩ := omTrans_s w hwL w' hw'
      exact hfix w' _ (hmov u v (mem_omTp.1 hu) (mem_omTp.1 hv) hqu hpuv w hw) hm
    intro x hx
    obtain ⟨a, ha, haL, b, hb, hbL, rfl⟩ := omSpan_s x (mem_omTp.2 hx)
    refine hadd _ ?_ _ ?_
    · rcases haL with rfl | rfl | h
      · exact h0
      · exact ht
      · exact hL a h
    · rcases hbL with rfl | rfl | h
      · exact h0
      · exact ht
      · exact hL b h
  · have hwL : w ∈ omLn := by simp [omLn, mem_omTp, hwp, hq]
    have hL : ∀ w' ∈ omLn, w' ∈ S := by
      intro w' hw'
      obtain ⟨u, hu, v, hv, hqu, hpuv, hm⟩ := omTrans_n w hwL w' hw'
      exact hfix w' _ (hmov u v (mem_omTp.1 hu) (mem_omTp.1 hv) hqu hpuv w hw) hm
    intro x hx
    obtain ⟨a, ha, haL, b, hb, hbL, rfl⟩ := omSpan_n x (mem_omTp.2 hx)
    refine hadd _ ?_ _ ?_
    · rcases haL with rfl | rfl | h
      · exact h0
      · exact ht
      · exact hL a h
    · rcases hbL with rfl | rfl | h
      · exact h0
      · exact ht
      · exact hL b h

theorem eichG_apply_move {u v : F6} (hu : qMinus u = 0) (hv : polarMinus u v = 0) (x : F6) :
    (eichG u v : F6 ≃ₗ[ZMod 2] F6) x = omMove u v x :=
  eichG_apply hu hv x

theorem Et_le_of_normalized {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) (W : Subgroup OmG)
    (hWE : W ≤ Et t) (hN : ∀ g ∈ stabilizer OmG t, ∀ x ∈ W, g * x * g⁻¹ ∈ W) (hW : W ≠ ⊥) :
    Et t ≤ W := by
  obtain ⟨⟨ω, hωW⟩, hω1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
  have hω1 : ω ≠ 1 := fun h => hω1' (Subtype.ext h)
  obtain ⟨w, hw, hωw'⟩ := hWE hωW
  set T : Set F6 := {x | polarMinus t x = 0 ∧ eichG t x ∈ W} with hT
  have hT0 : (0 : F6) ∈ T := ⟨polarMinus_zero_right t, by rw [eichG_zero]; exact W.one_mem⟩
  have hTt : t ∈ T := ⟨polarMinus_self t, by rw [eichG_self ht]; exact W.one_mem⟩
  have hTadd : ∀ x ∈ T, ∀ y ∈ T, x + y ∈ T := by
    rintro x ⟨hx, hxW⟩ y ⟨hy, hyW⟩
    refine ⟨by rw [polarMinus_add_right, hx, hy, add_zero], ?_⟩
    rw [← eichG_mul hx hy]
    exact W.mul_mem hxW hyW
  have hTg : ∀ g ∈ stabilizer OmG t, ∀ x ∈ T, (g : F6 ≃ₗ[ZMod 2] F6) x ∈ T := by
    rintro g hg x ⟨hx, hxW⟩
    have hgt : (g : F6 ≃ₗ[ZMod 2] F6) t = t := mem_stabilizer_vec.1 hg
    refine ⟨?_, ?_⟩
    · have := omp g t x
      rw [hgt] at this
      rw [this, hx]
    · have e := eichG_conj g t x
      rw [hgt] at e
      rw [← e]
      exact hN g hg _ hxW
  have hwT : w ∈ T := by
    refine ⟨hw, ?_⟩
    rw [← hωw']
    exact hωW
  have hw0 : w ≠ 0 := by
    intro hw0'
    rw [hw0'] at hωw'
    exact hω1 (by rw [hωw', eichG_zero])
  have hwt : w ≠ t := by
    intro hwt'
    rw [hwt'] at hωw'
    exact hω1 (by rw [hωw', eichG_self ht])
  obtain ⟨h, hh, hht⟩ := exists_mem_timmesfeldOmega_apply_eq (v := omT0) (w := t)
    (by decide) h0 (by rw [ht]; decide)
  set H : OmG := ⟨h, hh⟩ with hH
  have hHt : (H : F6 ≃ₗ[ZMod 2] F6) omT0 = t := hht
  have hall : ∀ x : F6, polarMinus omT0 x = 0 → (H : F6 ≃ₗ[ZMod 2] F6) x ∈ T := by
    refine omIrr0 {x | (H : F6 ≃ₗ[ZMod 2] F6) x ∈ T} ?_ ?_ ?_ ?_ (w := (H : F6 ≃ₗ[ZMod 2] F6).symm w) ?_ ?_ ?_ ?_
    · intro x hx y hy
      show (H : F6 ≃ₗ[ZMod 2] F6) (x + y) ∈ T
      rw [map_add]
      exact hTadd _ hx _ hy
    · show (H : F6 ≃ₗ[ZMod 2] F6) 0 ∈ T
      rw [map_zero]
      exact hT0
    · show (H : F6 ≃ₗ[ZMod 2] F6) omT0 ∈ T
      rw [hHt]
      exact hTt
    · intro u v hu hv hqu hpuv x hx
      show (H : F6 ≃ₗ[ZMod 2] F6) (omMove u v x) ∈ T
      have hu' : qMinus ((H : F6 ≃ₗ[ZMod 2] F6) u) = 0 := by rw [omq, hqu]
      have hv' : polarMinus ((H : F6 ≃ₗ[ZMod 2] F6) u) ((H : F6 ≃ₗ[ZMod 2] F6) v) = 0 := by
        rw [omp, hpuv]
      have htu : polarMinus t ((H : F6 ≃ₗ[ZMod 2] F6) u) = 0 := by
        rw [← hHt, omp, hu]
      have htv : polarMinus t ((H : F6 ≃ₗ[ZMod 2] F6) v) = 0 := by
        rw [← hHt, omp, hv]
      have hstab : eichG ((H : F6 ≃ₗ[ZMod 2] F6) u) ((H : F6 ≃ₗ[ZMod 2] F6) v) ∈
          stabilizer OmG t := by
        rw [mem_stabilizer_vec, eichG_apply_move hu' hv']
        simp only [omMove]
        rw [htu, htv]
        simp
      have key := hTg _ hstab _ hx
      have e : (eichG ((H : F6 ≃ₗ[ZMod 2] F6) u) ((H : F6 ≃ₗ[ZMod 2] F6) v) :
          F6 ≃ₗ[ZMod 2] F6) ((H : F6 ≃ₗ[ZMod 2] F6) x) =
          (H : F6 ≃ₗ[ZMod 2] F6) (omMove u v x) := by
        rw [eichG_apply_move hu' hv']
        simp only [omMove, map_add, map_smul, omp, omq]
      rw [← e]
      exact key
    · show (H : F6 ≃ₗ[ZMod 2] F6) ((H : F6 ≃ₗ[ZMod 2] F6).symm w) ∈ T
      have : (H : F6 ≃ₗ[ZMod 2] F6) (((H : F6 ≃ₗ[ZMod 2] F6).symm w)) = w :=
        (H : F6 ≃ₗ[ZMod 2] F6).apply_symm_apply w
      rw [this]
      exact hwT
    · have := omp H omT0 (((H : F6 ≃ₗ[ZMod 2] F6).symm w))
      have e : (H : F6 ≃ₗ[ZMod 2] F6) (((H : F6 ≃ₗ[ZMod 2] F6).symm w)) = w :=
        (H : F6 ≃ₗ[ZMod 2] F6).apply_symm_apply w
      rw [e, hHt] at this
      rw [← this]
      exact hw
    · intro h'
      apply hw0
      have : (H : F6 ≃ₗ[ZMod 2] F6) (((H : F6 ≃ₗ[ZMod 2] F6).symm w)) = w :=
        (H : F6 ≃ₗ[ZMod 2] F6).apply_symm_apply w
      rw [h', map_zero] at this
      exact this.symm
    · intro h'
      apply hwt
      have : (H : F6 ≃ₗ[ZMod 2] F6) (((H : F6 ≃ₗ[ZMod 2] F6).symm w)) = w :=
        (H : F6 ≃ₗ[ZMod 2] F6).apply_symm_apply w
      rw [h', hHt] at this
      exact this.symm
  rintro _ ⟨z, hz, rfl⟩
  have hz' : polarMinus omT0 ((H : F6 ≃ₗ[ZMod 2] F6).symm z) = 0 := by
    have := omp H omT0 (((H : F6 ≃ₗ[ZMod 2] F6).symm z))
    have e : (H : F6 ≃ₗ[ZMod 2] F6) (((H : F6 ≃ₗ[ZMod 2] F6).symm z)) = z :=
      (H : F6 ≃ₗ[ZMod 2] F6).apply_symm_apply z
    rw [e, hHt] at this
    rw [← this]
    exact hz
  have := hall _ hz'
  have e : (H : F6 ≃ₗ[ZMod 2] F6) (((H : F6 ≃ₗ[ZMod 2] F6).symm z)) = z :=
    (H : F6 ≃ₗ[ZMod 2] F6).apply_symm_apply z
  rw [e] at this
  exact this.2

theorem Om_parabolic_irred {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) :
    ∀ W : Subgroup OmG, W ≤ Op 2 (stabilizer OmG t) →
      stabilizer OmG t ≤ Nor W → W = ⊥ ∨ W = Op 2 (stabilizer OmG t) := by
  intro W hW hN
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    have hWE : W ≤ Et t := by rw [← Op_eq_Et ht h0]; exact hW
    refine le_antisymm hW ?_
    rw [Op_eq_Et ht h0]
    refine Et_le_of_normalized ht h0 W hWE (fun g hg x hx => ?_) hb
    exact ((Subgroup.mem_set_normalizer_iff.1 (hN hg) x).1 hx)

theorem Om_parabolic {t : F6} (ht : qMinus t = 0) (h0 : t ≠ 0) :
    IsElemAb 2 4 (Op 2 (MulAction.stabilizer OmG t)) ∧
      (∀ W : Subgroup OmG, W ≤ Op 2 (MulAction.stabilizer OmG t) →
        MulAction.stabilizer OmG t ≤ Nor W → W = ⊥ ∨ W = Op 2 (MulAction.stabilizer OmG t)) ∧
      (∀ g : OmG, (∀ x : F6, polarMinus x t = 0 → (g : F6 ≃ₗ[ZMod 2] F6) x = x) → g = 1) ∧
      AddSubgroup.closure {y : F6 | ∃ g ∈ Op 2 (MulAction.stabilizer OmG t), ∃ x : F6,
        y = (g : F6 ≃ₗ[ZMod 2] F6) x - x} = AddSubgroup.closure {x : F6 | polarMinus x t = 0} :=
  ⟨Om_parabolic_elemAb ht h0, Om_parabolic_irred ht h0, fun g hg => Om_parabolic_fix ht h0 g hg,
    Om_parabolic_closure ht h0⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
