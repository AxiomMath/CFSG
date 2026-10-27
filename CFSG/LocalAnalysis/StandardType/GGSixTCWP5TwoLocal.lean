module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSix

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

private lemma w6T_sq_comm_of_conj_eq_inv {G : Type*} [Group G] (ρ h : G)
    (hρh : ρ * h * ρ⁻¹ = h⁻¹) : ρ ^ 2 * h = h * ρ ^ 2 := by
  have h1 : ρ * h = h⁻¹ * ρ := by
    calc ρ * h = (ρ * h * ρ⁻¹) * ρ := by group
      _ = h⁻¹ * ρ := by rw [hρh]
  have hinv : ρ * h⁻¹ * ρ⁻¹ = h := by
    have := congrArg (fun x : G => x⁻¹) hρh
    simpa [mul_assoc] using this
  have h2 : ρ * h⁻¹ = h * ρ := by
    calc ρ * h⁻¹ = (ρ * h⁻¹ * ρ⁻¹) * ρ := by group
      _ = h * ρ := by rw [hinv]
  calc ρ ^ 2 * h = ρ * (ρ * h) := by rw [pow_two]; group
    _ = ρ * (h⁻¹ * ρ) := by rw [h1]
    _ = (ρ * h⁻¹) * ρ := by group
    _ = (h * ρ) * ρ := by rw [h2]
    _ = h * ρ ^ 2 := by rw [mul_assoc, pow_two]

private lemma w6T_even_orderOf_of_conj_eq_inv {G : Type*} [Group G] {ρ h : G}
    (hρh : ρ * h * ρ⁻¹ = h⁻¹) (hh3 : h ^ 3 = 1) (h1 : h ≠ 1) :
    Even (orderOf ρ) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hc : Commute (ρ ^ 2) h := w6T_sq_comm_of_conj_eq_inv ρ h hρh
  obtain ⟨k, hk⟩ := hodd
  have hc' : Commute ((ρ ^ 2) ^ k) h := hc.pow_left k
  have h1' : ρ * h = h⁻¹ * ρ := by
    calc ρ * h = (ρ * h * ρ⁻¹) * ρ := by group
      _ = h⁻¹ * ρ := by rw [hρh]
  have hpow2 : ρ ^ (2 * k) = (ρ ^ 2) ^ k := pow_mul ρ 2 k
  have hpow : ρ ^ orderOf ρ * h = h⁻¹ := by
    calc ρ ^ orderOf ρ * h = ρ ^ (2 * k + 1) * h := by rw [hk]
      _ = (ρ ^ (2 * k) * ρ) * h := by rw [pow_succ]
      _ = ((ρ ^ 2) ^ k * ρ) * h := by rw [hpow2]
      _ = (ρ ^ 2) ^ k * (ρ * h) := by group
      _ = (ρ ^ 2) ^ k * (h⁻¹ * ρ) := by rw [h1']
      _ = ((ρ ^ 2) ^ k * h⁻¹) * ρ := by group
      _ = (h⁻¹ * (ρ ^ 2) ^ k) * ρ := by rw [hc'.inv_right.eq]
      _ = h⁻¹ * ((ρ ^ 2) ^ k * ρ) := by group
      _ = h⁻¹ * ρ ^ (2 * k + 1) := by rw [← hpow2, ← pow_succ]
      _ = h⁻¹ * ρ ^ orderOf ρ := by rw [hk]
      _ = h⁻¹ := by rw [pow_orderOf_eq_one, mul_one]
  have hh_inv : h = h⁻¹ := by
    have := hpow
    rw [pow_orderOf_eq_one, one_mul] at this
    exact this
  have hsq : h ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hh_inv]
    exact mul_inv_cancel h
  have hone : h = 1 := by
    calc h = h ^ 3 * (h ^ 2)⁻¹ := by group
      _ = 1 := by rw [hh3, hsq, inv_one, mul_one]
  exact h1 hone


section TwoLocal

theorem exists_twoLocal_rankFive_twE6
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ E T : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      E ≤ (RecipeExcLang.twConj K σ).range ∧ T ≤ (RecipeExcLang.twConj K σ).range ∧
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (T : Set (MulAut ↥(graphFixedRootGroup TwistTag.E6 K
        σ.toRingHom))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set Ω := AlgebraicClosure K
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g₀, hg₀, hgn₀⟩ :=
    CFSG.RankThree.Classical2.exists_inv_mul_twistE6_eq (ℓ := 2) (f := n) hn hFr
      (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω
        CFSG.HardMathSupport.Lang.E6Descent.twE6W0)
  set Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    TwE6DD2.langCube hn hK σ hσ Fr hFr g₀ with hYdef
  have hYel : IsElemAbelian 3 Y := TwE6DD2.isElemAbelian_langCube hn hK σ hσ Fr hFr g₀
  have hYle : Y ≤ (RecipeExcLang.twConj K σ).range :=
    TwE6DD2.langCube_le_range hn hK σ hσ Fr hFr g₀
  have hYcard : Nat.card Y = 3 ^ 6 :=
    TwE6DD2.card_langCube hn hK σ hσ Fr hFr h3 hg₀ hgn₀
  obtain ⟨ρ, h, hρmem, hhmem, hρy, hρh, hclosure⟩ :=
    TwE6DD2.reflData_langCube hn hK σ hσ h3 Fr hFr hg₀ hgn₀
  have hex : ∃ i, h i ≠ 1 := by
    by_contra hcont
    push Not at hcont
    have hbot : Subgroup.closure (Set.range h) = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro _ ⟨i, rfl⟩
      exact hcont i
    have hcardbot : Nat.card (⊥ : Subgroup
        (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) = 1 := Subgroup.card_bot
    rw [hbot, hcardbot] at hclosure
    norm_num at hclosure
  obtain ⟨i, hi1⟩ := hex
  have hhiY : (h i) ∈ Y := hhmem i
  have hhi3 : (h i) ^ 3 = 1 := hYel.2 (h i) hhiY
  have hρi : (ρ i) * (h i) * (ρ i)⁻¹ = (h i)⁻¹ := hρh i
  have horder : orderOf (h i) = 3 := by
    have hdvd : orderOf (h i) ∣ 3 := orderOf_dvd_of_pow_eq_one hhi3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    · exact absurd (orderOf_eq_one_iff.mp h1) hi1
    · exact h3'
  let E : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    Y ⊓ Subgroup.centralizer {(ρ i)}
  have hEle : E ≤ Y := inf_le_left
  have hEel : IsElemAbelian 3 E := hYel.mono hEle
  have hκmem : ∀ y : ↥Y,
      ((ρ i) * ((y : ↥Y) : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) * (ρ i)⁻¹) *
        (((y : ↥Y) : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)))⁻¹ ∈
        Subgroup.zpowers (h i) := by
    intro y
    obtain ⟨k, hk⟩ := hρy i (y : MulAut _) y.2
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    rw [show ρ i * (y : MulAut _) * (ρ i)⁻¹ = (h i) ^ k * (y : MulAut _) from hk]
    group
  let κ : ↥Y →* Subgroup.zpowers (h i) :=
    { toFun := fun y => ⟨_, hκmem y⟩
      map_one' := by
        apply Subtype.ext
        change ((ρ i) * 1 * (ρ i)⁻¹) * 1⁻¹ = 1
        group
      map_mul' := by
        intro y z
        apply Subtype.ext
        obtain ⟨ky, hky⟩ := hρy i (y : MulAut _) y.2
        obtain ⟨kz, hkz⟩ := hρy i (z : MulAut _) z.2
        have hcommyz : (y : MulAut _) * (h i) ^ kz = (h i) ^ kz * (y : MulAut _) := by
          have hc : Commute (h i) (y : MulAut _) := hYel.comm hhiY y.2
          exact (hc.pow_left kz).eq.symm
        have hval_y : ((ρ i) * (y : MulAut _) * (ρ i)⁻¹) * (y : MulAut _)⁻¹ = (h i) ^ ky := by
          rw [hky]
          group
        have hval_z : ((ρ i) * (z : MulAut _) * (ρ i)⁻¹) * (z : MulAut _)⁻¹ = (h i) ^ kz := by
          rw [hkz]
          group
        have hval_yz : ((ρ i) * ((y * z : ↥Y) : MulAut _) * (ρ i)⁻¹) *
            (((y * z : ↥Y) : MulAut _))⁻¹ = (h i) ^ (ky + kz) := by
          rw [Subgroup.coe_mul]
          calc ((ρ i) * ((y : MulAut _) * (z : MulAut _)) * (ρ i)⁻¹) *
                ((y : MulAut _) * (z : MulAut _))⁻¹
              = ((ρ i) * (y : MulAut _) * (ρ i)⁻¹) * ((ρ i) * (z : MulAut _) * (ρ i)⁻¹) *
                  ((y : MulAut _) * (z : MulAut _))⁻¹ := by group
            _ = ((h i) ^ ky * (y : MulAut _)) * ((h i) ^ kz * (z : MulAut _)) *
                  ((y : MulAut _) * (z : MulAut _))⁻¹ := by rw [hky, hkz]
            _ = (h i) ^ ky * ((y : MulAut _) * (h i) ^ kz) * (z : MulAut _) *
                  ((y : MulAut _) * (z : MulAut _))⁻¹ := by group
            _ = (h i) ^ ky * ((h i) ^ kz * (y : MulAut _)) * (z : MulAut _) *
                  ((y : MulAut _) * (z : MulAut _))⁻¹ := by rw [hcommyz]
            _ = (h i) ^ (ky + kz) := by
                  rw [pow_add]
                  group
        change ((ρ i) * ((y * z : ↥Y) : MulAut _) * (ρ i)⁻¹) *
            (((y * z : ↥Y) : MulAut _))⁻¹ =
          (((ρ i) * (y : MulAut _) * (ρ i)⁻¹) * (y : MulAut _)⁻¹) *
            (((ρ i) * (z : MulAut _) * (ρ i)⁻¹) * (z : MulAut _)⁻¹)
        rw [hval_yz, hval_y, hval_z, pow_add] }
  have hκapply : ∀ y : ↥Y, ((κ y : Subgroup.zpowers (h i)) : MulAut _) =
      (ρ i * (y : MulAut _) * (ρ i)⁻¹) * (y : MulAut _)⁻¹ := fun y => rfl
  have hmap_ker : (κ.ker).map Y.subtype = E := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      have hv : ((ρ i) * (y' : MulAut _) * (ρ i)⁻¹) * (y' : MulAut _)⁻¹ = 1 := by
        have hh := congrArg Subtype.val (MonoidHom.mem_ker.1 hy')
        rw [hκapply y'] at hh
        exact hh
      have hconj : (ρ i) * (y' : MulAut _) * (ρ i)⁻¹ = (y' : MulAut _) := by
        have hh := congrArg (fun x => x * (y' : MulAut _)) hv
        have hcalc : ((ρ i) * (y' : MulAut _) * (ρ i)⁻¹) * (y' : MulAut _)⁻¹ *
            (y' : MulAut _) = (ρ i) * (y' : MulAut _) * (ρ i)⁻¹ := by group
        rw [hcalc, one_mul] at hh
        exact hh
      have hmemc : (y' : MulAut _) ∈ Subgroup.centralizer {(ρ i)} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (y' : MulAut _) * (ρ i) = ((ρ i) * (y' : MulAut _) * (ρ i)⁻¹) * (ρ i) := by rw [hconj]
          _ = (ρ i) * (y' : MulAut _) := by group
      exact ⟨y'.2, hmemc⟩
    · intro hy
      have hyY : y ∈ Y := hy.1
      have hyC : y ∈ Subgroup.centralizer {(ρ i)} := hy.2
      refine ⟨⟨y, hyY⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      apply Subtype.ext
      change ((ρ i) * y * (ρ i)⁻¹) * y⁻¹ = 1
      have hc : Commute (ρ i) y := (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
      rw [hc.eq]
      group
  have hcardker : Nat.card E = Nat.card κ.ker := by
    rw [← hmap_ker, Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
  have hEcard : 3 ^ 5 ≤ Nat.card E := by
    have hkerprod := Subgroup.card_ker_mul_card_range κ
    have hrange3 : Nat.card κ.range ≤ 3 := by
      have : Finite ↥(Subgroup.zpowers (h i)) :=
        Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, horder]; norm_num)
      calc Nat.card κ.range ≤ Nat.card (⊤ : Subgroup (Subgroup.zpowers (h i))) :=
            Subgroup.card_le_of_le (le_top : κ.range ≤ ⊤)
        _ = Nat.card (Subgroup.zpowers (h i)) := Subgroup.card_top
        _ = orderOf (h i) := Nat.card_zpowers (h i)
        _ = 3 := horder
    have hle : 3 ^ 6 ≤ Nat.card κ.ker * 3 := by
      calc 3 ^ 6 = Nat.card ↥Y := hYcard.symm
        _ = Nat.card κ.ker * Nat.card κ.range := hkerprod.symm
        _ ≤ Nat.card κ.ker * 3 := Nat.mul_le_mul_left _ hrange3
    rw [hcardker]
    have hle' : 3 ^ 5 * 3 ≤ Nat.card κ.ker * 3 := by
      rwa [show 3 ^ 5 * 3 = 3 ^ 6 by norm_num]
    exact Nat.le_of_mul_le_mul_right hle' (by norm_num)
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (hρmem i)
  have : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by infer_instance
  have hfinρ : IsOfFinOrder (ρ i) := by
    rw [← hc]
    exact MonoidHom.isOfFinOrder (MulAut.conj : _ →* _) (isOfFinOrder_of_finite c)
  have hordne : orderOf (ρ i) ≠ 0 := orderOf_ne_zero_iff.mpr hfinρ
  have heven : Even (orderOf (ρ i)) := w6T_even_orderOf_of_conj_eq_inv hρi hhi3 hi1
  have htwodvd : 2 ∣ orderOf (ρ i) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by rw [hk, two_mul]⟩
  let t : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (ρ i) ^ (orderOf (ρ i) / 2)
  have htorder : orderOf t = 2 := orderOf_pow_orderOf_div hordne htwodvd
  let T : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    Subgroup.zpowers t
  have hTcard : Nat.card T = 2 := by
    change Nat.card (Subgroup.zpowers t) = 2
    rw [Nat.card_zpowers, htorder]
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [hTcard]; norm_num)
  have htne : t ≠ 1 := by
    intro ht
    have h1 : orderOf t = 1 := by rw [ht]; exact orderOf_one
    rw [htorder] at h1
    exact (by norm_num : (2 : ℕ) ≠ 1) h1
  have hTne : T ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr htne
  have hTle : T ≤ (RecipeExcLang.twConj K σ).range := by
    rw [show T = Subgroup.zpowers t from rfl, Subgroup.zpowers_le]
    have hconj_le : (MulAut.conj : (↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))).range ≤
        (RecipeExcLang.twConj K σ).range := by
      rintro x ⟨c, rfl⟩
      exact ⟨⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩,
        RecipeExcLang.twConj_of_mem_C0 σ c⟩
    exact Subgroup.pow_mem _ (hconj_le (hρmem i)) _
  have hEcent : E ≤ Subgroup.centralizer (T : Set (MulAut ↥(graphFixedRootGroup
      TwistTag.E6 K σ.toRingHom))) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hecent : Commute (ρ i) e :=
      (Subgroup.mem_centralizer_singleton_iff.mp he.2).symm
    have het : Commute e t := by
      change Commute e ((ρ i) ^ (orderOf (ρ i) / 2))
      exact hecent.symm.pow_right _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk]
    exact (het.zpow_right k).eq.symm
  have hEcent' : E ≤ Subgroup.centralizer
      (T : Set (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) := hEcent
  exact ⟨E, T, hEle.trans hYle, hTle, hEel, hEcard, hT2, hTne,
    hEcent'.trans (Subgroup.centralizer_le_normalizer
      (T : Set (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))))⟩

end TwoLocal

end CFSG.StandardType.TableCRes

end
