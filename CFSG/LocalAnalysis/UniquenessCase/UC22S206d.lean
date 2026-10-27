module

public import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

open scoped IsMulCommutative in
theorem uc22s206d_cubic {W : Type*} [Group W] [IsElementaryAbelian 2 W] (σ : W →* W)
    (h7 : ∀ w, σ (σ (σ (σ (σ (σ (σ w)))))) = w) (hfix : ∀ w, σ w = w → w = 1)
    (hirr : ∀ R : Subgroup W, (∀ r ∈ R, σ r ∈ R) → R = ⊥ ∨ R = ⊤) :
    (∀ w, σ (σ (σ w)) = w * σ w) ∨ (∀ w, σ (σ (σ w)) = w * σ (σ w)) := by
  have h2 : ∀ w : W, w * w = 1 := fun w => by
    rw [← pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have hN : ∀ w : W, w * σ w * σ (σ w) * σ (σ (σ w)) * σ (σ (σ (σ w))) *
      σ (σ (σ (σ (σ w)))) * σ (σ (σ (σ (σ (σ w))))) = 1 := by
    intro w
    apply hfix
    simp only [map_mul, h7]
    ac_rfl
  let f : W →* W :=
    { toFun := fun w => w * σ w * σ (σ (σ w))
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul]; ac_rfl }
  let g : W →* W :=
    { toFun := fun w => w * σ (σ w) * σ (σ (σ w))
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul]; ac_rfl }
  have hf : ∀ w, f w = w * σ w * σ (σ (σ w)) := fun _ => rfl
  have hg : ∀ w, g w = w * σ (σ w) * σ (σ (σ w)) := fun _ => rfl
  have hfg : ∀ w, f (g w) = 1 := by
    intro w
    rw [hf, hg]
    simp only [map_mul]
    calc _ = (w * σ w * σ (σ w) * σ (σ (σ w)) * σ (σ (σ (σ w))) * σ (σ (σ (σ (σ w)))) *
          σ (σ (σ (σ (σ (σ w)))))) * (σ (σ (σ w)) * σ (σ (σ w))) := by ac_rfl
      _ = 1 := by rw [hN, h2, one_mul]
  have hinv : ∀ r ∈ f.ker, σ r ∈ f.ker := by
    intro r hr
    rw [MonoidHom.mem_ker, hf] at hr ⊢
    have h := congrArg σ hr
    simpa only [map_mul, map_one] using h
  rcases hirr f.ker hinv with h | h
  · right
    intro w
    have hgw : g w = 1 := (MonoidHom.ker_eq_bot_iff f).mp h (by rw [hfg, map_one])
    rw [hg] at hgw
    calc σ (σ (σ w)) = (w * σ (σ w))⁻¹ := eq_inv_of_mul_eq_one_right hgw
      _ = w * σ (σ w) := inv_eq_of_mul_eq_one_right (h2 _)
  · left
    intro w
    have hfw : f w = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact mem_top w
    rw [hf] at hfw
    calc σ (σ (σ w)) = (w * σ w)⁻¹ := eq_inv_of_mul_eq_one_right hfw
      _ = w * σ w := inv_eq_of_mul_eq_one_right (h2 _)

theorem uc22s206d_closure_eq_top {W : Type*} [Group W] [IsElementaryAbelian 2 W] (σ : W →* W)
    (h7 : ∀ w, σ (σ (σ (σ (σ (σ (σ w)))))) = w) (hfix : ∀ w, σ w = w → w = 1)
    (hirr : ∀ R : Subgroup W, (∀ r ∈ R, σ r ∈ R) → R = ⊥ ∨ R = ⊤) {v : W} (hv : v ≠ 1) :
    closure ({v, σ v, σ (σ v)} : Set W) = ⊤ := by
  have hrel := uc22s206d_cubic σ h7 hfix hirr
  have hle : closure ({v, σ v, σ (σ v)} : Set W) ≤
      (closure ({v, σ v, σ (σ v)} : Set W)).comap σ := by
    rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_comap]
    rcases hx with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · rcases hrel with h | h <;> rw [h]
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  rcases hirr (closure ({v, σ v, σ (σ v)} : Set W)) (fun r hr => hle hr) with h | h
  · exfalso
    apply hv
    have hmem : v ∈ closure ({v, σ v, σ (σ v)} : Set W) := subset_closure (by simp)
    rwa [h, mem_bot] at hmem
  · exact h

theorem uc22s206d_card_sup_le {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    Nat.card ↥(H ⊔ N) ≤ Nat.card H * Nat.card N := by
  have h := Set.natCard_mul_le (s := (H : Set G)) (t := (N : Set G))
  rw [← mul_normal H N] at h
  exact h

open scoped IsMulCommutative in
theorem uc22s206d_card_le {W : Type*} [Group W] [Finite W] [Nontrivial W]
    [IsElementaryAbelian 2 W] (σ : W →* W) (h7 : ∀ w, σ (σ (σ (σ (σ (σ (σ w)))))) = w)
    (hfix : ∀ w, σ w = w → w = 1) (hirr : ∀ R : Subgroup W, (∀ r ∈ R, σ r ∈ R) → R = ⊥ ∨ R = ⊤) :
    Nat.card W ≤ 8 := by
  obtain ⟨v, hv⟩ := exists_ne (1 : W)
  have htop := uc22s206d_closure_eq_top σ h7 hfix hirr hv
  have hz : ∀ w : W, Nat.card (zpowers w) ≤ 2 := fun w => by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 W) w)
  have hle : (⊤ : Subgroup W) ≤ zpowers v ⊔ zpowers (σ v) ⊔ zpowers (σ (σ v)) := by
    rw [← htop, closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_zpowers _))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  calc Nat.card W = Nat.card (⊤ : Subgroup W) := card_top.symm
    _ ≤ Nat.card ↥(zpowers v ⊔ zpowers (σ v) ⊔ zpowers (σ (σ v))) := card_le_of_le hle
    _ ≤ Nat.card ↥(zpowers v ⊔ zpowers (σ v)) * Nat.card (zpowers (σ (σ v))) :=
        uc22s206d_card_sup_le _ _
    _ ≤ Nat.card (zpowers v) * Nat.card (zpowers (σ v)) * Nat.card (zpowers (σ (σ v))) :=
        Nat.mul_le_mul_right _ (uc22s206d_card_sup_le _ _)
    _ ≤ 2 * 2 * 2 := Nat.mul_le_mul (Nat.mul_le_mul (hz _) (hz _)) (hz _)
    _ = 8 := by norm_num

theorem uc22s206d_eq_eight {m : ℕ} (hm : ∃ n, m = 2 ^ n) (h1 : 1 < m) (h8 : m ≤ 8)
    (h7 : m ≡ 1 [MOD 7]) : m = 8 := by
  obtain ⟨n, rfl⟩ := hm
  have hn : n < 4 := by
    by_contra h
    push Not at h
    have h16 : 16 ≤ 2 ^ n :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases n <;> simp_all [Nat.ModEq]

theorem uc22s206d_comm {P : Type*} [Group P] (σ : P →* P)
    (hZ : ∀ x y : P, ⁅x, y⁆ ∈ center P) (hσ : ∀ x y : P, σ ⁅x, y⁆ = ⁅x, y⁆)
    (h2 : ∀ x y : P, ⁅x, y⁆ * ⁅x, y⁆ = 1) {a z : P} (hz : z ∈ center P)
    (hrel : σ (σ (σ a)) = a * σ a * z ∨ σ (σ (σ a)) = a * σ (σ a) * z) :
    ⁅a, σ a⁆ = 1 ∧ ⁅a, σ (σ a)⁆ = 1 := by
  have hmul : ∀ x y w : P, ⁅x, y * w⁆ = ⁅x, y⁆ * ⁅x, w⁆ := by
    intro x y w
    rw [commutatorElement_mul_right_eq, mem_center_iff.mp (hZ x w) y, mul_inv_cancel_right]
  have hcz : ∀ x : P, ⁅x, z⁆ = 1 := fun x =>
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)
  have hsw : ∀ x y : P, ⁅y, x⁆ = ⁅x, y⁆⁻¹ := fun x y => (commutatorElement_inv x y).symm
  have s1 : ⁅σ a, σ (σ a)⁆ = ⁅a, σ a⁆ := by rw [← map_commutatorElement σ, hσ]
  have s2 : ⁅σ (σ a), σ (σ (σ a))⁆ = ⁅a, σ a⁆ := by rw [← map_commutatorElement σ, s1, hσ]
  have s3 : ⁅σ a, σ (σ (σ a))⁆ = ⁅a, σ (σ a)⁆ := by rw [← map_commutatorElement σ, hσ]
  rcases hrel with h | h
  · have e1 : ⁅σ (σ a), σ (σ (σ a))⁆ = ⁅a, σ (σ a)⁆⁻¹ * ⁅a, σ a⁆⁻¹ := by
      rw [h, hmul, hmul, hcz, mul_one, hsw a, hsw (σ a) (σ (σ a)), s1]
    have h2' : ⁅a, σ (σ a)⁆ = 1 := by
      have e := e1.symm.trans s2
      rw [mul_inv_eq_iff_eq_mul, h2] at e
      exact inv_eq_one.mp e
    have e2 : ⁅σ a, σ (σ (σ a))⁆ = ⁅a, σ a⁆⁻¹ := by
      rw [h, hmul, hmul, hcz, mul_one, commutatorElement_self, mul_one, hsw a (σ a)]
    exact ⟨inv_eq_one.mp (e2.symm.trans (s3.trans h2')), h2'⟩
  · have e3 : ⁅σ a, σ (σ (σ a))⁆ = 1 := by
      rw [h, hmul, hmul, hcz, mul_one, hsw a (σ a), s1, inv_mul_cancel]
    have h2' : ⁅a, σ (σ a)⁆ = 1 := s3.symm.trans e3
    have e4 : ⁅σ (σ a), σ (σ (σ a))⁆ = ⁅a, σ (σ a)⁆⁻¹ := by
      rw [h, hmul, hmul, hcz, mul_one, commutatorElement_self, mul_one, hsw a (σ (σ a))]
    refine ⟨?_, h2'⟩
    rw [← s2, e4, h2', inv_one]

theorem uc22s206d_smul_induction {Γ X : Type*} [Group Γ] {c : Γ} (hc : IsOfFinOrder c)
    [MulAction (zpowers c) X] (p : X → Prop)
    (hp : ∀ x, p x → p ((⟨c, mem_zpowers c⟩ : zpowers c) • x)) (a : zpowers c) (x : X)
    (hx : p x) : p (a • x) := by
  have key : ∀ (n : ℕ) (x : X), p x → p (((⟨c, mem_zpowers c⟩ : zpowers c) ^ n) • x) := by
    intro n
    induction n with
    | zero => intro x hx; rwa [pow_zero, one_smul]
    | succ n ih => intro x hx; rw [pow_succ, mul_smul]; exact ih _ (hp x hx)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (hc.mem_powers_iff_mem_zpowers.mpr a.2)
  have ha : a = (⟨c, mem_zpowers c⟩ : zpowers c) ^ n :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hn.symm)
  rw [ha]
  exact key n x hx

theorem uc22s206d_eq_one {Γ X : Type*} [Group Γ] [Group X] {c : Γ} (hc : IsOfFinOrder c)
    [MulDistribMulAction (zpowers c) X] (hF : fixedPointSubgroup (zpowers c) X = ⊥) {x : X}
    (hx : (⟨c, mem_zpowers c⟩ : zpowers c) • x = x) : x = 1 := by
  have hmem : x ∈ fixedPointSubgroup (zpowers c) X := by
    intro a
    exact uc22s206d_smul_induction hc (fun y => y = x) (fun y hy => by rw [hy, hx]) a x rfl
  rwa [hF, mem_bot] at hmem

theorem uc22s206d_smul_seven {A X : Type*} [Group A] [MulAction A X] {m : A} (hm : m ^ 7 = 1)
    (x : X) : m • m • m • m • m • m • m • x = x := by
  have h : m * (m * (m * (m * (m * (m * m))))) = 1 := by
    rw [← hm]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  simp only [smul_smul, h, one_smul]

theorem uc22s206d_e8 {Γ : Type*} [Group Γ] {P₀ : Subgroup Γ} [Finite P₀] (hP₀ : IsPGroup 2 P₀)
    {c : Γ} (hc7 : c ^ 7 = 1) (hcN : c ∈ normalizer (P₀ : Set Γ))
    (hnc : ∃ g ∈ P₀, c * g * c⁻¹ ≠ g) :
    ∃ E : Subgroup Γ, E ≤ P₀ ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      c ∈ normalizer (E : Set Γ) ∧ ∀ e ∈ E, c * e * c⁻¹ = e → e = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, ⟨hSP, hcS, hSnc⟩, hSmin⟩ := (measure fun S : Subgroup Γ => Nat.card S).wf.has_min
    {S | S ≤ P₀ ∧ c ∈ normalizer (S : Set Γ) ∧ ∃ g ∈ S, c * g * c⁻¹ ≠ g}
    ⟨P₀, le_rfl, hcN, hnc⟩
  haveI : Finite S := Finite.of_injective _ (inclusion_injective hSP)
  have hSp : IsPGroup 2 S := hP₀.to_le hSP
  have hcfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨7, by norm_num, hc7⟩
  haveI : Finite (zpowers c) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hcfin.orderOf_pos.ne')
  have hA : ¬ 2 ∣ Nat.card (zpowers c) := by
    rw [Nat.card_zpowers]
    exact fun h => (by decide : ¬ 2 ∣ 7) (h.trans (orderOf_dvd_of_pow_eq_one hc7))
  have hcop : Nat.Coprime (Nat.card (zpowers c)) (Nat.card S) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
    rw [hk]
    exact Nat.Coprime.pow_right k
      ((Nat.coprime_comm).mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hA))
  have hAS : zpowers c ≤ normalizer (S : Set Γ) := zpowers_le.mpr hcS
  letI : MulDistribMulAction (zpowers c) S := MulDistribMulAction.compHom S (inclusion hAS)
  set c' : zpowers c := ⟨c, mem_zpowers c⟩ with hc'
  have hc'7 : c' ^ 7 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hc7)
  have hnt : ∃ (a : zpowers c) (q : S), a • q ≠ q := by
    obtain ⟨g, hg, hgc⟩ := hSnc
    exact ⟨c', ⟨g, hg⟩, fun h => hgc (congrArg Subtype.val h)⟩
  have hmin : ∀ R : Subgroup S, R ≠ ⊤ → (∀ (a : zpowers c), ∀ r ∈ R, a • r ∈ R) →
      ∀ (a : zpowers c), ∀ r ∈ R, a • r = r := by
    intro R hR hinv
    by_contra hcon
    push Not at hcon
    obtain ⟨a, r, hr, har⟩ := hcon
    refine hSmin (R.map S.subtype) ⟨?_, ?_, ?_⟩ ?_
    · rintro _ ⟨s, -, rfl⟩
      exact hSP s.2
    · rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨c' • s, hinv c' s hs, rfl⟩
      · rintro ⟨s, hs, hseq⟩
        refine ⟨c'⁻¹ • s, hinv c'⁻¹ s hs, ?_⟩
        have hs' : (s : Γ) = c * h * c⁻¹ := hseq
        show c⁻¹ * (s : Γ) * c⁻¹⁻¹ = h
        rw [hs']
        group
    · by_contra hall
      push Not at hall
      apply har
      have hfix : c' • r = r := Subtype.ext (hall _ ⟨r, hr, rfl⟩)
      exact uc22s206d_smul_induction hcfin (fun x => x = r) (fun x hx => by rw [hx, hfix]) a r rfl
    · show Nat.card ↥(R.map S.subtype) < Nat.card S
      rw [card_map_of_injective S.subtype_injective]
      exact lt_of_le_of_ne (card_le_card_group R) (fun h => hR ((card_eq_iff_eq_top R).mp h))
  obtain ⟨htop, -, ⟨hWnt, hWel, -, hWirr⟩, habel, hnab⟩ :=
    minimal_coprime_action_elementary_or_special (l := 2) hSp hA hnt hmin
  by_cases hab : IsMulCommutative S
  ·
    obtain ⟨-, hel⟩ := habel hab
    have hF : fixedPointSubgroup (zpowers c) S = ⊥ := by
      have h :=
        isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
          (A := zpowers c) (G := S) (by rw [htop, sup_top_eq]) hcop hab
      rw [htop] at h
      simpa using h.inf_eq_bot
    have hfixS : ∀ s : S, c' • s = s → s = 1 := fun s hs => uc22s206d_eq_one hcfin hF hs
    have hirrS : ∀ R : Subgroup S, (∀ r ∈ R, c' • r ∈ R) → R = ⊥ ∨ R = ⊤ := by
      intro R hR
      by_cases hRt : R = ⊤
      · exact Or.inr hRt
      · left
        have hRfix := hmin R hRt (fun a r hr => uc22s206d_smul_induction hcfin (· ∈ R) hR a r hr)
        rw [eq_bot_iff]
        intro r hr
        rw [mem_bot]
        exact hfixS r (hRfix c' r hr)
    haveI : IsElementaryAbelian 2 S := hel
    haveI : Nontrivial S := by
      obtain ⟨g, hg, hgc⟩ := hSnc
      refine ⟨⟨⟨g, hg⟩, 1, fun h => hgc ?_⟩⟩
      have hg1 : g = 1 := congrArg Subtype.val h
      rw [hg1, mul_one, mul_inv_cancel]
    have hle : Nat.card S ≤ 8 := uc22s206d_card_le (MulDistribMulAction.toMonoidHom S c')
      (fun w => uc22s206d_smul_seven hc'7 w) hfixS hirrS
    have h7p : IsPGroup 7 (zpowers c) := by
      intro a
      obtain ⟨n, hn⟩ :=
        (Submonoid.mem_powers_iff _ _).mp (hcfin.mem_powers_iff_mem_zpowers.mpr a.2)
      refine ⟨1, Subtype.ext ?_⟩
      have h1 : (a : Γ) ^ 7 = 1 := by rw [← hn, ← pow_mul, mul_comm, pow_mul, hc7, one_pow]
      simpa using h1
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hmod := h7p.card_modEq_card_fixedPoints S
    have hfp : MulAction.fixedPoints (zpowers c) S = {1} := by
      ext s
      constructor
      · intro hs
        exact hfixS s (MulAction.mem_fixedPoints.mp hs c')
      · intro hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact MulAction.mem_fixedPoints.mpr fun a => smul_one a
    have hone : Nat.card ↥({1} : Set S) = 1 := Nat.card_unique
    rw [hfp, hone] at hmod
    have hcard : Nat.card S = 8 :=
      uc22s206d_eq_eight (IsPGroup.iff_card.mp hSp) Finite.one_lt_card hle hmod
    refine ⟨S, hSP, ⟨hab, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩, hcard, hcS,
      fun e he hce => ?_⟩
    exact congrArg Subtype.val (hfixS ⟨e, he⟩ (Subtype.ext hce))
  ·
    exfalso
    obtain ⟨hcF, hFZ, -, hcel, hZfix⟩ := hnab hab
    letI := frattiniQuotientAction (zpowers c) S
    haveI : Nontrivial (S ⧸ frattini S) := hWnt
    haveI : IsElementaryAbelian 2 (S ⧸ frattini S) := hWel
    have hFinv : CFSG.IsInvariant (zpowers c) S (frattini S) :=
      isInvariant_of_characteristic _
    have hWF := fixedPointSubgroup_quotient_eq_bot hcop htop (frattini S) hFinv
      hWel.toIsMulCommutative
    change fixedPointSubgroup (zpowers c) (S ⧸ frattini S) = ⊥ at hWF
    have hfixW : ∀ w : S ⧸ frattini S, c' • w = w → w = 1 := fun w hw =>
      uc22s206d_eq_one hcfin hWF hw
    have hirrW : ∀ R : Subgroup (S ⧸ frattini S), (∀ r ∈ R, c' • r ∈ R) → R = ⊥ ∨ R = ⊤ :=
      fun R hR => hWirr R (fun a r hr => uc22s206d_smul_induction hcfin (· ∈ R) hR a r hr)
    have h7W : ∀ w : S ⧸ frattini S, c' • c' • c' • c' • c' • c' • c' • w = w :=
      fun w => uc22s206d_smul_seven hc'7 w
    have hT := uc22s206d_cubic (MulDistribMulAction.toMonoidHom (S ⧸ frattini S) c') h7W hfixW
      hirrW
    obtain ⟨w, hw⟩ := exists_ne (1 : S ⧸ frattini S)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
    have hcl := uc22s206d_closure_eq_top (MulDistribMulAction.toMonoidHom (S ⧸ frattini S) c')
      h7W hfixW hirrW hw
    have hZ : ∀ x y : S, ⁅x, y⁆ ∈ center S := fun x y => by
      rw [← hFZ, ← hcF]
      exact commutator_mem_commutator (mem_top x) (mem_top y)
    obtain ⟨z, hz, hrel⟩ : ∃ z ∈ center S, c' • c' • c' • a = a * (c' • a) * z ∨
        c' • c' • c' • a = a * (c' • c' • a) * z := by
      rcases hT with h | h
      · have h1 : ((a * (c' • a) : S) : S ⧸ frattini S) =
            ((c' • c' • c' • a : S) : S ⧸ frattini S) := (h (a : S ⧸ frattini S)).symm
        rw [QuotientGroup.eq, hFZ] at h1
        exact ⟨_, h1, Or.inl (mul_inv_cancel_left _ _).symm⟩
      · have h1 : ((a * (c' • c' • a) : S) : S ⧸ frattini S) =
            ((c' • c' • c' • a : S) : S ⧸ frattini S) := (h (a : S ⧸ frattini S)).symm
        rw [QuotientGroup.eq, hFZ] at h1
        exact ⟨_, h1, Or.inr (mul_inv_cancel_left _ _).symm⟩
    have hσZ : ∀ x y : S, c' • ⁅x, y⁆ = ⁅x, y⁆ := fun x y => hZfix c' _ (hZ x y)
    haveI : IsElementaryAbelian 2 (commutator S) := hcel
    have h2Z : ∀ x y : S, ⁅x, y⁆ * ⁅x, y⁆ = 1 := fun x y => by
      rw [← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian (A := commutator S) _
        (commutator_mem_commutator (mem_top x) (mem_top y))
    obtain ⟨hU1, hU2⟩ :=
      uc22s206d_comm (MulDistribMulAction.toMonoidHom S c') hZ hσZ h2Z hz hrel
    have hc1 : Commute a (c' • a) := commutatorElement_eq_one_iff_mul_comm.mp hU1
    have hc2 : Commute a (c' • c' • a) := commutatorElement_eq_one_iff_mul_comm.mp hU2
    have hc3 : Commute (c' • a) (c' • c' • a) := by
      have h := congrArg (c' • ·) hc1.eq
      simp only [smul_mul'] at h
      exact h
    have hpair : ({a, c' • a, c' • c' • a} : Set S).Pairwise Commute := by
      intro x hx y hy _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact Commute.refl _
        | exact hc1 | exact hc1.symm | exact hc2 | exact hc2.symm | exact hc3 | exact hc3.symm
    haveI := isMulCommutative_closure hpair
    have hmap : (closure ({a, c' • a, c' • c' • a} : Set S)).map
        (QuotientGroup.mk' (frattini S)) = ⊤ := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      exact hcl
    have hdec : ∀ x : S, ∃ t ∈ closure ({a, c' • a, c' • c' • a} : Set S), t⁻¹ * x ∈ center S := by
      intro x
      have hx : QuotientGroup.mk' (frattini S) x ∈
          (closure ({a, c' • a, c' • c' • a} : Set S)).map (QuotientGroup.mk' (frattini S)) := by
        rw [hmap]
        exact mem_top _
      obtain ⟨t, ht, htx⟩ := hx
      refine ⟨t, ht, ?_⟩
      rw [← hFZ]
      exact QuotientGroup.eq.mp htx
    apply hab
    refine ⟨⟨fun x x' => ?_⟩⟩
    obtain ⟨t, ht, hz1⟩ := hdec x
    obtain ⟨t', ht', hz2⟩ := hdec x'
    have htt : Commute t t' := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := closure ({a, c' • a, c' • c' • a} : Set S))).comm
        ⟨t, ht⟩ ⟨t', ht'⟩)
    have hzt : Commute (t⁻¹ * x) t' := (mem_center_iff.mp hz1 t').symm
    have hzz : Commute (t⁻¹ * x) (t'⁻¹ * x') := (mem_center_iff.mp hz1 _).symm
    have htz : Commute t (t'⁻¹ * x') := mem_center_iff.mp hz2 t
    have hcomm : Commute (t * (t⁻¹ * x)) (t' * (t'⁻¹ * x')) :=
      (htt.mul_right htz).mul_left (hzt.mul_right hzz)
    simp only [mul_inv_cancel_left] at hcomm
    exact hcomm

theorem uc22s206d_section {K Q : Type*} [Group K] [Finite K] [Group Q] (β : K →* Q)
    (hβ : Function.Surjective β) (hβ2 : IsPGroup 2 β.ker) (X₀ : Subgroup Q)
    (hX₀ : Odd (Nat.card X₀)) : ∃ s : X₀ →* K, ∀ q : X₀, β (s q) = q := by
  classical
  set φ : X₀.comap β →* X₀ := β.subgroupComap X₀ with hφdef
  have hφ : Function.Surjective φ := β.subgroupComap_surjective X₀ hβ
  have hker : IsPGroup 2 φ.ker := by
    intro g
    have h1 : φ g = 1 := MonoidHom.mem_ker.mp g.2
    have hg : ((g : X₀.comap β) : K) ∈ β.ker := MonoidHom.mem_ker.mpr (congrArg Subtype.val h1)
    obtain ⟨n, hn⟩ := hβ2 ⟨_, hg⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hcop : Nat.Coprime (Nat.card φ.ker) φ.ker.index := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hφ, card_top]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hX₀)
  obtain ⟨H, hH⟩ := exists_right_complement'_of_coprime hcop
  have hbij : Function.Bijective (φ.comp H.subtype) := by
    refine ⟨?_, fun q => ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro h hh
      have h2 : (h : X₀.comap β) ∈ φ.ker ⊓ H := ⟨hh, h.2⟩
      rw [hH.disjoint.eq_bot, mem_bot] at h2
      exact mem_bot.mpr (Subtype.ext h2)
    · obtain ⟨g, rfl⟩ := hφ q
      obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 g
      refine ⟨h, ?_⟩
      have hn1 : φ n = 1 := MonoidHom.mem_ker.mp n.2
      simp only at hnh
      rw [MonoidHom.comp_apply, coe_subtype, ← hnh, map_mul, hn1, one_mul]
  refine ⟨((X₀.comap β).subtype.comp H.subtype).comp
    (MulEquiv.ofBijective _ hbij).symm.toMonoidHom, fun q => ?_⟩
  exact congrArg Subtype.val ((MulEquiv.ofBijective _ hbij).apply_symm_apply q)

theorem uc22s206d_lift {K Q Γ : Type*} [Group K] [Finite K] [Group Q] [Group Γ]
    (β : K →* Q) (hβ : Function.Surjective β) (hβ2 : IsPGroup 2 β.ker) (ρ : K →* Γ)
    (hρ : ρ.ker ≤ β.ker) {x₀ y₀ : Q} (hx₀ : orderOf x₀ = 3) (hy₀ : orderOf y₀ = 7)
    (hxy₀ : x₀ * y₀ * x₀⁻¹ = y₀ ^ 2) {E₀ : Subgroup Q} (hE₀ : IsPGroup 2 E₀)
    (hyE₀ : y₀ ∈ normalizer (E₀ : Set Q)) (hnc : ∃ e ∈ E₀, y₀ * e * y₀⁻¹ ≠ e) :
    ∃ x y : K, β x = x₀ ∧ β y = y₀ ∧ orderOf x = 3 ∧ orderOf y = 7 ∧ x * y * x⁻¹ = y ^ 2 ∧
      ∃ E : Subgroup Γ, E ≤ ρ.range ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
        ρ y ∈ normalizer (E : Set Γ) ∧ ∀ e ∈ E, ρ y * e * (ρ y)⁻¹ = e → e = 1 := by
  classical
  haveI : Finite Q := Finite.of_surjective β hβ
  have hxN : zpowers x₀ ≤ normalizer (zpowers y₀ : Set Q) := by
    rw [zpowers_le]
    apply mem_normalizer_fintype
    intro n hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [← conj_zpow, hxy₀, ← zpow_natCast, ← zpow_mul]
    exact zpow_mem (mem_zpowers y₀) _
  have hX₀ : Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) = 21 := by
    have hle : Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) ≤ 21 := by
      have h := Set.natCard_mul_le (s := (zpowers y₀ : Set Q)) (t := (zpowers x₀ : Set Q))
      rw [← coe_mul_of_right_le_normalizer_left _ _ hxN] at h
      calc Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) ≤
          Nat.card (zpowers y₀) * Nat.card (zpowers x₀) := h
        _ = 21 := by rw [Nat.card_zpowers, Nat.card_zpowers, hy₀, hx₀]
    have h7 : 7 ∣ Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) := by
      have h := card_dvd_of_le (le_sup_left : zpowers y₀ ≤ zpowers y₀ ⊔ zpowers x₀)
      rwa [Nat.card_zpowers, hy₀] at h
    have h3 : 3 ∣ Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) := by
      have h := card_dvd_of_le (le_sup_right : zpowers x₀ ≤ zpowers y₀ ⊔ zpowers x₀)
      rwa [Nat.card_zpowers, hx₀] at h
    have h21 : 7 * 3 ∣ Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h7 h3
    have hpos : 0 < Nat.card ↥(zpowers y₀ ⊔ zpowers x₀) := Nat.card_pos
    have := Nat.le_of_dvd hpos h21
    omega
  obtain ⟨s, hs⟩ := uc22s206d_section β hβ hβ2 (zpowers y₀ ⊔ zpowers x₀)
    (by rw [hX₀]; exact ⟨10, rfl⟩)
  have hsinj : Function.Injective s := fun a b hab =>
    Subtype.ext (by rw [← hs a, ← hs b, hab])
  set qx : ↥(zpowers y₀ ⊔ zpowers x₀) := ⟨x₀, mem_sup_right (mem_zpowers x₀)⟩ with hqx
  set qy : ↥(zpowers y₀ ⊔ zpowers x₀) := ⟨y₀, mem_sup_left (mem_zpowers y₀)⟩ with hqy
  have hq : qx * qy * qx⁻¹ = qy ^ 2 := Subtype.ext hxy₀
  have hox : orderOf (s qx) = 3 := by rw [orderOf_injective s hsinj qx, orderOf_mk]; exact hx₀
  have hoy : orderOf (s qy) = 7 := by rw [orderOf_injective s hsinj qy, orderOf_mk]; exact hy₀
  have hy7 : s qy ^ 7 = 1 := by rw [← hoy]; exact pow_orderOf_eq_one _
  refine ⟨s qx, s qy, hs qx, hs qy, hox, hoy, ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul, hq, map_pow]
  have hP₁ : IsPGroup 2 (E₀.comap β) := hE₀.comap_of_ker_isPGroup β hβ2
  have hyP₁ : s qy ∈ normalizer ((E₀.comap β : Subgroup K) : Set K) :=
    le_normalizer_comap β (show s qy ∈ (normalizer (E₀ : Set Q)).comap β by
      rw [mem_comap, hs qy]
      exact hyE₀)
  haveI : Finite ↥((E₀.comap β).map ρ) :=
    Finite.of_surjective _ (ρ.subgroupMap_surjective (E₀.comap β))
  obtain ⟨E, hEP, hEel, hE8, hyE, hfix⟩ := uc22s206d_e8 (hP₁.map ρ) (c := ρ (s qy))
    (by rw [← map_pow, hy7, map_one]) (le_normalizer_map ρ (mem_map_of_mem ρ hyP₁)) (by
      obtain ⟨e, he, hye⟩ := hnc
      obtain ⟨k, rfl⟩ := hβ e
      refine ⟨ρ k, mem_map_of_mem ρ (show k ∈ E₀.comap β from he), fun h => hye ?_⟩
      have hk : s qy * k * (s qy)⁻¹ * k⁻¹ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel]
      have hk' := hρ hk
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs qy,
        mul_inv_eq_one] at hk'
      exact hk')
  exact ⟨E, hEP.trans (map_le_range ρ _), hEel, hE8, hyE, hfix⟩

@[expose] def uc22s206dPermY : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 4, 6, 3, 1, 7, 5]
  invFun := ![0, 5, 1, 4, 2, 7, 3, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206dPermX : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 4, 5, 6, 7, 2, 3]
  invFun := ![0, 1, 6, 7, 2, 3, 4, 5]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206dPermT1 : Equiv.Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206dPermT2 : Equiv.Perm (Fin 8) where
  toFun := ![2, 3, 0, 1, 6, 7, 4, 5]
  invFun := ![2, 3, 0, 1, 6, 7, 4, 5]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206dPermT4 : Equiv.Perm (Fin 8) where
  toFun := ![4, 5, 6, 7, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 0, 1, 2, 3]
  left_inv := by decide
  right_inv := by decide

@[expose] def uc22s206dY0 : alternatingGroup (Fin 8) :=
  ⟨uc22s206dPermY, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206dX0 : alternatingGroup (Fin 8) :=
  ⟨uc22s206dPermX, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206dT1 : alternatingGroup (Fin 8) :=
  ⟨uc22s206dPermT1, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206dT2 : alternatingGroup (Fin 8) :=
  ⟨uc22s206dPermT2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206dT4 : alternatingGroup (Fin 8) :=
  ⟨uc22s206dPermT4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def uc22s206dE0 : Subgroup (alternatingGroup (Fin 8)) :=
  closure {uc22s206dT1, uc22s206dT2, uc22s206dT4}

theorem uc22s206d_orderOf_Y0 : orderOf uc22s206dY0 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem uc22s206d_orderOf_X0 : orderOf uc22s206dX0 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem uc22s206d_conj_X0_Y0 :
    uc22s206dX0 * uc22s206dY0 * uc22s206dX0⁻¹ = uc22s206dY0 ^ 2 := by
  decide

theorem uc22s206d_isPGroup_E0 : IsPGroup 2 uc22s206dE0 := by
  have hpair : ({uc22s206dT1, uc22s206dT2, uc22s206dT4} :
      Set (alternatingGroup (Fin 8))).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rw [commute_iff_eq]
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide
  haveI := isMulCommutative_closure hpair
  have h2 : ∀ g ∈ uc22s206dE0, g ^ 2 = 1 := by
    intro g hg
    induction hg using closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hc : Commute x y := by
        have h := (IsMulCommutative.is_comm (M := closure ({uc22s206dT1, uc22s206dT2,
          uc22s206dT4} : Set (alternatingGroup (Fin 8))))).comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val h
      rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow]
  exact h2 _ g.2

theorem uc22s206d_mem_normalizer_E0 :
    uc22s206dY0 ∈ normalizer (uc22s206dE0 : Set (alternatingGroup (Fin 8))) := by
  apply mem_normalizer_fintype
  intro n hn
  have hle : uc22s206dE0 ≤ uc22s206dE0.comap (MulAut.conj uc22s206dY0).toMonoidHom := by
    rw [uc22s206dE0, closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_comap]
    show uc22s206dY0 * x * uc22s206dY0⁻¹ ∈ _
    rcases hx with rfl | rfl | rfl
    · rw [show uc22s206dY0 * uc22s206dT1 * uc22s206dY0⁻¹ = uc22s206dT2 by decide]
      exact subset_closure (by simp)
    · rw [show uc22s206dY0 * uc22s206dT2 * uc22s206dY0⁻¹ = uc22s206dT4 by decide]
      exact subset_closure (by simp)
    · rw [show uc22s206dY0 * uc22s206dT4 * uc22s206dY0⁻¹ = uc22s206dT1 * uc22s206dT2 by decide]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  exact hle hn

theorem uc22s206d_not_centralizer_E0 :
    ∃ e ∈ uc22s206dE0, uc22s206dY0 * e * uc22s206dY0⁻¹ ≠ e :=
  ⟨uc22s206dT1, subset_closure (by simp), by decide⟩

theorem uc22s206d_alt8 {K Γ : Type*} [Group K] [Finite K] [Group Γ]
    (β : K →* alternatingGroup (Fin 8)) (hβ : Function.Surjective β) (hβ2 : IsPGroup 2 β.ker)
    (ρ : K →* Γ) (hρ : ρ.ker ≤ β.ker) :
    ∃ x y : K, β x = uc22s206dX0 ∧ β y = uc22s206dY0 ∧ orderOf x = 3 ∧ orderOf y = 7 ∧
      x * y * x⁻¹ = y ^ 2 ∧ ∃ E : Subgroup Γ, E ≤ ρ.range ∧ CFSG.Open.IsElemAbelian 2 E ∧
        Nat.card E = 8 ∧ ρ y ∈ normalizer (E : Set Γ) ∧
          ∀ e ∈ E, ρ y * e * (ρ y)⁻¹ = e → e = 1 :=
  uc22s206d_lift β hβ hβ2 ρ hρ uc22s206d_orderOf_X0 uc22s206d_orderOf_Y0 uc22s206d_conj_X0_Y0
    uc22s206d_isPGroup_E0 uc22s206d_mem_normalizer_E0 uc22s206d_not_centralizer_E0

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
