module

public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.SevenThreeConclusion
import CFSG.OddTranspositions.SevenFourEight.PrimeOrder
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.Quasithin.Background.A3Structure36AQuasi
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_mul_sq_mem_of_isPGroup {X : Type*} [Group X] {Θ : Set X}
    (hΘ : IsOddTransp Θ) {P : Subgroup X} (hP : IsPGroup 2 P) {x y : X} (hx : x ∈ Θ)
    (hy : y ∈ Θ) (hxy : (x * y) ^ 2 ∈ P) : Commute x y := by
  rcases hΘ.commute_or_odd hx hy with h | hodd
  · exact h
  obtain ⟨k, hk⟩ := hP ⟨_, hxy⟩
  have hk' : (x * y) ^ 2 ^ (k + 1) = 1 := by
    have h := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h
    rw [pow_succ', pow_mul]
    exact h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases i with _ | i
  · rw [pow_zero, orderOf_eq_one_iff] at hi
    rw [← hΘ.eq_of_mul_eq_one hx hi]
  · rw [hi, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even])

theorem commute_map_of_orderOf_mul {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {x y : X} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : orderOf (x * y) ∣ 2 ∨ orderOf (x * y) = p)
    (h3 : orderOf (f x * f y) ∈ ({1, 2, 3} : Set ℕ)) : Commute (f x) (f y) := by
  have hdvd : orderOf (f x * f y) ∣ orderOf (x * y) := by
    rw [← map_mul]
    exact orderOf_map_dvd f (x * y)
  have h2 : orderOf (f x * f y) ∣ 2 := by
    rcases hxy with h | h
    · exact hdvd.trans h
    · rw [h] at hdvd
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · rw [h1]
        exact one_dvd 2
      · rcases h3 with h | h | h
        · rw [h]
          exact one_dvd 2
        · rw [h]
        · exact absurd (h1.symm.trans h) hp3
  rw [CFSG.Timmesfeld.commute_iff_mul_sq_eq_one (by rw [← map_mul, hx, map_one])
    (by rw [← map_mul, hy, map_one])]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem commute_of_closure_eq_top {Y : Type*} [Group Y] {S : Set Y}
    (hS : Subgroup.closure S = ⊤) (hc : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (a b : Y) :
    Commute a b := by
  have hZ : Subgroup.closure S ≤ Subgroup.center Y := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht s hs).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hS ▸ Subgroup.mem_top g))
  exact Subgroup.mem_center_iff.mp (hZ (hS ▸ Subgroup.mem_top b)) a

theorem not_two_dvd_index_pCore_two_commutator {X : Type} [Group X] [Finite X] {Θ : Set X}
    (hS : Setup X Θ) (hsol : Group.IsSolvable X) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpΘ : ∀ x ∈ Θ, ∀ y ∈ Θ, orderOf (x * y) ∣ 2 ∨ orderOf (x * y) = p) :
    ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator X)).index := by
  classical
  set Q := CFSG.pCore 2 X
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hodd : Odd (Nat.card ↥(commutator (X ⧸ Q))) := by
    rcases hS.subset_or_disjoint Q with hΘQ | hΘQ
    ·
      have htop : Q = ⊤ := hS.eq_top_of_subset Q hΘQ
      have hcard : Nat.card ↥(commutator (X ⧸ Q)) ∣ 1 := by
        rw [← Subgroup.index_top (G := X), ← htop, Subgroup.index_eq_card]
        exact Subgroup.card_subgroup_dvd_card _
      rw [Nat.dvd_one.mp hcard]
      exact odd_one
    ·
      obtain ⟨d₀, hd₀⟩ := hS.isClass
      have hS' : Setup (X ⧸ Q) (QuotientGroup.mk' Q '' Θ) :=
        { isClass := image_isClass_quotient hd₀ Q
          oddT := image_isOddTransp_quotient Q hS.oddT fun x hx h1 =>
            hΘQ x hx ((QuotientGroup.eq_one_iff x).mp h1)
          gen := image_closure_eq_top_quotient Q hS.gen }
      set O := CFSG.oddCore (X ⧸ Q)
      have hcomm : ∀ a b : (X ⧸ Q) ⧸ O, Commute a b := by
        rcases PartThree.sixThree hS' with h1 | h2 | h3
        ·
          refine commute_of_closure_eq_top (image_closure_eq_top_quotient O hS'.gen) ?_
          rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact commute_map_of_orderOf_mul ((QuotientGroup.mk' O).comp (QuotientGroup.mk' Q))
            hp hp3 (hS.oddT.mul_self_eq_one hx) (hS.oddT.mul_self_eq_one hy) (hpΘ x hx y hy)
            (h1 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
        ·
          have hR : (⊤ : Subgroup (X ⧸ Q)) ≤ CFSG.solvableRadical (X ⧸ Q) :=
            le_sSup ⟨inferInstance, inferInstance⟩
          intro a b
          obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective O a
          exact (Subgroup.mem_center_iff.mp
            (h2 (Subgroup.mem_map_of_mem _ (hR (Subgroup.mem_top a')))) b).symm
        ·
          have hF : CFSG.fittingSubgroup (X ⧸ Q) ≤ Subgroup.center (X ⧸ Q) := by
            refine CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore.trans ?_
            rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, bot_sup_eq]
            exact h3
          have hR : (⊤ : Subgroup (X ⧸ Q)) ≤ Subgroup.center (X ⧸ Q) :=
            (le_sSup ⟨inferInstance, inferInstance⟩ :
              (⊤ : Subgroup (X ⧸ Q)) ≤ CFSG.solvableRadical (X ⧸ Q)).trans
              (CFSG.Quasithin.A36A.solvableRadical_le_center hF)
          intro a b
          obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective O a
          obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective O b
          exact (show Commute a' b' from Subgroup.mem_center_iff.mp
            (hR (Subgroup.mem_top b')) a').map (QuotientGroup.mk' O)
      have hle : commutator (X ⧸ Q) ≤ O :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨fun a b => (hcomm a b).eq⟩⟩
      exact (CFSG.ABGLocalTools.odd_card_oddCore (H := X ⧸ Q)).of_dvd_nat
        (Subgroup.card_dvd_of_le hle)
  set ψ : ↥(commutator X) →* X ⧸ Q := (QuotientGroup.mk' Q).comp (commutator X).subtype
  have hker : ψ.ker ≤ CFSG.pCore 2 ↥(commutator X) := by
    refine le_sSup ⟨ψ.normal_ker, fun k => ?_⟩
    have hkQ : ((k : ↥(commutator X)) : X) ∈ Q :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp k.2)
    obtain ⟨n, hn⟩ := hQp ⟨_, hkQ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg Subtype.val hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h ⊢
    exact h
  have hrange : ψ.range = commutator (X ⧸ Q) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_commutator_eq, QuotientGroup.range_mk',
      commutator_def]
  have hindex : ψ.ker.index = Nat.card ↥(commutator (X ⧸ Q)) := by
    rw [Subgroup.index_ker, hrange]
  intro h2
  have h2' : 2 ∣ Nat.card ↥(commutator (X ⧸ Q)) :=
    hindex ▸ h2.trans (Subgroup.index_dvd_of_le hker)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2')

theorem alpha_eq_singleton_of_pCore_not_le (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    hC.alpha = {hC.d} := by
  classical
  have hD := hC.setup.oddT
  have hL : LocalSecond D := fun _ _ x y t _ _ _ h => hsecond x y t h
  have hW1 : ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c :=
    sixSeven hC (QZ.faithfulOnBlocks_of_localSecond hC hrad hL)
      (fun u _ v _ w h => hsecond u w v h)
  set Q := CFSG.pCore 2 ↥(Halpha D hC.alpha)
  have hconj : ∀ x ∈ DstarH hC, ∀ y ∈ DstarH hC, Commute x y → ∀ r ∈ Q,
      Commute x (r * y * r⁻¹) := by
    intro x hx y hy hxy r hr
    refine commute_of_mul_sq_mem_of_isPGroup (DstarH_isOddTransp hC) CFSG.pCore_isPGroup hx
      (DstarH_conj_mem hC hy) ?_
    have hr1 : QuotientGroup.mk' Q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    have hxy2 : (x * y) ^ 2 = 1 :=
      (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one ((DstarH_isOddTransp hC).mul_self_eq_one hx)
        ((DstarH_isOddTransp hC).mul_self_eq_one hy)).mp hxy
    have h1 : QuotientGroup.mk' Q ((x * (r * y * r⁻¹)) ^ 2) = 1 := by
      rw [map_pow, map_mul, map_mul, map_mul, map_inv, hr1, one_mul, inv_one, mul_one, ← map_mul,
        ← map_pow, hxy2, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨b, hb, q, hq, hqb⟩ : ∃ b ∈ DstarH hC, ∃ q ∈ Q, q * b * q⁻¹ ≠ b := by
    by_contra h
    push Not at h
    refine hQ fun q hq => Subgroup.mem_center_iff.mpr fun g => ?_
    have hle : Subgroup.closure (DstarH hC) ≤ Subgroup.centralizer {q} := by
      rw [Subgroup.closure_le]
      intro c hc
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      calc c * q = q * c * q⁻¹ * q := by rw [h c hc q hq]
        _ = q * c := by group
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hle (by rw [DstarH_closure_eq_top hC]; exact Subgroup.mem_top g))
  set d := q * b * q⁻¹ with hd
  have hdD : d ∈ DstarH hC := DstarH_conj_mem hC hb
  have hbd : Commute (b : G) (d : G) :=
    (hconj b hb b hb (Commute.refl b) q hq).map (Halpha D hC.alpha).subtype
  obtain ⟨β, hβ, hbβ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hb)
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ.1
  have hW1β : ∀ a ∈ g • hC.alpha, ∀ c ∈ g • hC.alpha, Commute a c → a = c := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ hac
    rw [hW1 a ha c hc ((Commute.conj_iff (ConjAct.ofConjAct g)).mp (by
      simpa only [ConjAct.smul_def] using hac))]
  have hdβ : (d : G) ∉ g • hC.alpha := fun h =>
    hqb (Subtype.ext (hW1β _ hbβ _ h hbd).symm)
  have hdβc := commute_of_mem_block hC.setup.normal hD (hC.isBlock_alpha.conj hC.setup.normal g)
    hbβ (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hdD)) hdβ hbd
  have hβb : ∀ b' ∈ g • hC.alpha, b' = (b : G) := by
    intro b' hb'
    have hb'D : b' ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hb'
    let c : Halpha D hC.alpha := ⟨b', Subgroup.subset_closure hb'D⟩
    have hcd : Commute c d := Subtype.ext (hdβc b' hb').symm.eq
    have hcb := hconj c hb'D d hdD hcd q⁻¹ (inv_mem hq)
    rw [show q⁻¹ * d * q⁻¹⁻¹ = b by rw [hd]; group] at hcb
    exact hW1β b' hb' b hbβ (hcb.map (Halpha D hC.alpha).subtype)
  ext a
  rw [Set.mem_singleton_iff]
  refine ⟨fun ha => ?_, fun ha => ha ▸ hC.d_mem_alpha⟩
  exact smul_left_cancel g ((hβb _ ⟨a, ha, rfl⟩).trans (hβb _ ⟨hC.d, hC.d_mem_alpha, rfl⟩).symm)

theorem exists_prime_pTransp_of_alpha_eq_singleton
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hα : hC.alpha = {hC.d}) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p := by
  have hL : LocalSecond D := fun _ _ x y t _ _ _ h => hsecond x y t h
  obtain ⟨p, hp, hpA⟩ := exists_prime_orderOf_eq_AalphaStar hC hsecond
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨w, hw, hw3⟩ := sevenThree hC hrad hL hpA hnot3
    exact hw3 (hpA w hw)
  refine ⟨p, hp, hp3, fun x hx y hy hxy => ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hx)
  have hy' : g⁻¹ * y * g ∈ AalphaStar D hC.alpha := by
    rw [hC.AalphaStar_eq_diff_alpha, hα]
    have hyu : ¬ Commute (g⁻¹ * y * g) hC.d := fun h => by
      have h' := (Commute.conj_iff g).mpr h
      rw [hg, show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h'
      exact hxy h'.symm
    refine ⟨⟨by simpa using hC.setup.normal g⁻¹ y hy, hyu⟩, fun h => hyu ?_⟩
    rw [Set.mem_singleton_iff.mp h]
  rw [← hpA _ hy']
  refine SemiconjBy.orderOf_eq g⁻¹ ?_
  unfold SemiconjBy
  rw [← hg]
  group

theorem orderOf_mul_DstarH_of_pTransp (hC : HypothesisC D) {p : ℕ}
    (hpD : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    {x y : Halpha D hC.alpha} (hx : x ∈ DstarH hC) (hy : y ∈ DstarH hC) :
    orderOf (x * y) ∣ 2 ∨ orderOf (x * y) = p := by
  by_cases hc : Commute x y
  · left
    rw [orderOf_dvd_iff_pow_eq_one]
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one ((DstarH_isOddTransp hC).mul_self_eq_one hx)
      ((DstarH_isOddTransp hC).mul_self_eq_one hy)).mp hc
  · right
    rw [← Subgroup.orderOf_coe]
    exact hpD _ (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx)) _
      (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy))
      fun h => hc (Subtype.ext h.eq)

theorem isSolvable_Halpha_of_pTransp (hC : HypothesisC D) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpD : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (h10 : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)) :
    Group.IsSolvable ↥(Halpha D hC.alpha) := by
  have : Group.IsSolvable ↥(CFSG.solvableRadical ↥(Halpha D hC.alpha)) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have : Group.IsSolvable (↥(Halpha D hC.alpha) ⧸ CFSG.solvableRadical ↥(Halpha D hC.alpha)) :=
    Group.isSolvable_of_comm fun a b => (commute_of_closure_eq_top (imageClass_gen hC) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact commute_map_of_orderOf_mul _ hp hp3 ((DstarH_isOddTransp hC).mul_self_eq_one hx)
        ((DstarH_isOddTransp hC).mul_self_eq_one hy) (orderOf_mul_DstarH_of_pTransp hC hpD hx hy)
        (h10 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)) a b).eq
  exact Group.isSolvable_of_subgroup_quotient (CFSG.solvableRadical ↥(Halpha D hC.alpha))

theorem sevenFive_of_pCore_not_le
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (h10 : ∀ x ∈ imageClass hC, ∀ y ∈ imageClass hC, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (hQ : ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha)) :
    hC.alpha = {hC.d} ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p) ∧
      Group.IsSolvable ↥(Halpha D hC.alpha) ∧
      ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index := by
  have hα := alpha_eq_singleton_of_pCore_not_le hC hrad hsecond hQ
  obtain ⟨p, hp, hp3, hpD⟩ := exists_prime_pTransp_of_alpha_eq_singleton hC hrad hsecond hnot3 hα
  have hsol := isSolvable_Halpha_of_pTransp hC hp hp3 hpD h10
  refine ⟨hα, ⟨p, hp, hp3, hpD⟩, hsol, ?_⟩
  exact not_two_dvd_index_pCore_two_commutator
    ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩ hsol hp hp3
    fun x hx y hy => orderOf_mul_DstarH_of_pTransp hC hpD hx hy

end CFSG.OddTranspositions

end
