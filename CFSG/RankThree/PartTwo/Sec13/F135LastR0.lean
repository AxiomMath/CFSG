module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR0Elem
public import CFSG.RankThree.PartTwo.Sec13.F135LastR0Config
public import CFSG.RankThree.PartTwo.Sec13.F135LastR0Sylow
public import CFSG.RankThree.PartTwo.Sec13.F135LastR0Action
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre
public import CFSG.RankThree.PartOne.K1214.PGroupCyclic
public import CFSG.RankThree.PartTwo.Sec13.F135LastParts

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

theorem r0_isPGroup_three {G : Type*} [Group G] {A : Subgroup G} (hA : ∀ x ∈ A, x ^ 3 = 1) :
    IsPGroup 3 A := by
  intro x
  exact ⟨1, by simpa using Subtype.ext (hA x x.2)⟩

theorem r0_le_normalizer_zpowers_of_le_centralizer {G : Type*} [Group G] {A : Subgroup G} {c : G}
    (hA : A ≤ Subgroup.centralizer ({c} : Set G)) :
    A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro a ha
  have hcomm : ∀ x ∈ Subgroup.zpowers c, x * a = a * x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hA ha)
    exact (Commute.zpow_left h.symm k).eq
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : a * h * a⁻¹ = h := by rw [← hcomm h hh, mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hx
    have e : h = a⁻¹ * (a * h * a⁻¹) * a := by group
    rw [e, mul_assoc, hcomm _ hx, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hx

theorem r0_commutator_eq_top {G : Type*} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : ⁅a, b⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem exists_abelian_sylow {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (hD : Sec13Data G A c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hcL : c ∉ L)
    (hcardAut : Nat.card (MulAut (L ⧸ aschbacherSolvableCore 3 L)) = 5040)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ Q : Sylow 3 G, (∀ x ∈ (Q : Subgroup G), ∀ y ∈ (Q : Subgroup G), x * y = y * x) ∧
      A ≤ (Q : Subgroup G) ∧
      Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  have hc3 : orderOf c = 3 := hD.orderOf_eq
  have hAexp : ∀ x ∈ A, x ^ 3 = 1 := hD.isElemAbelian.2
  have hA3 : IsPGroup 3 A := r0_isPGroup_three hAexp
  set M : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (L : Set G) with hMdef
  have hAM : A ≤ M := le_inf (r0_le_normalizer_zpowers_of_le_centralizer hD.A_le_centralizer)
    hD.le_normalizer
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQsyl, hAQ⟩ := exists_sylowOf_ge hA3 hAM
  have hQM : Q ≤ M := hQsyl.le
  have hQ3 : IsPGroup 3 Q := hQsyl.isPGroup
  have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_isPGroup_three hc3 hQ3 (hQM.trans inf_le_left)
  have hΘ : Q ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := inf_theta_eq_bot hQ3
  have hker : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
    inf_thetaQuotCentralizer_eq hD
  have hAker : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ≤ 3 := by
    rw [hker]
    exact hD.card_zpowers.le
  have hdecomp : ∀ q ∈ Q, ∃ a ∈ A, a⁻¹ * q ∈ Sec4.thetaQuotCentralizer L :=
    exists_mul_mem_thetaQuotCentralizer (inf_le_right : M ≤ _) hAQ hQM hQ3 hcardAut hD.card_eq
      hAker
  have hAsup : A = Subgroup.zpowers c ⊔ (A ⊓ L) := eq_sup_of_card_nine' hD h9 hcL
  have hcentr : ∀ r ∈ Q, r ∈ Sec4.thetaQuotCentralizer L → ∀ a ∈ A, a * r = r * a := by
    intro r hrQ hrK a ha
    have hle : A ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [hAsup]
      refine sup_le ?_ ?_
      · refine Subgroup.zpowers_le.mpr ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hQc hrQ)).symm
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commute_of_mem_thetaQuotCentralizer hΘ hb.2 (hAQ hb.1) hrQ hrK
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hcK : c ∈ Sec4.thetaQuotCentralizer L := by
    have : c ∈ A ⊓ Sec4.thetaQuotCentralizer L := by
      rw [hker]
      exact Subgroup.mem_zpowers c
    exact this.2
  have hQ₀pow : ∀ x ∈ Q, x ∈ Sec4.thetaQuotCentralizer L → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers c := by
    intro x hxQ hxK hx3
    have hxA : x ∈ A :=
      mem_of_pow_three_of_commute hD hx3 (fun a ha => hcentr x hxQ hxK a ha)
    have : x ∈ A ⊓ Sec4.thetaQuotCentralizer L := ⟨hxA, hxK⟩
    rwa [hker] at this
  have hcQ₀ : c ∈ (Q ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := ⟨hAQ hD.mem_A, hcK⟩
  have hcyc : IsCyclic (Q ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
    have hQ₀3 : IsPGroup 3 (Q ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := hQ3.to_inf_left
    refine CFSG.RankThree.PartOne.K1214.isCyclic_of_pow_eq_one_subset Nat.prime_three
      (by norm_num) hQ₀3 (b := ⟨c, hcQ₀⟩) ?_ ?_
    · rw [← Subgroup.orderOf_coe]
      exact hc3
    · intro g hg
      have hg' : (g : G) ^ 3 = 1 := by
        have := congrArg Subtype.val hg
        simpa using this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hQ₀pow g g.2.1 g.2.2 hg')
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  have hQabel : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a₁, ha₁, hr₁⟩ := hdecomp x hx
    obtain ⟨a₂, ha₂, hr₂⟩ := hdecomp y hy
    have hr₁Q : a₁⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hAQ ha₁)) hx
    have hr₂Q : a₂⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem (hAQ ha₂)) hy
    have hr : (a₁⁻¹ * x) * (a₂⁻¹ * y) = (a₂⁻¹ * y) * (a₁⁻¹ * x) := by
      haveI := hcyc
      have := (IsMulCommutative.is_comm (M := (Q ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))).comm
        (⟨a₁⁻¹ * x, hr₁Q, hr₁⟩ : (Q ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
        ⟨a₂⁻¹ * y, hr₂Q, hr₂⟩
      exact congrArg Subtype.val this
    obtain ⟨u₁, hu₁⟩ : ∃ u₁, u₁ = a₁⁻¹ * x := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ u₂, u₂ = a₂⁻¹ * y := ⟨_, rfl⟩
    rw [← hu₁] at hr hr₁Q hr₁
    rw [← hu₂] at hr hr₂Q hr₂
    have hx' : x = a₁ * u₁ := by rw [hu₁]; group
    have hy' : y = a₂ * u₂ := by rw [hu₂]; group
    have h12 : a₁ * a₂ = a₂ * a₁ := hD.commute ha₁ ha₂
    have c1 : a₂ * u₁ = u₁ * a₂ := hcentr u₁ hr₁Q hr₁ a₂ ha₂
    have c2 : a₁ * u₂ = u₂ * a₁ := hcentr u₂ hr₂Q hr₂ a₁ ha₁
    rw [hx', hy']
    calc a₁ * u₁ * (a₂ * u₂) = a₁ * (u₁ * a₂) * u₂ := by group
      _ = a₁ * (a₂ * u₁) * u₂ := by rw [c1]
      _ = (a₁ * a₂) * (u₁ * u₂) := by group
      _ = (a₂ * a₁) * (u₂ * u₁) := by rw [h12, hr]
      _ = a₂ * (a₁ * u₂) * u₁ := by group
      _ = a₂ * (u₂ * a₁) * u₁ := by rw [c2]
      _ = a₂ * u₂ * (a₁ * u₁) := by group
  have hNA : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    have key : ∀ n ∈ Subgroup.normalizer (Q : Set G), ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
      intro n hn a ha
      have hnaQ : n * a * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hn a).mp (hAQ ha)
      refine mem_of_pow_three_of_commute hD ?_ (fun a' ha' => hQabel a' (hAQ ha') _ hnaQ)
      rw [conj_pow, hAexp a ha]
      group
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => key n hn h hh
    · intro hh
      have hn' : n⁻¹ ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inv_mem _ hn
      have := key n⁻¹ hn' _ hh
      simpa [mul_assoc] using this
  have hNM : Subgroup.normalizer (Q : Set G) ≤ M :=
    hNA.trans (le_inf hW (normalizer_A_le_normalizer_L hD h9 hcL hW))
  obtain ⟨S, hS⟩ := exists_sylow_of_normalizer_le hQsyl hNM
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hS]
    exact hQabel
  · rw [hS]
    exact hAQ
  · rw [hS]
    exact hNA

theorem r0_eq_of_mem_zpowers {G : Type*} [Group G] {c x : G} (hc : orderOf c = 3)
    (hx : x ∈ Subgroup.zpowers c) (h1 : x ≠ 1) (h2 : x ≠ c⁻¹) : x = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : c ^ k = c ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hc]
    simp
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hk] at h1 h2 ⊢
  rcases h3 with h | h | h
  · rw [h] at h1
    simp at h1
  · rw [h]
    simp
  · rw [h] at h2
    exfalso
    apply h2
    have hc3 : c ^ 3 = 1 := by
      rw [← hc]
      exact pow_orderOf_eq_one c
    calc c ^ (2 : ℤ) = c ^ 3 * c⁻¹ := by group
      _ = c⁻¹ := by rw [hc3, one_mul]

theorem exists_inverter {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L) (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L)
    (hcardAut : Nat.card (MulAut (L ⧸ aschbacherSolvableCore 3 L)) = 5040)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), w * c * w⁻¹ = c⁻¹ := by
  obtain ⟨S, hab, hAS, hNA⟩ := exists_abelian_sylow hD h9 hcL hcardAut hW
  haveI : IsMulCommutative (S : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hno
  push Not at hno
  have hfix : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * c * n = c := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := Subgroup.inv_mem _ hn
    have hnW : n⁻¹ ∈ Subgroup.normalizer (A : Set G) := hNA hn'
    have hne := hno n⁻¹ hnW
    have hmem : n⁻¹ * c * n⁻¹⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hW hnW) c).mp (Subgroup.mem_zpowers c)
    have h1 : n⁻¹ * c * n⁻¹⁻¹ ≠ 1 := by
      intro h
      apply hD.ne_one
      have : c = n * 1 * n⁻¹ := by
        calc c = n * (n⁻¹ * c * n⁻¹⁻¹) * n⁻¹ := by group
          _ = n * 1 * n⁻¹ := by rw [h]
      simpa using this
    have := r0_eq_of_mem_zpowers hD.orderOf_eq hmem h1 hne
    simpa using this
  have := CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre.eq_one_of_normalizer_fixed
    (p := 3) (r0_commutator_eq_top hs hn) S c (hAS hD.mem_A) hfix
  exact hD.ne_one this

theorem r0_holds : R0 := by
  intro G _ _ A c L p C c0
  have hD := c0.data
  have hcardAut : Nat.card (MulAut (L ⧸ aschbacherSolvableCore 3 L)) = 5040 :=
    card_mulAut_of_alt7 c0.alt7
  have key : ∃ t ∈ Subgroup.normalizer (A : Set G), t ∈ Subgroup.normalizer (L : Set G) ∧
      t * c * t⁻¹ = c⁻¹ := by
    rcases c0.w_disj with hW | ⟨-, -, -, -, t, htA, htc, htL, -⟩
    · obtain ⟨w, hwA, hwc⟩ := exists_inverter hD hD.toTheoremFourHyp.isSimpleGroup
        hD.toTheoremFourHyp.nonabelian c0.card_nine c0.c_not_mem hcardAut hW
      exact ⟨w, hwA, normalizer_A_le_normalizer_L hD c0.card_nine c0.c_not_mem hW hwA, hwc⟩
    · exact ⟨t, htA, htL, htc⟩
  obtain ⟨t, htA, htL, htc⟩ := key
  obtain ⟨m, hm, n, hn⟩ := exists_odd_pow_two t
  exact ⟨{ toCfg0 := c0
           t := t ^ m
           t_mem_W := Subgroup.pow_mem _ htA m
           t_norm_L := Subgroup.pow_mem _ htL m
           t_two := ⟨n, hn⟩
           t_inv := pow_conj_inv_of_odd htc hm }⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
