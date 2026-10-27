module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Close

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools

theorem comm_of_isCyclic {α : Type*} [Group α] [IsCyclic α] (a b : α) : a * b = b * a := by
  letI := IsCyclic.commGroup (α := α)
  exact mul_comm a b

theorem comm_of_mem_cyclic {G : Type*} [Group G] (H : Subgroup G) [IsCyclic H] {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (comm_of_isCyclic (⟨x, hx⟩ : H) ⟨y, hy⟩)

theorem inv_conj_inv_of_conj {G : Type*} [Group G] {n s : G} (h : n * s * n⁻¹ = s⁻¹) :
    n⁻¹ * s * n = s⁻¹ := by
  have h2 : n⁻¹ * s⁻¹ * n = s := by
    rw [← h]
    group
  calc n⁻¹ * s * n = (n⁻¹ * s⁻¹ * n)⁻¹ := by group
    _ = s⁻¹ := by rw [h2]

theorem mulAut_eq_inv_of_isCyclic {S : Type} [Group S] [IsCyclic S] {a : ℕ}
    (hS : Nat.card S = 3 ^ a) {c : MulAut S} (hc2 : c * c = 1) (hc1 : c ≠ 1) (s : S) :
    c s = s⁻¹ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  have hord : orderOf g = 3 ^ a := by
    rw [← hS]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hc_sq : ∀ x, c (c x) = x := fun x => by
    have h := congrArg (fun f : MulAut S => f x) hc2
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (c g))
  have hgk : g ^ (k * k) = g := by
    have h1 := hc_sq g
    rw [← hk, map_zpow, ← hk, ← zpow_mul] at h1
    exact h1
  have hdiv : (3 : ℤ) ^ a ∣ k * k - 1 := by
    have h1 : g ^ (k * k - 1) = 1 := by
      rw [zpow_sub, zpow_one, hgk, mul_inv_cancel]
    have h2 : ((orderOf g : ℕ) : ℤ) ∣ k * k - 1 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hord] at h2
    exact_mod_cast h2
  have hsplit : (3 : ℤ) ^ a ∣ k - 1 ∨ (3 : ℤ) ^ a ∣ k + 1 := by
    have hprod : (3 : ℤ) ^ a ∣ (k - 1) * (k + 1) := by
      have e : (k - 1) * (k + 1) = k * k - 1 := by ring
      rw [e]
      exact hdiv
    by_cases hd : (3 : ℤ) ∣ k - 1
    · left
      have hnd : ¬ (3 : ℤ) ∣ k + 1 := by
        intro hd'
        have h2 : (3 : ℤ) ∣ 2 := by
          have h3 := dvd_sub hd' hd
          have e : k + 1 - (k - 1) = 2 := by ring
          rwa [e] at h3
        norm_num at h2
      have hc : IsCoprime (3 : ℤ) (k + 1) := (Int.prime_three.coprime_iff_not_dvd).2 hnd
      exact (hc.pow_left).dvd_of_dvd_mul_right hprod
    · right
      have hc : IsCoprime (3 : ℤ) (k - 1) := (Int.prime_three.coprime_iff_not_dvd).2 hd
      exact (hc.pow_left).dvd_of_dvd_mul_left hprod
  have hc_g : ∀ j : ℤ, c (g ^ j) = (c g) ^ j := fun j => map_zpow c g j
  rcases hsplit with hm | hp
  ·
    exfalso
    apply hc1
    have hcg : c g = g := by
      have h1 : g ^ (k - 1) = 1 := by
        have h2 : ((orderOf g : ℕ) : ℤ) ∣ k - 1 := by
          rw [hord]
          exact_mod_cast hm
        exact orderOf_dvd_iff_zpow_eq_one.1 h2
      rw [← hk]
      have e : g ^ k = g ^ (k - 1) * g := by
        rw [zpow_sub_one, inv_mul_cancel_right]
      rw [e, h1, one_mul]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    rw [hc_g j, hcg, MulAut.one_apply]
  ·
    have hcg : c g = g⁻¹ := by
      have h1 : g ^ (k + 1) = 1 := by
        have h2 : ((orderOf g : ℕ) : ℤ) ∣ k + 1 := by
          rw [hord]
          exact_mod_cast hp
        exact orderOf_dvd_iff_zpow_eq_one.1 h2
      rw [← hk]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← zpow_add_one]
      exact h1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg s)
    rw [hc_g j, hcg, inv_zpow]

theorem no_pgroup_quotient_of_simple_nonabelian {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p (G ⧸ N)) : N = ⊤ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    subst h
    have hG : IsPGroup p G := by
      intro g
      obtain ⟨k, hk⟩ := hN (g : G ⧸ (⊥ : Subgroup G))
      refine ⟨k, ?_⟩
      have h2 : ((g ^ p ^ k : G) : G ⧸ (⊥ : Subgroup G)) = 1 := by
        rw [QuotientGroup.mk_pow]
        exact hk
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_bot] at h2
      exact h2
    haveI := hsimple.toNontrivial
    have hc := hG.center_nontrivial
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · exact (Subgroup.nontrivial_iff_ne_bot _).1 hc hb
    · obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center G := by
        rw [ht]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  · exact h

theorem exists_inverting_normalizer {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 3 G) (hcyc : IsCyclic (S : Subgroup G))
    (hS1 : (S : Subgroup G) ≠ ⊥) :
    ∃ n ∈ normalizer (S : Set G), ∀ s ∈ (S : Subgroup G), n * s * n⁻¹ = s⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hcyc
  have hW : ∀ (N : Subgroup (S : Subgroup G)) [N.Normal],
      IsEmpty ((↥(S : Subgroup G) ⧸ N) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :=
    fun N _ => isEmpty_wreath_of_isCyclic Nat.prime_three N
  have hK : ∀ (N : Subgroup G) [N.Normal], IsPGroup 3 (G ⧸ N) → N = ⊤ :=
    fun N _ hN => no_pgroup_quotient_of_simple_nonabelian hsimple hnab N hN
  have hY := (CFSG.RankThree.Transfer.yoshida_transfer_toolkit_form G 3 Nat.prime_three S hW).2 hK
  obtain ⟨n, hn, s₀, hs₀, hns⟩ :
      ∃ n ∈ normalizer (S : Set G), ∃ s ∈ (S : Subgroup G), n * s * n⁻¹ ≠ s := by
    by_contra hcon
    push Not at hcon
    have hcomm : ⁅(S : Subgroup G), normalizer (S : Set G)⁆ ≤ ⊥ := by
      rw [commutator_le]
      intro s hs n hn
      rw [Subgroup.mem_bot, commutatorElement_def]
      have h' : n * s = s * n := mul_inv_eq_iff_eq_mul.1 (hcon n hn s hs)
      have e : s * n * s⁻¹ * n⁻¹ = (s * n) * (n * s)⁻¹ := by group
      rw [e, h', mul_inv_cancel]
    apply hS1
    rw [eq_bot_iff, hY]
    exact hcomm
  letI : MulDistribMulAction (normalizer (S : Set G)) (S : Subgroup G) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer _ _ le_rfl
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : normalizer (S : Set G) →* MulAut (S : Subgroup G),
      ρ = MulDistribMulAction.toMulAut _ _ := ⟨_, rfl⟩
  have hρapp : ∀ (a : normalizer (S : Set G)) (x : (S : Subgroup G)),
      (((ρ a) x : (S : Subgroup G)) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    intro a x
    rw [hρdef]
    rfl
  have hSN : (S : Subgroup G) ≤ normalizer (S : Set G) := Subgroup.le_normalizer
  have hkerS : (S : Subgroup G).subgroupOf (normalizer (S : Set G)) ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxS : (x : G) ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.1 hx
    refine MulEquiv.ext fun s => ?_
    rw [MulAut.one_apply]
    apply Subtype.ext
    rw [hρapp]
    have h := comm_of_mem_cyclic (S : Subgroup G) hxS s.2
    show (x : G) * (s : G) * (x : G)⁻¹ = (s : G)
    rw [h, mul_inv_cancel_right]
  obtain ⟨nn, hnn⟩ : ∃ nn : normalizer (S : Set G), (nn : G) = n := ⟨⟨n, hn⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : MulAut (S : Subgroup G), c = ρ nn := ⟨_, rfl⟩
  have hc_apply : ∀ x : (S : Subgroup G), ((c x : (S : Subgroup G)) : G) = n * (x : G) * n⁻¹ := by
    intro x
    rw [hc, hρapp, hnn]
  have hc1 : c ≠ 1 := by
    intro h
    apply hns
    have h1 := hc_apply ⟨s₀, hs₀⟩
    rw [h, MulAut.one_apply] at h1
    exact h1.symm
  obtain ⟨e, hScard⟩ : ∃ e : ℕ, Nat.card (S : Subgroup G) = 3 ^ e :=
    ⟨_, S.card_eq_multiplicity⟩
  have hcop : ¬ (3 ∣ orderOf c) := by
    intro h3
    have h1 : orderOf c = orderOf (QuotientGroup.mk nn : normalizer (S : Set G) ⧸ ρ.ker) := by
      have h0 := orderOf_injective (QuotientGroup.kerLift ρ) (QuotientGroup.kerLift_injective ρ)
        (QuotientGroup.mk nn : normalizer (S : Set G) ⧸ ρ.ker)
      rw [QuotientGroup.kerLift_mk] at h0
      rw [hc]
      exact h0
    have h2 : orderOf (QuotientGroup.mk nn : normalizer (S : Set G) ⧸ ρ.ker) ∣ ρ.ker.index :=
      _root_.orderOf_dvd_natCard _
    have h3' : ρ.ker.index ∣ ((S : Subgroup G).subgroupOf (normalizer (S : Set G))).index :=
      Subgroup.index_dvd_of_le hkerS
    have h4 : ((S : Subgroup G).subgroupOf (normalizer (S : Set G))).index ∣
        (S : Subgroup G).index := by
      rw [← Subgroup.relIndex_mul_index hSN]
      exact dvd_mul_right _ _
    rw [h1] at h3
    exact S.not_dvd_index ((h3.trans h2).trans (h3'.trans h4))
  have htot : orderOf c ∣ (Nat.card (S : Subgroup G)).totient := by
    rw [← IsCyclic.card_mulAut (S : Subgroup G)]
    exact _root_.orderOf_dvd_natCard c
  rw [hScard] at htot
  have hnt : Nontrivial (S : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hS1
  have hgt : 1 < Nat.card (S : Subgroup G) := (Finite.one_lt_card_iff_nontrivial).2 hnt
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [hScard, pow_zero] at hgt
    exact lt_irrefl _ hgt
  obtain ⟨b, rfl⟩ : ∃ b, e = b + 1 := ⟨e - 1, by omega⟩
  rw [Nat.totient_prime_pow_succ Nat.prime_three] at htot
  have hcop' : Nat.Coprime (orderOf c) (3 ^ b) :=
    Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop).symm
  have h2 : orderOf c ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_left hcop' htot
  have hc2 : c * c = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  refine ⟨n, hn, fun s hs => ?_⟩
  have h := congrArg Subtype.val (mulAut_eq_inv_of_isCyclic hScard hc2 hc1 ⟨s, hs⟩)
  rw [hc_apply] at h
  exact h

theorem exists_inverting_core {Kg : Type} [Group Kg] [Finite Kg] (U : Subgroup Kg) [U.Normal]
    (hU : Nat.Coprime 3 (Nat.card U)) (hsimple : IsSimpleGroup (Kg ⧸ U))
    (hnab : ∃ a b : Kg ⧸ U, a * b ≠ b * a) {Z : Subgroup Kg} (hZ : Nat.card Z = 3)
    (hcyc : ∀ S : Sylow 3 Kg, IsCyclic S) :
    ∃ t : Kg, ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZU : Z ⊓ U = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (H := Z) (K := U) (by rw [hZ]; exact hU)).eq_bot
  have hinj : ∀ a ∈ Z, ∀ b ∈ Z, (a : Kg ⧸ U) = (b : Kg ⧸ U) → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ Z ⊓ U := ⟨Z.mul_mem (Z.inv_mem ha) hb, QuotientGroup.eq.1 hab⟩
    rw [hZU, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hZp : IsPGroup 3 Z := IsPGroup.iff_card.2 ⟨1, by rw [hZ]; norm_num⟩
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  obtain ⟨Sb, hSbcoe⟩ : ∃ Sb : Sylow 3 (Kg ⧸ U),
      (Sb : Subgroup (Kg ⧸ U)) = (P : Subgroup Kg).map (QuotientGroup.mk' U) :=
    ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective U) P, rfl⟩
  have hSbcyc : IsCyclic (Sb : Subgroup (Kg ⧸ U)) := by
    haveI := hcyc P
    let f : (P : Subgroup Kg) →* (Sb : Subgroup (Kg ⧸ U)) :=
      { toFun := fun x => ⟨QuotientGroup.mk' U (x : Kg), by
          rw [hSbcoe]
          exact Subgroup.mem_map_of_mem _ x.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      rw [hSbcoe] at hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
    exact isCyclic_of_surjective f hf
  have hZbar : Z.map (QuotientGroup.mk' U) ≤ (Sb : Subgroup (Kg ⧸ U)) := by
    rw [hSbcoe]
    exact Subgroup.map_mono hZP
  have hZbar' : ∀ z ∈ Z, (z : Kg ⧸ U) ∈ (Sb : Subgroup (Kg ⧸ U)) := fun z hz =>
    hZbar (Subgroup.mem_map_of_mem _ hz)
  have hSb1 : (Sb : Subgroup (Kg ⧸ U)) ≠ ⊥ := by
    haveI : Nontrivial Z := (Finite.one_lt_card_iff_nontrivial).1 (by rw [hZ]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : Z)
    intro h
    have hmem := hZbar' x x.2
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : (x : Kg) = 1 := hinj _ x.2 _ Z.one_mem (by rw [hmem, QuotientGroup.mk_one])
    exact hx (Subtype.ext h1)
  have hUbot : U.map (QuotientGroup.mk' U) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    exact (QuotientGroup.eq_one_iff u).2 hu
  have hsup : ∀ x ∈ U ⊔ Z, (x : Kg ⧸ U) ∈ (Sb : Subgroup (Kg ⧸ U)) := by
    intro x hx
    have h1 : (x : Kg ⧸ U) ∈ (U ⊔ Z).map (QuotientGroup.mk' U) :=
      Subgroup.mem_map_of_mem _ hx
    rw [Subgroup.map_sup, hUbot, bot_sup_eq] at h1
    exact hZbar h1
  obtain ⟨nb, hnb, hnbS⟩ := exists_inverting_normalizer hsimple hnab Sb hSbcyc hSb1
  haveI := hSbcyc
  have hcommS : ∀ a ∈ (Sb : Subgroup (Kg ⧸ U)), ∀ b ∈ (Sb : Subgroup (Kg ⧸ U)), a * b = b * a :=
    fun a ha b hb => comm_of_mem_cyclic (Sb : Subgroup (Kg ⧸ U)) ha hb
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective nb
  have hnS : ∀ z ∈ Z, (n : Kg ⧸ U) * (z : Kg ⧸ U) * (n : Kg ⧸ U)⁻¹ = (z : Kg ⧸ U)⁻¹ := by
    intro z hz
    rw [hn]
    exact hnbS _ (hZbar' z hz)
  have hnS' : ∀ z ∈ Z, (n : Kg ⧸ U)⁻¹ * (z : Kg ⧸ U) * (n : Kg ⧸ U) = (z : Kg ⧸ U)⁻¹ := by
    intro z hz
    rw [hn]
    exact inv_conj_inv_of_conj (hnbS _ (hZbar' z hz))
  obtain ⟨Z', hZ'def⟩ : ∃ Z' : Subgroup Kg, Z' = Z.map (MulAut.conj n).toMonoidHom := ⟨_, rfl⟩
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ'def, Subgroup.card_map_of_injective (MulAut.conj n).injective, hZ]
  have hZ'le : Z' ≤ U ⊔ Z := by
    intro y hy
    rw [hZ'def] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    have hu : n * z * n⁻¹ * z ∈ U := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hnS z hz, inv_mul_cancel]
    have e : (MulAut.conj n).toMonoidHom z = (n * z * n⁻¹ * z) * z⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Z.inv_mem hz))
  have hZsyl : IsSylowOf 3 Z (U ⊔ Z) := isSylowOf_sup_of_coprime hU hZp
  have hZ'syl : IsSylowOf 3 Z' (U ⊔ Z) :=
    isSylowOf_of_card hZ'le ((hZ'card.trans hZ.symm).trans hZsyl.card_eq)
  obtain ⟨k, hkH, hk⟩ := hZ'syl.exists_mem_conj hZsyl
  refine ⟨n⁻¹ * k⁻¹, fun z hz => ?_⟩
  have hconjZ : (n⁻¹ * k⁻¹) * z * (n⁻¹ * k⁻¹)⁻¹ ∈ Z := by
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.1 (hZ'def ▸ (hk z).1 hz)
    have hz'eq' : n * z' * n⁻¹ = k⁻¹ * z * k := hz'eq
    have e : (n⁻¹ * k⁻¹) * z * (n⁻¹ * k⁻¹)⁻¹ = z' := by
      calc n⁻¹ * k⁻¹ * z * (n⁻¹ * k⁻¹)⁻¹ = n⁻¹ * (k⁻¹ * z * k) * n := by group
        _ = n⁻¹ * (n * z' * n⁻¹) * n := by rw [hz'eq']
        _ = z' := by group
    rw [e]
    exact hz'
  have hφ : (((n⁻¹ * k⁻¹) * z * (n⁻¹ * k⁻¹)⁻¹ : Kg) : Kg ⧸ U) = (z : Kg ⧸ U)⁻¹ := by
    have hkS : (k : Kg ⧸ U) ∈ (Sb : Subgroup (Kg ⧸ U)) := hsup k hkH
    have hzS : (z : Kg ⧸ U) ∈ (Sb : Subgroup (Kg ⧸ U)) := hZbar' z hz
    have hcomm : (k : Kg ⧸ U)⁻¹ * (z : Kg ⧸ U) * (k : Kg ⧸ U) = (z : Kg ⧸ U) := by
      rw [mul_assoc, hcommS _ hzS _ hkS, inv_mul_cancel_left]
    have e : (n⁻¹ * k⁻¹) * z * (n⁻¹ * k⁻¹)⁻¹ = n⁻¹ * (k⁻¹ * z * k) * n := by group
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm]
    exact hnS' z hz
  exact hinj _ hconjZ _ (Z.inv_mem hz) (by rw [hφ, QuotientGroup.mk_inv])

theorem exists_inverting_of_cyclic_sylow {p : ℕ} (hp : p = 3) {Kg : Type} [Group Kg] [Finite Kg]
    {Z : Subgroup Kg} (hZ : Nat.card Z = p)
    (hsimple : IsSimpleGroup (Kg ⧸ CFSG.pPrimeCore p Kg))
    (hnab : ∃ a b : Kg ⧸ CFSG.pPrimeCore p Kg, a * b ≠ b * a)
    (hcyc : ∀ S : Sylow p Kg, IsCyclic S) :
    ∃ t : Kg, ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹ := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 Kg).Normal := CFSG.pPrimeCore_normal
  exact exists_inverting_core (CFSG.pPrimeCore 3 Kg) CFSG.pPrimeCore_coprime_card hsimple hnab hZ
    hcyc

end CFSG.LocalAnalysis.UniquenessCase.UC6
