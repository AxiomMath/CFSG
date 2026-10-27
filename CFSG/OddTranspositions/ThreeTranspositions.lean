module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.CharacterTheory.Burnside
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Timmesfeld.Bridge.RootStructR2IrrForm

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem center_eq_bot_of_isComponent
    (hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥)
    {K : Subgroup G} (hK : IsComponent K) : Subgroup.center K = ⊥ := by
  have hle := CFSG.LocalCores.center_component_le_center_layer hK
  have hmap : (Subgroup.center K).map K.subtype = ⊥ := by
    refine le_bot_iff.mp (hle.trans ?_)
    rw [hZmap]
  rw [eq_bot_iff]
  intro z hz
  have hmem : (z : G) ∈ (Subgroup.center K).map K.subtype := ⟨z, hz, rfl⟩
  rw [hmap] at hmem
  have hz1 : z = 1 := by
    simpa using hmem
  exact hz1

private theorem isSimpleGroup_of_isComponent
    (hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥)
    {K : Subgroup G} (hK : IsComponent K) : IsSimpleGroup K := by
  have hKZ := center_eq_bot_of_isComponent hZmap hK
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2.1
  have e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hKZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

private theorem map_conj_eq_self_of_isComponent
    (hP : Pair G D)
    (hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥)
    {K : Subgroup G} (hK : IsComponent K) {d : G} (hd : d ∈ D) :
    K.map (MulAut.conj d).toMonoidHom = K := by
  classical
  by_contra hne
  let L : Subgroup G := K.map (MulAut.conj d).toMonoidHom
  have hL : IsComponent L :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d) hK
  have hLne : L ≠ K := hne
  have hKq : IsQuasisimple K := hK.1
  have hKZ : Subgroup.center K = ⊥ := center_eq_bot_of_isComponent hZmap hK
  have hKLcomm : ⁅K, L⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
    · exact absurd h.symm hLne
    · exact h
  have hKinfL : K ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzK : z ∈ K := hz.1
    have hzcenter : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hcomm : z * (k : G) = (k : G) * z :=
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKLcomm k.2) z hz.2
      simpa using hcomm.symm
    rw [hKZ] at hzcenter
    have hz1 : (⟨z, hzK⟩ : K) = 1 := by simpa using hzcenter
    simpa using congrArg Subtype.val hz1
  have hnoPrime : ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card K := by
    intro p hp hp3 hdvd
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := K) p hdvd
    let xG : G := (x : G)
    have hxGord : orderOf xG = p := by
      change orderOf (x : G) = p
      rw [Subgroup.orderOf_coe, hxord]
    let C : G := MulAut.conj d (xG⁻¹)
    have hCord : orderOf C = p := by
      rw [show C = MulAut.conj d (xG⁻¹) from rfl, MulEquiv.orderOf_eq, orderOf_inv, hxGord]
    have hCK : C ∈ L := by
      refine Subgroup.mem_map.mpr ⟨xG⁻¹, K.inv_mem x.2, ?_⟩
      rfl
    have hxK : xG ∈ K := x.2
    have hcomm : Commute C xG := by
      have hx : xG ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKLcomm hxK
      exact (Subgroup.mem_centralizer_iff.mp hx C hCK)
    have hdunit : d⁻¹ = d := inv_eq_of_mul_eq_one_right (Pair.mul_self hP hd)
    have hCx_eq : C * xG = d * MulAut.conj (xG⁻¹) d := by
      simp [C, MulAut.conj_apply, hdunit, mul_assoc]
    have hmem : orderOf (C * xG) ∈ ({1, 2, 3} : Set ℕ) := by
      rw [hCx_eq]
      exact hP.2.2.2.1 d hd _ (Pair.conj_mem hP hd (xG⁻¹))
    have hdiv : orderOf (C * xG) ∣ p := by
      have h := Commute.orderOf_mul_dvd_lcm hcomm
      rwa [hCord, hxGord, Nat.lcm_self] at h
    rcases (Nat.dvd_prime hp).mp hdiv with h1 | hp'
    · have hCx1 : C * xG = 1 := orderOf_eq_one_iff.mp h1
      have hCeq : C = xG⁻¹ := by
        calc C = (C⁻¹)⁻¹ := (inv_inv C).symm
          _ = xG⁻¹ := by rw [inv_eq_of_mul_eq_one_right hCx1]
      have hCK' : C ∈ K := by
        rw [hCeq]
        exact K.inv_mem hxK
      have hCbot : C = 1 := by
        have hmemKL : C ∈ K ⊓ L := ⟨hCK', hCK⟩
        rw [hKinfL] at hmemKL
        simpa using hmemKL
      rw [hCbot, orderOf_one] at hCord
      omega
    · have hp_mem : p ∈ ({1, 2, 3} : Set ℕ) := by
        simpa [hp'] using hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp_mem
      omega
  have hsupp : (Nat.card K).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hp3 : p ≤ 3 := by
      by_contra h
      exact hnoPrime p hpp (by omega) hdvd
    have hp2 := hpp.two_le
    interval_cases p <;> simp
  have hcard :
      Nat.card K = 2 ^ (Nat.card K).factorization 2 * 3 ^ (Nat.card K).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self Nat.card_pos.ne']
    rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _]
    simp
  letI : Fintype K := Fintype.ofFinite K
  have hsolvK : Group.IsSolvable K :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hKnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hKperf : Group.IsPerfect K := hKq.1
  exact (Group.IsPerfect.not_isSolvable K) hsolvK

private theorem normal_of_isComponent
    (hP : Pair G D)
    (hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥)
    {K : Subgroup G} (hK : IsComponent K) : K.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
  intro d hd
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  simpa using map_conj_eq_self_of_isComponent hP hZmap hK hd

private theorem not_forall_commute_of_isComponent
    (hP : Pair G D) (hcenter : Subgroup.center G = ⊥)
    {K : Subgroup G} (hK : IsComponent K) (hKn : K.Normal) {d : G} (hd : d ∈ D) :
    ¬ ∀ k ∈ K, Commute d k := by
  intro hcen
  have hDcentral : ∀ e ∈ D, ∀ k ∈ K, Commute e k := by
    intro e he k hk
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
    have hkg : g⁻¹ * k * g ∈ K := by
      simpa using hKn.conj_mem k hk g⁻¹
    have hcomm := (hcen (g⁻¹ * k * g) hkg).conj g
    have hx : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
    rw [hx] at hcomm
    exact hcomm
  have htop : Subgroup.centralizer (K : Set G) = ⊤ := by
    rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
    intro e he
    change e ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hDcentral e he k hk).symm.eq
  have hKleZ : K ≤ Subgroup.center G := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (K : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg k hk).symm
  have hKnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).mp hKnt
  exact hKne (le_bot_iff.mp (hcenter ▸ hKleZ))

private theorem exists_commuting_conj_of_isComponent
    (hP : Pair G D)
    (hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥)
    {K : Subgroup G} (hK : IsComponent K) (hKn : K.Normal)
    {d : G} (hd : d ∈ D)
    (hnotcen : ¬ ∀ k ∈ K, Commute d k) :
    ∃ x ∈ K, MulAut.conj x d ≠ d ∧ Commute d (MulAut.conj x d) := by
  classical
  by_contra hcon
  have hno : ∀ x ∈ K, Commute d (MulAut.conj x d) → MulAut.conj x d = d := by
    intro x hx hxc
    by_contra hne
    exact hcon ⟨x, hx, hne, hxc⟩
  haveI : K.Normal := hKn
  let H : Subgroup G := K ⊔ Subgroup.zpowers d
  have hdHmem : d ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  let dH : H := ⟨d, hdHmem⟩
  have hdH1 : dH ≠ 1 := by
    intro h
    exact Pair.ne_one hP hd (by simpa [dH] using congrArg Subtype.val h)
  have hdH2 : dH * dH = 1 := by
    apply Subtype.ext
    simp [dH, Pair.mul_self hP hd]
  have hzpow : ∀ z ∈ Subgroup.zpowers dH, z = 1 ∨ z = dH := by
    intro z hz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hmod := zpow_mod_orderOf dH n
    have hdHord : orderOf dH = 2 := by
      rw [Subgroup.orderOf_mk, Pair.orderOf_eq_two hP hd]
    rw [hdHord] at hmod
    have hmod' : dH ^ (n % 2) = dH ^ n := by simpa using hmod
    rw [← hn]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      rw [← hmod', h0]; simp
    · right
      rw [← hmod', h1]; simp
  have hiso : ∀ g : H, (g * dH * g⁻¹) * dH = dH * (g * dH * g⁻¹) →
      g * dH * g⁻¹ = dH := by
    intro g hcomm
    obtain ⟨k, hk, z, hz, hkz⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := K) (t := Subgroup.zpowers d)).mp g.2
    have hcommG : (g : G) * d * (g : G)⁻¹ * d = d * ((g : G) * d * (g : G)⁻¹) := by
      simpa using congrArg Subtype.val hcomm
    have hdunit : d⁻¹ = d := inv_eq_of_mul_eq_one_right (Pair.mul_self hP hd)
    have hzpowG : ∀ z ∈ Subgroup.zpowers d, z = 1 ∨ z = d := by
      intro z hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hmod := zpow_mod_orderOf d n
      have hdord : orderOf d = 2 := Pair.orderOf_eq_two hP hd
      rw [hdord] at hmod
      have hmod' : d ^ (n % 2) = d ^ n := by simpa using hmod
      rw [← hn]
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · left
        rw [← hmod', h0]; simp
      · right
        rw [← hmod', h1]; simp
    have hconjk : (g : G) * d * (g : G)⁻¹ = k * d * k⁻¹ := by
      rcases hzpowG z hz with hz1 | hz1
      · rw [hz1, mul_one] at hkz
        rw [← hkz]
      · rw [hz1] at hkz
        rw [← hkz]
        calc (k * d) * d * (k * d)⁻¹ = k * d * d * (k * d)⁻¹ := by rfl
          _ = k * d * k⁻¹ := by
            rw [mul_inv_rev, hdunit]
            calc k * d * d * (d * k⁻¹) = k * (d * d) * d * k⁻¹ := by group
              _ = k * d * k⁻¹ := by rw [Pair.mul_self hP hd]; group
    have hcommK : Commute (MulAut.conj k d) d := by
      rw [show MulAut.conj k d = k * d * k⁻¹ by rfl, ← hconjk]
      exact hcommG
    have hkd : MulAut.conj k d = d := hno k hk hcommK.symm
    apply Subtype.ext
    change (g : G) * d * (g : G)⁻¹ = d
    rw [hconjk]
    simpa [MulAut.conj_apply] using hkd
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨N, hNn, hNodd, hN⟩ :=
    CFSG.ZStar.glauberman_zStar H dH hdH1 hdH2 hiso
  let KH : Subgroup H := K.subgroupOf H
  have hKHnormal : KH.Normal := by
    dsimp [KH]
    infer_instance
  have hKHsimple : IsSimpleGroup KH := by
    haveI : IsSimpleGroup K := isSimpleGroup_of_isComponent hZmap hK
    dsimp [KH]
    exact (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ H)).isSimpleGroup
  let M : Subgroup H := ⁅KH, Subgroup.zpowers dH⁆
  have hMleK : M ≤ KH := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases hzpow b hb with rfl | rfl
    · simp
    · have hamem : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
      have hda : d * (a : G)⁻¹ * d⁻¹ ∈ K := by
        have hmap := map_conj_eq_self_of_isComponent hP hZmap hK hd
        have hmem : MulAut.conj d ((a : G)⁻¹) ∈ K.map (MulAut.conj d).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(a : G)⁻¹, K.inv_mem hamem, rfl⟩
        rwa [hmap] at hmem
      have hdunit : d⁻¹ = d := inv_eq_of_mul_eq_one_right (Pair.mul_self hP hd)
      change ((a : G) * d * (a : G)⁻¹ * d⁻¹) ∈ K
      simpa [hdunit, mul_assoc] using K.mul_mem hamem hda
  have hMleN : M ≤ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases hzpow b hb with rfl | rfl
    · simp
    · have hdHinv : dH⁻¹ = dH := inv_eq_of_mul_eq_one_right hdH2
      have := hN a
      simpa [M, commutatorElement_def, hdHinv] using this
  have hNinter : N.subgroupOf KH = ⊥ ∨ N.subgroupOf KH = ⊤ := by
    haveI : (N.subgroupOf KH).Normal := inferInstance
    exact hKHsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf KH)
  rcases hNinter with hbot | htop
  · have hMbot : M = ⊥ := by
      apply le_bot_iff.mp
      have hdisj : Disjoint N KH := Subgroup.subgroupOf_eq_bot.mp hbot
      rw [← hdisj.eq_bot]
      exact le_inf hMleN hMleK
    have hle : KH ≤ Subgroup.centralizer (Subgroup.zpowers dH : Set H) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hMbot
    have hcenK : ∀ k ∈ K, Commute d k := by
      intro k hk
      let kH : H := ⟨k, Subgroup.mem_sup_left hk⟩
      have hkH : kH ∈ KH := hk
      have hmem := hle hkH
      have hcommH : Commute dH kH :=
        Subgroup.mem_centralizer_iff.mp hmem dH (Subgroup.mem_zpowers dH)
      exact congrArg Subtype.val hcommH.eq
    exact hnotcen hcenK
  · have hKHleN : KH ≤ N := (Subgroup.subgroupOf_eq_top.mp htop)
    have hoddKH : Odd (Nat.card KH) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hKHleN)
    have hcardKH : Nat.card KH = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ H)).toEquiv
    rw [hcardKH] at hoddKH
    have hoddK : Odd (Nat.card K) := hoddKH
    have hsolvK : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddK
    have hKnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have hKperf : Group.IsPerfect K := hK.1.1
    exact (Group.IsPerfect.not_isSolvable K) hsolvK

private theorem exists_order_three_of_isComponent
    (hP : Pair G D)
    (hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥)
    {K : Subgroup G} (hK : IsComponent K) (hKn : K.Normal)
    {d : G} (hd : d ∈ D)
    (hnotcen : ¬ ∀ k ∈ K, Commute d k) :
    ∃ y ∈ K, orderOf (d * MulAut.conj y d) = 3 := by
  classical
  by_contra hcon
  have hno3 : ∀ y ∈ K, orderOf (d * MulAut.conj y d) ≠ 3 := by
    intro y hy h3
    exact hcon ⟨y, hy, h3⟩
  haveI : K.Normal := hKn
  let H : Subgroup G := K ⊔ Subgroup.zpowers d
  have hdHmem : d ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  let dH : H := ⟨d, hdHmem⟩
  have hdH2 : dH * dH = 1 := by
    apply Subtype.ext
    simp [dH, Pair.mul_self hP hd]
  have hzpow : ∀ z ∈ Subgroup.zpowers dH, z = 1 ∨ z = dH := by
    intro z hz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hmod := zpow_mod_orderOf dH n
    have hdHord : orderOf dH = 2 := by
      rw [Subgroup.orderOf_mk, Pair.orderOf_eq_two hP hd]
    rw [hdHord] at hmod
    have hmod' : dH ^ (n % 2) = dH ^ n := by simpa using hmod
    rw [← hn]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      rw [← hmod', h0]; simp
    · right
      rw [← hmod', h1]; simp
  let KH : Subgroup H := K.subgroupOf H
  have hKHnormal : KH.Normal := by
    dsimp [KH]
    infer_instance
  have hKHsimple : IsSimpleGroup KH := by
    haveI : IsSimpleGroup K := isSimpleGroup_of_isComponent hZmap hK
    dsimp [KH]
    exact (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ H)).isSimpleGroup
  let M : Subgroup H := ⁅KH, Subgroup.zpowers dH⁆
  have hMleK : M ≤ KH := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases hzpow b hb with rfl | rfl
    · simp
    · have hamem : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
      have hda : d * (a : G)⁻¹ * d⁻¹ ∈ K := by
        have hmap := map_conj_eq_self_of_isComponent hP hZmap hK hd
        have hmem : MulAut.conj d ((a : G)⁻¹) ∈ K.map (MulAut.conj d).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(a : G)⁻¹, K.inv_mem hamem, rfl⟩
        rwa [hmap] at hmem
      have hdunit : d⁻¹ = d := inv_eq_of_mul_eq_one_right (Pair.mul_self hP hd)
      change ((a : G) * d * (a : G)⁻¹ * d⁻¹) ∈ K
      simpa [hdunit, mul_assoc] using K.mul_mem hamem hda
  have hMleC : M ≤ Subgroup.centralizer ({dH} : Set H) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases hzpow b hb with rfl | rfl
    · simp
    · have hamem : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
      let e : G := MulAut.conj (a : G) d
      have he2 : e * e = 1 := by
        change MulAut.conj (a : G) d * MulAut.conj (a : G) d = 1
        rw [← map_mul, Pair.mul_self hP hd, map_one]
      have hord : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) :=
        hP.2.2.2.1 d hd e (Pair.conj_mem hP hd (a : G))
      have hle2 : orderOf (d * e) ≤ 2 := by
        have hne : orderOf (d * e) ≠ 3 := hno3 (a : G) hamem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hord
        omega
      have hsq : (d * e) * (d * e) = 1 := by
        rcases (show orderOf (d * e) = 1 ∨ orderOf (d * e) = 2 by
          have hpos := orderOf_pos (d * e)
          omega) with h | h
        · rw [orderOf_eq_one_iff.mp h]; simp
        · rw [← pow_two, ← h, pow_orderOf_eq_one]
      have hde : d * e = e * d := by
        have h1 : e * d * e = d := by
          have h := congrArg (fun z => d * z) hsq
          have h' : d * ((d * e) * (d * e)) = d := by simpa using h
          calc e * d * e = (d * d) * e * d * e := by rw [Pair.mul_self hP hd, one_mul]
            _ = d * ((d * e) * (d * e)) := by group
            _ = d := h'
        calc d * e = (e * d * e) * e := by rw [h1]
          _ = e * d * (e * e) := by group
          _ = e * d := by rw [he2, mul_one]
      have hcommC : Commute d (d * e) := (Commute.refl d).mul_right hde
      have hcommInv : Commute d ((d * e)⁻¹) := hcommC.inv_right
      have hdunit : d⁻¹ = d := inv_eq_of_mul_eq_one_right (Pair.mul_self hP hd)
      have hcommH : Commute dH (⁅a, dH⁆) := by
        apply Subtype.ext
        change d * ((a : G) * d * (a : G)⁻¹ * d⁻¹) =
          ((a : G) * d * (a : G)⁻¹ * d⁻¹) * d
        have heq : (a : G) * d * (a : G)⁻¹ * d⁻¹ = (d * e)⁻¹ := by
          simp [e, MulAut.conj_apply, hdunit, mul_assoc]
        rw [heq]
        exact hcommInv.eq
      change ⁅a, dH⁆ ∈ Subgroup.centralizer ({dH} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommH.symm
  have hMnormSup : (M.subgroupOf (KH ⊔ Subgroup.zpowers dH)).Normal :=
    CFSG.commutator_normal_in_sup KH (Subgroup.zpowers dH)
  have hMleSup : M ≤ KH ⊔ Subgroup.zpowers dH := hMleK.trans le_sup_left
  have hKHleNorm : KH ≤ Subgroup.normalizer (M : Set H) := by
    haveI : (M.subgroupOf (KH ⊔ Subgroup.zpowers dH)).Normal := hMnormSup
    exact le_trans le_sup_left (Subgroup.le_normalizer_of_normal_subgroupOf hMleSup)
  have hMnormK : (M.subgroupOf KH).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleK).mpr hKHleNorm
  have hcases : M.subgroupOf KH = ⊥ ∨ M.subgroupOf KH = ⊤ :=
    hKHsimple.eq_bot_or_eq_top_of_normal (M.subgroupOf KH)
  have hcen_of_singleton :
      KH ≤ Subgroup.centralizer ({dH} : Set H) → ∀ k ∈ K, Commute d k := by
    intro hle k hk
    let kH : H := ⟨k, Subgroup.mem_sup_left hk⟩
    have hkH : kH ∈ KH := hk
    have hcommH : Commute kH dH :=
      Subgroup.mem_centralizer_singleton_iff.mp (hle hkH)
    exact congrArg Subtype.val hcommH.symm.eq
  rcases hcases with hbot | htop
  · have hMbot : M = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hMleK
    have hle : KH ≤ Subgroup.centralizer (Subgroup.zpowers dH : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMbot
    have hsingle : KH ≤ Subgroup.centralizer ({dH} : Set H) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' := hle hx
      have hcomm := Subgroup.mem_centralizer_iff.mp hx' dH (Subgroup.mem_zpowers dH)
      exact hcomm.symm
    exact hnotcen (hcen_of_singleton hsingle)
  · have hKHleM : KH ≤ M := Subgroup.subgroupOf_eq_top.mp htop
    exact hnotcen (hcen_of_singleton (hKHleM.trans hMleC))

theorem commutator_isSimpleGroup_of_threeTranspositions
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hEG : commutator G = layer G) :
    IsSimpleGroup (commutator G) := by
  classical
  have hP : Pair G D := ⟨inferInstance, hcls, hinv, hprod, hgen⟩
  obtain ⟨d₀, hD⟩ := hcls
  have hd₀ : d₀ ∈ D := by rw [hD]; exact IsConj.refl d₀
  have hd₀ne : d₀ ≠ 1 := Pair.ne_one hP hd₀
  have hGnt : Nontrivial G := ⟨1, d₀, fun h => hd₀ne h.symm⟩
  have hrad : CFSG.solvableRadical G = ⊥ := by
    change sSup {N : Subgroup G | N.Normal ∧ Group.IsSolvable N} = ⊥
    apply sSup_eq_bot.mpr
    rintro N ⟨hNn, hNs⟩
    exact hsolv N hNn hNs
  have hfit_le : fittingSubgroup G ≤ CFSG.solvableRadical G := by
    change sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N} ≤
      CFSG.solvableRadical G
    refine sSup_le ?_
    intro N hN
    exact le_sSup ⟨hN.1, by letI := hN.2; infer_instance⟩
  have hfitBot : fittingSubgroup G = ⊥ := by
    apply le_bot_iff.mp
    calc fittingSubgroup G ≤ CFSG.solvableRadical G := hfit_le
      _ = ⊥ := hrad
  have hgf : CFSG.generalizedFitting G ≠ ⊥ :=
    (CFSG.LocalCores.generalized_fitting_minimal_normal (G := G)).2 hGnt
  have hEne : layer G ≠ ⊥ := by
    intro hbot
    apply hgf
    rw [CFSG.generalizedFitting.eq_sup, hbot, hfitBot, sup_bot_eq]
  have hZmap : (Subgroup.center (layer G)).map (layer G).subtype = ⊥ :=
    CFSG.WholeGroup.center_layer_eq_bot_of_solvableRadical_eq_bot hrad
  have hex : ∃ K : Subgroup G, IsComponent K := by
    by_contra h
    apply hEne
    apply CFSG.LocalCores.layer_eq_bot_of_forall
    intro K hK
    exact h ⟨K, hK⟩
  by_cases htop : ∃ K : Subgroup G, IsComponent K ∧ K = ⊤
  · obtain ⟨K, hK, rfl⟩ := htop
    have hKsimple : IsSimpleGroup (⊤ : Subgroup G) := isSimpleGroup_of_isComponent hZmap hK
    have hlayer : layer G = ⊤ := le_antisymm le_top (by simpa using CFSG.LocalCores.component_le_layer hK)
    rw [hEG, hlayer]
    exact hKsimple
  obtain ⟨K, hK⟩ := hex
  have hKproper : K ≠ ⊤ := fun h => htop ⟨K, hK, h⟩
  have hnormal : ∀ L : Subgroup G, IsComponent L → L.Normal :=
    fun L hL => normal_of_isComponent hP hZmap hL
  have hKnotcen : ¬ ∀ k ∈ K, Commute d₀ k :=
    not_forall_commute_of_isComponent hP hcenter hK (hnormal K hK) hd₀
  have huniq : ∀ L : Subgroup G, IsComponent L → L = K := by
    intro L hL
    by_contra hne
    have hLn : L.Normal := hnormal L hL
    have hLnotcen : ¬ ∀ k ∈ L, Commute d₀ k :=
      not_forall_commute_of_isComponent hP hcenter hL hLn hd₀
    have hKLcomm : ⁅K, L⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
      · exact absurd h.symm hne
      · exact h
    have hKLcommute : ∀ a ∈ K, ∀ b ∈ L, Commute a b := by
      intro a ha b hb
      have hmem : a ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKLcomm ha
      exact (Subgroup.mem_centralizer_iff.mp hmem b hb).symm
    obtain ⟨x, hxK, hxne, hxcomm⟩ :=
      exists_commuting_conj_of_isComponent hP hZmap hK (hnormal K hK) hd₀ hKnotcen
    obtain ⟨y, hyL, hyord⟩ :=
      exists_order_three_of_isComponent hP hZmap hL hLn hd₀ hLnotcen
    have hCxK : ⁅d₀, x⁆ ∈ K := by
      have hdx : d₀ * x * d₀⁻¹ ∈ K := by
        have hmap := map_conj_eq_self_of_isComponent hP hZmap hK hd₀
        have hmem : MulAut.conj d₀ x ∈ K.map (MulAut.conj d₀).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
        rwa [hmap] at hmem
      rw [commutatorElement_def]
      exact K.mul_mem hdx (K.inv_mem hxK)
    have hCxEq : ⁅d₀, x⁆ = d₀ * MulAut.conj x d₀ := by
      rw [commutatorElement_def, MulAut.conj_apply, Pair.inv_eq hP hd₀]
      group
    have hCx2 : MulAut.conj x d₀ * MulAut.conj x d₀ = 1 := by
      change MulAut.conj x d₀ * MulAut.conj x d₀ = 1
      rw [← map_mul, Pair.mul_self hP hd₀, map_one]
    have hCxOrd : orderOf ⁅d₀, x⁆ = 2 := by
      rw [hCxEq]
      have hsq : (d₀ * MulAut.conj x d₀) * (d₀ * MulAut.conj x d₀) = 1 := by
        calc (d₀ * MulAut.conj x d₀) * (d₀ * MulAut.conj x d₀)
            = d₀ * (MulAut.conj x d₀ * (d₀ * MulAut.conj x d₀)) := by group
          _ = d₀ * ((MulAut.conj x d₀ * d₀) * MulAut.conj x d₀) := by group
          _ = d₀ * ((d₀ * MulAut.conj x d₀) * MulAut.conj x d₀) := by
              rw [← hxcomm.eq]
          _ = (d₀ * d₀) * (MulAut.conj x d₀ * MulAut.conj x d₀) := by group
          _ = 1 := by rw [Pair.mul_self hP hd₀, hCx2, mul_one]
      have hne1 : d₀ * MulAut.conj x d₀ ≠ 1 := by
        intro h
        apply hxne
        have := eq_inv_of_mul_eq_one_right h
        rwa [Pair.inv_eq hP hd₀] at this
      exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hne1
    have hCyL : ⁅d₀, y⁆ ∈ L := by
      have hdy : d₀ * y * d₀⁻¹ ∈ L := by
        have hmap := map_conj_eq_self_of_isComponent hP hZmap hL hd₀
        have hmem : MulAut.conj d₀ y ∈ L.map (MulAut.conj d₀).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨y, hyL, rfl⟩
        rwa [hmap] at hmem
      rw [commutatorElement_def]
      exact L.mul_mem hdy (L.inv_mem hyL)
    have hCyEq : ⁅d₀, y⁆ = d₀ * MulAut.conj y d₀ := by
      rw [commutatorElement_def, MulAut.conj_apply, Pair.inv_eq hP hd₀]
      group
    have hCyOrd : orderOf ⁅d₀, y⁆ = 3 := by
      rw [hCyEq, hyord]
    have hcommProd : Commute ⁅d₀, x⁆ ⁅d₀, y⁆ := hKLcommute _ hCxK _ hCyL
    have hxyProd : ⁅d₀, x * y⁆ = ⁅d₀, x⁆ * ⁅d₀, y⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hcommXY : Commute x ⁅d₀, y⁆ := hKLcommute x hxK _ hCyL
      have hconj : x * ⁅d₀, y⁆ * x⁻¹ = ⁅d₀, y⁆ := by
        rw [hcommXY.eq, mul_assoc, mul_inv_cancel, mul_one]
      calc ⁅d₀, x⁆ * x * ⁅d₀, y⁆ * x⁻¹ = ⁅d₀, x⁆ * (x * ⁅d₀, y⁆ * x⁻¹) := by group
        _ = ⁅d₀, x⁆ * ⁅d₀, y⁆ := by rw [hconj]
    have hord6 : orderOf (⁅d₀, x⁆ * ⁅d₀, y⁆) = 6 := by
      rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcommProd
        (by rw [hCxOrd, hCyOrd]; norm_num), hCxOrd, hCyOrd]
    have hfinal : d₀ * MulAut.conj (x * y) d₀ = ⁅d₀, x⁆ * ⁅d₀, y⁆ := by
      rw [← hxyProd, commutatorElement_def, MulAut.conj_apply, Pair.inv_eq hP hd₀]
      group
    have hprodxy : orderOf (d₀ * MulAut.conj (x * y) d₀) ∈ ({1, 2, 3} : Set ℕ) :=
      hP.2.2.2.1 d₀ hd₀ _ (Pair.conj_mem hP hd₀ (x * y))
    rw [hfinal, hord6] at hprodxy
    norm_num at hprodxy
  have hlayer : layer G = K := by
    apply le_antisymm
    · rw [CFSG.layer.eq_sSup]
      exact sSup_le fun L hL => by rw [huniq L hL]
    · exact CFSG.LocalCores.component_le_layer hK
  rw [hEG, hlayer]
  exact isSimpleGroup_of_isComponent hZmap hK

end CFSG.OddTranspositions
