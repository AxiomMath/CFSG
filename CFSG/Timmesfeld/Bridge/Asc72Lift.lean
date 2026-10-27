module

public import CFSG.Timmesfeld.Bridge.Asc72Width
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeHyperplaneGeneration
public import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

theorem commute_of_inv_mul_mem_two (hD : IsOddTransp D) {P : Subgroup G} (hP : IsPGroup 2 P)
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : x⁻¹ * y ∈ P) : Commute x y := by
  rcases hD.commute_or_odd hx hy with h | h
  · exact h
  · rw [hD.inv_eq hx] at hxy
    obtain ⟨k, hk⟩ := hP ⟨x * y, hxy⟩
    have hk' : (x * y) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf (x * y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases i with _ | i
    · rw [pow_zero, orderOf_eq_one_iff] at hi
      rw [hD.eq_of_mul_eq_one hx hi]
    · rw [hi, pow_succ] at h
      exact absurd h (by simp [Nat.not_odd_iff_even])

theorem conj_eq_of_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1) {k : ℕ}
    (hk : orderOf (x * y) = 2 * k + 1) : (x * y) ^ k * x * ((x * y) ^ k)⁻¹ = y := by
  have hpow : (x * y) ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one _
  have hc := mul_zpow_mul_eq_zpow_neg_mul hx hy (-(k : ℤ))
  rw [neg_neg, zpow_natCast, zpow_neg, zpow_natCast] at hc
  calc (x * y) ^ k * x * ((x * y) ^ k)⁻¹ = (x * y) ^ k * (x * y) ^ k * x := by
        rw [mul_assoc, hc, mul_assoc]
    _ = (x * y) ^ (2 * k + 1) * (x * y)⁻¹ * x := by
        rw [← pow_add, pow_succ, mul_inv_cancel_right, two_mul]
    _ = y := by
        rw [hpow, one_mul, mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hy]

theorem mem_closure_pair_iff_of_commute {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : Commute u v) {g : G} :
    g ∈ Subgroup.closure ({u, v} : Set G) ↔ g = 1 ∨ g = u ∨ g = v ∨ g = u * v := by
  have huv : u * v * (u * v) = 1 := by
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hc.eq]
      _ = 1 := by rw [← mul_assoc, hu, one_mul, hv]
  have hsq : (u * v) ^ (2 : ℤ) = 1 := by rw [zpow_two, huv]
  constructor
  · intro hg
    obtain ⟨i, rfl | rfl⟩ := exists_zpow_of_mem_closure_pair hu hv hg
    · obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' i
      · left
        rw [zpow_mul, hsq, one_zpow]
      · right; right; right
        rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
    · obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' i
      · right; left
        rw [zpow_mul, hsq, one_zpow, one_mul]
      · right; right; left
        rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one, mul_assoc, ← hc.eq,
          ← mul_assoc, hu, one_mul]
  · have hu' : u ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
    have hv' : v ∈ Subgroup.closure ({u, v} : Set G) := Subgroup.subset_closure (by simp)
    rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hu'
    · exact hv'
    · exact Subgroup.mul_mem _ hu' hv'

theorem odd_normal_le_sup_centralizer [Finite G] {N : Subgroup G} [N.Normal]
    (hodd : Odd (Nat.card N)) {u v : G} (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hc : Commute u v) :
    N ≤ (N ⊓ Subgroup.centralizer {u}) ⊔ (N ⊓ Subgroup.centralizer {v}) ⊔
      (N ⊓ Subgroup.centralizer {u * v}) := by
  classical
  set P := Subgroup.closure ({u, v} : Set G) with hP
  have hmem := fun g => mem_closure_pair_iff_of_commute (g := g) hu hv hc
  have huv1 : u * v ≠ 1 := fun h => huv (by
    rw [← inv_eq_of_mul_eq_one_right hu]
    exact (eq_inv_of_mul_eq_one_right h).symm)
  have hcomm : ∀ g ∈ P, Commute g u ∧ Commute g v := by
    intro g hg
    rcases (hmem g).mp hg with h | h | h | h <;> rw [h]
    · exact ⟨Commute.one_left u, Commute.one_left v⟩
    · exact ⟨Commute.refl u, hc⟩
    · exact ⟨hc.symm, Commute.refl v⟩
    · exact ⟨(Commute.refl u).mul_left hc.symm, hc.mul_left (Commute.refl v)⟩
  have hab : IsMulCommutative P := ⟨⟨fun a b => by
    apply Subtype.ext
    show (a : G) * b = b * a
    rcases (hmem b).mp b.2 with h | h | h | h
    · rw [h, mul_one, one_mul]
    · rw [h]; exact (hcomm a a.2).1.eq
    · rw [h]; exact (hcomm a a.2).2.eq
    · rw [h]; exact ((hcomm a a.2).1.mul_right (hcomm a a.2).2).eq⟩⟩
  have hexp : ∀ g ∈ P, g ^ 2 = 1 := by
    intro g hg
    rw [pow_two]
    rcases (hmem g).mp hg with h | h | h | h <;> rw [h]
    · rw [mul_one]
    · exact hu
    · exact hv
    · calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [hc.eq]
        _ = 1 := by rw [← mul_assoc, hu, one_mul, hv]
  have hcard : Nat.card P = 2 ^ 2 := by
    have hset : (P : Set G) = {1, u, v, u * v} := by
      ext g
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hmem g
    have : Nat.card P = (P : Set G).ncard := (Nat.card_coe_set_eq _)
    rw [this, hset]
    have h1 : (1 : G) ∉ ({u, v, u * v} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hu1.symm, hv1.symm, huv1.symm⟩
    have h2 : u ∉ ({v, u * v} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨huv, fun h => hv1 ?_⟩
      have := congrArg (u⁻¹ * ·) h
      simpa using this.symm
    have h3 : v ∉ ({u * v} : Set G) := by
      simp only [Set.mem_singleton_iff]
      intro h
      apply hu1
      have := congrArg (· * v⁻¹) h
      simpa using this.symm
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
    norm_num
  let : CommGroup P :=
    { (inferInstance : Group P) with mul_comm := fun a b => hab.is_comm.comm a b }
  have hstable : ∀ c : P, ∀ n : G, n ∈ N → P.subtype c * n * (P.subtype c)⁻¹ ∈ N :=
    fun c n hn => ‹N.Normal›.conj_mem n hn c
  let action := CFSG.LargeEvenClassification.Helpers.invariantSubgroupConjugation P.subtype N
    hstable
  have hPp : IsPGroup 2 P := IsPGroup.of_card hcard
  have hexp' : ∀ c : P, c ^ 2 = 1 := fun c => Subtype.ext (by simpa using hexp c c.2)
  have hcop : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.LargeEvenClassification.Helpers.coprime_hyperplane_fixed_generation
    Nat.prime_two hPp hexp' action hcop
  intro n hn
  have hmemtop : (⟨n, hn⟩ : N) ∈
      CFSG.LargeEvenClassification.Helpers.hyperplaneFixedSpan 2 action := by
    rw [hgen]
    trivial
  set T := (N ⊓ Subgroup.centralizer {u}) ⊔ (N ⊓ Subgroup.centralizer {v}) ⊔
    (N ⊓ Subgroup.centralizer {u * v}) with hT
  have hle : CFSG.LargeEvenClassification.Helpers.hyperplaneFixedSpan 2 action ≤
      T.comap N.subtype := by
    refine iSup_le fun F => ?_
    have hF : (F.val : Subgroup P) ≠ ⊥ := by
      intro hbot
      have h2 := F.2
      rw [hbot, Subgroup.index_bot, hcard] at h2
      norm_num at h2
    obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF
    intro m hm
    have hfix : action f.val m = m := hm f
    have hcomm : (f : P).val * (m : G) = m * (f : P).val := by
      have := congrArg Subtype.val hfix
      change (f : P).val * (m : G) * ((f : P).val)⁻¹ = m at this
      calc (f : P).val * (m : G) = (f : P).val * (m : G) * ((f : P).val)⁻¹ * (f : P).val := by
            group
        _ = m * (f : P).val := by rw [this]
    have hf1' : ((f : P) : G) ≠ 1 := fun h => hf1 (Subtype.ext (Subtype.ext h))
    show (m : G) ∈ T
    rcases (hmem ((f : P) : G)).mp (f : P).2 with h | h | h | h
    · exact absurd h hf1'
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨m.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (h ▸ hcomm).symm⟩))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨m.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (h ▸ hcomm).symm⟩))
    · exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨m.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (h ▸ hcomm).symm⟩)
  exact hle hmemtop

theorem odd_normal_le_compStab [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D)
    {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N)) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x ≠ y) (hc : Commute x y) : N ≤ compStab hN x := by
  have hle := odd_normal_le_sup_centralizer hodd (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy)
    (hD.ne_one hx) (hD.ne_one hy) hxy hc
  refine hle.trans (sup_le (sup_le ?_ ?_) ?_)
  · intro n hn
    rw [mem_compStab_iff]
    have : n * x * n⁻¹ = x := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hn).2,
        mul_inv_cancel_right]
    rw [this]
    exact reach_refl x
  · intro n hn
    rw [mem_compStab_iff]
    have hny : n * y * n⁻¹ = y := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hn).2,
        mul_inv_cancel_right]
    have h1 : Reach D y (n * x * n⁻¹) := by
      have := reach_conj hN n (reach_of_commute hy hx hc.symm)
      rwa [hny] at this
    exact reach_trans (reach_of_commute hx hy hc) h1
  · intro n hn
    have hnx : Commute n x :=
      commute_of_mem_odd_normal hD hN hodd hx hy hxy hc (Subgroup.mem_inf.mp hn).1
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hn).2)
    rw [mem_compStab_iff, hnx.eq, mul_inv_cancel_right]
    exact reach_refl x

theorem reach_of_inv_mul_mem_odd [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D)
    {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N))
    (hnb : ∀ x ∈ D, ∃ y ∈ D, x ≠ y ∧ Commute x y) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : x⁻¹ * y ∈ N) : Reach D x y := by
  rcases hD.commute_or_odd hx hy with hc | hoddxy
  · exact reach_of_commute hx hy hc
  obtain ⟨y₀, hy₀, hne, hc₀⟩ := hnb x hx
  have hle := odd_normal_le_compStab hD hN hodd hx hy₀ hne hc₀
  obtain ⟨k, hk⟩ := hoddxy
  have hconj := conj_eq_of_odd (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy) hk
  have hmem : (x * y) ^ k ∈ N := by
    rw [hD.inv_eq hx] at hxy
    exact N.pow_mem hxy k
  have := hle hmem
  rwa [mem_compStab_iff, hconj] at this

theorem reach_of_reach_quotient (hD : IsOddTransp D) {N : Subgroup G} [N.Normal]
    (hlift : ∀ x ∈ D, ∀ y ∈ D, x⁻¹ * y ∈ N → Reach D x y) {x y : G}
    (hx : x ∈ D) (hy : y ∈ D)
    (h : Reach (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)) :
    Reach D x y := by
  have key : ∀ q, Reach (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N x) q →
      ∀ p ∈ D, QuotientGroup.mk' N p = q → Reach D x p := by
    intro q hq
    induction hq with
    | refl =>
      intro p hp hpq
      apply hlift x hx p hp
      rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, hpq]
    | tail _ hbc ih =>
      intro p hp hpq
      obtain ⟨⟨b, hb, rfl⟩, -, hcomm⟩ := hbc
      have hxb := ih b hb rfl
      subst hpq
      by_cases hbp : QuotientGroup.mk' N b = QuotientGroup.mk' N p
      · exact reach_trans hxb (hlift b hb p hp (by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hbp
          exact hbp))
      ·
        rcases hD.commute_or_odd hb hp with hc | hodd
        · exact reach_trans hxb (reach_of_commute hb hp hc)
        · exfalso
          have hsq : (QuotientGroup.mk' N (b * p)) ^ 2 = 1 := by
            rw [map_mul, ← commute_iff_mul_sq_eq_one]
            · exact hcomm
            · rw [← map_mul, hD.mul_self_eq_one hb, map_one]
            · rw [← map_mul, hD.mul_self_eq_one hp, map_one]
          have hdvd : orderOf (QuotientGroup.mk' N (b * p)) ∣ orderOf (b * p) :=
            orderOf_map_dvd _ _
          have h2 : orderOf (QuotientGroup.mk' N (b * p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
          have h1 : orderOf (QuotientGroup.mk' N (b * p)) = 1 := by
            have hodd' := Odd.of_dvd_nat hodd hdvd
            obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
              (show orderOf (QuotientGroup.mk' N (b * p)) ∣ 2 ^ 1 by simpa using h2)
            rcases i with _ | i
            · simpa using hi
            · rw [hi, pow_succ] at hodd'
              exact absurd hodd' (by simp [Nat.not_odd_iff_even])
          rw [orderOf_eq_one_iff, map_mul, mul_eq_one_iff_eq_inv] at h1
          apply hbp
          rw [h1, ← map_inv, hD.inv_eq hp]
  exact key _ h y hy rfl

theorem exists_normal_le_isPGroup_two_or_odd [Finite G] {R : Subgroup G} (hR : Group.IsSolvable R)
    (hR1 : R ≠ ⊥) [R.Normal] :
    ∃ N : Subgroup G, N.Normal ∧ N ≤ R ∧ N ≠ ⊥ ∧ (IsPGroup 2 N ∨ Odd (Nat.card N)) := by
  classical
  have hex : ∃ k, ∃ N : Subgroup G, N.Normal ∧ N ≤ R ∧ N ≠ ⊥ ∧ Nat.card N = k :=
    ⟨_, R, inferInstance, le_rfl, hR1, rfl⟩
  obtain ⟨N, hNn, hNR, hN1, hNk⟩ := Nat.find_spec hex
  have hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := by
    intro K hKn hKN
    by_cases hK1 : K = ⊥
    · exact Or.inl hK1
    · right
      have hle := Nat.find_min' hex ⟨K, hKn, hKN.trans hNR, hK1, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge hKN (by rw [hNk]; exact hle)
  have := hNn
  have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => hmin K hK hKN⟩
  have := hR
  have : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNR)
      (Subgroup.inclusion_injective hNR)
  obtain ⟨p, hp, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have hpg : IsPGroup p N := CFSG.IsElementaryAbelian.isPGroup p N
  refine ⟨N, hNn, hNR, hN1, ?_⟩
  by_cases hp2 : p = 2
  · exact Or.inl (hp2 ▸ hpg)
  · right
    have := Fact.mk hp
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    rw [hk]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem reach_of_inv_mul_mem_solvable {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) (hns : ¬ Group.IsSolvable G) {R : Subgroup G} [R.Normal]
    (hR : Group.IsSolvable R) {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : x⁻¹ * y ∈ R) :
    Reach D x y := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
      ¬ Group.IsSolvable G → ∀ (R : Subgroup G), R.Normal → Group.IsSolvable R →
      Nat.card R = n → ∀ x ∈ D, ∀ y ∈ D, x⁻¹ * y ∈ R → Reach D x y from
    key _ G D hS hns R inferInstance hR rfl x hx y hy hxy
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ D hS hns R hRn hR hRc x hx y hy hxy
  by_cases hR1 : R = ⊥
  · subst hR1
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hxy
    subst hxy
    exact reach_refl x
  obtain ⟨N, hNn, hNR, hN1, hNp⟩ := exists_normal_le_isPGroup_two_or_odd hR hR1
  have hPN : ∀ a ∈ D, ∀ b ∈ D, a⁻¹ * b ∈ N → Reach D a b := by
    intro a ha b hb hab
    rcases hNp with h2 | hodd
    · exact reach_of_commute ha hb (commute_of_inv_mul_mem_two hS.oddT h2 ha hb hab)
    · exact reach_of_inv_mul_mem_odd hS.oddT hS.normal hodd
        (fun z hz => hS.exists_commute_ne_of_not_isSolvable hns hz) ha hb hab
  have := hR
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNR)
      (Subgroup.inclusion_injective hNR)
  have hND : ∀ a ∈ D, a ∉ N := by
    rcases hS.subset_or_disjoint N with h | h
    · exfalso
      apply hns
      have htop := hS.eq_top_of_subset N h
      exact Group.isSolvable_of_surjective (f := N.subtype) (fun g => ⟨⟨g, htop ▸ trivial⟩, rfl⟩)
    · exact h
  have hS' : Setup (G ⧸ N) (QuotientGroup.mk' N '' D) :=
    hS.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (fun d hd h1 =>
      hND d hd ((QuotientGroup.eq_one_iff d).mp h1))
  have hns' : ¬ Group.IsSolvable (G ⧸ N) := fun hQ =>
    hns (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  set R' := R.map (QuotientGroup.mk' N) with hR'
  have hR'n : R'.Normal := Subgroup.Normal.map hRn _ (QuotientGroup.mk'_surjective N)
  have hR'sol : Group.IsSolvable R' :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).subgroupMap R)
      ((QuotientGroup.mk' N).subgroupMap_surjective R)
  have hcard : Nat.card R' < n := by
    rw [← hRc]
    by_contra hle
    push Not at hle
    have hbij := ((QuotientGroup.mk' N).subgroupMap_surjective R).bijective_of_nat_card_le hle
    obtain ⟨⟨m, hmN⟩, hm1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
    have hm1 : m ≠ 1 := fun h => hm1' (Subtype.ext h)
    have := hbij.1 (a₁ := ⟨m, hNR hmN⟩) (a₂ := 1) (by
      apply Subtype.ext
      simp only [MonoidHom.subgroupMap_apply_coe, QuotientGroup.mk'_apply, map_one,
        OneMemClass.coe_one]
      exact (QuotientGroup.eq_one_iff _).mpr hmN)
    exact hm1 (by simpa using congrArg Subtype.val this)
  have hreach := ih _ hcard (G ⧸ N) _ hS' hns' R' hR'n hR'sol rfl
    (QuotientGroup.mk' N x) ⟨x, hx, rfl⟩ (QuotientGroup.mk' N y) ⟨y, hy, rfl⟩ (by
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hxy)
  exact reach_of_reach_quotient hS.oddT hPN hx hy hreach

end CFSG.Timmesfeld.Bridge.Asc72
