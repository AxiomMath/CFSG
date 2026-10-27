module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Solvable

public section

lemma modA_eq_of_sub {W : Type*} [AddCommGroup W] {x y p q : W} (hp : p = 0) (hq : q = 0)
    (h : x - y = p - q) : x = y := by
  rw [← sub_eq_zero, h, hp, hq, sub_self]

theorem exists_fixed_of_modular {H V : Type*} [Group H] [AddCommGroup V] [DistribMulAction H V]
    [Nontrivial V] (a z δ : H) (ha : a ^ 3 = 1) (hδ : δ ^ 3 = 1) (haδ : a * δ = δ * a)
    (hzδ : z * δ = δ * z) (haz : a * z * a⁻¹ = z * δ)
    (hfree : ∀ v : V, δ • v = v → v = 0) : ∃ v : V, v ≠ 0 ∧ a • v = v := by
  by_contra hcon
  have H0 : ∀ v : V, a • v = v → v = 0 := by
    intro v hv
    by_contra hne
    exact hcon ⟨v, hne, hv⟩
  have hA : a * (a * a) = 1 := (pow_three a).symm.trans ha
  have hD : δ * (δ * δ) = 1 := (pow_three δ).symm.trans hδ
  have hA3 : ∀ v : V, a • (a • (a • v)) = v := by
    intro v
    calc a • (a • (a • v)) = (a * (a * a)) • v := by rw [mul_smul, mul_smul]
      _ = v := by rw [hA, one_smul]
  have hD3 : ∀ v : V, δ • (δ • (δ • v)) = v := by
    intro v
    calc δ • (δ • (δ • v)) = (δ * (δ * δ)) • v := by rw [mul_smul, mul_smul]
      _ = v := by rw [hD, one_smul]
  have hS1 : ∀ v : V, a • (a • v) + a • v + v = 0 := by
    intro v
    apply H0
    simp only [smul_add]
    rw [hA3 v]
    abel
  have hS2 : ∀ v : V, δ • (δ • v) + δ • v + v = 0 := by
    intro v
    apply hfree
    simp only [smul_add]
    rw [hD3 v]
    abel
  have hcomm : ∀ x : V, a • (δ • x) = δ • (a • x) := by
    intro x
    calc a • (δ • x) = (a * δ) • x := (mul_smul a δ x).symm
      _ = (δ * a) • x := by rw [haδ]
      _ = δ • (a • x) := mul_smul δ a x
  have hzd : ∀ x : V, δ • (z • x) = z • (δ • x) := by
    intro x
    calc δ • (z • x) = (δ * z) • x := (mul_smul δ z x).symm
      _ = (z * δ) • x := by rw [hzδ]
      _ = z • (δ • x) := mul_smul z δ x
  have haz' : a * z = z * δ * a := by
    rw [← haz, inv_mul_cancel_right]
  have hAZ : ∀ x : V, a • (z • x) = z • (δ • (a • x)) := by
    intro x
    calc a • (z • x) = (a * z) • x := (mul_smul a z x).symm
      _ = (z * δ * a) • x := by rw [haz']
      _ = (z * δ) • (a • x) := mul_smul (z * δ) a x
      _ = z • (δ • (a • x)) := mul_smul z δ (a • x)
  have hT : ∀ v : V, δ • (δ • (a • (a • v))) + δ • (a • v) + v = 0 := by
    intro v
    have h2 : z⁻¹ • (a • (a • (z • v)) + a • (z • v) + z • v) = 0 := by
      rw [hS1 (z • v), smul_zero]
    have e1 : z⁻¹ • (a • (a • (z • v))) = δ • (δ • (a • (a • v))) := by
      rw [hAZ v, hAZ (δ • (a • v)), inv_smul_smul, hcomm (a • v)]
    have e2 : z⁻¹ • (a • (z • v)) = δ • (a • v) := by
      rw [hAZ v, inv_smul_smul]
    have e3 : z⁻¹ • (z • v) = v := inv_smul_smul z v
    rw [smul_add, smul_add, e1, e2, e3] at h2
    exact h2
  have hS3 : ∀ v : V, δ • (a • (a • v)) + a • (a • v) + a • v = 0 := by
    intro v
    apply hfree
    exact modA_eq_of_sub (hT v) (hS1 v) (by simp only [smul_add]; abel)
  have hS4 : ∀ u : V, a • (a • u) = δ • (δ • u) := by
    intro u
    have h3 := hS3 (a • u)
    rw [hA3 u] at h3
    exact modA_eq_of_sub h3 (hS2 u) (by abel)
  have hS5 : ∀ u : V, a • u = δ • u := by
    intro u
    have h4 := hS4 (a • (a • u))
    rw [hA3 (a • u), hS4 u, hD3 (δ • u)] at h4
    exact h4
  have hfix : ∀ v : V, δ • v = v := by
    intro v
    have h1 : a • (z • v) = z • (δ • (δ • v)) := by
      rw [hAZ v, hS5 v]
    have h2 : a • (z • v) = δ • (z • v) := hS5 (z • v)
    have h3 : δ • (z • v) = z • (δ • v) := hzd v
    have h4 : z • (δ • (δ • v)) = z • (δ • v) := by
      rw [← h1, h2, h3]
    have h5 : δ • (δ • v) = δ • v := by
      calc δ • (δ • v) = z⁻¹ • (z • (δ • (δ • v))) := (inv_smul_smul z _).symm
        _ = z⁻¹ • (z • (δ • v)) := by rw [h4]
        _ = δ • v := inv_smul_smul z _
    have h6 : v = δ • (δ • v) := by
      calc v = δ • (δ • (δ • v)) := (hD3 v).symm
        _ = δ • (δ • v) := congrArg (fun y : V => δ • y) h5
    exact h5.symm.trans h6.symm
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hfree x (hfix x))

theorem central_threeGroup_eq_bot_of_perfect {Q : Type*} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) (hsyl : ∀ P : Sylow 3 Q, IsCyclic P)
    (Z : Subgroup Q) (hZ : Z ≤ Subgroup.center Q) (hZ3 : IsPGroup 3 Z) : Z = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Q) := inferInstance
  have hcyc : IsCyclic (P : Subgroup Q) := hsyl P
  letI : CommGroup ↥(P : Subgroup Q) := IsCyclic.commGroup
  have hT : ∀ g : Q, MonoidHom.transfer (MonoidHom.id ↥(P : Subgroup Q)) g = 1 := by
    have hle : commutator Q ≤ (MonoidHom.transfer (MonoidHom.id ↥(P : Subgroup Q))).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    rw [hperf] at hle
    intro g
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzc : z ∈ Subgroup.center Q := hZ hz
  obtain ⟨k, hk⟩ := hZ3 ⟨z, hz⟩
  have hz3k : z ^ 3 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have key : ∀ (m : ℕ) (g₀ : Q), g₀⁻¹ * z ^ m * g₀ ∈ (P : Subgroup Q) →
      g₀⁻¹ * z ^ m * g₀ = z ^ m := by
    intro m g₀ _
    have hcomm : g₀ * z ^ m = z ^ m * g₀ :=
      (show Commute g₀ z from Subgroup.mem_center_iff.mp hzc g₀).pow_right m
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have htf := MonoidHom.transfer_eq_pow (MonoidHom.id ↥(P : Subgroup Q)) z key
  rw [hT z] at htf
  have hidx : z ^ (P : Subgroup Q).index = 1 := by
    have h := congrArg Subtype.val htf
    simpa using h.symm
  have hcop : Nat.Coprime (3 ^ k) (P : Subgroup Q).index :=
    Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (Sylow.not_dvd_index P))
  have hone := pow_gcd_eq_one.mpr ⟨hz3k, hidx⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hone
  exact hone

open Subgroup

lemma pel_perfect_top {G : Type*} [Group G] {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
  have hmap : Subgroup.map K.subtype (⊤ : Subgroup K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_commutator, hmap]
  exact hK

lemma pel_isSolvable_subgroupOf {G : Type*} [Group G] (K θ : Subgroup G)
    [Group.IsSolvable θ] : Group.IsSolvable (θ.subgroupOf K) := by
  let f : (θ.subgroupOf K) →* θ :=
    { toFun := fun x => ⟨((x : K) : G), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  exact Group.isSolvable_of_isSolvable_injective hf

lemma pel_eq_one_of_solvable_perfect {D : Type*} [Group D] [Group.IsSolvable D]
    (hD : ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ = ⊤) (d : D) : d = 1 := by
  have hder : ∀ n : ℕ, derivedSeries D n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, hD]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, derivedSeries D n = ⊥ := Group.IsSolvable.solvable
  have htb : (⊤ : Subgroup D) = ⊥ := by rw [← hder n, hn]
  have hd : d ∈ (⊥ : Subgroup D) := by
    rw [← htb]
    exact Subgroup.mem_top d
  exact Subgroup.mem_bot.mp hd

lemma pel_eq_top_of_cover {H : Type*} [Group H] {N C : Subgroup H}
    [C.Normal] [Group.IsSolvable N]
    (hperf : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤)
    (hcov : ∀ h : H, ∃ c ∈ C, c⁻¹ * h ∈ N) : C = ⊤ := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp N.subtype) := by
    intro d
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective C d
    obtain ⟨c, hc, hn⟩ := hcov h
    refine ⟨⟨c⁻¹ * h, hn⟩, ?_⟩
    have hcC : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff (N := C) c).mpr hc
    show QuotientGroup.mk' C (c⁻¹ * h) = QuotientGroup.mk' C h
    rw [map_mul, map_inv, hcC, inv_one, one_mul]
  haveI : Group.IsSolvable (H ⧸ C) := Group.isSolvable_of_surjective hsurj
  have hcomm : ⁅(⊤ : Subgroup (H ⧸ C)), (⊤ : Subgroup (H ⧸ C))⁆ = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' C) ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ := by
      rw [hperf, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)] at h1
    exact h1
  ext h
  simp only [Subgroup.mem_top, iff_true]
  have hd : QuotientGroup.mk' C h = 1 := pel_eq_one_of_solvable_perfect hcomm _
  exact (QuotientGroup.eq_one_iff (N := C) h).mp hd

theorem centralizes_of_pElements {G : Type*} [Group G] [Finite G] {K S θ : Subgroup G}
    [(θ.subgroupOf K).Normal]
    (hKperf : ⁅K, K⁆ = K) (hKS : K ≤ Subgroup.normalizer (S : Set G))
    (hθs : Group.IsSolvable θ)
    (hsimp : IsSimpleGroup (K ⧸ θ.subgroupOf K)) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card (K ⧸ θ.subgroupOf K))
    (hall : ∀ x ∈ K, IsPGroup p (Subgroup.zpowers x) → ∀ s ∈ S, x * s * x⁻¹ = s) :
    ∀ x ∈ K, ∀ s ∈ S, x * s * x⁻¹ = s := by
  have hK' : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S := fun k hk s hs =>
    (Subgroup.mem_normalizer_iff.mp (hKS hk) s).mp hs
  obtain ⟨C, hC⟩ : ∃ C : Subgroup K,
      ∀ k : K, k ∈ C ↔ ∀ s ∈ S, (k : G) * s * (k : G)⁻¹ = s := by
    refine ⟨{ carrier := {k : K | ∀ s ∈ S, (k : G) * s * (k : G)⁻¹ = s},
              mul_mem' := fun {a b} ha hb => ?_,
              one_mem' := ?_,
              inv_mem' := fun {a} ha => ?_ }, fun k => Iff.rfl⟩
    · have ha' : ∀ s ∈ S, (a : G) * s * (a : G)⁻¹ = s := ha
      have hb' : ∀ s ∈ S, (b : G) * s * (b : G)⁻¹ = s := hb
      show ∀ s ∈ S, ((a * b : K) : G) * s * ((a * b : K) : G)⁻¹ = s
      intro s hs
      rw [Subgroup.coe_mul]
      calc (a : G) * (b : G) * s * ((a : G) * (b : G))⁻¹
          = (a : G) * ((b : G) * s * (b : G)⁻¹) * (a : G)⁻¹ := by group
        _ = (a : G) * s * (a : G)⁻¹ := by rw [hb' s hs]
        _ = s := ha' s hs
    · show ∀ s ∈ S, ((1 : K) : G) * s * ((1 : K) : G)⁻¹ = s
      intro s _
      simp
    · have ha' : ∀ s ∈ S, (a : G) * s * (a : G)⁻¹ = s := ha
      show ∀ s ∈ S, ((a⁻¹ : K) : G) * s * ((a⁻¹ : K) : G)⁻¹ = s
      intro s hs
      rw [Subgroup.coe_inv, inv_inv]
      calc (a : G)⁻¹ * s * (a : G)
          = (a : G)⁻¹ * ((a : G) * s * (a : G)⁻¹) * (a : G) := by rw [ha' s hs]
        _ = s := by group
  haveI hCn : C.Normal := ⟨fun n hn g => by
    rw [hC] at hn ⊢
    intro s hs
    have ht : (g : G)⁻¹ * s * (g : G) ∈ S := by
      have h1 := hK' ((g : G)⁻¹) (K.inv_mem g.2) s hs
      rwa [inv_inv] at h1
    have hn' := hn _ ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc _ = (g : G) * ((n : G) * ((g : G)⁻¹ * s * (g : G)) * (n : G)⁻¹) * (g : G)⁻¹ := by
          group
      _ = (g : G) * ((g : G)⁻¹ * s * (g : G)) * (g : G)⁻¹ := by rw [hn']
      _ = s := by group⟩
  haveI hCbar : (C.map (QuotientGroup.mk' (θ.subgroupOf K))).Normal :=
    Subgroup.Normal.map hCn (QuotientGroup.mk' (θ.subgroupOf K))
      (QuotientGroup.mk'_surjective (θ.subgroupOf K))
  haveI hNsolv : Group.IsSolvable (θ.subgroupOf K) := pel_isSolvable_subgroupOf K θ
  have hperfK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := pel_perfect_top hKperf
  have hCtop : C = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top
        (C.map (QuotientGroup.mk' (θ.subgroupOf K))) with hbot | htop
    ·
      exfalso
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Finite (K ⧸ θ.subgroupOf K) := inferInstance
      obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := K ⧸ θ.subgroupOf K) p hpd
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (θ.subgroupOf K) q
      have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
      obtain ⟨a, m, hpm, hyeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
      have hm0 : m ≠ 0 := fun h => hpm (by rw [h]; exact dvd_zero p)
      have hmdvd : m ∣ orderOf y := ⟨p ^ a, by rw [hyeq]; ring⟩
      have hxord : orderOf (y ^ m) = p ^ a := by
        rw [orderOf_pow_of_dvd hm0 hmdvd, hyeq, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
      have hPg : IsPGroup p (Subgroup.zpowers ((y ^ m : K) : G)) :=
        IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord])
      have hxC : y ^ m ∈ C := (hC (y ^ m)).mpr (hall _ (y ^ m).2 hPg)
      have hmem : QuotientGroup.mk' (θ.subgroupOf K) (y ^ m) ∈
          C.map (QuotientGroup.mk' (θ.subgroupOf K)) :=
        Subgroup.mem_map_of_mem _ hxC
      rw [hbot, Subgroup.mem_bot, map_pow] at hmem
      have hdvd := orderOf_dvd_of_pow_eq_one hmem
      rw [hq] at hdvd
      exact hpm hdvd
    ·
      have hcov : ∀ h : K, ∃ c ∈ C, c⁻¹ * h ∈ θ.subgroupOf K := by
        intro h
        have hh : QuotientGroup.mk' (θ.subgroupOf K) h ∈
            C.map (QuotientGroup.mk' (θ.subgroupOf K)) := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hh
        exact ⟨c, hc, (QuotientGroup.eq (s := θ.subgroupOf K)).mp hceq⟩
      exact pel_eq_top_of_cover hperfK hcov
  intro x hx s hs
  have hxC : (⟨x, hx⟩ : K) ∈ C := by
    rw [hCtop]
    exact Subgroup.mem_top _
  exact (hC ⟨x, hx⟩).mp hxC s hs
