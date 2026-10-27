module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrW6
public import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenExtra

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w16g_ext_center_of_extraspecial {K : Subgroup (MulAut W)}
    (hK : IsPOnePlusTwo 3 ↥K) :
    ∃ z : MulAut W, z ∈ K ∧ orderOf z = 3 ∧ (∀ y ∈ K, y * z = z * y) ∧
      (∀ x ∈ K, (∀ y ∈ K, y * x = x * y) → x ∈ Subgroup.zpowers z) := by
  haveI : CFSG.IsExtraspecial 3 ↥K := hK.1
  have hcardK : Nat.card ↥K = 27 := by rw [hK.2.1]; norm_num
  have hZcard : Nat.card (Subgroup.center ↥K) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcyc : IsCyclic (Subgroup.center ↥K) := isCyclic_of_prime_card hZcard
  obtain ⟨z0, hz0gen⟩ := IsCyclic.exists_generator (α := Subgroup.center ↥K)
  have hz0top : Subgroup.zpowers z0 = ⊤ := le_antisymm le_top fun x _ => hz0gen x
  have hz0ord : orderOf z0 = 3 := by
    rw [← Nat.card_zpowers z0, hz0top, Subgroup.card_top, hZcard]
  have hzord : orderOf (((z0 : ↥K)) : MulAut W) = 3 := by
    calc orderOf (((z0 : ↥K)) : MulAut W) = orderOf (z0 : ↥K) := Subgroup.orderOf_coe _
      _ = orderOf z0 := Subgroup.orderOf_coe _
      _ = 3 := hz0ord
  have hzcent : ∀ y ∈ K, y * ((z0 : ↥K) : MulAut W) = ((z0 : ↥K) : MulAut W) * y := by
    intro y hy
    exact congrArg (fun w : ↥K => (w : MulAut W))
      (Subgroup.mem_center_iff.mp z0.2 (⟨y, hy⟩ : ↥K))
  refine ⟨((z0 : ↥K) : MulAut W), (z0 : ↥K).2, hzord, hzcent, ?_⟩
  have hzpowers_eq : Subgroup.zpowers (z0 : ↥K) = Subgroup.center ↥K := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z0.2) ?_
    rw [hZcard, Nat.card_zpowers, Subgroup.orderOf_coe, hz0ord]
  intro x hx hxc
  have hxcent : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hxc y y.2)
  have hxzp : (⟨x, hx⟩ : ↥K) ∈ Subgroup.zpowers (z0 : ↥K) := by
    rw [hzpowers_eq]
    exact hxcent
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxzp
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have hval : ((z0 : ↥K) : MulAut W) ^ n = x := by
    rw [← Subgroup.coe_zpow, hn]
  exact hval

theorem w16g_commSub_extraspecial_eq_and_irreducible (hW : ∀ w : W, w * w = 1)
    {K : Subgroup (MulAut W)} (hK : IsPOnePlusTwo 3 ↥K) {z : MulAut W} (hzK : z ∈ K)
    (hz3 : orderOf z = 3) (hzc : ∀ y ∈ K, y * z = z * y)
    (hZK : ∀ x ∈ K, (∀ y ∈ K, y * x = x * y) → x ∈ Subgroup.zpowers z)
    (hrkK : rk ↥(commSub ⊤ K) = 6) :
    commSub ⊤ K = commSub ⊤ (Subgroup.zpowers z) ∧ IsIrrOn K (commSub ⊤ K) ⊥ := by
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hz3pow : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz3] at this
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz3]
    norm_num
  have hJstab : StableUnder K (commSub ⊤ (Subgroup.zpowers z)) := by
    intro c hc u hu
    exact CFSG.Quasithin.Asc81c.Pf.commSub_stable_of_commute (X := Subgroup.zpowers z)
      (fun x hx => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact (show Commute c z from hzc c hc).zpow_right n) hu
  have hJne : commSub ⊤ (Subgroup.zpowers z) ≠ ⊥ := by
    intro hbot
    have hfixall : ∀ u : W, z u = u := by
      intro u
      have hle : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers z) := (commSub_eq_bot_iff).mp hbot
      exact hle (Subgroup.mem_top u) z (Subgroup.mem_zpowers z)
    exact hz1 (MulEquiv.ext hfixall)
  have hJfix : commSub ⊤ (Subgroup.zpowers z) ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    rw [inf_comm]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hodd
  have h6 := s13_six_le_rk_of_stable hW hK hzK hz3 hzc hZK hJstab hJne hJfix
  have hle : commSub ⊤ (Subgroup.zpowers z) ≤ commSub ⊤ K :=
    commSub_mono le_top (Subgroup.zpowers_le.mpr hzK)
  have hJeq : commSub ⊤ (Subgroup.zpowers z) = commSub ⊤ K :=
    eq_of_le_of_rk_le hW2 hle (by rw [hrkK]; exact h6)
  have hrkz : rk ↥(commSub ⊤ (Subgroup.zpowers z)) = 6 := by rw [hJeq]; exact hrkK
  have h' := s13_W6_irreducible hW hK hzK hz3 hzc hZK hrkz
  exact ⟨hJeq.symm, by rwa [hJeq] at h'⟩

theorem w16g_isPOnePlusTwo_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  haveI : CFSG.IsExtraspecial p X := hX
  refine ⟨isExtraspecial_of_mulEquiv e.symm, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hc
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hp x, map_one]

theorem w16g_commSub_zpowers_t_ne_bot {P : Subgroup (MulAut W)} (hP : IsPGroup 3 ↥P)
    (hcardP : Nat.card P = 81) {t : MulAut W} (ht : orderOf t = 2)
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P)
    {K : Subgroup (MulAut W)} (hKP : K ≤ P) (hK : IsPOnePlusTwo 3 ↥K) :
    ⁅K, Subgroup.zpowers t⁆ ≠ ⊥ := by
  classical
  intro hbot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have ht_norm : t ∈ Subgroup.normalizer (P : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hn y hy, fun hy => ?_⟩
    have hmem : t * (t * y * t⁻¹) * t⁻¹ ∈ P := hn (t * y * t⁻¹) hy
    have hyy : t * (t * y * t⁻¹) * t⁻¹ = y := by
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left htt]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [htt]; simp
    rwa [hyy] at hmem
  have hKcard : Nat.card ↥K = 27 := by rw [hK.2.1]; norm_num
  have hKcent : K ≤ Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hKt : ∀ k ∈ K, Commute k t := by
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKcent hk) t (Subgroup.mem_zpowers t)).symm
  have hlefri : P ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) ≤
      (frattini ↥P).map P.subtype := by
    set Z : Subgroup (MulAut W) := Subgroup.zpowers t with hZ
    have hZU : Z ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
      Subgroup.zpowers_le.mpr ht_norm
    letI : Subgroup.Normalizes Z P := ⟨hZU⟩
    have htop : commutatorAction (A := ↥Z) (G := ↥P) = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [CFSG.commutatorAction_subgroup_conj_map_eq_commutator P Z hZU, hc,
        Subgroup.map_top, Subgroup.range_subtype]
    have hcop : Nat.Coprime (Nat.card ↥Z) (Nat.card ↥P) := by
      have hZcard : Nat.card ↥Z = 2 := by rw [hZ, Nat.card_zpowers, ht]
      rw [hZcard, hcardP]
      norm_num
    letI : MulDistribMulAction ↥Z (↥P ⧸ frattini ↥P) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.frattiniQuotientAction ↥Z ↥P
    have hbotfix : fixedPointSubgroup ↥Z (↥P ⧸ frattini ↥P) = ⊥ :=
      CFSG.RankThree.GroupTheory.SteinbergBY.fixedPointSubgroup_quotient_eq_bot hcop htop
        (frattini P)
        (CFSG.RankThree.GroupTheory.SteinbergBY.isInvariant_of_characteristic _)
        (CFSG.GroupTheory.frattini_elementary_quotient hP).2.1
    rintro x ⟨hxP, hxg⟩
    have hfix : ((⟨x, hxP⟩ : ↥P) : ↥P ⧸ frattini ↥P) ∈
        fixedPointSubgroup ↥Z (↥P ⧸ frattini ↥P) := by
      rw [FixedPoints.mem_subgroup]
      intro z
      have hz : z • (⟨x, hxP⟩ : ↥P) = ⟨x, hxP⟩ := by
        apply Subtype.ext
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_inv_eq_iff_eq_mul]
        obtain ⟨n, hn'⟩ := Subgroup.mem_zpowers_iff.mp z.2
        have hxz : Commute x (t ^ n) :=
          Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hxg) n
        rw [hn'] at hxz
        exact hxz.eq.symm
      change ((z • (⟨x, hxP⟩ : ↥P) : ↥P) : ↥P ⧸ frattini ↥P) =
        ((⟨x, hxP⟩ : ↥P) : ↥P ⧸ frattini ↥P)
      rw [hz]
    rw [hbotfix, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hfix
    exact ⟨⟨x, hxP⟩, hfix, rfl⟩
  have hKle : K ≤ P ⊓ Subgroup.centralizer ({t} : Set (MulAut W)) :=
    fun k hk => ⟨hKP hk, Subgroup.mem_centralizer_singleton_iff.mpr (hKt k hk)⟩
  have hKfr : K ≤ (frattini ↥P).map P.subtype := hKle.trans hlefri
  have hKidx : (K.subgroupOf P).index = 3 := by
    have hcard_sub : Nat.card ↥(K.subgroupOf P) = 27 := by
      rw [show Nat.card ↥(K.subgroupOf P) = Nat.card ↥K from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv, hKcard]
    rw [Subgroup.index_eq_card_div, hcard_sub, hcardP]
  have hKcoatom : IsCoatom (K.subgroupOf P) :=
    Subgroup.isCoatom_of_index_prime (by rw [hKidx]; norm_num)
  have hfrK : frattini ↥P ≤ K.subgroupOf P := frattini_le_coatom hKcoatom
  have hfrKmap : (frattini ↥P).map P.subtype ≤ K := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hfrK hy)
  have hKfrsub : K.subgroupOf P ≤ frattini ↥P := by
    intro y hy
    have hy' : (y : MulAut W) ∈ K := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hKfr hy')
    have hzy' : z = y := Subtype.ext hzy
    rwa [hzy'] at hz
  have hPhiK : frattini ↥P = K.subgroupOf P := le_antisymm hfrK hKfrsub
  obtain ⟨x, hxP, hxK⟩ : ∃ x : MulAut W, x ∈ P ∧ x ∉ K := by
    by_contra h
    push Not at h
    have hPK : P ≤ K := fun y hy => h y hy
    have hle := Subgroup.card_le_of_le hPK
    rw [hcardP, hKcard] at hle
    omega
  let x' : ↥P := ⟨x, hxP⟩
  have hx'K : x' ∉ K.subgroupOf P := by
    intro h
    exact hxK (Subgroup.mem_subgroupOf.mp h)
  have hx'Phi : x' ∉ frattini ↥P := by rw [hPhiK]; exact hx'K
  have hcardq : Nat.card (↥P ⧸ frattini ↥P) = 3 := by
    rw [← Subgroup.index_eq_card, hPhiK, hKidx]
  have htopq : Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x') = ⊤ := by
    have hne1 : Nat.card (Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x')) ≠ 1 := by
      intro h1
      have hmem : QuotientGroup.mk' (frattini ↥P) x' ∈
          Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x') :=
        Subgroup.mem_zpowers _
      have hbot : Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x') = ⊥ :=
        Subgroup.card_eq_one.mp h1
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hx'Phi ((QuotientGroup.eq_one_iff (N := frattini ↥P) x').mp hmem)
    have hdvd : Nat.card (Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x')) ∣ 3 := by
      rw [← hcardq]
      exact Subgroup.card_subgroup_dvd_card _
    have hcardzp : Nat.card (Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x')) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    exact Subgroup.eq_top_of_card_eq
      (H := Subgroup.zpowers (QuotientGroup.mk' (frattini ↥P) x'))
      (by rw [hcardzp, hcardq])
  have hsupx : Subgroup.zpowers x' ⊔ frattini ↥P = ⊤ := by
    have hmap : (Subgroup.zpowers x' ⊔ frattini ↥P).map
        (QuotientGroup.mk' (frattini ↥P)) = ⊤ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, htopq, top_sup_eq]
    have hker : (QuotientGroup.mk' (frattini ↥P)).ker ≤
        Subgroup.zpowers x' ⊔ frattini ↥P := by
      rw [QuotientGroup.ker_mk']
      exact le_sup_right
    have hcme := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (frattini ↥P)) hker
    rw [hmap, Subgroup.comap_top] at hcme
    exact hcme.symm
  letI : Fact (IsPGroup 3 ↥P) := ⟨hP⟩
  have hcycgen : Subgroup.zpowers x' = ⊤ :=
    CFSG.lemma_1_7_a (p := 3) (Subgroup.zpowers x') hsupx
  haveI : IsCyclic ↥P := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x', hcycgen⟩
  haveI : IsCyclic (K.subgroupOf P) := inferInstance
  haveI : IsCyclic ↥K := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hKP) (Subgroup.subgroupOfEquivOfLe hKP).surjective
  haveI : CFSG.IsExtraspecial 3 ↥K := hK.1
  have hctr : Subgroup.center ↥K = ⊤ := Subgroup.center_eq_top
  haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.IsExtraspecial.quotient_nontrivial 3 ↥K
  have hsub : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
    rw [hctr]
    exact QuotientGroup.subsingleton_quotient_top (G := ↥K)
  exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance

end CFSG.LocalAnalysis.WeakClosure81
