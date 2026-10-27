module

public import CFSG.Quasithin.EmptyFaithful.SBc16S
public import CFSG.Quasithin.EmptyFaithful.SBc17Mix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem pCoreOf_le_sup_of_normalizes {K₁ K₂ : Subgroup G}
    (h₂ : K₂ ≤ Subgroup.normalizer (K₁ : Set G)) : pCoreOf 2 K₁ ≤ pCoreOf 2 (K₁ ⊔ K₂) := by
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₁).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 K₁)
  exact sup_le (le_normalizer_pCoreOf 2 K₁) (h₂.trans (normalizer_le_normalizer_pCoreOf 2 K₁))

theorem inf_le_pCoreOf_of_simple {K₁ K₂ : Subgroup G} (hperf : ⁅K₁, K₁⁆ = K₁)
    (hsimple : IsSimpleGroup (OTwoQuot K₁)) (h₁ : K₁ ≤ Subgroup.normalizer (K₂ : Set G))
    (hne : ¬ K₁ ≤ K₂) : K₁ ⊓ K₂ ≤ pCoreOf 2 K₁ := by
  set A := K₁ ⊓ K₂
  have hAK : A ≤ K₁ := inf_le_left
  have hKN : K₁ ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    SBc14.mem_normalizer_inf (Subgroup.le_normalizer hg) (h₁ hg)
  have hAn : (A.subgroupOf K₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hKN
  let π : ↥K₁ →* OTwoQuot K₁ := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K₁)
  have hnorm : ((A.subgroupOf K₁).map π).Normal :=
    Subgroup.Normal.map hAn π (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A.subgroupOf K₁).map π) with hbot | htop
  · intro x hx
    have hxK : x ∈ K₁ := hAK hx
    have h1 : π ⟨x, hxK⟩ ∈ (A.subgroupOf K₁).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact (SBc16.mem_pCore_iff_coe K₁ ⟨x, hxK⟩).mp ((QuotientGroup.eq_one_iff _).mp h1)
  · exfalso
    have hKAR : ∀ k ∈ K₁, ∃ a ∈ A, ∃ r ∈ pCoreOf 2 K₁, a * r = k := by
      intro k hk
      have hmem : π ⟨k, hk⟩ ∈ (A.subgroupOf K₁).map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hmem
      refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (a : G)⁻¹ * k, ?_, by group⟩
      have h1 : a⁻¹ * ⟨k, hk⟩ ∈ CFSG.Open.pCore 2 ↥K₁ := QuotientGroup.eq.mp hak
      exact ⟨a⁻¹ * ⟨k, hk⟩, h1, by simp⟩
    have hle : K₁ ≤ A :=
      CFSG.Quasithin.SteinbergBM.perfect_le_of_le_mul_pGroup Nat.prime_two
        (pCoreOf_isPGroup 2 K₁) hAK hKN hKAR le_rfl hperf
    exact hne (hle.trans inf_le_right)

theorem exists_commuting_five_of_inf_le {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ≤ Subgroup.normalizer (K₂ : Set G)) (h₂ : K₂ ≤ Subgroup.normalizer (K₁ : Set G))
    (hKO : K₁ ⊓ K₂ ≤ pCoreOf 2 (K₁ ⊔ K₂)) {z z₂ : G} (hz : z ∈ K₁) (hz5 : orderOf z = 5)
    (hz₂ : z₂ ∈ K₂) (hz₂5 : orderOf z₂ = 5) :
    ∃ k ∈ K₂, orderOf k = 5 ∧ z * k = k * z ∧
      Subgroup.zpowers z ⊓ Subgroup.zpowers k = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K := K₁ ⊔ K₂
  set O := pCoreOf 2 K
  set W := K₂ ⊓ O
  have hzK : z ∈ K := Subgroup.mem_sup_left hz
  have hz₂K : z₂ ∈ K := Subgroup.mem_sup_right hz₂
  have hzN : z ∈ Subgroup.normalizer (W : Set G) :=
    SBc14.mem_normalizer_inf (h₁ hz) (le_normalizer_pCoreOf 2 K hzK)
  have hy : ∀ e ∈ Subgroup.zpowers z, ∃ w ∈ W, e * z₂ * e⁻¹ = z₂ * w := by
    intro e he
    have heK₁ : e ∈ K₁ := (Subgroup.zpowers_le.mpr hz) he
    have h1 : e * z₂ * e⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp (h₁ heK₁) z₂).mp hz₂
    have h2 : z₂⁻¹ * (e * z₂ * e⁻¹) ∈ K₁ := by
      have e1 : z₂⁻¹ * (e * z₂ * e⁻¹) = (z₂⁻¹ * e * z₂⁻¹⁻¹) * e⁻¹ := by group
      rw [e1]
      exact K₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (h₂ (K₂.inv_mem hz₂)) e).mp heK₁)
        (K₁.inv_mem heK₁)
    have h3 : z₂⁻¹ * (e * z₂ * e⁻¹) ∈ K₂ := K₂.mul_mem (K₂.inv_mem hz₂) h1
    exact ⟨z₂⁻¹ * (e * z₂ * e⁻¹), ⟨h3, hKO ⟨h2, h3⟩⟩, by group⟩
  have hE : IsPGroup 5 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz5]; norm_num)
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 K
  have hW2 : IsPGroup 2 W := hO2.to_le inf_le_right
  obtain ⟨w, hwW, hfix⟩ := exists_fixed_mem_coset hE hW2 (Subgroup.zpowers_le.mpr hzN) hy
  set x := z₂ * w with hx
  have hxK₂ : x ∈ K₂ := K₂.mul_mem hz₂ hwW.1
  have hxc : z * x = x * z := by
    have := hfix z (Subgroup.mem_zpowers z)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hxO : x ∉ O := by
    intro hxO
    refine not_mem_of_isPGroup_two hO2 hz₂5 ?_
    have : z₂ = x * w⁻¹ := by rw [hx]; group
    rw [this]
    exact O.mul_mem hxO (O.inv_mem hwW.2)
  have hx5 : x ^ 5 ∈ O := by
    obtain ⟨c, hc, h⟩ := exists_pow_mul_eq (le_normalizer_pCoreOf 2 K hz₂K) hwW.2 5
    have h5 : z₂ ^ 5 = 1 := hz₂5 ▸ pow_orderOf_eq_one z₂
    rw [hx, h, h5, one_mul]
    exact hc
  obtain ⟨n, hn5, -⟩ := exists_five_part hO2 hx5 hxO
  refine ⟨x ^ n, K₂.pow_mem hxK₂ n, hn5, Commute.pow_right (hxc : z * x = x * z) n, ?_⟩
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  have hgK₁ : g ∈ K₁ := (Subgroup.zpowers_le.mpr hz) hg1
  have hgK₂ : g ∈ K₂ := (Subgroup.zpowers_le.mpr (K₂.pow_mem hxK₂ n)) hg2
  have hgO : g ∈ O := hKO ⟨hgK₁, hgK₂⟩
  have hg5 : g ^ 5 = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz5, pow_orderOf_eq_one,
      one_zpow]
  by_contra hne
  have hord : orderOf g = 5 := orderOf_eq_prime hg5 hne
  exact not_mem_of_isPGroup_two hO2 hord hgO

omit [Finite G] in
theorem isSimpleGroup_oTwoQuot_of_equiv {K : Subgroup G}
    (hφ : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    IsSimpleGroup (OTwoQuot K) := by
  obtain ⟨φ⟩ := hφ
  have := SBc16.isSimpleGroup_L216
  exact φ.isSimpleGroup

theorem le_of_diag_shapeOne {K₁ K₂ J : Subgroup G} (h₁ : K₁ ≤ Subgroup.normalizer (K₂ : Set G))
    (h₂ : K₂ ≤ Subgroup.normalizer (K₁ : Set G)) (hKO : K₁ ⊓ K₂ ≤ pCoreOf 2 (K₁ ⊔ K₂))
    (hperf : oTwoUpper K₁ = K₁)
    (hφ : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hKJ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G)) {k₁ k₂ : G} (hk₁ : k₁ ∈ K₁)
    (hk₂ : k₂ ∈ K₂) (hk₁5 : orderOf k₁ = 5) {l : ℕ} (ha : k₁ * k₂ ^ l ∈ J) : K₁ ≤ J := by
  have hsimple : IsSimpleGroup (OTwoQuot K₁) := isSimpleGroup_oTwoQuot_of_equiv hφ
  obtain ⟨φ⟩ := hφ
  set K := K₁ ⊔ K₂
  set O := pCoreOf 2 K
  set N₀ := J ⊓ K
  set P := N₀ ⊔ O
  have hK₁K : K₁ ≤ K := le_sup_left
  have hK₂K : K₂ ≤ K := le_sup_right
  have hKN₀ : K ≤ Subgroup.normalizer (N₀ : Set G) := fun g hg =>
    SBc14.mem_normalizer_inf (hKJ hg) (Subgroup.le_normalizer hg)
  have hKO' : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 K
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup N₀ O ⟨hKN₀ hg, hKO' hg⟩
  have hk₁K : k₁ ∈ K := hK₁K hk₁
  have hk₂K : k₂ ∈ K := hK₂K hk₂
  have haK : k₁ * k₂ ^ l ∈ K := K.mul_mem hk₁K (K.pow_mem hk₂K l)
  have haN : k₁ * k₂ ^ l ∈ N₀ := ⟨ha, haK⟩
  have hcomm : ∀ g ∈ K₁, ⁅g, k₁⁆ ∈ P := by
    intro g hg
    have hgK : g ∈ K := hK₁K hg
    have hm : k₂ ^ l ∈ K₂ := K₂.pow_mem hk₂ l
    have hc1 : ⁅g, k₂ ^ l⁆ ∈ O := by
      refine hKO ⟨?_, ?_⟩
      · have e : ⁅g, k₂ ^ l⁆ = g * ((k₂ ^ l) * g⁻¹ * (k₂ ^ l)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact K₁.mul_mem hg ((Subgroup.mem_normalizer_iff.mp (h₂ hm) g⁻¹).mp (K₁.inv_mem hg))
      · exact K₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (h₁ hg) (k₂ ^ l)).mp hm) (K₂.inv_mem hm)
    have hc2 : k₁ * ⁅g, k₂ ^ l⁆ * k₁⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hKO' hk₁K) _).mp hc1
    have hga : ⁅g, k₁ * k₂ ^ l⁆ ∈ N₀ := by
      have h1 : g * (k₁ * k₂ ^ l) * g⁻¹ ∈ N₀ := (Subgroup.mem_normalizer_iff.mp (hKN₀ hgK) _).mp haN
      exact N₀.mul_mem h1 (N₀.inv_mem haN)
    have e : ⁅g, k₁⁆ = ⁅g, k₁ * k₂ ^ l⁆ * (k₁ * ⁅g, k₂ ^ l⁆ * k₁⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem (Subgroup.mem_sup_left hga) (P.inv_mem (Subgroup.mem_sup_right hc2))
  let π : ↥K₁ →* OTwoQuot K₁ := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K₁)
  set N₁ : Subgroup ↥K₁ := P.subgroupOf K₁ with hN₁
  have hN₁n : N₁.Normal :=
    ⟨fun n hn g => by
      rw [hN₁, Subgroup.mem_subgroupOf] at hn ⊢
      simpa using (Subgroup.mem_normalizer_iff.mp (hKP (hK₁K g.2)) _).mp hn⟩
  have hnorm : (N₁.map π).Normal := Subgroup.Normal.map hN₁n π (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₁.map π) with hbot | htop
  ·
    exfalso
    have hcen : π ⟨k₁, hk₁⟩ ∈ Subgroup.center (OTwoQuot K₁) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥K₁) q
      have hmem : π ⁅γ, (⟨k₁, hk₁⟩ : ↥K₁)⁆ ∈ N₁.map π :=
        Subgroup.mem_map_of_mem π (by rw [hN₁, Subgroup.mem_subgroupOf]; exact hcomm γ γ.2)
      rw [hbot, Subgroup.mem_bot, map_commutatorElement] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    have hz : φ (π ⟨k₁, hk₁⟩) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨q, rfl⟩ := φ.surjective x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen q]
    rw [SBc16.center_L216, Subgroup.mem_bot, map_eq_one_iff φ φ.injective] at hz
    have h1 : (⟨k₁, hk₁⟩ : ↥K₁) ∈ CFSG.Open.pCore 2 ↥K₁ := (QuotientGroup.eq_one_iff _).mp hz
    exact not_mem_of_isPGroup_two (pCoreOf_isPGroup 2 K₁) hk₁5
      ((SBc16.mem_pCore_iff_coe K₁ _).mp h1)
  ·
    have hK₁P : K₁ ≤ P := by
      intro g hg
      have hmem : π ⟨g, hg⟩ ∈ N₁.map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hmem
      have h1 : n⁻¹ * ⟨g, hg⟩ ∈ CFSG.Open.pCore 2 ↥K₁ := QuotientGroup.eq.mp hng
      have h2 : (n : G)⁻¹ * g ∈ pCoreOf 2 K₁ := (SBc16.mem_pCore_iff_coe K₁ _).mp h1
      have h3 : (n : G)⁻¹ * g ∈ O := pCoreOf_le_sup_of_normalizes h₂ h2
      have e : g = (n : G) * ((n : G)⁻¹ * g) := by group
      rw [e]
      exact P.mul_mem ((Subgroup.mem_subgroupOf.mp (hN₁ ▸ hn))) (Subgroup.mem_sup_right h3)
    have hON : O ≤ Subgroup.normalizer (N₀ : Set G) := fun o ho => hKN₀ (pCoreOf_le 2 K ho)
    have hup : oTwoUpper P ≤ N₀ :=
      Der6A.oTwoUpper_le_of_normal_sup le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
          (sup_le Subgroup.le_normalizer hON))
        (pCoreOf_isPGroup 2 K) le_sup_right le_rfl
    calc K₁ = oTwoUpper K₁ := hperf.symm
      _ ≤ oTwoUpper P := oTwoUpper_mono hK₁P
      _ ≤ N₀ := hup
      _ ≤ J := inf_le_left

set_option linter.unusedVariables false in
theorem le_of_innerSub_shapeOne (h36 : A36ForSQTK) (S : Setting146 G T M) {PQ : Subgroup G}
    (hp5 : p = 5) (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    {K₁ K₂ : Subgroup G} {s : G} (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hc₁ : K₁ ∈ cComp (mcOf T)) (hc₂ : K₂ ∈ cComp (mcOf T))
    (hφ : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    {J : Subgroup G} (hX : SQTKGroup ↥(g2_14615 K₂)) (hJc : J ∈ cComp (g2_14615 K₂))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : K₂ ≤ Subgroup.normalizer (J : Set G)) (hK₂c : ⁅J, K₂⁆ ≤ pCoreOf 2 J)
    (hKJ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (J : Set G))
    (hJn : g2_14615 K₂ ≤ Subgroup.normalizer (J : Set G))
    (hin : K₁ ⊔ K₂ ≤ innerSub J) (hnc : ¬ ⁅J, K₁⁆ ≤ pCoreOf 2 J) : K₁ ≤ J := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKG₂ : K₁ ⊔ K₂ ≤ g2_14615 K₂ := by
    have := kz_le_g2_14615 hdec hset
    rwa [hset.kz] at this
  have h₁ : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx => hKG₂ (Subgroup.mem_sup_left hx)
  have h₂ : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := fun x hx =>
    SBc16.sup_le_normalizer_of_mem_cComp hc₁ hc₂ (Subgroup.mem_sup_right hx)
  have hnle : ¬ K₁ ≤ K₂ := fun h =>
    SBc13.K₁_ne_K₂ hset (Subgroup.eq_of_le_of_card_ge h (SBc13.card_K₁ hset).symm.le)
  have hKO : K₁ ⊓ K₂ ≤ pCoreOf 2 (K₁ ⊔ K₂) :=
    (inf_le_pCoreOf_of_simple (perfect_of_mem_cComp hc₁) (isSimpleGroup_oTwoQuot_of_equiv hφ) h₁
      hnle).trans (pCoreOf_le_sup_of_normalizes h₂)
  have hgen₁ : K₁ ≤ Subgroup.closure {x | x ∈ K₁ ∧ orderOf x = 5} :=
    le_closure_five_of_sl2_component le_rfl hc₁ hφ
  have hK₁nc : ¬ K₁ ≤ cMod J := by
    intro h
    apply hnc
    refine Subgroup.commutator_le.mpr fun x hx c hc => ?_
    exact ((mem_cMod.mp (h hc)).2 x hx)
  obtain ⟨k₁, hk₁K, hk₁5, hk₁nc'⟩ := exists_five_not_mem_of_not_le hgen₁ hK₁nc
  have hz₂ : s * k₁ * s⁻¹ ∈ K₂ := by
    rw [hset.conj]
    exact mul_mem_conjSub hk₁K
  have hz₂5 : orderOf (s * k₁ * s⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective k₁
    simpa [MulAut.conj_apply, hk₁5] using this
  obtain ⟨k₂, hk₂K, hk₂5, hcomm, hind⟩ :=
    exists_commuting_five_of_inf_le h₁ h₂ hKO hk₁K hk₁5 hz₂ hz₂5
  have hk₂c : k₂ ∈ cMod J :=
    mem_cMod.mpr ⟨hK₂N hk₂K, fun x hx => hK₂c (Subgroup.commutator_mem_commutator hx hk₂K)⟩
  have hk₁in : k₁ ∈ innerSub J := hin (Subgroup.mem_sup_left hk₁K)
  have h5Z : ∀ z ∈ J, z ∈ cMod J → orderOf z ≠ 5 := fun z hzJ hzc hz5 =>
    SBc13.not_mem_of_commutes hX (h36 _ (SQTKHyp.of_sqtkGroup _ hX)) hJc hJq hz5
      (fun x hx => (mem_cMod.mp hzc).2 x hx) hzJ
  have hX2 : CFSG.Open.pRank 5 (g2_14615 K₂) ≤ 2 := by
    have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥(g2_14615 K₂)) ≤ 2 :=
      hX.1 5 (by norm_num) (by norm_num)
    rwa [pRank_top_subtype] at h2
  obtain ⟨l, hl⟩ := exists_diag_mem hX2 (le_of_mem_cComp hJc) (hKG₂ (Subgroup.mem_sup_left hk₁K))
    (hKG₂ (Subgroup.mem_sup_right hk₂K)) hk₁5 hk₂5 hcomm hind hk₂c hk₁in hk₁nc' h5Z
  exact le_of_diag_shapeOne h₁ h₂ hKO (SBc13.oTwoUpper_K₁ hset) hφ hKJ hk₁K hk₂K hk₁5 hl

end SBc17

end CFSG.Quasithin
