module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Quasithin.SteinbergBMPerfectSubnormalSignalizer
public import CFSG.Quasithin.EmptyFaithful.S14612DC
public import CFSG.Quasithin.EmptyFaithful.S146P4
public import CFSG.Quasithin.EmptyFaithful.S146P5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section KzA

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem kz_le_g2_14615 (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    conjClosure (oTwoUpper H) (mcOf T) ≤ g2_14615 K₂ := by
  rw [hset.kz]
  refine sup_le ?_ Subgroup.le_normalizer
  rcases hset.shape with ⟨hK₁, hK₂, -, -⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hle, hn⟩ := cComp_normal_span_of_le hK₂
    exact (le_cCompSpan hK₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hn)
  · intro x hx
    have hxH₁ : x ∈ H₁ := oTwoUpper_le H₁ hx
    exact normalizer_le_normalizer_oTwoUpper_P (hdec.H₁_le_normalizer_H₂ hxH₁)

theorem normalizer_kz_le_mcOf_14615 (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    Subgroup.normalizer ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) ≤ mcOf T := by
  set Kz := conjClosure (oTwoUpper H) (mcOf T) with hKz
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hGN : mcOf T ≤ Subgroup.normalizer (Kz : Set G) := le_normalizer_conjClosure _ _
  have hG1 : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG1
  have hUG : conjClosure (VZ T M) (mcOf T) ≤ mcOf T := fun u hu =>
    S.mem_mcOf_of_mem_conjClosure hG1 hu
  have hUp : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) := fun g =>
    ⟨1, Subtype.ext (by simpa using hUab.2 g g.2)⟩
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) :=
    le_pCoreOf_of_le_normalizer 2 hUG (le_normalizer_conjClosure _ _) hUp
  have hUHU : conjClosure (VZ T M) H ≤ conjClosure (VZ T M) (mcOf T) :=
    conjClosure_mono le_rfl hHG
  have hO₁Kz : oTwoUpper H₁ ≤ Kz := by
    rw [hKz, hset.kz]
    exact hset.oTwo₁.trans le_sup_left
  obtain ⟨hZ₁, -⟩ := Z_le_commutator_of_isDecP h5 S hred hdec
  have hKzG : Kz ≤ mcOf T := by
    refine conjClosure_le fun h hh x hx => ?_
    exact (mcOf T).mul_mem ((mcOf T).mul_mem hh (hHG ((oTwoUpper_le H) hx))) ((mcOf T).inv_mem hh)
  have hQ₁N : mcOf T ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
    le_normalizer_pCoreOf 2 (mcOf T)
  have h1 : ⁅conjClosure (VZ T M) H, Kz⁆ ≤ ⁅pCoreOf 2 (mcOf T), Kz⁆ :=
    Subgroup.commutator_mono (hUHU.trans hUQ) le_rfl
  have h2 : ⁅pCoreOf 2 (mcOf T), Kz⁆ ≤ pCoreOf 2 (mcOf T) :=
    S145.commutator_le_of_le_normalizer (hKzG.trans hQ₁N)
  have h3 : ⁅pCoreOf 2 (mcOf T), Kz⁆ ≤ Kz := by
    rw [Subgroup.commutator_comm]
    exact S145.commutator_le_of_le_normalizer ((pCoreOf_le 2 (mcOf T)).trans hGN)
  have hnorm : Kz ≤ Subgroup.normalizer ((pCoreOf 2 (mcOf T) ⊓ Kz : Subgroup G) : Set G) :=
    S146A.le_normalizer_of_forall_conj_mem fun g hg x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hQ₁N (hKzG hg)) x).mp hx.1,
        Kz.mul_mem (Kz.mul_mem hg hx.2) (Kz.inv_mem hg)⟩
  have h4 : pCoreOf 2 (mcOf T) ⊓ Kz ≤ pCoreOf 2 Kz :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
      (IsPGroup.to_le (pCoreOf_isPGroup 2 (mcOf T)) inf_le_left)
  have hZ : quasithinOmegaOneCenter T ≤ pCoreOf 2 Kz :=
    hZ₁.trans ((Subgroup.commutator_mono le_rfl hO₁Kz).trans (h1.trans ((le_inf h2 h3).trans h4)))
  have hP0 : pCoreOf 2 Kz ≠ ⊥ := by
    intro hbot
    have hZb : quasithinOmegaOneCenter T ≤ ⊥ := hbot ▸ hZ
    have h1 : Nat.card (quasithinOmegaOneCenter T) = 1 := by
      rw [le_bot_iff.mp hZb]
      exact Subgroup.card_bot
    have h2 := S.card_Z
    omega
  have hL : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Kz : Set G)) :=
    ⟨pCoreOf 2 Kz, hP0, pCoreOf_isPGroup 2 Kz, rfl⟩
  have hGL : mcOf T ≤ Subgroup.normalizer (pCoreOf 2 Kz : Set G) :=
    hGN.trans (normalizer_le_normalizer_pCoreOf 2 Kz)
  have hEq := S.hyp.mc_max.2 _ hL hGL
  exact (normalizer_le_normalizer_pCoreOf 2 Kz).trans (le_of_eq hEq)

theorem IsDecP.orderOf_dvd_of_odd (hp : p.Prime)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H₁) (hodd : Odd (orderOf x)) :
    orderOf x ∣ p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let x' : ↥H₁ := ⟨x, hx⟩
  let y : DihedralGroup p := e (QuotientGroup.mk x')
  have hox : orderOf x' = orderOf x := (Subgroup.orderOf_coe x').symm
  have hyx : orderOf y ∣ orderOf x := by
    have h1 : orderOf y ∣ orderOf (QuotientGroup.mk x' : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) :=
      orderOf_map_dvd e.toMonoidHom _
    have h2 : orderOf (QuotientGroup.mk x' : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) ∣ orderOf x' :=
      orderOf_map_dvd (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁)) x'
    exact h1.trans (h2.trans hox.dvd)
  have hyodd : Odd (orderOf y) := hodd.of_dvd_nat hyx
  have hyp : orderOf y ∣ p := by
    cases hy : y with
    | r i =>
      rw [DihedralGroup.orderOf_r]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left p i.val)
    | sr i =>
      rw [hy, DihedralGroup.orderOf_sr] at hyodd
      exact absurd hyodd (by decide)
  set m := orderOf y with hm
  have hm1 : y ^ m = 1 := pow_orderOf_eq_one y
  have hxm : x' ^ m ∈ (pCoreOf 2 H).subgroupOf H₁ := by
    have h1 : e (QuotientGroup.mk (x' ^ m)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow]
      exact hm1
    have h2 : (QuotientGroup.mk (x' ^ m) : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = 1 :=
      e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hxm' : x ^ m ∈ pCoreOf 2 H := by
    have := Subgroup.mem_subgroupOf.mp hxm
    simpa using this
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  obtain ⟨k, hk⟩ := hQ2 ⟨x ^ m, hxm'⟩
  have hk' : (x ^ m) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd1 : orderOf (x ^ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (x ^ m) ∣ orderOf x := orderOf_pow_dvd m
  have hodd2 : Odd (orderOf (x ^ m)) := hodd.of_dvd_nat hd2
  have hcop : Nat.Coprime (orderOf (x ^ m)) (2 ^ k) := (Odd.coprime_two_right hodd2).pow_right k
  have hone : orderOf (x ^ m) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
  have hxm1 : x ^ m = 1 := orderOf_eq_one_iff.mp hone
  exact (orderOf_dvd_of_pow_eq_one hxm1).trans hyp

theorem IsDecP.oTwoUpper_le_closure_five (hp5 : p = 5) (h : IsDecP T M H p H₀ H₁ H₂ t)
    {W : Subgroup G} (hW : oTwoUpper H₁ ≤ W) :
    oTwoUpper H₁ ≤ Subgroup.closure {x | x ∈ W ∧ orderOf x = 5} := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxH, hxodd⟩ := hx
  have hd : orderOf x ∣ p := h.orderOf_dvd_of_odd (by rw [hp5]; norm_num) hxH hxodd
  rw [hp5] at hd
  have hxW : x ∈ W := hW (mem_oTwoUpper_of_odd hxH hxodd)
  rcases (Nat.dvd_prime (by norm_num)).mp hd with h1 | h5
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hxW, h5⟩

end KzA

section KzB

theorem sl2_gf16_simple_and_five_dvd :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) ∧
      5 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  have hcardF : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcardF]; norm_num)
  refine ⟨(CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 4)).symm.isSimpleGroup, ?_⟩
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcardF]
  norm_num

variable {G : Type} [Group G] [Finite G]

theorem le_closure_five_of_simple_quotient {X K W : Subgroup G} (hKW : K ≤ W) (hK : K ∈ cComp X)
    (hQsimple : IsSimpleGroup (OTwoQuot K)) (h5Q : 5 ∣ Nat.card (OTwoQuot K)) :
    K ≤ Subgroup.closure {x | x ∈ W ∧ orderOf x = 5} := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.closure {x | x ∈ K ∧ orderOf x = 5} with hA
  have hAK : A ≤ K := (Subgroup.closure_le K).mpr fun x hx => hx.1
  have h5K : 5 ∣ Nat.card K := by
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K)
    rw [h2]
    exact Dvd.dvd.mul_right h5Q _
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 h5K
  have hconj : ∀ g ∈ K, ∀ y ∈ A, g * y * g⁻¹ ∈ A := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hg hz.1) (K.inv_mem hg), ?_⟩
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
      simpa [MulAut.conj_apply, hz.2] using this
    | one => simp
    | mul a b _ _ iha ihb => simpa [mul_assoc] using A.mul_mem iha ihb
    | inv a _ iha => simpa [mul_assoc] using A.inv_mem iha
  have hAn : (A.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g g.2 n hn⟩
  have hQ2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥K) := CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K)
  have hxQ : x ∉ CFSG.Open.pCore 2 ↥K := by
    intro hxQ
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hxQ⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h52 : 5 ∣ 2 ^ k := hx5 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h52
    omega
  let π : ↥K →* OTwoQuot K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)
  have hxA : (x : G) ∈ A :=
    Subgroup.subset_closure ⟨x.2, by rw [← hx5]; exact Subgroup.orderOf_coe x⟩
  have himg : (A.subgroupOf K).map π = ⊤ := by
    have hnorm : ((A.subgroupOf K).map π).Normal :=
      Subgroup.Normal.map hAn π (QuotientGroup.mk'_surjective _)
    have := hQsimple
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A.subgroupOf K).map π) with hbot | htop
    · exfalso
      have hxmem : π x ∈ (A.subgroupOf K).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxA)
      rw [hbot, Subgroup.mem_bot] at hxmem
      exact hxQ ((QuotientGroup.eq_one_iff x).mp hxmem)
    · exact htop
  have hKAR : ∀ k ∈ K, ∃ a ∈ A, ∃ r ∈ pCoreOf 2 K, a * r = k := by
    intro k hk
    have hmem : π ⟨k, hk⟩ ∈ (A.subgroupOf K).map π := by
      rw [himg]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hmem
    refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (a : G)⁻¹ * k, ?_, by group⟩
    have h1 : a⁻¹ * ⟨k, hk⟩ ∈ CFSG.Open.pCore 2 ↥K := QuotientGroup.eq.mp hak
    exact ⟨a⁻¹ * ⟨k, hk⟩, h1, by simp⟩
  have hKN : K ≤ Subgroup.normalizer (A : Set G) := S146A.le_normalizer_of_forall_conj_mem hconj
  have hle : K ≤ A :=
    CFSG.Quasithin.SteinbergBM.perfect_le_of_le_mul_pGroup Nat.prime_two
      (pCoreOf_isPGroup 2 K) hAK hKN hKAR le_rfl (perfect_of_mem_cComp hK)
  exact hle.trans (Subgroup.closure_mono fun y hy => ⟨hKW hy.1, hy.2⟩)

theorem le_closure_five_of_sl2_component {X K W : Subgroup G} (hKW : K ≤ W) (hK : K ∈ cComp X)
    (hφ : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    K ≤ Subgroup.closure {x | x ∈ W ∧ orderOf x = 5} := by
  obtain ⟨φ⟩ := hφ
  obtain ⟨hsimple, h5⟩ := sl2_gf16_simple_and_five_dvd
  have hQsimple : IsSimpleGroup (OTwoQuot K) := φ.isSimpleGroup
  refine le_closure_five_of_simple_quotient hKW hK hQsimple ?_
  rwa [Nat.card_congr φ.toEquiv]

end KzB

section KzFinal

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem kz_le_closure_five_14615 (S : Setting146 G T M) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hp5 : p = 5) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    conjClosure (oTwoUpper H) (mcOf T) ≤
      Subgroup.closure {x | x ∈ conjClosure (oTwoUpper H) (mcOf T) ∧ orderOf x = 5} := by
  set Kz := conjClosure (oTwoUpper H) (mcOf T) with hKz
  set A := Subgroup.closure {x | x ∈ Kz ∧ orderOf x = 5} with hA
  have hK₁Kz : K₁ ≤ Kz := by
    rw [hKz, hset.kz]
    exact le_sup_left
  have hK₂Kz : K₂ ≤ Kz := by
    rw [hKz, hset.kz]
    exact le_sup_right
  have hGN : mcOf T ≤ Subgroup.normalizer (Kz : Set G) := le_normalizer_conjClosure _ _
  have hAconj : ∀ g ∈ mcOf T, ∀ y ∈ A, g * y * g⁻¹ ∈ A := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (hGN hg) z).mp hz.1, ?_⟩
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
      simpa [MulAut.conj_apply, hz.2] using this
    | one => simp
    | mul a b _ _ iha ihb => simpa [mul_assoc] using A.mul_mem iha ihb
    | inv a _ iha => simpa [mul_assoc] using A.inv_mem iha
  have hsG : s ∈ mcOf T := S.isHTM_mcOf.1.1 hset.s_mem
  calc Kz = K₁ ⊔ K₂ := hset.kz
    _ ≤ A := by
      rcases hset.shape with ⟨hK₁, -, -, hφ⟩ | ⟨h1, h2⟩
      · refine sup_le (le_closure_five_of_sl2_component hK₁Kz hK₁ hφ) fun y hy => ?_
        have hy' : s⁻¹ * y * s ∈ K₁ := by
          rw [hset.conj] at hy
          exact mem_conjSub.mp hy
        have hmem := hAconj s hsG _ (le_closure_five_of_sl2_component hK₁Kz hK₁ hφ hy')
        simpa [mul_assoc] using hmem
      · subst h1 h2
        exact sup_le (hdec.oTwoUpper_le_closure_five hp5 hK₁Kz)
          (hdec.swap.oTwoUpper_le_closure_five hp5 hK₂Kz)

end KzFinal

theorem input14615KzP_proved (h5 : Stage1461Five) : Input14615KzP := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂
  exact ⟨kz_le_g2_14615 hdec hset, kz_le_closure_five_14615 S hdec hctx.1 hset,
    normalizer_kz_le_mcOf_14615 S h5 hred hdec hset⟩

end CFSG.Quasithin
