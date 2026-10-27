module

public import CFSG.Quasithin.Vol2.Ch7Sec77Min
public import CFSG.Quasithin.EmptyFaithful.SzN18Top

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem normalizer_le_normalizer_inf_centralizer (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ A ⊓ Subgroup.centralizer (A : Set G),
      g * x * g⁻¹ ∈ A ⊓ Subgroup.centralizer (A : Set G) := by
    intro g hg x hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem oTwoUpper_le_normalizer_cComp (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {H K : Subgroup G} (hH2 : pCoreOf 2 H ≠ ⊥)
    (hK : K ∈ cComp H) : oTwoUpper H ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke).1
  have hKH : K ≤ H := le_of_mem_cComp hK
  rcases Vol2Native.lemma_1_2_1_three hloc h37c h38c hH2 hK with hn | ⟨h2, -⟩
  · exact (oTwoUpper_le H).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  · have hidx : ((Subgroup.normalizer (K : Set G)).subgroupOf H).index = 2 := by
      rw [← A5.ncard_conjSubgroupsBy_eq_index]
      exact h2
    have hn : ((Subgroup.normalizer (K : Set G)).subgroupOf H).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxo⟩
    set q := (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) :
      ↥H ⧸ (Subgroup.normalizer (K : Set G)).subgroupOf H) with hq
    have hq1 : orderOf q ∣ 2 := by
      rw [← hidx, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard q
    have hq2 : orderOf q ∣ orderOf x := by
      have h1 : orderOf q ∣ orderOf (⟨x, hxH⟩ : ↥H) :=
        orderOf_map_dvd (QuotientGroup.mk' ((Subgroup.normalizer (K : Set G)).subgroupOf H)) _
      rwa [Subgroup.orderOf_mk] at h1
    have hq3 : orderOf q = 1 := by
      have h1 := Nat.dvd_gcd hq1 hq2
      have h2 : Nat.gcd 2 (orderOf x) = 1 := Nat.coprime_two_left.mpr hxo
      rw [h2] at h1
      exact Nat.dvd_one.mp h1
    rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff] at hq3
    exact hq3

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem isQuasisimple_K
    (h443 : Stmt4_4_3Orbit') (h36 : Vol2Native.A36CoreForSQTKCat) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp (thompsonJ H)) (hKM : ¬ K ≤ fsuM T L)
    (hKq : CFSG.IsQuasisimple ↥(autOn K (conjClosure (quasithinOmegaOneCenter
      (T ⊓ Subgroup.centralizer (Vp : Set G))) H)))
    (hKl : B56QuasisimpleList ↥(autOn K (conjClosure (quasithinOmegaOneCenter
      (T ⊓ Subgroup.centralizer (Vp : Set G))) H))) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  set U := conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer (Vp : Set G))) H
    with hUdef
  obtain ⟨hUe, hred⟩ := C.isTwoReduced_U hF
  have : IsMulCommutative ↥U := hUe.1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKH : K ∈ cComp H := S153D.mem_cComp_of_mem_cComp_thompsonJ hK
  have hKle : K ≤ H := le_of_mem_cComp hKH
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := hKle.trans hHU
  have : IsSimpleGroup G := S.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke).1
  obtain ⟨hconc, -, -⟩ := Vol2Native.lemma_1_2_1_four_core hloc h36 C.conf.pCoreOf_ne_bot hKH
  obtain ⟨e'⟩ := modO2_mulEquiv hKH
  have h34 : ¬ (A36Case3 ↥(modO2Image H K) ∨ A36Case4 ↥(modO2Image H K)) := by
    intro h34
    obtain ⟨-, hF6⟩ := SzN18.fitting_primes_of_case34 h34
    set π := InternalSec.autOnHom hKU with hπ
    have hπs : Function.Surjective π := InternalSec.autOnHom_surjective hKU
    set Q : Subgroup ↥K :=
      (CFSG.fittingSubgroup ↥(modO2Image H K)).comap (SzN18.toBar hKle) with hQdef
    have hQn : Q.Normal := Subgroup.Normal.comap inferInstance _
    have hcop3 : ∀ q ∈ Q, Nat.Coprime (orderOf q) 3 := by
      intro q hq
      have hqF : SzN18.toBar hKle q ∈ CFSG.fittingSubgroup ↥(modO2Image H K) := hq
      set k := Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image H K)) with hk
      have h3k : ¬ 3 ∣ k := fun h => (hF6 3 Nat.prime_three h).2 rfl
      have hpow : SzN18.toBar hKle (q ^ k) = 1 := by
        rw [map_pow]
        have := pow_card_eq_one'
          (G := ↥(CFSG.fittingSubgroup ↥(modO2Image H K))) (x := ⟨SzN18.toBar hKle q, hqF⟩)
        exact congrArg Subtype.val this
      obtain ⟨j, hj⟩ := SzN18.isPGroup_ker_toBar hKle (⟨q ^ k, hpow⟩ : ↥(SzN18.toBar hKle).ker)
      have hqj : q ^ (k * 2 ^ j) = 1 := by
        have := congrArg (fun z : ↥(SzN18.toBar hKle).ker => (z : ↥K)) hj
        simpa [pow_mul] using this
      have hc : Nat.Coprime (k * 2 ^ j) 3 :=
        Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3k).symm
          (Nat.Coprime.pow_left j (by decide))
      exact hc.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hqj)
    have hN : Q.map π = ⊥ := by
      have : (Q.map π).Normal := hQn.map π hπs
      exact SzN18.normal_eq_bot_of_coprime_three hKl hKq (Q.map π) fun n hn => by
        obtain ⟨q, hq, rfl⟩ := hn
        exact (hcop3 q hq).coprime_dvd_left (orderOf_map_dvd π q)
    have hQV : ∀ q ∈ Q, (q : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
      intro q hq
      have h1 : π q = 1 := by
        have : π q ∈ Q.map π := ⟨q, hq, rfl⟩
        rw [hN, Subgroup.mem_bot] at this
        exact this
      have hqU := (InternalSec.mem_ker_autOnHom hKU q).1 h1
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.V_le_U) hqU
    have hFne : Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image H K)) ≠ 1 := by
      intro h1
      rcases h34 with ⟨p, hp, hp3, -, ⟨eF⟩, -⟩ | ⟨hgf, -, ⟨eSL⟩, -⟩
      · have : Fact p.Prime := ⟨hp⟩
        have hc : Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image H K)) = p ^ 2 := by
          rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
            Fintype.card_fun, ZMod.card, Fintype.card_fin]
        rw [hc] at h1
        rcases Nat.pow_eq_one.mp h1 with h | h
        · exact hp.one_lt.ne' h
        · omega
      ·
        have hbot : CFSG.fittingSubgroup ↥(modO2Image H K) = ⊥ := Subgroup.card_eq_one.mp h1
        have hcen := CFSG.centralizer_generalizedFitting_le ↥(modO2Image H K)
        rw [hgf, hbot] at hcen
        have hX1 : Nat.card ↥(modO2Image H K) = 1 := by
          rw [← Subgroup.card_top (G := ↥(modO2Image H K))]
          refine Subgroup.card_eq_one.mpr (eq_bot_iff.mpr fun x _ => hcen ?_)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
          rw [hy, one_mul, mul_one]
        have hq1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (CFSG.fittingSubgroup ↥(modO2Image H K))
        rw [hX1, h1, mul_one] at hq1
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        have h120 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
          have h2 : (∏ i : Fin 2, (Fintype.card (ZMod 5) ^ 2 - Fintype.card (ZMod 5) ^ (i : ℕ))) /
              (Fintype.card (ZMod 5) - 1) = 120 := by
            rw [Fin.prod_univ_two, ZMod.card]
            norm_num
          exact (Matrix.card_SL_field (𝔽 := ZMod 5) 2).trans h2
        rw [← Nat.card_congr eSL.toEquiv, ← hq1] at h120
        omega
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hFne
    have hp2 : p ≠ 2 := (hF6 p hp hpdvd).1
    have : Fact p.Prime := ⟨hp⟩
    have hsurj : Function.Surjective (SzN18.toBar hKle) := by
      rintro ⟨x, ⟨y, hyK, hyx⟩⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hyK⟩, Subtype.ext hyx⟩
    have hpQ : p ∣ Nat.card ↥Q := by
      have hmap : Q.map (SzN18.toBar hKle) = CFSG.fittingSubgroup ↥(modO2Image H K) :=
        Subgroup.map_comap_eq_self_of_surjective hsurj _
      have h1 := Subgroup.card_map_dvd Q (SzN18.toBar hKle)
      rw [hmap] at h1
      exact hpdvd.trans h1
    obtain ⟨P⟩ : Nonempty (Sylow p ↥Q) := inferInstance
    have hfr := Sylow.normalizer_sup_eq_top (N := Q) P
    set PG : Subgroup G := ((P : Subgroup ↥Q).map Q.subtype).map K.subtype with hPG
    set B : Subgroup G := PG ⊓ Subgroup.centralizer (PG : Set G) with hB
    have hPp : IsPGroup p ↥PG := (P.2.map Q.subtype).map K.subtype
    have hPne : PG ≠ ⊥ := by
      rw [hPG, Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective,
        Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective]
      exact P.ne_bot_of_dvd_card hpQ
    have hBne : B ≠ ⊥ := by
      have : Nontrivial ↥PG := (Subgroup.nontrivial_iff_ne_bot PG).mpr hPne
      have := hPp.center_nontrivial
      obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥PG))
      intro hB0
      apply hz
      have hzB : ((z : ↥PG) : G) ∈ B := ⟨(z : ↥PG).2, fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)⟩
      rw [hB0, Subgroup.mem_bot] at hzB
      exact Subtype.ext (Subtype.ext hzB)
    have hBc : IsMulCommutative ↥B := ⟨⟨fun a b => Subtype.ext (a.2.2 b b.2.1).symm⟩⟩
    have hBo : Odd (Nat.card ↥B) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hPp.to_le inf_le_left)
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have hBV : B ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      intro b hb
      obtain ⟨k, hk, rfl⟩ := Subgroup.map_mono (f := K.subtype)
        (Subgroup.map_subtype_le (P : Subgroup ↥Q)) hb.1
      exact hQV k hk
    have hBM : B ≤ fsuM T L := fun b hb => S.centralizer_le_fsuM (hBV hb)
    have hNB := S.normalizer_le h443 hBM hBV hBne hBc hBo
    apply hKM
    have hKt : (⊤ : Subgroup ↥K).map K.subtype ≤ fsuM T L := by
      rw [← hfr, Subgroup.map_sup]
      refine sup_le ((Subgroup.le_normalizer_map K.subtype).trans
        ((normalizer_le_normalizer_inf_centralizer PG).trans hNB)) ?_
      rintro _ ⟨q, hq, rfl⟩
      exact S.centralizer_le_fsuM (hQV q hq)
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hKt
  rcases hconc with hcomp | h3 | h4
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hcomp.1
  · exact absurd (Or.inl h3) h34
  · exact absurd (Or.inr h4) h34

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
