module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cBadOrd
public import CFSG.Quasithin.Vol2.Ch11SecA02Ctx
public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34Out
public import CFSG.Quasithin.Vol2.Ch11SecBL2F
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_centralizer_of_normalizer {V : Subgroup G} {t x : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hw : t⁻¹ * v * t ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) v).mp hv
    simpa using this
  have hc : t⁻¹ * v * t * x = x * (t⁻¹ * v * t) := Subgroup.mem_centralizer_iff.mp hx _ hw
  calc v * (t * x * t⁻¹) = t * (t⁻¹ * v * t * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * v * t)) * t⁻¹ := by rw [hc]
    _ = t * x * t⁻¹ * v := by group

theorem fsuL0_le_normalizer_fsuV {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip) :
    fsuL0 T Kp ≤ Subgroup.normalizer (fsuV T Ip : Set G) :=
  CFSG.Quasithin.le_normalizer_conjClosure_of_le hfsu.irrPlus.2.2.1
    (le_normalizer_conjClosure Kp T)

theorem autOn_fsuL0_ne_bot {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip) :
    autOn (fsuL0 T Kp) (fsuV T Ip) ≠ ⊥ := by
  intro hb
  have hN := fsuL0_le_normalizer_fsuV hfsu
  have hC : fsuL0 T Kp ≤ Subgroup.centralizer (fsuV T Ip : Set G) := by
    intro x hx
    have h1 : conjAct (fsuV T Ip) ⟨x, hN hx⟩ ∈ autOn (fsuL0 T Kp) (fsuV T Ip) :=
      ⟨⟨x, hN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.mp h1
  have hI : ⁅Ip, fsuL0 T Kp⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro i hi x hx
    have hxi : i * x = x * i :=
      Subgroup.mem_centralizer_iff.mp (hC hx) i (le_conjClosure Ip T hi)
    rw [Subgroup.mem_bot, commutatorElement_def, hxi]
    group
  exact hfsu.irrPlus.2.1 (hfsu.irrPlus.2.2.2.1.symm.trans hI)

theorem autOn_ne_bot_of_fsu {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip) :
    autOn Kp (fsuV T Ip) ≠ ⊥ := by
  intro hb
  apply autOn_fsuL0_ne_bot hfsu
  have hKpN : Kp ≤ Subgroup.normalizer (fsuV T Ip : Set G) :=
    (le_conjClosure Kp T).trans (fsuL0_le_normalizer_fsuV hfsu)
  have hTN : T ≤ Subgroup.normalizer (fsuV T Ip : Set G) := le_normalizer_conjClosure Ip T
  have hC : Kp ≤ Subgroup.centralizer (fsuV T Ip : Set G) := by
    intro x hx
    have h1 : conjAct (fsuV T Ip) ⟨x, hKpN hx⟩ ∈ autOn Kp (fsuV T Ip) :=
      ⟨⟨x, hKpN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.mp h1
  have hC0 : fsuL0 T Kp ≤ Subgroup.centralizer (fsuV T Ip : Set G) :=
    conjClosure_le fun t ht x hx => conj_mem_centralizer_of_normalizer (hTN ht) (hC hx)
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_bot]
  exact A4.conjAct_eq_one_iff.mpr (hC0 (Subgroup.mem_subgroupOf.mp hy))

theorem autOn_eq_autOn_fsuL0 {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip)
    (hs : IsSimpleGroup ↥(autOn (fsuL0 T Kp) (fsuV T Ip))) :
    autOn Kp (fsuV T Ip) = autOn (fsuL0 T Kp) (fsuV T Ip) := by
  have hKpc : Kp ∈ cComp (Kp ⊔ T) := hfsu.faithful.1.2.1
  have hKpL0 : Kp ≤ fsuL0 T Kp := le_conjClosure Kp T
  have hL0X : fsuL0 T Kp ≤ Kp ⊔ T := conjClosure_le fun t ht x hx =>
    (Kp ⊔ T).mul_mem ((Kp ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hx))
      ((Kp ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  have hsn : IsSubnormal Kp (fsuL0 T Kp) :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hKpc) hKpL0 hL0X
  have hsn' := A4.autOn_subnormal (V := fsuV T Ip) hsn
  have hle : autOn Kp (fsuV T Ip) ≤ autOn (fsuL0 T Kp) (fsuV T Ip) := A4.autOn_mono hKpL0
  have hne := autOn_ne_bot_of_fsu hfsu
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  · exfalso
    obtain ⟨P, hPlt, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hsn' hlt
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf (autOn (fsuL0 T Kp) (fsuV T Ip)))
      with h | h
    · apply hne
      rw [eq_bot_iff]
      intro a ha
      have hmem : (⟨a, hle ha⟩ : ↥(autOn (fsuL0 T Kp) (fsuV T Ip))) ∈
          P.subgroupOf (autOn (fsuL0 T Kp) (fsuV T Ip)) := Subgroup.mem_subgroupOf.mpr (hKP ha)
      rw [h, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
    · apply not_le_of_gt hPlt
      intro a ha
      have hmem : (⟨a, ha⟩ : ↥(autOn (fsuL0 T Kp) (fsuV T Ip))) ∈
          P.subgroupOf (autOn (fsuL0 T Kp) (fsuV T Ip)) := by
        rw [h]
        trivial
      exact Subgroup.mem_subgroupOf.mp hmem

theorem autOn_fsuL0_of_concl701J4 (hM : FactMathieuOrders) {T Kp Ip : Subgroup G}
    (hfsu : FSU G T Kp Ip) [IsMulCommutative ↥(fsuV T Ip)] (hJ : Concl701J4 T Kp Ip) :
    IsSimpleGroup ↥(autOn (fsuL0 T Kp) (fsuV T Ip)) ∧
      Nat.card ↥(autOn (fsuL0 T Kp) (fsuV T Ip)) = 244823040 := by
  have hM24 : IsSimpleGroup ↥NativeSporadic.M24 := hM.2.2.1
  have hM24c : Nat.card ↥NativeSporadic.M24 = 244823040 := hM.2.2.2
  obtain ⟨-, -, -, -, ⟨π, hπ⟩, -⟩ := hJ
  have hLB : fsuL0 T Kp ≤ fsuM T Kp := Subgroup.le_normalizer
  have hsub : autOn (fsuL0 T Kp) (fsuV T Ip) ≤ autOn (fsuM T Kp) (fsuV T Ip) :=
    Subgroup.map_mono fun _ hx => hLB hx
  have hne := autOn_fsuL0_ne_bot hfsu
  have := SecA.autOn_normal_subgroupOf (A := fsuL0 T Kp) (B := fsuM T Kp) (V := fsuV T Ip) le_rfl
  have hne' : ∃ y : ↥(autOn (fsuM T Kp) (fsuV T Ip)), y ≠ 1 := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    refine ⟨⟨y, hsub hy⟩, fun h1 => hy1 ?_⟩
    have h2 : y = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hinj := @SecA.injective_of_isSimpleGroup _ _ _ _ hM24 π hπ.1 hne'
  have hB : IsSimpleGroup ↥(autOn (fsuM T Kp) (fsuV T Ip)) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hM24 (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  have hc : Nat.card ↥(autOn (fsuM T Kp) (fsuV T Ip)) = Nat.card ↥NativeSporadic.M24 :=
    @SecA.card_eq_of_simple_quot _ _ _ _ hM24 π hπ.1 hne'
  have heq := SecA.eq_of_normal_of_isSimpleGroup hsub hB hne
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hB
  · rw [heq, hc, hM24c]

theorem autOn_fsuL0_of_concl701Orth {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip)
    [IsMulCommutative ↥(fsuV T Ip)] (hO : Concl701Orth T Kp Ip) :
    ∃ m : ℕ, 2 ≤ m ∧ IsSimpleGroup ↥(autOn (fsuL0 T Kp) (fsuV T Ip)) ∧
      Nat.card ↥(autOn (fsuL0 T Kp) (fsuV T Ip)) = ordA 1 (2 ^ (2 * m)) := by
  obtain ⟨m, hm, K, _, _, _, hK, π, hπ⟩ := hO
  have hs : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    SecA.isSimpleGroup_statedSL (SecA.isSimpleGroup_SL_two hK (by omega))
  have hne : ∃ y : ↥(autOn (fsuL0 T Kp) (fsuV T Ip)), y ≠ 1 :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (autOn_fsuL0_ne_bot hfsu)
  have hinj := @SecA.injective_of_isSimpleGroup _ _ _ _ hs π hπ.1 hne
  have hc1 : Nat.card ↥(autOn (fsuL0 T Kp) (fsuV T Ip)) =
      Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    @SecA.card_eq_of_simple_quot _ _ _ _ hs π hπ.1 hne
  have hc2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) =
      2 ^ (2 * m) * (2 ^ (2 * (2 * m)) - 1) := by
    rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact SecA.card_SL_two hK
  refine ⟨m, by omega, @MulEquiv.isSimpleGroup _ _ _ _ hs
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm, ?_⟩
  rw [hc1, hc2, ordA_one_two_pow_eq (n := 2 * m) (by omega), ← pow_mul, mul_comm (2 * m) 2]

theorem card_carrier_m23 :
    Nat.card (NativeSporadic.Carrier .M23) = 10200960 :=
  CFSG.Sporadic.Schreier.m23_card

theorem false_of_surjective_simple_overgroup
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hM : FactMathieuOrders) {T L I : Subgroup G} {n : ℕ} {H K : Subgroup G} {k : ℕ}
    (hS : L2Setting G T L I n H K k)
    (hY : L2BadType k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K))
    {Kp Ip : Subgroup G} (hKKp : K ≤ Kp) (hfsu : FSU G T Kp Ip)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (ψS : ↥Kp →* S)
    (hψS : Function.Surjective ψS)
    (h1 : Nat.card ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) ≠ Nat.card S)
    (h2 : ∀ j : ℕ, 1 ≤ j → ordTwistedF4 (2 ^ (2 * j + 1)) ≠ Nat.card S)
    (h3 : ¬ Nat.card S ∣ 10200960) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 := hS.two_le
  have hKf : quasithinIsFaithfulLocal T K := l2Faithful_holds G T L I n H K k hS
  have hKl := hKf.1
  have hKpl : quasithinIsLocal T Kp := hfsu.faithful.1
  have hKpc : Kp ∈ cComp (Kp ⊔ T) := hKpl.2.1
  have hKH : K ≤ H := by rw [hS.gen]; exact le_sup_left
  set X := H ⊓ Subgroup.normalizer (L : Set G) with hXdef
  set ψ : ↥K →* ↥(E2.star X H K) :=
    ((QuotientGroup.mk' ((kerIn X H).subgroupOf H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have : IsSimpleGroup ↥(E2.star X H K) := hY.isSimpleGroup hk2
  have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  have hYab := nonabelian_of_perfect_surjective ψ hψs
  have : Group.IsPerfect ↥Kp := A36A.isPerfect_of_mem_cComp hKpc
  have : (CFSG.pCore 2 ↥Kp).Normal := CFSG.pCore_normal
  have hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ CFSG.pCore 2 ↥Kp) :=
    ⟨hfsu.quasisimple.1.commutator_eq_top, hfsu.quasisimple.2.1⟩
  have hSab := nonabelian_of_perfect_surjective ψS hψS
  have hG' := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hKpl.2.2.2
  have h312 := a312_refined hF hG' (h36 _ hG') (h37 _ hG') (h39 _ hG')
  have hiso : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) → False := by
    rintro ⟨e⟩
    obtain ⟨ψ', hψ'⟩ := exists_surjective_of_modO2_equiv hYab e ψ hψs
    obtain ⟨e'⟩ :=
      nonempty_mulEquiv_of_two_surjective hYab hSab CFSG.pCore_isPGroup hQ ψ' hψ' ψS hψS
    exact h1 (Nat.card_congr e'.toEquiv)
  rcases hY with hSz | hU | hL3 | hSp
  ·
    rcases overgroup_iso_or_c3_of_not_three hM hk2 (Or.inl hSz) (not_three_dvd_card_isSz hSz)
        (lt_card_isSz hSz) hKl hKpl hKKp hS.quasisimple ψ hψs h312 with he | hc3
    · exact hiso he
    · obtain ⟨f, -, h2F4, -⟩ := hc3
      have hKpH : Kp ≤ Kp ⊔ T := le_sup_left
      set σ : ↥Kp →* ↥(modO2Image (Kp ⊔ T) Kp) :=
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T))).subgroupMap
          (Kp.subgroupOf (Kp ⊔ T))).comp (Subgroup.subgroupOfEquivOfLe hKpH).symm.toMonoidHom
        with hσ
      have hσs : Function.Surjective σ :=
        (MonoidHom.subgroupMap_surjective _ _).comp
          (Subgroup.subgroupOfEquivOfLe hKpH).symm.surjective
      obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_2f4_simplicity _ 2 f h2F4
      obtain ⟨j, hj, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h2F4
      have hab := nonabelian_of_perfect_surjective σ hσs
      obtain ⟨e'⟩ :=
        nonempty_mulEquiv_of_two_surjective hab hSab CFSG.pCore_isPGroup hQ σ hσs ψS hψS
      exact h2 j hj (hcard.symm.trans (Nat.card_congr e'.toEquiv))
  ·
    rcases overgroup_iso_or_a312Out hM hk2 (Or.inr (Or.inl hU)) hKl hKpl hKKp hS.quasisimple ψ
        hψs h312 with he | hout
    · exact hiso he
    · exact not_a312Out_of_isPSU3 hk2 hU hout
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    ·
      obtain rfl : k = 2 := by omega
      rcases overgroup_iso_or_m23_of_l34 hM hL3 hKl hKpl hKKp hS.quasisimple ψ hψs h312 with
        he | hm23
      · exact hiso he
      · obtain ⟨e₁⟩ := modO2_mulEquiv hKpc
        obtain ⟨e₂⟩ := hm23
        have hle := le_ker_of_simple hSab CFSG.pCore_isPGroup ψS hψS
        set ψ₀ : ↥Kp ⧸ CFSG.pCore 2 ↥Kp →* S := QuotientGroup.lift _ ψS hle with hψ₀
        have hψ₀s : Function.Surjective ψ₀ := by
          intro y
          obtain ⟨x, rfl⟩ := hψS y
          exact ⟨QuotientGroup.mk x, rfl⟩
        have hdvd := Subgroup.card_dvd_of_surjective hψ₀s
        rw [Nat.card_congr (e₁.trans e₂).toEquiv, card_carrier_m23] at hdvd
        exact h3 hdvd
    ·
      rcases overgroup_iso_or_a312Out hM hk2 (Or.inr (Or.inr (Or.inl hL3))) hKl hKpl hKKp
          hS.quasisimple ψ hψs h312 with he | hout
      · exact hiso he
      · exact not_a312Out_of_isPSL3 hk3 hL3 hout
  ·
    rcases overgroup_iso_or_a312Out hM hk2 (Or.inr (Or.inr (Or.inr hSp))) hKl hKpl hKKp
        hS.quasisimple ψ hψs h312 with he | hout
    · exact hiso he
    · exact not_a312Out_of_isPSp4 hk2 (isPSp4_of_isSp4Prime hk2 hSp) hout

theorem l2NotJ4Orth_of
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hM : FactMathieuOrders) : L2NotJ4Orth := by
  intro G _ _ T L I n H K k hS hY Kp Ip hKKp hfsu hcomm
  have hk2 := hS.two_le
  have hKpV : Kp ≤ Subgroup.normalizer (fsuV T Ip : Set G) :=
    (le_conjClosure Kp T).trans (fsuL0_le_normalizer_fsuV hfsu)
  refine ⟨fun hJ => ?_, fun hO => ?_⟩
  ·
    obtain ⟨hs, hc⟩ := autOn_fsuL0_of_concl701J4 hM hfsu hJ
    have heq := autOn_eq_autOn_fsuL0 hfsu hs
    have : IsSimpleGroup ↥(autOn Kp (fsuV T Ip)) := by
      rw [heq]
      exact hs
    have hc' : Nat.card ↥(autOn Kp (fsuV T Ip)) = 244823040 := by
      rw [heq]
      exact hc
    refine false_of_surjective_simple_overgroup hF h36 h37 h39 hM hS hY hKKp hfsu
      (InternalSec.autOnHom hKpV) (InternalSec.autOnHom_surjective hKpV) ?_ ?_ ?_
    · rw [hc']
      exact card_l2BadType_ne_m24 hk2 hY
    · intro j _
      rw [hc']
      exact ordTwistedF4_ne_m24 (by omega)
    · rw [hc']
      decide
  ·
    obtain ⟨m, hm, hs, hc⟩ := autOn_fsuL0_of_concl701Orth hfsu hO
    have heq := autOn_eq_autOn_fsuL0 hfsu hs
    have : IsSimpleGroup ↥(autOn Kp (fsuV T Ip)) := by
      rw [heq]
      exact hs
    have hc' : Nat.card ↥(autOn Kp (fsuV T Ip)) = ordA 1 (2 ^ (2 * m)) := by
      rw [heq]
      exact hc
    refine false_of_surjective_simple_overgroup hF h36 h37 h39 hM hS hY hKKp hfsu
      (InternalSec.autOnHom hKpV) (InternalSec.autOnHom_surjective hKpV) ?_ ?_ ?_
    · rw [hc']
      exact card_l2BadType_ne_psl2 hk2 (by omega) hY
    · intro j _
      rw [hc']
      exact ordTwistedF4_ne_ordA (by omega) le_rfl (by omega)
    · rw [hc']
      exact not_ordA_one_dvd_m23 hm

end CFSG.Quasithin.Vol2.Ch11.SecB
