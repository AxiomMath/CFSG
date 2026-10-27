module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cUnitary
public import CFSG.Quasithin.Vol2.Ch11L2Q5cF4FF
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Quasithin.Vol2.Ch11L2Q5cSzFF

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

@[expose] def L2SuzukiMovedFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k →
    IsSz k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ¬ T ≤ Subgroup.normalizer (Kp : Set G) →
      ∀ _ : IsMulCommutative ↥(fsuV T Ip), ¬ Concl701FF T Kp Ip

@[expose] def L2SuzukiMovedFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k →
    IsSz k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ¬ T ≤ Subgroup.normalizer (Kp : Set G) →
      ¬ Concl701Four T Kp Ip

variable {G : Type} [Group G] [Finite G]

theorem l2Suzuki_of
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hM : FactMathieuOrders) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (hG2 : FactG2Simple)
    (hmFF : L2SuzukiMovedFF) (hm4 : L2SuzukiMovedFour) : L2Suzuki := by
  intro G _ _ T L I n H K k hS hSz Kp Ip hKKp hfsu hcomm hconcl
  by_cases hTKp : T ≤ Subgroup.normalizer (Kp : Set G)
  swap
  · rcases hconcl with hFF | h4
    · exact hmFF G T L I n H K k hS hSz Kp Ip hKKp hfsu hTKp hcomm hFF
    · exact hm4 G T L I n H K k hS hSz Kp Ip hKKp hfsu hTKp h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 := hS.two_le
  have hKf : quasithinIsFaithfulLocal T K := l2Faithful_holds G T L I n H K k hS
  have hKl := hKf.1
  have hKpl : quasithinIsLocal T Kp := hfsu.faithful.1
  rcases hconcl with hFF | h4
  swap
  ·
    have hL0 : fsuL0 T Kp ≤ Kp :=
      conjClosure_le fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTKp ht) x).mp hx
    exact absurd h4.1 (not_lt_of_ge hL0)
  have hKH : K ≤ H := by rw [hS.gen]; exact le_sup_left
  set X := H ⊓ Subgroup.normalizer (L : Set G) with hXdef
  set ψ : ↥K →* ↥(E2.star X H K) :=
    ((QuotientGroup.mk' ((kerIn X H).subgroupOf H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have hY : L2BadType k ↥(E2.star X H K) := Or.inl hSz
  have : IsSimpleGroup ↥(E2.star X H K) := hY.isSimpleGroup hk2
  have : Group.IsPerfect ↥K := A36A.isPerfect_of_mem_cComp hKl.2.1
  have hYab := nonabelian_of_perfect_surjective ψ hψs
  have hG' := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hKpl.2.2.2
  have h312 := a312_refined hF hG' (h36 _ hG') (h37 _ hG') (h39 _ hG')
  have : Group.IsPerfect ↥Kp := A36A.isPerfect_of_mem_cComp hKpl.2.1
  have : (CFSG.pCore 2 ↥Kp).Normal := CFSG.pCore_normal
  have hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ CFSG.pCore 2 ↥Kp) :=
    ⟨hfsu.quasisimple.1.commutator_eq_top, hfsu.quasisimple.2.1⟩
  have hVN := sup_le_normalizer_fsuV hfsu hTKp
  rcases overgroup_iso_or_c3_of_not_three hM hk2 hY (not_three_dvd_card_isSz hSz)
      (lt_card_isSz hSz) hKl hKpl hKKp hS.quasisimple ψ hψs h312 with he | hc3
  ·
    obtain ⟨e⟩ := he
    obtain ⟨ψ', hψ'⟩ := exists_surjective_of_modO2_equiv hYab e ψ hψs
    exact sz_false_of_concl701FF h325 h328 hG2 hfsu hTKp hVN hYab CFSG.pCore_isPGroup hQ ψ'
      hψ' hSz hFF
  ·
    obtain ⟨f, -, h2F4, -⟩ := hc3
    have hKpH : Kp ≤ Kp ⊔ T := le_sup_left
    set σ : ↥Kp →* ↥(modO2Image (Kp ⊔ T) Kp) :=
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T))).subgroupMap (Kp.subgroupOf (Kp ⊔ T))).comp
        (Subgroup.subgroupOfEquivOfLe hKpH).symm.toMonoidHom with hσ
    have hσs : Function.Surjective σ :=
      (MonoidHom.subgroupMap_surjective _ _).comp
        (Subgroup.subgroupOfEquivOfLe hKpH).symm.surjective
    obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_2f4_simplicity _ 2 f h2F4
    obtain ⟨j, hj, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h2F4
    have hab := nonabelian_of_perfect_surjective σ hσs
    exact twoF4_false_of_concl701FF h325 h328 hG2 hfsu hTKp hVN hab CFSG.pCore_isPGroup hQ σ
      hσs hj hcard hFF

end CFSG.Quasithin.Vol2.Ch11.SecB
