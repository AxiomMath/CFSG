module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cJ4Orth
public import CFSG.Quasithin.Vol2.Ch11L2Q5cM23FF
public import CFSG.Quasithin.Vol2.Ch11L2Q5cUnitary

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13

@[expose] def L2GraphIso : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    L2Setting G T L I n H K k → T ≤ Subgroup.normalizer (K : Set G) →
    (IsPSL 3 2 k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K) ∨
      E2.IsSp4Prime k ↥(E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K)) →
    E2.IsDiagramNontrivial (E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H T)
      (E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H K)
      (E2.star (H ⊓ Subgroup.normalizer (L : Set G)) H (T ⊓ K)) →
    ∀ Kp Ip : Subgroup G, K ≤ Kp → FSU G T Kp Ip → ∀ _ : IsMulCommutative ↥(fsuV T Ip),
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) → ¬ Concl701FF T Kp Ip

variable {G : Type} [Group G] [Finite G]

theorem l2Graph_of
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hM : FactMathieuOrders) (hM23 : IsSimpleGroup ↥NativeSporadic.M23) (h325 : Stmt3_2_5)
    (h328 : Stmt3_2_8) (hG2 : FactG2Simple) (hiso : L2GraphIso) : L2Graph := by
  intro G _ _ T L I n H K k hS hTK htype hdiag Kp Ip hKKp hfsu hcomm hconcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 := hS.two_le
  have hKf : quasithinIsFaithfulLocal T K := l2Faithful_holds G T L I n H K k hS
  have hKl := hKf.1
  have hKpl : quasithinIsLocal T Kp := hfsu.faithful.1
  have hTKp := le_normalizer_overgroup hF h36 h37 h39 hfsu hKl hKKp hTK
  rcases hconcl with hFF | h4
  swap
  ·
    have hL0 : fsuL0 T Kp ≤ Kp :=
      conjClosure_le fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTKp ht) x).mp hx
    exact absurd h4.1 (not_lt_of_ge hL0)
  have hisoE : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) → False :=
    fun he => hiso G T L I n H K k hS hTK htype hdiag Kp Ip hKKp hfsu hcomm he hFF
  have hKH : K ≤ H := by rw [hS.gen]; exact le_sup_left
  set X := H ⊓ Subgroup.normalizer (L : Set G) with hXdef
  set ψ : ↥K →* ↥(E2.star X H K) :=
    ((QuotientGroup.mk' ((kerIn X H).subgroupOf H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have hG' := sqtkHyp_quotient_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hKpl.2.2.2
  have h312 := a312_refined hF hG' (h36 _ hG') (h37 _ hG') (h39 _ hG')
  rcases htype with hL3 | hSp
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    ·
      obtain rfl : k = 2 := by omega
      rcases overgroup_iso_or_m23_of_l34 hM hL3 hKl hKpl hKKp hS.quasisimple ψ hψs h312 with
        he | hm23
      · exact hisoE he
      · obtain ⟨e⟩ := hm23
        have hKpH : Kp ≤ Kp ⊔ T := le_sup_left
        set σ : ↥Kp →* ↥(modO2Image (Kp ⊔ T) Kp) :=
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T))).subgroupMap
            (Kp.subgroupOf (Kp ⊔ T))).comp (Subgroup.subgroupOfEquivOfLe hKpH).symm.toMonoidHom
          with hσ
        have hσs : Function.Surjective σ :=
          (MonoidHom.subgroupMap_surjective _ _).comp
            (Subgroup.subgroupOfEquivOfLe hKpH).symm.surjective
        have : IsSimpleGroup ↥(modO2Image (Kp ⊔ T) Kp) := @MulEquiv.isSimpleGroup _ _ _ _ hM23 e
        have hc : Nat.card ↥(modO2Image (Kp ⊔ T) Kp) = 2 ^ 7 * 79695 :=
          (Nat.card_congr e.toEquiv).trans (card_carrier_m23.trans (by norm_num))
        have : Group.IsPerfect ↥Kp := A36A.isPerfect_of_mem_cComp hKpl.2.1
        have : (CFSG.pCore 2 ↥Kp).Normal := CFSG.pCore_normal
        have hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ CFSG.pCore 2 ↥Kp) :=
          ⟨hfsu.quasisimple.1.commutator_eq_top, hfsu.quasisimple.2.1⟩
        have hab := nonabelian_of_perfect_surjective σ hσs
        exact m23_false_of_concl701FF h325 h328 hG2 hfsu hTKp (sup_le_normalizer_fsuV hfsu hTKp)
          hab CFSG.pCore_isPGroup hQ σ hσs hc hFF
    ·
      rcases overgroup_iso_or_a312Out hM hk2 (Or.inr (Or.inr (Or.inl hL3))) hKl hKpl hKKp
          hS.quasisimple ψ hψs h312 with he | hout
      · exact hisoE he
      · exact not_a312Out_of_isPSL3 hk3 hL3 hout
  ·
    rcases overgroup_iso_or_a312Out hM hk2 (Or.inr (Or.inr (Or.inr hSp))) hKl hKpl hKKp
        hS.quasisimple ψ hψs h312 with he | hout
    · exact hisoE he
    · exact not_a312Out_of_isPSp4 hk2 (isPSp4_of_isSp4Prime hk2 hSp) hout

end CFSG.Quasithin.Vol2.Ch11.SecB
