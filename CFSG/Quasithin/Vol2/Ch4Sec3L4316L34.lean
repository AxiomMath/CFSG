module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Star
public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Quasithin.Background.A3Structure36AQuasi

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

namespace L4316

open CFSG.LocalAnalysis.ComponentInitial in
theorem two_le_pRank_three_of_isPSL {S : Type} [Group S] [Finite S] (h : IsPSL 3 2 2 S) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let e' : S ≃* LinearFlag.projectiveSL 3 K := e.trans (Id2519.projectiveSLEquivStatedProj 3 K).symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
  have hcard := LinearThreeFourFixedNine.card_map_proj_qSub hK4
  have hel := LinearThreeFourFixedNine.isElementaryAbelian_three_of_card hcard fun x hx =>
    LinearThreeFourFixedNine.pow_three_of_mem_map_proj hK4 hx
  refine CFSG.SectionRank.le_pRank (by norm_num) le_top
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mp hel) ?_
  rw [hcard]
  norm_num

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem a318Case2_of_L34 (hF : A318Facts) (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hm : m = 2) (hL : IsPSL 3 2 2 ↥(s.star KZ)) :
    A318Case2 (starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))) := by
  have hKZGZ : KZ ≤ Subgroup.normalizer (ZS : Set G) := le_of_mem_cComp s.KZ_mem
  have hKZc : KZ ∈ cComp (Subgroup.centralizer (ZS : Set G)) :=
    cComp_mem_of_le s.KZ_mem s.KZ_cent (Subgroup.centralizer_le_normalizer _)
  have hKZn : (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKZGZ).mpr s.KZ_normal
  have h3 : 3 ∣ 2 ^ m - 1 := by
    rw [hm]
    norm_num
  rcases s.pRank_KZ_le_one hF h135 hR hC h36 h37 h38 h39 hKZc s.K₂_le_KZ hKZn Nat.prime_three
    (by norm_num) h3 with hr | ⟨-, h2⟩
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hM : CFSG.pRank 3 ↥KZ ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_top_subtype]
      exact hr
    have h' := L436.pRank_le_one_of_surjective' Nat.prime_three (by norm_num)
      (s.starHom s.KZ_le_G₀) (s.starHom_surjective s.KZ_le_G₀) hM
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h'
    have := L4316.two_le_pRank_three_of_isPSL hL
    omega
  · exact h2

theorem card_center_modO2 (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Nat.card (Subgroup.center (ModO2 KZ)) = 1 ∨ Nat.card (Subgroup.center (ModO2 KZ)) = 3 := by
  have hyp := s.sk.base.hyp
  have hH : pCoreOf 2 (Subgroup.normalizer (ZS : Set G)) ≠ ⊥ := s.inH_GZ.2
  have hstrong := lemma_1_2_1_four_strong hyp.qtke hyp.simple hyp.nonabelian h36 hH s.KZ_mem
  obtain ⟨e⟩ := modO2_mulEquiv s.KZ_mem
  have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
  set X := ↥(modO2Image (Subgroup.normalizer (ZS : Set G)) KZ) with hX
  have hqX : CFSG.IsQuasisimple X := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hcZ : Nat.card (Subgroup.center (ModO2 KZ)) = Nat.card (Subgroup.center X) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  obtain ⟨-, -, hcase, -, -⟩ := hstrong.2.1
  rcases hcase with ⟨hF, -⟩ | ⟨hFZ, -, hcard⟩
  · exfalso
    rw [A36A.generalizedFitting_eq_top hqX] at hF
    have hnil : Group.IsNilpotent ↥(⊤ : Subgroup X) := by
      rw [hF]
      infer_instance
    have : Group.IsSolvable ↥(⊤ : Subgroup X) := by
      have := hnil
      infer_instance
    have hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
      rw [← commutator_def]
      exact hqX.1.commutator_eq_top
    have hbot := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hperf
    obtain ⟨-, -, a, b, hab⟩ := hqX
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a' = 1 := (Subgroup.eq_bot_iff_forall _).mp hbot a' (Subgroup.mem_top _)
    have hb : b' = 1 := (Subgroup.eq_bot_iff_forall _).mp hbot b' (Subgroup.mem_top _)
    apply hab
    rw [ha, hb]
  · rw [hcZ, ← hFZ]
    exact hcard

theorem mem_pPrimeCore_of_mem_center
    (hSK : IsSimpleGroup ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))))
    {c : ↥KZ} (hc : (QuotientGroup.mk c : ModO2 KZ) ∈ Subgroup.center (ModO2 KZ)) :
    (⟨c, le_of_mem_cComp s.KZ_mem c.2⟩ : ↥(Subgroup.normalizer (ZS : Set G))) ∈
      CFSG.pPrimeCore 3 ↥(Subgroup.normalizer (ZS : Set G)) := by
  classical
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp s.KZ_mem
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
  set SK := starImage 3 (KZ.subgroupOf GZ) with hSKdef
  let ψ₀ : ↥KZ →* PStar 3 ↥GZ := π.comp (Subgroup.inclusion hKZGZ)
  have hrange : ψ₀.range = SK := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let ψ : ↥KZ →* ↥SK := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ₀.rangeRestrict
  have hψ : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ₀.rangeRestrict_surjective
  have hψv : ∀ k : ↥KZ, ((ψ k : ↥SK) : PStar 3 ↥GZ) = π ⟨k, hKZGZ k.2⟩ := fun k => rfl
  have hperf : Group.IsPerfect ↥SK := by
    have : Group.IsPerfect ↥KZ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp s.KZ_mem)
    exact Group.IsPerfect.ofSurjective hψ
  have hO₂3 : ∀ k : ↥KZ, (k : G) ∈ pCoreOf 2 KZ → π ⟨k, hKZGZ k.2⟩ = 1 := by
    intro k hk
    exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥GZ)
      (⟨k, hKZGZ k.2⟩ : ↥GZ)).mpr
      (Setting436Sp4.pCoreOf_subgroupOf_le_pPrimeCore (x := ⟨k, hKZGZ k.2⟩) hKZGZ s.KZ_normal hk)
  have hψc : ψ c = 1 := by
    apply L436.eq_one_of_forall_commute hperf
    intro w
    obtain ⟨k, rfl⟩ := hψ w
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hψv, hψv, ← map_mul, ← map_mul]
    have hck : (c : G) * k * (c : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 KZ := by
      have hz := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk k)
      have h1 : (QuotientGroup.mk (c * k * c⁻¹ * k⁻¹) : ModO2 KZ) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hz]
        group
      rw [QuotientGroup.eq_one_iff] at h1
      exact (mem_pCoreOf_iff' _).mpr h1
    have hmem : (c : G) * k * (c : G)⁻¹ * (k : G)⁻¹ ∈ KZ :=
      mul_mem (mul_mem (mul_mem c.2 k.2) (inv_mem c.2)) (inv_mem k.2)
    have h1 : π ⟨(c : G) * k * (c : G)⁻¹ * (k : G)⁻¹, hKZGZ hmem⟩ = 1 := hO₂3 ⟨_, hmem⟩ hck
    have e : (⟨(c : G), hKZGZ c.2⟩ * ⟨(k : G), hKZGZ k.2⟩ : ↥GZ) =
        ⟨(c : G) * k * (c : G)⁻¹ * (k : G)⁻¹, hKZGZ hmem⟩ *
          (⟨(k : G), hKZGZ k.2⟩ * ⟨(c : G), hKZGZ c.2⟩) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group
    rw [e, map_mul, h1, one_mul, map_mul]
  have h1 := congrArg Subtype.val hψc
  rw [hψv] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem center_modO2_eq_bot (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK)
    (hSK : IsSimpleGroup ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G))))) :
    Subgroup.center (ModO2 KZ) = ⊥ := by
  rcases s.card_center_modO2 h135 hR hC h36 h37 h38 h39 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (ModO2 KZ))) 3
      (by rw [h3])
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (z : ModO2 KZ)
    have hcZ : (QuotientGroup.mk c : ModO2 KZ) ∈ Subgroup.center (ModO2 KZ) := hc ▸ z.2
    have hmem := s.mem_pPrimeCore_of_mem_center hSK hcZ
    have hcop : Nat.Coprime 3 (orderOf (⟨c, le_of_mem_cComp s.KZ_mem c.2⟩ :
        ↥(Subgroup.normalizer (ZS : Set G)))) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hmem)
        CFSG.pPrimeCore_coprime_card
    have hk' : orderOf c = orderOf (⟨c, le_of_mem_cComp s.KZ_mem c.2⟩ :
        ↥(Subgroup.normalizer (ZS : Set G))) := by
      rw [← Subgroup.orderOf_coe c, ← Subgroup.orderOf_coe (⟨c, le_of_mem_cComp s.KZ_mem c.2⟩ :
        ↥(Subgroup.normalizer (ZS : Set G)))]
    have hdvd : orderOf z ∣ orderOf c := by
      rw [← Subgroup.orderOf_coe z, ← hc]
      exact orderOf_map_dvd (QuotientGroup.mk' _) c
    rw [hz, hk'] at hdvd
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)

theorem isPSL_modO2_of_L34 (hL : IsPSL 3 2 2 ↥(s.star KZ))
    (hZ : Subgroup.center (ModO2 KZ) = ⊥) : IsPSL 3 2 2 (ModO2 KZ) :=
  IsPSL.of_mulEquiv (s.mulEquiv_star_KZ.trans ((L4315.innEquiv _).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))) hL

theorem exists_config_of_L34 (h43 : Step43L34) (hF : A318Facts) (h135 : AsC135Three)
    (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2) (hL : IsPSL 3 2 2 ↥(s.star KZ)) :
    ∃ (Γ A B : Subgroup G) (α' : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))
      (P : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F))),
      Config43L34 G T M L n I H K t F ZS K₂ R₂ (Subgroup.zpowers y) KZ Γ A B α' P := by
  have hA := s.a318Case2_of_L34 hF h135 hR hC h36 h37 h38 h39 hm hL
  have hSK : IsSimpleGroup ↥(starImage 3 (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G)))) := by
    obtain ⟨s', q, -, hpslq, -⟩ := hA
    exact L436.isSimpleGroup_of_isPSLEps3q hpslq
  have hZ := s.center_modO2_eq_bot h135 hR hC h36 h37 h38 h39 hSK
  have hcard : Fintype.card F = 4 := by
    rw [s.card_F, hm]
    norm_num
  exact h43 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ s.toSetting4311 s.KZ_mem s.KZ_normal
    s.K₂_le_KZ s.KZ_cent hcard (s.isPSL_modO2_of_L34 hL hZ) s.N_R₂ s.O2_le s.R₂_eq_P₀ hA

end Setting4315

end CFSG.Quasithin.H13.Ch4
