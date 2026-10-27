module

public import CFSG.RankThree.PartTwo.Sec17.Item1730Chosen
public import CFSG.RankThree.PartTwo.KFacts.KS17J2Aut
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.KFacts.KS14HJLocal
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_normalizerMonoidHom_of_mem {K : Subgroup G} (k : K) :
    Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer k.2⟩) =
      MulAut.conj (k : ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem exists_inv_mul_mem_thetaQuotCentralizer (hJout : KFacts.KS17J2AutThree)
    {K : Subgroup G}
    (hJ : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2))
    {b : G} (hb : b ∈ Subgroup.normalizer (K : Set G)) (hb3 : b ^ 3 = 1) :
    ∃ k ∈ K, k⁻¹ * b ∈ Sec4.thetaQuotCentralizer K := by
  have h3 : ((Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom) ⟨b, hb⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hb⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext hb3
    rw [this, map_one]
  obtain ⟨q, hq⟩ := hJout _ hJ _ h3
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hdN : (k : G)⁻¹ * b ∈ Subgroup.normalizer (K : Set G) := mul_mem (inv_mem hkN) hb
  refine ⟨k, k.2, Subgroup.mem_map.mpr ⟨⟨_, hdN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩⟩
  have he : (⟨(k : G)⁻¹ * b, hdN⟩ : Subgroup.normalizer (K : Set G)) =
      (⟨k, hkN⟩ : Subgroup.normalizer (K : Set G))⁻¹ * ⟨b, hb⟩ := rfl
  rw [he, map_mul, map_inv]
  change (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨k, hkN⟩))⁻¹ *
    ((Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom) ⟨b, hb⟩ = 1
  rw [thetaQuotMulAut_normalizerMonoidHom_of_mem k, ← hq, inv_mul_cancel]

theorem inf_thetaQuotCentralizer_le {K : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K) = ⊥) :
    K ⊓ Sec4.thetaQuotCentralizer K ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  rintro g ⟨hgK, hg⟩
  obtain ⟨-, hgl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hg
  have hc : ((⟨g, hgK⟩ : K) : ↥K ⧸ aschbacherSolvableCore 3 ↥K) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨t, ht, hte⟩ := hgl l l.2
    have hte' : (t : G) = (l : G)⁻¹ * (g * l * g⁻¹) := hte
    have hmem := (aschbacherSolvableCore_normal 3 K).conj_mem t ht (⟨g, hgK⟩⁻¹)
    convert hmem using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hte', inv_inv]
    group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact ⟨⟨g, hgK⟩, hc, rfl⟩

omit [Finite G] in
theorem pow_three_mem_of_mem_normalizer {K : Subgroup G} {b k : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hb3 : b ^ 3 = 1) (hk : k ∈ K) :
    (b * k) ^ 3 ∈ K := by
  have e : (b * k) ^ 3 = (b * k * b⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) * (b ^ 3 * k) := by
    rw [pow_three]
    group
  rw [e, hb3, one_mul]
  have hb2 : b ^ 2 ∈ Subgroup.normalizer (K : Set G) := pow_mem hb 2
  exact mul_mem (mul_mem ((Subgroup.mem_normalizer_iff.mp hb k).mp hk)
    ((Subgroup.mem_normalizer_iff.mp hb2 k).mp hk)) hk

theorem false_of_le_thetaQuotCentralizer (h415 : Sec4.Item4_15)
    (hFE : partTwoF G = partTwoE G) {K : Subgroup G}
    (hJ : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2))
    {R : Subgroup G} (hRe : CFSG.Assembly.IsElemAbelian 3 R) (hR9 : Nat.card R = 9)
    (hRc : R ≤ Sec4.thetaQuotCentralizer K) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 ↥K with hNdef
  obtain ⟨-, -, hN3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥K)
      Nat.prime_three
  have hRN : R ≤ Subgroup.normalizer (K : Set G) :=
    hRc.trans (Sec6.thetaQuotCentralizer_le_normalizer K)
  have htriv : ∀ r ∈ R, ∀ x : K, ∀ hx : r * (x : G) * r⁻¹ ∈ K,
      ((⟨_, hx⟩ : K) : ↥K ⧸ N) = (x : ↥K ⧸ N) := by
    intro r hr x hx
    obtain ⟨-, hrl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hRc hr)
    obtain ⟨t, ht, hte⟩ := hrl x x.2
    rw [eq_comm, QuotientGroup.eq]
    have hxt : x⁻¹ * (⟨_, hx⟩ : K) = t := Subtype.ext hte.symm
    rw [hxt]
    exact ht
  let α : R →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  have hα : ∀ (r : R) (x : K), ((α r x : K) : G) = r * x * r⁻¹ := fun r x => rfl
  have hαN : ∀ r : R, ∀ n ∈ N, α r n ∈ N := by
    intro r n hn
    have h1 : K.subtype (α r n) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
      change ((α r n : K) : G) ∈ _
      rw [hα]
      exact (Subgroup.mem_normalizer_iff.mp
        (Sec6.normalizer_le_normalizer_theta K (hRN r.2)) _).mp ⟨n, hn, rfl⟩
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp h1
  have hR3 : IsPGroup 3 R := fun g => ⟨1, Subtype.ext (by simpa using hRe.2 g g.2)⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hR3 α N hαN hN3
  have hcover : ∀ q : ↥K ⧸ N, ∃ c : K,
      (c : G) ∈ Subgroup.centralizer (R : Set G) ∧ (c : ↥K ⧸ N) = q := by
    intro q
    have hq : q ∈ {q : ↥K ⧸ N | ∀ r : R,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN r q = q} := by
      show ∀ r : R, _
      intro r
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      exact htriv r r.2 x (α r x).2
    rw [hlift] at hq
    obtain ⟨c, hc, hce⟩ := hq
    refine ⟨c, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_, hce⟩
    have h1 : r * (c : G) * r⁻¹ = c := congrArg Subtype.val (hc ⟨r, hr⟩)
    calc r * (c : G) = r * c * r⁻¹ * r := by group
      _ = c * r := by rw [h1]
  have hcardX : Nat.card (↥K ⧸ N) = 604800 := KFacts.KS14.card_eq_of_j2 hJ
  obtain ⟨Fb, hFb9⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K ⧸ N) 3 (n := 2)
    (by rw [hcardX]; norm_num)
  have hFb9' : Nat.card Fb = 9 := by rw [hFb9]; norm_num
  obtain ⟨P, hFbP, -, -⟩ := KFacts.KS14.j2_exists_sylow_of_card_nine h415 hJ hFb9'
  obtain ⟨⟨⟨-, -, hexp⟩, -⟩, -⟩ := h415 (↥K ⧸ N) hJ P _ rfl _ rfl
  have hFbe : CFSG.Assembly.IsElemAbelian 3 Fb := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hFb9, fun y hy => ?_⟩
    have := Monoid.pow_exponent_eq_one (⟨y, hFbP hy⟩ : (P : Subgroup (↥K ⧸ N)))
    rw [hexp] at this
    exact congrArg Subtype.val this
  obtain ⟨x, y, z, hxy, -, -, hS⟩ :=
    Set.ncard_eq_three.mp (KFacts.KS14.j2_maxInvariant_two_ncard h415 hJ P hFbP hFb9')
  obtain ⟨Vb, hVbmax, hVb1⟩ : ∃ V ∈ maxInvariantPiSubgroups ⊤ Fb (piOf 2), V ≠ ⊥ := by
    by_cases hx : x = ⊥
    · refine ⟨y, by rw [hS]; simp, fun hy => hxy (hx.trans hy.symm)⟩
    · exact ⟨x, by rw [hS]; simp, hx⟩
  obtain ⟨-, hVb2, hFbVb⟩ := hVbmax.1
  have hVbp : IsPGroup 2 Vb := (isPiSubgroup_piOf_iff Nat.prime_two Vb).mp hVb2
  set F₁ : Subgroup K := (Subgroup.centralizer (R : Set G)).subgroupOf K ⊓
    Fb.comap (QuotientGroup.mk' N) with hF₁
  have hF₁map : F₁.map (QuotientGroup.mk' N) = Fb := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun q hq => ?_
    obtain ⟨c, hcR, rfl⟩ := hcover q
    exact ⟨c, ⟨Subgroup.mem_subgroupOf.mpr hcR, hq⟩, rfl⟩
  have h9F₁ : 3 ^ 2 ∣ Nat.card F₁ := by
    have h := Subgroup.card_map_dvd F₁ (QuotientGroup.mk' N)
    rwa [hF₁map, hFb9] at h
  obtain ⟨S, hS9⟩ := Sylow.exists_subgroup_card_pow_prime (G := F₁) 3 h9F₁
  set S' : Subgroup K := S.map F₁.subtype with hS'
  have hS'F₁ : S' ≤ F₁ := Subgroup.map_subtype_le S
  have hS'9 : Nat.card S' = 9 := by
    rw [hS', Subgroup.card_map_of_injective F₁.subtype_injective, hS9]
    norm_num
  have hS'p : IsPGroup 3 S' := IsPGroup.of_card (n := 2) (by rw [hS'9]; norm_num)
  have hinj : Set.InjOn (QuotientGroup.mk' N) (S' : Set K) :=
    CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hS'p
  have hS'Fb : ∀ s ∈ S', QuotientGroup.mk' N s ∈ Fb := fun s hs => (hS'F₁ hs).2
  have hS'R : ∀ s ∈ S', (s : G) ∈ Subgroup.centralizer (R : Set G) := fun s hs =>
    Subgroup.mem_subgroupOf.mp (hS'F₁ hs).1
  have hS'e : CFSG.Assembly.IsElemAbelian 3 S' := by
    refine ⟨⟨⟨fun u v => Subtype.ext (hinj (mul_mem u.2 v.2) (mul_mem v.2 u.2) ?_)⟩⟩,
      fun s hs => hinj (pow_mem hs 3) (one_mem _) ?_⟩
    · simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hFbe.1.is_comm.comm ⟨_, hS'Fb u u.2⟩ ⟨_, hS'Fb v v.2⟩)
    · rw [map_pow, map_one]
      exact hFbe.2 _ (hS'Fb s hs)
  set F : Subgroup G := S'.map K.subtype with hFdef
  have hFK : F ≤ K := Subgroup.map_subtype_le _
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := Sec4.Census.isElemAbelian_map_subtype hS'e
  have hF9 : Nat.card F = 9 := by
    rw [hFdef, Subgroup.card_map_of_injective K.subtype_injective, hS'9]
  have hFR : ∀ f ∈ F, ∀ r ∈ R, f * r = r * f := by
    rintro _ ⟨s, hs, rfl⟩ r hr
    exact (Subgroup.mem_centralizer_iff.mp (hS'R s hs) r hr).symm
  have hZ := KFacts.KS14.center_eq_bot_of_j2 h415 hJ
  obtain ⟨-, hNθ3⟩ := Sec6.theta_solvable_and_not_dvd K
  have hFR1 : F ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgF, hgR⟩
    have hgθ := inf_thetaQuotCentralizer_le hZ ⟨hFK hgF, hRc hgR⟩
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hord : orderOf g = 3 := orderOf_eq_prime (hRe.2 g hgR) hg1
    have h3 := Subgroup.orderOf_dvd_natCard _ hgθ
    rw [hord] at h3
    exact hNθ3 h3
  set T := F ⊔ R with hT
  have hTe : CFSG.Assembly.IsElemAbelian 3 T := Sec13.isElemAbelian_sup hFe hRe hFR
  have hT81 : Nat.card T = 81 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F R hFR).1
    rw [hFR1, Subgroup.card_bot, mul_one, hF9, hR9] at h
    exact h
  set V₀ : Subgroup G := (Vb.comap (QuotientGroup.mk' N)).map K.subtype with hV₀
  have hV₀card : Nat.card V₀ = Nat.card N * Nat.card Vb := by
    rw [hV₀, Subgroup.card_map_of_injective K.subtype_injective]
    exact QuotientGroup.card_preimage_mk N (Vb : Set (↥K ⧸ N))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVbp
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hVb1 (Subgroup.card_eq_one.mp hm)
  have hcop : Nat.Coprime 3 (Nat.card V₀) := by
    rw [hV₀card, hm]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
      (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card V₀ := by
    rw [hV₀card, hm]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hFV₀ : F ≤ Subgroup.normalizer (V₀ : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨w, hw, rfl⟩
    refine ⟨s * w * s⁻¹, ?_, rfl⟩
    show QuotientGroup.mk' N (s * w * s⁻¹) ∈ Vb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hFbVb (hS'Fb s hs)) _).mp hw
  have hRV₀ : R ≤ Subgroup.normalizer (V₀ : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem ?_
    rintro r hr _ ⟨w, hw, rfl⟩
    have hx : r * (w : G) * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hRN hr) _).mp w.2
    refine ⟨⟨_, hx⟩, ?_, rfl⟩
    show QuotientGroup.mk' N ⟨_, hx⟩ ∈ Vb
    rw [QuotientGroup.mk'_apply, htriv r hr w hx]
    exact hw
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := sup_le hFV₀ hRV₀
  have hT3 : IsPGroup 3 T := fun g => ⟨1, Subtype.ext (by simpa using hTe.2 g g.2)⟩
  obtain ⟨U, hTU, hU1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two T V₀ hT3 hTV₀ hcop h2
  have hU2 : IsPGroup 2 ((U : Subgroup V₀).map V₀.subtype) := U.isPGroup'.map V₀.subtype
  obtain ⟨E, hE27⟩ := Sylow.exists_subgroup_card_pow_prime (G := T) 3 (n := 3)
    (by rw [hT81]; norm_num)
  have hET : E.map T.subtype ≤ T := Subgroup.map_subtype_le E
  have hEmem : E.map T.subtype ∈ partTwoE G := by
    refine ⟨⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from congrArg Subtype.val
      (hTe.1.is_comm.comm ⟨u, hET u.2⟩ ⟨v, hET v.2⟩))⟩⟩, fun u hu => hTe.2 u (hET hu)⟩, ?_,
      _, hU1, hU2, hET.trans hTU⟩
    rw [Subgroup.card_map_of_injective T.subtype_injective, hE27]
    norm_num
  obtain ⟨M, hTM, hM⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hTe
  have hMF : M ∈ partTwoF G :=
    ⟨hM.1, fun B hB hMB => (hM.2 hB hMB).antisymm hMB, _, hEmem, hET.trans hTM⟩
  rw [hFE] at hMF
  have hdvd := Subgroup.card_dvd_of_le hTM
  rw [hT81, hMF.2.1] at hdvd
  norm_num at hdvd

theorem le_zpowers_sup_of_j2 (h415 : Sec4.Item4_15) (hJout : KFacts.KS17J2AutThree)
    (hFE : partTwoF G = partTwoE G) {K : Subgroup G}
    (hJ : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2))
    {a : G} (haK : a ∉ K) {B : Subgroup G} (hBe : CFSG.Assembly.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) (haB : a ∈ B) (hBK : B ≤ Subgroup.normalizer (K : Set G)) :
    B ≤ Subgroup.zpowers a ⊔ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := KFacts.KS14.center_eq_bot_of_j2 h415 hJ
  obtain ⟨-, hNθ3⟩ := Sec6.theta_solvable_and_not_dvd K
  set H := B ⊔ K with hH
  set D := H ⊓ Sec4.thetaQuotCentralizer K with hD
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := sup_le hBK Subgroup.le_normalizer
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := inf_le_left.trans hHK
  have hDKH : D ⊔ K = H := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le (fun b hb => ?_) le_sup_right)
    obtain ⟨k, hk, hkd⟩ :=
      exists_inv_mul_mem_thetaQuotCentralizer hJout hJ (hBK hb) (hBe.2 b hb)
    have hkH : k ∈ H := Subgroup.mem_sup_right hk
    have hkdH : k⁻¹ * b ∈ H := mul_mem (inv_mem hkH) (Subgroup.mem_sup_left hb)
    have hb' : b = k * (k⁻¹ * b) := by group
    rw [hb']
    exact mul_mem (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left ⟨hkdH, hkd⟩)
  have h1 := Sec6.card_sup_mul_card_inf hBK
  have h2 := Sec6.card_sup_mul_card_inf hDK
  rw [hDKH] at h2
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have key : Nat.card D * Nat.card (B ⊓ K : Subgroup G) =
      27 * Nat.card (D ⊓ K : Subgroup G) := by
    have e : Nat.card D * Nat.card K * Nat.card (B ⊓ K : Subgroup G) =
        27 * Nat.card (D ⊓ K : Subgroup G) * Nat.card K := by
      calc Nat.card D * Nat.card K * Nat.card (B ⊓ K : Subgroup G)
          = Nat.card H * Nat.card (D ⊓ K : Subgroup G) * Nat.card (B ⊓ K : Subgroup G) := by
            rw [h2]
        _ = Nat.card H * Nat.card (B ⊓ K : Subgroup G) * Nat.card (D ⊓ K : Subgroup G) := by
            ring
        _ = 27 * Nat.card (D ⊓ K : Subgroup G) * Nat.card K := by
            rw [h1, hB27]
            ring
    have e' : Nat.card D * Nat.card (B ⊓ K : Subgroup G) * Nat.card K =
        27 * Nat.card (D ⊓ K : Subgroup G) * Nat.card K := by
      rw [← e]
      ring
    exact Nat.eq_of_mul_eq_mul_right hKpos e'
  have hD9 : ¬ 9 ∣ Nat.card D := by
    intro h9D
    obtain ⟨R₀, hR₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 3 (n := 2)
      (by norm_num; exact h9D)
    set R : Subgroup G := R₀.map D.subtype with hRdef
    have hRD : R ≤ D := Subgroup.map_subtype_le _
    have hR9 : Nat.card R = 9 := by
      rw [hRdef, Subgroup.card_map_of_injective D.subtype_injective, hR₀]
      norm_num
    have hRK : ∀ g ∈ R, g ∈ K → g = 1 := by
      intro g hgR hgK
      have hgθ := inf_thetaQuotCentralizer_le hZ ⟨hgK, (hRD hgR).2⟩
      have ho1 : orderOf g ∣ 3 ^ 2 := by
        have := Subgroup.orderOf_dvd_natCard R hgR
        rwa [hR9] at this
      have ho2 : orderOf g ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
        Subgroup.orderOf_dvd_natCard _ hgθ
      have hcop : Nat.Coprime (3 ^ 2) (Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hNθ3)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop ho1 ho2)
    have hRe : CFSG.Assembly.IsElemAbelian 3 R := by
      refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hR9]; norm_num),
        fun r hr => hRK _ (pow_mem hr 3) ?_⟩
      have hrH : r ∈ ((B ⊔ K : Subgroup G) : Set G) := (hRD hr).1
      rw [Subgroup.coe_mul_of_left_le_normalizer_right B K hBK] at hrH
      obtain ⟨b, hb, k, hk, rfl⟩ := Set.mem_mul.mp hrH
      exact pow_three_mem_of_mem_normalizer (hBK hb) (hBe.2 b hb) hk
    exact false_of_le_thetaQuotCentralizer h415 hFE hJ hRe hR9 fun r hr => (hRD hr).2
  have hBKdvd : Nat.card (B ⊓ K : Subgroup G) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ K ≤ B)
    rwa [hB27] at this
  have hBK27 : Nat.card (B ⊓ K : Subgroup G) ≠ 27 := by
    intro h
    have hBKB : B ⊓ K = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hB27])
    have haBK : a ∈ B ⊓ K := by
      rw [hBKB]
      exact haB
    exact haK haBK.2
  have h9 : Nat.card (B ⊓ K : Subgroup G) = 9 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hBKdvd
    interval_cases i
    · exfalso
      rw [hi', pow_zero, mul_one] at key
      exact hD9 ⟨3 * Nat.card (D ⊓ K : Subgroup G), by omega⟩
    · exfalso
      rw [hi', pow_one] at key
      exact hD9 ⟨Nat.card (D ⊓ K : Subgroup G), by omega⟩
    · rw [hi']
      norm_num
    · exact absurd (hi'.trans (by norm_num)) hBK27
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hBe.2 a haB) fun h => haK (h ▸ K.one_mem)
  have hcomm : ∀ x ∈ B ⊓ K, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBe.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, (Subgroup.zpowers_le.mpr haB) hy⟩)
  have hdisj : (B ⊓ K) ⊓ Subgroup.zpowers a = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_right).trans
      (Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three ha3 haK).le)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, h9, Nat.card_zpowers, ha3] at hcard
  have hle : (B ⊓ K) ⊔ Subgroup.zpowers a ≤ B := sup_le inf_le_left (Subgroup.zpowers_le.mpr haB)
  have heq : (B ⊓ K) ⊔ Subgroup.zpowers a = B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hB27])
  rw [← heq]
  exact sup_le (inf_le_right.trans le_sup_right) le_sup_left

theorem ks17HJConjugacy_of (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (hJ2 : KFacts.KS17J2NotList)
    (hJout : KFacts.KS17J2AutThree) : KFacts.KS17HJConjugacy := by
  intro G _ _ A c L hD hJ a ha B hB hBC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK, hJK, haK, huniq⟩ :=
    exists_hj_data h131 hspor hSLC h134 h48 h415 hJs hJ2 hD hJ ha
  have hFE : partTwoF G = partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  obtain ⟨haA, ha3c, -⟩ := zpowers_mem_omegaA_iff.mp ha
  have ha3o : orderOf a = 3 := by
    rw [← Nat.card_zpowers]
    exact ha3c
  have ha3 : a ^ 3 = 1 := by
    rw [← ha3o]
    exact pow_orderOf_eq_one a
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have haB : a ∈ B := Sec15.mem_of_mem_partTwoF (hFE ▸ hB) ha3 hBC
  have h3K : 3 ∣ Nat.card K := by
    have h1 := KFacts.KS14.card_eq_of_j2 hJK
    have h2 : Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) ∣ Nat.card K :=
      Subgroup.card_quotient_dvd_card _
    rw [h1] at h2
    exact (by norm_num : 3 ∣ 604800).trans h2
  have hNK : ∀ g ∈ Subgroup.centralizer ({a} : Set G),
      g ∈ Subgroup.normalizer (K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmem := map_mem_thetaComponentsAt (MulAut.conj g) hK.1
    have hga : (MulAut.conj g) a = a := by
      rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    rw [hga] at hmem
    refine huniq _ hmem ?_
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := fun b hb => hNK b (hBC hb)
  have hAK := le_zpowers_sup_of_j2 h415 hJout hFE hJK haK hD.isElemAbelian
    hD.mem_partTwoE.2.1 haA hK.2.1
  have hBK := le_zpowers_sup_of_j2 h415 hJout hFE hJK haK hB.1 hB.2.1 haB hBN
  have hzC : a ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => Subgroup.mem_centralizer_singleton_iff.mp (hKC hh)
  obtain ⟨-, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥K)
      Nat.prime_three
  obtain ⟨g, hgK, hgB⟩ := KFacts.KS14.j2_exists_conjugate_of_card_twentySeven_of_quot h415 hθ3
    hJK hzC haK ha3 hAK hBK haA haB hD.mem_partTwoE.2.1 hB.2.1
  refine ⟨g⁻¹, inv_mem (hKC hgK), ?_⟩
  rw [hgB]
  rfl

theorem rank3II_17_30_of_item1728 (h1728 : Item1728) (h131 : Item131)
    (hspor : SporadicModels131) (hSLC : SLTwoCenter) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hJ2 : KFacts.KS17J2NotList) (hJout : KFacts.KS17J2AutThree) : Item1730 :=
  rank3II_17_30_of_inputs h1728 h131 hspor hSLC h134 h48 h415 hJs hJ2
    (ks17HJConjugacy_of h131 hspor hSLC h134 h48 h415 hJs hJ2 hJout)

end CFSG.RankThree.PartTwo.Sec17
