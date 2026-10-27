module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverDbl
public import CFSG.Quasithin.Vol2.KGFactC31Ru
public import CFSG.Sporadic.Recognition.HeMultiplier
public import CFSG.Quasithin.Background.C48SporCoverM22

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.C48Spor
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover CFSG.Sporadic.J4.QT
open scoped commutatorElement

theorem two_pow_mul_ne (a b : ℕ) : 2 ^ a * 387072 ≠ 2 ^ b * 168 := by
  intro h
  have h1 : 2 ^ b * 168 = 2 ^ a * 2304 * 168 := by rw [← h]; ring
  have h2 : 2 ^ b = 2 ^ a * 2304 := Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have h3 : 3 ∣ 2 ^ b := h2 ▸ Dvd.dvd.mul_left (by norm_num) _
  have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h4

theorem c48SporCoverRu_holds
    {G : Type} [Group G] [Finite G] : C48SporCoverRu G := by
  intro H R M L V K h hK hc h9 hpsl
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h31 : C31Basic H R M L V K := hc.basic
  obtain ⟨hLM₀, -, hM₀K, hMK, hZ, -⟩ := hc
  set M₀ := conjClosure L M with hM₀
  rw [hLM₀] at hpsl
  have hcard168 : Nat.card (ModO2 M₀) = 168 := GoldS146R.card_of_isPSL_three_two hpsl
  have hback : V.subgroupOf K ⊓ Subgroup.center ↥K = ⊥ → V ⊓ centerOf K = ⊥ := by
    intro hcore
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxK, hxC⟩
    have hx1 : (⟨x, hxK⟩ : ↥K) ∈ V.subgroupOf K ⊓ Subgroup.center ↥K :=
      ⟨hxV, Subgroup.mem_center_iff.mpr fun g => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hxC g g.2)⟩
    rw [hcore, Subgroup.mem_bot] at hx1
    exact congrArg Subtype.val hx1
  apply hback
  have hKperf : commutator ↥K = ⊤ := hK.2.2.1
  have hKp : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKperf
  obtain ⟨hsK, -⟩ := h9
  obtain ⟨eK⟩ := id hsK
  have hle2 : Nat.card (Subgroup.center ↥K) ≤ 2 := by
    obtain ⟨hpos, hle⟩ := CFSG.Sporadic.Recognition.RuMultiplier.card_griessHopfMultiplier_J_le
      Certificates.certificate15024 Certificates.certificate15026
    have e' : ↥K ⧸ Subgroup.center ↥K ≃*
        ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Recognition.RuMultiplier.ruVec) :=
      (eK.trans ruEquivP).trans ruJEquivP.symm
    have hd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess
      (S := ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Recognition.RuMultiplier.ruVec)) hKp e'
    exact (Nat.le_of_dvd hpos hd).trans hle
  rcases Nat.lt_or_ge (Nat.card (Subgroup.center ↥K)) 2 with h1 | h2
  · have hZ1 : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_le _ (by omega)
    rw [hZ1, inf_bot_eq]
  have hZ2 : Nat.card (Subgroup.center ↥K) = 2 := le_antisymm hle2 h2
  have hKX := K_le_sporX (H := H) hK.1
  have hM0ne : img (sporN H K) M₀ ≠ ⊥ := fun hb =>
    img_V_ne_bot h h31 (le_bot_iff.mp (hb ▸ img_mono h.V_le))
  have hsK' : IsSporadic .Ru ↥(img (sporN H K) K) := IsSporadic.of_mulEquiv (kStarEquiv hKX) hsK
  have hCS := centralizer_kStar_eq_bot (commutator_eq_of_isComponentOf hK) hKX
  obtain ⟨-, hStop, -⟩ := KGC31.Ru.exists_equiv (img_K_normal H K) hsK' hCS
  obtain ⟨e, hcfg⟩ := KGC31.Ru.config_ru_insp (img (sporN H K) K) (img (sporN H K) M₀)
    (img (sporN H K) R) (img (sporN H K) M) (img (sporN H K) V) (img_K_normal H K) hsK' hCS
    (img_mono h31.1) (img_M0_perfect h h31) hM0ne (exists_cComp_img h h31)
    (isPGroup_img h.pgroup) (img_mono h.le_M)
    (img_le_normalizer (le_normalizer_conjClosure L M)) (img_le_normalizer (c2_9_two h).1)
    (img_isSylowTwoOf h h31) (img_mono h.V_le) (img_V_ne_bot h h31)
    (isElemAbelian_img h.V_elem) (img_V_comm h h31) (img_V_le_center h h31)
    (normalizer_inf_le_img_M h h31) (normalizer_img_R_le h h31) (not_img_K_le h hK h31)
  have hM0X := M0_le_sporX h h31
  have hcardM₀ : ∃ a, Nat.card ↥M₀ = 2 ^ a * Nat.card ↥(img (sporN H K) M₀) := by
    set φ := imgHom (N := sporN H K) hM0X
    have hφ := imgHom_surjective (N := sporN H K) hM0X
    have hk2 : IsPGroup 2 ↥φ.ker := by
      intro y
      have hy := (mem_ker_imgHom (N := sporN H K) hM0X (y : ↥M₀)).mp y.2
      rw [mem_sporN] at hy
      have hyZ : ((y : ↥M₀) : G) ∈ centerOf K := ⟨hM₀K (y : ↥M₀).2, hy⟩
      obtain ⟨k, hk⟩ := hZ ⟨_, hyZ⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this))⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hk2
    refine ⟨a, ?_⟩
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hφ).toEquiv, ha, mul_comm]
  have hcardO₂ : ∃ b, Nat.card ↥M₀ = 2 ^ b * 168 := by
    have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥M₀) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hp
    refine ⟨b, ?_⟩
    rw [(CFSG.pCore 2 ↥M₀).card_eq_card_quotient_mul_card_subgroup, hb, mul_comm]
    exact congrArg (2 ^ b * ·) hcard168
  rcases hcfg with ⟨hVe, hMe, -⟩ | ⟨-, hMe, -⟩
  swap
  · exfalso
    obtain ⟨a, ha⟩ := hcardM₀
    obtain ⟨b, hb⟩ := hcardO₂
    rw [hMe, KGC31.Ru.card_img e KGC31.Ru.M64_le_ruP, KGC31.Ru.card_M64] at ha
    exact two_pow_mul_ne a b (ha.symm.trans hb)
  obtain ⟨q, hqx⟩ : ∃ q : ↥K →* ↥ruP,
      ∀ k : ↥K, q k = e.symm ((⟨k, hKX k.2⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ sporN H K) :=
    ⟨e.symm.toMonoidHom.comp ((QuotientGroup.mk' (sporN H K)).comp
      (Subgroup.inclusion hKX)), fun _ => rfl⟩
  have hq : Function.Surjective q := by
    intro g
    have hmem : e g ∈ img (sporN H K) K := by rw [hStop]; exact Subgroup.mem_top _
    obtain ⟨x, hxK, hx⟩ := mem_img.1 hmem
    refine ⟨⟨x, hxK⟩, ?_⟩
    rw [hqx]
    have : ((⟨(x : G), hKX hxK⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ sporN H K) = e g := by
      rw [← hx]
    rw [this, MulEquiv.symm_apply_apply]
  have hqker : q.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, hqx, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, mem_sporN,
      Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hk g
      exact Subtype.ext (hk g g.2)
    · intro hk g hg
      exact congrArg Subtype.val (hk ⟨g, hg⟩)
  have hZne : Subgroup.center ↥K ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hZ2]
    norm_num
  obtain ⟨⟨t, htZ⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have ht1 : t ≠ 1 := fun h1 => ht1' (Subtype.ext h1)
  have ht2 : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := by
      rw [← hZ2]
      exact Subgroup.orderOf_dvd_natCard _ htZ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1
    · exact h1
  have hZt : Subgroup.center ↥K = Subgroup.zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr htZ) ?_).symm
    rw [Nat.card_zpowers, ht2, hZ2]
  have hker : q.ker = Subgroup.zpowers t := hqker.trans hZt
  have hcen : Subgroup.zpowers t ≤ Subgroup.center ↥K := hZt ▸ le_rfl
  obtain ⟨eL, nL, he, hconj, het, hE, hN0, hN1⟩ := exists_lifts hq ht2 hker hcen
  have hqV : ∀ v : ↥K, (v : G) ∈ V →
      ((q v : ↥ruP) : Equiv.Perm (Fin 4060)) ∈ ruESub := by
    intro v hv
    have h1 : ((⟨v, hKX v.2⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ sporN H K) ∈
        img (sporN H K) V := mk_mem_img hv
    rw [hVe, KGC31.Ru.mem_img] at h1
    rw [hqx]
    exact h1
  have hqM : ∀ m : ↥K, (m : G) ∈ M₀ →
      ((q m : ↥ruP) : Equiv.Perm (Fin 4060)) ∈ ruN := by
    intro m hm
    have h1 : ((⟨m, hKX m.2⟩ : ↥(sporX H K)) : ↥(sporX H K) ⧸ sporN H K) ∈
        img (sporN H K) M₀ := mk_mem_img hm
    rw [hMe, KGC31.Ru.mem_img] at h1
    rw [hqx]
    exact h1
  have hNlift : ∀ g ∈ ruN, ∃ w ∈ Subgroup.closure {nL 0, nL 1},
      ((q w : ↥ruP) : Equiv.Perm (Fin 4060)) = g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨nL 0, Subgroup.subset_closure (Set.mem_insert _ _), hN0⟩
      · exact ⟨nL 1, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), hN1⟩
    | one => exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w * w', Subgroup.mul_mem _ hw hw', by rw [map_mul]; rfl⟩
    | inv x _ hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w⁻¹, Subgroup.inv_mem _ hw, by rw [map_inv]; rfl⟩
  have hVc : ⁅V.subgroupOf K, M₀.subgroupOf K⁆ = V.subgroupOf K := by
    rw [← C48Spor.commutator_subgroupOf_of_le (h.V_le.trans hM₀K) hM₀K, h.V_comm]
  rw [← hqker]
  refine inf_ker_eq_bot q ht2 hker hcen he hconj het (fun v hv => ?_) (fun m hm => ?_) hVc
  · have h1 := hqV v hv
    rcases mem_ruESub.1 h1 with h0 | ⟨k, hk, hke⟩
    · exact ⟨0, by rw [eta_zero, map_one]; exact Subtype.ext h0⟩
    · obtain ⟨c, hc⟩ := hE k hk
      exact ⟨c, Subtype.ext (by rw [hc, hke])⟩
  · obtain ⟨w, hw, hwm⟩ := hNlift _ (hqM m hm)
    exact ⟨w, hw, Subtype.ext hwm.symm⟩

theorem c48SporCoverFact_holds
    {G : Type} [Group G] [Finite G] : C48SporCoverFact G :=
  c48SporCoverFact_of_ru c48SporCoverRu_holds

end CFSG.Quasithin.C48Cover

end
