module

public import CFSG.RankThree.PartTwo.Sec15.Item1423ProofLocal
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
public import CFSG.RankThree.PartTwo.Sec21.Hering214EK2
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13

variable {G : Type} [Group G] [Finite G]

theorem suzukiModel_thetaQuot_of_not_three_dvd (hSz : KFacts.KPSz) {M K : Subgroup G}
    (hM : SectionFourHyp M) (hK : K ∈ thetaComponentsIn M) (hK3 : ¬ 3 ∣ Nat.card K) :
    ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (K ⧸ aschbacherSolvableCore 3 K) 2 f := by
  have hKM : K ≤ M := le_of_mem_thetaComponentsIn hK
  have hKq := Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 hK
  have hZ := Sec15.Proof1423.center_thetaQuot_eq_bot hK3
  set Kb := K ⧸ aschbacherSolvableCore 3 K
  have hsimple : IsSimpleGroup Kb := by
    have := hKq.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hnab : ∃ a b : Kb, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hKq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have h3 : ¬ 3 ∣ Nat.card Kb := fun h => hK3 (h.trans (Subgroup.card_quotient_dvd_card _))
  set e := (Subgroup.subgroupOfEquivOfLe hKM).symm
  set φ : Kb ≃* ↥(K.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf M) :=
    QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)
  have hs' : IsSimpleGroup (↥(K.subgroupOf M) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf M)) :=
    φ.symm.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := hM.kGroup (K.subgroupOf M) (aschbacherSolvableCore 3 ↥(K.subgroupOf M)) hs'
  exact hSz Kb hnab ⟨i, ⟨φ.trans f⟩⟩ h3

theorem exists_involution_centralizer_of_suzukiModel
    {A K : Subgroup G} (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {f : ℕ}
    (hSzK : CFSG.Blueprint.SuzukiModel (K ⧸ aschbacherSolvableCore 3 K) 2 f) :
    ∃ s ∈ K, orderOf s = 2 ∧ ∀ a ∈ A, a * s = s * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : ↥A →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hAK) with hρ
  set ρ' : ↥A →* MulAut (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    (Sec4.thetaQuotMulAut ↥K).comp ρ with hρ'
  obtain ⟨t, ht2, htfix⟩ := KFacts.KP7.exists_involution_fixed_of_suzukiModel hSzK ρ'
    (E := ⊤) (fun x _ => Subtype.ext (by simpa using hA x x.2))
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
  have hAp : IsPGroup 3 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hA x x.2)⟩
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥K) :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  obtain ⟨y', hy'y, hy'fix⟩ := KFacts.exists_fixed_of_coprime hAp ρ
    (aschbacherSolvableCore 3 ↥K) hθ3
    (fun g n hn => by
      have h := Sec4.map_aschbacherSolvableCore (ρ g)
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hn)
    y (fun g => htfix g (Subgroup.mem_top g))
  have hord : orderOf ((y' : ↥K) : ↥K ⧸ aschbacherSolvableCore 3 ↥K) = 2 := by rw [hy'y, ht2]
  have h2 : 2 ∣ orderOf y' := by
    rw [← hord]
    exact orderOf_map_dvd (QuotientGroup.mk' _) y'
  obtain ⟨m, hm⟩ := h2
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hm
    exact (orderOf_pos y').ne' hm
  set s : ↥K := y' ^ m with hs
  have hs2 : orderOf s = 2 := by
    rw [hs, orderOf_pow_of_dvd hm0.ne' ⟨2, by rw [hm, mul_comm]⟩, hm,
      Nat.mul_div_cancel _ hm0]
  refine ⟨(s : G), s.2, by rw [Subgroup.orderOf_coe, hs2], fun a ha => ?_⟩
  have hfix : ρ ⟨a, ha⟩ s = s := by rw [hs, map_pow, hy'fix]
  have hfix' : a * (s : G) * a⁻¹ = s := congrArg Subtype.val hfix
  calc a * (s : G) = a * (s : G) * a⁻¹ * a := by group
    _ = s * a := by rw [hfix']

theorem three_dvd_card_of_m22 {L' : Subgroup G}
    (φ : ↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) :
    3 ∣ Nat.card L' := by
  have h : 3 ∣ Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
    norm_num
  exact h.trans (Subgroup.card_quotient_dvd_card _)

theorem mem_thetaQuotCentralizer_of_m22
    (hM22 : Sec21.Hering214Even.M22E9NoInvol) {B L' : Subgroup G} (hBL' : B ≤ L')
    (hBe : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (φ : ↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)
    {s : G} (hsN : s ∈ Subgroup.normalizer (L' : Set G)) (hs2 : s ^ 2 = 1)
    (hsB : ∀ b ∈ B, b * s = s * b) : s ∈ Sec4.thetaQuotCentralizer L' := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L' with hθ
  set σ : MulAut (↥L' ⧸ θ) := Sec4.thetaQuotMulAut ↥L' (L'.normalizerMonoidHom ⟨s, hsN⟩)
    with hσ
  set τ : MulAut CFSG.Blueprint.NativeSporadic.M22 := MulAut.congr φ σ with hτ
  set ψ : ↥L' →* MulAut CFSG.Blueprint.NativeSporadic.M22 :=
    (MulAut.conj : CFSG.Blueprint.NativeSporadic.M22 →* _).comp
      (φ.toMonoidHom.comp (QuotientGroup.mk' θ)) with hψ
  set B' := B.subgroupOf L' with hB'
  set F := B'.map ψ with hF
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => Subtype.ext (hBe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
    apply Subtype.ext
    apply Subtype.ext
    have := hBe.1.is_comm.comm (⟨((x : ↥L') : G), Subgroup.mem_subgroupOf.mp x.2⟩ : ↥B)
      ⟨((y : ↥L') : G), Subgroup.mem_subgroupOf.mp y.2⟩
    show ((x : ↥L') : G) * ((y : ↥L') : G) = ((y : ↥L') : G) * ((x : ↥L') : G)
    exact congrArg Subtype.val this
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.map hB'e ψ
  have hZ : Subgroup.center CFSG.Blueprint.NativeSporadic.M22 = ⊥ :=
    CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥L') h3).2.2.1
  have hinj : ∀ x ∈ B', ψ x = 1 → x = 1 := by
    intro x hx hψx
    have h1 : MulAut.conj (φ (QuotientGroup.mk' θ x)) = 1 := hψx
    have hc : φ (QuotientGroup.mk' θ x) ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.M22 := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := DFunLike.congr_fun h1 g
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * φ (QuotientGroup.mk' θ x) = φ (QuotientGroup.mk' θ x) * g *
            (φ (QuotientGroup.mk' θ x))⁻¹ * φ (QuotientGroup.mk' θ x) := by rw [h2]
        _ = φ (QuotientGroup.mk' θ x) * g := by group
    rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hc
    have hx3 : x ^ 3 = 1 := Subtype.ext (hBe.2 _ (Subgroup.mem_subgroupOf.mp hx))
    by_contra hx1
    have hord : orderOf (⟨x, hc⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hx3 hx1
    exact hθ3 (hord ▸ orderOf_dvd_natCard _)
  have hF9 : Nat.card F = 9 := by
    set ψ' : ↥B' →* MulAut CFSG.Blueprint.NativeSporadic.M22 := ψ.comp B'.subtype with hψ'
    have hinj' : Function.Injective ψ' := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hinj x x.2 hx)
    have hFr : F = ψ'.range := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [hFr, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv, hB',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL').toEquiv, hB9]
  have hτF : τ ∈ Subgroup.centralizer (F : Set (MulAut CFSG.Blueprint.NativeSporadic.M22)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hfix : σ (QuotientGroup.mk' θ x) = QuotientGroup.mk' θ x := by
      rw [hσ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have := hsB x (Subgroup.mem_subgroupOf.mp hx)
      calc s * (x : G) * s⁻¹ = (x : G) * s * s⁻¹ := by rw [this]
        _ = x := by group
    set m := φ (QuotientGroup.mk' θ x) with hm
    have hτm : τ m = m := by
      rw [hτ]
      change φ (σ (φ.symm m)) = m
      rw [hm, MulEquiv.symm_apply_apply, hfix]
    have hψx : ψ x = MulAut.conj m := rfl
    rw [hψx]
    apply MulEquiv.ext
    intro g
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, hτm]
  have hτ2 : τ ^ 2 = 1 := by
    have hσ2 : σ ^ 2 = 1 := by
      rw [hσ, ← map_pow, ← map_pow]
      have : (⟨s, hsN⟩ : Subgroup.normalizer (L' : Set G)) ^ 2 = 1 := Subtype.ext hs2
      rw [this, map_one, map_one]
    rw [hτ, ← map_pow, hσ2, map_one]
  have hτ1 := hM22 F hFe hF9 τ hτF hτ2
  have hσ1 : σ = 1 := by
    have : MulAut.congr φ σ = MulAut.congr φ 1 := by rw [← hτ, hτ1, map_one]
    exact (MulAut.congr φ).injective this
  exact ⟨⟨s, hsN⟩, MonoidHom.mem_ker.mpr hσ1, rfl⟩

theorem false_of_mem_thetaComponentsIn_of_not_three_dvd
    (h45 : Sec4.Item4_5) (hSz : KFacts.KPSz) (hM22 : Sec21.Hering214Even.M22E9NoInvol)
    {A L' : Subgroup G} {c' : G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hc'A : c' ∈ A)
    (hS4 : SectionFourHyp (Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)))
    (hL' : L' ∈ thetaComponentsAt 3 c')
    (huniq : ∀ K ∈ thetaComponentsAt 3 c', 3 ∣ Nat.card K → K = L')
    (φ : ↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)
    (hB9 : Nat.card (A ⊓ L' : Subgroup G) = 9)
    (hodd : ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L'))
    {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G)))
    (hK3 : ¬ 3 ∣ Nat.card K) : False := by
  set B := A ⊓ L' with hBdef
  set C := Subgroup.centralizer (B : Set G) with hCdef
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    hcomm b hb.1 a ha
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hS4 hAC hAe
      ⟨3, le_rfl, by rw [hA27]; norm_num⟩ K hK
  obtain ⟨f, hSzK⟩ := suzukiModel_thetaQuot_of_not_three_dvd hSz hS4 hK hK3
  obtain ⟨s, hsK, hs2, hsA⟩ :=
    exists_involution_centralizer_of_suzukiModel (fun a ha => hAe.2 a ha) hAK hSzK
  have hsC : s ∈ C := le_of_mem_thetaComponentsIn hK hsK
  have hsB : ∀ b ∈ B, b * s = s * b := fun b hb => Subgroup.mem_centralizer_iff.mp hsC b hb
  have hsc' : s * c' = c' * s := (hsA c' hc'A).symm
  have hL's : L'.map (MulAut.conj s).toMonoidHom = L' := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj s) hL'
    have hc : (MulAut.conj s) c' = c' := by
      rw [MulAut.conj_apply, hsc', mul_inv_cancel_right]
    rw [hc] at h1
    refine huniq _ h1 ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
    exact three_dvd_card_of_m22 φ
  have hsN : s ∈ Subgroup.normalizer (L' : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hL's
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm _ x.2.1 _ y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
  have hsθ : s ∈ Sec4.thetaQuotCentralizer L' :=
    mem_thetaQuotCentralizer_of_m22 hM22 inf_le_right hBe hB9 φ hsN
      (by rw [← hs2, pow_orderOf_eq_one]) hsB
  have hsc'C : s ∈ Subgroup.centralizer ({c'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hsc'
  apply hodd
  have hord : orderOf (⟨s, Subgroup.mem_inf.mpr ⟨hsc'C, hsθ⟩⟩ :
      ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L')) = 2 := by
    rw [Subgroup.orderOf_mk, hs2]
  exact hord ▸ orderOf_dvd_natCard _

end CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB
