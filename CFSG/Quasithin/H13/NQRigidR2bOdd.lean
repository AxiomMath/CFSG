module

public import CFSG.Quasithin.H13.NQRigidR2b
public import CFSG.Quasithin.H13.Sp4OddPower
public import CFSG.Quasithin.H13.NQRigidAsmSubgroupOf
public import CFSG.Quasithin.H13.NQRigidAsmTransport
public import CFSG.Quasithin.H13.NQRigidFacts
public import CFSG.Quasithin.H13.NQRigidObl
public import CFSG.Quasithin.H13.NQRigidR2bTools

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Equiv CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped Pointwise IsMulCommutative

theorem oddOrder_transport_pow {C : Type*} [Group C] [Finite C] {f : ℕ} (hf : 2 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = 2 ^ f) (ψ : C ≃* StatedProj (StatedSp 2 k)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {P₀ U₀ : Subgroup C}
    (hU₀ : ∃ U : Sylow 2 C, (U : Subgroup C) = U₀) (hPexp : ∀ y ∈ P₀, y ^ p = 1)
    (hPnc : ¬ IsCyclic P₀) (hPU : (P₀ : Set C) * U₀ = U₀ * P₀) {γ : MulAut C}
    (hγP : P₀.map γ.toMonoidHom = P₀) {r : ℕ} (hr : Odd r) (hγr : γ ^ r = 1) :
    ∃ m : ℕ, ∀ y ∈ P₀, γ y = y ^ m := by
  classical
  obtain ⟨U, hU⟩ := hU₀
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  set U' : Sylow 2 (StatedProj (StatedSp 2 k)) := U.mapSurjective hψs with hU'def
  have hU' : (U' : Subgroup (StatedProj (StatedSp 2 k))) = U₀.map ψ.toMonoidHom := by
    rw [hU'def, Sylow.coe_mapSurjective, hU]
  set A := P₀.map ψ.toMonoidHom with hA
  have hAexp : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hPexp y hy, map_one]
  have hAnc : ¬ IsCyclic A := fun hc =>
    hPnc (isCyclic_of_surjective (P₀.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.toMonoidHom
      (MulEquiv.surjective _))
  have hAU : (A : Set (StatedProj (StatedSp 2 k))) *
        ((U' : Subgroup (StatedProj (StatedSp 2 k))) : Set (StatedProj (StatedSp 2 k))) =
      ((U' : Subgroup (StatedProj (StatedSp 2 k))) : Set (StatedProj (StatedSp 2 k))) *
        (A : Set (StatedProj (StatedSp 2 k))) := by
    rw [hU', hA, coe_map ψ.toMonoidHom P₀, coe_map ψ.toMonoidHom U₀, ← Set.image_mul, hPU,
      Set.image_mul]
  set α : MulAut (StatedProj (StatedSp 2 k)) := MulAut.congr ψ γ with hαdef
  have hαapp : ∀ y : C, α (ψ y) = ψ (γ y) := fun y => by
    rw [hαdef]
    simp [MulAut.congr_apply]
  have hαA : A.map α.toMonoidHom = A := by
    rw [hA, map_map]
    conv_rhs => rw [← hγP, map_map]
    congr 1
    exact MonoidHom.ext fun y => hαapp y
  have hαr : α ^ r = 1 := by rw [hαdef, ← map_pow, hγr, map_one]
  obtain ⟨m, hm⟩ := Sp4.oddOrder_acts_by_pow hf hk hp hp5 U' A hAexp hAnc hAU hr hαr hαA
  refine ⟨m, fun y hy => ψ.injective ?_⟩
  rw [← hαapp, hm (ψ y) ⟨y, hy, rfl⟩, map_pow]

theorem sylow_action_pow_of_oddOrder {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H} (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D)
    {K : Subgroup H} (hKn : K.Normal) {X : Subgroup H} (hXD : X ≤ D)
    (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {f : ℕ} (hf : 2 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = 2 ^ f)
    (e : (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃* StatedProj (StatedSp 2 k))
    {P : Subgroup H} (hP : IsSylowOf p P X) (hPexp : ∀ x ∈ P, x ^ p = 1) (hPnc : ¬ IsCyclic P)
    {n₀ : H} (hnP : n₀ ∈ normalizer (P : Set H)) {r : ℕ} (hr : Odd r) (hnr : n₀ ^ r = 1) :
    ∃ m : ℕ, ∀ x ∈ P, n₀ * x * n₀⁻¹ = x ^ m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have := hKn
  obtain ⟨N, hNc, hN, ι, -⟩ := exists_centerPreimage_compat K hKn hp hp2 hZ
  obtain ⟨hσinj, ⟨U, hU⟩, hPU, -⟩ :=
    SteinbergCC.original_local_sylow_prime_action_is_quotient_of_common_normalizer_restriction
      hp hp2 Q hQD hXD hXn hXK hXA hN hP
  have hPK : P ≤ K := hP.le.trans hXK
  set γ : MulAut (K ⧸ N) := CFSG.SectionRank.Ccomm.autQuotient N (MulAut.conjNormal n₀)
    with hγdef
  have hγmk : ∀ (x : H) (hx : x ∈ K), γ (QuotientGroup.mk' N (⟨x, hx⟩ : K)) =
      QuotientGroup.mk' N (⟨n₀ * x * n₀⁻¹, hKn.conj_mem x hx n₀⟩ : K) := by
    intro x hx
    rw [hγdef, QuotientGroup.mk'_apply, CFSG.SectionRank.Ccomm.autQuotient_mk]
    congr 1
  have hγP : ((P.subgroupOf K).map (QuotientGroup.mk' N)).map γ.toMonoidHom =
      (P.subgroupOf K).map (QuotientGroup.mk' N) := by
    have hle : ((P.subgroupOf K).map (QuotientGroup.mk' N)).map γ.toMonoidHom ≤
        (P.subgroupOf K).map (QuotientGroup.mk' N) := by
      rintro _ ⟨_, ⟨⟨x, hxK⟩, hx, rfl⟩, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hγmk]
      exact ⟨⟨n₀ * x * n₀⁻¹, hKn.conj_mem x hxK n₀⟩,
        (mem_normalizer_iff.mp hnP x).mp (mem_subgroupOf.mp hx), rfl⟩
    exact eq_of_le_of_card_ge hle
      (by rw [card_map_of_injective (f := γ.toMonoidHom) γ.injective])
  have hγr : γ ^ r = 1 := by
    have h1 : γ = ((CFSG.SectionRank.Ccomm.autQuotient N).comp MulAut.conjNormal) n₀ := rfl
    rw [h1, ← map_pow, hnr, map_one]
  have hP₀exp : ∀ y ∈ (P.subgroupOf K).map (QuotientGroup.mk' N), y ^ p = 1 := by
    rintro _ ⟨⟨x, hxK⟩, hx, rfl⟩
    rw [← map_pow]
    have h1 : (⟨x, hxK⟩ : K) ^ p = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hPexp x (mem_subgroupOf.mp hx))
    rw [h1, map_one]
  have hrange : ((QuotientGroup.mk' N).comp (P.subgroupOf K).subtype).range =
      (P.subgroupOf K).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hP₀nc : ¬ IsCyclic ((P.subgroupOf K).map (QuotientGroup.mk' N)) := by
    intro hc
    let eA : P.subgroupOf K ≃* (P.subgroupOf K).map (QuotientGroup.mk' N) :=
      (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
    have : IsCyclic (P.subgroupOf K) :=
      isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective
    exact hPnc (isCyclic_of_surjective (subgroupOfEquivOfLe hPK).toMonoidHom
      (subgroupOfEquivOfLe hPK).surjective)
  obtain ⟨m, hm⟩ := oddOrder_transport_pow hf hk (ι.symm.trans e) hp hp5 ⟨U, hU⟩ hP₀exp hP₀nc
    hPU hγP hr hγr
  refine ⟨m, fun x hx => ?_⟩
  have hxK : x ∈ K := hPK hx
  have hyP : n₀ * x * n₀⁻¹ ∈ P := (mem_normalizer_iff.mp hnP x).mp hx
  have hyK : n₀ * x * n₀⁻¹ ∈ K := hPK hyP
  have hpowP : x ^ m ∈ P := pow_mem hx _
  have hpowK : x ^ m ∈ K := hPK hpowP
  have hσx : QuotientGroup.mk' N (⟨x, hxK⟩ : K) ∈ (P.subgroupOf K).map (QuotientGroup.mk' N) :=
    ⟨⟨x, hxK⟩, hx, rfl⟩
  have h1 := hm _ hσx
  have h3 : (QuotientGroup.mk' N (⟨x, hxK⟩ : K)) ^ m =
      QuotientGroup.mk' N (⟨x ^ m, hpowK⟩ : K) := by
    rw [← map_pow]
    rfl
  rw [hγmk, h3] at h1
  have h4 := @hσinj ⟨⟨n₀ * x * n₀⁻¹, hyK⟩, hyP⟩ ⟨⟨x ^ m, hpowK⟩, hpowP⟩ h1
  exact congrArg (fun z : (P.subgroupOf K) => ((z : K) : H)) h4

variable {G : Type} [Group G] [Finite G]

theorem normalizerFrattiniConj_ne_one_of_not_mem_radical
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {l : G} (hl : l ∈ L) (hlR : (⟨l, hl⟩ : L) ∉ CFSG.solvableRadical L)
    (hln : l ∈ normalizer (X : Set G)) : normalizerFrattiniConj X ⟨l, hln⟩ ≠ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hLN : L ≤ normalizer (X : Set G) :=
    le_normalizer.trans (NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc)
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXA⟩
  have : CFSG.IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  set W := (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) with hWdef
  set α : L →* (Additive W ≃ₗ[ZMod p] Additive W) :=
    (NQSetup.mulAutLinear p W).comp ((normalizerFrattiniConj X).comp (inclusion hLN)) with hα
  have hα1 : α ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 := congrArg (fun f : L →* (Additive W ≃ₗ[ZMod p] Additive W) => f ⟨l, hlL⟩) h1
    simp only [MonoidHom.one_apply, hα, MonoidHom.comp_apply] at h2
    rw [← map_one (NQSetup.mulAutLinear p W)] at h2
    have h3 := NQSetup.mulAutLinear_injective p W h2
    rwa [show inclusion hLN ⟨(l : G), hlL⟩ = l from Subtype.ext rfl] at h3
  have hWdim : Module.finrank (ZMod p) (Additive W) = 2 := NQSetup.finrank_additive_eq_two hW
  obtain ⟨hR, -, -, -⟩ := NQSetup.ccomponent_plane_radical (by omega) hLC hWdim α hα1
  intro h1
  apply hlR
  rw [hR]
  left
  have h2 : inclusion hLN ⟨l, hl⟩ = ⟨l, hln⟩ := Subtype.ext rfl
  simp only [hα, MonoidHom.comp_apply, h2, h1, map_one]

omit [Finite G] in
theorem pow_eq_one_of_isSylowOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X P : Subgroup G}
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p) (hP : IsSylowOf p P X) :
    ∀ x ∈ P, x ^ p = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxX : x ∈ X := hP.le hx
  set y : X := ⟨x, hxX⟩ with hy
  have h1 : ((y : X ⧸ CFSG.pCore 2 X)) ^ p = 1 := by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one _
  have h2 : y ^ p ∈ CFSG.pCore 2 X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h1
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup) (⟨y ^ p, h2⟩ : CFSG.pCore 2 X)
  have hxp : x ^ p ∈ P := pow_mem hx p
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) (⟨x ^ p, hxp⟩ : P)
  rw [Subgroup.orderOf_mk] at ha
  rw [Subgroup.orderOf_mk] at hb
  have h3 : orderOf (y ^ p) = orderOf (x ^ p) := by
    rw [← Subgroup.orderOf_coe, SubgroupClass.coe_pow]
  rw [h3, hb] at ha
  have hb0 : b = 0 := by
    by_contra hb0
    have h4 : p ∣ 2 ^ a := by
      rw [← ha]
      exact dvd_pow_self p hb0
    have h5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4)
    exact hp2 h5
  rw [hb0, pow_zero, orderOf_eq_one_iff] at hb
  exact hb

theorem oblRigidCPUSymplecticFourDeleted_of_center
    (hcen : FactCenterOddPart) : OblRigidCPUSymplecticFourDeleted := by
  intro G _ _ T L M p X v K hcfg Ω _ _ hΩ β θ hθ hv hw f hf _ hS
  classical
  obtain ⟨h, -, hp, hp5, hXL, hXc, hXR, -, hXN, -, hexp, -, hW, hLW, -, hvU, hv1, -, -, hQH,
    -, hKn, hX'K, -, -, hKq⟩ := hcfg
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hS
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : p ≠ 2 := by omega
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent hexp
  have hLN : L ≤ normalizer (X : Set G) :=
    le_normalizer.trans (NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc)
  have hXH : X ≤ centralizer ({v} : Set G) := le_centralizer_of_le_radical h β θ hθ hXL hXR hv
  have hθi : Function.Injective fun x : qtnqU L M => (θ (Additive.ofMul x) : Ω → ZMod 2) :=
    fun x y hxy => Additive.ofMul.injective (θ.injective (Subtype.ext hxy))
  have hstab := NQSetup.card_altStab_weight_two hΩ _ hw
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card (NQSetup.altStab ((θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2))) by
      rw [hstab]; norm_num)
  have hmap := NQSetup.map_centralizer_eq_comap_altStab h β _ hθi hθ hv
  have hσmem : β.symm (σ : alternatingGroup Ω) ∈ ((centralizer ({v} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical L)) := by
    rw [hmap, mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact σ.2
  obtain ⟨l, hlC, hlσ⟩ := hσmem
  have hlv : (l : G) ∈ centralizer ({v} : Set G) := mem_subgroupOf.mp hlC
  have hβl : β (l : L ⧸ CFSG.solvableRadical L) = σ := by
    rw [← QuotientGroup.mk'_apply, hlσ, MulEquiv.apply_symm_apply]
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hlX : (l : G) ∈ normalizer (X : Set G) := hLN l.2
  have hP' : IsSylowOf p (P.map (MulAut.conj (l : G)).toMonoidHom) X := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hlX y).mp (hP.le hy)
    · rw [card_map_of_injective (f := (MulAut.conj (l : G)).toMonoidHom)
        (MulAut.conj (l : G)).injective]
      exact hP.card_eq
  obtain ⟨x₀, hx₀X, hx₀⟩ := hP.exists_mem_conj hP'
  have hn₀P : x₀⁻¹ * (l : G) ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have e1 : x₀⁻¹ * (l : G) * y * (x₀⁻¹ * (l : G))⁻¹ =
        x₀⁻¹ * ((l : G) * y * (l : G)⁻¹) * x₀ := by group
    rw [e1]
    constructor
    · intro hy
      exact (hx₀ _).mp ⟨y, hy, rfl⟩
    · intro hy
      obtain ⟨y', hy', hy'e⟩ := (hx₀ _).mpr hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy'e
      have : y' = y := by
        have h1 := hy'e
        rw [mul_left_inj, mul_right_inj] at h1
        exact h1
      rw [← this]
      exact hy'
  have hx₀L : x₀ ∈ L := hXL hx₀X
  have hn₀L : x₀⁻¹ * (l : G) ∈ L := L.mul_mem (L.inv_mem hx₀L) l.2
  have hn₀v : x₀⁻¹ * (l : G) ∈ centralizer ({v} : Set G) :=
    (centralizer _).mul_mem ((centralizer _).inv_mem (hXH hx₀X)) hlv
  have hx₀R : (⟨x₀, hx₀L⟩ : L) ∈ CFSG.solvableRadical L := by
    obtain ⟨y, hy, hyx⟩ := hXR hx₀X
    have : y = ⟨x₀, hx₀L⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hβn₀ : β ((⟨x₀⁻¹ * (l : G), hn₀L⟩ : L) : L ⧸ CFSG.solvableRadical L) = σ := by
    have e1 : (⟨x₀⁻¹ * (l : G), hn₀L⟩ : L) = (⟨x₀, hx₀L⟩ : L)⁻¹ * l := Subtype.ext rfl
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff _).mpr hx₀R, inv_one, one_mul, hβl]
  obtain ⟨s, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x₀⁻¹ * (l : G))).ne'
  set n' : G := (x₀⁻¹ * (l : G)) ^ (2 ^ s) with hn'
  have hn'r : n' ^ r = 1 := by rw [hn', ← pow_mul, ← hor, pow_orderOf_eq_one]
  have hn'L : n' ∈ L := pow_mem hn₀L _
  have hn'v : n' ∈ centralizer ({v} : Set G) := pow_mem hn₀v _
  have hn'P : n' ∈ normalizer (P : Set G) := pow_mem hn₀P _
  have hβn' : β ((⟨n', hn'L⟩ : L) : L ⧸ CFSG.solvableRadical L) ≠ 1 := by
    have e1 : (⟨n', hn'L⟩ : L) = (⟨x₀⁻¹ * (l : G), hn₀L⟩ : L) ^ (2 ^ s) :=
      Subtype.ext (by rw [SubgroupClass.coe_pow])
    rw [e1, QuotientGroup.mk_pow, map_pow, hβn₀]
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hσ] at h2
    have h3 := Nat.prime_three.dvd_of_dvd_pow h2
    omega
  have hne := normalizerFrattiniConj_ne_one_of_not_mem_radical h hp hp5 hXL hXc hXA hW hLW hn'L
    (fun hR => hβn' (by rw [(QuotientGroup.eq_one_iff _).mpr hR, map_one])) (hLN hn'L)
  have hX'A : IsPGroup p (X.subgroupOf (centralizer ({v} : Set G)) ⧸
      CFSG.pCore 2 (X.subgroupOf (centralizer ({v} : Set G)))) :=
    isPGroup_coreQuot_subgroupOf hXH hXA
  have hMX : M ≤ normalizer (X : Set G) := hXN.ge
  have hX'D : X.subgroupOf (centralizer ({v} : Set G)) ≤
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) :=
    fun x hx => mem_subgroupOf.mpr ⟨(hXL.trans h.l_le) (mem_subgroupOf.mp hx), x.2⟩
  have hDN : (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) ≤
      normalizer ((X.subgroupOf (centralizer ({v} : Set G)) :
        Subgroup (centralizer ({v} : Set G))) : Set (centralizer ({v} : Set G))) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hMX (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'n : ((X.subgroupOf (centralizer ({v} : Set G))).subgroupOf
      ((M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hX'D).mpr hDN
  obtain ⟨Q', hQ'⟩ := hQH.exists_sylow_eq_subgroupOf
  have hQ'D : (Q' : Subgroup (centralizer ({v} : Set G))) ≤
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) := by
    rw [hQ']
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact ⟨h.t_le hx.1, hx.2⟩
  have hHSQ := isSQTKCat_centralizer h hvU hv1
  have hKSQ := isSQTKCat_subgroup_quotient_pCore hHSQ K
  have hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := hcen _ hKq hKSQ p hp hp5
  have hPHle : P ≤ centralizer ({v} : Set G) := hP.le.trans hXH
  have hPH : IsSylowOf p (P.subgroupOf (centralizer ({v} : Set G)))
      (X.subgroupOf (centralizer ({v} : Set G))) := (isSylowOf_subgroupOf_iff hPHle hXH).mpr hP
  have hPexpG := pow_eq_one_of_isSylowOf hp hp2 hexp hP
  have hPexp : ∀ x ∈ P.subgroupOf (centralizer ({v} : Set G)), x ^ p = 1 := fun x hx =>
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hPexpG _ (mem_subgroupOf.mp hx))
  have hW' : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 := hW
  have hPnc : ¬ IsCyclic (P.subgroupOf (centralizer ({v} : Set G))) := by
    intro hc
    apply NQCat.not_isCyclic_of_isSylowOf_of_card_eq_sq hXA hW' hP
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hPHle).toMonoidHom
      (subgroupOfEquivOfLe hPHle).surjective
  have hn'HP : (⟨n', hn'v⟩ : centralizer ({v} : Set G)) ∈
      normalizer ((P.subgroupOf (centralizer ({v} : Set G)) :
        Subgroup (centralizer ({v} : Set G))) : Set (centralizer ({v} : Set G))) :=
    mem_normalizer_subgroupOf_of hn'v hn'P
  have hn'Hr : (⟨n', hn'v⟩ : centralizer ({v} : Set G)) ^ r = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hn'r)
  obtain ⟨m, hm⟩ := sylow_action_pow_of_oddOrder hp hp5 Q' hQ'D hKn hX'D hX'n hX'K hX'A hZ hf hk
    e hPH hPexp hPnc hn'HP hr hn'Hr
  have hpowH := normalizerFrattiniConj_eq_pow hX'A hPH
    ⟨⟨n', hn'v⟩, mem_normalizer_subgroupOf_of hn'v (hLN hn'L)⟩ m hm
  have hcong := congr_normalizerFrattiniConj hXH hn'v (hLN hn'L)
  have hpow : ∀ w, normalizerFrattiniConj X ⟨n', hLN hn'L⟩ w = w ^ m := by
    intro w
    rw [← hcong]
    change frattiniEquivSubgroupOf hXH (normalizerFrattiniConj _ _
      ((frattiniEquivSubgroupOf hXH).symm w)) = w ^ m
    rw [hpowH, map_pow, MulEquiv.apply_symm_apply]
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXA⟩
  have : CFSG.IsElementaryAbelian p ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have hLperf : Group.IsPerfect L := ⟨by
    rw [_root_.commutator_def]
    exact (NQSetup.isCComponent_top_of_qtnq h).2.1⟩
  have hdet := det_normalizerFrattiniConj_eq_one (p := p) hLN hLperf n' hn'L
  have hsq := sq_eq_one_of_pow_of_det_eq_one hW _ m hpow hdet
  apply hne
  have hγr : normalizerFrattiniConj X ⟨n', hLN hn'L⟩ ^ r = 1 := by
    have e1 : (⟨n', hLN hn'L⟩ : normalizer (X : Set G)) ^ r = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hn'r)
    rw [← map_pow, e1, map_one]
  obtain ⟨t, rfl⟩ := hr
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at hγr
  exact hγr

end CFSG.Quasithin.H13.NQRigid
