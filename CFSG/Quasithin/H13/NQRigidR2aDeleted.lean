module

public import CFSG.Quasithin.H13.PSL3OddPower
public import CFSG.Quasithin.H13.NQRigidR2aLine

public section

open Subgroup Equiv CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)
open scoped Pointwise IsMulCommutative commutatorElement

namespace CFSG.Quasithin.H13.NQRigid

theorem map_subgroupOf_ne_top_of_not_le {H : Type} [Group H] [Finite H] {D : Subgroup H}
    (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} (hKn : K.Normal)
    (hKD : ¬ K ≤ D) (hJ : Group.IsPerfect (K ⧸ CFSG.pCore 2 K)) {N : Subgroup K} [N.Normal]
    (hNZ : ∀ x ∈ N, QuotientGroup.mk' (CFSG.pCore 2 K) x ∈ center (K ⧸ CFSG.pCore 2 K)) :
    (D.subgroupOf K).map (QuotientGroup.mk' N) ≠ ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  intro htop
  apply hKD
  set O := CFSG.pCore 2 K with hO
  set Ā := (D.subgroupOf K).map (QuotientGroup.mk' O) with hĀ
  have hdec : ∀ a : K, ∃ d : K, d ∈ D.subgroupOf K ∧ d⁻¹ * a ∈ N := by
    intro a
    have ha : QuotientGroup.mk' N a ∈ (D.subgroupOf K).map (QuotientGroup.mk' N) :=
      htop ▸ mem_top _
    obtain ⟨d, hd, hda⟩ := ha
    exact ⟨d, hd, QuotientGroup.eq.mp hda⟩
  have hsplit : ∀ a : K, ∃ d : K, d ∈ D.subgroupOf K ∧
      QuotientGroup.mk' O a = QuotientGroup.mk' O d * QuotientGroup.mk' O (d⁻¹ * a) ∧
      QuotientGroup.mk' O (d⁻¹ * a) ∈ center (K ⧸ O) := by
    intro a
    obtain ⟨d, hd, hdn⟩ := hdec a
    exact ⟨d, hd, by rw [← map_mul, mul_inv_cancel_left], hNZ _ hdn⟩
  have hcomm : commutator (K ⧸ O) ≤ Ā := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective O a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective O b
    obtain ⟨d₁, hd₁, e₁, hz₁⟩ := hsplit a'
    obtain ⟨d₂, hd₂, e₂, hz₂⟩ := hsplit b'
    rw [e₁, e₂, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ hz₁ hz₂,
      ← map_commutatorElement]
    refine ⟨⁅d₁, d₂⁆, ?_, rfl⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)
  have hĀtop : Ā = ⊤ := by
    have h1 : commutator (K ⧸ O) = ⊤ := hJ.1
    rw [h1, top_le_iff] at hcomm
    exact hcomm
  have hOQ : O.map K.subtype ≤ (Q : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup.map _) Q
  intro k hk
  have hk' : QuotientGroup.mk' O ⟨k, hk⟩ ∈ Ā := hĀtop ▸ mem_top _
  obtain ⟨d, hd, hdk⟩ := hk'
  have h1 : d⁻¹ * ⟨k, hk⟩ ∈ O := QuotientGroup.eq.mp hdk
  have h2 : (d : H)⁻¹ * k ∈ D := hQD (hOQ ⟨d⁻¹ * ⟨k, hk⟩, h1, rfl⟩)
  have h3 : k = (d : H) * ((d : H)⁻¹ * k) := by group
  rw [h3]
  exact D.mul_mem (mem_subgroupOf.mp hd) h2

theorem sylow_action_pow_of_oddOrder_linearThree {H : Type} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {D : Subgroup H} (Q : Sylow 2 H) (hQD : (Q : Subgroup H) ≤ D)
    {K : Subgroup H} (hKn : K.Normal) (hKD : ¬ K ≤ D) {X : Subgroup H} (hXD : X ≤ D)
    (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hJ : Group.IsPerfect (K ⧸ CFSG.pCore 2 K))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {F : Type} [Field F] [Finite F]
    [CharP F 2]
    (η : (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    {P : Subgroup H} (hP : IsSylowOf p P X) (hPexp : ∀ x ∈ P, x ^ p = 1) (hPnc : ¬ IsCyclic P)
    {n₀ : H} (hnD : n₀ ∈ D) (hnP : n₀ ∈ normalizer (P : Set H)) {r : ℕ} (hr : Odd r)
    (hnr : n₀ ^ r = 1) :
    ∃ m : ℕ, ∀ x ∈ P, n₀ * x * n₀⁻¹ = x ^ m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have := hKn
  obtain ⟨N, hNc, hN, hNZ, ι, -⟩ := exists_centerPreimage_central K hKn hp hp2 hZ
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
  have hUA : ((Q : Subgroup H).subgroupOf K).map (QuotientGroup.mk' N) ≤
      (D.subgroupOf K).map (QuotientGroup.mk' N) :=
    map_mono fun x hx => mem_subgroupOf.mpr (hQD (mem_subgroupOf.mp hx))
  have hA₀ : (D.subgroupOf K).map (QuotientGroup.mk' N) ≠ ⊤ :=
    map_subgroupOf_ne_top_of_not_le Q hQD hKn hKD hJ fun x hx => (hNZ x).mp hx
  have hγA : ∀ y ∈ (D.subgroupOf K).map (QuotientGroup.mk' N),
      γ y ∈ (D.subgroupOf K).map (QuotientGroup.mk' N) := by
    rintro _ ⟨⟨x, hxK⟩, hx, rfl⟩
    rw [hγmk]
    exact ⟨⟨n₀ * x * n₀⁻¹, hKn.conj_mem x hxK n₀⟩,
      mem_subgroupOf.mpr (D.mul_mem (D.mul_mem hnD (mem_subgroupOf.mp hx)) (D.inv_mem hnD)), rfl⟩
  obtain ⟨m, hm⟩ := PSL3.oddOrder_acts_by_pow (ι.symm.trans η) hp5 ⟨U, hU⟩ hP₀exp hP₀nc hPU hUA
    hA₀ hr hγr hγP hγA
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

theorem false_of_linearThree_of_deleted (hcen : FactCenterOddPart)
    {T L M : Subgroup G} {p : ℕ} {X : Subgroup G} {v : G}
    {K : Subgroup (centralizer ({v} : Set G))} (hcfg : RigidSingleCPUConfig T L M p X v K)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (β : (L ⧸ CFSG.solvableRadical L) ≃* alternatingGroup Ω)
    (θ : Additive (qtnqU L M) ≃+ evenWeight Ω)
    (hθ : ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
      (θ (Additive.ofMul y) : Ω → ZMod 2) =
        permAct (β (l : L ⧸ CFSG.solvableRadical L) : Perm Ω) (θ (Additive.ofMul x)))
    (hv : v ∈ qtnqU L M)
    (hw : (Finset.univ.filter fun ω => (θ (Additive.ofMul ⟨v, hv⟩) : Ω → ZMod 2) ω ≠ 0).card = 2)
    {f : ℕ}
    (hS : StatedClassicalModel ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 2 f) :
    False := by
  classical
  obtain ⟨h, -, hp, hp5, hXL, hXc, hXR, -, hXN, -, hexp, -, hW, hLW, -, hvU, hv1, -, -, hQH,
    -, hKn, hX'K, hKD, -, hKq⟩ := hcfg
  obtain ⟨-, F, _, _, hFcard, ⟨η₀⟩⟩ := hS
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : p ≠ 2 := by omega
  have hF2 : ringChar F = 2 := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hr, hrn⟩ := FiniteField.card F (ringChar F)
    rw [← Nat.card_eq_fintype_card, hFcard] at hrn
    have hdvd : ringChar F ∣ 2 ^ f := by
      rw [hrn]
      exact dvd_pow_self _ n.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd)
  have : CharP F 2 := ringChar.eq_iff.mp hF2
  let η : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    η₀.trans (PSL3.statedProjEquivProjectiveSL 3 F)
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
  have hn'HD : (⟨n', hn'v⟩ : centralizer ({v} : Set G)) ∈
      (M ⊓ centralizer ({v} : Set G)).subgroupOf (centralizer ({v} : Set G)) :=
    mem_subgroupOf.mpr ⟨h.l_le hn'L, hn'v⟩
  have hn'HP : (⟨n', hn'v⟩ : centralizer ({v} : Set G)) ∈
      normalizer ((P.subgroupOf (centralizer ({v} : Set G)) :
        Subgroup (centralizer ({v} : Set G))) : Set (centralizer ({v} : Set G))) :=
    mem_normalizer_subgroupOf_of hn'v hn'P
  have hn'Hr : (⟨n', hn'v⟩ : centralizer ({v} : Set G)) ^ r = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hn'r)
  obtain ⟨m, hm⟩ := sylow_action_pow_of_oddOrder_linearThree hp hp5 Q' hQ'D hKn hKD hX'D hX'n
    hX'K hX'A hKq.1 hZ η hPH hPexp hPnc hn'HD hn'HP hr hn'Hr
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

theorem oblRigidCPUEvenLinearThreeParabolic_of_center
    (hcen : FactCenterOddPart) : OblRigidCPUEvenLinearThreeParabolic := by
  intro G _ _ T L M p X v K hcfg f _ hS
  exfalso
  have hcfg₀ := hcfg
  obtain ⟨h, hmod, -, -, -, -, -, -, -, -, -, -, -, -, -, hvU, -⟩ := hcfg
  rcases exists_four_or_deleted_weight_two h hmod hvU with hB | ⟨Ω, _, _, hΩ, β, θ, hθ, hw⟩
  · exact false_of_linearThree_of_four hcen hcfg₀ hB hS
  · exact false_of_linearThree_of_deleted hcen hcfg₀ hΩ β θ hθ hvU hw hS

end CFSG.Quasithin.H13.NQRigid
