module

public import CFSG.Quasithin.H13.NQBlockWitnessSingleton
public import CFSG.Quasithin.SteinbergBQReducibleTwoNormalizers
public import CFSG.Quasithin.H13.NQTermPerfectSmallFamily

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sylow_normalizer_irreducible
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {P : Subgroup G} (hP : IsSylowOf p P X)
    (W₁ : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)))
    (hW₁ : ∀ n : normalizer (X : Set G), (n : G) ∈ T → (n : G) ∈ normalizer (P : Set G) →
      ∀ w ∈ W₁, normalizerFrattiniConj X n w ∈ W₁) :
    W₁ = ⊥ ∨ W₁ = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPX, -, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hLN : normalizer (L : Set G) ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have hTN : T ≤ normalizer (X : Set G) := (h.t_le.trans h.eq_normalizer.le).trans hLN
  have hLX : L ≤ normalizer (X : Set G) := le_normalizer.trans hLN
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, h.sylow.1, h.sylow.2⟩
  set AX := (CFSG.pCore 2 X).map X.subtype with hAXdef
  have hAX2 : IsPGroup 2 AX := CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : G) ∈ AX ↔ x ∈ CFSG.pCore 2 X := fun x =>
    mem_map_iff_mem (subtype_injective X)
  have hNAX : normalizer (X : Set G) ≤ normalizer (AX : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set G), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hAXT : AX ≤ T := by
    have h1 := hTtop.eq_of_le le_sup_left le_top
      (h.sylow.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hπP : (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
    obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
    have h1 := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (hXA.to_subgroup ⊤) le_top
    rw [h1, Sylow.coe_mapSurjective, hS₁]
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := hπP ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  have hQdec : ∀ q ∈ T, ∃ a ∈ AX, a⁻¹ * q ∈ T ⊓ normalizer (P : Set G) := by
    intro q hq
    have hqP : IsSylowOf p (P.map (MulAut.conj q).toMonoidHom) X := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy)
      · rw [card_map_of_injective (MulAut.conj q).injective, hP.card_eq]
    obtain ⟨x, hx, hxP⟩ := SteinbergCC.exists_conj_eq_of_isSylowOf hP hqP
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have haA : x * y⁻¹ ∈ AX := by
      have h1 := hNA y (le_normalizer (hPX hy)) _ hya
      rwa [show y * (y⁻¹ * x) * y⁻¹ = x * y⁻¹ by group] at h1
    refine ⟨x * y⁻¹, haA, mem_inf.mpr ⟨mul_mem (inv_mem (hAXT haA)) hq,
      mem_normalizer_iff.mpr fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩⟩
    · have h1 : q * z * q⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom := by
        rw [hxP]
        exact ⟨z, hz, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : x * z' * x⁻¹ = q * z * q⁻¹ := hzz'
      have e : (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ = y * z' * y⁻¹ := by
        rw [show (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ =
          y * x⁻¹ * (q * z * q⁻¹) * x * y⁻¹ by group, ← hzz']
        group
      rw [e]
      exact mul_mem (mul_mem hy hz') (inv_mem hy)
    · have hu : y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y ∈ P :=
        mul_mem (mul_mem (inv_mem hy) hz) hy
      have h1 : x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ ∈
          P.map (MulAut.conj q).toMonoidHom := by
        rw [← hxP]
        exact ⟨_, hu, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : q * z' * q⁻¹ =
          x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ := hzz'
      have e : z = z' := by
        have h2 : q * z' * q⁻¹ = q * z * q⁻¹ := by rw [hzz']; group
        exact (mul_left_cancel (mul_right_cancel h2)).symm
      rw [e]
      exact hz'
  have hconjmk : ∀ (g : G) (hg : g ∈ normalizer (X : Set G)) (x : X),
      normalizerFrattiniConj X ⟨g, hg⟩
        (QuotientGroup.mk' _ (QuotientGroup.mk' (CFSG.pCore 2 X) x)) =
      QuotientGroup.mk' _ (QuotientGroup.mk' (CFSG.pCore 2 X) (X.normalizerMonoidHom ⟨g, hg⟩ x)) :=
    fun _ _ _ => rfl
  have hAtriv : ∀ (a : G) (ha : a ∈ AX) (haN : a ∈ normalizer (X : Set G)),
      normalizerFrattiniConj X ⟨a, haN⟩ = 1 := by
    intro a ha haN
    ext w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    rw [hconjmk, MulAut.one_apply]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply (hmemA _).mp
    change (a * x * a⁻¹)⁻¹ * x ∈ AX
    have h1 := hNA (x : G)⁻¹ (le_normalizer (inv_mem x.2)) a⁻¹ (inv_mem ha)
    rw [inv_inv] at h1
    rw [show (a * (x : G) * a⁻¹)⁻¹ * x = a * ((x : G)⁻¹ * a⁻¹ * x) by group]
    exact mul_mem ha h1
  have hTW : ∀ q : normalizer (X : Set G), (q : G) ∈ T →
      ∀ w ∈ W₁, normalizerFrattiniConj X q w ∈ W₁ := by
    intro q hqT w hw
    obtain ⟨a, ha, han⟩ := hQdec q hqT
    have haN : a ∈ normalizer (X : Set G) := hTN (hAXT ha)
    have hn : normalizerFrattiniConj X q = normalizerFrattiniConj X (⟨a, haN⟩⁻¹ * q) := by
      rw [map_mul, map_inv, hAtriv a ha haN, inv_one, one_mul]
    rw [hn]
    exact hW₁ _ (mem_inf.mp han).1 (mem_inf.mp han).2 w hw
  have : Group.IsPerfect L :=
    ⟨by rw [commutator_def]; exact (NQSetup.isCComponent_top_of_qtnq h).2.1⟩
  let ρL : L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hLX)
  have hTL : IsSylowOf 2 (T ⊓ L) L :=
    (hTtop.of_le h.t_le le_top).inf_of_le_normalizer h.l_le h.eq_normalizer.le
  obtain ⟨SL, hSL⟩ := hTL.exists_sylow_eq_subgroupOf
  obtain ⟨-, hWc, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXA
  have : IsMulCommutative ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := hWc
  have hρL : ρL ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 : ρL ⟨l, hlL⟩ = 1 := by rw [h1, MonoidHom.one_apply]
    have h3 : inclusion hLX ⟨(l : G), hlL⟩ = l := Subtype.ext rfl
    change (normalizerFrattiniConj X).comp (inclusion hLX) ⟨l, hlL⟩ = 1 at h2
    rwa [MonoidHom.comp_apply, h3] at h2
  refine SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWpow hW ρL hρL SL W₁
    fun s hs w hw => ?_
  have hs' : s ∈ (T ⊓ L).subgroupOf L := hSL ▸ hs
  exact hTW (inclusion hLX s) (mem_inf.mp (mem_subgroupOf.mp hs')).1 w hw

open SteinbergBQ in
theorem original_characteristic_witness_excludes_normal_cross_characteristic_linear_three_quotient
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (_hJq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    {f : ℕ} (_hf : 1 ≤ f) :
    ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel
      ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 ℓ f := by
  classical
  rintro ⟨-, F, _, _, hFcard, ⟨η₀⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hFp : ringChar F ≠ p := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hr, hrn⟩ := FiniteField.card F (ringChar F)
    rw [← Nat.card_eq_fintype_card, hFcard] at hrn
    have hdvd : ringChar F ∣ ℓ ^ f := by
      rw [hrn]
      exact dvd_pow_self _ n.ne_zero
    have hrℓ := (Nat.prime_dvd_prime_iff_eq hr hℓ).mp (hr.dvd_of_dvd_pow hdvd)
    intro hrp
    exact hℓp (hrℓ.symm.trans hrp)
  let η : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* LinearFlag.projectiveSL 3 F :=
    η₀.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (n := 3) (K := F)).symm))
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  obtain ⟨hPX, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hPK : P ≤ K := hPX.trans hXK
  have hTY : T ≤ Y := le_sup_right.trans hXTY
  have hYK : Y ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKY).mp hKn
  have hTK : T ≤ normalizer (K : Set G) := hTY.trans hYK
  have hLN : normalizer (L : Set G) ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have hTN : T ≤ normalizer (X : Set G) := (h.t_le.trans h.eq_normalizer.le).trans hLN
  set σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    with hσ
  have hσinj : Function.Injective (σ.comp (P.subgroupOf K).subtype) :=
    (NQTerm.original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hZ P hP).1
  set θ : K →* LinearFlag.projectiveSL 3 F := η.toMonoidHom.comp σ with hθ
  have hθinj : Function.Injective (θ.comp (P.subgroupOf K).subtype) :=
    η.injective.comp hσinj
  obtain ⟨Q, hQ⟩ := hP
  have hbij := NQTerm.sylow_bijective_coreQuot hp2 hXA Q
  have hcardP : Nat.card P = Nat.card (X ⧸ CFSG.pCore 2 X) := by
    rw [← hQ, card_map_of_injective X.subtype_injective]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  have hcardW : p ^ 2 ≤ Nat.card (X ⧸ CFSG.pCore 2 X) := by
    rw [← hW]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hPexp : ∀ z ∈ P, z ^ p = 1 := by
    intro z hz
    have hzX : z ∈ X := hPX hz
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) (⟨z, hzX⟩ ^ p) = 1 := by
      rw [map_pow, ← hexp]
      exact Monoid.pow_exponent_eq_one _
    have h2 : (⟨z, hzX⟩ : X) ^ p ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).mp h1
    have h4 : ¬ p ∣ Nat.card (CFSG.pCore 2 X) := by
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)).exists_card_eq
      rw [hm]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨z, hz⟩
    rw [Subgroup.orderOf_mk] at hk
    have h5 : orderOf ((⟨z, hzX⟩ : X) ^ p) ∣ p ^ k := by
      refine (orderOf_pow_dvd p).trans ?_
      rw [Subgroup.orderOf_mk, hk]
    have h6 := NQTerm.eq_one_of_orderOf_dvd_prime_pow hp h4 h2 h5
    simpa using congrArg Subtype.val h6
  set Pst := (P.subgroupOf K).map θ with hPst
  have hPstmap : Pst = (θ.comp (P.subgroupOf K).subtype).range := by
    rw [hPst, MonoidHom.range_comp, range_subtype]
  have hcardPst : Nat.card Pst = Nat.card P := by
    rw [hPstmap, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv
  have hPstexp : ∀ y ∈ Pst, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h1 : x ^ p = 1 := Subtype.ext (by simpa using hPexp _ (mem_subgroupOf.mp hx))
    rw [h1, map_one]
  have hPstc : ¬ IsCyclic Pst := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Pst)
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hPstexp _ g.2)
    have htop : zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
    have h1 : Nat.card Pst ≤ p := by
      have h2 : Nat.card (zpowers g) = orderOf g := Nat.card_zpowers g
      rw [htop, card_top] at h2
      rw [h2]
      exact orderOf_le_of_pow_eq_one hp.pos hgp
    rw [hcardPst, hcardP] at h1
    have h2 := hcardW.trans h1
    nlinarith [hp.two_le]
  let τ : normalizer (K : Set G) →*
      MulAut ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
    (CFSG.SectionRank.Ccomm.autQuotient (center (K ⧸ CFSG.pCore 2 K))).comp
      ((CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 K)).comp K.normalizerMonoidHom)
  let ψ : normalizer (K : Set G) →* MulAut (LinearFlag.projectiveSL 3 F) :=
    (MulAut.congr η).toMonoidHom.comp τ
  have hψ : ∀ (n : normalizer (K : Set G)) (k : K), ψ n (θ k) = θ (K.normalizerMonoidHom n k) := by
    intro n k
    change η (τ n (η.symm (η (σ k)))) = η (σ (K.normalizerMonoidHom n k))
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hNK : T ⊓ normalizer (P : Set G) ≤ normalizer (K : Set G) := inf_le_left.trans hTK
  set B := (ψ.comp (inclusion hNK)).range with hB
  have hB2 : IsPGroup 2 B := by
    rw [hB, MonoidHom.range_eq_map]
    exact (IsPGroup.of_equiv (h.sylow.1.to_le inf_le_left) Subgroup.topEquiv.symm).map _
  have hBP : ∀ b ∈ B, Pst.map (b : MulAut (LinearFlag.projectiveSL 3 F)).toMonoidHom = Pst := by
    rintro _ ⟨n, rfl⟩
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨K.normalizerMonoidHom (inclusion hNK n) x, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        exact (mem_normalizer_iff.mp (mem_inf.mp n.2).2 x).mp (mem_subgroupOf.mp hx)
      · exact (hψ (inclusion hNK n) x).symm
    · exact (card_map_of_injective (f := (ψ.comp (inclusion hNK) n).toMonoidHom)
        (ψ.comp (inclusion hNK) n).injective).symm.le
  obtain ⟨-, -, hcard2, -, -, -, -, -, -, hred⟩ :=
    noncyclic_exponent_prime_projective_linear_three_subgroups_have_reducible_two_normalizers
      hp5 hFp Pst hPstc hPstexp
  obtain ⟨P₁, hP₁lt, hP₁card, hP₁B⟩ := hred B hB2 hBP
  have hcardXW : Nat.card (X ⧸ CFSG.pCore 2 X) =
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
    rw [hW, ← hcardP, ← hcardPst, hcard2]
  have hWinj : Function.Injective
      (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))) :=
    ((Function.Surjective.bijective_of_nat_card_le (QuotientGroup.mk'_surjective _)
      hcardXW.le)).1
  set φ : X →* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 X)) with hφ
  have hφinj : Function.Injective (φ.comp (P.subgroupOf X).subtype) := by
    have hQ' : P.subgroupOf X = (Q : Subgroup X) := by
      rw [← hQ]
      exact comap_map_eq_self_of_injective X.subtype_injective _
    have h1 : Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp
        (P.subgroupOf X).subtype) := by
      intro a b hab
      have ha : (a : X) ∈ (Q : Subgroup X) := by
        rw [← hQ']
        exact a.2
      have hb : (b : X) ∈ (Q : Subgroup X) := by
        rw [← hQ']
        exact b.2
      have h2 := hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
      have h3 : (a : X) = (b : X) := congrArg (fun w : (Q : Subgroup X) => (w : X)) h2
      exact Subtype.ext h3
    exact hWinj.comp h1
  set Q₁ : Subgroup G := ((P.subgroupOf K) ⊓ P₁.comap θ).map K.subtype with hQ₁
  have hQ₁P : Q₁ ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (mem_inf.mp hx).1
  set W₁ := (Q₁.subgroupOf X).map φ with hW₁
  have hQ₁card : Nat.card Q₁ = p := by
    have hmap : ((P.subgroupOf K) ⊓ P₁.comap θ).map θ = P₁ := by
      refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨x, hx, rfl⟩ := hy
        exact (mem_inf.mp hx).2
      · obtain ⟨x, hx, rfl⟩ := hP₁lt.le hy
        exact ⟨x, mem_inf.mpr ⟨hx, hy⟩, rfl⟩
    have hinj : Set.InjOn θ ((P.subgroupOf K) ⊓ P₁.comap θ : Subgroup K) := by
      intro a ha b hb hab
      have h1 := hθinj (a₁ := ⟨a, (mem_inf.mp ha).1⟩) (a₂ := ⟨b, (mem_inf.mp hb).1⟩) hab
      exact congrArg Subtype.val h1
    rw [hQ₁, card_map_of_injective K.subtype_injective, ← hP₁card]
    have h1 : Nat.card ↥(((P.subgroupOf K) ⊓ P₁.comap θ).map θ) =
        Nat.card ↥((P.subgroupOf K) ⊓ P₁.comap θ) := by
      change Nat.card (θ '' (((P.subgroupOf K) ⊓ P₁.comap θ : Subgroup K) : Set K)) = _
      exact Nat.card_image_of_injOn hinj
    rw [← h1, hmap]
  have hW₁inv : ∀ n : normalizer (X : Set G), (n : G) ∈ T → (n : G) ∈ normalizer (P : Set G) →
      ∀ w ∈ W₁, normalizerFrattiniConj X n w ∈ W₁ := by
    intro n hnT hnP w hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨y, hy, hyx⟩ := mem_subgroupOf.mp hx
    have hyP : (y : G) ∈ P := mem_subgroupOf.mp (mem_inf.mp hy).1
    have hyP₁ : θ y ∈ P₁ := (mem_inf.mp hy).2
    have hnK : (n : G) ∈ normalizer (K : Set G) := hTK hnT
    have hnTP : (n : G) ∈ T ⊓ normalizer (P : Set G) := mem_inf.mpr ⟨hnT, hnP⟩
    refine ⟨X.normalizerMonoidHom n x, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    refine ⟨K.normalizerMonoidHom ⟨n, hnK⟩ y, mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [mem_subgroupOf]
      exact (mem_normalizer_iff.mp hnP y).mp hyP
    · have hb : ψ.comp (inclusion hNK) ⟨n, hnTP⟩ ∈ B := ⟨_, rfl⟩
      have h1 := hP₁B _ hb
      change θ (K.normalizerMonoidHom ⟨n, hnK⟩ y) ∈ P₁
      rw [← hψ]
      rw [← h1]
      exact ⟨θ y, hyP₁, rfl⟩
    · change (n : G) * (y : G) * (n : G)⁻¹ = (n : G) * (x : G) * (n : G)⁻¹
      have hyx' : (y : G) = (x : G) := hyx
      rw [hyx']
  have hW₁card : Nat.card W₁ = p := by
    have hQ₁X : Q₁.subgroupOf X ≤ P.subgroupOf X := fun z hz => hQ₁P hz
    have hinj : Set.InjOn φ (Q₁.subgroupOf X : Subgroup X) := by
      intro a ha b hb hab
      have h1 := hφinj (a₁ := ⟨a, hQ₁X ha⟩) (a₂ := ⟨b, hQ₁X hb⟩) hab
      exact congrArg Subtype.val h1
    rw [hW₁, ← hQ₁card]
    have h1 : Nat.card ((Q₁.subgroupOf X).map φ) = Nat.card (Q₁.subgroupOf X) := by
      change Nat.card (φ '' (Q₁.subgroupOf X : Set X)) = _
      exact Nat.card_image_of_injOn hinj
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe (hQ₁P.trans hPX)).toEquiv
  rcases sylow_normalizer_irreducible h hp hp5 hXL hXc hXA hW hLW ⟨Q, hQ⟩ W₁ hW₁inv with
    hbot | htop
  · rw [hbot, card_bot] at hW₁card
    exact hp.one_lt.ne hW₁card
  · rw [htop, card_top, hW] at hW₁card
    have h1 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega

theorem originalWitnessExcludesCrossLinearThree
    : OriginalWitnessExcludesCrossLinearThree :=
  fun _ _ _ _ _ _ h _ hp hp5 _ hXL hXc hXA hexp hW hLW _ _ hXTY hKY hKn hXK hJq hZ _ hℓ hℓp _ hf =>
    original_characteristic_witness_excludes_normal_cross_characteristic_linear_three_quotient h hp
      hp5 hXL hXc hXA hexp hW hLW hXTY hKY hKn hXK hJq hZ hℓ hℓp hf

theorem original_characteristic_witness_singleton_of
    (hProd : OriginalXTNormalComponent)
    (hSp4 : OriginalWitnessExcludesEvenSymplecticFour)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
      V = ⊥ ∨ V = ⊤) :
    quasithinIsMaxTwoLocal M ∧ X ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' → M' = M :=
  original_characteristic_witness_singleton_of_inputs hProd
    originalWitnessExcludesCrossLinearThree hSp4 h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW
    hirr

end CFSG.Quasithin.H13.NQBlock
