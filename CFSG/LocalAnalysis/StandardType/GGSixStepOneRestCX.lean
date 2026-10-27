module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

theorem ggMulAut_eq_one_of_fix {p : ℕ} [Fact p.Prime] {S : Type*} [Group S] [Finite S]
    [IsCyclic S] (hS : IsPGroup p S) (σ : MulAut S) (hσ : ¬ p ∣ orderOf σ) {x : S}
    (hx : orderOf x = p) (hfix : σ x = x) : σ = 1 := by
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  set ϕ := MulDistribMulAction.toMonoidHomZModOfIsCyclic S (MulAut S) rfl with hϕ
  have hcop : (orderOf (ϕ σ)).Coprime (Nat.card S) := by
    have h : (orderOf (ϕ σ)).Coprime (p ^ a) := by
      refine Nat.Coprime.pow_right _ ?_
      refine Nat.Coprime.coprime_dvd_left (orderOf_map_dvd ϕ σ) ?_
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hσ)
    rw [← ha] at h
    exact h
  rcases ZMod.eq_one_or_isUnit_sub_one ha (ϕ σ) hcop with h1 | hu
  · ext g
    have := MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply rfl σ g 1
      (by rw [← hϕ, h1, Int.cast_one])
    simpa using this
  · exfalso
    have hN0 : NeZero (Nat.card S) := ⟨Nat.card_pos.ne'⟩
    set k : ℤ := ((ϕ σ).val : ℤ) with hk
    have hkc : ((k : ℤ) : ZMod (Nat.card S)) = ϕ σ := by
      rw [hk, Int.cast_natCast, ZMod.natCast_zmod_val]
    have h1 := MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply rfl σ x k hkc.symm
    have h1' : x = x ^ k := by
      rw [← h1]
      exact hfix.symm
    have h2 : x ^ (k - 1) = 1 := by
      rw [zpow_sub_one, ← h1', mul_inv_cancel]
    have hdvd : (p : ℤ) ∣ k - 1 := by
      rw [← hx]
      exact orderOf_dvd_iff_zpow_eq_one.mpr h2
    have hpS : p ∣ Nat.card S := hx ▸ orderOf_dvd_natCard x
    have hu' : IsUnit (((k - 1 : ℤ)) : ZMod (Nat.card S)) := by
      rw [Int.cast_sub, hkc, Int.cast_one]
      exact hu
    have hu'' := hu'.map (ZMod.castHom hpS (ZMod p))
    rw [map_intCast, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd] at hu''
    exact not_isUnit_zero hu''

theorem ggFalse_of_perfect_of_center {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hperf : commutator H = ⊤) {x : H} (hx : orderOf x = p) (hxc : x ∈ Subgroup.center H)
    (hcyc : ∀ P : Sylow p H, IsCyclic (P : Subgroup H)) : False := by
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  have hxP : x ∈ (P : Subgroup H) := hP (Subgroup.mem_zpowers x)
  have hPc : IsCyclic (P : Subgroup H) := hcyc P
  have hPp : IsPGroup p (P : Subgroup H) := P.isPGroup'
  set N := Subgroup.normalizer ((P : Subgroup H) : Set H) with hN
  set r := (P : Subgroup H).relIndex N with hr
  have hrp : ¬ p ∣ r := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le P.le_normalizer))
  have hnr : ∀ n : N, (n : H) ^ r ∈ (P : Subgroup H) := by
    intro n
    have hnorm : ((P : Subgroup H).subgroupOf N).Normal :=
      Subgroup.normal_subgroupOf_iff_le_normalizer P.le_normalizer |>.mpr le_rfl
    have hcard : Nat.card (N ⧸ (P : Subgroup H).subgroupOf N) = r := by
      rw [← Subgroup.index_eq_card]
      rfl
    have h1 : ((n : N ⧸ (P : Subgroup H).subgroupOf N)) ^ r = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hNC : N ≤ Subgroup.centralizer ((P : Subgroup H) : Set H) := by
    intro n hn
    set n' : N := ⟨n, hn⟩
    have hσ1 : (P : Subgroup H).normalizerMonoidHom n' = 1 := by
      refine ggMulAut_eq_one_of_fix hPp _ ?_ (x := ⟨x, hxP⟩) ?_ ?_
      · intro hpd
        apply hrp
        refine hpd.trans (orderOf_dvd_of_pow_eq_one ?_)
        rw [← map_pow]
        ext g
        show ((n' ^ r : N) : H) * g * ((n' ^ r : N) : H)⁻¹ = g
        have hc : ((⟨(n : H) ^ r, hnr n'⟩ : (P : Subgroup H)) * g : (P : Subgroup H)) =
            g * ⟨(n : H) ^ r, hnr n'⟩ :=
          (IsCyclic.isMulCommutative (α := (P : Subgroup H))).is_comm.comm _ _
        have hc' := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at hc'
        rw [show ((n' ^ r : N) : H) = (n : H) ^ r from rfl, hc']
        group
      · rw [Subgroup.orderOf_mk]
        exact hx
      · ext
        show (n : H) * x * (n : H)⁻¹ = x
        rw [Subgroup.mem_center_iff.mp hxc n]
        group
    have hker : n' ∈ (P : Subgroup H).normalizerMonoidHom.ker := hσ1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hker : (MonoidHom.transferSylow P hNC).ker = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Abelianization.commutator_subset_ker _
  rw [hker] at hcomp
  have hbot : (P : Subgroup H) = ⊥ := top_disjoint.mp hcomp.disjoint
  rw [hbot, Subgroup.mem_bot] at hxP
  rw [hxP, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.orderOf_x (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : orderOf x = p :=
  have : Fact p.Prime := ⟨h.prime⟩
  orderOf_eq_prime (h.d_elem.2 x h.x_mem_d) h.sstar.2.2.1

theorem GGSixCtxV2.l_isComponentOf_inf (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
  CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le h.sstar.2.2.2.1
    (le_inf (le_sup_left : L ≤ ggG0 p B x L D J) h.sstar.2.2.2.1.1) inf_le_right

theorem GGSixCtxV2.le_centralizer_of_isComponentOf_ne (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}))
    (hKL : K ≠ L) : K ≤ Subgroup.centralizer (L : Set G) := by
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK
    h.l_isComponentOf_inf with h' | h'
  · exact absurd h' hKL
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'

omit [Finite G] in
theorem ggPow_eq_one_of_mem_sup_zpowers {p : ℕ} {a b : G} (hab : a * b = b * a) (ha : a ^ p = 1)
    (hb : b ^ p = 1) {g : G} (hg : g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : g ^ p = 1 := by
  have hc : Commute a b := hab
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [ggCentralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
    exact hab
  have hg' : g ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hg'
  obtain ⟨u, hu, v, hv, rfl⟩ := hg'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hij : Commute (a ^ i) (b ^ j) := hc.zpow_zpow i j
  rw [hij.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm,
    zpow_mul, mul_comm (j : ℤ), zpow_mul, zpow_natCast, zpow_natCast, ha, hb, one_zpow, one_zpow,
    mul_one]

theorem GGSixCtxV2.not_dvd_card_of_isComponentOf_le (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}))
    (hKL : K ≤ Subgroup.centralizer (L : Set G)) : ¬ p ∣ Nat.card K := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hcyc := h.sstar.2.2.2.2
  have hKx : K ≤ Subgroup.centralizer ({x} : Set G) := hK.1.trans inf_le_right
  have hxp : x ^ p = 1 := h.d_elem.2 x h.x_mem_d
  have hox : orderOf x = p := h.orderOf_x
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.sstar.2.2.2.1.1 hl)
  intro hpK
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  have hok : orderOf (k : G) = p := by rw [Subgroup.orderOf_coe, hk]
  have hkp : (k : G) ^ p = 1 := hok ▸ pow_orderOf_eq_one _
  have hxk : x * (k : G) = (k : G) * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hKx k.2)).symm
  set T : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers (k : G) with hT
  have hTexp : ∀ g ∈ T, g ^ p = 1 := fun g hg =>
    ggPow_eq_one_of_mem_sup_zpowers hxk hxp hkp hg
  have hTL : T ≤ Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxL) (Subgroup.zpowers_le.mpr (hKL k.2))
  have hTp : IsPGroup p T := fun g => ⟨1, Subtype.ext (by simpa using hTexp g g.2)⟩
  have hTc : IsCyclic T := hcyc T hTL hTp
  have hTdvd : Nat.card T ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext ?_
    simpa using hTexp g g.2
  have hxT : Subgroup.zpowers x ≤ T := le_sup_left
  have hcx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hox]
  have hTeq : Subgroup.zpowers x = T := by
    refine Subgroup.eq_of_le_of_card_ge hxT ?_
    rw [hcx]
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos hTdvd
  have hkx : (k : G) ∈ Subgroup.zpowers x := hTeq ▸ (le_sup_right : _ ≤ T) (Subgroup.mem_zpowers _)
  have hkz : Subgroup.zpowers (k : G) = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkx) ?_
    rw [hcx, Nat.card_zpowers, hok]
  have hxK : x ∈ K := by
    have : x ∈ Subgroup.zpowers (k : G) := hkz ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr k.2) this
  refine ggFalse_of_perfect_of_center (H := ↥K) (p := p) hK.2.2.1 (x := ⟨x, hxK⟩)
    (by rw [Subgroup.orderOf_mk, hox]) ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro k'
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKx k'.2))
  · intro P
    have hPm : IsCyclic ((P : Subgroup ↥K).map K.subtype) :=
      hcyc _ ((Subgroup.map_subtype_le _).trans hKL) (P.isPGroup'.map K.subtype)
    let e := Subgroup.equivMapOfInjective (P : Subgroup ↥K) K.subtype K.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Ctx

section Inputs

@[expose] def GGSixLayerCXPPrimeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
      ∀ K : Subgroup G, IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) →
        K ≤ Subgroup.centralizer (L : Set G) → p ∣ Nat.card K

@[expose] def GGLayerPDivInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ y : G, y ^ p = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {y}) → p ∣ Nat.card K

@[expose] def GGSixLayerCXNonsplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
      ∀ K : Subgroup G, IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) →
        K ≤ Subgroup.centralizer (L : Set G) → p ∣ Nat.card K

theorem ggSixLayerCXInput_of_pPrime (hP : GGSixLayerCXPPrimeInput) : GGSixLayerCXInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx K hK
  by_contra hKL
  have hKc := hctx.le_centralizer_of_isComponentOf_ne hK hKL
  exact hctx.not_dvd_card_of_isComponentOf_le hK hKc (hP G p B Bs x L D J t n f ψ hctx K hK hKc)

theorem ggSixLayerCXPPrimeInput_of_layerCX (hCX : GGSixLayerCXInput) : GGSixLayerCXPPrimeInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx K hK hKc
  have hKL := hCX G p B Bs x L D J t n f ψ hctx K hK
  subst hKL
  exact absurd hKc (CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
    hK.2.2)

theorem ggSixLayerCXPPrimeInput_of_split (hKG : GGLayerPDivInput)
    (hNS : GGSixLayerCXNonsplitInput) : GGSixLayerCXPPrimeInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx K hK hKc
  by_cases hs : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1
  · exact hKG G t n f ψ _ hctx.presents p hctx.prime hctx.ne_two hs x
      (hctx.d_elem.2 x hctx.x_mem_d) (hctx.d_le_ggM hctx.x_mem_d)
      (hctx.d_innerDiag x hctx.x_mem_d) K hK
  · exact hNS G p B Bs x L D J t n f ψ hctx (fun h1 => hs (Or.inl h1)) (fun h2 => hs (Or.inr h2))
      K hK hKc

theorem ggSixLayerCXInput_of_split (hKG : GGLayerPDivInput) (hNS : GGSixLayerCXNonsplitInput) :
    GGSixLayerCXInput :=
  ggSixLayerCXInput_of_pPrime (ggSixLayerCXPPrimeInput_of_split hKG hNS)

end Inputs

end CFSG.StandardType
