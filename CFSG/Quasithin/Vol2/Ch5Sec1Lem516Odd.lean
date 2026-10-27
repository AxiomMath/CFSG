module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Quasithin.Background.InternalSecIrr
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped MatrixGroups

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo in
theorem exists_conj_of_coprime_orderOf_galoisField {n : ℕ} (hn : n ≠ 0)
    (g : MulAut PSL(2, GaloisField 2 n)) (hg : Nat.Coprime n (orderOf g)) :
    ∃ x : PSL(2, GaloisField 2 n), g = MulAut.conj x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 n
  let e := semilinearEquivAut K
  set y := e.symm g
  have hGal : Nat.card (K ≃+* K) = n := natCard_ringEquiv_galoisField 2 hn
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hGal]; exact hn)
  have hπ : (SemidirectProduct.rightHom y : K ≃+* K) = 1 := by
    have hdvd1 : orderOf (SemidirectProduct.rightHom y) ∣ orderOf g := by
      rw [← MulEquiv.orderOf_eq e.symm g]
      exact orderOf_map_dvd _ _
    have hdvd2 : orderOf (SemidirectProduct.rightHom y) ∣ n :=
      (orderOf_dvd_natCard _).trans (dvd_of_eq hGal)
    have h := Nat.dvd_gcd hdvd2 hdvd1
    rw [hg.gcd_eq_one] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  have hy : y = SemidirectProduct.inl y.left := SemidirectProduct.ext rfl (by simpa using hπ)
  obtain ⟨x, hx⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective K y.left
  refine ⟨x, ?_⟩
  calc g = e y := (e.apply_symm_apply g).symm
    _ = e (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x)) := by
        rw [hy, hx]
    _ = MulAut.conj x := by
        change semilinearAction K _ = _
        rw [semilinearAction_inl, pglAction_toPGL]

section Conj

variable {G : Type} [Group G]

theorem map_normalizerMonoidHom_pCore (L : Subgroup G) (g : ↥(Subgroup.normalizer (L : Set G))) :
    (CFSG.pCore 2 ↥L).map (Subgroup.normalizerMonoidHom L g : ↥L →* ↥L) = CFSG.pCore 2 ↥L := by
  rw [← MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance _

@[expose] noncomputable def conjQuotPCore (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L) where
  toFun g := QuotientGroup.congr _ _ (Subgroup.normalizerMonoidHom L g)
    (map_normalizerMonoidHom_pCore L g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [QuotientGroup.congr_mk, map_mul]
    rfl

theorem conjQuotPCore_mk (L : Subgroup G) (g : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    conjQuotPCore L g (QuotientGroup.mk l) =
      QuotientGroup.mk ⟨(g : G) * l * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 l).mp l.2⟩ := by
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L g l

theorem mem_pCore_iff_mem_pCoreOf (L : Subgroup G) (y : ↥L) :
    y ∈ CFSG.pCore 2 ↥L ↔ (y : G) ∈ pCoreOf 2 L := by
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← Subtype.ext hzy]

end Conj

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem pCoreOf_le_T (h : Hyp5_0_1 G T M L n) : pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : IsSubnormal L (L ⊔ T) :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.sup_le_normalizer)
      (IsSubnormal.refl _)
  exact (A4.pCoreOf_le_of_subnormal 2 hsub).trans
    (F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf le_sup_right))

theorem exists_mem_inf_conj_eq (h : Hyp5_0_1 G T M L n) (hodd : ¬ Even n) {t : G}
    (ht : t ∈ T) :
    ∃ s ∈ T ⊓ L, ∀ l ∈ L, (t * l * t⁻¹)⁻¹ * (s * l * s⁻¹) ∈ pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := h.T_le_normalizer
  obtain ⟨eL⟩ := nonempty_equiv_psl_of_lieModel (by have := h.two_le; omega) h.lie
  have := h.isSimple
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases (inferInstance : (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).Normal).eq_bot_or_eq_top
      with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple h.isQuasisimple
      have ha : a ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := h1 ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  set γ := conjQuotPCore L ⟨t, hTN ht⟩ with hγ
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
  have hγk : γ ^ 2 ^ k = 1 := by
    have h1 : (⟨t, hTN ht⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have h2 := congrArg Subtype.val hk
      simpa using h2
    rw [hγ, ← map_pow, h1, map_one]
  have hn0 : n ≠ 0 := by have := h.two_le; omega
  have hcop : Nat.Coprime n (orderOf (MulAut.congr eL γ)) := by
    have hdvd : orderOf (MulAut.congr eL γ) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hγk, map_one])
    have h2 : Nat.Coprime n (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp hodd))
    exact h2.coprime_dvd_right hdvd
  obtain ⟨y, hy⟩ := exists_conj_of_coprime_orderOf_galoisField hn0 _ hcop
  set x := eL.symm y with hx
  have hγx : ∀ q, γ q = x * q * x⁻¹ := by
    intro q
    have h1 := DFunLike.congr_fun hy (eL q)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    apply eL.injective
    rw [h1, map_mul, map_mul, map_inv, hx, MulEquiv.apply_symm_apply]
  have hx2 : x ^ 2 ^ k = 1 := by
    have hc : ∀ q, x ^ 2 ^ k * q * (x ^ 2 ^ k)⁻¹ = q := by
      intro q
      have hγc : γ = MulAut.conj x := by
        ext q'
        rw [hγx, MulAut.conj_apply]
      have h1 := DFunLike.congr_fun hγk q
      rw [hγc, ← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
      exact h1
    have hmem : x ^ 2 ^ k ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h1 := hc q
      calc q * x ^ 2 ^ k = x ^ 2 ^ k * q * (x ^ 2 ^ k)⁻¹ * x ^ 2 ^ k := by rw [h1]
        _ = x ^ 2 ^ k * q := by group
    rw [hZ] at hmem
    exact hmem
  have hxP : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    show (x ^ m) ^ 2 ^ k = 1
    rw [← zpow_natCast (x ^ m), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left h.sup_le_normalizer
  set Sb : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (A4.toSylow hSL).mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
  have hSbeq : (Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) =
      ((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := rfl
  have hγS : ∀ (t' : G) (ht' : t' ∈ T) (q : ↥L ⧸ CFSG.pCore 2 ↥L),
      q ∈ (Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) →
        conjQuotPCore L ⟨t', hTN ht'⟩ q ∈ (Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    intro t' ht' q hq
    rw [hSbeq] at hq ⊢
    obtain ⟨s, hs₀, rfl⟩ := hq
    have hs : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hs₀
    rw [QuotientGroup.mk'_apply, conjQuotPCore_mk]
    refine ⟨_, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem (T.mul_mem ht' hs.1) (T.inv_mem ht'),
      (Subgroup.mem_normalizer_iff.mp (hTN ht') s).mp s.2⟩
  have hxN : x ∈ Subgroup.normalizer ((Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
      Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [← hγx]
      exact hγS t ht q hq
    · intro hq
      have h1 : q = γ⁻¹ (x * q * x⁻¹) := by
        rw [← hγx, MulAut.inv_apply_self]
      have h2 : γ⁻¹ = conjQuotPCore L ⟨t⁻¹, hTN (T.inv_mem ht)⟩ := by
        rw [hγ, ← map_inv]
        rfl
      rw [h1, h2]
      exact hγS t⁻¹ (T.inv_mem ht) _ hq
  have hxS : x ∈ (Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    have hH : IsPGroup 2 ↥((Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ⊔ Subgroup.zpowers x) :=
      IsPGroup.to_sup_of_normal_left' Sb.isPGroup' hxP (Subgroup.zpowers_le.mpr hxN)
    have hmax := Sb.is_maximal' hH le_sup_left
    have h1 : x ∈ (Sb : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [hmax] at h1
    exact h1
  rw [hSbeq] at hxS
  obtain ⟨s₀, hs₀, hs₀x⟩ := hxS
  refine ⟨s₀, Subgroup.mem_subgroupOf.mp hs₀, fun l hl => ?_⟩
  have h1 := hγx (QuotientGroup.mk ⟨l, hl⟩)
  rw [hγ, conjQuotPCore_mk, ← hs₀x, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  exact (mem_pCore_iff_mem_pCoreOf L _).1 h1

end Hyp5_0_1

theorem stmt5_1_6_odd : Stmt5_1_6_odd := by
  intro G _ _ T M L D n h hD hodd
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hD.1.trans inf_le_right
  have hO2T : pCoreOf 2 L ≤ T := h.pCoreOf_le_T
  have key : ∀ d ∈ D, ∀ t ∈ T, d⁻¹ * t * d ∈ T := by
    intro d hd t ht
    obtain ⟨s, hs, hsP⟩ := h.exists_mem_inf_conj_eq hodd ht
    have hz := hsP d (hDL hd)
    have hds : d⁻¹ * s * d ∈ T ⊓ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hDN (D.inv_mem hd)) s).mp hs
      rwa [inv_inv] at h1
    have e : d⁻¹ * t * d =
        (d⁻¹ * s * d) * s⁻¹ * ((t * d * t⁻¹)⁻¹ * (s * d * s⁻¹))⁻¹ * t := by
      group
    rw [e]
    exact T.mul_mem (T.mul_mem (T.mul_mem hds.1 (T.inv_mem hs.1)) (T.inv_mem (hO2T hz))) ht
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h1 := key d⁻¹ (D.inv_mem hd) t ht
    rwa [inv_inv] at h1
  · intro ht
    have h1 := key d hd _ ht
    have e : d⁻¹ * (d * t * d⁻¹) * d = t := by group
    rwa [e] at h1

end CFSG.Quasithin.H13
