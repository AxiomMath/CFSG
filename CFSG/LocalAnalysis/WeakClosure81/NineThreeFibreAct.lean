module

public import CFSG.LocalAnalysis.WeakClosure81.NineStruct
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSetup
public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] def zmodRefl (p : ℕ) (c : ZMod p) : Equiv.Perm (ZMod p) :=
  Equiv.subLeft (2 * c)

private lemma nine3_refl_of_conj (hp : p.Prime) (hp2 : p ≠ 2) {π : Equiv.Perm (ZMod p)}
    {c : ZMod p} (hπ : π * π = 1) (hne : π ≠ 1)
    (hconj : π * Equiv.addRight (1 : ZMod p) * π = Equiv.addRight c) :
    ∃ a : ZMod p, π = zmodRefl p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2'
    · exact hp.ne_one h1
    · exact hp2 h2'
  have hπT : π * Equiv.addRight (1 : ZMod p) = Equiv.addRight c * π := by
    rw [← mul_one (π * Equiv.addRight (1 : ZMod p)), ← hπ, ← mul_assoc, hconj]
  have hrec : ∀ i : ZMod p, π (i + 1) = π i + c := by
    intro i
    have h := congrFun (congrArg DFunLike.coe hπT) i
    simpa [Equiv.Perm.mul_apply, Equiv.coe_addRight] using h
  have haffine : ∀ i : ZMod p, π i = π 0 + i * c := by
    have hnat : ∀ n : ℕ, π (n : ZMod p) = π 0 + (n : ZMod p) * c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Nat.cast_succ, hrec, ih]
          ring
    intro i
    have := hnat i.val
    rwa [ZMod.natCast_zmod_val] at this
  have hfix (i : ZMod p) : π (π i) = i := by
    have h := congrFun (congrArg DFunLike.coe hπ) i
    simpa [Equiv.Perm.mul_apply] using h
  have hA0 : π 0 + π 0 * c = 0 := by
    have h := haffine (π 0)
    rw [hfix] at h
    exact h.symm
  have hA : π 0 * (1 + c) = 0 := by
    rw [mul_add, mul_one, hA0]
  have hc2 : c * c = 1 := by
    have h := haffine (π 1)
    rw [hfix] at h
    have h1 : π 1 = π 0 + c := by simpa using haffine 1
    rw [h1] at h
    have hexp : π 0 + (π 0 + c) * c = c * c := by
      rw [add_mul, ← add_assoc, hA0, zero_add]
    rw [hexp] at h
    exact h.symm
  rcases mul_self_eq_one_iff.mp hc2 with hc1 | hcneg
  · exact absurd (by
      ext i
      rw [haffine i, hc1, mul_one]
      have hthis : π 0 * (1 + 1) = 0 := by simpa [hc1] using hA
      have htwo : (1 + 1 : ZMod p) ≠ 0 := by
        rw [show (1 + 1 : ZMod p) = 2 by ring]
        exact h2
      have hπ0 : π 0 = 0 := (mul_eq_zero.mp hthis).resolve_right htwo
      rw [hπ0]
      simp) hne
  · refine ⟨π 0 * (2 : ZMod p)⁻¹, ?_⟩
    have h2c : (2 : ZMod p) * (π 0 * (2 : ZMod p)⁻¹) = π 0 := by
      rw [← mul_assoc, mul_comm (2 : ZMod p) (π 0), mul_assoc, mul_inv_cancel₀ h2, mul_one]
    rw [zmodRefl, h2c]
    ext i
    rw [Equiv.subLeft_apply, haffine, hcneg]
    ring

structure Nine3FibreAct (K S : Subgroup G) (p : ℕ) (x : G)
    (ρ : ↥K →* Equiv.Perm (ZMod p)) : Prop where
  ker_le : ∀ k : ↥K, ρ k = 1 → (k : G) ∈ pCoreOf 2 K
  le_ker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρ k = 1
  stab : ∀ k : ↥K, ρ k 0 = 0 ↔ (k : G) ∈ S
  shift : ∀ k : ↥K, (k : G) = x → ∀ i : ZMod p, ρ k i = i + 1
  refl : ∀ k : ↥K, (k : G) ∉ pCoreOf 2 K → k * k = 1 → ∃ c : ZMod p, ρ k = zmodRefl p c

theorem nine3_exists_fibreAct (hc : Nine3Choice V T A K S X p g x) :
    ∃ ρ : ↥K →* Equiv.Perm (ZMod p), Nine3FibreAct K S p x ρ := by
  haveI : Fact p.Prime := ⟨hc.core.hyp.base.prime⟩
  have h : TwoPTwo K S X p := hc.core.hyp.base.toTwoPTwo
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := h.odd
  have hxK : x ∈ K := h.sylowP.le hc.x_mem
  let x₀ : ↥K := ⟨x, hxK⟩
  let Xsub : Subgroup ↥K := X.subgroupOf K
  have hx₀X : x₀ ∈ Xsub := hc.x_mem
  let g₀ : Xsub := ⟨x₀, hx₀X⟩
  have hg₀ : ∀ u : Xsub, u ∈ Subgroup.zpowers g₀ := by
    intro u
    rw [Subgroup.mem_zpowers_iff]
    have huX : (u : ↥K).val ∈ X := Subgroup.mem_subgroupOf.mp u.2
    rw [hc.x_gen] at huX
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp huX
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_zpow, Subgroup.coe_subtype]
    exact hn
  have hXsubcard : Nat.card Xsub = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sylowP.le).toEquiv, hc.core.card]
  let φ : Multiplicative (ZMod p) ≃* Xsub := zmodMulEquivOfGenerator hg₀ hXsubcard
  let Q := ↥K ⧸ (S.subgroupOf K)
  let ψfun : Xsub → Q := fun u => QuotientGroup.mk (u : ↥K)
  have hXinfS : X ⊓ S = ⊥ :=
    (IsPGroup.disjoint_of_ne p 2 h.odd X S h.sylowP.isPGroup h.sylowTwo.isPGroup).eq_bot
  have hψinj : Function.Injective ψfun := by
    intro u v huv
    have hmem : ((u : ↥K))⁻¹ * (v : ↥K) ∈ S.subgroupOf K := QuotientGroup.eq.mp huv
    have hmem2 : ((u : ↥K))⁻¹ * (v : ↥K) ∈ Xsub :=
      Xsub.mul_mem (Xsub.inv_mem u.2) v.2
    have hbot : Xsub ⊓ S.subgroupOf K = ⊥ := by
      have hXsub_eq : Xsub = X.subgroupOf K := rfl
      have : Xsub ⊓ S.subgroupOf K = (X ⊓ S).subgroupOf K := by
        rw [hXsub_eq]
        ext w
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      rw [this, hXinfS, Subgroup.bot_subgroupOf]
    have h1 : ((u : ↥K))⁻¹ * (v : ↥K) = 1 := by
      have hmem' : ((u : ↥K))⁻¹ * (v : ↥K) ∈ (⊥ : Subgroup ↥K) := by
        rw [← hbot]; exact ⟨hmem2, hmem⟩
      simpa using hmem'
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hψsurj : Function.Surjective ψfun := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have hainv : (a : G)⁻¹ ∈ (S : Set G) * (X : Set G) := by
      rw [← h.mul_eq]
      exact K.inv_mem a.2
    obtain ⟨s, hs, y, hy, hsy⟩ := Set.mem_mul.mp hainv
    have hy'X : y⁻¹ ∈ X := X.inv_mem hy
    have hs'S : s⁻¹ ∈ S := S.inv_mem hs
    have hy'K : y⁻¹ ∈ K := h.sylowP.le hy'X
    have hs'K : s⁻¹ ∈ K := h.sylowTwo.le hs'S
    refine ⟨⟨⟨y⁻¹, hy'K⟩, hy'X⟩, ?_⟩
    have hdecomp : a = (⟨y⁻¹, hy'K⟩ : ↥K) * ⟨s⁻¹, hs'K⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype]
      rw [show y⁻¹ * s⁻¹ = (s * y)⁻¹ by group, hsy, inv_inv]
    change QuotientGroup.mk ((⟨⟨y⁻¹, hy'K⟩, hy'X⟩ : Xsub) : ↥K) = QuotientGroup.mk a
    rw [hdecomp]
    rw [QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have hker : ((⟨y⁻¹, hy'K⟩ : ↥K))⁻¹ * ((⟨y⁻¹, hy'K⟩ : ↥K) * ⟨s⁻¹, hs'K⟩)
        = (⟨s⁻¹, hs'K⟩ : ↥K) := by group
    rw [hker]
    exact hs'S
  let ψ : Xsub ≃ Q := Equiv.ofBijective ψfun ⟨hψinj, hψsurj⟩
  let e : ZMod p ≃ Q := (Multiplicative.ofAdd.trans φ.toEquiv).trans ψ
  let ρ : ↥K →* Equiv.Perm (ZMod p) :=
    (e.symm.permCongrHom).toMonoidHom.comp (MulAction.toPermHom (↥K) Q)
  have hρ_apply : ∀ (k : ↥K) (i : ZMod p), ρ k i = e.symm (k • e i) := by
    intro k i
    change e.symm.permCongr ((MulAction.toPermHom (↥K) Q) k) i = e.symm (k • e i)
    rw [MulAction.toPermHom_apply, Equiv.permCongr_apply, Equiv.symm_symm,
      MulAction.toPerm_apply]
  have hsmul_gen : ∀ (c i : ZMod p),
      ((φ (Multiplicative.ofAdd c) : Xsub) : ↥K) • e i = e (c + i) := by
    intro c i
    have hi : e i = QuotientGroup.mk ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K) := rfl
    have hci : e (c + i) = QuotientGroup.mk
        ((φ (Multiplicative.ofAdd (c + i)) : Xsub) : ↥K) := rfl
    rw [hi, hci, MulAction.Quotient.smul_mk]
    congr 1
    rw [smul_eq_mul]
    apply Subtype.ext
    simpa using congrArg Subtype.val
      (map_mul φ (Multiplicative.ofAdd c) (Multiplicative.ofAdd i)).symm
  have hρφ : ∀ c : ZMod p,
      ρ ((φ (Multiplicative.ofAdd c) : Xsub) : ↥K) = Equiv.addRight c := by
    intro c
    ext i
    rw [hρ_apply, hsmul_gen c i, Equiv.symm_apply_apply, Equiv.coe_addRight]
    exact add_comm c i
  have hρx₀ : ρ x₀ = Equiv.addRight (1 : ZMod p) := by
    have hx₀eq : ((φ (Multiplicative.ofAdd (1 : ZMod p)) : Xsub) : ↥K) = x₀ := by
      change ((zmodMulEquivOfGenerator hg₀ hXsubcard (Multiplicative.ofAdd (1 : ZMod p))
        : Xsub) : ↥K) = x₀
      rw [zmodMulEquivOfGenerator_apply_ofAdd_one]
    rw [← hx₀eq]
    exact hρφ 1
  have hρX : ∀ u : ↥K, u ∈ Xsub → ∃ c : ZMod p, ρ u = Equiv.addRight c := by
    intro u hu
    obtain ⟨z, hz⟩ := φ.surjective ⟨u, hu⟩
    refine ⟨z.toAdd, ?_⟩
    have hzu : ((φ (Multiplicative.ofAdd z.toAdd) : Xsub) : ↥K) = u := by
      have hz' : φ (Multiplicative.ofAdd z.toAdd) = ⟨u, hu⟩ := by
        rw [show Multiplicative.ofAdd z.toAdd = z from rfl]
        exact hz
      exact congrArg (fun w : Xsub => (w : ↥K)) hz'
    rw [← hzu]
    exact hρφ z.toAdd
  have hle_ker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρ k = 1 := by
    intro k hk
    ext i
    rw [hρ_apply]
    have hfix : k • e i = e i := by
      have hi : e i = QuotientGroup.mk ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K) := rfl
      rw [hi, MulAction.Quotient.smul_mk]
      rw [QuotientGroup.eq]
      have hkR' : k ∈ CFSG.pCore 2 ↥K := by
        have hmem : (k : G) ∈ (CFSG.pCore 2 ↥K).map K.subtype := hk
        rcases Subgroup.mem_map.mp hmem with ⟨q, hq, hqk⟩
        have hqk' : q = k := Subtype.ext hqk
        rwa [hqk'] at hq
      have hconj : ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K)⁻¹ * k⁻¹
            * ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K) ∈ CFSG.pCore 2 ↥K := by
        simpa using Subgroup.Normal.conj_mem (inferInstance : (CFSG.pCore 2 ↥K).Normal)
          k⁻¹ ((CFSG.pCore 2 ↥K).inv_mem hkR')
          ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K)⁻¹
      have hker : (k • ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K))⁻¹
            * ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K)
          = ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K)⁻¹ * k⁻¹
            * ((φ (Multiplicative.ofAdd i) : Xsub) : ↥K) := by
        rw [smul_eq_mul]; group
      rw [Subgroup.mem_subgroupOf, hker]
      exact h.pCoreOf_le_sylowTwo (Subgroup.mem_map_of_mem K.subtype hconj)
    rw [hfix, Equiv.symm_apply_apply]
    rfl
  have hstab : ∀ k : ↥K, ρ k 0 = 0 ↔ (k : G) ∈ S := by
    intro k
    have h0 : e 0 = QuotientGroup.mk (1 : ↥K) := by
      show QuotientGroup.mk ((φ (Multiplicative.ofAdd (0 : ZMod p)) : Xsub) : ↥K)
        = QuotientGroup.mk (1 : ↥K)
      congr 1
      rw [show Multiplicative.ofAdd (0 : ZMod p) = 1 from rfl, map_one]
      rfl
    have hρ0 : ρ k 0 = e.symm (QuotientGroup.mk k) := by
      rw [hρ_apply]
      congr 1
      rw [h0, MulAction.Quotient.smul_mk]
      simp
    rw [hρ0, Equiv.symm_apply_eq, h0, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hker_le : ∀ k : ↥K, ρ k = 1 → (k : G) ∈ pCoreOf 2 K := by
    intro k hk
    have hNmapS : (ρ.ker).map K.subtype ≤ S := by
      rintro z ⟨q, hq, rfl⟩
      exact (hstab q).mp (by rw [MonoidHom.mem_ker.mp hq]; rfl)
    have hPg : IsPGroup 2 ((ρ.ker).map K.subtype) :=
      h.sylowTwo.isPGroup.to_le hNmapS
    have hcore : (ρ.ker).map K.subtype ≤ pCoreOf 2 K := by
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _) ?_ hPg
      have hsub : ((ρ.ker).map K.subtype).subgroupOf K = ρ.ker :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective ρ.ker
      rw [hsub]
      exact ρ.normal_ker
    exact hcore (Subgroup.mem_map_of_mem K.subtype (MonoidHom.mem_ker.mpr hk))
  have hrefl : ∀ k : ↥K, (k : G) ∉ pCoreOf 2 K → k * k = 1 →
      ∃ a : ZMod p, ρ k = zmodRefl p a := by
    intro k hkR hkk
    have hππ : ρ k * ρ k = 1 := by
      have h1 : ρ (k * k) = ρ k * ρ k := map_mul ρ k k
      rw [hkk, map_one] at h1
      exact h1.symm
    have hπne : ρ k ≠ 1 := fun h1 => hkR (hker_le k h1)
    have hx₀Rsup : x₀ ∈ (pCoreOf 2 K ⊔ X).subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right hc.x_mem
    have hconj : k * x₀ * k⁻¹ ∈ (pCoreOf 2 K ⊔ X).subgroupOf K :=
      Subgroup.Normal.conj_mem h.normal_pCoreOf_sup x₀ hx₀Rsup k
    have hXR : X ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      h.sylowP.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    have hprod : ((k * x₀ * k⁻¹ : ↥K) : G) ∈ (pCoreOf 2 K : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 K) X hXR]
      exact Subgroup.mem_subgroupOf.mp hconj
    obtain ⟨r, hr, y, hy, hry⟩ := Set.mem_mul.mp hprod
    have hrK : r ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hr
    have hyK : y ∈ K := h.sylowP.le hy
    have hdecomp : k * x₀ * k⁻¹ = (⟨r, hrK⟩ : ↥K) * ⟨y, hyK⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype]
      exact hry.symm
    have hρconj : ρ (k * x₀ * k⁻¹) = ρ (⟨y, hyK⟩ : ↥K) := by
      rw [hdecomp, map_mul, hle_ker ⟨r, hrK⟩ (by simpa using hr), one_mul]
    obtain ⟨c, hc⟩ := hρX ⟨y, hyK⟩ (by rw [Subgroup.mem_subgroupOf]; exact hy)
    have hconjπ : ρ k * Equiv.addRight (1 : ZMod p) * (ρ k)⁻¹ = Equiv.addRight c := by
      have h1 : ρ (k * x₀ * k⁻¹) = ρ k * ρ x₀ * (ρ k)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [← hρx₀, ← h1, hρconj, hc]
    have hπinv : (ρ k)⁻¹ = ρ k := inv_eq_of_mul_eq_one_right hππ
    have hconjπ' : ρ k * Equiv.addRight (1 : ZMod p) * ρ k = Equiv.addRight c := by
      rw [hπinv] at hconjπ
      exact hconjπ
    exact nine3_refl_of_conj hp hp2 hππ hπne hconjπ'
  have hshift : ∀ k : ↥K, (k : G) = x → ∀ i : ZMod p, ρ k i = i + 1 := by
    intro k hk i
    have hkx₀ : k = x₀ := Subtype.ext hk
    rw [hkx₀]
    have h := congrFun (congrArg DFunLike.coe hρx₀) i
    simpa [Equiv.coe_addRight] using h
  exact ⟨ρ, hker_le, hle_ker, hstab, hshift, hrefl⟩

end CFSG.LocalAnalysis.WeakClosure81
