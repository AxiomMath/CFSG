module

public import CFSG.RankThree.PartOne.S15K.NormAct
public import CFSG.RankThree.PartOne.S12.Hyp
import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.RankThree.PartOne

theorem E_le_normalizer_lieGenerated {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
  fun _ he => torusNormalizer_le_lieNormalizer hp E (Subgroup.le_normalizer he)

theorem card_le_of_injective_mod_normal {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    {K : Type*} [Field K] [Finite K] (hcyc : IsCyclic (K ≃+* K)) (F : (K ≃+* K) →* Γ) {p : ℕ} (hp : p.Prime)
    (hQ : ∀ γ : Γ, γ ^ p ∈ N → ∃ σ : K ≃+* K, γ * (F σ)⁻¹ ∈ N) {E : Type*} [Group E] [Finite E]
    (hE : ∀ e : E, e ^ p = 1) (ρ : E →* Γ) (hinj : ∀ e : E, ρ e ∈ N → e = 1) :
    Nat.card E ≤ p := by
  classical
  let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  let Fb : Subgroup (Γ ⧸ N) := (π.comp F).range
  have hFbcyc : IsCyclic Fb :=
    isCyclic_of_surjective (π.comp F).rangeRestrict (π.comp F).rangeRestrict_surjective
  have hFbmem : ∀ e : E, π (ρ e) ∈ Fb := by
    intro e
    obtain ⟨τ, hτ⟩ := hQ (ρ e) (by rw [← map_pow, hE e, map_one]; exact N.one_mem)
    have h1 : π (ρ e * (F τ)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hτ
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact ⟨τ, by simpa using h1.symm⟩
  let f : E →* Fb := (π.comp ρ).codRestrict Fb hFbmem
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hinj
    have : π (ρ e) = 1 := congrArg Subtype.val he
    exact (QuotientGroup.eq_one_iff _).1 this
  have hKfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have : Finite Fb := Finite.of_surjective _ (π.comp F).rangeRestrict_surjective
  let _ : Fintype Fb := Fintype.ofFinite Fb
  have hle := IsCyclic.card_pow_eq_one_le (α := Fb) hp.pos
  calc Nat.card E ≤ Nat.card {x : Fb // x ^ p = 1} := by
        refine Nat.card_le_card_of_injective (fun e => ⟨f e, ?_⟩) ?_
        · rw [← map_pow, hE e, map_one]
        · intro a b hab
          exact hfinj (congrArg Subtype.val hab)
    _ ≤ p := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact hle

theorem actP_mem_normal_of_bound {G : Type} [Group G] [Finite G] {P : Type*} [Group P] {p : ℕ}
    {I E : Subgroup G} (φ : ↥I ≃* P) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hWI : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (I : Set G))
    (hEcard : p < Nat.card E) (hirr : torusIrreducible E)
    (N : Subgroup (MulAut P)) (hN : N.Normal)
    (hbound : ∀ ρ : ↥E →* MulAut P, (∀ e : ↥E, ρ e ∈ N → e = 1) → Nat.card ↥E ≤ p) :
    ∀ e : ↥E, actP φ ⟨(e : G), hEI e.2⟩ ∈ N := by
  classical
  let ρ : ↥E →* MulAut P := (actP φ).comp (Subgroup.inclusion hEI)
  let E0 : Subgroup ↥E := N.comap ρ
  have hE0inv : torusInvariant E ⊤ (E0.map E.subtype) := by
    intro w hw b hb
    obtain ⟨b', hb', rfl⟩ := hb
    have hwW : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hmem : w * (b' : G) * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hwW (b' : G)).1 b'.2
    refine ⟨⟨w * (b' : G) * w⁻¹, hmem⟩, ?_, rfl⟩
    have hwI : w ∈ Subgroup.normalizer (I : Set G) := hWI hwW
    have hprod : (⟨w * (b' : G) * w⁻¹, hEI hmem⟩ : ↥(Subgroup.normalizer (I : Set G))) =
        ⟨w, hwI⟩ * ⟨(b' : G), hEI b'.2⟩ * ⟨w, hwI⟩⁻¹ := Subtype.ext rfl
    show actP φ ⟨w * (b' : G) * w⁻¹, hEI hmem⟩ ∈ N
    rw [hprod, map_mul, map_mul, map_inv]
    exact hN.conj_mem _ hb' _
  rcases hirr (E0.map E.subtype) (Subgroup.map_subtype_le E0) hE0inv with hbot | htop
  · exfalso
    have hinj : ∀ e : ↥E, ρ e ∈ N → e = 1 := by
      intro e he
      have : (e : G) ∈ E0.map E.subtype := ⟨e, he, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have := hbound ρ hinj
    omega
  · intro e
    have : (e : G) ∈ E0.map E.subtype := by rw [htop]; exact e.2
    obtain ⟨e', he', he'e⟩ := this
    have : e' = e := Subtype.ext he'e
    rw [← this]
    exact he'

theorem centralizer_inf_eq_bot {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E I : Subgroup G} [hE : IsElementaryAbelian p E]
    (hmax : ∀ F : Subgroup G, IsElementaryAbelian p F → E ≤ F → F = E)
    (hWI : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (I : Set G))
    (hirr : torusIrreducible E) (hZ : I ⊓ Subgroup.centralizer (I : Set G) = ⊥)
    (hpI : p ∣ Nat.card I) : E ⊓ Subgroup.centralizer (I : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hCinv : torusInvariant E ⊤ (E ⊓ Subgroup.centralizer (I : Set G)) := by
    intro w hw c hc
    have hwW : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hwI : w ∈ Subgroup.normalizer (I : Set G) := hWI hwW
    refine ⟨(Subgroup.mem_normalizer_iff.1 hwW c).1 hc.1, ?_⟩
    show w * c * w⁻¹ ∈ Subgroup.centralizer (I : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : w⁻¹ * x * w ∈ I := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (I : Set G)).inv_mem hwI) x).1 hx
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hx'
    calc x * (w * c * w⁻¹) = w * ((w⁻¹ * x * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * x * w)) * w⁻¹ := by rw [h1]
      _ = (w * c * w⁻¹) * x := by group
  rcases hirr _ inf_le_left hCinv with hbot | htop
  · exact hbot
  · exfalso
    have hEc : E ≤ Subgroup.centralizer (I : Set G) := fun g hg => by
      have : g ∈ E ⊓ Subgroup.centralizer (I : Set G) := by rw [htop]; exact hg
      exact this.2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpI
    have hxp : (x : G) ^ p = 1 := by
      have : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      exact congrArg Subtype.val this
    have hzel : IsElementaryAbelian p (Subgroup.zpowers (x : G)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    have hzc : Subgroup.zpowers (x : G) ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.1 (hEc hg) _ x.2).symm
    have hF := IsElementaryAbelian.sup_of_le_centralizer (p := p) (E := E)
      (C := Subgroup.zpowers (x : G)) hzc
    have hFE := hmax _ hF le_sup_left
    have hxE : (x : G) ∈ E := by
      rw [← hFE]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hx1 : (x : G) ∈ I ⊓ Subgroup.centralizer (I : Set G) := ⟨x.2, hEc hxE⟩
    rw [hZ, Subgroup.mem_bot] at hx1
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx

theorem mem_centralizer_of_actP_eq_one {G : Type*} [Group G] {P : Type*} [Group P] {I : Subgroup G}
    (φ : ↥I ≃* P) {g : ↥(Subgroup.normalizer (I : Set G))} (hg : actP φ g = 1) :
    (g : G) ∈ Subgroup.centralizer (I : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : actP φ g (φ ⟨y, hy⟩) = φ ⟨y, hy⟩ := by rw [hg]; rfl
  rw [actP_apply] at h1
  have h2 : I.normalizerMonoidHom g ⟨y, hy⟩ = ⟨y, hy⟩ := φ.injective h1
  have h3 := congrArg Subtype.val h2
  rw [coe_normalizerMonoidHom_apply] at h3
  calc y * (g : G) = ((g : G) * y * (g : G)⁻¹) * g := by rw [h3]
    _ = (g : G) * y := by group

end CFSG.RankThree.PartOne.S15K
