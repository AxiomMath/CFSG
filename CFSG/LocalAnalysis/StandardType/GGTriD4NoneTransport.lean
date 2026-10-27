module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Induced

variable {G : Type*} [Group G] (K : Subgroup G) {R : Type} [Group R]
  (θ : K ⧸ Subgroup.center K ≃* R)

theorem ggLAut_pow_eq_one_of_pow {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hxn : x ^ n = 1) : ggLAut K θ ⟨x, hx⟩ ^ n = 1 := by
  rw [← map_pow]
  have h : (⟨x, hx⟩ : Subgroup.normalizer (K : Set G)) ^ n = 1 :=
    Subtype.ext (by simpa using hxn)
  rw [h, map_one]

theorem ggLAut_mem_of_split (S : Subgroup (MulAut R)) {B₁ Bs : Subgroup G} {x : G}
    (hBN : Bs ≤ Subgroup.normalizer (K : Set G)) (hsplit : Bs = B₁ ⊔ Subgroup.zpowers x)
    (hB₁Bs : B₁ ≤ Bs) (hxBs : x ∈ Bs)
    (h₁ : ∀ b (hb : b ∈ B₁), ggLAut K θ ⟨b, hBN (hB₁Bs hb)⟩ ∈ S)
    (hxS : ggLAut K θ ⟨x, hBN hxBs⟩ ∈ S) :
    ∀ b (hb : b ∈ Bs), ggLAut K θ ⟨b, hBN hb⟩ ∈ S := by
  intro b hb
  have hT : Bs ≤ (S.comap (ggLAut K θ)).map (Subgroup.normalizer (K : Set G)).subtype := by
    rw [hsplit]
    refine sup_le ?_ ?_
    · intro c hc
      exact ⟨⟨c, hBN (hB₁Bs hc)⟩, h₁ c hc, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨x, hBN hxBs⟩, hxS, rfl⟩
  obtain ⟨n, hn, hnb⟩ := hT hb
  have h : n = ⟨b, hBN hb⟩ := Subtype.ext hnb
  rw [h] at hn
  exact hn

end Induced

section Centerless

variable {G : Type*} [Group G] {K : Subgroup G} {R : Type} [Group R]

theorem ggCenterlessMap_injective (θ : K ⧸ Subgroup.center K ≃* R) (hZ : Subgroup.center K = ⊥) :
    Function.Injective
      ((θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))) := by
  intro a b hab
  have h1 : (a : K ⧸ Subgroup.center K) = b := θ.injective hab
  have h2 := QuotientGroup.eq.1 h1
  rw [hZ, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem ggCenterlessMap_surjective (θ : K ⧸ Subgroup.center K ≃* R) :
    Function.Surjective
      ((θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))) := by
  intro r
  obtain ⟨q, rfl⟩ := θ.surjective r
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨k, rfl⟩

@[expose] noncomputable def ggCenterlessEquiv (θ : K ⧸ Subgroup.center K ≃* R)
    (hZ : Subgroup.center K = ⊥) : K ≃* R :=
  MulEquiv.ofBijective
    ((θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K)))
    ⟨ggCenterlessMap_injective θ hZ, ggCenterlessMap_surjective θ⟩

theorem ggCenterlessEquiv_apply (θ : K ⧸ Subgroup.center K ≃* R) (hZ : Subgroup.center K = ⊥)
    (k : K) : ggCenterlessEquiv θ hZ k = θ (k : K ⧸ Subgroup.center K) :=
  rfl

theorem ggAutFixedSubgroup_eq_map (θ : K ⧸ Subgroup.center K ≃* R) (hZ : Subgroup.center K = ⊥)
    {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ggAutFixedSubgroup (ggLAut K θ ⟨x, hx⟩) =
      ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K).map
        (ggCenterlessEquiv θ hZ).toMonoidHom := by
  ext r
  obtain ⟨k, rfl⟩ := (ggCenterlessEquiv θ hZ).surjective r
  rw [mem_ggAutFixedSubgroup, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨k, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨k.2, ?_⟩
    have h1 : ggLAut K θ ⟨x, hx⟩ (θ (k : K ⧸ Subgroup.center K)) =
        θ (k : K ⧸ Subgroup.center K) := h
    rw [ggLAut_apply] at h1
    have h2 := θ.injective h1
    have h3 : (K.normalizerMonoidHom ⟨x, hx⟩ k : K) = k := by
      have := QuotientGroup.eq.1 h2
      rw [hZ, Subgroup.mem_bot] at this
      exact inv_mul_eq_one.1 this
    have h4 := congrArg Subtype.val h3
    rw [normalizerMonoidHom_coe] at h4
    calc (k : G) * x = (x * k * x⁻¹) * x := by rw [h4]
      _ = x * k := by group
  · rintro ⟨k', hk', hkk'⟩
    have hkk : k' = k := (ggCenterlessEquiv θ hZ).injective hkk'
    subst hkk
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hk'
    have h3 : (K.normalizerMonoidHom ⟨x, hx⟩ k' : K) = k' := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      calc x * (k' : G) * x⁻¹ = (k' : G) * x * x⁻¹ := by rw [hk'.2]
        _ = k' := by group
    change ggLAut K θ ⟨x, hx⟩ (θ (k' : K ⧸ Subgroup.center K)) = θ (k' : K ⧸ Subgroup.center K)
    rw [ggLAut_apply, h3]

theorem exists_component_fixed_of_centerless (θ : K ⧸ Subgroup.center K ≃* R)
    (hZ : Subgroup.center K = ⊥) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    {J : Subgroup G} (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∃ (Q : Subgroup R) (_ : ↥J ≃* ↥Q),
      IsComponentOf Q (ggAutFixedSubgroup (ggLAut K θ ⟨x, hx⟩)) := by
  set e := ggCenterlessEquiv θ hZ with he
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  let e' : ↥J ≃* ↥((J.subgroupOf K).map e.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hJK).symm.trans
      ((J.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective)
  refine ⟨(J.subgroupOf K).map e.toMonoidHom, e', ?_⟩
  rw [ggAutFixedSubgroup_eq_map θ hZ hx]
  refine ⟨Subgroup.map_mono (Subgroup.comap_mono hJ.1), ?_, ?_⟩
  · exact (hJ.2.1.comap K.subtype).map e.toMonoidHom
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv e'.symm hJ.2.2

end Centerless

section StdSub

variable {G : Type} [Group G] [Finite G]

theorem isComponentOf_inf_centralizer_of_ggNbr {p : ℕ} {B : Subgroup G} {x y : G}
    {L D J K : Subgroup G} (hS : LargeEvenSStar p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hnbr : GGNbr p B x D J y K) (hJK : J ≤ K) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hJc := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnbr.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnbr.1.2.2.2.1
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := hJc.1.trans inf_le_right
  exact hJc.of_le_of_le (le_inf hJK hJx) (inf_le_inf_right _ hKy)

end StdSub

end CFSG.StandardType
