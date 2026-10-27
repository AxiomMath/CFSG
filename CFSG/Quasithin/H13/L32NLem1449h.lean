module

public import CFSG.Quasithin.H13.L32NLem1449g
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.H13.L32NLem1449d
public import CFSG.Quasithin.H13.L32NLem1449e

public section

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert Q1449Cert L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

namespace Good

variable
  {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem isDelta5_image (hout : ∃ w ∈ Subgroup.normalizer (dI T V i : Set G), w ∉ l32nH T V) :
    CFSG.QuasithinUnique.A5.G3.IsDelta5Group ↥(CFSG.Quasithin.modO2Image
      (Subgroup.normalizer (dI T V i : Set G)) (preH D e (cenA c x₀))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Subgroup.normalizer (dI T V i : Set G) with hX
  set N := preH D e (cenA c x₀) with hN
  have hNX : N ≤ X := C.preH_le_normalizer
  have hNH : N ≤ l32nH T V := preH_le_H
  have hUR := C.U_inf_R hout
  set ψ : ↥N →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hNX) with hψ
  have hrange : ψ.range = modO2Image X N := by
    unfold modO2Image
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  set φ : ↥N →* ↥(modO2Image X N) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict with hφ
  have hφs : Function.Surjective φ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective
  have hφ1 : ∀ n : ↥N, φ n = 1 ↔ (n : G) ∈ pCoreOf 2 X := by
    intro n
    have e1 : φ n = 1 ↔ ψ n = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [e1, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact CFSG.QuasithinUnique.A5.G3.mem_pCore_iff_mem_pCoreOf (Subgroup.inclusion hNX n)
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hker2 : IsPGroup 2 ↥φ.ker := by
    intro n
    have hnR : ((n : ↥N) : G) ∈ pCoreOf 2 X := (hφ1 n).mp n.2
    obtain ⟨k, hk⟩ := hR2 ⟨_, hnR⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  set U' := (fsuU T V).subgroupOf N with hU'
  have hUn : U'.Normal := ⟨fun u hu n => by
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    simpa using L128A.HatU.conj_mem (HN (hNH n.2)) hu⟩
  have hU2 : IsPGroup 2 ↥U' := by
    intro u
    obtain ⟨k, hk⟩ := C.U_two ⟨_, Subgroup.mem_subgroupOf.mp u.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  set starA : ↥N →* ↥(cenA c x₀) :=
    ((hom8 D e (HN (T := T) (V := V))).comp (Subgroup.inclusion hNH)).codRestrict (cenA c x₀)
      (fun n => (mem_preH.mp n.2).2) with hstarA
  have hstarA_val : ∀ n : ↥N, ((starA n : ↥(cenA c x₀)) : GL (Fin 8) (ZMod 2)) =
      matOf e (D.ρ ⟨n, HN (hNH n.2)⟩) := fun n => rfl
  set α₀ : ↥N →* alternatingGroup (Fin 5) := (sigA5 C.hc C.hx₀).comp starA with hα₀
  have hstar_s : Function.Surjective starA := by
    intro a
    have haΓ : (a : GL (Fin 8) (ZMod 2)) ∈ img8 D e (l32nH T V) := by
      rw [C.imgH]
      exact (cenA_le C.hc x₀ a.2).1
    obtain ⟨h, hh, hhN, hha⟩ := (mem_img8 D e).mp haΓ
    have hhN' : h ∈ N := mem_preH.mpr ⟨hh, by rw [hha]; exact a.2⟩
    exact ⟨⟨h, hhN'⟩, Subtype.ext (by rw [hstarA_val]; exact hha)⟩
  have hα₀s : Function.Surjective α₀ := by
    intro b
    obtain ⟨a, rfl⟩ := (sigA5_bijective C.hc C.hx₀).2 b
    obtain ⟨n, rfl⟩ := hstar_s a
    exact ⟨n, rfl⟩
  have hα₀k : α₀.ker = U' := by
    ext n
    rw [MonoidHom.mem_ker, hU', Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : starA n = 1 := (sigA5_bijective C.hc C.hx₀).1 (by rw [map_one]; exact h)
      have h2 : matOf e (D.ρ ⟨n, HN (hNH n.2)⟩) = 1 := by
        rw [← hstarA_val, h1]
        rfl
      exact C.mem_U_of_star (hNH n.2) h2
    · intro h
      have h1 : starA n = 1 := Subtype.ext (by rw [hstarA_val]; exact C.star_U h)
      rw [hα₀, MonoidHom.comp_apply, h1, map_one]
  have hβmem : ∀ v : Fin 8 → ZMod 2, betaL c v ∈ evenWeight 5 := fun v => betaL_even C.hc v
  let β₀ : ↥U' →* Multiplicative (evenWeight 5) :=
    { toFun := fun u => Multiplicative.ofAdd ⟨betaL c (e (D.π ((u : ↥N) : G))), hβmem _⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp [L128A.HatU.π_one]
      map_mul' := fun u v => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        have hu := Subgroup.mem_subgroupOf.mp u.2
        have hv := Subgroup.mem_subgroupOf.mp v.2
        change betaL c (e (D.π (((u * v : ↥U') : ↥N) : G))) =
          betaL c (e (D.π ((u : ↥N) : G))) + betaL c (e (D.π ((v : ↥N) : G)))
        rw [Subgroup.coe_mul, Subgroup.coe_mul, D.π_mul _ hu _ hv, map_add, map_add] }
  have hβ₀v : ∀ u : ↥U', ((Multiplicative.toAdd (β₀ u) : evenWeight 5) : Fin 5 → ZMod 2) =
      betaL c (e (D.π ((u : ↥N) : G))) := fun u => rfl
  have hβ₀s : Function.Surjective β₀ := by
    intro w
    have hw : ∑ j, ((Multiplicative.toAdd w : evenWeight 5) : Fin 5 → ZMod 2) j = 0 :=
      (Multiplicative.toAdd w).2
    set J := Finset.univ.filter
      (fun j => ((Multiplicative.toAdd w : evenWeight 5) : Fin 5 → ZMod 2) j = 1) with hJ
    have hw' := eq_sum_fV _ hw
    set v : Fin 8 → ZMod 2 := ∑ j ∈ J, vec8 ((fiveS c).getD j 0) with hv
    have hbv : betaL c v = ((Multiplicative.toAdd w : evenWeight 5) : Fin 5 → ZMod 2) := by
      rw [hv, map_sum, hw']
      exact Finset.sum_congr rfl fun j _ => betaL_u C.hc j
    obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm v)
    refine ⟨⟨⟨u, C.U_le_preH hu⟩, Subgroup.mem_subgroupOf.mpr hu⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [hβ₀v]
    show betaL c (e (D.π u)) = _
    rw [hue, LinearEquiv.apply_symm_apply, hbv]
  have hβ₀k : ∀ u : ↥U', β₀ u = 1 ↔ φ u = 1 := by
    intro u
    have hu := Subgroup.mem_subgroupOf.mp u.2
    rw [hφ1]
    have e1 : β₀ u = 1 ↔ betaL c (e (D.π ((u : ↥N) : G))) = 0 := by
      rw [← hβ₀v]
      constructor
      · intro h
        rw [h]
        rfl
      · intro h
        apply Multiplicative.toAdd.injective
        exact Subtype.ext h
    rw [e1, betaL_eq_zero_iff C.hc C.hx₀, ← C.mem_rI_iff hu, ← hUR]
    exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
  have hcomp : ∀ (n : ↥N) (u v : ↥U'), (v : ↥N) = n * u * n⁻¹ → ∀ j : Fin 5,
      ((Multiplicative.toAdd (β₀ v) : evenWeight 5) : Fin 5 → ZMod 2) j =
        ((Multiplicative.toAdd (β₀ u) : evenWeight 5) : Fin 5 → ZMod 2)
          (((α₀ n : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ j) := by
    intro n u v huv j
    have hu := Subgroup.mem_subgroupOf.mp u.2
    have hv : ((v : ↥N) : G) = (n : G) * ((u : ↥N) : G) * (n : G)⁻¹ := by
      rw [huv]
      rfl
    rw [hβ₀v, hβ₀v, hv]
    have h1 : e (D.π ((n : G) * ((u : ↥N) : G) * (n : G)⁻¹)) =
        (((starA n : ↥(cenA c x₀)) : GL (Fin 8) (ZMod 2)) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π ((u : ↥N) : G))) := by
      rw [hstarA_val, matOf_mulVec, D.ρ_π _ _ hu]
    rw [h1, sigA_spec C.hc C.hx₀, permL_apply, hα₀, MonoidHom.comp_apply, coe_sigA5]
  exact isDelta5Group_of_surj φ hφs hker2 hUn hU2 α₀ hα₀s hα₀k β₀ hβ₀s hβ₀k hcomp

theorem false_of (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hΔ : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      CFSG.SectionRank.IsSQTKCat X → CFSG.pCore 2 X = ⊥ →
        CFSG.QuasithinUnique.A5.G3.NoDelta5In X)
    {z x : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hx : x⁻¹ * z * x = i) : False := by
  obtain ⟨hUx, u, hu, hux⟩ := C.exists_out hz hz1 hx
  have hout : ∃ w ∈ Subgroup.normalizer (dI T V i : Set G), w ∉ l32nH T V :=
    ⟨x⁻¹ * u * x, hUx u hu, hux⟩
  have hD5 := C.isDelta5_image hout
  obtain ⟨S₀, hS₀, hS₀N⟩ := C.exists_sylow
  have h13 := C.base.hyp.hyp.h13
  have := h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h13.nonabelian h13.qtke).1
  have hXne : pCoreOf 2 (Subgroup.normalizer (dI T V i : Set G)) ≠ ⊥ := by
    intro h
    have h1 := C.dI_le_R y_mem_dI
    rw [h, Subgroup.mem_bot] at h1
    apply C.y_not_mem_U
    rw [h1]
    exact one_mem _
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hXne
  have hS := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
    (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hS₀)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.normalizer (dI T V i : Set G))))
    (QuotientGroup.mk'_surjective _)
  have hSN := CFSG.QuasithinUnique.A5.G3.map_normalizes
    (C := Subgroup.normalizer (dI T V i : Set G)) hS₀N
  have hcore : Vol2Native.A36CoreForSQTKCat :=
    Vol2Native.A36ForSQTKCat.core fun Q _ hQ => h36 Q (sqtkHyp_of_cat hQ)
  exact false_of_delta5 hQ hcore (fun Q _ hQ => h37 Q (sqtkHyp_of_cat hQ))
    (fun Q _ hQ => h39 Q (sqtkHyp_of_cat hQ)) hΔ hS hSN hD5

end Good

end CFSG.Quasithin.H13.L1449
