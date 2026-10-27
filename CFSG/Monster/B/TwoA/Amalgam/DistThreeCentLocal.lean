module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentStruct

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

section Act

variable {u : CVert} {ρ : vStab u →* GStar} {iu : cgraph.neighborSet u ≃ rootClass}

theorem cvMul_mem_nbr {g : Shat} (hg : g ∈ vStab u) {z : CVert} (hz : z ∈ cgraph.neighborSet u) :
    cvMul z g ∈ cgraph.neighborSet u := cvMul_mem_neighborSet hg hz

theorem inl_iv_cvMul (h : IsCompatLocal u ρ iu) {g : Shat} (hg : g ∈ vStab u) {z : CVert}
    (hz : z ∈ cgraph.neighborSet u) :
    SemidirectProduct.inl (iu ⟨cvMul z g, cvMul_mem_nbr hg hz⟩ : stdGroup) =
      (ρ ⟨g, hg⟩)⁻¹ * SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup) * ρ ⟨g, hg⟩ :=
  h.2.2.1 ⟨g, hg⟩ ⟨z, hz⟩

theorem cvMul_eq_self_iff (h : IsCompatLocal u ρ iu) {g : Shat} (hg : g ∈ vStab u) {z : CVert}
    (hz : z ∈ cgraph.neighborSet u) :
    cvMul z g = z ↔ Commute (ρ ⟨g, hg⟩) (SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup)) := by
  have key := inl_iv_cvMul h hg hz
  constructor
  · intro e
    have e' : (⟨cvMul z g, cvMul_mem_nbr hg hz⟩ : cgraph.neighborSet u) = ⟨z, hz⟩ :=
      Subtype.ext e
    rw [e'] at key
    calc ρ ⟨g, hg⟩ * SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup)
        = ρ ⟨g, hg⟩ * ((ρ ⟨g, hg⟩)⁻¹ * SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup) *
            ρ ⟨g, hg⟩) := by rw [← key]
      _ = SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup) * ρ ⟨g, hg⟩ := by group
  · intro hc
    have e : (SemidirectProduct.inl (iu ⟨cvMul z g, cvMul_mem_nbr hg hz⟩ : stdGroup) : GStar) =
        SemidirectProduct.inl (iu ⟨z, hz⟩ : stdGroup) := by
      rw [key, mul_assoc, ← hc.eq, inv_mul_cancel_left]
    have e2 := iu.injective (Subtype.ext (SemidirectProduct.inl_injective e))
    exact congrArg Subtype.val e2

end Act

theorem conj_mul_eq {G : Type*} [Group G] (A B X : G) :
    (A * B)⁻¹ * X * (A * B) = B⁻¹ * (A⁻¹ * X * A) * B := by group

theorem hom_conj_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (a x : G) :
    f (a⁻¹ * x * a) = (f a)⁻¹ * f x * f a := by
  rw [map_mul f, map_mul f, map_inv f]

theorem conj_inl_of_mem_starSub
    {γ : GStar}
    (hγ : γ ∈ CFSG.Monster.B.E6.FieldInvF4.starSub CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed)
    {x : stdGroup} (hx : x ∈ groupJ.subgroupOf stdGroup) :
    γ⁻¹ * SemidirectProduct.inl x * γ = SemidirectProduct.inl (γ.left⁻¹ * x * γ.left) := by
  have hγl : γ.left ∈ groupJ.subgroupOf stdGroup := hγ
  have hy : γ.left⁻¹ * x * γ.left ∈ groupJ.subgroupOf stdGroup :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγl) hx) hγl
  have e1 := conj_mul_eq (SemidirectProduct.inl γ.left : GStar) (SemidirectProduct.inr γ.right)
    (SemidirectProduct.inl x)
  rw [SemidirectProduct.inl_left_mul_inr_right γ] at e1
  rw [e1, ← hom_conj_eq, ← map_inv SemidirectProduct.inr, ← SemidirectProduct.inl_aut_inv]
  congr 1
  have hfix := CFSG.Monster.B.E6.FieldInvF4.apply_of_mem_betaGroup
    CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed γ.right⁻¹ hy
  exact hfix

section Pair

variable {v u : CVert} {ρ : vStab u →* GStar} {iu : cgraph.neighborSet u ≃ rootClass}
  {c : vStab u}

theorem mem_vStab_of_mem_comap
    (h : IsCompatLocal u ρ iu) (hρc : ρ c = betaStarElt)
    (hRC : (vStab v).subgroupOf (vStab u) = Subgroup.centralizer {c}) {y : vStab u}
    (hy : y ∈ jStar.comap ρ) : (y : Shat) ∈ vStab v :=
  Subgroup.mem_subgroupOf.1 (hRC.ge (Subgroup.mem_centralizer_singleton_iff.2
    (commute_of_mem h.1 (ker_eq_zpowers_cStab h.2.1) hρc hy)))

theorem betaStarElt_mul_self : betaStarElt * betaStarElt = 1 := by
  rw [← sq, ← CFSG.Monster.B.E6.FieldInvF4.orderOf_betaStarElt, pow_orderOf_eq_one]

theorem range_rho_pair
    (h : IsCompatLocal u ρ iu) (hc : (c : Shat) = clabelS v)
    (hρc : ρ c = betaStarElt) (hRC : (vStab v).subgroupOf (vStab u) = Subgroup.centralizer {c}) :
    (ρ.comp (Subgroup.inclusion (inf_le_right : vStab v ⊓ vStab u ≤ vStab u))).range =
      Subgroup.centralizer {betaStarElt} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : Subgroup.inclusion (inf_le_right : vStab v ⊓ vStab u ≤ vStab u) x ∈
        Subgroup.centralizer {c} := hRC.le (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 x.2).1)
    have hcomm : Commute (Subgroup.inclusion (inf_le_right : vStab v ⊓ vStab u ≤ vStab u) x) c :=
      Subgroup.mem_centralizer_singleton_iff.1 hx
    have hc2 := hcomm.map ρ
    rw [hρc] at hc2
    exact Subgroup.mem_centralizer_singleton_iff.2 hc2
  · intro γ hγ
    have hγ' : Commute γ betaStarElt := Subgroup.mem_centralizer_singleton_iff.1 hγ
    refine (mem_jStar_or_of_commute hγ').elim (fun h1 => ?_) (fun h1 => ?_)
    · refine (h.1 γ).elim (fun y hy => ?_)
      have hyN : y ∈ jStar.comap ρ := by
        show ρ y ∈ jStar
        rw [hy]
        exact h1
      refine ⟨⟨y, Subgroup.mem_inf.2 ⟨mem_vStab_of_mem_comap h hρc hRC hyN, y.2⟩⟩, ?_⟩
      exact hy
    · refine (h.1 (γ * betaStarElt)).elim (fun y hy => ?_)
      have hyN : y ∈ jStar.comap ρ := by
        show ρ y ∈ jStar
        rw [hy]
        exact h1
      have hcv : ((c : vStab u) : Shat) ∈ vStab v := by
        rw [hc]
        exact clabelS_mem_vStab_self v
      have hm : ((y * c : vStab u) : Shat) ∈ vStab v :=
        (vStab v).mul_mem (mem_vStab_of_mem_comap h hρc hRC hyN) hcv
      refine ⟨⟨(y * c : vStab u), Subgroup.mem_inf.2 ⟨hm, (y * c).2⟩⟩, ?_⟩
      show ρ (y * c) = γ
      rw [map_mul ρ, hy, hρc, mul_assoc, betaStarElt_mul_self, mul_one]

end Pair

section Stab

variable {v u : CVert} {ρ : vStab u →* GStar} {iu : cgraph.neighborSet u ≃ rootClass}
  {c : vStab u}

theorem mem_centralizer_beta_of_tStar {γ : GStar}
    (hγ : γ ∈ Subgroup.centralizer {CFSG.Monster.B.E6.FieldInvF4.tStar}) :
    γ ∈ Subgroup.centralizer {betaStarElt} := by
  rw [CFSG.Monster.B.E6.FieldInvF4.centralizer_tStar,
    CFSG.Monster.B.E6.FieldInvF4.mem_starSub, Subgroup.mem_subgroupOf] at hγ
  rw [CFSG.Monster.B.E6.FieldInvF4.centralizer_betaStarElt,
    CFSG.Monster.B.E6.FieldInvF4.mem_starSub, Subgroup.mem_subgroupOf]
  exact hγ.1

theorem commute_rootStar_of_tStar {γ : GStar}
    (hγ : γ ∈ Subgroup.centralizer {CFSG.Monster.B.E6.FieldInvF4.tStar}) :
    Commute γ rootStar := by
  have h1 : Commute γ CFSG.Monster.B.E6.FieldInvF4.tStar :=
    Subgroup.mem_centralizer_singleton_iff.1 hγ
  have h2 : Commute γ betaStarElt :=
    Subgroup.mem_centralizer_singleton_iff.1 (mem_centralizer_beta_of_tStar hγ)
  have h3 := h1.mul_right h2.inv_right
  rwa [CFSG.Monster.B.E6.FieldInvF4.tStar, mul_inv_cancel_right] at h3

theorem natCard_stab_root
    (hsv : clabelS u ∈ vStab v) (h : IsCompatLocal u ρ iu)
    (hc : (c : Shat) = clabelS v) (hρc : ρ c = betaStarElt)
    (hRC : (vStab v).subgroupOf (vStab u) = Subgroup.centralizer {c}) {z₀ : CVert}
    (hz₀ : z₀ ∈ cgraph.neighborSet u) (ht : (iu ⟨z₀, hz₀⟩ : stdGroup) = rootInv) :
    Nat.card (vStab v ⊓ vStab u ⊓ vStab z₀ : Subgroup Shat) = 190253629440 := by
  have hle : vStab v ⊓ vStab u ⊓ vStab z₀ ≤ vStab u := inf_le_left.trans inf_le_right
  have hcard := Subgroup.card_ker_mul_card_range (ρ.comp (Subgroup.inclusion hle))
  have hrange : (ρ.comp (Subgroup.inclusion hle)).range =
      Subgroup.centralizer {CFSG.Monster.B.E6.FieldInvF4.tStar} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hxR : (x : Shat) ∈ vStab v ⊓ vStab u := (Subgroup.mem_inf.1 x.2).1
      have hβ : ρ (Subgroup.inclusion hle x) ∈ Subgroup.centralizer {betaStarElt} := by
        rw [← range_rho_pair h hc hρc hRC]
        exact ⟨⟨x, hxR⟩, rfl⟩
      have hfix : cvMul z₀ (x : Shat) = z₀ := (Subgroup.mem_inf.1 x.2).2
      have ht' := (cvMul_eq_self_iff h (hle x.2) hz₀).1 hfix
      rw [ht] at ht'
      have h1 : Commute (ρ (Subgroup.inclusion hle x)) betaStarElt :=
        Subgroup.mem_centralizer_singleton_iff.1 hβ
      exact Subgroup.mem_centralizer_singleton_iff.2 (ht'.mul_right h1)
    · intro γ hγ
      have hβ := mem_centralizer_beta_of_tStar hγ
      rw [← range_rho_pair h hc hρc hRC] at hβ
      refine hβ.elim (fun x hx => ?_)
      have hcomm : Commute (ρ ⟨(x : Shat), (Subgroup.mem_inf.1 x.2).2⟩)
          (SemidirectProduct.inl (iu ⟨z₀, hz₀⟩ : stdGroup)) := by
        rw [ht]
        have e : ρ ⟨(x : Shat), (Subgroup.mem_inf.1 x.2).2⟩ = γ := hx
        rw [e]
        exact commute_rootStar_of_tStar hγ
      have hfix := (cvMul_eq_self_iff h (Subgroup.mem_inf.1 x.2).2 hz₀).2 hcomm
      exact ⟨⟨(x : Shat), Subgroup.mem_inf.2 ⟨x.2, hfix⟩⟩, hx⟩
  have hk := ker_eq_zpowers_cStab h.2.1
  have hker_le : Nat.card (ρ.comp (Subgroup.inclusion hle)).ker ≤ 2 := by
    have hinj : Nat.card (ρ.comp (Subgroup.inclusion hle)).ker ≤ Nat.card ρ.ker := by
      refine Nat.card_le_card_of_injective (fun x => ⟨Subgroup.inclusion hle x, x.2⟩) ?_
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ρ.ker => ((z : vStab u) : Shat)) hxy))
    have hk2 : Nat.card ρ.ker = 2 :=
      (congrArg (fun H : Subgroup (vStab u) => Nat.card H) hk).trans (natCard_zpowers_cStab u)
    omega
  have hfixu := (fix_neighborSet_iff u (clabelS u)).2 (by
    rw [coe_clabelS]; exact Subgroup.mem_zpowers _)
  have hmem0 : clabelS u ∈ vStab v ⊓ vStab u ⊓ vStab z₀ :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hsv, clabelS_mem_vStab_self u⟩, hfixu.2 z₀ hz₀⟩
  have hx0 : (⟨clabelS u, hmem0⟩ : (vStab v ⊓ vStab u ⊓ vStab z₀ : Subgroup Shat)) ∈
      (ρ.comp (Subgroup.inclusion hle)).ker := by
    have e : Subgroup.inclusion hle
        (⟨clabelS u, hmem0⟩ : (vStab v ⊓ vStab u ⊓ vStab z₀ : Subgroup Shat)) = cStab u := rfl
    have h1 : ρ (cStab u) = 1 := by
      rw [← MonoidHom.mem_ker, hk]
      exact Subgroup.mem_zpowers _
    exact MonoidHom.mem_ker.2 ((congrArg ρ e).trans h1)
  have hne : (ρ.comp (Subgroup.inclusion hle)).ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hx0
    have h1 := congrArg Subtype.val hx0
    have h2 : orderOf (clabelS u) = 1 := by
      rw [show clabelS u = 1 from h1, orderOf_one]
    rw [orderOf_clabelS] at h2
    exact absurd h2 (by decide)
  have : Finite (vStab v ⊓ vStab u ⊓ vStab z₀ : Subgroup Shat) :=
    Finite.of_injective _ Subtype.val_injective
  have hker_ge := (Subgroup.one_lt_card_iff_ne_bot (ρ.comp (Subgroup.inclusion hle)).ker).2 hne
  have hker : Nat.card (ρ.comp (Subgroup.inclusion hle)).ker = 2 := by omega
  have h2 : Nat.card (ρ.comp (Subgroup.inclusion hle)).range = 95126814720 :=
    (congrArg (fun H : Subgroup GStar => Nat.card H) hrange).trans
      CFSG.Monster.B.E6.FieldInvF4.card_centralizer_tStar
  calc Nat.card (vStab v ⊓ vStab u ⊓ vStab z₀ : Subgroup Shat) =
        Nat.card (ρ.comp (Subgroup.inclusion hle)).ker *
          Nat.card (ρ.comp (Subgroup.inclusion hle)).range := hcard.symm
    _ = 2 * 95126814720 := congrArg₂ (· * ·) hker h2
    _ = 190253629440 := by norm_num

end Stab

end CFSG.Monster.B.TwoA.Amalgam
