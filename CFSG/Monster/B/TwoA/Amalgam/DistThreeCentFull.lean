module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentImage

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

section Full

variable {v u : CVert} {ρ : vStab v →* GStar} {s : vStab v}

theorem comap_le_subgroupOf
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (hidx : ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) ≤ 102)
    (hcu : clabelS v ∈ vStab u) :
    jStar.comap ρ ≤ (vStab u).subgroupOf (vStab v) := by
  have : Finite (vStab v) := Finite.of_injective _ Subtype.val_injective
  have hNC : jStar.comap ρ ≤ Subgroup.centralizer {s} := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem hsurj hker hs hn)
  have hpos : ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hle : (((vStab u).subgroupOf (vStab v)).subgroupOf (jStar.comap ρ)).index ≤ 102 :=
    (Subgroup.relIndex_le_of_le_right hNC hpos).trans hidx
  have hdvd := Subgroup.index_map_dvd
    (H := ((vStab u).subgroupOf (vStab v)).subgroupOf (jStar.comap ρ)) (jHom_surjective ρ hsurj)
  have hKpos : (((vStab u).subgroupOf (vStab v)).subgroupOf (jStar.comap ρ)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hmap : ((((vStab u).subgroupOf (vStab v)).subgroupOf (jStar.comap ρ)).map
      (jHom ρ)).index ≤ 102 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hKpos) hdvd).trans hle
  have htop : (((vStab u).subgroupOf (vStab v)).subgroupOf (jStar.comap ρ)).map (jHom ρ) = ⊤ := by
    by_contra hne
    have := le_index_of_ne_top hne
    omega
  intro n hn
  have hmem : jHom ρ ⟨n, hn⟩ ∈
      (((vStab u).subgroupOf (vStab v)).subgroupOf (jStar.comap ρ)).map (jHom ρ) := by
    rw [htop]; exact Subgroup.mem_top _
  refine (Subgroup.mem_map.1 hmem).elim (fun k hk => ?_)
  have hρ : ρ n = ρ k := ((jHom_eq_jHom_iff ρ k ⟨n, hn⟩).1 hk.2).symm
  have h1 : (k : vStab v)⁻¹ * n ∈ ρ.ker := (ρ.eq_iff).1 hρ
  rw [hker] at h1
  have hcR : cStab v ∈ (vStab u).subgroupOf (vStab v) := Subgroup.mem_subgroupOf.2 hcu
  have h2 : (k : vStab v)⁻¹ * n ∈ (vStab u).subgroupOf (vStab v) :=
    (Subgroup.zpowers_le.2 hcR) h1
  have h3 : (k : vStab v) ∈ (vStab u).subgroupOf (vStab v) := Subgroup.mem_subgroupOf.1 hk.1
  have h4 := ((vStab u).subgroupOf (vStab v)).mul_mem h3 h2
  rwa [mul_inv_cancel_left] at h4

theorem subgroupOf_eq_centralizer
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2)
    (hsu : (s : Shat) = clabelS u)
    (hidx : ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) ≤ 102)
    (hcu : clabelS v ∈ vStab u) :
    (vStab u).subgroupOf (vStab v) = Subgroup.centralizer {s} := by
  have hR := subgroupOf_le_centralizer s hsu
  refine le_antisymm hR ?_
  rw [← comap_sup_zpowers hsurj hker hs hs2]
  refine sup_le (comap_le_subgroupOf hsurj hker hs hidx hcu)
    ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 ?_))
  rw [hsu]
  exact clabelS_mem_vStab_self u

end Full

section Quot

variable {v u : CVert} {ρ : vStab v →* GStar}

theorem rho_mem_starSub {s : vStab v} (hs : ρ s = betaStarElt) {x : vStab v}
    (hx : x ∈ Subgroup.centralizer {s}) :
    ρ x ∈ CFSG.Monster.B.E6.FieldInvF4.starSub CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed := by
  have hxs : Commute x s := Subgroup.mem_centralizer_singleton_iff.1 hx
  have hc : Commute (ρ x) betaStarElt := hs ▸ hxs.map ρ
  rw [← CFSG.Monster.B.E6.FieldInvF4.centralizer_betaStarElt]
  exact Subgroup.mem_centralizer_singleton_iff.2 hc

@[expose] def pairToStar (ρ : vStab v →* GStar) {s : vStab v} (hs : ρ s = betaStarElt)
    (hsu : (s : Shat) = clabelS u) :
    (vStab v ⊓ vStab u : Subgroup Shat) →*
      CFSG.Monster.B.E6.FieldInvF4.starSub CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed :=
  (ρ.comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun x =>
    rho_mem_starSub hs (subgroupOf_le_centralizer s hsu (Subgroup.mem_subgroupOf.2 x.2.2))

@[expose] def pairHom (ρ : vStab v →* GStar) {s : vStab v} (hs : ρ s = betaStarElt)
    (hsu : (s : Shat) = clabelS u) : (vStab v ⊓ vStab u : Subgroup Shat) →* groupJ :=
  jSubEquiv.toMonoidHom.comp ((MonoidHom.fst _ _).comp
    ((CFSG.Monster.B.E6.FieldInvF4.prodStar
      CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed).symm.toMonoidHom.comp (pairToStar ρ hs hsu)))

theorem pairHom_apply {s : vStab v} (hs : ρ s = betaStarElt) (hsu : (s : Shat) = clabelS u)
    (x : (vStab v ⊓ vStab u : Subgroup Shat)) :
    pairHom ρ hs hsu x = jSubEquiv ((CFSG.Monster.B.E6.FieldInvF4.prodStar
      CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed).symm (pairToStar ρ hs hsu x)).1 := rfl

theorem pairHom_eq_one_iff {s : vStab v} (hs : ρ s = betaStarElt) (hsu : (s : Shat) = clabelS u)
    (x : (vStab v ⊓ vStab u : Subgroup Shat)) :
    pairHom ρ hs hsu x = 1 ↔ (ρ (Subgroup.inclusion inf_le_left x)).left = 1 := by
  rw [pairHom_apply, MulEquiv.map_eq_one_iff]
  exact Subtype.ext_iff

theorem eq_one_or_eq_beta_of_left_eq_one {γ : GStar} (h : γ.left = 1) :
    γ = 1 ∨ γ = betaStarElt := by
  rcases mem_betaGroup_iff.1 γ.right.2 with e | e
  · left
    exact SemidirectProduct.ext h (Subtype.ext e)
  · right
    exact SemidirectProduct.ext h (Subtype.ext e)

theorem prodStar_symm_fst
    (γ : CFSG.Monster.B.E6.FieldInvF4.starSub CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed) :
    ((CFSG.Monster.B.E6.FieldInvF4.prodStar CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed).symm γ).1 =
      ⟨(γ : GStar).left, γ.2⟩ := rfl

theorem pairHom_surjective (hsurj : Function.Surjective ρ) {s : vStab v}
    (hs : ρ s = betaStarElt) (hsu : (s : Shat) = clabelS u)
    (hNR : jStar.comap ρ ≤ (vStab u).subgroupOf (vStab v)) :
    Function.Surjective (pairHom ρ hs hsu) := by
  intro j
  refine (hsurj (SemidirectProduct.inl ((jSubEquiv.symm j : groupJ.subgroupOf stdGroup) :
    stdGroup))).elim (fun y hy => ?_)
  have hyN : y ∈ jStar.comap ρ := by
    rw [Subgroup.mem_comap, hy]
    exact ⟨_, (jSubEquiv.symm j).2, rfl⟩
  have hyu : (y : Shat) ∈ vStab u := Subgroup.mem_subgroupOf.1 (hNR hyN)
  refine ⟨⟨y, y.2, hyu⟩, ?_⟩
  rw [pairHom_apply, prodStar_symm_fst]
  have e : (⟨((pairToStar ρ hs hsu ⟨y, y.2, hyu⟩ :
      CFSG.Monster.B.E6.FieldInvF4.starSub CFSG.Monster.B.E6.FieldInvF4.groupJ_fixed) :
        GStar).left, (pairToStar ρ hs hsu ⟨y, y.2, hyu⟩).2⟩ : groupJ.subgroupOf stdGroup) =
      jSubEquiv.symm j := by
    apply Subtype.ext
    show (ρ y).left = _
    rw [hy, SemidirectProduct.left_inl]
  rw [e, MulEquiv.apply_symm_apply]

theorem clabelS_mem_closure_left (v u : CVert) :
    clabelS v ∈ Subgroup.closure ({clabelS v, clabelS u} : Set Shat) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem clabelS_mem_closure_right (v u : CVert) :
    clabelS u ∈ Subgroup.closure ({clabelS v, clabelS u} : Set Shat) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ker_pairHom
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) {s : vStab v}
    (hs : ρ s = betaStarElt) (hsu : (s : Shat) = clabelS u) (hcu : clabelS v ∈ vStab u) :
    (pairHom ρ hs hsu).ker =
      (Subgroup.closure {clabelS v, clabelS u}).subgroupOf (vStab v ⊓ vStab u) := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, pairHom_eq_one_iff] at hx
    rw [Subgroup.mem_subgroupOf]
    rcases eq_one_or_eq_beta_of_left_eq_one hx with h1 | h1
    · have h2 : Subgroup.inclusion inf_le_left x ∈ ρ.ker := h1
      rw [hker] at h2
      have h3 : ((Subgroup.inclusion inf_le_left x : vStab v) : Shat) ∈
          Subgroup.zpowers (clabelS v) := (mem_zpowers_subtype_iff _ _).1 h2
      exact (Subgroup.zpowers_le.2 (clabelS_mem_closure_left v u)) h3
    · have h2 : s⁻¹ * Subgroup.inclusion inf_le_left x ∈ ρ.ker := (ρ.eq_iff).1 (h1.trans hs.symm)
      rw [hker] at h2
      have h3 : ((s⁻¹ * Subgroup.inclusion inf_le_left x : vStab v) : Shat) ∈
          Subgroup.zpowers (clabelS v) := (mem_zpowers_subtype_iff _ _).1 h2
      have hsC : (s : Shat) ∈ Subgroup.closure ({clabelS v, clabelS u} : Set Shat) := by
        rw [hsu]
        exact clabelS_mem_closure_right v u
      have h4 : ((s * (s⁻¹ * Subgroup.inclusion inf_le_left x) : vStab v) : Shat) ∈
          Subgroup.closure ({clabelS v, clabelS u} : Set Shat) :=
        Subgroup.mul_mem _ hsC ((Subgroup.zpowers_le.2 (clabelS_mem_closure_left v u)) h3)
      have e : ((s * (s⁻¹ * Subgroup.inclusion inf_le_left x) : vStab v) : Shat) = (x : Shat) :=
        congrArg Subtype.val (mul_inv_cancel_left s (Subgroup.inclusion inf_le_left x))
      exact e ▸ h4
  · intro x hx
    have hx' : (x : Shat) ∈ Subgroup.closure ({clabelS v, clabelS u} : Set Shat) :=
      Subgroup.mem_subgroupOf.1 hx
    have hcR : clabelS v ∈ vStab v ⊓ vStab u :=
      Subgroup.mem_inf.2 ⟨clabelS_mem_vStab_self v, hcu⟩
    have hsR : clabelS u ∈ vStab v ⊓ vStab u :=
      Subgroup.mem_inf.2 ⟨hsu ▸ s.2, clabelS_mem_vStab_self u⟩
    have hck : (⟨clabelS v, hcR⟩ : (vStab v ⊓ vStab u : Subgroup Shat)) ∈
        (pairHom ρ hs hsu).ker := by
      refine (MonoidHom.mem_ker).2 ((pairHom_eq_one_iff hs hsu _).2 ?_)
      have h1 : Subgroup.inclusion inf_le_left
          (⟨clabelS v, hcR⟩ : (vStab v ⊓ vStab u : Subgroup Shat)) = cStab v := rfl
      have h2 : ρ (cStab v) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact Subgroup.mem_zpowers _
      rw [h1, h2]
      rfl
    have hsk : (⟨clabelS u, hsR⟩ : (vStab v ⊓ vStab u : Subgroup Shat)) ∈
        (pairHom ρ hs hsu).ker := by
      refine (MonoidHom.mem_ker).2 ((pairHom_eq_one_iff hs hsu _).2 ?_)
      have h1 : Subgroup.inclusion inf_le_left
          (⟨clabelS u, hsR⟩ : (vStab v ⊓ vStab u : Subgroup Shat)) = s := Subtype.ext hsu.symm
      rw [h1, hs]
      rfl
    have hle : Subgroup.closure ({clabelS v, clabelS u} : Set Shat) ≤
        (pairHom ρ hs hsu).ker.map (vStab v ⊓ vStab u).subtype := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_map.2 ⟨_, hck, rfl⟩
      · exact Subgroup.mem_map.2 ⟨_, hsk, rfl⟩
    refine (Subgroup.mem_map.1 (hle hx')).elim (fun k hk => ?_)
    have e : k = x := Subtype.ext hk.2
    rw [← e]
    exact hk.1

end Quot

theorem natCard_vStab_eq_mul
    (hP : DistThreePathInput) {v u : CVert}
    (hvu : u ∈ sphereDistThree v) :
    Nat.card (vStab v) =
      (sphereDistThree v).ncard * Nat.card (vStab v ⊓ vStab u : Subgroup Shat) := by
  have h := natCard_subgroup_eq_mul (vStab v) u
  have horb : {x | ∃ g ∈ vStab v, cvMul u g = x} = sphereDistThree v := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have h1 := sphereDistThree_cvMul hvu g
      rwa [mem_vStab.1 hg] at h1
    · intro hx
      refine (hP.1 v u x hvu hx).elim (fun g hg => ⟨g, hg.1, hg.2⟩)
  rw [horb] at h
  exact h

theorem native_distance_three_pair_is_full_local_centralizer
    (hL : DistThreeLabelsInput)
    (hO : DistThreeOuterInput) (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    ∃ s : vStab v, (s : Shat) = clabelS u ∧
      (vStab u).subgroupOf (vStab v) = Subgroup.centralizer {s} ∧
      (∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ρ s = betaStarElt →
          (vStab u).subgroupOf (vStab v) = jStar.comap ρ ⊔ Subgroup.zpowers s ∧
          jStar.comap ρ ⊓ Subgroup.zpowers s = ⊥ ∧ ∀ n ∈ jStar.comap ρ, Commute n s) ∧
      (∃ φ : (vStab v ⊓ vStab u : Subgroup Shat) →* groupJ, Function.Surjective φ ∧
        φ.ker = (Subgroup.closure {clabelS v, clabelS u}).subgroupOf (vStab v ⊓ vStab u)) ∧
      Nat.card (vStab v ⊓ vStab u : Subgroup Shat) = 13244506413465600 ∧
      (xSet v u).ncard = 3898440 ∧ (sphereDistThree v).ncard = 23113728 := by
  have hvu' : u ∈ sphereDistThree v := mem_sphereDistThree.2 hvu
  have hLvu := hL v u hvu
  have hsv : clabelS u ∈ vStab v := hLvu.1
  have hcu : clabelS v ∈ vStab u := hLvu.2.1
  have hex : ∃ s : vStab v, (s : Shat) = clabelS u := ⟨⟨clabelS u, hsv⟩, rfl⟩
  refine hex.elim (fun s hs => ?_)
  have hs2 := orderOf_sLabel s hs
  refine (exists_compat_beta hO hP hT hvu s hs).elim (fun ρ₀ h₀ => h₀.elim (fun iv₀ h₁ => ?_))
  have hk₀ := ker_eq_zpowers_cStab h₁.1.2.1
  have hC := natCard_centralizer_s h₁.1.1 hk₀ h₁.2 hs2
  have hidx := relIndex_le_102 hP hT hvu' s hs hC
  have hR' := subgroupOf_eq_centralizer h₁.1.1 hk₀ h₁.2 hs2 hs hidx hcu
  have hNR : jStar.comap ρ₀ ≤ (vStab u).subgroupOf (vStab v) := fun n hn =>
    hR'.ge (Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem h₁.1.1 hk₀ h₁.2 hn))
  have hRcard : Nat.card (vStab v ⊓ vStab u : Subgroup Shat) = 13244506413465600 :=
    (natCard_subgroupOf_vStab v u).symm.trans
      ((congrArg (fun H : Subgroup (vStab v) => Nat.card H) hR').trans hC)
  have hX := natCard_pairStab hP hvu'
  have hV := natCard_vStab_eq_mul hP hvu'
  rw [natCard_vStab_of_compat h₁.1.1 h₁.1.2.1, hRcard] at hV
  rw [hRcard] at hX
  refine ⟨s, hs, hR', fun ρ hsurj hker hρs => ?_, ⟨pairHom ρ₀ h₁.2 hs,
    pairHom_surjective h₁.1.1 h₁.2 hs hNR, ker_pairHom hk₀ h₁.2 hs hcu⟩, hRcard, by omega,
    by omega⟩
  have hk := ker_eq_zpowers_cStab hker
  exact ⟨hR'.trans (comap_sup_zpowers hsurj hk hρs hs2).symm, comap_inf_zpowers hρs hs2,
    fun n hn => commute_of_mem hsurj hk hρs hn⟩

end CFSG.Monster.B.TwoA.Amalgam
