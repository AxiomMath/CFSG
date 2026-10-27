module

public import CFSG.OddTranspositions.TheoremTwo.ImageS5

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ CFSG.GroupTheory

theorem eq_bot_of_normal_of_isSolvable_perm_five (N : Subgroup (Equiv.Perm (Fin 5)))
    [hN : N.Normal] (hs : Group.IsSolvable N) : N = ⊥ := by
  classical
  have hA : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hc1 : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 5) := by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap']
  have hc2 : Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4 ∈ alternatingGroup (Fin 5) := by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap']
  have hc3 : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 3 ∈ alternatingGroup (Fin 5) := by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap']
  let P : Subgroup (alternatingGroup (Fin 5)) := N.subgroupOf (alternatingGroup (Fin 5))
  have hP : P.Normal := hN.subgroupOf _
  rcases hA.eq_bot_or_eq_top_of_normal P with h | h
  · have hcomm : ∀ n ∈ N, ∀ a ∈ alternatingGroup (Fin 5), n * a = a * n := by
      intro n hn a ha
      have hcN : n * a * n⁻¹ * a⁻¹ ∈ N := by
        have := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) a)
        simpa [mul_assoc] using this
      have hcA : n * a * n⁻¹ * a⁻¹ ∈ alternatingGroup (Fin 5) :=
        (alternatingGroup (Fin 5)).mul_mem
          ((alternatingGroup.normal : (alternatingGroup (Fin 5)).Normal).conj_mem a ha n)
          ((alternatingGroup (Fin 5)).inv_mem ha)
      have hmem : (⟨_, hcA⟩ : alternatingGroup (Fin 5)) ∈ P := Subgroup.mem_subgroupOf.mpr hcN
      rw [h, Subgroup.mem_bot] at hmem
      have h1 : n * a * n⁻¹ * a⁻¹ = 1 := by
        simpa using congrArg (fun y : alternatingGroup (Fin 5) => (y : Equiv.Perm (Fin 5))) hmem
      have h2 : n * a * n⁻¹ = a := mul_inv_eq_one.mp h1
      calc n * a = n * a * n⁻¹ * n := by group
        _ = a * n := by rw [h2]
    have key : ∀ g : Equiv.Perm (Fin 5),
        g * (Equiv.swap 0 1 * Equiv.swap 1 2) = (Equiv.swap 0 1 * Equiv.swap 1 2) * g →
        g * (Equiv.swap 2 3 * Equiv.swap 3 4) = (Equiv.swap 2 3 * Equiv.swap 3 4) * g →
        g = 1 := by
      decide +kernel
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact key n (hcomm n hn _ hc1) (hcomm n hn _ hc2)
  · exfalso
    have hAN : alternatingGroup (Fin 5) ≤ N := by
      intro a ha
      have hmem : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ P := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hAs : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAN)
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable).mpr hAs
    have h3 := hcomm ⟨_, hc1⟩ ⟨_, hc3⟩
    have h4 := congrArg (fun y : alternatingGroup (Fin 5) => (y : Equiv.Perm (Fin 5))) h3
    simp only [Subgroup.coe_mul] at h4
    exact absurd h4 (by decide)

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem wCover_of_config (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R))
    (e' : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Equiv.Perm (Fin 5))
    (he' : e' '' imageClass hC = transpositions) :
    ∀ τ ∈ transpositions, ∃ (x : X) (hx : x ∈ W D u X R (u_mem_X_config hQ hKX)),
      e' (starImage hC (x : G)
        (W_subset_DalphaStar_config hC hQ htri hu hv hKX hR hPX x hx)) = τ := by
  classical
  obtain ⟨e, -, -, himg⟩ := W_eq_preimage_ten hC hQ htri hu hKX hPX
  obtain ⟨e₅, he₅⟩ := fixK_equiv_s5
  let Wset : Set X := W D u X R (u_mem_X_config hQ hKX)
  have hWD : ∀ x ∈ Wset, (x : G) ∈ DalphaStar D hC.alpha :=
    W_subset_DalphaStar_config hC hQ htri hu hv hKX hR hPX
  let Wsub : Subgroup G := Subgroup.closure ((Subtype.val : X → G) '' Wset)
  have hWX : Wsub ≤ X := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hWH : Wsub ≤ Halpha D hC.alpha := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (hWD x hx)
  let gen : Wset → Wsub := fun x => ⟨(x.1 : G), Subgroup.subset_closure ⟨x.1, x.2, rfl⟩⟩
  let f : Wsub →* PSigmaL225 :=
    e.toMonoidHom.comp ((QuotientGroup.mk' R).comp (Subgroup.inclusion hWX))
  have hf_gen : ∀ x : Wset, f (gen x) = e (QuotientGroup.mk' R x.1) := by
    intro x
    have hinc : Subgroup.inclusion hWX (gen x) = x.1 := Subtype.ext rfl
    simp [f, hinc]
  have himgW : ∀ x : Wset, e (QuotientGroup.mk' R x.1) ∈ Set.range y := by
    intro x
    rw [← himg]
    exact ⟨_, ⟨x.1, x.2, rfl⟩, rfl⟩
  have hsurjW : ∀ i, ∃ x : Wset, e (QuotientGroup.mk' R x.1) = y i := by
    intro i
    have hyi : y i ∈ e '' {z : X ⧸ R | ∃ y : X, y ∈ Wset ∧ QuotientGroup.mk' R y = z} := by
      rw [himg]
      exact Set.mem_range_self i
    obtain ⟨_, ⟨x, hx, rfl⟩, hz⟩ := hyi
    exact ⟨⟨x, hx⟩, hz⟩
  have hgen_top : Subgroup.closure (Set.range gen) = ⊤ := by
    have hpre : Wsub.subtype ⁻¹' ((Subtype.val : X → G) '' Wset) = Set.range gen := by
      ext q
      constructor
      · rintro ⟨x, hx, hxq⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
    have h := Subgroup.closure_preimage_eq_top (s := (Subtype.val : X → G) '' Wset)
    change Subgroup.closure (Wsub.subtype ⁻¹' ((Subtype.val : X → G) '' Wset)) = ⊤ at h
    rw [← hpre]
    exact h
  have hfr : ∀ q : Wsub, f q ∈ Yten := by
    intro q
    have hq : q ∈ Subgroup.closure (Set.range gen) := by
      rw [hgen_top]
      exact Subgroup.mem_top q
    induction hq using Subgroup.closure_induction with
    | mem p hp =>
        obtain ⟨x, rfl⟩ := hp
        rw [hf_gen]
        obtain ⟨i, hi⟩ := himgW x
        rw [← hi]
        exact Subgroup.subset_closure (Set.mem_range_self i)
    | one =>
        rw [map_one]
        exact Yten.one_mem
    | mul p q _ _ ihp ihq =>
        rw [map_mul]
        exact Yten.mul_mem ihp ihq
    | inv p _ ihp =>
        rw [map_inv]
        exact Yten.inv_mem ihp
  let φ : Wsub →* Yten := f.codRestrict Yten hfr
  have hφsurj : Function.Surjective φ := by
    have hle : Yten ≤ (φ.range).map Yten.subtype := by
      change Subgroup.closure (Set.range y) ≤ (φ.range).map Yten.subtype
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := hsurjW i
      refine Subgroup.mem_map.mpr ⟨φ (gen x), ⟨gen x, rfl⟩, ?_⟩
      change f (gen x) = y i
      rw [hf_gen, hx]
    have hEq : (φ.range).map Yten.subtype = Yten :=
      le_antisymm (by rintro _ ⟨t, -, rfl⟩; exact t.2) hle
    refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr fun t _ => ?_)
    have ht : (t : PSigmaL225) ∈ (φ.range).map Yten.subtype := by
      rw [hEq]
      exact t.2
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp ht
    have hst' : s = t := Subtype.ext hst
    exact hst' ▸ hs
  let ψ₁ : Wsub →* Equiv.Perm (Fin 5) := e₅.toMonoidHom.comp (leftHomYten.comp φ)
  have hψ₁surj : Function.Surjective ψ₁ :=
    e₅.surjective.comp (leftHomYten_surjective.comp hφsurj)
  have hψ₁gen : ∀ (x : Wset) (i : Fin 10), e (QuotientGroup.mk' R x.1) = y i →
      ψ₁ (gen x) = e₅ (leftY i) := by
    intro x i hi
    have hl : leftHomYten (φ (gen x)) = leftY i := by
      apply Subtype.ext
      change (f (gen x)).left = (y i).left
      rw [hf_gen, hi]
    change e₅ (leftHomYten (φ (gen x))) = e₅ (leftY i)
    rw [hl]
  let ψ₂ : Wsub →* Equiv.Perm (Fin 5) :=
    e'.toMonoidHom.comp
      ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp
        (Subgroup.inclusion hWH))
  have hψ₂gen : ∀ x : Wset, ψ₂ (gen x) = e' (starImage hC (x : G) (hWD x x.2)) :=
    fun x => rfl
  have hK2s : Group.IsSolvable ψ₂.ker := by
    have hmem : ∀ k : ψ₂.ker,
        Subgroup.inclusion hWH k.1 ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
      intro k
      have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have h1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
          (Subgroup.inclusion hWH k.1) = 1 := by
        have : e' (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
            (Subgroup.inclusion hWH k.1)) = 1 := hk
        simpa using this
      exact (QuotientGroup.eq_one_iff _).mp h1
    let g : ψ₂.ker →* CFSG.solvableRadical (Halpha D hC.alpha) :=
      { toFun := fun k => ⟨Subgroup.inclusion hWH k.1, hmem k⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro k₁ k₂ hk
      have h' := congrArg (fun t : CFSG.solvableRadical (Halpha D hC.alpha) => (t : G)) hk
      exact Subtype.ext (Subtype.ext h')
    have : Group.IsSolvable (CFSG.solvableRadical (Halpha D hC.alpha)) :=
      OddTransp.isSolvable_solvableRadical
    exact Group.isSolvable_of_isSolvable_injective hg
  have hle : ψ₂.ker ≤ ψ₁.ker := by
    have : ((ψ₂.ker).map ψ₁).Normal := Subgroup.Normal.map inferInstance ψ₁ hψ₁surj
    have hmaps : Group.IsSolvable ((ψ₂.ker).map ψ₁) :=
      Group.isSolvable_of_surjective (ψ₁.subgroupMap_surjective ψ₂.ker)
    have hbot := eq_bot_of_normal_of_isSolvable_perm_five _ hmaps
    intro k hk
    rw [MonoidHom.mem_ker]
    have hk' : ψ₁ k ∈ (ψ₂.ker).map ψ₁ := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hk'
    exact hk'
  have hc1 : Nat.card (Wsub ⧸ ψ₁.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ₁ hψ₁surj).toEquiv,
      Nat.card_perm, Nat.card_fin]
    rfl
  have hc2 : Nat.card (Wsub ⧸ ψ₂.ker) ≤ 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ₂).toEquiv]
    calc Nat.card ψ₂.range ≤ Nat.card (Equiv.Perm (Fin 5)) := Subgroup.card_le_card_group _
      _ = 120 := by rw [Nat.card_perm, Nat.card_fin]; rfl
  have hk : Nat.card ψ₂.ker ≤ Nat.card ψ₁.ker := Subgroup.card_le_of_le hle
  have hW1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ₁.ker
  have hW2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ₂.ker
  have hpos : 0 < Nat.card ψ₂.ker := Nat.card_pos
  have hkeq : Nat.card ψ₁.ker ≤ Nat.card ψ₂.ker := by nlinarith
  have hq2 : Nat.card (Wsub ⧸ ψ₂.ker) = 120 := by nlinarith
  have hker : ψ₁.ker = ψ₂.ker := (Subgroup.eq_of_le_of_card_ge hle hkeq).symm
  have hψ₂surj : Function.Surjective ψ₂ := by
    have hr : Nat.card ψ₂.range = Nat.card (Equiv.Perm (Fin 5)) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ₂).toEquiv, hq2,
        Nat.card_perm, Nat.card_fin]
      rfl
    exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ hr)
  let θ : Equiv.Perm (Fin 5) ≃* Equiv.Perm (Fin 5) :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ₁ hψ₁surj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ₂ hψ₂surj))
  have hθ : ∀ q : Wsub, θ (ψ₁ q) = ψ₂ q := by
    intro q
    have hs : (QuotientGroup.quotientKerEquivOfSurjective ψ₁ hψ₁surj).symm (ψ₁ q) =
        (q : Wsub ⧸ ψ₁.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change (QuotientGroup.quotientKerEquivOfSurjective ψ₂ hψ₂surj)
      ((QuotientGroup.quotientMulEquivOfEq hker)
        ((QuotientGroup.quotientKerEquivOfSurjective ψ₁ hψ₁surj).symm (ψ₁ q))) = ψ₂ q
    rw [hs]
    rfl
  have hT1 : ∀ τ ∈ transpositions, ∃ x : Wset, ψ₁ (gen x) = τ := by
    intro τ hτ
    rw [← he₅] at hτ
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hτ
    obtain ⟨x, hx⟩ := hsurjW i
    exact ⟨x, hψ₁gen x i hx⟩
  have hθT : θ '' transpositions ⊆ transpositions := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := hT1 t ht
    rw [hθ, hψ₂gen, ← he']
    exact ⟨_, ⟨⟨(x.1 : G), Subgroup.subset_closure (hWD x x.2)⟩, hWD x x.2, rfl⟩, rfl⟩
  have hθT' : θ '' transpositions = transpositions :=
    Set.eq_of_subset_of_ncard_le hθT (by rw [Set.ncard_image_of_injective _ θ.injective])
      (Set.toFinite _)
  intro τ hτ
  rw [← hθT'] at hτ
  obtain ⟨t, ht, rfl⟩ := hτ
  obtain ⟨x, rfl⟩ := hT1 t ht
  exact ⟨x.1, x.2, by rw [hθ, hψ₂gen]⟩

theorem DalphaStar_subset_X_of_prop47
    (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (hmin : SmallerTwoStar (Nat.card G))
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (hR : Group.IsSolvable R)
    (hKX : thirdK D z ≤ X) (hPX : O4PairData (X ⧸ R) (Omega D X R))
    (hfib : ∀ (e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      e '' imageClass hC = transpositions →
      ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
        (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
        e (starImage hC d hd) = e (starImage hC d' hd') → d = d') :
    DalphaStar D hC.alpha ⊆ (X : Set G) :=
  DalphaStar_subset_X_of_fibres hC hQ hmin htri hu hv hR hKX hPX
    (W_subset_DalphaStar_config hC hQ htri hu hv hKX hR hPX)
    (fun e he => wCover_of_config hC hQ htri hu hv hR hKX hPX e he) hfib

end CFSG.OddTranspositions

end
