module

public import CFSG.RankThree.CentralCover.ReflectionRadical
public import CFSG.Mathlib.LinearAlgebra.BilinForm.FiniteRadical
public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedReflection
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Reflection

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggResI_alpha_self_eq_two_of_A3
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 3 → V} {α : Fin 3 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3)) :
    ∀ j : Fin 3, α j (h j) = 2 := by
  intro j
  rw [hpair j j]
  have hdiag : CartanMatrix.A 3 j j = 2 := by
    fin_cases j <;> decide
  rw [hdiag]
  norm_num

theorem ggCharacter_apply_corootSpan
    {G : Type} [Group G] {Bs J : Subgroup G} {k : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin k → MulAut ↥Bs) (h : Fin k → V)
    (α : Fin k → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    {C : Type*} [Group C] (hCexp : ∀ c : C, c ^ 3 = 1)
    (χ : ↥Bs →* C)
    (hχinv : ∀ φ ∈ ggAutomizer J Bs, ∀ b : ↥Bs, χ (φ b) = χ b) :
    ∀ v ∈ Submodule.span (ZMod 3) (Set.range h),
      χ (Additive.toMul (ι.symm v)) = 1 := by
  classical
  have hrA : ∀ j : Fin k, r j ∈ ggAutomizer J Bs := by
    intro j
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  have hker : ∀ j : Fin k,
      ((Additive.toMul (ι.symm (h j)) : ↥Bs) : G) ∈ χ.ker.map Bs.subtype := by
    intro j
    let b : ↥Bs := Additive.toMul (ι.symm (h j))
    have hb1 : χ b = 1 := by
      have hinv : r j b = b⁻¹ := by
        rw [ggLin_inv_iff (p := 3) (ι := ι) (φ := r j) (b := b)]
        rw [hform j]
        have hb : ι (Additive.ofMul b) = h j := by simp [b]
        rw [hb, hα2 j]
        module
      have hχb : χ b = (χ b)⁻¹ := by
        calc
          χ b = χ (r j b) := (hχinv (r j) (hrA j) b).symm
          _ = χ (b⁻¹) := by rw [hinv]
          _ = (χ b)⁻¹ := map_inv χ b
      have hsq : χ b * χ b = 1 := eq_inv_iff_mul_eq_one.mp hχb
      have hcube : (χ b) ^ 3 = χ b := by
        rw [pow_succ, pow_two, hsq, one_mul]
      exact hcube.symm.trans (hCexp (χ b))
    exact Subgroup.mem_map.mpr ⟨b, MonoidHom.mem_ker.mpr hb1, rfl⟩
  have hle : ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h)) ≤
      χ.ker.map Bs.subtype :=
    ggSpanSub_le (p := 3) (X := χ.ker.map Bs.subtype) (hv := h) ι hker
  intro v hv
  have hvker : ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ χ.ker.map Bs.subtype :=
    hle ⟨v, hv, rfl⟩
  obtain ⟨b, hbker, hbeq⟩ := Subgroup.mem_map.mp hvker
  have hbs : (Additive.toMul (ι.symm v) : ↥Bs) = b := Subtype.ext hbeq.symm
  rw [hbs]
  exact MonoidHom.mem_ker.mp hbker

theorem ggGamma_injective_on_span_of_cartan {G : Type} [Group G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {n : Type} [Fintype n] {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) (r : n → MulAut ↥Bs)
    (h : n → V) (α : n → Module.Dual (ZMod 3) V) (C : Matrix n n ℤ)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hC : ∀ c : n → ZMod 3, (∀ j, ∑ k, (C j k : ZMod 3) * c k = 0) → c = 0)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r)) :
    Function.Injective (fun w : Submodule.span (ZMod 3) (Set.range h) =>
      ggGamma J hN (Additive.toMul (ι.symm w.1))) := by
  classical
  set W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h) with hW
  have hrA : ∀ j : n, r j ∈ ggAutomizer J Bs := by
    intro j
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  intro x y hxy
  let bx : ↥Bs := Additive.toMul (ι.symm x.1)
  let by' : ↥Bs := Additive.toMul (ι.symm y.1)
  let d : ↥Bs := bx * by'⁻¹
  have hγ : ggGamma J hN bx = ggGamma J hN by' := hxy
  have hγd : ggGamma J hN d = 1 := by
    have hd' : d = bx * by'⁻¹ := rfl
    rw [hd', map_mul, map_inv]
    show ggGamma J hN bx * (ggGamma J hN by')⁻¹ = 1
    rw [hγ, mul_inv_cancel]
  have hdcent : (d : G) ∈ Subgroup.centralizer (J : Set G) :=
    (ggGamma_eq_one_iff J hN d).mp hγd
  have hfixd : ∀ j : n, r j d = d := by
    intro j
    obtain ⟨g, hgJ, _hgN, hg⟩ := mem_ggAutomizer_iff.mp (hrA j)
    apply Subtype.ext
    rw [hg d]
    have hcomm : (g : G) * (d : G) = (d : G) * (g : G) :=
      (Subgroup.mem_centralizer_iff.mp hdcent) (g : G) hgJ
    rw [hcomm]
    group
  have hfixlin : ∀ j : n,
      ggLin (p := 3) ι (r j) (ι (Additive.ofMul d)) = ι (Additive.ofMul d) := by
    intro j
    rw [ggLin_apply_ofMul, hfixd j]
  have hαd : ∀ j : n, α j (ι (Additive.ofMul d)) = 0 := by
    intro j
    exact ggResI_alpha_eq_zero (p := 3) (by decide) (hform j) (hα2 j) (hfixlin j)
  have hxyvec : ι (Additive.ofMul d) = x.1 - y.1 := by
    dsimp only [d, bx, by']
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_toMul, ofMul_toMul,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    abel
  have hvecW : x.1 - y.1 ∈ W := Submodule.sub_mem W x.2 y.2
  have hvec : x.1 - y.1 ∈ Submodule.span (ZMod 3) (Set.range h) := hW ▸ hvecW
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3) (v := h)).mp hvec
  have hα0 : ∀ j : n, α j (x.1 - y.1) = 0 := by
    intro j
    rw [← hxyvec]
    exact hαd j
  have hker : ∀ j : n, ∑ k, (C j k : ZMod 3) * c k = 0 := by
    intro j
    calc
      ∑ k, (C j k : ZMod 3) * c k = ∑ k, c k * α j (h k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hpair j k]
        ring
      _ = α j (∑ k, c k • h k) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_smul, smul_eq_mul]
      _ = α j (x.1 - y.1) := by rw [hc]
      _ = 0 := hα0 j
  have hc0 : c = 0 := hC c hker
  have hxy0 : x.1 - y.1 = 0 := by
    rw [← hc, hc0]
    simp
  exact Subtype.ext (sub_eq_zero.mp hxy0)

namespace GGResLineJDatum

theorem coroot_span_subgroup_properties_of_cartan
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} {k : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (ι : Additive ↥Bs ≃+ V) (r : Fin k → MulAut ↥Bs) (h : Fin k → V)
    (α : Fin k → Module.Dual (ZMod 3) V) (C : Matrix (Fin k) (Fin k) ℤ)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hC : ∀ c : Fin k → ZMod 3, (∀ j, ∑ l, (C j l : ZMod 3) * c l = 0) → c = 0)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (W : Submodule (ZMod 3) V) (hW : W = Submodule.span (ZMod 3) (Set.range h)) :
    ggSpanSub ι W ≤ Bs ⊓ J ∧ IsElemAbelian 3 (ggSpanSub ι W) ∧
      Nat.card (ggSpanSub ι W) = 3 ^ k ∧
      ggSpanSub ι W ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  classical
  rw [hW]
  have hg := ggGamma_injective_on_span_of_cartan (n := Fin k) (C := C)
    hN ι r h α hform hα2 hpair hC hgen
  have hrA : ∀ j : Fin k, r j ∈ ggAutomizer J Bs := by
    intro j
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  have hmem : ∀ j : Fin k, ((Additive.toMul (ι.symm (h j)) : ↥Bs) : G) ∈ J := by
    intro j
    exact ggCoroot_mem (p := 3) (by decide) hN ι (hform j) (hα2 j) (hrA j)
  have hE : ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h)) ≤ Bs ⊓ J :=
    le_inf (ggSpanSub_le_bs ι _) (ggSpanSub_le ι hmem)
  have hEelem : IsElemAbelian 3 (ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h))) :=
    isElemAbelian_ggSpanSub ι _
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hcardW : Nat.card (Submodule.span (ZMod 3) (Set.range h)) = 3 ^ k := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 (Submodule.span (ZMod 3) (Set.range h)),
      finrank_span_eq_card hind, Fintype.card_fin]
  have hEcard : Nat.card (ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h))) = 3 ^ k := by
    rw [card_ggSpanSub, hcardW]
  have hEbot : ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h)) ⊓
      Subgroup.centralizer (J : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro g ⟨hgE, hgC⟩
    obtain ⟨v, hvW, hgv⟩ := mem_ggSpanSub.mp hgE
    have hγ1 : ggGamma J hN (Additive.toMul (ι.symm v)) = 1 := by
      rw [ggGamma_eq_one_iff J hN]
      rwa [hgv]
    have hw0 : (⟨v, hvW⟩ : Submodule.span (ZMod 3) (Set.range h)) = 0 := by
      apply hg
      simpa using hγ1
    have hv0 : v = 0 := congrArg Subtype.val hw0
    refine Subgroup.mem_bot.mpr ?_
    rw [← hgv, hv0]
    simp
  exact ⟨hE, hEelem, hEcard, hEbot⟩

theorem coroot_span_subgroup_properties_of_A3
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (W : Submodule (ZMod 3) V) (hW : W = Submodule.span (ZMod 3) (Set.range h)) :
    ggSpanSub ι W ≤ Bs ⊓ J ∧ IsElemAbelian 3 (ggSpanSub ι W) ∧
      Nat.card (ggSpanSub ι W) = 27 ∧
      ggSpanSub ι W ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := ggResI_alpha_self_eq_two_of_A3 hpair
  have hC : ∀ c : Fin 3 → ZMod 3,
      (∀ j, ∑ l, (CartanMatrix.A 3 j l : ZMod 3) * c l = 0) → c = 0 :=
    ggCartanAInd_ker_zero (p := 3) (N := 3) (by norm_num)
  have hprops := coroot_span_subgroup_properties_of_cartan (k := 3) hN ι r h α
    (CartanMatrix.A 3) hform hα2 hpair hind hC hgen W hW
  refine ⟨hprops.1, hprops.2.1, ?_, hprops.2.2.2⟩
  simpa using hprops.2.2.1

theorem exists_coroot_subgroup_of_A3 {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ E : Subgroup G, E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  have hpairA : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := ggResI_alpha_self_eq_two_of_A3 hpairA
  have hC : ∀ c : Fin 3 → ZMod 3,
      (∀ j, ∑ k, (CartanMatrix.A 3 j k : ZMod 3) * c k = 0) → c = 0 :=
    ggCartanAInd_ker_zero (p := 3) (N := 3) (by norm_num)
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hprops := coroot_span_subgroup_properties_of_cartan (k := 3) (hN := hN) ι r h α
    (CartanMatrix.A 3) hform hα2 hpairA hind hC hgen W rfl
  refine ⟨ggSpanSub ι W, hprops.1, hprops.2.1, ?_, hprops.2.2.2⟩
  rw [hprops.2.2.1]
  norm_num

theorem exists_coroot_subgroup_of_A3_character {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ E : Subgroup G, E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ ∧
      (∀ (C : Type*) [Group C], (∀ c : C, c ^ 3 = 1) →
        ∀ (χ : Bs →* C),
          (∀ φ ∈ ggAutomizer J Bs, ∀ b : Bs, χ (φ b) = χ b) →
          ∀ e (_heE : e ∈ E) (he : (e : G) ∈ Bs), χ ⟨e, he⟩ = 1) := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  have hpairA : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := ggResI_alpha_self_eq_two_of_A3 hpairA
  have hC : ∀ c : Fin 3 → ZMod 3,
      (∀ j, ∑ k, (CartanMatrix.A 3 j k : ZMod 3) * c k = 0) → c = 0 :=
    ggCartanAInd_ker_zero (p := 3) (N := 3) (by norm_num)
  let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hprops := coroot_span_subgroup_properties_of_cartan (k := 3) (hN := hN) ι r h α
    (CartanMatrix.A 3) hform hα2 hpairA hind hC hgen W rfl
  refine ⟨ggSpanSub ι W, hprops.1, hprops.2.1, ?_, hprops.2.2.2, ?_⟩
  · rw [hprops.2.2.1]
    norm_num
  · intro C _ hCexp χ hχinv e heE he
    obtain ⟨v, hvW, hve⟩ := mem_ggSpanSub.mp heE
    have hrep : χ (Additive.toMul (ι.symm v)) = 1 :=
      ggCharacter_apply_corootSpan ι r h α hform hα2 hgen hCexp χ hχinv v hvW
    have hsub : (⟨e, he⟩ : ↥Bs) = Additive.toMul (ι.symm v) := Subtype.ext hve.symm
    rw [hsub]
    exact hrep

theorem exists_coroot_quotient_of_A3 {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ E : Subgroup (J ⧸ Subgroup.center J), IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  obtain ⟨E, hE, hEelem, hEcard, hEbot⟩ := exists_coroot_subgroup_of_A3 hN hD
  have hEJ : E ≤ J := hE.trans inf_le_right
  let H : Subgroup J := E.subgroupOf J
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let E' : Subgroup (J ⧸ Subgroup.center J) := H.map π
  have hE' : IsElemAbelian 3 E' := (hEelem.subgroupOf J).map π
  refine ⟨E', hE', ?_⟩
  let g : ↥H → ↥E' := fun x => ⟨π x, ⟨x, x.2, rfl⟩⟩
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxH, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxH⟩, Subtype.ext hxy⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    have hq : π (x : J) = π (y : J) := congrArg Subtype.val hxy
    have hz : (x : J) / (y : J) ∈ Subgroup.center J :=
      (QuotientGroup.eq_iff_div_mem).mp hq
    have hxE : ((x : J) : G) ∈ E := Subgroup.mem_subgroupOf.mp x.2
    have hyE : ((y : J) : G) ∈ E := Subgroup.mem_subgroupOf.mp y.2
    have hzE : (((x : J) / (y : J) : J) : G) ∈ E := by
      rw [Subgroup.coe_div]
      exact E.div_mem hxE hyE
    have hzC : (((x : J) / (y : J) : J) : G) ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hcz := Subgroup.mem_center_iff.mp hz ⟨j, hj⟩
      simpa only [Subgroup.coe_mul] using congrArg (fun t : J => (t : G)) hcz
    have hmem : (((x : J) / (y : J) : J) : G) ∈
        E ⊓ Subgroup.centralizer (J : Set G) := ⟨hzE, hzC⟩
    rw [hEbot, Subgroup.mem_bot] at hmem
    have hdiv : (x : J) / (y : J) = 1 := Subtype.ext hmem
    have hxyJ : (x : J) = (y : J) := by
      calc (x : J) = (x : J) / (y : J) * (y : J) := by rw [div_mul_cancel]
        _ = (y : J) := by rw [hdiv, one_mul]
    exact Subtype.ext hxyJ
  have hcardg : Nat.card E' = Nat.card H :=
    (Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm
  have hcardH : Nat.card H = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  calc Nat.card E' = Nat.card H := hcardg
    _ = Nat.card E := hcardH
    _ = 27 := hEcard

theorem card_le_card_range_ggGamma_of_le_of_inf_eq_bot
    {G : Type} [Group G] [Finite G] {Bs J E : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hEBs : E ≤ Bs)
    (hEbot : E ⊓ Subgroup.centralizer (J : Set G) = ⊥) :
    Nat.card E ≤ Nat.card (ggGamma J hN).range := by
  classical
  let f : E → (ggGamma J hN).range := fun e =>
    ⟨ggGamma J hN ⟨e.1, hEBs e.2⟩, ⟨⟨e.1, hEBs e.2⟩, rfl⟩⟩
  have hf : Function.Injective f := by
    intro e1 e2 he
    have hγ : ggGamma J hN ⟨e1.1, hEBs e1.2⟩ =
        ggGamma J hN ⟨e2.1, hEBs e2.2⟩ := congrArg Subtype.val he
    have hdγ : ggGamma J hN ⟨(e1 * e2⁻¹).1, hEBs (e1 * e2⁻¹).2⟩ = 1 := by
      have hmul : (⟨(e1 * e2⁻¹).1, hEBs (e1 * e2⁻¹).2⟩ : ↥Bs) =
          ⟨e1.1, hEBs e1.2⟩ * ⟨e2.1, hEBs e2.2⟩⁻¹ := Subtype.ext (by simp)
      rw [hmul, map_mul, map_inv, hγ, mul_inv_cancel]
    have hdcent : ((e1 * e2⁻¹).1 : G) ∈ Subgroup.centralizer (J : Set G) :=
      (ggGamma_eq_one_iff J hN ⟨(e1 * e2⁻¹).1, hEBs (e1 * e2⁻¹).2⟩).mp hdγ
    have hmem : (e1 * e2⁻¹).1 ∈ E ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨(e1 * e2⁻¹).2, hdcent⟩
    have h1 : (e1 * e2⁻¹).1 = 1 := by
      have hbot := hmem
      rw [hEbot, Subgroup.mem_bot] at hbot
      exact hbot
    have hprod : e1 * e2⁻¹ = 1 := Subtype.ext h1
    calc e1 = e1 * e2⁻¹ * e2 := by group
      _ = e2 := by rw [hprod, one_mul]
  exact Nat.card_le_card_of_injective f hf

theorem cube_le_card_gamma_of_A3 {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hD : GGResLineJDatum 3 Bs J .A3) :
    3 ^ 3 ≤ Nat.card (ggGamma J hN).range := by
  obtain ⟨E, hE, _hEelem, hEcard, hEbot⟩ := exists_coroot_subgroup_of_A3 hN hD
  have hEBs : E ≤ Bs := hE.trans inf_le_left
  calc 3 ^ 3 = Nat.card E := hEcard.symm
    _ ≤ Nat.card (ggGamma J hN).range :=
        card_le_card_range_ggGamma_of_le_of_inf_eq_bot hN hEBs hEbot

theorem coroot_span_le_ker_of_diag_two
    {G : Type} [Group G] {Bs J : Subgroup G} {k : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin k → MulAut ↥Bs) (h : Fin k → V)
    (α : Fin k → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] W) (hbalt : b.IsAlt)
    (hinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v,
      b (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = b u v) :
    (∀ j, b (h j) = 0) ∧
      Submodule.span (ZMod 3) (Set.range h) ≤ b.ker ∧
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = k := by
  have hmem : ∀ j : Fin k, b (h j) = 0 := by
    intro j
    have hrA : r j ∈ ggAutomizer J Bs := by
      rw [hgen]
      exact Subgroup.subset_closure (Set.mem_range_self j)
    have hρ : ∀ u v, b (u - α j u • h j) (v - α j v • h j) = b u v := by
      intro u v
      simpa only [hform j u, hform j v] using hinv (r j) hrA u v
    exact LinearMap.BilinMap.apply_left_eq_zero_of_preReflection b hbalt (by decide)
      (h j) (α j) (hα2 j) hρ
  refine ⟨hmem, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro v ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (hmem j)
  · rw [finrank_span_eq_card hind, Fintype.card_fin]

theorem coroot_span_le_ker_of_A3
    {G : Type} [Group G] {Bs J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] W) (hbalt : b.IsAlt)
    (hinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v,
      b (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = b u v) :
    (∀ j, b (h j) = 0) ∧
      Submodule.span (ZMod 3) (Set.range h) ≤ b.ker ∧
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 3 := by
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
    intro j
    rw [hpair j j]
    have hdiag : CartanMatrix.A 3 j j = 2 := by
      fin_cases j <;> decide
    rw [hdiag]
    norm_num
  exact coroot_span_le_ker_of_diag_two ι r h α hform hα2 hind hgen b hbalt hinv

theorem exists_coroot_span_le_ker_of_A3
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hD : GGResLineJDatum 3 Bs J .A3)
    {W : Type} [AddCommGroup W] [Module (ZMod 3) W] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
      (α : Fin 3 → Module.Dual (ZMod 3) V),
      (∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j) ∧
        (∀ j, GGIsReflection 3 (r j)) ∧
        (∀ i j, α i (h j) = (GGResLineJType.cartan .A3 i j : ZMod 3)) ∧
        LinearIndependent (ZMod 3) h ∧
        ggAutomizer J Bs = Subgroup.closure (Set.range r) ∧
        ∀ (b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] W), b.IsAlt →
          (∀ φ ∈ ggAutomizer J Bs, ∀ u v,
            b (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = b u v) →
          (∀ j, b (h j) = 0) ∧
            Submodule.span (ZMod 3) (Set.range h) ≤ b.ker ∧
            Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 3 := by
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  let : AddCommGroup V := instA
  let : Module (ZMod 3) V := instM
  have hpairA : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  exact ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen,
    fun b hbalt hinv => coroot_span_le_ker_of_A3 ι r h α hform hpairA hind hgen b hbalt hinv⟩

theorem card_ker_of_A3
    {G : Type} [Group G] {Bs J : Subgroup G} [Finite Bs]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] W) (hbalt : b.IsAlt)
    (hinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v,
      b (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = b u v) :
    27 ≤ Nat.card b.ker := by
  classical
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  obtain ⟨hmem, hspan, hfin⟩ :=
    coroot_span_le_ker_of_A3 ι r h α hform hpair hind hgen b hbalt hinv
  have : Finite (Submodule.span (ZMod 3) (Set.range h)) := Subtype.finite
  have : Finite b.ker := Subtype.finite
  have hcard : Nat.card (Submodule.span (ZMod 3) (Set.range h)) = 27 := by
    rw [← FiniteField.pow_finrank_eq_natCard 3
      (Submodule.span (ZMod 3) (Set.range h)), hfin]
    norm_num
  have hle : Nat.card (Submodule.span (ZMod 3) (Set.range h)) ≤ Nat.card b.ker :=
    Nat.card_le_card_of_injective
      (fun x : Submodule.span (ZMod 3) (Set.range h) => (⟨x.1, hspan x.2⟩ : b.ker))
      (fun x y hxy => Subtype.ext (congrArg (fun z : b.ker => z.1) hxy))
  rw [hcard] at hle
  exact hle

end GGResLineJDatum

theorem GGResHyp.exists_coroot_subgroup_of_A3 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ E : Subgroup G, E ≤ Bs ⊓ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E ⊓ Subgroup.centralizer (J : Set G) = ⊥ :=
  GGResLineJDatum.exists_coroot_subgroup_of_A3 (GGResHyp.Bs_le_normalizer_J hH) hD

theorem GGResHyp.exists_coroot_quotient_of_A3 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3) :
    ∃ E : Subgroup (J ⧸ Subgroup.center J), IsElemAbelian 3 E ∧ Nat.card E = 27 :=
  GGResLineJDatum.exists_coroot_quotient_of_A3 (GGResHyp.Bs_le_normalizer_J hH) hD

theorem GGResHyp.cube_le_card_gamma_of_A3 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3) :
    3 ^ 3 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range :=
  GGResLineJDatum.cube_le_card_gamma_of_A3 (GGResHyp.Bs_le_normalizer_J hH) hD

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.RankThree.CentralCover
open CFSG.RankThree.Classical2
open CFSG.RankThree.GroupTheory
open scoped IsMulCommutative

attribute [local instance] kernelOmega_isElementaryAbelian

theorem ker_zero_of_det_two {k : ℕ} {C : Matrix (Fin k) (Fin k) ℤ}
    (hdet : C.det = 2) :
    ∀ c : Fin k → ZMod 3, (∀ j, ∑ l, (C j l : ZMod 3) * c l = 0) → c = 0 := by
  have hdet3 : (RingHom.mapMatrix (Int.castRingHom (ZMod 3)) C).det ≠ 0 := by
    rw [← RingHom.map_det, hdet]
    decide
  intro c hc
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet3
  ext j
  simpa [RingHom.mapMatrix, Matrix.mulVec, dotProduct] using hc j


theorem pair_zero_on_coroot_span
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {k : ℕ}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (ι : Additive ↥Bs ≃+ V) (r : Fin k → MulAut ↥Bs) (h : Fin k → V)
    (α : Fin k → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    {Y H : Type} [Group Y] [Group H] {π : Y →* H}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    {ρ : ↥Bs →* H}
    (hρker : ∀ b : ↥Bs, ρ b = 1 ↔ ggGamma J hN b = 1)
    (hconj : ∀ φ ∈ ggAutomizer J Bs, ∃ t : H, ∀ b : ↥Bs,
      ρ (φ b) = t * ρ b * t⁻¹)
    (W : Submodule (ZMod 3) V) (hW : W = Submodule.span (ZMod 3) (Set.range h))
    (hWrange : ∀ y ∈ ρ.range, ∃ w : W,
      ρ (Additive.toMul (ι.symm (w : V))) = y) :
    ∀ x y : Y, π x ∈ ρ.range → π y ∈ ρ.range → x * y = y * x := by
  classical
  haveI : Finite (Additive ↥Bs) := Subtype.finite
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let eBs : Multiplicative V ≃* ↥Bs := AddEquiv.toMultiplicativeLeft ι.symm
  let e : Multiplicative V →* H := ρ.comp eBs.toMonoidHom
  let b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (kernelOmega hker 3) :=
    liftCommBilinear (p := 3) hπ hker e
  have hrange : e.range = ρ.range := by
    change (ρ.comp eBs.toMonoidHom).range = ρ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eBs.surjective, Subgroup.map_top]
  have hρcomm : ∀ a b' : ↥Bs, Commute (ρ a) (ρ b') := by
    intro a b'
    have ha : ρ a ∈ e.range := by rw [hrange]; exact ⟨a, rfl⟩
    have hb : ρ b' ∈ e.range := by rw [hrange]; exact ⟨b', rfl⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hb
    change ρ a * ρ b' = ρ b' * ρ a
    calc ρ a * ρ b' = e x * e y := by rw [← hx, ← hy]
      _ = e (x * y) := (map_mul e x y).symm
      _ = e (y * x) := by rw [mul_comm x y]
      _ = e y * e x := map_mul e y x
      _ = ρ b' * ρ a := by rw [hy, hx]
  have he_ofMul : ∀ z : ↥Bs, e (Multiplicative.ofAdd (ι (Additive.ofMul z))) = ρ z := by
    intro z
    change ρ (eBs (Multiplicative.ofAdd (ι (Additive.ofMul z)))) = ρ z
    congr 1
    change eBs (Multiplicative.ofAdd (ι (Additive.ofMul z))) = z
    simp [eBs]
  have hinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v,
      b (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = b u v := by
    intro φ hφ u v
    obtain ⟨g, hg⟩ := hconj φ hφ
    let c : ↥Bs := Additive.toMul (ι.symm u)
    let d : ↥Bs := Additive.toMul (ι.symm v)
    have hu : ι (Additive.ofMul c) = u := by simp [c]
    have hv : ι (Additive.ofMul d) = v := by simp [d]
    have hgu : ggLin (p := 3) ι φ u = ι (Additive.ofMul (φ c)) := by
      rw [← hu, ggLin_apply_ofMul]
    have hgv : ggLin (p := 3) ι φ v = ι (Additive.ofMul (φ d)) := by
      rw [← hv, ggLin_apply_ofMul]
    rw [hgu, hgv, ← hu, ← hv]
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((Additive.toMul (liftCommBilinear (p := 3) hπ hker e
        (ι (Additive.ofMul (φ c))) (ι (Additive.ofMul (φ d)))) :
          kernelOmega hker 3) : Y) =
      ((Additive.toMul (liftCommBilinear (p := 3) hπ hker e
        (ι (Additive.ofMul c)) (ι (Additive.ofMul d))) :
          kernelOmega hker 3) : Y)
    rw [liftCommBilinear_apply, liftCommBilinear_apply]
    rw [he_ofMul, he_ofMul, he_ofMul, he_ofMul]
    rw [hg c, hg d]
    exact liftComm_conj hπ hker (hρcomm c d) g
  have hbalt : b.IsAlt := by
    change (liftCommBilinear (p := 3) hπ hker e).IsAlt
    exact liftCommBilinear_isAlt (p := 3) hπ hker e
  have hcoroot := GGResLineJDatum.coroot_span_le_ker_of_diag_two ι r h α hform hα2 hind hgen
    b hbalt hinv
  obtain ⟨_hvan, _hspan, _hfinrank⟩ := hcoroot
  have hspanW : W ≤ b.ker := by
    rw [hW]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (_hvan j)
  have hUcomm : ∀ s ∈ e.range, ∀ t ∈ e.range, liftComm π hπ s t = 1 := by
    intro s hs t ht
    have hsρ : s ∈ ρ.range := by rwa [← hrange]
    have htρ : t ∈ ρ.range := by rwa [← hrange]
    obtain ⟨w, hw⟩ := hWrange s hsρ
    obtain ⟨w', hw'⟩ := hWrange t htρ
    have hes : e (Multiplicative.ofAdd (w : V)) = s := by
      simpa [e, eBs] using hw
    have het : e (Multiplicative.ofAdd (w' : V)) = t := by
      simpa [e, eBs] using hw'
    have hb0 : b (w : V) (w' : V) = 0 := by
      have h : b (w : V) = 0 := LinearMap.mem_ker.mp (hspanW w.2)
      exact congrArg (fun f => f (w' : V)) h
    have happ := liftCommBilinear_apply (p := 3) hπ hker e (w : V) (w' : V)
    rw [show liftCommBilinear (p := 3) hπ hker e = b from rfl, hb0] at happ
    rw [hes, het] at happ
    simpa using happ.symm
  intro x y hx hy
  exact mul_comm_of_liftComm_eq_one hπ hker hUcomm
    (by rw [Subgroup.mem_comap, hrange]; exact hx)
    (by rw [Subgroup.mem_comap, hrange]; exact hy)


theorem pair_zero_of_rank_three_coroot
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (ι : Additive ↥Bs ≃+ V) (r : Fin 3 → MulAut ↥Bs) (h : Fin 3 → V)
    (α : Fin 3 → Module.Dual (ZMod 3) V)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hα2 : ∀ j, α j (h j) = 2)
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (hEcard : Nat.card (ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h))) = 27)
    (hEbot : ggSpanSub ι (Submodule.span (ZMod 3) (Set.range h)) ⊓
      Subgroup.centralizer (J : Set G) = ⊥)
    {Y H : Type} [Group Y] [Group H] {π : Y →* H}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    {ρ : ↥Bs →* H}
    (hρker : ∀ b : ↥Bs, ρ b = 1 ↔ ggGamma J hN b = 1)
    (hρcard : Nat.card ρ.range ≤ 81)
    (hconj : ∀ φ ∈ ggAutomizer J Bs, ∃ t : H, ∀ b : ↥Bs,
      ρ (φ b) = t * ρ b * t⁻¹) :
    ∀ x y : Y, π x ∈ ρ.range → π y ∈ ρ.range → x * y = y * x := by
  classical
  haveI : Finite (Additive ↥Bs) := Subtype.finite
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let eBs : Multiplicative V ≃* ↥Bs := AddEquiv.toMultiplicativeLeft ι.symm
  let e : Multiplicative V →* H := ρ.comp eBs.toMonoidHom
  let b : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (kernelOmega hker 3) :=
    liftCommBilinear (p := 3) hπ hker e
  have hrange : e.range = ρ.range := by
    change (ρ.comp eBs.toMonoidHom).range = ρ.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eBs.surjective, Subgroup.map_top]
  have hρcomm : ∀ a b' : ↥Bs, Commute (ρ a) (ρ b') := by
    intro a b'
    have ha : ρ a ∈ e.range := by rw [hrange]; exact ⟨a, rfl⟩
    have hb : ρ b' ∈ e.range := by rw [hrange]; exact ⟨b', rfl⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hb
    change ρ a * ρ b' = ρ b' * ρ a
    calc ρ a * ρ b' = e x * e y := by rw [← hx, ← hy]
      _ = e (x * y) := (map_mul e x y).symm
      _ = e (y * x) := by rw [mul_comm x y]
      _ = e y * e x := map_mul e y x
      _ = ρ b' * ρ a := by rw [hy, hx]
  have he_ofMul : ∀ z : ↥Bs, e (Multiplicative.ofAdd (ι (Additive.ofMul z))) = ρ z := by
    intro z
    change ρ (eBs (Multiplicative.ofAdd (ι (Additive.ofMul z)))) = ρ z
    congr 1
    change eBs (Multiplicative.ofAdd (ι (Additive.ofMul z))) = z
    simp [eBs]
  have hinv : ∀ φ ∈ ggAutomizer J Bs, ∀ u v,
      b (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ v) = b u v := by
    intro φ hφ u v
    obtain ⟨g, hg⟩ := hconj φ hφ
    let c : ↥Bs := Additive.toMul (ι.symm u)
    let d : ↥Bs := Additive.toMul (ι.symm v)
    have hu : ι (Additive.ofMul c) = u := by simp [c]
    have hv : ι (Additive.ofMul d) = v := by simp [d]
    have hgu : ggLin (p := 3) ι φ u = ι (Additive.ofMul (φ c)) := by
      rw [← hu, ggLin_apply_ofMul]
    have hgv : ggLin (p := 3) ι φ v = ι (Additive.ofMul (φ d)) := by
      rw [← hv, ggLin_apply_ofMul]
    rw [hgu, hgv, ← hu, ← hv]
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((Additive.toMul (liftCommBilinear (p := 3) hπ hker e
        (ι (Additive.ofMul (φ c))) (ι (Additive.ofMul (φ d)))) :
          kernelOmega hker 3) : Y) =
      ((Additive.toMul (liftCommBilinear (p := 3) hπ hker e
        (ι (Additive.ofMul c)) (ι (Additive.ofMul d))) :
          kernelOmega hker 3) : Y)
    rw [liftCommBilinear_apply, liftCommBilinear_apply]
    rw [he_ofMul, he_ofMul, he_ofMul, he_ofMul]
    rw [hg c, hg d]
    exact liftComm_conj hπ hker (hρcomm c d) g
  have hbalt : b.IsAlt := by
    change (liftCommBilinear (p := 3) hπ hker e).IsAlt
    exact liftCommBilinear_isAlt (p := 3) hπ hker e
  have hcoroot := GGResLineJDatum.coroot_span_le_ker_of_diag_two ι r h α hform hα2 hind hgen
    b hbalt hinv
  obtain ⟨_hvan, _hspan, _hfinrank⟩ := hcoroot
  set W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h) with hW
  have hEcardW : Nat.card (ggSpanSub ι W) = 27 := by
    rw [hW]
    exact hEcard
  have hEbotW : ggSpanSub ι W ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
    rw [hW]
    exact hEbot
  let K : AddSubgroup V := e.ker.toAddSubgroup'
  have hspanW : W ≤ b.ker := by
    rw [hW]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (_hvan j)
  have hKS : K ⊓ W.toAddSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huK, huS⟩ := AddSubgroup.mem_inf.mp hu
    have huW : u ∈ W := by simpa using huS
    have heu : e (Multiplicative.ofAdd u) = 1 :=
      MonoidHom.mem_ker.mp (by simpa [K] using huK)
    have hρu : ρ (eBs (Multiplicative.ofAdd u)) = 1 := heu
    have heBs : eBs (Multiplicative.ofAdd u) = Additive.toMul (ι.symm u) := rfl
    have hγu : ggGamma J hN (Additive.toMul (ι.symm u)) = 1 := by
      rw [← heBs]
      exact (hρker (eBs (Multiplicative.ofAdd u))).mp hρu
    have hmemE : ((Additive.toMul (ι.symm u) : ↥Bs) : G) ∈ ggSpanSub ι W :=
      mem_ggSpanSub.mpr ⟨u, huW, rfl⟩
    have hmemC : ((Additive.toMul (ι.symm u) : ↥Bs) : G) ∈
        Subgroup.centralizer (J : Set G) :=
      (ggGamma_eq_one_iff J hN (Additive.toMul (ι.symm u))).mp hγu
    have hbot : ((Additive.toMul (ι.symm u) : ↥Bs) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hEbotW]
      exact ⟨hmemE, hmemC⟩
    have h1 : Additive.toMul (ι.symm u) = 1 := by
      apply Subtype.ext
      simpa using (Subgroup.mem_bot.mp hbot)
    have h1' : ι.symm u = 0 := by
      apply Additive.toMul.injective
      simpa using h1
    have hu0 : u = 0 := by
      apply ι.symm.injective
      simpa using h1'
    simpa [hu0]
  have hKle : K ≤ b.ker.toAddSubgroup := by
    intro u hu
    rw [Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((Additive.toMul (liftCommBilinear (p := 3) hπ hker e u v) :
      kernelOmega hker 3) : Y) = 1
    rw [liftCommBilinear_apply]
    have heu : e (Multiplicative.ofAdd u) = 1 :=
      MonoidHom.mem_ker.mp (by simpa [K] using hu)
    rw [heu]
    exact liftComm_one_left hπ hker (e (Multiplicative.ofAdd v))
  have hSle : W.toAddSubgroup ≤ b.ker.toAddSubgroup := by
    intro u hu
    rw [Submodule.mem_toAddSubgroup]
    exact hspanW (by simpa using hu)
  have hWcard : Nat.card W = 27 := by
    rw [← card_ggSpanSub ι W, hEcardW]
  have hScard : Nat.card W.toAddSubgroup = 27 := hWcard
  have hVcard : Nat.card V = Nat.card K * Nat.card e.range := by
    have h1 := Subgroup.card_ker_mul_card_range e
    have h2 : Nat.card e.ker = Nat.card K := by
      let ek : e.ker ≃ K :=
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Nat.card_congr ek
    calc Nat.card V = Nat.card (Multiplicative V) := rfl
      _ = Nat.card e.ker * Nat.card e.range := h1.symm
      _ = Nat.card K * Nat.card e.range := by rw [h2]
  have hcard : Nat.card V ≤ 3 * (Nat.card K * Nat.card W.toAddSubgroup) := by
    rw [hScard, hVcard, hrange]
    calc Nat.card K * Nat.card ρ.range ≤ Nat.card K * 81 :=
          Nat.mul_le_mul_left _ hρcard
      _ = 3 * (Nat.card K * 27) := by ring
  have hb0 : b = 0 :=
    LinearMap.BilinMap.eq_zero_of_card_le_three_mul_card_mul_card b hbalt K
      W.toAddSubgroup hKle hSle hKS hcard
  have hUcomm : ∀ s ∈ e.range, ∀ t ∈ e.range, liftComm π hπ s t = 1 := by
    intro s hs t ht
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hs
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp ht
    have hzero : liftCommBilinear (p := 3) hπ hker e
        (Multiplicative.toAdd u) (Multiplicative.toAdd v) = 0 := by
      have := congrArg (fun f : V →ₗ[ZMod 3] V →ₗ[ZMod 3] Additive (kernelOmega hker 3) =>
        f (Multiplicative.toAdd u) (Multiplicative.toAdd v)) hb0
      simpa [b] using this
    have happ := liftCommBilinear_apply (p := 3) hπ hker e
      (Multiplicative.toAdd u) (Multiplicative.toAdd v)
    rw [hzero] at happ
    simpa using happ.symm
  intro x y hx hy
  exact mul_comm_of_liftComm_eq_one hπ hker hUcomm
    (by rw [Subgroup.mem_comap, hrange]; exact hx)
    (by rw [Subgroup.mem_comap, hrange]; exact hy)

theorem a3_actual_pair_zero
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResLineJDatum 3 Bs J .A3)
    {Y H : Type} [Group Y] [Group H] {π : Y →* H}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    {ρ : ↥Bs →* H}
    (hρker : ∀ b : ↥Bs, ρ b = 1 ↔ ggGamma J hN b = 1)
    (hρcard : Nat.card ρ.range ≤ 81)
    (hconj : ∀ φ ∈ ggAutomizer J Bs, ∃ t : H, ∀ b : ↥Bs,
      ρ (φ b) = t * ρ b * t⁻¹) :
    ∀ x y : Y, π x ∈ ρ.range → π y ∈ ρ.range → x * y = y * x := by
  classical
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  letI : AddCommGroup V := instA
  letI : Module (ZMod 3) V := instM
  have hpairA : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa only [GGResLineJType.cartan] using hpair i j
  have hα2 : ∀ j : Fin 3, α j (h j) = 2 := ggResI_alpha_self_eq_two_of_A3 hpairA
  have hEprops := GGResLineJDatum.coroot_span_subgroup_properties_of_A3
    hN ι r h α hform hpairA hind hgen
    (Submodule.span (ZMod 3) (Set.range h)) rfl
  exact pair_zero_of_rank_three_coroot hN ι r h α hform hα2 hind hgen
    hEprops.2.2.1 hEprops.2.2.2 hπ hker hρker hρcard hconj

theorem actual_pair_zero_of_line
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} {T : GGResLineJType}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    {Y H : Type} [Group Y] [Group H] {π : Y →* H}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    {ρ : ↥Bs →* H}
    (hρker : ∀ b : ↥Bs, ρ b = 1 ↔ ggGamma J hN b = 1)
    (hρcard : Nat.card ρ.range ≤ 81)
    (hconj : ∀ φ ∈ ggAutomizer J Bs, ∃ t : H, ∀ b : ↥Bs,
      ρ (φ b) = t * ρ b * t⁻¹) :
    ∀ x y : Y, π x ∈ ρ.range → π y ∈ ρ.range → x * y = y * x := by
  rcases hT with rfl | hT
  · exact a3_actual_pair_zero hN hD hπ hker hρker hρcard hconj
  · rcases hT with rfl | rfl
    · obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
      letI : AddCommGroup V := instA
      letI : Module (ZMod 3) V := instM
      have hpairB : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.B 3 i j : ZMod 3) := by
        intro i j
        simpa only [GGResLineJType.cartan] using hpair i j
      have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
        intro j
        rw [hpairB j j]
        fin_cases j <;> norm_num [CartanMatrix.B]
      have hC := ker_zero_of_det_two (C := CartanMatrix.B 3)
        (CartanMatrix.B_det (by norm_num))
      have hEprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 3)
        hN ι r h α (CartanMatrix.B 3) hform hα2 hpairB hind hC hgen
        (Submodule.span (ZMod 3) (Set.range h)) rfl
      have hcard27 : Nat.card (ggSpanSub ι
          (Submodule.span (ZMod 3) (Set.range h))) = 27 := by
        have h := hEprops.2.2.1
        norm_num at h
        exact h
      exact pair_zero_of_rank_three_coroot hN ι r h α hform hα2 hind hgen
        hcard27 hEprops.2.2.2 hπ hker hρker hρcard hconj
    · obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
      letI : AddCommGroup V := instA
      letI : Module (ZMod 3) V := instM
      have hpairC : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.C 3 i j : ZMod 3) := by
        intro i j
        simpa only [GGResLineJType.cartan] using hpair i j
      have hα2 : ∀ j : Fin 3, α j (h j) = 2 := by
        intro j
        rw [hpairC j j]
        fin_cases j <;> norm_num [CartanMatrix.C]
      have hC := ker_zero_of_det_two (C := CartanMatrix.C 3)
        (CartanMatrix.C_det (by norm_num))
      have hEprops := GGResLineJDatum.coroot_span_subgroup_properties_of_cartan (k := 3)
        hN ι r h α (CartanMatrix.C 3) hform hα2 hpairC hind hC hgen
        (Submodule.span (ZMod 3) (Set.range h)) rfl
      have hcard27 : Nat.card (ggSpanSub ι
          (Submodule.span (ZMod 3) (Set.range h))) = 27 := by
        have h := hEprops.2.2.1
        norm_num at h
        exact h
      exact pair_zero_of_rank_three_coroot hN ι r h α hform hα2 hind hgen
        hcard27 hEprops.2.2.2 hπ hker hρker hρcard hconj

end CFSG.StandardType

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.GGFinModel


theorem actual_rankThree_recipe_abelianPreimage
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} {T : GGResLineJType}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : ↥J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center ↥J)
    (hperf : commutator ↥J = ⊤)
    (hAI : ∀ a ∈ (ggGamma J hN).range,
      ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : ↥J, φ (ψ l) = ψ (a l))
    (hcardA : Nat.card (ggGamma J hN).range ≤ 81) :
    CFSG.StandardType.LieCore.M6c.GGLieAbelianPreimageE6
      (rgrpModel hn hK σ hσ Fr hFr ε
        (TypeA.inducedSub ψ (ggGamma J hN).range)) := by
  classical
  intro k₀ hk₀ hk₀fin ι₀ x y hx hy
  let A := (ggGamma J hN).range
  let e : A →* ModGL Tag.E6 GGL :=
    (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom
  obtain ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, hek, hjk, hconj, hek_inj⟩ :=
    exists_actual_recipe_action_finite_descent hN hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI k₀ ι₀
  letI : Field k := hk
  letI : Finite k := hkfin
  letI : CharP k 2 := hchar
  let π : ↥(e6Data_valid.minGroup k) →* adjointGroup Tag.E6 k := e6Isogeny k
  let ρ : ↥Bs →* adjointGroup Tag.E6 k :=
    { toFun := fun b => e_k ((ggGamma J hN).rangeRestrict b)
      map_one' := by
        rw [map_one]
        exact map_one e_k
      map_mul' := fun b c => by
        calc
          e_k ((ggGamma J hN).rangeRestrict (b * c)) =
              e_k ((ggGamma J hN).rangeRestrict b *
                (ggGamma J hN).rangeRestrict c) := by rw [map_mul]
          _ = e_k ((ggGamma J hN).rangeRestrict b) *
                e_k ((ggGamma J hN).rangeRestrict c) := map_mul e_k _ _ }
  have hπ : Function.Surjective π := e6Isogeny_surjective k
  have hkerπ : π.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := k)]
  have hρker : ∀ b : ↥Bs, ρ b = 1 ↔ ggGamma J hN b = 1 := by
    intro b
    constructor
    · intro hb
      have h1 : (ggGamma J hN).rangeRestrict b = 1 := by
        apply hek_inj
        calc
          e_k ((ggGamma J hN).rangeRestrict b) = 1 := by
            simpa [ρ, MonoidHom.comp_apply] using hb
          _ = e_k (1 : A) := (map_one e_k).symm
      simpa using congrArg Subtype.val h1
    · intro hb
      have h1 : (ggGamma J hN).rangeRestrict b = 1 := Subtype.ext hb
      calc
        ρ b = e_k ((ggGamma J hN).rangeRestrict b) := rfl
        _ = e_k 1 := congrArg e_k h1
        _ = 1 := map_one e_k
  have hρrange : ρ.range = e_k.range := by
    ext h
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(ggGamma J hN).rangeRestrict b, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := MonoidHom.rangeRestrict_surjective (ggGamma J hN) a
      exact ⟨b, by simpa [ρ, MonoidHom.comp_apply] using congrArg e_k hb⟩
  have hcard_e : Nat.card e_k.range = Nat.card A := by
    let ee : A ≃ e_k.range :=
      Equiv.ofBijective e_k.rangeRestrict
        ⟨fun x y h => hek_inj (congrArg Subtype.val h), e_k.rangeRestrict_surjective⟩
    exact (Nat.card_congr ee).symm
  have hρcard : Nat.card ρ.range ≤ 81 := by
    rw [hρrange, hcard_e]
    exact hcardA
  have hα_apply (n : actualRecipeActorNormalizer hN) (a : A) :
      actualRecipeActorNormalizerAction hN n a = ggConjAut A n.2 a := by
    apply Subtype.ext
    change ((A.normalizerMonoidHom
      (⟨(MulAut.conj : ↥J →* MulAut ↥J) (n : ↥J), n.2⟩ : Subgroup.normalizer (A : Set (MulAut ↥J))))
        a : MulAut ↥J) = ((ggConjAut A n.2 a : A) : MulAut ↥J)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hconj : ∀ φ ∈ ggAutomizer J Bs, ∃ t : adjointGroup Tag.E6 k, ∀ b : ↥Bs,
      ρ (φ b) = t * ρ b * t⁻¹ := by
    intro φ hφ
    obtain ⟨g, hgJ, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    let gJ : ↥J := ⟨g, hgJ⟩
    have hgn : MulAut.conj gJ ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) :=
      conj_mem_normalizer_range_ggGamma hN hgJ hgN
    let n : actualRecipeActorNormalizer hN := ⟨gJ, hgn⟩
    refine ⟨j_k n, ?_⟩
    have hφeq : φ = ggConjAut Bs hgN := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      simpa [ggConjAut_apply] using hφg b
    intro b
    calc
      ρ (φ b) = e_k ((ggGamma J hN).rangeRestrict (φ b)) := rfl
      _ = e_k ((ggGamma J hN).rangeRestrict (ggConjAut Bs hgN b)) := by rw [hφeq]
      _ = e_k (ggConjAut A hgn ((ggGamma J hN).rangeRestrict b)) := by
        rw [ggOverGamma_conjAut hgJ hgN b]
      _ = e_k (actualRecipeActorNormalizerAction hN n ((ggGamma J hN).rangeRestrict b)) := by
        rw [hα_apply]
      _ = j_k n * e_k ((ggGamma J hN).rangeRestrict b) * (j_k n)⁻¹ := hconj n _
      _ = j_k n * ρ b * (j_k n)⁻¹ := rfl
  have hcomm := CFSG.StandardType.actual_pair_zero_of_line hN hD hT
    (π := π) (ρ := ρ) hπ hkerπ hρker hρcard hconj
  let x' : ↥(e6Data_valid.minGroup k) := minBC e6Data_valid κ x
  let y' : ↥(e6Data_valid.minGroup k) := minBC e6Data_valid κ y
  have hxmem : π x' ∈ ρ.range := by
    have hx' : baseChangeGL ι (e6Isogeny k x' : ModGL Tag.E6 k) ∈
        rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) := by
      rw [show (e6Isogeny k x' : ModGL Tag.E6 k) =
        baseChangeGL κ (e6Isogeny k₀ x : ModGL Tag.E6 k₀) from e6Isogeny_minBC κ x]
      rw [baseChangeGL_baseChangeGL, hcomp]
      exact hx
    let m : ↥(rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) :=
      ⟨baseChangeGL ι (e6Isogeny k x' : ModGL Tag.E6 k), hx'⟩
    let a : A := (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).symm m
    have heq : e_k a = π x' := by
      apply Subtype.ext
      apply baseChangeGL_injective ι
      calc
        baseChangeGL ι (e_k a).val = e a := hek a
        _ = m.val := by
          change (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a).val = m.val
          rw [MulEquiv.apply_symm_apply]
        _ = baseChangeGL ι (π x') := rfl
    rw [hρrange]
    exact ⟨a, heq⟩
  have hymem : π y' ∈ ρ.range := by
    have hy' : baseChangeGL ι (e6Isogeny k y' : ModGL Tag.E6 k) ∈
        rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) := by
      rw [show (e6Isogeny k y' : ModGL Tag.E6 k) =
        baseChangeGL κ (e6Isogeny k₀ y : ModGL Tag.E6 k₀) from e6Isogeny_minBC κ y]
      rw [baseChangeGL_baseChangeGL, hcomp]
      exact hy
    let m : ↥(rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)) :=
      ⟨baseChangeGL ι (e6Isogeny k y' : ModGL Tag.E6 k), hy'⟩
    let a : A := (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).symm m
    have heq : e_k a = π y' := by
      apply Subtype.ext
      apply baseChangeGL_injective ι
      calc
        baseChangeGL ι (e_k a).val = e a := hek a
        _ = m.val := by
          change (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a).val = m.val
          rw [MulEquiv.apply_symm_apply]
        _ = baseChangeGL ι (π y') := rfl
    rw [hρrange]
    exact ⟨a, heq⟩
  have hxy' : x' * y' = y' * x' := hcomm x' y' hxmem hymem
  have hxy : minBC e6Data_valid κ (x * y) = minBC e6Data_valid κ (y * x) := by
    rw [map_mul, map_mul]
    exact hxy'
  exact (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
    e6Data_valid κ) hxy

theorem actual_A3_recipe_abelianPreimage
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResLineJDatum 3 Bs J .A3)
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : ↥J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center ↥J)
    (hperf : commutator ↥J = ⊤)
    (hAI : ∀ a ∈ (ggGamma J hN).range,
      ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : ↥J, φ (ψ l) = ψ (a l))
    (hcardA : Nat.card (ggGamma J hN).range ≤ 81) :
    CFSG.StandardType.LieCore.M6c.GGLieAbelianPreimageE6
      (rgrpModel hn hK σ hσ Fr hFr ε
        (TypeA.inducedSub ψ (ggGamma J hN).range)) :=
  actual_rankThree_recipe_abelianPreimage hN hD (Or.inl rfl) hn hK σ hσ Fr hFr ε hε
    hψ hker hperf hAI hcardA

end CFSG.StandardType.SCFourCover
