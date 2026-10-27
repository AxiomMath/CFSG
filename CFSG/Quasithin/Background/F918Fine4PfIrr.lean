module

public import CFSG.Quasithin.Background.F918Fine4PfCen
public import CFSG.Quasithin.Background.F918C0

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

namespace F918Fine4Pf

section Module

variable {U : Type} [CommGroup U] [Finite U]

theorem exists_mem_irrPlus_le {X : Subgroup (MulAut U)} (hX : ⁅X, X⁆ = X) {M : Subgroup U}
    (hM : ∀ x ∈ X, ∀ m ∈ M, x m ∈ M) (hne : commSub M X ≠ ⊥) :
    ∃ I, I ∈ IrrPlus X (⊤ : Subgroup U) ∧ I ≤ M := by
  classical
  let S : Set (Subgroup U) := {J | J ≤ M ∧ (∀ x ∈ X, ∀ w ∈ J, x w ∈ J) ∧ commSub J X ≠ ⊥}
  have hSne : S.Nonempty := ⟨M, le_rfl, hM, hne⟩
  obtain ⟨I, hI, hmin⟩ := Set.exists_min_image S (fun J => Nat.card J) (Set.toFinite S) hSne
  obtain ⟨hIM, hIinv, hIne⟩ := hI
  have hmin' : ∀ J : Subgroup U, (∀ x ∈ X, ∀ w ∈ J, x w ∈ J) → J < I → commSub J X = ⊥ := by
    intro J hJinv hJI
    by_contra hJne
    have hc : Nat.card I ≤ Nat.card J := hmin J ⟨hJI.le.trans hIM, hJinv, hJne⟩
    exact hJI.ne (Subgroup.eq_of_le_of_card_ge hJI.le hc)
  have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.2 hX
  have hcomm : commSub I X = I := by
    apply le_antisymm (commSub_le_of_invariant hIinv)
    by_contra hnot
    have hlt : commSub I X < I :=
      lt_of_le_of_ne (commSub_le_of_invariant hIinv) fun h => hnot h.ge
    have hfix : commSub I X ≤ fixV X :=
      commSub_eq_bot_iff.1 (hmin' _ (commSub_inv_H X I) hlt)
    apply hIne
    rw [commSub_eq_bot_iff]
    intro i hi x hx
    let c : ↥X →* ↥(commSub I X) :=
      { toFun := fun y => ⟨(y : MulAut U) i * i⁻¹,
          Subgroup.subset_closure ⟨y, y.2, i, hi, rfl⟩⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y z => by
          apply Subtype.ext
          have hz : (z : MulAut U) i * i⁻¹ ∈ commSub I X :=
            Subgroup.subset_closure ⟨z, z.2, i, hi, rfl⟩
          have hy : (y : MulAut U) ((z : MulAut U) i * i⁻¹) = (z : MulAut U) i * i⁻¹ :=
            hfix hz y y.2
          have e : (y : MulAut U) ((z : MulAut U) i) =
              (y : MulAut U) ((z : MulAut U) i * i⁻¹) * (y : MulAut U) i := by
            rw [← map_mul]
            simp
          show ((y : MulAut U) * (z : MulAut U)) i * i⁻¹ =
            ((y : MulAut U) i * i⁻¹) * ((z : MulAut U) i * i⁻¹)
          rw [MulAut.mul_apply, e, hy]
          cgroup }
    have hker : commutator ↥X ≤ c.ker := Abelianization.commutator_subset_ker c
    have h1 : (⟨x, hx⟩ : ↥X) ∈ c.ker := hker (by rw [hperf.commutator_eq_top]; trivial)
    have h2 := congrArg Subtype.val h1
    simpa [c, mul_inv_eq_one] using h2
  have hlt : I ⊓ fixV X < I := by
    refine lt_of_le_of_ne inf_le_left fun h => hIne ?_
    rw [commSub_eq_bot_iff]
    intro i hi
    have hmem : i ∈ I ⊓ fixV X := by rw [h]; exact hi
    exact hmem.2
  refine ⟨I, (mem_irrPlus_top_iff).2 ⟨hIinv, hcomm, hlt, ?_⟩, hIM⟩
  intro J hJinv hJ1 hJ2
  by_cases hJI : J = I
  · exact Or.inr hJI
  · left
    have hJlt : J < I := lt_of_le_of_ne hJ2 hJI
    have hJfix : J ≤ fixV X := commSub_eq_bot_iff.1 (hmin' J hJinv hJlt)
    exact le_antisymm (le_inf hJ2 hJfix) hJ1

omit [Finite U] in
theorem commSub_top_invariant {Y : Subgroup (MulAut U)} {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut U))) :
    ∀ m ∈ commSub ⊤ Y, g m ∈ commSub ⊤ Y := by
  intro m hm
  refine Subgroup.closure_induction (p := fun m _ => g m ∈ commSub ⊤ Y) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨y, hy, w, -, rfl⟩
    refine Subgroup.subset_closure
      ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp hy, g w, Subgroup.mem_top _, ?_⟩
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
  · rw [map_one]
    exact one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]
    exact mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact inv_mem ha

omit [Finite U] in
theorem mem_normalizer_map_center {X : Subgroup (MulAut U)} {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut U))) :
    g ∈ Subgroup.normalizer
      (((Subgroup.center ↥X).map X.subtype : Subgroup (MulAut U)) : Set (MulAut U)) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set (MulAut U)),
      ∀ y ∈ (Subgroup.center ↥X).map X.subtype,
        g * y * g⁻¹ ∈ (Subgroup.center ↥X).map X.subtype := by
    rintro g hg _ ⟨y, hy, rfl⟩
    have hgy : g * (y : MulAut U) * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg _).mp y.2
    refine ⟨⟨_, hgy⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext ?_, rfl⟩
    have hk : g⁻¹ * (k : MulAut U) * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) _).mp k.2
      simpa using this
    have hc := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hy ⟨g⁻¹ * (k : MulAut U) * g, hk⟩)
    simp only [Subgroup.coe_mul] at hc
    show (k : MulAut U) * (g * (y : MulAut U) * g⁻¹) = g * (y : MulAut U) * g⁻¹ * k
    calc (k : MulAut U) * (g * (y : MulAut U) * g⁻¹)
        = g * ((g⁻¹ * (k : MulAut U) * g) * (y : MulAut U)) * g⁻¹ := by group
      _ = g * ((y : MulAut U) * (g⁻¹ * (k : MulAut U) * g)) * g⁻¹ := by rw [hc]
      _ = g * (y : MulAut U) * g⁻¹ * k := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

end Module

section Group

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem exists_irrPlus_fixFree (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T = K)
    (hZ : Subgroup.center ↥(autIH V₁ Vp H K) ≠ ⊥) :
    ∃ I : Subgroup G, V₁ ≤ I ∧ I ≤ conjClosure Vp H ∧
      (∃ W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)),
        (∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) ∧ IsIrrPlusTildeU h I W) ∧
      ∀ u ∈ I, (∀ x : ↥K, toAutI h Vp x ∈ Subgroup.center ↥(autIH V₁ Vp H K) →
        (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ V₁) → u ∈ V₁ := by
  have hF := factElem h (le_conjClosure Vp H)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hV : ∀ v : ↥(tildeOf V₁ (conjClosure Vp H)), v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))).2
      (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
    simpa using this
  set U := ↥(tildeOf V₁ (conjClosure Vp H)) with hU
  set X : Subgroup (MulAut U) := autIH V₁ Vp H K with hX
  have hX₀ : autIH V₁ Vp H (conjClosure K T) = X := by rw [hK]
  have hperf : ⁅X, X⁆ = X := by
    have := (isPerfect_autIH h Vp)
    exact Subgroup.isPerfect_iff.mp (by rw [← Group.IsPerfect.top_iff]; infer_instance)
  set Zm : Subgroup (MulAut U) := (Subgroup.center ↥X).map X.subtype with hZm
  have hodd : Odd (Nat.card Zm) := by
    rw [hZm, Subgroup.card_map_of_injective X.subtype_injective]
    exact odd_card_center_autIH h hK
  set M : Subgroup U := commSub ⊤ Zm with hM
  have hMN : ∀ g ∈ Subgroup.normalizer (X : Set (MulAut U)), ∀ m ∈ M, g m ∈ M :=
    fun g hg => commSub_top_invariant (mem_normalizer_map_center hg)
  have hMX : ∀ x ∈ X, ∀ m ∈ M, x m ∈ M := fun x hx => hMN x (Subgroup.le_normalizer hx)
  have hTX : autIH V₁ Vp H T ≤ Subgroup.normalizer (X : Set (MulAut U)) := by
    have := autIH_T_le_normalizer h Vp
    rwa [hX₀] at this
  have hMT : ∀ t ∈ autIH V₁ Vp H T, ∀ m ∈ M, t m ∈ M := fun t ht => hMN t (hTX ht)
  have hdec := coprime_decomp hodd hV (W := ⊤) (fun g _ w _ => Subgroup.mem_top _)
  have hMfix : M ⊓ fixV Zm = ⊥ := by
    have h2 := hdec.2
    rwa [top_inf_eq] at h2
  have hZmX : Zm ≤ X := Subgroup.map_subtype_le _
  have hne : commSub M X ≠ ⊥ := by
    intro h0
    have hMX' : M ≤ fixV X := commSub_eq_bot_iff.1 h0
    have hMZ : M ≤ fixV Zm := fun m hm y hy => hMX' hm y (hZmX hy)
    have hM0 : M = ⊥ := by
      rw [← hMfix]
      exact (inf_eq_left.mpr hMZ).symm
    apply hZ
    rw [eq_bot_iff]
    intro y hy
    have htop : (⊤ : Subgroup U) ≤ fixV Zm := commSub_eq_bot_iff.1 hM0
    have hy1 : ((y : X) : MulAut U) = 1 := by
      refine MulEquiv.ext fun u => ?_
      exact htop (Subgroup.mem_top u) _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext hy1)
  obtain ⟨I₀, hI₀, hI₀M⟩ := exists_mem_irrPlus_le hperf hMX hne
  rw [← hX₀] at hI₀
  have hTH : T ≤ H := h.T_le_H
  have hT2 : IsPGroup 2 ↥(autIH V₁ Vp H T) := by
    rw [autIH_eq_map h hTH]
    exact (h.sylow_H.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
  obtain ⟨I', hI'⟩ := irrPlusOn_nonempty hV (autIH_T_le_normalizer h Vp) hT2 hI₀
  have hI'M : I' ≤ M := by
    refine hI'.1.1.trans (iSup₂_le fun y hy => ?_)
    intro w hw
    obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hw
    exact hMT y hy i (hI₀M hi)
  have hV₁U : V₁ ≤ conjClosure Vp H := h.toHypF98.toHypF91.V₁_le_Vp.trans (le_conjClosure Vp H)
  set Y : Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) :=
    I'.map (tildeOf V₁ (conjClosure Vp H)).subtype with hY
  have hYU : Y ≤ tildeOf V₁ (conjClosure Vp H) := Subgroup.map_subtype_le _
  have hsub : subM V₁ (conjClosure Vp H) (secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y) =
      I' := by
    unfold subM tildeOf
    rw [secImg_secPre]
    exact map_subtype_subgroupOf' I'
  have hV₁I : V₁ ≤ secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y :=
    le_secPre Subgroup.le_normalizer Y
  have hIU : secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y ≤ conjClosure Vp H :=
    secPre_le hV₁U hYU
  refine ⟨secPre (Subgroup.normalizer (V₁ : Set G)) V₁ Y, hV₁I, hIU,
    ⟨⨆ y ∈ autIH V₁ Vp H T, y • I₀, fun t ht w hw => smul_mem_biSup_smul ht hw, ?_⟩, ?_⟩
  · show subM V₁ (conjClosure Vp H) _ ∈ _
    rw [hsub]
    exact hI'
  · intro u hu hcom
    have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
      h.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
    have hIH : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
      le_normalizer_conjClosure Vp H
    set ū : U := modMk hUN u (hIU hu) with hū
    have hūM : ū ∈ M := by
      apply hI'M
      rw [← hsub]
      exact (modMk_mem_subM_iff hUN hV₁I (hIU hu)).mpr hu
    have hūfix : ū ∈ fixV Zm := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := toAutI_surjective h Vp y
      have hxZ : toAutI h Vp x ∈ Subgroup.center ↥X := by rw [hx]; exact hy
      have hc := hcom x hxZ
      have hxH : (x : G) ∈ H := hKH x.2
      have hconj := actH_modMk h.H_le_normalizer_V₁ hUN hIH
        (Subgroup.inclusion hKH x) (hIU hu)
      show ((y : X) : MulAut U) ū = ū
      rw [← hx, toAutI_coe, hū, hconj]
      apply Subtype.ext
      show secMk _ _ ⟨(x : G) * u * (x : G)⁻¹, _⟩ = secMk _ _ ⟨u, _⟩
      refine (secMk_eq_secMk_iff.mpr ?_).symm
      have e : u⁻¹ * ((x : G) * u * (x : G)⁻¹) =
          u⁻¹ * ((x : G) * u * (x : G)⁻¹ * u⁻¹) * u⁻¹⁻¹ := by group
      show u⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ V₁
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hUN (inv_mem (hIU hu))) _).mp hc
    have hū1 : ū = 1 := by
      have hmem : ū ∈ M ⊓ fixV Zm := ⟨hūM, hūfix⟩
      rw [hMfix] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h1 := congrArg Subtype.val hū1
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨u, hUN (hIU hu)⟩)).mp h1

end Group

end F918Fine4Pf

end CFSG.Quasithin
