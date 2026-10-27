module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res5ProofLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Res5L34

open Module

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

@[expose] def restrictHom {F : Type*} [Monoid F] (τ : F →* Module.End K W) (P : Submodule K W)
    (hP : ∀ x : F, ∀ w ∈ P, τ x w ∈ P) : F →* Module.End K P where
  toFun x := (τ x).restrict (hP x)
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [LinearMap.restrict_apply]
  map_mul' x y := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [LinearMap.restrict_apply, map_mul]

theorem restrictHom_apply_coe {F : Type*} [Monoid F] (τ : F →* Module.End K W)
    (P : Submodule K W) (hP : ∀ x : F, ∀ w ∈ P, τ x w ∈ P) (x : F) (w : P) :
    ((restrictHom τ P hP x) w : W) = τ x w :=
  rfl

theorem injective_of_group {F : Type*} [Group F] {M : Type*} [AddCommGroup M] [Module K M]
    (τ : F →* Module.End K M) (x : F) : Function.Injective (τ x) := by
  intro a b h
  have h' := congrArg (τ x⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    at h'

theorem eq_one_or_eq_of_sq_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C] {z c : C}
    (hz : z ^ 2 = 1) (hz1 : z ≠ 1) (hc : c ^ 2 = 1) : c = 1 ∨ c = z := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra h
  push Not at h
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, z, c} : Finset C) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hz
    · exact hc
  have h3 : ({1, z, c} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hz1, Ne.symm h.1⟩
  have := Finset.card_le_card hsub
  omega

variable [IsAlgClosed K] [FiniteDimensional K W]

theorem false_of_twoLocal (h2 : (2 : K) ≠ 0) (hW : Module.finrank K W ≤ 3) {F : Type*} [Group F]
    [Finite F] (τ : F →* Module.End K W) (C : Subgroup F) (hCc : C ≤ Subgroup.center F)
    (hCcyc : IsCyclic C) (hsq : ∀ x : F, x ^ 2 ∈ C)
    (hcomm : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ C) (hcard : 16 * Nat.card C ≤ Nat.card F)
    (hZ : (∀ x y : F, x * y = y * x) ∨ Subgroup.center F ≤ C) (hker : τ.ker ≤ C) : False := by
  classical
  have hcen : ∀ c ∈ C, ∀ g : F, c * g = g * c := fun c hc g =>
    ((Subgroup.mem_center_iff.mp (hCc hc)) g).symm
  by_cases hab : ∀ x y : F, τ x * τ y = τ y * τ x
  ·
    let T : F →* (Module.End K W)ˣ := τ.toHomUnits
    have hTv : ∀ x, (T x : Module.End K W) = τ x := fun x => rfl
    have hkerT : T.ker ≤ C := fun x hx => hker (by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [← hTv, hx, Units.val_one])
    set R := T.range with hR
    have : Finite R := by
      rw [hR]
      exact Finite.of_surjective T.rangeRestrict T.rangeRestrict_surjective
    have hRcomm : ∀ a b : R, a * b = b * a := by
      rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, hTv]
      exact hab x y
    let _ : CommGroup R := { (inferInstance : Group R) with mul_comm := hRcomm }
    let s : R →* R := powMonoidHom 2
    let f : s.ker →* Module.End K W :=
      (Units.coeHom (Module.End K W)).comp (R.subtype.comp s.ker.subtype)
    have hf : Function.Injective f := by
      intro a b hab'
      apply Subtype.ext
      apply Subtype.ext
      exact Units.ext hab'
    have hexp : ∀ a : s.ker, a ^ 2 = 1 := by
      intro a
      apply Subtype.ext
      exact a.2
    have hle8 := card_le_pow_finrank (n := 2) (by norm_num) (by exact_mod_cast h2) f hf hexp
    have h8 : Nat.card s.ker ≤ 8 := hle8.trans (by
      calc 2 ^ Module.finrank K W ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hW
        _ = 8 := by norm_num)
    have hFker : Nat.card T.ker * Nat.card R = Nat.card F := by
      rw [hR, ← Subgroup.index_ker, Subgroup.card_mul_index]
    let TC : C →* (Module.End K W)ˣ := T.comp C.subtype
    have h3 : TC.range = C.map T := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have : Finite (C.map T) := by
      rw [← h3]
      exact Finite.of_surjective TC.rangeRestrict TC.rangeRestrict_surjective
    have hTC : Nat.card T.ker * Nat.card (C.map T) = Nat.card C := by
      have h1 : Nat.card TC.ker * Nat.card TC.range = Nat.card C := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index]
      have h2' : Nat.card TC.ker = Nat.card T.ker := by
        have : TC.ker = T.ker.subgroupOf C := by
          ext c; simp [TC, Subgroup.mem_subgroupOf]
        rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerT).toEquiv]
      rw [← h2', ← h3, h1]
    have hRs : Nat.card s.ker * Nat.card s.range = Nat.card R := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have hrange : Nat.card s.range ≤ Nat.card (C.map T) := by
      let g : s.range → C.map T := fun a => ⟨(a.1 : (Module.End K W)ˣ), by
        obtain ⟨b, hb⟩ := a.2
        obtain ⟨_, ⟨x, rfl⟩⟩ := b
        have hx : (a.1 : (Module.End K W)ˣ) = T (x ^ 2) := by
          rw [← hb]
          simp [s, map_pow]
        rw [hx]
        exact ⟨_, hsq x, rfl⟩⟩
      refine Nat.card_le_card_of_injective g ?_
      intro a b hab'
      have h' := congrArg (fun t : C.map T => (t : (Module.End K W)ˣ)) hab'
      apply Subtype.ext
      apply Subtype.ext
      exact h'
    have hpos : 0 < Nat.card s.range := Nat.card_pos
    have hposk : 0 < Nat.card T.ker := Nat.card_pos
    have key : 16 * Nat.card s.range ≤ Nat.card s.ker * Nat.card s.range := by
      have h1 : 16 * (Nat.card T.ker * Nat.card (C.map T)) ≤ Nat.card T.ker * Nat.card R := by
        rw [hTC, hFker]; exact hcard
      have h2' : 16 * Nat.card (C.map T) ≤ Nat.card R := by
        have : Nat.card T.ker * (16 * Nat.card (C.map T)) ≤ Nat.card T.ker * Nat.card R := by
          calc Nat.card T.ker * (16 * Nat.card (C.map T)) =
              16 * (Nat.card T.ker * Nat.card (C.map T)) := by ring
            _ ≤ _ := h1
        exact Nat.le_of_mul_le_mul_left this hposk
      calc 16 * Nat.card s.range ≤ 16 * Nat.card (C.map T) := Nat.mul_le_mul_left _ hrange
        _ ≤ Nat.card R := h2'
        _ = Nat.card s.ker * Nat.card s.range := hRs.symm
    have := Nat.le_of_mul_le_mul_right key hpos
    omega
  ·
    push Not at hab
    obtain ⟨x, y, hxy⟩ := hab
    have hFab : ¬ ∀ a b : F, a * b = b * a := fun h => hxy (by rw [← map_mul, h, map_mul])
    have hZC : Subgroup.center F ≤ C := hZ.resolve_left hFab
    set z := x * y * x⁻¹ * y⁻¹ with hzdef
    have hzC : z ∈ C := hcomm x y
    have hxyz : x * y = z * (y * x) := by rw [hzdef]; group
    have hτz1 : τ z ≠ 1 := by
      intro h
      apply hxy
      rw [← map_mul, hxyz, map_mul, h, one_mul, map_mul]
    have hcsq : ∀ g h : F, (g * h * g⁻¹ * h⁻¹) ^ 2 = 1 := by
      intro g h
      set c := g * h * g⁻¹ * h⁻¹ with hcdef
      have hc : c ∈ C := hcomm g h
      have hgg : g * g ∈ C := by rw [← sq]; exact hsq g
      have hgc : g * c * g⁻¹ = c := by rw [← hcen c hc g]; group
      have e1 : (g * g) * h * (g * g)⁻¹ * h⁻¹ = 1 := by
        rw [hcen _ hgg h]; group
      have e2 : (g * g) * h * (g * g)⁻¹ * h⁻¹ = (g * c * g⁻¹) * c := by rw [hcdef]; group
      rw [e2, hgc] at e1
      rw [sq, e1]
    have hz2 : z ^ 2 = 1 := hcsq x y
    have hz1 : z ≠ 1 := fun h => hτz1 (by rw [h, map_one])
    have hcomm2 : ∀ g h : F, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = z := by
      intro g h
      have := eq_one_or_eq_of_sq_eq_one (C := C) (z := ⟨z, hzC⟩) (c := ⟨_, hcomm g h⟩)
        (Subtype.ext (by simpa using hz2)) (fun h' => hz1 (congrArg Subtype.val h'))
        (Subtype.ext (by simpa using hcsq g h))
      rcases this with h' | h'
      · exact Or.inl (congrArg Subtype.val h')
      · exact Or.inr (congrArg Subtype.val h')
    have hssz : (τ z).IsSemisimple :=
      isSemisimple_of_pow_eq_one (n := 2) (by exact_mod_cast h2) (by rw [← map_pow, hz2, map_one])
    set Wm := (τ z).eigenspace (-1) with hWm
    have hWm0 : Wm ≠ ⊥ := by
      intro hbot
      apply hτz1
      have htop := hssz.iSup_eigenspace_eq_top
      have hle : ⨆ μ, (τ z).eigenspace μ ≤ (τ z).eigenspace 1 := by
        refine iSup_le fun μ => ?_
        by_cases hμ : (τ z).eigenspace μ = ⊥
        · rw [hμ]; exact bot_le
        · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
          have hzv : τ z v = μ • v := Module.End.mem_eigenspace_iff.mp hv
          have h2v := pow_apply_of_apply_eq_smul hzv 2
          rw [← map_pow, hz2, map_one, Module.End.one_apply] at h2v
          have hμ2 : (μ - 1) * (μ + 1) = 0 := by
            have h3 : (μ ^ 2 - 1) • v = 0 := by rw [sub_smul, ← h2v, one_smul, sub_self]
            have := (smul_eq_zero.mp h3).resolve_right hv0
            linear_combination this
          rcases mul_eq_zero.mp hμ2 with h | h
          · rw [sub_eq_zero.mp h]
          · exfalso
            apply hμ
            rw [show μ = -1 by linear_combination h]
            exact hbot
      rw [htop] at hle
      apply LinearMap.ext
      intro v
      have := Module.End.mem_eigenspace_iff.mp (hle (Submodule.mem_top (x := v)))
      rw [this, one_smul, Module.End.one_apply]
    have hWmInv : ∀ g : F, ∀ w ∈ Wm, τ g w ∈ Wm := by
      intro g w hw
      rw [hWm, Module.End.mem_eigenspace_iff] at hw ⊢
      rw [← Module.End.mul_apply, ← map_mul, hcen z hzC g, map_mul, Module.End.mul_apply, hw,
        map_smul]
    let ρ := restrictHom τ Wm hWmInv
    have hρz : ρ z = (-1 : K) • 1 := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      have hw := Module.End.mem_eigenspace_iff.mp w.2
      rw [restrictHom_apply_coe]
      simpa using hw
    have hm1 : (-1 : K) ≠ 1 := by
      intro h
      apply h2
      linear_combination -h
    have hd : Module.finrank K Wm = 2 := by
      let d : F →* K := LinearMap.det.comp ρ
      have e : ∀ a : F, d a * d a⁻¹ = 1 := fun a => by rw [← map_mul, mul_inv_cancel, map_one]
      have hdz : d z = 1 := by
        calc d z = d x * d y * d x⁻¹ * d y⁻¹ := by rw [hzdef]; simp only [map_mul]
          _ = (d x * d x⁻¹) * (d y * d y⁻¹) := by ring
          _ = 1 := by rw [e, e, one_mul]
      have hdz' : d z = (-1) ^ Module.finrank K Wm := by
        show LinearMap.det (ρ z) = _
        rw [hρz, LinearMap.det_smul, map_one, mul_one]
      have heven : Even (Module.finrank K Wm) := by
        rw [← neg_one_pow_eq_one_iff_even hm1, ← hdz', hdz]
      have h1 : 0 < Module.finrank K Wm :=
        Nat.pos_of_ne_zero (fun h => hWm0 (Submodule.finrank_eq_zero.mp h))
      have h3 : Module.finrank K Wm ≤ 3 := (Submodule.finrank_le Wm).trans hW
      obtain ⟨k, hk⟩ := heven
      omega
    have hXY : ρ x * ρ y = -(ρ y * ρ x) := by
      have h' : ρ z * (ρ y * ρ x) = -(ρ y * ρ x) := by rw [hρz]; simp
      rw [← map_mul, hxyz, map_mul ρ z (y * x), map_mul ρ y x]
      exact h'
    have hCsc : ∀ c ∈ C, ∃ a : K, ρ c = a • 1 := by
      intro c hc
      exact exists_eq_smul_of_commute_of_anticommute h2 hd hXY (injective_of_group ρ x)
        (injective_of_group ρ y) (by rw [← map_mul, ← map_mul, hcen c hc x])
        (by rw [← map_mul, ← map_mul, hcen c hc y])
    have hscC : ∀ g : F, (∃ a : K, ρ g = a • 1) → g ∈ C := by
      rintro g ⟨a, ha⟩
      apply hZC
      rw [Subgroup.mem_center_iff]
      intro h
      rcases hcomm2 g h with e | e
      · calc h * g = (g * h * g⁻¹ * h⁻¹)⁻¹ * (g * h) := by group
          _ = g * h := by rw [e, inv_one, one_mul]
      · exfalso
        have hcomm' : ρ g * ρ h = ρ h * ρ g := by
          rw [ha, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
        have h1 : ρ (g * h * g⁻¹ * h⁻¹) = 1 := by
          calc ρ (g * h * g⁻¹ * h⁻¹) = ρ g * ρ h * ρ g⁻¹ * ρ h⁻¹ := by simp only [map_mul]
            _ = ρ h * (ρ g * ρ g⁻¹) * ρ h⁻¹ := by rw [hcomm']; simp only [mul_assoc]
            _ = 1 := by
              rw [← map_mul ρ g, mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel,
                map_one]
        rw [e, hρz] at h1
        obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWm0
        have h3 := congrArg (fun T : Module.End K Wm => ((T ⟨w, hw⟩ : Wm) : W)) h1
        simp only [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul] at h3
        have h4 : (2 : K) • w = 0 := by
          rw [two_smul]
          nth_rewrite 1 [← h3]
          rw [neg_one_smul, neg_add_cancel]
        exact hw0 ((smul_eq_zero.mp h4).resolve_left h2)
    have hCn : C.Normal := ⟨fun n hn g => by
      rw [← hcen n hn g, mul_inv_cancel_right]; exact hn⟩
    let _ : Fintype (F ⧸ C) := Fintype.ofFinite _
    let r : F ⧸ C → F := Quotient.out
    have hr : ∀ i j, i ≠ j → ∀ a : K, ρ (r i * (r j)⁻¹) ≠ a • 1 := by
      intro i j hij a ha
      apply hij
      have hmem := hscC _ ⟨a, ha⟩
      rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq]
      rw [show Quotient.out i = r i from rfl, show Quotient.out j = r j from rfl]
      have h' := hCn.conj_mem _ (C.inv_mem hmem) (r i)⁻¹
      convert h' using 1
      group
    have hsq' : ∀ g : F, ∃ a : K, ρ g * ρ g = a • 1 := fun g => by
      rw [← map_mul, ← sq]
      exact hCsc _ (hsq g)
    have h4 := card_le_four_of_sq_smul h2 hd ρ hsq' r hr
    have hcardQ : Nat.card (F ⧸ C) * Nat.card C = Nat.card F :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup C).symm
    rw [Nat.card_eq_fintype_card (α := F ⧸ C)] at hcardQ
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have : 16 * Nat.card C ≤ 4 * Nat.card C := by
      calc 16 * Nat.card C ≤ Nat.card F := hcard
        _ = Fintype.card (F ⧸ C) * Nat.card C := hcardQ.symm
        _ ≤ 4 * Nat.card C := Nat.mul_le_mul_right _ h4
    omega

end CFSG.RankThree.PartTwo.Sec4.Census.Res5L34
