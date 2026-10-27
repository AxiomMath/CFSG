module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2Kernel
public import CFSG.GroupTheory.AlternatingFive.NoSubgroupsTwentyThirty

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open


theorem mem_center_of_mulVec_smul {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (M : Matrix.GeneralLinearGroup n K) (c : K)
    (hM : ∀ v : n → K, Matrix.mulVec (M : Matrix n n K) v = c • v) :
    M ∈ Subgroup.center (Matrix.GeneralLinearGroup n K) := by
  rw [Subgroup.mem_center_iff]
  intro A
  apply Units.ext
  simp only [Units.val_mul]
  apply Matrix.ext_of_mulVec_single
  intro j
  calc Matrix.mulVec ((A : Matrix n n K) * (M : Matrix n n K)) (Pi.single j 1)
      = Matrix.mulVec (A : Matrix n n K) (Matrix.mulVec (M : Matrix n n K) (Pi.single j 1)) :=
        (Matrix.mulVec_mulVec (Pi.single j 1) (A : Matrix n n K) (M : Matrix n n K)).symm
    _ = Matrix.mulVec (A : Matrix n n K) (c • Pi.single j 1) := by rw [hM]
    _ = c • (Matrix.mulVec (A : Matrix n n K) (Pi.single j 1)) :=
        Matrix.mulVec_smul _ _ _
    _ = Matrix.mulVec (M : Matrix n n K) (Matrix.mulVec (A : Matrix n n K) (Pi.single j 1)) :=
        (hM _).symm
    _ = Matrix.mulVec ((M : Matrix n n K) * (A : Matrix n n K)) (Pi.single j 1) :=
        Matrix.mulVec_mulVec (Pi.single j 1) (M : Matrix n n K) (A : Matrix n n K)

theorem hGL_mem_center_of_scalar {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {h : MulAut W} (hcomm : h * x = x * h) (c : GaloisField 2 2)
    (hc : letI := galoisModule hw2 x hx3 hfix;
      ∀ v : Additive W,
        hGaloisLinearEquiv hw2 x hx3 hfix h hcomm v = c • v) :
    letI := galoisModule hw2 x hx3 hfix
    hGL hw2 x hx3 hfix h hcomm hW ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) := by
  letI := galoisModule hw2 x hx3 hfix
  let e := galoisEquivFun hw2 x hx3 hfix hW
  have hM : ∀ u : Fin 2 → GaloisField 2 2,
      Matrix.mulVec (hGL hw2 x hx3 hfix h hcomm hW : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) u
        = c • u := by
    intro u
    have hstep := galoisEquivFun_hGL_apply hw2 x hx3 hfix hW hcomm (e.symm u)
    rw [e.apply_symm_apply] at hstep
    rw [← hstep, hc (e.symm u), LinearEquiv.map_smul, e.apply_symm_apply]
  exact mem_center_of_mulVec_smul (hGL hw2 x hx3 hfix h hcomm hW) c hM

theorem card_units_galoisField_two_two :
    Nat.card (GaloisField 2 2)ˣ = 3 := by
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Nat.card_units, hF]

theorem card_GL_two_galoisField_two :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) = 180 := by
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, hq]

theorem card_range_scalar_GL_two :
    Nat.card (MonoidHom.range
      (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (GaloisField 2 2)ˣ →*
          Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))) = 3 := by
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (GaloisField 2 2)ˣ →*
          Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) := by
    intro u v huv
    apply Units.ext
    have h := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) =>
      (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) 0 0) huv
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  have hcard := Nat.card_congr (Equiv.ofInjective _ hinj)
  rw [card_units_galoisField_two_two] at hcard
  exact hcard.symm

theorem card_eq_thirty_or_sixty_or_ninety_or_180 {n : ℕ}
    (h180 : n ∣ 180) (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h2 : 2 ∣ n)
    (hk : n / 3 ∣ 60) :
    n = 30 ∨ n = 60 ∨ n = 90 ∨ n = 180 := by
  obtain ⟨k, rfl⟩ := h3
  have hk' : k ∣ 60 := by
    have hdiv : 3 * k / 3 = k := Nat.mul_div_right k (m := 3) (by norm_num)
    rwa [hdiv] at hk
  have h5k : 5 ∣ k :=
    (by decide : Nat.Coprime 5 3).dvd_of_dvd_mul_left h5
  have h2k : 2 ∣ k :=
    (by decide : Nat.Coprime 2 3).dvd_of_dvd_mul_left h2
  have h10 : 10 ∣ k := by
    have := (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2k h5k
    simpa using this
  obtain ⟨m, hm⟩ := h10
  have hm6 : m ∣ 6 := by
    have h : 10 * m ∣ 10 * 6 := by
      rwa [show (60 : ℕ) = 10 * 6 by norm_num, hm] at hk'
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0] at hk'
      norm_num at hk'
    · exact hpos
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0] at hm
      simp at hm
      omega
    · exact hpos
  have hmle : m ≤ 6 := Nat.le_of_dvd (by norm_num) hm6
  interval_cases m
  · left; norm_num at hm; omega
  · right; left; norm_num at hm; omega
  · right; right; left; norm_num at hm; omega
  · exfalso; norm_num at hm6
  · exfalso; norm_num at hm6
  · right; right; right; norm_num at hm; omega

theorem isNatGL4_or_card_thirty_of_transitive {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H : Subgroup (MulAut W)}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hxgen : X = Subgroup.zpowers x)
    (hXcard : Nat.card X = 3) (hXG : X ≤ G)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (htrans : letI := galoisModule hw2 x hx3 hfix;
      ∀ L M : LineOf (K := GaloisField 2 2) (V := Additive W),
        ∃ h : ↥H, lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = M)
    (hd : ∃ d ∈ H, orderOf d = 2) :
    IsNatGL4 W H 2 ∨ Nat.card H = 30 := by
  subst hH
  classical
  letI := galoisModule hw2 x hx3 hfix
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  let H : Subgroup (MulAut W) :=
    G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  let f : ↥H →* Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
    { toFun := fun h => hGL hw2 x hx3 hfix (h : MulAut W)
        (hcommOf x G X hxgen h) hW
      map_one' := by
        exact hGL_one hw2 x hx3 hfix (hcommOf x G X hxgen 1) hW
      map_mul' := by
        intro h₁ h₂
        exact hGL_mul hw2 x hx3 hfix (h₁ : MulAut W) (h₂ : MulAut W)
          (hcommOf x G X hxgen h₁) (hcommOf x G X hxgen h₂)
          (hcommOf x G X hxgen (h₁ * h₂)) hW }
  have hGL_eq_one_imp_eq_one : ∀ {d : MulAut W} (hcd : d * x = x * d),
      hGL hw2 x hx3 hfix d hcd hW = 1 → d = 1 := by
    intro d hcd h1
    by_contra hne
    letI := galoisModule hw2 x hx3 hfix
    let b := galoisBasis hw2 x hx3 hfix hW
    have hfixb : ∀ j : Fin 2,
        hGaloisLinearEquiv hw2 x hx3 hfix d hcd (b j) = b j := by
      intro j
      rw [hGaloisLinearEquiv_apply]
      rw [hGL_expansion hw2 x hx3 hfix hW hcd j, h1]
      simp [b, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply]
    have hL : hGaloisLinearEquiv hw2 x hx3 hfix d hcd = 1 := by
      apply b.ext'
      intro j
      simpa using hfixb j
    exact hGaloisLinearEquiv_ne_one hw2 x hx3 hfix hcd hne hL
  have hfinj : Function.Injective f := by
    intro h₁ h₂ hEq
    apply Subtype.ext
    have hEq' : hGL hw2 x hx3 hfix (h₁ : MulAut W)
          (hcommOf x G X hxgen h₁) hW =
        hGL hw2 x hx3 hfix (h₂ : MulAut W)
          (hcommOf x G X hxgen h₂) hW := by
      simpa [f] using hEq
    let d : MulAut W := (h₁ : MulAut W) * (h₂ : MulAut W)⁻¹
    have hdH : d ∈ H := H.mul_mem h₁.2 (H.inv_mem h₂.2)
    have hcd : d * x = x * d := hcommOf x G X hxgen ⟨d, hdH⟩
    have hd2 : d * (h₂ : MulAut W) = (h₁ : MulAut W) := by
      dsimp [d]
      group
    have hGLd : hGL hw2 x hx3 hfix d hcd hW = 1 := by
      have hmul := hGL_mul hw2 x hx3 hfix d (h₂ : MulAut W) hcd
        (hcommOf x G X hxgen h₂)
        (hcommOf x G X hxgen ⟨d * (h₂ : MulAut W), H.mul_mem hdH h₂.2⟩) hW
      have hcongr : hGL hw2 x hx3 hfix (d * (h₂ : MulAut W))
            (hcommOf x G X hxgen ⟨d * (h₂ : MulAut W), H.mul_mem hdH h₂.2⟩) hW =
          hGL hw2 x hx3 hfix (h₁ : MulAut W) (hcommOf x G X hxgen h₁) hW :=
        hGL_congr hw2 x hx3 hfix hW _ _ hd2
      have hmain : hGL hw2 x hx3 hfix d hcd hW *
            hGL hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) hW =
          hGL hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) hW := by
        rw [← hmul, hcongr, hEq']
      have hmain' : hGL hw2 x hx3 hfix d hcd hW *
            hGL hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) hW =
          1 * hGL hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) hW := by
        simpa using hmain
      exact mul_right_cancel hmain'
    have hd1 : d = 1 := hGL_eq_one_imp_eq_one hcd hGLd
    calc (h₁ : MulAut W) = d * (h₂ : MulAut W) := hd2.symm
      _ = 1 * (h₂ : MulAut W) := by rw [hd1]
      _ = (h₂ : MulAut W) := one_mul _
  let det : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) →*
      (GaloisField 2 2)ˣ := Matrix.GeneralLinearGroup.det
  let g : ↥H →* (GaloisField 2 2)ˣ := det.comp f
  have hXH : X ≤ H := le_inf_centralizer_self hXG hXcard
  have hscalar : ∀ (a : MulAut W) (ha : a ∈ X),
      ∃ c : GaloisField 2 2, ∀ v : Additive W,
        hGaloisLinearEquiv hw2 x hx3 hfix a
          (hcommOf x G X hxgen ⟨a, hXH ha⟩) v = c • v := by
    intro a ha
    obtain ⟨c, hc⟩ :=
      X_scalar_of_transitive hw2 x hx3 hfix hW rfl hxgen hcommH htrans a ha
    refine ⟨c, fun v => ?_⟩
    convert hc v using 1
  have hfcenter : ∀ a : ↥X,
      f (Subgroup.inclusion hXH a) ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) := by
    intro a
    obtain ⟨c, hc⟩ := hscalar (a : MulAut W) a.2
    exact hGL_mem_center_of_scalar hw2 x hx3 hfix hW
      (hcommOf x G X hxgen ⟨(a : MulAut W), hXH a.2⟩) c hc
  let gX : ↥X →* Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2) :=
    f.comp (Subgroup.inclusion hXH)
  have hX'leS : gX.range ≤
      (MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (GaloisField 2 2)ˣ →* Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))) := by
    rintro _ ⟨a, rfl⟩
    have h := hfcenter a
    rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  have hX'card : Nat.card gX.range = 3 := by
    have hinj : Function.Injective gX := hfinj.comp (Subgroup.inclusion_injective hXH)
    have h := Nat.card_congr (Equiv.ofInjective gX hinj)
    rw [hXcard] at h
    exact h.symm
  have hS_card : Nat.card
      (MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (GaloisField 2 2)ˣ →* Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))) = 3 :=
    card_range_scalar_GL_two
  have hX'eqS : gX.range =
      (MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (GaloisField 2 2)ˣ →* Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2))) :=
    Subgroup.eq_of_le_of_card_ge hX'leS (by rw [hX'card, hS_card])
  have hsq_surj : Function.Surjective (fun u : (GaloisField 2 2)ˣ => u ^ 2) := by
    intro t
    refine ⟨t ^ 2, ?_⟩
    have ht3 : t ^ 3 = 1 := by
      have := pow_card_eq_one' (G := (GaloisField 2 2)ˣ) (x := t)
      rwa [card_units_galoisField_two_two] at this
    calc (t ^ 2) ^ 2 = t ^ (2 * 2) := by rw [pow_mul]
      _ = t ^ 4 := by norm_num
      _ = t ^ (3 + 1) := by norm_num
      _ = t ^ 3 * t := by rw [pow_add, pow_one]
      _ = 1 * t := by rw [ht3]
      _ = t := one_mul t
  have hdet_surj : Function.Surjective g := by
    intro t
    obtain ⟨u, hu⟩ := hsq_surj t
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ gX.range := by
      rw [hX'eqS]
      exact ⟨u, rfl⟩
    obtain ⟨a, ha⟩ := hmem
    refine ⟨Subgroup.inclusion hXH a, ?_⟩
    have hgval : g (Subgroup.inclusion hXH a) =
        Matrix.GeneralLinearGroup.det (gX a) := rfl
    rw [hgval, ha, Matrix.GeneralLinearGroup.det_scalar]
    simp only [Fintype.card_fin]
    exact hu
  have hg_range : g.range = ⊤ := MonoidHom.range_eq_top.mpr hdet_surj
  have hg_card_range : Nat.card g.range = 3 := by
    rw [hg_range, Subgroup.card_top]
    exact card_units_galoisField_two_two
  have hcard_ker : Nat.card g.ker * 3 = Nat.card H := by
    have h := Subgroup.card_ker_mul_card_range g
    rwa [hg_card_range] at h
  let B : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :=
    f.range ⊓ det.ker
  have hBcard : Nat.card B = Nat.card g.ker := by
    have hmap : (g.ker).map f = B := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        refine Subgroup.mem_inf.mpr ⟨⟨z, rfl⟩, ?_⟩
        rw [MonoidHom.mem_ker]
        simpa [g] using (MonoidHom.mem_ker.mp hz)
      · intro y hy
        rw [Subgroup.mem_inf] at hy
        obtain ⟨⟨z, rfl⟩, hz⟩ := hy
        rw [Subgroup.mem_map]
        refine ⟨z, ?_, rfl⟩
        rw [MonoidHom.mem_ker]
        simpa [g] using (MonoidHom.mem_ker.mp hz)
    rw [← hmap]
    exact Subgroup.card_map_of_injective hfinj
  have hB_le_SL : B ≤
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField 2 2)).range := by
    intro b hb
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact (Subgroup.mem_inf.mp hb).2
  let Bsl : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    B.comap (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField 2 2))
  have hBsl_card : Nat.card Bsl = Nat.card B := by
    have hmap : Bsl.map
        (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := GaloisField 2 2)) = B := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        rwa [Subgroup.mem_comap] at hz
      · intro y hy
        obtain ⟨z, hz⟩ := hB_le_SL hy
        rw [Subgroup.mem_map]
        refine ⟨z, ?_, hz⟩
        rw [Subgroup.mem_comap]
        rwa [hz]
    rw [← hmap]
    exact (Subgroup.card_map_of_injective
      (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2)
        (R := GaloisField 2 2))).symm
  have hH180 : Nat.card H ∣ 180 :=
    card_inf_centralizer_dvd_180 hw2 x hx3 hfix G X hxgen hW
  have hH3dvd : 3 ∣ Nat.card H := by
    have hXsubcard : Nat.card (X.subgroupOf H) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    rw [← hXcard, ← hXsubcard]
    exact (X.subgroupOf H).card_subgroup_dvd_card
  obtain ⟨d, hdH, hdord⟩ := hd
  have hH2dvd : 2 ∣ Nat.card H := by
    have hZle : Subgroup.zpowers d ≤ H := Subgroup.zpowers_le.mpr hdH
    have hZcard : Nat.card (Subgroup.zpowers d) = 2 := by
      rw [Nat.card_zpowers, hdord]
    have hZsubcard : Nat.card ((Subgroup.zpowers d).subgroupOf H) =
        Nat.card (Subgroup.zpowers d) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
    rw [← hZcard, ← hZsubcard]
    exact ((Subgroup.zpowers d).subgroupOf H).card_subgroup_dvd_card
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hcard5 : Nat.card (LineOf (K := GaloisField 2 2) (V := Additive W)) = 5 :=
    card_f4Line hw2 x hx3 hfix hW
  haveI : Fintype (LineOf (K := GaloisField 2 2) (V := Additive W)) := Fintype.ofFinite _
  haveI : Nonempty (LineOf (K := GaloisField 2 2) (V := Additive W)) := by
    rw [← Fintype.card_pos_iff, Fintype.card_eq_nat_card, hcard5]
    norm_num
  let L₀ : LineOf (K := GaloisField 2 2) (V := Additive W) := Classical.arbitrary _
  letI : MulAction ↥H (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
  { smul := fun h L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L
    one_smul := by
      intro L
      change lineMap (HLinHom hw2 x hx3 hfix H hcommH 1) L = L
      rw [map_one]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
      · intro hv
        exact ⟨v, hv, rfl⟩
    mul_smul := by
      intro h₁ h₂ L
      change lineMap (HLinHom hw2 x hx3 hfix H hcommH (h₁ * h₂)) L =
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h₁)
          (lineMap (HLinHom hw2 x hx3 hfix H hcommH h₂) L)
      rw [map_mul]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(HLinHom hw2 x hx3 hfix H hcommH h₂) w,
          ⟨w, hw, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, rfl⟩ }
  have horbit : MulAction.orbit ↥H L₀ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro M
    rw [MulAction.mem_orbit_iff]
    exact htrans L₀ M
  haveI : Fintype (MulAction.orbit ↥H L₀) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥H L₀) := Fintype.ofFinite _
  have hcard_orbit : Nat.card (MulAction.orbit ↥H L₀) = 5 := by
    calc Nat.card (MulAction.orbit ↥H L₀)
        = Nat.card (Set.univ : Set (LineOf (K := GaloisField 2 2) (V := Additive W))) :=
          Nat.card_congr (Set.equivOfEq horbit)
      _ = Nat.card (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
          Nat.card_congr (Equiv.Set.univ _)
      _ = 5 := hcard5
  have hstab := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥H) L₀
  have hstab' : 5 * Nat.card (MulAction.stabilizer ↥H L₀) = Nat.card H := by
    have h := hstab
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      Fintype.card_eq_nat_card] at h
    rw [hcard_orbit] at h
    simpa using h
  have hH5dvd : 5 ∣ Nat.card H :=
    ⟨Nat.card (MulAction.stabilizer ↥H L₀), hstab'.symm⟩
  have hk60 : Nat.card H / 3 ∣ 60 :=
    card_div_three_inf_centralizer_dvd_60 hw2 x hx3 hfix G X hxgen hW hXG hXcard
  have hcases := card_eq_thirty_or_sixty_or_ninety_or_180 hH180 hH3dvd hH5dvd hH2dvd hk60
  have hH3_eq : Nat.card H = 3 * Nat.card B := by
    rw [← hcard_ker, hBcard, mul_comm]
  rcases hcases with h30 | h60 | h90 | h180
  · right
    exact h30
  · exfalso
    have hB20 : Nat.card B = 20 := by omega
    have hBsl20 : Nat.card Bsl = 20 := by rw [hBsl_card, hB20]
    exact (CFSG.GroupTheory.SpecialLinear.sl2_four_no_subgroup_card_twenty_or_thirty Bsl).1
      hBsl20
  · exfalso
    have hB30 : Nat.card B = 30 := by omega
    have hBsl30 : Nat.card Bsl = 30 := by rw [hBsl_card, hB30]
    exact (CFSG.GroupTheory.SpecialLinear.sl2_four_no_subgroup_card_twenty_or_thirty Bsl).2
      hBsl30
  · left
    have hrange_top : (hGLHom hw2 x hx3 hfix G X hxgen hW).range = ⊤ := by
      have hinj := hGLHom_injective hw2 x hx3 hfix G X hxgen hW
      have hcard_range : Nat.card (hGLHom hw2 x hx3 hfix G X hxgen hW).range =
          Nat.card H := by
        have h := Nat.card_congr (Equiv.ofInjective _ hinj)
        exact h.symm
      apply Subgroup.eq_top_of_card_eq
      rw [hcard_range, h180, card_GL_two_galoisField_two]
    have hsurj : Function.Surjective (hGLHom hw2 x hx3 hfix G X hxgen hW) :=
      MonoidHom.range_eq_top.mp hrange_top
    exact isNatGL4_of_surjective hw2 x hx3 hfix G X hxgen hW hsurj

end CFSG.LocalAnalysis.WeakClosure81
