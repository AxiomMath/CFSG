module

public import CFSG.RankThree.GF2n.Stroth80.Sec53bProd
public import CFSG.RankThree.GF2n.Stroth80.Sec52bProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_mul_card_inf_of_prod {A B D : Subgroup G} (hA : A ≤ D) (hB : B ≤ D)
    (hprod : ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, d = a * b) :
    Nat.card D * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := CFSG.Quasithin.H13.GM22.card_mul_set_mul_card_inf A B
  have heq : (A : Set G) * (B : Set G) = (D : Set G) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact D.mul_mem (hA ha) (hB hb)
    · intro d hd
      obtain ⟨a, ha, b, hb, rfl⟩ := hprod d hd
      exact ⟨a, ha, b, hb, rfl⟩
  rw [heq] at h1
  exact h1

theorem Ctx.exists_mul_of_mem_Vt_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ∃ a ∈ Vt M (LB M Q B) B Z t ⊓ QB B,
      ∃ b ∈ Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B), v = a * b := by
  classical
  obtain ⟨K₁, iF, iFin, hK, hrep⟩ := hV
  letI := iF
  letI := iFin
  haveI : CharP K₁ 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hnat : SpNat hc t := ⟨K₁, iF, iFin, hK, m, hm, hrep⟩
  obtain ⟨φ, hφ, hker, hact⟩ := hrep
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ₂, M₀₂, hD₂, θ, hθ, u₀, hu₀, hBiff₀, hW₀⟩ :=
    Ctx.sp_perp_data h34 hc hs hnotQB hK hm φ hφ hker ψ hψ
  obtain ⟨u₁, hu₁, hBiff₁, hL₁, hplane₁⟩ :=
    Ctx.sp_points_core h34 hRoot hc hs hK hm φ hφ hker ψ hψ
  obtain ⟨c, hc₁⟩ := (hBiff₀ u₁).mp ((hBiff₁ u₁).mpr ⟨1, (one_smul K₁ u₁).symm⟩)
  have hne₁ : spForm m K₁ u₁
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₁) ≠ 0 :=
    ((hplane₁ ⟨r, hr⟩).1).mp hplane
  have hne₀ : spForm m K₁ u₀
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀) ≠ 0 := by
    intro h0
    apply hne₁
    have hform : ∀ x y : Fin m ⊕ Fin m → K₁,
        spForm m K₁ x y = CFSG.Timmesfeld.ARS.CaseM.spForm x y := fun x y =>
      (spForm_apply x y).trans rfl
    rw [hc₁, Matrix.mulVec_smul]
    have hsc : spForm m K₁ (c • u₀)
        (c • ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀)) =
        c * (c * spForm m K₁ u₀
          ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀)) := by
      rw [hform (c • u₀) (c • _),
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left',
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right',
        ← hform u₀ _]
    rw [hsc, h0]
    simp
  have hW' := Ctx.sp_perp_conj_W hc hs φ hφ ψ hψ hr hW₀
  set u' : Fin m ⊕ Fin m → K₁ :=
    (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀ with hu'def
  have hspan_nat : (spForm m K₁).orthogonal (Submodule.span K₁ {u₀}) ⊔
      (spForm m K₁).orthogonal (Submodule.span K₁ {u'}) = ⊤ :=
    spForm_orthogonal_sup_eq_top hne₀
  have hmem_orth : ∀ w z : Fin m ⊕ Fin m → K₁,
      w ∈ (spForm m K₁).orthogonal (Submodule.span K₁ {z}) ↔ spForm m K₁ w z = 0 := by
    intro w z
    rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    rw [LinearMap.mem_ker]
    have hsym : ∀ a b : Fin m ⊕ Fin m → K₁,
        spForm m K₁ a b = 0 ↔ spForm m K₁ b a = 0 := by
      intro a b
      rw [← spForm_isAlt.neg_eq a b, neg_eq_zero]
    exact ⟨fun h => (hsym z w).mp h, fun h => (hsym w z).mp h⟩
  intro v hvV
  let v' : ↥(Vt M (LB M Q B) B Z t) := ⟨v, hvV⟩
  set x : Fin m ⊕ Fin m → K₁ := secVec ψ v' with hxdef
  have hxsum : x ∈ (spForm m K₁).orthogonal (Submodule.span K₁ {u₀}) ⊔
      (spForm m K₁).orthogonal (Submodule.span K₁ {u'}) := by
    rw [hspan_nat]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hxsum
  obtain ⟨a, ha, b, hb, hxab⟩ := hxsum
  have haW : spForm m K₁ a u₀ = 0 := (hmem_orth a u₀).mp ha
  have hbW : spForm m K₁ b u' = 0 := (hmem_orth b u').mp hb
  obtain ⟨a', ha', ha'x⟩ := (hW₀ a).mpr haW
  obtain ⟨b', hb', hb'x⟩ := (hW' b).mpr hbW
  have habV : (a' : G) * (b' : G) ∈ Vt M (LB M Q B) B Z t :=
    (Vt M (LB M Q B) B Z t).mul_mem a'.2 b'.2
  let w : ↥(Vt M (LB M Q B) B Z t) := ⟨(a' : G) * (b' : G), habV⟩
  have hsecw : secVec ψ w = x := by
    rw [show w = a' * b' from Subtype.ext rfl, secVec_mul, ha'x, hb'x]
    exact hxab
  have hz : (v' : G) * (w : G)⁻¹ ∈ Z :=
    (secVec_eq_iff ψ v' w).mp (by rw [hsecw])
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZB : Z ≤ QB B := hc.Z_le_QB.1
  refine ⟨((v' : G) * (w : G)⁻¹) * (a' : G),
    ⟨(Vt M (LB M Q B) B Z t).mul_mem (hZV hz) a'.2,
      (QB B).mul_mem (hZB hz) (Subgroup.mem_inf.mp ha').2⟩,
    (b' : G), Subgroup.mem_inf.mp hb' |> fun h => ⟨h.1, h.2⟩, ?_⟩
  show (v : G) = ((v' : G) * (w : G)⁻¹ * (a' : G)) * (b' : G)
  have e : (v : G) = ((v' : G) * (w : G)⁻¹) * ((a' : G) * (b' : G)) := by
    show (v : G) = ((v : G) * ((a' : G) * (b' : G))⁻¹) * ((a' : G) * (b' : G))
    group
  exact e.trans (by simp only [mul_assoc])

theorem card_Vt_inf_QB_inf_QB_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Nat.card ↥((Vt M (LB M Q B) B Z t ⊓ QB B) ⊓
        (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B))) * Nat.card Z ^ (2 * m + 1) =
      Nat.card Z ^ (2 * m) * Nat.card Z ^ (2 * m) := by
  have h := card_mul_card_inf_of_prod (A := Vt M (LB M Q B) B Z t ⊓ QB B)
    (B := Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)) (D := Vt M (LB M Q B) B Z t)
    inf_le_left inf_le_left (hc.exists_mul_of_mem_Vt_sp h34 hRoot hs hm hV hr hplane)
  rw [SpMNat.card_V hV, card_Vt_inf_QB_sp h34 hRoot hc hs hm hV,
    card_Vt_inf_QB_sp_conj h34 hRoot hc hs hm hV hr] at h
  exact (mul_comm _ _).trans h

theorem Ctx.card_QB_inf_Wt_pair (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) (hr : r ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n ∧
      Nat.card ↥(QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n := by
  have hAc : Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n :=
    sec53b_card_QB_inf_Wt_sp h34 hRoot hc hs hm hV
  exact ⟨hAc, (sec52b_card_QB_inf_Wt_conj hc hs hr).trans hAc⟩

private theorem Ctx.comm_of_mem_inf_QB (hc : Ctx M Q Z B) :
    ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem Ctx.QB_inf_Wt_le_Wt_vone (hc : Ctx M Q Z B) (C V : Subgroup G) :
    QB B ⊓ Wt Q V ≤ Wt Q (Vone Q B C V) := fun a ha =>
  mem_Wt_of_le_sup ha.2
    (fun s hs' => hc.comm_of_mem_inf_QB s hs' a ⟨(inf_le_left : Wt Q V ≤ Q) ha.2, ha.1⟩)
    inf_le_left

theorem Ctx.QB_inf_Wt_le_Wt_vone' {C : Subgroup G} (hcC : Ctx M Q Z C) (V : Subgroup G) :
    QB C ⊓ Wt Q V ≤ Wt Q (Vone Q B C V) := fun a ha =>
  mem_Wt_of_le_sup ha.2
    (fun s hs' => hcC.comm_of_mem_inf_QB s hs' a ⟨(inf_le_left : Wt Q V ≤ Q) ha.2, ha.1⟩)
    inf_le_right

theorem Ctx.card_Wt_vone_mul_pow (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hV : SpMNat hc t m) {C : Subgroup G} (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C))
    (hcard : Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z) :
    Nat.card ↥(Wt Q (Vone Q B C (Vt M (LB M Q B) B Z t))) * Nat.card Z ^ (2 * m) =
      Nat.card Z ^ (2 * n) := by
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hQ : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have h := hc.card_Wt_mul_card_vone hs hcC hnoC
  rw [hcard, SpMNat.card_V hV, hQ] at h
  refine Nat.eq_of_mul_eq_mul_right (pow_pos hq 2) ?_
  calc Nat.card ↥(Wt Q (Vone Q B C (Vt M (LB M Q B) B Z t))) * Nat.card Z ^ (2 * m) *
        Nat.card Z ^ 2
      = Nat.card ↥(Wt Q (Vone Q B C (Vt M (LB M Q B) B Z t))) *
        (Nat.card Z ^ (2 * m + 1) * Nat.card Z) := by ring
    _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z := h
    _ = Nat.card Z ^ (2 * n) * Nat.card Z ^ 2 := by ring

theorem vone_le_sup_of_prod {Q B C V : Subgroup G} (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hVQ : V ≤ Q) (hnorm : Q ≤ Subgroup.normalizer (V : Set G))
    (hVS : ∀ v ∈ V, ∃ a ∈ V ⊓ QB B, ∃ b ∈ V ⊓ QB C, v = a * b) :
    Vone Q B C V ≤ (QB B ⊓ QB C ⊓ Q) ⊔ V := by
  intro x hx
  obtain ⟨a, ha, v, hv, hxav⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (H := Q ⊓ QB B) (K := V) (fun y hy => hnorm hy.1) hx.1
  obtain ⟨c, hc, w, hw, hxcw⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (H := Q ⊓ QB C) (K := V) (fun y hy => hnorm hy.1) hx.2
  obtain ⟨vB, hvB, vC, hvC, hv'⟩ := hVS v hv
  obtain ⟨wB, hwB, wC, hwC, hw'⟩ := hVS w hw
  have hE : a * vB * vC = c * wB * wC := by
    calc a * vB * vC = a * v := by rw [hv', mul_assoc]
      _ = x := hxav
      _ = c * w := hxcw.symm
      _ = c * wB * wC := by rw [hw', mul_assoc]
  have hcomm : wB * (wC * vC⁻¹) = (wC * vC⁻¹) * wB :=
    hVab wB hwB.1 _ (V.mul_mem hwC.1 (V.inv_mem hvC.1))
  have hy : a * vB * wB⁻¹ = c * (wC * vC⁻¹) := by
    calc a * vB * wB⁻¹ = (a * vB * vC) * vC⁻¹ * wB⁻¹ := by group
      _ = (c * wB * wC) * vC⁻¹ * wB⁻¹ := by rw [hE]
      _ = c * (wB * (wC * vC⁻¹) * wB⁻¹) := by group
      _ = c * (wC * vC⁻¹) := by rw [hcomm]; group
  have hyB : a * vB * wB⁻¹ ∈ QB B :=
    (QB B).mul_mem ((QB B).mul_mem ha.2 hvB.2) ((QB B).inv_mem hwB.2)
  have hyC : a * vB * wB⁻¹ ∈ QB C := by
    rw [hy]
    exact (QB C).mul_mem hc.2 ((QB C).mul_mem hwC.2 ((QB C).inv_mem hvC.2))
  have hyQ : a * vB * wB⁻¹ ∈ Q :=
    Q.mul_mem (Q.mul_mem ha.1 (hVQ hvB.1)) (Q.inv_mem (hVQ hwB.1))
  have hxe : x = (a * vB * wB⁻¹) * (wB * vC) := by
    rw [← hxav, hv']
    group
  rw [hxe]
  exact Subgroup.mul_mem_sup ⟨⟨hyB, hyC⟩, hyQ⟩ (V.mul_mem hwB.1 hvC.1)

omit [Finite G] in
theorem sup_mul_comm_of_comm {X V : Subgroup G} (hXX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hXV : ∀ x ∈ X, ∀ v ∈ V, x * v = v * x) :
    ∀ a ∈ X ⊔ V, ∀ b ∈ X ⊔ V, a * b = b * a := by
  have h1 : ∀ x ∈ X, X ⊔ V ≤ Subgroup.centralizer {x} := fun x hx =>
    sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hXX y hy x hx))
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (hXV x hx v hv).symm)
  have h2 : ∀ v ∈ V, X ⊔ V ≤ Subgroup.centralizer {v} := fun v hv =>
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hXV x hx v hv))
      (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hVV w hw v hv))
  intro a ha b hb
  have hle : X ⊔ V ≤ Subgroup.centralizer {a} :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (h1 x hx ha)).symm)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (h2 v hv ha)).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm

theorem sec53_inf_QB_inf_QB_le_Wt (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hne : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t) :
    QB B ⊓ QB (conjSubgroup r B) ⊓ Q ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  obtain ⟨K, iF, iFin, iCh, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := iF
  letI := iFin
  letI := iCh
  let T : Submodule K M₀.E :=
    imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hD t)
  have hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun e => mem_imgSub
  have hBC := (Ctx.hBC_iff_vone_ne h34 hRoot h51 hc hs hm hV hr hplane hD T hTmem).mpr hne
  have hspan := Ctx.le_sup_imgQInfQB_sp_of_hplane h34 hRoot hc hs hm hV hr hplane hD T hTmem
  have hcard := Ctx.card_vone_sp_of_hBC h34 hRoot hc hs hm hV hr hD T hTmem hBC hspan
  have hAD := hc.QB_inf_Wt_le_Wt_vone (conjSubgroup r B) (Vt M (LB M Q B) B Z t)
  have hCD := hcC.QB_inf_Wt_le_Wt_vone' (B := B) (Vt M (LB M Q B) B Z t)
  have hDc := hc.card_Wt_vone_mul_pow hs hV hcC hnoC hcard
  have hprod := sec53b_prod_of_model_count h34 hRoot hc hs hm hV hr hD hBC hAD hCD hDc
  obtain ⟨hAc, hCc⟩ := Ctx.card_QB_inf_Wt_pair h34 hRoot hc hs hm hV hr
  have hI := card_mul_card_inf_of_prod hAD hCD hprod
  have hIeq : Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) = Nat.card Z ^ (2 * m) := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos
      (α := ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))))) ?_
    calc Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
          Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
            (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)))
        = Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) *
          Nat.card ↥(QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) := hI
      _ = Nat.card Z ^ n * Nat.card Z ^ n := by rw [hAc, hCc]
      _ = Nat.card Z ^ (2 * n) := by rw [← pow_add, two_mul]
      _ = Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
          Nat.card Z ^ (2 * m) := hDc.symm
  have hX := hc.card_le_of_le_inf_QB_inf_QB hs hcC hnoC hD
    (Y := QB B ⊓ QB (conjSubgroup r B) ⊓ Q)
    (le_inf (le_inf hc.Z_le_QB.1 hcC.Z_le_QB.1) hc.Z_le_Q) inf_le_right
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) hBC
  have hle : (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ≤
      QB B ⊓ QB (conjSubgroup r B) ⊓ Q := fun y hy =>
    ⟨⟨hy.1.1, hy.2.1⟩, (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hy.1.2⟩
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hIeq]; exact hX)
  intro y hy
  have hy' : y ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) := heq.ge hy
  exact hy'.1.2

theorem sec53_vone_le_Wt_vone (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hne : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t) :
    Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≤
      Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVW := sec7ctr_Vt_le_Wt h34 hc hs
  have hVab : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ w ∈ Vt M (LB M Q B) B Z t, v * w = w * v :=
    fun v hv w hw => (Subgroup.mem_centralizer_iff.mp (hVW hv).2 w hw).symm
  have hQV : Q ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hx' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hVQ hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hx') hy
  have hF5 := sec53_inf_QB_inf_QB_le_Wt h34 hRoot h51 hc hs hm hV hr hplane hne
  have hL4 := vone_le_sup_of_prod hVab hVQ hQV
    (hc.exists_mul_of_mem_Vt_sp h34 hRoot hs hm hV hr hplane)
  have hcommQB : ∀ x ∈ QB B ⊓ QB (conjSubgroup r B) ⊓ Q, ∀ y ∈ QB B ⊓ QB (conjSubgroup r B) ⊓ Q,
      x * y = y * x := fun x hx y hy =>
    hc.comm_of_mem_inf_QB x ⟨hx.2, hx.1.1⟩ y ⟨hy.2, hy.1.1⟩
  have hcomm := sup_mul_comm_of_comm hcommQB hVab (fun x hx v hv =>
    ((Subgroup.mem_centralizer_iff.mp (hF5 hx).2 v hv)).symm)
  intro v hv
  exact ⟨vone_le_Q hVQ hv, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    hcomm y (hL4 hy) v (hL4 hv)⟩

theorem stroth53VW_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  obtain ⟨K₀, iF₀, iFin₀, hK₀, m, hm, hrep₀⟩ := hsp
  by_cases hE : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t
  · show Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≤
      Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))
    rw [hE]
    exact sec7ctr_Vt_le_Wt h34 hc hs
  · exact sec53_vone_le_Wt_vone h34 hRoot h51 hc hs hm ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩ hr hplane hE

theorem stroth53Inf_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊓
          ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ≤
          Sec8V1 M Q Z B t r := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  refine le_inf (inf_le_left.trans ?_) (inf_le_right.trans ?_)
  · refine sup_le (fun x hx => Subgroup.mem_sup_left ⟨?_, hx.1⟩) ?_
    · exact (inf_le_left : Wt Q _ ≤ Q) hx.2
    · exact inf_le_left
  · refine sup_le (fun x hx => Subgroup.mem_sup_left ⟨?_, hx.1⟩) ?_
    · exact (inf_le_left : Wt Q _ ≤ Q) hx.2
    · exact inf_le_right

end CFSG.RankThree.GF2n.Stroth80
