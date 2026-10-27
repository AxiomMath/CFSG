module

public import CFSG.Quasithin.Vol2.KGNatSL3ParIn

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

section General

variable {W : Type*} [CommGroup W]

theorem fix_of_perfect {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hL : ⁅L, L⁆ = L)
    (hZ : ∀ h ∈ L, ∀ z ∈ Z, h z = z) (hU : ∀ h ∈ L, ∀ u ∈ U, h u * u⁻¹ ∈ Z) :
    ∀ h ∈ L, ∀ u ∈ U, h u = u := by
  let C : Subgroup (MulAut W) :=
    { carrier := {h | ∀ u ∈ U, h u = u}
      mul_mem' := fun {a b} ha hb u hu => by rw [MulAut.mul_apply, hb u hu, ha u hu]
      one_mem' := fun u _ => rfl
      inv_mem' := fun {a} ha u hu => by
        conv_lhs => rw [← ha u hu]
        exact MulAut.inv_apply_self W a u }
  have hle : ⁅L, L⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha b hb u hu
    obtain ⟨za, hza, hau⟩ : ∃ za ∈ Z, a u = za * u := ⟨a u * u⁻¹, hU a ha u hu, by group⟩
    obtain ⟨zb, hzb, hbu⟩ : ∃ zb ∈ Z, b u = zb * u := ⟨b u * u⁻¹, hU b hb u hu, by group⟩
    have hai : a⁻¹ u = za⁻¹ * u := by
      have h1 : a (za⁻¹ * u) = u := by rw [map_mul, map_inv, hZ a ha za hza, hau]; group
      calc a⁻¹ u = a⁻¹ (a (za⁻¹ * u)) := by rw [h1]
        _ = za⁻¹ * u := MulAut.inv_apply_self W a _
    have hbi : b⁻¹ u = zb⁻¹ * u := by
      have h1 : b (zb⁻¹ * u) = u := by rw [map_mul, map_inv, hZ b hb zb hzb, hbu]; group
      calc b⁻¹ u = b⁻¹ (b (zb⁻¹ * u)) := by rw [h1]
        _ = zb⁻¹ * u := MulAut.inv_apply_self W b _
    show (a * b * a⁻¹ * b⁻¹) u = u
    have e1 := hZ a ha za hza
    have e2 := hZ a ha zb hzb
    have e3 := hZ b hb za hza
    have e4 := hZ b hb zb hzb
    have e5 := hZ _ (L.inv_mem ha) zb hzb
    simp only [MulAut.mul_apply, hbi, map_mul, map_inv, e5, hai, e3, e4, hbu, e1, e2, hau]
    rw [mul_left_comm za⁻¹ zb, inv_mul_cancel_left, inv_mul_cancel_left]
  intro h hh u hu
  rw [← hL] at hh
  exact hle hh u hu

theorem maps_fixV {H : Subgroup (MulAut W)} {x : MulAut W} (hx : ∀ h ∈ H, x⁻¹ * h * x ∈ H) :
    ∀ z ∈ fixV H, x z ∈ fixV H := by
  intro z hz h hh
  have h1 : (x⁻¹ * h * x) z = z := hz _ (hx h hh)
  rw [MulAut.mul_apply, MulAut.mul_apply] at h1
  calc h (x z) = x (x⁻¹ (h (x z))) := (MulAut.apply_inv_self W x _).symm
    _ = x z := by rw [h1]

theorem eq_one_of_commV {H : Subgroup (MulAut W)} (hW : commV H = ⊤) {τ : MulAut W}
    (hτH : ∀ x ∈ H, τ * x = x * τ) (hτ : ∀ w, τ w * w⁻¹ ∈ fixV H) : τ = 1 := by
  let C : Subgroup W :=
    { carrier := {w | τ w = w}
      mul_mem' := fun {a b} ha hb => by
        change τ (a * b) = a * b
        rw [map_mul, show τ a = a from ha, show τ b = b from hb]
      one_mem' := map_one τ
      inv_mem' := fun {a} ha => by
        change τ a⁻¹ = a⁻¹
        rw [map_inv, show τ a = a from ha] }
  have hle : commV H ≤ C := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    change τ (x v * v⁻¹) = x v * v⁻¹
    have hz := hτ v
    have hxz : x (τ v * v⁻¹) = τ v * v⁻¹ := hz x hx
    have hτx : τ (x v) = x (τ v) := by
      rw [← MulAut.mul_apply, hτH x hx, MulAut.mul_apply]
    rw [map_mul, map_inv, hτx]
    rw [map_mul, map_inv] at hxz
    calc x (τ v) * (τ v)⁻¹ = (x (τ v) * (x v)⁻¹) * (x v * (τ v)⁻¹) := by group
      _ = (τ v * v⁻¹) * (x v * (τ v)⁻¹) := by rw [hxz]
      _ = x v * v⁻¹ := by
        rw [mul_comm (x v) (τ v)⁻¹, mul_assoc, ← mul_assoc v⁻¹, mul_comm v⁻¹ (τ v)⁻¹,
          mul_assoc, ← mul_assoc (τ v), mul_inv_cancel, one_mul, mul_comm]
  ext w
  have : w ∈ C := hle (hW ▸ Subgroup.mem_top w)
  exact this

end General

section SL3

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

omit [Finite K] in
theorem commute_of_trivial_mod (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    {τ : MulAut W} (hτN : ∀ x ∈ H, τ * x * τ⁻¹ ∈ H) (hτ : ∀ w, f (τ w) = f w) :
    ∀ x ∈ H, τ * x = x * τ := by
  have hτi : ∀ w, f (τ⁻¹ w) = f w := fun w => by
    rw [← hτ (τ⁻¹ w), MulAut.apply_inv_self]
  intro x hx
  obtain ⟨X, hX⟩ := (rho3_bijective hf).2 ⟨x, hx⟩
  have hxv : ∀ v, f (x v) = (X : Matrix (Fin 3) (Fin 3) K) *ᵥ f v := fun v => by
    have h1 := hf.act3 X v
    rwa [hX] at h1
  have hxi : ∀ v, f (x⁻¹ v) =
      ((X⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f v := fun v => by
    have h1 := hxv (x⁻¹ v)
    rw [MulAut.apply_inv_self] at h1
    rw [h1, ginv_g_mulVec]
  have hcH : τ * x * τ⁻¹ * x⁻¹ ∈ H := H.mul_mem (hτN x hx) (H.inv_mem hx)
  obtain ⟨C, hC⟩ := (rho3_bijective hf).2 ⟨_, hcH⟩
  have hC1 : C = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← hf.act3, hC]
    change f ((τ * x * τ⁻¹ * x⁻¹) w) = f w
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hτ, hxv, hτi, hxi, g_ginv_mulVec]
  have h1 : τ * x * τ⁻¹ * x⁻¹ = 1 := by
    have h2 := congrArg Subtype.val hC
    rw [hC1, map_one] at h2
    exact h2.symm
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

variable [CharP K 2]

theorem factParSL3_holds : Ch11.SecB.FactParSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hfixV hcommV P hP U hU S hS2 hSH hSU _
  subst hfixV
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  have ha : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u = u :=
    fix_of_perfect (U := U) (Z := fixV H) (perfectCore_perfect _)
      (fun h hh z hz => mem_fixV.mp hz h (perfectCore_le _ hh).1)
      (factPointSL3_holds K n hn hK W hW H (fixV H) π hπ P hP U hU)
  refine ⟨ha, fun s hs hcomm u hu => ?_⟩
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  have hU' : Ch11.SecA.IsFlagW H P (fixV H) (Nat.card K) 1 U := by rw [hK]; exact hU
  have hUeq := eq_U1_of_isFlagW hW hf hg hU'
  subst hUeq
  have hs' : ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun h hh => by
    have := hSH s⁻¹ (S.inv_mem hs) h hh
    rwa [inv_inv] at this
  have hs'' : ∀ h ∈ H, s⁻¹⁻¹ * h * s⁻¹ ∈ H := fun h hh => by
    rw [inv_inv]
    exact hSH s hs h hh
  have hsZ : ∀ z ∈ fixV H, s z ∈ fixV H := maps_fixV hs'
  have he0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 s hsZ (maps_fixV hs'') hs'
  have hσid := sigma_eq_id_of_centralizes hSL hf g hsZ (hSU hs) hcomm hσ
  have hTf : ∀ w, hf.autMap s hsZ (f w) = f (s w) := hf.autMap_apply s hsZ
  let TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := hf.autMap s hsZ
      map_add' := map_add _
      map_smul' := fun c v => by rw [hσ, hσid]; rfl }
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  set A := LinearMap.toMatrix' TL with hA
  have hAv : ∀ w, A *ᵥ f w = f (s w) := fun w => by
    rw [hA, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    exact hTf w
  have hpow : ∀ j : ℕ, ∀ w, (A ^ j) *ᵥ f w = f ((s ^ j) w) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, Matrix.one_mulVec, MulAut.one_apply]
    | succ j ih =>
      intro w
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih, hAv, MulAut.mul_apply]
  have hA1 : A ^ 2 ^ m = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hpow, hm', MulAut.one_apply, Matrix.one_mulVec]
  have hdet : A.det = 1 :=
    eq_one_of_pow_two_pow (by rw [← Matrix.det_pow, hA1, Matrix.det_one])
  set B : SpecialLinearGroup (Fin 3) K := ⟨A, hdet⟩ with hBdef
  have hsB : ∀ w, f (s w) = f (((rho3 π B : ↥H) : MulAut W) w) := fun w => by
    rw [hf.act3, ← hAv]
  have hhi : (((rho3 π B : ↥H) : MulAut W))⁻¹ = ((rho3 π B⁻¹ : ↥H) : MulAut W) := by
    rw [map_inv, Subgroup.coe_inv]
  have hτ : ∀ w, f ((((rho3 π B : ↥H) : MulAut W)⁻¹ * s) w) = f w := by
    intro w
    rw [MulAut.mul_apply, hhi, hf.act3, hsB, hf.act3, ginv_g_mulVec]
  have hτN : ∀ x ∈ H, ((((rho3 π B : ↥H) : MulAut W))⁻¹ * s) * x *
      ((((rho3 π B : ↥H) : MulAut W))⁻¹ * s)⁻¹ ∈ H := by
    intro x hx
    have h1 : s * x * s⁻¹ ∈ H := hSH s hs x hx
    rw [show ((((rho3 π B : ↥H) : MulAut W))⁻¹ * s) * x *
        ((((rho3 π B : ↥H) : MulAut W))⁻¹ * s)⁻¹ =
        (((rho3 π B : ↥H) : MulAut W))⁻¹ * (s * x * s⁻¹) * ((rho3 π B : ↥H) : MulAut W) by
      group]
    exact H.mul_mem (H.mul_mem (H.inv_mem (rho3 π B).2) h1) (rho3 π B).2
  have hτ1 := eq_one_of_commV hcommV (commute_of_trivial_mod hf hτN hτ)
    (fun w => (hf.ker _).mp (by rw [hf.map_mul_inv, hτ, sub_self]))
  have hsh : ((rho3 π B : ↥H) : MulAut W) = s := inv_mul_eq_one.mp hτ1
  have hUmem : ∀ w, w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup ↔
      ∃ t : K, f w = t • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := fun w => by
    rw [← stdLine_eq_flagSpace]
    exact mem_gmap_stdLine_iff
  obtain ⟨u₀, hu₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have hu₀U := (hUmem u₀).mpr ⟨1, by rw [hu₀, one_smul]⟩
  obtain ⟨t, ht⟩ := (hUmem _).mp ((Ch11.SecA.mem_stabW.mp (hSU hs) u₀).mp hu₀U)
  have hB' : ((g⁻¹ * B * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![1, 0, 0] = t • ![1, 0, 0] := by
    rw [← mulVec_gconj, ← hu₀, ← hf.act3, hsh, ht, Matrix.mulVec_smul, ginv_g_mulVec]
  have hBpow : B ^ 2 ^ m = 1 :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact hA1)
  have hB'pow : (g⁻¹ * B * g) ^ 2 ^ m = 1 := by
    rw [show g⁻¹ * B * g = g⁻¹ * B * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hBpow, mul_one,
      mul_inv_cancel]
  have hiter : ∀ j : ℕ, (((g⁻¹ * B * g) ^ j : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = t ^ j • ![1, 0, 0] := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
        one_smul]
    | succ j ih =>
      rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ih,
        Matrix.mulVec_smul, hB', smul_smul, ← pow_succ]
  have ht1 : t = 1 := by
    have h1 := hiter (2 ^ m)
    rw [hB'pow, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
    have h2 := congrFun h1 0
    simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_one] at h2
    exact eq_one_of_pow_two_pow h2.symm
  rw [ht1, one_smul] at hB'
  have hsL : s ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) := by
    refine (mem_perfectCore_HU1_iff hSL hf g s).mpr ⟨g⁻¹ * B * g, hB', ?_⟩
    rw [show g * (g⁻¹ * B * g) * g⁻¹ = B by group, hsh]
  exact ha s hsL u hu

end SL3

end CFSG.Quasithin.Vol2.KGNat
