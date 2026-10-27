module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {d u₁ z : G}

omit [Finite G] in
theorem matrix_eq_of_cols_ch611 {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ j, A.col j = B.col j) : A = B :=
  Matrix.ext fun i j => congrFun (h j) i

namespace Data611

variable (D : Data611 G T M L V d u₁ z)
include D

theorem V_le_H : V ≤ hCh611 T := D.hyp.V_le_hCh611

theorem basis0 : (D.basis 0 : G) = z := rfl

theorem basis1 : (D.basis 1 : G) = d * z * d⁻¹ := rfl

theorem basis2 : (D.basis 2 : G) = u₁ := rfl

theorem basis3 : (D.basis 3 : G) = d * u₁ * d⁻¹ := rfl

theorem kv_e0 : D.kv ![1, 0, 0, 0] = z := by rw [D.kv_vec]; simp [zv1]

theorem kv_e1 : D.kv ![0, 1, 0, 0] = d * z * d⁻¹ := by rw [D.kv_vec]; simp [zv1]

theorem kv_ZS_mul {x : G} (hx : x ∈ ch6ZS T L V) (c₂ c₃ : ZMod 2) :
    ∃ a b : ZMod 2, x * (u₁ ^ c₂.val * (d * u₁ * d⁻¹) ^ c₃.val) = D.kv ![a, b, c₂, c₃] := by
  obtain ⟨a, b, rfl⟩ := (D.mem_ZS_iff).mp hx
  refine ⟨a, b, ?_⟩
  rw [D.kv_vec]
  group

theorem col0_of_mem_H {g : G} (hg : g ∈ hCh611 T) {A : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : D.IsMat g A) : A.col 0 = ![1, 0, 0, 0] := by
  apply D.kv_injective
  rw [D.kv_col h, D.kv_e0, D.basis0, ← Subgroup.mem_centralizer_iff.mp hg z D.zZ,
    mul_inv_cancel_right]

omit [Group G] [Finite G] D in
theorem vY_cols (a b c e : ZMod 2) :
    (vYCh611 a b c e).col 0 = ![1, 0, 0, 0] ∧ (vYCh611 a b c e).col 1 = ![0, 1, 0, 0] ∧
      (vYCh611 a b c e).col 2 = ![a, c, 1, 0] ∧ (vYCh611 a b c e).col 3 = ![b, e, 0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> rfl

theorem isMat_conj_d {g : G} {A : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A) :
    D.IsMat (d * g * d⁻¹) (matDCh611 * A * (matDCh611 * matDCh611)) ∧
    D.IsMat (d * (d * g * d⁻¹) * d⁻¹) (matDCh611 * matDCh611 * A * matDCh611) := by
  have hdi := D.isMat_inv D.isMat_d matDCh611_pow
  have h1 := D.isMat_mul (D.isMat_mul D.isMat_d h) hdi
  refine ⟨h1, ?_⟩
  have h2 := D.isMat_mul (D.isMat_mul D.isMat_d h1) hdi
  have hD4 : matDCh611 * matDCh611 * (matDCh611 * matDCh611) = matDCh611 := by decide
  have e : matDCh611 * (matDCh611 * A * (matDCh611 * matDCh611)) * (matDCh611 * matDCh611) =
      matDCh611 * matDCh611 * A * matDCh611 := by
    calc matDCh611 * (matDCh611 * A * (matDCh611 * matDCh611)) * (matDCh611 * matDCh611)
        = matDCh611 * matDCh611 * A * (matDCh611 * matDCh611 * (matDCh611 * matDCh611)) := by
          simp only [Matrix.mul_assoc]
      _ = matDCh611 * matDCh611 * A * matDCh611 := by rw [hD4]
  rwa [e] at h2

theorem isMat_v {v : G} (hv : v ∈ V) : ∃ i, D.IsMat v (vhatCh611 i) := by
  have hV := D.hyp.toHyp611.isElemAbelian
  have hvH := D.V_le_H hv
  obtain ⟨A, hA⟩ := D.exists_isMat (hCh611_le_normalizer_u T L V hvH)
  have hzV : z ∈ V := ZS_le_V D.zS
  have hz'V : d * z * d⁻¹ ∈ V := ZS_le_V D.z'_mem
  have hfix : ∀ x ∈ V, v * x * v⁻¹ = x := fun x hx => by
    rw [B2F.isElemAbelian_comm hV hv hx, mul_inv_cancel_right]
  have c0 : A.col 0 = ![1, 0, 0, 0] := D.col0_of_mem_H hvH hA
  have c1 : A.col 1 = ![0, 1, 0, 0] := by
    apply D.kv_injective
    rw [D.kv_col hA, D.kv_e1, D.basis1, hfix _ hz'V]
  have hu₂U : d * u₁ * d⁻¹ ∈ uCh611 T L V := D.conj_d_mem D.u₁U
  obtain ⟨a, c, hac⟩ := D.kv_ZS_mul (D.vuc v hv u₁ D.u₁U) 1 0
  obtain ⟨b, e, hbe⟩ := D.kv_ZS_mul (D.vuc v hv _ hu₂U) 0 1
  have c2 : A.col 2 = ![a, c, 1, 0] := by
    apply D.kv_injective
    rw [D.kv_col hA, D.basis2, ← hac, zv1, zv0, pow_one, pow_zero, mul_one]
    group
  have c3 : A.col 3 = ![b, e, 0, 1] := by
    apply D.kv_injective
    rw [D.kv_col hA, D.basis3, ← hbe, zv1, zv0, pow_one, pow_zero, one_mul]
    group
  have hAeq : A = vYCh611 a b c e := by
    obtain ⟨y0, y1, y2, y3⟩ := vY_cols a b c e
    refine matrix_eq_of_cols_ch611 fun j => ?_
    fin_cases j
    · exact c0.trans y0.symm
    · exact c1.trans y1.symm
    · exact c2.trans y2.symm
    · exact c3.trans y3.symm
  obtain ⟨h1, h2⟩ := D.isMat_conj_d hA
  have hprod := D.isMat_mul (D.isMat_mul hA h1) h2
  have hone := D.orbit_prod (X := V) (fun a ha b hb => B2F.isElemAbelian_comm hV ha hb)
    (D.hyp.data.le_normalizer D.dL) (fun x hx hdx => D.dV x hx hdx) hv
  rw [hone] at hprod
  have hrel := D.isMat_unique hprod D.isMat_one
  rw [hAeq] at hrel
  obtain ⟨i, hi⟩ := vYCh611_mem_of_orbit a b c e hrel
  exact ⟨i, by rw [← hi, ← hAeq]; exact hA⟩

theorem exists_v (i : Fin 4) : ∃ v ∈ V, D.IsMat v (vhatCh611 i) := by
  classical
  by_cases hi : i = 0
  · subst hi
    exact ⟨1, V.one_mem, D.isMat_one⟩
  obtain ⟨v₀, hv₀, hv₀Z⟩ : ∃ v ∈ V, v ∉ ch6ZS T L V := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show V ≤ ch6ZS T L V from hcon)
    rw [D.card_ZS, D.hyp.natural.card_eq] at this
    norm_num at this
  obtain ⟨i₀, hi₀⟩ := D.isMat_v hv₀
  have hi₀0 : i₀ ≠ 0 := by
    rintro rfl
    exact hv₀Z (D.vc v₀ hv₀ ((D.mem_centralizer_iff_isMat hi₀).mpr rfl))
  obtain ⟨h1, h2⟩ := D.isMat_conj_d hi₀
  have hdV := D.hyp.data.le_normalizer D.dL
  have hv₁ : d * v₀ * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdV v₀).mp hv₀
  have hv₂ : d * (d * v₀ * d⁻¹) * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hdV _).mp hv₁
  rcases vhatCh611_orbit i₀ i hi₀0 hi with e | e | e
  · exact ⟨v₀, hv₀, e ▸ hi₀⟩
  · exact ⟨_, hv₁, e ▸ h1⟩
  · exact ⟨_, hv₂, e ▸ h2⟩

omit [Group G] [Finite G] D in
theorem uni_cols (x : Fin 6 → ZMod 2) :
    (uniCh611 x).col 0 = ![1, 0, 0, 0] ∧ (uniCh611 x).col 1 = ![x 0, 1, 0, 0] ∧
      (uniCh611 x).col 2 = ![x 1, x 3, 1, 0] ∧ (uniCh611 x).col 3 = ![x 2, x 4, x 5, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> rfl

theorem isMat_t {t : G} (ht : t ∈ T) : ∃ x, D.IsMat t (uniCh611 x) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have htH : t ∈ hCh611 T := T_le_hCh611 T ht
  obtain ⟨A, hA⟩ := D.exists_isMat (hCh611_le_normalizer_u T L V htH)
  have c0 := D.col0_of_mem_H htH hA
  have hTZ := D.hyp.toHyp611Nat.T_le_normalizer_ZS ht
  have hz't : t * (d * z * d⁻¹) * t⁻¹ ∈ ch6ZS T L V :=
    (Subgroup.mem_normalizer_iff.mp hTZ _).mp D.z'_mem
  obtain ⟨a, b, hab⟩ := (D.mem_ZS_iff).mp hz't
  obtain ⟨hz'1, hz'z⟩ := D.z'_ne
  have hb : b = 1 := by
    rcases hz b with rfl | rfl
    · exfalso
      rw [zv0, pow_zero, mul_one] at hab
      rcases hz a with rfl | rfl
      · rw [zv0, pow_zero] at hab
        apply hz'1
        have := congrArg (fun y => t⁻¹ * y * t) hab
        simpa [mul_assoc] using this
      · rw [zv1, pow_one] at hab
        apply hz'z
        have h1 : t * z * t⁻¹ = z := by
          rw [← Subgroup.mem_centralizer_iff.mp htH z D.zZ, mul_inv_cancel_right]
        have := congrArg (fun y => t⁻¹ * y * t) (hab.trans h1.symm)
        simpa [mul_assoc] using this
    · rfl
  have c1 : A.col 1 = ![a, 1, 0, 0] := by
    apply D.kv_injective
    rw [D.kv_col hA, D.basis1, hab, hb, D.kv_vec, zv0, zv1]
    group
  obtain ⟨a', b', hab'⟩ := D.kv_ZS_mul (D.u₁T t ht) 1 0
  have c2 : A.col 2 = ![a', b', 1, 0] := by
    apply D.kv_injective
    rw [D.kv_col hA, D.basis2, ← hab', zv1, zv0, pow_one, pow_zero, mul_one]
    group
  set c := A.col 3 with hc
  obtain ⟨A', hA'⟩ := D.exists_isMat (hCh611_le_normalizer_u T L V ((hCh611 T).inv_mem htH))
  have hAA' : A * A' = 1 := by
    have := D.isMat_mul hA hA'
    rw [mul_inv_cancel] at this
    exact D.isMat_unique this D.isMat_one
  have hc3 : c 3 = 1 := by
    rcases hz (c 3) with h3 | h3
    · exfalso
      have hrow : ∀ k, A 3 k = 0 := by
        intro k
        fin_cases k
        · exact congrFun c0 3
        · exact congrFun c1 3
        · exact congrFun c2 3
        · exact h3
      have := congrFun (congrFun hAA' 3) 3
      rw [Matrix.mul_apply] at this
      simp [hrow] at this
    · exact h3
  refine ⟨![a, a', c 0, b', c 1, c 2], ?_⟩
  have hAeq : A = uniCh611 ![a, a', c 0, b', c 1, c 2] := by
    obtain ⟨y0, y1, y2, y3⟩ := uni_cols ![a, a', c 0, b', c 1, c 2]
    refine matrix_eq_of_cols_ch611 fun j => ?_
    fin_cases j
    · exact c0.trans y0.symm
    · exact c1.trans y1.symm
    · exact c2.trans y2.symm
    · show c = (uniCh611 ![a, a', c 0, b', c 1, c 2]).col 3
      rw [y3]
      ext i
      fin_cases i <;> simp [hc3]
  rw [← hAeq]
  exact hA

theorem eq_of_sameMod {g g' : G} (hg : g ∈ hCh611 T) (hg' : g' ∈ hCh611 T)
    {A A' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : D.IsMat g A) (h' : D.IsMat g' A')
    (hs : SameModCh611 A A') : A = A' := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hw : ∀ c, ∃ a : ZMod 2, A.mulVec c = A'.mulVec c + ![a, 0, 0, 0] := by
    intro c
    refine ⟨A.mulVec c 0 + A'.mulVec c 0, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hs
    ext i
    fin_cases i
    · show A.mulVec c 0 = A'.mulVec c 0 + (A.mulVec c 0 + A'.mulVec c 0)
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    · show A.mulVec c 1 = A'.mulVec c 1 + 0
      rw [add_zero]; simp only [Matrix.mulVec, h1]
    · show A.mulVec c 2 = A'.mulVec c 2 + 0
      rw [add_zero]; simp only [Matrix.mulVec, h2]
    · show A.mulVec c 3 = A'.mulVec c 3 + 0
      rw [add_zero]; simp only [Matrix.mulVec, h3]
  have hkvZ : ∀ a : ZMod 2, D.kv ![a, 0, 0, 0] ∈ zCh611 T := by
    intro a
    rcases hz a with rfl | rfl
    · rw [show (![0, 0, 0, 0] : Fin 4 → ZMod 2) = 0 by decide]
      have := D.isMulCommutative
      rw [show D.kv 0 = 1 from kvCh611_zero _ _]
      exact (zCh611 T).one_mem
    · rw [D.kv_e0]; exact D.zZ
  set x := g'⁻¹ * g with hx
  have hxH : x ∈ hCh611 T := (hCh611 T).mul_mem ((hCh611 T).inv_mem hg') hg
  have hxU : x ∈ Subgroup.centralizer (uCh611 T L V : Set G) := by
    refine D.cu x hxH fun u hu => ?_
    obtain ⟨c, rfl⟩ := D.kv_surj u hu
    obtain ⟨a, ha⟩ := hw c
    have h1 : g * D.kv c * g⁻¹ = D.kv (A'.mulVec c) * D.kv ![a, 0, 0, 0] := by
      rw [(D.isMat_iff).mp h c, ha, D.kv_add]
    have h2 : g'⁻¹ * D.kv (A'.mulVec c) * g' = D.kv c := by
      rw [← (D.isMat_iff).mp h' c]
      group
    have h3 : g'⁻¹ * D.kv ![a, 0, 0, 0] * g' = D.kv ![a, 0, 0, 0] := by
      have := Subgroup.mem_centralizer_iff.mp ((hCh611 T).inv_mem hg') _ (hkvZ a)
      rw [← this]
      group
    have e : x * D.kv c * x⁻¹ * (D.kv c)⁻¹ = D.kv ![a, 0, 0, 0] := by
      calc x * D.kv c * x⁻¹ * (D.kv c)⁻¹
          = (g'⁻¹ * (g * D.kv c * g⁻¹) * g') * (D.kv c)⁻¹ := by rw [hx]; group
        _ = (g'⁻¹ * D.kv (A'.mulVec c) * g') * (g'⁻¹ * D.kv ![a, 0, 0, 0] * g') *
              (D.kv c)⁻¹ := by rw [h1]; group
        _ = D.kv c * D.kv ![a, 0, 0, 0] * (D.kv c)⁻¹ := by rw [h2, h3]
        _ = D.kv ![a, 0, 0, 0] := by
            rw [D.comm' (D.kv_mem c) (D.kv_mem _), mul_inv_cancel_right]
    rw [e]
    exact hkvZ a
  have hv : ∀ c, A.mulVec c = A'.mulVec c := by
    intro c
    apply D.kv_injective
    rw [← (D.isMat_iff).mp h c, ← (D.isMat_iff).mp h' c]
    have h1 : x * D.kv c * x⁻¹ = D.kv c := by
      rw [← Subgroup.mem_centralizer_iff.mp hxU _ (D.kv_mem c), mul_inv_cancel_right]
    calc g * D.kv c * g⁻¹ = g' * (x * D.kv c * x⁻¹) * g'⁻¹ := by rw [hx]; group
      _ = g' * D.kv c * g'⁻¹ := by rw [h1]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem exists_t1 : ∃ t₁ ∈ T, ∃ β, D.IsMat t₁ (matT1Ch611 β) := by
  obtain ⟨t, ht, htL⟩ := Set.not_subset.mp D.tl
  obtain ⟨x, hx⟩ := D.isMat_t ht
  have htH : t ∈ hCh611 T := T_le_hCh611 T ht
  have hz : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases hz (x 5) with h5 | h5
  · exfalso
    obtain ⟨i, hi⟩ := uniCh611_sameMod_vhat x h5
    obtain ⟨v, hv, hvi⟩ := D.exists_v i
    have heq := D.eq_of_sameMod htH (D.V_le_H hv) hx hvi hi
    rw [heq] at hx
    have hvinv := D.isMat_inv hvi (vhatCh611_sq i)
    have h1 := D.isMat_mul hvinv hx
    rw [vhatCh611_sq i] at h1
    have h2 : v⁻¹ * t ∈ L :=
      D.tcu _ (T.mul_mem (T.inv_mem (D.hyp.toHyp611.le_T hv)) ht)
        ((D.mem_centralizer_iff_isMat h1).mpr rfl)
    have hVL : V ≤ L := D.hyp.toHyp611Nat.V_le_pCoreOf_L.trans (pCoreOf_le 2 L)
    apply htL
    have := L.mul_mem (hVL hv) h2
    simpa using this
  · obtain ⟨i, β, he⟩ := uniCh611_eq_vhat_mul x h5
    obtain ⟨v, hv, hvi⟩ := D.exists_v i
    refine ⟨v * t, T.mul_mem (D.hyp.toHyp611.le_T hv) ht, β, ?_⟩
    rw [← he]
    exact D.isMat_mul hvi hx

omit [Group G] [Finite G] D in
theorem matH0_cols (γ : Fin 3 → ZMod 2) :
    (matH0Ch611 γ).col 0 = ![1, 0, 0, 0] ∧ (matH0Ch611 γ).col 1 = ![γ 0, 0, 0, 1] ∧
      (matH0Ch611 γ).col 2 = ![γ 1, 0, 1, 0] ∧ (matH0Ch611 γ).col 3 = ![γ 2, 1, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> rfl

theorem exists_h0 : ∃ h₀ ∈ hCh611 T, ∃ γ, D.IsMat h₀ (matH0Ch611 γ) := by
  classical
  have := D.isMulCommutative
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  set A0 := matH0Ch611 0 with hA0
  have hA0sq : A0 * A0 = 1 := by rw [hA0]; decide
  have hinj : Function.Injective (kapCh611 D.basis D.basis_sq) := fun c c' hcc' =>
    D.kv_injective (congrArg (fun x => ((Additive.toMul x : ↥(uCh611 T L V)) : G)) hcc')
  have hsurj : Function.Surjective (kapCh611 D.basis D.basis_sq) := by
    intro x
    obtain ⟨c, hc⟩ := D.kv_surj ((Additive.toMul x : ↥(uCh611 T L V)) : G)
      (Additive.toMul x).2
    exact ⟨c, Additive.toMul.injective (Subtype.ext hc)⟩
  let e := AddEquiv.ofBijective (kapCh611 D.basis D.basis_sq) ⟨hinj, hsurj⟩
  let P : (Fin 4 → ZMod 2) ≃+ (Fin 4 → ZMod 2) :=
    { toFun := A0.mulVec
      invFun := A0.mulVec
      left_inv := fun c => by
        show A0.mulVec (A0.mulVec c) = c
        rw [Matrix.mulVec_mulVec, hA0sq, Matrix.one_mulVec]
      right_inv := fun c => by
        show A0.mulVec (A0.mulVec c) = c
        rw [Matrix.mulVec_mulVec, hA0sq, Matrix.one_mulVec]
      map_add' := Matrix.mulVec_add A0 }
  let α : ↥(uCh611 T L V) ≃* ↥(uCh611 T L V) :=
    MulEquiv.toAdditive.symm (e.symm.trans (P.trans e))
  have he : ∀ c, e c = kapCh611 D.basis D.basis_sq c := fun c => rfl
  have hαkv : ∀ c, (α ⟨D.kv c, D.kv_mem c⟩ : G) = D.kv (A0.mulVec c) := by
    intro c
    have h1 : (Additive.ofMul (⟨D.kv c, D.kv_mem c⟩ : ↥(uCh611 T L V))) = e c := rfl
    show ((Additive.toMul (e (P (e.symm (Additive.ofMul ⟨D.kv c, D.kv_mem c⟩)))) :
      ↥(uCh611 T L V)) : G) = _
    rw [h1, AddEquiv.symm_apply_apply]
    rfl
  have hαZ : ∀ x : ↥(uCh611 T L V), (x : G) ∈ zCh611 T → α x = x := by
    intro x hx
    rcases (D.mem_Z_iff).mp hx with h1 | h1
    · have : x = 1 := Subtype.ext h1
      rw [this, map_one]
    · have hx' : x = ⟨D.kv ![1, 0, 0, 0], D.kv_mem _⟩ := Subtype.ext (h1.trans D.kv_e0.symm)
      apply Subtype.ext
      rw [hx', hαkv]
      rw [show A0.mulVec ![1, 0, 0, 0] = ![1, 0, 0, 0] by rw [hA0]; decide]
  obtain ⟨k, hk, hkα⟩ := D.aut α hαZ
  obtain ⟨A, hA⟩ := D.exists_isMat (hCh611_le_normalizer_u T L V hk)
  have hcol : ∀ j, ∃ a : ZMod 2, A.col j = A0.col j + ![a, 0, 0, 0] := by
    intro j
    have h1 := hkα (D.basis j)
    have hb : D.basis j = ⟨D.kv (Pi.single j 1), D.kv_mem _⟩ :=
      Subtype.ext (D.kv_single j).symm
    rw [hb, hαkv, Matrix.mulVec_single_one] at h1
    have h2 : k * D.kv (Pi.single j 1) * k⁻¹ = D.kv (A.col j) := by
      rw [← Matrix.mulVec_single_one, ← (D.isMat_iff).mp hA]
    simp only at h1
    rw [h2, D.inv_eq (D.kv_mem _), ← D.kv_add] at h1
    rcases (D.mem_Z_iff).mp h1 with h3 | h3
    · refine ⟨0, ?_⟩
      have h4 : A0.col j + A.col j = 0 := by
        apply D.kv_injective
        rw [h3]
        exact (kvCh611_zero _ _).symm
      rw [show (![0, 0, 0, 0] : Fin 4 → ZMod 2) = 0 by decide, add_zero]
      have hself : A0.col j + A0.col j = 0 := by ext i; exact CharTwo.add_self_eq_zero _
      calc A.col j = A0.col j + (A0.col j + A.col j) := by rw [← add_assoc, hself, zero_add]
        _ = A0.col j := by rw [h4, add_zero]
    · refine ⟨1, ?_⟩
      have h4 : A0.col j + A.col j = ![1, 0, 0, 0] := by
        apply D.kv_injective
        rw [h3, D.kv_e0]
      rw [← h4, ← add_assoc, show A0.col j + A0.col j = 0 by
        ext i; exact CharTwo.add_self_eq_zero _, zero_add]
  obtain ⟨a₁, ha₁⟩ := hcol 1
  obtain ⟨a₂, ha₂⟩ := hcol 2
  obtain ⟨a₃, ha₃⟩ := hcol 3
  have c0 := D.col0_of_mem_H hk hA
  refine ⟨k, hk, ![a₁, a₂, a₃], ?_⟩
  have hAeq : A = matH0Ch611 ![a₁, a₂, a₃] := by
    obtain ⟨y0, y1, y2, y3⟩ := matH0_cols ![a₁, a₂, a₃]
    obtain ⟨-, x1, x2, x3⟩ := matH0_cols (0 : Fin 3 → ZMod 2)
    refine matrix_eq_of_cols_ch611 fun j => ?_
    fin_cases j
    · exact c0.trans y0.symm
    · show A.col 1 = (matH0Ch611 ![a₁, a₂, a₃]).col 1
      rw [ha₁, hA0, x1, y1]
      ext i; fin_cases i <;> simp
    · show A.col 2 = (matH0Ch611 ![a₁, a₂, a₃]).col 2
      rw [ha₂, hA0, x2, y2]
      ext i; fin_cases i <;> simp
    · show A.col 3 = (matH0Ch611 ![a₁, a₂, a₃]).col 3
      rw [ha₃, hA0, x3, y3]
      ext i; fin_cases i <;> simp
  rw [← hAeq]
  exact hA

end Data611

end CFSG.Quasithin.H13
