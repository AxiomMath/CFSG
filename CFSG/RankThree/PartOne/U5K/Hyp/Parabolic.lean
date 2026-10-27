module

public import CFSG.RankThree.PartOne.U5K.Hyp.Dlin
public import CFSG.RankThree.PartOne.U5K.Hyp.Thompson

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

section Normal

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem mem_normalizer_Vh {T : Subgroup (MulAut (hypPSU hK 2 1))}
    (hTU : T ⊓ Pi hK = Uh hK) {ρ : MulAut (hypPSU hK 2 1)} (hρ : ρ ∈ T) :
    ρ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
  have := finite_mulAut_hyp hK
  have hUh : ∀ u ∈ Uh hK, ρ * u * ρ⁻¹ ∈ Uh hK := by
    intro u hu
    rw [← hTU] at hu ⊢
    exact ⟨T.mul_mem (T.mul_mem hρ hu.1) (T.inv_mem hρ),
      (inferInstance : (Pi hK).Normal).conj_mem u hu.2 ρ⟩
  refine mem_normalizer_of_conj_le fun v hv => ?_
  set W : Subgroup (MulAut (hypPSU hK 2 1)) := Vh hK |>.map (MulAut.conj ρ).toMonoidHom with hW
  have hWU : W ≤ Uh hK := by
    rintro _ ⟨w, hw, rfl⟩
    exact hUh w (Vh_le_Sh.trans Sh_le_Uh hw)
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ρ * a * ρ⁻¹ * (ρ * b * ρ⁻¹) = ρ * (a * b) * ρ⁻¹ := by group
      _ = ρ * (b * a) * ρ⁻¹ := by rw [Vh_comm ha hb]
      _ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := by group
  have hWs : ∀ x ∈ W, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ρ * a * ρ⁻¹ * (ρ * a * ρ⁻¹) = ρ * (a * a) * ρ⁻¹ := by group
      _ = 1 := by rw [Vh_sq ha]; group
  have hWcard : Nat.card W = (2 ^ f) ^ 4 := by
    rw [hW, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, card_Vh hZ]
  rcases elemAb_Uh hZ hWU hWc hWs with h | h
  · exact h ⟨v, hv, rfl⟩
  · exfalso
    rw [hWcard] at h
    have h1 : 1 < 2 ^ f := hK.one_lt_pow
    have : (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right h1 (by norm_num)
    omega

end Normal

section Outer

theorem exists_outer_lift {ρ : MulAut (hypPSU hK 2 1)} (hρ2 : ρ * ρ = 1) (hρP : ρ ∉ Pi hK) :
    ∃ x : Gam hK, Phi hK x = ρ ∧ x.1.right ≠ 1 ∧ ∀ c : K, hK.bar c = c → x.1.right c = c := by
  obtain ⟨x, hx⟩ := Phi_surjective hK ρ
  have hr : x.1.right ≠ 1 := fun h => hρP (Dlin_two_mem_Pi ((mem_Dlin_iff hx).2 h) (k := 1)
    (by rw [pow_one, pow_two]; exact hρ2))
  have hbar := (right_sq_of_sq hρ2 hx).resolve_left hr
  exact ⟨x, hx, hr, fun c hc => by rw [hbar c, hc]⟩

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem card_le_of_outer {ρ : MulAut (hypPSU hK 2 1)} {x : Gam hK} (hx : Phi hK x = ρ)
    (hρN : ρ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))))
    (hσ : x.1.right ≠ 1) (hσF : ∀ c : K, hK.bar c = c → x.1.right c = c)
    {F₀ : Subgroup (MulAut (hypPSU hK 2 1))} (hF₀ : F₀ ≤ Vh hK)
    (hcomm : ∀ w ∈ F₀, ρ * w = w * ρ) : Nat.card F₀ ≤ (2 ^ f) ^ 3 := by
  classical
  have hρ' : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := hx ▸ hρN
  have hv : ∀ w : F₀, ∃ v ∈ Vsub hK, innM hK v = (w : MulAut (hypPSU hK 2 1)) :=
    fun w => hF₀ w.2
  choose v hvV hve using hv
  have hact : ∀ w : F₀, act hK x (v w) = v w := by
    intro w
    apply eq_of_innM_eq_of_sq hZ _ (by rw [← act_mul, Vsub_sq (hvV w), act_one])
      (Vsub_sq (hvV w))
    rw [← Phi_mul_innM_mul_inv, hve w, hx, hcomm w w.2]
    group
  have hinj : Function.Injective (fun w : F₀ =>
      (⟨⟨v w, hvV w⟩, (mem_ker_chi hZ hρ').2 (hact w)⟩ : (chi hZ hρ').ker)) := by
    intro w w' h
    have h1 : v w = v w' :=
      congrArg (fun k : (chi hZ hρ').ker => ((k.1 : Vsub hK) : hypSU hK 2 1)) h
    apply Subtype.ext
    rw [← hve w, ← hve w', h1]
  calc Nat.card F₀ ≤ Nat.card (chi hZ hρ').ker := Nat.card_le_card_of_injective _ hinj
    _ ≤ (2 ^ f) ^ 3 := card_ker_chi_le hZ hρ' hσ hσF

theorem elemAb_T (hq : 3 ≤ 2 ^ f) {T : Subgroup (MulAut (hypPSU hK 2 1))}
    (hTU : T ⊓ Pi hK = Uh hK) {F : Subgroup (MulAut (hypPSU hK 2 1))} (hFT : F ≤ T)
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ (2 ^ f) ^ 4 ∧ (Nat.card F = (2 ^ f) ^ 4 → F = Vh hK) := by
  have := finite_mulAut_hyp hK
  have hF₀U : F ⊓ Pi hK ≤ Uh hK := by
    rw [← hTU]
    exact inf_le_inf_right _ hFT
  have hc₀ : ∀ x ∈ F ⊓ Pi hK, ∀ y ∈ F ⊓ Pi hK, x * y = y * x := fun x hx y hy => hc x hx.1 y hy.1
  have hs₀ : ∀ x ∈ F ⊓ Pi hK, x * x = 1 := fun x hx => hs x hx.1
  have hidx := card_le_two_mul_inf_Pi F hc hs
  have hlt : 2 * (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := by
    have : (2 ^ f) ^ 4 = (2 ^ f) ^ 3 * 2 ^ f := by ring
    have hpos : 0 < (2 ^ f) ^ 3 := by positivity
    nlinarith
  have hsmall : ∀ m : ℕ, m ≤ (2 ^ f) ^ 3 → Nat.card F ≤ 2 * m →
      Nat.card F ≤ (2 ^ f) ^ 4 ∧ (Nat.card F = (2 ^ f) ^ 4 → F = Vh hK) := by
    intro m hm hF
    refine ⟨by omega, fun h => by omega⟩
  rcases elemAb_Uh hZ hF₀U hc₀ hs₀ with h | h
  · by_cases hall : ∀ ρ ∈ F, ρ ∈ Pi hK
    · have hFV : F ≤ Vh hK := fun ρ hρ => h ⟨hρ, hall ρ hρ⟩
      refine ⟨?_, fun hcard => ?_⟩
      · calc Nat.card F ≤ Nat.card (Vh hK) := Subgroup.card_le_of_le hFV
          _ = (2 ^ f) ^ 4 := card_Vh hZ
      · exact Subgroup.eq_of_le_of_card_ge hFV (by rw [card_Vh hZ, hcard])
    · push Not at hall
      obtain ⟨ρ, hρ, hρP⟩ := hall
      obtain ⟨x, hx, hσ, hσF⟩ := exists_outer_lift (hs ρ hρ) hρP
      have hρN := mem_normalizer_Vh hZ hTU (hFT hρ)
      have hF₀card := card_le_of_outer hZ hx hρN hσ hσF h
        (fun w hw => hc ρ hρ w hw.1)
      exact hsmall _ hF₀card hidx
  · exact hsmall _ h hidx

end Outer

section Push

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem pushingUpS_eq_Sh (hq : 3 ≤ 2 ^ f) {T : Subgroup (MulAut (hypPSU hK 2 1))}
    (hT2 : IsPGroup 2 T) (hTU : T ⊓ Pi hK = Uh hK) : pushingUpS T = Sh hK := by
  have := finite_mulAut_hyp hK
  have hUT : Uh hK ≤ T := by rw [← hTU]; exact inf_le_left
  have hVT : Vh hK ≤ T := Vh_le_Sh.trans (Sh_le_Uh.trans hUT)
  have hcenter := elemCenter_eq_of_max (T := T) (V := Vh hK) (n := f * 4) hVT
    (fun x hx y hy => Vh_comm hx hy) (fun x hx => by simpa [pow_two] using Vh_sq hx)
    (by rw [card_Vh hZ, pow_mul]) (fun F hFT hc hs => by
      have := elemAb_T hZ hq hTU hFT hc (fun x hx => by simpa [pow_two] using hs x hx)
      rwa [← pow_mul] at this)
  have hP : pushingUpS T = T ⊓ Subgroup.centralizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
    unfold pushingUpS
    rw [← hcenter]
    rfl
  rw [hP]
  apply le_antisymm
  · rintro ρ ⟨hρT, hρC⟩
    have hρc : ∀ w ∈ Vh hK, ρ * w = w * ρ := fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hρC w hw).symm
    obtain ⟨x, hx⟩ := Phi_surjective hK ρ
    have hρN : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
      rw [hx]
      exact mem_normalizer_Vh hZ hTU hρT
    have hcen : ∀ v ∈ Vsub hK, act hK x v = v := by
      intro v hv
      apply eq_of_innM_eq_of_sq hZ _ (by rw [← act_mul, Vsub_sq hv, act_one]) (Vsub_sq hv)
      rw [← Phi_mul_innM_mul_inv, hx, hρc _ ⟨v, hv, rfl⟩]
      group
    have hσ := sigma_eq_one_of_central hZ hρN hcen
    have hD : ρ ∈ Dlin hK := (mem_Dlin_iff hx).2 hσ
    obtain ⟨k, hk⟩ := hT2 ⟨ρ, hρT⟩
    have hk' : ρ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hPi := Dlin_two_mem_Pi hD hk'
    have hU : ρ ∈ Uh hK := by rw [← hTU]; exact ⟨hρT, hPi⟩
    obtain ⟨u, hu, rfl⟩ := hU
    refine ⟨u, (commute_Vsub_iff hu).1 fun v hv => ?_, rfl⟩
    apply innM_injOn hZ (mul_mem hu (Ssub_le_Usub (Vsub_le_Ssub hv)) |> fun h => h)
      (mul_mem (Ssub_le_Usub (Vsub_le_Ssub hv)) hu)
    rw [map_mul, map_mul]
    exact hρc _ ⟨v, hv, rfl⟩
  · intro ρ hρ
    refine ⟨hUT (Sh_le_Uh hρ), Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    obtain ⟨s, hs, rfl⟩ := hρ
    obtain ⟨v, hv, rfl⟩ := hw
    rw [← map_mul, ← map_mul, (central_Ssub_iff (Vsub_le_Ssub hv)).2 hv s hs]

end Push

section Alg2

theorem exists_pow_five_ne_one (hK : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) :
    ∃ m : K, m ≠ 0 ∧ m ^ 5 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Finite K := hK.finite
  have h1 : Nat.card Kˣ ≤ 5 := by
    calc Nat.card Kˣ ≤ Nat.card (rootsOfUnity 5 K) :=
          Nat.card_le_card_of_injective (fun u => ⟨u, by
            rw [mem_rootsOfUnity]
            exact Units.ext (by simpa using hcon u u.ne_zero)⟩) fun a b h => congrArg Subtype.val h
      _ ≤ 5 := card_rootsOfUnity K 5
  rw [Nat.card_units, hK.card_eq_sq] at h1
  have : 4 ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
  omega

theorem sigma_eq_one_of_levi (hK : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) (σ : K ≃+* K)
    (E : Matrix (Fin 2) (Fin 2) K) (hE : E.det ≠ 0)
    (h : ∀ m : K, m ≠ 0 → m ^ 5 ≠ 1 → ∃ c : K, c ^ 5 = 1 ∧
      E * (!![m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).map σ = c • ((!![m, 0; 0, 1] :
        Matrix (Fin 2) (Fin 2) K) * E)) : σ = 1 := by
  have hfix : ∀ m : K, m ≠ 0 → m ^ 5 ≠ 1 → σ m = m := by
    intro m hm0 hm
    obtain ⟨c, hc5, hc⟩ := h m hm0 hm
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e10 := congrFun (congrFun hc 1) 0
    have e11 := congrFun (congrFun hc 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e00 e01 e10 e11
    have hdet : E 0 0 * E 1 1 - E 0 1 * E 1 0 ≠ 0 := by
      simpa [Matrix.det_fin_two] using hE
    by_cases hd : E 1 1 = 0
    ·
      have hb : E 0 1 ≠ 0 := fun hb => hdet (by rw [hb, hd]; ring)
      have hc' : E 1 0 ≠ 0 := fun hc' => hdet (by rw [hc', hd]; ring)
      have h1 : c * m = 1 := by
        have : E 0 1 * (c * m - 1) = 0 := by linear_combination -e01
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hb
        · linear_combination h
      have h2 : σ m = c := by
        have : E 1 0 * (σ m - c) = 0 := by linear_combination e10
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hc'
        · linear_combination h
      have hcm : c = m⁻¹ := by
        field_simp
        linear_combination h1
      exfalso
      apply hm
      have : m ^ 5 = 1 := by
        have := hc5
        rw [hcm, inv_pow] at this
        exact inv_eq_one.1 this
      exact this
    · have hc1 : c = 1 := by
        have : E 1 1 * (c - 1) = 0 := by linear_combination -e11
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hd
        · linear_combination h
      subst hc1
      have hm1 : m ≠ 1 := fun h => hm (by rw [h]; norm_num)
      have hb : E 0 1 = 0 := by
        have : E 0 1 * (m - 1) = 0 := by linear_combination (-1 : K) * e01
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) hm1
      have hσm : σ m ≠ 1 := fun h' => hm1 (σ.injective (by rw [h', map_one]))
      have hc' : E 1 0 = 0 := by
        have : E 1 0 * (σ m - 1) = 0 := by linear_combination e10
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) hσm
      have ha : E 0 0 ≠ 0 := fun ha => hdet (by rw [ha, hb]; ring)
      apply mul_left_cancel₀ ha
      linear_combination e00
  obtain ⟨m, hm0, hm⟩ := exists_pow_five_ne_one hK hq
  ext t
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases ht : t ^ 5 = 1
  · have h1 := hfix (t * m) (mul_ne_zero ht0 hm0) (by rw [mul_pow, ht, one_mul]; exact hm)
    rw [map_mul, hfix m hm0 hm] at h1
    exact mul_right_cancel₀ hm0 h1
  · exact hfix t ht0 ht

end Alg2

section LeviEq

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
include hZ

theorem levi_eq {x : Gam hK} (hP : IsParaW (lmat x)) {m : K} (hm : m ≠ 0) {s : hypSU hK 2 1}
    (hs : s ∈ Ssub hK)
    (hrel : innM hK (act hK x (lev !![m, 0; 0, 1] (isUnit_det_diag hm))) =
      innM hK (s * lev !![m, 0; 0, 1] (isUnit_det_diag hm))) :
    ∃ c : K, c ^ 5 = 1 ∧ blkEE x * (!![m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).map x.1.right =
      c • ((!![m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * blkEE x) := by
  set l : hypSU hK 2 1 := lev !![m, 0; 0, 1] (isUnit_det_diag hm) with hl
  have h1 : innM hK ((s * l)⁻¹ * act hK x l) = 1 := by
    rw [map_mul, map_inv, hrel, inv_mul_cancel]
  obtain ⟨c, -, hc5, hc⟩ := (innM_eq_one_iff hZ).1 h1
  have hmat : mat (act hK x l) = mat (s * l) * Matrix.scalar (HypIndex 2 1) (c : K) := by
    have h2 : act hK x l = (s * l) * ((s * l)⁻¹ * act hK x l) := by group
    have h3 : mat ((s * l)⁻¹ * act hK x l) = Matrix.scalar (HypIndex 2 1) (c : K) := by
      change ((((s * l)⁻¹ * act hK x l : hypSU hK 2 1)) : GL (HypIndex 2 1) K).1 = _
      rw [hc]
      rfl
    conv_lhs => rw [h2]
    rw [mat_mul, h3]
  have h4 := lmat_mul_map x l
  rw [hmat] at h4
  refine ⟨(c : K), by simpa using congrArg (fun u : Kˣ => (u : K)) hc5, ?_⟩
  obtain ⟨-, xs, Cs, hsm⟩ := hs
  ext i j
  have e := congrFun (congrFun h4 (.inl i)) (.inl j)
  have hP1 := hP.1
  have hP2 := hP.2
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, mat_mul, hsm, hl, mat_lev,
      oddDiag, oddUni, blkEE, Matrix.scalar_apply, Matrix.diagonal_apply, barInvT, hP1, hP2,
      Matrix.vecHead, Matrix.vecTail] at e ⊢ <;>
    linear_combination e

theorem core_Sh (hq : 4 ≤ 2 ^ f) {R : Subgroup (MulAut (hypPSU hK 2 1))} (hR2 : IsPGroup 2 R)
    (hN : ∀ ρ ∈ Pi hK, ρ ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) →
      ρ ∈ Subgroup.normalizer (R : Set (MulAut (hypPSU hK 2 1)))) : R ≤ Sh hK := by
  have := finite_mulAut_hyp hK
  have hR0 : R ⊓ Pi hK ≤ Sh hK := by
    refine core_inner hZ inf_le_right (hR2.to_le inf_le_left) fun ρ hρ hρS => ?_
    refine mem_normalizer_of_conj_le fun n hn => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hN ρ hρ hρS) n).1 hn.1,
      (inferInstance : (Pi hK).Normal).conj_mem n hn.2 ρ⟩
  have hcomm : ∀ ρ ∈ R, ∀ l ∈ Pi hK, l ∈ Subgroup.normalizer
      (Sh hK : Set (MulAut (hypPSU hK 2 1))) → ρ * l * ρ⁻¹ * l⁻¹ ∈ Sh hK := by
    intro ρ hρ l hlP hlS
    apply hR0
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hN l hlP hlS) ρ⁻¹).1 (R.inv_mem hρ)
      have h2 : ρ * l * ρ⁻¹ * l⁻¹ = ρ * (l * ρ⁻¹ * l⁻¹) := by group
      rw [h2]
      exact R.mul_mem hρ this
    · exact (Pi hK).mul_mem ((inferInstance : (Pi hK).Normal).conj_mem l hlP ρ⁻¹⁻¹ |> fun h => by
        simpa using h) ((Pi hK).inv_mem hlP)
  intro ρ hρ
  have hSP : ∀ s ∈ Sh hK, s ∈ Pi hK ∧ s ∈ Subgroup.normalizer
      (Sh hK : Set (MulAut (hypPSU hK 2 1))) := by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := hs
    exact ⟨Uh_le_Pi ⟨s', Ssub_le_Usub hs', rfl⟩, innM_Usub_mem_normalizer_Sh (Ssub_le_Usub hs')⟩
  have hρS : ρ ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) := by
    refine mem_normalizer_of_conj_le fun s hs => ?_
    have := hcomm ρ hρ s (hSP s hs).1 (hSP s hs).2
    have h2 : ρ * s * ρ⁻¹ = (ρ * s * ρ⁻¹ * s⁻¹) * s := by group
    rw [h2]
    exact (Sh hK).mul_mem this hs
  have hρV : ρ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) :=
    mem_normalizer_Vh_of_Sh hZ hρS
  obtain ⟨x, hx⟩ := Phi_surjective hK ρ
  have hρ' : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
    rw [hx]; exact hρV
  have hP := isParaW_of_act_mem (fun v hv => act_mem_Vsub hZ hρ' hv)
  have hσ : x.1.right = 1 := by
    refine sigma_eq_one_of_levi hK hq x.1.right (blkEE x) (det_blkEE_ne_zero hP)
      fun m hm0 _ => ?_
    set l : hypSU hK 2 1 := lev !![m, 0; 0, 1] (isUnit_det_diag hm0) with hl
    have hlP : innM hK l ∈ Pi hK := ⟨hypProj hK 2 1 l, rfl⟩
    have hlN := innM_lev_mem_normalizer_Sh (hK := hK) !![m, 0; 0, 1] (isUnit_det_diag hm0)
    obtain ⟨s, hs, hse⟩ := hcomm ρ hρ (innM hK l) hlP hlN
    refine levi_eq hZ hP hm0 hs ?_
    show innM hK (act hK x l) = innM hK (s * l)
    rw [← Phi_mul_innM_mul_inv, hx, map_mul, hse]
    group
  have hD : ρ ∈ Dlin hK := (mem_Dlin_iff hx).2 hσ
  obtain ⟨k, hk⟩ := hR2 ⟨ρ, hρ⟩
  have hk' : ρ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact hR0 ⟨hρ, Dlin_two_mem_Pi hD hk'⟩

end LeviEq

end CFSG.RankThree.PartOne.U5K.Hyp
