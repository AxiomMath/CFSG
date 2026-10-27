module

public import CFSG.Timmesfeld.ARS.CaseOANSLAssembleC
public import CFSG.Timmesfeld.ARS.CaseOANSLFrameMinus

public section

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open CFSG.LieType.CurtisTits CFSG.Timmesfeld.RankTwo CFSG.Assembly.LowTwoRank
open Matrix

namespace CFSG.Timmesfeld.ARS

namespace CaseOANSL

section MinusRoots

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

omit hirr in
theorem minusXL_pow (γ : Fin (n - 1) → ℤ) (a : K) (k : ℕ) :
    minusXL n b c γ a ^ k = minusXL n b c γ (k * a) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, minusXL_zero]
  | succ k ih => rw [pow_succ, ih, ← minusXL_add, Nat.cast_succ, add_mul, one_mul]

theorem charP_two_of_isPGroup_minus {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ)
    (h : IsPGroup 2 ((minusDatum n hirr).rootGroup γ)) : CharP K 2 := by
  obtain ⟨k, hk⟩ := h ⟨_, minusXL_mem hirr hγ (1 : K)⟩
  have hk' : minusXL n b c γ ((2 ^ k : ℕ) * 1) = minusXL n b c γ 0 := by
    rw [← minusXL_pow, minusXL_zero]
    simpa using congrArg Subtype.val hk
  have h2k := minusXL_injective (b := b) (c := c) hγ hk'
  rw [mul_one, Nat.cast_pow, Nat.cast_ofNat] at h2k
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h2k
  have h2 : (2 : K) = 0 := (pow_eq_zero_iff hk0).1 h2k
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)

theorem map_upper_eq_rootGroup_minus
    {φ : SpecialLinearGroup (Fin 2) K →* spinGroup (quadMinus n K b c)} {i : Fin (n - 1)}
    (hi : i.val + 2 < n) (hφU : ∀ x, φ (sl2Upper x) = minusXL n b c (Pi.single i 1) x) :
    (upperUnipotent K).map φ = (minusDatum n hirr).rootGroup (Pi.single i 1) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hg
    have := minusXL_mem hirr (minusLong_single hi) t
    rw [← hφU t] at this
    exact this
  · intro hy
    obtain ⟨t, rfl⟩ := exists_minusXL_eq hirr (minusLong_single hi) hy
    exact ⟨RankOne.upperElt K t, (RankOne.mem_upperUnipotent_iff K).2 ⟨t, rfl⟩, hφU t⟩

theorem map_lower_eq_rootGroup_minus
    {φ : SpecialLinearGroup (Fin 2) K →* spinGroup (quadMinus n K b c)} {i : Fin (n - 1)}
    (hi : i.val + 2 < n) (hφL : ∀ x, φ (sl2Lower x) = minusXL n b c (-Pi.single i 1) x) :
    (lowerUnipotent K).map φ = (minusDatum n hirr).rootGroup (-Pi.single i 1) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, rfl⟩ := (RankOne.mem_lowerUnipotent_iff K).1 hg
    have := minusXL_mem hirr (minusLong_neg_single hi) t
    rw [← hφL t] at this
    exact this
  · intro hy
    obtain ⟨t, rfl⟩ := exists_minusXL_eq hirr (minusLong_neg_single hi) hy
    exact ⟨RankOne.lowerElt K t, (RankOne.mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩, hφL t⟩

end MinusRoots

theorem cartanB_end {N : ℕ} {i j : Fin N} (hij : i.val + 1 = j.val) (h : j.val + 1 = N) :
    cartanB N i j = -1 ∧ cartanB N j i = -2 := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  constructor <;> split_ifs <;> omega

theorem exists_weylAction_single_eqB {N : ℕ} (hN : 1 ≤ N) :
    ∀ j (hj : j + 1 < N), ∃ w, (Pi.single (⟨j, by omega⟩ : Fin N) 1 : Fin N → ℤ) =
      weylAction (isFiniteType_cartanB N) w (Pi.single ⟨0, hN⟩ 1)
  | 0, _ => ⟨1, by simp⟩
  | j + 1, hj => by
    obtain ⟨w, hw⟩ := exists_weylAction_single_eqB hN j (by omega)
    obtain ⟨-, -, r0s, r10, -, -⟩ := reflectionB_A2 (N := N) (p := ⟨j, by omega⟩)
      (q := ⟨j + 1, by omega⟩) rfl (by simp only; omega)
    refine ⟨(coxeterMatrix (isFiniteType_cartanB N)).toCoxeterSystem.simple ⟨j, by omega⟩ *
      (coxeterMatrix (isFiniteType_cartanB N)).toCoxeterSystem.simple ⟨j + 1, by omega⟩ * w, ?_⟩
    rw [weylAction_mul_apply, weylAction_mul_apply, ← hw, weylAction_simple, weylAction_simple,
      r10, r0s]

theorem map_tv_ringHom {F F' : Type} [Field F] [Field F'] (f : F →+* F') {N : ℕ} (i j : Fin N)
    (x : F) : SpecialLinearGroup.map f (tv i j x) = tv i j (f x) := by
  by_cases h : i = j
  · subst h
    simp [tv]
  · rw [tv_of_ne h, tv_of_ne h]
    apply Subtype.ext
    rw [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.transvection_coe,
      SpecialLinearGroup.transvection_coe]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp

theorem comp_map_tv {F F' : Type} [Field F] [Field F'] {H : Type*} [Group H] {N : ℕ}
    (ψ : SpecialLinearGroup (Fin N) F →* H) (f : F' →+* F) (i j : Fin N) (x : F') :
    (ψ.comp (SpecialLinearGroup.map f)) (tv i j x) = ψ (tv i j (f x)) := by
  rw [MonoidHom.comp_apply, map_tv_ringHom]

theorem range_comp_map_ringEquiv {F F' : Type} [Field F] [Field F'] {H : Type*} [Group H]
    (ψ : SpecialLinearGroup (Fin 2) F →* H) (e : F ≃+* F') :
    (ψ.comp (SpecialLinearGroup.map (e.symm : F' →+* F))).range = ψ.range := by
  rw [MonoidHom.range_comp]
  have htop : (SpecialLinearGroup.map (n := Fin 2) (e.symm : F' →+* F)).range = ⊤ := by
    refine MonoidHom.range_eq_top.2 fun g => ⟨SpecialLinearGroup.map (e : F →+* F') g, ?_⟩
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  rw [htop, ← MonoidHom.range_eq_map]

section ShortRoot

variable {G : Type} [Group G] {n : ℕ} {K : Type} [Field K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem short_mem_centralizer (Θ : spinGroup (quadMinus n K b c) →* G) {D : Subgroup G}
    {i : Fin (n - 1)} (h : i.val + 3 = n) (hi : i.val ≠ 0)
    (hnorm : ∀ β ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅, β ⟨0, by omega⟩ = 0 →
      ∀ x ∈ (minusDatum n hirr).rootGroup β, Θ x ∈ Subgroup.normalizer (D : Set G))
    (hc1 : ∀ t, Θ (minusXL n b c (Pi.single i 1) t) ∈ Subgroup.centralizer (D : Set G))
    (hc2 : ∀ t, Θ (minusXL n b c
      (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t) ∈
        Subgroup.centralizer (D : Set G)) (p : Fin 2 → K) :
    Θ (minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p) ∈
        Subgroup.centralizer (D : Set G) ∧
      Θ (minusXS n hirr (-Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p) ∈
        Subgroup.centralizer (D : Set G) := by
  have hj2 : i.val + 1 + 2 = n := by omega
  have hjS : MinusShort n (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) :=
    minusShort_single hj2
  have habS : MinusShort n
      (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) := minusShort_B2sum h
  have hsing : ∀ l : Fin (n - 1), l.val ≠ 0 →
      (Pi.single l 1 : Fin (n - 1) → ℤ) ⟨0, by omega⟩ = 0 := fun l hl =>
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (0 : ℕ) ≠ l.val from Ne.symm hl)) 1
  have hsr : ∀ l : Fin (n - 1), (Pi.single l 1 : Fin (n - 1) → ℤ) ∈
      RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ := fun l => Or.inl ⟨1, l, by simp⟩
  have hwN : ∀ l : Fin (n - 1), l.val ≠ 0 →
      Θ (minusWeyl n hirr l) ∈ Subgroup.normalizer (D : Set G) := by
    intro l hl
    have hle : (minusDatum n hirr).rootGroup (Pi.single l 1) ⊔
        (minusDatum n hirr).rootGroup (-Pi.single l 1) ≤
          (Subgroup.normalizer (D : Set G)).comap Θ :=
      sup_le (fun x hx => hnorm _ (hsr l) (hsing l hl) x hx)
        (fun x hx => hnorm _ ((Steinberg.RootSystem.ofCartan (isFiniteType_cartanB (n - 1))
          ∅).neg_mem _ (hsr l)) (neg_eq_zero.2 (hsing l hl)) x hx)
    exact hle (minusDatum_n_mem n hirr l)
  have hab : ∀ q, Θ (minusXS n hirr
      (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q) ∈
        Subgroup.centralizer (D : Set G) := by
    intro q
    have hc := minus_comm_B2 hirr h q 1
    rw [one_smul, one_mul] at hc
    have e : minusXS n hirr
        (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q =
        ⁅minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q,
          minusXL n b c (Pi.single i 1) 1⁆ *
        (minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
          (planeNorm b c q))⁻¹ := by
      rw [hc, mul_inv_cancel_right]
    have hy : Θ (minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q) ∈
        Subgroup.normalizer (D : Set G) :=
      hnorm _ hjS.mem_roots (hsing _ (by simp)) _ (minusXS_mem hirr hjS q)
    rw [e, map_mul, map_inv, map_commutatorElement, commutatorElement_def]
    exact mul_mem (mul_mem (conj_mem_centralizer hy (hc1 1)) (inv_mem (hc1 1)))
      (inv_mem (hc2 _))
  obtain ⟨h1, -⟩ := cartanB_end (N := n - 1) (i := i) (j := ⟨i.val + 1, by omega⟩) rfl
    (by simp only; omega)
  have rab : reflection (cartanB (n - 1)) i
      (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) =
        Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1 := by
    rw [map_add, reflection_single_self (cartanB_self i), reflection_single', h1]
    module
  have hb : ∀ q, Θ (minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q) ∈
      Subgroup.centralizer (D : Set G) := by
    intro q
    have e := minusWeyl_conj_minusXS hirr i habS q
    rw [ite_eq_right (show ¬ (i.val + 2 = n) by omega), rab] at e
    rw [← e, map_mul, map_mul, map_inv]
    exact conj_mem_centralizer (hwN i hi) (hab q)
  refine ⟨hb p, ?_⟩
  have e := minusWeyl_conj_minusXS hirr ⟨i.val + 1, by omega⟩ hjS (planeRefl b c planeOne p)
  rw [ite_eq_left (show (⟨i.val + 1, by omega⟩ : Fin (n - 1)).val + 2 = n from hj2),
    reflection_single_self (cartanB_self _), planeRefl_planeRefl planeNorm_planeOne_ne_zero] at e
  rw [← e, map_mul, map_mul, map_inv]
  exact conj_mem_centralizer (hwN _ (by simp)) (hb _)

end ShortRoot

theorem cartan_F4_ne_cartanB :
    CFSG.Blueprint.Chevalley.Tag.cartan .F4 ≠
      Spin.cartanB (CFSG.Blueprint.Chevalley.Tag.rank .F4) := by
  decide

theorem cartan_G2_ne_cartanB :
    CFSG.Blueprint.Chevalley.Tag.cartan .G2 ≠
      Spin.cartanB (CFSG.Blueprint.Chevalley.Tag.rank .G2) := by
  decide

section Main

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
  {Δ₁ Δ₂ : Set (Subgroup G)}

open ExclNS (memberRoots memberRoots_subset weylAction_mem_memberRoots neg_mem_memberRoots)

theorem output_of_frame_minus (hset : CaseOASetting G R A A₀ Δ₁ Δ₂)
    (F : NSLFrameData (CompBar Δ₁) (quotClass (gen Δ₁) Δ₁))
    (hCt : F.D.cartan = Spin.cartanB F.D.rank) : Output G R := by
  obtain ⟨h, hA, -, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, -, hS₂⟩ := hset
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := center_gen_eq_bot h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F hS₂
  obtain ⟨P₂, hP₂, Q₂, hQ₂, hPQ₂, hgen₂⟩ := hS₂
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  have hc₁₂ := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  obtain ⟨hn, B, C, X₀, Y₀, -, hα₀O, hB, hC, hF', hBF', hX₀, hY₀, hXY₀, hX₀q, hY₀q, e0, e1,
    hstab⟩ := exists_frame_data h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne F hP₂ hQ₂ hPQ₂ hgen₂
  have hnorm : ∀ β ∈ F.D.roots, β ⟨0, by omega⟩ = 0 → ∀ x ∈ F.D.rootGroup β,
      liftHom hZ F.Ψ x ∈ Subgroup.normalizer (B : Set G) ∧
        liftHom hZ F.Ψ x ∈ Subgroup.normalizer (C : Set G) := by
    intro β hβ hβ0 x hx
    obtain ⟨h1, h2'⟩ := hstab β hβ hβ0
    exact ⟨conjSub_eq_self_iff.1 (conjSub_liftHom_eq h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hZ F.Ψ hB
        (h1 ⟨x, hx, rfl⟩)),
      conjSub_eq_self_iff.1 (conjSub_liftHom_eq h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hZ F.Ψ hC
        (h2' ⟨x, hx, rfl⟩))⟩
  have hcent : ∀ β ∈ memberRoots F, β ⟨0, by omega⟩ = 0 → ∀ x ∈ F.D.rootGroup β,
      liftHom hZ F.Ψ x ∈ Subgroup.centralizer (B : Set G) ∧
        liftHom hZ F.Ψ x ∈ Subgroup.centralizer (C : Set G) := by
    intro β hβ hβ0 x hx
    obtain ⟨X, hX, hXq⟩ := exists_member₁ h hA hAne hA₀ hΔ₁ hβ
    obtain ⟨h1, h2'⟩ := hstab β (memberRoots_subset F hβ) hβ0
    exact ⟨Subgroup.mem_centralizer_iff.2 fun b hb => (commute_liftHom_of_mem h hA hAne hmax hA₀ h2
        hΔ₁ hΔ₂ hne hZ F.Ψ hB hX hXq h1 hx b hb).symm.eq,
      Subgroup.mem_centralizer_iff.2 fun b hb => (commute_liftHom_of_mem h hA hAne hmax hA₀ h2
        hΔ₁ hΔ₂ hne hZ F.Ψ hC hX hXq h2' hx b hb).symm.eq⟩
  have hMW : ∀ γ ∈ memberRoots F, ∀ w, weylAction F.D.isFiniteType w γ ∈ memberRoots F :=
    fun γ hγ w => weylAction_mem_memberRoots F hγ w
  have hMneg : ∀ γ ∈ memberRoots F, -γ ∈ memberRoots F := fun γ hγ => neg_mem_memberRoots F hγ
  generalize memberRoots F = M at hα₀O hcent hMW hMneg
  have hV₁A₀ : ∀ k, liftHom hZ F.Ψ k ∈ Subgroup.centralizer (A₀ : Set G) := fun k =>
    levi_le_centralizer_right A A₀ (gen_le_levi h hA hAne hA₀ hΔ₁ (liftHom_mem hZ F.Ψ k))
  have hsurj := F.surj
  clear hstab
  cases F with
  | mk K D nw T hct hext hdiv i₀ htype hpg Ψ _ hker _ _ _ hconc =>
  cases hconc with
  | symplectic m F₀ =>
    have hm : 3 ≤ m := hn
    exact absurd hCt.symm (cartanB_ne_cartanC (m := m) (by omega))
  | g2 K' => exact absurd hCt cartan_G2_ne_cartanB
  | twistedD4 f => exact absurd hCt cartan_G2_ne_cartanB
  | f4 K' => exact absurd hCt cartan_F4_ne_cartanB
  | twistedE6 f => exact absurd hCt cartan_F4_ne_cartanB
  | @minus n K' _ b c hirr =>
  have hn' : 3 ≤ n - 1 := hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  set Θ : spinGroup (quadMinus (m + 4) K' b c) →* G := liftHom hZ Ψ with hΘ
  have h0L : (0 : ℕ) + 2 < m + 4 := by omega
  have hy0L : MinusLong (m + 4) (Pi.single (y0 m) 1) := minusLong_single h0L
  have : CharP K' 2 := charP_two_of_isPGroup_minus hirr hy0L (hpg _ hy0L.mem_roots)
  obtain ⟨φr, hφinj, hφU, hφL⟩ := exists_sl2_minusXL (n := m + 4) (b := b) (c := c)
    (k := y0 m) h0L
  have hΘinj : Function.Injective (Θ.comp φr) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : Ψ (φr g) = 1 := (liftHom_eq_one_iff hZ Ψ (φr g)).1 hg
    exact Linear.eq_one_of_map_mem_center K' hφinj (hker hg')
  have hup : (upperUnipotent K').map (Θ.comp φr) = X₀ := by
    rw [← Subgroup.map_map, map_upper_eq_rootGroup_minus hirr h0L hφU]
    exact map_liftHom hZ Ψ (le_gen hX₀) hX₀q
  have hlow : (lowerUnipotent K').map (Θ.comp φr) = Y₀ := by
    rw [← Subgroup.map_map, map_lower_eq_rootGroup_minus hirr h0L hφL]
    exact map_liftHom hZ Ψ (le_gen hY₀) hY₀q
  obtain ⟨f, hf, hcard, -⟩ := hXY₀.exists_mulEquiv_SL2' hR (hl₁ hX₀).1.1
  have hK' : Nat.card K' = 2 ^ f := by
    rw [← RankOne.card_upperUnipotent, ← Subgroup.card_map_of_injective hΘinj, hup, hcard]
  have : Finite K' := Nat.finite_of_card_ne_zero (by rw [hK']; positivity)
  let _ : Fintype K' := Fintype.ofFinite K'
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite (GaloisField 2 f)
  have hGF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let e : GaloisField 2 f ≃+* K' := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGF, hK'])
  set ρX := (Θ.comp φr).comp (SpecialLinearGroup.map (e : GaloisField 2 f →+* K')) with hρX
  have hρXinj : Function.Injective ρX := hΘinj.comp (map_injective_of_injective e.injective)
  have hρXU : (upperUnipotent (GaloisField 2 f)).map ρX = X₀ := by
    rw [hρX, ← Subgroup.map_map, map_upperUnipotent_ringEquiv, hup]
  have hρXL : (lowerUnipotent (GaloisField 2 f)).map ρX = Y₀ := by
    rw [hρX, ← Subgroup.map_map, map_lowerUnipotent_ringEquiv, hlow]
  obtain ⟨ρ, hρ2, hρ, hedge⟩ := Linear.exists_chain hR hiso (m := 3)
    (A := ![P₂, B, X₀]) (B := ![Q₂, ⁅A₀, C⁆, Y₀])
    (fun i => by fin_cases i; exacts [(hl₂ hP₂).1.1, hB.1.1.1, (hl₁ hX₀).1.1])
    (fun i => by fin_cases i; exacts [(hl₂ hQ₂).1.1, hF'.1.1.1, (hl₁ hY₀).1.1])
    (fun i => by fin_cases i; exacts [hPQ₂, hBF', hXY₀])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exacts [e0, e1])
    (k₀ := 2) hcard hρXinj hρXU hρXL
  obtain ⟨φ₀, hφ₀⟩ := hedge 0 1 rfl
  obtain ⟨φ₁, hφ₁⟩ := hedge 1 2 rfl
  have hρ0 : (ρ 0).range = P₂ ⊔ Q₂ := range_eq_sup_of_map (hρ 0).2.1 (hρ 0).2.2
  have hρ1 : (ρ 1).range = B ⊔ ⁅A₀, C⁆ := range_eq_sup_of_map (hρ 1).2.1 (hρ 1).2.2
  have hmemJ : ∀ j : Fin (m + 4 - 1), j.val + 2 < m + 4 →
      (Pi.single j 1 : Fin (m + 4 - 1) → ℤ) ∈ M := by
    intro j hj
    obtain ⟨w, hw⟩ := exists_weylAction_single_eqB (N := m + 4 - 1) (by omega) j.val (by omega)
    have := hMW _ hα₀O w
    have hj' : (Pi.single j 1 : Fin (m + 4 - 1) → ℤ) =
        weylAction (isFiniteType_cartanB (m + 4 - 1)) w (Pi.single ⟨0, by omega⟩ 1) := hw
    rw [hj']
    exact this
  have hmemL2 : (Pi.single (⟨m + 1, by omega⟩ : Fin (m + 4 - 1)) 1 +
      2 • Pi.single (⟨m + 1 + 1, by omega⟩ : Fin (m + 4 - 1)) 1 : Fin (m + 4 - 1) → ℤ) ∈ M := by
    have e' : weylAction (isFiniteType_cartanB (m + 4 - 1))
        ((coxeterMatrix (isFiniteType_cartanB (m + 4 - 1))).toCoxeterSystem.simple
          ⟨m + 1 + 1, by omega⟩) (Pi.single ⟨m + 1, by omega⟩ 1) =
          Pi.single ⟨m + 1, by omega⟩ 1 + 2 • Pi.single ⟨m + 1 + 1, by omega⟩ 1 := by
      rw [weylAction_simple, reflection_single',
        (cartanB_end (N := m + 4 - 1) (i := ⟨m + 1, by omega⟩) (j := ⟨m + 1 + 1, by omega⟩) rfl
          (by simp only; omega)).2]
      module
    have h1 := hMW _ (hmemJ ⟨m + 1, by omega⟩ (by simp only; omega))
      ((coxeterMatrix (isFiniteType_cartanB (m + 4 - 1))).toCoxeterSystem.simple
        ⟨m + 1 + 1, by omega⟩)
    rw [← e']
    exact h1
  have hsing : ∀ j : Fin (m + 4 - 1), j.val ≠ 0 →
      (Pi.single j 1 : Fin (m + 4 - 1) → ℤ) ⟨0, by omega⟩ = 0 := fun j hj =>
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (0 : ℕ) ≠ j.val from Ne.symm hj)) 1
  have hcentJ : ∀ j : Fin (m + 4 - 1), j.val ≠ 0 →
      (minusDatum (m + 4) hirr).rootGroup (Pi.single j 1) ⊔
        (minusDatum (m + 4) hirr).rootGroup (-Pi.single j 1) ≤
          (Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (C : Set G)).comap Θ := by
    intro j hj
    by_cases hjl : j.val + 2 < m + 4
    · exact sup_le (fun x hx => hcent _ (hmemJ j hjl) (hsing j hj) x hx)
        (fun x hx => hcent _ (hMneg _ (hmemJ j hjl))
          (neg_eq_zero.2 (hsing j hj)) x hx)
    · have hjv := j.isLt
      have hj' : j = ⟨m + 1 + 1, by omega⟩ := Fin.ext (show j.val = m + 1 + 1 by omega)
      rw [hj']
      have hc1 : ∀ t, Θ (minusXL (m + 4) b c (Pi.single (⟨m + 1, by omega⟩ : Fin (m + 4 - 1)) 1)
          t) ∈ Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (C : Set G) := fun t =>
        hcent _ (hmemJ ⟨m + 1, by omega⟩ (by simp only; omega)) (hsing _ (by simp)) _
          (minusXL_mem hirr (minusLong_single (show m + 1 + 2 < m + 4 by omega)) t)
      have hc2 : ∀ t, Θ (minusXL (m + 4) b c (Pi.single (⟨m + 1, by omega⟩ : Fin (m + 4 - 1)) 1 +
          2 • Pi.single (⟨m + 1 + 1, by omega⟩ : Fin (m + 4 - 1)) 1) t) ∈
            Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (C : Set G) := fun t =>
        hcent _ hmemL2 (show (Pi.single (⟨m + 1, by omega⟩ : Fin (m + 4 - 1)) 1 +
            2 • Pi.single (⟨m + 1 + 1, by omega⟩ : Fin (m + 4 - 1)) 1 : Fin (m + 4 - 1) → ℤ)
              ⟨0, by omega⟩ = 0 by
          rw [Pi.add_apply, Pi.smul_apply, hsing _ (by simp), hsing _ (by simp), smul_zero,
            add_zero]) _
          (minusXL_mem hirr (minusLong_B2long (i := ⟨m + 1, by omega⟩)
            (show m + 1 + 3 = m + 4 by omega)) t)
      have hB' := short_mem_centralizer hirr Θ (D := B) (i := ⟨m + 1, by omega⟩)
        (show m + 1 + 3 = m + 4 by omega) (by simp) (fun β hβ hβ0 x hx => (hnorm β hβ hβ0 x hx).1)
        (fun t => (hc1 t).1) (fun t => (hc2 t).1)
      have hC' := short_mem_centralizer hirr Θ (D := C) (i := ⟨m + 1, by omega⟩)
        (show m + 1 + 3 = m + 4 by omega) (by simp) (fun β hβ hβ0 x hx => (hnorm β hβ hβ0 x hx).2)
        (fun t => (hc1 t).2) (fun t => (hc2 t).2)
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr
          (minusShort_single (show m + 1 + 1 + 2 = m + 4 by omega)) hx
        exact ⟨(hB' p).1, (hC' p).1⟩
      · obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr
          (minusShort_neg_single (show m + 1 + 1 + 2 = m + 4 by omega)) hx
        exact ⟨(hB' p).2, (hC' p).2⟩
  have hg0 : ∀ g, ρ 0 g ∈ gen Δ₂ := fun g => by
    have : ρ 0 g ∈ (ρ 0).range := ⟨g, rfl⟩
    rw [hρ0] at this
    exact sup_le (le_gen hP₂) (le_gen hQ₂) this
  have key : ∀ g, ∀ y : G, y ∈ Subgroup.centralizer (B : Set G) →
      y ∈ Subgroup.centralizer (C : Set G) → y ∈ Subgroup.centralizer (A₀ : Set G) →
        Commute (ρ 1 g) y := by
    intro g y hyB hyC hyA
    have hle : B ⊔ ⁅A₀, C⁆ ≤ Subgroup.centralizer ({y} : Set G) :=
      sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hyB b hb))
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (mem_centralizer_commutator hyA hyC) z hz))
    have hg : ρ 1 g ∈ B ⊔ ⁅A₀, C⁆ := by
      rw [← hρ1]
      exact ⟨g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  obtain ⟨ε, hε⟩ : ∃ ε : K' →+* GaloisField 2 f, ε = (e.symm : K' →+* GaloisField 2 f) :=
    ⟨_, rfl⟩
  have hes : ∀ x, (e : GaloisField 2 f →+* K') (ε x) = x := fun x => by
    rw [hε]
    exact e.apply_symm_apply x
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ, ψ = φ₀.comp (SpecialLinearGroup.map (n := Fin 3) ε) := ⟨_, rfl⟩
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ, ψ = φ₁.comp (SpecialLinearGroup.map (n := Fin 3) ε) := ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ, σ = (ρ 0).comp (SpecialLinearGroup.map (n := Fin 2) ε) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ, σ = (ρ 1).comp (SpecialLinearGroup.map (n := Fin 2) ε) := ⟨_, rfl⟩
  have H : FrameHypM hirr Θ ψ₀ ψ₁ σ₀ σ₁ :=
    { φ₀01 := fun x => by rw [hψ₀, hσ₀, comp_map_tv, comp_map_tv]; exact (hφ₀ _).1
      φ₀10 := fun x => by rw [hψ₀, hσ₀, comp_map_tv, comp_map_tv]; exact (hφ₀ _).2.1
      φ₀12 := fun x => by rw [hψ₀, hσ₁, comp_map_tv, comp_map_tv]; exact (hφ₀ _).2.2.1
      φ₀21 := fun x => by rw [hψ₀, hσ₁, comp_map_tv, comp_map_tv]; exact (hφ₀ _).2.2.2
      φ₁01 := fun x => by rw [hψ₁, hσ₁, comp_map_tv, comp_map_tv]; exact (hφ₁ _).1
      φ₁10 := fun x => by rw [hψ₁, hσ₁, comp_map_tv, comp_map_tv]; exact (hφ₁ _).2.1
      φ₁12 := fun x => by
        rw [hψ₁, comp_map_tv, (hφ₁ _).2.2.1, hρ2, hρX, MonoidHom.comp_apply, map_tv_ringHom,
          hes, MonoidHom.comp_apply, LevisExtras.tv01_eq_sl2Upper, hφU]
      φ₁21 := fun x => by
        rw [hψ₁, comp_map_tv, (hφ₁ _).2.2.2, hρ2, hρX, MonoidHom.comp_apply, map_tv_ringHom,
          hes, MonoidHom.comp_apply, LevisExtras.tv10_eq_sl2Lower, hφL]
      V := fun g y => by
        rw [hσ₀]
        exact (hc₁₂ (Θ y) (liftHom_mem hZ Ψ y) _ (hg0 _)).symm
      E := fun j hj g y hy => by
        rw [hσ₁]
        exact key _ _ (hcentJ j hj hy).1 (hcentJ j hj hy).2 (hV₁A₀ _) }
  have htop : levi R A A₀ ⊔ B ⊔ ⁅A₀, C⁆ = ⊤ :=
    CaseOA.levi_sup_sup_eq_top h hA hAne hmax hA₀ hB hF'
  rw [CaseOA.levi_eq_sup h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne] at htop
  have hgen : σ₀.range ⊔ σ₁.range ⊔ Θ.range = ⊤ := by
    rw [hσ₀, hσ₁, hε, range_comp_map_ringEquiv, range_comp_map_ringEquiv, hρ0, hρ1,
      range_liftHom hZ hsurj, ← hgen₂, eq_top_iff, ← htop]
    exact sup_le (sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_left.trans (le_sup_right.trans le_sup_left)))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))
  have hnt : σ₀ (tv 0 1 1) ≠ 1 := by
    rw [hσ₀, comp_map_tv, map_one]
    intro h1
    have h1' := (hρ 0).1 (h1.trans (map_one (ρ 0)).symm)
    rw [LevisExtras.tv01_eq_sl2Upper] at h1'
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) (GaloisField 2 f) =>
      (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1) h1'
    simp [sl2Upper] at this
  have := fact_shortField hirr
  have hframe := (H.isMinusFrame hgen hnt).isCTFrame
  have hadm : StatedLieAdmissible .POmegaMinus (m + 4 + 2) 2 f := ⟨Nat.prime_two, hf, by omega⟩
  have hCT := CurtisTits.curtisTitsConclusion_spinMinus (n := m + 4 + 2) hirr hadm hK'
  have hL := leviConePresented_spinMinus hirr (show 4 ≤ m + 4 + 2 by omega)
  refine Output.of_nonSimplyLaced
    (.inr (.inl ⟨m + 4 + 2, f, by omega, hf, hframe.lieModel hCT hL h.center⟩)) ?_
  refine .inr (hframe.nslFrame hCT hL (minusDatum_isCTGroupDatum (m + 4 + 2) hirr (by omega))
    (minusDatum_steinbergExtras (m + 4 + 2) hirr) rfl (NSLType.minusDatum (by omega) hirr)
    (fun _ hγ => isPGroup_minusRootGroup hirr hγ) (NSLFrameData.comm_minusDatum (by omega) hirr)
    (hl₂ hP₂).1.1 ?_ ?_ hPQ₂)
  · refine Eq.symm ((range_minusPhiOf_long hirr _ _
      (minusLong_single (show 0 + 2 < m + 4 + 2 by omega))).trans ?_)
    have e' : oaPsiL Θ ψ₀ ψ₁ (d0 m) = fun x => σ₀ (tv 0 1 x) := funext H.v_d0
    show Set.range (oaPsiL Θ ψ₀ ψ₁ (d0 m)) = _
    rw [e', Linear.range_tv_upper, hσ₀, ← Subgroup.map_map, hε,
      map_upperUnipotent_ringEquiv e.symm, (hρ 0).2.1]
    rfl
  · refine Eq.symm ((range_minusPhiOf_long hirr _ _
      (minusLong_neg_single (show 0 + 2 < m + 4 + 2 by omega))).trans ?_)
    have e' : oaPsiL Θ ψ₀ ψ₁ (-d0 m) = fun x => σ₀ (tv 1 0 x) := funext H.v_nd0
    show Set.range (oaPsiL Θ ψ₀ ψ₁ (-d0 m)) = _
    rw [e', Linear.range_tv_lower, hσ₀, ← Subgroup.map_map, hε,
      map_lowerUnipotent_ringEquiv e.symm, (hρ 0).2.2]
    rfl

end Main

end CaseOANSL

end CFSG.Timmesfeld.ARS
