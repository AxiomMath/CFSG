module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddBase
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddAdm

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open Module QuadraticMap

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_fixed_mod {S : Subgroup (V ≃ₗ[K] V)} (hS : IsPGroup 2 S) {W L : Submodule K V}
    (hWL : ¬ W ≤ L) (hW : ∀ s ∈ S, ∀ w ∈ W, s w ∈ W)
    (hL : ∀ s ∈ S, ∀ l ∈ L, s l ∈ L) : ∃ w ∈ W, w ∉ L ∧ ∀ s ∈ S, s w - w ∈ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  set L' : Submodule K W := L.comap W.subtype with hL'
  set M := W ⧸ L'
  have : Finite M := Finite.of_surjective _ (Submodule.mkQ_surjective L')
  let f : S → (W →ₗ[K] W) := fun s => (s.1 : V →ₗ[K] V).restrict (hW s.1 s.2)
  have hf : ∀ s : S, L' ≤ L'.comap (f s) := fun s w hw => hL s.1 s.2 _ hw
  have hf1 : f 1 = LinearMap.id := LinearMap.ext fun w => Subtype.ext rfl
  have hfmul : ∀ s t : S, f (s * t) = (f s).comp (f t) := fun s t =>
    LinearMap.ext fun w => Subtype.ext rfl
  let act : MulAction S M :=
    { smul := fun s m => L'.mapQ L' (f s) (hf s) m
      one_smul := fun m => by
        change L'.mapQ L' (f 1) (hf 1) m = m
        obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective L' m
        rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hf1]
        rfl
      mul_smul := fun s t m => by
        change L'.mapQ L' (f (s * t)) (hf (s * t)) m =
          L'.mapQ L' (f s) (hf s) (L'.mapQ L' (f t) (hf t) m)
        obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective L' m
        simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, hfmul]
        rfl }
  have hne : (⊤ : Submodule K M) ≠ ⊥ := by
    intro h
    apply hWL
    intro w hw
    have h1 : Submodule.Quotient.mk (p := L') ⟨w, hw⟩ = 0 := by
      have : Submodule.Quotient.mk (p := L') ⟨w, hw⟩ ∈ (⊤ : Submodule K M) := Submodule.mem_top
      rw [h, Submodule.mem_bot] at this
      exact this
    exact (Submodule.Quotient.mk_eq_zero L').mp h1
  have hdvd : 2 ∣ Nat.card M := by
    have h := CFSG.RankThree.PartOne.AUTSL.Four.two_dvd_card_of_ne_bot (K := K) (V := M) ⊤ hne
    rwa [Nat.card_congr (Submodule.topEquiv (R := K) (M := M)).toEquiv] at h
  have h0 : (0 : M) ∈ MulAction.fixedPoints S M := fun s => by
    change L'.mapQ L' (f s) (hf s) 0 = 0
    exact map_zero _
  obtain ⟨m, hm, hm0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hdvd h0
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective L' m
  refine ⟨w, w.2, fun hwL => hm0 ?_, fun s hs => ?_⟩
  · rw [Submodule.mkQ_apply, eq_comm, Submodule.Quotient.mk_eq_zero]
    exact hwL
  · have h1 : L'.mapQ L' (f ⟨s, hs⟩) (hf ⟨s, hs⟩) (Submodule.mkQ L' w) = Submodule.mkQ L' w :=
      hm ⟨s, hs⟩
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h1
    exact h1

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_singularPart (R : Submodule K V)
    (hRiso : ∀ y ∈ R, ∀ y' ∈ R, polar Q y y' = 0) :
    ∃ R₀ : Submodule K V, R₀ ≤ R ∧ (∀ v, v ∈ R₀ ↔ v ∈ R ∧ Q v = 0) := by
  refine ⟨{ carrier := {v | v ∈ R ∧ Q v = 0}
            add_mem' := fun {a b} ha hb => ⟨R.add_mem ha.1 hb.1, by
              rw [QuadraticMap.map_add (⇑Q) a b, ha.2, hb.2, hRiso a ha.1 b hb.1, add_zero,
                add_zero]⟩
            zero_mem' := ⟨R.zero_mem, QuadraticMap.map_zero Q⟩
            smul_mem' := fun c v hv => ⟨R.smul_mem c hv.1, by
              rw [QuadraticMap.map_smul, hv.2, smul_zero]⟩ }, fun v hv => hv.1,
    fun v => Iff.rfl⟩

omit [FiniteDimensional K V] in
theorem exists_singular_comb {u v : V} (huv : polar Q u v = 0) (hu : Q u ≠ 0) :
    ∃ c : K, Q (c • u + v) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q v / Q u)
  refine ⟨r, ?_⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.map_add (⇑Q) (r • u) v, QuadraticMap.map_smul, polar_smul_left, huv,
    smul_zero, add_zero, smul_eq_mul, ← hr, div_mul_cancel₀ _ hu]
  linear_combination Q v * h2

@[expose] def fixSub (S : Subgroup (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ s ∈ S, s v = v}
  add_mem' ha hb s hs := by rw [map_add, ha s hs, hb s hs]
  zero_mem' s _ := map_zero s
  smul_mem' c v hv s hs := by rw [map_smul, hv s hs]

variable (Q) in
abbrev perp (W : Submodule K V) : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) W

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_perp {W : Submodule K V} {v : V} : v ∈ perp Q W ↔ ∀ w ∈ W, polar Q w v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polarBilin_isRefl : LinearMap.BilinForm.IsRefl (polarBilin Q) := fun u w h => by
  rw [polarBilin_apply_apply] at h ⊢
  rw [polar_comm]
  exact h

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem map_mem_fixSub {S : Subgroup (V ≃ₗ[K] V)} {n : V ≃ₗ[K] V}
    (hn : ∀ s ∈ S, n⁻¹ * s * n ∈ S) {v : V} (hv : v ∈ fixSub S) : n v ∈ fixSub S := by
  intro s hs
  have h1 := hv _ (hn s hs)
  simp only [LinearEquiv.mul_apply] at h1
  have h2 := congrArg n h1
  rw [← LinearEquiv.mul_apply n n⁻¹, mul_inv_cancel] at h2
  exact h2

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem map_mem_perp {n : V ≃ₗ[K] V} (hnQ : ∀ v, Q (n v) = Q v) {W : Submodule K V}
    (hW : ∀ w ∈ W, n⁻¹ w ∈ W) {v : V} (hv : v ∈ perp Q W) : n v ∈ perp Q W := by
  rw [mem_perp] at hv ⊢
  intro w hw
  have h1 := hv _ (hW w hw)
  rw [← polar_map hnQ, ← LinearEquiv.mul_apply n n⁻¹, mul_inv_cancel] at h1
  exact h1

theorem rad_fixSub_ne_bot {S : Subgroup (V ≃ₗ[K] V)}
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hSQ : ∀ s ∈ S, ∀ v, Q (s v) = Q v) :
    fixSub S ⊓ perp Q (fixSub S) ≠ ⊥ := by
  have : Finite V := Module.finite_of_finite K
  intro hY
  have hdisj : Disjoint (fixSub S) (perp Q (fixSub S)) := by rw [disjoint_iff]; exact hY
  have hc : IsCompl (fixSub S) (perp Q (fixSub S)) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint polarBilin_isRefl).mpr hdisj
  by_cases hF'0 : perp Q (fixSub S) = ⊥
  · apply hS1
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have hFtop : fixSub S = ⊤ := by rw [hF'0] at hc; exact eq_top_of_isCompl_bot hc
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ fixSub S := hFtop ▸ Submodule.mem_top
    exact hw s hs
  · have hinv : ∀ s ∈ S, ∀ w ∈ perp Q (fixSub S), s w ∈ perp Q (fixSub S) := by
      intro s hs w hw
      rw [mem_perp] at hw ⊢
      intro f hf
      rw [← hf s hs, polar_map (hSQ s hs)]
      exact hw f hf
    obtain ⟨w, hwF', hw0, hwfix⟩ :=
      CFSG.RankThree.PartOne.AUTSL.Four.exists_fixed_vector hS2 hF'0 hinv
    have : w ∈ fixSub S ⊓ perp Q (fixSub S) := ⟨hwfix, hwF'⟩
    rw [hY, Submodule.mem_bot] at this
    exact hw0 this

omit [Finite K] [FiniteDimensional K V] in
variable (Q) in
@[expose] def lev2 (S : Subgroup (V ≃ₗ[K] V)) (y : V) : Submodule K V where
  carrier := {v | polar Q y v = 0 ∧ ∀ s ∈ S, s v - v ∈ K ∙ y}
  add_mem' := fun {a b} ha hb => ⟨by rw [polar_add_right, ha.1, hb.1, add_zero], fun s hs => by
    have h := (K ∙ y).add_mem (ha.2 s hs) (hb.2 s hs)
    rw [map_add]
    convert h using 1
    abel⟩
  zero_mem' := ⟨polar_zero_right Q y, fun s _ => by rw [map_zero, sub_zero]; exact zero_mem _⟩
  smul_mem' := fun c v hv => ⟨by rw [polar_smul_right, hv.1, smul_zero], fun s hs => by
    rw [map_smul, ← smul_sub]
    exact (K ∙ y).smul_mem c (hv.2 s hs)⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem map_mem_lev2 {S : Subgroup (V ≃ₗ[K] V)} {y : V} {n : V ≃ₗ[K] V}
    (hnQ : ∀ v, Q (n v) = Q v) (hny : n y = y) (hn : ∀ s ∈ S, n⁻¹ * s * n ∈ S) {v : V}
    (hv : v ∈ lev2 Q S y) : n v ∈ lev2 Q S y := by
  refine ⟨?_, fun s hs => ?_⟩
  · rw [← hny, polar_map hnQ]
    exact hv.1
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv.2 _ (hn s hs))
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    have h1 := congrArg n ha
    simp only [LinearEquiv.mul_apply, map_smul, map_sub, hny] at h1
    rw [← LinearEquiv.mul_apply n n⁻¹, mul_inv_cancel] at h1
    exact h1

theorem exists_lev2 (hQ : (polarBilin Q).Nondegenerate) {S : Subgroup (V ≃ₗ[K] V)}
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hSQ : ∀ s ∈ S, ∀ v, Q (s v) = Q v)
    (hSΩ : ∀ s ∈ S, Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace s)))
    {y : V} (hy : Q y ≠ 0) (hSy : ∀ s ∈ S, s y = y) :
    ∃ z ∈ lev2 Q S y ⊓ perp Q (lev2 Q S y), z ∉ K ∙ y := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  by_contra hcon
  push Not at hcon
  set F₂ := lev2 Q S y with hF₂
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (QuadraticMap.map_zero Q)
  have hyF : y ∈ F₂ := ⟨OrthRestOdd.polar_self_eq_zero Q y, fun s hs => by
    rw [hSy s hs, sub_self]; exact zero_mem _⟩
  have hperp_y : ∀ w ∈ perp Q F₂, polar Q y w = 0 := fun w hw => (mem_perp.mp hw) y hyF
  have hSF : ∀ s ∈ S, ∀ v ∈ F₂, s v ∈ F₂ := fun s hs v hv =>
    map_mem_lev2 (hSQ s hs) (hSy s hs) (fun s' hs' => mul_mem (mul_mem (inv_mem hs) hs') hs) hv
  have hSperp : ∀ s ∈ S, ∀ w ∈ perp Q F₂, s w ∈ perp Q F₂ := fun s hs w hw =>
    map_mem_perp (hSQ s hs) (fun v hv => hSF s⁻¹ (inv_mem hs) v hv) hw
  have hSL : ∀ s ∈ S, ∀ l ∈ K ∙ y, s l ∈ K ∙ y := by
    intro s hs l hl
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hl
    rw [map_smul, hSy s hs]
    exact (K ∙ y).smul_mem a (Submodule.mem_span_singleton_self y)
  have hle : perp Q F₂ ≤ K ∙ y := by
    by_contra h
    obtain ⟨w, hw, hwy, hwS⟩ := exists_fixed_mod hS2 h hSperp hSL
    exact hwy (hcon w ⟨⟨hperp_y w hw, hwS⟩, hw⟩)
  have hle2 : perp Q (K ∙ y) ≤ F₂ := by
    have h1 := LinearMap.BilinForm.orthogonal_le (B := polarBilin Q) hle
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ polarBilin_isRefl] at h1
  have hfix : ∀ s ∈ S, ∀ v ∈ perp Q (K ∙ y), s v = v := by
    intro s hs v hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hle2 hv).2 s hs)
    have hvy : polar Q v y = 0 := by
      rw [polar_comm]
      exact (mem_perp.mp hv) y (Submodule.mem_span_singleton_self y)
    have hsv : s v = v + c • y := by rw [hc]; abel
    have e := hSQ s hs v
    rw [hsv, QuadraticMap.map_add (⇑Q) v (c • y), QuadraticMap.map_smul, polar_smul_right, hvy,
      smul_zero, add_zero, smul_eq_mul] at e
    have hc0 : c * c = 0 := by
      have : c * c * Q y = 0 := by linear_combination e
      exact (mul_eq_zero.mp this).resolve_right hy
    rw [hsv, mul_self_eq_zero.mp hc0, zero_smul, add_zero]
  apply hS1
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  have hdim := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace s
  have hperp := LinearMap.BilinForm.finrank_orthogonal hQ (K ∙ y)
  rw [finrank_span_singleton hy0] at hperp
  have hle3 : perp Q (K ∙ y) ≤ CFSG.RankThree.OrthogonalInvolutions.fixSpace s := fun v hv =>
    CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mpr (hfix s hs v hv)
  have h3 := Submodule.finrank_mono hle3
  have hpos : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨y, hy0⟩
  obtain ⟨k, hk⟩ := hSΩ s hs
  have hc0 : finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace s) = 0 := by
    change finrank K (perp Q (K ∙ y)) = finrank K V - 1 at hperp
    omega
  by_contra hs1
  have := CFSG.RankThree.OrthogonalInvolutions.one_le_finrank_commSpace hs1
  omega

theorem exists_singular_of_two (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {S N : Subgroup (V ≃ₗ[K] V)} (hS2 : IsPGroup 2 S)
    (hS1 : S ≠ ⊥) (hSQ : ∀ s ∈ S, ∀ v, Q (s v) = Q v)
    (hSΩ : ∀ s ∈ S, Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace s)))
    (hNQ : ∀ n ∈ N, ∀ v, Q (n v) = Q v) (hNp : ∀ n ∈ N, n ^ p = 1)
    (hnorm : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) :
    ∃ Y : Submodule K V, Y ≠ ⊥ ∧ (∀ n ∈ N, ∀ y ∈ Y, n y ∈ Y) ∧ ∀ y ∈ Y, Q y = 0 := by
  have hnorm' : ∀ n ∈ N, ∀ s ∈ S, n⁻¹ * s * n ∈ S := fun n hn s hs => by
    simpa using hnorm n⁻¹ (inv_mem hn) s hs
  set F := fixSub S with hF
  set R := F ⊓ perp Q F with hR
  have hR0 : R ≠ ⊥ := rad_fixSub_ne_bot hS2 hS1 hSQ
  have hFinv : ∀ n ∈ N, ∀ v ∈ F, n v ∈ F := fun n hn v hv => map_mem_fixSub (hnorm' n hn) hv
  have hRinv : ∀ n ∈ N, ∀ v ∈ R, n v ∈ R := fun n hn v hv =>
    ⟨hFinv n hn v hv.1, map_mem_perp (hNQ n hn) (fun w hw => hFinv n⁻¹ (inv_mem hn) w hw) hv.2⟩
  have hRiso : ∀ u ∈ R, ∀ v ∈ R, polar Q u v = 0 := fun u hu v hv => (mem_perp.mp hv.2) u hu.1
  obtain ⟨R₀, -, hR₀⟩ := exists_singularPart (Q := Q) R hRiso
  by_cases hR₀0 : R₀ = ⊥
  ·
    obtain ⟨y, hyR, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
    have hQy : Q y ≠ 0 := fun h => hy0 (by
      have : y ∈ R₀ := (hR₀ y).mpr ⟨hyR, h⟩
      rw [hR₀0] at this
      exact this)
    have hmult : ∀ v ∈ R, ∃ c : K, v = c • y := by
      intro v hv
      obtain ⟨c, hc⟩ := exists_singular_comb (hRiso y hyR v hv) hQy
      have hmem : c • y + v ∈ R₀ := (hR₀ _).mpr ⟨R.add_mem (R.smul_mem c hyR) hv, hc⟩
      rw [hR₀0, Submodule.mem_bot] at hmem
      exact ⟨-c, by rw [neg_smul]; exact eq_neg_of_add_eq_zero_right hmem⟩
    have hNy : ∀ n ∈ N, n y = y := by
      intro n hn
      obtain ⟨c, hc⟩ := hmult (n y) (hRinv n hn y hyR)
      exact apply_eq_of_eigen (hNp n hn) hK1 hy0 hc
    have hSy : ∀ s ∈ S, s y = y := fun s hs => hyR.1 s hs
    obtain ⟨z, hzR₂, hzy⟩ := exists_lev2 hQ hS2 hS1 hSQ hSΩ hQy hSy
    set F₂ := lev2 Q S y with hF₂
    set R₂ := F₂ ⊓ perp Q F₂ with hR₂
    have hF₂inv : ∀ n ∈ N, ∀ v ∈ F₂, n v ∈ F₂ := fun n hn v hv =>
      map_mem_lev2 (hNQ n hn) (hNy n hn) (hnorm' n hn) hv
    have hR₂inv : ∀ n ∈ N, ∀ v ∈ R₂, n v ∈ R₂ := fun n hn v hv =>
      ⟨hF₂inv n hn v hv.1,
        map_mem_perp (hNQ n hn) (fun w hw => hF₂inv n⁻¹ (inv_mem hn) w hw) hv.2⟩
    have hR₂iso : ∀ u ∈ R₂, ∀ v ∈ R₂, polar Q u v = 0 := fun u hu v hv =>
      (mem_perp.mp hv.2) u hu.1
    have hyF₂ : y ∈ F₂ := ⟨OrthRestOdd.polar_self_eq_zero Q y, fun s hs => by
      rw [hSy s hs, sub_self]; exact zero_mem _⟩
    have hyR₂ : y ∈ R₂ := ⟨hyF₂, mem_perp.mpr fun w hw => by rw [polar_comm]; exact hw.1⟩
    obtain ⟨R₂₀, -, hR₂₀⟩ := exists_singularPart (Q := Q) R₂ hR₂iso
    obtain ⟨c, hc⟩ := exists_singular_comb (hR₂iso y hyR₂ z hzR₂) hQy
    refine ⟨R₂₀, fun h => ?_, fun n hn v hv => ?_, fun v hv => ((hR₂₀ v).mp hv).2⟩
    · have hmem : c • y + z ∈ R₂₀ := (hR₂₀ _).mpr ⟨R₂.add_mem (R₂.smul_mem c hyR₂) hzR₂, hc⟩
      rw [h, Submodule.mem_bot] at hmem
      apply hzy
      rw [eq_neg_of_add_eq_zero_right hmem]
      exact (K ∙ y).neg_mem ((K ∙ y).smul_mem c (Submodule.mem_span_singleton_self y))
    · rw [hR₂₀] at hv ⊢
      exact ⟨hR₂inv n hn v hv.1, by rw [hNQ n hn]; exact hv.2⟩
  · exact ⟨R₀, hR₀0, fun n hn v hv => by
      rw [hR₀] at hv ⊢
      exact ⟨hRinv n hn v hv.1, by rw [hNQ n hn]; exact hv.2⟩, fun v hv => ((hR₀ v).mp hv).2⟩

end OrthBstarOdd

end CFSG.StandardType
