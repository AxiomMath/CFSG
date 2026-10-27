module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K]

theorem isElemAbelian_bot {G : Type*} [Group G] : IsElemAbelian p (⊥ : Subgroup G) :=
  ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun y hy => by
    rw [Subgroup.mem_bot.mp hy, one_pow]⟩

theorem ggTorusLift_zero {R : Type} [Group R] (h2 : 2 ∣ Nat.card R) : GGTorusLift p 0 R := by
  intro L' _ _ ψ hψ _ _
  have h2' : 2 ∣ Nat.card L' := h2.trans (Subgroup.card_dvd_of_surjective (f := ψ) hψ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := L') 2 h2'
  refine ⟨Subgroup.zpowers u, ⊥, ?_, ?_, bot_le, isElemAbelian_bot, ?_, bot_inf_eq _⟩
  · intro h
    have hu1 : u = 1 := by
      have : u ∈ (⊥ : Subgroup L') := h ▸ Subgroup.mem_zpowers u
      exact Subgroup.mem_bot.mp this
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  · rw [Subgroup.card_bot, pow_zero]

theorem two_dvd_card_projectiveSL [Finite K] [CharP K 2] (hd : 2 ≤ d) :
    2 ∣ Nat.card (projectiveSL d K) := by
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  set t : SpecialLinearGroup (Fin d) K := SpecialLinearGroup.transvection h01 1 with ht
  have ht1 : proj d K t ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp [ht, CFSG.LinearGroups.coe_transvection] at h1
  have ht2 : proj d K t ^ 2 = 1 := by
    rw [← map_pow, ht, CFSG.RankThree.CALinearPlane.transvection_pow, Nat.cast_ofNat,
      CharTwo.two_eq_zero, zero_mul]
    have : SpecialLinearGroup.transvection h01 (0 : K) = 1 :=
      Matrix.SpecialLinearGroup.transvection_coeff_zero h01
    rw [this, map_one]
  have hord : orderOf (proj d K t) = 2 := orderOf_eq_prime ht2 ht1
  exact hord ▸ orderOf_dvd_natCard _

theorem conj_transvection_of_diagonal {g : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hg : (g : Matrix (Fin d) (Fin d) K) = diagonal t) {i j : Fin d} (hij : i ≠ j) (c : K) :
    g * SpecialLinearGroup.transvection hij c * g⁻¹ =
      SpecialLinearGroup.transvection hij (t i * c * (t j)⁻¹) := by
  have ht0 : ∀ k, t k ≠ 0 := by
    intro k hk
    have h1 := g.2
    rw [hg, det_diagonal] at h1
    exact one_ne_zero (h1 ▸ Finset.prod_eq_zero (Finset.mem_univ k) hk)
  rw [mul_inv_eq_iff_eq_mul]
  ext a b
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection, hg,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hia : ¬(i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [hia]
  · by_cases hia : i = a <;> by_cases hjb : j = b
    · subst hia hjb
      simp only [hab, ite_false, true_and, ite_true, zero_add]
      field_simp [ht0 j]
    · simp [hab, hia, hjb]
    · simp [hab, hia, hjb]
    · simp [hab, hia, hjb]

theorem le_normalizer_rootGroup {E₀ : Subgroup (SpecialLinearGroup (Fin d) K)}
    (hdiag : ∀ g ∈ E₀, ∃ t : Fin d → K, (g : Matrix (Fin d) (Fin d) K) = diagonal t)
    {i j : Fin d} (hij : i ≠ j) :
    E₀ ≤ Subgroup.normalizer
      (((SpecialLinearGroup.transvectionHom hij : Multiplicative K →* _).range : Subgroup _) :
        Set (SpecialLinearGroup (Fin d) K)) := by
  apply le_normalizer_of_map_conj_le
  intro g hg
  obtain ⟨t, ht⟩ := hdiag g hg
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  refine ⟨Multiplicative.ofAdd (t i * Multiplicative.toAdd c * (t j)⁻¹), ?_⟩
  rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]
  change _ = g * SpecialLinearGroup.transvectionHom hij c * g⁻¹
  rw [SpecialLinearGroup.transvectionHom_apply, conj_transvection_of_diagonal ht hij]

theorem ggTorusLift_of_diagonal [Finite K] [CharP K 2] (hd : 2 ≤ d) (hsec : SLHasSections d K)
    {r : ℕ} {E₀ : Subgroup (SpecialLinearGroup (Fin d) K)} (hE₀ : IsElemAbelian p E₀)
    (hcard : Nat.card E₀ = p ^ r) (hscal : ∀ g ∈ E₀, g ∈ scalars d K → g = 1)
    (hdiag : ∀ g ∈ E₀, ∃ t : Fin d → K, (g : Matrix (Fin d) (Fin d) K) = diagonal t) :
    GGTorusLift p r (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨φ, -, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  have hkerφ : ∀ g, φ g = 1 → g ∈ scalars d K := fun g hg =>
    proj_eq_one_iff.mp (by rw [← hφ, hg, map_one])
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  set U₀ := (SpecialLinearGroup.transvectionHom h01 : Multiplicative K →* _).range with hU₀
  have hinjE : ∀ g ∈ E₀, ∀ h ∈ E₀, φ g = φ h → g = h := by
    intro g hg h hh hgh
    have h1 : φ (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hscal _ (E₀.mul_mem (E₀.inv_mem hg) hh) (hkerφ _ h1))
  refine ⟨U₀.map φ, E₀.map φ, ?_, ?_, ?_, TableB.isElemAbelian_map hE₀ φ, ?_, ?_⟩
  · intro hbot
    have hmem : φ (SpecialLinearGroup.transvection h01 1) ∈ U₀.map φ :=
      ⟨_, ⟨Multiplicative.ofAdd 1, by rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]⟩,
        rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (hkerφ _ hmem)
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp [CFSG.LinearGroups.coe_transvection] at h1
  · refine IsPGroup.map (fun x => ⟨1, ?_⟩) φ
    obtain ⟨y, c, hc⟩ := x
    have h2 : y ^ 2 = 1 := by
      rw [← hc, SpecialLinearGroup.transvectionHom_apply,
        CFSG.RankThree.CALinearPlane.transvection_pow, Nat.cast_ofNat, CharTwo.two_eq_zero,
        zero_mul]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero h01
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h2
  · exact (Subgroup.map_mono (le_normalizer_rootGroup hdiag h01)).trans
      (Subgroup.le_normalizer_map φ)
  · rw [← hcard]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun g : E₀ => (⟨φ g, g, g.2, rfl⟩ : E₀.map φ))
      ⟨fun g h hgh => Subtype.ext (hinjE g g.2 h h.2 (congrArg Subtype.val hgh)), ?_⟩)
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨g, hg, rfl⟩, hx⟩
    have h1 : proj d K g = 1 := by rw [← hφ]; exact hx
    rw [hscal g hg (proj_eq_one_iff.mp h1), map_one]
    exact Subgroup.one_mem _

section Tori

@[expose] def piProd (p d : ℕ) (K : Type) [Field K] :
    (Fin d → rootsOfUnity p K) →* rootsOfUnity p K where
  toFun u := ∏ i, u i
  map_one' := by simp
  map_mul' u v := by simp [Finset.prod_mul_distrib]

@[expose] def rootEnt (u : Fin d → rootsOfUnity p K) (i : Fin d) : K := ((u i : Kˣ) : K)

theorem prod_rootEnt (u : Fin d → rootsOfUnity p K) :
    ∏ i, rootEnt u i = (((piProd p d K u : rootsOfUnity p K) : Kˣ) : K) := by
  simp [rootEnt, piProd]

@[expose] noncomputable def diagSL (p d : ℕ) (K : Type) [Field K] :
    (piProd p d K).ker →* SpecialLinearGroup (Fin d) K where
  toFun u := ⟨diagonal (rootEnt (u : Fin d → rootsOfUnity p K)), by
    rw [det_diagonal, prod_rootEnt, MonoidHom.mem_ker.mp u.2]
    rfl⟩
  map_one' := by
    ext i j
    simp [rootEnt, Matrix.one_apply, diagonal_apply]
  map_mul' u v := by
    apply Subtype.ext
    change diagonal (rootEnt ((u * v : (piProd p d K).ker) : Fin d → rootsOfUnity p K)) =
      diagonal (rootEnt (u : Fin d → rootsOfUnity p K)) *
        diagonal (rootEnt (v : Fin d → rootsOfUnity p K))
    rw [diagonal_mul_diagonal]
    rfl

theorem coe_diagSL (u : (piProd p d K).ker) :
    (diagSL p d K u : Matrix (Fin d) (Fin d) K) =
      diagonal (rootEnt (u : Fin d → rootsOfUnity p K)) :=
  rfl

theorem diagSL_injective : Function.Injective (diagSL p d K) := by
  intro u v huv
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Units.ext
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin d) K => (g : Matrix (Fin d) (Fin d) K) i i)
    huv
  simpa [coe_diagSL, rootEnt] using h1

theorem isElemAbelian_map_diagSL (T : Subgroup (piProd p d K).ker) :
    IsElemAbelian p (T.map (diagSL p d K)) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, u, -, rfl⟩ ⟨_, v, -, rfl⟩
    apply Subtype.ext
    change diagSL p d K u * diagSL p d K v = diagSL p d K v * diagSL p d K u
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨u, -, rfl⟩
    rw [← map_pow]
    have hu : ∀ i, ((u : Fin d → rootsOfUnity p K) i) ^ p = 1 := fun i =>
      Subtype.ext ((mem_rootsOfUnity _ _).mp ((u : Fin d → rootsOfUnity p K) i).2)
    have : u ^ p = 1 := Subtype.ext (funext fun i => by simpa using hu i)
    rw [this, map_one]

theorem diagonal_of_mem_map_diagSL (T : Subgroup (piProd p d K).ker) :
    ∀ g ∈ T.map (diagSL p d K), ∃ t : Fin d → K, (g : Matrix (Fin d) (Fin d) K) = diagonal t := by
  rintro _ ⟨u, -, rfl⟩
  exact ⟨_, coe_diagSL u⟩

end Tori

theorem card_rootsOfUnity_of_dvd [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    Nat.card (rootsOfUnity p K) = p := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have : NeZero p := ⟨hp.ne_zero⟩
  exact hζ.card_rootsOfUnity

theorem piProd_surjective (hd : 0 < d) : Function.Surjective (piProd p d K) := by
  classical
  intro v
  refine ⟨Pi.mulSingle ⟨0, hd⟩ v, ?_⟩
  simp [piProd]

theorem card_ker_piProd [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) :
    Nat.card (piProd p d K).ker = p ^ (d - 1) := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f := piProd p d K) (piProd_surjective hd)
  rw [card_rootsOfUnity_of_dvd hp hpK, Nat.card_fun, card_rootsOfUnity_of_dvd hp hpK,
    Nat.card_fin, show p ^ d = p ^ (d - 1) * p by rw [← pow_succ, Nat.sub_add_cancel hd]] at h1
  exact Nat.eq_of_mul_eq_mul_right hp.pos h1

@[expose] def evalOne (hd : 2 ≤ d) : (piProd p d K).ker →* rootsOfUnity p K :=
  (Pi.evalMonoidHom (fun _ : Fin d => rootsOfUnity p K) ⟨1, by omega⟩).comp
    (piProd p d K).ker.subtype

theorem evalOne_apply (hd : 2 ≤ d) (u : (piProd p d K).ker) :
    evalOne hd u = (u : Fin d → rootsOfUnity p K) ⟨1, by omega⟩ :=
  rfl

theorem evalOne_surjective (hd : 2 ≤ d) : Function.Surjective (evalOne (p := p) (K := K) hd) := by
  classical
  intro v
  have h10 : (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := by simp
  refine ⟨⟨Pi.mulSingle ⟨1, by omega⟩ v * Pi.mulSingle ⟨0, by omega⟩ v⁻¹, ?_⟩, ?_⟩
  · rw [MonoidHom.mem_ker]
    simp [piProd, Finset.prod_mul_distrib]
  · rw [evalOne_apply]
    simp [h10]

theorem card_ker_evalOne [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 2 ≤ d) :
    Nat.card (evalOne (p := p) (K := K) hd).ker = p ^ (d - 2) := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f := evalOne (p := p) (K := K) hd)
    (evalOne_surjective hd)
  rw [card_rootsOfUnity_of_dvd hp hpK, card_ker_piProd hp hpK (by omega),
    show p ^ (d - 1) = p ^ (d - 2) * p by rw [← pow_succ]; congr 1; omega] at h1
  exact Nat.eq_of_mul_eq_mul_right hp.pos h1

theorem ggTorusLift_coprime [Finite K] [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 2 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGTorusLift p (d - 1) (projectiveSL d K) := by
  refine ggTorusLift_of_diagonal hd hsec
    (E₀ := (⊤ : Subgroup (piProd p d K).ker).map (diagSL p d K))
    (isElemAbelian_map_diagSL ⊤) ?_ ?_ (diagonal_of_mem_map_diagSL ⊤)
  · rw [Subgroup.card_map_of_injective diagSL_injective, Subgroup.card_top,
      card_ker_piProd hp hpK (by omega)]
  · intro g hg hgs
    exact eq_one_of_scalar_of_pow hpd hgs ((isElemAbelian_map_diagSL ⊤).2 g hg)

theorem ggTorusLift_sub_two [Finite K] [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 2 ≤ d) (hsec : SLHasSections d K) : GGTorusLift p (d - 2) (projectiveSL d K) := by
  refine ggTorusLift_of_diagonal hd hsec
    (E₀ := (evalOne (p := p) (K := K) hd).ker.map (diagSL p d K))
    (isElemAbelian_map_diagSL _) ?_ ?_ (diagonal_of_mem_map_diagSL _)
  · rw [Subgroup.card_map_of_injective diagSL_injective, card_ker_evalOne hp hpK hd]
  · rintro _ ⟨u, hu, rfl⟩ hgs
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hgs
    have hu1 : (u : Fin d → rootsOfUnity p K) ⟨1, by omega⟩ = 1 := hu
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨1, by omega⟩ ⟨1, by omega⟩) hc
    simp only [coe_diagSL, diagonal_apply_eq, scalar_apply, rootEnt, hu1] at h1
    have hc1 : (c : K) = 1 := by rw [← h1]; rfl
    ext i j
    rw [hc, hc1, map_one]
    rfl

end CFSG.StandardType.TypeA
