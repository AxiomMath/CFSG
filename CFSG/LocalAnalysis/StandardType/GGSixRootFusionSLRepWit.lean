module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepCases

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SLRep

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
  {p : ℕ} {B Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r : G}
  {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) F}

omit [Finite F] [CharP F 2] in
theorem inv_pow_pow_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ p) (a : ℕ) : (ζ⁻¹ ^ a) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]

omit [Finite F] [CharP F 2] in
theorem inv_pow_ne {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hζ0 : ζ ≠ 0) {a : ℕ}
    (ha : ¬ p ∣ a + 1) : ζ⁻¹ ^ a ≠ ζ := by
  intro h
  apply ha
  rw [← hζ.pow_eq_one_iff_dvd, pow_succ]
  calc ζ ^ a * ζ = ζ ^ a * ζ⁻¹ ^ a := by rw [h]
    _ = 1 := by rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hζ0)]

theorem ggRootFusionWitnessAlt_mid_coprime (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {l : ℕ} (hl2 : 2 ≤ l) (hl : 2 * l < n)
    (hpn : ¬ p ∣ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hc.prime.ne_zero
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  set δ : Fin n → F := Function.update (fun _ => ζ) l' (ζ⁻¹ ^ (n - 1)) with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, prod_update_const, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hζ0)]
  have hval : ∀ i, i ≠ l' → δ i = ζ := fun i hi => by
    rw [hδdef, Function.update_of_ne hi]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hi : i = l'
    · rw [hi, hδdef, Function.update_self]
      exact inv_pow_pow_eq_one hζ _
    · rw [hval i hi, hζ.pow_eq_one]
  have hne : ζ⁻¹ ^ (n - 1) ≠ ζ := inv_pow_ne hζ hζ0 (by rwa [Nat.sub_add_cancel (by omega)])
  have hcS : ({l'} : Finset (Fin n))ᶜ.card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  refine ggRootFusionWitnessAlt_of_inner hc hle hδ hδp (S := ({l'} : Finset (Fin n))ᶜ) (μ := ζ)
    (fun i hi => hval i (by simpa using hi)) (fun i hi => ?_) ?_ ?_ ?_ (i₁ := l')
    (by simp) 1 ?_
  · obtain rfl : i = l' := by simpa using hi
    rw [hδdef, Function.update_self]
    exact hne
  · rw [compl_compl, Finset.card_singleton, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, Finset.card_singleton]
    omega
  · intro a c hc' ha
    simp only [Equiv.Perm.one_apply] at hc' ha
    rw [hval a (fun h => by rw [h] at ha; simp only [hl'] at ha; omega),
      hval c (fun h => by rw [h] at hc'; simp only [hl'] at hc'; omega)]

theorem ggRootFusionWitnessAlt_pair_coprime (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {l : ℕ} (hl2 : 2 ≤ l) (hn : n = 2 * l) (h5 : 5 ≤ n)
    (hpn : ¬ p ∣ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hc.prime.ne_zero
  set o' : Fin n := ⟨0, by omega⟩ with ho'
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  have hol : o' ≠ l' := by
    intro h
    have := congrArg Fin.val h
    simp only [ho', hl'] at this
    omega
  set ν : F := ζ⁻¹ ^ (l - 1) with hν
  set δ : Fin n → F := Function.update (Function.update (fun _ => ζ) o' ν) l' ν with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, prod_update_update_const hol, hν, show n - 2 = (l - 1) + (l - 1) by omega,
      pow_add, inv_pow]
    have h0 : ζ ^ (l - 1) ≠ 0 := pow_ne_zero _ hζ0
    field_simp
  have hδl : δ l' = ν := by rw [hδdef, Function.update_self]
  have hδo : δ o' = ν := by
    rw [hδdef, Function.update_of_ne hol, Function.update_self]
  have hval : ∀ i, i ≠ o' → i ≠ l' → δ i = ζ := fun i hio hil => by
    rw [hδdef, Function.update_of_ne hil, Function.update_of_ne hio]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hil : i = l'
    · rw [hil, hδl, hν]
      exact inv_pow_pow_eq_one hζ _
    by_cases hio : i = o'
    · rw [hio, hδo, hν]
      exact inv_pow_pow_eq_one hζ _
    · rw [hval i hio hil, hζ.pow_eq_one]
  have hne : ν ≠ ζ := inv_pow_ne hζ hζ0 (fun h => hpn (by
    rw [Nat.sub_add_cancel (by omega)] at h
    exact hn ▸ dvd_mul_of_dvd_right h 2))
  have hpairc : ({o', l'} : Finset (Fin n)).card = 2 := Finset.card_pair hol
  have hcS : ({o', l'} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hpairc]
  refine ggRootFusionWitnessAlt_of_inner hc hle hδ hδp (S := ({o', l'} : Finset (Fin n))ᶜ)
    (μ := ζ) (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ ?_ (i₁ := l') (by simp) 1 ?_
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hval i hi.1 hi.2
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, not_and,
      not_not] at hi
    by_cases hio : i = o'
    · rw [hio, hδo]
      exact hne
    · rw [hi hio, hδl]
      exact hne
  · rw [compl_compl, hpairc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, hpairc]
  · intro a c hc' ha
    simp only [Equiv.Perm.one_apply] at hc' ha
    by_cases hc0 : (c : ℕ) = 0
    · have hco : c = o' := Fin.ext hc0
      have hal : a = l' := Fin.ext (by simp only [hl']; omega)
      rw [hco, hal, hδo, hδl]
    · rw [hval a (fun h => by rw [h] at ha; simp only [ho'] at ha; omega)
          (fun h => by rw [h] at ha; simp only [hl'] at ha; omega),
        hval c (fun h => by rw [h] at hc0; exact hc0 rfl)
          (fun h => by rw [h] at hc'; simp only [hl'] at hc'; omega)]

theorem ggRootFusionWitnessAlt_mid_two (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {l : ℕ} (hl2 : 2 ≤ l) (hl : 2 * l + 2 ≤ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hc.prime.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hc.prime.one_lt
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  set l1 : Fin n := ⟨l + 1, by omega⟩ with hl1
  have hll : l' ≠ l1 := by
    intro h
    have := congrArg Fin.val h
    simp only [hl', hl1] at this
    omega
  set δ : Fin n → F := Function.update (Function.update (fun _ => 1) l' ζ) l1 ζ⁻¹ with hδdef
  have hδ : ∏ i, δ i = 1 := by
    rw [hδdef, prod_update_update_const hll, one_pow, mul_one, inv_mul_cancel₀ hζ0]
  have hδ1 : δ l1 = ζ⁻¹ := by rw [hδdef, Function.update_self]
  have hδl : δ l' = ζ := by
    rw [hδdef, Function.update_of_ne hll, Function.update_self]
  have hval : ∀ i, i ≠ l' → i ≠ l1 → δ i = 1 := fun i hil hi1 => by
    rw [hδdef, Function.update_of_ne hi1, Function.update_of_ne hil]
  have hδp : ∀ i, δ i ^ p = 1 := by
    intro i
    by_cases hi1 : i = l1
    · rw [hi1, hδ1, inv_pow, hζ.pow_eq_one, inv_one]
    by_cases hil : i = l'
    · rw [hil, hδl, hζ.pow_eq_one]
    · rw [hval i hil hi1, one_pow]
  have hpairc : ({l', l1} : Finset (Fin n)).card = 2 := Finset.card_pair hll
  have hcS : ({l', l1} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hpairc]
  refine ggRootFusionWitnessAlt_of_inner hc hle hδ hδp (S := ({l', l1} : Finset (Fin n))ᶜ)
    (μ := 1) (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ ?_ (i₁ := l') (by simp) 1 ?_
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hval i hi.1 hi.2
  · simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, not_and,
      not_not] at hi
    by_cases hil : i = l'
    · rw [hil, hδl]
      exact hζ1
    · rw [hi hil, hδ1]
      exact inv_ne_one.mpr hζ1
  · rw [compl_compl, hpairc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, hpairc]
  · intro a c hc' ha
    simp only [Equiv.Perm.one_apply] at hc' ha
    rw [hval a (fun h => by rw [h] at ha; simp only [hl'] at ha; omega)
        (fun h => by rw [h] at ha; simp only [hl1] at ha; omega),
      hval c (fun h => by rw [h] at hc'; simp only [hl'] at hc'; omega)
        (fun h => by rw [h] at hc'; simp only [hl1] at hc'; omega)]

omit [Finite F] [CharP F 2] in
@[expose] def GGFrameSingle (φ : Matrix.SpecialLinearGroup (Fin n) F →* G) (b : G) : Prop :=
  b ≠ 1 ∧ ∃ (D : GL (Fin n) F) (t : Fin n → F) (j : Fin n),
    (D : Matrix (Fin n) (Fin n) F) = diagonal t ∧ (∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) ∧
      ∀ i i', i ≠ j → i' ≠ j → t i = t i'

omit [Finite F] [CharP F 2] in
theorem ne_of_single {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {b : G} (hb1 : b ≠ 1)
    {D : GL (Fin n) F} {t : Fin n → F} (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) {j : Fin n}
    (hconst : ∀ i i', i ≠ j → i' ≠ j → t i = t i') {i : Fin n} (hij : i ≠ j) : t j ≠ t i := by
  intro h
  apply hb1
  have hall : ∀ a c, t a = t c := by
    have hv : ∀ a, t a = t i := fun a => by
      by_cases ha : a = j
      · rw [ha, h]
      · exact hconst a i ha hij
    intro a c
    rw [hv a, hv c]
  refine eq_of_act_eq hcent fun s => ?_
  rw [hb, slConj_eq_self_of_const hD hall, one_mul, inv_one, mul_one]

theorem exists_ne_fin (hn : 2 ≤ n) (j : Fin n) : ∃ i : Fin n, i ≠ j := by
  by_cases hj : (j : ℕ) = 0
  · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; simp only at this; omega⟩
  · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; simp only at this; omega⟩

theorem ggRootFusionWitnessAlt_single_mid (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    {l : ℕ} (hl2 : 2 ≤ l) (hl : 2 * l < n) {b₁ : G} (hb₁ : b₁ ∈ Bs)
    (hs : GGFrameSingle (ggFrame ψ A₀) b₁) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  obtain ⟨hb1, D₁, τ₁, j, hD₁, hact, hconst⟩ := hs
  have hcent' : Subgroup.centralizer ((ggFrame ψ A₀).range : Set G) = ⊥ := by
    rw [range_ggFrame, hc.range]
    exact hc.cent
  obtain ⟨i, hij⟩ := exists_ne_fin (by omega) j
  have hν := ne_of_single hcent' hb1 hD₁ hact hconst hij
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  have hcS : ({j} : Finset (Fin n))ᶜ.card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  refine ggRootFusionWitnessAlt_of_frame hc hle hb₁ hb1 hD₁ hact
    (S := ({j} : Finset (Fin n))ᶜ) (μ := τ₁ i) (fun a ha => hconst a i (by simpa using ha) hij)
    (fun a ha => by obtain rfl : a = j := by simpa using ha
                    exact hν) ?_ ?_ ?_ (i₁ := j) (by simp) (Equiv.swap j l') ?_
  · rw [compl_compl, Finset.card_singleton, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, Finset.card_singleton]
    omega
  · intro a c hc' ha
    have hcj : c ≠ j := by
      rintro rfl
      rw [Equiv.swap_apply_left] at hc'
      simp only [hl'] at hc'
      omega
    have haj : a ≠ j := by
      rintro rfl
      rw [Equiv.swap_apply_left] at ha
      simp only [hl'] at ha
      omega
    exact hconst a c haj hcj

theorem ggRootFusionWitnessAlt_single_pair (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M)
    {l : ℕ} (hl2 : 2 ≤ l) (hn : n = 2 * l) (h5 : 5 ≤ n) {b₁ : G} (hb₁ : b₁ ∈ Bs)
    (hs : GGFrameSingle (ggFrame ψ A₀) b₁) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  obtain ⟨hb1, D₁, τ₁, j, hD₁, hact, hconst⟩ := hs
  have hcent' : Subgroup.centralizer ((ggFrame ψ A₀).range : Set G) = ⊥ := by
    rw [range_ggFrame, hc.range]
    exact hc.cent
  have hkerφ := ker_ggFrame_le hc.ker A₀
  have hp := hc.prime
  have hp3 : 3 ≤ p := by have := hp.two_le; have := hc.odd; omega
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hc.odd
  obtain ⟨i, hij⟩ := exists_ne_fin (by omega) j
  set μ := τ₁ i with hμ
  have hν := ne_of_single hcent' hb1 hD₁ hact hconst hij
  have hμ0 : μ ≠ 0 := ne_zero_of_diagonal hD₁ i
  have hval₁ : ∀ a, a ≠ j → τ₁ a = μ := fun a ha => hconst a i ha hij
  set ρ := τ₁ j / μ with hρ
  have hρp : ρ ^ p = 1 := by
    rw [hρ, div_pow, pow_eq_pow_of_frame hkerφ (hc.bstar.2.1.2 b₁ hb₁) hD₁ hact j i,
      div_self (pow_ne_zero _ hμ0)]
  have hρ1 : ρ ≠ 1 := fun h => hν ((div_eq_one_iff_eq hμ0).mp h)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ρ = p := orderOf_eq_prime hρp hρ1
  set e₁ := ρ ^ ((p - 1) / 2) with he₁
  set e₂ := ρ ^ ((p + 1) / 2) with he₂
  have he12 : e₂ * e₁ = 1 := by
    rw [he₁, he₂, ← pow_add, show (p + 1) / 2 + (p - 1) / 2 = p by omega, hρp]
  have hτj : τ₁ j * e₁ = μ * e₂ := by
    have h1 : τ₁ j = μ * ρ := by rw [hρ]; field_simp
    rw [h1, he₁, he₂, mul_assoc, ← pow_succ', show (p - 1) / 2 + 1 = (p + 1) / 2 by omega]
  have he2 : e₂ ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hνμ : μ * e₂ ≠ μ := fun h => he2 (by
    have := mul_left_cancel₀ hμ0 (h.trans (mul_one μ).symm)
    exact this)
  set o' : Fin n := ⟨0, by omega⟩ with ho'
  set l' : Fin n := ⟨l, by omega⟩ with hl'
  have hol : o' ≠ l' := by
    intro h
    have := congrArg Fin.val h
    simp only [ho', hl'] at this
    omega
  set σ : Equiv.Perm (Fin n) := Equiv.swap j o' with hσ
  set j₂ := σ l' with hj₂
  have hσj : σ j = o' := Equiv.swap_apply_left j o'
  have hσj₂ : σ j₂ = l' := Equiv.swap_apply_self j o' l'
  have hjj : j ≠ j₂ := by
    intro h
    apply hol
    rw [← hσj, ← hσj₂, h]
  set δ : Fin n → F := Function.update (Function.update (fun _ => 1) j e₁) j₂ e₂ with hδdef
  have hδ : ∏ k, δ k = 1 := by
    rw [hδdef, prod_update_update_const hjj, one_pow, mul_one, he12]
  have hδj₂ : δ j₂ = e₂ := by rw [hδdef, Function.update_self]
  have hδj : δ j = e₁ := by rw [hδdef, Function.update_of_ne hjj, Function.update_self]
  have hδo : ∀ a, a ≠ j → a ≠ j₂ → δ a = 1 := fun a haj ha2 => by
    rw [hδdef, Function.update_of_ne ha2, Function.update_of_ne haj]
  have hδp : ∀ k, δ k ^ p = 1 := by
    intro k
    by_cases h2 : k = j₂
    · rw [h2, hδj₂, he₂, ← pow_mul, mul_comm, pow_mul, hρp, one_pow]
    by_cases h1 : k = j
    · rw [h1, hδj, he₁, ← pow_mul, mul_comm, pow_mul, hρp, one_pow]
    · rw [hδo k h1 h2, one_pow]
  set d := ggDiagSL δ hδ with hd
  have hdδ : (d : Matrix (Fin n) (Fin n) F) = diagonal δ := rfl
  have hdBs := mem_of_frame_diagonal_inner hc.bstar hc.frame hdδ (ggDiagSL_pow_eq_one hδ hδp)
  set τ₂ : Fin n → F := fun k => τ₁ k * δ k with hτ₂
  have hD₂ : ((D₁ * Matrix.SpecialLinearGroup.toGL d : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = diagonal τ₂ := by
    rw [Units.val_mul, hD₁]
    change diagonal τ₁ * diagonal δ = _
    rw [diagonal_mul_diagonal]
  have hact₂ := mul_act hact (act_map (ggFrame ψ A₀) d)
  have hv₂ : ∀ a, a ≠ j → a ≠ j₂ → τ₂ a = μ := fun a haj ha2 => by
    simp only [hτ₂]
    rw [hval₁ a haj, hδo a haj ha2, mul_one]
  have hvj : τ₂ j = μ * e₂ := by simp only [hτ₂]; rw [hδj, hτj]
  have hvj₂ : τ₂ j₂ = μ * e₂ := by
    simp only [hτ₂]
    rw [hδj₂, hval₁ j₂ (Ne.symm hjj)]
  have hpairc : ({j, j₂} : Finset (Fin n)).card = 2 := Finset.card_pair hjj
  have hcS : ({j, j₂} : Finset (Fin n))ᶜ.card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hpairc]
  obtain ⟨i₀, hi₀⟩ : (({j, j₂} : Finset (Fin n))ᶜ).Nonempty :=
    Finset.card_pos.mp (by rw [hcS]; omega)
  have hi₀' : i₀ ≠ j ∧ i₀ ≠ j₂ := by simpa using hi₀
  have hb₂1 : b₁ * ggFrame ψ A₀ d ≠ 1 :=
    ne_one_of_frame hkerφ hD₂ hact₂ (i := j) (j := i₀)
      (by rw [hvj, hv₂ i₀ hi₀'.1 hi₀'.2]; exact hνμ)
  refine ggRootFusionWitnessAlt_of_frame hc hle (Bs.mul_mem hb₁ hdBs) hb₂1 hD₂ hact₂
    (S := ({j, j₂} : Finset (Fin n))ᶜ) (μ := μ) (fun a ha => ?_) (fun a ha => ?_) ?_ ?_ ?_
    (i₁ := j) (by simp) σ ?_
  · have ha' : a ≠ j ∧ a ≠ j₂ := by simpa using ha
    exact hv₂ a ha'.1 ha'.2
  · have ha'' : ¬a = j → a = j₂ := by simpa using ha
    rcases or_iff_not_imp_left.mpr ha'' with rfl | rfl
    · rw [hvj]; exact hνμ
    · rw [hvj₂]; exact hνμ
  · rw [compl_compl, hpairc, hcS]
    omega
  · rw [hcS]
    omega
  · rw [compl_compl, hpairc]
  · intro a c hc' ha
    by_cases hc0 : σ c = o'
    · have hcj : c = j := by rw [← hσj] at hc0; exact σ.injective hc0
      have hal : σ a = l' := Fin.ext (by rw [ha, hc0]; simp only [ho', hl']; omega)
      have haj₂ : a = j₂ := by rw [← hσj₂] at hal; exact σ.injective hal
      rw [hcj, haj₂, hvj, hvj₂]
    · have hcj : c ≠ j := fun h => hc0 (by rw [h, hσj])
      have hcj₂ : c ≠ j₂ := fun h => by
        rw [h, hσj₂] at hc'
        simp only [hl'] at hc'
        omega
      have hc0' : (σ c : ℕ) ≠ 0 := fun h => hc0 (Fin.ext h)
      have haj : a ≠ j := fun h => by
        rw [h, hσj] at ha
        simp only [ho'] at ha
        omega
      have haj₂ : a ≠ j₂ := fun h => by
        rw [h, hσj₂] at ha
        simp only [hl'] at ha
        omega
      rw [hv₂ a haj haj₂, hv₂ c hcj hcj₂]

end SLRep

end CFSG.StandardType
