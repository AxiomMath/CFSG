module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.OrthRot

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

namespace OmegaEven

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven
open scoped commutatorElement

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def diagGL : (ι → Kˣ) →* GL ι K :=
  (Units.map (Matrix.diagonalRingHom ι K).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : ι => K)).symm.toMonoidHom

theorem coe_diagGL (d : ι → Kˣ) :
    ((diagGL d : GL ι K) : Matrix ι ι K) = diagonal fun i => (d i : K) :=
  rfl

theorem mulVec_diagGL (d : ι → Kˣ) (v : ι → K) :
    ((diagGL d : GL ι K) : Matrix ι ι K) *ᵥ v = fun j => (d j : K) * v j := by
  funext j
  rw [coe_diagGL, mulVec_diagonal]

@[expose] noncomputable def permGL : Equiv.Perm ι →* GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits

theorem mulVec_permGL (σ : Equiv.Perm ι) (v : ι → K) :
    ((permGL σ : GL ι K) : Matrix ι ι K) *ᵥ v = v ∘ ⇑(σ⁻¹ : Equiv.Perm ι) := by
  change (Matrix.permMatrixHom (n := ι) (R := K) σ) *ᵥ v = _
  rw [Matrix.permMatrixHom_apply, permMatrix_mulVec]

theorem permGL_mul_diagGL (σ : Equiv.Perm ι) (e : ι → Kˣ) :
    (permGL σ : GL ι K) * diagGL e = diagGL (fun j => e (σ⁻¹ j)) * permGL σ :=
  OrthRot.gl_ext fun v => by
    rw [OrthRot.mul_mulVec, OrthRot.mul_mulVec, mulVec_diagGL, mulVec_permGL, mulVec_permGL,
      mulVec_diagGL]
    rfl

theorem diagGL_mem_statedOmega {Q : (ι → K) → K} {σ : Equiv.Perm ι}
    (hσ : ∀ v, Q (v ∘ σ) = Q v) {r : ℕ} (hr : Odd r) {d : ι → Kˣ} (hd : ∀ j, d j ^ r = 1)
    (hdQ : ∀ v, Q (fun j => (d j : K) * v j) = Q v) (hdσ : ∀ j, d (σ j) = (d j)⁻¹) :
    (diagGL d : GL ι K) ∈ StatedOmega Q := by
  set O : Subgroup (GL ι K) := Subgroup.closure
    {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} with hO
  have hΩO : StatedOmega Q = ⁅O, O⁆ := rfl
  rw [hΩO]
  obtain ⟨k, hk⟩ := hr
  set a : ι → Kˣ := d ^ (k + 1) with ha
  have haa : a * a = d := by
    funext j
    simp only [Pi.mul_apply, ha, Pi.pow_apply]
    rw [← pow_add, show k + 1 + (k + 1) = r + 1 by omega, pow_succ, hd j, one_mul]
  have haσ : ∀ j, a (σ j) = (a j)⁻¹ := fun j => by
    simp only [ha, Pi.pow_apply]
    rw [hdσ j, inv_pow]
  have hDO : (diagGL d : GL ι K) ∈ O := Subgroup.subset_closure (fun v => by
    rw [mulVec_diagGL]
    exact hdQ v)
  have hPO : (permGL σ : GL ι K) ∈ O := Subgroup.subset_closure (fun v => by
    rw [mulVec_permGL]
    have h := hσ (v ∘ ⇑(σ⁻¹ : Equiv.Perm ι))
    rw [show (v ∘ ⇑(σ⁻¹ : Equiv.Perm ι)) ∘ σ = v from funext fun j => by simp] at h
    exact h.symm)
  have haO : (diagGL a : GL ι K) ∈ O := by
    rw [ha, map_pow]
    exact Subgroup.pow_mem O hDO _
  have hconj : (permGL σ : GL ι K) * (diagGL a)⁻¹ = diagGL a * permGL σ := by
    rw [← map_inv, permGL_mul_diagGL]
    congr 2
    funext j
    rw [Pi.inv_apply]
    have h3 : σ (σ⁻¹ j) = j := by simp
    have := haσ (σ⁻¹ j)
    rw [h3] at this
    rw [this]
  have hcomm : ⁅(diagGL a : GL ι K), permGL σ⁆ = diagGL d := by
    calc ⁅(diagGL a : GL ι K), permGL σ⁆
        = diagGL a * (permGL σ * (diagGL a)⁻¹) * (permGL σ)⁻¹ := by
          rw [commutatorElement_def]
          simp only [mul_assoc]
      _ = diagGL a * diagGL a := by
          rw [hconj]
          simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = diagGL d := by rw [← map_mul, haa]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator haO hPO

theorem rootsOfUnity_pow_eq_one' {r : ℕ} (x : rootsOfUnity r K) : x ^ r = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity r (x : Kˣ)).mp x.2

theorem card_rootsOfUnity_of_dvd' [Finite K] {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card Kˣ) : Nat.card (rootsOfUnity r K) = r := by
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hprim : IsPrimitiveRoot ζ r := hζ ▸ IsPrimitiveRoot.orderOf ζ
  exact hprim.card_rootsOfUnity'

theorem le_pRank_torus [Finite K] {Q : (ι → K) → K} {σ : Equiv.Perm ι}
    (hσ : ∀ v, Q (v ∘ σ) = Q v) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hK : r ∣ Nat.card Kˣ) (E : (Fin k → Kˣ) →* (ι → Kˣ))
    (hEQ : ∀ t v, Q (fun j => ((E t j : Kˣ) : K) * v j) = Q v)
    (hEσ : ∀ t j, E t (σ j) = (E t j)⁻¹)
    (hE1 : ∀ t : Fin k → Kˣ, t ^ r = 1 → ∀ c : Kˣ, (∀ j, E t j = c) → t = 1) :
    k ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  have hμ := card_rootsOfUnity_of_dvd' (K := K) hr hK
  have hodd : Odd r := hr.odd_of_ne_two hr2
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  have hinc : ∀ s : Fin k → μ, (incl.compLeft (Fin k) s) ^ r = 1 := fun s => funext fun i => by
    rw [Pi.pow_apply, MonoidHom.compLeft_apply, Function.comp_apply, ← map_pow,
      rootsOfUnity_pow_eq_one', map_one, Pi.one_apply]
  set τ0 : (Fin k → μ) →* GL ι K := (diagGL.comp E).comp (incl.compLeft (Fin k)) with hτ0
  have hτ : ∀ s, τ0 s ∈ StatedOmega Q := fun s => by
    have ht := hinc s
    refine diagGL_mem_statedOmega hσ hodd (d := E (incl.compLeft (Fin k) s)) (fun j => ?_)
      (hEQ _) (hEσ _)
    have h := congrFun (show (E (incl.compLeft (Fin k) s)) ^ r = 1 by
      rw [← map_pow, ht, map_one]) j
    rwa [Pi.pow_apply, Pi.one_apply] at h
  let τ : (Fin k → μ) →* StatedOmega Q := τ0.codRestrict _ hτ
  let φ : (Fin k → μ) →* StatedProj (StatedOmega Q) := (QuotientGroup.mk' _).comp τ
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hs
    have hc' : Matrix.GeneralLinearGroup.scalar ι c = diagGL (E (incl.compLeft (Fin k) s)) := hc
    have hEc : ∀ j, E (incl.compLeft (Fin k) s) j = c := fun j => by
      have h1 := congrArg (fun A : GL ι K => (A : Matrix ι ι K) j j) hc'
      simp only [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        coe_diagGL] at h1
      exact (Units.ext h1).symm
    have h1 := hE1 _ (hinc s) c hEc
    rw [Subgroup.mem_bot]
    funext i
    exact Subtype.ext (congrFun h1 i)
  exact CFSG.SectionRank.le_pRank_of_injective hr.one_lt (fun a b => mul_comm a b)
    (fun a => funext fun i => by
      rw [Pi.pow_apply, rootsOfUnity_pow_eq_one', Pi.one_apply])
    (by rw [Nat.card_fun, hμ, Nat.card_fin]) φ hφ le_top

theorem unit_eq_one_of_sq_eq_one {r : ℕ} (hr : Odd r) {x : Kˣ} (h2 : x ^ 2 = 1) (hx : x ^ r = 1) :
    x = 1 := by
  obtain ⟨m, hm⟩ := hr
  have : x ^ r = x * (x ^ 2) ^ m := by rw [hm, pow_succ, pow_mul, mul_comm]
  rwa [this, h2, one_pow, mul_one] at hx

end Generic

section Plus

variable {K : Type} [Field K]

@[expose] def torusEntPlus (n : ℕ) (K : Type) [Field K] :
    (Fin n → Kˣ) →* (Fin n ⊕ Fin n → Kˣ) where
  toFun t := Sum.elim t fun i => (t i)⁻¹
  map_one' := by
    funext j
    rcases j with j | j <;> simp
  map_mul' s t := by
    funext j
    rcases j with j | j <;> simp [mul_inv, mul_comm]

theorem le_pRank_omegaPlus_torus [Finite K] {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hK : r ∣ Nat.card Kˣ) :
    n ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) := by
  refine le_pRank_torus (σ := Equiv.sumComm (Fin n) (Fin n)) (fun v => ?_) hr hr2 hK
    (torusEntPlus n K) (fun t v => ?_) (fun t j => ?_) (fun t ht c hc => ?_)
  · change ∑ i, v (Sum.inr i) * v (Sum.inl i) = ∑ i, v (Sum.inl i) * v (Sum.inr i)
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · change ∑ i, ((t i : K) * v (Sum.inl i)) * ((((t i)⁻¹ : Kˣ) : K) * v (Sum.inr i)) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i)
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (v (Sum.inl i) * v (Sum.inr i)) * (t i).mul_inv
  · rcases j with j | j <;> simp [torusEntPlus]
  · funext i
    have h1 := hc (Sum.inl i)
    have h2 := hc (Sum.inr i)
    simp only [torusEntPlus, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inl, Sum.elim_inr] at h1 h2
    refine unit_eq_one_of_sq_eq_one (hr.odd_of_ne_two hr2) ?_ (by
      simpa only [Pi.pow_apply, Pi.one_apply] using congrFun ht i)
    have h3 : t i = (t i)⁻¹ := h1.trans h2.symm
    rw [sq]
    calc t i * t i = t i * (t i)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _

end Plus

section Minus

variable {K : Type} [Field K]

@[expose] def torusEntMinus (m : ℕ) (K : Type) [Field K] :
    (Fin m → Kˣ) →* (Fin m ⊕ Fin m ⊕ Fin 2 → Kˣ) where
  toFun t := Sum.elim t (Sum.elim (fun i => (t i)⁻¹) fun _ => 1)
  map_one' := by
    funext j
    rcases j with j | j | j <;> simp
  map_mul' s t := by
    funext j
    rcases j with j | j | j <;> simp [mul_inv, mul_comm]

@[expose] def swapMinus (m : ℕ) : Fin m ⊕ Fin m ⊕ Fin 2 → Fin m ⊕ Fin m ⊕ Fin 2
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr k) => .inr (.inr k)

theorem swapMinus_swapMinus (m : ℕ) (j : Fin m ⊕ Fin m ⊕ Fin 2) :
    swapMinus m (swapMinus m j) = j := by
  rcases j with j | j | j <;> rfl

@[expose] def swapMinusPerm (m : ℕ) : Equiv.Perm (Fin m ⊕ Fin m ⊕ Fin 2) :=
  ⟨swapMinus m, swapMinus m, swapMinus_swapMinus m, swapMinus_swapMinus m⟩

theorem le_pRank_omegaMinus_torus [Finite K] {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hK : r ∣ Nat.card Kˣ) (b c : K) :
    n - 1 ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) := by
  refine le_pRank_torus (σ := swapMinusPerm (n - 1)) (fun v => ?_) hr hr2 hK
    (torusEntMinus (n - 1) K) (fun t v => ?_) (fun t j => ?_) (fun t ht c' hc => ?_)
  · change ∑ i : Fin (n - 1), v (Sum.inr (Sum.inl i)) * v (Sum.inl i) +
        v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
          c * v (Sum.inr (Sum.inr 1)) ^ 2 =
      ∑ i : Fin (n - 1), v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
        v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
          c * v (Sum.inr (Sum.inr 1)) ^ 2
    rw [Finset.sum_congr rfl fun i _ => mul_comm (v (Sum.inr (Sum.inl i))) (v (Sum.inl i))]
  · change ∑ i : Fin (n - 1), ((t i : K) * v (Sum.inl i)) *
        ((((t i)⁻¹ : Kˣ) : K) * v (Sum.inr (Sum.inl i))) +
        (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 0))) ^ 2 +
        b * (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 0))) *
          (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 1))) +
        c * (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 1))) ^ 2 =
      ∑ i : Fin (n - 1), v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
        v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
          c * v (Sum.inr (Sum.inr 1)) ^ 2
    simp only [Units.val_one, one_mul]
    rw [Finset.sum_congr rfl fun i _ => (by
      linear_combination (v (Sum.inl i) * v (Sum.inr (Sum.inl i))) * (t i).mul_inv :
      ((t i : K) * v (Sum.inl i)) * ((((t i)⁻¹ : Kˣ) : K) * v (Sum.inr (Sum.inl i))) =
        v (Sum.inl i) * v (Sum.inr (Sum.inl i)))]
  · rcases j with j | j | j <;> simp [torusEntMinus, swapMinusPerm, swapMinus]
  · funext i
    have h0 := hc (Sum.inr (Sum.inr 0))
    have h1 := hc (Sum.inl i)
    simp only [torusEntMinus, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inl, Sum.elim_inr] at h0 h1
    rw [Pi.one_apply]
    exact h1.trans h0.symm

end Minus

end OmegaEven

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
