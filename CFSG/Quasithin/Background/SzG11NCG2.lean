module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.SzG11NC

open CFSG.Open CFSG.Quasithin.G11

section Zorn

variable {K : Type} [Field K]

@[expose] def zornUnit : quasithinZorn K := (1, 0, 0, 1)

theorem zornMul_zornUnit_left (y : quasithinZorn K) : quasithinZornMul zornUnit y = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp [quasithinZornMul, zornUnit, quasithinCross]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp

theorem zornMul_zornUnit_right (y : quasithinZorn K) : quasithinZornMul y zornUnit = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp [quasithinZornMul, zornUnit, quasithinCross]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp

theorem cross_self (u : Fin 3 → K) : quasithinCross u u = 0 := by
  funext i
  fin_cases i <;> simp [quasithinCross] <;> ring

theorem zornMul_self_eq (x : quasithinZorn K) :
    quasithinZornMul x x = (x.1 * x.1 + ∑ i, x.2.1 i * x.2.2.1 i, (x.1 + x.2.2.2) • x.2.1,
      (x.1 + x.2.2.2) • x.2.2.1, x.2.2.2 * x.2.2.2 + ∑ i, x.2.2.1 i * x.2.1 i) := by
  obtain ⟨r, u, v, s⟩ := x
  simp only [quasithinZornMul, cross_self]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  · funext i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

@[expose] def IsAlgAut (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) : Prop :=
  ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)

theorem IsAlgAut.map_unit {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsAlgAut g) :
    g zornUnit = zornUnit := by
  have h := hg zornUnit (g.symm zornUnit)
  rw [zornMul_zornUnit_left, LinearEquiv.apply_symm_apply, zornMul_zornUnit_right] at h
  exact h.symm

theorem IsAlgAut.map_smul_unit {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsAlgAut g)
    (c : K) : g ((c, 0, 0, c) : quasithinZorn K) = (c, 0, 0, c) := by
  have h1 : ((c, 0, 0, c) : quasithinZorn K) = c • zornUnit := by
    simp [zornUnit]
  rw [h1, map_smul, hg.map_unit]

theorem IsAlgAut.trace_zero [CharP K 2] {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : IsAlgAut g) {x : quasithinZorn K} (hx : x.1 + x.2.2.2 = 0) :
    (g x).1 + (g x).2.2.2 = 0 := by
  have hs : x.2.2.2 = x.1 := by
    have := eq_neg_of_add_eq_zero_right hx
    rw [this, CharTwo.neg_eq]
  set N : K := x.1 * x.1 + ∑ i, x.2.1 i * x.2.2.1 i with hN
  have hxx : quasithinZornMul x x = ((N, 0, 0, N) : quasithinZorn K) := by
    rw [zornMul_self_eq]
    have h0 : x.1 + x.2.2.2 = 0 := hx
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [h0]
    · simp [h0]
    · simp only [hs, hN]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hyy := hg x x
  rw [hxx, hg.map_smul_unit] at hyy
  set y := g x with hy
  have hyy' := zornMul_self_eq y
  rw [← hyy] at hyy'
  have h1 := congrArg Prod.fst hyy'
  have h4 := congrArg (fun z => z.2.2.2) hyy'
  simp only at h1 h4
  have hsum : ∑ i, y.2.1 i * y.2.2.1 i = ∑ i, y.2.2.1 i * y.2.1 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsq : y.1 * y.1 = y.2.2.2 * y.2.2.2 := by
    have : y.1 * y.1 + ∑ i, y.2.1 i * y.2.2.1 i =
        y.2.2.2 * y.2.2.2 + ∑ i, y.2.2.1 i * y.2.1 i := by
      rw [← h1, ← h4]
    rw [hsum] at this
    exact add_right_cancel this
  have h2 : (y.1 + y.2.2.2) * (y.1 + y.2.2.2) = 0 := by
    have hc : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (y.1 + y.2.2.2) * (y.1 + y.2.2.2)
        = y.1 * y.1 + y.2.2.2 * y.2.2.2 + 2 * (y.1 * y.2.2.2) := by ring
      _ = 0 := by rw [hc, zero_mul, add_zero, hsq, CharTwo.add_self_eq_zero]
  exact mul_self_eq_zero.mp h2

theorem isAlgAut_of_mem_quasithinG2 {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ quasithinG2 K) : IsAlgAut g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => intro x y; rfl
  | mul g h _ _ hg hh =>
    intro x y
    show g (h (quasithinZornMul x y)) = quasithinZornMul (g (h x)) (g (h y))
    rw [hh, hg]
  | inv g _ hg =>
    intro x y
    have h1 := hg (g⁻¹ x) (g⁻¹ y)
    have e1 : g (g⁻¹ x) = x := LinearEquiv.apply_symm_apply g x
    have e2 : g (g⁻¹ y) = y := LinearEquiv.apply_symm_apply g y
    rw [e1, e2] at h1
    show g.symm (quasithinZornMul x y) = quasithinZornMul (g.symm x) (g.symm y)
    rw [← h1]
    exact LinearEquiv.symm_apply_apply g _

theorem commutator_quasithinG2_le : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := by
  refine Subgroup.commutator_le.2 ?_
  intro a ha b hb
  rw [commutatorElement_def]
  exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
    ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)

end Zorn

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_scalars_of_g2 (K : Type) [Field K] [Algebra (ZMod 2) K] {H : Subgroup (GLV V)}
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (hG₀ : G₀ ≤ quasithinG2 K)
    (hnat : IsG2NaturalModule H G₀) :
    ∃ sc : K →+* Module.End (ZMod 2) V, ∀ κ, ∀ h ∈ H, ∀ v, sc κ (h v) = h (sc κ v) := by
  classical
  have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  obtain ⟨φ, π, hsurj, hker, hequiv⟩ := hnat
  choose pre pre_tz pre_spec using hsurj
  have smul_tz : ∀ (κ : K) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 →
      (κ • x).1 + (κ • x).2.2.2 = 0 := by
    intro κ x hx
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← mul_add, hx, mul_zero]
  have congr_smul : ∀ (κ : K) (x x' : quasithinZorn K), x.1 + x.2.2.2 = 0 →
      x'.1 + x'.2.2.2 = 0 → π x = π x' → π (κ • x) = π (κ • x') := by
    intro κ x x' hx hx' hxx
    have hd0 : (x - x').1 + (x - x').2.2.2 = 0 := by
      simp only [Prod.fst_sub, Prod.snd_sub]
      linear_combination hx - hx'
    have hπ : π (x - x') = 0 := by rw [map_sub, hxx, sub_self]
    obtain ⟨c, hc⟩ := (hker _ hd0).1 hπ
    have h2 : κ • (x - x') = (κ * c, 0, 0, κ * c) := by
      rw [hc]
      simp [Prod.smul_def]
    have h3 : π (κ • (x - x')) = 0 := by
      rw [hker _ (smul_tz κ _ hd0)]
      exact ⟨κ * c, h2⟩
    rw [smul_sub, map_sub, sub_eq_zero] at h3
    exact h3
  let scAdd : K → V →+ V := fun κ =>
    { toFun := fun v => π (κ • pre v)
      map_zero' := by
        have := congr_smul κ (pre 0) 0 (pre_tz 0) (by simp) (by rw [pre_spec, map_zero])
        simpa using this
      map_add' := fun v w => by
        have := congr_smul κ (pre (v + w)) (pre v + pre w) (pre_tz _)
          (by simp only [Prod.fst_add, Prod.snd_add]; linear_combination pre_tz v + pre_tz w)
          (by rw [pre_spec, map_add, pre_spec, pre_spec])
        rw [this, smul_add, map_add] }
  have scAdd_apply : ∀ κ v, scAdd κ v = π (κ • pre v) := fun κ v => rfl
  let sc : K →+* Module.End (ZMod 2) V :=
    { toFun := fun κ => (scAdd κ).toZModLinearMap 2
      map_one' := by
        apply LinearMap.ext
        intro v
        simp [scAdd_apply, pre_spec]
      map_mul' := fun κ κ' => by
        apply LinearMap.ext
        intro v
        show scAdd (κ * κ') v = scAdd κ (scAdd κ' v)
        rw [scAdd_apply, scAdd_apply, scAdd_apply]
        have := congr_smul κ (pre (π (κ' • pre v))) (κ' • pre v) (pre_tz _)
          (smul_tz κ' _ (pre_tz v)) (by rw [pre_spec])
        rw [this, mul_smul]
      map_zero' := by
        apply LinearMap.ext
        intro v
        simp [scAdd_apply]
      map_add' := fun κ κ' => by
        apply LinearMap.ext
        intro v
        show scAdd (κ + κ') v = scAdd κ v + scAdd κ' v
        rw [scAdd_apply, scAdd_apply, scAdd_apply, add_smul, map_add] }
  have sc_apply : ∀ κ v, sc κ v = π (κ • pre v) := fun κ v => rfl
  refine ⟨sc, fun κ h hh v => ?_⟩
  set g : quasithinZorn K ≃ₗ[K] quasithinZorn K :=
    ((φ ⟨h, hh⟩ : ↥G₀) : quasithinZorn K ≃ₗ[K] quasithinZorn K) with hgdef
  have hZ := isAlgAut_of_mem_quasithinG2 (hG₀ (φ ⟨h, hh⟩).2)
  have htr : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → (g x).1 + (g x).2.2.2 = 0 :=
    fun x hx => hZ.trace_zero hx
  have hge : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → π (g x) = h (π x) :=
    fun x hx => hequiv ⟨h, hh⟩ x hx
  rw [sc_apply, sc_apply]
  have e1 := congr_smul κ (pre (h v)) (g (pre v)) (pre_tz _) (htr _ (pre_tz v))
    (by rw [pre_spec, hge _ (pre_tz v), pre_spec])
  rw [e1, ← map_smul g, hge _ (smul_tz κ _ (pre_tz v))]

theorem card_pow_six_le_of_g2 (K : Type) [Field K] [Finite K] [Algebra (ZMod 2) K] [Finite V]
    {H : Subgroup (GLV V)} {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hnat : IsG2NaturalModule H G₀) : Nat.card K ^ 6 ≤ Nat.card V := by
  obtain ⟨φ, π, hsurj, hker, hequiv⟩ := hnat
  let Φ : (Fin 3 → K) × (Fin 3 → K) → V := fun w => π ((0, w.1, w.2, 0) : quasithinZorn K)
  have hΦ : Function.Injective Φ := by
    intro w w' hww
    have htz : ((0, w.1 - w'.1, w.2 - w'.2, 0) : quasithinZorn K).1 +
        ((0, w.1 - w'.1, w.2 - w'.2, 0) : quasithinZorn K).2.2.2 = 0 := by simp
    have hsub : ((0, w.1 - w'.1, w.2 - w'.2, 0) : quasithinZorn K) =
        (0, w.1, w.2, 0) - (0, w'.1, w'.2, 0) := by
      simp
    have h0 : π ((0, w.1 - w'.1, w.2 - w'.2, 0) : quasithinZorn K) = 0 := by
      rw [hsub, map_sub]
      exact sub_eq_zero.2 hww
    obtain ⟨c, hc⟩ := (hker _ htz).1 h0
    have hu : w.1 - w'.1 = 0 := congrArg (fun z : quasithinZorn K => z.2.1) hc
    have hv : w.2 - w'.2 = 0 := congrArg (fun z : quasithinZorn K => z.2.2.1) hc
    exact Prod.ext (sub_eq_zero.1 hu) (sub_eq_zero.1 hv)
  have hcard : Nat.card ((Fin 3 → K) × (Fin 3 → K)) ≤ Nat.card V :=
    Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, ← pow_add] at hcard
  exact hcard

theorem twelve_le_finrank_of_g2 (K : Type) [Field K] [Finite K] [Algebra (ZMod 2) K] [Finite V]
    (hK : 4 ≤ Nat.card K) {H : Subgroup (GLV V)}
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (hnat : IsG2NaturalModule H G₀) :
    12 ≤ Module.finrank (ZMod 2) V := by
  have hcard := card_pow_six_le_of_g2 K hnat
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  by_contra hlt
  push Not at hlt
  have : 4 ^ 6 ≤ 2 ^ 11 := by
    calc 4 ^ 6 ≤ Nat.card K ^ 6 := Nat.pow_le_pow_left hK 6
      _ ≤ Nat.card V := hcard
      _ = 2 ^ Module.finrank (ZMod 2) V := hV
      _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at this

end CFSG.Quasithin.SzG11NC
