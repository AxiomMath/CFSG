module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviPlane
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag

public section

namespace CFSG.StandardType.TorC

open CFSG.Open CFSG.StandardType.SpJoin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Matrix

variable {F : Type} [Field F]

theorem coe_spPlaneTorus {m : ℕ} (n : ℕ)
    (ζ : Multiplicative (ZMod m) →* SpecialLinearGroup (Fin 2) F)
    (f : Fin n → Multiplicative (ZMod m)) :
    (((spPlaneTorus n ζ f : StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      WitSpNs.planeMat
        (fun j => ((ζ (f j) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  classical
  let L : (Fin n → Multiplicative (ZMod m)) →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    (Units.coeHom _).comp ((StatedSp n F).subtype.comp (spPlaneTorus n ζ))
  let P : (Fin n → Multiplicative (ZMod m)) →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    { toFun := fun f => WitSpNs.planeMat
        (fun j => ((ζ (f j) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      map_one' := by
        simp only [Pi.one_apply, map_one, Matrix.SpecialLinearGroup.coe_one]
        exact WitSpNs.planeMat_one
      map_mul' := fun f g => by
        rw [WitSpNs.planeMat_mul]
        congr 1
        funext j
        simp only [Pi.mul_apply, map_mul, Matrix.SpecialLinearGroup.coe_mul] }
  have hLP : L = P := MonoidHom.pi_ext fun i a => by
    simp only [L, P, MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      Subgroup.coe_subtype, spPlaneTorus_mulSingle, coe_lam]
    ext x y
    rw [WitSpNs.planeMat_apply]
    rcases x with j | j <;> rcases y with k | k <;>
      by_cases hj : j = i <;> by_cases hk : k = i <;> by_cases hjk : j = k <;>
      simp_all [pairMat, Pi.mulSingle_apply, Matrix.one_apply, WitSpNs.plane, WitSpNs.side]
  exact congrArg (fun φ : (Fin n → Multiplicative (ZMod m)) →*
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F => φ f) hLP

theorem spPlaneTorus_eq_of_forall {p m n : ℕ}
    {ζp : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    {ζm : Multiplicative (ZMod m) →* SpecialLinearGroup (Fin 2) F}
    {f : Fin n → Multiplicative (ZMod p)} {g : Fin n → Multiplicative (ZMod m)}
    (h : ∀ j, ζp (f j) = ζm (g j)) : spPlaneTorus n ζp f = spPlaneTorus n ζm g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_spPlaneTorus, coe_spPlaneTorus]
  congr 1
  funext j
  rw [h j]

theorem spPlaneTorus_injective {m : ℕ}
    {ζ : Multiplicative (ZMod m) →* SpecialLinearGroup (Fin 2) F} (hζ : Function.Injective ζ)
    (n : ℕ) : Function.Injective (spPlaneTorus n ζ) := by
  intro f g h
  have h' := congrArg (fun x : StatedSp n F =>
    ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h
  simp only [coe_spPlaneTorus] at h'
  have h'' := WitSpNs.planeMat_injective h'
  funext j
  exact hζ (Subtype.ext (congrFun h'' j))

theorem spLeviBlock_injective (n : ℕ) :
    Function.Injective (CFSG.StandardType.spLeviBlock n F) := by
  intro s s' h
  have h1 : spPlaneLevi n F (1, s) = spPlaneLevi n F (1, s') := by
    rw [spPlaneLevi_apply, spPlaneLevi_apply, h]
  exact congrArg Prod.snd (spPlaneLevi_injective n h1)

theorem mem_range_spPlaneTorus_of_commute [CharP F 2] {m : ℕ}
    {ζ : Multiplicative (ZMod m) →* SpecialLinearGroup (Fin 2) F}
    {T₀ : SpecialLinearGroup (Fin 2) F} (htr : (T₀ : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    (hcent : ∀ h : SpecialLinearGroup (Fin 2) F, h * T₀ = T₀ * h → h ∈ ζ.range) :
    ∀ (n : ℕ) (u : StatedSp n F), (∀ i : Fin n, u * lam i T₀ = lam i T₀ * u) →
      u ∈ (spPlaneTorus n ζ).range
  | 0, u, _ => by
    rw [Subsingleton.elim u 1]
    exact one_mem _
  | n + 1, u, hu => by
    obtain ⟨h, s, rfl, hh⟩ := exists_lam_zero_mul_levi_of_commute htr (hu 0)
    obtain ⟨a, rfl⟩ := hcent h hh
    have hs : ∀ i : Fin n, s * lam i T₀ = lam i T₀ * s := by
      intro i
      have h1 := hu i.succ
      rw [← spLeviBlock_lam] at h1
      have hc := lam_zero_commute_spLeviBlock (ζ a) (lam i T₀)
      apply spLeviBlock_injective n
      rw [map_mul, map_mul]
      apply mul_left_cancel (a := lam (0 : Fin (n + 1)) (ζ a))
      calc lam (0 : Fin (n + 1)) (ζ a) * (CFSG.StandardType.spLeviBlock n F s *
            CFSG.StandardType.spLeviBlock n F (lam i T₀))
          = lam (0 : Fin (n + 1)) (ζ a) * CFSG.StandardType.spLeviBlock n F s *
            CFSG.StandardType.spLeviBlock n F (lam i T₀) := by rw [mul_assoc]
        _ = CFSG.StandardType.spLeviBlock n F (lam i T₀) *
            (lam (0 : Fin (n + 1)) (ζ a) * CFSG.StandardType.spLeviBlock n F s) := h1
        _ = lam (0 : Fin (n + 1)) (ζ a) * (CFSG.StandardType.spLeviBlock n F (lam i T₀) *
            CFSG.StandardType.spLeviBlock n F s) := by rw [← mul_assoc, ← hc, mul_assoc]
    obtain ⟨f', hf'⟩ := mem_range_spPlaneTorus_of_commute htr hcent n s hs
    refine ⟨Fin.cons a f', ?_⟩
    rw [spPlaneTorus_succ, Fin.cons_zero, Fin.tail_cons, hf']

theorem mem_range_spPlaneTorus_iff {p m : ℕ} (n : ℕ)
    {ζp : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    {ζm : Multiplicative (ZMod m) →* SpecialLinearGroup (Fin 2) F} (hζm : Function.Injective ζm)
    (hpm : ∀ a, ∃ b, ζm b = ζp a) (hmp : ∀ b, ζm b ^ p = 1 → ∃ a, ζp a = ζm b)
    (x : StatedSp n F) :
    x ∈ (spPlaneTorus n ζp).range ↔ x ^ p = 1 ∧ x ∈ (spPlaneTorus n ζm).range := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨?_, ?_⟩
    · have hfp : f ^ p = 1 := by
        funext j
        obtain ⟨y, hy⟩ : ∃ y : ZMod p, Multiplicative.ofAdd y = f j :=
          ⟨Multiplicative.toAdd (f j), rfl⟩
        rw [Pi.pow_apply, ← hy, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
          ofAdd_zero, Pi.one_apply]
      rw [← map_pow, hfp, map_one]
    · choose b hb using fun j => hpm (f j)
      exact ⟨b, (spPlaneTorus_eq_of_forall fun j => (hb j).symm).symm⟩
  · rintro ⟨hx, g, rfl⟩
    have hg : g ^ p = 1 := spPlaneTorus_injective hζm n (by rw [map_pow, hx, map_one])
    choose a ha using fun j => hmp (g j) (by rw [← map_pow, show g j ^ p = 1 from
      congrFun hg j, map_one])
    exact ⟨a, spPlaneTorus_eq_of_forall ha⟩

end CFSG.StandardType.TorC

end
