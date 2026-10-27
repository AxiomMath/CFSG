module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerWedge

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.sec717_typing_T (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {m : ℕ} {γ : G → GaloisField 2 m} (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ)
    (hM : GlobalModelData M Q Z γ M₀)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule (GaloisField 2 m) M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∃ η : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) →*
        Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m),
      Function.Surjective η ∧
      (∀ r, η r = 1 ↔
        (r : ↥(bar M Q (H0 M Z))) ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) ∧
      ∃ ψ : ↥T ≃ₗ[GaloisField 2 m] (Fin 3 ⊕ Fin 3 → GaloisField 2 m),
        ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))) (w w' : ↥T),
          (w' : M₀.E) = φ (r : ↥(bar M Q (H0 M Z))) w →
            ψ w' = PartOne.K159.Klein.rho (η r) (ψ w) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQCN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  obtain ⟨K', fK', finK', hK'Z, ρΩ, hρr, hρker, hsec⟩ := id hp3
  obtain ⟨k, -, hk, -⟩ := hc.hyp.cp
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'Z.trans hk)
  obtain ⟨η₀, hη₀s, hη₀k, hη₀ρ⟩ := exists_sl4_of_omegaPlus_three ρΩ hρr
  have hmemN : ∀ h : ↥(Rt M (LB M Q B) t), η₀ h = 1 ↔ (h : G) ∈ hc.CN t := by
    intro h
    rw [hη₀k, ← MonoidHom.mem_ker, hρker, Subgroup.mem_subgroupOf]
  let π' : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (H0 M Z)) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (Q.subgroupOf M)).comp
      (Subgroup.inclusion hRM)) (bar M Q (H0 M Z)) fun x =>
        (mk_mem_bar_iff_sec4 hQH _).mpr (hRH x.2)
  have hπ'R : ∀ x, π' x ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) :=
    fun x => Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr x.2)
  have hπ'N : ∀ x, π' x ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ↔
      (x : G) ∈ hc.CN t := fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact mk_mem_bar_iff_sec4 hQCN _
  obtain ⟨e, he⟩ := hc.sec717_transport_hom hZcard hZc hZV hs hZ0 ρΩ hsec M₀ φ hφπ T hT
  have he' : ∀ (x : ↥(Rt M (LB M Q B) t)) (u : Fin 3 ⊕ Fin 3 → K'),
      (e ((ρΩ x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : M₀.E) = φ (π' x) (e u) :=
    fun x u => he x _ u
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_transport (hM.card.trans hK'Z.symm) ρΩ hρr φ π' T e he'
  let ι : (Fin 3 ⊕ Fin 3 → K') ≃ₗ[K'] (Fin 3 ⊕ Fin 3 → K') := LinearEquiv.refl K' _
  have hη₂T : ∀ h u, PartOne.K159.Klein.rho (η₀ h) (ι u) =
      ι ((ρΩ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) := fun h u => hη₀ρ h u
  let f : K' →+* GaloisField 2 m := σ.symm.toRingHom
  have hfσ : ∀ c, f (σ c) = c := fun c => σ.symm_apply_apply c
  have hσf : ∀ c, σ (f c) = c := fun c => σ.apply_symm_apply c
  let η₃ : ↥(Rt M (LB M Q B) t) →* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m) :=
    (Matrix.SpecialLinearGroup.map f).comp η₀
  have hmapf_inj : ∀ A : Matrix.SpecialLinearGroup (Fin 4) K',
      Matrix.SpecialLinearGroup.map f A = 1 ↔ A = 1 := by
    intro A
    constructor
    · intro h1
      apply Subtype.ext
      ext i j
      have h2 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m) =>
        (B : Matrix (Fin 4) (Fin 4) (GaloisField 2 m)) i j) h1
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one] at h2
      have h3 := congrArg σ h2
      rw [hσf] at h3
      rw [h3, Matrix.SpecialLinearGroup.coe_one]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.one_apply, hij]
    · intro h1
      rw [h1, map_one]
  have he_symm : ∀ (x : ↥(Rt M (LB M Q B) t)) (w : ↥T) (hw : φ (π' x) w ∈ T),
      e.symm ⟨φ (π' x) w, hw⟩ =
        (ρΩ x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ e.symm w := by
    intro x w hw
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [he', AddEquiv.apply_symm_apply]
  have he_smul : ∀ (c : GaloisField 2 m) (w : ↥T), e.symm (c • w) = σ c • e.symm w := by
    intro c w
    rw [AddEquiv.symm_apply_eq, ← hσ, AddEquiv.apply_symm_apply]
  let ψT : ↥T ≃ₗ[GaloisField 2 m] (Fin 3 ⊕ Fin 3 → GaloisField 2 m) :=
    { toFun := fun w i => f (ι (e.symm w) i)
      invFun := fun z => e (ι.symm fun i => σ (z i))
      map_add' := fun w₁ w₂ => by
        funext i
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c w => by
        funext i
        simp only [he_smul, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, hfσ,
          RingHom.id_apply]
      left_inv := fun w => by
        simp only [hσf]
        rw [show (fun i => ι (e.symm w) i) = ι (e.symm w) from rfl, LinearEquiv.symm_apply_apply,
          AddEquiv.apply_symm_apply]
      right_inv := fun z => by
        funext i
        simp only [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, hfσ] }
  have hψT : ∀ (w : ↥T), ψT w = fun i => f (ι (e.symm w) i) := fun w => rfl
  have hψTeq : ∀ (x : ↥(Rt M (LB M Q B) t)) (w : ↥T) (hw : φ (π' x) w ∈ T),
      ψT ⟨φ (π' x) w, hw⟩ = PartOne.K159.Klein.rho (η₃ x) (ψT w) := by
    intro x w hw
    rw [hψT, hψT, he_symm, ← hη₂T]
    exact (kleinRho_map f (η₀ x) (ι (e.symm w))).symm
  let π'R : ↥(Rt M (LB M Q B) t) →*
      ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) :=
    π'.codRestrict _ hπ'R
  have hπ'R_coe : ∀ x, ((π'R x : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf
      (bar M Q (H0 M Z)))) : ↥(bar M Q (H0 M Z))) = π' x := fun x => rfl
  have hπ'R_surj : Function.Surjective π'R := by
    intro r
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M)
      ((r : ↥(bar M Q (H0 M Z))) : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp r.2)
    exact ⟨⟨(y : G), hyR⟩, Subtype.ext (Subtype.ext hy)⟩
  have hQmem : ∀ x : ↥(Rt M (LB M Q B) t), π' x = 1 → (x : G) ∈ Q := by
    intro x hx
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨(x : G), hRM x.2⟩ : ↥M) = 1 :=
      congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hker3 : π'R.ker ≤ η₃.ker := by
    intro x hx
    have hx1 : π' x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxN : (x : G) ∈ hc.CN t := hQCN (hQmem x hx1)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (hmemN x).mpr hxN, map_one]
  let η := MonoidHom.liftOfRightInverse π'R (Function.surjInv hπ'R_surj)
    (Function.rightInverse_surjInv hπ'R_surj) ⟨η₃, hker3⟩
  have hη : ∀ x, η (π'R x) = η₃ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply π'R (Function.surjInv hπ'R_surj)
      (Function.rightInverse_surjInv hπ'R_surj) ⟨η₃, hker3⟩ x
  refine ⟨η, fun g => ?_, fun r => ?_, ψT, fun r w w' hw' => ?_⟩
  ·
    obtain ⟨x, hx⟩ := hη₀s (Matrix.SpecialLinearGroup.map σ.toRingHom g)
    refine ⟨π'R x, ?_⟩
    rw [hη, MonoidHom.comp_apply, hx]
    apply Subtype.ext
    ext i j
    simp [f, Matrix.SpecialLinearGroup.map_apply_coe]
  ·
    obtain ⟨x, rfl⟩ := hπ'R_surj r
    rw [hη, MonoidHom.comp_apply, hmapf_inj, hmemN, hπ'R_coe, hπ'N]
  ·
    obtain ⟨x, rfl⟩ := hπ'R_surj r
    have hmemw : φ (π' x) w ∈ T := by
      have h1 := w'.2
      rw [hw'] at h1
      exact h1
    have hw'' : w' = ⟨φ (π' x) w, hmemw⟩ := Subtype.ext hw'
    rw [hw'', hψTeq, hη]

theorem Ctx.sec717_wedge_of_typing (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {L : Subgroup G} {m : ℕ} {γ : G → GaloisField 2 m}
    (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ) (hM : GlobalModelData M Q Z γ M₀)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule (GaloisField 2 m) M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T)
    (η₁ : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) →*
      Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m))
    (hη₁s : Function.Surjective η₁)
    (hη₁k : ∀ r, η₁ r = 1 ↔
      (r : ↥(bar M Q (H0 M Z))) ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    (θ₁ : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) →*
      Multiplicative (Fin 4 → GaloisField 2 m))
    (hθ₁s : Function.Surjective θ₁)
    (hθ₁k : ∀ l, θ₁ l = 1 ↔
      (l : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
    (hθ₁ : ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))))
      (l l' : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z)))),
      (l' : ↥(bar M Q (H0 M Z))) =
          (r : ↥(bar M Q (H0 M Z))) * l * (r : ↥(bar M Q (H0 M Z)))⁻¹ →
        Multiplicative.toAdd (θ₁ l') = η₁ r • Multiplicative.toAdd (θ₁ l)) :
    ∃ η : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) →*
        Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m),
      Function.Surjective η ∧
      (∀ r, η r = 1 ↔
        (r : ↥(bar M Q (H0 M Z))) ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) ∧
      (∃ θ : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) →*
          Multiplicative (Fin 4 → GaloisField 2 m),
        Function.Surjective θ ∧
        (∀ l, θ l = 1 ↔
          (l : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ∧
        ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))))
          (l l' : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z)))),
          (l' : ↥(bar M Q (H0 M Z))) =
              (r : ↥(bar M Q (H0 M Z))) * l * (r : ↥(bar M Q (H0 M Z)))⁻¹ →
            Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l)) ∧
      ∃ ψ : ↥T ≃ₗ[GaloisField 2 m] (Fin 3 ⊕ Fin 3 → GaloisField 2 m),
        ∀ (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))) (w w' : ↥T),
          (w' : M₀.E) = φ (r : ↥(bar M Q (H0 M Z))) w →
            ψ w' = PartOne.K159.Klein.rho (η r) (ψ w) := by
  obtain ⟨η₂, hη₂s, hη₂k, ψ₂, hψ₂⟩ :=
    hc.sec717_typing_T hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ T hT
  obtain ⟨η, hηs, hηk, ⟨θ, hθs, hθk, hθ⟩, ψ, hψ⟩ :=
    exists_sl4_common_typing η₁ η₂ hη₁s hη₂s (fun r => (hη₁k r).trans (hη₂k r).symm)
      (fun (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))))
        (l l' : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z)))) => (l' : ↥(bar M Q (H0 M Z))) =
          (r : ↥(bar M Q (H0 M Z))) * l * (r : ↥(bar M Q (H0 M Z)))⁻¹) θ₁ hθ₁s hθ₁
      (fun (r : ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))) (w w' : ↥T) =>
        (w' : M₀.E) = φ (r : ↥(bar M Q (H0 M Z))) w) ψ₂ hψ₂
  exact ⟨η, hηs, fun r => (hηk r).trans (hη₂k r), ⟨θ, hθs, fun l => (hθk l).trans (hθ₁k l), hθ⟩,
    ψ, hψ⟩

theorem sec717LayerWedge_of_typing (hTyp : Sec717LTypingStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) : Sec717LayerWedgeStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZN hTI L hL hLn m γ M₀ hM φ hφπ T hT
  obtain ⟨η₁, hη₁s, hη₁k, θ₁, hθ₁s, hθ₁k, hθ₁⟩ :=
    hTyp G M Q Z B hc n t hs hp3 Z0 hZ0 hZN hTI L hL hLn m γ M₀ hM φ hφπ
  exact hc.sec717_wedge_of_typing hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ T hT η₁ hη₁s hη₁k θ₁
    hθ₁s hθ₁k hθ₁

end CFSG.RankThree.GF2n.Stroth80
