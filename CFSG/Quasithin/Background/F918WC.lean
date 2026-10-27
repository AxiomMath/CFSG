module

public import CFSG.Quasithin.Background.F918WB
public import CFSG.Quasithin.Background.F918WE

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.D35ValChk Matrix

@[expose] def d35MulVecEquiv (P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toFun v := P *ᵥ v
  invFun v := Q *ᵥ v
  left_inv v := by simp [Matrix.mulVec_mulVec, hQP]
  right_inv v := by simp [Matrix.mulVec_mulVec, hPQ]
  map_add' v w := Matrix.mulVec_add P v w

theorem d35MulVecEquiv_apply (P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (v : Fin 6 → ZMod 2) : d35MulVecEquiv P Q hQP hPQ v = P *ᵥ v := rfl

theorem d35_map_center_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' := Subgroup.mem_center_iff.mp hg
    refine Subgroup.mem_center_iff.mpr fun k => ?_
    obtain ⟨k', rfl⟩ := e.surjective k
    have := congrArg e (hg' k')
    simpa using this
  · intro hh
    have hh' := Subgroup.mem_center_iff.mp hh
    refine ⟨e.symm h, Subgroup.mem_center_iff.mpr fun k => ?_, by simp⟩
    apply e.injective
    simpa using hh' (e k)

theorem offF2_of_offNat {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (hK : Nat.card K = 4) (ρ : ↥Γ ≃* G0) (ψ : (Fin 3 → K) ≃+ (Fin 6 → ZMod 2))
    (hψ : ∀ (γ : ↥Γ) (w : Fin 3 → K),
      ψ (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        (((ρ γ : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ψ w)
    {E : Subgroup ↥Γ} (hE : OffNat Γ E) : OffF2 (E.map ρ.toMonoidHom) := by
  obtain ⟨h0, hab, hsq, hmax⟩ := hE
  have hfix : ∀ (B : Subgroup ↥Γ), Nat.card ↥(fixNat Γ B) =
      Nat.card {v : Fin 6 → ZMod 2 // ∀ e ∈ B.map ρ.toMonoidHom,
        (((e : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} := by
    intro B
    refine Nat.card_congr
      { toFun := fun w => ⟨ψ (w : Fin 3 → K), ?_⟩
        invFun := fun v => ⟨ψ.symm (v : Fin 6 → ZMod 2), ?_⟩
        left_inv := fun w => by simp
        right_inv := fun v => Subtype.ext (by simp) }
    · rintro _ ⟨γ, hγ, rfl⟩
      have h1 := w.2 γ hγ
      change (((ρ γ : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        ψ (w : Fin 3 → K) = ψ (w : Fin 3 → K)
      rw [← hψ γ w, h1]
    · intro γ hγ
      apply ψ.injective
      rw [hψ γ]
      have h1 := v.2 (ρ γ) ⟨γ, hγ, rfl⟩
      simpa using h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    exact h0 ((Subgroup.map_eq_bot_iff_of_injective _ ρ.injective).mp hb)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hab a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_pow]
    rw [hsq a ha, map_one]
  · have h64 : 64 ≤ Nat.card E * Nat.card ↥(fixNat Γ E) := by
      have := hmax ⊥ bot_le
      have hbot : Nat.card ↥(fixNat Γ (⊥ : Subgroup ↥Γ)) = 64 := by
        have e1 : fixNat Γ (⊥ : Subgroup ↥Γ) = Set.univ := by
          ext w
          simp [fixNat, Subgroup.mem_bot]
        rw [e1, Nat.card_congr (Equiv.Set.univ (Fin 3 → K))]
        rw [Nat.card_pi, Fin.prod_univ_three, hK]
        norm_num
      rw [Subgroup.card_bot, hbot] at this
      omega
    rw [Subgroup.card_map_of_injective ρ.injective, ← hfix E]
    exact h64

theorem d35ValCore_of_facts (hF : D35Facts) : D35ValCore := by
  intro K _ _ Γ hv α E F hE hF' hα
  obtain ⟨ρ, ψ, hψ⟩ := valentiner_transfer hF hv
  have hc : (Subgroup.center ↥Γ).map ρ.toMonoidHom = Subgroup.center G0 := d35_map_center_equiv ρ
  let ρb : (↥Γ ⧸ Subgroup.center ↥Γ) ≃* (G0 ⧸ Subgroup.center G0) := QuotientGroup.congr _ _ ρ hc
  have hρb : ∀ γ : ↥Γ, ρb (QuotientGroup.mk γ) = QuotientGroup.mk (ρ γ) := fun γ => rfl
  let α' : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0) := ρb.symm.trans (α.trans ρb)
  have hα'ρb : ∀ x, α' (ρb x) = ρb (α x) := fun x => by simp [α']
  have hmapE : ∀ B : Subgroup ↥Γ, (B.map ρ.toMonoidHom).map (QuotientGroup.mk' (Subgroup.center G0)) =
      (B.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map ρb.toMonoidHom := by
    intro B
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hcomp : α'.toMonoidHom.comp ρb.toMonoidHom = ρb.toMonoidHom.comp α.toMonoidHom := by
    ext x
    exact hα'ρb x
  have hrel : ((E.map ρ.toMonoidHom).map (QuotientGroup.mk' (Subgroup.center G0))).map α'.toMonoidHom =
      (F.map ρ.toMonoidHom).map (QuotientGroup.mk' (Subgroup.center G0)) := by
    calc ((E.map ρ.toMonoidHom).map (QuotientGroup.mk' (Subgroup.center G0))).map α'.toMonoidHom
        = ((E.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map ρb.toMonoidHom).map α'.toMonoidHom := by
          rw [hmapE]
      _ = (E.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map (α'.toMonoidHom.comp ρb.toMonoidHom) :=
          Subgroup.map_map _ _ _
      _ = (E.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map (ρb.toMonoidHom.comp α.toMonoidHom) := by
          rw [hcomp]
      _ = ((E.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map α.toMonoidHom).map ρb.toMonoidHom :=
          (Subgroup.map_map _ _ _).symm
      _ = (F.map (QuotientGroup.mk' (Subgroup.center ↥Γ))).map ρb.toMonoidHom := by rw [hα]
      _ = (F.map ρ.toMonoidHom).map (QuotientGroup.mk' (Subgroup.center G0)) := (hmapE F).symm
  obtain ⟨β', P, Q, hPQ, hQP, hβ', hP⟩ := core0_of_facts hF α' (E.map ρ.toMonoidHom) (F.map ρ.toMonoidHom)
    (offF2_of_offNat hv.1 ρ ψ hψ hE) (offF2_of_offNat hv.1 ρ ψ hψ hF') hrel
  refine ⟨ρ.trans (β'.trans ρ.symm), ψ.trans ((d35MulVecEquiv P Q hQP hPQ).trans ψ.symm), ?_, ?_⟩
  · intro γ
    apply ρb.injective
    have h1 : ρb (QuotientGroup.mk' (Subgroup.center ↥Γ) ((ρ.trans (β'.trans ρ.symm)) γ)) =
        QuotientGroup.mk' (Subgroup.center G0) (β' (ρ γ)) := by simp [hρb]
    rw [h1, hβ' (ρ γ)]
    have h2 : QuotientGroup.mk' (Subgroup.center G0) (ρ γ) = ρb (QuotientGroup.mk' (Subgroup.center ↥Γ) γ) := rfl
    rw [h2, hα'ρb]
  · intro γ w
    apply ψ.injective
    have hβγ : ρ ((ρ.trans (β'.trans ρ.symm)) γ) = β' (ρ γ) := by simp
    have hL : ψ ((ψ.trans ((d35MulVecEquiv P Q hQP hPQ).trans ψ.symm))
        (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w)) =
        P *ᵥ ((((ρ γ : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          ψ w) := by
      simp [AddEquiv.trans_apply, d35MulVecEquiv_apply, hψ]
    have hR : ψ (((((ρ.trans (β'.trans ρ.symm)) γ : Matrix.GeneralLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ ((ψ.trans ((d35MulVecEquiv P Q hQP hPQ).trans ψ.symm)) w)) =
        (((β' (ρ γ) : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          (P *ᵥ ψ w) := by
      rw [hψ, hβγ]
      simp [AddEquiv.trans_apply, d35MulVecEquiv_apply]
    rw [hL, hR, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP (ρ γ)]

theorem d35ValCore_of_chk (h : CFSG.Quasithin.D35ValChk.run = true) : D35ValCore :=
  d35ValCore_of_facts (run_facts h)

end CFSG.Quasithin
