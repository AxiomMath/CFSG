module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Vol2.Ch10SecQ6O4a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix

variable {F : Type} [Field F]

@[expose] def IsHerm (n : ℕ) (X : Matrix (Fin 2) (Fin 2) F) : Prop := (frobPow n X)ᵀ = X

theorem isHerm_iff {n : ℕ} {X : Matrix (Fin 2) (Fin 2) F} :
    IsHerm n X ↔ sig n (X 0 0) = X 0 0 ∧ sig n (X 1 1) = X 1 1 ∧ sig n (X 0 1) = X 1 0 ∧
      sig n (X 1 0) = X 0 1 := by
  unfold IsHerm
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      [have := congrFun (congrFun h 0) 0; have := congrFun (congrFun h 1) 1;
        have := congrFun (congrFun h 1) 0; have := congrFun (congrFun h 0) 1] <;>
      simpa [frobPow, sig] using this
  · rintro ⟨h00, h11, h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [frobPow, sig]

theorem card_herm [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) F // IsHerm n X} = 2 ^ (4 * n) := by
  let e : {X : Matrix (Fin 2) (Fin 2) F // IsHerm n X} ≃ (fixSig F n × fixSig F n) × F :=
    { toFun := fun X => ((⟨X.1 0 0, (isHerm_iff.mp X.2).1⟩, ⟨X.1 1 1, (isHerm_iff.mp X.2).2.1⟩),
        X.1 0 1)
      invFun := fun p => ⟨!![(p.1.1 : F), p.2; sig n p.2, (p.1.2 : F)], isHerm_iff.mpr
        ⟨by
          have h := p.1.1.2
          change sig n (p.1.1 : F) = p.1.1 at h
          simpa using h, by
          have h := p.1.2.2
          change sig n (p.1.2 : F) = p.1.2 at h
          simpa using h, by simp, by simp [sig_sig hF]⟩⟩
      left_inv := fun X => by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [(isHerm_iff.mp X.2).2.2.1]
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, card_fixSig hF hn, hF]
  rw [show 4 * n = n + n + 2 * n by ring, pow_add, pow_add, pow_mul]
  norm_num

@[expose] def toMat [CharP F 2] (n : ℕ)
    (x : (FFModel.twistTensor n (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).Amb) :
    Matrix (Fin 2) (Fin 2) F :=
  Multiplicative.toAdd (x : Multiplicative (Matrix (Fin 2) (Fin 2) F))

variable {W : Type*} [CommGroup W]

@[expose] def IsO4Coord (n : ℕ) (Λ : Subgroup (MulAut W)) (π : SpecialLinearGroup (Fin 2) F →* Λ)
    (Ψ : W → Matrix (Fin 2) (Fin 2) F) : Prop :=
  Function.Surjective π ∧ (∀ w w', Ψ (w * w') = Ψ w + Ψ w') ∧ Function.Injective Ψ ∧
    (∀ w, IsHerm n (Ψ w)) ∧ (∀ X, IsHerm n X → ∃ w, Ψ w = X) ∧
    ∀ (γ : SpecialLinearGroup (Fin 2) F) (w : W), Ψ ((π γ : MulAut W) w) =
      (γ : Matrix (Fin 2) (Fin 2) F) * Ψ w * (frobPow n (γ : Matrix (Fin 2) (Fin 2) F))ᵀ

theorem exists_isO4Coord [CharP F 2] {Λ : Subgroup (MulAut W)} {n : ℕ}
    (h : (FFModel.twistTensor n (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).Realizes Λ ⊤ ⊥) :
    ∃ (π : SpecialLinearGroup (Fin 2) F →* Λ) (Ψ : W → Matrix (Fin 2) (Fin 2) F),
      IsO4Coord n Λ π Ψ := by
  obtain ⟨π0, hsurj, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  let κ : (↥(FFModel.twistTensor n (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec ⧸
      (FFModel.twistTensor n (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).ker.subgroupOf
        (FFModel.twistTensor n (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec) →*
      ↥(FFModel.twistTensor n (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec :=
    QuotientGroup.lift _ (MonoidHom.id _)
      (fun x hx => Subtype.ext (Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hx)))
  have hκ : ∀ m, κ (QuotientGroup.mk m) = m := fun m => QuotientGroup.lift_mk _ _ _
  have hmk : ∀ q, (QuotientGroup.mk (κ q) : ↥(FFModel.twistTensor n
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec ⧸ (FFModel.twistTensor n
        (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).ker.subgroupOf (FFModel.twistTensor n
          (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec) = q := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hκ]
  let Ψ : W → Matrix (Fin 2) (Fin 2) F := fun w => toMat n (κ (β ⟨w, Subgroup.mem_top w⟩)).1
  refine ⟨π0.comp e.toMonoidHom, Ψ, hsurj.comp e.surjective, fun w w' => ?_, fun w w' hww => ?_,
    fun w => (κ (β _)).2, fun X hX => ?_, fun γ w => ?_⟩
  · exact congrArg (fun x => toMat n x.1)
      ((congrArg κ (map_mul β ⟨w, Subgroup.mem_top w⟩ ⟨w', Subgroup.mem_top w'⟩)).trans
        (map_mul κ _ _))
  · have h1 : κ (β ⟨w, Subgroup.mem_top w⟩) = κ (β ⟨w', Subgroup.mem_top w'⟩) :=
      Subtype.ext (Multiplicative.toAdd.injective hww)
    have h2 : β ⟨w, Subgroup.mem_top w⟩ = β ⟨w', Subgroup.mem_top w'⟩ := by
      rw [← hmk (β _), h1, hmk]
    have h3 : β (⟨w, Subgroup.mem_top w⟩ * (⟨w', Subgroup.mem_top w'⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  · obtain ⟨⟨w, hw0⟩, hw⟩ := hβs (QuotientGroup.mk ⟨Multiplicative.ofAdd X, hX⟩)
    refine ⟨w, ?_⟩
    have h1 := congrArg (fun q => toMat n (κ q).1) hw
    simp only [hκ] at h1
    exact h1
  · have he := hβe (e γ) ⟨w, Subgroup.mem_top w⟩ (κ (β ⟨w, Subgroup.mem_top w⟩))
      (Subgroup.mem_top _) (hsec (e γ) _ (κ (β ⟨w, Subgroup.mem_top w⟩)).2)
      (hmk (β ⟨w, Subgroup.mem_top w⟩)).symm
    have h1 := congrArg (fun q => toMat n (κ q).1) he
    simp only [hκ] at h1
    exact h1

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
