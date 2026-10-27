module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBound
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.StandardType.B36

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType.InndiagSU
open CFSG.SectionRank.OddCover (diagHom diagHom_injective det_diagHom)

theorem twA41_selfCent_elemAbelian_three :
    LargeEvenLabelAll ⟨.twA, 4, 1⟩ fun R _ _ _ =>
      ∀ E : Subgroup R, IsElemAbelian 3 E →
        (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) → Nat.card E = 3 ^ 4 := by
  intro Q hQ
  change LargeEvenRecipeUnitary 5 2 Q at hQ
  change LargeEvenRecipeUnitary 5 2 (fun R _ I F => Q R I F ∧
    ∀ E : Subgroup R, IsElemAbelian 3 E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) → Nat.card E = 3 ^ 4)
  refine recipeUnitary_and (fun (K : Type) [Field K] [Finite K]
    (hKcard : Nat.card K = 2 ^ 2) => ?_) hQ
  intro E hE hsc
  have h : UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hKcard]⟩
  have hcardK : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hKcard]; norm_num
  have hscal : Nat.card (unitaryScalars h 5) = 1 := by
    rw [card_unitaryScalars h (by norm_num)]; norm_num
  have hbot : unitaryScalars h 5 = ⊥ := Subgroup.eq_bot_of_card_eq _ hscal
  let e : LargeEvenProj (LargeEvenSUGroup (Fin 5) K 2) ≃* ↥(unitarySU 2 1 K 5) :=
    (unitaryPSUEquiv h (by norm_num)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
  set E' : Subgroup ↥(unitarySU 2 1 K 5) := E.map e.toMonoidHom with hE'def
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE e.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card E := by
    rw [hE'def]
    exact (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : LargeEvenProj (LargeEvenSUGroup (Fin 5) K 2), e x ∈ E' ↔ x ∈ E := by
    intro x
    rw [hE'def]
    exact ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g : ↥(unitarySU 2 1 K 5),
      (∀ x ∈ E', g * x = x * g) → g ^ 3 = 1 → g ∈ E' := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h Nat.prime_three (by norm_num) hE'
  set c : ↥(unitarySU 2 1 K 5) ≃* ↥(unitarySU 2 1 K 5) :=
    TableBUE.conjSU h P hP with hc
  have hPd' : ∀ x ∈ E', ∃ σ : Fin 5 → Kˣ,
      ((c x : ↥(unitarySU 2 1 K 5)) : GL (Fin 5) K) = diagHom 5 σ := by
    simpa only [hc] using hPd
  let prodHom : (Fin 5 → Kˣ) →* Kˣ :=
    MonoidHom.mk' (fun σ => ∏ i, σ i) (fun σ τ => by
      simp only [Pi.mul_apply, Finset.prod_mul_distrib])
  have hsurj : Function.Surjective prodHom := by
    intro b
    refine ⟨fun i => if i = 0 then b else 1, ?_⟩
    show (∏ i : Fin 5, (if i = 0 then b else 1 : Kˣ)) = b
    rw [Finset.prod_eq_single (0 : Fin 5)]
    · simp
    · intro i _ hi; simp [hi]
    · intro h0; exact absurd (Finset.mem_univ (0 : Fin 5)) h0
  set W : Subgroup (Fin 5 → Kˣ) := prodHom.ker with hW
  have hcardFun : Nat.card (Fin 5 → Kˣ) = 3 ^ 5 := by
    rw [Nat.card_fun, Nat.card_fin, hcardK]
  have hkerCard : Nat.card W = 3 ^ 4 := by
    have h1 := TableB.card_range_mul_card_ker prodHom
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcardK, hcardFun] at h1
    rw [← hW] at h1
    have h2 : (3 : ℕ) ^ 5 = 3 * 3 ^ 4 := by norm_num
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hpow3 : ∀ a : Kˣ, a ^ 3 = 1 := by
    intro a
    have h1 := pow_card_eq_one' (G := Kˣ) (x := a)
    rwa [hcardK] at h1
  let diagH : W →* ↥(unitarySU 2 1 K 5) :=
    MonoidHom.codRestrict ((diagHom 5).comp W.subtype) (unitarySU 2 1 K 5) (fun σ => by
      have hσker : prodHom σ = 1 := MonoidHom.mem_ker.mp (by simpa [W] using σ.2)
      exact TableBUE.diagHom_mem_unitarySU h (fun k => hpow3 ((σ : Fin 5 → Kˣ) k))
        (by simpa [prodHom] using hσker))
  set D : Subgroup ↥(unitarySU 2 1 K 5) := (⊤ : Subgroup W).map diagH with hD
  have hdiagH_inj : Function.Injective diagH := by
    intro σ τ hστ
    apply Subtype.ext
    apply diagHom_injective 5
    have h := congrArg (fun x : ↥(unitarySU 2 1 K 5) => (x : GL (Fin 5) K)) hστ
    exact h
  have hDcardW : Nat.card D = Nat.card W := by
    rw [hD, Subgroup.card_map_of_injective hdiagH_inj, Subgroup.card_top]
  have hDcard : Nat.card D = 3 ^ 4 := by rw [hDcardW, hkerCard]
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    rw [hD] at ha hb
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, mul_comm σ τ]
  have hED : E'.map c ≤ D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hD]
    obtain ⟨σ, hσ⟩ := hPd' x hx
    have hdet : (diagHom 5 σ : GL (Fin 5) K) ∈ unitarySU 2 1 K 5 := by
      rw [← hσ]; exact (c x).2
    have hprod : (∏ i, σ i : Kˣ) = 1 := by
      apply Units.ext
      have hd := ((mem_unitarySU_iff h).mp hdet).1
      rw [det_diagHom] at hd
      simpa using hd
    refine Subgroup.mem_map.mpr ⟨⟨σ, MonoidHom.mem_ker.mpr (by simpa [prodHom] using hprod)⟩,
      Subgroup.mem_top _, ?_⟩
    exact Subtype.ext hσ.symm
  have hDE : D ≤ E'.map c := by
    intro d hd
    rw [hD] at hd
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hd
    have hσD : diagH σ ∈ D := by
      rw [hD]
      exact Subgroup.mem_map.mpr ⟨σ, Subgroup.mem_top _, rfl⟩
    have hσ3 : σ ^ 3 = 1 := by
      apply Subtype.ext
      funext k
      simpa using hpow3 ((σ : Fin 5 → Kˣ) k)
    have hmem' : c.symm (diagH σ) ∈ E' := by
      apply hsc'
      · intro x hx
        apply c.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hDcomm _ hσD _ (hED ⟨x, hx, rfl⟩)
      · apply c.injective
        rw [map_pow, map_one, MulEquiv.apply_symm_apply, ← map_pow, hσ3, map_one]
    exact Subgroup.mem_map.mpr
      ⟨c.symm (diagH σ), hmem', by exact MulEquiv.apply_symm_apply c _⟩
  have hmapED : E'.map c = D := le_antisymm hED hDE
  have hcardE'D : Nat.card E' = Nat.card D := by
    rw [← hmapED]
    exact Nat.card_congr (E'.equivMapOfInjective c.toMonoidHom c.injective).toEquiv
  rw [← hcardE', hcardE'D, hDcard]

end CFSG.StandardType.B36

end
