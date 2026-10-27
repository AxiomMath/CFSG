module

public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl
public import CFSG.Quasithin.Vol2.Ch10SecQ34B0
public import CFSG.Quasithin.Vol2.Ch10SecQ3CB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open SecA

variable {F : Type} [Field F]

theorem sl_inv_mul (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem mulVec_conj (g γ : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    (g : Matrix (Fin 2) (Fin 2) F).mulVec ((γ : Matrix (Fin 2) (Fin 2) F).mulVec w) =
      ((g * γ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec ((g : Matrix (Fin 2) (Fin 2) F).mulVec w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, sl_inv_mul, Matrix.mul_one]

theorem eq_one_of_sq_of_odd {M : Type*} [Monoid M] {d : M} (hd : d ^ 2 = 1)
    (hodd : Odd (orderOf d)) : d = 1 := by
  have h := orderOf_dvd_of_pow_eq_one hd
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

end C11AmS

open SecA C11AmS

theorem factNatBorelFix_holds : FactNatBorelFix := by
  intro V _ _ H n hnat S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, π, hR⟩ := hnat
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_beta_of_realizesVia_nat hR
  have hπinj : Function.Injective π := hR.injective_of_faithful (FFModel.nat_faithful _)
  set eρ : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥H :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).trans
      (MulEquiv.ofBijective π ⟨hπinj, hR.1⟩) with heρ
  have hβe' : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) K) (v : V),
      β (((eρ γ : ↥H) : MulAut V) v) = Multiplicative.ofAdd
        ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β v))) :=
    fun γ v => hβe _ v
  set P := (S.subgroupOf H).comap eρ.toMonoidHom with hPdef
  have hmemP : ∀ γ, γ ∈ P ↔ ((eρ γ : ↥H) : MulAut V) ∈ S := fun γ => Iff.rfl
  have hP2 : IsPGroup 2 P :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).comap_of_injective
      eρ.toMonoidHom eρ.injective
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hPdef, Subgroup.index_comap_of_surjective _ eρ.surjective]
    exact hS.2.2
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip hK hP2 hPidx
  set ζ : V → (Fin 2 → K) := fun v =>
    (g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β v)) with hζ
  have hζinj : Function.Injective ζ := by
    intro v v' h
    have h1 := congrArg (fun z => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec z) h
    simp only [hζ, Matrix.mulVec_mulVec, sl_inv_mul, Matrix.one_mulVec] at h1
    have h2 : β v = β v' := by simpa using congrArg Multiplicative.ofAdd h1
    have h3 : β (v * v'⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hβk _).mp h3))
  have hζsurj : Function.Surjective ζ := by
    intro z
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec z))
    refine ⟨v, ?_⟩
    simp only [hζ, hv, toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec]
  have hζe : ∀ γ v, ζ (((eρ γ : ↥H) : MulAut V) v) =
      ((g * γ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).mulVec (ζ v) := by
    intro γ v
    simp only [hζ, hβe', toAdd_ofAdd]
    exact mulVec_conj g γ _
  have hζ1 : ζ 1 = 0 := by simp [hζ]
  have hfixS : ∀ v, v ∈ fixV S ↔ ζ v 1 = 0 := by
    intro v
    constructor
    · intro hv
      have h1 := hv _ ((hmemP _).mp (hPg 1))
      have h2 := congrArg ζ h1
      rw [hζe, show g * (g⁻¹ * unipSL 1 * g) * g⁻¹ = unipSL (1 : K) by group, coe_unipSL,
        unipSL_mulVec] at h2
      have h3 := congrFun h2 0
      simp only [Matrix.cons_val_zero, one_mul] at h3
      linear_combination h3
    · intro h1 s hs
      set γ := eρ.symm ⟨s, hS.1 hs⟩ with hγ
      have hγs : ((eρ γ : ↥H) : MulAut V) = s := by rw [hγ, MulEquiv.apply_symm_apply]
      obtain ⟨b, hb⟩ := hgP γ ((hmemP γ).mpr (by rw [hγs]; exact hs))
      apply hζinj
      rw [← hγs, hζe, hb, coe_unipSL, unipSL_mulVec, h1, mul_zero, add_zero]
      ext i
      fin_cases i <;> simp [h1]
  refine ⟨?_, ?_⟩
  ·
    rw [← hK]
    refine Nat.card_eq_of_bijective (fun v : ↥(fixV S) => ζ v 0) ⟨fun v v' h => ?_, fun c => ?_⟩
    · apply Subtype.ext
      apply hζinj
      ext i
      fin_cases i
      · exact h
      · simp only [Fin.mk_one, Fin.isValue]
        rw [(hfixS v).mp v.2, (hfixS v').mp v'.2]
    · obtain ⟨v, hv⟩ := hζsurj ![c, 0]
      refine ⟨⟨v, (hfixS v).mpr (by rw [hv]; rfl)⟩, ?_⟩
      simp only [hv]
      rfl
  ·
    intro d hd hd1 hodd
    set δ := eρ.symm ⟨d, hd.1⟩ with hδ
    have hδd : ((eρ δ : ↥H) : MulAut V) = d := by rw [hδ, MulEquiv.apply_symm_apply]
    have hδP : ∀ γ ∈ P, δ * γ * δ⁻¹ ∈ P := by
      intro γ hγ
      rw [hmemP] at hγ ⊢
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hδd]
      exact (Subgroup.mem_normalizer_iff.mp hd.2 _).mp hγ
    set δ' := g * δ * g⁻¹ with hδ'
    obtain ⟨c, hc⟩ := hgP _ (hδP _ (hPg 1))
    have hc' : δ' * unipSL 1 = unipSL c * δ' := by
      have : δ' * unipSL 1 * δ'⁻¹ = unipSL c := by rw [← hc, hδ']; group
      rw [← this]
      group
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [unipSL_zero, one_mul] at hc'
      have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K) 0 1) (mul_left_cancel (a := δ') (hc'.trans (mul_one _).symm))
      simp [coe_unipSL] at h1
    have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 0) hc'
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      coe_unipSL] at h00
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.empty_val'] at h00
    have h10 : (δ' : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      have : c * (δ' : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination -h00
      exact (mul_eq_zero.mp this).resolve_left hc0
    have hdet := δ'.2
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hdv : d v = v := hv d (Subgroup.mem_zpowers d)
    have hz := congrArg ζ hdv
    rw [← hδd, hζe, ← hδ'] at hz
    set z := ζ v with hzdef
    have hz0 := congrFun hz 0
    have hz1 := congrFun hz 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, zero_mul, zero_add] at hz0 hz1
    by_cases he : (δ' : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
    · exfalso
      have ha : (δ' : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by rw [he, mul_one] at hdet; exact hdet
      have hδu : δ' = unipSL ((δ' : Matrix (Fin 2) (Fin 2) K) 0 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [coe_unipSL, ha, he, h10]
      have hsq : δ' * δ' = 1 := by rw [hδu]; exact unipSL_mul_self _
      have hδsq : δ ^ 2 = 1 := by
        have : g⁻¹ * (δ' * δ') * g = δ * δ := by rw [hδ']; group
        rw [sq, ← this, hsq]
        group
      have hdsq : d ^ 2 = 1 := by
        rw [← hδd, ← Subgroup.coe_pow, ← map_pow, hδsq, map_one, Subgroup.coe_one]
      exact hd1 (eq_one_of_sq_of_odd hdsq hodd)
    · have hz1' : z 1 = 0 := by
        have : ((δ' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * z 1 = 0 := by
          linear_combination hz1
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr he)
      have ha : (δ' : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 1 := by
        intro ha
        rw [ha, one_mul] at hdet
        exact he hdet
      have hz0' : z 0 = 0 := by
        rw [hz1', mul_zero, add_zero] at hz0
        have : ((δ' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * z 0 = 0 := by
          linear_combination hz0
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha)
      apply hζinj
      rw [hζ1]
      ext i
      fin_cases i
      · exact hz0'
      · exact hz1'

end CFSG.Quasithin.Vol2.Ch10.SecB
