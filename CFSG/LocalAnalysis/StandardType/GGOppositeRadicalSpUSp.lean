module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUBasis
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUGen
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer
public import CFSG.GroupTheory.OppositeRadicals

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank GGOppRad

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_lt_of_spU_ne_bot {ℓ : Fin n ⊕ Fin n → ℕ} (h : spU n K ℓ ≠ ⊥) :
    ∃ c a, ℓ c < ℓ a := by
  by_contra hno
  refine h ((Subgroup.eq_bot_iff_forall _).mpr fun g hg => Subtype.ext (Units.ext ?_))
  ext c a
  rw [Subgroup.coe_one, Units.val_one]
  exact mem_spU_iff.mp hg c a fun hca => hno ⟨c, a, hca⟩

theorem hasGoodOppositePRadicals_spU {r : ℕ} [Fact r.Prime] [CharP K r] {M : ℕ}
    {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    (hQ : CFSG.GroupTheory.IsRadicalPGroup r ⊤ (spU n K ℓ))
    (hN : (⊤ : Subgroup (StatedSp n K)) ⊓
      Subgroup.normalizer (spU n K ℓ : Set (StatedSp n K)) = spP n K ℓ)
    (hne : spU n K ℓ ≠ ⊥) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r ⊤ (spU n K ℓ) := by
  refine ⟨spU n K (ℓ ∘ Sum.swap), ⟨?_, card_spU_comp_swap n K ℓ, ?_⟩,
    sup_spU_comp_swap hℓ (exists_lt_of_spU_ne_bot hne), fun V hV => ?_⟩
  · rw [spU_comp_swap]
    exact hQ.map_mulAut (MulAut.conj (spJ' n K))
      (Subgroup.map_top_of_surjective _ (MulAut.conj (spJ' n K)).surjective)
  · rw [hN]
    exact spU_comp_swap_inf_spP hℓ
  obtain ⟨hVrad, hVcard, hVbot⟩ := hV
  set F' := isoFlag (spForm n K) (natRep (StatedSp n K)) V with hF'def
  obtain ⟨hVeq, -⟩ := eq_flagKernel_isoFlag_of_isRadicalPGroup (F := spForm n K)
    (ρ := natRep (StatedSp n K)) r (natRep_injective _) (isIsometric_natRep_statedSp n K) hVrad
  have hbot : flagKernel (natRep (StatedSp n K)) F' ⊓
      flagStab (natRep (StatedSp n K)) (stdFlag ℓ) = ⊥ := by
    rw [← hVeq]
    rw [hN] at hVbot
    exact hVbot
  have hF' := isSelfDual_isoFlag (spForm n K) (natRep (StatedSp n K)) V
  have hA := isSelfDual_stdFlag (K := K) hℓ
  have hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j) :=
    exists_isCompl_of_inf_eq_bot (natRep (StatedSp n K)) (fun x => exists_transvection x)
      (fun _ _ hxy => exists_siegel hxy) hA hF' hbot
  obtain ⟨u, i, hi, hu, huF, hle⟩ := exists_eq_flagMap_of_isCompl hℓ hF' (by omega) hcompl
  have hVD : V = (spU n K i).map (MulAut.conj u).toMonoidHom := by
    rw [spU, ← flagKernel_flagMap, huF]
    exact hVeq
  have hcV : Nat.card V = Nat.card (spU n K i) := by
    rw [hVD]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hc1 : Nat.card (spU n K ℓ) ≤ Nat.card (spU n K (i ∘ Sum.swap)) := by
    rw [card_spU_comp_swap, ← hcV, hVcard]
  have heq : spU n K (i ∘ Sum.swap) = spU n K ℓ := Subgroup.eq_of_le_of_card_ge hle hc1
  have hii : (i ∘ Sum.swap) ∘ Sum.swap = i := by
    funext a
    simp
  have heq' : spU n K i = spU n K (ℓ ∘ Sum.swap) := by
    rw [← hii, spU_comp_swap, heq, ← spU_comp_swap]
  exact ⟨u, hu, hVD.trans (by rw [heq'])⟩

theorem hasGoodOppositePRadicals_sp {r : ℕ} [Fact r.Prime] [CharP K r]
    {Q : Subgroup (StatedSp n K)} (hQne : Q ≠ ⊥)
    (hQ : CFSG.GroupTheory.IsRadicalPGroup r ⊤ Q) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r ⊤ Q := by
  obtain ⟨hQeq, hQN⟩ := eq_flagKernel_isoFlag_of_isRadicalPGroup (F := spForm n K)
    (ρ := natRep (StatedSp n K)) r (natRep_injective _) (isIsometric_natRep_statedSp n K) hQ
  obtain ⟨g, ℓ, hℓ, hF⟩ := exists_isoFlag_eq_flagMap (K := K) Q
  have hQU : Q = (spU n K ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [spU, ← flagKernel_flagMap, ← hF]
    exact hQeq
  have hQP : Subgroup.normalizer (Q : Set (StatedSp n K)) =
      (spP n K ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [spP, ← flagStab_flagMap, ← hF, ← hQN, top_inf_eq]
  have hQ0 : spU n K ℓ = Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hQU, ← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one]
  have hrad0 : CFSG.GroupTheory.IsRadicalPGroup r ⊤ (spU n K ℓ) := by
    rw [hQ0]
    exact hQ.map_mulAut (MulAut.conj g⁻¹)
      (Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective)
  have hN0 : (⊤ : Subgroup (StatedSp n K)) ⊓
      Subgroup.normalizer (spU n K ℓ : Set (StatedSp n K)) = spP n K ℓ := by
    rw [hQ0, top_inf_eq, ← GGTwoSig.map_conj_normalizer, hQP, ← GGTwoSig.map_conj_mul,
      inv_mul_cancel, GGTwoSig.map_conj_one]
  have hne0 : spU n K ℓ ≠ ⊥ := fun h => hQne (by rw [hQU, h, Subgroup.map_bot])
  rw [hQU]
  exact (hasGoodOppositePRadicals_spU hℓ hrad0 hN0 hne0).map_mulAut (MulAut.conj g)
    (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective)

section CharTwo

variable [CharP K 2]

theorem ggOppRadGood_spU {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    (hQ : GGRadicalTwo ⊤ (spU n K ℓ))
    (hN : (⊤ : Subgroup (StatedSp n K)) ⊓
      Subgroup.normalizer (spU n K ℓ : Set (StatedSp n K)) = spP n K ℓ)
    (hne : spU n K ℓ ≠ ⊥) : GGOppRadGood ⊤ (spU n K ℓ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hasGoodOppositePRadicals_spU hℓ hQ hN hne

theorem ggOppRadGood_sp {Q : Subgroup (StatedSp n K)} (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ⊤ Q) :
    GGOppRadGood ⊤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hasGoodOppositePRadicals_sp hQne hQ

omit [Finite K] in
theorem eq_one_of_mem_center_sp {z : StatedSp n K}
    (hz : z ∈ Subgroup.center (StatedSp n K)) (h2 : z ^ 2 = 1) : z = 1 := by
  have hcomm : ∀ h : StatedSp n K,
      ((z : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          ((h : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        ((h : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          ((z : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    intro h
    have h1 := Subgroup.mem_center_iff.mp hz h
    have h3 := congrArg (fun x : StatedSp n K =>
      ((x : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h1
    simpa only [Subgroup.coe_mul, Units.val_mul] using h3.symm
  have hmem : ∀ x : TauCeti.GLSymplectic (Fin n) K, (x : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K :=
    fun x => by
      rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
      exact x.2
  obtain ⟨d, hd⟩ := CFSG.ClassicalGroups.Symplectic.eq_scalar_of_commute_unipotents
    ((z : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (fun B hB => by
      have := hcomm ⟨_, hmem (CFSG.ClassicalGroups.Symplectic.upperUnipotent hB)⟩
      simpa only [CFSG.ClassicalGroups.Symplectic.coe_upperUnipotent] using this)
    (fun C hC => by
      have := hcomm ⟨_, hmem (CFSG.ClassicalGroups.Symplectic.lowerUnipotent hC)⟩
      simpa only [CFSG.ClassicalGroups.Symplectic.coe_lowerUnipotent] using this)
  refine Subtype.ext (Units.ext ?_)
  ext a b
  have h3 : ((z : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      ((z : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
    have := congrArg (fun x : StatedSp n K =>
      ((x : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h2
    simpa only [pow_two, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
      using this
  rw [hd, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at h3
  have hd2 : d * d = 1 := by
    have := congrFun (congrFun h3 a) a
    rwa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
  have hd1 : d = 1 := by
    have h4 : (d - 1) ^ 2 = 0 := by
      calc (d - 1) ^ 2 = (d * d - 1) - 2 * (d - 1) := by ring
        _ = 0 := by rw [hd2, CharTwo.two_eq_zero]; ring
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h4)
  rw [hd, hd1, Matrix.scalar_apply, Subgroup.coe_one, Units.val_one, Matrix.diagonal_one]

theorem ggOppRadGood_of_sp {G : Type*} [Group G] [Finite G] (ψ : StatedSp n K →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n K)) {Q : Subgroup G}
    (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ψ.range Q) : GGOppRadGood ψ.range Q :=
  GGOppRadGood.of_lift ψ hker (fun _ hz h2 => eq_one_of_mem_center_sp (hker hz) h2)
    (fun _ hQne' hQ' => ggOppRadGood_sp hQne' hQ') hQne hQ

end CharTwo

end GGOppRadSpU

end CFSG.StandardType
