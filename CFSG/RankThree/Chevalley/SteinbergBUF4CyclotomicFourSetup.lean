module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace EvenF4QPlus

theorem torusRootChar_baseChangeGL {τ : Tag} {L Ω : Type} [Field L] [Field Ω] (ι : L →+* Ω)
    (g : ModGL τ L) (α : Fin τ.rank → ℤ) :
    torusRootChar (baseChangeGL ι g) α = ι (torusRootChar g α) := by
  by_cases hα : IsRoot τ α
  · rw [torusRootChar, torusRootChar, dite_eq_left hα, dite_eq_left hα,
      rootVec_eq_single_of_isRoot hα, rootVec_eq_single_of_isRoot hα, baseChangeGL_apply_single,
      Finsupp.mapRange_apply]
  · rw [torusRootChar_of_not_isRoot _ hα, torusRootChar_of_not_isRoot _ hα, map_one]

section Element

variable {L Ω : Type} [Field L] [Field Ω] (ι : L →+* Ω)

theorem exists_rootDiagUnit_of_conj {p : ℕ} (hp : p.Prime) {x₀ : ModGL Tag.F4 L}
    (hx₀ : x₀ ∈ torusGroup Tag.F4 L) (hxp : orderOf (baseChangeGL ι x₀) = p)
    (u : WeylGroup Tag.F4)
    (hu : (fun α => u • α) '' {α | IsRoot Tag.F4 α ∧ torusRootChar (baseChangeGL ι x₀) α = 1} =
      parabolicRoots Tag.F4 {1, 2}) :
    ∃ c : Fin Tag.F4.rank → Lˣ,
      canonicalRep (coxeterSystem Tag.F4) L u * x₀ * (canonicalRep (coxeterSystem Tag.F4) L u)⁻¹ =
        rootDiagUnit Tag.F4 c ∧ c ^ p = 1 ∧ c ≠ 1 ∧
        rootCharKernel c = parabolicRoots Tag.F4 {1, 2} := by
  set y₀ := canonicalRep (coxeterSystem Tag.F4) L u * x₀ *
    (canonicalRep (coxeterSystem Tag.F4) L u)⁻¹ with hy₀
  have hy₀H : y₀ ∈ torusGroup Tag.F4 L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer u) x₀).1 hx₀
  have hinj := baseChangeGL_injective (τ := Tag.F4) ι
  have hord : orderOf y₀ = p := by
    rw [hy₀, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj _).injective x₀,
      ← orderOf_injective _ hinj x₀, hxp]
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy₀H
  have hcp : c ^ p = 1 := rootDiagUnit_injective (by
    rw [← rootDiagUnit_pow, ← hc, ← hord, pow_orderOf_eq_one, rootDiagUnit_one])
  have hc1 : c ≠ 1 := fun h1 => by
    rw [h1, rootDiagUnit_one] at hc
    rw [hc, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hker₀ : {β | IsRoot Tag.F4 β ∧ torusRootChar y₀ β = 1} = parabolicRoots Tag.F4 {1, 2} := by
    rw [← hu]
    have e := survivingRoots_canonicalRep_conj (L := L) hx₀ u
    rw [← hy₀] at e
    rw [e]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq, torusRootChar_baseChangeGL, map_eq_one_iff _ ι.injective]
  refine ⟨c, hc, hcp, hc1, ?_⟩
  rw [← hker₀]
  ext β
  constructor
  · rintro ⟨hβ, h1⟩
    refine ⟨hβ, ?_⟩
    rw [hc, torusRootChar_rootDiagUnit c hβ, h1, Units.val_one]
  · rintro ⟨hβ, h1⟩
    refine ⟨hβ, ?_⟩
    rw [hc, torusRootChar_rootDiagUnit c hβ] at h1
    exact Units.val_eq_one.1 h1

end Element

theorem canonicalRep_conj_eq_of_charTwo {M : Type} [Field M] [CharP M 2]
    (u w : WeylGroup Tag.F4) :
    canonicalRep (coxeterSystem Tag.F4) M u * canonicalRep (coxeterSystem Tag.F4) M w *
        (canonicalRep (coxeterSystem Tag.F4) M u)⁻¹ =
      canonicalRep (coxeterSystem Tag.F4) M (u * w * u⁻¹) := by
  rw [EvenF4QPlus.canonicalRep_inv_of_charTwo, ← EvenF4QPlus.canonicalRep_mul_of_charTwo,
    ← EvenF4QPlus.canonicalRep_mul_of_charTwo]

theorem smul_eq_of_weylAct_eq {v w' : WeylGroup Tag.F4}
    (h : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots Tag.F4 {f4Index 1, f4Index 2}),
      weylAct Tag.F4 v z = weylAct Tag.F4 w' z)
    (α : Fin Tag.F4.rank → ℤ) (h0 : α 0 = 0) (h3 : α 3 = 0) : v • α = w' • α := by
  have hsingle : ∀ i ∈ ({f4Index 1, f4Index 2} : Set (Fin Tag.F4.rank)),
      (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ parabolicRoots Tag.F4 {f4Index 1, f4Index 2} :=
    fun i hi => ⟨isRoot_single Tag.F4 i, fun k hk => Pi.single_eq_of_ne (fun e => hk (by
      rw [e]
      exact hi)) 1⟩
  have hα : α = α 1 • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) +
      α 2 • (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) := by
    have key : ∀ k : Fin Tag.F4.rank, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
    funext k
    rcases key k with rfl | rfl | rfl | rfl
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (by decide : (0 : Fin Tag.F4.rank) ≠ 1),
        Pi.single_eq_of_ne (by decide : (0 : Fin Tag.F4.rank) ≠ 2), h0]
      simp
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (1 : Fin Tag.F4.rank) ≠ 2)]
      simp
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (2 : Fin Tag.F4.rank) ≠ 1)]
      simp
    · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (by decide : (3 : Fin Tag.F4.rank) ≠ 1),
        Pi.single_eq_of_ne (by decide : (3 : Fin Tag.F4.rank) ≠ 2), h3]
      simp
  have hmem : ofLattice α ∈
      Submodule.span ℝ (ofLattice '' parabolicRoots Tag.F4 {f4Index 1, f4Index 2}) := by
    rw [hα, show ofLattice (α 1 • (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) +
        α 2 • (Pi.single 2 1 : Fin Tag.F4.rank → ℤ)) =
          α 1 • ofLattice (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) +
            α 2 • ofLattice (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) from by
        rw [← ofLatticeHom_apply, map_add, map_zsmul, map_zsmul, ofLatticeHom_apply,
          ofLatticeHom_apply]]
    refine add_mem (zsmul_mem (Submodule.subset_span
      (Set.mem_image_of_mem ofLattice (hsingle _ (Or.inl rfl)))) _)
      (zsmul_mem (Submodule.subset_span (Set.mem_image_of_mem ofLattice
        (hsingle _ (Or.inr rfl)))) _)
  have e := h _ hmem
  rw [weylAct_ofLattice, weylAct_ofLattice] at e
  exact ofLattice_injective e

section Levi

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {M : Type} [Field M] [Algebra K M]
  [FiniteDimensional K M]

theorem exists_levi_fixed_data (h4 : Module.finrank K M = 4) (σ : M ≃+* M)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (v : WeylGroup Tag.F4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hv : ∀ α : Fin Tag.F4.rank → ℤ, α 0 = 0 → α 3 = 0 →
      v • α = ((simple Tag.F4 1 * simple Tag.F4 2) ^ ε) • α) :
    ∃ Zf QK : Subgroup (ModGL Tag.F4 M), ∃ a ∈ subsystemGroup Tag.F4 M {1, 2},
      Zf ≤ torusGroup Tag.F4 M ∧ Odd (Nat.card Zf) ∧
      (∀ z ∈ Zf, ∀ x ∈ subsystemGroup Tag.F4 M {1, 2}, z * x = x * z) ∧
      (∀ g, g ∈ QK ↔ ∃ y ∈ subsystemGroup Tag.F4 K {1, 2},
        g = a * baseChangeGL (algebraMap K M) y * a⁻¹) ∧
      QK ≤ subsystemGroup Tag.F4 M {1, 2} ∧
      (torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M {1, 2}) ⊓
          ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) M v)).toMonoidHom.comp
            (Units.map (entrywiseHom σ.toRingHom))).eqLocus (MonoidHom.id _) = Zf ⊔ QK ∧
      Zf ⊓ QK = ⊥ ∧ Nonempty (QK ≃* EvenQuartic.spJ K) ∧
      Nonempty (QK ≃* subsystemGroup Tag.F4 K {1, 2}) ∧
      ∀ A : SL2 K, a * rootSL2 Tag.F4 M (Pi.single 1 1)
        (Matrix.SpecialLinearGroup.map (algebraMap K M) A) * a⁻¹ ∈ QK := by
  have : CharP M 2 := charP_of_injective_algebraMap (algebraMap K M).injective 2
  have : Finite M := Module.finite_of_finite K
  set θ : ModGL Tag.F4 M →* ModGL Tag.F4 M :=
    (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) M v)).toMonoidHom.comp
      (Units.map (entrywiseHom σ.toRingHom)) with hθdef
  let Z : Subgroup (ModGL Tag.F4 M) :=
    { carrier := {h | h ∈ torusGroup Tag.F4 M ∧ torusRootChar h (Pi.single 1 1) = 1 ∧
        torusRootChar h (Pi.single 2 1) = 1}
      one_mem' := ⟨one_mem _, torusRootChar_one _, torusRootChar_one _⟩
      mul_mem' := fun {a b} ha hb => by
        have hda := torusGroup_le_diagonalGroup ha.1
        have hdb := torusGroup_le_diagonalGroup hb.1
        refine ⟨mul_mem ha.1 hb.1, ?_, ?_⟩
        · rw [torusRootChar_mul hda hdb, ha.2.1, hb.2.1, one_mul]
        · rw [torusRootChar_mul hda hdb, ha.2.2, hb.2.2, one_mul]
      inv_mem' := fun {a} ha => by
        have hda := torusGroup_le_diagonalGroup ha.1
        refine ⟨inv_mem ha.1, ?_, ?_⟩
        · rw [torusRootChar_inv hda, ha.2.1, inv_one]
        · rw [torusRootChar_inv hda, ha.2.2, inv_one] }
  have hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 M ∧ torusRootChar h (Pi.single 1 1) = 1 ∧
      torusRootChar h (Pi.single 2 1) = 1 := fun h => Iff.rfl
  obtain ⟨-, -, hodd, a, ha, QK, hQK, hQfix, hsp, hLfix, -, hρ⟩ :=
    even_F4_native_B2_quartic_descent_and_full_Levi_direct_product K M h4 σ hσ Z
      (torusGroup Tag.F4 M ⊔ subsystemGroup Tag.F4 M {1, 2}) hZ rfl v ε hε hv θ
      (fun g => rfl)
  have hQKQ : QK ≤ subsystemGroup Tag.F4 M {1, 2} := hQfix ▸ inf_le_left
  have hZcomm : ∀ z ∈ Z, ∀ x ∈ subsystemGroup Tag.F4 M {1, 2}, z * x = x * z :=
    fun z hz x hx => commute_of_mem_char hZ hz hx
  refine ⟨Z ⊓ θ.eqLocus (MonoidHom.id _), QK, a, ha, fun z hz => hz.1.1, ?_,
    fun z hz x hx => hZcomm z hz.1 x hx, hQK, hQKQ, hLfix, ?_, hsp, ?_,
    fun A => by rw [← hQfix]; exact hρ A⟩
  · have hdvd : Nat.card (Z ⊓ θ.eqLocus (MonoidHom.id _) : Subgroup _) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat hodd hdvd
  · rw [eq_bot_iff, ← char_inf_subsystemGroup hZ]
    exact inf_le_inf inf_le_left hQKQ
  · have hinj : Function.Injective ((MulAut.conj a).toMonoidHom.comp
        (baseChangeGL (algebraMap K M)) : ModGL Tag.F4 K →* ModGL Tag.F4 M) :=
      (MulAut.conj a).injective.comp (baseChangeGL_injective (algebraMap K M))
    have hQKeq : QK = (subsystemGroup Tag.F4 K {1, 2}).map
        ((MulAut.conj a).toMonoidHom.comp (baseChangeGL (algebraMap K M))) := by
      ext g
      rw [hQK, Subgroup.mem_map]
      exact ⟨fun ⟨y, hy, hyg⟩ => ⟨y, hy, hyg.symm⟩, fun ⟨y, hy, hyg⟩ => ⟨y, hy, hyg.symm⟩⟩
    rw [hQKeq]
    exact ⟨((subsystemGroup Tag.F4 K {1, 2}).equivMapOfInjective _ hinj).symm⟩

end Levi

end CFSG.RankThree.Chevalley
