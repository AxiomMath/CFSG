module

public import CFSG.LocalAnalysis.StandardType.GGSelectedPSUModel
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.SelectedRoot CFSG.StandardType.SelectedRoot.SelPSU
open Matrix

namespace SelectedRoot

theorem exists_selectedModel_PSU_chart_rootPair_at
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (i : Fin n) (hi : i ≠ Fin.rev i) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot n i),
      model.phi.range = (Unitary.rootDatum hF n).rootGroup
          (InnerDiagSU.twoWtRoot n i) ⊔
        (Unitary.rootDatum hF n).rootGroup (-InnerDiagSU.twoWtRoot n i) ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f),
        (((model.phi A : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) =
          embM (pairCoord i)
            ((fixedSubfield F 2 f).subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) _)) := by
  classical
  let γ : Fin (Unitary.rootDatum hF n).rank → ℤ := InnerDiagSU.twoWtRoot n i
  let σ := unitaryInvolution F 2 f
  let k := fixedSubfield F 2 f
  have hσ : ∀ c : F, σ (σ c) = c := unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hk : ∀ c ∈ k, σ c = c := fun c hc => mem_fixedSubfield.mp hc
  have hrev : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hi.symm
  have hneg : toStd n (-γ) = 2 • weight n (Fin.rev i) :=
    toStd_neg_eq_two_weight_rev (InnerDiagSU.toStd_twoWtRoot i)
  obtain ⟨model, hmat⟩ := exists_selectedModel_PSU_chart_twoWt_at hF i hi
  have hphi : ∀ A, model.phi A =
      chart σ k (pairCoord_injective hi) (pairCoord_rev i) h2 hk A := by
    intro A
    apply Subtype.ext
    apply Units.ext
    exact hmat A
  have hlow : Set.range (fun t : k => model.phi (sl2Lower t)) =
      ((Unitary.rootDatum hF n).rootGroup (-γ) : Set (SU σ n)) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      change model.phi (sl2Lower t) ∈ (Unitary.rootDatum hF n).rootGroup (-γ)
      rw [hphi, chart_lower σ k hi h2 hk]
      exact SUExtras.longRootHom_mem hσ hrev hneg.symm _
    · intro hy
      obtain ⟨c, rfl⟩ := rootGroup_le_range_long hσ hrev hneg.symm hy
      let t : k := ⟨((Multiplicative.toAdd c : traceZero σ) : F),
        mem_fixedSubfield.mpr (fixed_of_mem_traceZero σ h2 (Multiplicative.toAdd c).2)⟩
      refine ⟨t, ?_⟩
      change model.phi (sl2Lower t) = (longRootHom σ hrev) c
      rw [hphi, chart_lower σ k hi h2 hk]
      congr 1
  refine ⟨model, ?_, hmat⟩
  exact SelectedSL2Model.ofRootMap_range _ _ model.root_mem model.phi model.injective
    model.upper_eq model.diag_mem
    (fun h hh => by obtain ⟨c, hc⟩ := model.scalar h hh; exact ⟨c, hc⟩) hlow

theorem exists_selectedModel_PSU_chart_rootPair
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ n) :
    ∃ model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot n ⟨0, by omega⟩),
      model.phi.range = (Unitary.rootDatum hF n).rootGroup
          (InnerDiagSU.twoWtRoot n ⟨0, by omega⟩) ⊔
        (Unitary.rootDatum hF n).rootGroup (-InnerDiagSU.twoWtRoot n ⟨0, by omega⟩) := by
  let i : Fin n := ⟨0, by omega⟩
  have hi : i ≠ Fin.rev i := by
    intro h
    have h' := congrArg Fin.val h
    dsimp [i] at h'
    omega
  obtain ⟨model, hrange, -⟩ := exists_selectedModel_PSU_chart_rootPair_at hF i hi
  exact ⟨model, hrange⟩

end SelectedRoot

theorem exists_unitary_models_conj_range_eq_twoWt
    {F : Type} [Field F] [Finite F] [CharP F 2] {f r n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hr : 4 ≤ r) (hn : 4 ≤ n)
    (ι : SU (unitaryInvolution F 2 f) r →* SU (unitaryInvolution F 2 f) n)
    {v w : Fin n → F}
    (hv : vecMul (fun i => unitaryInvolution F 2 f (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : vecMul (fun i => unitaryInvolution F 2 f (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : vecMul (fun i => unitaryInvolution F 2 f (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1)
    (hX : (((Unitary.rootDatum hF r).rootGroup
      (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
      (SU (unitaryInvolution F 2 f) n).subtype =
      unitTransvGroup (unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) v)
    (hXm : (((Unitary.rootDatum hF r).rootGroup
      (-InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
      (SU (unitaryInvolution F 2 f) n).subtype =
      unitTransvGroup (unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) w) :
    ∃ (model' : SelectedSL2Model (Unitary.rootDatum hF r) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩))
      (model : SelectedSL2Model (Unitary.rootDatum hF n) (fixedSubfield F 2 f)
        (InnerDiagSU.twoWtRoot n ⟨0, by omega⟩))
      (u : SU (unitaryInvolution F 2 f) n),
      ((MulAut.conj u).toMonoidHom.comp model.phi).range = (ι.comp model'.phi).range := by
  classical
  obtain ⟨model', hmodel'⟩ := exists_selectedModel_PSU_chart_rootPair hF hr
  obtain ⟨model, hmodel⟩ := exists_selectedModel_PSU_chart_rootPair hF hn
  let i : Fin n := ⟨0, by omega⟩
  have hi : i ≠ Fin.rev i := by
    intro h
    have h0 := congrArg Fin.val h
    dsimp [i] at h0
    omega
  obtain ⟨u, huX, huXm⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU_of_toStd hF n (by omega) i hi
      (InnerDiagSU.twoWtRoot n i) (InnerDiagSU.toStd_twoWtRoot i) v w hv hw hvw
  have hpos : ((Unitary.rootDatum hF n).rootGroup
      (InnerDiagSU.twoWtRoot n i)).map (MulAut.conj u).toMonoidHom =
      ((Unitary.rootDatum hF r).rootGroup
        (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι :=
    Subgroup.map_injective (f := (SU (unitaryInvolution F 2 f) n).subtype)
      Subtype.val_injective (huX.trans hX.symm)
  have hneg : ((Unitary.rootDatum hF n).rootGroup
      (-InnerDiagSU.twoWtRoot n i)).map (MulAut.conj u).toMonoidHom =
      ((Unitary.rootDatum hF r).rootGroup
        (-InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι :=
    Subgroup.map_injective (f := (SU (unitaryInvolution F 2 f) n).subtype)
      Subtype.val_injective (huXm.trans hXm.symm)
  refine ⟨model', model, u, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_comp, hmodel, hmodel',
    Subgroup.map_sup, Subgroup.map_sup, hpos, hneg]


theorem exists_rootMatch_of_unitary_twoWt_pair
    {F : Type} [Field F] [Finite F] [CharP F 2] {f r n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hr : 4 ≤ r) (hn : 4 ≤ n)
    (ι : SU (unitaryInvolution F 2 f) r →* SU (unitaryInvolution F 2 f) n)
    (hι : Function.Injective ι) {G : Type} [Group G]
    (ψ : SU (unitaryInvolution F 2 f) n →* G)
    (hψ : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    {v w : Fin n → F}
    (hv : vecMul (fun i => unitaryInvolution F 2 f (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : vecMul (fun i => unitaryInvolution F 2 f (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : vecMul (fun i => unitaryInvolution F 2 f (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1)
    (hX : (((Unitary.rootDatum hF r).rootGroup
      (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
      (SU (unitaryInvolution F 2 f) n).subtype =
      unitTransvGroup (unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) v)
    (hXm : (((Unitary.rootDatum hF r).rootGroup
      (-InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
      (SU (unitaryInvolution F 2 f) n).subtype =
      unitTransvGroup (unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) w) :
    ∃ u : SU (unitaryInvolution F 2 f) n,
      GGRootMatch (Unitary.rootDatum hF n) (Unitary.rootDatum hF r) ψ (ψ.comp ι)
        (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)
        (InnerDiagSU.twoWtRoot n ⟨0, by omega⟩) u := by
  obtain ⟨model', model, u, hS⟩ :=
    exists_unitary_models_conj_range_eq_twoWt hF hr hn ι hv hw hvw hX hXm
  apply SelectedRoot.selectedRootMatch_of_map_eq model model' ψ (ψ.comp ι) hψ
    (ker_comp_le_center_of_injective hψ hι) u
  have hmap := congrArg (fun S : Subgroup (SU (unitaryInvolution F 2 f) n) => S.map ψ) hS
  simpa only [MonoidHom.range_comp, MonoidHom.comp_assoc] using hmap



theorem exists_unitary_twoWt_pair_of_block
    {F : Type} [Field F] [Finite F] [CharP F 2] {f r n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hr : 4 ≤ r)
    {E : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {V : Matrix (Fin r) (Fin n) F} (hUV : U * V = E) (hVU : V * U = 1)
    (hA : transpose (U.map (unitaryInvolution F 2 f).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U = Unitary.antidiag r)
    (hE : transpose (E.map (unitaryInvolution F 2 f).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n * E)
    (ι : SU (unitaryInvolution F 2 f) r →* SU (unitaryInvolution F 2 f) n)
    (hιform : ∀ x, ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * V + (1 - E)) :
    ∃ v w : Fin n → F,
      vecMul (fun i => unitaryInvolution F 2 f (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      vecMul (fun i => unitaryInvolution F 2 f (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      vecMul (fun i => unitaryInvolution F 2 f (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1 ∧
      (((Unitary.rootDatum hF r).rootGroup
        (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
        (SU (unitaryInvolution F 2 f) n).subtype =
        unitTransvGroup (unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) v ∧
      (((Unitary.rootDatum hF r).rootGroup
        (-InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
        (SU (unitaryInvolution F 2 f) n).subtype =
        unitTransvGroup (unitaryInvolution F 2 f).toRingHom (Unitary.antidiag n) w := by
  classical
  let σ := unitaryInvolution F 2 f
  let i : Fin r := ⟨0, by omega⟩
  let v₀ : Fin r → F := Pi.single i 1
  let w₀ : Fin r → F := Pi.single (Fin.rev i) 1
  have hi : i ≠ Fin.rev i := by
    intro h
    have h0 := congrArg Fin.val h
    dsimp [i] at h0
    omega
  have hσv : (fun j => σ (v₀ j)) = v₀ := by
    funext j
    simp [v₀, Pi.single_apply]
  have hσw : (fun j => σ (w₀ j)) = w₀ := by
    funext j
    simp [w₀, Pi.single_apply]
  have hv₀ : vecMul (fun j => σ (v₀ j)) (Unitary.antidiag r) ⬝ᵥ v₀ = 0 := by
    rw [hσv]
    simp [v₀, dotProduct_single, Unitary.antidiag, hi]
  have hw₀ : vecMul (fun j => σ (w₀ j)) (Unitary.antidiag r) ⬝ᵥ w₀ = 0 := by
    rw [hσw]
    simp [w₀, dotProduct_single, Unitary.antidiag, hi.symm]
  have hvw₀ : vecMul (fun j => σ (v₀ j)) (Unitary.antidiag r) ⬝ᵥ w₀ = 1 := by
    rw [hσv]
    simp [v₀, w₀, dotProduct_single, Unitary.antidiag]
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hδ := InnerDiagSU.toStd_twoWtRoot i
  have hδm := toStd_neg_eq_two_weight_rev hδ
  have hir : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hi.symm
  have hplus := isUTransGroup_map_subtype_eq_unitTransvGroup σ
    (CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hi hδ)
  have hminus := isUTransGroup_map_subtype_eq_unitTransvGroup σ
    (CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hir hδm)
  have hX := unitTransvGroup_map_of_unitary_block σ hσ hUV hVU hA hE ι hιform v₀ hv₀
  have hXm := unitTransvGroup_map_of_unitary_block σ hσ hUV hVU hA hE ι hιform w₀ hw₀
  rw [← hplus, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq] at hX
  rw [← hminus, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq] at hXm
  exact ⟨U *ᵥ v₀, U *ᵥ w₀,
    (unitary_block_form_apply σ U hA v₀ v₀).trans hv₀,
    (unitary_block_form_apply σ U hA w₀ w₀).trans hw₀,
    (unitary_block_form_apply σ U hA v₀ w₀).trans hvw₀, hX, hXm⟩

section Canonical


theorem ggCompatPresented_of_unitary_twoWt_pair
    {f r n : ℕ} (hf : 1 ≤ f) (hr : 4 ≤ r) (hn : 4 ≤ n)
    (ι : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) r →*
      SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n)
    (hι : Function.Injective ι) {G : Type} [Group G]
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n →* G)
    (hψ : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n))
    {v w : Fin n → GaloisField 2 (2 * f)}
    (hv : vecMul (fun i => unitaryInvolution (GaloisField 2 (2 * f)) 2 f (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : vecMul (fun i => unitaryInvolution (GaloisField 2 (2 * f)) 2 f (w i))
      (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : vecMul (fun i => unitaryInvolution (GaloisField 2 (2 * f)) 2 f (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1)
    (hX : (((Unitary.rootDatum (card_galoisField_two_mul 2 f hf) r).rootGroup
      (InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
      (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n).subtype =
      unitTransvGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f).toRingHom
        (Unitary.antidiag n) v)
    (hXm : (((Unitary.rootDatum (card_galoisField_two_mul 2 f hf) r).rootGroup
      (-InnerDiagSU.twoWtRoot r ⟨0, by omega⟩)).map ι).map
      (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n).subtype =
      unitTransvGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f).toRingHom
        (Unitary.antidiag n) w) :
    GGCompatPresented (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n)
      ψ (ψ.comp ι).range := by
  obtain ⟨u, hmatch⟩ := exists_rootMatch_of_unitary_twoWt_pair
    (card_galoisField_two_mul 2 f hf) hr hn ι hι ψ hψ hv hw hvw hX hXm
  have hadm : StatedLieAdmissible .PSU r 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_⟩
    intro h
    have h3 := congrArg Prod.fst h
    dsimp only at h3
    omega
  have hMr : ggU .PSU r f =
      (⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) r,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) r⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  have hi : (⟨0, by omega⟩ : Fin r) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have h0 := congrArg Fin.val h
    simp only [Fin.val_rev] at h0
    omega
  have hj : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have h0 := congrArg Fin.val h
    simp only [Fin.val_rev] at h0
    omega
  unfold GGCompatPresented
  refine ⟨.PSU, r, f, ?_⟩
  rw [hMr]
  refine ⟨ψ.comp ι, hadm, ?_, ker_comp_le_center_of_injective hψ hι, rfl,
    InnerDiagSU.twoWtRoot r ⟨0, by omega⟩, InnerDiagSU.twoWtRoot_mem_roots hi,
    InnerDiagSU.twoWtRoot n ⟨0, by omega⟩, InnerDiagSU.twoWtRoot_mem_roots hj,
    u, hmatch⟩
  change 2 ≤ r / 2
  omega


theorem ggCompatPresented_of_unitary_block
    {f r n : ℕ} (hf : 1 ≤ f) (hr : 4 ≤ r) (hn : 4 ≤ n)
    {E : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f))}
    {U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * f))}
    {V : Matrix (Fin r) (Fin n) (GaloisField 2 (2 * f))}
    (hUV : U * V = E) (hVU : V * U = 1)
    (hA : transpose (U.map (unitaryInvolution (GaloisField 2 (2 * f)) 2 f).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f))) * U =
        Unitary.antidiag r)
    (hE : transpose (E.map (unitaryInvolution (GaloisField 2 (2 * f)) 2 f).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f))) =
        Unitary.antidiag n * E)
    (ι : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) r →*
      SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n)
    (hιform : ∀ x, ((ι x : GL (Fin n) (GaloisField 2 (2 * f))) :
      Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f))) =
      U * ((x : GL (Fin r) (GaloisField 2 (2 * f))) :
        Matrix (Fin r) (Fin r) (GaloisField 2 (2 * f))) * V + (1 - E))
    {G : Type} [Group G]
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n →* G)
    (hψ : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n)) :
    GGCompatPresented (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n)
      ψ (ψ.comp ι).range := by
  have hι : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    apply Units.ext
    have hmat := congrArg (fun z : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n =>
      ((z : GL (Fin n) (GaloisField 2 (2 * f))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f)))) h
    rw [hιform x, hιform y] at hmat
    have hblock := congrArg (fun A => V * A * U) (add_right_cancel hmat)
    have hcancel (A : Matrix (Fin r) (Fin r) (GaloisField 2 (2 * f))) :
        V * (U * A * V) * U = A := by
      calc V * (U * A * V) * U = (V * U) * A * (V * U) := by
              simp only [Matrix.mul_assoc]
        _ = A := by rw [hVU, Matrix.one_mul, Matrix.mul_one]
    rwa [hcancel, hcancel] at hblock
  obtain ⟨v, w, hv, hw, hvw, hX, hXm⟩ := exists_unitary_twoWt_pair_of_block
    (card_galoisField_two_mul 2 f hf) hr hUV hVU hA hE ι hιform
  exact ggCompatPresented_of_unitary_twoWt_pair hf hr hn ι hι ψ hψ hv hw hvw hX hXm



end Canonical

end CFSG.StandardType

end
