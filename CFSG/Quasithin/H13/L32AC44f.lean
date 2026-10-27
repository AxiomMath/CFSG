module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.SmithB42L2Alt5
public import CFSG.Quasithin.Background.SmithB45SL3Excl
public import CFSG.Quasithin.Background.SmithB45SL3Herm

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.B45SL3 CFSG.Quasithin.H CFSG.Quasithin
open CFSG.Quasithin.H.L3Nine (HMod rho rhoT img norm mat)
open CFSG.Quasithin.B42SL3 (innerPart exists_lift_of_inner)
open scoped MatrixGroups Matrix

theorem natural_or_nine
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f)
    (hq2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    BinaryNaturalSL L ⊤ ⊥ 3 f ∨ ∃ m, 1 ≤ m ∧ f = 2 * m ∧ BinaryNineTensor L ⊤ ⊥ m := by
  classical
  obtain ⟨-, F, _, _, φ₀, hFcard, hcov⟩ := B42SL3.exists_cover hV hHyp (by omega) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV'
  have hirrV := Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set ρ := B42SL3.repOf θ φ₀ with hρ
  have hker := B42SL3.repOf_ker θ hcov
  have hirr := B42SL3.repOf_irreducible θ hirrV hcov.surjective
  have hnt : ∃ x, ρ x ≠ 1 := ⟨up3 0 0 1, fun h => by
    obtain ⟨c, -, hc⟩ := hker _ h
    exact not_scalar_up3 (F := F) ⟨(c : F), hc⟩⟩
  have hLG : L ≤ G := hHyp.2.1 ▸ quasithinGenFitting_le G
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B42L2.le_normalizer_of_b4Hyp hHyp
  let bas := Module.finBasis (ZMod 2) W
  obtain ⟨a, b, Wj, hne, hWirr, heq, -, hO, hsd⟩ := exists_label_pkg hF (by omega) ρ bas hirr hnt
  obtain ⟨e₀⟩ := heq 0
  have htrW : ∀ {B : Subgroup (MulAut V)}, IsA2 G B →
      CFSG.IsElementaryAbelian 2 ↥(B.map (binPsi θ).toMonoidHom) ∧
        B.map (binPsi θ).toMonoidHom ≠ ⊥ ∧
        ∀ x ∈ B.map (binPsi θ).toMonoidHom, ∀ y : SL(3, F), ∃ z, Intertwines ρ x y z := by
    intro B hB
    refine ⟨(isElemAbelian2_iff_map θ B).1 hB.2.2, ?_,
      B42SL3.intertwines_map θ hcov.surjective (hB.1.trans hGN)⟩
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective B (binPsi θ).injective]
    exact hB.2.1
  obtain ⟨A, hA2, -, hAr⟩ := kq_le_iff.1 hq2
  obtain ⟨hAWel, hAWne, hAWn⟩ := htrW hA2
  have h2F : Nat.card W ≤ Nat.card ↥(A.map (binPsi θ).toMonoidHom) ^ 2 *
      Nat.card {w : W // ∀ x ∈ A.map (binPsi θ).toMonoidHom, x w = w} := by
    rw [B42SL3.card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective, ← natCard_eq θ]
    exact (rAV_le_two_iff hV hA2).1 hAr
  rcases natural_or_row ρ hker _ hAWn (by omega) hF hirr hAWne h2F bas hne (Wj 0) (hWirr 0) e₀
    hO with hnat | ⟨hS, hH, hlt⟩
  ·
    obtain ⟨ψ, hψ, E, hE⟩ :=
      B42SL3.exists_natural_of_single hF ρ bas hirr hnat.1 hnat.2 (Wj 0) e₀
    let ε := specialLinearGroupEquivStatedSL 3 F
    let π : ↥(StatedSL 3 F) →* ↥L := φ₀.comp (ψ.comp ε.symm.toMonoidHom)
    have hπ : Function.Surjective π := by
      intro l
      obtain ⟨x, rfl⟩ := hcov.surjective l
      exact ⟨ε (ψ x), by simp [π, hψ]⟩
    let e : V ≃* H.StdMod (Fin 3) F := θ.trans (AddEquiv.toMultiplicative E)
    have he : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
        e (((π γ : ↥L) : MulAut V) v) = natAct (StatedSL 3 F) γ (e v) := by
      intro γ v
      obtain ⟨g, rfl⟩ := ε.surjective γ
      have h1 : π (ε g) = φ₀ (ψ g) := by simp [π]
      have h2 := B42SL3.repOf_toAdd θ φ₀ (ψ g) v
      show Multiplicative.ofAdd (E (Multiplicative.toAdd (θ (((π (ε g) : ↥L) : MulAut V) v)))) =
        Multiplicative.ofAdd ((((ε g : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ E (Multiplicative.toAdd (θ v)))
      rw [h1, ← h2, hE, hψ]
      rfl
    left
    have hHU : ∀ h : ↥L, ∀ u ∈ (⊤ : Subgroup V), (h : MulAut V) u ∈ (⊤ : Subgroup V) :=
      fun _ _ _ => Subgroup.mem_top _
    have hHZ : ∀ h : ↥L, ∀ z ∈ (⊥ : Subgroup V), (h : MulAut V) z ∈ (⊥ : Subgroup V) := by
      intro h z hz
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]
    refine ⟨F, inferInstance, inferInstance, hFcard, π, G64.realizesVia_nat_of hπ bot_le hHU hHZ
      (e.toMonoidHom.comp (⊤ : Subgroup V).subtype) ?_ ?_ ?_⟩
    · intro w
      obtain ⟨v, rfl⟩ := e.surjective w
      exact ⟨⟨v, Subgroup.mem_top v⟩, rfl⟩
    · intro u
      rw [Subgroup.mem_bot, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        MulEquiv.map_eq_one_iff]
    · intro γ u hu
      exact he γ u
  ·
    obtain ⟨m, hm, hfm, hK, ψ, hψ, E, hE⟩ := exists_herm_of_row hF ρ bas hirr hS hH hlt (Wj 0) e₀
    let eV : V ≃* HMod m F := θ.trans E
    have heV : ∀ (g : SL(3, F)) (v : V),
        eV (((φ₀ g : ↥L) : MulAut V) v) = rho hK (ψ g) (eV v) := by
      intro g v
      have h1 : θ (((φ₀ g : ↥L) : MulAut V) v) =
          Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (θ v))) := by
        rw [B42SL3.repOf_toAdd]
        rfl
      show E (θ _) = rho hK (ψ g) (E (θ v))
      rw [h1, hE]
      rfl
    let ε := specialLinearGroupEquivStatedSL 3 F
    let π : ↥(StatedSL 3 F) →* ↥L := φ₀.comp (ψ.comp ε.symm.toMonoidHom)
    have hπ : Function.Surjective π := by
      intro l
      obtain ⟨x, rfl⟩ := hcov.surjective l
      exact ⟨ε (ψ x), by simp [π, hψ]⟩
    have hπe : ∀ (γ : ↥(StatedSL 3 F)) (v : V),
        eV (((π γ : ↥L) : MulAut V) v) = rhoT hK (γ : GL (Fin 3) F) (eV v) := by
      intro γ v
      rw [show π γ = φ₀ (ψ (ε.symm γ)) from rfl, heV, hψ]
      show rhoT hK (Matrix.SpecialLinearGroup.toGL (ε.symm γ)) (eV v) = _
      congr 2
      apply Units.ext
      show ((ε.symm γ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
      rw [← specialLinearGroupEquivStatedSL_coe 3 F (ε.symm γ), MulEquiv.apply_symm_apply]
    have hcard2 : Nat.card F = 2 ^ (2 * m) := by rw [hFcard, hfm]
    have hBNT : BinaryNineTensor L ⊤ ⊥ m := by
      refine ⟨F, inferInstance, inferInstance, inferInstance, hcard2, π,
        B42L2.realizesVia_of_secEquiv (FFModel.twistTensor_isActionModel m (StatedSL 3 F) hcard2)
          rfl π hπ eV fun (γ : ↥(StatedSL 3 F)) v => ?_⟩
      refine (congrArg (fun X : HMod m F => (X : Multiplicative (Matrix (Fin 3) (Fin 3) F)))
        (hπe γ v)).trans ?_
      change Multiplicative.ofAdd (H.L3Nine.tw m ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          (mat (eV v))) = Multiplicative.ofAdd (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          mat (eV v) * (CFSG.Quasithin.frobPow m ((γ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F))ᵀ)
      rw [H.L3Nine.frobPow_eq_conjM]
      rfl
    right
    exact ⟨m, hm, hfm, hBNT⟩

end CFSG.Quasithin.H13.L32A.C
