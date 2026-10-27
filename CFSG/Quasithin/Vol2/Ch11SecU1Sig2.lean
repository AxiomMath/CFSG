module

public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCentPGL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.Sig

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F]

theorem commute_inr_iff (σ : F ≃+* F) (x : PSL2 F) :
    SemidirectProduct.inr σ * incl F x = incl F x * SemidirectProduct.inr σ ↔
      x ∈ fieldCent σ := by
  rw [commute_incl_iff, semilinearAction_inr]
  rfl

theorem exists_mul_ne_of_perfect {X : Type*} [Group X] [Nontrivial X] [hX : Group.IsPerfect X] :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have h1 : commutator X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact h y x
  exact bot_ne_top (h1.symm.trans hX.commutator_eq_top)

theorem sigmaFacts_inr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = p ^ 2) {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    SigmaFacts (pGammaL2PSLRange F) (SemidirectProduct.inr σ) := by
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    simpa using congrArg (fun τ : F ≃+* F => τ z) h1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  have hK₀p : Nat.card K₀ = p := Nat.pow_left_injective two_ne_zero (by
    show Nat.card K₀ ^ 2 = p ^ 2
    rw [← hcard, hF])
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hpodd, by norm_num, hF⟩
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := ⟨p, 1, hp, hpodd, le_rfl, by rw [hK₀p, pow_one]⟩
  have hperf : Group.IsPerfect (PSL2 K₀) := psl2_isPerfect_of_card_gt_three K₀ (by omega)
  have : IsSimpleGroup (PSL2 K₀) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  set v : PGammaL2 F := SemidirectProduct.inr σ with hv
  set ι : PSL2 K₀ →* PGammaL2 F := (incl F).comp (psl2Sub K₀) with hιdef
  have hι : Function.Injective ι := (incl_injective F).comp (psl2Sub_injective K₀)
  set L := pGammaL2PSLRange F with hLdef
  have hLn : L.Normal := pGammaL2PSLRange_normal F hodd (by rw [hF]; nlinarith)
  let e : PSL2 K₀ ≃* ↥ι.range := MonoidHom.ofInjective hι
  have hL₀C : ι.range ≤ Subgroup.centralizer {v} := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((commute_inr_iff σ _).mpr (psl2Sub_mem_fieldCent hK₀ x)).symm
  have hL₀L : ι.range ≤ L := by
    rintro _ ⟨x, rfl⟩
    exact ⟨psl2Sub K₀ x, rfl⟩
  set C₀ := L ⊓ Subgroup.centralizer {v} with hC₀def
  have hC₀ : C₀ = (fieldCent σ).map (incl F) := by
    ext z
    constructor
    · rintro ⟨⟨y, rfl⟩, hz⟩
      exact ⟨y, (commute_inr_iff σ y).mp (Subgroup.mem_centralizer_singleton_iff.mp hz).symm, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        ((commute_inr_iff σ y).mpr hy).symm⟩
  have hC₀card : Nat.card C₀ = 2 * Nat.card ι.range := by
    rw [hC₀, Subgroup.card_map_of_injective (incl_injective F),
      card_fieldCent_eq hK₀ h90 hσσ hcard hodd, pgl2_card_eq_two_mul hK₀odd,
      ← Nat.card_congr e.toEquiv]
  have hL₀C₀ : ι.range ≤ C₀ := le_inf hL₀L hL₀C
  have hperfL₀ : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      hperf.commutator_eq_top]
  have hidx : (ι.range.subgroupOf C₀).index = 2 := by
    have h := (ι.range.subgroupOf C₀).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀C₀).toEquiv, hC₀card] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (mul_comm _ _))
  have hcomm : ⁅C₀, C₀⁆ ≤ ι.range := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h : ⁅(⟨a, ha⟩ : ↥C₀), ⟨b, hb⟩⁆ ∈ ι.range.subgroupOf C₀ := by
      rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
        Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
        inv_mem_iff, inv_mem_iff]
      tauto
    rw [Subgroup.mem_subgroupOf] at h
    simpa [commutatorElement_def] using h
  have hL₀eq : ι.range = ⁅C₀, C₀⁆ := by
    refine le_antisymm ?_ hcomm
    calc ι.range = ⁅ι.range, ι.range⁆ := hperfL₀.symm
      _ ≤ ⁅C₀, C₀⁆ := Subgroup.commutator_mono hL₀C₀ hL₀C₀
  have hmap : ∀ y ∈ Subgroup.centralizer {v}, C₀.map (MulAut.conj y).toMonoidHom ≤ C₀ := by
    rintro y hy _ ⟨z, hz, rfl⟩
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    exact ⟨hLn.conj_mem z hzL y, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hzC) (inv_mem hy)⟩
  have key : ∀ y ∈ Subgroup.centralizer {v}, ∀ x ∈ ι.range, y * x * y⁻¹ ∈ ι.range := by
    intro y hy x hx
    rw [hL₀eq] at hx ⊢
    have h : (⁅C₀, C₀⁆ : Subgroup (PGammaL2 F)).map (MulAut.conj y).toMonoidHom ≤ ⁅C₀, C₀⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (hmap y hy) (hmap y hy)
    exact h ⟨x, hx, rfl⟩
  have hN : Subgroup.centralizer {v} ≤ Subgroup.normalizer (ι.range : Set (PGammaL2 F)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun h => ?_⟩
    simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h
  have hCL : L ⊓ Subgroup.centralizer (ι.range : Set (PGammaL2 F)) = ⊥ := by
    refine le_bot_iff.mp fun z hz => ?_
    obtain ⟨⟨y, rfl⟩, hzC⟩ := Subgroup.mem_inf.mp hz
    have hfix : ∀ g : PSL2 K₀,
        semilinearAction F (incl F y) (psl2Sub K₀ g) = psl2Sub K₀ g := fun g => by
      rw [← commute_incl_iff]
      exact (Subgroup.mem_centralizer_iff.mp hzC (ι g) ⟨g, rfl⟩).symm
    rcases eq_of_fixes_psl2Sub hσ1 hK₀ hcard _ hfix with h | h
    · exact Subgroup.mem_bot.mpr h
    · exfalso
      have h1 := congrArg SemidirectProduct.right h
      rw [incl_apply, SemidirectProduct.right_inl, SemidirectProduct.right_inr] at h1
      exact hσ1 h1.symm
  refine ⟨ι.range, le_inf hL₀L hL₀C, e.symm.isSimpleGroup, ?_, hN, hCL⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_perfect (X := PSL2 K₀)
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

end CFSG.Quasithin.Vol2.Ch11.SecU1.Sig
