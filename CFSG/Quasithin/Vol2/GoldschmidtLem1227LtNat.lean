module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtSLFam
public import CFSG.Quasithin.Vol2.Ch11SecA15Q
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

namespace Lem1227Lt

section Action

variable {G : Type} [Group G] [Finite G] {T K Y V : Subgroup G}

theorem pCoreOf_le_centralizer_V (h : Hyp1223 G T Y V) :
    pCoreOf 2 Y ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : Y ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    (sup_le Subgroup.le_normalizer h.normalizes).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hle : pCoreOf 2 Y ≤ pCoreOf 2 (Y ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans le_sup_left) hE (LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' := Vol2.Ch11.SecA.reducedAggregate_le_centralizer (Y ⊔ T) (h.irrPlus.1 hv)
  exact (Subgroup.mem_centralizer_iff.1 hv' x (hle hx)).symm

theorem not_le_centralizer_V (h : Hyp1223 G T Y V) :
    ¬ Y ≤ Subgroup.centralizer (V : Set G) := by
  intro hne
  have hVbot : V = ⊥ := by
    have h1 : ⁅V, Y⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.2 hne)
    rw [← h.irrPlus.2.2.2.1, h1]
  exact h.irrPlus.2.1 hVbot

theorem actionOn_eq_one_of_mem_pCore (h : Hyp1223 G T Y V)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) {y : ↥Y} (hy : y ∈ CFSG.pCore 2 ↥Y) :
    A4.actionOn V Y hYV y = 1 := by
  rw [A4.actionOn_eq_one_iff]
  apply pCoreOf_le_centralizer_V h
  exact ⟨y, hy, rfl⟩

theorem ker_actionOn_le_pCore [IsMulCommutative ↥V] (h : Hyp1223 G T Y V)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) {Γ : Type} [Group Γ] [IsSimpleGroup Γ]
    (e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Γ) (y : ↥Y) (hy : A4.actionOn V Y hYV y = 1) :
    y ∈ CFSG.pCore 2 ↥Y := by
  have hker : CFSG.pCore 2 ↥Y ≤ (A4.actionOn V Y hYV).ker := fun k hk =>
    actionOn_eq_one_of_mem_pCore h hYV hk
  have : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  set ρ : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* MulAut ↥V :=
    QuotientGroup.lift (CFSG.pCore 2 ↥Y) (A4.actionOn V Y hYV) hker with hρ
  have : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h0 | h1
  · have hm : (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact hy
    rw [h0, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff y).1 hm
  · exfalso
    apply not_le_centralizer_V h
    intro k hk
    have h2 : (QuotientGroup.mk ⟨k, hk⟩ : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ ρ.ker := by
      rw [h1]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h2
    exact (A4.actionOn_eq_one_iff hYV ⟨k, hk⟩).1 h2

theorem actionOn_conjY (h : LtHyp G T K Y) (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (t : ↥T) (y : ↥Y) :
    A4.actionOn V Y hYV (conjY h t y) =
      A4.actionOn V T hTV t * A4.actionOn V Y hYV y * (A4.actionOn V T hTV t)⁻¹ := by
  rw [← map_inv]
  refine MulEquiv.ext fun w => Subtype.ext ?_
  simp only [MulAut.mul_apply, A4.actionOn_apply_coe, coe_conjY, Subgroup.coe_inv]
  group

theorem hin_of_autOn_top [IsMulCommutative ↥V] (h : LtHyp G T K Y)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (htop : autOn Y V = ⊤)
    (hker : ∀ y : ↥Y, A4.actionOn V Y hYV y = 1 → y ∈ CFSG.pCore 2 ↥Y) {Λ : Type} [Group Λ]
    (φ : ↥Y →* Λ) (hφs : Function.Surjective φ)
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (t : ↥T) (α : MulAut Λ) (hα : ∀ y : ↥Y, α (φ y) = φ (conjY h t y)) :
    ∃ g : Λ, ∀ x : Λ, α x = g * x * g⁻¹ := by
  have hct : A4.actionOn V T hTV t ∈ autOn Y V := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y₀, hy₀⟩ := (A4.mem_autOn_iff hYV).1 hct
  have hkey : ∀ y : ↥Y, φ (conjY h t y) = φ (y₀ * y * y₀⁻¹) := by
    intro y
    have h1 : A4.actionOn V Y hYV ((conjY h t y)⁻¹ * (y₀ * y * y₀⁻¹)) = 1 := by
      rw [map_mul, map_inv, actionOn_conjY h hYV hTV t y, ← hy₀]
      simp only [map_mul, map_inv]
      group
    have h2 := hker _ h1
    have h3 : φ ((conjY h t y)⁻¹ * (y₀ * y * y₀⁻¹)) = 1 :=
      (hk _).2 (by rw [(QuotientGroup.eq_one_iff _).2 h2]; exact Subgroup.one_mem _)
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3
  refine ⟨φ y₀, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hφs x
  rw [hα, hkey, map_mul, map_mul, map_inv]

end Action

section Natural

variable {G : Type} [Group G] [Finite G] {T K Y H M₀ V : Subgroup G}

theorem false_of_natural [IsMulCommutative ↥V]
    (h1223 : Hyp1223 G T Y V) (h : LtHyp G T K Y) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (hfam : B69.E22Fam ↥(E2.star M₀ H K)) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hnat : BinaryNaturalSL (V := ↥V) (autOn Y V) ⊤ ⊥ n 1) : False := by
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := h1223.irrPlus.2.2.1
  have hsimple := sl_isSimple_of_card_two SL.card_zmod_two (by omega : 3 ≤ n)
  have hnonab := sl_nonabelian_of_card_two SL.card_zmod_two (by omega : 3 ≤ n)
  obtain ⟨φ, hφs, hk, hS⟩ := exists_phi_sylow h hnonab
    (SL.isSylowTwoOf_unitriangular (by omega)) e.toMonoidHom e.surjective
  obtain ⟨m, hm, -, Θ, hΘ⟩ := sl_data h hn4 hn5 φ hk hS
  refine false_of_sl_model h hKH hHK hmin hker hq hlist hfam φ hφs hk hm Θ hΘ ?_
  intro t α hα _
  exact hin_of_autOn_top h hYV hTV (G64.BinaryNaturalSL.eq_top hnat)
    (ker_actionOn_le_pCore h1223 hYV e) φ hφs hk t α hα

end Natural

end Lem1227Lt

end CFSG.Quasithin.H13
