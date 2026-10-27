module

public import CFSG.Quasithin.H13.L32AC49c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActual

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lin

abbrev SLn (n : ℕ) : Type := SpecialLinearGroup (Fin n) (ZMod 2)

theorem three_le_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL n 2 1 X) : 3 ≤ n := by
  obtain ⟨⟨-, -, h2, h22, -⟩, -⟩ := h
  by_contra hn
  apply h22
  have : n = 2 := by omega
  subst this
  rfl

theorem nonempty_mulEquiv_sl_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL n 2 1 X) :
    Nonempty (X ≃* SLn n) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  have hunits : ∀ c : Kˣ, c = 1 := fun c => by
    have h1 : Units.map ε.toMonoidHom c = 1 := Subsingleton.elim _ _
    exact (Units.map_injective ε.injective) (by simpa using h1)
  exact ⟨e.trans ((CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL n K).trans
    ((slEquivProjectiveSL_two hunits n).symm.trans (slMulEquivOfRingEquiv ε n)))⟩

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem center_eq_bot (n : ℕ) : Subgroup.center (SLn n) = ⊥ := by
  rw [← scalars_eq_center]
  exact CFSG.QuasithinUnique.Setup.Family.scalars_zmod_two n

theorem conj_injective (n : ℕ) : Function.Injective (MulAut.conj : SLn n →* MulAut (SLn n)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← center_eq_bot n, Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun α : MulAut (SLn n) => α x) (MonoidHom.mem_ker.mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * g = g * x * g⁻¹ * g := by rw [this]
    _ = g * x := by group

theorem upper_eq_uni (n : ℕ) : upperTriangular n (ZMod 2) = unitriangular n (ZMod 2) :=
  le_antisymm (CFSG.QuasithinUnique.Vol2Native.A312L.upperTriangular_le_unitriangular
    card_zmod_two) (unitriangular_le_upperTriangular n _)

theorem uni_sylow {n : ℕ} (hn : 1 ≤ n) :
    IsPGroup 2 ↥(unitriangular n (ZMod 2)) ∧ ¬ 2 ∣ (unitriangular n (ZMod 2)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) hn
  refine ⟨?_, ?_⟩
  · have := P.isPGroup'
    rwa [hP] at this
  · have := P.not_dvd_index
    rwa [hP] at this

theorem eq_uni_of_le {n : ℕ} (hn : 1 ≤ n) {Q : Subgroup (SLn n)} (hQ : IsPGroup 2 Q)
    (hUQ : unitriangular n (ZMod 2) ≤ Q) : Q = unitriangular n (ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) hn
  rw [← hP] at hUQ ⊢
  exact P.3 hQ hUQ

end Lin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_pi_sln {K : Subgroup G} {n : ℕ} (hP : IsPSL n 2 1 (cStar K)) (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hTsylH : IsSylowTwoOf T H) :
    ∃ π : ↥K →* Lin.SLn n, Function.Surjective π ∧
      (∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K) ∧
      (T.subgroupOf K).map π = unitriangular n (ZMod 2) := by
  have hn := Lin.three_le_of_isPSL hP
  obtain ⟨φ⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
  set π₀ : ↥K →* Lin.SLn n := φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hTsyl : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTsylH hKH hKn
  have hS2 : IsPGroup 2 (T.subgroupOf K) :=
    hTsylH.2.1.comap_of_injective K.subtype K.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf K).index := Subgroup.inf_subgroupOf_right T K ▸ hTsyl.2.2
  obtain ⟨hU2, hUi⟩ := Lin.uni_sylow (n := n) (by omega)
  obtain ⟨h, hhD⟩ := exists_conj_map_eq_of_sylow π₀ hπ₀ hS2 hSi hU2 hUi
  refine ⟨(MulAut.conj h⁻¹).toMonoidHom.comp π₀, (MulAut.conj h⁻¹).surjective.comp hπ₀,
    fun k => ?_, by rw [← hhD, Subgroup.map_map]⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]

end CFSG.Quasithin.H13.L32A.C
