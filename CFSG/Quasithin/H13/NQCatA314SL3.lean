module

public import CFSG.Quasithin.H13.NQCatA314SL25
public import CFSG.Quasithin.H13.NQCatA314CentU35

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique Matrix
open CFSG.Adapters.RankTwoModelTransports CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin.H13.NQCat.T513.U35 (PU SU)
open CFSG.Quasithin.H13.KGU35 (f25Data)

theorem eq_perfectCore_of_sl25 {G : Type} [Group G] [Finite G] {L B : Subgroup G} (hBL : B ≤ L)
    (hBp : ⁅B, B⁆ = B) (e : ↥B ≃* SpecialLinearGroup (Fin 2) (ZMod 5))
    (hL : ∀ w : ↥L, orderOf w = 2 →
      Nat.card ↥⁅Subgroup.centralizer ({w} : Set ↥L), Subgroup.centralizer ({w} : Set ↥L)⁆ ≤
        120) :
    B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G)) := by
  obtain ⟨z, hz2, hzO, hBC⟩ := sl25_core e
  have hzB : z ∈ B := by
    obtain ⟨p, -, hp⟩ := hzO
    rw [← hp]
    exact p.2
  have hzL : z ∈ L := hBL hzB
  set X := L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G) with hX
  set Y := L ⊓ Subgroup.centralizer ({z} : Set G) with hY
  have hXY : X ≤ Y :=
    inf_le_inf_left L (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzO))
  have h1 : B ≤ perfectCore X := le_perfectCore_of_perfect (le_inf hBL hBC) hBp
  have h2 : perfectCore X ≤ ⁅Y, Y⁆ :=
    calc perfectCore X ≤ perfectCore Y := perfectCore_mono hXY
      _ = ⁅perfectCore Y, perfectCore Y⁆ := (perfectCore_perfect Y).symm
      _ ≤ ⁅Y, Y⁆ := Subgroup.commutator_mono (perfectCore_le Y) (perfectCore_le Y)
  set w : ↥L := ⟨z, hzL⟩ with hw
  have hw2 : orderOf w = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hYC : Y ≤ (Subgroup.centralizer ({w} : Set ↥L)).map L.subtype := by
    intro g hg
    obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgc
    refine ⟨⟨g, hgL⟩, ?_, rfl⟩
    show (⟨g, hgL⟩ : ↥L) ∈ Subgroup.centralizer ({w} : Set ↥L)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hgc'
  have h3 : Nat.card ↥⁅Y, Y⁆ ≤ 120 := by
    have h4 : ⁅Y, Y⁆ ≤ (⁅Subgroup.centralizer ({w} : Set ↥L),
        Subgroup.centralizer ({w} : Set ↥L)⁆).map L.subtype := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hYC hYC
    calc Nat.card ↥⁅Y, Y⁆ ≤ Nat.card ↥((⁅Subgroup.centralizer ({w} : Set ↥L),
          Subgroup.centralizer ({w} : Set ↥L)⁆).map L.subtype) := Subgroup.card_le_of_le h4
      _ = Nat.card ↥⁅Subgroup.centralizer ({w} : Set ↥L),
            Subgroup.centralizer ({w} : Set ↥L)⁆ :=
          Subgroup.card_map_of_injective L.subtype_injective
      _ ≤ 120 := hL w hw2
  have hcB : Nat.card B = 120 := (Nat.card_congr e.toEquiv).trans card_sl25
  exact Subgroup.eq_of_le_of_card_ge h1 (by
    calc Nat.card ↥(perfectCore X) ≤ Nat.card ↥⁅Y, Y⁆ := Subgroup.card_le_of_le h2
      _ ≤ 120 := h3
      _ = Nat.card B := hcB.symm)

theorem center_sl35 : Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 5)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h3 : ∀ r : ZMod 5, r ^ 3 = 1 → r = 1 := by decide
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, h3 r hr, map_one]
  rfl

theorem cent_of_mulEquiv {X M : Type} [Group X] [Group M] [Finite M] (φ : X ≃* M)
    (hM : ∀ w : M, orderOf w = 2 →
      Nat.card ↥⁅Subgroup.centralizer ({w} : Set M), Subgroup.centralizer ({w} : Set M)⁆ ≤ 120) :
    ∀ w : X, orderOf w = 2 →
      Nat.card ↥⁅Subgroup.centralizer ({w} : Set X), Subgroup.centralizer ({w} : Set X)⁆ ≤ 120 :=
  fun w hw => (card_commutator_centralizer_le_of_injective φ.toMonoidHom φ.injective w).trans
    (hM _ (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hw))

theorem nonempty_ringEquiv_zmod_five (K : Type) [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nonempty (K ≃+* ZMod 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Nat.card_zmod])⟩

theorem nonempty_ringEquiv_f25' (K : Type) [Field K] [Finite K] (hK : Nat.card K = 25) :
    Nonempty (K ≃+* CFSG.RankThree.PartOne.HNB.F25) := by
  have : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.RankThree.PartOne.HNB.F25.card, hK])⟩

theorem cent_sl3five {X : Type} [Group X] (hX : ∃ s : Bool, IsPSLEps3 s 5 1 X ∨ IsSLEps3 s 5 X) :
    ∀ w : X, orderOf w = 2 →
      Nat.card ↥⁅Subgroup.centralizer ({w} : Set X), Subgroup.centralizer ({w} : Set X)⁆ ≤ 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := hX
  cases s
  · rcases hs with hQ | hQ
    ·
      obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
      obtain ⟨φ⟩ := nonempty_ringEquiv_f25' K (by rw [hK]; norm_num)
      let E : X ≃* PU := e₀.trans
        ((statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (5 ^ 1))
          (glCongr_statedScalars φ)).trans (unitaryPSUEquiv f25Data (n := 3) (by norm_num)).symm)
      exact cent_of_mulEquiv E fun w hw => card_commutator_centralizer_pu35 hw
    ·
      obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
      obtain ⟨φ⟩ := nonempty_ringEquiv_f25' K (by rw [hK]; norm_num)
      let E : X ≃* ↥SU := e₀.trans
        (((glCongr (ι := Fin 3) φ).subgroupMap (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K)).trans
          (MulEquiv.subgroupCongr (glCongr_statedSU φ 3 5)))
      exact cent_of_mulEquiv E fun w hw => card_commutator_centralizer_su35 hw
  · rcases hs with hQ | hQ
    ·
      obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
      obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_five K (by rw [hK, pow_one])
      let e₂ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5) ≃*
          SpecialLinearGroup (Fin 3) (ZMod 5) :=
        (QuotientGroup.quotientMulEquivOfEq center_sl35).trans QuotientGroup.quotientBot
      let E : X ≃* SpecialLinearGroup (Fin 3) (ZMod 5) := e₀.trans
        ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
          ((projectiveSpecialLinearGroupCongr (Fin 3) σ).trans e₂))
      exact cent_of_mulEquiv E fun w hw => card_commutator_centralizer_sl35 hw
    ·
      obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
      obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_five K hK
      let E : X ≃* SpecialLinearGroup (Fin 3) (ZMod 5) := e₀.trans
        ((specialLinearGroupEquivStatedSL 3 K).symm.trans (specialLinearGroupCongr (Fin 3) σ))
      exact cent_of_mulEquiv E fun w hw => card_commutator_centralizer_sl35 hw

theorem desc_sl3five (G : Type) [Group G] [Finite G] (L T B : Subgroup G)
    (_hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (_hne : B ≠ L)
    (hL : ∃ s : Bool, IsPSLEps3 s 5 1 ↥L ∨ IsSLEps3 s 5 ↥L) (hB2 : IsSL2 5 ↥B) :
    B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G)) := by
  obtain ⟨e⟩ := hB2
  exact eq_perfectCore_of_sl25 hBL (perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)) e
    (cent_sl3five hL)

end CFSG.Quasithin.H13.NQCat.A314D
