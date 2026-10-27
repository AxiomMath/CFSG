module

public import CFSG.Quasithin.EmptyFaithful.S152He10E
public import CFSG.Quasithin.EmptyFaithful.S152He16C

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_quot {H L : Subgroup G} (hL : L ∈ cComp H)
    (hq : CFSG.IsQuasisimple ↥(modO2Image H L)) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := modO2_mulEquiv hL
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

omit [Finite G] in
theorem mem_oTwoZIn_iff {L : Subgroup G} {z : G} :
    z ∈ oTwoZIn L ↔ z ∈ L ∧ ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  unfold oTwoZIn
  rw [mem_preimageModTwoCore]
  constructor
  · rintro ⟨hz, hcen⟩
    refine ⟨hz, fun l hl => ?_⟩
    have := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk ⟨l, hl⟩)
    exact (mk_commute_iff' ⟨z, hz⟩ ⟨l, hl⟩).mp this.symm
  · rintro ⟨hz, h⟩
    refine ⟨hz, Subgroup.mem_center_iff.mpr fun u => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective u
    exact ((mk_commute_iff' ⟨z, hz⟩ l).mpr (h l l.2)).symm

omit [Finite G] in
theorem conj_mem_oTwoZIn {L : Subgroup G} {g z : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hz : z ∈ oTwoZIn L) : g * z * g⁻¹ ∈ oTwoZIn L := by
  obtain ⟨hzL, h⟩ := mem_oTwoZIn_iff.mp hz
  refine mem_oTwoZIn_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzL, fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
    simpa using this
  have h1 := h _ hl'
  have h2 : g * z * g⁻¹ * l * (g * z * g⁻¹)⁻¹ * l⁻¹ =
      g * (z * (g⁻¹ * l * g) * z⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ := by group
  rw [h2]
  exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 L hg) _).mp h1

theorem commutator_le_of_le_O2_oTwoZ {G₀ L R Y : Subgroup G} (hLG : L ≤ G₀) (hsub : IsSubnormal L G₀)
    (hRG : R ≤ G₀) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hY : Y ≤ pCoreOf 2 (L ⊔ R) ⊔ oTwoZIn L) : ⁅Y, L⁆ ≤ pCoreOf 2 G₀ := by
  set O := pCoreOf 2 (L ⊔ R) with hO
  set N := pCoreOf 2 G₀ with hN
  have hLRG : L ⊔ R ≤ G₀ := sup_le hLG hRG
  have hLRN : L ⊔ R ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRL
  have hON : L ⊔ R ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 (L ⊔ R)
  have hOL : O ≤ Subgroup.normalizer (L : Set G) := (pCoreOf_le 2 (L ⊔ R)).trans hLRN
  have hZN : O ≤ Subgroup.normalizer (oTwoZIn L : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact fun hz => conj_mem_oTwoZIn (hOL hg) hz
    · intro hz
      have := conj_mem_oTwoZIn (Subgroup.inv_mem _ (hOL hg)) hz
      simpa [mul_assoc] using this
  have hLO : pCoreOf 2 L ≤ N := A4.pCoreOf_le_of_subnormal 2 hsub
  have hGN : G₀ ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pCoreOf 2 G₀
  rw [Subgroup.commutator_le]
  intro y hy l hl
  have hy' : y ∈ oTwoZIn L ⊔ O := by rw [sup_comm]; exact hY hy
  obtain ⟨z, hz, o, ho, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZN).1 hy'
  have hzL : z ∈ L := (mem_oTwoZIn_iff.mp hz).1
  have h1 : z * l * z⁻¹ * l⁻¹ ∈ pCoreOf 2 L := (mem_oTwoZIn_iff.mp hz).2 l hl
  have h2 : o * l * o⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    have hLN : L ≤ Subgroup.normalizer ((O ⊓ L : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hON (Subgroup.mem_sup_left hg),
        Subgroup.le_normalizer hg⟩
    have hle : O ⊓ L ≤ pCoreOf 2 L :=
      le_pCoreOf_of_le_normalizer inf_le_right hLN ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    refine hle ⟨?_, ?_⟩
    · have : o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) := by group
      rw [this]
      exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hON (Subgroup.mem_sup_left hl)) o⁻¹).mp
        (O.inv_mem ho))
    · have : o * l * o⁻¹ * l⁻¹ = (o * l * o⁻¹) * l⁻¹ := by group
      rw [this]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hOL ho) l).mp hl) (L.inv_mem hl)
  have h3 : z * o * l * (z * o)⁻¹ * l⁻¹ =
      z * (o * l * o⁻¹ * l⁻¹) * z⁻¹ * (z * l * z⁻¹ * l⁻¹) := by group
  rw [commutatorElement_def, h3]
  exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hGN (hLG hzL)) _).mp (hLO h2)) (hLO h1)

theorem exists_five_element (hC27 : ASC27Statement G) {T Mc M H K₁ K₂ : Subgroup G}
    {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G}
    (tail : Tail15204 c Lc) (hYL : yOf152 T Mc M ≤ Lc)
    (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc)) :
    ∃ y ∈ yOf152 T Mc M,
      ∃ hy : y ∈ Subgroup.normalizer
          (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)) : Set G),
        orderOf (conjAct (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) ⟨y, hy⟩) = 5 := by
  by_contra hno
  push Not at hno
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨⟨-, h12, -⟩, -, -⟩ := hC27 (g0Of T Mc M K₁) R (M ⊓ g0Of T Mc M K₁) Lc V tail.hyp tail.comp
    (isQuasisimple_quot tail.comp hq)
    (CFSG.Quasithin.CT.CharTwo.of_normal tail.charTwo hLG tail.normal) tail.not_le hRN rfl
  have hYC : yOf152 T Mc M ≤ (Lc ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := by
    rw [yOf152_eq_oTwoUpper T Mc M]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨hyY, hyodd⟩ := hy
    have hyLR : y ∈ Lc ⊔ R := Subgroup.mem_sup_left (hYL hyY)
    have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
      A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R))
        (le_normalizer_pCoreOf 2 (Lc ⊔ R) hyLR)
    have hy5 : y ^ 5 = 1 := He10.pow_five_of_odd c y hyY hyodd
    have hord : orderOf (conjAct V ⟨y, hyN⟩) ∣ 5 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
      rw [this, map_one]
    rcases (Nat.dvd_prime Nat.prime_five).mp hord with h1 | h5
    · exact ⟨hyLR, A4.conjAct_eq_one_iff.mp (orderOf_eq_one_iff.mp h1)⟩
    · exact absurd h5 (hno y hyY hyN)
  have hcomm : ⁅yOf152 T Mc M, Lc⁆ ≤ pCoreOf 2 (g0Of T Mc M K₁) :=
    commutator_le_of_le_O2_oTwoZ hLG (subnormal_of_mem_cComp tail.comp) hRG hRN (hYC.trans h12)
  exact c.false_of_commutator_le tail.le hLG tail.sylow hcomm

end CFSG.Quasithin.He17
