module

public import CFSG.Quasithin.EmptyFaithful.S151TCQ
public import CFSG.Quasithin.EmptyFaithful.S151TBDef

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S151TB
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_top_of_isPGroup_quotient_of_perfect [Finite G] {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (N : Subgroup ↥L) [N.Normal] (hN : IsPGroup 2 (↥L ⧸ N)) : N = ⊤ := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  by_contra hne
  have : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  have : Group.IsNilpotent (↥L ⧸ N) := hN.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N) ‹_›

theorem conj_eq_of_card_two {Z : Subgroup G} (hZ : Nat.card ↥Z = 2) {g : G}
    (hg : g ∈ Subgroup.normalizer (Z : Set G)) {z : G} (hz : z ∈ Z) : g * z * g⁻¹ = z := by
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).1 hZ
    have h1 : (⟨z, hz⟩ : ↥Z) = y := hy _ (fun h => hz1 (congrArg Subtype.val h))
    have hgz : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hg z).1 hz
    have hne : g * z * g⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
    have h2 : (⟨g * z * g⁻¹, hgz⟩ : ↥Z) = y := hy _ (fun h => hne (congrArg Subtype.val h))
    exact congrArg Subtype.val (h2.trans h1.symm)

theorem sq_eq_one_of_card_two {Z : Subgroup G} (hZ : Nat.card ↥Z = 2) {z : G} (hz : z ∈ Z) :
    z ^ 2 = 1 := by
  have h := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
  rw [hZ] at h
  exact congrArg Subtype.val h

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hA x) (hB x)

theorem blockU_le_omegaOneCenterOf [Finite G] {L R : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hVL : ⁅omegaOneCenterOf (pCoreOf 2 (L ⊔ R)), L⁆ ≠ ⊥)
    (hcard : Nat.card ↥(c134CQ (L ⊔ R) L) = 2)
    (hirr : ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L →
      L ≤ Subgroup.normalizer (W : Set G) → W = blockZ L ∨ W = blockU L) :
    blockU L ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ R)) := by
  set G₀ : Subgroup G := L ⊔ R
  have hG₀N : G₀ ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRN
  have hLG₀ : L ≤ G₀ := le_sup_left
  set P : Subgroup G := pCoreOf 2 G₀
  have hPN : G₀ ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 G₀
  have hPG₀ : P ≤ G₀ := pCoreOf_le 2 G₀
  set V : Subgroup G := omegaOneCenterOf P
  have hVP : V ≤ P := A4.omegaOneCenterOf_le P
  have hVN : G₀ ≤ Subgroup.normalizer (V : Set G) :=
    hPN.trans (A4.normalizer_le_normalizer_omegaOneCenterOf P)
  have hQ : c134Q G₀ L = blockU L := c134Q_eq_blockU hperf hRN
  have hU : blockU L = ⁅P, L⁆ := hQ.symm
  have hZ : c134CQ G₀ L = blockZ L := by
    unfold c134CQ blockZ
    rw [hQ]
  have hcardZ : Nat.card ↥(blockZ L) = 2 := hZ ▸ hcard
  have hUN : G₀ ≤ Subgroup.normalizer (blockU L : Set G) := fun x hx => by
    rw [hU]
    exact normalizer_commutator (hPN hx) (hG₀N hx)
  have hUP : blockU L ≤ P := by
    rw [hU, Subgroup.commutator_le]
    intro x hx l hl
    have h1 : l * x⁻¹ * l⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 (hPN (hLG₀ hl)) x⁻¹).1 (P.inv_mem hx)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem hx h1
  have hZN : G₀ ≤ Subgroup.normalizer (blockZ L : Set G) := fun x hx =>
    mem_normalizer_inf (hUN hx) (s151v_mem_normalizer_centralizer (hG₀N hx))
  have hZV : blockZ L ≤ V := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact mul_inv_eq_iff_eq_mul.1 (conj_eq_of_card_two hcardZ (hZN (hPG₀ hh)) hz)
    exact Subgroup.subset_closure ⟨⟨hUP hz.1, hzC⟩, sq_eq_one_of_card_two hcardZ hz⟩
  have hV₀V : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hVN (hLG₀ hl)) v⁻¹).1 (V.inv_mem hv)
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem hv h1
  have hV₀U : ⁅V, L⁆ ≤ blockU L := by
    rw [hU]
    exact Subgroup.commutator_mono hVP le_rfl
  have hLV₀ : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hVN (hLG₀ hx)) (Subgroup.le_normalizer hx)
  have hLW : L ≤ Subgroup.normalizer ((⁅V, L⁆ ⊔ blockZ L : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hLV₀ hx, hZN (hLG₀ hx)⟩
  have hZU : blockZ L ≤ blockU L := inf_le_left
  rcases hirr (⁅V, L⁆ ⊔ blockZ L) le_sup_right (sup_le hV₀U hZU) hLW with hW | hW
  ·
    exfalso
    have hVC : ⁅V, L⁆ ≤ Subgroup.centralizer (L : Set G) :=
      (le_sup_left.trans hW.le).trans inf_le_right
    have h1 : ⁅⁅V, L⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hVC
    have h2 : ⁅⁅L, V⁆, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm L V]
    have h3 : ⁅⁅L, L⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    rw [hperf, Subgroup.commutator_comm] at h3
    exact hVL h3
  · intro x hx
    exact sup_le hV₀V hZV (hW ▸ hx)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.S151TB in
theorem isShort2_of_case5 {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hchar : CharTwo L) (hq : CFSG.IsQuasisimple (LStar L))
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hVL : ⁅omegaOneCenterOf (pCoreOf 2 (L ⊔ R)), L⁆ ≠ ⊥)
    (h5 : ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧
      Nat.card ↥(c134CQ (L ⊔ R) L) = 2 ∧
      IsSumOfNaturalModulesVia L (c134Q (L ⊔ R) L) (c134CQ (L ⊔ R) L) α false 1)
    (hlt : blockZ L < blockU L)
    (hirr : ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L →
      L ≤ Subgroup.normalizer (W : Set G) → W = blockZ L ∨ W = blockU L) :
    IsShort2 L := by
  obtain ⟨-, -, hcard, -⟩ := h5
  have hUV := blockU_le_omegaOneCenterOf hperf hRN hVL hcard hirr
  have hG₀N : L ⊔ R ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRN
  have hOP : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ R) := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (fun x hx => ?_) (pCoreOf_isPGroup 2 L)
    exact normalizer_le_normalizer_pCoreOf 2 L (hG₀N hx)
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) := le_normalizer_pCoreOf 2 L
  refine ⟨eq_top_of_isPGroup_quotient_of_perfect hperf, hchar, ⟨?_, ?_⟩, Or.inl hq, hlt, hirr⟩
  · refine le_inf ?_ ?_
    ·
      rw [blockU, Subgroup.commutator_le]
      intro x hx l hl
      have h1 : l * x⁻¹ * l⁻¹ ∈ blockQ L :=
        (Subgroup.mem_normalizer_iff.1 (hLQ hl) x⁻¹).1 ((blockQ L).inv_mem hx)
      have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (blockQ L).mul_mem hx h1
    ·
      exact (hUV.trans ((A4.omegaOneCenterOf_le_centerOf _).trans
        (A4.centerOf_le_centralizer _))).trans (Subgroup.centralizer_le hOP)
  · exact fun x hx => A4.sq_eq_one_of_mem_omegaOneCenterOf (hUV hx)

end CFSG.Quasithin.S151TC
