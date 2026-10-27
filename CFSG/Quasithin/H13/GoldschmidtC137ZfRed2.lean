module

public import CFSG.Quasithin.H13.GoldschmidtC137ZfRed1
public import CFSG.Quasithin.H13.GoldschmidtC137ZfStmt
public import CFSG.Quasithin.EmptyFaithful.S1422Center

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem zf_card_sup_eq_of_le {A D Z : Subgroup G} (hAD : A ≤ centralizer (D : Set G))
    (hZ : A ⊓ D = Z) (hA : Nat.card A = 4 * Nat.card Z) :
    Nat.card ↥(A ⊔ D) = 4 * Nat.card D := by
  have h := card_sup_mul_card_inf_of_le_centralizer hAD
  rw [hZ, hA] at h
  have hpos : 0 < Nat.card ↥Z := Nat.card_pos
  have : Nat.card ↥(A ⊔ D) * Nat.card ↥Z = 4 * Nat.card ↥D * Nat.card ↥Z := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem zf_line_of_U {X L V P : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ normalizer (V : Set G)) (hn : X ≤ normalizer (L : Set G)) (hPX : P ≤ X)
    (hUV : ⁅V, L⁆ ≤ V)
    (h : ∃ l : Subgroup G, ⁅V, L⁆ ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ ⁅V, L⁆ ∧
      Nat.card ↥l = 4 * Nat.card ↥(⁅V, L⁆ ⊓ centralizer (L : Set G)) ∧
        P ≤ normalizer (l : Set G)) :
    ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ V ∧
      Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧ P ≤ normalizer (l : Set G) := by
  obtain ⟨l, hZl, hlU, hl4, hPl⟩ := h
  refine ⟨l ⊔ (V ⊓ centralizer (L : Set G)), le_sup_right, sup_le (hlU.trans hUV) inf_le_left,
    ?_, ?_⟩
  · refine zf_card_sup_eq_of_le (Z := ⁅V, L⁆ ⊓ centralizer (L : Set G)) ?_ ?_ hl4
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (B2F.isElemAbelian_comm hV (hUV (hlU ha)) hd.1).symm
    · refine le_antisymm (fun x hx => ⟨hlU hx.1, hx.2.2⟩) ?_
      intro x hx
      exact ⟨hZl hx, ⟨hUV hx.1, hx.2⟩⟩
  · intro g hg
    have hlE := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPl hg)
    have hVE := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXN (hPX hg))
    have hCE := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (B2F.normalizer_le_normalizer_centralizer L (hn (hPX hg)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, hlE,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hVE, hCE]

theorem zf_card_autOn_eq {X A V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : IsElemAbelian 2 U)
    (hXN : X ≤ normalizer (V : Set G)) (hXU : X ≤ normalizer (U : Set G)) (hAX : A ≤ X)
    (hCeq : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G)) :
    Nat.card ↥(autOn A U) = Nat.card ↥(autOn A V) := by
  have hAC : A ⊓ centralizer (U : Set G) = A ⊓ centralizer (V : Set G) := by
    have h1 : ∀ C : Subgroup G, A ⊓ C = A ⊓ (X ⊓ C) := fun C => by
      rw [← inf_assoc, inf_eq_left.2 hAX]
    rw [h1 (centralizer (U : Set G)), hCeq, ← h1]
  have h1 := card_autI_mul_card_inf hU (hAX.trans hXU)
  have h2 := card_autI_mul_card_inf hV (hAX.trans hXN)
  rw [hAC] at h1
  have hpos : 0 < Nat.card ↥(A ⊓ centralizer (V : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem zf_concl_of_U {X T V L P : Subgroup G} (hred : IsTwoReducedIn X V)
    (hT : IsSylowTwoOf T X) (hn : X ≤ normalizer (L : Set G)) (hPX : P ≤ X)
    (hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G))
    (hUe : IsElemAbelian 2 ⁅V, L⁆) (hUV : ⁅V, L⁆ ≤ V)
    (hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G)) (h : Concl X T ⁅V, L⁆ L P) :
    Concl X T V L P := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  rcases h with h | h | ⟨hc, hl⟩ | ⟨htype, hl, hhat, A, hA, hcard⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, zf_line_of_U hV hXN hn hPX hUV hl⟩))
    rw [← zf_card_autOn_eq hV hUe hXN hXU le_rfl hCeq]
    exact hc
  · refine Or.inr (Or.inr (Or.inr ⟨htype, zf_line_of_U hV hXN hn hPX hUV hl, hhat, A, hA, ?_⟩))
    rw [← zf_card_autOn_eq hV hUe hXN hXU (hA.1.trans hT.1) hCeq]
    exact hcard

theorem c137CaseS6Z_of_M
    (Mdl : ∀ {G : Type} [Group G] [Finite G] (U : Subgroup G), Subgroup G →
      IsElemAbelian 2 U → Prop)
    (hM : ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
      CharTwo X → SQTKGroup ↥X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
      L ∈ cComp X → CharTwo L →
      (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) →
      ¬ autOn T V ≤ autOn L V → T ≤ P → P ≤ M → M < X →
      (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
      (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
      ∀ hred : IsTwoReducedIn X V, ⁅V, L⁆ ≠ ⊥ → Mdl V L hred.2.2.1 → Concl X T V L P)
    (hmodZ : ∀ {G : Type} [Group G] [Finite G] {V L U : Subgroup G}, IsElemAbelian 2 V →
      ∀ hU : IsElemAbelian 2 U, L ≤ normalizer (V : Set G) → L ≤ normalizer (U : Set G) →
      ⁅V, L⁆ = U → ⁅U, L⁆ = U →
      (∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
        ((centralizer (L : Set G)).subgroupOf V) 6) → Mdl U L hU) :
    C137CaseS6Z := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 htype hnin hnat hTP hPM hMX hmax hPeq hred hVL
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hXN : X ≤ normalizer (V : Set G) := hred.2.1
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans hXN
  have hPX : P ≤ X := hPM.trans hMX.le
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  obtain ⟨hredU, hUU, hCeq⟩ := zf_reduce hred hT hprod hL htype hVL hnat
  have hninU : ¬ autOn T ⁅V, L⁆ ≤ autOn L ⁅V, L⁆ :=
    zf_not_autOn_le_of_centralizer_eq hXN hredU.2.1 hT.1 hLX hCeq hnin
  have hUL : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by rw [hUU]; exact hVL
  have hmod : Mdl ⁅V, L⁆ L hredU.2.2.1 :=
    hmodZ hred.2.2.1 hredU.2.2.1 hLN (hLX.trans hredU.2.1) rfl hUU hnat
  exact zf_concl_of_U hred hT hn hPX hCeq hredU.2.2.1 hUV hredU.2.1
    (hM G X T ⁅V, L⁆ L P M hX hSQ hT hprod hL hL2 htype hninU hTP hPM hMX hmax hPeq hredU hUL
      hmod)

end CFSG.Quasithin.H13.U3.GC137
