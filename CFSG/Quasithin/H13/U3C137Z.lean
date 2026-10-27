module

public import CFSG.Quasithin.H13.U3C137Five
public import CFSG.Quasithin.Background.B5FinPerm

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def C137StatementFiveZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T V L P M : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → (∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) →
    L ∈ cComp X → CharTwo L →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨ autOn T V ≤ autOn L V ∨
      ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
        ((centralizer (L : Set G)).subgroupOf V) 6) →
    T ≤ P → P ≤ M → M < X → (∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) →
    (P = M ∨ (A6.IsHatA6 L ∧ P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ A6.o2Z L)) →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ →
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      Nat.card ↥⁅V, L⁆ = 8 ∧ ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ centralizer ({u} : Set G)) →
    CharNormal (baum (pCoreOf 2 P)) X ∨
      ((LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsLnBlock L 3) ∧
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) → H13.IsA6Block L) ∧
        (A6.IsHatA6 L → H13.IsHatA6Block L) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → H13.IsG2Block L)) ∨
      (Nat.card ↥(autOn X V) = 12096 ∧ ∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧
        l ≤ V ∧ Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
        P ≤ normalizer (l : Set G)) ∨
      ((Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 L) ∧
        (∃ l : Subgroup G, V ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ V ∧
          Nat.card ↥l = 4 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
          P ≤ normalizer (l : Set G)) ∧
        (A6.IsHatA6 L → ¬ oTwoUpper (A6.o2Z L) ≤ P) ∧
        ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V))

@[expose] def FixModOmega (σ : Perm (Fin 6)) (m : G6.PermMod 6) : Prop :=
  m⁻¹ * G6.permAct 6 σ m = 1 ∨ m⁻¹ * G6.permAct 6 σ m = G6.allOnes 6

instance (σ : Perm (Fin 6)) : DecidablePred (FixModOmega σ) := fun m => by
  unfold FixModOmega; infer_instance

theorem d6_fixed_trivial : ∀ m : G6.PermMod 6, ∑ i, Multiplicative.toAdd m i = 0 →
    FixModOmega (swap 0 1 * swap 1 2) m → FixModOmega (swap 1 2 * swap 2 3) m →
    FixModOmega (swap 2 3 * swap 3 4) m → FixModOmega (swap 3 4 * swap 4 5) m →
    m = 1 ∨ m = G6.allOnes 6 := by
  decide +kernel

theorem centralizer_subgroupOf_eq_bot_of_natural {G : Type} [Group G] {L V : Subgroup G}
    [IsMulCommutative ↥V] (h : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) :
    (centralizer (L : Set G)).subgroupOf V = ⊥ := by
  obtain ⟨π, -, -, -, -, -, -, -, β, -, hβ1, hβeq⟩ := h
  rw [eq_bot_iff]
  intro v hv
  rw [mem_subgroupOf] at hv
  have hfix : ∀ a ∈ autOn L V, (a : MulAut ↥V) v = v := by
    rintro a ⟨g, hg, rfl⟩
    apply Subtype.ext
    have hgL : (g : G) ∈ L := hg
    have happ : ((conjAct V g v : ↥V) : G) = g * v * (g : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v
    rw [happ, mem_centralizer_iff.mp hv (g : G) hgL, mul_inv_cancel_right]
  set u : ↥(⊤ : Subgroup ↥V) := ⟨v, mem_top v⟩ with hu
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hgen : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) →
      FixModOmega σ (show G6.PermMod 6 from m.1) := by
    intro σ hσ
    have hπ : ((π ⟨σ, hσ⟩ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V) = u := hfix _ (π _).2
    have hm' : (FFModel.altDn 6).act ⟨σ, hσ⟩ m.1 ∈ (FFModel.altDn 6).sec :=
      G6.permAct_mem_coreMod σ m.2
    have h1 := hβeq ⟨σ, hσ⟩ u m (by rw [hπ]; exact mem_top _) hm' hm.symm
    have h2 : (⟨((π ⟨σ, hσ⟩ : ↥(autOn L V)) : MulAut ↥V) (u : ↥V), by rw [hπ]; exact mem_top _⟩ :
        ↥(⊤ : Subgroup ↥V)) = u := Subtype.ext hπ
    rw [h2, ← hm] at h1
    have h3 := QuotientGroup.eq.1 h1
    rw [mem_subgroupOf] at h3
    have h4 : (show G6.PermMod 6 from (m⁻¹ * ⟨_, hm'⟩ : ↥(FFModel.altDn 6).sec).1) ∈
        Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 := h3
    exact B5FinPerm.mem_zpowers_allOnes_iff.1 (mem_inf.1 h4).1
  have hm1 := d6_fixed_trivial (show G6.PermMod 6 from m.1) (G6.mem_coreMod.1 m.2)
    (hgen _ (Perm.mem_alternatingGroup.2 (by decide)))
    (hgen _ (Perm.mem_alternatingGroup.2 (by decide)))
    (hgen _ (Perm.mem_alternatingGroup.2 (by decide)))
    (hgen _ (Perm.mem_alternatingGroup.2 (by decide)))
  have hβu : β u = 1 := by
    rw [← hm, QuotientGroup.eq_one_iff, mem_subgroupOf]
    show (show G6.PermMod 6 from m.1) ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6
    exact mem_inf.2 ⟨B5FinPerm.mem_zpowers_allOnes_iff.2 hm1, m.2⟩
  have := (hβ1 u).1 hβu
  rw [mem_bot] at this
  rw [mem_bot]
  exact this

theorem c137StatementFive_of_Z (h : C137StatementFiveZ) : C137StatementFive := by
  intro G _ _ X T V L P M hX hT hXLT hL hL2 htype hdyn hTP hPM hMX hmax hPeq hred hVL hL32
  refine h G X T V L P M hX hT hXLT hL hL2 htype ?_ hTP hPM hMX hmax hPeq hred hVL hL32
  rcases hdyn with h1 | h2 | ⟨hab, h6⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨hab, ?_⟩)
    rw [centralizer_subgroupOf_eq_bot_of_natural h6]
    exact h6

end CFSG.Quasithin.H13.U3
