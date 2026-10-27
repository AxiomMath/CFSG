module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def L1LocalAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r →
      ∃ B : Basis3 G (r.n + 1), Adapted B b₀ K E ∧ LocalData r B b₀

theorem l1Local_of_rows (h6 : L1LocalAt Row.D6) (h7 : L1LocalAt Row.twD7)
    (hE : L1LocalAt Row.E7) : L1Local := by
  intro G _ _ b₀ K E r hstd
  cases r with
  | D6 => exact h6 G b₀ K E hstd
  | twD7 => exact h7 G b₀ K E hstd
  | E7 => exact hE G b₀ K E hstd

@[expose] def L2ConstructYAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → RecOut r B b₀ →
      ∃ Y : Subgroup G, IsEm r.m Y ∧
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K ∧
        ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)

@[expose] def L2ConstructYGenAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → RecOut r B b₀ →
      ∃ Y : Subgroup G, IsEm r.m Y ∧
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K ∧
        (∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)) ∧
        Y ≤ K ⊔ Subgroup.normalizer (E : Set G)

theorem l2ConstructYAt_of_gen {r : Row} (h : L2ConstructYGenAt r) : L2ConstructYAt r := by
  intro G _ _ b₀ K E hstd B hB hrec
  obtain ⟨Y, h1, h2, h3, -⟩ := h G b₀ K E hstd B hB hrec
  exact ⟨Y, h1, h2, h3⟩

theorem iSup_le_sup_normalizer_of_frame {G : Type} [Group G] {ι : Type} {U : ι → Subgroup G}
    {K N : Subgroup G} {g : G} (hUK : ∀ k, U k ≤ K ∨ U k ≤ K.map (MulAut.conj g).toMonoidHom)
    (hg : g ∈ K ⊔ N) : ⨆ k, U k ≤ K ⊔ N := by
  refine iSup_le fun k => (hUK k).elim (fun h => h.trans le_sup_left) (fun h => h.trans ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (Subgroup.mem_sup_left hx))
    (Subgroup.inv_mem _ hg)

theorem l2ConstructY_of_rows (h6 : L2ConstructYAt Row.D6) (h7 : L2ConstructYAt Row.twD7)
    (hE : L2ConstructYAt Row.E7) : L2ConstructY := by
  intro G _ _ b₀ K E r hstd B hB hrec
  cases r with
  | D6 => exact h6 G b₀ K E hstd B hB hrec
  | twD7 => exact h7 G b₀ K E hstd B hB hrec
  | E7 => exact hE G b₀ K E hstd B hB hrec

@[expose] def L3RootFusionAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → IsCharTwoType G →
      ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → RecOut r B b₀ → Fus42 B b₀ →
      ∀ Y : Subgroup G, IsEm r.m Y →
        Subgroup.centralizer ({b₀} : Set G) ⊓ Y = Subgroup.zpowers b₀ ⊔ K →
        (∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) →
          (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
          R ≤ Subgroup.centralizer (Y : Set G)) →
        ∃ (S : Subgroup G) (t : G), IsSylow2In S Y ∧ t ∈ S ∧ orderOf t = 2 ∧
          (∀ s ∈ S, s * t = t * s) ∧ ∀ g : G, g * t * g⁻¹ ∈ Y → g ∈ Y

theorem l3RootFusion_of_rows (h6 : L3RootFusionAt Row.D6) (h7 : L3RootFusionAt Row.twD7)
    (hE : L3RootFusionAt Row.E7) : L3RootFusion := by
  intro G _ _ b₀ K E r hstd hchar B hB hrec hfus Y hYm hCY hRY
  cases r with
  | D6 => exact h6 G b₀ K E hstd hchar B hB hrec hfus Y hYm hCY hRY
  | twD7 => exact h7 G b₀ K E hstd hchar B hB hrec hfus Y hYm hCY hRY
  | E7 => exact hE G b₀ K E hstd hchar B hB hrec hfus Y hYm hCY hRY

end CFSG.StandardType.FrameRoute.FS81
