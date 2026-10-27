module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] {V : Type} [CommGroup V]

@[expose] def S16C11ActPairs (ρ : G →* MulAut V) (T₁ : Subgroup G) (N : ℕ) :
    Set (V × Subgroup G) :=
  {p | (∀ t ∈ T₁, ρ t p.1 = p.1) ∧ {z : V | ∃ g : G, ρ g p.1 = z}.ncard ≤ N ∧
    T₁ ≤ p.2 ∧ T₁.relIndex p.2 = 3 ∧ ∃ g ∈ p.2, ρ g p.1 ≠ p.1}

@[expose] def S16C11ModelPairs {D : FFModel} (h : D.IsActionModel) (T₁ : Subgroup D.Gam)
    (N : ℕ) : Set (D.Mod × Subgroup D.Gam) :=
  S16C11ActPairs h.modAct T₁ N

private lemma s16c11_case2alt_inf_stabilizer_eq {ρ : G →* MulAut V} {T X : Subgroup G} {y : V}
    (hTX : T ≤ X) (h3 : T.relIndex X = 3) (hfix : ∀ t ∈ T, ρ t y = y)
    (hmov : ∃ g ∈ X, ρ g y ≠ y) :
    X ⊓ (MulAction.stabilizer (MulAut V) y).comap ρ = T := by
  set S : Subgroup G := X ⊓ (MulAction.stabilizer (MulAut V) y).comap ρ with hS
  have hTS : T ≤ S := fun t ht =>
    Subgroup.mem_inf.2 ⟨hTX ht, Subgroup.mem_comap.2 (by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix t ht)⟩
  have hSX : S ≤ X := inf_le_left
  have hne : ¬ X ≤ S := by
    rintro h
    obtain ⟨g, hgX, hgy⟩ := hmov
    exact hgy (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (h hgX)).2)
  have hmul := Subgroup.relIndex_mul_relIndex T S X hTS hSX
  rw [h3] at hmul
  have h1 : S.relIndex X ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.1 h)
  have hd : S.relIndex X ∣ 3 := ⟨T.relIndex S, by rw [← hmul, mul_comm]⟩
  have h2 : S.relIndex X = 3 := ((Nat.dvd_prime Nat.prime_three).1 hd).resolve_left h1
  rw [h2] at hmul
  have h4 : T.relIndex S = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h4) hTS

private lemma s16c11_case2alt_ncard_orbit_eq_relIndex [Finite G] {ρ : G →* MulAut V}
    {T X : Subgroup G} {y : V}
    (hS : X ⊓ (MulAction.stabilizer (MulAut V) y).comap ρ = T) :
    {z : V | ∃ x ∈ X, ρ x y = z}.ncard = T.relIndex X := by
  letI : MulAction G V := MulAction.compHom V ρ
  have hstab : MulAction.stabilizer G y = (MulAction.stabilizer (MulAut V) y).comap ρ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MulAction.compHom_smul_def]
  have horb : {z : V | ∃ x ∈ X, ρ x y = z} = MulAction.orbit ↥X y := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
  rw [horb, ← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf X y, hstab,
    ← Subgroup.inf_subgroupOf_left ((MulAction.stabilizer (MulAut V) y).comap ρ) X, ← hS]
  rfl

private lemma s16c11_case2alt_inv_mul_mem_iff {A : Type*} [CommGroup A] {K : Subgroup A}
    {a b : A} : a⁻¹ * b ∈ K ↔ a * b⁻¹ ∈ K := by
  have h : a * b⁻¹ = (a⁻¹ * b)⁻¹ := by
    rw [mul_inv_rev]
    simp only [inv_inv]
    exact mul_comm a b⁻¹
  rw [h]
  exact K.inv_mem_iff.symm

private lemma s16c11_case2alt_orbit_range (ρ : G →* MulAut V) (y : V) :
    {z : V | ∃ l ∈ ρ.range, l y = z} = {z : V | ∃ g : G, ρ g y = z} := by
  ext z
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hl
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ρ g, MonoidHom.mem_range.2 ⟨g, rfl⟩, rfl⟩

private lemma s16c11_case2alt_modelPairs_ncard {D : FFModel} (hD : D.Faithful)
    (h : D.IsActionModel) {T₁ : Subgroup D.Gam} {N : ℕ} :
    (S16C11ModelPairs h T₁ N).ncard =
      (S16C11Pairs h.modAct.range ⊤ (T₁.map h.modAct) N).ncard := by
  classical
  have hρ : Function.Injective h.modAct := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply hD γ
    intro m hm
    have h1 : h.modAct γ (QuotientGroup.mk (⟨m, hm⟩ : ↥D.sec)) =
        QuotientGroup.mk (⟨m, hm⟩ : ↥D.sec) := by rw [hγ]; rfl
    rw [FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk] at h1
    have h2 : (h.actSec γ ⟨m, hm⟩)⁻¹ * (⟨m, hm⟩ : ↥D.sec) ∈ D.ker.subgroupOf D.sec :=
      QuotientGroup.eq.1 h1
    have h3 : (D.act γ m)⁻¹ * m ∈ D.ker := by
      simpa [FFModel.IsActionModel.actSec] using (Subgroup.mem_subgroupOf.1 h2)
    exact s16c11_case2alt_inv_mul_mem_iff.1 h3
  refine Set.ncard_congr (s := S16C11ModelPairs h T₁ N)
    (t := S16C11Pairs h.modAct.range ⊤ (T₁.map h.modAct) N)
    (fun p _ => (p.1, p.2.map h.modAct)) ?_ ?_ ?_
  · rintro ⟨y, X⟩ hp
    change (y, X) ∈ S16C11ActPairs h.modAct T₁ N at hp
    obtain ⟨hfix, horb, hT, h3, hmov⟩ := hp
    refine ⟨trivial, ?_, ?_, Subgroup.map_le_range _ _, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
      exact hfix s hs
    · rw [s16c11_case2alt_orbit_range]
      exact horb
    · exact Subgroup.map_mono hT
    · rw [Subgroup.relIndex_map_map_of_injective T₁ X hρ, h3]
    · obtain ⟨g, hg, hgy⟩ := hmov
      exact ⟨h.modAct g, Subgroup.mem_map_of_mem _ hg, hgy⟩
  · rintro ⟨y₁, X₁⟩ ⟨y₂, X₂⟩ _ _ heq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 heq
    exact Prod.ext h1 (Subgroup.map_injective hρ h2)
  · rintro ⟨y, X'⟩ hq
    obtain ⟨-, hfix, horb, hX'range, hT, h3, hmov⟩ := hq
    have hmap : (X'.comap h.modAct).map h.modAct = X' := Subgroup.map_comap_eq_self hX'range
    refine ⟨(y, X'.comap h.modAct), ?_, Prod.ext rfl hmap⟩
    change (y, X'.comap h.modAct) ∈ S16C11ActPairs h.modAct T₁ N
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hfix (h.modAct t) (Subgroup.mem_map_of_mem _ ht)
    · rw [← s16c11_case2alt_orbit_range]
      exact horb
    · intro t ht
      exact Subgroup.mem_comap.2 (hT (Subgroup.mem_map_of_mem _ ht))
    · rw [← Subgroup.relIndex_map_map_of_injective T₁ (X'.comap h.modAct) hρ, hmap]
      exact h3
    · obtain ⟨g, hg, hgy⟩ := hmov
      obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.1 (hX'range hg)
      exact ⟨g₀, Subgroup.mem_comap.2 (hg₀ ▸ hg), by rw [hg₀]; exact hgy⟩

theorem s16c11_rf3Odd_of_modelPairs {W : Type} [CommGroup W] {D : FFModel} (hD : D.Faithful)
    (h : D.IsActionModel) {L : Subgroup (MulAut W)} {J : Subgroup W} (hR : D.Realizes L J ⊥)
    {T₁ : Subgroup D.Gam} {N : ℕ} (hT : IsPGroup 2 ↥T₁) (hidx : ¬ 2 ∣ T₁.index)
    (hodd : Odd (S16C11ModelPairs h T₁ N).ncard) : S16C11RF3Odd L J := by
  have hρ : Function.Injective h.modAct := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply hD γ
    intro m hm
    have h1 : h.modAct γ (QuotientGroup.mk (⟨m, hm⟩ : ↥D.sec)) =
        QuotientGroup.mk (⟨m, hm⟩ : ↥D.sec) := by rw [hγ]; rfl
    rw [FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk] at h1
    have h2 : (h.actSec γ ⟨m, hm⟩)⁻¹ * (⟨m, hm⟩ : ↥D.sec) ∈ D.ker.subgroupOf D.sec :=
      QuotientGroup.eq.1 h1
    have h3 : (D.act γ m)⁻¹ * m ∈ D.ker := by
      simpa [FFModel.IsActionModel.actSec] using (Subgroup.mem_subgroupOf.1 h2)
    exact s16c11_case2alt_inv_mul_mem_iff.1 h3
  have hrel : (T₁.map h.modAct).relIndex h.modAct.range = T₁.index := by
    rw [MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective T₁ ⊤ hρ, Subgroup.relIndex_top_right]
  exact s16c11_rf3Odd_of_realizes hD hR h.realizesMod_range
    ⟨N, T₁.map h.modAct, Subgroup.map_le_range _ _, hT.map h.modAct, by rw [hrel]; exact hidx, by
      rw [← s16c11_case2alt_modelPairs_ncard hD h]; exact hodd⟩

@[expose] def S16C11SetStab (ρ : G →* MulAut V) (Y : Set V) : Subgroup G :=
  (MulAction.stabilizer (MulAut V) Y).comap ρ

@[expose] def S16C11Forced (ρ : G →* MulAut V) (T₁ : Subgroup G) (N : ℕ) (y₀ a b : V) : Prop :=
  y₀ ≠ 1 ∧ (∀ t ∈ T₁, ρ t y₀ = y₀) ∧ {z : V | ∃ g : G, ρ g y₀ = z}.ncard ≤ N ∧
    (∀ y : V, y ≠ 1 → (∀ t ∈ T₁, ρ t y = y) → {z : V | ∃ g : G, ρ g y = z}.ncard ≤ N → y = y₀) ∧
    a ≠ b ∧
    (∀ z : V, (∃ g : G, ρ g y₀ = z) → z ≠ y₀ → {w : V | ∃ t ∈ T₁, ρ t z = w}.ncard ≤ 2 →
      z = a ∨ z = b)

@[expose] def S16C11ForcedPairs (ρ : G →* MulAut V) (T₁ : Subgroup G) (y₀ a b : V) :
    Set (V × Subgroup G) :=
  {p | p.1 = y₀ ∧ T₁ ≤ p.2 ∧ p.2 ≤ S16C11SetStab ρ {y₀, a, b} ∧ T₁.relIndex p.2 = 3 ∧
    ∃ g ∈ p.2, ρ g y₀ ≠ y₀}

theorem s16c11_actPairs_eq_forcedPairs [Finite G] {ρ : G →* MulAut V} {T₁ : Subgroup G} {N : ℕ}
    {y₀ a b : V} (hF : S16C11Forced ρ T₁ N y₀ a b) :
    S16C11ActPairs ρ T₁ N = S16C11ForcedPairs ρ T₁ y₀ a b := by
  obtain ⟨hy₀, hfix₀, horb₀, huniq, hab, hz⟩ := hF
  refine Set.Subset.antisymm ?_ ?_
  · rintro ⟨y, X⟩ hp
    obtain ⟨hfixy, horby, hT₁X, h3, hmov⟩ := hp
    have hyne : y ≠ 1 := by
      rintro rfl
      obtain ⟨g, -, hgy⟩ := hmov
      exact hgy (map_one (ρ g))
    have hyy₀ : y = y₀ := huniq y hyne hfixy horby
    rw [hyy₀] at hfixy hmov ⊢
    have hstab : X ⊓ (MulAction.stabilizer (MulAut V) y₀).comap ρ = T₁ :=
      s16c11_case2alt_inf_stabilizer_eq hT₁X h3 hfixy hmov
    set Y : Set V := {z : V | ∃ x ∈ X, ρ x y₀ = z} with hY
    have hYfin : Y.Finite := by
      refine (Set.finite_range (fun g : G => ρ g y₀)).subset ?_
      rintro z ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    have hYcard : Y.ncard = 3 := by
      rw [hY, s16c11_case2alt_ncard_orbit_eq_relIndex hstab, h3]
    have hy₀Y : y₀ ∈ Y := by
      rw [hY]
      exact ⟨1, X.one_mem, by simp⟩
    have hYdiffcard : (Y \ {y₀}).ncard = 2 := by
      rw [Set.ncard_sdiff_singleton_of_mem hy₀Y, hYcard]
    have hYdiffsub : Y \ {y₀} ⊆ {a, b} := by
      rintro z ⟨hzY, hzY0⟩
      rw [hY] at hzY
      obtain ⟨x, hxX, rfl⟩ := hzY
      have hzY0' : ρ x y₀ ≠ y₀ := by simpa using hzY0
      have hzT : {w : V | ∃ t ∈ T₁, ρ t (ρ x y₀) = w}.ncard ≤ 2 := by
        have hsub : {w : V | ∃ t ∈ T₁, ρ t (ρ x y₀) = w} ⊆ Y \ {y₀} := by
          rintro w ⟨t, htT, rfl⟩
          refine ⟨?_, ?_⟩
          · rw [hY]
            exact ⟨t * x, X.mul_mem (hT₁X htT) hxX, by rw [map_mul, MulAut.mul_apply]⟩
          · intro hcon
            simp only [Set.mem_singleton_iff] at hcon
            refine hzY0' ?_
            have h2 : ρ t⁻¹ (ρ t (ρ x y₀)) = ρ x y₀ := by
              rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
            rw [hcon] at h2
            rw [← h2]
            exact hfixy t⁻¹ (T₁.inv_mem htT)
        calc {w : V | ∃ t ∈ T₁, ρ t (ρ x y₀) = w}.ncard
            ≤ (Y \ {y₀}).ncard := Set.ncard_le_ncard hsub (hYfin.subset Set.sdiff_subset)
          _ = 2 := hYdiffcard
      rcases hz (ρ x y₀) ⟨x, rfl⟩ hzY0' hzT with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hYdiff : Y \ {y₀} = {a, b} :=
      Set.eq_of_subset_of_ncard_le hYdiffsub (by rw [Set.ncard_pair hab, hYdiffcard])
    have hYeq : Y = {y₀, a, b} := by
      ext z
      constructor
      · intro hz
        by_cases hz0 : z = y₀
        · subst hz0; exact Set.mem_insert_iff.2 (Or.inl rfl)
        · have hz' : z ∈ Y \ {y₀} := ⟨hz, by simpa using hz0⟩
          rw [hYdiff] at hz'
          rcases hz' with h | h <;> subst h
          · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl)))
          · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inr rfl)))
      · intro hz
        rcases Set.mem_insert_iff.1 hz with rfl | hz
        · exact hy₀Y
        · have hz' : z ∈ Y \ {y₀} := by rw [hYdiff]; exact hz
          exact hz'.1
    refine ⟨rfl, hT₁X, ?_, h3, hmov⟩
    intro x hxX
    rw [S16C11SetStab, Subgroup.mem_comap, MulAction.mem_stabilizer_set]
    intro z
    have hm : ρ x z ∈ Y ↔ z ∈ Y := by
      rw [hY]
      constructor
      · rintro ⟨y, hyX, hyz⟩
        refine ⟨x⁻¹ * y, X.mul_mem (X.inv_mem hxX) hyX, ?_⟩
        calc ρ (x⁻¹ * y) y₀ = ρ x⁻¹ (ρ y y₀) := by rw [map_mul, MulAut.mul_apply]
          _ = ρ x⁻¹ (ρ x z) := by rw [hyz]
          _ = z := by
            rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      · rintro ⟨y, hyX, hyz⟩
        exact ⟨x * y, X.mul_mem hxX hyX, by rw [map_mul, MulAut.mul_apply, hyz]⟩
    rw [hYeq] at hm
    exact hm
  · rintro ⟨y, X⟩ hp
    obtain ⟨hy, hT₁X, hXS, h3, hmov⟩ := hp
    subst hy
    exact ⟨hfix₀, horb₀, hT₁X, h3, hmov⟩

theorem s16c11_forcedPairs_ncard_eq_one {ρ : G →* MulAut V} {T₁ : Subgroup G} {y₀ a b : V}
    (hT : T₁ ≤ S16C11SetStab ρ {y₀, a, b}) (h3 : T₁.relIndex (S16C11SetStab ρ {y₀, a, b}) = 3)
    (hmov : ∃ g ∈ S16C11SetStab ρ {y₀, a, b}, ρ g y₀ ≠ y₀) :
    (S16C11ForcedPairs ρ T₁ y₀ a b).ncard = 1 := by
  have hset : S16C11ForcedPairs ρ T₁ y₀ a b = {(y₀, S16C11SetStab ρ {y₀, a, b})} := by
    ext ⟨y, X⟩
    simp only [S16C11ForcedPairs, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hy, hTX, hXS, hX3, -⟩
      refine ⟨hy, le_antisymm hXS ?_⟩
      have hm := Subgroup.relIndex_mul_relIndex T₁ X _ hTX hXS
      rw [hX3, h3] at hm
      have h1 : X.relIndex (S16C11SetStab ρ {y₀, a, b}) = 1 := by omega
      exact Subgroup.relIndex_eq_one.1 h1
    · rintro ⟨hy, hX⟩
      subst hX
      exact ⟨hy, hT, le_rfl, h3, hmov⟩
  rw [hset, Set.ncard_singleton]

@[expose] noncomputable def S16C11AltAct (n : ℕ) :
    (FFModel.altDn n).Gam →* MulAut (FFModel.altDn n).Mod :=
  (FFModel.altDn_isActionModel n).modAct

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
