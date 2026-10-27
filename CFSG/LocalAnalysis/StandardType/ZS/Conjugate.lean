module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.HardMathSupport.Kantor79.CommutatorSpace
public import CFSG.Quasithin.Background.SimsG4Defs
public import CFSG.Quasithin.Background.SimsG4OrthUPrim
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U]

private def NInv (N : Subgroup (U ≃ₗ[K] U)) (W : Submodule K U) : Prop :=
  ∀ n ∈ N, ∀ w ∈ W, n w ∈ W

private def NSimple (N : Subgroup (U ≃ₗ[K] U)) (W : Submodule K U) : Prop :=
  W ≠ ⊥ ∧ NInv N W ∧ ∀ W' : Submodule K U, W' ≤ W → NInv N W' → W' = ⊥ ∨ W' = W

private theorem le_ker_or_le {N : Subgroup (U ≃ₗ[K] U)} {r : U ≃ₗ[K] U}
    (hr : r ∈ N) {W : Submodule K U} (hW : NInv N W)
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1) :
    W ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1) ∨
      HardMathSupport.Kantor79.movedSpace r ≤ W := by
  by_cases h : ∀ w ∈ W, w ∈ LinearMap.ker ((r : U →ₗ[K] U) - 1)
  · exact Or.inl fun w hw => h w hw
  · right
    push Not at h
    obtain ⟨w, hw, hw'⟩ := h
    have hmem : r w - w ∈ W := by
      have := hW r hr w hw
      simpa using W.sub_mem this hw
    have hM : HardMathSupport.Kantor79.movedSpace r = Submodule.span K ({r w - w} : Set U) := by
      have hx : r w - w ∈ HardMathSupport.Kantor79.movedSpace r := ⟨w, rfl⟩
      exact eq_span_singleton_of_mem_of_finrank_eq_one hr1 hx (by simpa using hw')
    rw [hM]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem)

private theorem movedSpace_conj (g r : U ≃ₗ[K] U) :
    HardMathSupport.Kantor79.movedSpace (g * r * g⁻¹) =
      (HardMathSupport.Kantor79.movedSpace r).map (g : U →ₗ[K] U) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨r (g⁻¹ x) - g⁻¹ x, ⟨g⁻¹ x, rfl⟩, by simp [mul_assoc]⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨g x, by simp [mul_assoc]⟩

private theorem mem_ker_conj (g r : U ≃ₗ[K] U) (x : U) :
    g x ∈ LinearMap.ker (((g * r * g⁻¹ : U ≃ₗ[K] U) : U →ₗ[K] U) - 1) ↔
      x ∈ LinearMap.ker ((r : U →ₗ[K] U) - 1) := by
  simp only [LinearMap.mem_ker, LinearMap.sub_apply]
  constructor
  · intro h
    have h' : g ((r : U →ₗ[K] U) x - x) = g 0 := by
      simpa [map_sub, LinearEquiv.mul_apply] using h
    exact g.injective h'
  · intro h
    simpa [map_sub, LinearEquiv.mul_apply] using congrArg g h

private theorem map_simple {G N : Subgroup (U ≃ₗ[K] U)}
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    {X : Submodule K U} (hX : NSimple N X) {g : U ≃ₗ[K] U} (hg : g ∈ G) :
    NSimple N (X.map (g : U →ₗ[K] U)) := by
  obtain ⟨hX0, hXinv, hXmin⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hX0
    have := congrArg (Submodule.map (g.symm : U →ₗ[K] U)) h
    simpa [Submodule.map_bot, ← Submodule.map_comp, LinearEquiv.mul_apply] using this
  · intro n hn v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    have hgn : g⁻¹ * n * g ∈ N := by
      have := hN g⁻¹ (G.inv_mem hg) n hn
      simpa [mul_assoc] using this
    refine ⟨(g⁻¹ * n * g) x, hXinv _ hgn x hx, ?_⟩
    simp only [LinearEquiv.mul_apply]
    simp
  · intro W' hW' hW'inv
    have hW'g : NInv N (W'.map (g.symm : U →ₗ[K] U)) := by
      intro n hn w hw
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
      have hgn : g * n * g⁻¹ ∈ N := hN g hg n hn
      refine ⟨(g * n * g⁻¹) u, hW'inv _ hgn u hu, ?_⟩
      simp only [LinearEquiv.mul_apply]
      simp
    have hle : W'.map (g.symm : U →ₗ[K] U) ≤ X := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp (hW' hu)
      simpa using hy
    rcases hXmin _ hle hW'g with h | h
    · left
      have := congrArg (Submodule.map (g : U →ₗ[K] U)) h
      simpa [Submodule.map_bot, ← Submodule.map_comp, LinearEquiv.mul_apply] using this
    · right
      have := congrArg (Submodule.map (g : U →ₗ[K] U)) h
      simpa [← Submodule.map_comp, LinearEquiv.mul_apply] using this

private theorem NInv_sSup {N : Subgroup (U ≃ₗ[K] U)} {S : Set (Submodule K U)}
    (hS : ∀ Y ∈ S, NInv N Y) : NInv N (sSup S) := by
  intro n hn w hw
  have hle : sSup S ≤ (sSup S).comap (n : U →ₗ[K] U) := by
    refine sSup_le fun Y hY => ?_
    intro v hv
    exact le_sSup hY (hS Y hY n hn v hv)
  exact hle hw

private theorem NInv_inf {N : Subgroup (U ≃ₗ[K] U)} {W W' : Submodule K U}
    (hW : NInv N W) (hW' : NInv N W') : NInv N (W ⊓ W') :=
  fun n hn w hw => ⟨hW n hn w hw.1, hW' n hn w hw.2⟩

private theorem exists_simple [FiniteDimensional K U] (N : Subgroup (U ≃ₗ[K] U))
    (hU : Nontrivial U) : ∃ X : Submodule K U, NSimple N X := by
  classical
  let P : ℕ → Prop := fun k => ∃ X : Submodule K U, X ≠ ⊥ ∧ NInv N X ∧ Module.finrank K X = k
  have hP : ∃ k, P k := by
    refine ⟨Module.finrank K U, ⊤, ?_, fun _ _ _ _ => Submodule.mem_top, by simp⟩
    intro h
    have hsub : Subsingleton U := by
      refine ⟨fun x y => ?_⟩
      have hx : x ∈ (⊤ : Submodule K U) := Submodule.mem_top
      rw [h] at hx
      have hx0 : x = 0 := by simpa using hx
      have hy : y ∈ (⊤ : Submodule K U) := Submodule.mem_top
      rw [h] at hy
      have hy0 : y = 0 := by simpa using hy
      rw [hx0, hy0]
    obtain ⟨x, y, hxy⟩ := hU.exists_pair_ne
    exact hxy (hsub.elim x y)
  obtain ⟨X, hX0, hXinv, hXdim⟩ := Nat.find_spec hP
  refine ⟨X, hX0, hXinv, ?_⟩
  intro W' hW'le hW'inv
  by_cases hW'0 : W' = ⊥
  · exact Or.inl hW'0
  · right
    by_contra hW'ne
    have hlt : Module.finrank K W' < Nat.find hP := by
      rw [← hXdim]
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hW'le hW'ne)
    have hP' : P (Module.finrank K W') := ⟨W', hW'0, hW'inv, rfl⟩
    exact absurd (Nat.find_min' hP hP') (not_le.mpr hlt)

private theorem movedSpace_one_ne_bot {r : U ≃ₗ[K] U}
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1) :
    HardMathSupport.Kantor79.movedSpace r ≠ ⊥ := by
  intro h
  rw [h] at hr1
  simp at hr1

private theorem eq_of_le {N : Subgroup (U ≃ₗ[K] U)} {r : U ≃ₗ[K] U}
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1)
    {Z Z' : Submodule K U} (hZ : NSimple N Z) (hZ' : NSimple N Z')
    (hMZ : HardMathSupport.Kantor79.movedSpace r ≤ Z)
    (hMZ' : HardMathSupport.Kantor79.movedSpace r ≤ Z') : Z = Z' := by
  have hinf : Z ⊓ Z' ≠ ⊥ := by
    intro h
    have : HardMathSupport.Kantor79.movedSpace r ≤ Z ⊓ Z' := le_inf hMZ hMZ'
    rw [h] at this
    exact movedSpace_one_ne_bot hr1 (le_bot_iff.mp this)
  have hinv := NInv_inf hZ.2.1 hZ'.2.1
  have h1 : Z ⊓ Z' = Z := by
    rcases hZ.2.2 (Z ⊓ Z') inf_le_left hinv with h | h
    · exact absurd h hinf
    · exact h
  have h2 : Z ⊓ Z' = Z' := by
    rcases hZ'.2.2 (Z ⊓ Z') inf_le_right hinv with h | h
    · exact absurd h hinf
    · exact h
  exact h1.symm.trans h2

private theorem exists_Z_iSup_eq_top [FiniteDimensional K U] {G N : Subgroup (U ≃ₗ[K] U)}
    (hirr : ∀ W : Submodule K U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {X : Submodule K U} (hX : NSimple N X) :
    (⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)) = ⊤ := by
  have hSinv : NInv G (⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)) := by
    intro h hh w hw
    have hmap : (⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)).map (h : U →ₗ[K] U) ≤
        ⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U) := by
      rw [Submodule.map_iSup]
      refine iSup_le fun g => ?_
      rw [← Submodule.map_comp]
      refine le_iSup_of_le (⟨h * (g : U ≃ₗ[K] U), G.mul_mem hh g.2⟩ : G) ?_
      rfl
    exact hmap ⟨w, hw, rfl⟩
  rcases hirr _ hSinv with h | h
  · exfalso
    have h1 : (1 : U ≃ₗ[K] U) ∈ G := G.one_mem
    have hXle : X ≤ ⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U) := by
      have := le_iSup (fun g : G => X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)) (⟨1, h1⟩ : G)
      simpa using this
    rw [h] at hXle
    exact hX.1 (le_bot_iff.mp hXle)
  · exact h

private theorem exists_Z_not_all {G : Subgroup (U ≃ₗ[K] U)} {X : Submodule K U}
    {r : U ≃ₗ[K] U} (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1)
    (hStop : (⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)) = ⊤) :
    ¬ (∀ g ∈ G, X.map (g : U →ₗ[K] U) ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1)) := by
  intro hall
  have hker : (⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)) ≤
      LinearMap.ker ((r : U →ₗ[K] U) - 1) := by
    refine iSup_le fun g => hall (g : U ≃ₗ[K] U) g.2
  have htop : LinearMap.ker ((r : U →ₗ[K] U) - 1) = ⊤ := by
    rw [hStop] at hker
    exact top_le_iff.mp hker
  have hr1eq : r = 1 := by
    ext v
    have : v ∈ LinearMap.ker ((r : U →ₗ[K] U) - 1) := by rw [htop]; trivial
    exact sub_eq_zero.mp (by simpa [LinearMap.mem_ker] using this)
  have hbot : HardMathSupport.Kantor79.movedSpace r = ⊥ := by
    rw [hr1eq]
    show LinearMap.range ((1 : U →ₗ[K] U) - 1) = ⊥
    rw [sub_self]
    exact LinearMap.range_zero
  exact movedSpace_one_ne_bot hr1 hbot

private theorem exists_Z [FiniteDimensional K U] {G N : Subgroup (U ≃ₗ[K] U)}
    (hirr : ∀ W : Submodule K U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    {r : U ≃ₗ[K] U} (hr : r ∈ N)
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1)
    {X : Submodule K U} (hX : NSimple N X) :
    ∃ g₀ ∈ G, NSimple N (X.map (g₀ : U →ₗ[K] U)) ∧
      ¬ X.map (g₀ : U →ₗ[K] U) ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1) ∧
      HardMathSupport.Kantor79.movedSpace r ≤ X.map (g₀ : U →ₗ[K] U) := by
  let S : Submodule K U := ⨆ g : G, X.map ((g : U ≃ₗ[K] U) : U →ₗ[K] U)
  have hStop : S = ⊤ := exists_Z_iSup_eq_top hirr hX
  have hnotall : ¬ (∀ g ∈ G, X.map (g : U →ₗ[K] U) ≤
      LinearMap.ker ((r : U →ₗ[K] U) - 1)) := exists_Z_not_all hr1 hStop
  push Not at hnotall
  obtain ⟨g₀, hg₀, hg₀ker⟩ := hnotall
  have hZ : NSimple N (X.map (g₀ : U →ₗ[K] U)) := map_simple hN hX hg₀
  refine ⟨g₀, hg₀, hZ, hg₀ker, ?_⟩
  rcases le_ker_or_le hr hZ.2.1 hr1 with h | h
  · exact absurd h hg₀ker
  · exact h

private theorem sSupIndep_translates_Yker {r : U ≃ₗ[K] U} {Z : Submodule K U}
    (hZker : ¬ Z ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1)) (g : U ≃ₗ[K] U) :
    ¬ Z.map (g : U →ₗ[K] U) ≤
      LinearMap.ker ((((g * r * g⁻¹) : U ≃ₗ[K] U) : U →ₗ[K] U) - 1) := by
  intro h
  apply hZker
  intro z hz
  have hgz : g z ∈ Z.map (g : U →ₗ[K] U) := ⟨z, hz, rfl⟩
  have hzg : g z ∈ LinearMap.ker ((((g * r * g⁻¹) : U ≃ₗ[K] U) : U →ₗ[K] U) - 1) := h hgz
  exact (mem_ker_conj g r z).mp hzg

private theorem sSupIndep_translates_other [FiniteDimensional K U]
    {G N : Subgroup (U ≃ₗ[K] U)}
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {r : U ≃ₗ[K] U} (hr : r ∈ N)
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1)
    {Z : Submodule K U} (hZ : NSimple N Z)
    (hZker : ¬ Z ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1) ∧
      HardMathSupport.Kantor79.movedSpace r ≤ Z)
    {g : U ≃ₗ[K] U} (hg : g ∈ G) :
    ∀ Y' ∈ {Y : Submodule K U | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)} \
      {Z.map (g : U →ₗ[K] U)},
      Y' ≤ LinearMap.ker ((((g * r * g⁻¹) : U ≃ₗ[K] U) : U →ₗ[K] U) - 1) := by
  set rg : U ≃ₗ[K] U := g * r * g⁻¹ with hrg
  have hrgN : rg ∈ N := by
    have := hN g hg r hr
    simpa [hrg, mul_assoc] using this
  have hrg1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace rg) = 1 := by
    rw [hrg, movedSpace_conj, LinearEquiv.finrank_map_eq]
    exact hr1
  have hMle : HardMathSupport.Kantor79.movedSpace rg ≤ Z.map (g : U →ₗ[K] U) := by
    rw [hrg, movedSpace_conj]
    exact Submodule.map_mono hZker.2
  intro Y' hY'
  rw [Set.mem_diff, Set.mem_singleton_iff] at hY'
  obtain ⟨⟨g', hg', rfl⟩, hne⟩ := hY'
  have hYsimple : NSimple N (Z.map (g : U →ₗ[K] U)) := map_simple hN hZ hg
  have hY'simple : NSimple N (Z.map (g' : U →ₗ[K] U)) := map_simple hN hZ hg'
  rcases le_ker_or_le hrgN hY'simple.2.1 hrg1 with h | h
  · exact h
  · exact absurd (eq_of_le hrg1 hY'simple hYsimple h hMle) hne

private theorem sSupIndep_translates [FiniteDimensional K U] {G N : Subgroup (U ≃ₗ[K] U)}
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    {r : U ≃ₗ[K] U} (hr : r ∈ N)
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1)
    {Z : Submodule K U} (hZ : NSimple N Z)
    (hZker : ¬ Z ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1) ∧
      HardMathSupport.Kantor79.movedSpace r ≤ Z) :
    sSupIndep {Y : Submodule K U | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)} := by
  intro Y hY
  rw [disjoint_iff]
  obtain ⟨g, hg, rfl⟩ := hY
  have hYsimple : NSimple N (Z.map (g : U →ₗ[K] U)) := map_simple hN hZ hg
  have hYker := sSupIndep_translates_Yker hZker.1 g
  have hsup := sSup_le (sSupIndep_translates_other hN hr hr1 hZ hZker hg)
  by_contra hne
  have hinf_inv : NInv N (Z.map (g : U →ₗ[K] U) ⊓
      sSup ({Y : Submodule K U | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)} \
        {Z.map (g : U →ₗ[K] U)})) :=
    NInv_inf hYsimple.2.1 (NInv_sSup fun Y hY' => by
      rw [Set.mem_diff] at hY'
      obtain ⟨⟨g'', hg'', rfl⟩, _⟩ := hY'
      exact (map_simple hN hZ hg'').2.1)
  rcases hYsimple.2.2 _ inf_le_left hinf_inv with h | h
  · exact hne h
  · apply hYker
    rw [← h]
    exact inf_le_right.trans hsup

private theorem sSup_translates_eq_top [FiniteDimensional K U] {G : Subgroup (U ≃ₗ[K] U)}
    (hirr : ∀ W : Submodule K U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {Z : Submodule K U} (hZne : Z ≠ ⊥) :
    sSup {Y : Submodule K U | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)} = ⊤ := by
  let S : Set (Submodule K U) := {Y | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)}
  have hSinv : NInv G (sSup S) := by
    intro h hh v hv
    have hle : sSup S ≤ (sSup S).comap (h : U →ₗ[K] U) := by
      refine sSup_le fun Y hY => ?_
      intro v hv
      obtain ⟨g, hg, hYeq⟩ := hY
      rw [hYeq] at hv
      have hv' : h v ∈ (Z.map (g : U →ₗ[K] U)).map (h : U →ₗ[K] U) := ⟨v, hv, rfl⟩
      exact le_sSup (show (Z.map (g : U →ₗ[K] U)).map (h : U →ₗ[K] U) ∈ S from by
        rw [← Submodule.map_comp]
        exact ⟨h * g, G.mul_mem hh hg, rfl⟩) hv'
    exact hle hv
  rcases hirr (sSup S) hSinv with h | h
  · exfalso
    have hZS : Z ∈ S := ⟨1, G.one_mem, by simp⟩
    have : Z ≤ sSup S := le_sSup hZS
    rw [h] at this
    exact hZne (le_bot_iff.mp this)
  · exact h

private theorem finite_translates [FiniteDimensional K U] {G N : Subgroup (U ≃ₗ[K] U)}
    {Z : Submodule K U} (hZsimple : NSimple N Z)
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hSind : sSupIndep {Y : Submodule K U | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)}) :
    Finite {Y : Submodule K U | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)} := by
  let S : Set (Submodule K U) := {Y | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)}
  have hSne : ∀ Y : S, (Y : Submodule K U) ≠ ⊥ := by
    intro Y
    obtain ⟨g, hg, hYeq⟩ := Y.2
    rw [hYeq]
    exact (map_simple hN hZsimple hg).1
  have : Finite S := by
    have hfin : Fintype {Y : S // (Y : Submodule K U) ≠ ⊥} :=
      iSupIndep.fintypeNeBotOfFiniteDimensional (p := fun Y : S => (Y : Submodule K U))
        ((sSupIndep_iff S).mp hSind)
    exact Finite.of_injective (fun Y : S =>
        (⟨Y, hSne Y⟩ : {Y : S // (Y : Submodule K U) ≠ ⊥}))
      (by intro a b hab; exact Subtype.mk.inj hab)
  exact this

private theorem isImprimitive_of_two_translates [FiniteDimensional K U]
    {G : Subgroup (U ≃ₗ[K] U)} {Z : Submodule K U}
    {S : Set (Submodule K U)} (hS : S = {Y | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)})
    [Finite S] (hcard : 1 < Nat.card S)
    (hSind : sSupIndep S) (hSsup : sSup S = ⊤)
    (hSne : ∀ Y : S, (Y : Submodule K U) ≠ ⊥) :
    Quasithin.SimsG4.IsImprimitiveOnV G := by
  refine Quasithin.SimsG4.isImprimitiveOnV_of_family hcard
    (fun Y : S => (Y : Submodule K U)) (fun Y => hSne Y)
    ((sSupIndep_iff S).mp hSind) ?_ ?_
  · exact (sSup_eq_iSup' S).symm.trans hSsup
  · intro h hh Y
    have hY2 : (Y : Submodule K U) ∈ {Y | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)} := by
      rw [← hS]
      exact Y.2
    obtain ⟨g, hg, hYeq⟩ := hY2
    rw [hYeq, hS]
    refine ⟨⟨(Z.map (g : U →ₗ[K] U)).map (h : U →ₗ[K] U), by
      rw [← Submodule.map_comp]
      exact ⟨h * g, G.mul_mem hh hg, rfl⟩⟩, rfl⟩

private theorem subsingleton_translates_eq_top {Z : Submodule K U} {S : Set (Submodule K U)}
    [Finite S] (hcard : ¬ 1 < Nat.card S) (hSsup : sSup S = ⊤) (hZmem : Z ∈ S) :
    Z = ⊤ := by
  have hsub : S.Subsingleton := by
    intro a ha b hb
    by_contra hab
    have h2 : 2 ≤ Nat.card S := by
      have hinj : Function.Injective (fun i : Fin 2 =>
          if i = 0 then (⟨a, ha⟩ : S) else ⟨b, hb⟩) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      have hle := Nat.card_le_card_of_injective (fun i : Fin 2 =>
        if i = 0 then (⟨a, ha⟩ : S) else ⟨b, hb⟩) hinj
      simpa using hle
    omega
  have hSeq : S = {Z} := by
    rw [Set.eq_singleton_iff_unique_mem]
    exact ⟨hZmem, fun Y hY => hsub hY hZmem⟩
  have : sSup S ≤ Z := by
    refine sSup_le fun Y hY => ?_
    rw [hSeq, Set.mem_singleton_iff] at hY
    rw [hY]
  rw [hSsup] at this
  exact top_le_iff.mp this

theorem irreducible_of_normal_of_finrank_movedSpace_eq_one [FiniteDimensional K U]
    {G N : Subgroup (U ≃ₗ[K] U)}
    (hirr : ∀ W : Submodule K U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    {r : U ≃ₗ[K] U} (hr : r ∈ N)
    (hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1) :
    ∀ W : Submodule K U, (∀ n ∈ N, ∀ w ∈ W, n w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  intro W hW
  have hU : Nontrivial U := by
    by_contra h
    have hsub : Subsingleton U := by
      refine ⟨fun x y => ?_⟩
      by_contra hxy
      exact h ⟨x, y, hxy⟩
    have hbot : HardMathSupport.Kantor79.movedSpace r = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v _
      exact hsub.elim v 0
    exact movedSpace_one_ne_bot hr1 hbot
  obtain ⟨X, hX⟩ := exists_simple N hU
  obtain ⟨g₀, hg₀, hZsimple, hZker, hMZ⟩ := exists_Z hirr hN hr hr1 hX
  let Z : Submodule K U := X.map (g₀ : U →ₗ[K] U)
  have hZsimple' : NSimple N Z := hZsimple
  have hZker' : ¬ Z ≤ LinearMap.ker ((r : U →ₗ[K] U) - 1) := hZker
  have hMZ' : HardMathSupport.Kantor79.movedSpace r ≤ Z := hMZ
  let S : Set (Submodule K U) := {Y | ∃ g ∈ G, Y = Z.map (g : U →ₗ[K] U)}
  have hSind : sSupIndep S := sSupIndep_translates hN hr hr1 hZsimple' ⟨hZker', hMZ'⟩
  have hSsup : sSup S = ⊤ := sSup_translates_eq_top hirr hZsimple'.1
  have hSne : ∀ Y : S, (Y : Submodule K U) ≠ ⊥ := by
    intro Y
    obtain ⟨g, hg, hYeq⟩ := Y.2
    rw [hYeq]
    exact (map_simple hN hZsimple' hg).1
  have hfin : Finite S := finite_translates hZsimple' hN hSind
  by_cases hcard : 1 < Nat.card S
  · exfalso
    exact hprim (isImprimitive_of_two_translates rfl hcard hSind hSsup hSne)
  · have hZmem : Z ∈ S := ⟨1, G.one_mem, by simp⟩
    have hZtop : Z = ⊤ := subsingleton_translates_eq_top hcard hSsup hZmem
    rcases hZsimple'.2.2 W (hZtop ▸ le_top) hW with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hZtop)

private theorem map_eq_of_maps [FiniteDimensional K U] {σ : U ≃ₗ[K] U} {W : Submodule K U}
    (h : ∀ w ∈ W, σ w ∈ W) : W.map (σ : U →ₗ[K] U) = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  · rw [LinearEquiv.finrank_map_eq]

private theorem inv_maps_of_maps [FiniteDimensional K U] {σ : U ≃ₗ[K] U} {W : Submodule K U}
    (h : ∀ w ∈ W, σ w ∈ W) : ∀ w ∈ W, σ⁻¹ w ∈ W := by
  have hmap := map_eq_of_maps h
  intro w hw
  have hmem : σ (σ⁻¹ w) ∈ W := by simpa using hw
  rw [← hmap] at hmem
  obtain ⟨y, hy, hgy⟩ := hmem
  simpa [σ.injective hgy] using hy

private def PresSub [FiniteDimensional K U] (W : Submodule K U) : Subgroup (U ≃ₗ[K] U) where
  carrier := {σ | ∀ w ∈ W, σ w ∈ W}
  one_mem' := by intro w hw; simpa using hw
  mul_mem' := by
    intro σ τ hσ hτ w hw
    simpa [mul_apply] using hσ (τ w) (hτ w hw)
  inv_mem' := by intro σ hσ; exact inv_maps_of_maps hσ

private theorem S₁_nonempty [FiniteDimensional K U] {G : Subgroup (U ≃ₗ[K] U)}
    {L : Set (U ≃ₗ[K] U)} {W₁ : Submodule K U} {S₁ : Set (U ≃ₗ[K] U)}
    (hG : G = Subgroup.closure L)
    (hirr : ∀ W : Submodule K U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₁ : W₁ ≠ ⊥) (h₁' : W₁ ≠ ⊤)
    (hS₁ : S₁ = {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G,
      σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁}) :
    S₁.Nonempty := by
  by_contra hemp
  push Not at hemp
  have hLpres : L ⊆ PresSub W₁ := by
    intro l hl w hw
    by_contra hw'
    have hl₁ : l ∈ S₁ := by
      rw [hS₁]
      exact ⟨l, hl, 1, G.one_mem, by simp, w, hw, hw'⟩
    rw [hemp] at hl₁
    exact hl₁
  have hGpres : G ≤ PresSub W₁ := by
    rw [hG]
    exact (Subgroup.closure_le _).mpr hLpres
  rcases hirr W₁ (fun g hg w hw => hGpres hg w hw) with h | h
  · exact h₁ h
  · exact h₁' h

private theorem closure_maps_W₂ [FiniteDimensional K U] {G : Subgroup (U ≃ₗ[K] U)}
    {L : Set (U ≃ₗ[K] U)}
    {W₁ W₂ : Submodule K U}
    (hcon : ∀ l ∈ L, ∀ g ∈ G, (∃ w ∈ W₁, (g * l * g⁻¹) w ∉ W₁) →
      ∀ w₂ ∈ W₂, (g * l * g⁻¹) w₂ ∈ W₂) :
    Subgroup.closure {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G,
      σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁} ≤ PresSub W₂ := by
  rw [Subgroup.closure_le]
  rintro σ ⟨l, hl, g, hg, rfl, w, hw, hw'⟩ w₂ hw₂
  exact hcon l hl g hg ⟨w, hw, hw'⟩ w₂ hw₂

private theorem conj_iff_mem_W₁ [FiniteDimensional K U] {σ : U ≃ₗ[K] U} {W₁ : Submodule K U}
    (hσW₁ : ∀ w ∈ W₁, σ w ∈ W₁) : ∀ v, σ v ∈ W₁ ↔ v ∈ W₁ := by
  intro v
  constructor
  · intro hv
    have := inv_maps_of_maps hσW₁ (σ v) hv
    simpa using this
  · intro hv
    rw [← map_eq_of_maps hσW₁]
    exact ⟨v, hv, rfl⟩

private theorem conjS₁_mem [FiniteDimensional K U] {G : Subgroup (U ≃ₗ[K] U)}
    {L : Set (U ≃ₗ[K] U)} {W₁ : Submodule K U}
    (hG : G = Subgroup.closure L) :
    ∀ σ ∈ {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G, σ = g * l * g⁻¹},
      σ ∉ {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G,
        σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁} →
      ∀ τ ∈ {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G,
        σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁},
      σ * τ * σ⁻¹ ∈ {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G,
        σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁} ∧
      σ⁻¹ * τ * σ ∈ {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G,
        σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁} := by
  let S : Set (U ≃ₗ[K] U) := {σ | ∃ l ∈ L, ∃ g ∈ G, σ = g * l * g⁻¹}
  let S₁ : Set (U ≃ₗ[K] U) :=
    {σ | ∃ l ∈ L, ∃ g ∈ G, σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁}
  intro σ hσ hσ₁ τ hτ
  obtain ⟨l, hl, g, hg, rfl⟩ := hσ
  have hσG : g * l * g⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem hg (hG ▸ Subgroup.subset_closure hl)) (G.inv_mem hg)
  have hσW₁ : ∀ w ∈ W₁, (g * l * g⁻¹) w ∈ W₁ := by
    intro w hw
    by_contra hw'
    exact hσ₁ ⟨l, hl, g, hg, rfl, w, hw, hw'⟩
  have hiff := conj_iff_mem_W₁ hσW₁
  obtain ⟨l', hl', g', hg', rfl, w, hw, hw'⟩ := hτ
  constructor
  · refine ⟨l', hl', (g * l * g⁻¹) * g', G.mul_mem hσG hg', by group,
      (g * l * g⁻¹) w, hσW₁ w hw, ?_⟩
    have heq : ((g * l * g⁻¹) * (g' * l' * g'⁻¹) * (g * l * g⁻¹)⁻¹) ((g * l * g⁻¹) w)
        = (g * l * g⁻¹) ((g' * l' * g'⁻¹) w) := by simp [mul_assoc]
    rw [heq]
    intro hmem
    exact hw' ((hiff _).mp hmem)
  · refine ⟨l', hl', (g * l * g⁻¹)⁻¹ * g', G.mul_mem (G.inv_mem hσG) hg', by group,
      (g * l * g⁻¹)⁻¹ w, inv_maps_of_maps hσW₁ w hw, ?_⟩
    have heq : ((g * l * g⁻¹)⁻¹ * (g' * l' * g'⁻¹) * (g * l * g⁻¹))
        ((g * l * g⁻¹)⁻¹ w) = (g * l * g⁻¹)⁻¹ ((g' * l' * g'⁻¹) w) := by simp [mul_assoc]
    rw [heq]
    intro hmem
    exact hw' (by
      have h1 := hσW₁ ((g * l * g⁻¹)⁻¹ ((g' * l' * g'⁻¹) w)) hmem
      have h2 : (g * l * g⁻¹) ((g * l * g⁻¹)⁻¹ ((g' * l' * g'⁻¹) w))
          = (g' * l' * g'⁻¹) w := by simp [mul_assoc]
      rwa [h2] at h1)

private theorem normalizer_conjS₁ {S S₁ : Set (U ≃ₗ[K] U)}
    (hconjS₁ : ∀ σ ∈ S, σ ∉ S₁ → ∀ τ ∈ S₁, σ * τ * σ⁻¹ ∈ S₁ ∧ σ⁻¹ * τ * σ ∈ S₁) :
    ∀ σ ∈ S, (∀ n ∈ Subgroup.closure S₁, σ * n * σ⁻¹ ∈ Subgroup.closure S₁) ∧
      (∀ n ∈ Subgroup.closure S₁, σ⁻¹ * n * σ ∈ Subgroup.closure S₁) := by
  let N : Subgroup (U ≃ₗ[K] U) := Subgroup.closure S₁
  intro σ hσ
  have key : ∀ τ ∈ S₁, σ * τ * σ⁻¹ ∈ N ∧ σ⁻¹ * τ * σ ∈ N := by
    intro τ hτ
    by_cases hσ₁ : σ ∈ S₁
    · exact ⟨N.mul_mem (N.mul_mem (Subgroup.subset_closure hσ₁) (Subgroup.subset_closure hτ))
          (N.inv_mem (Subgroup.subset_closure hσ₁)),
        N.mul_mem (N.mul_mem (N.inv_mem (Subgroup.subset_closure hσ₁))
          (Subgroup.subset_closure hτ)) (Subgroup.subset_closure hσ₁)⟩
    · exact ⟨Subgroup.subset_closure (hconjS₁ σ hσ hσ₁ τ hτ).1,
        Subgroup.subset_closure (hconjS₁ σ hσ hσ₁ τ hτ).2⟩
  constructor
  · intro n hn
    let K : Subgroup (U ≃ₗ[K] U) :=
      { carrier := {m | σ * m * σ⁻¹ ∈ N}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          show σ * (x * y) * σ⁻¹ ∈ N
          convert N.mul_mem hx hy using 1
          group
        inv_mem' := by
          intro x hx
          show σ * x⁻¹ * σ⁻¹ ∈ N
          convert N.inv_mem hx using 1
          group }
    exact ((Subgroup.closure_le K).mpr (fun τ hτ => (key τ hτ).1)) hn
  · intro n hn
    let K : Subgroup (U ≃ₗ[K] U) :=
      { carrier := {m | σ⁻¹ * m * σ ∈ N}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          show σ⁻¹ * (x * y) * σ ∈ N
          convert N.mul_mem hx hy using 1
          group
        inv_mem' := by
          intro x hx
          show σ⁻¹ * x⁻¹ * σ ∈ N
          convert N.inv_mem hx using 1
          group }
    exact ((Subgroup.closure_le K).mpr (fun τ hτ => (key τ hτ).2)) hn

private theorem normalizer_closure_S₁ {G : Subgroup (U ≃ₗ[K] U)} {L : Set (U ≃ₗ[K] U)}
    {S S₁ : Set (U ≃ₗ[K] U)} (hG : G = Subgroup.closure L)
    (hS : S = {σ : U ≃ₗ[K] U | ∃ l ∈ L, ∃ g ∈ G, σ = g * l * g⁻¹})
    (hconjN : ∀ σ ∈ S, (∀ n ∈ Subgroup.closure S₁, σ * n * σ⁻¹ ∈ Subgroup.closure S₁) ∧
      (∀ n ∈ Subgroup.closure S₁, σ⁻¹ * n * σ ∈ Subgroup.closure S₁)) :
    ∀ g ∈ G, ∀ n ∈ Subgroup.closure S₁, g * n * g⁻¹ ∈ Subgroup.closure S₁ := by
  let N : Subgroup (U ≃ₗ[K] U) := Subgroup.closure S₁
  have hLnorm : L ⊆ Subgroup.normalizer (N : Set (U ≃ₗ[K] U)) := by
    intro l hl
    refine (Subgroup.mem_normalizer_iff).mpr ?_
    intro n
    constructor
    · intro hn
      have hσ : l ∈ S := by
        rw [hS]
        exact ⟨l, hl, 1, G.one_mem, by simp⟩
      exact (hconjN l hσ).1 n hn
    · intro hn
      have hσ : l ∈ S := by
        rw [hS]
        exact ⟨l, hl, 1, G.one_mem, by simp⟩
      have := (hconjN l hσ).2 (l * n * l⁻¹) hn
      simpa [mul_assoc] using this
  have hGnorm : G ≤ Subgroup.normalizer (N : Set (U ≃ₗ[K] U)) := by
    rw [hG]
    exact (Subgroup.closure_le _).mpr hLnorm
  intro g hg n hn
  exact (Subgroup.mem_normalizer_iff.mp (hGnorm hg) n).mp hn

theorem exists_conj_moves_two [FiniteDimensional K U] {G : Subgroup (U ≃ₗ[K] U)}
    {L : Set (U ≃ₗ[K] U)} (hG : G = Subgroup.closure L)
    (hL : ∀ l ∈ L, Module.finrank K (HardMathSupport.Kantor79.movedSpace l) = 1)
    (hirr : ∀ W : Submodule K U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {W₁ W₂ : Submodule K U}
    (h₁ : W₁ ≠ ⊥) (h₁' : W₁ ≠ ⊤) (h₂ : W₂ ≠ ⊥) (h₂' : W₂ ≠ ⊤) :
    ∃ l ∈ L, ∃ g ∈ G,
      (∃ w ∈ W₁, (g * l * g⁻¹) w ∉ W₁) ∧ ∃ w ∈ W₂, (g * l * g⁻¹) w ∉ W₂ := by
  by_contra hcon
  push Not at hcon
  let S : Set (U ≃ₗ[K] U) := {σ | ∃ l ∈ L, ∃ g ∈ G, σ = g * l * g⁻¹}
  let S₁ : Set (U ≃ₗ[K] U) :=
    {σ | ∃ l ∈ L, ∃ g ∈ G, σ = g * l * g⁻¹ ∧ ∃ w ∈ W₁, σ w ∉ W₁}
  let N : Subgroup (U ≃ₗ[K] U) := Subgroup.closure S₁
  have hS₁ne : S₁.Nonempty := S₁_nonempty hG hirr h₁ h₁' rfl
  have hNW₂ : N ≤ PresSub W₂ := closure_maps_W₂ hcon
  have hconjS₁ : ∀ σ ∈ S, σ ∉ S₁ → ∀ τ ∈ S₁, σ * τ * σ⁻¹ ∈ S₁ ∧ σ⁻¹ * τ * σ ∈ S₁ :=
    conjS₁_mem (W₁ := W₁) hG
  have hconjN : ∀ σ ∈ S, (∀ n ∈ N, σ * n * σ⁻¹ ∈ N) ∧ (∀ n ∈ N, σ⁻¹ * n * σ ∈ N) :=
    normalizer_conjS₁ hconjS₁
  have hnormal : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    normalizer_closure_S₁ (S := S) (S₁ := S₁) hG rfl hconjN
  obtain ⟨r, hrS₁⟩ := hS₁ne
  have hr1 : Module.finrank K (HardMathSupport.Kantor79.movedSpace r) = 1 := by
    obtain ⟨l, hl, g, hg, rfl, _⟩ := hrS₁
    rw [movedSpace_conj, LinearEquiv.finrank_map_eq]
    exact hL l hl
  rcases irreducible_of_normal_of_finrank_movedSpace_eq_one hirr hprim hnormal
    (Subgroup.subset_closure hrS₁) hr1 W₂ (fun n hn w hw => hNW₂ hn w hw) with h | h
  · exact h₂ h
  · exact h₂' h



end Field

section Prime

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem exists_isRefl_moves_two [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : ReflGen p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {W₁ W₂ : Submodule (ZMod p) U}
    (h₁ : W₁ ≠ ⊥) (h₁' : W₁ ≠ ⊤) (h₂ : W₂ ≠ ⊥) (h₂' : W₂ ≠ ⊤) :
    ∃ t ∈ G, IsRefl p t ∧ (∃ w ∈ W₁, t w ∉ W₁) ∧ ∃ w ∈ W₂, t w ∉ W₂ := by
  let L : Set (U ≃ₗ[ZMod p] U) := {t | t ∈ G ∧ IsRefl p t}
  have hL : ∀ l ∈ L, Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace l) = 1 :=
    fun l hl => hl.2.2
  have hG' : G = Subgroup.closure L := hG
  obtain ⟨l, hl, g, hg, hw₁, hw₂⟩ :=
    exists_conj_moves_two hG' hL hirr hprim h₁ h₁' h₂ h₂'
  exact ⟨g * l * g⁻¹, G.mul_mem (G.mul_mem hg hl.1) (G.inv_mem hg), IsRefl.conj hl.2 g, hw₁, hw₂⟩

end Prime

end CFSG.StandardType.ZS
