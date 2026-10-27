module

public import CFSG.RankThree.GF2n.Smith81.S81ZRD

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81V
open scoped commutatorElement


section Parabolic

variable {K : Type} [Field K] [CharP K 2]

theorem tor_le_PN : Tor K ≤ PN K := by
  refine iSup_le fun i => ?_
  rintro g ⟨c, rfl⟩
  exact hm_mem_linNorm i c

theorem pr_a7_of_pos {γ : Rt} (hγ : IsRoot .E7 γ) (hpos : 0 < ht γ) :
    pr a7 γ = 0 ∨ pr a7 γ = 1 := by
  have h := pr_zero_ne_neg_one_of_pos hγ hpos
  rcases pr_mem hγ a7 with h1 | h1 | h1
  · exact absurd h1 h
  · exact Or.inl h1
  · exact Or.inr h1

theorem uni_le_PN : Uni K ≤ PN K := by
  show (⨆ γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}, (e7Datum K).rootGroup γ) ≤ PN K
  refine iSup₂_le fun γ hγ => ?_
  rintro g hg
  obtain ⟨hγr, hγp⟩ := hγ
  have hroot : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγr
  obtain ⟨c, rfl⟩ := mem_XR.1 hg
  exact xE_mem_linNorm hroot (pr_a7_of_pos hroot hγp) c

theorem bor_le_PN : Bor K ≤ PN K := by
  intro b hb
  obtain ⟨u, hu, t, ht, rfl⟩ := bor_eq_mul hb
  exact (PN K).mul_mem (uni_le_PN hu) (tor_le_PN ht)

theorem nm_mem_PN (i : Fin (Tag.rank .E7)) (hi : i ≠ nodeA) : e7Data_valid.nm K i ∈ PN K := by
  have hroot : IsRoot .E7 (Pi.single i 1 : Rt) := IsRoot.basis i
  have hpr : pr a7 (Pi.single i 1 : Rt) = 0 := pr_single_ne i hi
  have hprn : pr a7 (-(Pi.single i 1 : Rt)) = 0 := by rw [pr_neg, hpr, neg_zero]
  show (e7Data_valid.xm K (Pi.single i 1) 1 * e7Data_valid.xm K (-Pi.single i 1)
      (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * e7Data_valid.xm K (Pi.single i 1) 1 : Gp K) ∈ PN K
  exact (PN K).mul_mem ((PN K).mul_mem (xE_mem_linNorm hroot (Or.inl hpr) 1)
    (xE_mem_linNorm (isRoot_neg hroot) (Or.inl hprn) _)) (xE_mem_linNorm hroot (Or.inl hpr) 1)

theorem closure_PN_s (H : Subgroup (Gp K)) (hP : PN K ≤ H) (hs : sN K ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := bruhat_decomp g
  have hnW : nW K w ∈ H := by
    obtain ⟨ω, hω, hw⟩ :=
      (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.exists_isReduced w
    have h : nW K w = (ω.map (e7Data_valid.nm K)).prod := by
      rw [hw]
      exact CFSG.LieType.Steinberg.nrep_wordProd (e7Datum_isCTGroupDatum K) hω
    rw [h]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    by_cases hi : i = nodeA
    · subst hi
      exact hs
    · exact hP (nm_mem_PN i hi)
  exact H.mul_mem (H.mul_mem (hP (bor_le_PN hb₁)) hnW) (hP (bor_le_PN hb₂))

end Parabolic

section Fix

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (A : Gp K →* (V ≃ₗ[K] V))

@[expose] def fix7 : Submodule K V where
  carrier := {v | ∀ u ∈ UA K a7, A u v = v}
  add_mem' {v w} hv hw u hu := by rw [map_add, hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fix7 {v : V} : v ∈ fix7 A ↔ ∀ u ∈ UA K a7, A u v = v := Iff.rfl

@[expose] def V17 (β : V →ₗ[K] V →ₗ[K] K) : Submodule K V where
  carrier := {w | (∀ v ∈ fix7 A, β v w = 0) ∧ ∀ u ∈ UA K a7, A u w - w ∈ fix7 A}
  add_mem' {w w'} hw hw' := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_add, hw.1 v hv, hw'.1 v hv, add_zero]
    · have : A u (w + w') - (w + w') = (A u w - w) + (A u w' - w') := by rw [map_add]; abel
      rw [this]
      exact (fix7 A).add_mem (hw.2 u hu) (hw'.2 u hu)
  zero_mem' := ⟨fun v _ => by simp, fun u _ => by simp⟩
  smul_mem' c w hw := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_smul, hw.1 v hv, smul_zero]
    · have : A u (c • w) - c • w = c • (A u w - w) := by rw [map_smul, smul_sub]
      rw [this]
      exact (fix7 A).smul_mem c (hw.2 u hu)

theorem mem_V17 {β : V →ₗ[K] V →ₗ[K] K} {w : V} :
    w ∈ V17 A β ↔ (∀ v ∈ fix7 A, β v w = 0) ∧ ∀ u ∈ UA K a7, A u w - w ∈ fix7 A := Iff.rfl

theorem toRankOne_fix_eq : ((rootDatumE7 K).toRankOne A).fix = fix7 A := by
  ext v
  rw [RankOneData.mem_fix, mem_fix7]
  constructor
  · intro h u hu
    obtain ⟨n, rfl⟩ := exists_uN hu
    exact h n
  · intro h n
    exact h _ (uN_mem n)

theorem toRankOne_V1_eq (β : V →ₗ[K] V →ₗ[K] K) :
    ((rootDatumE7 K).toRankOne A).V1 β = V17 A β := by
  ext w
  rw [RankOneData.mem_V1, mem_V17, toRankOne_fix_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    obtain ⟨n, rfl⟩ := exists_uN hu
    exact h2 n
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun n => h2 _ (uN_mem n)⟩

theorem conj_mem_UA_of_mem_PN {g : Gp K} (hg : g ∈ PN K) {u : Gp K} (hu : u ∈ UA K a7) :
    g * u * g⁻¹ ∈ UA K a7 := by
  obtain ⟨n, rfl⟩ := exists_uN hu
  obtain ⟨φ, hφ⟩ := hg
  rw [← hφ n]
  exact uN_mem _

theorem fix7_map_le_of_mem_PN {g : Gp K} (hg : g ∈ PN K) :
    (fix7 A).map (A g : V →ₗ[K] V) ≤ fix7 A := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_fix7]
  intro u hu
  have hc : g⁻¹ * u * g ∈ UA K a7 := by
    have := conj_mem_UA_of_mem_PN ((PN K).inv_mem hg) hu
    simpa using this
  have hfix : A (g⁻¹ * u * g) v = v := (mem_fix7 A).1 hv _ hc
  have key : A u * A g = A g * A (g⁻¹ * u * g) := by
    rw [← map_mul, ← map_mul]
    exact congrArg A (by group)
  have h2 : A u (A g v) = A g (A (g⁻¹ * u * g) v) := by
    rw [← LinearEquiv.mul_apply (A u) (A g), ← LinearEquiv.mul_apply (A g) (A (g⁻¹ * u * g)), key]
  show A u (A g v) = A g v
  rw [h2, hfix]

def lineStab (L : Submodule K V) : Subgroup (Gp K) where
  carrier := {g | (∀ x ∈ L, A g x ∈ L) ∧ ∀ x ∈ L, A g⁻¹ x ∈ L}
  mul_mem' {g h} hg hh := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply]
      exact hg.1 _ (hh.1 x hx)
    · rw [_root_.mul_inv_rev, map_mul, LinearEquiv.mul_apply]
      exact hh.2 _ (hg.2 x hx)
  one_mem' := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_one]
      exact hx
    · rw [inv_one, map_one]
      exact hx
  inv_mem' {g} hg := by
    refine ⟨hg.2, fun x hx => ?_⟩
    rw [inv_inv]
    exact hg.1 x hx

theorem mem_lineStab {L : Submodule K V} {g : Gp K} :
    g ∈ lineStab A L ↔ (∀ x ∈ L, A g x ∈ L) ∧ ∀ x ∈ L, A g⁻¹ x ∈ L := Iff.rfl

variable [FiniteDimensional K V]

theorem sv_E7 (hline : Module.finrank K (fix7 A) = 1)
    (hspan : ⨆ g : Gp K, (fix7 A).map (A g : V →ₗ[K] V) = ⊤) (hV : 1 < Module.finrank K V)
    {v₀ : V} (hv₀ : v₀ ∈ fix7 A) (hne : v₀ ≠ 0) : A (sN K) v₀ ∉ fix7 A := by
  intro hs
  have hmul : ∀ x ∈ fix7 A, ∃ c : K, c • v₀ = x := by
    intro x hx
    have hnz : (⟨v₀, hv₀⟩ : ↥(fix7 A)) ≠ 0 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hnz ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hlin : ∀ g : Gp K, A g v₀ ∈ fix7 A → ∀ x ∈ fix7 A, A g x ∈ fix7 A := by
    intro g hg x hx
    obtain ⟨c, rfl⟩ := hmul x hx
    rw [map_smul]
    exact (fix7 A).smul_mem c hg
  have hsStab : sN K ∈ lineStab A (fix7 A) := by
    rw [mem_lineStab, sN_inv]
    exact ⟨hlin _ hs, hlin _ hs⟩
  have hPle : PN K ≤ lineStab A (fix7 A) := by
    intro g hg
    rw [mem_lineStab]
    exact ⟨fun x hx => fix7_map_le_of_mem_PN A hg (Submodule.mem_map_of_mem hx),
      fun x hx => fix7_map_le_of_mem_PN A ((PN K).inv_mem hg) (Submodule.mem_map_of_mem hx)⟩
  have hTop : lineStab A (fix7 A) = ⊤ := closure_PN_s _ hPle hsStab
  have hall : ∀ g : Gp K, ∀ x ∈ fix7 A, A g x ∈ fix7 A := by
    intro g
    have hg : g ∈ lineStab A (fix7 A) := by
      rw [hTop]
      exact Subgroup.mem_top g
    exact ((mem_lineStab A).1 hg).1
  have hle : (⨆ g : Gp K, (fix7 A).map (A g : V →ₗ[K] V)) ≤ fix7 A := by
    refine iSup_le fun g => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hall g x hx
  rw [hspan, top_le_iff] at hle
  rw [hle, finrank_top] at hline
  omega

end Fix

end CFSG.RankThree.GF2n.Smith81.S81Z
