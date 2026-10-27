module

public import CFSG.Quasithin.Background.C124YLH6Woff

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.C124.YL.A6
open scoped MatrixGroups

theorem isSylowTwoOf_of_card {G : Type*} [Group G] [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    {a m : ℕ} (ha : Nat.card A = 2 ^ a) (hb : Nat.card B = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    IsSylowTwoOf A B := by
  refine ⟨hAB, IsPGroup.of_card ha, ?_⟩
  have h := Subgroup.index_mul_card (A.subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, ha, hb] at h
  have hpos : 0 < 2 ^ a := by positivity
  have : (A.subgroupOf B).index = m := by
    have h' : (A.subgroupOf B).index * 2 ^ a = m * 2 ^ a := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  rw [this]
  exact hm

namespace HatCtx

variable {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K] [Finite K]
  {Γ₀ : Subgroup (GL (Fin 3) K)} {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : HatCtx K Γ₀ Ls U Z)

theorem comm_mem_iff {c : ↥U →* Multiplicative (Fin 3 → K)} (hc : IsCoord U Z c)
    (hequiv : ∀ (γ : ↥Γ₀) (u : ↥U) (hu : C.phi γ (u : W) ∈ U),
      c ⟨C.phi γ (u : W), hu⟩ = natAct Γ₀ γ (c u))
    (γ : ↥Γ₀) (u : ↥U) :
    C.phi γ (u : W) * (u : W)⁻¹ ∈ Z ↔ natAct Γ₀ γ (c u) = c u := by
  have hu : C.phi γ (u : W) ∈ U := C.phi_stab γ u u.2
  have h1 := hc.ker (⟨C.phi γ (u : W), hu⟩ * u⁻¹)
  rw [map_mul, map_inv, mul_inv_eq_one, hequiv γ u hu] at h1
  exact h1.symm

theorem map_phi_le (B : Subgroup ↥Γ₀) : B.map C.phi ≤ Ls := fun x hx => by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  exact C.phi_mem g

theorem map_comap_phi {B : Subgroup (MulAut W)} (hB : B ≤ Ls) :
    (B.comap C.phi).map C.phi = B :=
  Subgroup.map_comap_eq_self (hB.trans C.phi_range.ge)

theorem model_facts {K1' : Subgroup ↥Γ₀} (hw : WOff U Z (K1'.map C.phi)) :
    K1' ≠ ⊥ ∧ (∀ a ∈ K1', ∀ b ∈ K1', a * b = b * a) ∧ (∀ a ∈ K1', a * a = 1) ∧
      Nat.card K1' = 4 ∧ Nat.card (fixS K1') = 16 ∧ K1' = stabS (fixS K1') := by
  obtain ⟨hne, hc, hs, hoff⟩ := (C.woff_map_iff K1').1 hw
  obtain ⟨h4, h16, hst⟩ := offender_facts C.hK C.two_eq_zero C.hdet C.h4 hne hc hs hoff
  exact ⟨hne, hc, hs, h4, h16, hst⟩

theorem tight_model {K1' : Subgroup ↥Γ₀} (h4 : Nat.card K1' = 4)
    (h16 : Nat.card (fixS K1') = 16) :
    Nat.card U = Nat.card (K1'.map C.phi) * Nat.card (liftFix U Z (K1'.map C.phi)) := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  have hZB := Z_le_liftFix_real C.real (C.map_phi_le K1')
  rw [hc.card_U, hc.card_liftFix hZB, C.card_Q, C.card_fixImg hc hequiv, h16,
    Subgroup.card_map_of_injective C.phi_injective, h4]
  ring

theorem cent_model {K1' : Subgroup ↥Γ₀} (hst : K1' = stabS (fixS K1')) {x : MulAut W}
    (hx : x ∈ Ls) (hfix : ∀ u ∈ liftFix U Z (K1'.map C.phi), x u * u⁻¹ ∈ Z) :
    x ∈ K1'.map C.phi := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  obtain ⟨γ, rfl⟩ : x ∈ C.phi.range := C.phi_range.ge hx
  have hγ : γ ∈ stabS (fixS K1') := by
    intro y hy
    have hq : Multiplicative.ofAdd y ∈ fixImg U Z c (K1'.map C.phi) :=
      (C.mem_fixImg_iff hc hequiv K1' _).2 hy
    obtain ⟨u, hu, hb⟩ := mem_fixImg.1 hq
    have hul : (u : W) ∈ liftFix U Z (K1'.map C.phi) := mem_liftFix.2 ⟨u.2, hb⟩
    have h2 := (C.comm_mem_iff hc hequiv γ u).1 (hfix u hul)
    rw [hu] at h2
    exact (natAct_eq_iff γ _).1 h2
  rw [← hst] at hγ
  exact Subgroup.mem_map_of_mem _ hγ

theorem moves_model {K1' Y' : Subgroup ↥Γ₀} (hY : ¬ Y' ≤ stabS (fixS K1')) :
    ∃ u ∈ liftFix U Z (K1'.map C.phi), ∃ y ∈ Y'.map C.phi, y u * u⁻¹ ∉ Z := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  obtain ⟨γ, hγY, hγs⟩ : ∃ γ ∈ Y', γ ∉ stabS (fixS K1') := by
    by_contra h
    push Not at h
    exact hY h
  obtain ⟨w, hw, hmove⟩ : ∃ w ∈ fixS K1', (mat Γ₀ γ).mulVec w ≠ w := by
    by_contra h
    push Not at h
    exact hγs h
  have hq : Multiplicative.ofAdd w ∈ fixImg U Z c (K1'.map C.phi) :=
    (C.mem_fixImg_iff hc hequiv K1' _).2 hw
  obtain ⟨u, hu, hb⟩ := mem_fixImg.1 hq
  refine ⟨u, mem_liftFix.2 ⟨u.2, hb⟩, C.phi γ, Subgroup.mem_map_of_mem _ hγY, fun hz => ?_⟩
  have h2 := (C.comm_mem_iff hc hequiv γ u).1 hz
  rw [hu] at h2
  exact hmove ((natAct_eq_iff γ _).1 h2)

theorem unique_in_sylow {K1' P' : Subgroup ↥Γ₀} (hP : Nat.card P' = 8) (hKP : K1' ≤ P')
    (hw1 : WOff U Z (K1'.map C.phi)) {B : Subgroup (MulAut W)} (hBP : B ≤ P'.map C.phi)
    (hwB : WOff U Z B) : B = K1'.map C.phi := by
  have hBL : B ≤ Ls := hBP.trans (C.map_phi_le P')
  have hBeq : (B.comap C.phi).map C.phi = B := C.map_comap_phi hBL
  have hB'P : B.comap C.phi ≤ P' := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hBP hx)
    rw [← C.phi_injective hyx]
    exact hy
  rw [← hBeq] at hwB ⊢
  obtain ⟨hne, hc, hs, h4B, -, -⟩ := C.model_facts hwB
  obtain ⟨hne1, hc1, hs1, h41, -, -⟩ := C.model_facts hw1
  have hinter := inf_ne_bot_of_card hP hB'P hKP h4B h41
  have hoff := (C.woff_map_iff _).1 hwB
  have hoff1 := (C.woff_map_iff _).1 hw1
  rw [offender_unique C.hK C.two_eq_zero C.hdet C.h4 hne hc hs hoff.2.2.2 hne1 hc1 hs1
    hoff1.2.2.2 hinter]

theorem gen_map {K' Y' : Subgroup ↥Γ₀} (hgen : Y' ⊔ Subgroup.normalizer (K' : Set ↥Γ₀) = ⊤) :
    Ls = Y'.map C.phi ⊔ (Ls ⊓ Subgroup.normalizer ((K'.map C.phi : Subgroup (MulAut W)) :
      Set (MulAut W))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ : x ∈ C.phi.range := C.phi_range.ge hx
    have hg' : g ∈ Y' ⊔ Subgroup.normalizer (K' : Set ↥Γ₀) := by
      rw [hgen]
      exact Subgroup.mem_top g
    have hmap : (Y' ⊔ Subgroup.normalizer (K' : Set ↥Γ₀)).map C.phi =
        Y'.map C.phi ⊔ (Subgroup.normalizer (K' : Set ↥Γ₀)).map C.phi := Subgroup.map_sup _ _ _
    have hmem := Subgroup.mem_map_of_mem C.phi hg'
    rw [hmap] at hmem
    have hN : (Subgroup.normalizer (K' : Set ↥Γ₀)).map C.phi ≤
        Ls ⊓ Subgroup.normalizer ((K'.map C.phi : Subgroup (MulAut W)) : Set (MulAut W)) := by
      intro y hy
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
      refine ⟨C.phi_mem n, Subgroup.mem_normalizer_fintype fun k hk => ?_⟩
      obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hk
      have := (Subgroup.mem_normalizer_iff.1 hn κ).1 hκ
      exact Subgroup.mem_map.2 ⟨n * κ * n⁻¹, this, by simp [map_mul, map_inv]⟩
    exact (sup_le_sup_left hN (Y'.map C.phi)) hmem
  · refine sup_le ?_ inf_le_left
    exact C.map_phi_le Y'

end HatCtx

end CFSG.Quasithin.C124.YL.H6
