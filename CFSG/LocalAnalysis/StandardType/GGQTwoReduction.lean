module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2r_fixed {G : Type} [Group G] {Bs : Subgroup G} (t : MulAut ↥Bs) :
    Subgroup ↥Bs where
  carrier := {b | t b = b}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

private lemma ggQ2r_exists_fixed {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (F D' : Subgroup ↥Bs) (hF : Nat.card F * p = Nat.card ↥Bs)
    (hD : Nat.card D' = p ^ 2) :
    ∃ u : ↥Bs, u ∈ D' ∧ u ≠ 1 ∧ u ∈ F := by
  by_contra hcon
  have hcon' : ∀ u : ↥Bs, u ∈ D' → u ∈ F → u = 1 := by
    intro u huD huF
    by_contra hu1
    exact hcon ⟨u, huD, hu1, huF⟩
  have hinf : D' ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    exact hcon' u hu.1 hu.2
  have hdisj : Disjoint D' F := disjoint_iff.mpr hinf
  have hinj : Function.Injective (fun x : D' × F => (x.1 : ↥Bs) * (x.2 : ↥Bs)) :=
    Subgroup.mul_injective_of_disjoint hdisj
  have hle : Nat.card (D' × F) ≤ Nat.card ↥Bs :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hD, ← hF] at hle
  have hcpos : 0 < Nat.card F := by
    haveI : Nonempty ↥F := ⟨⟨1, F.one_mem⟩⟩
    exact Nat.card_pos
  have hle2 : Nat.card F * p ^ 2 ≤ Nat.card F * p := by
    calc Nat.card F * p ^ 2 = p ^ 2 * Nat.card F := Nat.mul_comm _ _
      _ ≤ Nat.card F * p := hle
  have hp2le : p ^ 2 ≤ p := Nat.le_of_mul_le_mul_left hle2 hcpos
  have hplt : p < p ^ 2 := by nlinarith [hp.two_le]
  exact (not_le.mpr hplt) hp2le

private theorem ggQ2r_refl_mem {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hΓ : ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u)
    {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer ⊤ Bs) (ht : GGIsReflection p t) :
    t ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hstdPre : LargeEvenStdSubPre p B x L D J := hS.1.1.2.2.1
  have hp : p.Prime := hcfg.tableB_facts.1
  have hBle : B ≤ Bs := hBstar.1
  have hDle : D ≤ Bs := hstdPre.1.trans hBle
  have hcardD : Nat.card D = p ^ 2 := hstdPre.2.2.1
  have hF : Nat.card (ggQ2r_fixed t) * p = Nat.card ↥Bs := ht.2
  have hcardD' : Nat.card (D.subgroupOf Bs) = p ^ 2 := by
    have h1 : Nat.card (D.subgroupOf Bs) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
    rw [h1, hcardD]
  obtain ⟨u, huD', hu1, huF⟩ :=
    ggQ2r_exists_fixed hp (ggQ2r_fixed t) (D.subgroupOf Bs) hF hcardD'
  have huD : (u : G) ∈ D := Subgroup.mem_subgroupOf.mp huD'
  have hfix : t u = u := huF
  refine (hΓ u huD hu1) t htA ?_
  rw [hfix]
  exact Subgroup.mem_zpowers u

theorem ggQ2r_reflGp_le_M {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hΓ : ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u) :
    ggReflGp p Bs ≤ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  rw [ggReflGp]
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨htA, ht⟩
  exact ggQ2r_refl_mem hS hΓ htA ht

private theorem ggQ2r_reflGp_le_automizer {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} :
    ggReflGp p Bs ≤ ggAutomizer ⊤ Bs := by
  rw [ggReflGp]
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨htA, -⟩
  exact htA

private theorem ggQ2r_automizer_le_M {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hΓ : ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u)
    (hP : ∃ u : ↥Bs, (u : G) ∈ D ∧ u ≠ 1 ∧ GGOrbitStableAt p Bs u) :
    ggAutomizer ⊤ Bs ≤ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  have hRM := ggQ2r_reflGp_le_M hS hΓ
  have hRA := ggQ2r_reflGp_le_automizer (p := p) (Bs := Bs)
  intro φ hφA
  obtain ⟨u, huD, hu1, hstab⟩ := hP
  obtain ⟨r, hrR, horbit⟩ := hstab φ hφA
  have hrA : r ∈ ggAutomizer ⊤ Bs := hRA hrR
  have hrM : r ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := hRM hrR
  have hψA : r⁻¹ * φ ∈ ggAutomizer ⊤ Bs :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hrA) hφA
  have hψmem : (r⁻¹ * φ) u ∈ Subgroup.zpowers u := by
    have hmem : φ u ∈ Subgroup.zpowers (r u) := horbit ▸ Subgroup.mem_zpowers (φ u)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [MulAut.mul_apply, Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (calc (r⁻¹ : MulAut ↥Bs) ((r u) ^ k)
        = ((r⁻¹ : MulAut ↥Bs) (r u)) ^ k := map_zpow _ _ _
      _ = u ^ k := by rw [MulAut.inv_apply_self]).symm
  have hψM : r⁻¹ * φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs :=
    (hΓ u huD hu1) _ hψA hψmem
  have hφeq : r * (r⁻¹ * φ) = φ := by group
  rw [← hφeq]
  exact Subgroup.mul_mem _ hrM hψM

theorem ggQ2_normalizer_le_of_automizer_le {G : Type} [Group G] {Bs N : Subgroup G}
    (hC : Subgroup.centralizer (Bs : Set G) ≤ N) (hAM : ggAutomizer ⊤ Bs ≤ ggAutomizer N Bs) :
    Subgroup.normalizer (Bs : Set G) ≤ N := by
  intro g hg
  have hφM : ggConjAut Bs hg ∈ ggAutomizer N Bs :=
    hAM (ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg)
  rw [mem_ggAutomizer_iff] at hφM
  obtain ⟨g', hg'N, -, hg'eq⟩ := hφM
  have hmem : g'⁻¹ * g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : g * b * g⁻¹ = g' * b * g'⁻¹ := by
      have hb' := hg'eq ⟨b, hb⟩
      rw [ggConjAut_apply] at hb'
      simpa using hb'
    have h2 : (g'⁻¹ * g) * b * (g'⁻¹ * g)⁻¹ = b := by
      calc (g'⁻¹ * g) * b * (g'⁻¹ * g)⁻¹
          = g'⁻¹ * (g * b * g⁻¹) * g' := by group
        _ = g'⁻¹ * (g' * b * g'⁻¹) * g' := by rw [h1]
        _ = b := by group
    have h3 : (g'⁻¹ * g) * b = b * (g'⁻¹ * g) := by
      calc (g'⁻¹ * g) * b
          = (g'⁻¹ * g) * b * (g'⁻¹ * g)⁻¹ * (g'⁻¹ * g) := by group
        _ = b * (g'⁻¹ * g) := by rw [h2]
    exact h3.symm
  have hge : g' * (g'⁻¹ * g) = g := by group
  rw [← hge]
  exact Subgroup.mul_mem _ hg'N (hC hmem)

theorem ggQ2_reduction {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hC : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G))
    (hΓ : ∀ u : ↥Bs, (u : G) ∈ D → u ≠ 1 → GGGammaAt p B Bs x L D J u)
    (hP : ∃ u : ↥Bs, (u : G) ∈ D ∧ u ≠ 1 ∧ GGOrbitStableAt p Bs u) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
  ggQ2_normalizer_le_of_automizer_le hC (ggQ2r_automizer_le_M hS hΓ hP)

end CFSG.StandardType

end
