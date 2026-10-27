module

public import CFSG.Quasithin.Vol2.Ch10SecBInner
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_normal_of_ne {L N : Subgroup G} (hNL : N ≤ L)
    (hnorm : L ≤ Subgroup.normalizer (N : Set G))
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hperf : ⁅L, L⁆ = L) (hne : N ≠ L) :
    N ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN' : (N.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hnorm
  have hP : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hNb : ((N.subgroupOf L).map π).Normal := hN'.map π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map π) with hb | ht
  · intro x hx
    have h1 : π ⟨x, hNL hx⟩ ∈ (N.subgroupOf L).map π := ⟨⟨x, hNL hx⟩, hx, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  · exfalso
    apply hne
    have hsup : N.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
      have h1 := congrArg (Subgroup.comap π) ht
      rw [Subgroup.comap_top, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
      exact h1
    let ρ := QuotientGroup.mk' (N.subgroupOf L)
    have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
    have hPp : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) (r := 2)
    have hsurj : Function.Surjective (ρ.comp (CFSG.pCore 2 ↥L).subtype) := by
      intro q
      obtain ⟨y, rfl⟩ := hρs q
      have hy : y ∈ N.subgroupOf L ⊔ CFSG.pCore 2 ↥L := hsup ▸ Subgroup.mem_top y
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      refine ⟨⟨b, hb⟩, ?_⟩
      show ρ b = ρ (a * b)
      have ha1 : ρ a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      rw [map_mul, ha1, one_mul]
    have h2 : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := hPp.of_surjective _ hsurj
    have hL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
      rw [← commutator_def]
      exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
    have h3 : ⁅(⊤ : Subgroup (↥L ⧸ N.subgroupOf L)), (⊤ : Subgroup (↥L ⧸ N.subgroupOf L))⁆ =
        (⊤ : Subgroup (↥L ⧸ N.subgroupOf L)) := by
      rw [← Subgroup.map_top_of_surjective _ hρs, ← Subgroup.map_commutator, hL]
    by_contra hNe
    have hnt : Nontrivial (↥L ⧸ N.subgroupOf L) := by
      rw [QuotientGroup.nontrivial_iff]
      intro htop
      exact hNe (le_antisymm hNL (Subgroup.subgroupOf_eq_top.mp htop))
    have := h2.isNilpotent
    have hsolv : Group.IsSolvable (↥L ⧸ N.subgroupOf L) := inferInstance
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := ↥L ⧸ N.subgroupOf L)).ne h3

omit [Finite G] in
theorem mem_autOn_iff {H V : Subgroup G} {g : MulAut ↥V} :
    g ∈ autOn H V ↔ ∃ x : ↥(Subgroup.normalizer (V : Set G)), (x : G) ∈ H ∧ conjAct V x = g := by
  simp only [autOn, Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem conj_mem_centralizer_iff {X : Subgroup G} {s u : G}
    (hs : s ∈ Subgroup.normalizer (X : Set G)) :
    s * u * s⁻¹ ∈ Subgroup.centralizer (X : Set G) ↔ u ∈ Subgroup.centralizer (X : Set G) := by
  have key : ∀ {a v : G}, a ∈ Subgroup.normalizer (X : Set G) →
      v ∈ Subgroup.centralizer (X : Set G) → a * v * a⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro a v ha hv
    rw [Subgroup.mem_centralizer_iff] at hv ⊢
    intro y hy
    have hy' : a⁻¹ * y * a⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) y).mp hy
    have := hv _ hy'
    calc y * (a * v * a⁻¹) = a * ((a⁻¹ * y * a⁻¹⁻¹) * v) * a⁻¹ := by group
      _ = a * (v * (a⁻¹ * y * a⁻¹⁻¹)) * a⁻¹ := by rw [this]
      _ = a * v * a⁻¹ * y := by group
  refine ⟨fun h => ?_, key hs⟩
  have := key (inv_mem hs) h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isSimpleGroup_of_LBarL32 {L : Subgroup G} (h : LBarL32 L) :
    IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  exact (Classical.choice h).isSimpleGroup

theorem inner_of_case3 {T L I : Subgroup G} (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    {s : G} (hs : s ∈ T1 T L) : ∃ x₀ ∈ L,
      (∀ x ∈ L, s * x * s⁻¹ * (x₀ * x * x₀⁻¹)⁻¹ ∈ pCoreOf 2 L) ∧
      ∀ u ∈ fsuUL T L I, s * u * s⁻¹ * (x₀ * u * x₀⁻¹)⁻¹ ∈ fsuCVM T L I := by
  obtain ⟨hL32, hcomm, hnat⟩ := h3
  have hloc : quasithinIsLocal T L := h.fsu.maximal.1
  have hL0N : ∀ y ∈ fsuL0 T L ⊔ T, y ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
    fun y hy => (sup_le Subgroup.le_normalizer (le_fsuM T L)) hy
  have hT1U : T1 T L ≤ Subgroup.normalizer ((fsuUL T L I) : Set G) :=
    SecA.le_normalizer_commutator (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I))
      inf_le_right
  have hLU : L ≤ Subgroup.normalizer ((fsuUL T L I) : Set G) :=
    SecA.le_normalizer_commutator ((SecA.le_fsuL0 T L).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I)) Subgroup.le_normalizer
  have hsU : s ∈ Subgroup.normalizer ((fsuUL T L I) : Set G) := hT1U hs
  have hsL : s ∈ Subgroup.normalizer (L : Set G) := hs.2
  have hsL0 : s ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
    hL0N s (Subgroup.mem_sup_right hs.1)
  obtain ⟨D⟩ := BinaryNaturalSL.toL3Coord hnat
  let c : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) ⟨s, hsU⟩
  have hc : ∀ u : ↥(fsuUL T L I), ((c u : ↥(fsuUL T L I)) : G) = s * u * s⁻¹ := fun u =>
    A1b.conjAct_coe (fsuUL T L I) ⟨s, hsU⟩ u
  have hcZ : ∀ u ∈ (⊤ : Subgroup ↥(fsuUL T L I)), (c u ∈ cV1 T L I ↔ u ∈ cV1 T L I) := by
    intro u _
    simp only [cV1, Subgroup.mem_subgroupOf, hc]
    exact conj_mem_centralizer_iff hsL0
  have hcΛ : ∀ g ∈ autOn L (fsuUL T L I), c * g * c⁻¹ ∈ autOn L (fsuUL T L I) := by
    intro g hg
    obtain ⟨x, hxL, rfl⟩ := mem_autOn_iff.mp hg
    refine mem_autOn_iff.mpr ⟨⟨s, hsU⟩ * x * ⟨s, hsU⟩⁻¹, ?_, by simp [c, map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp hsL x).mp hxL
    simpa using this
  obtain ⟨A, hA⟩ := exists_conj_rho D (fun u _ => Subgroup.mem_top _) hcZ hcΛ
  obtain ⟨x₀, hx₀L, hx₀⟩ := mem_autOn_iff.mp (D.rho_mem A)
  have hUV : (fsuUL T L I) ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  refine ⟨x₀, hx₀L, ?_, ?_⟩
  ·
    have hCU : ∀ y ∈ Subgroup.normalizer ((fsuUL T L I) : Set G),
        y ∈ Subgroup.normalizer (Subgroup.centralizer ((fsuUL T L I) : Set G) : Set G) :=
        fun y hy => by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact (conj_mem_centralizer_iff hy).symm
    have hCnorm : L ≤ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer ((fsuUL T L I) : Set G) : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hCU y (hLU hy)⟩
    have hne : L ⊓ Subgroup.centralizer ((fsuUL T L I) : Set G) ≠ L := by
      intro heq
      obtain ⟨y, hyL, hy⟩ := mem_autOn_iff.mp (D.rho_mem tr12)
      have hyC : (y : G) ∈ L ⊓ Subgroup.centralizer ((fsuUL T L I) : Set G) := heq.symm ▸ hyL
      have hy1 : conjAct (fsuUL T L I) y = 1 := A1b.conjAct_eq_one_iff.mpr hyC.2
      have h1 : D.rho tr12 = D.rho 1 := by rw [← hy, hy1, map_one]
      exact absurd (D.rho_injective h1) (by decide)
    have hO2 := le_pCoreOf_of_normal_of_ne inf_le_left hCnorm (isSimpleGroup_of_LBarL32 hL32)
      (SecA.perfect_L hloc) hne
    intro x hx
    apply hO2
    refine ⟨L.mul_mem (by simpa using (Subgroup.mem_normalizer_iff.mp hsL x).mp hx)
      (L.inv_mem (L.mul_mem (L.mul_mem hx₀L hx) (L.inv_mem hx₀L))), ?_⟩
    let xN : ↥(Subgroup.normalizer ((fsuUL T L I) : Set G)) := ⟨x, hLU hx⟩
    obtain ⟨γ, hγ⟩ := D.exists_rho (mem_autOn_iff.mpr ⟨xN, hx, rfl⟩)
    have key := hA γ
    rw [hγ, ← hx₀] at key
    have h2 : conjAct (fsuUL T L I) ((⟨s, hsU⟩ * xN * ⟨s, hsU⟩⁻¹) * (x₀ * xN * x₀⁻¹)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [show c = conjAct (fsuUL T L I) ⟨s, hsU⟩ from rfl] at key
      rw [key]
      group
    have h3 := A1b.conjAct_eq_one_iff.mp h2
    simpa [mul_assoc] using h3
  ·
    let c' : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) (x₀⁻¹ * ⟨s, hsU⟩)
    have hc'Z : ∀ u ∈ (⊤ : Subgroup ↥(fsuUL T L I)), (c' u ∈ cV1 T L I ↔ u ∈ cV1 T L I) := by
      intro u _
      have hx₀L0 : (x₀ : G) ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
        hL0N _ (Subgroup.mem_sup_left (SecA.le_fsuL0 T L hx₀L))
      simp only [cV1, Subgroup.mem_subgroupOf, c', A1b.conjAct_coe]
      exact conj_mem_centralizer_iff (Subgroup.mul_mem _ (inv_mem hx₀L0) hsL0)
    have hc'Λ : ∀ g ∈ autOn L (fsuUL T L I), c' * g = g * c' := by
      intro g hg
      obtain ⟨γ, rfl⟩ := D.exists_rho hg
      have key := hA γ
      have hc' : c' = (D.rho A)⁻¹ * c := by
        simp only [c', c, map_mul, map_inv, hx₀]
      rw [hc']
      calc (D.rho A)⁻¹ * c * D.rho γ = (D.rho A)⁻¹ * (c * D.rho γ * c⁻¹) * c := by group
        _ = D.rho γ * ((D.rho A)⁻¹ * c) := by rw [key]; group
    have htriv := trivial_on_section_of_commute D (fun u _ => Subgroup.mem_top _) hc'Z hc'Λ
    intro u hu
    have h1 := htriv ⟨u, hu⟩ (Subgroup.mem_top _)
    simp only [cV1, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, c',
      A1b.conjAct_coe] at h1
    have hx₀L0 : (x₀ : G) ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
      hL0N _ (Subgroup.mem_sup_left (SecA.le_fsuL0 T L hx₀L))
    have hx₀V : (x₀ : G) ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.le_fsuL0 T L hx₀L)
    have hsV : s ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.le_normalizer_fsuVM T L I hs.1
    refine Subgroup.mem_inf.mpr ⟨(fsuVM T L I).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hsV u).mp (hUV hu))
      ((fsuVM T L I).inv_mem ((Subgroup.mem_normalizer_iff.mp hx₀V u).mp (hUV hu))), ?_⟩
    have h2 := (conj_mem_centralizer_iff hx₀L0).mpr h1
    have heq : s * u * s⁻¹ * ((x₀ : G) * u * (x₀ : G)⁻¹)⁻¹ =
        (x₀ : G) * ((x₀ : G)⁻¹ * s * u * ((x₀ : G)⁻¹ * s)⁻¹ * u⁻¹) * (x₀ : G)⁻¹ := by group
    rw [heq]
    exact h2

end CFSG.Quasithin.Vol2.Ch10.SecB
