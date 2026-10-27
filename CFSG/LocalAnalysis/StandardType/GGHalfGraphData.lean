module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphE6
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagE
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofHalf

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem ggHalfGraphData_f2 (x : F2) : x = 0 ∨ x = 1 := by
  rcases eq_or_ne x 0 with h | h
  · exact Or.inl h
  · right
    have hcard : Nat.card F2 = 2 := by
      rw [GaloisField.card 2 1 (by norm_num)]
      norm_num
    obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    rw [hy x h, hy 1 one_ne_zero]

private theorem ggHalfGraphData_slE_eq (a b : Fin 6) (h : a ≠ b) :
    slE a b = SpecialLinearGroup.transvection h 1 := by
  unfold slE
  rw [dif_neg h]

private theorem ggHalfGraphData_slE_closure :
    Subgroup.closure {s : SpecialLinearGroup (Fin 6) F2 | ∃ c d, c ≠ d ∧ s = slE c d} = ⊤ := by
  apply le_antisymm le_top
  rw [← slOn_univ 6]
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨a, b, hab, c, -, -, rfl⟩
  rcases ggHalfGraphData_f2 c with rfl | rfl
  · rw [SpecialLinearGroup.transvection_coeff_zero]
    exact Subgroup.one_mem _
  · have hs : slE a b ∈
        Subgroup.closure {s : SpecialLinearGroup (Fin 6) F2 | ∃ c d, c ≠ d ∧ s = slE c d} :=
      Subgroup.subset_closure ⟨a, b, hab, rfl⟩
    rwa [ggHalfGraphData_slE_eq a b hab] at hs

private theorem ggHalfGraphData_labL (c : Fin 6) : GGHalfBlk.L.Lab (GGHalfBlk.L.lab c) := by
  show (GGHalfBlk.L.lab c).val < 6
  simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk, Nat.zero_add]
  exact c.isLt

private theorem ggHalfGraphData_torus_bot :
    ggTorus (CFSG.LieType.Universal.SpecialLinear.rootDatum 5 F2) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  have hd := CompatA.isDiag_of_mem_ggTorus (m := 5) (by norm_num) hh
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have hne := CompatA.diag_ne_zero hd i
    rcases ggHalfGraphData_f2 ((h : Matrix (Fin 6) (Fin 6) F2) i i) with h0 | h1
    · exact absurd h0 hne
    · simpa using h1
  · rw [hd hij]
    simp [Matrix.one_apply_ne hij]

private theorem ggHalfGraphData_theta
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (m : GGHalfE6Model) (hm : m.Good)
    (φ : GGE6Two →* G)
    (hL : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) = φ₁ (slE c d)) :
    ∃ θ : SpecialLinearGroup (Fin 6) F2 →* GGE6Two, Function.Injective θ ∧
      (∀ c d : Fin 6, c ≠ d → θ (slE c d) =
        ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) ∧
      φ.comp θ = φ₁ := by
  obtain ⟨hFL, -⟩ := hm
  obtain ⟨θ, hθinj, hθ⟩ := m.exists_theta .L hFL
  refine ⟨θ, hθinj, hθ, ?_⟩
  apply MonoidHom.ext
  intro s
  have hs : s ∈
      Subgroup.closure {s : SpecialLinearGroup (Fin 6) F2 | ∃ c d, c ≠ d ∧ s = slE c d} := by
    rw [ggHalfGraphData_slE_closure]
    trivial
  refine Subgroup.closure_induction (p := fun s _ => (φ.comp θ) s = φ₁ s) ?_ ?_ ?_ ?_ hs
  · intro a hx
    rcases hx with ⟨c, d, hcd, rfl⟩
    rw [MonoidHom.comp_apply, hθ c d hcd]
    exact hL c d hcd
  · simp
  · intro a b _ _ iha ihb
    simp only [MonoidHom.comp_apply, map_mul, iha, ihb]
  · intro a _ iha
    simp only [MonoidHom.comp_apply, map_inv, iha]

private theorem ggHalfGraphData_ggG0_le_range
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (m : GGHalfE6Model) (hm : m.Good)
    (φ : GGE6Two →* G)
    (hL : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) = φ₁ (slE c d))
    (hnbr : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ φ.range) :
    ggG0 p B x L D J ≤ φ.range := by
  obtain ⟨θ, -, -, hcomp⟩ := ggHalfGraphData_theta h m hm φ hL
  rw [ggG0]
  refine sup_le ?_ ?_
  · rw [← h.coords.range₁]
    rintro r ⟨s, rfl⟩
    exact ⟨θ s, by rw [← MonoidHom.comp_apply, hcomp]⟩
  · refine iSup_le fun y' => iSup_le fun K' => iSup_le fun hN => ?_
    exact hnbr y' K' hN

theorem secFiveData_of_graph
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (m : GGHalfE6Model) (hm : m.Good)
    (φ : GGE6Two →* G) (hinj : Function.Injective φ) (hrange : φ.range ≤ ggG0 p B x L D J)
    (hL : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) = φ₁ (slE c d))
    (hnbr : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ φ.range) :
    GGSecFiveData p B x L D J := by
  have hadm : StatedLieAdmissible .E6 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl⟩
  have hrank : 3 ≤ CFSG.LieType.Universal.bnRank .E6 0 := by
    change 3 ≤ 6
    norm_num
  have hrange : φ.range = ggG0 p B x L D J :=
    le_antisymm hrange (ggHalfGraphData_ggG0_le_range h m hm φ hL hnbr)
  have hker : φ.ker ≤ Subgroup.center (ggU .E6 0 1).K := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hinj]
    exact bot_le
  exact Or.inr (Or.inr ⟨.E6, 0, 1,
    ggSecFivePres_of_psi_E6 hadm hrank φ hker hrange⟩)

theorem secFiveCompat_of_graph
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (m : GGHalfE6Model) (hm : m.Good)
    (φ : GGE6Two →* G) (hinj : Function.Injective φ) (hrange : φ.range ≤ ggG0 p B x L D J)
    (hL : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) = φ₁ (slE c d))
    (hnbr : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ φ.range) :
    GGSecFiveCompat p B x L D J := by
  have hadmE6 : StatedLieAdmissible .E6 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl⟩
  have hrankE6 : 3 ≤ CFSG.LieType.Universal.bnRank .E6 0 := by
    change 3 ≤ 6
    norm_num
  have hrange : φ.range = ggG0 p B x L D J :=
    le_antisymm hrange (ggHalfGraphData_ggG0_le_range h m hm φ hL hnbr)
  have hker : φ.ker ≤ Subgroup.center (ggU .E6 0 1).K := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hinj]
    exact bot_le
  have hpres5 : GGSecFivePres p B x L D J .E6 0 1 :=
    ggSecFivePres_of_psi_E6 hadmE6 hrankE6 φ hker hrange
  have hpresG0 : GGPresentsG0 (ggG0 p B x L D J) (ggU .E6 0 1).D .E6 0 1 φ := by
    obtain ⟨ψ', h1, -, h3, h4⟩ := ggPresentsG0_of_secFivePres hpres5
    exact ⟨h1, ⟨hrange, hker⟩, h3, h4⟩
  obtain ⟨θ, hθinj, hθ, hcomp⟩ := ggHalfGraphData_theta h m hm φ hL
  have hadmPSL : StatedLieAdmissible .PSL 6 2 1 := ⟨Nat.prime_two, le_rfl, by decide⟩
  have hrkPSL : 2 ≤ (ggU .PSL 6 1).D.rank := by
    change 2 ≤ 5
    norm_num
  have hδ : (Pi.single (0 : Fin 5) 1 : Fin 5 → ℤ) ∈ (ggU .PSL 6 1).D.roots := by
    change (Pi.single (0 : Fin 5) 1 : Fin 5 → ℤ) ∈
      CFSG.LieType.RootSystem.roots
        (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 5) (∅ : Set (Fin 5))
    exact (CFSG.LieType.RootSystem.isCTRootSystem
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 5)
      (∅ : Set (Fin 5))).single_mem 0
  have hγ : m.frame .L (GGHalfBlk.L.lab 0) (GGHalfBlk.L.lab 1) ∈ (ggU .E6 0 1).D.roots := by
    refine (CFSG.LieType.Steinberg.Minuscule.MinData.Valid.mem_minDatum_roots
      (hV := CFSG.LieType.Steinberg.Minuscule.e6Data_valid)
      (hA := CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6)
      (k := F2)).mpr ?_
    exact CFSG.Blueprint.Chevalley.mem_rootFinset.mp
      (hm.1.1 (GGHalfBlk.L.lab 0) (GGHalfBlk.L.lab 1)
        (ggHalfGraphData_labL 0) (ggHalfGraphData_labL 1) (by decide))
  have hroot : ∀ z ∈ (ggU .E6 0 1).D.rootGroup
        (m.frame .L (GGHalfBlk.L.lab 0) (GGHalfBlk.L.lab 1)),
      ∃ z' ∈ (ggU .PSL 6 1).D.rootGroup (Pi.single (0 : Fin 5) 1), θ z' = z := by
    intro z hz
    obtain ⟨c, hc⟩ := (CFSG.LieType.Steinberg.Minuscule.MinData.Valid.mem_rootGroup
      (hV := CFSG.LieType.Steinberg.Minuscule.e6Data_valid) (k := F2)).mp hz
    rcases ggHalfGraphData_f2 c with rfl | rfl
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [← hc, CFSG.LieType.Steinberg.Minuscule.MinData.Valid.xm_zero]
      exact map_one θ
    · refine ⟨slE 0 1, ?hmem, ?heq⟩
      · have h01 : (0 : Fin 6) ≠ 1 := by decide
        change slE 0 1 ∈ CFSG.LieType.Universal.SpecialLinear.rootGroup 5 F2 (Pi.single (0 : Fin 5) 1)
        rw [CFSG.LieType.Universal.SpecialLinear.rootGroup_eq 5 F2 h01
          (by simpa using CFSG.LieType.Universal.SpecialLinear.toStd_single 5 (0 : Fin 5))]
        rw [ggHalfGraphData_slE_eq 0 1 h01]
        exact CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup h01 1
      · rw [hθ 0 1 (by decide)]
        exact hc
  have htorus : ∀ h' ∈ ggTorus (ggU .PSL 6 1).D, θ h' ∈ ggTorus (ggU .E6 0 1).D := by
    intro h' hh'
    have h1 : h' = 1 := by
      have hh'' : h' ∈ ggTorus (CFSG.LieType.Universal.SpecialLinear.rootDatum 5 F2) := hh'
      rw [ggHalfGraphData_torus_bot] at hh''
      exact Subgroup.mem_bot.mp hh''
    have heq : θ h' = 1 := by
      rw [h1]
      exact map_one θ
    rw [heq]
    change (1 : (ggU .E6 0 1).K) ∈ ggTorus (ggU .E6 0 1).D
    exact Subgroup.one_mem _
  have hcompPres : GGCompatPresented (ggU .E6 0 1).D φ (φ.comp θ).range :=
    ggCompatPresented_comp (Δ := (ggU .E6 0 1).D) hker hadmPSL hrkPSL hθinj hδ hγ hroot htorus
  rw [hcomp, h.coords.range₁] at hcompPres
  exact ⟨.E6, 0, 1, φ, hpresG0, L, Or.inl rfl, hcompPres⟩

end GGHalfCtx

end CFSG.StandardType

end
