module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd
public import CFSG.LocalAnalysis.StandardType.PhanEFlagBlkMap
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable {M : ChevModel2 D n H Fld}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

theorem hmbS3_range_e_one {L : SLPath M 1} {z : Fin D.rank} (hz : L.e 0 = z) :
    Set.range L.e = ({z} : Set (Fin D.rank)) := by
  ext i
  constructor
  · rintro ⟨k, rfl⟩
    rw [Set.mem_singleton_iff]
    fin_cases k
    exact hz
  · intro hi
    rw [Set.mem_singleton_iff] at hi
    exact ⟨0, by rw [hz, hi]⟩

private theorem hmbS3_leviM_mono {I J : Set (Fin D.rank)} (h : I ⊆ J) :
    leviM D I ≤ leviM D J := by
  rw [leviM, leviM]
  refine iSup₂_le fun i hi => ?_
  exact le_iSup₂_of_le i (h hi) le_rfl

private theorem hmbS3_leviM_union (A B : Set (Fin D.rank)) :
    leviM D (A ∪ B) = leviM D A ⊔ leviM D B := by
  apply le_antisymm
  · rw [leviM]
    refine iSup₂_le fun i hi => ?_
    rcases hi with hi | hi
    · exact le_sup_of_le_left (le_iSup₂_of_le i hi le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl)
  · refine sup_le (hmbS3_leviM_mono Set.subset_union_left)
      (hmbS3_leviM_mono Set.subset_union_right)

private theorem hmbS3_leviM_singleton (z : Fin D.rank) :
    leviM D ({z} : Set (Fin D.rank)) = rankOne D.rootGroup z := by
  apply le_antisymm
  · rw [leviM]
    refine iSup₂_le fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
  · exact le_iSup₂_of_le z rfl le_rfl

theorem hmbS3_eps_mem_rankOne {L : SLPath M 1} {z : Fin D.rank} (hz : L.e 0 = z)
    (A : SpecialLinearGroup (Fin 2) Fld) : L.ε A ∈ rankOne D.rootGroup z := by
  have h := hmbSP_range_eps_le_leviM L (Set.mem_range_self A)
  rw [hmbS3_range_e_one hz, hmbS3_leviM_singleton] at h
  exact h

theorem hmbS3_eps_mem_leviM {L : SLPath M 1} {z : Fin D.rank} (hz : L.e 0 = z)
    {I : Set (Fin D.rank)} (hzI : z ∈ I) (A : SpecialLinearGroup (Fin 2) Fld) :
    L.ε A ∈ leviM D I := by
  refine hmbS3_leviM_mono (Set.singleton_subset_iff.mpr hzI) ?_
  rw [hmbS3_leviM_singleton]
  exact hmbS3_eps_mem_rankOne hz A

private theorem hmbS3_blockSL_one_eq_bot {d : List ℕ} (h0 : (0 : Fin 1) ∉ cutTypes 1 d) :
    blockSL Fld 1 d = ⊥ := by
  have hset : cutTypes 1 d = (∅ : Set (Fin 1)) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    fin_cases k
    exact h0 hk
  rw [blockSL, hset]
  have hemp : {A : SpecialLinearGroup (Fin 2) Fld | ∃ k : Fin 1,
      k ∈ (∅ : Set (Fin 1)) ∧ ∃ c : Fld,
        A = tv Fld k.castSucc k.succ c ∨ A = tv Fld k.succ k.castSucc c} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro A ⟨k, hk, -⟩
    exact hk
  rw [hemp, Subgroup.closure_empty]

theorem hmbS3_eps_mem_leviM_of_mem_blockSL {L : SLPath M 1} {z : Fin D.rank}
    (hz : L.e 0 = z) {I : Set (Fin D.rank)} {dz : List ℕ}
    (hI : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dz)
    (A : SpecialLinearGroup (Fin 2) Fld) (hA : A ∈ blockSL Fld 1 dz) :
    L.ε A ∈ leviM D I := by
  by_cases hzI : z ∈ I
  · exact hmbS3_eps_mem_leviM hz hzI A
  · have hbot := hmbS3_blockSL_one_eq_bot (Fld := Fld) (d := dz) (fun h => hzI ((hI).mpr h))
    have hA1 : A = 1 := Subgroup.mem_bot.mp (hbot ▸ hA)
    rw [hA1, map_one]
    exact Subgroup.one_mem _

private theorem hmbS3_mem_sup_of_commute {A B : Subgroup K}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : K} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure A B] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hyA | hyB
    · exact ⟨y, hyA, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hyB, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y z hy hz ihy ihz =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ihy
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ihz
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  | inv y hy ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev, ← hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]

private theorem hmbS3_commutes_sup_left {A A' B : Subgroup K}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (h' : ∀ x ∈ A', ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ A', ∀ y ∈ B, x * y = y * x := by
  have hA : A ≤ Subgroup.centralizer (B : Set K) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h z hz w hw).symm
  have hA' : A' ≤ Subgroup.centralizer (B : Set K) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h' z hz w hw).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 ((sup_le hA hA') hx) y hy).symm

private theorem hmbS3_image_cutTypes {L : SLPath M 1} {z : Fin D.rank} (hz : L.e 0 = z)
    {I : Set (Fin D.rank)} {d : List ℕ} (hI : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 d) :
    L.e '' cutTypes 1 d = ({z} : Set (Fin D.rank)) ∩ I := by
  ext i
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain rfl : k = 0 := Subsingleton.elim k 0
    exact ⟨hz, by rw [hz]; exact (hI).mpr hk⟩
  · rintro ⟨hiz, hiI⟩
    rw [Set.mem_singleton_iff] at hiz
    subst hiz
    exact ⟨0, (hI).mp hiI, hz⟩

private theorem hmbS3_leviM_eq {Lx Ly Lz : SLPath M 1} {x y z : Fin D.rank}
    {I : Set (Fin D.rank)} {dx dy dz : List ℕ}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z)
    (hIJ : I ⊆ insert z (insert y {x}))
    (hIx : x ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dx)
    (hIy : y ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dy)
    (hIz : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dz) :
    leviM D I = (blockSL Fld 1 dx).map Lx.ε ⊔ (blockSL Fld 1 dy).map Ly.ε ⊔
      (blockSL Fld 1 dz).map Lz.ε := by
  have hIeq : I = ({x} ∩ I) ∪ ({y} ∩ I) ∪ ({z} ∩ I) := by
    ext i
    constructor
    · intro hi
      have hmem := hIJ hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact Or.inr ⟨rfl, hi⟩
      · exact Or.inl (Or.inr ⟨rfl, hi⟩)
      · exact Or.inl (Or.inl ⟨rfl, hi⟩)
    · intro hi
      rcases hi with (hx' | hy') | hz'
      · exact hx'.2
      · exact hy'.2
      · exact hz'.2
  rw [hIeq, hmbS3_leviM_union (({x} ∩ I) ∪ ({y} ∩ I)) ({z} ∩ I),
    hmbS3_leviM_union ({x} ∩ I) ({y} ∩ I),
    ← hmbS3_image_cutTypes hx hIx, ← hmbS3_image_cutTypes hy hIy,
    ← hmbS3_image_cutTypes hz hIz,
    ← map_blockSL Lx dx, ← map_blockSL Ly dy, ← map_blockSL Lz dz]

include hext in
private theorem hmbS3_commute_map_blockSL {L₁ L₂ : SLPath M 1} {z₁ z₂ : Fin D.rank}
    (hz₁ : L₁.e 0 = z₁) (hz₂ : L₂.e 0 = z₂)
    (h2 : coxeterMatrix D.isFiniteType z₁ z₂ = 2) (d₁ d₂ : List ℕ) :
    ∀ a ∈ (blockSL Fld 1 d₁).map L₁.ε, ∀ b ∈ (blockSL Fld 1 d₂).map L₂.ε,
      a * b = b * a := by
  intro a ha b hb
  obtain ⟨A, -, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨B, -, rfl⟩ := Subgroup.mem_map.mp hb
  exact hmbSP_commutes_rankOne hext h2 (L₁.ε A) (hmbS3_eps_mem_rankOne hz₁ A)
    (L₂.ε B) (hmbS3_eps_mem_rankOne hz₂ B)

include hext in
theorem hmbS3_decomp3 {Lx Ly Lz : SLPath M 1} {x y z : Fin D.rank}
    {I : Set (Fin D.rank)} {dx dy dz : List ℕ}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z)
    (hmxy : coxeterMatrix D.isFiniteType x y = 2)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    (hIJ : I ⊆ insert z (insert y {x}))
    (hIx : x ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dx)
    (hIy : y ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dy)
    (hIz : z ∈ I ↔ (0 : Fin 1) ∈ cutTypes 1 dz)
    {l₀ : K} (hl₀ : l₀ ∈ leviM D I) :
    ∃ A₀x ∈ blockSL Fld 1 dx, ∃ A₀y ∈ blockSL Fld 1 dy, ∃ A₀z ∈ blockSL Fld 1 dz,
      l₀ = Lx.ε A₀x * Ly.ε A₀y * Lz.ε A₀z := by
  have hlevi := hmbS3_leviM_eq hx hy hz hIJ hIx hIy hIz
  have hcommAB := hmbS3_commute_map_blockSL (hext := hext) hx hy hmxy dx dy
  have hcommAC := hmbS3_commute_map_blockSL (hext := hext) hx hz hmxz dx dz
  have hcommBC := hmbS3_commute_map_blockSL (hext := hext) hy hz hmyz dy dz
  have hcommABC := hmbS3_commutes_sup_left hcommAC hcommBC
  obtain ⟨ab, hab_mem, c, hc, hsum⟩ := hmbS3_mem_sup_of_commute hcommABC (hlevi ▸ hl₀)
  obtain ⟨a, ha, b, hb, hab_eq⟩ := hmbS3_mem_sup_of_commute hcommAB hab_mem
  obtain ⟨A₀x, hA₀x, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨A₀y, hA₀y, rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨A₀z, hA₀z, rfl⟩ := Subgroup.mem_map.mp hc
  refine ⟨A₀x, hA₀x, A₀y, hA₀y, A₀z, hA₀z, ?_⟩
  rw [← hsum, ← hab_eq]

include hext in
theorem hmbS3_commute3 {Lx Ly Lz : SLPath M 1} {x y z : Fin D.rank}
    (hx : Lx.e 0 = x) (hy : Ly.e 0 = y) (hz : Lz.e 0 = z)
    (hmxz : coxeterMatrix D.isFiniteType x z = 2)
    (hmyz : coxeterMatrix D.isFiniteType y z = 2)
    (Ax Ay Az : SpecialLinearGroup (Fin 2) Fld) :
    Lx.ε Ax * Ly.ε Ay * Lz.ε Az = Lz.ε Az * (Lx.ε Ax * Ly.ε Ay) := by
  have h1 : Lx.ε Ax * Lz.ε Az = Lz.ε Az * Lx.ε Ax :=
    hmbSP_commutes_rankOne hext hmxz (Lx.ε Ax) (hmbS3_eps_mem_rankOne hx Ax)
      (Lz.ε Az) (hmbS3_eps_mem_rankOne hz Az)
  have h2 : Ly.ε Ay * Lz.ε Az = Lz.ε Az * Ly.ε Ay :=
    hmbSP_commutes_rankOne hext hmyz (Ly.ε Ay) (hmbS3_eps_mem_rankOne hy Ay)
      (Lz.ε Az) (hmbS3_eps_mem_rankOne hz Az)
  calc Lx.ε Ax * Ly.ε Ay * Lz.ε Az
      = Lx.ε Ax * (Ly.ε Ay * Lz.ε Az) := by group
    _ = Lx.ε Ax * (Lz.ε Az * Ly.ε Ay) := by rw [h2]
    _ = Lx.ε Ax * Lz.ε Az * Ly.ε Ay := by group
    _ = Lz.ε Az * Lx.ε Ax * Ly.ε Ay := by rw [h1]
    _ = Lz.ε Az * (Lx.ε Ax * Ly.ε Ay) := by group

theorem hmbS3_rearrange_prod {a₁ a₂ b₁ b₂ c₁ c₂ : K}
    (hba : b₁ * a₂ = a₂ * b₁) (hca : c₁ * a₂ = a₂ * c₁) (hcb : c₁ * b₂ = b₂ * c₁) :
    a₁ * b₁ * c₁ * a₂ * b₂ * c₂ = a₁ * a₂ * b₁ * b₂ * c₁ * c₂ := by
  calc a₁ * b₁ * c₁ * a₂ * b₂ * c₂
      = a₁ * b₁ * (c₁ * a₂) * b₂ * c₂ := by group
    _ = a₁ * b₁ * (a₂ * c₁) * b₂ * c₂ := by rw [hca]
    _ = a₁ * (b₁ * a₂) * c₁ * b₂ * c₂ := by group
    _ = a₁ * (a₂ * b₁) * c₁ * b₂ * c₂ := by rw [hba]
    _ = a₁ * a₂ * b₁ * (c₁ * b₂) * c₂ := by group
    _ = a₁ * a₂ * b₁ * (b₂ * c₁) * c₂ := by rw [hcb]
    _ = a₁ * a₂ * b₁ * b₂ * c₁ * c₂ := by group

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
