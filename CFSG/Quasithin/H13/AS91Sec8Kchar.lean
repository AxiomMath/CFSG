module

public import CFSG.Quasithin.H13.AS91Sec5Line
public import CFSG.Quasithin.H13.AS91Sec8Defs
public import CFSG.Quasithin.H13.AS91Sec8Perm5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshGL3Facts
public import CFSG.Quasithin.H13.AS91Sec5Eltr

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem exists_derived_mul_R (k : ↥c.K) :
    ∃ a ∈ derivedSeries ↥c.K 2, (a : G)⁻¹ * (k : G) ∈ c.R := by
  obtain ⟨φ, hφs, hφk⟩ := c.K_quot
  have hperf : ∀ m, derivedSeries (GL (Fin 3) (ZMod 2)) m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero _
    | succ m ih =>
      rw [derivedSeries_succ, ih, ← commutator_def]
      exact CFSG.EvenSporadicStandard.M12Std.Yosh.commutator_gl32
  have hmap : (derivedSeries ↥c.K 2).map φ = ⊤ := by rw [map_derivedSeries_eq hφs, hperf]
  have hk : φ k ∈ (derivedSeries ↥c.K 2).map φ := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨a, ha, haφ⟩ := Subgroup.mem_map.mp hk
  refine ⟨a, ha, ?_⟩
  have h1 : a⁻¹ * k ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, haφ, inv_mul_cancel]
  rw [hφk, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem kchar' (hJ : HypJ4 G z) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0)
    (M : Subgroup G) (hM : M = c.G1 ⊓ stabilizer G y) (hLU : c.G1 ⊓ stabilizer G y ≤ c.G2)
    (φ : ↥M ≃* ↥M) (k : ↥M) (hk : (k : G) ∈ c.K) : ((φ k : ↥M) : G) ∈ c.K := by
  classical
  have hMG2 : M ≤ c.G2 := by
    rw [hM]
    exact hLU
  have hMx : ∀ m ∈ M, m • c.x0 = c.x0 := fun m hm => by
    rw [hM] at hm
    have : m ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact (Subgroup.mem_inf.mp hm).1
    exact mem_stabilizer_iff.mp this
  have hMy : ∀ m ∈ M, m • y = y := fun m hm => by
    rw [hM] at hm
    exact mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hm).2
  have hKM : c.K ≤ M := fun x hx => by
    rw [hM]
    exact Subgroup.mem_inf.mpr ⟨c.K_le_G1 hx, c.K_le_stab hy hx⟩
  let ρ : ↥M →* Equiv.Perm ↥c.ptsL := (residuePerm c.G1 c.G2).comp (Subgroup.inclusion hMG2)
  have hρ : ∀ (m : ↥M) (q : ↥c.ptsL),
      ((ρ m q : ↥c.ptsL) : G ⧸ c.G1) = (m : G) • (q : G ⧸ c.G1) := fun m q =>
    residuePerm_apply c.G1 c.G2 (Subgroup.inclusion hMG2 m) q
  let X0 : ↥c.ptsL := ⟨c.x0, c.x0_mem_ptsL⟩
  let Y0 : ↥c.ptsL := ⟨y, hy⟩
  have hne : X0 ≠ Y0 := fun h => hyx (congrArg Subtype.val h).symm
  have hfix : ∀ m : ↥M, ρ m X0 = X0 ∧ ρ m Y0 = Y0 := fun m =>
    ⟨Subtype.ext (by rw [hρ]; exact hMx m m.2), Subtype.ext (by rw [hρ]; exact hMy m m.2)⟩
  have hsurj : ∀ σ : Equiv.Perm ↥c.ptsL, σ X0 = X0 → σ Y0 = Y0 → ∃ m, ρ m = σ := by
    intro σ hσx hσy
    obtain ⟨s, hsCZ, hs⟩ := c.exists_CZ_perm σ
    have hsx : s • c.x0 = c.x0 := by
      have := hs X0
      rw [hσx] at this
      exact this
    have hsy : s • y = y := by
      have := hs Y0
      rw [hσy] at this
      exact this
    have hsM : s ∈ M := by
      rw [hM]
      refine Subgroup.mem_inf.mpr ⟨?_, mem_stabilizer_iff.mpr hsy⟩
      rw [← c.stab_x0]
      exact mem_stabilizer_iff.mpr hsx
    refine ⟨⟨s, hsM⟩, Equiv.ext fun q => Subtype.ext ?_⟩
    rw [hρ]
    exact hs q
  obtain ⟨hA, hB⟩ := perm5_stab2_aux c.card_ptsL ρ X0 Y0 hne hfix hsurj
  have hkerK : ∀ m : ↥M, m ∈ ρ.ker → (m : G) ∈ c.K := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    refine (c.kernel_ptsL m (hMG2 m.2)).mp fun p hp => ?_
    have := congrArg (fun f : Equiv.Perm ↥c.ptsL => ((f ⟨p, hp⟩ : ↥c.ptsL) : G ⧸ c.G1)) hm
    simp only [Equiv.Perm.coe_one, id_eq] at this
    rw [hρ] at this
    exact this
  obtain ⟨a, ha, har⟩ := c.exists_derived_mul_R ⟨k, hk⟩
  let ι : ↥c.K →* ↥M := Subgroup.inclusion hKM
  have haM : ι a ∈ derivedSeries ↥M 2 :=
    map_derivedSeries_le_derivedSeries ι 2 (Subgroup.mem_map_of_mem ι ha)
  let r : ↥M := (ι a)⁻¹ * k
  have hrR : (r : G) ∈ c.R := by
    show ((a : G))⁻¹ * (k : G) ∈ c.R
    exact har
  have hkar : k = ι a * r := by
    show k = ι a * ((ι a)⁻¹ * k)
    simp
  have hφa : φ (ι a) ∈ derivedSeries ↥M 2 :=
    map_derivedSeries_le_derivedSeries φ.toMonoidHom 2 (Subgroup.mem_map_of_mem φ.toMonoidHom haM)
  have hφaK : ((φ (ι a) : ↥M) : G) ∈ c.K := hkerK _ (hA hφa)
  let P : Subgroup ↥M := c.R.subgroupOf M
  haveI hPn : P.Normal := ⟨fun n hn m => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using c.R_conj_G2 (hMG2 m.2) hn⟩
  have hRM : c.R ≤ M := (c.R_le_K).trans hKM
  have hPp : IsPGroup 2 P := by
    refine IsPGroup.of_card (n := 15) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, c.card_R]
  haveI : (P.map φ.toMonoidHom).Normal := hPn.map φ.toMonoidHom φ.surjective
  have hφP : IsPGroup 2 (P.map φ.toMonoidHom) := hPp.map φ.toMonoidHom
  have hφr : φ r ∈ P.map φ.toMonoidHom :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (by rw [Subgroup.mem_subgroupOf]; exact hrR)
  have hφrK : ((φ r : ↥M) : G) ∈ c.K := hkerK _ (hB _ inferInstance hφP hφr)
  rw [hkar, map_mul]
  exact mul_mem hφaK hφrK

end Loc49

theorem stmt8_Kchar_of (h : Stmt5_LineU) : Stmt8_Kchar := by
  intro G _ _ z hJ c y hy hyx φ k hk
  exact c.kchar' hJ hy hyx (stabilizer G c.x0 ⊓ stabilizer G y)
    (by rw [c.stab_x0]) (h G z hJ c y hy hyx) φ k hk

end CFSG.Quasithin.H13.AS91
