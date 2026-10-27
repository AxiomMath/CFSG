module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Inner
public import CFSG.LocalAnalysis.StandardType.FS81.RowCent
public import CFSG.LocalAnalysis.StandardType.FS81.ConstructYD6
public import CFSG.LocalAnalysis.StandardType.FS81.D6CentAux
public import CFSG.LocalAnalysis.StandardType.FS81.D6CentAux2

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Pointwise

theorem exists_cent_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.D6 B b₀) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) ∧
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
      Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) ∧
      R ≤ Subgroup.centralizer (K : Set G) ∧
      (∀ x ∈ Subgroup.centralizer ({b₀} : Set G), x ^ 3 = 1 → x ∈ Subgroup.zpowers b₀ ⊔ K) ∧
      ∀ c ∈ Subgroup.centralizer (E : Set G), ¬ 3 ∣ orderOf c → c ∈ R :=
  exists_cent_D6_aux hstd hB hrec

theorem rowCentAt_D6 : RowCentAt Row.D6 := by
  intro G _ _ b₀ K E hstd B hB hrec _hfus
  obtain ⟨R, hRC, hRn, hR3, hCeq, -⟩ := exists_cent_D6 hstd.toLoc hB hrec
  exact ⟨R, hRC, hRn, hR3, hCeq⟩

theorem d6CapAt_holds : D6CapAt := by
  intro G _ _ b₀ K E hstd B hB hrec Y hKY hb₀Y hcap hRY
  obtain ⟨hA, hE, hb₀E, -, -, -⟩ := hstd.2.1
  obtain ⟨hb₀ord, hKC, hKn, hKz, -, hA2, -, -⟩ := hA
  let C := Subgroup.centralizer ({b₀} : Set G)
  let T : Subgroup G := Subgroup.zpowers b₀ ⊔ K
  obtain ⟨R, hRC, hRn, hR3, hCeq, hRCK, h3elem, h3prime⟩ :=
    exists_cent_D6 hstd.toLoc hB hrec
  have hb₀Z : b₀ ∈ C :=
    Subgroup.mem_centralizer_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx])
  have hRZ : R ≤ C ⊓ Subgroup.centralizer (K : Set G) := by
    intro x hx
    exact ⟨hRC hx, hRCK hx⟩
  have hRT : ∀ r ∈ R, ∀ t ∈ T, r * t = t * r :=
    commute_zpowers_sup_K_of_le_inf hRZ
  have hRnormT : R ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro r hr t ht
    rw [hRT r hr t ht]
    simpa using ht
  have hcoe : (↑(R ⊔ T) : Set G) = (R : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right R T hRnormT
  apply le_antisymm
  · intro c hc
    have hcC : c ∈ C := hc.1
    have hcY : c ∈ Y := hc.2
    have hcT : c ∈ R ⊔ T := by rw [← hCeq]; exact hcC
    have hcT' : c ∈ (R : Set G) * (T : Set G) := by
      rw [← hcoe]
      exact hcT
    obtain ⟨r, hr, t, ht, rct⟩ := hcT'
    have hRleY : R ≤ Subgroup.centralizer (Y : Set G) := hRY R hRC hRn hR3
    have hTY : T ≤ Y :=
      sup_le (Subgroup.zpowers_le.mpr hb₀Y) hKY
    have htY : t ∈ Y := hTY ht
    have hrY : r ∈ Y := by
      have : r = c * t⁻¹ := by rw [← rct]; group
      rw [this]
      exact Y.mul_mem hcY (Y.inv_mem htY)
    have hrbot : r ∈ Subgroup.centralizer (Y : Set G) ⊓ Y := ⟨hRleY hr, hrY⟩
    rw [hcap] at hrbot
    have hr1 : r = 1 := by simpa using hrbot
    rw [← rct, hr1]
    simpa using ht
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨Subgroup.zpowers_le.mpr hb₀Z hx, Subgroup.zpowers_le.mpr hb₀Y hx⟩
    · exact le_inf hKC hKY

end CFSG.StandardType.FrameRoute.FS81
