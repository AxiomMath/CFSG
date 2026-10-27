module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Mod2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.C56

variable {G : Type} [Group G]

theorem relIndex_sup_zpowers_le_two {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) (hg2 : g ^ 2 ∈ U) :
    U.relIndex (U ⊔ Subgroup.zpowers g) ∣ 2 := by
  have hn : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set G) := Subgroup.zpowers_le.mpr hg
  rw [Subgroup.relIndex_dvd_two_iff]
  refine ⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g), fun b hb => ?_⟩
  obtain ⟨u, hu, c, hc, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hn).mp hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : g ^ (2 : ℤ) ∈ U := by simpa using hg2
  have hk : g ^ k = (g ^ (2 : ℤ)) ^ (k / 2) * g ^ (k % 2) := by
    rw [← zpow_mul, ← zpow_add, Int.mul_ediv_add_emod]
  have hm : (g ^ (2 : ℤ)) ^ (k / 2) ∈ U := U.zpow_mem h2 _
  rcases Int.emod_two_eq_zero_or_one k with hr | hr
  · right
    rw [hk, hr]
    simpa using U.mul_mem hu hm
  · left
    rw [hk, hr, zpow_one, mul_assoc, mul_assoc, ← sq]
    exact U.mul_mem hu (U.mul_mem hm hg2)

theorem relIndex_ne_zero' [Finite G] (E K : Subgroup G) : E.relIndex K ≠ 0 := by
  intro h
  have := Subgroup.relIndex_dvd_card (H := E) (K := K)
  rw [h] at this
  exact Nat.card_pos.ne' (zero_dvd_iff.mp this)

theorem relIndex_le_of_le [Finite G] {E I U : Subgroup G} (hIU : I ≤ U) :
    E.relIndex I ≤ E.relIndex U :=
  Subgroup.relIndex_le_of_le_right hIU (relIndex_ne_zero' E U)

theorem exists_mul_of_relIndex_two {N T : Subgroup G} (h : N.relIndex T = 2) {u v : G}
    (hu : u ∈ T) (hv : v ∈ T) (hun : u ∉ N) (hvn : v ∉ N) : u⁻¹ * v ∈ N := by
  have h2 : (N.subgroupOf T).index = 2 := h
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp h2
  have hu' := ha ⟨u, hu⟩
  have hv' := ha ⟨v, hv⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hu' hv'
  unfold Xor at hu' hv'
  have h1 : (a : G) * u ∈ N := by tauto
  have h2' : (a : G) * v ∈ N := by tauto
  have := N.mul_mem (N.inv_mem h1) h2'
  simpa [mul_assoc] using this

theorem mem_normalizer_of_sec {X E F U : Subgroup G} (hs : IsSec X E F) (hEU : E ≤ U)
    (hUF : U ≤ F) {g : G} (hg : g ∈ F) : g ∈ Subgroup.normalizer (U : Set G) := by
  have key : ∀ g ∈ F, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have h1 : g * u * g⁻¹ * u⁻¹ ∈ E := hs.comm g hg u (hUF hu)
    have := U.mul_mem (hEU h1) hu
    simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key g hg u, fun hu => ?_⟩
  have := key g⁻¹ (F.inv_mem hg) _ hu
  simpa [mul_assoc] using this

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
