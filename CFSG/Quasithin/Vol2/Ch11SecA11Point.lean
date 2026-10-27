module

public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11SecAFacts11

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem le_centralizer_of_perfect {X U Z : Subgroup G} (hperf : ⁅X, X⁆ = X)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hXZ : X ≤ Subgroup.centralizer (Z : Set G))
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hact : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ Z) :
    X ≤ Subgroup.centralizer (U : Set G) := by
  rw [← hperf, Subgroup.commutator_le]
  intro x hx y hy
  have hconj : ∀ {x : G}, x ∈ X → ∀ {z : G}, z ∈ Z → x * z * x⁻¹ = z := by
    intro x hx z hz
    rw [← Subgroup.mem_centralizer_iff.mp (hXZ hx) z hz, mul_inv_cancel_right]
  have key : ∀ u ∈ U, (x * y) * u * (x * y)⁻¹ = (y * x) * u * (y * x)⁻¹ := by
    intro u hu
    have haZ := hact x hx u hu
    have hbZ := hact y hy u hu
    have e1 : (x * y) * u * (x * y)⁻¹ =
        (x * (y * u * y⁻¹ * u⁻¹) * x⁻¹) * (x * u * x⁻¹ * u⁻¹) * u := by group
    have e2 : (y * x) * u * (y * x)⁻¹ =
        (y * (x * u * x⁻¹ * u⁻¹) * y⁻¹) * (y * u * y⁻¹ * u⁻¹) * u := by group
    rw [e1, e2, hconj hx hbZ, hconj hy haZ, hZ _ hbZ _ haZ]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hyx : (y * x)⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.inv_mem _ (hXU (X.mul_mem hy hx))
  have hw : (y * x)⁻¹ * u * ((y * x)⁻¹)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hyx u).mp hu
  rw [inv_inv] at hw
  have h1 := key _ hw
  have h2 : (y * x) * ((y * x)⁻¹ * u * (y * x)) * (y * x)⁻¹ = u := by group
  rw [h2] at h1
  calc u * ⁅x, y⁆ = (x * y) * ((y * x)⁻¹ * u * (y * x)) * (x * y)⁻¹ * ⁅x, y⁆ := by rw [h1]
    _ = ⁅x, y⁆ * u := by rw [commutatorElement_def]; group

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lOf_one_le_centralizer (hF : Facts11) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {U : Subgroup G} (hU : IsVi T L I n 1 U) :
    LOf L U ≤ Subgroup.centralizer (U : Set G) := by
  have hLV := L_le_normalizer_fsuV h
  have hUV := IsVi.le_fsuV hU
  have hflag := isFlagW_of_isVi h hU
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  have hpt : ∀ g ∈ perfectCore (autOn L (fsuV T I) ⊓ stabW (U.subgroupOf (fsuV T I))),
      ∀ u ∈ U.subgroupOf (fsuV T I),
        g u * u⁻¹ ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
      ⟨-, -, -, -, -, hG2⟩
    · exact hF.pointSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
    · exact hF.pointSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
    · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
      exact hF.pointG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
  set X := L ⊓ Subgroup.normalizer (U : Set G) with hXdef
  have hX : X ≤ Subgroup.normalizer (fsuV T I : Set G) := inf_le_left.trans hLV
  have hPX : perfectCore X ≤ X := iInf_le (derivedSeriesOf X) 0
  have hautOn : autOn (perfectCore X) (fsuV T I) =
      perfectCore (autOn L (fsuV T I) ⊓ stabW (U.subgroupOf (fsuV T I))) := by
    rw [autOn_perfectCore hX, autOn_inf_normalizer hUV]
  have hcomm : ∀ a ∈ fsuV T I, ∀ b ∈ fsuV T I, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElemAbelian_fsuV h).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine le_centralizer_of_perfect (Z := fsuV T I ⊓ Subgroup.centralizer (L : Set G))
    (perfectCore_perfect X) (hPX.trans inf_le_right) ?_ ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 x (Subgroup.mem_inf.mp (hPX hx)).1).symm
  · intro a ha b hb
    exact hcomm a ha.1 b hb.1
  · intro x hx u hu
    have hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G) := hX (hPX hx)
    have hg := conjV_mem_autOn hx hxV
    rw [hautOn] at hg
    have h1 := hpt _ hg ⟨u, hUV hu⟩ hu
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : x * u * x⁻¹ * u⁻¹ ∈ fsuV T I :=
      (fsuV T I).mul_mem ((Subgroup.mem_normalizer_iff.mp hxV u).mp (hUV hu))
        ((fsuV T I).inv_mem (hUV hu))
    refine ⟨h2, ?_⟩
    simpa [conjV_apply_coe] using h1

end CFSG.Quasithin.Vol2.Ch11.SecA
