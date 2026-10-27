module

public import CFSG.RankThree.GF2n.Tim79aSec25

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem mem_wOf_of_centralizes_gen {v : G} (hv : v ∈ V)
    (hvc : ∀ w ∈ wOf V H, v * w = w * v) : v ∈ wOf V H := by
  by_contra hvW
  have hvH : v ∈ H := hc.V_le_H hv
  set C : Subgroup G := Subgroup.centralizer (wOf V H : Set G) ⊓ xOf V H
  have hCconj : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C := by
    intro h hh c hcC
    obtain ⟨hcZ, hcX⟩ := Subgroup.mem_inf.mp hcC
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer (H_le_normalizer_wOf V H hh)) c).mp hcZ
    · exact (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H hh) c).mp hcX
  have hNconj : ∀ y : Hbar V H, ∀ n ∈ barOf V H C, y * n * y⁻¹ ∈ barOf V H C := by
    intro y n hn
    obtain ⟨h, rfl⟩ := piBar_surjective V H y
    obtain ⟨c, hcC, rfl⟩ := mem_barOf_iff.mp hn
    refine mem_barOf_iff.mpr ⟨h * c * h⁻¹, ?_, by simp⟩
    have : ((h * c * h⁻¹ : ↥H) : G) = (h : G) * c * (h : G)⁻¹ := by simp
    rw [this]
    exact hCconj h h.2 c hcC
  have hv1 : piBar V H ⟨v, hvH⟩ ≠ 1 := fun h => hvW ((piBar_eq_one_iff _).1 h)
  have hvC : piBar V H ⟨v, hvH⟩ ∈ barOf V H C := by
    refine mem_barOf_iff.mpr ⟨⟨v, hvH⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => (hvc w hw).symm
    · exact le_xOf (V_mem_omegaOf V H) hv
  have hvD : piBar V H ⟨v, hvH⟩ ∈ dbarOf V H :=
    hc.barOf_V_subset_dbarOf (mem_barOf_iff.mpr ⟨⟨v, hvH⟩, hv, rfl⟩) hv1
  obtain ⟨d₀, -, hcls⟩ := hc.dbarOf_isClass
  obtain ⟨x₁, -, hvx⟩ := (hcls _).1 hvD
  have hd₀C : d₀ ∈ barOf V H C := by
    have := hNconj x₁⁻¹ _ hvC
    rwa [hvx, show x₁⁻¹ * (x₁ * d₀ * x₁⁻¹) * x₁⁻¹⁻¹ = d₀ by group] at this
  have hDC : dbarOf V H ⊆ (barOf V H C : Set (Hbar V H)) := fun y hy => by
    obtain ⟨x, -, rfl⟩ := (hcls y).1 hy
    exact hNconj x d₀ hd₀C
  have hXC : barOf V H (xOf V H) ≤ barOf V H C := by
    rw [← hc.closure_dbarOf]
    exact (Subgroup.closure_le _).2 hDC
  have hXc : ∀ x ∈ xOf V H, ∀ w ∈ wOf V H, w * x = x * w := by
    intro x hx w hw
    have hxH : x ∈ H := xOf_le_H hc.V_le_H hx
    obtain ⟨c, hcC, hcx⟩ := mem_barOf_iff.mp (hXC (mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩))
    obtain ⟨hcZ, -⟩ := Subgroup.mem_inf.mp hcC
    have h1 : piBar V H (c⁻¹ * ⟨x, hxH⟩) = 1 := by rw [map_mul, map_inv, hcx]; simp
    have h2 : (c : G)⁻¹ * x ∈ wOf V H := by simpa using (piBar_eq_one_iff _).1 h1
    have h3 : ((c : G)⁻¹ * x) * w = w * ((c : G)⁻¹ * x) := hc.wOf_isElemAbelian.comm h2 hw
    have h4 : w * (c : G) = c * w := Subgroup.mem_centralizer_iff.mp hcZ w hw
    calc w * x = (w * c) * ((c : G)⁻¹ * x) := by group
      _ = c * (w * ((c : G)⁻¹ * x)) := by rw [h4]; group
      _ = c * (((c : G)⁻¹ * x) * w) := by rw [h3]
      _ = x * w := by group
  have hWle : wOf V H ≤ wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) :=
    le_inf le_rfl fun w hw =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => (hXc x hx w hw).symm
  rw [hc.wOf_inf_centralizer_xOf_eq_bot, le_bot_iff] at hWle
  apply hc.V_inf_wOf_ne_bot
  rw [hWle, inf_bot_eq]

theorem commutator_mem_wOf_of_centralizes_gen {c : G} (hcH : c ∈ H)
    (hcW : ∀ w ∈ wOf V H, c * w = w * c) :
    ∀ y ∈ xOf V H, ⁅c, y⁆ ∈ wOf V H := by
  have hcZ : c ∈ Subgroup.centralizer (wOf V H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun w hw => (hcW w hw).symm
  have hVC : ∀ h ∈ H, ∀ y ∈ conjSubgroup h V, ⁅c, y⁆ ∈ wOf V H := by
    intro h hh y hy
    have hyH : y ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hh hy
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.conj_inf_wOf_ne_bot hh)
    obtain ⟨hbB, hbW⟩ := Subgroup.mem_inf.mp hb
    have hcN : c ∈ Subgroup.normalizer (conjSubgroup h V : Set G) :=
      Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti h) hbB
        (fun h' => hb1 (Subtype.ext h')) (hcW b hbW)
    have hzB : ⁅c, y⁆ ∈ conjSubgroup h V :=
      (conjSubgroup h V).mul_mem ((Subgroup.mem_normalizer_iff.mp hcN y).mp hy)
        ((conjSubgroup h V).inv_mem hy)
    have hzZ : ⁅c, y⁆ ∈ Subgroup.centralizer (wOf V H : Set G) := by
      have hyN : y ∈ Subgroup.normalizer
          (Subgroup.centralizer (wOf V H : Set G) : Set G) :=
        mem_normalizer_centralizer (H_le_normalizer_wOf V H hyH)
      have h2 : y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (wOf V H : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hyN _).mp (Subgroup.inv_mem _ hcZ)
      have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hcZ h2
    generalize ⁅c, y⁆ = z at hzB hzZ ⊢
    have hu : h⁻¹ * z * h ∈ V := mem_conjSubgroup.mp hzB
    have hu' : h⁻¹ * z * h ∈ wOf V H := by
      refine hc.mem_wOf_of_centralizes_gen hu fun w hw => ?_
      have hw₀ : h * w * h⁻¹ ∈ wOf V H := (hc.wOf_conj_facts hh).2.2 h hh w hw
      have hcomm := Subgroup.mem_centralizer_iff.mp hzZ _ hw₀
      calc h⁻¹ * z * h * w = h⁻¹ * (z * (h * w * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * w * h⁻¹) * z) * h := by rw [hcomm]
        _ = w * (h⁻¹ * z * h) := by group
    have := (hc.wOf_conj_facts hh).2.2 h hh _ hu'
    have e : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
    rwa [e] at this
  let C : Subgroup ↥H :=
    (Subgroup.centralizer ({piBar V H ⟨c, hcH⟩} : Set (Hbar V H))).comap (piBar V H)
  have hCmem : ∀ y : ↥H, y ∈ C ↔ ⁅c, (y : G)⁆ ∈ wOf V H := by
    intro y
    have h1 : piBar V H ⁅(⟨c, hcH⟩ : ↥H), y⁆ = ⁅piBar V H ⟨c, hcH⟩, piBar V H y⁆ :=
      map_commutatorElement _ _ _
    have h2 : ((⁅(⟨c, hcH⟩ : ↥H), y⁆ : ↥H) : G) = ⁅c, (y : G)⁆ := rfl
    rw [← h2, ← piBar_eq_one_iff, h1, commutatorElement_eq_one_iff_mul_comm,
      Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hXC : xOf V H ≤ C.map H.subtype := iSup₂_le fun U hU => by
    obtain ⟨h, hh, rfl⟩ := hU
    intro y hy
    have hyH : y ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hh hy
    exact ⟨⟨y, hyH⟩, (hCmem _).2 (hVC h hh y hy), rfl⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hXC hy
  exact (hCmem y').1 hy'

theorem cPbar_eq_inf_centralizer :
    cPbar V H P = P ⊓ Subgroup.centralizer (wOf V H : Set G) := by
  refine le_antisymm (fun c hcP => ?_) (fun c hcP => ?_)
  · refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcP).1, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (hc.cPbar_centralizes_wOf hcP w hw).symm
  · obtain ⟨hcP', hcZ⟩ := Subgroup.mem_inf.mp hcP
    refine Subgroup.mem_inf.mpr ⟨hcP', hc.PleH hcP', ?_⟩
    exact hc.commutator_mem_wOf_of_centralizes_gen (hc.PleH hcP') fun w hw =>
      (Subgroup.mem_centralizer_iff.mp hcZ w hw).symm

theorem exists_noncomm_conj (hd : Sec23Data V H) :
    ∃ g ∈ xOf V H, ∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hdV, hdW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  set dd : ↥H := ⟨d, hc.V_le_H hdV⟩
  have hd1 : piBar V H dd ≠ 1 := fun h => hdW ((piBar_eq_one_iff _).1 h)
  have hdV' : piBar V H dd ∈ barOf V H V := mem_barOf_iff.mpr ⟨dd, hdV, rfl⟩
  have hdD : piBar V H dd ∈ dbarOf V H := hc.barOf_V_subset_dbarOf hdV' hd1
  have hcomm : ∀ y ∈ dbarOf V H, piBar V H dd * y = y * piBar V H dd := by
    intro y hy
    obtain ⟨d₀, -, hcls⟩ := hc.dbarOf_isClass
    obtain ⟨x₀, hx₀, hdx₀⟩ := (hcls _).1 hdD
    obtain ⟨x₁, hx₁, hyx₁⟩ := (hcls _).1 hy
    obtain ⟨g, hgX, hgx⟩ := mem_barOf_iff.mp
      ((barOf V H (xOf V H)).mul_mem hx₁ ((barOf V H (xOf V H)).inv_mem hx₀))
    have hgy : y = piBar V H (g * dd * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hgx, hdx₀, hyx₁]; group
    have hmem : (g : G) * d * (g : G)⁻¹ ∈ conjSubgroup (g : G) V := by
      rw [mem_conjSubgroup]
      have e : (g : G)⁻¹ * ((g : G) * d * (g : G)⁻¹) * (g : G) = d := by group
      rw [e]
      exact hdV
    have hW : ((⁅dd, g * dd * g⁻¹⁆ : ↥H) : G) ∈ wOf V H := hcon g hgX d hdV _ hmem
    have h1 : piBar V H ⁅dd, g * dd * g⁻¹⁆ = 1 := (piBar_eq_one_iff _).2 hW
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, ← hgy] at h1
    exact h1
  set v : Xbar V H := ⟨piBar V H dd, barOf_V_le V H hdV'⟩
  have hvcen : v ∈ Subgroup.center (Xbar V H) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : z ∈ Subgroup.closure (Dy V H) := by
      rw [hd.gen]; exact Subgroup.mem_top z
    have hle : Subgroup.closure (Dy V H) ≤ Subgroup.centralizer ({v} : Set (Xbar V H)) := by
      refine (Subgroup.closure_le _).2 fun y hy => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hcomm (y : Hbar V H) hy).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  exact hd.noncentral v hdD hvcen

end MinCex

end CFSG.RankThree.GF2n.Tim79a
