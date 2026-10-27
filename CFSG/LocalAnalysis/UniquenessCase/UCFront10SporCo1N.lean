module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1J
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMathieu
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OrbitCentralizer
public import CFSG.GroupTheory.ConjClassCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2 CFSG.Blueprint
  CFSG.EvenSporadicStandard.TwoCo1 CFSG.QuasithinUnique

attribute [local irreducible] rho rhoGL phiOf theta iota epsHom

theorem normalizer_epsHom_range_le_theta_range :
    Subgroup.normalizer (epsHom.range : Set NativeSporadic.Co1) ≤ theta.range := by
  classical
  have : Finite NativeSporadic.Co1 := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
  intro g hg
  have hE0 : epsMask eMaskC ∈ epsHom.range := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := (Subgroup.mem_normalizer_iff.1 hg (epsMask eMaskC)).1 hE0
  have hε0 : epsMask eMaskC ≠ 1 := by
    have h := epsC_facts.1
    intro h1
    rw [h1, orderOf_one] at h
    omega
  have hy1 : y ≠ 1 := by
    intro h1
    apply hε0
    have h3 : g * epsMask eMaskC * g⁻¹ = 1 := by rw [← hy, h1, map_one]
    calc epsMask eMaskC = g⁻¹ * (g * epsMask eMaskC * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  have hy0 : Multiplicative.toAdd y ≠ 0 := by
    intro h0
    exact hy1 (by rw [← ofAdd_toAdd y, h0, ofAdd_zero])
  rcases orbit_cover (Multiplicative.toAdd y) hy0 with hA | hC
  · obtain ⟨p, hp⟩ := hA
    have hiA : iota p * epsMask eMaskA * (iota p)⁻¹ =
        epsHom (Multiplicative.ofAdd (rho p (toVecD 11 eMaskA))) := by
      rw [epsMask, iota_conj, toAdd_ofAdd]
    have hconjA : g * epsMask eMaskC * g⁻¹ = iota p * epsMask eMaskA * (iota p)⁻¹ := by
      rw [← hy, ← ofAdd_toAdd y, ← hp]
      exact hiA.symm
    exfalso
    have hconj : IsConj (epsMask eMaskA) (epsMask eMaskC) :=
      isConj_iff.2 ⟨g⁻¹ * iota p, by
        calc (g⁻¹ * iota p) * epsMask eMaskA * (g⁻¹ * iota p)⁻¹
            = g⁻¹ * (iota p * epsMask eMaskA * (iota p)⁻¹) * g := by group
          _ = g⁻¹ * (g * epsMask eMaskC * g⁻¹) * g := by rw [hconjA]
          _ = epsMask eMaskC := by group⟩
    have h1 := card_centralizer_epsC
    have h2 := card_centralizer_Theta_epsA
    have h3 := CFSG.GroupTheory.card_centralizer_eq_of_isConj hconj
    have h4 : Nat.card (Subgroup.centralizer ({epsMask eMaskA} : Set NativeSporadic.Co1)) =
        389283840 := h3.trans h1
    have h5 : Nat.card ↥(Subgroup.centralizer ({epsMask eMaskA} : Set NativeSporadic.Co1) ⊓
        theta.range) ≤
        Nat.card (Subgroup.centralizer ({epsMask eMaskA} : Set NativeSporadic.Co1)) :=
      Subgroup.card_le_of_le inf_le_left
    rw [h2, h4] at h5
    norm_num at h5
  · obtain ⟨p, hp⟩ := hC
    have hiC : iota p * epsMask eMaskC * (iota p)⁻¹ =
        epsHom (Multiplicative.ofAdd (rho p (toVecD 11 eMaskC))) := by
      rw [epsMask, iota_conj, toAdd_ofAdd]
    have hconjC : g * epsMask eMaskC * g⁻¹ = iota p * epsMask eMaskC * (iota p)⁻¹ := by
      rw [← hy, ← ofAdd_toAdd y, ← hp]
      exact hiC.symm
    have hc : (iota p)⁻¹ * g ∈
        Subgroup.centralizer ({epsMask eMaskC} : Set NativeSporadic.Co1) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul]
      calc (iota p)⁻¹ * g * epsMask eMaskC * ((iota p)⁻¹ * g)⁻¹
          = (iota p)⁻¹ * (g * epsMask eMaskC * g⁻¹) * iota p := by group
        _ = (iota p)⁻¹ * (iota p * epsMask eMaskC * (iota p)⁻¹) * iota p := by rw [hconjC]
        _ = epsMask eMaskC := by group
    have hcθ : (iota p)⁻¹ * g ∈ theta.range := centralizer_epsC_le_theta_range hc
    have hip : iota p ∈ theta.range := ⟨SemidirectProduct.inr p, theta_inr p⟩
    have hg' : g = iota p * ((iota p)⁻¹ * g) := by group
    rw [hg']
    exact theta.range.mul_mem hip hcθ

theorem k105In_normalizer_epsHom_range :
    K105In (Subgroup.normalizer (epsHom.range : Set NativeSporadic.Co1)) co1Sylow := by
  intro Y hSY hYN hYs hY3
  have hYtheta : Y ≤ theta.range := hYN.trans normalizer_epsHom_range_le_theta_range
  have hmap : (Y.comap theta).map theta = Y := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hYtheta
  have hcard : Nat.card (Y.comap theta) = Nat.card Y := by
    have h1 : Nat.card ((Y.comap theta).map theta) = Nat.card (Y.comap theta) :=
      Subgroup.card_map_of_injective theta_injective
    rw [← h1, hmap]
  have hYs' : Group.IsSolvable ↥(Y.comap theta) := by
    have : Group.IsSolvable ↥Y := hYs
    have hf : ∀ s : ↥(Y.comap theta), theta (s : SM24) ∈ Y := by
      intro s
      have h : theta (s : SM24) ∈ (Y.comap theta).map theta := ⟨s, s.2, rfl⟩
      rwa [hmap] at h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (theta.comp (Y.comap theta).subtype).codRestrict Y hf)
      (fun a b h => Subtype.ext (theta_injective (congrArg Subtype.val h)))
  let W : Subgroup PM24 := (Y.comap theta).map (SemidirectProduct.rightHom : SM24 →* PM24)
  have hWsol : Group.IsSolvable ↥W := by
    have : Group.IsSolvable ↥(Y.comap theta) := hYs'
    exact Group.isSolvable_of_surjective
      (f := (SemidirectProduct.rightHom : SM24 →* PM24).subgroupMap (Y.comap theta))
      (MonoidHom.subgroupMap_surjective _ _)
  have ht24W : t24 ≤ W := by
    intro q hq
    have hqY : theta (SemidirectProduct.inr q) ∈ Y :=
      hSY ((theta_mem_co1Sylow_iff (SemidirectProduct.inr q)).2 (by simpa using hq))
    rw [← hmap] at hqY
    obtain ⟨s, hs, hst⟩ := hqY
    have hsinr : s = SemidirectProduct.inr q := theta_injective hst
    exact ⟨s, hs, by rw [hsinr, SemidirectProduct.rightHom_inr]⟩
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    exact hY3 (hcard ▸ h3.trans (Subgroup.card_map_dvd (Y.comap theta) _))
  have : Finite PM24 :=
    Nat.finite_of_card_ne_zero (by rw [natCard_PM24]; norm_num)
  have hspor : IsSpor PM24 .M24 := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
    exact ⟨e.symm⟩
  have hWt : W ≤ t24 :=
    k105SporAt_M24 (X := PM24) hspor t24 W isSylowTwoOf_t24 ht24W hWsol hW3
  have hY'le : Y.comap theta ≤
      t24.comap (SemidirectProduct.rightHom : SM24 →* PM24) := by
    intro s hs
    exact hWt ⟨s, hs, rfl⟩
  calc Y = (Y.comap theta).map theta := hmap.symm
    _ ≤ (t24.comap (SemidirectProduct.rightHom : SM24 →* PM24)).map theta :=
        Subgroup.map_mono hY'le
    _ = co1Sylow := rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
