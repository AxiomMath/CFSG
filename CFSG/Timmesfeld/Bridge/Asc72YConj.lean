module

public import CFSG.Timmesfeld.Bridge.Asc72YTri

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] {D : Set G}

theorem false_of_eq_mul_of_not_reach (hS : Setup G D) {u w z r s : G} (hu : u ∈ D)
    (hw : w ∈ D) (huz : Commute u z) (hwz : Commute w z) (huw : ¬ Reach D u w) (hr : r ∈ D)
    (hs : s ∈ D) (hrs : r ≠ s) (hc : Commute r s) (heq : z = r * s) : False := by
  subst heq
  have h1 := ((hS.oddT.commute_mul_iff hr hs hu hrs hc).mp huz).1
  have h2 := ((hS.oddT.commute_mul_iff hr hs hw hrs hc).mp hwz).1
  exact huw (reach_trans (reach_of_commute hu hr h1) (reach_of_commute hr hw h2.symm))

section Local

variable [Finite G]
  (hS : Setup G D) {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
  (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
  (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
    (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n)
include hS htri hn hord huw hO2

theorem localGroup_involution_cases {t : G} (htH : t ∈ localGroup D ((u * v * w) ^ n))
    (htt : t * t = 1) :
    t = 1 ∨ t = (u * v * w) ^ n ∨ t ∈ centSet D ((u * v * w) ^ n) ∨
      t * (u * v * w) ^ n ∈ centSet D ((u * v * w) ^ n) := by
  obtain ⟨hzz, -, -, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  obtain ⟨hu', hv', -, huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have hzH := thirdKind_z_mem_localGroup hS htri hn hord
  have hSH := localSetup hS htri hn hord huw
  have hdiscH := localSet_disconnected hS htri hn hord huw
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  have hz'c : (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) ∈
      Subgroup.center (localGroup D ((u * v * w) ^ n)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
  have : (Subgroup.zpowers
      (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hO2' : CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)) ≤
      Subgroup.zpowers (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) := by
    intro q hq
    rcases hO2 q hq with h | h
    · rw [show q = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show q = ⟨(u * v * w) ^ n, hzH⟩ from Subtype.ext h]
      exact Subgroup.mem_zpowers _
  have hu'' : (⟨u, mem_localGroup_of_mem hu'⟩ : localGroup D ((u * v * w) ^ n)) ∈
      localSet D ((u * v * w) ^ n) := hu'
  have hv'' : (⟨v, mem_localGroup_of_mem hv'⟩ : localGroup D ((u * v * w) ^ n)) ∈
      localSet D ((u * v * w) ^ n) := hv'
  have htt' : (⟨t, htH⟩ : localGroup D ((u * v * w) ^ n)) * ⟨t, htH⟩ ∈
      Subgroup.zpowers (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) := by
    rw [show (⟨t, htH⟩ : localGroup D ((u * v * w) ^ n)) * ⟨t, htH⟩ = 1 from Subtype.ext htt]
    exact Subgroup.one_mem _
  rcases CentralQuot.involution_cases hz'c (Subtype.ext hzz) hSH (fun h => hzD h.1) hdiscH hu''
      hv'' (fun h => htri.2.2.2.1 (congrArg Subtype.val h)) (commute_coe_iff.mp htri.2.2.2.2.1)
      huvz hO2' htt' with h | h | h
  · rcases (mem_zpowers_of_mul_self (Subtype.ext hzz :
        (⟨(u * v * w) ^ n, hzH⟩ : localGroup D ((u * v * w) ^ n)) * ⟨(u * v * w) ^ n, hzH⟩ = 1)).mp
        h with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h1))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem conj_eq_of_mem_localGroup {g : G}
    (hg : g * (u * v * w) ^ n * g⁻¹ ∈ localGroup D ((u * v * w) ^ n)) :
    g * (u * v * w) ^ n * g⁻¹ = (u * v * w) ^ n := by
  obtain ⟨hzz, hz1, hzu, hzv, hzw, huvzD⟩ := htri.third_kind hS.oddT hS.normal hn hord
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  obtain ⟨hu', -, -, -⟩ := thirdKind_mem_centSet hS htri hn hord
  have htt : g * (u * v * w) ^ n * g⁻¹ * (g * (u * v * w) ^ n * g⁻¹) = 1 := by
    rw [show g * (u * v * w) ^ n * g⁻¹ * (g * (u * v * w) ^ n * g⁻¹) =
      g * ((u * v * w) ^ n * (u * v * w) ^ n) * g⁻¹ by group, hzz, mul_one, mul_inv_cancel]
  rcases localGroup_involution_cases hS htri hn hord huw hO2 hg htt with h | h | h | h
  · exact absurd (conj_eq_one_iff.mp h) hz1
  · exact h
  · exfalso
    apply hzD
    have h1 := hS.conj_mem g⁻¹ h.1
    rwa [show g⁻¹ * (g * (u * v * w) ^ n * g⁻¹) * g⁻¹⁻¹ = (u * v * w) ^ n by group] at h1
  · exfalso
    have hSH := localSetup hS htri hn hord huw
    obtain ⟨k, hk⟩ := isConj_iff.mp (hSH.isConj
      (show (⟨_, mem_localGroup_of_mem h⟩ : localGroup D ((u * v * w) ^ n)) ∈
        localSet D ((u * v * w) ^ n) from h)
      (show (⟨u, mem_localGroup_of_mem hu'⟩ : localGroup D ((u * v * w) ^ n)) ∈
        localSet D ((u * v * w) ^ n) from hu'))
    have hk' : (k : G) * (g * (u * v * w) ^ n * g⁻¹ * (u * v * w) ^ n) * (k : G)⁻¹ = u := by
      simpa using congrArg Subtype.val hk
    have hkz : Commute (k : G) ((u * v * w) ^ n) := commute_of_mem_localGroup k.2
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : G, (k : G) = k₀ := ⟨_, rfl⟩
    rw [hk₀] at hk' hkz
    obtain ⟨z, hzdef⟩ : ∃ z, (u * v * w) ^ n = z := ⟨_, rfl⟩
    rw [hzdef] at hk' hkz hzz hzD hzu hzv hzw huvzD
    have hz_eq : z = (g⁻¹ * k₀⁻¹) * (u * z) * (g⁻¹ * k₀⁻¹)⁻¹ := by
      have e1 : k₀ * (g * z * g⁻¹) * k₀⁻¹ = u * z := by
        calc k₀ * (g * z * g⁻¹) * k₀⁻¹
            = k₀ * (g * z * g⁻¹ * z) * k₀⁻¹ * (k₀ * z * k₀⁻¹) := by
              rw [show k₀ * (g * z * g⁻¹ * z) * k₀⁻¹ * (k₀ * z * k₀⁻¹) =
                k₀ * (g * z * g⁻¹) * (z * z) * k₀⁻¹ by group, hzz, mul_one]
          _ = u * z := by rw [hk', hkz.eq, mul_inv_cancel_right]
      calc z = g⁻¹ * k₀⁻¹ * (k₀ * (g * z * g⁻¹) * k₀⁻¹) * (k₀ * g) := by
            group
        _ = (g⁻¹ * k₀⁻¹) * (u * z) * (g⁻¹ * k₀⁻¹)⁻¹ := by rw [e1]; group
    have huv := htri.2.2.2.2.1
    have hv2 := hS.oddT.mul_self_eq_one htri.2.1
    have huz : u * z = v * (u * v * z) := by
      calc u * z = u * (v * v) * z := by rw [hv2, mul_one]
        _ = (u * v) * v * z := by group
        _ = (v * u) * v * z := by rw [huv.eq]
        _ = v * (u * v * z) := by group
    have hvne : v ≠ u * v * z := by
      intro h
      apply hzD
      have h1 : u * z = 1 := by rw [huz, ← h, hv2]
      have h2 : z = u⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, hS.oddT.inv_eq htri.1]
      exact htri.1
    have hvc : Commute v (u * v * z) :=
      (huv.symm.mul_right (Commute.refl v)).mul_right hzv.symm
    refine false_of_eq_mul_of_not_reach hS htri.1 htri.2.2.1 hzu.symm hzw.symm huw
      (hS.conj_mem (g⁻¹ * k₀⁻¹) htri.2.1) (hS.conj_mem (g⁻¹ * k₀⁻¹) huvzD)
      (fun h => hvne (by simpa using h)) ((Commute.conj_iff _).mpr hvc) ?_
    calc z = (g⁻¹ * k₀⁻¹) * (u * z) * (g⁻¹ * k₀⁻¹)⁻¹ := hz_eq
      _ = (g⁻¹ * k₀⁻¹) * (v * (u * v * z)) * (g⁻¹ * k₀⁻¹)⁻¹ := by rw [huz]
      _ = _ := by group

end Local

end CFSG.Timmesfeld.Bridge.Asc72
