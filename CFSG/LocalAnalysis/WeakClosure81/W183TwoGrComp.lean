module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoDyn
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoSwap
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoGraph

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSp4)

theorem false_of_graph_component (hGraph : FinGraphOdd) {G : Type} [Group G] [Finite G]
    {K H L : Subgroup G} (hL : IsComponentModN K H L) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnc : ∃ u v : X, u * v ≠ v * u) (φ : ↥L →* X)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K)
    (hX : IsAlt X 6 ∨ IsSp4 X 2) {t : G} (htH : t ∈ H) (hDyn : ActsOnDynkinMod K L t)
    {Y : Type} [Group Y] [Finite Y] (π : ↥H →* Y) (hπs : Function.Surjective π)
    (hπk : ∀ h : ↥H, π h = 1 → (h : G) ∈ K) {a : Y} (ha : orderOf a = 2)
    (hOT : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : Y | IsConj a x})
    (hgen : L ≤ ((Subgroup.normalClosure ({a} : Set Y)).comap π).map H.subtype) : False := by
  classical
  have hKL : K ≤ L := hL.2.1
  have hLH : L ≤ H := hL.2.2.1
  have hKH : K ≤ H := hKL.trans hLH
  have hKconj : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K :=
    fun h hh k hk => (Subgroup.normal_subgroupOf_iff hKH).mp hL.1 k h hk hh
  let Q : Subgroup ↥H :=
    { carrier := {h : ↥H | ∀ l ∈ L, (h : G) * l * (h : G)⁻¹ * l⁻¹ ∈ K}
      one_mem' := by
        intro l hl
        simp
      mul_mem' := by
        intro b c hb hc l hl
        have h1 : (b : G) * (c * l * c⁻¹ * l⁻¹) * (b : G)⁻¹ ∈ K :=
          hKconj (b : G) b.2 _ (hc l hl)
        have h2 : (b : G) * l * (b : G)⁻¹ * l⁻¹ ∈ K := hb l hl
        have heq : ((b * c : ↥H) : G) * l * ((b * c : ↥H) : G)⁻¹ * l⁻¹ =
            ((b : G) * (c * l * c⁻¹ * l⁻¹) * (b : G)⁻¹) *
              ((b : G) * l * (b : G)⁻¹ * l⁻¹) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [heq]
        exact K.mul_mem h1 h2
      inv_mem' := by
        intro b hb l hl
        have h2 : (b : G) * l * (b : G)⁻¹ * l⁻¹ ∈ K := hb l hl
        have h1 : (b : G)⁻¹ * ((b : G) * l * (b : G)⁻¹ * l⁻¹)⁻¹ * (b : G) ∈ K := by
          simpa using hKconj (b : G)⁻¹ (H.inv_mem b.2) _ (K.inv_mem h2)
        have heq : ((b⁻¹ : ↥H) : G) * l * ((b⁻¹ : ↥H) : G)⁻¹ * l⁻¹ =
            (b : G)⁻¹ * ((b : G) * l * (b : G)⁻¹ * l⁻¹)⁻¹ * (b : G) := by
          simp only [Subgroup.coe_inv, inv_inv]
          group
        rw [heq]
        exact h1 }
  let P : Subgroup ↥H := (Subgroup.normalClosure ({a} : Set Y)).comap π
  have hkerQ : π.ker ≤ Q := by
    intro k hk l hl
    have hkK : (k : G) ∈ K := hπk k (MonoidHom.mem_ker.mp hk)
    have h1 : (k : G) * (l * (k : G)⁻¹ * l⁻¹) ∈ K :=
      K.mul_mem hkK (hKconj l (hLH hl) (k : G)⁻¹ (K.inv_mem hkK))
    have heq : (k : G) * l * (k : G)⁻¹ * l⁻¹ = (k : G) * (l * (k : G)⁻¹ * l⁻¹) := by
      group
    rw [heq]
    exact h1
  have hex : ∃ d : ↥H, IsConj a (π d) ∧
      ∃ l ∈ L, (d : G) * l * (d : G)⁻¹ * l⁻¹ ∉ K := by
    by_contra hno
    have hDQ : ∀ d : ↥H, IsConj a (π d) → d ∈ Q := by
      intro d hd l hl
      by_contra h
      exact hno ⟨d, hd, l, hl, h⟩
    have hPleQ : P ≤ Q := by
      intro h hh
      have hπh0 : π h ∈ Subgroup.normalClosure ({a} : Set Y) := hh
      have hCsub : Group.conjugatesOfSet ({a} : Set Y) ⊆ (Q.map π : Subgroup Y) := by
        intro c hc
        rw [Group.mem_conjugatesOfSet_iff] at hc
        obtain ⟨b, hb, hbc⟩ := hc
        rw [Set.mem_singleton_iff] at hb
        rw [hb] at hbc
        obtain ⟨y, hy⟩ := hπs c
        exact Subgroup.mem_map.mpr ⟨y, hDQ y (by rw [hy]; exact hbc), hy⟩
      have hclosure : Subgroup.normalClosure ({a} : Set Y) ≤ (Q.map π : Subgroup Y) := by
        change Subgroup.closure (Group.conjugatesOfSet ({a} : Set Y)) ≤ (Q.map π : Subgroup Y)
        exact (Subgroup.closure_le (Q.map π)).mpr hCsub
      obtain ⟨q, hqQ, hqπ⟩ := Subgroup.mem_map.mp (hclosure hπh0)
      have hker : h * q⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hqπ, mul_inv_cancel]
      have hkerQ : h * q⁻¹ ∈ Q := hkerQ hker
      have heq : h = (h * q⁻¹) * q := by group
      rw [heq]
      exact Q.mul_mem hkerQ hqQ
    have hLL : ∀ l ∈ L, ∀ l' ∈ L, l * l' * l⁻¹ * l'⁻¹ ∈ K := by
      intro l hl l' hl'
      obtain ⟨p, hpP, hp_eq⟩ := Subgroup.mem_map.mp (hgen hl)
      have hpQ : p ∈ Q := hPleQ hpP
      have hpk : (p : G) * l' * (p : G)⁻¹ * l'⁻¹ ∈ K := hpQ l' hl'
      have hval : (p : G) = l := hp_eq
      rwa [hval] at hpk
    have hXcomm : ∀ u v : X, u * v = v * u := by
      intro u v
      obtain ⟨l, rfl⟩ := hφs u
      obtain ⟨l', rfl⟩ := hφs v
      have hcK : ((l * l' * l⁻¹ * l'⁻¹ : ↥L) : G) ∈ K := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hLL (l : G) l.2 (l' : G) l'.2
      have hcφ : φ (l * l' * l⁻¹ * l'⁻¹) = 1 := (hφk _).mpr hcK
      have hcφ' : φ l * φ l' * (φ l)⁻¹ * (φ l')⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using hcφ
      have h1 : (φ l * φ l') * (φ l' * φ l)⁻¹ = 1 := by
        rw [mul_inv_rev]
        simpa [mul_assoc] using hcφ'
      exact mul_inv_eq_one.mp h1
    obtain ⟨u, v, huv⟩ := hnc
    exact huv (hXcomm u v)
  obtain ⟨d, hdconj, l₀, hl₀L, hnt⟩ := hex
  have hd2 : (d : G) ^ 2 ∈ K := by
    have hker : d ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      have h2 : orderOf (π d) = 2 := hOT.1 (π d) hdconj
      rw [← h2]
      exact pow_orderOf_eq_one (π d)
    have := hπk (d ^ 2) hker
    simpa using this
  have hOT2 : ∀ y ∈ H, ∀ y' ∈ H, ∃ m : ℕ, 0 < m ∧ (m ∣ 2 ∨ Odd m) ∧
      ((y * (d : G) * y⁻¹) * (y' * (d : G) * y'⁻¹)) ^ m ∈ K := by
    intro y hy y' hy'
    let yH : ↥H := ⟨y, hy⟩
    let yH' : ↥H := ⟨y', hy'⟩
    let u : Y := π yH * π d * (π yH)⁻¹
    let v : Y := π yH' * π d * (π yH')⁻¹
    have hu : IsConj a u := hdconj.trans (isConj_iff.mpr ⟨π yH, by simp [u]⟩)
    have hv : IsConj a v := hdconj.trans (isConj_iff.mpr ⟨π yH', by simp [v]⟩)
    refine ⟨orderOf (u * v), orderOf_pos (u * v), hOT.2 u hu v hv, ?_⟩
    have hπ : π ((yH * d * yH⁻¹) * (yH' * d * yH'⁻¹)) = u * v := by
      simp only [map_mul, map_inv, u, v]
    have hmem : ((yH * d * yH⁻¹) * (yH' * d * yH'⁻¹)) ^ orderOf (u * v) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hπ]
      exact pow_orderOf_eq_one (u * v)
    have := hπk _ hmem
    simpa [yH, yH'] using this
  by_cases hdn : (d : G) ∈ Subgroup.normalizer (L : Set G)
  · exact false_of_normalizing_class hGraph hL hnc φ hφs hφk hX htH hDyn d.2 hdn hd2
      ⟨l₀, hl₀L, hnt⟩ hOT2
  · apply false_of_swap_class_mod hL φ hφs hφk
      (exists_orderOf_four_of_isAlt_six_or_isSp4 hX) d.2 hd2 ?_ ?_
    · intro heq
      apply hdn
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [← mem_conjSubgroup_iff (A := L) (g := (d : G)) (x := x), heq]
    · intro y hy
      obtain ⟨m, hm0, hm2odd, hmK⟩ := hOT2 1 H.one_mem y hy
      exact ⟨m, hm0, hm2odd, by simpa using hmK⟩

end CFSG.LocalAnalysis.WeakClosure81

end
