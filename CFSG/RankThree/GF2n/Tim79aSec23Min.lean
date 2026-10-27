module

public import CFSG.RankThree.GF2n.Tim79aSec23Defs
public import CFSG.RankThree.GF2n.Tim79aSec22Min
public import CFSG.RankThree.GF2n.Tim79aSec2Root

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem sup_eq_or_commutator_le {N : Subgroup G} (hWN : wOf V H ≤ N) (hNX : N ≤ xOf V H)
    (hNn : H ≤ Subgroup.normalizer (N : Set G)) :
    N ⊔ P = H ∨ ∀ n ∈ N, ∀ v ∈ V, ⁅n, v⁆ ∈ inSubgroup (pCore 2) (xOf V H) := by
  by_cases hK : N ⊔ P = H
  · exact Or.inl hK
  right
  have hXH : xOf V H ≤ H := xOf_le_H hc.V_le_H
  have hNH : N ≤ H := hNX.trans hXH
  have hKH : N ⊔ P ≤ H := sup_le hNH hc.PleH
  have hlt : N ⊔ P < H := lt_of_le_of_ne hKH hK
  have hWK : wOf V H ≤ inSubgroup (pCore 2) (N ⊔ P) := by
    refine Tim78.le_inSubgroup_pCore (hWN.trans le_sup_left) ?_ ?_
    · intro x hx
      exact H_le_normalizer_wOf V H (hKH hx)
    · exact CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian
  have hO : inSubgroup (pCore 2) (N ⊔ P) ≠ ⊥ := by
    intro hbot
    have hW : wOf V H = ⊥ := le_bot_iff.mp (hbot ▸ hWK)
    exact hc.V_inf_wOf_ne_bot (by rw [hW]; simp)
  have hV : V ≤ inSubgroup (pCore 2) (N ⊔ P) := hc.min (N ⊔ P) le_sup_right hO hlt
  intro n hn v hv
  obtain ⟨hK2, hKK, hKn⟩ := inSubgroup_pCore_two (N ⊔ P)
  have hnK : n ∈ N ⊔ P := Subgroup.mem_sup_left hn
  have h1 : ⁅n, v⁆ ∈ inSubgroup (pCore 2) (N ⊔ P) := by
    have : n * v * n⁻¹ ∈ inSubgroup (pCore 2) (N ⊔ P) :=
      (Subgroup.mem_normalizer_iff.mp (hKn hnK) v).mp (hV hv)
    rw [commutatorElement_def]
    exact (inSubgroup (pCore 2) (N ⊔ P)).mul_mem this
      ((inSubgroup (pCore 2) (N ⊔ P)).inv_mem (hV hv))
  have h2 : ⁅n, v⁆ ∈ N := by
    have hvH : v ∈ H := hc.V_le_H hv
    have : v * n⁻¹ * v⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hNn hvH) n⁻¹).mp (N.inv_mem hn)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact N.mul_mem hn (by simpa [mul_assoc] using this)
  have hT : inSubgroup (pCore 2) (N ⊔ P) ⊓ N ≤ inSubgroup (pCore 2) N := by
    refine Tim78.le_inSubgroup_pCore inf_le_right ?_ ?_
    · intro x hx
      exact mem_normalizer_inf (hKn (Subgroup.mem_sup_left hx)) (Subgroup.le_normalizer hx)
    · exact hK2.to_le inf_le_left
  have hNX' : (N.subgroupOf (xOf V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 fun x hx => hNn (hXH hx)
  exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 N (xOf V H) hNX
    hNX' (hT ⟨h1, h2⟩)


theorem sup_eq_or_commutator_le_bar {S : Subgroup (Hbar V H)} [S.Normal]
    (hSX : S ≤ barOf V H (xOf V H)) :
    preimOf V H S ⊔ P = H ∨ ∀ s ∈ S, ∀ v ∈ barOf V H V,
      ⁅s, v⁆ ∈ barOf V H (inSubgroup (pCore 2) (xOf V H)) := by
  rcases hc.sup_eq_or_commutator_le (wOf_le_preimOf V H S) (preimOf_le_xOf hSX)
    normalizer_preimOf with h | h
  · exact Or.inl h
  right
  intro s hs v hv
  have hs' : s ∈ barOf V H (preimOf V H S) := by rw [barOf_preimOf]; exact hs
  obtain ⟨x, hx, rfl⟩ := mem_barOf_iff.mp hs'
  obtain ⟨y, hy, rfl⟩ := mem_barOf_iff.mp hv
  refine mem_barOf_iff.mpr ⟨⁅x, y⁆, ?_, by simp [map_commutatorElement]⟩
  have : ((⁅x, y⁆ : ↥H) : G) = ⁅(x : G), (y : G)⁆ := by simp [commutatorElement_def]
  rw [this]
  exact h _ hx _ hy


theorem oBar_central : ∀ z ∈ barOf V H (inSubgroup (pCore 2) (xOf V H)),
    ∀ y ∈ barOf V H (xOf V H), z * y = y * z := by
  have hF : inSubgroup generalizedFitting (xOf V H) = inSubgroup (pCore 2) (xOf V H) := by
    unfold inSubgroup
    rw [hc.fitting_xOf]
  have h := hc.fitting_xOf_central_bar
  rw [hF] at h
  exact h

theorem exists_pow_eq_one_of_mem_oBar {z : Hbar V H}
    (hz : z ∈ barOf V H (inSubgroup (pCore 2) (xOf V H))) : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  obtain ⟨a, ha, rfl⟩ := mem_barOf_iff.mp hz
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (inSubgroup_pCore_two (xOf V H)).1 ⟨(a : G), ha⟩
  refine ⟨k, ?_⟩
  have h0 : (⟨(a : G), ha⟩ : inSubgroup (pCore 2) (xOf V H)) ^ 2 ^ k = 1 := by
    rw [← hk]; exact pow_orderOf_eq_one _
  have h1 : (a : G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val h0
    simpa using this
  have h2 : a ^ 2 ^ k = 1 := Subtype.ext (by simpa using h1)
  rw [← map_pow, h2, map_one]

theorem exists_conj_of_mem_dbarOf {y : Hbar V H} (hy : y ∈ dbarOf V H) :
    ∃ a ∈ barOf V H (xOf V H), ∃ v ∈ barOf V H V, y = a * v * a⁻¹ := by
  obtain ⟨x, ⟨hx1, U, ⟨h, hh, rfl⟩, hxU⟩, hxW, rfl⟩ := mem_dbarOf_iff.mp hy
  obtain ⟨x₀, hx₀, hconj⟩ := hc.exists_conj_xOf hh
  have hxU' : (x : G) ∈ conjSubgroup x₀ V := hconj ▸ hxU
  have hv : x₀⁻¹ * (x : G) * x₀ ∈ V := mem_conjSubgroup.mp hxU'
  have hx₀H : x₀ ∈ H := xOf_le_H hc.V_le_H hx₀
  set a : ↥H := ⟨x₀, hx₀H⟩ with ha
  refine ⟨piBar V H a, mem_barOf_iff.mpr ⟨a, hx₀, rfl⟩, piBar V H (a⁻¹ * x * a),
    mem_barOf_iff.mpr ⟨a⁻¹ * x * a, by simpa [ha] using hv, rfl⟩, ?_⟩
  simp only [map_mul, map_inv]
  group

theorem sup_eq_or_central_of_odd {S : Subgroup (Hbar V H)} [S.Normal]
    (hSX : S ≤ barOf V H (xOf V H)) (hodd : Odd (Nat.card S)) :
    preimOf V H S ⊔ P = H ∨ ∀ s ∈ S, ∀ y ∈ barOf V H (xOf V H), s * y = y * s := by
  rcases hc.sup_eq_or_commutator_le_bar hSX with h | h
  · exact Or.inl h
  right
  have h1 : ∀ s ∈ S, ∀ v ∈ barOf V H V, s * v = v * s := by
    intro s hs v hv
    have hcomm := h s hs v hv
    have hS : ⁅s, v⁆ ∈ S := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact S.mul_mem hs (by simpa [mul_assoc] using
        Subgroup.Normal.conj_mem ‹S.Normal› _ (S.inv_mem hs) v)
    obtain ⟨k, hk⟩ := hc.exists_pow_eq_one_of_mem_oBar hcomm
    have hd1 : orderOf ⁅s, v⁆ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hd2 : orderOf ⁅s, v⁆ ∣ Nat.card S := by
      have := orderOf_dvd_natCard (⟨⁅s, v⁆, hS⟩ : S)
      simpa [Subgroup.orderOf_mk] using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card S) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    have h1' : orderOf ⁅s, v⁆ = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
    exact commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp h1')
  have hD : ∀ y ∈ dbarOf V H, ∀ s ∈ S, s * y = y * s := by
    intro y hy s hs
    obtain ⟨a, ha, v, hv, rfl⟩ := hc.exists_conj_of_mem_dbarOf hy
    have hs' : a⁻¹ * s * a ∈ S := by
      simpa using Subgroup.Normal.conj_mem ‹S.Normal› s hs a⁻¹
    have := h1 _ hs' v hv
    calc s * (a * v * a⁻¹) = a * ((a⁻¹ * s * a) * v) * a⁻¹ := by group
      _ = a * (v * (a⁻¹ * s * a)) * a⁻¹ := by rw [this]
      _ = a * v * a⁻¹ * s := by group
  intro s hs y hy
  have hT : barOf V H (xOf V H) ≤ Subgroup.centralizer (S : Set (Hbar V H)) := by
    rw [← hc.closure_dbarOf]
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun s hs => hD y hy s hs
  exact Subgroup.mem_centralizer_iff.mp (hT hy) s hs

end MinCex

end CFSG.RankThree.GF2n.Tim79a
