module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.SeitzReduction.LinearPilot

private theorem ggDiagConj_diagAt_eq_self_of_mem_blockSpecialLinear
    {m : ℕ} {F : Type} [Field F] {I : Finset (Fin m)} {r : Fin m} (hr : r ∉ I) (τ : Fˣ)
    {s : SpecialLinearGroup (Fin m) F} (hs : s ∈ blockSpecialLinear I) :
    ggDiagConj (diagAt r τ) s = s := by
  apply Subtype.ext
  ext i j
  rw [ggDiagConj_apply]
  obtain hi | hi := eq_or_ne i r
  · rw [hi]
    obtain hj | hj := eq_or_ne j r
    · rw [hj, diagAt_apply_self]
      have h1 : (s : Matrix (Fin m) (Fin m) F) r r = 1 := by
        have := hs r r (Or.inl hr)
        simpa using this
      rw [h1]
      simp
    · rw [diagAt_apply_self, diagAt_apply_of_ne hj]
      have h1 : (s : Matrix (Fin m) (Fin m) F) r j = 0 := by
        have := hs r j (Or.inl hr)
        rw [Matrix.one_apply_ne (Ne.symm hj)] at this
        simpa using this
      rw [h1]
      simp
  · obtain hj | hj := eq_or_ne j r
    · rw [hj, diagAt_apply_of_ne hi, diagAt_apply_self]
      have h1 : (s : Matrix (Fin m) (Fin m) F) i r = 0 := by
        have := hs i r (Or.inr hr)
        rw [Matrix.one_apply_ne hi] at this
        simpa using this
      rw [h1]
      simp
    · rw [diagAt_apply_of_ne hi, diagAt_apply_of_ne hj]
      simp

private theorem exists_zpow_mul_zpow_of_mem_closure_pair {G : Type*} [Group G] {a b c : G}
    (hab : a * b = b * a) (hc : c ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ i j : ℤ, c = a ^ i * b ^ j := by
  have hcomm : Commute a b := hab
  refine Subgroup.closure_induction (k := ({a, b} : Set G)) ?_ ?_ ?_ ?_ hc
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · exact ⟨0, 0, by simp⟩
  · intro x y hx hy ihx ihy
    obtain ⟨i, j, rfl⟩ := ihx
    obtain ⟨k, l, rfl⟩ := ihy
    refine ⟨i + k, j + l, ?_⟩
    calc a ^ i * b ^ j * (a ^ k * b ^ l)
        = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [(hcomm.symm.zpow_zpow j k).eq]
      _ = (a ^ i * a ^ k) * (b ^ j * b ^ l) := by group
      _ = a ^ (i + k) * b ^ (j + l) := by rw [← _root_.zpow_add, ← _root_.zpow_add]
  · intro x hx ihx
    obtain ⟨i, j, rfl⟩ := ihx
    refine ⟨-i, -j, ?_⟩
    rw [_root_.mul_inv_rev, ← _root_.zpow_neg, ← _root_.zpow_neg]
    exact (hcomm.symm.zpow_zpow (-j) (-i)).eq

theorem exists_eq_map_blockSpecialLinear_erase {X : Type} [Group X] [Finite X] {F : Type}
    [Field F] [Finite F] [CharP F 2] {p n : ℕ} (hp : p.Prime) {Bs : Subgroup X}
    (hBs : IsElemAbelian p Bs) {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    (hD : ∀ r, ∃ g ∈ Bs, ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ))
    {z w : X} (hzB : z ∈ Bs) (hwB : w ∈ Bs) (hz : ∀ s, z * φ s = φ s * z)
    (hw : ¬ ∀ s, w * φ s = φ s * w) {D J : Subgroup X} (hDzw : D = Subgroup.closure {z, w})
    (hJ : CFSG.Assembly.IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set X)))
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set X) ≤ D) :
    ∃ r : Fin (n + 1),
      J = (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase r)).map φ := by
  classical
  obtain ⟨h_w, hw_acts⟩ := hdiag w hwB
  have hzD : z ∈ D := by rw [hDzw]; exact Subgroup.subset_closure (by simp)
  have hwD : w ∈ D := by rw [hDzw]; exact Subgroup.subset_closure (by simp)
  have hcent : (φ.range ⊓ Subgroup.centralizer (D : Set X)) =
      φ.range ⊓ Subgroup.centralizer (Set.range (fun _ : Unit => w)) := by
    rw [Set.range_const]
    apply le_antisymm
    · refine inf_le_inf_left _ (Subgroup.centralizer_le ?_)
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hwD
    · rintro x ⟨hxr, hxw⟩
      obtain ⟨s, rfl⟩ := hxr
      have hxw' : ∀ h ∈ ({w} : Set X), h * φ s = φ s * h :=
        Subgroup.mem_centralizer_iff.mp hxw
      refine Subgroup.mem_inf.mpr ⟨⟨s, rfl⟩, ?_⟩
      rw [hDzw, Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      rcases hy with rfl | hy
      · exact hz s
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hxw' w (by simp)
  have hJ' : CFSG.Assembly.IsComponentOf J
      (φ.range ⊓ Subgroup.centralizer (Set.range (fun _ : Unit => w))) := hcent ▸ hJ
  obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf
    (m := n) (F := F) (ψ := φ) hker
    (d := fun _ : Unit => h_w) (b := fun _ : Unit => w)
    (fun _ => (ggActsVec_iff_mem_ggInducedPairs).mp hw_acts) hJ'
  set I : Finset (Fin (n + 1)) := LinSemisimple.eigClass (fun _ : Unit => h_w) i with hIdef
  have hiI : J = (blockSpecialLinear I).map φ := hi
  have hI_ne : I ≠ Finset.univ := by
    intro hIuniv
    apply hw
    intro s
    have hJle : J ≤ Subgroup.centralizer (D : Set X) := hJ.1.trans inf_le_right
    have hrange : J = φ.range := by
      rw [hiI, hIuniv, blockSpecialLinear_univ]
      exact (MonoidHom.range_eq_map φ).symm
    have hsJ : φ s ∈ J := by rw [hrange]; exact ⟨s, rfl⟩
    have hmem := Subgroup.mem_centralizer_iff.mp (hJle hsJ)
    exact hmem w hwD
  obtain ⟨r, hr⟩ : ∃ r : Fin (n + 1), r ∉ I := by
    by_contra h
    push Not at h
    exact hI_ne (Finset.eq_univ_iff_forall.mpr h)
  have hir : i ≠ r :=
    fun h => hr (h ▸ LinSemisimple.self_mem_eigClass (fun _ : Unit => h_w) i)
  have hm : 2 ≤ n + 1 := by
    have h1 : 1 < Fintype.card (Fin (n + 1)) := Fintype.one_lt_card_iff.mpr ⟨i, r, hir⟩
    have h1' : 1 < n + 1 := by simpa using h1
    omega
  obtain ⟨g, hgB, τ, hτ, hgacts⟩ := hD r
  have hgcentJ : g ∈ Subgroup.centralizer (J : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    have hxJ : x ∈ (blockSpecialLinear I).map φ := by rw [← hiI]; exact hx
    obtain ⟨s, hs, rfl⟩ := hxJ
    have hconj := hgacts s
    rw [ggDiagConj_diagAt_eq_self_of_mem_blockSpecialLinear hr τ hs] at hconj
    have hcomm : g * φ s = φ s * g := by
      calc g * φ s = (g * φ s * g⁻¹) * g := by group
        _ = φ s * g := by rw [hconj]
    exact hcomm.symm
  have hgD : g ∈ D := hCJ (Subgroup.mem_inf.mpr ⟨hgB, hgcentJ⟩)
  have hcomm_zw : Commute z w := by
    haveI : IsMulCommutative Bs := hBs.1
    have h := mul_comm' (⟨z, hzB⟩ : Bs) (⟨w, hwB⟩ : Bs)
    exact (commute_iff_eq z w).mpr (Subtype.ext_iff.mp h)
  obtain ⟨a, k, hg_eq⟩ :=
    exists_zpow_mul_zpow_of_mem_closure_pair hcomm_zw.eq (hDzw ▸ hgD)
  have hg_acts : GGActsVec φ g (h_w ^ k) := by
    rw [hg_eq]
    have h2 : GGActsVec φ (z ^ a) (1 : Fin (n + 1) → Fˣ) := by
      simpa using GGActsVec.zpow (GGActsVec.one_of_commute hz) a
    have h3 : GGActsVec φ (w ^ k) (h_w ^ k) := GGActsVec.zpow hw_acts k
    have h := GGActsVec.mul h2 h3
    have hone : (1 : Fin (n + 1) → Fˣ) * (h_w ^ k) = h_w ^ k := by
      funext l; simp
    rwa [hone] at h
  have hvec : GGVecEq (diagAt r τ) (h_w ^ k) := GGActsVec.vecEq hker hgacts hg_acts
  obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp hvec
  have hp_const : ∀ j j' : Fin (n + 1), h_w j ^ p = h_w j' ^ p := by
    have hacts_p : GGActsVec φ (w ^ p) (h_w ^ p) := by
      simpa using GGActsVec.zpow hw_acts (p : ℤ)
    have h1 : GGActsVec φ (w ^ p) (1 : Fin (n + 1) → Fˣ) := by
      rw [hBs.2 w hwB]
      exact GGActsVec.one_of_commute (fun s => by simp)
    have hve : GGVecEq (h_w ^ p) 1 := GGActsVec.vecEq hker hacts_p h1
    intro j j'
    have := (ggVecEq_one_iff.mp hve) j j'
    simpa using this
  have hpow_eq : ∀ j j' : Fin (n + 1), j ≠ r → j' ≠ r → h_w j ^ k = h_w j' ^ k := by
    intro j j' hj hj'
    have h1 := hc j
    have h2 := hc j'
    rw [diagAt_apply_of_ne hj] at h1
    rw [diagAt_apply_of_ne hj'] at h2
    exact mul_left_cancel (h1.symm.trans h2)
  have hpk : ¬ ((p : ℤ) ∣ k) := by
    intro hdiv
    obtain ⟨t, ht⟩ := hdiv
    have hwk : w ^ k = 1 := by
      rw [ht, _root_.zpow_mul, _root_.zpow_natCast, hBs.2 w hwB, _root_.one_zpow]
    have hg_comm : ∀ s, g * φ s = φ s * g := by
      have hza : GGActsVec φ (z ^ a) (1 : Fin (n + 1) → Fˣ) := by
        simpa using GGActsVec.zpow (GGActsVec.one_of_commute hz) a
      rw [hg_eq, hwk, mul_one]
      exact GGActsVec.commute_of_vecEq_one hza (GGVecEq.refl 1)
    have hve2 : GGVecEq (h_w ^ k) 1 :=
      GGActsVec.vecEq hker hg_acts (GGActsVec.one_of_commute hg_comm)
    exact hτ ((ggVecEq_diagAt_one_iff (m := n + 1) hm r τ).mp (hvec.trans hve2))
  have hconst_erase : ∀ j j' : Fin (n + 1), j ≠ r → j' ≠ r → h_w j = h_w j' := by
    intro j j' hj hj'
    have hk1 : (h_w j * (h_w j')⁻¹) ^ k = 1 := by
      rw [_root_.mul_zpow, _root_.inv_zpow, hpow_eq j j' hj hj', mul_inv_cancel]
    have hp1 : (h_w j * (h_w j')⁻¹) ^ p = 1 := by
      rw [_root_.mul_pow, _root_.inv_pow, hp_const j j', mul_inv_cancel]
    have hdvd_k : (orderOf (h_w j * (h_w j')⁻¹) : ℤ) ∣ k :=
      orderOf_dvd_iff_zpow_eq_one.mpr hk1
    have hdvd_p : orderOf (h_w j * (h_w j')⁻¹) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr hp1
    rcases (Nat.dvd_prime hp).mp hdvd_p with h1 | hp_eq
    · exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp h1)
    · exact absurd (hp_eq ▸ hdvd_k) hpk
  have hIerase : I = Finset.univ.erase r := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      rw [Finset.mem_erase]
      exact ⟨fun hjr => hr (hjr ▸ hj), Finset.mem_univ j⟩
    · intro hj
      rw [Finset.mem_erase] at hj
      exact (LinSemisimple.mem_eigClass).mpr (fun _ => hconst_erase j i hj.1 hir)
  exact ⟨r, by rw [hiI, hIerase]⟩

end CFSG.StandardType

end
