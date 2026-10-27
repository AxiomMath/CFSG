module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.FFC

open CFSG.Quasithin

theorem exists_core_move {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    ∃ m ∈ G6.coreMod n, G6.permAct n σ m * m⁻¹ ∉ Subgroup.zpowers (G6.allOnes n) := by
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  have hcard : ({i, σ i} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ ({i, σ i} : Finset (Fin n)) := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin n)) ⊆ {i, σ i} := fun j _ => h j
    have := Finset.card_le_card this
    simp at this
    omega
  have hji : j ≠ i := fun h => hj (by simp [h])
  have hjs : j ≠ σ i := fun h => hj (by simp [h])
  have hsj : σ j ≠ σ i := fun h => hji (σ.injective h)
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ ({i, j, σ i, σ j} : Finset (Fin n)) := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin n)) ⊆ {i, j, σ i, σ j} := fun l _ => h l
    have h4 := Finset.card_le_card this
    have h5 : ({i, j, σ i, σ j} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
    simp only [Finset.card_univ, Fintype.card_fin] at h4
    omega
  have hki : k ≠ i := fun h => hk (by simp [h])
  have hkj : k ≠ j := fun h => hk (by simp [h])
  have hksi : k ≠ σ i := fun h => hk (by simp [h])
  have hksj : k ≠ σ j := fun h => hk (by simp [h])
  let w : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1
  have hwi : w i = 1 := by simp [w, Ne.symm hji]
  have hwsi : w (σ i) = 0 := by simp [w, hi, hjs.symm]
  have hwk : w k = 0 := by simp [w, hki, hkj]
  have hwsk : w (σ⁻¹ k) = 0 := by
    have h1 : σ.symm k ≠ i := fun h => hksi (by rw [← h]; simp)
    have h2 : σ.symm k ≠ j := fun h => hksj (by rw [← h]; simp)
    simp [w, h1, h2]
  refine ⟨Multiplicative.ofAdd w, ?_, ?_⟩
  · show ∑ l, w l = 0
    simp [w, Finset.sum_add_distrib]
    decide
  · intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hcoord : ∀ l, (t : ZMod 2) = w (σ⁻¹ l) + w l := by
      intro l
      have := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x l) ht
      have hneg : ∀ y : ZMod 2, -y = y := by decide
      simpa [G6.allOnes, G6.permAct_apply, sub_eq_add_neg, hneg] using this
    have h1 := hcoord (σ i)
    have h2 := hcoord k
    have e1 : σ⁻¹ (σ i) = i := by simp
    rw [e1, hwi, hwsi] at h1
    rw [hwsk, hwk] at h2
    rw [h1] at h2
    exact absurd h2 (by decide)


theorem injective_of_symDn_realizes {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    (hn : 5 ≤ n) {π : Equiv.Perm (Fin n) →* ↥H}
    (h : (FFModel.symDn n).RealizesVia H ⊤ ⊥ π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨m, hm, hmove⟩ := exists_core_move hn hne
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, -, hβe⟩ := h
  have hm0 : m ∈ (FFModel.symDn n).sec := hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm0⟩)
  have hm' : (FFModel.symDn n).act σ m ∈ (FFModel.symDn n).sec := hsec σ m hm0
  have h1 := hβe σ u ⟨m, hm0⟩ (by trivial) hm' hu
  have h2 : (⟨((π σ : ↥H) : MulAut V) (u : V), (by trivial)⟩ : ↥(⊤ : Subgroup V)) = u := by
    apply Subtype.ext
    show ((π σ : ↥H) : MulAut V) (u : V) = (u : V)
    rw [hσ]
    rfl
  have h1' : β u = ((⟨(FFModel.symDn n).act σ m, hm'⟩ : ↥(FFModel.symDn n).sec) :
      ↥(FFModel.symDn n).sec ⧸ (FFModel.symDn n).ker.subgroupOf (FFModel.symDn n).sec) :=
    (congrArg β h2).symm.trans h1
  rw [hu] at h1'
  have h3 := QuotientGroup.eq.1 h1'
  rw [Subgroup.mem_subgroupOf] at h3
  apply hmove
  have h4 : (G6.permAct n σ m) * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := by
    have : ((⟨m, hm0⟩ : ↥(FFModel.symDn n).sec)⁻¹ * ⟨(FFModel.symDn n).act σ m, hm'⟩ : _) ∈
        (FFModel.symDn n).ker.subgroupOf (FFModel.symDn n).sec := h3
    rw [Subgroup.mem_subgroupOf] at this
    have h5 : ((⟨m, hm0⟩ : ↥(FFModel.symDn n).sec)⁻¹ * ⟨(FFModel.symDn n).act σ m, hm'⟩ :
        ↥(FFModel.symDn n).sec).1 = m⁻¹ * G6.permAct n σ m := rfl
    rw [h5, mul_comm] at this
    exact this
  exact h4.1

end CFSG.Quasithin.FFC
