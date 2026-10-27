module

public import CFSG.RankThree.PartOne.FIS.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7

variable {G : Type*} [Group G] {D : Set G}

@[expose] def VRel (D : Set G) (x y : G) : Prop := centralizerIn D x = centralizerIn D y

@[expose] def WRel (D : Set G) (x y : G) : Prop := localSet D x = localSet D y

theorem mem_centralizerIn_conj (hD : IsThreeTranspositions D) (g x y : G) :
    y ∈ centralizerIn D (g * x * g⁻¹) ↔ g⁻¹ * y * g ∈ centralizerIn D x := by
  have key : y * (g * x * g⁻¹) = (g * x * g⁻¹) * y ↔ (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g) := by
    rw [← conj_comm_iff g (g⁻¹ * y * g) x]
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group, eq_comm]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨?_, key.1 h⟩
    simpa using tt_conj_mem hD hy g⁻¹
  · rintro ⟨hy, h⟩
    refine ⟨?_, key.2 h⟩
    have := tt_conj_mem hD hy g
    simpa [mul_assoc] using this

theorem mem_localSet_conj (hD : IsThreeTranspositions D) (g x y : G) :
    y ∈ localSet D (g * x * g⁻¹) ↔ g⁻¹ * y * g ∈ localSet D x := by
  have key : y * (g * x * g⁻¹) = (g * x * g⁻¹) * y ↔ (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g) := by
    rw [← conj_comm_iff g (g⁻¹ * y * g) x]
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group, eq_comm]
  have hne : y ≠ g * x * g⁻¹ ↔ g⁻¹ * y * g ≠ x := by
    constructor
    · intro h h'
      apply h
      rw [← h']
      group
    · intro h h'
      apply h
      rw [h']
      group
  constructor
  · rintro ⟨hy, h, h'⟩
    refine ⟨?_, key.1 h, hne.1 h'⟩
    simpa using tt_conj_mem hD hy g⁻¹
  · rintro ⟨hy, h, h'⟩
    refine ⟨?_, key.2 h, hne.2 h'⟩
    have := tt_conj_mem hD hy g
    simpa [mul_assoc] using this

theorem VRel.conj (hD : IsThreeTranspositions D) (g : G) {x y : G} (h : VRel D x y) :
    VRel D (g * x * g⁻¹) (g * y * g⁻¹) := by
  ext z
  rw [mem_centralizerIn_conj hD, mem_centralizerIn_conj hD, h]

theorem WRel.conj (hD : IsThreeTranspositions D) (g : G) {x y : G} (h : WRel D x y) :
    WRel D (g * x * g⁻¹) (g * y * g⁻¹) := by
  ext z
  rw [mem_localSet_conj hD, mem_localSet_conj hD, h]

theorem conj_eq_of_comm {a b c : G} (hca : c * a = a * c) (hcb : c * b = b * c) :
    (a * b) * c * (a * b)⁻¹ = c := by
  calc (a * b) * c * (a * b)⁻¹ = a * (b * c) * b⁻¹ * a⁻¹ := by group
    _ = a * (c * b) * b⁻¹ * a⁻¹ := by rw [← hcb]
    _ = a * c * a⁻¹ := by group
    _ = c * a * a⁻¹ := by rw [hca]
    _ = c := by group

theorem rel_conj_of_noncomm [Finite G] (hD : IsThreeTranspositions D) (R : G → G → Prop)
    (hRinv : ∀ (g x y : G), R x y → R (g * x * g⁻¹) (g * y * g⁻¹))
    (hRsymm : ∀ x y : G, R x y → R y x) {a b c : G} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : R a b) (hca : c * a ≠ a * c) (hcb : c * b ≠ b * c) :
    R ((a * b) * c * (a * b)⁻¹) c := by
  have hg := tt_conj_eq_of_noncomm' hD hc ha hca
  have hh := tt_conj_eq_of_noncomm' hD hc hb hcb
  have e0 : (c * a)⁻¹ * (c * b) = a * b := by
    rw [show (c * a)⁻¹ * (c * b) = a⁻¹ * b by group, tt_inv_eq hD ha]
  have e1 : (a * b) * c * (a * b)⁻¹ = (c * a)⁻¹ * b * (c * a) := by
    calc (a * b) * c * (a * b)⁻¹ = ((c * a)⁻¹ * (c * b)) * c * ((c * a)⁻¹ * (c * b))⁻¹ := by
          rw [e0]
      _ = (c * a)⁻¹ * ((c * b) * c * (c * b)⁻¹) * (c * a) := by group
      _ = (c * a)⁻¹ * b * (c * a) := by rw [hh]
  have e2 : c = (c * a)⁻¹ * a * (c * a) := by
    calc c = (c * a)⁻¹ * ((c * a) * c * (c * a)⁻¹) * (c * a) := by group
      _ = (c * a)⁻¹ * a * (c * a) := by rw [hg]
  have h := hRinv (c * a)⁻¹ b a (hRsymm a b hab)
  rw [inv_inv] at h
  rw [e1]
  rwa [← e2] at h

theorem vRel_mul_mem [Finite G] (hD : IsThreeTranspositions D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) (hab : VRel D a b) {c : G} (hc : c ∈ D) :
    VRel D ((a * b) * c * (a * b)⁻¹) c := by
  by_cases hca : c * a = a * c
  · have hcb : c * b = b * c := by
      have : c ∈ centralizerIn D b := by rw [← hab]; exact ⟨hc, hca⟩
      exact this.2
    rw [conj_eq_of_comm hca hcb]
    exact rfl
  · have hcb : c * b ≠ b * c := by
      intro h
      apply hca
      have : c ∈ centralizerIn D a := by rw [hab]; exact ⟨hc, h⟩
      exact this.2
    exact rel_conj_of_noncomm hD (VRel D) (fun g x y h => VRel.conj hD g h)
      (fun x y h => h.symm) ha hb hc hab hca hcb

theorem wRel_ne_or_noncomm {a b : G} (hb : b ∈ D)
    (hab : WRel D a b) : a = b ∨ a * b ≠ b * a := by
  by_cases h : a = b
  · exact Or.inl h
  · right
    intro hcomm
    have hmem : b ∈ localSet D a := ⟨hb, hcomm.symm, Ne.symm h⟩
    have : b ∈ localSet D b := by rw [← hab]; exact hmem
    exact this.2.2 rfl

theorem wRel_mul_mem [Finite G] (hD : IsThreeTranspositions D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) (hab : WRel D a b) {c : G} (hc : c ∈ D) :
    WRel D ((a * b) * c * (a * b)⁻¹) c := by
  rcases wRel_ne_or_noncomm hb hab with rfl | hnc
  · rw [tt_mul_self hD ha, one_mul, inv_one, mul_one]
    exact rfl
  · by_cases hca : c * a = a * c
    · by_cases hc_a : c = a
      · rw [hc_a, tt_conj_eq_of_noncomm' hD ha hb hnc]
        exact hab.symm
      · have hcb : c * b = b * c := by
          have : c ∈ localSet D b := by rw [← hab]; exact ⟨hc, hca, hc_a⟩
          exact this.2.1
        rw [conj_eq_of_comm hca hcb]
        exact rfl
    · by_cases hcb : c * b = b * c
      · by_cases hc_b : c = b
        · rw [hc_b]
          have e : (a * b) * b * (a * b)⁻¹ = a * b * a := by
            rw [mul_inv_rev, tt_inv_eq hD ha, tt_inv_eq hD hb]
            calc a * b * b * (b * a) = a * (b * b) * (b * a) := by simp only [mul_assoc]
              _ = a * b * a := by rw [tt_mul_self hD hb, mul_one, mul_assoc]
          rw [e]
          have h1 := WRel.conj hD a hab.symm
          have e1 : a * b * a⁻¹ = a * b * a := by rw [tt_inv_eq hD ha]
          have e2 : a * a * a⁻¹ = a := by rw [tt_mul_self hD ha, one_mul, tt_inv_eq hD ha]
          rw [e1, e2] at h1
          exact h1.trans hab
        · exfalso
          apply hca
          have : c ∈ localSet D a := by rw [hab]; exact ⟨hc, hcb, hc_b⟩
          exact this.2.1
      · exact rel_conj_of_noncomm hD (WRel D) (fun g x y h => WRel.conj hD g h)
          (fun x y h => h.symm) ha hb hc hab hca hcb

theorem inKer_closure (hD : IsThreeTranspositions D) (R : G → G → Prop)
    (hRsymm : ∀ x y : G, R x y → R y x) (hRtrans : ∀ x y z : G, R x y → R y z → R x z)
    (hRrefl : ∀ x : G, R x x) {S : Set G} (hS : ∀ s ∈ S, ∀ c ∈ D, R (s * c * s⁻¹) c) :
    ∀ g ∈ Subgroup.closure S, ∀ c ∈ D, R (g * c * g⁻¹) c := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => intro c _; simpa using hRrefl c
  | mul g h _ _ hg hh =>
    intro c hc
    have h1 := hg (h * c * h⁻¹) (tt_conj_mem hD hc h)
    have h2 := hh c hc
    have e : g * h * c * (g * h)⁻¹ = g * (h * c * h⁻¹) * g⁻¹ := by group
    rw [e]
    exact hRtrans _ _ _ h1 h2
  | inv g _ hg =>
    intro c hc
    have h1 := hg (g⁻¹ * c * g) (by simpa using tt_conj_mem hD hc g⁻¹)
    have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
    rw [e] at h1
    rw [inv_inv]
    exact hRsymm _ _ h1

@[expose] def prodSet (R : G → G → Prop) (D : Set G) (x : G) : Set G :=
  {s | ∃ a ∈ D, ∃ b ∈ D, R a x ∧ R b x ∧ s = a * b}

@[expose] def Xgrp (R : G → G → Prop) (D : Set G) (x : G) : Subgroup G :=
  Subgroup.closure (prodSet R D x)

section Xgrp

variable (hD : IsThreeTranspositions D) (R : G → G → Prop)
  (hRinv : ∀ (g x y : G), R x y → R (g * x * g⁻¹) (g * y * g⁻¹))
  (hRsymm : ∀ x y : G, R x y → R y x) (hRtrans : ∀ x y z : G, R x y → R y z → R x z)
  (hRrefl : ∀ x : G, R x x)
  (hker : ∀ a ∈ D, ∀ b ∈ D, R a b → ∀ c ∈ D, R ((a * b) * c * (a * b)⁻¹) c)

include hD hRsymm hRtrans hRrefl hker in
theorem Xgrp_inKer (x : G) : ∀ g ∈ Xgrp R D x, ∀ c ∈ D, R (g * c * g⁻¹) c := by
  refine inKer_closure hD R hRsymm hRtrans hRrefl ?_
  rintro _ ⟨a, ha, b, hb, hax, hbx, rfl⟩ c hc
  exact hker a ha b hb (hRtrans _ _ _ hax (hRsymm _ _ hbx)) c hc

include hD hRsymm hRtrans hRrefl hker in
theorem Xgrp_normalizes {x y : G} :
    Xgrp R D x ≤ Subgroup.normalizer (Xgrp R D y : Set G) := by
  have hA : ∀ g ∈ Xgrp R D x, ∀ h ∈ Xgrp R D y, g * h * g⁻¹ ∈ Xgrp R D y := by
    intro g hg h hh
    have hgk := Xgrp_inKer hD R hRsymm hRtrans hRrefl hker x g hg
    induction hh using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨a, ha, b, hb, hay, hby, rfl⟩ := hs
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      refine Subgroup.subset_closure ⟨_, tt_conj_mem hD ha g, _, tt_conj_mem hD hb g,
        hRtrans _ _ _ (hgk a ha) hay, hRtrans _ _ _ (hgk b hb) hby, rfl⟩
    | one => simp
    | mul h1 h2 _ _ ih1 ih2 =>
      have e : g * (h1 * h2) * g⁻¹ = (g * h1 * g⁻¹) * (g * h2 * g⁻¹) := by group
      rw [e]
      exact mul_mem ih1 ih2
    | inv h1 _ ih =>
      have e : g * h1⁻¹ * g⁻¹ = (g * h1 * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ih
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hA g hg h hh, fun hh => ?_⟩
  have := hA g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

include hD hRinv in
theorem Xgrp_conj {x : G} (g : G) {k : G} (hk : k ∈ Xgrp R D x) :
    g * k * g⁻¹ ∈ Xgrp R D (g * x * g⁻¹) := by
  induction hk using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨a, ha, b, hb, hax, hbx, rfl⟩ := hs
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.subset_closure ⟨_, tt_conj_mem hD ha g, _, tt_conj_mem hD hb g,
      hRinv g _ _ hax, hRinv g _ _ hbx, rfl⟩
  | one => simp
  | mul h1 h2 _ _ ih1 ih2 =>
    have e : g * (h1 * h2) * g⁻¹ = (g * h1 * g⁻¹) * (g * h2 * g⁻¹) := by group
    rw [e]
    exact mul_mem ih1 ih2
  | inv h1 _ ih =>
    have e : g * h1⁻¹ * g⁻¹ = (g * h1 * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ih

include hD hRinv hRsymm hRtrans hRrefl hker in
theorem Xgrp_le_pCore [Finite G] (p : ℕ) [Fact p.Prime] (hp : ∀ x ∈ D, IsPGroup p (Xgrp R D x)) :
    ∀ x ∈ D, Xgrp R D x ≤ CFSG.pCore p G := by
  intro x hx
  rw [Xgrp, Subgroup.closure_le]
  intro s hs
  have hsX : s ∈ Xgrp R D x := Subgroup.subset_closure hs
  refine CFSG.BaerSuzuki.baer_suzuki s ?_ ?_
  · exact (hp x hx).to_le (Subgroup.zpowers_le.2 hsX)
  · intro g
    have hgx : g * x * g⁻¹ ∈ D := tt_conj_mem hD hx g
    have hY := (hp x hx).to_sup_of_normal_right' (hp _ hgx)
      (Xgrp_normalizes hD R hRsymm hRtrans hRrefl hker)
    refine hY.to_le ?_
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact Subgroup.mem_sup_left hsX
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.mem_sup_right (Xgrp_conj hD R hRinv g hsX)

end Xgrp

end CFSG.RankThree.PartOne.FIS
