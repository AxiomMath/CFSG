module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13T

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem map_conj_J {g : G} (hg : g ∈ H z) : (J z).map (MulAut.conj g).toMonoidHom = J z := by
  apply le_antisymm
  · rintro _ ⟨j, hj, rfl⟩
    exact conj_mem_J hg hj
  · intro j hj
    refine ⟨g⁻¹ * j * g⁻¹⁻¹, conj_mem_J ((H z).inv_mem hg) hj, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_commutator_conj_iff {g σ : G} (hg : g ∈ H z) (hgσ : g * σ = σ * g) (a : G) :
    a ∈ ⁅zpowers σ, J z⁆ ↔ g * a * g⁻¹ ∈ ⁅zpowers σ, J z⁆ := by
  have hmap : ∀ x : G, x ∈ H z → x * σ = σ * x →
      ⁅zpowers σ, J z⁆.map (MulAut.conj x).toMonoidHom = ⁅zpowers σ, J z⁆ := by
    intro x hx hxσ
    rw [Subgroup.map_commutator, map_conj_J hx, MonoidHom.map_zpowers]
    congr 2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxσ, mul_inv_cancel_right]
  have hgσ' : g⁻¹ * σ = σ * g⁻¹ := by
    calc g⁻¹ * σ = g⁻¹ * (σ * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * σ) * g⁻¹ := by rw [hgσ]
      _ = σ * g⁻¹ := by group
  constructor
  · intro ha
    rw [← hmap g hg hgσ]
    exact ⟨a, ha, by simp⟩
  · intro ha
    have h := hmap g⁻¹ ((H z).inv_mem hg) hgσ'
    rw [← h]
    exact ⟨g * a * g⁻¹, ha, by simp [mul_assoc]⟩

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem commute_of_cube {g a : G} (hg : g ∈ H z) (hg3 : g ^ 3 = 1)
    (ha : g * a * g⁻¹ * a⁻¹ ∈ zpowers z) : g * a = a * g := by
  set d := g * a * g⁻¹ * a⁻¹ with hd
  have hgd : g * d = d * g := hy.commute_of_mem_zpowers_of_mem_H hg ha
  have hd2 : d * d = 1 := by
    rcases hy.mem_zpowers_z_iff.mp ha with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hy.z_sq]
  have hg3' : g * g * g = 1 := by rw [← hg3, pow_succ, pow_two]
  have h1 : g * a * g⁻¹ = d * a := by rw [hd]; group
  have h2 : g * (g * a * g⁻¹) * g⁻¹ = d * d * a := by
    calc g * (g * a * g⁻¹) * g⁻¹ = g * (d * a) * g⁻¹ := by rw [h1]
      _ = (g * d) * a * g⁻¹ := by group
      _ = (d * g) * a * g⁻¹ := by rw [hgd]
      _ = d * (g * a * g⁻¹) := by group
      _ = d * (d * a) := by rw [h1]
      _ = d * d * a := by group
  have h3 : g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = d * a := by
    calc g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = g * (d * d * a) * g⁻¹ := by rw [h2]
      _ = g * a * g⁻¹ := by rw [hd2, one_mul]
      _ = d * a := h1
  have h4 : g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = a := by
    calc g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * a * (g * g * g)⁻¹ := by group
      _ = a := by rw [hg3']; group
  have hd1 : d = 1 := by
    have e : a = d * a := h4.symm.trans h3
    calc d = d * a * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [← e]
      _ = 1 := mul_inv_cancel a
  have : g * a * g⁻¹ * a⁻¹ = 1 := hd1
  calc g * a = g * a * g⁻¹ * a⁻¹ * (a * g) := by group
    _ = a * g := by rw [this, one_mul]

theorem W_eq : ⁅zpowers s1, J z⁆ = J z ⊓ Subgroup.centralizer (CJ z s1 : Set G) := by
  apply le_antisymm
  · intro w hw
    refine ⟨hy.W_le_J hw, Subgroup.mem_centralizer_iff.mpr fun a ha => hy.comm1 a ha w hw⟩
  · rintro x ⟨hxJ, hxc⟩
    obtain ⟨a, ha, w, hw, rfl⟩ := hy.exists_mul_J0_W hxJ
    have haz : a ∈ zpowers z := by
      apply hy.mem_zpowers_of_mem_J0_of_commute ha
      intro b hb
      have h1 : b * (a * w) = (a * w) * b := Subgroup.mem_centralizer_iff.mp hxc b hb
      have h2 : w * b = b * w := (hy.comm1 b hb w hw).symm
      have e : (a * w) * b * w⁻¹ = a * b := by
        calc (a * w) * b * w⁻¹ = a * (w * b) * w⁻¹ := by group
          _ = a * (b * w) * w⁻¹ := by rw [h2]
          _ = a * b := by group
      calc a * b = (a * w) * b * w⁻¹ := e.symm
        _ = b * (a * w) * w⁻¹ := by rw [← h1]
        _ = b * a := by group
    exact (⁅zpowers s1, J z⁆).mul_mem (hy.zpowers_le_W haz) hw

theorem mem_Q_conj_s1_iff (a : G) : a ∈ hy.Q ↔ s1 * a * s1⁻¹ ∈ hy.Q := by
  have hs1s : s1 * (s1 * s2⁻¹) = (s1 * s2⁻¹) * s1 := by
    have h : s1 * s2⁻¹ = s2⁻¹ * s1 := by
      calc s1 * s2⁻¹ = s2⁻¹ * (s2 * s1) * s2⁻¹ := by group
        _ = s2⁻¹ * (s1 * s2) * s2⁻¹ := by rw [hy.comm12]
        _ = s2⁻¹ * s1 := by group
    calc s1 * (s1 * s2⁻¹) = s1 * (s2⁻¹ * s1) := by rw [h]
      _ = (s1 * s2⁻¹) * s1 := by group
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_CJ_conj_iff hy.s1_mem hs1s a).mp h1,
      (mem_commutator_conj_iff hy.s1_mem rfl a).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_CJ_conj_iff hy.s1_mem hs1s a).mpr h1,
      (mem_commutator_conj_iff hy.s1_mem rfl a).mpr h2⟩

theorem mem_zpowers_of_mem_Q_of_commute_s1 {q : G} (hq : q ∈ hy.Q) (hqs : s1 * q = q * s1) :
    q ∈ zpowers z := by
  rw [← hy.inf1]
  refine ⟨mem_CJ.mpr ⟨?_, (CJ_le_J _) hq.1⟩, hq.2⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hqs.symm

theorem s1_pow_three : s1 ^ 3 = 1 := by
  rw [← hy.orderOf_s1, pow_orderOf_eq_one]

theorem commute_of_mem_Q {b : G} (hb : b ∈ H z) (hbQ : ∀ a : G, a ∈ hy.Q ↔ b * a * b⁻¹ ∈ hy.Q)
    {k : ℕ} (hbk : b ^ 2 ^ k = 1)
    (hbs : ∀ q ∈ hy.Q, b * (s1 * q * s1⁻¹) * b⁻¹ = s1 * (b * q * b⁻¹) * s1⁻¹) :
    ∀ q ∈ hy.Q, b * q = q * b := by
  have hQJ : hy.Q ≤ J z := fun q hq => (CJ_le_J _) hq.1
  have hB : Nat.card (imV z hy.Q) = 4 := by
    have h := card_imV hy.hA1 hQJ hy.zpowers_le_Q
    rw [hy.card_Q] at h
    omega
  set B := imV z hy.Q with hBdef
  set bH : ↥(H z) := ⟨b, hb⟩
  set sH : ↥(H z) := ⟨s1, hy.s1_mem⟩
  have hφ : ∀ v, conjVA z bH v ∈ B ↔ v ∈ B :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_Q bH hbQ
  have hβ : ∀ v, conjVA z sH v ∈ B ↔ v ∈ B :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_Q sH hy.mem_Q_conj_s1_iff
  have hβ3 : ∀ v ∈ B, (conjVA z sH ^ 3) v = v := by
    intro v _
    have : sH ^ 3 = 1 := Subtype.ext (by simpa [sH] using hy.s1_pow_three)
    rw [← map_pow, this, map_one]
    rfl
  have hβfix : ∀ v ∈ B, conjVA z sH v = v → v = 1 := by
    intro v hv hfix
    obtain ⟨q, hq, rfl⟩ := mem_imV.mp hv
    have hc := (conjVA_pi_eq_iff hy.hA1 sH q).mp hfix
    have hcomm := hy.commute_of_cube hy.s1_mem hy.s1_pow_three hc
    exact (pi_eq_one_iff hy.hA1).mpr (hy.mem_zpowers_of_mem_Q_of_commute_s1 hq hcomm)
  have hk : ∀ v ∈ B, (conjVA z bH ^ 2 ^ k) v = v := by
    intro v _
    have : bH ^ 2 ^ k = 1 := Subtype.ext (by simpa [bH] using hbk)
    rw [← map_pow, this, map_one]
    rfl
  have hβφ : ∀ v ∈ B, conjVA z sH (conjVA z bH v) = conjVA z bH (conjVA z sH v) := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := mem_imV.mp hv
    rw [conjVA_pi, conjVA_pi, conjVA_pi, conjVA_pi]
    congr 1
    apply Subtype.ext
    exact (hbs q hq).symm
  have hA := apply_eq_of_commute_of_cube B hB (conjVA z sH) (conjVA z bH) hβ hφ hβ3 hβfix hk hβφ
  have hd : ∀ q ∈ hy.Q, b * q * b⁻¹ * q⁻¹ ∈ zpowers z := by
    intro q hq
    exact (conjVA_pi_eq_iff hy.hA1 bH ⟨q, hQJ hq⟩).mp (hA _ (pi_mem_imV hq))
  have hsum : ∀ q ∈ hy.Q, q * (s1 * q * s1⁻¹) * (s1 * (s1 * q * s1⁻¹) * s1⁻¹) ∈ zpowers z := by
    intro q hq
    have hq1 : s1 * q * s1⁻¹ ∈ hy.Q := (hy.mem_Q_conj_s1_iff q).mp hq
    have hq2 : s1 * (s1 * q * s1⁻¹) * s1⁻¹ ∈ hy.Q := (hy.mem_Q_conj_s1_iff _).mp hq1
    have hmem : q * (s1 * q * s1⁻¹) * (s1 * (s1 * q * s1⁻¹) * s1⁻¹) ∈ hy.Q :=
      hy.Q.mul_mem (hy.Q.mul_mem hq hq1) hq2
    set v := pi z ⟨q, hQJ hq⟩ with hv
    have hv1 : conjVA z sH v = pi z ⟨s1 * q * s1⁻¹, hQJ hq1⟩ := conjVA_pi sH _
    have hv2 : conjVA z sH (conjVA z sH v) = pi z ⟨s1 * (s1 * q * s1⁻¹) * s1⁻¹, hQJ hq2⟩ := by
      rw [hv1, conjVA_pi]
    have hv3 : conjVA z sH (conjVA z sH (conjVA z sH v)) = v := by
      have h3 := hβ3 v (pi_mem_imV hq)
      simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply] using h3
    have hpi : pi z ⟨q * (s1 * q * s1⁻¹) * (s1 * (s1 * q * s1⁻¹) * s1⁻¹), hQJ hmem⟩ =
        v * conjVA z sH v * conjVA z sH (conjVA z sH v) := by
      rw [hv2, hv1, ← map_mul, ← map_mul]
      rfl
    rw [← pi_eq_one_iff hy.hA1 (a := ⟨_, hQJ hmem⟩)]
    apply hβfix _ (pi_mem_imV hmem)
    rw [hpi, map_mul, map_mul, hv3,
      V_comm hy.hA1 (conjVA z sH v * conjVA z sH (conjVA z sH v)) v, mul_assoc]
  intro q hq
  set d := b * q * b⁻¹ * q⁻¹ with hd_def
  have hdz : d ∈ zpowers z := hd q hq
  have hd2 : d * d = 1 := by
    rcases hy.mem_zpowers_z_iff.mp hdz with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hy.z_sq]
  have hdq : ∀ x ∈ hy.Q, x * d = d * x := fun x hx =>
    hy.commute_of_mem_zpowers_of_mem_H (J_le_H (hQJ hx)) hdz
  have hs1d : s1 * d = d * s1 := hy.commute_of_mem_zpowers_of_mem_H hy.s1_mem hdz
  have hq1 : s1 * q * s1⁻¹ ∈ hy.Q := (hy.mem_Q_conj_s1_iff q).mp hq
  have hbq : b * q * b⁻¹ = d * q := by rw [hd_def]; group
  have hbq1 : b * (s1 * q * s1⁻¹) * b⁻¹ = d * (s1 * q * s1⁻¹) := by
    rw [hbs q hq, hbq]
    calc s1 * (d * q) * s1⁻¹ = (s1 * d) * q * s1⁻¹ := by group
      _ = (d * s1) * q * s1⁻¹ := by rw [hs1d]
      _ = d * (s1 * q * s1⁻¹) := by group
  have hbq2 : b * (s1 * (s1 * q * s1⁻¹) * s1⁻¹) * b⁻¹ = d * (s1 * (s1 * q * s1⁻¹) * s1⁻¹) := by
    rw [hbs _ hq1, hbq1]
    calc s1 * (d * (s1 * q * s1⁻¹)) * s1⁻¹ = (s1 * d) * (s1 * q * s1⁻¹) * s1⁻¹ := by group
      _ = (d * s1) * (s1 * q * s1⁻¹) * s1⁻¹ := by rw [hs1d]
      _ = d * (s1 * (s1 * q * s1⁻¹) * s1⁻¹) := by group
  set q' := s1 * q * s1⁻¹ with hq'
  set q'' := s1 * q' * s1⁻¹ with hq''
  have hpz := hsum q hq
  have hbp : b * (q * q' * q'') * b⁻¹ = q * q' * q'' := conj_eq_of_mem_zpowers hb hpz
  have hbp' : b * (q * q' * q'') * b⁻¹ = d * (q * q' * q'') := by
    calc b * (q * q' * q'') * b⁻¹ = (b * q * b⁻¹) * (b * q' * b⁻¹) * (b * q'' * b⁻¹) := by group
      _ = (d * q) * (d * q') * (d * q'') := by rw [hbq, hbq1, hbq2]
      _ = d * (q * d) * q' * (d * q'') := by group
      _ = d * (d * q) * q' * (d * q'') := by rw [hdq q hq]
      _ = d * d * q * (q' * d) * q'' := by group
      _ = d * d * q * (d * q') * q'' := by rw [hdq q' hq1]
      _ = d * d * (q * d) * q' * q'' := by group
      _ = d * d * (d * q) * q' * q'' := by rw [hdq q hq]
      _ = (d * d) * d * (q * q' * q'') := by group
      _ = d * (q * q' * q'') := by rw [hd2, one_mul]
  have hd1 : d = 1 := by
    have h := hbp.symm.trans hbp'
    calc d = d * (q * q' * q'') * (q * q' * q'')⁻¹ := by group
      _ = (q * q' * q'') * (q * q' * q'')⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  calc b * q = b * q * b⁻¹ * q⁻¹ * (q * b) := by group
    _ = d * (q * b) := by rw [hd_def]
    _ = q * b := by rw [hd1, one_mul]

end Hyp

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
