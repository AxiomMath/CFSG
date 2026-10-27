module

public import CFSG.RankThree.GF2n.Tim78S42
import CFSG.RankThree.GF2n.Tim78Critical
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78Normal

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified


theorem exists_mem_B_of_normalizes {N D : Subgroup G} (hNQ : N ≤ Q) (hBN : B ≤ N)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hDN : D ≤ N) (hD : D ≠ ⊥)
    (hND : N ≤ Subgroup.normalizer (D : Set G)) : ∃ b ∈ D, b ∈ B ∧ b ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : IsPGroup 2 N := H.isPGroup_Q.to_le hNQ
  haveI : Group.IsNilpotent ↥N := hN2.isNilpotent
  haveI : (D.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDN).mpr hND
  have hne : D.subgroupOf N ≠ ⊥ := by
    obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    intro hbot
    have h1 : (⟨d, hDN hd⟩ : ↥N) ∈ D.subgroupOf N := hd
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : d = 1 := congrArg Subtype.val h1
    exact hd1 (Subtype.ext h2)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hxD : (x : G) ∈ D := (Subgroup.mem_inf.mp hxmem).1
  have hxZ : x ∈ Subgroup.center ↥N := (Subgroup.mem_inf.mp hxmem).2
  have hxC : (x : G) ∈ N ⊓ Subgroup.centralizer (N : Set G) := (mem_center_iff_mem_inf x).mp hxZ
  rw [H.inf_centralizer_eq_B hBN hNQ hMN] at hxC
  refine ⟨x, hxD, hxC, fun h1 => hx1 ?_⟩
  exact Subtype.ext (Subtype.ext h1)


theorem le_Q_of_stabilizes {A : Subgroup G} (hAM : A ≤ M)
    (h : ∀ m ∈ M, ∀ a ∈ conjSubgroup m A, ∀ r ∈ Q, ⁅a, r⁆ ∈ B) : A ≤ Q := by
  classical
  have hMB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B := fun m hm b hb =>
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B hm) b).mp hb
  have hMQ : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_Q hm) q).mp hq
  let K : Subgroup G :=
    { carrier := {a | a ∈ M ∧ ∀ r ∈ Q, ⁅a, r⁆ ∈ B}
      one_mem' := ⟨M.one_mem, fun r _ => by
        rw [commutatorElement_one_left]
        exact B.one_mem⟩
      mul_mem' := by
        rintro a₁ a₂ ⟨ha₁M, ha₁⟩ ⟨ha₂M, ha₂⟩
        refine ⟨M.mul_mem ha₁M ha₂M, fun r hr => ?_⟩
        have e : ⁅a₁ * a₂, r⁆ = a₁ * ⁅a₂, r⁆ * a₁⁻¹ * ⁅a₁, r⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact B.mul_mem (hMB a₁ ha₁M _ (ha₂ r hr)) (ha₁ r hr)
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨M.inv_mem haM, fun r hr => ?_⟩
        have e : ⁅a⁻¹, r⁆ = a⁻¹ * ⁅a, r⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hMB a⁻¹ (M.inv_mem haM) _ (B.inv_mem (ha r hr))
        rwa [inv_inv] at this }
  have hKM : K ≤ M := fun a ha => ha.1
  have hKn : M ≤ Subgroup.normalizer (K : Set G) := fun m hm => by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    refine ⟨M.mul_mem (M.mul_mem hm (hKM ha)) (M.inv_mem hm), fun r hr => ?_⟩
    have e : ⁅m * a * m⁻¹, r⁆ = m * ⁅a, m⁻¹ * r * m⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hMB m hm _ (ha.2 _ (by simpa using hMQ m⁻¹ (M.inv_mem hm) r hr))
  have hodd : ∀ c ∈ K, ∀ r : ℕ, r.Prime → r ≠ 2 → orderOf c = r → False := by
    intro c hcK r hr hr2 hcr
    have hcM := hKM hcK
    have htriv : ∀ k : ℤ, ∀ s ∈ Q, s⁻¹ * (c ^ k * s * (c ^ k)⁻¹) ∈ inSubgroup frattini Q := by
      intro k s hs
      have hck : c ^ k ∈ K := K.zpow_mem hcK k
      have h1 := hck.2 s hs
      have h2 := H.center_Q h1 hs
      have e : s⁻¹ * (c ^ k * s * (c ^ k)⁻¹) = ⁅c ^ k, s⁆ := by
        have e1 : c ^ k * s * (c ^ k)⁻¹ = ⁅c ^ k, s⁆ * s := by
          simp only [commutatorElement_def]; group
        rw [e1, h2]
        group
      rw [H.base_facts.1, e]
      exact h1
    have hcQ' : ∀ s ∈ Q, c * s = s * c :=
      commute_of_trivial_on_frattini H.isPGroup_Q (H.M_le_normalizer_Q hcM) hr hr2 hcr htriv
    have hCQ := inf_centralizer_le_of_generalizedFitting_eq H.fitting
    rw [← H.hQ] at hCQ
    have hcQ : c ∈ Q := hCQ ⟨hcM, Subgroup.mem_centralizer_iff.mpr fun s hs => (hcQ' s hs).symm⟩
    have hc1 := eq_one_of_odd_of_isPGroup H.isPGroup_Q hcQ (by rw [hcr]; exact hr.odd_of_ne_two hr2)
    rw [hc1, orderOf_one] at hcr
    exact hr.one_lt.ne' hcr.symm
  have hK2 : IsPGroup 2 K := by
    intro t
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (t : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    set u := (t : G) ^ 2 ^ a with hu
    have huK : u ∈ K := K.pow_mem t.2 _
    by_contra hu1
    have hne : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hrd)
    have hpos : orderOf u ≠ 0 := (orderOf_pos u).ne'
    exact hodd _ (K.pow_mem huK _) r hr hr2 (orderOf_pow_orderOf_div hpos hrd)
  have hKQ : K ≤ Q := H.hQ ▸ le_inSubgroup_pCore hKM hKn hK2
  intro a ha
  exact hKQ ⟨hAM ha, fun r hr => h 1 M.one_mem a (by rwa [conjSubgroup_one]) r hr⟩


omit H in
theorem mem_normalizer_conj_of_mem_conj {N : Subgroup G} (hMN : M ≤ Subgroup.normalizer (N : Set G))
    {g m : G} (hm : m ∈ conjSubgroup g M) : m ∈ Subgroup.normalizer (conjSubgroup g N : Set G) := by
  rw [normalizer_conjSubgroup]
  exact Subgroup.map_mono hMN hm

theorem le_conj_Q_of_commutator_mem {g : G} (hBM : B ≤ conjSubgroup g M)
    (h : ∀ b ∈ B, ∀ s ∈ conjSubgroup g Q, ⁅b, s⁆ ∈ conjSubgroup g B) :
    B ≤ conjSubgroup g Q := by
  have hA : conjSubgroup g⁻¹ B ≤ M := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hBM hz
    rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  have hst := H.le_Q_of_stabilizes hA fun m hm a ha r hr => by
    rw [mem_conjSubgroup, mem_conjSubgroup, inv_inv] at ha
    have hm1 : g * m * g⁻¹ ∈ conjSubgroup g M := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * m * g⁻¹) * g = m by group]
      exact hm
    have hr1 : g * r * g⁻¹ ∈ conjSubgroup g Q := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * r * g⁻¹) * g = r by group]
      exact hr
    have hs : (g * m * g⁻¹)⁻¹ * (g * r * g⁻¹) * (g * m * g⁻¹) ∈ conjSubgroup g Q := by
      have := (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_conj_of_mem_conj H.M_le_normalizer_Q (Subgroup.inv_mem _ hm1)) _).mp hr1
      simpa using this
    have h1 := h _ ha _ hs
    have h2 : g * m * g⁻¹ * ⁅g * (m⁻¹ * a * m) * g⁻¹, (g * m * g⁻¹)⁻¹ * (g * r * g⁻¹) *
        (g * m * g⁻¹)⁆ * (g * m * g⁻¹)⁻¹ ∈ conjSubgroup g B :=
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_conj_of_mem_conj H.M_le_normalizer_B hm1) _).mp h1
    rw [mem_conjSubgroup] at h2
    have e : ⁅a, r⁆ = g⁻¹ * (g * m * g⁻¹ * ⁅g * (m⁻¹ * a * m) * g⁻¹, (g * m * g⁻¹)⁻¹ *
        (g * r * g⁻¹) * (g * m * g⁻¹)⁆ * (g * m * g⁻¹)⁻¹) * g := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h2
  intro b hb
  rw [mem_conjSubgroup]
  exact hst (by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hb)


theorem frattini_conj_le {g : G} {N : Subgroup G} (hNQ : N ≤ Q) :
    inSubgroup frattini (conjSubgroup g N) ≤ conjSubgroup g B := by
  have hS2 : IsPGroup 2 (conjSubgroup g N) := (H.isPGroup_Q.to_le hNQ).map _
  refine inSubgroup_frattini_le_of_sq hS2 (fun s hs => ?_) (fun a ha b hb => ?_)
  · rw [mem_conjSubgroup] at hs ⊢
    rw [show g⁻¹ * s ^ 2 * g = (g⁻¹ * s * g) ^ 2 by rw [sq, sq]; group]
    exact H.sq_mem (hNQ hs)
  · rw [mem_conjSubgroup] at ha hb ⊢
    rw [show g⁻¹ * ⁅a, b⁆ * g = ⁅g⁻¹ * a * g, g⁻¹ * b * g⁆ by
      simp only [commutatorElement_def]; group]
    exact H.commutator_mem (hNQ ha) (hNQ hb)

theorem conj_B_le_center {g : G} {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q) :
    conjSubgroup g B ≤ conjSubgroup g N ⊓ Subgroup.centralizer (conjSubgroup g N : Set G) := by
  intro b hb
  rw [mem_conjSubgroup] at hb
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
  · rw [mem_conjSubgroup]
    exact hBN hb
  · have hs' := hs
    rw [SetLike.mem_coe, mem_conjSubgroup] at hs'
    have := H.center_Q hb (hNQ hs')
    calc s * b = g * ((g⁻¹ * s * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = b * s := by group

theorem comm_sq_mem_conj {g : G} {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hTN : T ≤ Subgroup.normalizer (conjSubgroup g N : Set G))
    (hNT : conjSubgroup g N ⊓ T = ⊥) {y : G} (hy : y ∈ T) :
    ∀ s ∈ conjSubgroup g N, s⁻¹ * (y ^ 2 * s * (y ^ 2)⁻¹) ∈ conjSubgroup g B := by
  intro s hs
  by_cases hy2 : y ^ 2 = 1
  · rw [hy2]
    simpa using (conjSubgroup g B).one_mem
  set S := conjSubgroup g N with hSdef
  have hS2 : IsPGroup 2 S := (H.isPGroup_Q.to_le hNQ).map _
  have hΦ : inSubgroup frattini S ≤ S ⊓ Subgroup.centralizer (S : Set G) :=
    (H.frattini_conj_le hNQ).trans (H.conj_B_le_center hBN hNQ)
  have hyB : y ^ 2 ∈ B := H.sq_mem (H.T_le_Q hy)
  have hx : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := H.isPGroup_Q ⟨y, H.T_le_Q hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hC : S ⊓ Subgroup.centralizer ({y} : Set G) =
      S ⊓ Subgroup.centralizer ({y ^ 2} : Set G) := by
    apply le_antisymm
    · intro c hc
      have hc2 : c * y = y * c :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
      have h0 : Commute c y := hc2
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hc).1,
        Subgroup.mem_centralizer_singleton_iff.mpr (h0.pow_right 2)⟩
    · intro c hc
      obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
      have hcM : c ∈ M := H.normalizer_eq_and_centralizer_le.2 _ hyB hy2 hcC
      have h1 : ⁅c, y⁆ ∈ S := by
        have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact S.mul_mem hcS ((Subgroup.mem_normalizer_iff.mp (hTN hy) c⁻¹).mp (S.inv_mem hcS))
      have h2 : ⁅c, y⁆ ∈ T := by
        have e : ⁅c, y⁆ = (c * y * c⁻¹) * y⁻¹ := by
          simp only [commutatorElement_def]
        rw [e]
        exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T hcM) y).mp hy)
          (T.inv_mem hy)
      have h3 : ⁅c, y⁆ ∈ S ⊓ T := ⟨h1, h2⟩
      rw [hNT, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
      exact Subgroup.mem_inf.mpr ⟨hcS, Subgroup.mem_centralizer_singleton_iff.mpr h3⟩
  exact H.frattini_conj_le hNQ ((tim78_2_2 hS2 hΦ (hTN hy) hx hC).2 s hs)


omit H in
theorem commutator_eq_one_of_rotate {x y z : G} (h1 : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ = 1)
    (h2 : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ = 1) : ⁅z, ⁅x, y⁆⁆ = 1 := by
  have e : ⁅z, ⁅x, y⁆⁆ = x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [e, h1, h2]
  group


theorem conj_T_le_centralizer_conj_P (g : G) :
    ∀ s ∈ conjSubgroup g T, ∀ a ∈ conjSubgroup g P, s * a = a * s := by
  intro s hs a ha
  rw [mem_conjSubgroup] at hs ha
  have := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P hs) _ ha
  calc s * a = g * ((g⁻¹ * s * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [← this]
    _ = a * s := by group

end Certified

end Hyp4

end CFSG.RankThree.GF2n.Tim78
