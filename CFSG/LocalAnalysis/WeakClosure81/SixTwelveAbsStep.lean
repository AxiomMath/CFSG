module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsSub
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsBlock
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.RankThree.GF2n (QuotPair pairConj)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Abs612

variable {T T₁ Z E : Subgroup X}

theorem conjSubgroup_le_E_of_fix (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1)
    {x : X} (hx : conjSubgroup s (conjSubgroup x T) = conjSubgroup x T) :
    conjSubgroup x T ≤ E := by
  exact h.le_E s hs hs1 x (CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.1 hx)

theorem commute_of_fix (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1) {x : X}
    (hx : conjSubgroup s (conjSubgroup x T) = conjSubgroup x T) {a : X}
    (ha : a ∈ conjSubgroup x T) : s * a = a * s := by
  have hsE : s ∈ E := h.le_E₁ hs
  have haE : a ∈ E := conjSubgroup_le_E_of_fix h hs hs1 hx ha
  have hmemZ : ⁅s, a⁆ ∈ Z := h.comm_E s hsE a haE
  have hsN : s ∈ Subgroup.normalizer (conjSubgroup x T : Set X) :=
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.1 hx
  have hmem : s * a * s⁻¹ ∈ conjSubgroup x T := (Subgroup.mem_normalizer_iff.1 hsN a).1 ha
  have hmemT : ⁅s, a⁆ ∈ conjSubgroup x T := by
    rw [commutatorElement_def]
    exact (conjSubgroup x T).mul_mem hmem ((conjSubgroup x T).inv_mem ha)
  have hbot : ⁅s, a⁆ ∈ (⊥ : Subgroup X) := by
    rw [← h.inf_Z_conj x]
    exact Subgroup.mem_inf.2 ⟨hmemT, hmemZ⟩
  exact (commutatorElement_eq_one_iff_mul_comm).1 (Subgroup.mem_bot.1 hbot)

private def b612_conjRestrict (Y : Subgroup X) {s : X}
    (hs : s ∈ Subgroup.normalizer (Y : Set X)) : ↥Y ≃* ↥Y where
  toFun z := ⟨s * z * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs z).mp z.2⟩
  invFun z := ⟨s⁻¹ * z * s, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) z).mp z.2
    rwa [inv_inv] at this⟩
  left_inv z := Subtype.ext (by simp only; group)
  right_inv z := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

section Certified

theorem exists_inner_sub (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1) {y : X}
    (hy : y ∈ T ⊔ conjSubgroup s T) (hc : ∀ a ∈ conjSubgroup y T, s * a = a * s) :
    ∃ t ∈ conjSubgroup y T, ∀ k ∈ T ⊔ conjSubgroup s T, s * k * s⁻¹ = t * k * t⁻¹ := by
  have hss : s * s = 1 := h.elem₁.mul_self_eq_one hs
  have hconjY : conjSubgroup s (T ⊔ conjSubgroup s T) = T ⊔ conjSubgroup s T := by
    have hmap : conjSubgroup s (T ⊔ conjSubgroup s T) =
        conjSubgroup s T ⊔ conjSubgroup s (conjSubgroup s T) :=
      Subgroup.map_sup T (conjSubgroup s T) (MulAut.conj s).toMonoidHom
    rw [hmap, ← CFSG.RankThree.GF2n.conjSubgroup_mul, hss,
      CFSG.CGT.Timmesfeld75.conjSubgroup_one, sup_comm]
  have hsY : s ∈ Subgroup.normalizer ((T ⊔ conjSubgroup s T : Subgroup X) : Set X) :=
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.1 hconjY
  let σ : MulAut ↥(T ⊔ conjSubgroup s T) :=
    b612_conjRestrict (T ⊔ conjSubgroup s T) hsY
  have hσ2 : ∀ k, σ (σ k) = k := by
    intro k
    apply Subtype.ext
    change s * (s * (k : X) * s⁻¹) * s⁻¹ = (k : X)
    calc s * (s * (k : X) * s⁻¹) * s⁻¹ = (s * s) * (k : X) * (s * s)⁻¹ := by group
      _ = (k : X) := by rw [hss, one_mul, inv_one, mul_one]
  have hcard : Nat.card (T.subgroupOf (T ⊔ conjSubgroup s T)) = Nat.card T :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ conjSubgroup s T)).toEquiv
  have h4 : 4 ≤ Nat.card (T.subgroupOf (T ⊔ conjSubgroup s T)) := by
    rw [hcard]
    exact h.four_le
  have hC : (conjSubgroup y T).subgroupOf (T ⊔ conjSubgroup s T) ∈
      pairConj (T.subgroupOf (T ⊔ conjSubgroup s T))
        ((conjSubgroup s T).subgroupOf (T ⊔ conjSubgroup s T)) :=
    ⟨⟨y, hy⟩, Or.inl (CFSG.CGT.Timmesfeld75.conjSubgroup_subgroupOf
      (T ⊔ conjSubgroup s T) T ⟨y, hy⟩).symm⟩
  have hfix : ∀ c ∈ (conjSubgroup y T).subgroupOf (T ⊔ conjSubgroup s T), σ c = c := by
    intro c hc'
    apply Subtype.ext
    have hcT : (c : X) ∈ conjSubgroup y T := Subgroup.mem_subgroupOf.1 hc'
    have hcomm := hc (c : X) hcT
    change s * (c : X) * s⁻¹ = (c : X)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨t', ht'C, ht'⟩ :=
    exists_inner_of_fix (h.quotPair_sub hs hs1) h4 hC σ hσ2 hfix
  refine ⟨(t' : X), Subgroup.mem_subgroupOf.1 ht'C, ?_⟩
  intro k hk
  have hv := congrArg (Subtype.val) (ht' ⟨k, hk⟩)
  have hσk : (σ ⟨k, hk⟩ : X) = s * k * s⁻¹ := by
    change s * ((⟨k, hk⟩ : ↥(T ⊔ conjSubgroup s T)) : X) * s⁻¹ = s * k * s⁻¹
    rfl
  rw [hσk] at hv
  simpa using hv

theorem exists_eq_mul_central (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1) {y : X}
    (hy : y ∈ T ⊔ conjSubgroup s T)
    (hx : conjSubgroup s (conjSubgroup y T) = conjSubgroup y T) :
    ∃ t ∈ conjSubgroup y T, ∃ z ∈ Z, s = t * z := by
  have hle : conjSubgroup y T ≤ E := conjSubgroup_le_E_of_fix h hs hs1 hx
  have hc : ∀ a ∈ conjSubgroup y T, s * a = a * s :=
    fun a ha => commute_of_fix h hs hs1 hx ha
  obtain ⟨t, ht, hst⟩ := h.exists_inner_sub hs hs1 hy hc
  have htE : t ∈ E := hle ht
  have hsE : s ∈ E := h.le_E₁ hs
  set e : X := t⁻¹ * s with he
  have heE : e ∈ E := by
    rw [he]
    exact E.mul_mem (E.inv_mem htE) hsE
  have heZ : e ∈ Z := by
    refine h.mem_Z e heE (fun a ha => ?_)
    have hsa : s * a * s⁻¹ = t * a * t⁻¹ :=
      hst a ((le_sup_left : T ≤ T ⊔ conjSubgroup s T) ha)
    rw [he]
    rw [show t⁻¹ * s * a = t⁻¹ * (s * a) by group,
      show s * a = t * a * t⁻¹ * s by
        calc s * a = s * a * s⁻¹ * s := by group
          _ = t * a * t⁻¹ * s := by rw [hsa]]
    group
  exact ⟨t, ht, e, heZ, by rw [he]; group⟩

theorem exists_conj_of_mem_conj_sub (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1)
    {y : X} (hy : y ∈ T ⊔ conjSubgroup s T) {a b : X} (ha : a ∈ conjSubgroup y T) (ha1 : a ≠ 1)
    (hb : b ∈ conjSubgroup y T) (hb1 : b ≠ 1) : ∃ g : X, g * a * g⁻¹ = b := by
  have hle : conjSubgroup y T ≤ T ⊔ conjSubgroup s T := by
    intro c hc
    have hw : y⁻¹ * c * y ∈ T := mem_conjSubgroup.1 hc
    have hwY : y⁻¹ * c * y ∈ T ⊔ conjSubgroup s T :=
      (le_sup_left : T ≤ T ⊔ conjSubgroup s T) hw
    have hmem : y * (y⁻¹ * c * y) * y⁻¹ ∈ T ⊔ conjSubgroup s T :=
      (T ⊔ conjSubgroup s T).mul_mem
        ((T ⊔ conjSubgroup s T).mul_mem hy hwY)
        ((T ⊔ conjSubgroup s T).inv_mem hy)
    rwa [show y * (y⁻¹ * c * y) * y⁻¹ = c by group] at hmem
  set u : ↥(T ⊔ conjSubgroup s T) := ⟨a, hle ha⟩ with hu
  set v : ↥(T ⊔ conjSubgroup s T) := ⟨b, hle hb⟩ with hv
  have hu2 : u * u = 1 := by
    rw [hu]
    exact Subtype.ext (by simpa using (h.elem_conj y).mul_self_eq_one ha)
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h'
    exact ha1 (by simpa using congrArg Subtype.val h')
  have hv2 : v * v = 1 := by
    rw [hv]
    exact Subtype.ext (by simpa using (h.elem_conj y).mul_self_eq_one hb)
  have hv1 : v ≠ 1 := by
    rw [hv]
    intro h'
    exact hb1 (by simpa using congrArg Subtype.val h')
  have hconj : IsConj u v :=
    (h.quotPair_sub hs hs1).isConj_of_involution CFSG.CGT.T75N.benderCenterInput
      CFSG.CGT.T75N.unitaryTwoGenerationInput hu2 hu1 hv2 hv1
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  refine ⟨(c : X), ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

end Certified

end Abs612

end CFSG.LocalAnalysis.WeakClosure81
