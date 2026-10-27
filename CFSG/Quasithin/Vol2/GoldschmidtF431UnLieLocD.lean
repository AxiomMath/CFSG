module

public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocA
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL
  CFSG.QuasithinUnique
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem card_N1F : Nat.card (miyamotoN1F h) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have := h.finite
  rw [← Nat.card_congr (miyamotoN1FEquiv h).toEquiv,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, h.card_fixedField]

theorem card_C0 (hf : 2 ≤ f) :
    Nat.card (miyamotoA1 h ⊔ miyamotoN1F h : Subgroup (GL (Fin 4) K)) =
      Nat.card (miyamotoA1 h) * Nat.card (miyamotoN1F h) := by
  have hN : miyamotoN1F h ≤ Subgroup.normalizer (miyamotoA1 h : Set (GL (Fin 4) K)) :=
    (miyamotoN1F_le_N1 h).trans (miyamotoN1_le_normalizer_A1 h)
  have hI : miyamotoA1 h ⊓ miyamotoN1F h = ⊥ := by
    refine eq_bot_iff.2 ?_
    rw [← miyamotoA1_inf_levi h hf]
    exact inf_le_inf_left _ ((miyamotoN1F_le_N1 h).trans le_sup_right)
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : miyamotoA1 h × miyamotoN1F h =>
      (⟨(p.1 : GL (Fin 4) K) * (p.2 : GL (Fin 4) K),
        Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
        ↥(miyamotoA1 h ⊔ miyamotoN1F h))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨n, hn⟩⟩ ⟨⟨a', ha'⟩, ⟨n', hn'⟩⟩ he
    have e : a * n = a' * n' := congrArg Subtype.val he
    have h1 : a'⁻¹ * a = n' * n⁻¹ :=
      calc a'⁻¹ * a = a'⁻¹ * (a * n) * n⁻¹ := by group
        _ = a'⁻¹ * (a' * n') * n⁻¹ := by rw [e]
        _ = n' * n⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ miyamotoA1 h ⊓ miyamotoN1F h :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha, by
        rw [h1]
        exact Subgroup.mul_mem _ hn' (Subgroup.inv_mem _ hn)⟩
    rw [hI, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    have : n = n' := mul_left_cancel e
    subst this
    rfl
  · rintro ⟨g, hg⟩
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left (miyamotoA1 h) (miyamotoN1F h) hN
    have hg' : g ∈ (miyamotoA1 h : Set (GL (Fin 4) K)) * (miyamotoN1F h : Set (GL (Fin 4) K)) := by
      rw [← hset]
      exact hg
    obtain ⟨a, ha, n, hn, rfl⟩ := hg'
    exact ⟨(⟨a, ha⟩, ⟨n, hn⟩), rfl⟩

theorem comm_z2_iff {a b c d : K} (hb : h.bar b = b) :
    miyamotoXGL h a b c d * miyamotoXGL h 0 0 1 0 = miyamotoXGL h 0 0 1 0 * miyamotoXGL h a b c d ↔
      h.bar a = a := by
  rw [miyamotoXGL_mul h hb, miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
  constructor
  · rintro ⟨-, -, -, h4⟩
    simp only [map_zero, map_one, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul] at h4
    exact add_left_cancel h4
  · intro ha
    refine ⟨by ring, by ring, by ring, ?_⟩
    simp only [map_zero, map_one, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, ha]

theorem mem_C0_iff_of_mem_P {a b c d : K} (hP : miyamotoXGL h a b c d ∈ miyamotoP h) :
    miyamotoXGL h a b c d ∈ miyamotoA1 h ⊔ miyamotoN1F h ↔ h.bar a = a := by
  have hb := ((miyamotoXGL_mem_P h).1 hP).1
  rw [← centralizer_miyamotoZ2 h, miyamotoZ2_eq h, ← comm_z2_iff h hb]
  constructor
  · rintro ⟨-, hc⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hc
  · intro hc
    exact ⟨miyamotoUnipotent_le_SU h false false hP, Subgroup.mem_centralizer_singleton_iff.2 hc⟩

theorem card_S0 :
    Nat.card (miyamotoP h ⊓ (miyamotoA1 h ⊔ miyamotoN1F h) : Subgroup (GL (Fin 4) K)) =
      (2 ^ f) ^ 5 := by
  have hbb := h.bar_bar
  have key := card_eq_of_param
    (H := (miyamotoP h ⊓ (miyamotoA1 h ⊔ miyamotoN1F h) : Subgroup (GL (Fin 4) K)))
    (fun v : h.fixedField × h.fixedField × K × h.fixedField =>
      miyamotoXGL h v.1 v.2.1 v.2.2.1 (v.2.2.2 + h.bar v.1 * v.2.2.1)) ?_ ?_
  · rw [key, Nat.card_prod, Nat.card_prod, Nat.card_prod, h.card_eq_sq, h.card_fixedField]
    ring
  · intro v v' hv
    obtain ⟨h1, h2, h3, h4⟩ := (miyamotoXGL_inj h).1 hv
    have h1' : (v.1 : K) = v'.1 := h1
    rw [h1', h3, add_left_inj] at h4
    exact Prod.ext (Subtype.ext h1') (Prod.ext (Subtype.ext h2)
      (Prod.ext h3 (Subtype.ext h4)))
  · intro g
    constructor
    · rintro ⟨hgP, hgC⟩
      obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hgP
      have ha := (mem_C0_iff_of_mem_P h hgP).1 hgC
      refine ⟨(⟨a, ha⟩, ⟨b, hb⟩, c, ⟨d + h.bar a * c, ?_⟩), ?_⟩
      · change h.bar (d + h.bar a * c) = d + h.bar a * c
        simp only [map_add, map_mul, ha]
        grind
      · simp only
        congr 1
        grind
    · rintro ⟨⟨a, b, c, e⟩, rfl⟩
      have ha : h.bar (a : K) = a := a.2
      have hb : h.bar (b : K) = b := b.2
      have he : h.bar (e : K) = e := e.2
      have hP : miyamotoXGL h a b c (e + h.bar a * c) ∈ miyamotoP h :=
        (miyamotoXGL_mem_P h).2 ⟨hb, by simp only [map_add, map_mul, he, ha]; grind⟩
      exact ⟨hP, (mem_C0_iff_of_mem_P h hP).2 ha⟩

theorem card_sg {M : Subgroup (GL (Fin 4) K)} (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    Nat.card (sg h M) = Nat.card M :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv

theorem C0_le_gramSU : miyamotoA1 h ⊔ miyamotoN1F h ≤ gramSU h (miyamotoJ4 K) :=
  sup_le (miyamotoUnipotent_le_SU h true false)
    ((miyamotoN1F_le_N1 h).trans (miyamotoN1_le_gramSU h))

theorem isSylowTwoOf_Psy_Cx (hf : 2 ≤ f) : IsSylowTwoOf (Psy h ⊓ Cx h) (Cx h) := by
  have hfin : Finite (Xg h) := finite_gramSU_miyamotoJ4 h
  have hle : Psy h ⊓ Cx h ≤ Cx h := inf_le_right
  refine ⟨hle, (isSylowTwoOf_Psy h).2.1.to_le inf_le_left, ?_⟩
  have cCx : Nat.card (Cx h) = (2 ^ f) ^ 5 * ((2 ^ f) ^ 2 - 1) := by
    rw [cent_z2X h, card_sg h (C0_le_gramSU h), card_C0 h hf, card_miyamotoA1, card_N1F,
      ← mul_assoc, ← pow_succ]
  have cS : Nat.card (Psy h ⊓ Cx h : Subgroup (Xg h)) = (2 ^ f) ^ 5 := by
    have e : Psy h ⊓ Cx h = sg h (miyamotoP h ⊓ (miyamotoA1 h ⊔ miyamotoN1F h)) := by
      rw [cent_z2X h]
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [e, card_sg h (inf_le_right.trans (C0_le_gramSU h)), card_S0 h]
  have e := Subgroup.card_mul_index ((Psy h ⊓ Cx h).subgroupOf (Cx h))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, cS, cCx] at e
  have hidx : ((Psy h ⊓ Cx h).subgroupOf (Cx h)).index = (2 ^ f) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) e
  rw [hidx]
  have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega : f ≠ 0)) two_ne_zero
  have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

end CFSG.Quasithin.H13.F431.Un.LL
