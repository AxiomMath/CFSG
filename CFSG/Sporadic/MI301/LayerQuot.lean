module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component

public section

namespace CFSG.Sporadic.MI301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem nonempty_pQuot_glaPLayer_top_of_surjective {Y W : Type} [Group Y] [Finite Y] [Group W]
    [Finite W] {p : ℕ} (hp : p.Prime) (π : Y →* W) (hπ : Function.Surjective π)
    (hN : ¬ p ∣ Nat.card π.ker) :
    Nonempty (PQuot p (GLAPLayer p (⊤ : Subgroup Y)) ≃*
      PQuot p (GLAPLayer p (⊤ : Subgroup W))) := by
  obtain ⟨e⟩ := nonempty_pQuot_equiv_map hp hN (GLAPLayer p (⊤ : Subgroup Y))
  rw [S267.map_glaPLayer hp π hN, Subgroup.map_top_of_surjective π hπ] at e
  exact ⟨e⟩

section Layer

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
private theorem glaPLayer_le_of_commutator_le {H B : Subgroup G} (hc : ⁅H, H⁆ ≤ B) :
    GLAPLayer p H ≤ B := by
  unfold GLAPLayer
  refine sSup_le fun J hJ => ?_
  have hJ' : GLAPComponent p H J := hJ
  rw [← CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ']
  exact (Subgroup.commutator_mono hJ'.1 hJ'.1).trans hc

private theorem glaPPrimeCore_eq_bot_of_isQuasisimple (hp : p.Prime) {S : Subgroup G}
    (hS : CFSG.Open.IsQuasisimple ↥S) (hpS : p ∣ Nat.card ↥S)
    (hZ : IsPGroup p ↥(Subgroup.center ↥S)) : GLAPPrimeCore p ↥S = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop := GL83.PiGen.coprime_card_glaPPrimeCore hp ↥S
  have hne : GLAPPrimeCore p ↥S ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hpS
  have hle := le_center_of_normal_of_isQuasisimple hS inferInstance hne
  rcases (hZ.to_le hle).card_eq_or_dvd with h1 | hdvd
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd hdvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop)

theorem nonempty_pQuot_equiv_self_of_isQuasisimple (hp : p.Prime) {S : Subgroup G}
    (hS : CFSG.Open.IsQuasisimple ↥S) (hpS : p ∣ Nat.card ↥S)
    (hZ : IsPGroup p ↥(Subgroup.center ↥S)) : Nonempty (PQuot p S ≃* ↥S) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
    (glaPPrimeCore_eq_bot_of_isQuasisimple hp hS hpS hZ)).trans QuotientGroup.quotientBot⟩

theorem glaPLayer_eq_of_isQuasisimple_normal (hp : p.Prime) {H S : Subgroup G} (hSH : S ≤ H)
    (hSn : (S.subgroupOf H).Normal) (hS : CFSG.Open.IsQuasisimple ↥S) (hpS : p ∣ Nat.card ↥S)
    (hZ : IsPGroup p ↥(Subgroup.center ↥S)) (hc : ⁅H, H⁆ ≤ S) : GLAPLayer p H = S := by
  have hSS : GLAPComponent p S S := CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hS
    (glaPPrimeCore_eq_bot_of_isQuasisimple hp hS hpS hZ)
  have hcomp : GLAPComponent p H S :=
    glaPComponent_of_isSubnormal' hp (IsSubnormal.step hSH hSn (IsSubnormal.refl H)) hSS
  refine le_antisymm (glaPLayer_le_of_commutator_le hc) ?_
  unfold GLAPLayer
  exact le_sSup hcomp

theorem glaPLayer_eq_sup_of_isSimple (hp : p.Prime) {H S₁ S₂ : Subgroup G}
    (hBH : IsSubnormal (S₁ ⊔ S₂) H) (h₁ : (S₁.subgroupOf (S₁ ⊔ S₂)).Normal)
    (h₂ : (S₂.subgroupOf (S₁ ⊔ S₂)).Normal) (hs₁ : IsSimpleGroup ↥S₁) (hs₂ : IsSimpleGroup ↥S₂)
    (hn₁ : ∃ a b : ↥S₁, a * b ≠ b * a) (hn₂ : ∃ a b : ↥S₂, a * b ≠ b * a)
    (hp₁ : p ∣ Nat.card ↥S₁) (hp₂ : p ∣ Nat.card ↥S₂) (hc : ⁅H, H⁆ ≤ S₁ ⊔ S₂) :
    GLAPLayer p H = S₁ ⊔ S₂ := by
  have c₁ : GLAPComponent p H S₁ := glaPComponent_of_isSubnormal' hp hBH
    (@GL83.PiGen.glaPComponent_of_normal_simple G _ _ p hp _ _ le_sup_left h₁ hs₁ hn₁ hp₁)
  have c₂ : GLAPComponent p H S₂ := glaPComponent_of_isSubnormal' hp hBH
    (@GL83.PiGen.glaPComponent_of_normal_simple G _ _ p hp _ _ le_sup_right h₂ hs₂ hn₂ hp₂)
  refine le_antisymm (glaPLayer_le_of_commutator_le hc) ?_
  unfold GLAPLayer
  exact sup_le (le_sSup c₁) (le_sSup c₂)

end Layer

section Product

private theorem center_eq_bot_of_isSimple {M : Type} [Group M] (hM : IsSimpleGroup M)
    (hn : ∃ a b : M, a * b ≠ b * a) : Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hn
    exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

private theorem eq_one_of_mk_one_mem {M N : Type} [Group M] [Group N] [Finite M] [Finite N]
    {p : ℕ} (hM : IsSimpleGroup M) (hpM : p ∣ Nat.card M) (O : Subgroup (M × N)) [O.Normal]
    (hO : ¬ p ∣ Nat.card O) {m : M} (hm : ((m, 1) : M × N) ∈ O) : m = 1 := by
  haveI : (O.comap (MonoidHom.inl M N)).Normal := Subgroup.Normal.comap inferInstance _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.comap (MonoidHom.inl M N)) with h | h
  · have hm' : m ∈ O.comap (MonoidHom.inl M N) := hm
    rw [h] at hm'
    exact hm'
  · exfalso
    have hle : (MonoidHom.inl M N).range ≤ O := by
      rintro _ ⟨m', rfl⟩
      have hm' : m' ∈ O.comap (MonoidHom.inl M N) := h ▸ Subgroup.mem_top m'
      exact hm'
    have hd := Subgroup.card_dvd_of_le hle
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (fun a b h => congrArg Prod.fst h : Function.Injective (MonoidHom.inl M N)),
      Subgroup.card_top] at hd
    exact hO (hpM.trans hd)

private theorem eq_one_of_one_mk_mem {M N : Type} [Group M] [Group N] [Finite M] [Finite N]
    {p : ℕ} (hN : IsSimpleGroup N) (hpN : p ∣ Nat.card N) (O : Subgroup (M × N)) [O.Normal]
    (hO : ¬ p ∣ Nat.card O) {n : N} (hn : ((1, n) : M × N) ∈ O) : n = 1 := by
  haveI : (O.comap (MonoidHom.inr M N)).Normal := Subgroup.Normal.comap inferInstance _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.comap (MonoidHom.inr M N)) with h | h
  · have hn' : n ∈ O.comap (MonoidHom.inr M N) := hn
    rw [h] at hn'
    exact hn'
  · exfalso
    have hle : (MonoidHom.inr M N).range ≤ O := by
      rintro _ ⟨n', rfl⟩
      have hn' : n' ∈ O.comap (MonoidHom.inr M N) := h ▸ Subgroup.mem_top n'
      exact hn'
    have hd := Subgroup.card_dvd_of_le hle
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (fun a b h => congrArg Prod.snd h : Function.Injective (MonoidHom.inr M N)),
      Subgroup.card_top] at hd
    exact hO (hpN.trans hd)

private theorem eq_bot_of_normal_prod {M N : Type} [Group M] [Group N] [Finite M] [Finite N]
    {p : ℕ} (hM : IsSimpleGroup M) (hN : IsSimpleGroup N) (hnM : ∃ a b : M, a * b ≠ b * a)
    (hnN : ∃ a b : N, a * b ≠ b * a) (hpM : p ∣ Nat.card M) (hpN : p ∣ Nat.card N)
    (O : Subgroup (M × N)) [hOn : O.Normal] (hO : ¬ p ∣ Nat.card O) : O = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hx
  have hc : ∀ y : M × N, (a, b) * y * (a, b)⁻¹ * y⁻¹ ∈ O := fun y => by
    have h := O.mul_mem hx (hOn.conj_mem _ (O.inv_mem hx) y)
    rwa [← mul_assoc, ← mul_assoc] at h
  have ha : a ∈ Subgroup.center M := Subgroup.mem_center_iff.2 fun m => by
    have h := hc (m, 1)
    rw [show ((a, b) * (m, 1) * (a, b)⁻¹ * (m, 1)⁻¹ : M × N) = (a * m * a⁻¹ * m⁻¹, 1) from
      Prod.ext rfl (by simp)] at h
    have h' := eq_one_of_mk_one_mem hM hpM O hO h
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  have hb : b ∈ Subgroup.center N := Subgroup.mem_center_iff.2 fun n => by
    have h := hc (1, n)
    rw [show ((a, b) * (1, n) * (a, b)⁻¹ * (1, n)⁻¹ : M × N) = (1, b * n * b⁻¹ * n⁻¹) from
      Prod.ext (by simp) rfl] at h
    have h' := eq_one_of_one_mk_mem hN hpN O hO h
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  rw [center_eq_bot_of_isSimple hM hnM, Subgroup.mem_bot] at ha
  rw [center_eq_bot_of_isSimple hN hnN, Subgroup.mem_bot] at hb
  rw [ha, hb]
  exact Subgroup.one_mem _

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem nonempty_pQuot_sup_equiv_prod (hp : p.Prime) {S₁ S₂ : Subgroup G}
    (hs₁ : IsSimpleGroup ↥S₁) (hs₂ : IsSimpleGroup ↥S₂) (hn₁ : ∃ a b : ↥S₁, a * b ≠ b * a)
    (hn₂ : ∃ a b : ↥S₂, a * b ≠ b * a) (hp₁ : p ∣ Nat.card ↥S₁) (hp₂ : p ∣ Nat.card ↥S₂)
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a) (hdisj : S₁ ⊓ S₂ = ⊥) :
    Nonempty (PQuot p (S₁ ⊔ S₂) ≃* ↥S₁ × ↥S₂) := by
  set φ : ↥S₁ × ↥S₂ →* G :=
    S₁.subtype.noncommCoprod S₂.subtype fun a b =>
      show Commute (S₁.subtype a) (S₂.subtype b) from hcomm a a.2 b b.2 with hφ
  have hinj : Function.Injective φ := Subgroup.mul_injective_of_disjoint (disjoint_iff.2 hdisj)
  have hr : φ.range = S₁ ⊔ S₂ := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  let e : ↥S₁ × ↥S₂ ≃* ↥(S₁ ⊔ S₂) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  set O := GLAPPrimeCore p ↥(S₁ ⊔ S₂) with hO
  have hcop : Nat.Coprime p (Nat.card O) := GL83.PiGen.coprime_card_glaPPrimeCore hp _
  haveI hn : (O.map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.symm.surjective
  have hcop' : ¬ p ∣ Nat.card (O.map e.symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop
  have hbot := eq_bot_of_normal_prod hs₁ hs₂ hn₁ hn₂ hp₁ hp₂ _ hcop'
  have hcore : O = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 hbot
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans
    e.symm⟩

end Product

end CFSG.Sporadic.MI301
