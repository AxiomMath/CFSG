module

public import CFSG.Quasithin.H13.NQRigidInputs

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

abbrev resQ {H : Type*} [Group H] {X : Subgroup H} (A : Subgroup H) (Q : Subgroup X) :
    Subgroup A :=
  (Q.map X.subtype).subgroupOf A

variable {H : Type*} [Group H] {X A : Subgroup H} (Q : Subgroup X) [Q.Normal]

omit [Q.Normal] in
theorem resQ_normal (hXA : X ≤ A)
    (hAQ : A ≤ normalizer ((Q.map X.subtype : Subgroup H) : Set H)) : (resQ A Q).Normal :=
  (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hXA)).mpr hAQ

omit [Q.Normal] in
theorem resX_normal (hXA : X ≤ A) (hAX : A ≤ normalizer (X : Set H)) :
    (X.subgroupOf A).Normal :=
  (normal_subgroupOf_iff_le_normalizer hXA).mpr hAX

omit [Q.Normal] in
theorem resQ_le_resX : resQ A Q ≤ X.subgroupOf A := fun _ ha =>
  mem_subgroupOf.mpr (map_subtype_le _ (mem_subgroupOf.mp ha))

omit [Q.Normal] in
theorem isPGroup_resQ (hQ2 : IsPGroup 2 Q) : IsPGroup 2 (resQ A Q) := by
  rw [resQ, ← comap_subtype]
  exact (hQ2.map X.subtype).comap_subtype

omit [Q.Normal] in
theorem noPQuotient_resX (hXA : X ≤ A) (hX2 : NoPQuotient 2 X) :
    ∀ (N : Subgroup (X.subgroupOf A)) [N.Normal], IsPGroup 2 ((X.subgroupOf A) ⧸ N) → N = ⊤ :=
  NoPQuotient.of_surjective (subgroupOfEquivOfLe hXA).symm.toMonoidHom
    (subgroupOfEquivOfLe hXA).symm.surjective hX2

section Bar

variable (hXA : X ≤ A) [(resQ A Q).Normal]

@[expose] noncomputable def resι : X →* A ⧸ resQ A Q :=
  (QuotientGroup.mk' (resQ A Q)).comp (inclusion hXA)

theorem ker_resι : (resι Q hXA).ker = Q := by
  ext x
  rw [MonoidHom.mem_ker, resι, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf]
  exact mem_map_iff_mem X.subtype_injective

theorem range_resι : (resι Q hXA).range = (X.subgroupOf A).map
    (QuotientGroup.mk' (resQ A Q)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨inclusion hXA x, mem_subgroupOf.mpr x.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, mem_subgroupOf.mp ha⟩, rfl⟩

@[expose] noncomputable def resEquiv : X ⧸ Q ≃* (X.subgroupOf A).map
    (QuotientGroup.mk' (resQ A Q)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_resι Q hXA).symm).trans
    ((QuotientGroup.quotientKerEquivRange (resι Q hXA)).trans
      (MulEquiv.subgroupCongr (range_resι Q hXA)))

omit [Q.Normal] in
theorem pow_eq_one_resBar {p : ℕ} (hpow : ∀ x : X, x ^ p ∈ Q) :
    ∀ z ∈ (X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)), z ^ p = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  refine ⟨⟨a, mem_subgroupOf.mp ha⟩ ^ p, hpow _, ?_⟩
  simp

include hXA in
theorem card_frattini_resBar :
    Nat.card ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)) ⧸
        frattini ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)))) =
      Nat.card ((X ⧸ Q) ⧸ frattini (X ⧸ Q)) :=
  (Nat.card_congr (QuotientGroup.congr _ _ (resEquiv Q hXA)
    (map_frattini_mulEquiv (resEquiv Q hXA))).toEquiv).symm

include hXA in
theorem irreducible_resBar (hlat : IsFrattiniLatticeIrreducible X A Q) :
    ∀ K : Subgroup (A ⧸ resQ A Q),
      (frattini ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)))).map
        ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q))).subtype ≤ K →
      K ≤ (X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)) →
      (∀ a : A, ∀ k ∈ K, (a : A ⧸ resQ A Q) * k * (a : A ⧸ resQ A Q)⁻¹ ∈ K) →
      K = (frattini ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)))).map
        ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q))).subtype ∨
        K = (X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)) := by
  classical
  intro K hΦK hKX hKn
  set Xb := (X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)) with hXb
  set e : X ⧸ Q ≃* Xb := resEquiv Q hXA with he
  have hfr : (frattini (X ⧸ Q)).map e.toMonoidHom = frattini Xb := map_frattini_mulEquiv e
  have he_mk : ∀ x : X, ((e (x : X ⧸ Q) : Xb) : A ⧸ resQ A Q) = resι Q hXA x := fun x => rfl
  have hmemΦ : ∀ x : X, (x : H) ∈ frattiniPreimage X Q ↔
      resι Q hXA x ∈ (frattini Xb).map Xb.subtype := by
    intro x
    have hpre : (x : H) ∈ frattiniPreimage X Q ↔ (x : X ⧸ Q) ∈ frattini (X ⧸ Q) := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyx' : y = x := Subtype.ext hyx
        subst hyx'
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre]
    constructor
    · intro hx
      have h1 : e (x : X ⧸ Q) ∈ frattini Xb := by
        rw [← hfr]
        exact ⟨_, hx, rfl⟩
      exact ⟨_, h1, he_mk x⟩
    · rintro ⟨z, hz, hzx⟩
      have hz' : z = e (x : X ⧸ Q) := Subtype.ext (hzx.trans (he_mk x).symm)
      rw [hz', ← hfr] at hz
      obtain ⟨w, hw, hwe⟩ := hz
      have h2 : w = (x : X ⧸ Q) := e.injective hwe
      rw [← h2]
      exact hw
  set Y : Subgroup H := (K.comap (QuotientGroup.mk' (resQ A Q))).map A.subtype with hY
  have hmemY : ∀ x : X, (x : H) ∈ Y ↔ resι Q hXA x ∈ K := by
    intro x
    constructor
    · rintro ⟨a, ha, hax⟩
      have : a = inclusion hXA x := Subtype.ext hax
      rw [this] at ha
      exact ha
    · intro hx
      exact ⟨inclusion hXA x, hx, rfl⟩
  have hYX : Y ≤ X := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (QuotientGroup.mk' (resQ A Q)) a ∈ Xb := hKX ha
    obtain ⟨b, hb, hba⟩ := h1
    have h2 : b⁻¹ * a ∈ resQ A Q := by
      rw [← QuotientGroup.eq]
      exact hba
    have h3 : ((b⁻¹ * a : A) : H) ∈ X := map_subtype_le _ (mem_subgroupOf.mp h2)
    have hbX : (b : H) ∈ X := mem_subgroupOf.mp (show b ∈ X.subgroupOf A from hb)
    have h5 := X.mul_mem hbX h3
    show (a : H) ∈ X
    simpa using h5
  have hΦY : frattiniPreimage X Q ≤ Y := by
    intro y hy
    have hyX : y ∈ X := (map_subtype_le _) hy
    have h1 := (hmemΦ ⟨y, hyX⟩).mp hy
    exact (hmemY ⟨y, hyX⟩).mpr (hΦK h1)
  have hAY : A ≤ normalizer (Y : Set H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨a, ha⟩ * b * ⟨a, ha⟩⁻¹,
        hKn ⟨a, ha⟩ (QuotientGroup.mk' (resQ A Q) b) hb, rfl⟩
    · rintro ⟨b, hb, hby⟩
      refine ⟨⟨a, ha⟩⁻¹ * b * ⟨a, ha⟩⁻¹⁻¹,
        hKn ⟨a, ha⟩⁻¹ (QuotientGroup.mk' (resQ A Q) b) hb, ?_⟩
      have hby' : a * y * a⁻¹ = (b : H) := hby.symm
      show (a : H)⁻¹ * b * a⁻¹⁻¹ = y
      rw [← hby']
      group
  rcases hlat Y hΦY hYX hAY with h1 | h1
  · left
    apply le_antisymm _ hΦK
    intro k hk
    obtain ⟨a, ha, rfl⟩ := hKX hk
    have haX : (a : H) ∈ X := mem_subgroupOf.mp (show a ∈ X.subgroupOf A from ha)
    have hx : resι Q hXA ⟨a, haX⟩ = QuotientGroup.mk' (resQ A Q) a := rfl
    have h2 : ((⟨a, haX⟩ : X) : H) ∈ Y := by
      rw [hmemY, hx]
      exact hk
    rw [h1] at h2
    have h3 := (hmemΦ ⟨a, haX⟩).mp h2
    rw [hx] at h3
    exact h3
  · right
    apply le_antisymm hKX
    rintro _ ⟨a, ha, rfl⟩
    have haX : (a : H) ∈ X := mem_subgroupOf.mp (show a ∈ X.subgroupOf A from ha)
    have h2 : ((⟨a, haX⟩ : X) : H) ∈ Y := by
      rw [h1]
      exact haX
    exact (hmemY ⟨a, haX⟩).mp h2

end Bar

end CFSG.Quasithin.H13.NQRigid
