module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K43Holds
public import CFSG.Quasithin.Background.SimsD1FourGeneral
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxM

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open CFSG.GroupTheory
open scoped commutatorElement MonoidAlgebra

variable {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] [Finite Γ]
  {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem kerRepresentation_eq_ofQuotient {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    Theory.Representation.kerRepresentation ρ = Representation.ofQuotient ρ ρ.ker := rfl

namespace FaithfulQuotient

variable (ρ : Representation (ZMod p) Γ V) (H : Subgroup Γ)

abbrev Quotient : Type := ↥H ⧸ (ρ.comp H.subtype).ker

noncomputable def map : ↥H →* Quotient ρ H :=
  QuotientGroup.mk' (ρ.comp H.subtype).ker

noncomputable def rep : Representation (ZMod p) (Quotient ρ H) V :=
  Theory.Representation.kerRepresentation (ρ.comp H.subtype)

theorem rep_faithful : Function.Injective (rep ρ H) :=
  Theory.Representation.kerRepresentation_faithful _

@[simp] theorem rep_map (h : ↥H) : rep ρ H (map ρ H h) = ρ (h : Γ) := by
  rw [show rep ρ H =
    Representation.ofQuotient (ρ.comp H.subtype) (ρ.comp H.subtype).ker from
    kerRepresentation_eq_ofQuotient (ρ.comp H.subtype)]
  ext v
  simpa [map] using
    (Representation.ofQuotient_coe_apply (ρ := ρ.comp H.subtype)
      (S := (ρ.comp H.subtype).ker) h v)

noncomputable abbrev image (A : Subgroup Γ) : Subgroup (Quotient ρ H) :=
  (A.subgroupOf H).map (map ρ H)

theorem image_sup (A B : Subgroup Γ) (hA : A ≤ H) (hB : B ≤ H) :
    image ρ H (A ⊔ B) = image ρ H A ⊔ image ρ H B := by
  rw [image, image, image, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem mem_image {A : Subgroup Γ} {x : Quotient ρ H} :
    x ∈ image ρ H A ↔ ∃ a : ↥H, (a : Γ) ∈ A ∧ map ρ H a = x := by
  rw [image, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem image_mem {A : Subgroup Γ} (hA : A ≤ H) {a : Γ} (ha : a ∈ A) :
    map ρ H ⟨a, hA ha⟩ ∈ image ρ H A :=
  (mem_image ρ H).mpr ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem fixV_image {A : Subgroup Γ} (hA : A ≤ H) :
    fixV (rep ρ H) (image ρ H A) = fixV ρ A := by
  ext v
  constructor
  · intro hv a ha
    have hmem : map ρ H ⟨a, hA ha⟩ ∈ image ρ H A := image_mem ρ H hA ha
    have := hv _ hmem
    simpa using this
  · intro hv x hx
    rw [mem_image ρ H] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simpa using hv (a : Γ) ha

theorem isPGroup_image {q : ℕ} {A : Subgroup Γ} (hA : A ≤ H) (h : IsPGroup q A) :
    IsPGroup q (image ρ H A) := by
  have h' : IsPGroup q (A.subgroupOf H) := h.comap_subtype (K := H)
  exact h'.map (map ρ H)

theorem le_normalizer_image {A B : Subgroup Γ} (h : A ≤ normalizer B) :
    image ρ H A ≤ normalizer (image ρ H B) :=
  CFSG.GroupTheory.map_subgroupOf_le_normalizer (map ρ H) h

theorem commutator_image (A B : Subgroup Γ) (hA : A ≤ H) (hB : B ≤ H) :
    ⁅image ρ H A, image ρ H B⁆ = image ρ H ⁅A, B⁆ := by
  rw [image, image, image, ← Subgroup.map_commutator, commutator_subgroupOf_eq hA hB]

theorem image_ne_bot_of_exists {A : Subgroup Γ} (hA : A ≤ H)
    (h : ∃ a ∈ A, ρ a ≠ 1) : image ρ H A ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha, hane⟩ := h
  have hmem : map ρ H ⟨a, hA ha⟩ ∈ image ρ H A := image_mem ρ H hA ha
  rw [hbot] at hmem
  have h1 : map ρ H ⟨a, hA ha⟩ = 1 := Subgroup.mem_bot.mp hmem
  exact hane (by rw [← rep_map ρ H ⟨a, hA ha⟩, h1, map_one])

theorem inf_ker_eq_bot_of_fixV_eq_bot {r : ℕ} (hr : r.Prime) {A : Subgroup Γ}
    (hA : A ≤ H) (hcard : Nat.card A = r) (hfix : fixV ρ A = ⊥) (hV : Nontrivial V) :
    A.subgroupOf H ⊓ (ρ.comp H.subtype).ker = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, haH⟩ ⟨haA, haN⟩
  by_contra hne
  have haA' : a ∈ A := Subgroup.mem_subgroupOf.mp haA
  have hane : (⟨a, haA'⟩ : A) ≠ 1 := by
    intro h
    apply hne
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  haveI : Fact r.Prime := ⟨hr⟩
  have htop : Subgroup.zpowers (⟨a, haA'⟩ : A) = ⊤ :=
    zpowers_eq_top_of_prime_card hcard hane
  have hone : ρ a = 1 := MonoidHom.mem_ker.mp haN
  have hAeq : A = Subgroup.zpowers a := by
    have hmap := MonoidHom.map_zpowers A.subtype ⟨a, haA'⟩
    rw [htop, Subgroup.map_top, Subgroup.range_subtype] at hmap
    simpa using hmap
  have hfixA : fixV ρ A = ⊤ := by
    rw [hAeq, eq_top_iff]
    intro v _
    exact (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6 ρ a v).mpr
      (by simp [hone])
  exact (top_ne_bot : (⊤ : Submodule (ZMod p) V) ≠ ⊥) (hfixA.symm.trans hfix)

theorem card_image_of_prime {r : ℕ} (hr : r.Prime) {A : Subgroup Γ} (hA : A ≤ H)
    (hcard : Nat.card A = r) (hdisj : A.subgroupOf H ⊓ (ρ.comp H.subtype).ker = ⊥) :
    Nat.card (image ρ H A) = r := by
  have hdvd : Nat.card (image ρ H A) ∣ Nat.card A := by
    have h := Subgroup.card_map_dvd (H := A.subgroupOf H) (f := map ρ H)
    rwa [show Nat.card (A.subgroupOf H) = Nat.card A from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at h
  rcases (Nat.dvd_prime hr).mp (hcard ▸ hdvd) with h1 | hr'
  · exfalso
    have hbot : image ρ H A = ⊥ := (Subgroup.card_eq_one).mp h1
    have hle : A.subgroupOf H ≤ (map ρ H).ker :=
      (Subgroup.map_eq_bot_iff (H := A.subgroupOf H) (f := map ρ H)).mp hbot
    have hAle : A.subgroupOf H ≤ (ρ.comp H.subtype).ker := by
      intro x hx
      have hx1 : map ρ H x = 1 := by
        simpa [MonoidHom.mem_ker] using hle hx
      exact (QuotientGroup.eq_one_iff (N := (ρ.comp H.subtype).ker) x).mp hx1
    have hinf : A.subgroupOf H = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxbot : x ∈ (⊥ : Subgroup ↥H) := by
        rw [← hdisj]
        exact Subgroup.mem_inf.mpr ⟨hx, hAle hx⟩
      exact Subgroup.mem_bot.mp hxbot
    have hcard1 : Nat.card A = 1 := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hinf, Subgroup.card_bot]
    exact hr.ne_one (by omega)
  · exact hr'

theorem isKGroup_quotient_sup {q r : ℕ} {P D : Subgroup Γ} (hq : q.Prime) (hr : r.Prime)
    (hP : IsPGroup q P) (hD : Nat.card D = r)
    (hDP : D ≤ Subgroup.normalizer (P : Set Γ)) :
    CFSG.Open.IsKGroup (Quotient ρ (P ⊔ D)) := by
  let H : Subgroup Γ := P ⊔ D
  haveI : Fact q.Prime := ⟨hq⟩
  have hPsolv : Group.IsSolvable ↥P := by
    haveI : Group.IsNilpotent ↥P := hP.isNilpotent
    infer_instance
  haveI : Fact r.Prime := ⟨hr⟩
  have hDsolv : Group.IsSolvable ↥D := by
    haveI : IsCyclic ↥D := isCyclic_of_prime_card hD
    infer_instance
  have hHsolv : Group.IsSolvable ↥H := by
    have hcomm : H = D ⊔ P := by simp [H, sup_comm]
    rw [hcomm]
    exact CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210.isSolvable_sup_of_le_normalizer
      hDP hPsolv hDsolv
  haveI : Group.IsSolvable ↥H := hHsolv
  haveI : Group.IsSolvable (Quotient ρ H) := inferInstance
  exact CFSG.Quasithin.SimsD1.FourGeneral.isKGroup_of_isSolvable _

theorem card_image_eq_of_fixV_eq_bot {r : ℕ} (hr : r.Prime) {D : Subgroup Γ}
    (hDH : D ≤ H) (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥) [Nontrivial V] :
    Nat.card (image ρ H D) = r :=
  card_image_of_prime (ρ := ρ) (H := H) hr hDH hD
    (inf_ker_eq_bot_of_fixV_eq_bot (ρ := ρ) (H := H) hr hDH hD hfix inferInstance)

theorem image_data {q : ℕ} {P D : Subgroup Γ} (hP : IsPGroup q P)
    (hDP : D ≤ Subgroup.normalizer (P : Set Γ))
    (hPD : ⁅D, P⁆ = P) (hfix : fixV ρ D = ⊥) (hPne : ∃ p ∈ P, ρ p ≠ 1) :
    fixV (rep ρ (P ⊔ D)) (image ρ (P ⊔ D) D) = ⊥ ∧
      IsPGroup q (image ρ (P ⊔ D) P) ∧
      image ρ (P ⊔ D) P ≠ ⊥ ∧
      image ρ (P ⊔ D) D ≤ normalizer (image ρ (P ⊔ D) P) ∧
      ⁅image ρ (P ⊔ D) D, image ρ (P ⊔ D) P⁆ = image ρ (P ⊔ D) P := by
  have hPH : P ≤ P ⊔ D := le_sup_left
  have hDH : D ≤ P ⊔ D := le_sup_right
  refine ⟨?_, isPGroup_image (ρ := ρ) (H := P ⊔ D) (A := P) hPH hP,
    image_ne_bot_of_exists (ρ := ρ) (H := P ⊔ D) (A := P) hPH hPne,
    le_normalizer_image (ρ := ρ) (H := P ⊔ D) (A := D) (B := P) hDP, ?_⟩
  · rw [fixV_image (ρ := ρ) (H := P ⊔ D) (A := D) hDH]
    exact hfix
  · rw [commutator_image (ρ := ρ) (H := P ⊔ D) (A := D) (B := P) hDH hPH, hPD]

end FaithfulQuotient

namespace FaithfulQuotient

variable (ρ : Representation (ZMod p) Γ V) (H : Subgroup Γ)

noncomputable def imageHom {A : Subgroup Γ} (hA : A ≤ H) : ↥A →* ↥(image ρ H A) :=
  ((map ρ H).subgroupMap (A.subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hA).symm.toMonoidHom

@[simp] theorem imageHom_apply {A : Subgroup Γ} (hA : A ≤ H) (a : ↥A) :
    (imageHom ρ H hA a : Quotient ρ H) = map ρ H ⟨a, hA a.2⟩ := by
  simp only [imageHom, MonoidHom.comp_apply, MonoidHom.subgroupMap_apply_coe]
  exact congrArg (map ρ H)
    (Subtype.ext (Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe hA a))

theorem imageHom_surjective {A : Subgroup Γ} (hA : A ≤ H) :
    Function.Surjective (imageHom ρ H hA) :=
  (MonoidHom.subgroupMap_surjective (map ρ H) (A.subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hA).symm.surjective

variable {T D : Subgroup Γ}

theorem mem_image_sup_iff (hTH : T ≤ H) (hDH : D ≤ H) {g : Quotient ρ H} :
    g ∈ image ρ H T ⊔ image ρ H D ↔
      ∃ gH : ↥H, (gH : Γ) ∈ T ⊔ D ∧ map ρ H gH = g := by
  rw [← image_sup (ρ := ρ) (H := H) (A := T) (B := D) hTH hDH, mem_image]

theorem image_invariant_of_sup (hTH : T ≤ H) (hDH : D ≤ H) {W : Submodule (ZMod p) V}
    (h : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    ∀ g ∈ image ρ H T ⊔ image ρ H D, ∀ w ∈ W, rep ρ H g w ∈ W := by
  intro g hg w hw
  obtain ⟨gH, hgTD, rfl⟩ := (mem_image_sup_iff (ρ := ρ) (H := H) hTH hDH).mp hg
  simpa using h (gH : Γ) hgTD w hw

theorem image_simple_of_sup (hTH : T ≤ H) (hDH : D ≤ H) {W : Submodule (ZMod p) V}
    (h : ∀ W' : Submodule (ZMod p) V, W' ≤ W →
      (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = W) :
    ∀ W' : Submodule (ZMod p) V, W' ≤ W →
      (∀ g ∈ image ρ H T ⊔ image ρ H D, ∀ w ∈ W', rep ρ H g w ∈ W') →
      W' = ⊥ ∨ W' = W := by
  intro W' hle hinv
  apply h W' hle
  intro g hg w hw
  let gH : ↥H := ⟨g, (sup_le hTH hDH) hg⟩
  have hmem : map ρ H gH ∈ image ρ H T ⊔ image ρ H D :=
    (mem_image_sup_iff (ρ := ρ) (H := H) hTH hDH).mpr ⟨gH, hg, rfl⟩
  simpa [gH] using hinv _ hmem w hw

theorem image_nontrivial_of_sup (hTH : T ≤ H) {W : Submodule (ZMod p) V}
    (h : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) :
    ∃ t ∈ image ρ H T, ∃ w ∈ W, rep ρ H t w ≠ w := by
  obtain ⟨t, ht, w, hw, hne⟩ := h
  exact ⟨map ρ H ⟨t, hTH ht⟩, image_mem ρ H hTH ht, w, hw, by simpa using hne⟩

end FaithfulQuotient

theorem nontrivial_of_exists_ne_one {ρ : Representation (ZMod p) Γ V}
    (h : ∃ g : Γ, ρ g ≠ 1) : Nontrivial V := by
  obtain ⟨g, hg⟩ := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact hg (by ext v; exact Subsingleton.elim _ _)

theorem k42_unfaithful (ρ : Representation (ZMod p) Γ V) {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    {D Q : Subgroup Γ} (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥) (hQ : IsPGroup q Q)
    (hQρ : ∃ t ∈ Q, ρ t ≠ 1) (hDQ : D ≤ Subgroup.normalizer (Q : Set Γ))
    (hDQc : ⁅D, Q⁆ = Q) :
    q = 2 ∧ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  let H : Subgroup Γ := Q ⊔ D
  have hDH : D ≤ H := le_sup_right
  have hK : CFSG.Open.IsKGroup (FaithfulQuotient.Quotient ρ H) :=
    FaithfulQuotient.isKGroup_quotient_sup (ρ := ρ) (P := Q) (D := D) hq hr hQ hD hDQ
  haveI : Nontrivial V :=
    nontrivial_of_exists_ne_one (ρ := ρ) ⟨hQρ.choose, hQρ.choose_spec.2⟩
  have hcardD : Nat.card (FaithfulQuotient.image ρ H D) = r :=
    FaithfulQuotient.card_image_eq_of_fixV_eq_bot (ρ := ρ) (H := H) hr hDH hD hfix
  obtain ⟨hfixD, hQ', hQ'ne, hN', hC'⟩ :=
    FaithfulQuotient.image_data (ρ := ρ) (P := Q) (D := D) hQ hDQ hDQc hfix hQρ
  have hres := UC6.k42_uc6 p (Fact.out : p.Prime) (FaithfulQuotient.Quotient ρ H) hK V
    (FaithfulQuotient.rep ρ H) (FaithfulQuotient.rep_faithful ρ H) q r hq hr hqp hrp hqr
    (FaithfulQuotient.image ρ H D) hcardD hfixD
    (FaithfulQuotient.image ρ H Q) hQ' hQ'ne hN' hC'
  exact ⟨hres.2.1, hres.2.2⟩

theorem k43gen_unfaithful (ρ : Representation (ZMod p) Γ V) (hp : 2 < p)
    {D T : Subgroup Γ} (hD : Nat.card D = 3) (hfix : fixV ρ D = ⊥)
    (hT : IsPGroup 2 T) (hDT : D ≤ Subgroup.normalizer (T : Set Γ))
    (hDTc : ⁅D, T⁆ = T) {W : Submodule (ZMod p) V}
    (hWinv : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hWs : ∀ W' : Submodule (ZMod p) V, W' ≤ W →
      (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = W)
    (hWt : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) :
    ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
      ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w := by
  let H : Subgroup Γ := T ⊔ D
  have hTH : T ≤ H := le_sup_left
  have hDH : D ≤ H := le_sup_right
  haveI : Nontrivial V := by
    obtain ⟨t, -, w, -, hne⟩ := hWt
    exact ⟨(w : V), 0, fun h => hne (by rw [h, map_zero])⟩
  have hK : CFSG.Open.IsKGroup (FaithfulQuotient.Quotient ρ H) :=
    FaithfulQuotient.isKGroup_quotient_sup (ρ := ρ) (P := T) (D := D)
      Nat.prime_two Nat.prime_three hT hD hDT
  have hcardD : Nat.card (FaithfulQuotient.image ρ H D) = 3 :=
    FaithfulQuotient.card_image_eq_of_fixV_eq_bot (ρ := ρ) (H := H)
      Nat.prime_three hDH hD hfix
  obtain ⟨hfixD, hT', -, hN', hC'⟩ :=
    FaithfulQuotient.image_data (ρ := ρ) (P := T) (D := D) hT hDT hDTc hfix (by
      obtain ⟨t, ht, w, hw, hne⟩ := hWt
      exact ⟨t, ht, fun h1 => hne (by rw [h1, Module.End.one_apply])⟩)
  have hWinv' : ∀ g ∈ FaithfulQuotient.image ρ H T ⊔ FaithfulQuotient.image ρ H D,
      ∀ w ∈ W, FaithfulQuotient.rep ρ H g w ∈ W :=
    FaithfulQuotient.image_invariant_of_sup (ρ := ρ) (H := H) hTH hDH hWinv
  have hWs' : ∀ W' : Submodule (ZMod p) V, W' ≤ W →
      (∀ g ∈ FaithfulQuotient.image ρ H T ⊔ FaithfulQuotient.image ρ H D,
        ∀ w ∈ W', FaithfulQuotient.rep ρ H g w ∈ W') → W' = ⊥ ∨ W' = W :=
    FaithfulQuotient.image_simple_of_sup (ρ := ρ) (H := H) hTH hDH hWs
  have hWt' : ∃ t ∈ FaithfulQuotient.image ρ H T, ∃ w ∈ W,
      FaithfulQuotient.rep ρ H t w ≠ w :=
    FaithfulQuotient.image_nontrivial_of_sup (ρ := ρ) (H := H) hTH hWt
  obtain ⟨φ', hφ'surj, hφ'ker⟩ :=
    (k43gen_holds p hp (FaithfulQuotient.Quotient ρ H) hK V
      (FaithfulQuotient.rep ρ H) (FaithfulQuotient.rep_faithful ρ H)
      (FaithfulQuotient.image ρ H D) hcardD hfixD
      (FaithfulQuotient.image ρ H T) hT' hN' hC' W hWinv' hWs' hWt').1
  let πT : ↥T →* ↥(FaithfulQuotient.image ρ H T) := FaithfulQuotient.imageHom ρ H hTH
  refine ⟨φ'.comp πT,
    hφ'surj.comp (FaithfulQuotient.imageHom_surjective ρ H hTH), ?_⟩
  intro t
  change φ' (πT t) = 1 ↔ ∀ w ∈ W, ρ (t : Γ) w = w
  rw [hφ'ker (πT t)]
  exact ⟨fun h w hw => by simpa [πT, FaithfulQuotient.imageHom] using h w hw,
    fun h w hw => by simpa [πT, FaithfulQuotient.imageHom] using h w hw⟩

theorem orderOf_two_eq_two_pow_of_fixV_eq_bot (ρ : Representation (ZMod p) Γ V)
    (hp2 : p ≠ 2) {T : Subgroup Γ} (hT : IsPGroup 2 T) {b : Γ} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hbr : orderOf b = r) (hbT : b ∈ Subgroup.normalizer (T : Set Γ))
    (hTb : ⁅Subgroup.zpowers b, T⁆ = T) (hfix : fixV ρ (Subgroup.zpowers b) = ⊥)
    (hnt : ∃ t ∈ T, ρ t ≠ 1) :
    ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  have hV : Nontrivial V :=
    nontrivial_of_exists_ne_one (ρ := ρ) ⟨hnt.choose, hnt.choose_spec.2⟩
  haveI : Nontrivial V := hV
  have hrp : r ≠ p := by
    intro hrp
    have hpgroup : IsPGroup p (Subgroup.zpowers b) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hbr, hrp, pow_one]
    exact (UC46.fixV_ne_bot_of_pGroup (ρ := ρ) hpgroup) hfix
  have hcard : Nat.card (Subgroup.zpowers b) = r := by rw [Nat.card_zpowers, hbr]
  have hDQ : Subgroup.zpowers b ≤ Subgroup.normalizer (T : Set Γ) :=
    Subgroup.zpowers_le.mpr hbT
  exact (k42_unfaithful (ρ := ρ) (q := 2) (r := r) Nat.prime_two hr (Ne.symm hp2) hrp
    (Ne.symm hr2) (D := Subgroup.zpowers b) (Q := T) hcard hfix hT hnt hDQ hTb).2

theorem exists_irreducible_unfaithful (ρ : Representation (ZMod p) Γ V) {r : ℕ}
    (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    {D T : Subgroup Γ} (hD : Nat.card D = r) (hT : IsPGroup 2 T)
    (hDT : D ≤ Subgroup.normalizer (T : Set Γ)) (hnt : ∃ t ∈ T, ρ t ≠ 1) :
    ∃ W : Submodule (ZMod p) V, (∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) ∧
      (∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) ∧
      ∀ W' : Submodule (ZMod p) V, W' ≤ W →
        (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = W := by
  let H : Subgroup Γ := T ⊔ D
  have hTH : T ≤ H := le_sup_left
  have hDH : D ≤ H := le_sup_right
  let ρH : Representation (ZMod p) ↥H V := ρ.comp H.subtype
  have hp : p.Prime := Fact.out
  have hpdvdH : ¬ p ∣ Nat.card ↥H :=
    UC6.not_dvd_card_sup_uc6 hp hp2 hr hr2 hrp hD hT hDT
  haveI : NeZero (Nat.card ↥H : ZMod p) := ⟨by
    intro h
    exact hpdvdH ((ZMod.natCast_eq_zero_iff (Nat.card ↥H) p).1 h)⟩
  haveI hss : Representation.IsSemisimpleRepresentation ρH := inferInstance
  haveI hssmod : IsSemisimpleModule (MonoidAlgebra (ZMod p) ↥H) ρH.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρH).mp hss
  have hTne : ¬ T.subgroupOf H ≤ ρH.ker := by
    intro hle
    obtain ⟨t, ht, hne⟩ := hnt
    have hmem : (⟨t, hTH ht⟩ : ↥H) ∈ T.subgroupOf H := Subgroup.mem_subgroupOf.mpr ht
    have h1 : ρH ⟨t, hTH ht⟩ = 1 := MonoidHom.mem_ker.mp (hle hmem)
    exact hne (by simpa [ρH] using h1)
  obtain ⟨m, hmSimple, hmker⟩ :=
    exists_simple_submodule_not_le_ker_of_semisimple ρH (T.subgroupOf H) hTne
  let M : Subrepresentation ρH := Subrepresentation.ofSubmodule' m
  have hMirr : Representation.IsIrreducible M.toRepresentation :=
    irreducible_subrepresentation_of_simple_asModuleSubmodule ρH hmSimple
  have hMatom : IsAtom M := (Subrepresentation.irreducible_iff_isAtom M).mp hMirr
  have hWinv : ∀ g ∈ T ⊔ D, ∀ w ∈ M.toSubmodule, ρ g w ∈ M.toSubmodule := by
    intro g hg w hw
    exact M.apply_mem_toSubmodule ⟨g, (sup_le hTH hDH) hg⟩ hw
  have hWt : ∃ t ∈ T, ∃ w ∈ M.toSubmodule, ρ t w ≠ w := by
    by_contra h
    push Not at h
    apply hmker
    intro t' ht'
    rw [MonoidHom.mem_ker]
    ext w
    exact h (t' : Γ) (Subgroup.mem_subgroupOf.mp ht') (w : V) w.2
  have hWs : ∀ W' : Submodule (ZMod p) V, W' ≤ M.toSubmodule →
      (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') →
      W' = ⊥ ∨ W' = M.toSubmodule := by
    intro W' hle hinv
    let S : Subrepresentation ρH :=
      ⟨W', fun h v hv => hinv (h : Γ) (by simpa [H] using h.2) v hv⟩
    have hSM : S ≤ M := fun v hv => hle hv
    by_cases hSbot : S = ⊥
    · left
      have hbot : (⊥ : Subrepresentation ρH).toSubmodule = ⊥ := rfl
      have h := congrArg Subrepresentation.toSubmodule hSbot
      simpa [S] using h.trans hbot
    · right
      have hSeq : S = M := (hMatom.le_iff_eq hSbot).mp hSM
      have h := congrArg Subrepresentation.toSubmodule hSeq
      simpa [S] using h
  exact ⟨M.toSubmodule, hWinv, hWt, hWs⟩
