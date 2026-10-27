module

public import CFSG.Quasithin.EmptyFaithful.S153WJOff
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

private theorem conjByElt_mul_aux' (s t : G) (K : Subgroup G) :
    conjByElt (s * t) K = conjByElt s (conjByElt t K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  rw [mul_inv_rev]
  group

private theorem conjByElt_one_aux' (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

private theorem mem_normalizer_of_conjByElt_eq_aux' {y : G} {L : Subgroup G}
    (h : conjByElt y L = L) : y ∈ Subgroup.normalizer (L : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

private theorem isElemAbelian_conjByElt_aux' {V : Subgroup G} (hV : IsElemAbelian 2 V) (a : G) :
    IsElemAbelian 2 (conjByElt a V) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, u, hu, rfl⟩ := x
    obtain ⟨y, v, hv, rfl⟩ := y
    apply Subtype.ext
    have h := congrArg Subtype.val (hV.1.is_comm.comm (⟨u, hu⟩ : V) ⟨v, hv⟩)
    change (a * u * a⁻¹) * (a * v * a⁻¹) = (a * v * a⁻¹) * (a * u * a⁻¹)
    have h' : u * v = v * u := h
    calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
      _ = a * (v * u) * a⁻¹ := by rw [h']
      _ = (a * v * a⁻¹) * (a * u * a⁻¹) := by group
  · obtain ⟨u, hu, rfl⟩ := hx
    have h := hV.2 u hu
    change (a * u * a⁻¹) ^ 2 = 1
    rw [conj_pow, h]
    group

variable [Finite G]

theorem le_normalizer_of_wreath_center {S L Z : Subgroup G} {q : ℕ} (hq : 3 ≤ q)
    (hZS : Z ≤ S ⊓ L) (hZea : IsElemAbelian 2 Z) (hZcard : Nat.card Z = q)
    (hLZ : ∀ z ∈ L, (∀ y ∈ L, y * z = z * y) → z = 1)
    (hZC : ∀ g ∈ Subgroup.normalizer (L : Set G),
      g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
        g ^ 2 ∈ Subgroup.centralizer (L : Set G) → ∀ z ∈ Z, g * z * g⁻¹ = z)
    {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ Subgroup.normalizer (L : Set G) := by
  classical
  by_contra hAnot
  obtain ⟨a, haA, han⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    exact hAnot fun x hx => by
      by_contra hc
      exact h ⟨x, hx, hc⟩
  have haS : a ∈ S := hA.1 haA
  have hM : ∀ y ∈ S, y ∉ Subgroup.normalizer (L : Set G) → conjByElt y L = conjByElt t L := by
    intro y hy hyn
    have h1 : conjByElt y L ∈ conjSubgroupsBy S L := ⟨y, hy, rfl⟩
    rw [hset] at h1
    rcases h1 with h1 | h1
    · exact absurd (mem_normalizer_of_conjByElt_eq_aux' h1) hyn
    · exact h1
  have hMa : conjByElt a L = conjByElt t L := hM a haS han
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [sq] at this
  have hhalf : ∀ x ∈ A, x ∈ A ⊓ Subgroup.normalizer (L : Set G) ∨
      a⁻¹ * x ∈ A ⊓ Subgroup.normalizer (L : Set G) := by
    intro x hx
    by_cases hxn : x ∈ Subgroup.normalizer (L : Set G)
    · exact Or.inl ⟨hx, hxn⟩
    · right
      refine ⟨A.mul_mem (A.inv_mem haA) hx, ?_⟩
      have h1 : conjByElt x L = conjByElt a L := (hM x (hA.1 hx) hxn).trans hMa.symm
      apply mem_normalizer_of_conjByElt_eq_aux'
      rw [conjByElt_mul_aux', h1, ← conjByElt_mul_aux', inv_mul_cancel, conjByElt_one_aux']
  have hindexA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) :=
    W153.card_le_two_mul_of_forall inf_le_left hAcomm haA ha2 hhalf
  have hZL : Z ≤ L := hZS.trans inf_le_right
  have hZS' : Z ≤ S := hZS.trans inf_le_left
  set ZM : Subgroup G := conjByElt a Z with hZMdef
  have hZMS : ZM ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem haS (hZS' hy)) (S.inv_mem haS)
  have hZMM : ZM ≤ conjByElt t L := by
    rw [← hMa]
    exact Subgroup.map_mono hZL
  have hLM : ∀ x ∈ L, ∀ y ∈ conjByElt t L, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm
  have hcommZ : ∀ x ∈ Z, ∀ y ∈ ZM, x * y = y * x := fun x hx y hy =>
    hLM x (hZL hx) y (hZMM hy)
  have hZMea : IsElemAbelian 2 ZM := isElemAbelian_conjByElt_aux' hZea a
  have hVea : IsElemAbelian 2 (Z ⊔ ZM) := B2F.isElemAbelian_sup_of_commute hZea hZMea hcommZ
  have hVS : Z ⊔ ZM ≤ S := sup_le hZS' hZMS
  have hbot : Z ⊓ ZM = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzL : z ∈ L := hZL hz.1
    have hzM : z ∈ conjByElt t L := hZMM hz.2
    have hz1 : z = 1 := hLZ z hzL (fun y hy => hLM y hy z hzM)
    rw [hz1]
    exact Subgroup.one_mem _
  have hZMcard : Nat.card ZM = q := by
    rw [← hZcard]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).injective
  have hVcard : Nat.card ↥(Z ⊔ ZM) = q * q := by
    have h := B2F.card_sup_mul_card_inf_of_commute hcommZ
    rw [hbot, Subgroup.card_bot, mul_one, hZMcard, hZcard] at h
    exact h
  have hA0 : A ⊓ Subgroup.normalizer (L : Set G) ≤
      A ⊓ Subgroup.centralizer ((Z ⊔ ZM : Subgroup G) : Set G) := by
    intro g hg
    refine ⟨hg.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    have hgNS : g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
      have key : ∀ h ∈ A ⊓ Subgroup.normalizer (L : Set G), ∀ k ∈ S ⊓ L, h * k * h⁻¹ ∈ S ⊓ L := by
        intro h hh k hk
        exact ⟨S.mul_mem (S.mul_mem (hA.1 hh.1) hk.1) (S.inv_mem (hA.1 hh.1)),
          (Subgroup.mem_normalizer_iff.mp hh.2 k).mp hk.2⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key g hg x, fun hx => ?_⟩
      have hg' : g⁻¹ ∈ A ⊓ Subgroup.normalizer (L : Set G) :=
        (A ⊓ Subgroup.normalizer (L : Set G)).inv_mem hg
      have := key g⁻¹ hg' _ hx
      simpa [mul_assoc] using this
    have hg2 : g ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
      rw [hA.2.1.2 g hg.1]
      exact Subgroup.one_mem _
    have hgZ : ∀ z ∈ Z, g * z = z * g := fun z hz => by
      have := hZC g hg.2 hgNS hg2 z hz
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [this]
    have hgac : Commute a g := hAcomm a haA g hg.1
    have hgZM : ∀ h ∈ ZM, h * g = g * h := by
      rintro _ ⟨v, hv, rfl⟩
      have hvg : Commute v g := (hgZ v hv).symm
      exact (((hgac.mul_left hvg).mul_left hgac.inv_left) : Commute (a * v * a⁻¹) g).eq
    have hle : Z ⊔ ZM ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hgZ h hh).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hgZM h hh
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hCA : Nat.card A ≤
      2 * Nat.card ↥(A ⊓ Subgroup.centralizer ((Z ⊔ ZM : Subgroup G) : Set G)) :=
    hindexA.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hA0))
  let μ : Z →* G :=
    { toFun := fun x => (x : G) * (a * (x : G) * a⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have h := hcommZ (y : G) y.2 (a * (x : G) * a⁻¹) ⟨x, x.2, rfl⟩
        change (x : G) * y * (a * ((x : G) * y) * a⁻¹) =
          ((x : G) * (a * x * a⁻¹)) * ((y : G) * (a * y * a⁻¹))
        calc (x : G) * y * (a * ((x : G) * y) * a⁻¹)
            = (x : G) * ((y : G) * (a * x * a⁻¹)) * (a * y * a⁻¹) := by group
          _ = (x : G) * ((a * x * a⁻¹) * (y : G)) * (a * y * a⁻¹) := by rw [h]
          _ = ((x : G) * (a * x * a⁻¹)) * ((y : G) * (a * y * a⁻¹)) := by group }
  have hle : A ⊓ (Z ⊔ ZM) ≤ μ.range := by
    rintro z ⟨hzA, hzV⟩
    have hset' := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z ZM hcommZ).2
    have hzmem : z ∈ (Z : Set G) * (ZM : Set G) := by rw [← hset']; exact hzV
    obtain ⟨x, hx, y, hy, rfl⟩ := hzmem
    obtain ⟨w, hw, rfl⟩ := hy
    have hcz : a * (x * (a * w * a⁻¹)) * a⁻¹ = x * (a * w * a⁻¹) :=
      mul_inv_eq_iff_eq_mul.mpr (hAcomm a haA _ hzA)
    have e1 : a * (x * (a * w * a⁻¹)) * a⁻¹ = (a * x * a⁻¹) * w := by
      calc a * (x * (a * w * a⁻¹)) * a⁻¹
          = (a * x * a⁻¹) * ((a * a) * w * (a * a)⁻¹) := by group
        _ = (a * x * a⁻¹) * w := by rw [ha2]; group
    have h3 : (a * x * a⁻¹) * w = x * (a * w * a⁻¹) := by rw [← e1]; exact hcz
    have hwx : w * (a * x * a⁻¹) = (a * x * a⁻¹) * w := hcommZ w hw _ ⟨x, hx, rfl⟩
    have h4 : x⁻¹ * w = (a * w * a⁻¹) * (a * x * a⁻¹)⁻¹ := by
      have h5 : w * (a * x * a⁻¹) = x * (a * w * a⁻¹) := hwx.trans h3
      calc x⁻¹ * w = x⁻¹ * (w * (a * x * a⁻¹)) * (a * x * a⁻¹)⁻¹ := by group
        _ = x⁻¹ * (x * (a * w * a⁻¹)) * (a * x * a⁻¹)⁻¹ := by rw [h5]
        _ = (a * w * a⁻¹) * (a * x * a⁻¹)⁻¹ := by group
    have hxw : x⁻¹ * w ∈ Z ⊓ ZM := by
      refine ⟨Z.mul_mem (Z.inv_mem hx) hw, w * x⁻¹, Z.mul_mem hw (Z.inv_mem hx), ?_⟩
      show a * (w * x⁻¹) * a⁻¹ = x⁻¹ * w
      rw [h4]
      group
    rw [hbot, Subgroup.mem_bot] at hxw
    have hwx' : w = x := by
      have : x⁻¹ * w = 1 := hxw
      calc w = x * (x⁻¹ * w) := by group
        _ = x := by rw [this, mul_one]
    subst hwx'
    exact ⟨⟨w, hx⟩, rfl⟩
  have hAV : Nat.card ↥(A ⊓ (Z ⊔ ZM)) ≤ q := by
    calc Nat.card ↥(A ⊓ (Z ⊔ ZM)) ≤ Nat.card μ.range := Subgroup.card_le_of_le hle
      _ ≤ Nat.card Z := Nat.card_le_card_of_surjective _ μ.rangeRestrict_surjective
      _ = q := hZcard
  have hineq := W153.card_mul_le_of_isMaxElemAbelian hA hVea hVS
  rw [hVcard] at hineq
  have hCpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer ((Z ⊔ ZM : Subgroup G) : Set G)) :=
    Nat.card_pos
  have h2 : q * q * Nat.card ↥(A ⊓ Subgroup.centralizer ((Z ⊔ ZM : Subgroup G) : Set G)) ≤
      (2 * q) * Nat.card ↥(A ⊓ Subgroup.centralizer ((Z ⊔ ZM : Subgroup G) : Set G)) := by
    calc _ ≤ Nat.card A * Nat.card ↥(A ⊓ (Z ⊔ ZM)) := hineq
      _ ≤ (2 * Nat.card ↥(A ⊓ Subgroup.centralizer ((Z ⊔ ZM : Subgroup G) : Set G))) * q :=
        Nat.mul_le_mul hCA hAV
      _ = _ := by ring
  have h3 : q * q ≤ 2 * q := Nat.le_of_mul_le_mul_right h2 hCpos
  nlinarith

theorem thompsonJ_le_normalizer_of_wreath_center {S L Z : Subgroup G} {q : ℕ} (hq : 3 ≤ q)
    (hZS : Z ≤ S ⊓ L) (hZea : IsElemAbelian 2 Z) (hZcard : Nat.card Z = q)
    (hLZ : ∀ z ∈ L, (∀ y ∈ L, y * z = z * y) → z = 1)
    (hZC : ∀ g ∈ Subgroup.normalizer (L : Set G),
      g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
        g ^ 2 ∈ Subgroup.centralizer (L : Set G) → ∀ z ∈ Z, g * z * g⁻¹ = z)
    {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥) :
    thompsonJ S ≤ Subgroup.normalizer (L : Set G) :=
  iSup₂_le fun _ hA => le_normalizer_of_wreath_center hq hZS hZea hZcard hLZ hZC hset hcomm hA

theorem thompsonJ_eq_inf_normalizer_of_wreath_center {S L Z : Subgroup G} {q : ℕ} (hq : 3 ≤ q)
    (hZS : Z ≤ S ⊓ L) (hZea : IsElemAbelian 2 Z) (hZcard : Nat.card Z = q)
    (hLZ : ∀ z ∈ L, (∀ y ∈ L, y * z = z * y) → z = 1)
    (hZC : ∀ g ∈ Subgroup.normalizer (L : Set G),
      g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
        g ^ 2 ∈ Subgroup.centralizer (L : Set G) → ∀ z ∈ Z, g * z * g⁻¹ = z)
    {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥) :
    thompsonJ S = thompsonJ (S ⊓ Subgroup.normalizer (L : Set G)) :=
  (B6.thompsonJ_eq_of_le
    (le_inf (B6.thompsonJ_le S)
      (thompsonJ_le_normalizer_of_wreath_center hq hZS hZea hZcard hLZ hZC hset hcomm))
    inf_le_left).symm

end CFSG.Quasithin
