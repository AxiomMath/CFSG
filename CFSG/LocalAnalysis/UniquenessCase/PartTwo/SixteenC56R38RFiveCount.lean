module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem card_inf_comap_ge_of_isElemAbelian_card_pow_three {M H : Type*} [Group M] [Finite M]
    [Group H] (π : M →* H) {r : ℕ} (hr : r.Prime) {F : Subgroup M} (hF : IsElemAbelian r F)
    (hFcard : Nat.card F = r ^ 3)
    (hker : ∀ A : Subgroup M, A ≤ π.ker → IsElemAbelian r A → Nat.card A ≤ r)
    (hrange : ∀ B : Subgroup H, B ≤ π.range → IsElemAbelian r B → Nat.card B ≤ r ^ 2)
    {L₁ L₂ : Subgroup H} (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hdisj : L₁ ⊓ L₂ = ⊥)
    (hL₁ : ∀ B : Subgroup H, B ≤ L₁ → IsElemAbelian r B → Nat.card B ≤ r)
    (hFL : F.map π ≤ L₁ ⊔ L₂) :
    r ^ 2 ≤ Nat.card ↥(F ⊓ L₂.comap π) := by
  classical
  have hrpos : 0 < r := hr.pos
  let B : Subgroup H := F.map π
  let Z : Subgroup M := F ⊓ π.ker
  have hZel : IsElemAbelian r Z := hF.mono inf_le_left
  have hZle : Nat.card Z ≤ r := hker Z inf_le_right hZel
  have hBel : IsElemAbelian r B := hF.map π
  have hBle_range : B ≤ π.range := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := hx
    exact ⟨m, rfl⟩
  have hBle : Nat.card B ≤ r ^ 2 := hrange B hBle_range hBel
  have hker_eq : (π.domRestrict F).ker = π.ker.subgroupOf F := rfl
  have hrange_eq : (π.domRestrict F).range = B := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m.1, m.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hZcard_eq : Nat.card Z = Nat.card (π.ker.subgroupOf F) := by
    have hmap : (π.ker.subgroupOf F).map F.subtype = Z := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_comm _ _
    calc Nat.card Z = Nat.card ((π.ker.subgroupOf F).map F.subtype) := by rw [hmap]
      _ = Nat.card (π.ker.subgroupOf F) :=
        Subgroup.card_map_of_injective F.subtype_injective
  have hcardF : Nat.card Z * Nat.card B = r ^ 3 := by
    rw [hZcard_eq]
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict F)
    rw [hker_eq, hrange_eq, hFcard] at h
    exact h
  have hZcard : Nat.card Z = r := by
    have h1 : r * r ^ 2 ≤ Nat.card Z * r ^ 2 := by
      calc r * r ^ 2 = r ^ 3 := by ring
        _ = Nat.card Z * Nat.card B := hcardF.symm
        _ ≤ Nat.card Z * r ^ 2 := Nat.mul_le_mul_left _ hBle
    exact le_antisymm hZle (Nat.le_of_mul_le_mul_right h1 (pow_pos hrpos 2))
  have hBcard : Nat.card B = r ^ 2 := by
    have h1 : r * Nat.card B = r * r ^ 2 := by
      calc r * Nat.card B = Nat.card Z * Nat.card B := by rw [hZcard]
        _ = r ^ 3 := hcardF
        _ = r * r ^ 2 := by ring
    exact Nat.mul_left_cancel hrpos h1
  have hcomm' : ∀ a : ↥L₁, ∀ b : ↥L₂, Commute (L₁.subtype a) (L₂.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let ψ : ↥L₁ × ↥L₂ →* H := MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm'
  have hψ_range : ψ.range = L₁ ⊔ L₂ := by
    show (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm').range = L₁ ⊔ L₂
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hdisj' : Disjoint L₁.subtype.range L₂.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.mpr hdisj
  have hψ_inj : Function.Injective ψ := by
    show Function.Injective (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm')
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨Subgroup.subtype_injective L₁, Subgroup.subtype_injective L₂, hdisj'⟩
  let β : ↥B →* ↥L₁ × ↥L₂ :=
    (MonoidHom.ofInjective hψ_inj).symm.toMonoidHom.comp
      (B.subtype.codRestrict ψ.range fun x => by
        rw [hψ_range]
        exact hFL x.2)
  have hβ : ∀ x : ↥B, ψ (β x) = B.subtype x := by
    intro x
    exact MonoidHom.apply_ofInjective_symm hψ_inj _
  let θ : ↥B →* ↥L₁ := (MonoidHom.fst ↥L₁ ↥L₂).comp β
  have hθker : θ.ker = (B ⊓ L₂).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hb
      change (β b).1 = 1 at hb
      have hψb : ψ (β b) = B.subtype b := hβ b
      have hval : ((β b).2 : H) = (b : H) := by
        have hψb' : ψ ((1 : ↥L₁), (β b).2) = B.subtype b := by
          rw [show β b = ((1 : ↥L₁), (β b).2) from Prod.ext hb rfl] at hψb
          exact hψb
        change MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm'
          ((1 : ↥L₁), (β b).2) = B.subtype b at hψb'
        rw [MonoidHom.noncommCoprod_apply, map_one, one_mul] at hψb'
        simpa using hψb'
      exact ⟨b.2, by rw [← hval]; exact (β b).2.2⟩
    · rintro ⟨-, hbL₂⟩
      have hψb : ψ (β b) = B.subtype b := hβ b
      have h2 : ψ ((1 : ↥L₁), (⟨(b : H), hbL₂⟩ : ↥L₂)) = B.subtype b := by
        change MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm'
          ((1 : ↥L₁), (⟨(b : H), hbL₂⟩ : ↥L₂)) = B.subtype b
        rw [MonoidHom.noncommCoprod_apply, map_one, one_mul]
        rfl
      have h3 : β b = ((1 : ↥L₁), (⟨(b : H), hbL₂⟩ : ↥L₂)) :=
        hψ_inj (by rw [hψb, h2])
      change (β b).1 = 1
      rw [h3]
  have hθker_card : Nat.card θ.ker = Nat.card ↥(B ⊓ L₂) := by
    rw [hθker]
    have hmap : ((B ⊓ L₂).subgroupOf B).map B.subtype = B ⊓ L₂ := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact le_antisymm inf_le_left (le_inf le_rfl inf_le_left)
    calc Nat.card ((B ⊓ L₂).subgroupOf B)
        = Nat.card (((B ⊓ L₂).subgroupOf B).map B.subtype) :=
          (Subgroup.card_map_of_injective (K := (B ⊓ L₂).subgroupOf B)
            (f := B.subtype) B.subtype_injective).symm
      _ = Nat.card ↥(B ⊓ L₂) := by rw [hmap]
  have hθrange_le : Nat.card θ.range ≤ r := by
    have htop : IsElemAbelian r (⊤ : Subgroup ↥B) := by
      have h := hBel.subgroupOf B
      rwa [Subgroup.subgroupOf_self] at h
    have hel : IsElemAbelian r (θ.range.map L₁.subtype) := by
      have h := htop.map (L₁.subtype.comp θ)
      have hmap : (⊤ : Subgroup ↥B).map (L₁.subtype.comp θ) = θ.range.map L₁.subtype := by
        ext y
        constructor
        · rintro ⟨x, -, rfl⟩
          exact ⟨θ x, ⟨x, rfl⟩, rfl⟩
        · rintro ⟨y', ⟨x, rfl⟩, rfl⟩
          exact ⟨x, trivial, rfl⟩
      rwa [hmap] at h
    have hle : θ.range.map L₁.subtype ≤ L₁ := Subgroup.map_subtype_le (H := L₁) θ.range
    have hbound := hL₁ (θ.range.map L₁.subtype) hle hel
    calc Nat.card θ.range
        = Nat.card (θ.range.map L₁.subtype) :=
          (Subgroup.card_map_of_injective (K := θ.range) (f := L₁.subtype)
            L₁.subtype_injective).symm
      _ ≤ r := hbound
  have hBinf_le : r ≤ Nat.card ↥(B ⊓ L₂) := by
    have hcardθ := Subgroup.card_ker_mul_card_range θ
    rw [hθker_card, hBcard] at hcardθ
    have h1 : r ^ 2 ≤ Nat.card ↥(B ⊓ L₂) * r := by
      calc r ^ 2 = Nat.card ↥(B ⊓ L₂) * Nat.card θ.range := hcardθ.symm
        _ ≤ Nat.card ↥(B ⊓ L₂) * r := Nat.mul_le_mul_left _ hθrange_le
    exact Nat.le_of_mul_le_mul_right (by simpa [pow_two] using h1) hrpos
  let K : Subgroup M := F ⊓ L₂.comap π
  have hKrange : (π.domRestrict K).range = B ⊓ L₂ := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨hmF, hmL₂⟩ := Subgroup.mem_inf.mp m.2
      exact Subgroup.mem_inf.mpr ⟨⟨m.1, hmF, rfl⟩, hmL₂⟩
    · rintro ⟨⟨m, hmF, rfl⟩, hmL₂⟩
      exact ⟨⟨m, Subgroup.mem_inf.mpr ⟨hmF, hmL₂⟩⟩, rfl⟩
  have hKker : Nat.card (π.domRestrict K).ker = Nat.card Z := by
    rw [show (π.domRestrict K).ker = π.ker.subgroupOf K from rfl]
    have hmap : (π.ker.subgroupOf K).map K.subtype = Z := by
      rw [Subgroup.subgroupOf_map_subtype]
      apply le_antisymm
      · intro x hx
        obtain ⟨hxk, hxK⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨hxF, -⟩ := Subgroup.mem_inf.mp hxK
        exact Subgroup.mem_inf.mpr ⟨hxF, hxk⟩
      · intro x hx
        obtain ⟨hxF, hxk⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨hxk, ?_⟩
        refine Subgroup.mem_inf.mpr ⟨hxF, ?_⟩
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hxk]
        exact L₂.one_mem
    calc Nat.card (π.ker.subgroupOf K)
        = Nat.card ((π.ker.subgroupOf K).map K.subtype) :=
          (Subgroup.card_map_of_injective (K := π.ker.subgroupOf K) (f := K.subtype)
            K.subtype_injective).symm
      _ = Nat.card Z := by rw [hmap]
  have hKcard : Nat.card Z * Nat.card ↥(B ⊓ L₂) = Nat.card K := by
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict K)
    rw [hKker, hKrange] at h
    exact h
  calc r ^ 2 = r * r := by ring
    _ ≤ r * Nat.card ↥(B ⊓ L₂) := Nat.mul_le_mul_left r hBinf_le
    _ = Nat.card Z * Nat.card ↥(B ⊓ L₂) := by rw [hZcard]
    _ = Nat.card K := hKcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
