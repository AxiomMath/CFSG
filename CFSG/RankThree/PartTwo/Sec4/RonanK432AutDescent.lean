module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.RankThree.PartTwo.Sec4.Item423Res5Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.KFacts (centerDescend)

theorem mem_normalizer_zpowers_of_map {G G' : Type} [Group G] [Group G'] (ρ : G →* G')
    (hρ : Function.Injective ρ) {σ τ : G}
    (h : ρ τ ∈ Subgroup.normalizer ((Subgroup.zpowers (ρ σ) : Subgroup G') : Set G')) :
    τ ∈ Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  have hmem : ∀ y : G, y ∈ Subgroup.zpowers σ ↔ ρ y ∈ Subgroup.zpowers (ρ σ) := by
    intro y
    rw [← MonoidHom.map_zpowers]
    exact (Subgroup.mem_map_iff_mem hρ).symm
  rw [hmem y, hmem (τ * y * τ⁻¹), map_mul, map_mul, map_inv]
  exact h (ρ y)

theorem autWeaklyClosed_descend {L : Type} [Group L] [Group.IsPerfect L] {σ : MulAut L}
    (h : AutWeaklyClosed σ) : AutWeaklyClosed (centerDescend L σ) := by
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have e : MulAut.conj (x : L ⧸ Subgroup.center L) * centerDescend L σ *
      (MulAut.conj (x : L ⧸ Subgroup.center L))⁻¹ =
      centerDescend L (MulAut.conj x * σ * (MulAut.conj x)⁻¹) := by
    rw [map_mul, map_mul, map_inv, Res423Five.centerDescend_conj']
  rw [e] at hxb ⊢
  have hinj : Function.Injective (centerDescend L) := Res423Five.centerDescend_injective
  have h1 := mem_normalizer_zpowers_of_map (centerDescend L) hinj hxb
  have h2 := h x h1
  rw [← MonoidHom.map_zpowers]
  exact Subgroup.mem_map_of_mem _ h2

theorem conj_injective_of_center_eq_bot {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have h1 : MulAut.conj (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, ← hab]; simp
  have h2 : a⁻¹ * b ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut S => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [hZ, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.mp h2)

theorem weaklyClosed_zpowers_of_autWeaklyClosed_conj {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) {b : S} (h : AutWeaklyClosed (MulAut.conj b)) :
    WeaklyClosed (Subgroup.zpowers b) := by
  have hinj := conj_injective_of_center_eq_bot hZ
  intro g hle
  obtain ⟨b', hb'⟩ : ∃ b' : S, b' = g * b * g⁻¹ := ⟨_, rfl⟩
  have hmap : (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers b' := by
    rw [MonoidHom.map_zpowers, hb']
    rfl
  rw [hmap] at hle ⊢
  have hb'N : b' ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup S) : Set S) :=
    hle (Subgroup.mem_zpowers b')
  have hconj : MulAut.conj g * MulAut.conj b * (MulAut.conj g)⁻¹ = MulAut.conj b' := by
    rw [hb', map_mul, map_mul, map_inv]
  have hbi : b'⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup S) : Set S) :=
    (Subgroup.normalizer _).inv_mem hb'N
  have hb'N' := Subgroup.mem_normalizer_iff.mp hb'N
  have hbi' := Subgroup.mem_normalizer_iff.mp hbi
  have hN : MulAut.conj b' ∈ Subgroup.normalizer
      ((Subgroup.zpowers (MulAut.conj b) : Subgroup (MulAut S)) : Set (MulAut S)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        ((hb'N' _).mp (Subgroup.zpow_mem_zpowers b k))
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      have : MulAut.conj b' * MulAut.conj b ^ k * (MulAut.conj b')⁻¹ =
          MulAut.conj (b' * b ^ k * b'⁻¹) := by
        rw [map_mul, map_mul, map_inv, map_zpow]
      rw [this, ← hm, map_zpow]
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hy' : y = MulAut.conj (b'⁻¹ * b ^ k * b') := by
        rw [map_mul, map_mul, map_inv, map_zpow, hk]
        group
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        ((hbi' _).mp (Subgroup.zpow_mem_zpowers b k))
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      rw [hy', ← map_zpow, hm, inv_inv]
  have hmem := h g (by rw [hconj]; exact hN)
  rw [hconj] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hb'eq : b' = b ^ m := by
    apply hinj
    rw [map_zpow]
    exact hm.symm
  have hle' : Subgroup.zpowers b' ≤ Subgroup.zpowers b := by
    rw [Subgroup.zpowers_le, hb'eq]
    exact Subgroup.zpow_mem_zpowers b m
  have hord : orderOf b' = orderOf b := by
    rw [hb']
    exact (MulEquiv.orderOf_eq (MulAut.conj g) b)
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hord]

end CFSG.RankThree.PartTwo.Sec4.RonanK432
