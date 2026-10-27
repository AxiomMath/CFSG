module

public import CFSG.Quasithin.EmptyFaithful.SzN4Local

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Center

theorem szN4_sl2_center_trivial {F : Type} [Field F] (h2 : (2 : F) = 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (hA : ∀ B : Matrix.SpecialLinearGroup (Fin 2) F, A * B = B * A) :
    A = 1 := by
  have hc : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.mpr fun B => (hA B).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  simp only [Fintype.card_fin] at hr
  have h1 : r = 1 := by
    have : (r - 1) ^ 2 = 0 := by
      have e : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
      rw [e, hr]; linear_combination (1 - r) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    exact sub_eq_zero.mp this
  apply Subtype.ext
  rw [← hrA, h1]
  simp

end Center

section Iterate

variable {G : Type} [Group G]

theorem szN4_pow_conj_agree {L Q : Subgroup G} {y w : G}
    (hwL : w ∈ Subgroup.normalizer (L : Set G))
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hag : ∀ x ∈ L, (y * x * y⁻¹) * (w * x * w⁻¹)⁻¹ ∈ Q) :
    ∀ j : ℕ, ∀ x ∈ L, (y ^ j * x * (y ^ j)⁻¹) * (w ^ j * x * (w ^ j)⁻¹)⁻¹ ∈ Q := by
  intro j
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
    intro x hx
    have hbL : w ^ j * x * (w ^ j)⁻¹ ∈ L := by
      have hwj : w ^ j ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hwL j
      exact (Subgroup.mem_normalizer_iff.mp hwj x).mp hx
    have h1 := ih x hx
    have h2 := hag _ hbL
    have e : (y ^ (j + 1) * x * (y ^ (j + 1))⁻¹) * (w ^ (j + 1) * x * (w ^ (j + 1))⁻¹)⁻¹ =
        (y * ((y ^ j * x * (y ^ j)⁻¹) * (w ^ j * x * (w ^ j)⁻¹)⁻¹) * y⁻¹) *
          ((y * (w ^ j * x * (w ^ j)⁻¹) * y⁻¹) * (w * (w ^ j * x * (w ^ j)⁻¹) * w⁻¹)⁻¹) := by
      rw [pow_succ', pow_succ']; group
    rw [e]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hyQ _).mp h1) h2

end Iterate


section TwoElement

variable {G : Type} [Group G] [Finite G]

theorem szN4_two_element_of_trivial_action {L : Subgroup G} {n : ℕ} (hlin : IsLin2Type L n) {y z : G}
    (hyL : y ∈ L) (hzN : z ∈ Subgroup.normalizer (L : Set G))
    (hz : ∀ x ∈ L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 L) {k : ℕ} (hw : (y * z⁻¹) ^ 2 ^ k = 1) :
    ∃ j : ℕ, y ^ 2 ^ j = 1 := by
  have hz' := szN4_inv_comm_mem hzN hz
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hwN : y * z⁻¹ ∈ Subgroup.normalizer (L : Set G) := mul_mem hyN (inv_mem hzN)
  have hyQ : y ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L hyL
  have hag : ∀ x ∈ L, (y * x * y⁻¹) * ((y * z⁻¹) * x * (y * z⁻¹)⁻¹)⁻¹ ∈ pCoreOf 2 L := by
    intro x hx
    have hq : x * z⁻¹ * x⁻¹ * z ∈ pCoreOf 2 L := by
      have := inv_mem (hz' x hx)
      have e : (z⁻¹ * x * z * x⁻¹)⁻¹ = x * z⁻¹ * x⁻¹ * z := by group
      rwa [e] at this
    have e : (y * x * y⁻¹) * ((y * z⁻¹) * x * (y * z⁻¹)⁻¹)⁻¹ = y * (x * z⁻¹ * x⁻¹ * z) * y⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hyQ _).mp hq
  have hiter := szN4_pow_conj_agree hwN hyQ hag (2 ^ k)
  have hg : ∀ x ∈ L, (y ^ 2 ^ k) * x * (y ^ 2 ^ k)⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
    intro x hx
    have := hiter x hx
    rw [hw] at this
    simpa using this
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβc⟩ := hlin
  have hgL : y ^ 2 ^ k ∈ L := Subgroup.pow_mem _ hyL _
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hcard] at this
    simp at this
  have h2 : (2 : F) = 0 := by
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [hcard] at h0
    push_cast at h0
    exact (pow_eq_zero_iff hn0).mp h0
  have hα1 : α ⟨y ^ 2 ^ k, hgL⟩ = 1 := by
    apply szN4_sl2_center_trivial h2
    intro B
    obtain ⟨x, rfl⟩ := hαs B
    have hmem : (⟨y ^ 2 ^ k, hgL⟩ * x * ⟨y ^ 2 ^ k, hgL⟩⁻¹ * x⁻¹ : ↥L) ∈ α.ker := by
      rw [hαk, szN4_mem_pCore_iff]
      exact hg x x.2
    have h3 := MonoidHom.mem_ker.mp hmem
    simp only [map_mul, map_inv] at h3
    have h4 : α ⟨y ^ 2 ^ k, hgL⟩ * α x * (α ⟨y ^ 2 ^ k, hgL⟩)⁻¹ = α x := mul_inv_eq_one.mp h3
    calc α ⟨y ^ 2 ^ k, hgL⟩ * α x
        = (α ⟨y ^ 2 ^ k, hgL⟩ * α x * (α ⟨y ^ 2 ^ k, hgL⟩)⁻¹) * α ⟨y ^ 2 ^ k, hgL⟩ := by group
      _ = α x * α ⟨y ^ 2 ^ k, hgL⟩ := by rw [h4]
  have hker : (⟨y ^ 2 ^ k, hgL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hαk ▸ MonoidHom.mem_ker.mpr hα1
  have hQ : y ^ 2 ^ k ∈ pCoreOf 2 L := (szN4_mem_pCore_iff _).mp hker
  obtain ⟨j', hj'⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hQ⟩
  refine ⟨k + j', ?_⟩
  have : (y ^ 2 ^ k) ^ 2 ^ j' = 1 := by simpa using congrArg Subtype.val hj'
  rwa [← pow_mul, ← pow_add] at this

end TwoElement

end CFSG.Quasithin
