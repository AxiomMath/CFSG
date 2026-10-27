module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sp4A
public import CFSG.Quasithin.EmptyFaithful.S146zQArith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Syl

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

namespace E9P2.Sp4

section Borel

variable {A : Type*} [Group A] {L U : Subgroup A} {K : Type} [Field K]

theorem mem_normalizer_iff_mem_borel (ψ : ↥L ≃* StatedSp 2 K) (hUL : U ≤ L)
    (hψU : ∀ l : L, ψ l ∈ unipotent 2 K ↔ (l : A) ∈ U) (l : L) :
    (l : A) ∈ Subgroup.normalizer (U : Set A) ↔ ψ l ∈ borelSubgroup 2 K := by
  rw [← normalizer_unipotent, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have hconj : ∀ m : L, ψ l * ψ m * (ψ l)⁻¹ ∈ unipotent 2 K ↔ (l : A) * m * (l : A)⁻¹ ∈ U :=
    fun m => by
      rw [← map_inv, ← map_mul, ← map_mul, hψU]
      rfl
  constructor
  · intro hl' k
    obtain ⟨m, rfl⟩ := ψ.surjective k
    rw [hconj, hψU]
    exact hl' m
  · intro hk a
    by_cases ha : a ∈ L
    · have := hk (ψ ⟨a, ha⟩)
      rw [hconj, hψU] at this
      exact this
    · refine ⟨fun h => absurd (hUL h) ha, fun h => absurd ?_ ha⟩
      have h1 : (l : A)⁻¹ * ((l : A) * a * (l : A)⁻¹) * l ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem l.2) (hUL h)) l.2
      simpa [mul_assoc] using h1

theorem normalizer_inf_equiv (ψ : ↥L ≃* StatedSp 2 K) (hUL : U ≤ L)
    (hψU : ∀ l : L, ψ l ∈ unipotent 2 K ↔ (l : A) ∈ U) :
    Nonempty (↥(Subgroup.normalizer (U : Set A) ⊓ L) ≃* ↥(borelSubgroup 2 K)) := by
  let ι : ↥(Subgroup.normalizer (U : Set A) ⊓ L) →* ↥L :=
    Subgroup.inclusion (inf_le_right : Subgroup.normalizer (U : Set A) ⊓ L ≤ L)
  let g : ↥(Subgroup.normalizer (U : Set A) ⊓ L) →* ↥(borelSubgroup 2 K) :=
    (ψ.toMonoidHom.comp ι).codRestrict (borelSubgroup 2 K) fun x =>
      (mem_normalizer_iff_mem_borel ψ hUL hψU ⟨x, x.2.2⟩).mp x.2.1
  refine ⟨MulEquiv.ofBijective g ⟨fun x y hxy => ?_, fun b => ?_⟩⟩
  · exact Subgroup.inclusion_injective _ (ψ.injective (congrArg Subtype.val hxy))
  · set l := ψ.symm b.1 with hl
    have hlb : ψ l ∈ borelSubgroup 2 K := by rw [hl, MulEquiv.apply_symm_apply]; exact b.2
    refine ⟨⟨(l : A), (mem_normalizer_iff_mem_borel ψ hUL hψU l).mpr hlb, l.2⟩, ?_⟩
    exact Subtype.ext (ψ.apply_symm_apply b.1)

end Borel

section Order

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem card_le_nine_of_sp4_four (hF : Nat.card F = 4) (ψ₀ : ↥L ≃* StatedSp 2 F)
    {P : Subgroup X} (hPL : P ≤ L) (hP3 : IsPGroup 3 ↥P) : Nat.card P ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : Nat.card L = 979200 := by
    rw [Nat.card_congr ψ₀.toEquiv,
      Nat.card_congr (CFSG.QuasithinUnique.Lin2.Five.projEquiv F).toEquiv]
    exact CFSG.QuasithinUnique.Id2519.USp4.card_projSp_two hF
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP3
  have hdvd : Nat.card P ∣ 979200 := hL ▸ Subgroup.card_dvd_of_le hPL
  by_contra hbig
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have h2 : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 27 ∣ Nat.card P := by
    rw [hn]
    exact pow_dvd_pow 3 hn3
  have := h27.trans hdvd
  omega

end Order

end E9P2.Sp4

section Local

variable {X : Type} [Group X] [Finite X] {L Th Hh Eh R : Subgroup X} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem E9Local.sp4_normalizer_data (h : E9Local L Th Hh Eh R) (hF : ∃ k : ℕ, Nat.card F = 2 ^ k)
    (ψ₀ : ↥L ≃* StatedSp 2 F) :
    Group.IsSolvable ↥(Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) ⊓ L) ∧
      Nat.card ↥(Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) ⊓ L) =
        Nat.card F ^ 2 ^ 2 * (Nat.card F - 1) ^ 2 := by
  obtain ⟨ψ, hψU⟩ := E9P2.Sp4.exists_equiv_unipotent ψ₀ (E9P2.Sp4.isSylowTwoOf_inf h)
  obtain ⟨e⟩ := E9P2.Sp4.normalizer_inf_equiv ψ inf_le_right hψU
  have : Group.IsSolvable ↥(borelSubgroup 2 F) :=
    CFSG.QuasithinUnique.Setup.X7a.isSolvable_borelSubgroup hF
  exact ⟨Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective,
    by rw [Nat.card_congr e.toEquiv, card_borelSubgroup]⟩

theorem E9Local.sp4_eq_two (h : E9Local L Th Hh Eh R) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (ψ₀ : ↥L ≃* StatedSp 2 F)
    (hr : ∀ A : Subgroup X, Hh ≤ A → Group.IsSolvable ↥A → ∀ r : ℕ, r.Prime → r ∣ Nat.card A →
      r = 2 ∨ r = 3) : n = 2 := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hHU, -⟩ := h.sp4_normalizes hF4 ψ₀
  obtain ⟨hNs, hNcard⟩ := h.sp4_normalizer_data ⟨n, hF⟩ ψ₀
  set N : Subgroup X := Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) ⊓ L with hN
  have hHN : Hh ≤ Subgroup.normalizer (N : Set X) := fun x hx =>
    E9P2.Loc.mem_normalizer_inf (Subgroup.le_normalizer (hHU x hx))
      (E9P2.Loc.mem_normalizer_of_normal h.normal_L x)
  have hsolv : Group.IsSolvable ↥(Hh ⊔ N) := E9P2.Loc.isSolvable_sup hHN h.solv_H hNs
  refine m_eq_two_of_prime_dvd hn fun r hr' hrd => ?_
  have hrN : r ∣ Nat.card N := by
    rw [hNcard, hF]
    exact Dvd.dvd.mul_left (dvd_pow hrd two_ne_zero) _
  rcases hr (Hh ⊔ N) le_sup_left hsolv r hr' (hrN.trans (Subgroup.card_dvd_of_le le_sup_right))
    with rfl | rfl
  · exfalso
    obtain ⟨m, hm⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have hp : 0 < 2 ^ n := by positivity
    omega
  · rfl

end Local

end CFSG.Quasithin
