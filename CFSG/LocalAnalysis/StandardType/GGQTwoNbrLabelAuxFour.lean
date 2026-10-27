module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabelAuxInn
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMSolv
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontMComp

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbrLabel_unpack_four {R : Type} [Group R] (h : LieModel R .PSU 4 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 4 ∧ Nonempty (R ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) F (2 ^ 1))) := by
  have hS := h.statedClassicalModel (by decide)
  obtain ⟨F, hF, hFfin, hFcard, he⟩ := recipeUnitary_of_statedClassicalModel hS
  exact ⟨F, hF, hFfin, by simpa using hFcard, he⟩

theorem qTwoNbrLabel_not_central {B D J : Subgroup G} {x y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) {a : ↥K}
    (ha : ∀ k : ↥K, x * (k : G) * x⁻¹ = ((a * k * a⁻¹ : ↥K) : G)) :
    a ∉ Subgroup.center ↥K := by
  intro hacen
  apply hnbr.2.2.2
  have hxK : x ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hka : (⟨k, hk⟩ : ↥K) * a = a * ⟨k, hk⟩ :=
      Subgroup.mem_center_iff.mp hacen ⟨k, hk⟩
    have hfix : a * (⟨k, hk⟩ : ↥K) * a⁻¹ = ⟨k, hk⟩ := by
      rw [hka.symm, mul_assoc, mul_inv_cancel, mul_one]
    have hx : x * k * x⁻¹ = k := by
      have h := ha ⟨k, hk⟩
      rw [show ((a * (⟨k, hk⟩ : ↥K) * a⁻¹ : ↥K) : G) = k from
        congrArg Subtype.val hfix] at h
      simpa using h
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hbot : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
      Subgroup.zpowers_le]
    exact hxK
  rw [hbot]
  exact bot_le

theorem qTwoNbrLabel_pow_three_central {x : G} {K : Subgroup G} (hx3 : x ^ 3 = 1) {a : ↥K}
    (ha : ∀ k : ↥K, x * (k : G) * x⁻¹ = ((a * k * a⁻¹ : ↥K) : G)) :
    a ^ 3 ∈ Subgroup.center ↥K := by
  have hpow : ∀ n : ℕ, ∀ l : ↥K,
      ((a ^ n * l * (a ^ n)⁻¹ : ↥K) : G) = x ^ n * (l : G) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
      intro l
      have hstep : a ^ (n + 1) * l * (a ^ (n + 1))⁻¹
          = a ^ n * (a * l * a⁻¹) * (a ^ n)⁻¹ := by
        simp only [pow_succ]; group
      calc ((a ^ (n + 1) * l * (a ^ (n + 1))⁻¹ : ↥K) : G)
          = ((a ^ n * (a * l * a⁻¹) * (a ^ n)⁻¹ : ↥K) : G) := by rw [hstep]
        _ = x ^ n * (x * (l : G) * x⁻¹) * (x ^ n)⁻¹ := by rw [ih (a * l * a⁻¹), ha l]
        _ = x ^ (n + 1) * (l : G) * (x ^ (n + 1))⁻¹ := by rw [pow_succ]; group
  have hfix : ∀ l : ↥K, a ^ 3 * l * (a ^ 3)⁻¹ = l := by
    intro l
    apply Subtype.ext
    have h := hpow 3 l
    rw [hx3] at h
    simpa using h
  rw [Subgroup.mem_center_iff]
  intro l
  exact (mul_inv_eq_iff_eq_mul.mp (hfix l)).symm

theorem qTwoNbrLabel_four_false {B Bs D J : Subgroup G} {x y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hxBs : x ∈ Bs) (hx3 : x ^ 3 = 1)
    (hperf : commutator ↥K = ⊤) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)))
    (hK : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 2 1) : False := by
  obtain ⟨a, ha⟩ := qTwoNbrLabel_inner hperf hN hK hxBs hx3
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := qTwoNbrLabel_unpack_four hK
  have hna : a ∉ Subgroup.center ↥K := qTwoNbrLabel_not_central hnbr ha
  have hp3 : a ^ 3 ∈ Subgroup.center ↥K := qTwoNbrLabel_pow_three_central hx3 ha
  have hs1 : e (QuotientGroup.mk a) ≠ 1 := fun h =>
    hna ((QuotientGroup.eq_one_iff a).mp ((MulEquiv.map_eq_one_iff e).mp h))
  have hs3 : e (QuotientGroup.mk a) ^ 3 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hp3, map_one]
  have hsol := qTwoFrontM_centralizer_solvable hFcard hs1 hs3
  let φ : ↥K →* LargeEvenProj (LargeEvenSUGroup (Fin 4) F (2 ^ 1)) :=
    (e : _ →* _).comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker ≤ Subgroup.center ↥K := fun k hk =>
    (QuotientGroup.eq_one_iff k).mp ((MulEquiv.map_eq_one_iff e).mp hk)
  have hcz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcomp' : IsComponentOf J
      (K ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    rw [hcz]
    exact hcomp
  exact qTwoFrontM_comp_false (Subgroup.mem_zpowers x) hcomp' φ hφker ha hsol

end CFSG.StandardType.QTwo

end
