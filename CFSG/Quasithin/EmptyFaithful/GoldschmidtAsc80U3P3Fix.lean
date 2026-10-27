module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80PFix

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3

variable {F : Type} [Field F] [Finite F]

theorem exists_fixed_vector_u3 (hF : Nat.card F = 3 ^ 2) {U : Subgroup (SU3F 3 F)}
    (hU : IsPGroup 3 U) :
    ∃ w : Fin 3 → F, w ≠ 0 ∧ ∀ u ∈ U, matU u *ᵥ w = w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (Fin 3 → F) := by
    rw [Nat.card_fun, hF]
    simp
  obtain ⟨w, hw0, hw⟩ := exists_fixed_ne_zero (V := Fin 3 → F) (p := 3) (U := U) hU hdvd
  exact ⟨w, hw0, fun u hu => hw ⟨u, hu⟩⟩

theorem false_of_normal_three_group_u3 (hF : Nat.card F = 3 ^ 2) {Y : Subgroup (SU3F 3 F)}
    (hirr : IsIrrIn (StatedSU 3 (3 ^ 1) F) Y) {U : Subgroup (SU3F 3 F)} (hU : IsPGroup 3 U)
    (hnorm : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) (hne : U ≠ ⊥) : False := by
  obtain ⟨w, hw0, hw⟩ := exists_fixed_vector_u3 hF hU
  let W : Submodule F (Fin 3 → F) :=
    { carrier := {v | ∀ u ∈ U, matU u *ᵥ v = v}
      add_mem' := fun {a b} ha hb u hu => by rw [Matrix.mulVec_add, ha u hu, hb u hu]
      zero_mem' := fun u _ => Matrix.mulVec_zero _
      smul_mem' := fun c a ha u hu => by rw [Matrix.mulVec_smul, ha u hu] }
  have hinv : ∀ g ∈ Y, ∀ v ∈ W, matU g *ᵥ v ∈ W := by
    intro g hg v hv u hu
    have hu' : g⁻¹ * u * g ∈ U := by simpa using hnorm g⁻¹ (Y.inv_mem hg) u hu
    have h1 : (g⁻¹ * u * g) • v = v := hv _ hu'
    have h2 : u • (g • v) = g • v := by
      calc u • (g • v) = (u * g) • v := (mul_smul u g v).symm
        _ = (g * (g⁻¹ * u * g)) • v := by congr 1; group
        _ = g • ((g⁻¹ * u * g) • v) := mul_smul g _ v
        _ = g • v := by rw [h1]
    exact h2
  have hW : ∀ g : ↥((Y.map (StatedSU 3 (3 ^ 1) F).subtype)), ∀ v ∈ W,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
    rintro ⟨_, g, hg, rfl⟩ v hv
    exact hinv g hg v hv
  rcases hirr W hW with hbot | htop
  · apply hw0
    have hwW : w ∈ W := fun u hu => hw u hu
    rw [hbot] at hwW
    simpa using hwW
  · apply hne
    rw [eq_bot_iff]
    intro u hu
    have hall : ∀ v : Fin 3 → F, matU u *ᵥ v = v := fun v => by
      have hv : v ∈ W := by rw [htop]; trivial
      exact hv u hu
    refine Subgroup.mem_bot.mpr (ext_matU ?_)
    rw [matU_one]
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end CFSG.Quasithin.E2P.Asc80
