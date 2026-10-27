module

public import CFSG.Quasithin.EmptyFaithful.S153PA1c
public import CFSG.Quasithin.EmptyFaithful.S153PA2b
public import CFSG.Quasithin.EmptyFaithful.S153PBb
public import CFSG.Quasithin.EmptyFaithful.S153PCa
public import CFSG.Quasithin.EmptyFaithful.S153PDc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise MatrixGroups

namespace S153P

section Core

variable {G : Type} [Group G]

open CFSG.LieType.BorelTits CFSG.Quasithin.S1417 in
theorem abs56_main [Finite G] {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y) :
    Abs56Concl U Z Mc y := by
  classical
  obtain ⟨u₀, hu₀, h₀⟩ := A.exists_u₀
  have hP := A.pts hu₀ h₀
  have hV0 : V0g Z y = V0of z (zp z y) := A.V0_eq
  have hu₀J : u₀ ∈ Jg U y := Subgroup.mem_sup_left hu₀
  have hu₀'J : (y⁻¹ * u₀ * y) ∈ Jg U y := Subgroup.mem_sup_right (A.u₀'_mem hu₀)
  have hJV : Jg U y ≤ Subgroup.normalizer ((V0of z (zp z y) : Subgroup G) : Set G) := by
    have := A.J_le_normV0
    rwa [hV0] at this
  obtain ⟨βp, hβps, hβpk⟩ := hP.exists_beta (Jg U y) hu₀J hu₀'J hJV
  have hcent : Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G) =
      Subgroup.centralizer ((V0of z (zp z y) : Subgroup G) : Set G) := by rw [hV0]
  have hNJ : Ng U Mc y ≤ Jg U y := A.N_le_J
  have hNn := A.N_normal
  have hNβ : ∀ x : ↥(Jg U y), (x : G) ∈ Ng U Mc y → βp x = 1 := fun x hx =>
    (hβpk x).2 (hcent ▸ A.N_le_cent hx)
  have hkerN := ker_le_of_dihedral hNJ hNn u₀ (y⁻¹ * u₀ * y) hu₀J hu₀'J (A.gen hu₀ h₀)
    (A.u₀_sq hu₀ h₀) (A.u₀'_sq hu₀ h₀) (A.conj_rel hu₀ h₀) βp hβps hNβ
  have hKN : ∀ x : G, x ∈ Jg U y → (x ∈ Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G) ↔ x ∈ Ng U Mc y) := by
    intro x hx
    constructor
    · intro hc
      exact hkerN ⟨x, hx⟩ ((hβpk ⟨x, hx⟩).2 (hcent ▸ hc))
    · intro hn
      exact hcent ▸ A.N_le_cent hn
  have hJnormN : Jg U y ≤ Subgroup.normalizer ((Ng U Mc y : Subgroup G) : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have := hNn j hj n hn
      simpa [mul_assoc] using this
    · intro hn
      have := hNn j⁻¹ (inv_mem hj) _ hn
      simpa [mul_assoc] using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let βsl : ↥(Jg U y) →* SL(2, ZMod 2) := (slEquivPerm.symm : Equiv.Perm (Fin 3) ≃* SL(2, ZMod 2)).toMonoidHom.comp βp
  have hβsl_s : Function.Surjective βsl := slEquivPerm.symm.surjective.comp hβps
  have hβsl_one : ∀ x : ↥(Jg U y), βsl x = 1 ↔ βp x = 1 := by
    intro x
    show slEquivPerm.symm (βp x) = 1 ↔ βp x = 1
    rw [MulEquiv.map_eq_one_iff]
  have hpc : pCoreOf 2 (Jg U y) = Ng U Mc y := by
    apply le_antisymm
    · intro x hx
      have hxJ : x ∈ Jg U y := pCoreOf_le 2 _ hx
      have hn : ∀ a ∈ Jg U y, ∀ b ∈ pCoreOf 2 (Jg U y), a * b * a⁻¹ ∈ pCoreOf 2 (Jg U y) := by
        intro a ha b hb
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (Jg U y) ha) b).mp hb
        exact this
      have h1 := normal_two_sub_trivial βsl hβsl_s (pCoreOf_le 2 _) hn (pCoreOf_isPGroup 2 _) ⟨x, hxJ⟩ hx
      have h2 : βp ⟨x, hxJ⟩ = 1 := (hβsl_one _).1 h1
      exact (hKN x hxJ).1 (hcent ▸ (hβpk _).1 h2)
    · exact le_pCoreOf_of_le_normalizer 2 hNJ hJnormN A.N_isPGroup
  have hj : (y⁻¹ * u₀ * y) * u₀ ∈ Jg U y := Subgroup.mul_mem _ hu₀'J hu₀J
  have hu₀c : u₀ ∉ Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G) := by
    rw [hcent]; exact hP.u₀_not_cent
  have hjc : (y⁻¹ * u₀ * y) * u₀ ∉ Subgroup.centralizer ((V0g Z y : Subgroup G) : Set G) := by
    rw [hcent]; exact hP.j_not_cent
  refine ⟨A.V0_card, ?_, hpc, ?_, A.E_comm, ?_⟩
  · rw [hpc]
    refine exists_natSum (J := Jg U y) (R := Ng U Mc y) (E := Eg U Mc y) (F := Fg U Mc y)
      (X := Xg U Mc y) (u₀ := u₀) (j := (y⁻¹ * u₀ * y) * u₀) βsl hβsl_s ?_ hNJ
      (inf_le_left.trans le_sup_left) le_sup_left le_sup_right rfl A.N_prod hNn A.E_normal
      A.N_abel A.N_sq hu₀J hj (A.mod_α1 hu₀ h₀) (A.mod_α2 hu₀ h₀) (A.mod_δ1 hu₀ h₀)
      (A.mod_δ2 hu₀ h₀) ?_ ?_ ?_ ?_
    · intro x
      rw [hβsl_one, hβpk, ← hcent]
      exact hKN x x.2
    · intro h
      apply hu₀c
      have := (hβsl_one ⟨u₀, hu₀J⟩).1 h
      exact hcent ▸ (hβpk _).1 this
    · rw [← map_mul, hβsl_one, hβpk]
      exact hP.u₀_sq_cent
    · intro h
      apply hjc
      have := (hβsl_one ⟨(y⁻¹ * u₀ * y) * u₀, hj⟩).1 h
      exact hcent ▸ (hβpk _).1 this
    · rw [← map_pow, hβsl_one, hβpk]
      exact hP.j_cube_cent
  · ext x
    rw [hpc, Subgroup.mem_inf]
    constructor
    · intro hx
      have hxJ : x ∈ Jg U y := hNJ hx
      exact ⟨hxJ, (hKN x hxJ).2 hx⟩
    · rintro ⟨hxJ, hxc⟩
      exact (hKN x hxJ).1 hxc
  · intro n hn
    rw [hV0] at hn
    obtain ⟨w, hwJ, hwc⟩ := hP.exists_word (Jg U y) hu₀J hu₀'J n hn
    have hw : w ∈ Subgroup.normalizer ((Eg U Mc y : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he; simpa [mul_assoc] using A.E_normal w hwJ e he
      · intro he; simpa [mul_assoc] using A.E_normal w⁻¹ (inv_mem hwJ) _ he
    have hc := A.cent_normalizes_E _ (hcent ▸ hwc)
    have := Subgroup.mul_mem _ hw hc
    simpa using this

theorem abs56Main : Abs56Main := fun _ _ _ _ _ _ _ _ A => abs56_main A

end Core

end S153P

end CFSG.Quasithin
