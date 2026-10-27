module

public import CFSG.Quasithin.EmptyFaithful.S152VM22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

public section

namespace CFSG.Quasithin.S152V

open CFSG.Blueprint CFSG.GorensteinWalter

variable {F : Type*} [Field F] [Finite F]

theorem no_m22_section_psl2_even (hF : ∃ n : ℕ, Nat.card F = 2 ^ n)
    (B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (φ : B →* NativeSporadic.Carrier .M22) (hφ : Function.Surjective φ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (NativeSporadic.Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  obtain ⟨Q, hQ, x, hx, y, hy, hxy⟩ := exists_nonabelian_two_subgroup
  obtain ⟨S, hS, hSQ⟩ := exists_two_subgroup_map_eq φ hφ Q hQ
  obtain ⟨𝒮, h𝒮⟩ := (hS.map B.subtype).exists_le_sylow
  obtain ⟨n, hn⟩ := hF
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hn 𝒮
  have hcomm : ∀ a b : ↥𝒮, a * b = b * a := fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  rw [← hSQ] at hx hy
  obtain ⟨s₁, hs₁, rfl⟩ := hx
  obtain ⟨s₂, hs₂, rfl⟩ := hy
  apply hxy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have h1 : B.subtype s₁ ∈ (𝒮 : Subgroup _) := h𝒮 ⟨s₁, hs₁, rfl⟩
  have h2 : B.subtype s₂ ∈ (𝒮 : Subgroup _) := h𝒮 ⟨s₂, hs₂, rfl⟩
  have key : (B.subtype s₁ * B.subtype s₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      B.subtype s₂ * B.subtype s₁ := congrArg Subtype.val (hcomm ⟨_, h1⟩ ⟨_, h2⟩)
  exact key

theorem no_m22_section_psl2_odd (hodd : IsOddPrimePower (Nat.card F))
    (B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (φ : B →* NativeSporadic.Carrier .M22) (hφ : Function.Surjective φ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (NativeSporadic.Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  obtain ⟨E, hE2, hE8⟩ := exists_elemAbelian_eight
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE2 x.1 x.2)⟩
  obtain ⟨S, hS, hSE⟩ := exists_two_subgroup_map_eq φ hφ E hEp
  obtain ⟨𝒮, h𝒮⟩ := (hS.map B.subtype).exists_le_sylow
  obtain ⟨m, hm, ⟨ρ⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hodd 𝒮
  have hcyc : HasCyclicIndexTwo ↥𝒮 :=
    HasCyclicIndexTwo.of_surjective ρ.symm.toMonoidHom ρ.symm.surjective
      (hasCyclicIndexTwo_dihedral (pow_ne_zero _ two_ne_zero))
  let ι : ↥S →* ↥𝒮 := (B.subtype.comp S.subtype).codRestrict (𝒮 : Subgroup _)
    (fun s => h𝒮 ⟨s.1, s.2, rfl⟩)
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : ((ι a : ↥𝒮) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
        ((ι b : ↥𝒮) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hS' : HasCyclicIndexTwo ↥S := HasCyclicIndexTwo.of_injective ι hι hcyc
  let ψ : ↥S →* ↥E := (φ.comp S.subtype).codRestrict E (fun s => by
    have : φ (s : B) ∈ S.map φ := ⟨s.1, s.2, rfl⟩
    rwa [hSE] at this)
  have hψ : Function.Surjective ψ := by
    intro e
    have : e.1 ∈ S.map φ := by rw [hSE]; exact e.2
    obtain ⟨s, hs, hse⟩ := this
    exact ⟨⟨s, hs⟩, Subtype.ext hse⟩
  have hE' : HasCyclicIndexTwo ↥E := HasCyclicIndexTwo.of_surjective ψ hψ hS'
  have h4 := card_le_four_of_exponent_two hE' ⊤ (fun x _ => Subtype.ext (by simpa using hE2 x.1 x.2))
  rw [Subgroup.card_top] at h4
  omega

theorem no_m22_section_psl2
    (hF : (∃ n : ℕ, Nat.card F = 2 ^ n) ∨ IsOddPrimePower (Nat.card F))
    (B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (φ : B →* NativeSporadic.Carrier .M22) (hφ : Function.Surjective φ) : False := by
  rcases hF with h | h
  · exact no_m22_section_psl2_even h B φ hφ
  · exact no_m22_section_psl2_odd h B φ hφ

end CFSG.Quasithin.S152V
