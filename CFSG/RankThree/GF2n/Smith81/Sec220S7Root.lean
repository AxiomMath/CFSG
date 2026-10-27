module

public import CFSG.RankThree.GF2n.Smith81.Sec1Types

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Root

variable [Finite G] {M Q Z : Subgroup G}

theorem card_le_card_inf_centralizer_mul (Hs : StrothHyp M Q Z) {S : Subgroup G}
    (hSQ : S ≤ Q) {d : G} (hd : d ∈ Q) :
    Nat.card S ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({d} : Set G)) * Nat.card Z := by
  let χ : ↥S →* ↥Z := MonoidHom.mk' (fun f => ⟨⁅(f : G), d⁆, comm_mem_Z Hs (hSQ f.2) hd⟩)
    (fun f₁ f₂ => by
      apply Subtype.ext
      show ⁅(f₁ : G) * f₂, d⁆ = ⁅(f₁ : G), d⁆ * ⁅(f₂ : G), d⁆
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, ⁅(f₂ : G), d⁆ = c₂ := ⟨_, rfl⟩
      have hc₂Z : c₂ ∈ Z := hc₂ ▸ comm_mem_Z Hs (hSQ f₂.2) hd
      have hc₁Q : ⁅(f₁ : G), d⁆ ∈ Q := Hs.Z_normal.1 (comm_mem_Z Hs (hSQ f₁.2) hd)
      have e1 : c₂ * (f₁ : G) = f₁ * c₂ := Z_central Hs hc₂Z (hSQ f₁.2)
      have e2 : c₂ * ⁅(f₁ : G), d⁆ = ⁅(f₁ : G), d⁆ * c₂ := Z_central Hs hc₂Z hc₁Q
      have h2 : (f₂ : G) * d * (f₂ : G)⁻¹ = c₂ * d := by
        rw [← hc₂, commutatorElement_def]
        group
      rw [hc₂]
      calc ⁅(f₁ : G) * f₂, d⁆ = f₁ * ((f₂ : G) * d * (f₂ : G)⁻¹) * (f₁ : G)⁻¹ * d⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = (f₁ * c₂) * d * (f₁ : G)⁻¹ * d⁻¹ := by
            rw [h2]
            group
        _ = (c₂ * f₁) * d * (f₁ : G)⁻¹ * d⁻¹ := by rw [e1]
        _ = c₂ * ⁅(f₁ : G), d⁆ := by
            rw [commutatorElement_def]
            group
        _ = ⁅(f₁ : G), d⁆ * c₂ := e2)
  have hker : χ.ker = (S ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf S := by
    ext f
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hf
      have h1 : ⁅(f : G), d⁆ = 1 := congrArg Subtype.val hf
      exact ⟨f.2, (commutatorElement_eq_one_iff_mul_comm.mp h1)⟩
    · rintro ⟨-, hf⟩
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hf)
  have hkc : Nat.card χ.ker = Nat.card ↥(S ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card χ.range ≤ Nat.card Z := Subgroup.card_le_card_group _
  calc Nat.card S = Nat.card χ.ker * Nat.card χ.range := (Subgroup.card_ker_mul_card_range χ).symm
    _ ≤ Nat.card χ.ker * Nat.card Z := Nat.mul_le_mul_left _ hrange
    _ = _ := by rw [hkc]

end Root

end CFSG.RankThree.GF2n.Smith81
