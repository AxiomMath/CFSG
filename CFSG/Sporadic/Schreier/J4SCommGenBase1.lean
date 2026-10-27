
module

public import CFSG.Sporadic.Schreier.J4SCommGenBase

public import CFSG.Sporadic.Schreier.J4SLocalNodesBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SCommGenInputs
public import Certificates.Certificate2169
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2.Native MulAction

section Generic

variable {G : Type*} [Group G]

end Generic

abbrev P1 : Subgroup (MulAut N) := P ⊓ stabilizer (MulAut N) (ηN 1)

theorem G1_le_P1 : G1 ≤ P1 := le_inf G1_le_P fun g hg => mem_stabilizer_iff.2 (G1_fix g hg)

theorem G2_le_P1 : G2 ≤ P1 := G2_le_G1.trans G1_le_P1

theorem orbit_two_eq : {m : J | ∃ k ∈ K ⊓ Subgroup.centralizer {η 1}, m = k * η 2 * k⁻¹} =
    Subtype.val '' orbit P1 (ηN 2) := by
  ext m
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Subgroup.mem_inf] at hk
    refine ⟨⟨k * η 2 * k⁻¹, conj_mem_N_of_mem_K hk.1 (η_mem_N 2)⟩,
      ⟨⟨ρK ⟨k, hk.1⟩, Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, mem_stabilizer_iff.2 (ρK_ηN ?_)⟩⟩, ?_⟩, rfl⟩
    · exact conj_eq_of_mem_centralizer hk.2
    · apply Subtype.ext
      show ((ρK ⟨k, hk.1⟩) (ηN 2) : J) = _
      rw [ρK_apply]
      rfl
  · rintro ⟨n, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    obtain ⟨⟨k, hkK⟩, rfl⟩ := (Subgroup.mem_inf.1 hg).1
    have hfix := mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hg).2
    refine ⟨k, Subgroup.mem_inf.2 ⟨hkK, mem_centralizer_of_conj_eq ?_⟩, ?_⟩
    · have := congrArg Subtype.val hfix
      rw [MulAut.smul_def, ρK_apply] at this
      exact this
    · show ((ρK ⟨k, hkK⟩) (ηN 2) : J) = k * η 2 * k⁻¹
      rw [ρK_apply]
      rfl

theorem commVec_span : ∀ c < 2048, ∃ m < 2048, xorSub (commPicks.map commVec) m = c :=
  Certificates.certificate2169

theorem η_inv (b : ℕ) : (η b)⁻¹ = η b := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← η_xor, Nat.xor_self, η_zero]

theorem η_xorSub_mem {D : Subgroup J} :
    ∀ (ws : List ℕ), (∀ w ∈ ws, η w ∈ D) → ∀ m, η (xorSub ws m) ∈ D
  | [], _, _ => by rw [xorSub, η_zero]; exact D.one_mem
  | w :: ws, h, m => by
    rw [xorSub, η_xor]
    refine D.mul_mem ?_ (η_xorSub_mem ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) _)
    split_ifs
    · exact h w List.mem_cons_self
    · rw [η_zero]; exact D.one_mem

theorem sgen_mem_K_one (g : ℕ) (hg : g < 8) :
    sgen idx1[g]! ∈ K ⊓ Subgroup.centralizer {η 1} := by
  refine Subgroup.mem_inf.2 ⟨sgen_mem_K _, mem_centralizer_of_conj_eq ?_⟩
  rw [sgen_conj, ← gens1_eq g hg, fixCheck_parts.1 g hg]

end CFSG.Sporadic.J4Schreier
