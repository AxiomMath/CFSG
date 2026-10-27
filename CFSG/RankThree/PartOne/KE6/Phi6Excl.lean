module

public import CFSG.RankThree.PartOne.KE6.Phi6Shape
public import CFSG.RankThree.Lattice.SteinbergBIE6TwoA2Graph

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Ω : Type} [Field Ω]

theorem two_mul_le_of_pow_eq [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (k₂ : Subfield Ω) (hk₂ : ∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ c ∈ k₂, c ^ ℓ ^ n = c) : 2 * f ≤ n := by
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hcardS : Nat.card {c : Ω | c ^ ℓ ^ n = c} = ℓ ^ n := natCard_setOf_pow_eq_self hn
  have hcardk : Nat.card {c : Ω | c ^ ℓ ^ (2 * f) = c} = ℓ ^ (2 * f) :=
    natCard_setOf_pow_eq_self (by omega)
  have hsub : {c : Ω | c ^ ℓ ^ (2 * f) = c} ⊆ {c : Ω | c ^ ℓ ^ n = c} := fun c hc =>
    h c ((hk₂ c).2 (by rw [hq2]; exact hc))
  have hfin : Finite {c : Ω | c ^ ℓ ^ n = c} :=
    Nat.finite_of_card_ne_zero (by rw [hcardS]; exact (pow_pos (Fact.out : ℓ.Prime).pos n).ne')
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardS, hcardk] at h1
  exact (Nat.pow_le_pow_iff_right (Fact.out : ℓ.Prime).one_lt).1 h1

theorem support13_disjoint_56 {i : Fin Tag.E6.rank} (h1 : i ∈ support13) (h2 : i ∈ support56) :
    False := by
  rcases (mem_support13 i).1 h1 with h | h <;> rcases (mem_support56 i).1 h2 with h' | h' <;>
    exact absurd (h.symm.trans h') (by decide)

theorem graph_not_preserve [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p) {y : ModGL Tag.E6 Ω} (hyH : y ∈ torusGroup Tag.E6 Ω)
    (hyp : y ^ p = 1) (hy1 : y ≠ 1)
    (hker : torusRootKernel y = parabolicRoots Tag.E6 supportA2A2) (w : WeylGroup Tag.E6)
    (hrc : ∀ b : Fin Tag.E6.rank → Ωˣ, y = rootDiagUnit Tag.E6 b → ∀ v : Fin Tag.E6.rank → ℤ,
      rootChar b (w • permLattice e6Rho v) = rootChar b v)
    (hpres : ∀ α ∈ parabolicRoots Tag.E6 support13,
      w • permLattice e6Rho α ∈ parabolicRoots Tag.E6 support13) : False := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨z, hz⟩ := exists_eq_rootDiagUnit_zetaPow hζ hyH hyp
  set b : Fin Tag.E6.rank → Ωˣ := fun i => ζ ^ (z i).val with hbdef
  have hker' : torusRootKernel y = rootKernel z := by
    rw [hz, torusRootKernel_rootDiagUnit, hbdef, rootCharKernel_zetaPow hζ z]
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hy1
    rw [hz]
    have : b = 1 := by
      rw [hbdef]
      funext i
      simp
    rw [this, rootDiagUnit_one]
  have hcol : ∀ l l' : Fin Tag.E6.rank → ℤ,
      rootChar b l = rootChar b l' ↔ charVal z l = charVal z l' := fun l l' => by
    rw [hbdef, ← mul_inv_eq_one, ← rootChar_sub, rootChar_zetaPow_eq_one_iff hζ, charVal_sub,
      sub_eq_zero]
  have hwz : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x := fun x =>
    (hcol _ _).1 (hrc b hz x)
  have hv : (fun x => (1 : WeylGroup Tag.E6) • x) '' rootKernel z =
      parabolicRoots Tag.E6 CFSG.RankThree.Lattice.supp1356 := by
    simp only [one_smul, Set.image_id']
    rw [← hker']
    exact hker
  obtain ⟨hex1, -⟩ :=
    CFSG.RankThree.Lattice.E6_large_prime_two_A2_graph_stabilizers_exchange_components hp5 z hz0
      1 hv w (graph_dual_fixed_iff.2 hwz)
  obtain ⟨hα, -, -⟩ := single13_mem
  have h1 : w • permLattice e6Rho (Pi.single (e6Index 0) 1) ∈
      (fun x => w • permLattice e6Rho x) '' ((fun x => (1 : WeylGroup Tag.E6)⁻¹ • x) ''
        parabolicRoots Tag.E6 CFSG.RankThree.Lattice.supp13) :=
    ⟨Pi.single (e6Index 0) 1, ⟨Pi.single (e6Index 0) 1, hα, by simp⟩, rfl⟩
  rw [hex1] at h1
  obtain ⟨γ, hγ, hγe⟩ := h1
  have h56 : w • permLattice e6Rho (Pi.single (e6Index 0) 1) ∈
      parabolicRoots Tag.E6 support56 := by
    rw [← hγe]
    simp only [inv_one, one_smul]
    exact hγ
  have h13 := hpres _ hα
  refine IsRoot.ne_zero h13.1 (funext fun i => ?_)
  by_cases hi : i ∈ support13
  · exact h56.2 i (fun hi' => support13_disjoint_56 hi hi')
  · exact h13.2 i hi

end CFSG.RankThree.PartOne.KE6
