module

public import CFSG.Quasithin.H13.NQCatLieMult
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.NQCat.LieMult

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem eq_gX_rC_of_mem_center_one
    {z : ModGL Tag.G2 K}
    (hz : z ∈ parabolicRadical Tag.G2 K {i1} ⊓
      Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K))) :
    ∃ t : K, z = gX rC t := by
  obtain ⟨hzQ, hzC⟩ := hz
  obtain ⟨t₁, t₂, t₃, t₄, t₅, rfl⟩ := coords_one hzQ
  have hN := N1_le_centralizer (K := K)
  have hmem : ∀ {d : Fin Tag.G2.rank → ℤ},
      (d = rA ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ c : K,
        gX d c ∈ parabolicRadical Tag.G2 K {i1} := fun hd c => mem_one hd c
  have hzg : ∀ g ∈ parabolicRadical Tag.G2 K {i1},
      ⁅gX rA t₁ * (gX rU t₂ * (gX rV t₃ * (gX rB t₄ * gX rC t₅))), g⁆ = 1 := by
    intro g hg
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have h1N : (1 : ModGL Tag.G2 K) ∈ N1 := N1.one_mem
  have ha : gX rA t₁ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inl rfl) t₁
  have hu : gX rU t₂ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inl rfl)) t₂
  have hv : gX rV t₃ ∈ parabolicRadical Tag.G2 K {i1} := hmem (Or.inr (Or.inr (Or.inl rfl))) t₃
  have hb : gX rB t₄ ∈ parabolicRadical Tag.G2 K {i1} :=
    hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) t₄
  have ht₁ : t₁ = 0 := by
    have st := hzg (gX rB 1) (hmem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 1)
    have v1 : ⁅gX rA t₁, gX rB (1 : K)⁆ = gX rC (t₁ * 1) := rel_ab _ _
    have v2 : ⁅gX rU t₂, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_ub _ _)
    have v3 : ⁅gX rV t₃, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_vb _ _)
    have v4 : ⁅gX rB t₄, gX rB (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v5 : ⁅gX rC t₅, gX rB (1 : K)⁆ = 1 := commutator_of_commute (comm_bc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₂ : t₂ = 0 := by
    have st := hzg (gX rV 1) (hmem (Or.inr (Or.inr (Or.inl rfl))) 1)
    have v1 : ⁅gX rA t₁, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_av _ _)
    have v2 : ⁅gX rU t₂, gX rV (1 : K)⁆ = gX rC (t₂ * 1) := rel_uv _ _
    have v3 : ⁅gX rV t₃, gX rV (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v4 : ⁅gX rB t₄, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vb 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rV (1 : K)⁆ = 1 := commutator_of_commute (comm_vc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact gX_c_mem_N1 _)
      (by rw [v3]; exact h1N) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₃ : t₃ = 0 := by
    have st := hzg (gX rU 1) (hmem (Or.inr (Or.inl rfl)) 1)
    have v1 : ⁅gX rA t₁, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_au _ _)
    have v2 : ⁅gX rU t₂, gX rU (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v3 : ⁅gX rV t₃, gX rU (1 : K)⁆ = gX rC (1 * t₃) := by
      rw [← commutatorElement_inv, rel_uv, gX_inv]
    have v4 : ⁅gX rB t₄, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_ub 1 t₄).symm
    have v5 : ⁅gX rC t₅, gX rU (1 : K)⁆ = 1 := commutator_of_commute (comm_uc 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact gX_c_mem_N1 _) (by rw [v4]; exact h1N) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  have ht₄ : t₄ = 0 := by
    have st := hzg (gX rA 1) (hmem (Or.inl rfl) 1)
    have v1 : ⁅gX rA t₁, gX rA (1 : K)⁆ = 1 := commutator_of_commute (gX_comm_self _ _ _)
    have v2 : ⁅gX rU t₂, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_au 1 t₂).symm
    have v3 : ⁅gX rV t₃, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_av 1 t₃).symm
    have v4 : ⁅gX rB t₄, gX rA (1 : K)⁆ = gX rC (1 * t₄) := by
      rw [← commutatorElement_inv, rel_ab, gX_inv]
    have v5 : ⁅gX rC t₅, gX rA (1 : K)⁆ = 1 := commutator_of_commute (comm_ac 1 t₅).symm
    rw [comm_five hN ha hu hv hb (by rw [v2]; exact h1N)
      (by rw [v3]; exact h1N) (by rw [v4]; exact gX_c_mem_N1 _) (by rw [v5]; exact h1N),
      v1, v2, v3, v4, v5] at st
    simp only [one_mul, mul_one] at st
    exact gX_eq_one st
  subst ht₁ ht₂ ht₃ ht₄
  exact ⟨t₅, by simp only [gX_zero, one_mul]⟩

theorem g24NoCentralE16_holds :
    G24NoCentralE16 := by
  intro S _ _ hS
  obtain ⟨-, F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_G2_model hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := F) 2).1)
  refine NoCentralE16.of_mulEquiv e (noCentralE16_of_sylow hU₀ fun E hEU hEC => ?_)
  have hFacts := G2.parabolicFacts_one hF le_rfl
  have hUP := posUnipotent_le_parabolicSubgroup (τ := Tag.G2) (K := F) {i1}
  have hQU := parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := F) {i1}
  have hUC : posUnipotent Tag.G2 F ≤ adjointGroup Tag.G2 F := posUnipotent_le_adjointGroup
  have hc : ∀ x : E, ∃ t : F, ((x : adjointGroup Tag.G2 F) : ModGL Tag.G2 F) = gX rC t := by
    intro x
    have hxU : ((x : adjointGroup Tag.G2 F) : ModGL Tag.G2 F) ∈ posUnipotent Tag.G2 F := hEU x.2
    have hxC : ((x : adjointGroup Tag.G2 F) : ModGL Tag.G2 F) ∈
        Subgroup.centralizer (parabolicRadical Tag.G2 F {i1} : Set (ModGL Tag.G2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := Subgroup.mem_centralizer_iff.mp (hEC x.2) ⟨q, hUC (hQU hq)⟩ (hQU hq)
      exact congrArg Subtype.val h1
    exact eq_gX_rC_of_mem_center_one ⟨hFacts.selfCentralizing ⟨hUP hxU, hxC⟩, hxC⟩
  choose β hβ using hc
  have hinj : Function.Injective β := fun x y hxy => by
    apply Subtype.ext
    apply Subtype.ext
    rw [hβ x, hβ y, hxy]
  have h1 : Nat.card E ≤ Nat.card F := Nat.card_le_card_of_injective β hinj
  rw [hF] at h1
  norm_num at h1
  omega

end CFSG.Quasithin.H13.NQCat.LieMult
