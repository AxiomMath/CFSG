module

public import CFSG.RankThree.PartOne.KE6.E6LRoots
public import CFSG.LieType.Chevalley.AllRootWeylConjugation
public import CFSG.RankThree.PartOne.KE6.E6LRes

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Sign

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L]

theorem xUnit_comp_m27Emb (j : Fin Tag.E6.rank) (c : L) :
    ((xUnit τ L (e6Idx j) c : ModGL τ L) : Module.End L (RootModule τ L)) ∘ₗ m27Emb τ L =
      m27Emb τ L ∘ₗ ((e6Data_valid.xu L (Pi.single j 1) c : GL27 L) :
        Module.End L (Fin e6Data.d →₀ L)) := by
  rw [e6Data_valid.xu_val]
  exact xOp_comp_m27Emb j c

theorem yUnit_comp_m27Emb (j : Fin Tag.E6.rank) (c : L) :
    ((yUnit τ L (e6Idx j) c : ModGL τ L) : Module.End L (RootModule τ L)) ∘ₗ m27Emb τ L =
      m27Emb τ L ∘ₗ ((e6Data_valid.xu L (-Pi.single j 1) c : GL27 L) :
        Module.End L (Fin e6Data.d →₀ L)) := by
  rw [e6Data_valid.xu_val]
  exact yOp_comp_m27Emb j c

theorem weylElt_comp_m27Emb (k : Fin Tag.E6.rank) :
    ((weylElt τ L (e6Idx k) 1 : ModGL τ L) : Module.End L (RootModule τ L)) ∘ₗ m27Emb τ L =
      m27Emb τ L ∘ₗ (((e6Data_valid.nm L k : e6Data_valid.minGroup L) : GL27 L) :
        Module.End L (Fin e6Data.d →₀ L)) := by
  rw [LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_comp_m27Emb (mul_comp_m27Emb (xUnit_comp_m27Emb k _) (yUnit_comp_m27Emb k _))
    (xUnit_comp_m27Emb k _)

theorem exists_sign_pinnedX_comp_m27Emb {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ ε : L, (ε = 1 ∨ ε = -1) ∧ ∀ c : L,
      ((pinnedX τ L (e6Lat τ β) c : ModGL τ L) : Module.End L (RootModule τ L)) ∘ₗ m27Emb τ L =
        m27Emb τ L ∘ₗ ((e6Data_valid.xu L β (ε * c) : GL27 L) :
          Module.End L (Fin e6Data.d →₀ L)) := by
  induction hβ with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun c => ?_⟩
    rw [e6Lat_single, pinnedX_single, one_mul]
    exact xUnit_comp_m27Emb j c
  | @reflect i v hv ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hv6 : IsRoot τ (e6Lat τ v) := isRoot_e6Lat_iff.2 hv
    obtain ⟨σm, hσm, hconj⟩ := e6Data_valid.nm_conj_xm L hv i
    have h6 := (all_root_weyl_infinitesimal.{0} τ).2.2.2.1 (e6Idx i) _ hv6
    set σt : ℤ := allRootWeylSign τ (e6Idx i) (e6Lat τ v) with hσt
    have hσt2 : ((σt : L) * (σt : L)) = 1 := by
      rcases h6 with h6 | h6 <;> simp [h6]
    refine ⟨σm * ε * (σt : L), ?_, fun c => ?_⟩
    · rcases hσm with h1 | h1 <;> rcases hε with h2 | h2 <;> rcases h6 with h3 | h3 <;>
        simp [h1, h2, h3]
    · have e6 := weylElt_one_mul_pinnedX_mul_inv L (e6Idx i) hv6 ((σt : L) * c)
      rw [← mul_assoc, hσt2, one_mul, ← e6Lat_reflect] at e6
      rw [← e6]
      have h1 := mul_comp_m27Emb (mul_comp_m27Emb (weylElt_comp_m27Emb (τ := τ) (L := L) i)
        (h ((σt : L) * c))) (inv_comp_m27Emb (weylElt_comp_m27Emb (τ := τ) (L := L) i))
      have hE : ((e6Data_valid.nm L i : e6Data_valid.minGroup L) : GL27 L) *
          e6Data_valid.xu L v (ε * ((σt : L) * c)) *
          ((e6Data_valid.nm L i : e6Data_valid.minGroup L) : GL27 L)⁻¹ =
          e6Data_valid.xu L (reflect Tag.E6 i v) (σm * ε * (σt : L) * c) := by
        have h2 := congrArg (fun z : e6Data_valid.minGroup L => (z : GL27 L))
          (hconj (ε * ((σt : L) * c)))
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
        rw [show σm * ε * (σt : L) * c = σm * (ε * ((σt : L) * c)) by ring]
        exact h2
      refine h1.trans ?_
      rw [hE]

end Sign

section Gen

variable {τ : Tag} [hτ : E6Sub τ] {K : Type} [Field K]

theorem exists_e6Id_eq {i : Fin τ.rank} (hi : i ∈ e6Set τ) :
    ∃ k : Fin Tag.E6.rank, e6Idx (τ := τ) k = i :=
  exists_e6Idx_eq (e6Set_lt hi)

omit hτ in
theorem closure_Q_generators : Subgroup.closure
    (((↑) : subsystemGroup τ K (e6Set τ) → ModGL τ K) ⁻¹'
      {g | ∃ i ∈ e6Set τ, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c}) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem hom_ext_Q {M : Type*} [Group M] {f g : subsystemGroup τ K (e6Set τ) →* M}
    (hx : ∀ (k : Fin Tag.E6.rank) (c : K),
      f ⟨xUnit τ K (e6Idx k) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ =
        g ⟨xUnit τ K (e6Idx k) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩)
    (hy : ∀ (k : Fin Tag.E6.rank) (c : K),
      f ⟨yUnit τ K (e6Idx k) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ =
        g ⟨yUnit τ K (e6Idx k) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense closure_Q_generators ?_
  rintro ⟨x, hx'⟩ ⟨i, hi, c, h | h⟩
  · obtain ⟨k, rfl⟩ := exists_e6Id_eq hi
    have e : (⟨x, hx'⟩ : subsystemGroup τ K (e6Set τ)) =
        ⟨xUnit τ K (e6Idx k) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ := Subtype.ext h
    rw [e]
    exact hx k c
  · obtain ⟨k, rfl⟩ := exists_e6Id_eq hi
    have e : (⟨x, hx'⟩ : subsystemGroup τ K (e6Set τ)) =
        ⟨yUnit τ K (e6Idx k) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ := Subtype.ext h
    rw [e]
    exact hy k c

end Gen

end CFSG.RankThree.PartOne.KE6
