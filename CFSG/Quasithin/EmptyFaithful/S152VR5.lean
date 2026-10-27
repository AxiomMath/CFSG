module

public import CFSG.Quasithin.EmptyFaithful.S152VR2
public import CFSG.Quasithin.EmptyFaithful.S152VL2b
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.S152UTail

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

namespace S152V

variable {G : Type} [Group G]

theorem center_eq_pCore {L : Subgroup G} (h : centerOf L = pCoreOf 2 L) :
    Subgroup.center ↥L = CFSG.pCore 2 ↥L := by
  apply Subgroup.map_injective (Subgroup.subtype_injective L)
  have h1 : (Subgroup.center ↥L).map L.subtype = centerOf L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact Subgroup.mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨w, hw⟩)
    · rintro ⟨hxL, hxc⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      exact Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)
  rw [h1, h]
  unfold CFSG.Open.pCoreOf
  try with_reducible rfl

theorem normalizer_of_involution {L : Subgroup G} {z : G} (hz2 : z ^ 2 = 1)
    (h : ∀ x ∈ L, z⁻¹ * x * z ∈ L) : z ∈ Subgroup.normalizer (L : Set G) := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := h x hx
    rw [hzinv] at this ⊢
    exact this
  · intro hx
    have := h _ hx
    have e : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    rwa [e] at this

theorem K_le_normalizer_of_cfg [Finite G] (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    {I S Mi L L₀ K P : Subgroup G} {z : G} (cfg : Tail15215Cfg I S Mi L L₀ K P z) :
    K ≤ Subgroup.normalizer (L : Set G) := by
  have hKI : K ≤ I := fun x hx => by
    have := cfg.K_le hx
    rw [cfg.hMi] at this
    exact this.1
  obtain ⟨horb, h2⟩ := hA3 G I S L cfg.sqtk cfg.sylow (Id2519.mem_cComp_of_isComponentIn cfg.comp)
  have h2' : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, conjSubgroupsBy S L = {L, conjByElt t L} := by
    rcases h2 with h | ⟨t, ht, -, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, h⟩
  obtain ⟨t, ht, hcos⟩ := exists_two_cosets cfg.sylow.1 horb h2'
  exact oTwoUpper_le_of_two_cosets hKI cfg.K_o2 ht hcos

theorem inner_sq_central {L : Subgroup G} {z l : G} (hz2 : z ^ 2 = 1) (hl : l ∈ L)
    (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) : ∀ x ∈ L, (l * l) * x = x * (l * l) := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  intro x hx
  have hy : z⁻¹ * x * z = l⁻¹ * x * l := h x hx
  have hyL : l⁻¹ * x * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
  have h1 : z⁻¹ * (z⁻¹ * x * z) * z = x := by
    rw [hzinv]
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz]; group
  have h2 : z⁻¹ * (z⁻¹ * x * z) * z = l⁻¹ * (l⁻¹ * x * l) * l := by
    rw [hy]
    exact h _ hyL
  have h3 : x = (l * l)⁻¹ * x * (l * l) := by
    calc x = l⁻¹ * (l⁻¹ * x * l) * l := h1.symm.trans h2
      _ = (l * l)⁻¹ * x * (l * l) := by group
  calc (l * l) * x = (l * l) * ((l * l)⁻¹ * x * (l * l)) := by rw [← h3]
    _ = x * (l * l) := by group

theorem inner_sq_eq_one_of_center_bot {L : Subgroup G} {z l : G} (hZ : Subgroup.center ↥L = ⊥)
    (hz2 : z ^ 2 = 1) (hl : l ∈ L) (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) : l * l = 1 := by
  have hc := inner_sq_central hz2 hl h
  have hmem : (⟨l * l, L.mul_mem hl hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [hZ] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)

theorem inner_ne_one {L : Subgroup G} {z l : G} (h : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l)
    (hnc : ∃ x ∈ L, z⁻¹ * x * z ≠ x) : l ≠ 1 := by
  intro h1
  obtain ⟨x, hx, hxne⟩ := hnc
  apply hxne
  rw [h x hx, h1]
  group

theorem exists_centralizing_subgroup_of_config_bot {L P : Subgroup G} {z : G}
    (hperf : Group.IsPerfect ↥L) (hZ : Subgroup.center ↥L = ⊥)
    (hOut : ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ g : ↥L, α = MulAut.conj g)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hPz : ∀ x ∈ P, x * z = z * x) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hfaith : ∀ x ∈ P, (∀ y ∈ L, x * y = y * x) → x = 1) :
    ∃ H : Subgroup ↥L, Nat.card H = Nat.card P ∧ (∀ g ∈ H, g ^ 3 = 1) ∧
      ∀ g ∈ H, z⁻¹ * (g : G) * z = g := by
  let ψ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨H, hcard, hH3, hfix⟩ :=
    exists_fixedSubgroup_of_config hperf ψ hZ hOut hPN hz hPz hexp hfaith
  refine ⟨H, hcard, hH3, fun g hg => ?_⟩
  have h1 := hfix g hg
  have h2 : g = ψ (QuotientGroup.mk g) := rfl
  have h3 : inducedAut ψ (L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩) g =
      L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩ g := by
    conv_lhs => rw [h2]
    rw [inducedAut_apply]
    rfl
  rw [h3] at h1
  have h4 := congrArg Subtype.val h1
  simpa using h4

end S152V

end CFSG.Quasithin
