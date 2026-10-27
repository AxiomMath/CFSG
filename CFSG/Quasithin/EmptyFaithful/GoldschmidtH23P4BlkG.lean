module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.EmptyFaithful.SBc17In
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkD

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_forall {L K : Subgroup G} (h : ∀ l ∈ L, ∀ x ∈ K, l * x * l⁻¹ ∈ K) :
    L ≤ Subgroup.normalizer (K : Set G) := fun l hl => by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h l hl x hx, fun hx => ?_⟩
  have := h l⁻¹ (inv_mem hl) _ hx
  simpa [mul_assoc] using this

theorem modData_of_block {L : Subgroup G} {y : G} (hL : IsShort2 L)
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hyc : y ∈ SBc17.cMod L) :
    ModData L (blockU L) (blockZ L) y := by
  have hUQ : blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) := hL.2.2.1.1
  have hQy : y ∈ Subgroup.normalizer (blockQ L : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L hyN
  have hnU : ∀ g ∈ Subgroup.normalizer (L : Set G),
      g ∈ Subgroup.normalizer (blockQ L : Set G) → ∀ u ∈ blockU L, g * u * g⁻¹ ∈ blockU L :=
    fun g hgL hgQ u hu => conj_mem_commutator hgQ hgL hu
  have hyU : ∀ u ∈ blockU L, y * u * y⁻¹ ∈ blockU L := hnU y hyN hQy
  have hlU : ∀ l ∈ L, ∀ u ∈ blockU L, l * u * l⁻¹ ∈ blockU L := fun l hl =>
    hnU l (Subgroup.le_normalizer hl) (le_normalizer_pCoreOf 2 L hl)
  have habel : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUQ hb)).2 a
      (Subgroup.mem_inf.mp (hUQ ha)).1
  refine ⟨fun z hz => (Subgroup.mem_inf.mp hz).1, habel, hL.2.2.1.2, ?_, hlU, hyU, ?_, ?_, ?_⟩
  · intro z hz l hl
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 l hl
  · intro z hz
    obtain ⟨hzU, hzc⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hyU z hzU, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hl' : y⁻¹ * l * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) l).mp hl
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hzc _ hl'
    calc l * (y * z * y⁻¹) = y * ((y⁻¹ * l * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * l * y)) * y⁻¹ := by rw [hc]
      _ = (y * z * y⁻¹) * l := by group
  · intro l hl u hu
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUQ hu)).2 _
      ((SBc17.mem_cMod.mp hyc).2 l hl)
  · intro W hZW hWU hW
    exact hL.2.2.2.2.2 W hZW hWU (le_normalizer_of_forall hW)

end CFSG.Quasithin.H23P4
