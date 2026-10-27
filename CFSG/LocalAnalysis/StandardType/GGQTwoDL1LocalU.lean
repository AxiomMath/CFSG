module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLinPerm
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.GroupTheory.SwapCommute

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

private theorem p9uLU_refl_eq_swap
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {n : ℕ}
    (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ a b : Fin n, a ≠ b →
      GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ a b : Fin n, a ≠ b ∧ r = ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let T : Equiv.Perm (Fin n) →* (V ≃ₗ[ZMod p] V) :=
    (ggLin (p := p) ι).comp ((Subgroup.subtype (ggAutomizer X Bs)).comp ε.toMonoidHom)
  have hT : ∀ π : Equiv.Perm (Fin n),
      T π = ggLin (p := p) ι (((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) := fun _ => rfl
  have hlin : ∀ {φ : MulAut ↥Bs}, GGIsReflection p φ → IsLinRefl (ggLin (p := p) ι φ) := by
    intro φ hφ
    obtain ⟨x, f, hfx, hrepr⟩ := exists_of_ggIsReflection (p := p) ι hφ
    rw [ggLin_eq_reflection ι hfx hrepr]
    exact ⟨x, f, hfx, fun v => Module.reflection_apply v hfx⟩
  have hinj : Function.Injective T := by
    intro x y hxy
    exact ε.injective (Subtype.ext (ggLin_injective ι hxy))
  have hsw : ∀ a b : Fin n, a ≠ b → IsLinRefl (T (Equiv.swap a b)) := by
    intro a b hab
    rw [hT]
    exact hlin (hεrefl a b hab)
  let π : Equiv.Perm (Fin n) := ε.symm ⟨r, hrA⟩
  have hπ : IsLinRefl (T π) := by
    rw [hT]
    have hval : ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r := by
      change ((ε (ε.symm ⟨r, hrA⟩) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
      simp
    rw [hval]
    exact hlin hr
  obtain ⟨a, b, hab, hswap⟩ := isSwap_of_isLinRefl hp2 T hinj hsw hπ
  refine ⟨a, b, hab, ?_⟩
  have hval : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r := by
    rw [← hswap]
    change ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
    change ((ε (ε.symm ⟨r, hrA⟩) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
    simp
  exact hval.symm

theorem qtwoDL1_local_unit {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    {r r' : MulAut ↥Bs} (hrX : r ∈ ggAutomizer X Bs) (hr'X : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) (hr' : GGIsReflection p r') (hne : r * r' ≠ r' * r) :
    216 ≤ Nat.card ↥(ggRankTwoIn X Bs r r') := by
  rw [← hrange] at hrX hr'X ⊢
  obtain ⟨ε, hact, hεrefl⟩ := ggNSDiag_automizer_perm (f := 1) h hd
  have hBs : IsElemAbelian p Bs := h.bstar.2.1
  obtain ⟨a, b, hab, hr_eq⟩ := p9uLU_refl_eq_swap h.prime h.odd hBs ε hεrefl hrX hr
  obtain ⟨c, d, hcd, hr'_eq⟩ := p9uLU_refl_eq_swap h.prime h.odd hBs ε hεrefl hr'X hr'
  have hnc : Equiv.swap a b * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap a b := by
    intro hswap
    apply hne
    have h3 := congrArg (fun π : Equiv.Perm (Fin n) =>
      ((ε π : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)) hswap
    simp only [map_mul, Subgroup.coe_mul] at h3
    rw [← hr_eq, ← hr'_eq] at h3
    exact h3
  obtain ⟨i, j, k, hij, hjk, hik, hswap1, hswap2⟩ :=
    CFSG.GroupTheory.exists_swap_swap_of_not_commute hab hcd hnc
  have hr_eq' : r = ((ε (Equiv.swap i j) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
    rw [hr_eq, hswap1]
  have hr'_eq' : r' = ((ε (Equiv.swap j k) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
    rw [hr'_eq, hswap2]
  have hrfun : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap i j)) * (s : G) * (ψ (ggPermSU (Equiv.swap i j)))⁻¹ := by
    intro s
    rw [hr_eq']
    simpa using hact (Equiv.swap i j) s
  have hr'fun : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap j k)) * (s : G) * (ψ (ggPermSU (Equiv.swap j k)))⁻¹ := by
    intro s
    rw [hr'_eq']
    simpa using hact (Equiv.swap j k) s
  have hcard := ggQTwoDUnit_card_map_coordBlockSU_three hK ψ h.ker h.four_le hij hjk hik
  have hle := ggQTwoDUnit_le_rankTwoIn h hK hd hij hjk hik hrfun hr'fun
  have hthis := Subgroup.card_le_of_le hle
  rw [hcard] at hthis
  exact hthis

end CFSG.StandardType.QTwo

end
