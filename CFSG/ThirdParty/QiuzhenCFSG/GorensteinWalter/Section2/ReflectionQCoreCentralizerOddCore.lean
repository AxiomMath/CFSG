module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed points of an odd prime core lie in the odd core of a reflection centralizer

For a reflection `s` and an odd prime `p`, the subgroup
`C_{O_p(U)}(s)` maps trivially into `C_G(s) / O(C_G(s))`.  Indeed, the
reflection gives a nontrivial central involution in `C_G(s)`, so the
`D`-group classification makes this quotient a `2`-group, while the image
of `C_{O_p(U)}(s)` is a `p`-group.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

public theorem reflection_qCore_centralizer_le_oddCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    centralizerIn (qCoreOf c.U p) s ≤
      oddCoreOf (Subgroup.centralizer ({s} : Set G)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let C : Subgroup G := Subgroup.centralizer ({s} : Set G)
  let X : Subgroup G := centralizerIn (qCoreOf c.U p) s
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c hs
  have hCproper : C ≠ ⊤ := by
    intro hCtop
    have hscenter : s ∈ Subgroup.center G := by
      have hsubset : ({s} : Set G) ⊆ Subgroup.center G :=
        Subgroup.centralizer_eq_top_iff_subset.mp hCtop
      exact hsubset (by simp)
    obtain ⟨g, hg⟩ :=
      fact_2_preamble_involutions_conjugate_proved hmin c.t s
        c.t_involution hsInv
    have hsg : g⁻¹ * s * g = s := by
      have hcomm : s * g = g * s :=
        (Subgroup.mem_center_iff.mp hscenter g).symm
      calc
        g⁻¹ * s * g = g⁻¹ * (s * g) := by group
        _ = g⁻¹ * (g * s) := by rw [hcomm]
        _ = s := by group
    have hts : c.t = s := by
      calc
        c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
        _ = g⁻¹ * s * g := by rw [hg]
        _ = s := hsg
    exact hs.2 (hts ▸ c.t_mem_S0)
  have hDC : IsDGroup C := properSubgroups_areDGroups hmin C hCproper
  have hsC : s ∈ C := by
    simp [C, Subgroup.mem_centralizer_iff]
  let sC : C := ⟨s, hsC⟩
  have hsCcenter : sC ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hsy : s * (y : G) = (y : G) * s := by
      exact Subgroup.mem_centralizer_iff.mp y.2 s (by simp)
    exact hsy.symm
  have hsC2 : sC ^ 2 = 1 := by
    apply Subtype.ext
    exact hsInv.2
  have hsCne : sC ≠ 1 := by
    intro h
    apply hsInv.1
    exact congrArg Subtype.val h
  let O : Subgroup C := pPrimeCore 2 C
  let : O.Normal := pPrimeCore_normal
  let q : C →* C ⧸ O := QuotientGroup.mk' O
  have hQ2 : IsPGroup 2 (C ⧸ O) := by
    simpa [O] using
      preambleCentralInvolution_quotient_two_of_dgroup
        hDC hsCcenter hsC2 hsCne
  have hXC : X ≤ C := inf_le_right
  let X' : Subgroup C := X.subgroupOf C
  have hXp : IsPGroup p X :=
    (qCoreOf_isPGroup c.U p).to_le inf_le_left
  have hX'p : IsPGroup p X' :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXC).symm
  have hmapTwo : IsPGroup 2 (X'.map q) :=
    IsPGroup.to_subgroup hQ2 (X'.map q)
  have hmapP : IsPGroup p (X'.map q) := hX'p.map q
  have hpneTwo : p ≠ 2 := by
    intro h
    subst p
    exact (by decide : ¬ Odd 2) hpodd
  have hmapBot : X'.map q = ⊥ :=
    Disjoint.eq_bot_of_self
      (IsPGroup.disjoint_of_ne 2 p hpneTwo.symm
        (X'.map q) (X'.map q) hmapTwo hmapP)
  intro x hx
  have hxC : x ∈ C := hXC hx
  have hxX' : (⟨x, hxC⟩ : C) ∈ X' :=
    Subgroup.mem_subgroupOf.mpr hx
  have hqx : q ⟨x, hxC⟩ ∈ X'.map q :=
    Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hxX', rfl⟩
  have hqxOne : q ⟨x, hxC⟩ = 1 := by
    rw [hmapBot] at hqx
    exact Subgroup.mem_bot.mp hqx
  have hxO : (⟨x, hxC⟩ : C) ∈ O :=
    (QuotientGroup.eq_one_iff (N := O) ⟨x, hxC⟩).mp hqxOne
  change x ∈ (pPrimeCore 2 C).map C.subtype
  exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hxO, rfl⟩

end

end CFSG.GorensteinWalter
