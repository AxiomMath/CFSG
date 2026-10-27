module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.Dihedral.NormalOddSubgroupModels
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.RankThree.PartOne.S12.ZStarStep
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree

def pgl2PermThreeCycle : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2

lemma kleinFourS4_isPGroup : IsPGroup 2 kleinFourS4 :=
  IsPGroup.of_card (n := 2) (by rw [card_kleinFourS4]; norm_num)

lemma kleinFourS4_comm_le (g : Equiv.Perm (Fin 4))
    (h : ∀ v : Equiv.Perm (Fin 4), v ∈ kleinFourS4 → v * g = g * v) :
    g ∈ kleinFourS4 := by
  revert h g
  change ∀ g : Equiv.Perm (Fin 4),
    (∀ v : Equiv.Perm (Fin 4), v ∈ kleinFourFinset → v * g = g * v) → g ∈ kleinFourFinset
  unfold kleinFourFinset
  decide +kernel

lemma kleinFourS4_threeCycle_conj (v : Equiv.Perm (Fin 4)) (hv : v ∈ kleinFourS4)
    (hv1 : v ≠ 1) :
    pgl2PermThreeCycle * v * pgl2PermThreeCycle⁻¹ ∈ kleinFourS4 ∧
      pgl2PermThreeCycle * v * pgl2PermThreeCycle⁻¹ ≠ v := by
  revert v
  change ∀ v : Equiv.Perm (Fin 4), v ∈ kleinFourFinset → v ≠ 1 →
    pgl2PermThreeCycle * v * pgl2PermThreeCycle⁻¹ ∈ kleinFourFinset ∧
      pgl2PermThreeCycle * v * pgl2PermThreeCycle⁻¹ ≠ v
  unfold kleinFourFinset pgl2PermThreeCycle
  decide +kernel

lemma exists_conj_mem_of_isSylowIn_perm_four {D : Subgroup (Equiv.Perm (Fin 4))}
    (hD : CFSG.Quasithin.IsSylowIn 2 D ⊤) {z : Equiv.Perm (Fin 4)}
    (hz1 : z ≠ 1) (hzc : ∀ d ∈ D, d * z = z * d) :
    ∃ h : Equiv.Perm (Fin 4), h * z * h⁻¹ ≠ z ∧ h * z * h⁻¹ ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVle : kleinFourS4 ≤ D :=
    hD.le_of_normal le_top
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr (by
        rw [Subgroup.normalizer_eq_top_iff.mpr kleinFourS4_normal]))
      kleinFourS4_isPGroup
  have hzV : z ∈ kleinFourS4 :=
    kleinFourS4_comm_le z (fun v hv => hzc v (hVle hv))
  obtain ⟨hmem, hne⟩ := kleinFourS4_threeCycle_conj z hzV hz1
  exact ⟨pgl2PermThreeCycle, hne, hVle hmem⟩

lemma isSylowIn_map_subgroupOf_of_mulEquiv {Q : Type} [Group Q] {X D : Subgroup Q}
    {H : Type} [Group H] (hDX : D ≤ X) (hD : CFSG.Quasithin.IsSylowIn 2 D X)
    (e : ↥X ≃* H) :
    CFSG.Quasithin.IsSylowIn 2 ((D.subgroupOf X).map e.toMonoidHom) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, ?_, ?_⟩
  · exact (hD.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hDX).symm).map e.toMonoidHom
  · have hidx : ((D.subgroupOf X).map e.toMonoidHom).index = (D.subgroupOf X).index :=
      Subgroup.index_map_equiv (D.subgroupOf X) e
    rw [Subgroup.relIndex_top_right, hidx]
    exact hD.not_dvd_relIndex

theorem exists_commuting_conj_pgl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {x : CFSG.GorensteinWalter.PGL2 (ZMod p)} (hx : orderOf x = 2) :
    ∃ c : CFSG.GorensteinWalter.PGL2 (ZMod p), c * x * c⁻¹ ≠ x ∧
      c * x * c⁻¹ * x = x * (c * x * c⁻¹) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  let : Finite (CFSG.GorensteinWalter.PGL2 (ZMod p)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) := by
    refine ⟨p, 1, Fact.out, hpodd, le_rfl, ?_⟩
    rw [Nat.card_zmod, pow_one]
  have ht2 : x * x = 1 := by
    have h2 : x ^ 2 = 1 := by simpa [hx] using pow_orderOf_eq_one x
    simpa [pow_two] using h2
  have hodd : ∀ N : Subgroup (CFSG.GorensteinWalter.PGL2 (ZMod p)), N.Normal →
      Odd (Nat.card N) → ∀ n ∈ N, n * x = x * n := by
    intro N hN hNodd n hn
    have hNbot : N = ⊥ :=
      CFSG.DihedralBlueprint.normal_odd_eq_bot_of_pgl2_model (ZMod p) hK
        (MulEquiv.refl (CFSG.GorensteinWalter.PGL2 (ZMod p))) N hN hNodd
    have hn1 : n = 1 := by
      have : n ∈ (⊥ : Subgroup (CFSG.GorensteinWalter.PGL2 (ZMod p))) := by
        simpa [hNbot] using hn
      exact Subgroup.mem_bot.mp this
    rw [hn1, one_mul, mul_one]
  have hnc : x ∉ Subgroup.center (CFSG.GorensteinWalter.PGL2 (ZMod p)) := by
    intro hc
    have hxbot : x ∈ (⊥ : Subgroup (CFSG.GorensteinWalter.PGL2 (ZMod p))) := by
      simpa [CFSG.GorensteinWalter.pgl2_center_eq_bot] using hc
    have hx1 : x = 1 := Subgroup.mem_bot.mp hxbot
    rw [hx1, orderOf_one] at hx
    exact (by decide : (1 : ℕ) ≠ 2) hx
  exact CFSG.RankThree.PartOne.exists_commuting_conj_of_not_central ht2 hodd hnc

theorem exists_commuting_conj_of_mulEquiv_pgl2 {Q : Type} [Group Q] {H : Subgroup Q} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (e : ↥H ≃* CFSG.GorensteinWalter.PGL2 (ZMod p)) {x : Q}
    (hxH : x ∈ H) (hx2 : orderOf x = 2) :
    ∃ c ∈ H, c * x * c⁻¹ ≠ x ∧ c * x * c⁻¹ * x = x * (c * x * c⁻¹) := by
  let xH : ↥H := ⟨x, hxH⟩
  have hx2H : orderOf xH = 2 := by
    rw [← Subgroup.orderOf_coe xH]
    simpa [xH] using hx2
  obtain ⟨c, hcne, hcomm⟩ :=
    exists_commuting_conj_pgl2 (p := p) hp2
      (x := e xH) (by rw [MulEquiv.orderOf_eq, hx2H])
  let cH : ↥H := e.symm c
  have hcH : e cH = c := by simp [cH]
  refine ⟨(cH : Q), cH.2, ?_, ?_⟩
  · intro h
    apply hcne
    have hH : cH * xH * cH⁻¹ = xH := by
      apply Subtype.ext
      simpa [xH] using h
    calc c * e xH * c⁻¹ = e (cH * xH * cH⁻¹) := by simp [hcH, map_mul]
      _ = e xH := by rw [hH]
  · have hcommH : (cH * xH * cH⁻¹) * xH = xH * (cH * xH * cH⁻¹) := by
      apply e.injective
      simpa [hcH, map_mul] using hcomm
    have hval := congrArg Subtype.val hcommH
    simpa [xH] using hval

theorem exists_conj_mem_of_mulEquiv_pgl2_three {Q : Type} [Group Q] [Finite Q]
    {X D : Subgroup Q} (e : ↥X ≃* CFSG.GorensteinWalter.PGL2 (ZMod 3)) (hDX : D ≤ X)
    (hD : CFSG.Quasithin.IsSylowIn 2 D X) {z : Q} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : ∀ d ∈ D, d * z = z * d) :
    ∃ h ∈ X, h * z * h⁻¹ ≠ z ∧ h * z * h⁻¹ ∈ D := by
  let e' : ↥X ≃* Equiv.Perm (Fin 4) :=
    e.trans CFSG.GorensteinWalter.pgl2_three_equiv_perm
  let DX : Subgroup ↥X := D.subgroupOf X
  let D' : Subgroup (Equiv.Perm (Fin 4)) := DX.map e'.toMonoidHom
  let zX : ↥X := ⟨z, hDX hzD⟩
  let z' : Equiv.Perm (Fin 4) := e' zX
  have hD' : CFSG.Quasithin.IsSylowIn 2 D' ⊤ :=
    isSylowIn_map_subgroupOf_of_mulEquiv hDX hD e'
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have hzX : zX = 1 := e'.injective (by simpa [z'] using h)
    simpa [zX] using congrArg Subtype.val hzX
  have hz'c : ∀ d ∈ D', d * z' = z' * d := by
    intro d hd
    obtain ⟨dX, hdX, rfl⟩ := Subgroup.mem_map.mp hd
    have hdD : (dX : Q) ∈ D := Subgroup.mem_subgroupOf.mp hdX
    have hcomm : dX * zX = zX * dX := by
      apply Subtype.ext
      simpa [zX] using hzc (dX : Q) hdD
    simp only [z']
    change e' dX * e' zX = e' zX * e' dX
    rw [← map_mul, ← map_mul, hcomm]
  obtain ⟨w, hwne, hwD⟩ :=
    exists_conj_mem_of_isSylowIn_perm_four hD' hz'1 hz'c
  obtain ⟨xX, rfl⟩ := e'.surjective w
  refine ⟨(xX : Q), xX.2, ?_, ?_⟩
  · intro h
    apply hwne
    have hX : xX * zX * xX⁻¹ = zX := by
      apply Subtype.ext
      simpa [zX] using h
    calc e' xX * z' * (e' xX)⁻¹ = e' (xX * zX * xX⁻¹) := by simp [z', map_mul]
      _ = e' zX := by rw [hX]
  · have hmem' : e' (xX * zX * xX⁻¹) ∈ D' := by
      have hcalc : e' (xX * zX * xX⁻¹) = e' xX * z' * (e' xX)⁻¹ := by
        simp [z', map_mul]
      rw [hcalc]
      exact hwD
    have hmemX : xX * zX * xX⁻¹ ∈ DX := by
      rcases Subgroup.mem_map.mp hmem' with ⟨y, hy, hyeq⟩
      have hy' : y = xX * zX * xX⁻¹ := e'.injective hyeq
      simpa [hy'] using hy
    simpa [zX] using
      (Subgroup.mem_subgroupOf.mp hmemX : ((xX * zX * xX⁻¹ : ↥X) : Q) ∈ D)

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
