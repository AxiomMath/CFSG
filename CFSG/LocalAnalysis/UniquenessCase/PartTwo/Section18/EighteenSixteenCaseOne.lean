module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenKHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Lift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16TsModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem rk_le_four_mul_of_singular_su4 {W : Type} [CommGroup W] [Finite W]
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (E : Subgroup W)
    (hE2 : ∀ x ∈ E, x * x = 1)
    (hE : ∀ x ∈ E, ∑ i, (Multiplicative.toAdd (ψ x)) i ^ (2 ^ n + 1) = 0) :
    rk E ≤ 4 * n := by
  classical
  let S : AddSubgroup (Fin 4 → F) := (E.map ψ.toMonoidHom).toAddSubgroup'
  have hcard_conv : Nat.card ↥S = Nat.card ↥(E.map ψ.toMonoidHom) := by
    let e : ↥S ≃ ↥(E.map ψ.toMonoidHom) :=
      { toFun := fun x => ⟨Multiplicative.ofAdd x.val, by
          have h := x.2
          rwa [Subgroup.mem_toAddSubgroup'] at h⟩
        invFun := fun y => ⟨Multiplicative.toAdd y.val, by
          have h := y.2
          simpa [S] using h⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
    exact Nat.card_congr e
  have hcard_map : Nat.card ↥(E.map ψ.toMonoidHom) = Nat.card ↥E :=
    Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective
  have hS : ∀ x ∈ S, x ≠ 0 → ∑ i, x i ^ (2 ^ n + 1) = 0 := by
    intro x hx _
    have hx' : Multiplicative.ofAdd x ∈ E.map ψ.toMonoidHom := by
      rwa [← Subgroup.mem_toAddSubgroup']
    rw [Subgroup.mem_map] at hx'
    obtain ⟨w, hwE, hw⟩ := hx'
    have hxw : x = Multiplicative.toAdd (ψ.toMonoidHom w) := by
      rw [hw]
      rfl
    rw [hxw]
    exact hE w hwE
  have hbound := totally_singular_card_le (n := n) hn hF S hS
  let φ : ↥E → (Fin 4 → F) := fun x => Multiplicative.toAdd (ψ (x : W))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : ψ (x : W) = ψ (y : W) := by
      rw [← Multiplicative.ofAdd.injective.eq_iff, ← Multiplicative.ofAdd.injective.eq_iff]
      change Multiplicative.ofAdd (φ x) = Multiplicative.ofAdd (φ y)
      rw [hxy]
    exact Subtype.ext (ψ.injective h1)
  have hφS : ∀ x : ↥E, φ x ∈ S := by
    intro x
    dsimp only [S]
    rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
    exact ⟨x, x.2, rfl⟩
  exact rk_le_mul_of_card_le E φ hφinj hE2 S hφS (by simpa using hbound)

section Certified


theorem nonsingular_centralizer_le_case1 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h141 : R18_14_1At D V₀ V p L h)
    {f : ℕ}
    (hf2 : 2 ≤ f)
    (hSUn : IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 f)
    (hNat : NatSUn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedSU 4 (2 ^ f) F))
    (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 4 → F))
    (hψ : NatCoordsSU4
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) f F ε ψ)
    (x : IntMod V h.hyp125.isElemAbelian) (hx0 : x.val ∉ V₀)
    (hns : (∑ i, (Multiplicative.toAdd
      (ψ (tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem))) i ^ (2 ^ f + 1)) ≠ 0) :
    centralizer ({x.val} : Set G) ≤ D.M := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
    have hU4 : IsU4 ↥H f := isU4_of_isSUn_four hSUn
    exact (isU4_barSub_cong h h1742 hU4).2.2.2
  have hSU3 : IsSU3 (Bar2 (Opp p (centVec H
      (tilOf V₀ V hV x.val x.val_mem)))) f :=
    (h141 f hf2 hSUn F hF ε ψ hψ x.val x.val_mem hx0).1 hns
  obtain ⟨E, hEH, hEp, hEc, hEfix⟩ :=
    k_K_SU4_nonsingPoint_holds H p f hf2 hSUn hNat h.p_prime hcong F hF ε ψ hψ
      (tilOf V₀ V hV x.val x.val_mem) (by simpa using hns)
  have hHM : H ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.X_le_M
  have hEM : E ≤ Mbar D.M V₀ V hV := hEH.trans hHM
  have hV0lt : Nat.card V₀ < p := by
    have hle : Nat.card V₀ ≤ 2 := (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
    have hp2 : p ≠ 2 := h.p_ne_two
    have := h.p_prime.two_le
    omega
  have hEfix' : ∀ e ∈ E, e (mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩)) =
      mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) := by
    intro e he
    simpa [tilOf] using hEfix e he
  obtain ⟨Q, hQM, hQp, hQc⟩ :=
    C163.exists_noncyclic_le_centralizer hV h.p_prime hV0lt x.val_mem hEM hEp hEc hEfix'
  exact centralizer_le_of_noncyclic D h61 h.hp (hQM.trans inf_le_left) hQp hQc
    (fun h1 => hx0 (h1 ▸ V₀.one_mem))
    ⟨1, by simpa using hV.2 x.val x.val_mem⟩ (hQM.trans inf_le_right)

theorem false_of_rk_imgTil_eq_case1 (D : Data G) (h61 : UC6.R6_1 D)
    {V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D ⊥ V p L)
    (hK : K_SU4Nat_totallySingular) {f : ℕ} (hf2 : 2 ≤ f)
    (hSUn : IsSUn ↥(barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 4 f)
    (hNat : NatSUn (barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 4 f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (ε : ↥(barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedSU 4 (2 ^ f) F))
    (ψ : Vtil ⊥ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 4 → F))
    (hψ : NatCoordsSU4
      (barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) f F ε ψ)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)])
    {U : Subgroup G} (hUV : U ≤ V) (hU : ¬ centralizer (U : Set G) ≤ D.M)
    (hSing : ∀ y ∈ imgTil ⊥ V h.hyp125.isElemAbelian U,
      ∑ i, (Multiplicative.toAdd (ψ y)) i ^ (2 ^ f + 1) = 0)
    (hrk : rk ↥(imgTil ⊥ V h.hyp125.isElemAbelian U) = 4 * f) : False := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    barSub ⊥ V hV (UC22.conjClosure D.M L)
  let Wt : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV U
  have hdata := hK H p f hf2 hSUn hNat h.p_prime hcong F hF ε ψ hψ Wt hrk hSing
  rcases hdata with ⟨X', hX'Wt, hX'ne, Pp, hPH, hPelem, hPc⟩
  let XG : Subgroup G := preTil ⊥ V hV X'
  have hXGV : XG ≤ V := preTil_le ⊥ V hV X'
  have hImage : imgTil ⊥ V hV XG = X' := imgTil_preTil ⊥ V hV X'
  have hXGU : XG ≤ U := by
    intro x hx
    obtain ⟨y, hyval, hy⟩ := (mem_preTil ⊥ V hV X').1 hx
    have hyWt : mkTil ⊥ V hV y ∈ Wt := hX'Wt hy
    obtain ⟨z, hzU, hz⟩ := (mem_imgTil ⊥ V hV U _).1 hyWt
    have hzy : z = y := by
      have h := (mkTil_eq_iff ⊥ V hV z y).1 hz
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h
      exact Subtype.ext h
    rw [← hyval, ← hzy]
    exact hzU
  have hXGne : XG ≠ ⊥ := by
    intro hbot
    apply hX'ne
    rw [← hImage, hbot, TwelveSeventeen.imgTil_bot]
  have hEH : Pp ≤ H := hPH.trans inf_le_left
  have hEM : Pp ≤ Mbar D.M ⊥ V hV := hEH.trans (barSub_mono ⊥ V hV h.X_le_M)
  have hEp : IsPGroup p Pp := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (hPelem.2 x.val x.2)
  have hEstab : Pp ≤ stabSub X' := hPH.trans inf_le_right
  obtain ⟨Q, hQN, hQM, hQp, hQc⟩ :=
    exists_noncyclic_le_normalizer_of_stab hV hXGV hImage h.p_prime hEM hEp hPc hEstab
  exact hQc (isCyclic_of_le_normalizer_of_not_centralizer_le D h61 h hXGV hXGU hXGne hU
    hQN hQM hQp)

theorem rk_imgTil_le_case1 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h141 : R18_14_1At D V₀ V p L h)
    (hKts : K_SU4Nat_totallySingular)
    (hs : P18_13_1 D V₀ V p L h) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    rk ↥(imgTil V₀ V h.hyp125.isElemAbelian U) ≤ 4 * S17.nOf L - 1 + mSub V₀ := by
  classical
  have hV := h.hyp125.isElemAbelian
  obtain ⟨f, hSUn, hNat⟩ := hs
  obtain ⟨-, hnof, hf1, hcong⟩ := isU4_barSub_cong h h1742 (isU4_of_isSUn_four hSUn)
  have hf2 : 2 ≤ f := by omega
  obtain ⟨F, hF, hFfin, hFcard, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  have htil : ∀ x : IntMod V hV,
      tilOf V₀ V hV x.val x.val_mem = mkTil V₀ V hV x := by
    intro x
    change mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) = mkTil V₀ V hV x
    exact congrArg (mkTil V₀ V hV) (IntMod.val_injective rfl)
  have hSing : ∀ x : IntMod V hV, x.val ∈ U → x.val ∉ V₀ →
      ∑ i, (Multiplicative.toAdd (ψ (mkTil V₀ V hV x))) i ^ (2 ^ f + 1) = 0 := by
    intro x hxU hx0
    by_contra hns
    exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
      (nonsingular_centralizer_le_case1 D h61 h h1742 h141 hf2 hSUn hNat hFcard ε ψ hψ
        x hx0 (by rwa [htil x])))
  have hWtSing : ∀ y ∈ imgTil V₀ V hV U,
      ∑ i, (Multiplicative.toAdd (ψ y)) i ^ (2 ^ f + 1) = 0 := by
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U y).1 hy
    by_cases hx0 : x.val ∈ V₀
    · have h1 : mkTil V₀ V hV x = 1 :=
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hx0
      rw [h1, map_one, toAdd_one]
      simp
    · exact hSing x hxU hx0
  have hrk : rk ↥(imgTil V₀ V hV U) ≤ 4 * f :=
    rk_le_four_mul_of_singular_su4 (le_of_lt hf1) hFcard ψ _
      (fun y _ => by simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV y) hWtSing
  rw [hnof]
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    have h0 : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk_bot]
    rw [h0, Nat.add_zero]
    by_cases hlt : rk ↥(imgTil ⊥ V hV U) ≤ 4 * f - 1
    · omega
    · exact absurd (false_of_rk_imgTil_eq_case1 D h61 h hKts hf2 hSUn hNat hFcard ε ψ hψ hcong
        hUV hU hWtSing (by omega)) (by simp)
  · have hm1 : mSub V₀ = 1 := by
      have hle := h.small
      have hne : mSub V₀ ≠ 0 := by
        intro h0
        apply hV0
        have hcard : Nat.card V₀ = 1 := by
          rw [card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup, h0]
          norm_num
        exact (Subgroup.card_eq_one).1 hcard
      omega
    omega

theorem eighteen_sixteen_one (D : Data G) (h61 : UC6.R6_1 D)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h)
    (hKts : K_SU4Nat_totallySingular) :
    R18_16_1At D V₀ V p L h := by
  intro hP
  have hP' := hP
  obtain ⟨f, hSU, hNat⟩ := hP
  obtain ⟨-, hnof, hf1, -⟩ := isU4_barSub_cong h h1742 (isU4_of_isSUn_four hSU)
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) = 8 * S17.nOf L := by
    rw [hnof]
    exact rk_top_eq_eight_mul_of_natSUn hNat
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_rMV_of_forall_rk_imgTil_le D h.hyp125
    (b := 4 * S17.nOf L - 1 + mSub V₀) (c := 4 * S17.nOf L + 1) ?_ ?_
  · have hn2 : 2 ≤ S17.nOf L := by rw [hnof]; exact hf1
    have h8 := le_mSub_of_rk_top_le D h.hyp125 (N := 8 * S17.nOf L) (le_of_eq hrk.symm)
    have hsub := rk_top_vtil_add_mSub V₀ V h.hyp125.isElemAbelian h.hyp125.pairFacts.le
    omega
  · intro U hUV hUC
    exact rk_imgTil_le_case1 D h61 h h1742 h141 hKts hP' hUV hUC

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
