module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviCell
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6iso_conj_injective {R : Type} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut R => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = (g * x * g⁻¹) * g := by rw [hx]
      _ = g * x := by group
  rw [hZ] at hc
  exact hc

private theorem e6iso_holds_of_eq_subgroup {m N : ℕ} {L' : Type} [Group L']
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {A A' : Subgroup (MulAut L')} (h : A = A') (w : GGTorusTorWit m N L' A')
    (hw : w.Holds C M) : (h.symm ▸ w).Holds C M := by
  cases h
  exact hw

private theorem e6iso_n_of_eq_subgroup {m N : ℕ} {L' : Type} [Group L']
    {A A' : Subgroup (MulAut L')} (h : A = A') (w : GGTorusTorWit m N L' A') (k : Fin N) :
    (h.symm ▸ w).n k = w.n k := by
  cases h
  rfl

theorem ggTBJE6Levi_of_isoFrame
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [NeZero p]
    {Bs J X : Subgroup G} {g : G} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs)
    (hJX : J ≤ X) (hgBs : g ∈ Bs) (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hZ : Subgroup.center ↥X = ⊥)
    {R : Type} [Group R] (e : ↥X ≃* R) {E : Subgroup R}
    (hA : (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : R →* MulAut R))
    (hF : GGE6LeviFrame p E) (bX : ↥Bs) (hbX1 : bX ≠ 1)
    (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  obtain ⟨Lf, hLf, ζ, hζ, ι₀, nk, m, wt, hζo, hι₀, hrange, hact, hwn, hwt, hClass⟩ := hF
  haveI : Finite R := Finite.of_equiv ↥X e.toEquiv
  have hZR : Subgroup.center R = ⊥ := by
    have h1 : (Subgroup.center ↥X).map (e : ↥X →* R) = Subgroup.center R :=
      Subgroup.map_center_eq e
    rw [← h1, hZ, Subgroup.map_bot]
  have hinjc : Function.Injective (MulAut.conj : R →* MulAut R) := e6iso_conj_injective hZR
  let ψ : ↥X →* R := e.toMonoidHom
  let Λ : R →* MulAut ↥X := (MulAut.congr e.symm).toMonoidHom.comp MulAut.conj
  have hΛapp : ∀ h l, Λ h l = e.symm (h * e l * h⁻¹) := by
    intro h l
    simp [Λ, MulAut.congr_apply, MulAut.conj_apply]
  have hΛc : ∀ x, Λ (ψ x) = MulAut.conj x := by
    intro x
    refine MulEquiv.ext fun l => ?_
    rw [hΛapp]
    apply e.injective
    simp [ψ, MulAut.conj_apply]
  have hΛn : ∀ h l, ψ (Λ h l) = h * ψ l * h⁻¹ := by
    intro h l
    rw [hΛapp]
    simp [ψ]
  have hΛi : Function.Injective Λ := by
    intro h h' hh
    apply hinjc
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := e.surjective r
    have h2 := congrArg (fun φ : MulAut ↥X => e (φ l)) hh
    simp only [hΛapp, MulEquiv.apply_symm_apply] at h2
    simpa [MulAut.conj_apply] using h2
  have hA' : (E.map (MulAut.conj : R →* MulAut R)).map (MulAut.congr e.symm).toMonoidHom =
      (ggGamma X hN).range := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut ↥X) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  have hAΛ : (ggGamma X hN).range = E.map Λ := by
    rw [← hA', Subgroup.map_map]
  let w'' : GGTorusTorWit m 6 ↥X
      ((E.map (MulAut.conj : R →* MulAut R)).map (MulAut.congr e.symm).toMonoidHom) :=
    wt.transport e.symm
  have hw'' : w''.Holds CartanMatrix.E₆ CoxeterMatrix.E₆ := wt.holds_transport e.symm hwt
  let w' : GGTorusTorWit m 6 ↥X ((ggGamma X hN).range) := hA' ▸ w''
  have hw' : w'.Holds CartanMatrix.E₆ CoxeterMatrix.E₆ :=
    e6iso_holds_of_eq_subgroup hA'.symm w'' hw''
  have hwn' : ∀ k, w'.n k = e.symm (nk k) := by
    intro k
    have h1 : w'.n k = w''.n k := e6iso_n_of_eq_subgroup hA'.symm w'' k
    rw [h1, GGTorusTorWit.transport_n, hwn]
  have hψk : ψ.ker ≤ Subgroup.center ↥X := by
    intro x hx
    have hx1 : x = 1 := e.injective (by simpa [ψ] using hx)
    rw [hx1]
    exact Subgroup.one_mem _
  have hZp : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1 := fun z hz _ => by
    rw [hZ] at hz
    exact Subgroup.mem_bot.mp hz
  refine ggTBJE6Levi_of_frame (E := E) hp2 hp3 hBs hSC hJX hgBs hJg hgX hcomp hN hZp ψ
    e.surjective hψk Λ hΛi hΛc hΛn hAΛ ι₀ hι₀ hrange w' ?_ hw' hζ hζo hClass bX hbX1 hbXc hcardJ
  intro k s
  rw [hwn' k]
  simpa [ψ] using hact k s

theorem ggTBJE6LeviL_of_cellFn
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (cell : IsElemAbelian p Bs →
      (∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs) → J ≤ L → y ∈ Bs →
      J ≤ Subgroup.centralizer ({y} : Set G) → (∃ l ∈ L, y * l * y⁻¹ ≠ l) →
      IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) → ∀ bX : ↥Bs, bX ≠ 1 →
      (bX : G) ∈ Subgroup.centralizer (L : Set G) →
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 →
      GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hH.1.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hD : D = Subgroup.closure {x, y} := hnb.2.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hgX : ∃ l ∈ L, y * l * y⁻¹ ≠ l := by
    by_contra h
    have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      by_contra hne
      exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
    have hyx : y ∈ Subgroup.zpowers x := by
      rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
      exact ⟨hyB, hyC⟩
    have hle : D ≤ Subgroup.zpowers x := by
      rw [hD, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact hyx
    have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hx1] at h1
    have : 1 < p := hp.one_lt
    nlinarith
  have hcomp0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hyD : y ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (by simp)
  have hLC : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD))
    · intro l hl
      refine ⟨hl.1, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hxl : x * l = l * x := Subgroup.mem_centralizer_iff.mp (hLx hl.1) x rfl
      have hyl : y * l = l * y := Subgroup.mem_centralizer_iff.mp hl.2 y rfl
      rw [hD] at hd
      refine Subgroup.closure_induction (p := fun d _ => d * l = l * d) ?_ ?_ ?_ ?_ hd
      · rintro d (rfl | rfl)
        · exact hxl
        · exact hyl
      · simp
      · intro a b _ _ ha hb
        rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
      · intro a _ ha
        exact (Commute.inv_left ha : Commute a⁻¹ l)
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := hLC ▸ hcomp0
  have hJX : J ≤ L := hcomp.1.trans inf_le_left
  have hJg : J ≤ Subgroup.centralizer ({y} : Set G) := hcomp.1.trans inf_le_right
  have hbXc : (x : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hx1' : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  exact cell hBs hSC hJX hyBs hJg hgX hcomp ⟨x, hxBs⟩ hx1' hbXc hcardJ

theorem ggTBJE6LeviK_of_cellFn
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K)
    (cell : IsElemAbelian p Bs →
      (∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs) → J ≤ K → x ∈ Bs →
      J ≤ Subgroup.centralizer ({x} : Set G) → (∃ l ∈ K, x * l * x⁻¹ ≠ l) →
      IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) → ∀ bX : ↥Bs, bX ≠ 1 →
      (bX : G) ∈ Subgroup.centralizer (K : Set G) →
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 →
      GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hH.1.2.1.2.2.2
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hH.1.1.2.2.2.2.2.2.1 hH.1.2.2 hnb hJK
  have hJg : J ≤ Subgroup.centralizer ({x} : Set G) := hcomp.1.trans inf_le_right
  have hgX : ∃ l ∈ K, x * l * x⁻¹ ≠ l := by
    by_contra h
    refine not_mem_centralizer_of_nbr hnb (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    by_contra hne
    exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
  have hbXc : (y : G) ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hl) y rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hy1' : (⟨y, hyBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hnb.1.2.2.1 (congrArg Subtype.val h)
  exact cell hBs hSC hJK hxBs hJg hgX hcomp ⟨y, hyBs⟩ hy1' hbXc hcardJ

end CFSG.StandardType

end
