module

public import CFSG.Timmesfeld.ARS.CaseMSkeleton
public import CFSG.Timmesfeld.ARS.CaseERoots
public import CFSG.Timmesfeld.ARS.CaseBHidden
public import CFSG.Timmesfeld.ARS.CaseMD4

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseM

theorem map_rootGroup_mem (hR : IsRootClass R) {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅) (Ψ : K →* G) (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ ∈ R)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : (D.rootGroup γ).map Ψ ∈ R := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single hdiv hγ
  rw [← actsAs_nrep hct w _
    ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i), ← map_conjSub_eq]
  exact hR.conjSub_mem (hP i) _

end CaseM

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem eq_of_deltaSet_eq {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (h : deltaSet R A A₀ B = deltaSet R A A₀ C) : B = C := by
  by_contra hBC
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  obtain ⟨X, hX⟩ := deltaSet_nonempty hS.hyp hA hS.sec8.2 hS.opp hB
  obtain ⟨Y, hY, hXY⟩ := Levi.exists_opposite_mem_leviSet hS.hyp hA hS.sec8.2 hS.opp hX.1
  have hXne : X ≠ ⊥ := hR.ne_bot X hX.1.1.1
  have hYR : Y ∈ R := hY.1.1
  have hYB : Y ∉ deltaSet R A A₀ B := fun hYB =>
    hXY.not_commuting hXne (hS.commuting_of_mem_deltaSet' hB hX hYB)
  have hsB : Special R B Y := (hS.mem_deltaSet_or_special hB hY).resolve_left hYB
  have hsC : Special R C Y := (hS.mem_deltaSet_or_special hC hY).resolve_left (h ▸ hYB)
  obtain ⟨hP, hPB, hPY⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hB hY hsB
  obtain ⟨hP', hP'C, hP'Y⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hC hY hsC
  have hPR : ⁅B, Y⁆ ∈ R := hP.1.1.1
  have hP'R : ⁅C, Y⁆ ∈ R := hP'.1.1.1
  have hBYnc : ¬ Commuting B Y := fun hc => hR.ne_bot _ hsB.1
    (commuting_iff_commutator_eq_bot.1 hc)
  have hCYnc : ¬ Commuting C Y := fun hc => hR.ne_bot _ hsC.1
    (commuting_iff_commutator_eq_bot.1 hc)
  have hPYc : Commuting ⁅B, Y⁆ Y := hPY.1.2.2.symm
  have hP'Yc : Commuting ⁅C, Y⁆ Y := hP'Y.1.2.2.symm
  obtain ⟨Z, hZB, hZP⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hP hPB
  obtain ⟨Z', ⟨hZ'B, hZ'P⟩, hZ'Z⟩ := hS.exists_ne_mem_deltaSet_inter hB hP hPB ⟨hZB, hZP⟩
  have hZY : Commuting Z Y := (hS.commuting_iff_mem_deltaSet_commutator hB hY hsB hZB).2 hZP
  have hZ'Y : Commuting Z' Y :=
    (hS.commuting_iff_mem_deltaSet_commutator hB hY hsB hZ'B).2 hZ'P
  have hZC : Z ∈ deltaSet R A A₀ C := h ▸ hZB
  have hZ'C : Z' ∈ deltaSet R A A₀ C := h ▸ hZ'B
  have hZP' : Z ∈ deltaSet R A A₀ ⁅C, Y⁆ :=
    (hS.commuting_iff_mem_deltaSet_commutator hC hY hsC hZC).1 hZY
  have hZ'P' : Z' ∈ deltaSet R A A₀ ⁅C, Y⁆ :=
    (hS.commuting_iff_mem_deltaSet_commutator hC hY hsC hZ'C).1 hZ'Y
  have hBP' : B ≠ ⁅C, Y⁆ := fun e => hBYnc (e ▸ hP'Yc)
  have hP'B : ⁅C, Y⁆ ∈ lambdaSet R B :=
    hS.mem_lambdaSet_of_mem_deltaSet_inter hB hP' hBP' ⟨hZB, hZP'⟩ ⟨hZ'B, hZ'P'⟩ hZ'Z.symm
  have hCB : C ∈ lambdaSet R B :=
    hS.mem_lambdaSet_of_mem_deltaSet_inter hB hC hBC ⟨hZB, hZC⟩ ⟨hZ'B, hZ'C⟩ hZ'Z.symm
  have hle1 : ⁅C, Y⁆ ≤ B ⊔ C := hS.le_sup_of_mem_lambdaSet hB hC hP' hCB hP'B hP'C
  have hle2 : ⁅C, Y⁆ ≤ B ⊔ ⁅B, Y⁆ := by
    by_cases hPP' : ⁅B, Y⁆ = ⁅C, Y⁆
    · rw [← hPP']
      exact le_sup_right
    · have hP'P : ⁅C, Y⁆ ∈ lambdaSet R ⁅B, Y⁆ :=
        hS.mem_lambdaSet_of_mem_deltaSet_inter hP hP' hPP' ⟨hZP, hZP'⟩ ⟨hZ'P, hZ'P'⟩ hZ'Z.symm
      exact hS.le_sup_of_mem_lambdaSet hB hP hP' hPB hP'B hP'P
  have hs1 : B ⊔ ⁅C, Y⁆ = B ⊔ C :=
    (mem_lambdaSet_of_le_sup hR hiso hBR hCB hBR le_sup_left hP'R hle1 hBP').2
  have hs2 : B ⊔ ⁅C, Y⁆ = B ⊔ ⁅B, Y⁆ :=
    (mem_lambdaSet_of_le_sup hR hiso hBR hPB hBR le_sup_left hP'R hle2 hBP').2
  have hCle : C ≤ B ⊔ ⁅B, Y⁆ := by
    rw [← hs2, hs1]
    exact le_sup_right
  have hCP : C ≠ ⁅B, Y⁆ := fun e => hCYnc (e ▸ hPYc)
  obtain ⟨y, hy, hyC⟩ := CaseB.exists_conjSub_eq_of_le_sup hR hiso hBR hYR hCR hsB hCle hCP
  have hy1 : y ≠ 1 := fun e => hBC (by rw [← hyC, e, conjSub_one])
  have hyV : y ∈ levi R A A₀ := le_gen hY hy
  have hXy : conjSub X y ∈ deltaSet R A A₀ B := by
    rw [h]
    refine ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hyV, ?_⟩
    have := conjSub_mem_lambdaSet hR hX.2 y
    rwa [hyC] at this
  exact (Sec5.opposite_conjSub_self hXY hy hy1).not_commuting hXne
    (hS.commuting_of_mem_deltaSet' hB hX hXy)

theorem conjSub_eq_of_forall_commute {z : G} (hz : z ∈ levi R A A₀)
    (hzV : ∀ v ∈ levi R A A₀, Commute z v) {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    conjSub B z = B := by
  have hR := hS.hyp.root
  have hfix : ∀ {X : Subgroup G}, X ∈ leviSet R A A₀ → ∀ g : G, (∀ x ∈ X, Commute g x) →
      conjSub X g = X := fun _ g hg => conjSub_of_forall_commute fun x hx => hg x hx
  have hzX : ∀ X ∈ leviSet R A A₀, ∀ x ∈ X, Commute z x := fun X hX x hx => hzV x (le_gen hX hx)
  have hzX' : ∀ X ∈ leviSet R A A₀, ∀ x ∈ X, Commute z⁻¹ x := fun X hX x hx =>
    (hzX X hX x hx).inv_left
  refine (hS.eq_of_deltaSet_eq (conjSub_mem_lambdaStar_of_mem_levi hR hB hz) hB ?_)
  ext X
  constructor
  · rintro ⟨hX, hXB⟩
    refine ⟨hX, ?_⟩
    have := conjSub_mem_lambdaSet hR hXB z⁻¹
    rwa [Plane.conjSub_conjSub_inv, hfix hX z⁻¹ (hzX' X hX)] at this
  · rintro ⟨hX, hXB⟩
    refine ⟨hX, ?_⟩
    have := conjSub_mem_lambdaSet hR hXB z
    rwa [hfix hX z (hzX X hX)] at this

theorem commute_of_isSubframe {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {z : G} (hz : z ∈ levi R A A₀)
    (hzV : ∀ v ∈ levi R A A₀, Commute z v) (hzA : ∀ a ∈ A, Commute z a) :
    ∀ e ∈ E, Commute z e := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  obtain ⟨-, -, hcfg⟩ := Sec12.IsSubframe.isConfig hS hfr
  obtain ⟨f, hf, hcard, Ψ, hΨA, -, -, -⟩ := CaseM.exists_hom_D hR hiso le_rfl hcfg
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpar := SpinPlus.isParametrization (n := 4) (K := GaloisField 2 f) CaseM.three_le_four
  have hxmem : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots, ∀ c,
      SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c ∈
        (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ :=
    fun γ hγ c => ((hpar γ hγ).1 _).2 ⟨c, rfl⟩
  have hxsurj : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots,
      ∀ g ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ,
        ∃ c, SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c = g :=
    fun γ hγ g hg => ((hpar γ hγ).1 g).1 hg
  have hsingle : ∀ k : Fin 4, (Pi.single k 1 : Fin 4 → ℤ) ∈
      (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots := fun k =>
    LevisExtras.single_mem_roots (D := Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four) k
  have hΨmem : ∀ k : Fin 4, ∀ c,
      Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single k 1) c) ∈
        ![P 0, E, P 1, P 2] k := by
    intro k c
    rw [← hΨA k]
    exact ⟨_, hxmem _ (hsingle k) c, rfl⟩
  have hP : ∀ k, ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      (Pi.single k 1)).map Ψ ∈ R := fun k => by
    have := hcfg.memA k
    rwa [← hΨA k] at this
  have hmemR : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots,
      ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ).map Ψ ∈ R :=
    fun γ hγ => CaseM.map_rootGroup_mem hR (Spin.plusDatum_isCTGroupDatum CaseM.three_le_four
      (Spin.plusDatum_iSup_eq_top 4 _ CaseM.three_le_four)) rfl Ψ hP hγ
  have hinjγ : ∀ γ ∈ (Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).roots,
      Function.Injective fun c => Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c) := by
    intro γ hγ c d hcd
    let φ : GaloisField 2 f →
        ↥(((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup γ).map Ψ) :=
      fun c => ⟨Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four γ c),
        ⟨_, hxmem γ hγ c, rfl⟩⟩
    have hsurj : Function.Surjective φ := by
      rintro ⟨_, g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hxsurj γ hγ g hg
      exact ⟨c, rfl⟩
    have hbij := hsurj.bijective_of_nat_card_le (by rw [hcard _ (hmemR γ hγ), hF])
    exact hbij.1 (Subtype.ext hcd)
  have hNM : ∀ {X : Subgroup G}, X ∈ leviSet R A A₀ →
      X ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) := fun hX =>
    QD.le_normalizer_M hR hA ⟨hX.1.1, hX.1.2.2⟩
  have hcm₁ : ∀ {n m : G}, n ∈ Subgroup.normalizer ((M R A : Subgroup G) : Set G) →
      m ∈ M R A → ⁅n, m⁆ ∈ M R A := fun {n m} hn hm => by
    rw [commutatorElement_def]
    exact (M R A).mul_mem ((Subgroup.mem_normalizer_iff.1 hn m).1 hm) ((M R A).inv_mem hm)
  have hcm₂ : ∀ {n m : G}, n ∈ Subgroup.normalizer ((M R A : Subgroup G) : Set G) →
      m ∈ M R A → ⁅m, n⁆ ∈ M R A := fun {n m} hn hm => by
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc n]
    refine (M R A).mul_mem hm ?_
    exact (Subgroup.mem_normalizer_iff.1 hn m⁻¹).1 ((M R A).inv_mem hm)
  have hP0 : P 0 ∈ leviSet R A A₀ := (hfr.memP 0).1
  have hP1 : P 1 ∈ leviSet R A A₀ := (hfr.memP 1).1
  have hP2 : P 2 ∈ leviSet R A A₀ := (hfr.memP 2).1
  have hEM : E ≤ M R A := QD.le_M hfr.memE.1
  have r1 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₁ c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 0 1) c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 1 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_α₀_α₁, mul_one]
  have r2 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₂ c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₁ c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 2 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_β₁_α₂, mul_one]
  have r3 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₃ c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₂ c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 3 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_β₂_α₃, mul_one]
  have r4 : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta c) =
      ⁅Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₃ c),
        Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 1 1) 1)⁆ := fun c => by
    rw [← map_commutatorElement, CaseM.commutator_x_β₃_α₁, mul_one]
  have hβ₁M : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₁ c) ∈
      M R A := fun c => by
    rw [r1]
    exact hcm₁ (hNM hP0 (hΨmem 0 c)) (hEM (hΨmem 1 1))
  have hβ₂M : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₂ c) ∈
      M R A := fun c => by
    rw [r2]
    exact hcm₂ (hNM hP1 (hΨmem 2 1)) (hβ₁M c)
  have hβ₃M : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootB₃ c) ∈
      M R A := fun c => by
    rw [r3]
    exact hcm₂ (hNM hP2 (hΨmem 3 1)) (hβ₂M c)
  have hX₃R : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ∈ R := hmemR _ CaseM.mem_roots_B₃
  have hX₃M : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ≤ M R A := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := hxsurj _ CaseM.mem_roots_B₃ g hg
    exact hβ₃M c
  have hθ1 : Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta 1) ≠ 1 :=
    fun h1 => by
      have h0 : Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta 0) = 1 := by
        have e0 := (hpar _ CaseM.mem_roots_theta).2.1 0 0
        rw [add_zero] at e0
        rw [left_eq_mul.1 e0, map_one]
      exact one_ne_zero (hinjγ _ CaseM.mem_roots_theta (h1.trans h0.symm))
  have hncomm : ¬ Commuting (((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ) E := fun hc => hθ1 (by
    rw [r4, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ ⟨_, hxmem _ CaseM.mem_roots_B₃ 1, rfl⟩ _ (hΨmem 1 1))
  have hX₃A : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ≠ A := fun e => hncomm (by rw [e]; exact hfr.memE.1.1.2.2)
  have hX₃E : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      CaseM.rootB₃).map Ψ ≠ E := fun e => hncomm (by rw [e]; exact hR.commuting_self hfr.memE.1.1.1)
  have hX₃EA := ((commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hA
    (mem_lambdaSet_of_le_M_of_hyp hS.hyp hA hX₃R hX₃M hX₃A) hfr.memE.1 hX₃E).resolve_left
      hncomm).2
  have hθA : ∀ c, Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four CaseM.rootTheta c) ∈ A :=
    fun c => by
      rw [r4, ← hX₃EA]
      exact Subgroup.commutator_mem_commutator ⟨_, hxmem _ CaseM.mem_roots_B₃ c, rfl⟩ (hΨmem 1 1)
  have hE1 : ((Spin.plusDatum 4 (GaloisField 2 f) CaseM.three_le_four).rootGroup
      (Pi.single (1 : Fin 4) 1)).map Ψ = E := hΨA 1
  have hzE₀ : conjSub E z = E := hS.conjSub_eq_of_forall_commute hz hzV hfr.memE
  have key := CaseM.commute_of_commute_legs (F := GaloisField 2 f) Ψ (z := z)
    (fun k hk c => by
      refine hzV _ (le_gen ?_ (hΨmem k c))
      fin_cases k
      · exact hP0
      · exact absurd rfl hk
      · exact hP1
      · exact hP2)
    (fun c => by
      have hmem : z * Ψ (SpinPlus.x 4 (GaloisField 2 f) CaseM.three_le_four (Pi.single 1 1) c) *
          z⁻¹ ∈ E := by
        rw [← hzE₀]
        exact conj_mem_conjSub z (hΨmem 1 c)
      rw [← hE1] at hmem
      obtain ⟨g, hg, hgz⟩ := hmem
      obtain ⟨d, rfl⟩ := hxsurj _ (hsingle 1) g hg
      exact ⟨d, hgz.symm⟩)
    (hinjγ _ CaseM.mem_roots_B₁) (hinjγ _ CaseM.mem_roots_theta)
    (fun c => hzA _ (hθA c))
  intro e he
  rw [← hE1] at he
  obtain ⟨g, hg, rfl⟩ := he
  obtain ⟨c, rfl⟩ := hxsurj _ (hsingle 1) g hg
  exact key c

theorem center_levi_eq_bot : Subgroup.center (levi R A A₀) = ⊥ := by
  have hA := hS.mem
  rw [eq_bot_iff]
  rintro ⟨z, hz⟩ hzc
  rw [Subgroup.mem_bot]
  have hzV : ∀ v ∈ levi R A A₀, Commute z v := fun v hv =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨v, hv⟩)).symm
  have hVc : ∀ {D : Subgroup G}, (∀ X ∈ leviSet R A A₀, Commuting D X) →
      ∀ v ∈ levi R A A₀, ∀ d ∈ D, Commute v d := by
    intro D hD v hv d hd
    have hle : levi R A A₀ ≤ Subgroup.centralizer (D : Set G) := iSup₂_le fun X hX x hx =>
      Subgroup.mem_centralizer_iff.2 fun d hd => hD X hX d hd x hx
    exact ((Subgroup.mem_centralizer_iff.1 (hle hv)) d hd).symm
  have hzA : ∀ a ∈ A, Commute z a := hVc (fun X hX => hX.1.2.2) z hz
  have hzA₀ : ∀ a ∈ A₀, Commute z a := hVc (fun X hX => hX.2.2.2) z hz
  obtain ⟨E, C, P, Q, hfr⟩ := hS.exists_isSubframe
  have hzE := hS.commute_of_isSubframe hfr hz hzV hzA
  have hzΛ : ∀ B ∈ lambdaStar R A A₀, ∀ b ∈ B, Commute z b := by
    intro B hB b hb
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hA hS.sec8.2
      hS.max hS.opp hfr.memE hB
    obtain ⟨e, he, rfl⟩ := hb
    exact ((hzV v hv).mul_right (hzE e he)).mul_right (hzV v hv).inv_right
  have hMc : M R A ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [M_eq_gen_lambdaStar hS.hyp hA hS.opp]
    exact gen_le fun B hB b hb => Subgroup.mem_centralizer_singleton_iff.2 (hzΛ B hB b hb).symm
  have hA₀c : A₀ ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzA₀ a ha).symm
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← gen_lambdaSet_sup_eq_top hS.hyp hA hS.opp]
    exact sup_le ((gen_le fun B hB => QD.le_M hB).trans hMc) hA₀c
  have hzc' : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (htop (Subgroup.mem_top g))
  rw [hS.hyp.center, Subgroup.mem_bot] at hzc'
  exact Subtype.ext hzc'

end Sec12

end CFSG.Timmesfeld.ARS
