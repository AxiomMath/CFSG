module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTorCTori
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusModelAux

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly TableBSymp CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.StandardType.SpJoin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open scoped commutatorElement

namespace SympMinus

private theorem sympMinus_spPlane_stdModel_aux
    {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [NeZero m] {K : Type} [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (hψ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hAe : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))), ∀ l : L', φ (ψ₀ l) = ψ₀ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K)
      (x : LargeEvenProj (LargeEvenSpGroup K m))
      (σ : (Fin m → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A),
      Function.Injective ζ ∧ (∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) ∧
      (∀ f, ψ₀ (σ f) =
        x * LargeEvenProjMk (LargeEvenSpGroup K m) (spPlaneTorus m ζ f) * x⁻¹) ∧
      (∀ f, σ f ^ p = 1) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot (K := K) (m := m)
  have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSpGroup K m)) := ggCenterPrime_sp hp hp2
  have hcpL : ¬ p ∣ Nat.card (Subgroup.center L') := hcp L' ψ₀ hψ hker hperf
  have hsub := sympMinus_range_conj_subset_matConjImage (K := K) (m := m)
  have hrankA : p ^ m ≤ Nat.card A :=
    (ggTorusSCRank_sp (K := K) (m := m) (p := p) hm hp hpq) L' ψ₀ hψ hker hperf A hAe
      (fun a ha => let ⟨φ, hφ, hψa⟩ := hAI a ha; ⟨φ, hsub hφ, hψa⟩) hsc
  obtain ⟨Λ, E, hΛn, hΛinj, -, hE, hAΛ, hEab, hcardE, -⟩ :=
    exists_liftConj_comap_model hp (I := Set.range (MulAut.conj :
        LargeEvenProj (LargeEvenSpGroup K m) →*
          MulAut (LargeEvenProj (LargeEvenSpGroup K m))))
      subset_rfl hZR hψ hker hperf hcpL hAe hAI hsc
  obtain ⟨D⟩ := TorC.nonempty_spTorusData_nonsplit (F := K) hp hp2 hpq
  let ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K := D.ζp
  have hζinj : Function.Injective ζ := D.inj_p
  have hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹ := by
    intro a
    obtain ⟨b, hb⟩ := D.mem_m a
    have hb' : ζ a = D.ζm b := hb.symm
    calc sl2W * ζ a * sl2W⁻¹ = sl2W * D.ζm b * sl2W⁻¹ := by rw [hb']
      _ = (D.ζm b)⁻¹ := by rw [D.inv_m b, map_inv]
      _ = (ζ a)⁻¹ := by rw [hb']
      _ = ζ (a⁻¹) := (map_inv ζ a).symm
  let e : StatedSp m K ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨AutPSp.proj_injective (n := m) (K := K), QuotientGroup.mk'_surjective _⟩
  let E₁ : Subgroup (StatedSp m K) := E.comap e.toMonoidHom
  have hE₁map : E₁.map e.toMonoidHom = E :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E
  have hE₁ab : IsElemAbelian p E₁ := IsElemAbelian.comap hEab e.injective
  have hcardE₁ : Nat.card E₁ = Nat.card E := by
    have h := Subgroup.card_map_of_injective (K := E₁) (f := e.toMonoidHom) e.injective
    rw [hE₁map] at h
    exact h.symm
  have hcard₁ : p ^ m ≤ Nat.card E₁ := by
    rw [hcardE₁, hcardE]
    exact hrankA
  obtain ⟨c, hc⟩ := D.conj m E₁ hE₁ab hcard₁
  have hc' : E₁.map (MulAut.conj c).toMonoidHom = (spPlaneTorus m ζ).range := hc
  let x : LargeEvenProj (LargeEvenSpGroup K m) := (e c)⁻¹
  let τ' : (Fin m → Multiplicative (ZMod p)) →*
      LargeEvenProj (LargeEvenSpGroup K m) :=
    (MulAut.conj x).toMonoidHom.comp (e.toMonoidHom.comp (spPlaneTorus m ζ))
  have hτ'mem : ∀ f, τ' f ∈ E := by
    intro f
    have hT : spPlaneTorus m ζ f ∈ E₁.map (MulAut.conj c).toMonoidHom := by
      rw [hc']
      exact ⟨f, rfl⟩
    obtain ⟨g, hg, hgT⟩ := Subgroup.mem_map.mp hT
    have hgT' : (MulAut.conj c) g = spPlaneTorus m ζ f := hgT
    have hτ'f : τ' f = e g := by
      show (e c)⁻¹ * e (spPlaneTorus m ζ f) * ((e c)⁻¹)⁻¹ = e g
      rw [← hgT', MulAut.conj_apply, map_mul, map_mul, map_inv]
      group
    rw [hτ'f]
    exact Subgroup.mem_comap.mp hg
  have hτ'range : τ'.range = E := by
    apply le_antisymm
    · rintro r ⟨f, rfl⟩
      exact hτ'mem f
    · intro r hr
      have hr' : r ∈ E₁.map e.toMonoidHom := by
        rw [hE₁map]
        exact hr
      obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp hr'
      have hge' : e g = r := hge
      have hcg : (MulAut.conj c) g ∈ (spPlaneTorus m ζ).range := by
        rw [← hc']
        exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
      obtain ⟨f, hf⟩ := hcg
      refine ⟨f, ?_⟩
      show (e c)⁻¹ * e (spPlaneTorus m ζ f) * ((e c)⁻¹)⁻¹ = r
      rw [hf, MulAut.conj_apply, map_mul, map_mul, map_inv, hge']
      group
  have hτ'inj : Function.Injective τ' := by
    let τ₀ : (Fin m → Multiplicative (ZMod p)) →* ↥E := τ'.codRestrict E hτ'mem
    have hτ₀surj : Function.Surjective τ₀ := by
      intro r
      have hr : (r : LargeEvenProj (LargeEvenSpGroup K m)) ∈ τ'.range := by
        rw [hτ'range]
        exact r.2
      obtain ⟨f, hf⟩ := hr
      exact ⟨f, Subtype.ext hf⟩
    have hcardV : Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m :=
      FrameBs.card_zmodFrame p m
    have hcardE' : Nat.card (Fin m → Multiplicative (ZMod p)) ≤ Nat.card ↥E := by
      rw [hcardV, hcardE]
      exact hrankA
    have hτ₀inj := sympMinus_injective_of_surjective_natCard τ₀ hτ₀surj hcardE'
    intro f g hfg
    exact hτ₀inj (Subtype.ext hfg)
  obtain ⟨σ, hσψ, hσp⟩ := exists_section_of_centerPrime hp hψ hker hcpL
    (fun v : Fin m → Multiplicative (ZMod p) => ReflInner.pow_eq_one_of_zmod v) τ'
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_of_range_comap Λ hΛinj hAΛ τ' hτ'inj
    (fun f => (hE _).mp (hτ'mem f)) fun r hr => hτ'range.ge ((hE r).mpr hr)
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f => by
    rw [hΘ f, ← hΛn (σ f), hσψ f]
  have hψσ : ∀ f, ψ₀ (σ f) = x * LargeEvenProjMk (LargeEvenSpGroup K m)
      (spPlaneTorus m ζ f) * x⁻¹ := fun f => by
    rw [hσψ f]
    rfl
  refine ⟨ζ, x, σ, Θ, hζinj, hζW, hψσ, hσp, hΘσ, fun n hn => ?_⟩
  refine ggTorusWeylElt_of_section hker σ hσp (fun a ha => ?_) fun v => ?_
  · obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    exact ⟨f, by rw [← hΘσ f, hf]⟩
  · obtain ⟨f', hf'⟩ := exists_torus_conj_of_normalizer Λ hΛn hE τ' hτ'mem
      (fun r hr => hτ'range.ge hr) hn v
    exact ⟨f', by rw [hσψ v, hσψ f']; exact hf'⟩

theorem ggTBJ_spPlane_model
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1) {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (hψ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hAe : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))), ∀ l : L', φ (ψ₀ l) = ψ₀ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K)
      (σ : (Fin m → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A),
      Function.Injective ζ ∧ (∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      ∃ x : LargeEvenProj (LargeEvenSpGroup K m),
      (∀ f, ψ₀ (σ f) =
        x * LargeEvenProjMk (LargeEvenSpGroup K m) (spPlaneTorus m ζ f) * x⁻¹) ∧
      ∀ (y : MulAut L') (hy : y ∈ A) (J : Subgroup L'), ∃ J₀ : Subgroup (StatedSp m K),
        (CFSG.Open.IsComponentOf J (fixSubgroup y) →
          CFSG.Assembly.IsComponentOf J₀ (Subgroup.centralizer
            ({spPlaneTorus m ζ (Θ.symm ⟨y, hy⟩)} : Set (StatedSp m K)))) ∧
        FrameBs.sectionFrameAut σ J = FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ ∧
        (∀ f : Fin m → Multiplicative (ZMod p),
          (∀ j₀ ∈ J₀, spPlaneTorus m ζ f * j₀ = j₀ * spPlaneTorus m ζ f) ↔
            ∀ j ∈ J, σ f * j = j * σ f) ∧
        (J₀ = ⊤ ↔ J = ⊤) ∧
        (J₀.map (LargeEvenProjMk (LargeEvenSpGroup K m))).map (MulAut.conj x).toMonoidHom =
          J.map ψ₀ := by
  classical
  obtain ⟨ζ, x, σ, Θ, hζinj, hζW, hψσ, hσp, hΘσ, hWeyl⟩ :=
    sympMinus_spPlane_stdModel_aux hp hp2 hpq ψ₀ hψ hker hperf A hAe hAI hsc
  haveI : Fact p.Prime := ⟨hp⟩
  have hcpL : ¬ p ∣ Nat.card (Subgroup.center L') :=
    (ggCenterPrime_sp hp hp2) L' ψ₀ hψ hker hperf
  let e : StatedSp m K ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨AutPSp.proj_injective (n := m) (K := K), QuotientGroup.mk'_surjective _⟩
  have hψσe : ∀ f, ψ₀ (σ f) = x * e (spPlaneTorus m ζ f) * x⁻¹ :=
    fun f => (hψσ f).trans rfl
  refine ⟨ζ, σ, Θ, hζinj, hζW, hΘσ, hWeyl, x, hψσ, fun y hy J => ?_⟩
  let f₀ : Fin m → Multiplicative (ZMod p) := Θ.symm ⟨y, hy⟩
  let S : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) :=
    (J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom
  let J₀ : Subgroup (StatedSp m K) := S.comap e.toMonoidHom
  have hmap : J₀.map e.toMonoidHom = S :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective S
  refine ⟨J₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro hJ
    have hy_eq : y = MulAut.conj (σ f₀) := by
      have h := hΘσ f₀
      rw [show Θ f₀ = ⟨y, hy⟩ from MulEquiv.apply_symm_apply Θ _] at h
      exact h
    have hfix : fixSubgroup y = Subgroup.centralizer ({σ f₀} : Set L') := by
      rw [hy_eq]
      exact ggTBJ_fixSubgroup_conj (σ f₀)
    have hJcent : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')) := by
      rw [hfix] at hJ
      exact hJ
    have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (σ f₀))) := by
      rw [ggTBJ_fixSubgroup_conj]
      exact hJcent
    have hJgg : CFSG.Assembly.IsComponentOf J (ggFix (MulAut.conj (σ f₀))) :=
      (isComponentOf_iff_open).mpr hJ'
    have hc : ∀ l : L', MulAut.conj (ψ₀ (σ f₀)) (ψ₀ l) = ψ₀ (MulAut.conj (σ f₀) l) := by
      intro l
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hSfix : CFSG.Assembly.IsComponentOf (J.map ψ₀)
        (fixSubgroup (MulAut.conj (ψ₀ (σ f₀)))) :=
      USixTwo.isComponentOf_map_fix hψ hker hc hJgg
    have hScent : CFSG.Assembly.IsComponentOf (J.map ψ₀)
        (Subgroup.centralizer ({ψ₀ (σ f₀)} :
          Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
      have h := hSfix
      rw [ggTBJ_fixSubgroup_conj] at h
      exact h
    have hSx : CFSG.Assembly.IsComponentOf S
        (Subgroup.centralizer ({e (spPlaneTorus m ζ f₀)} :
          Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
      have hcent : CFSG.Assembly.IsComponentOf (J.map ψ₀)
          (Subgroup.centralizer ({x * e (spPlaneTorus m ζ f₀) * x⁻¹} :
            Set (LargeEvenProj (LargeEvenSpGroup K m)))) := by
        rwa [hψσe f₀] at hScent
      have h := isComponentOf_map_of_injective (MulAut.conj x⁻¹).toMonoidHom
        (MulAut.conj x⁻¹).injective hcent
      rw [sympMinus_map_conj_centralizer x (e (spPlaneTorus m ζ f₀))] at h
      exact h
    have hJ₀c : CFSG.Assembly.IsComponentOf J₀
        (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))) := by
      apply (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff e.injective).mp
      change CFSG.Assembly.IsComponentOf (J₀.map e.toMonoidHom)
        ((Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))).map
          e.toMonoidHom)
      rw [hmap, sympMinus_map_centralizer_singleton_mulEquiv e (spPlaneTorus m ζ f₀)]
      exact hSx
    exact hJ₀c
  · apply le_antisymm
    · rintro τ ⟨n, hn, hτ⟩
      let j₀ : StatedSp m K := e.symm (x⁻¹ * ψ₀ n * x)
      have hj₀ : j₀ ∈ J₀ := by
        change e j₀ ∈ S
        refine Subgroup.mem_map.mpr ⟨ψ₀ n, Subgroup.mem_map.mpr ⟨n, hn, rfl⟩, ?_⟩
        change (MulAut.conj x⁻¹) (ψ₀ n) = e j₀
        rw [MulAut.conj_apply, inv_inv]
        exact (e.apply_symm_apply (x⁻¹ * ψ₀ n * x)).symm
      refine ⟨j₀, hj₀, fun f => ?_⟩
      apply e.injective
      show e (j₀ * spPlaneTorus m ζ f * j₀⁻¹) = e (spPlaneTorus m ζ (τ f))
      rw [map_mul, map_mul, map_inv,
        show e j₀ = x⁻¹ * ψ₀ n * x from e.apply_symm_apply _]
      calc (x⁻¹ * ψ₀ n * x) * e (spPlaneTorus m ζ f) * (x⁻¹ * ψ₀ n * x)⁻¹
          = x⁻¹ * (ψ₀ n * (x * e (spPlaneTorus m ζ f) * x⁻¹) * (ψ₀ n)⁻¹) * x := by group
        _ = x⁻¹ * (ψ₀ n * ψ₀ (σ f) * (ψ₀ n)⁻¹) * x := by rw [← hψσe f]
        _ = x⁻¹ * ψ₀ (n * σ f * n⁻¹) * x := by rw [← map_inv, ← map_mul, ← map_mul]
        _ = x⁻¹ * ψ₀ (σ (τ f)) * x := by rw [hτ]
        _ = x⁻¹ * (x * e (spPlaneTorus m ζ (τ f)) * x⁻¹) * x := by rw [hψσe (τ f)]
        _ = e (spPlaneTorus m ζ (τ f)) := by group
    · rintro τ ⟨j₀, hj₀, hτ⟩
      have hj₀S : e j₀ ∈ S := hj₀
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hj₀S
      obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.mp hu
      have hue' : (MulAut.conj x⁻¹) u = e j₀ := hue
      refine ⟨n, hn, fun f => ?_⟩
      apply eq_of_lift_pow_eq_one hp hker hcpL
      · have hconje : (x⁻¹ * ψ₀ n * x) * e (spPlaneTorus m ζ f) *
            (x⁻¹ * ψ₀ n * x)⁻¹ = e (spPlaneTorus m ζ (τ f)) := by
          have h := congrArg e (hτ f)
          rw [map_mul, map_mul, map_inv, ← hue', MulAut.conj_apply, inv_inv, ← hnu] at h
          exact h
        calc ψ₀ (n * σ f * n⁻¹)
            = ψ₀ n * ψ₀ (σ f) * (ψ₀ n)⁻¹ := by rw [map_mul, map_mul, map_inv]
          _ = ψ₀ n * (x * e (spPlaneTorus m ζ f) * x⁻¹) * (ψ₀ n)⁻¹ := by rw [hψσe f]
          _ = x * ((x⁻¹ * ψ₀ n * x) * e (spPlaneTorus m ζ f) *
                (x⁻¹ * ψ₀ n * x)⁻¹) * x⁻¹ := by group
          _ = x * e (spPlaneTorus m ζ (τ f)) * x⁻¹ := by rw [hconje]
          _ = ψ₀ (σ (τ f)) := (hψσe (τ f)).symm
      · rw [conj_pow, hσp f]
        group
      · exact hσp (τ f)
  · intro f
    constructor
    · intro hcomm j hj
      let j₀ : StatedSp m K := e.symm (x⁻¹ * ψ₀ j * x)
      have hj₀ : j₀ ∈ J₀ := by
        change e j₀ ∈ S
        refine Subgroup.mem_map.mpr ⟨ψ₀ j, Subgroup.mem_map.mpr ⟨j, hj, rfl⟩, ?_⟩
        change (MulAut.conj x⁻¹) (ψ₀ j) = e j₀
        rw [MulAut.conj_apply, inv_inv]
        exact (e.apply_symm_apply (x⁻¹ * ψ₀ j * x)).symm
      have h0 := hcomm j₀ hj₀
      have h0e : e (spPlaneTorus m ζ f) * (x⁻¹ * ψ₀ j * x) =
          (x⁻¹ * ψ₀ j * x) * e (spPlaneTorus m ζ f) := by
        have h := congrArg e h0
        rwa [map_mul, map_mul, show e j₀ = x⁻¹ * ψ₀ j * x from e.apply_symm_apply _] at h
      have hψcomm : ψ₀ (σ f) * ψ₀ j = ψ₀ j * ψ₀ (σ f) := by
        calc ψ₀ (σ f) * ψ₀ j
            = x * (e (spPlaneTorus m ζ f) * (x⁻¹ * ψ₀ j * x)) * x⁻¹ := by
              rw [hψσe f]; group
          _ = x * ((x⁻¹ * ψ₀ j * x) * e (spPlaneTorus m ζ f)) * x⁻¹ := by rw [h0e]
          _ = ψ₀ j * ψ₀ (σ f) := by rw [hψσe f]; group
      set z := σ f * j * (σ f)⁻¹ * j⁻¹ with hz
      have hzk : z ∈ ψ₀.ker := by
        rw [MonoidHom.mem_ker, hz]
        simp only [map_mul, map_inv]
        rw [hψcomm]
        group
      have hzp : z ^ p = 1 := by
        refine sympMinus_pow_eq_one_of_conj_eq_mul_center (s := σ f) (j := j) (z := z)
          (fun x => (Subgroup.mem_center_iff.mp (hker hzk) x).symm) ?_ (hσp f)
        rw [hz]
        group
      have hz1 : z = 1 := eq_one_of_mem_ker_of_pow hp hker hcpL hzk hzp
      have hcomm' : σ f * j = j * σ f := by
        have h4 : σ f * j * (σ f)⁻¹ * j⁻¹ = 1 := by rw [← hz, hz1]
        calc σ f * j = (σ f * j * (σ f)⁻¹ * j⁻¹) * (j * σ f) := by group
          _ = 1 * (j * σ f) := by rw [h4]
          _ = j * σ f := one_mul _
      exact hcomm'
    · intro hcomm j₀ hj₀
      have hj₀S : e j₀ ∈ S := hj₀
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hj₀S
      obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.mp hu
      have hue' : (MulAut.conj x⁻¹) u = e j₀ := hue
      have hψn : x⁻¹ * ψ₀ n * x = e j₀ := by
        have h1 : (MulAut.conj x⁻¹) u = e j₀ := hue'
        rw [← hnu] at h1
        rw [MulAut.conj_apply, inv_inv] at h1
        exact h1
      apply e.injective
      show e (spPlaneTorus m ζ f * j₀) = e (j₀ * spPlaneTorus m ζ f)
      rw [map_mul, map_mul, ← hψn]
      have hcommψ : ψ₀ (σ f) * ψ₀ n = ψ₀ n * ψ₀ (σ f) := by
        rw [← map_mul, ← map_mul, hcomm n hn]
      calc e (spPlaneTorus m ζ f) * (x⁻¹ * ψ₀ n * x)
          = x⁻¹ * ((x * e (spPlaneTorus m ζ f) * x⁻¹) * ψ₀ n) * x := by group
        _ = x⁻¹ * (ψ₀ (σ f) * ψ₀ n) * x := by rw [← hψσe f]
        _ = x⁻¹ * (ψ₀ n * ψ₀ (σ f)) * x := by rw [hcommψ]
        _ = (x⁻¹ * ψ₀ n * x) * e (spPlaneTorus m ζ f) := by rw [hψσe f]; group
  · constructor
    · intro hJ₀
      have hS : S = ⊤ := by
        rw [← hmap, hJ₀]
        exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
      have hJψ : J.map ψ₀ = ⊤ := by
        rw [eq_top_iff]
        intro r _
        have hr : (MulAut.conj x⁻¹) r ∈ S := by
          rw [hS]
          exact Subgroup.mem_top _
        obtain ⟨s, hs, hsr⟩ := Subgroup.mem_map.mp hr
        have hsr' : (MulAut.conj x⁻¹) s = (MulAut.conj x⁻¹) r := hsr
        rwa [show s = r from (MulAut.conj x⁻¹).injective hsr'] at hs
      have hcomm_le : commutator L' ≤ J := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        obtain ⟨ja, hja, hjae⟩ : ∃ j ∈ J, ψ₀ j = ψ₀ a :=
          Subgroup.mem_map.mp (by rw [hJψ]; exact Subgroup.mem_top _)
        obtain ⟨jb, hjb, hjbe⟩ : ∃ j ∈ J, ψ₀ j = ψ₀ b :=
          Subgroup.mem_map.mp (by rw [hJψ]; exact Subgroup.mem_top _)
        have hza : ja⁻¹ * a ∈ ψ₀.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hjae]
          simp
        have hzb : jb⁻¹ * b ∈ ψ₀.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hjbe]
          simp
        have haeq : a = ja * (ja⁻¹ * a) := by group
        have hbeq : b = jb * (jb⁻¹ * b) := by group
        have heq : ⁅a, b⁆ = ⁅ja, jb⁆ := by
          rw [haeq, hbeq]
          rw [sympMinus_commutatorElement_mul_right_central (hker hzb)]
          rw [sympMinus_commutatorElement_mul_left_of_commute (u := ja) (v := ja⁻¹ * a) (w := jb)
            (Subgroup.mem_center_iff.mp (hker hza) jb).symm]
        rw [heq, commutatorElement_def]
        exact J.mul_mem (J.mul_mem (J.mul_mem hja hjb) (J.inv_mem hja)) (J.inv_mem hjb)
      rw [hperf] at hcomm_le
      exact top_unique hcomm_le
    · intro hJ
      change ((J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom).comap e.toMonoidHom = ⊤
      rw [hJ, Subgroup.map_top_of_surjective ψ₀ hψ]
      rw [Subgroup.map_top_of_surjective _ (MulAut.conj x⁻¹).surjective]
      rw [Subgroup.comap_top]
  · change (J₀.map e.toMonoidHom).map (MulAut.conj x).toMonoidHom = J.map ψ₀
    rw [hmap]
    change ((J.map ψ₀).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      J.map ψ₀
    rw [Subgroup.map_map]
    have hid : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext r
      simp [MulAut.conj_apply]
    rw [hid, Subgroup.map_id]

end SympMinus

end CFSG.StandardType

end
