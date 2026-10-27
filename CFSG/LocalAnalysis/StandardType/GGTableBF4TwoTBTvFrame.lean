module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTvFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp Matrix

namespace TableBF4TwoTB

@[expose] def GGNoTransvectionSCrJ (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      (∃ a ∈ A, a ≠ 1 ∧ ∃ J : Subgroup L', (∀ l ∈ J, a l = l) ∧ ¬ Group.IsSolvable J) →
      ∀ α : Subgroup.normalizer (A : Set (MulAut L')),
        (∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ ((α : MulAut L') l)) →
        ¬ GGIsTransvection p (A.normalizerMonoidHom α)

theorem ggNoTransvectionSCrJ_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGNoTransvectionSCrJ p r R' I') :
    GGNoTransvectionSCrJ p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc hJ α hα
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc hJ α ?_
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]
  · obtain ⟨φ, hφa⟩ := hα
    exact ⟨MulAut.congr e φ, fun l => by simp [MulAut.congr_apply, hφa l]⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_nonsolvable_ggGamma {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ a ∈ (ggGamma L hN).range, a ≠ 1 ∧
      ∃ J' : Subgroup L, (∀ l ∈ J', a l = l) ∧ ¬ Group.IsSolvable J' := by
  classical
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hC.2.1.1
  have hDB : D ≤ B := hC.2.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hC.2.2.1.2.2.1
  have hxD : x ∈ D := hC.2.2.1.2.2.2.1
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hC.2.2.1.2.2.2.2.2.1
  obtain ⟨y, hyD, hyx⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Subgroup.zpowers x := fun y hy => hcon y hy
    have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf x ≤ p := orderOf_le_of_pow_eq_one hp.pos (hBs.2 x hxBs)
    have h3 : p ^ 2 ≤ p := hDcard ▸ h1.trans h2
    nlinarith [hp.two_le]
  have hyBs : y ∈ Bs := hBBs (hDB hyD)
  refine ⟨ggGamma L hN ⟨y, hyBs⟩, ⟨⟨y, hyBs⟩, rfl⟩, ?_, J.subgroupOf L, ?_, ?_⟩
  ·
    rw [Ne, ggGamma_eq_one_iff]
    intro hyC
    apply hyx
    rw [← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨hyBs, hyC⟩
  ·
    intro l hl
    have hlJ : (l : G) ∈ J := hl
    have hlC : (l : G) ∈ Subgroup.centralizer (D : Set G) := hJcomp.1 hlJ |>.2
    have hcomm : y * (l : G) = (l : G) * y := Subgroup.mem_centralizer_iff.mp hlC y hyD
    apply Subtype.ext
    rw [ggGamma_coe]
    change y * (l : G) * y⁻¹ = l
    rw [hcomm]
    group
  ·
    intro hsol
    have hJL : J ≤ L := hJcomp.1.trans inf_le_left
    haveI : Group.IsSolvable ↥(J.subgroupOf L) := hsol
    haveI : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hJL).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hJL).symm.injective
    haveI hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJcomp.2.2.1
    haveI : Nontrivial ↥J := by
      haveI := hJcomp.2.2.2
      by_contra hno
      rw [not_nontrivial_iff_subsingleton] at hno
      haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) :=
        (QuotientGroup.mk_surjective :
          Function.Surjective (QuotientGroup.mk : ↥J → ↥J ⧸ Subgroup.center ↥J)).subsingleton
      exact not_subsingleton (↥J ⧸ Subgroup.center ↥J) ‹_›
    exact Group.IsPerfect.not_isSolvable ↥J ‹_›

theorem mem_zpowers_of_noTransvectionSCrJ {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (htv : GGNoTransvectionSCrJ p r R I)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφt : GGIsTransvection p φ) (b : ↥Bs) : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  classical
  by_contra hb0
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hC.2.1.2.2.2
  obtain ⟨g, hgx, -, hφg⟩ := hφ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgx
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hC hL θ hN hlift
  set α : MulAut L := L.normalizerMonoidHom ⟨g, hgL⟩ with hα
  have hgc : ∀ c : Bs, g * (c : G) * g⁻¹ ∈ Bs := fun c => by rw [← hφg c]; exact (φ c).2
  have hconj : ∀ c : Bs, α * γ c * α⁻¹ = γ (φ c) := by
    intro c
    have h1 := normalizerMonoidHom_mul_ggGamma L hN ⟨g, hgL⟩ c (hgc c)
    rw [hα, h1]
    congr 1
    exact Subtype.ext (hφg c).symm
  have hNa : α ∈ Subgroup.normalizer ((γ.range : Subgroup (MulAut L)) : Set (MulAut L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨φ c, (hconj c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨φ.symm c, ?_⟩
      have h1 := hconj (φ.symm c)
      rw [MulEquiv.apply_symm_apply, hc] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  refine htv L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI
    hr h3 (ggTorusSelfCent_ggGamma hN hSC) (exists_fixed_nonsolvable_ggGamma hC hN) ⟨α, hNa⟩
    ⟨ggLAut L θ ⟨g, hgL⟩, fun l => by rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]⟩ ?_
  have hkerγ : γ.rangeRestrict.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    rw [MonoidHom.ker_rangeRestrict]
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hγ, ggGamma_eq_one_iff,
      ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  refine isTransvection_of_center_ne hp (fun c c' => Subtype.ext (IsElemAbelian.comm hBs c.2
    c'.2)) γ.rangeRestrict γ.rangeRestrict_surjective ?_ hφt ?_ ?_ (b := b) ?_
  · rw [hkerγ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1]
  · intro c hc
    rw [hkerγ, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    rw [hφg c, ← hk, (Commute.zpow_right hgx' k).eq, mul_inv_cancel_right]
  · intro c
    exact Subtype.ext (hconj c)
  · intro h1
    apply hb0
    have h2 : b⁻¹ * φ b ∈ γ.rangeRestrict.ker := h1
    rw [hkerγ, Subgroup.mem_subgroupOf] at h2
    exact h2

end Config

theorem ggLTransvectionCenterInputOn_of_labelsSCrJ' (ha₀ : GGLNoncyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCrJ p r R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionSCrJ hC (ha₀ G p B x L hC.1) hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift htvt hφ htv b

theorem exists_mem_centralizer_nonsolvable {R L' : Type} [Group R] [Group L'] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') (A : Subgroup (MulAut L')) (χ : A →* R)
    (hχ : ∀ a : A, ∀ l : L', ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹)
    (hχinj : Function.Injective χ)
    (hJ : ∃ a ∈ A, a ≠ 1 ∧ ∃ J : Subgroup L', (∀ l ∈ J, a l = l) ∧ ¬ Group.IsSolvable J) :
    ∃ e ∈ χ.range, e ≠ 1 ∧ ¬ Group.IsSolvable (Subgroup.centralizer ({e} : Set R)) := by
  obtain ⟨a₀, ha₀A, ha₀1, J₀, hJ₀fix, hJ₀ns⟩ := hJ
  refine ⟨χ ⟨a₀, ha₀A⟩, ⟨⟨a₀, ha₀A⟩, rfl⟩, fun h1 => ha₀1 ?_, fun hsol => hJ₀ns ?_⟩
  · exact congrArg Subtype.val (hχinj (h1.trans (map_one χ).symm))
  · have hle : J₀.map ψ ≤ Subgroup.centralizer ({χ ⟨a₀, ha₀A⟩} : Set R) := by
      rintro _ ⟨l, hl, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hχ ⟨a₀, ha₀A⟩ l
      rw [hJ₀fix l hl] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
    haveI : Group.IsSolvable ↥(J₀.map ψ) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    let g : J₀ →* ↥(J₀.map ψ) :=
      ((ψ.comp J₀.subtype).codRestrict (J₀.map ψ) fun j => ⟨j, j.2, rfl⟩)
    refine Group.isSolvable_of_ker_le_range (Subgroup.center J₀).subtype g ?_
    intro j hj
    have hjψ : ψ j = 1 := congrArg Subtype.val hj
    rw [MonoidHom.mem_range]
    refine ⟨⟨j, ?_⟩, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hjψ)) k)

theorem not_isTransvection_of_frameTorus_inner {n r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime 3 R) {t : Multiplicative (Fin n → ZMod 3) →* R}
    (ht : Function.Injective t)
    (hT : ∀ E : Subgroup R, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      (∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
      (∃ e ∈ E, e ≠ 1 ∧ ¬ Group.IsSolvable (Subgroup.centralizer ({e} : Set R))) →
        ∃ c : R, E = t.range.map (MulAut.conj c).toMonoidHom)
    (hK : ∀ g : R, (∀ x ∈ t.range, g * x * g⁻¹ ∈ t.range) →
      ∃ M : (Fin n → ZMod 3) →+ (Fin n → ZMod 3),
        (∀ v, g * t (Multiplicative.ofAdd v) * g⁻¹ = t (Multiplicative.ofAdd (M v))) ∧
          ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hr : 3 ^ r ≤ Nat.card A)
    (hsc : GGTorusSelfCent 3 A)
    (hJ : ∃ a ∈ A, a ≠ 1 ∧ ∃ J : Subgroup L', (∀ l ∈ J, a l = l) ∧ ¬ Group.IsSolvable J)
    (α : Subgroup.normalizer (A : Set (MulAut L')))
    (hα : ∃ g : R, ∀ l : L', ψ ((α : MulAut L') l) = g * ψ l * g⁻¹) :
    ¬ GGIsTransvection 3 (A.normalizerMonoidHom α) := by
  classical
  have := Fact.mk Nat.prime_three
  intro htv
  obtain ⟨g₀, hg₀⟩ := hα
  set φ : MulAut R := MulAut.conj g₀ with hφdef
  have hφ : ∀ l : L', φ (ψ l) = ψ ((α : MulAut L') l) := fun l => by
    rw [hφdef, MulAut.conj_apply, hg₀ l]
  have hex : ∀ a : A, ∃ g : R, ∀ l : L', ψ ((a : MulAut L') l) = g * ψ l * g⁻¹ := by
    intro a
    obtain ⟨φa, hφaI, hφa⟩ := hAI a a.2
    obtain ⟨g, rfl⟩ := hI hφaI
    exact ⟨g, fun l => (hφa l).symm⟩
  have huniq : ∀ (a : MulAut L') (g g' : R), (∀ l, ψ (a l) = g * ψ l * g⁻¹) →
      (∀ l, ψ (a l) = g' * ψ l * g'⁻¹) → g = g' := by
    intro a g g' hg hg'
    have hc : g'⁻¹ * g ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨l, rfl⟩ := hψ x
      have e := (hg l).symm.trans (hg' l)
      calc ψ l * (g'⁻¹ * g) = g'⁻¹ * (g' * ψ l * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * ψ l * g⁻¹) * g := by rw [e]
        _ = (g'⁻¹ * g) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => TableBSymp.eq_conj_of_induces hker hperf (a : MulAut L') t'
      (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  have hEA : IsElemAbelian 3 χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcard : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hKnot3 : ∀ z : L', ψ z = 1 → z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    by_contra hne
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hne
    have hzc : z ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hz)
    have h1 : orderOf z ∣ Nat.card (Subgroup.center L') := Subgroup.orderOf_dvd_natCard _ hzc
    rw [hord] at h1
    exact hcp L' ψ hψ hker hperf h1
  have hSCE : ∀ g : R, g ^ 3 = 1 → (∀ e ∈ χ.range, g * e = e * g) → g ∈ χ.range := by
    intro g hg3 hgc
    obtain ⟨n, hn⟩ := hψ g
    set N := Nat.card ψ.ker with hNdef
    have hN3 : ¬ 3 ∣ N := by
      intro hdvd
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      have h3z : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have hz3 : (z : L') ^ 3 = 1 := by
        have := congrArg Subtype.val h3z
        simpa using this
      have hz1 : (z : L') ≠ 1 := by
        intro h
        have hz0 : z = 1 := Subtype.ext h
        rw [hz0, orderOf_one] at hz
        norm_num at hz
      exact hz1 (hKnot3 _ (MonoidHom.mem_ker.mp z.2) hz3)
    have hN1 : N % 3 = 1 ∨ N % 3 = 2 := by omega
    have hmod : N ^ 2 % 3 = 1 := by
      rw [sq, Nat.mul_mod]
      rcases hN1 with h | h <;> simp [h]
    have hkN : ∀ k : L', ψ k = 1 → k ^ N = 1 := by
      intro k hk
      have h := pow_card_eq_one' (G := ψ.ker) (x := ⟨k, MonoidHom.mem_ker.mpr hk⟩)
      have h2 := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    set x : L' := n ^ (N ^ 2) with hxdef
    have hxpow : ψ x = g := by
      rw [hxdef, map_pow, hn]
      obtain ⟨q, hq⟩ : ∃ q, N ^ 2 = 3 * q + 1 := ⟨N ^ 2 / 3, by omega⟩
      rw [hq, pow_succ, pow_mul, hg3, one_pow, one_mul]
    have hx3 : x ^ 3 = 1 := by
      have hk0 : n ^ 3 ∈ ψ.ker := MonoidHom.mem_ker.mpr (by rw [map_pow, hn, hg3])
      rw [hxdef, ← pow_mul, mul_comm, pow_mul, sq, pow_mul, hkN _ (MonoidHom.mem_ker.mp hk0),
        one_pow]
    have huniq3 : ∀ y : L', ψ y = g → y ^ 3 = 1 → y = x := by
      intro y hy hy3
      set k := y⁻¹ * x with hkdef
      have hk : ψ k = 1 := by
        rw [hkdef, map_mul, map_inv, hy, hxpow, inv_mul_cancel]
      have hkc : k ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hk)
      have hkcomm : k * y = y * k := (Subgroup.mem_center_iff.mp hkc y).symm
      have hxk : x = y * k := by rw [hkdef]; group
      have hcomm : Commute y x := by
        show y * x = x * y
        rw [hxk, mul_assoc y k y, hkcomm]
      have hk3 : k ^ 3 = 1 := by
        rw [hkdef, Commute.mul_pow hcomm.inv_left, inv_pow, hy3, inv_one, hx3, one_mul]
      have hk1 : k = 1 := hKnot3 k hk hk3
      rw [hkdef] at hk1
      exact inv_mul_eq_one.mp hk1
    have hfix : ∀ a ∈ A, a x = x := by
      intro a ha
      apply huniq3
      · have h1 : ψ (a x) = χ ⟨a, ha⟩ * ψ x * (χ ⟨a, ha⟩)⁻¹ := hχ ⟨a, ha⟩ x
        rw [h1, hxpow]
        have hc := hgc (χ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
        rw [← hc, mul_inv_cancel_right]
      · rw [← map_pow, hx3, map_one]
    have hcA : MulAut.conj x ∈ A := hsc x hfix hx3
    exact ⟨⟨MulAut.conj x, hcA⟩, huniq (MulAut.conj x) _ g (hχ ⟨MulAut.conj x, hcA⟩)
      (fun l => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hxpow])⟩
  have hJE := exists_mem_centralizer_nonsolvable ψ hker A χ hχ hχinj hJ
  obtain ⟨c, hc⟩ := hT χ.range hEA (hcard ▸ hr) hSCE hJE
  set J : Multiplicative (Fin n → ZMod 3) →* R := (MulAut.conj c).toMonoidHom.comp t with hJdef
  have hJmem : ∀ s, J s ∈ χ.range := fun s => by
    rw [hc]
    exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  have hJinj : Function.Injective J := (MulAut.conj c).injective.comp ht
  set e : A ≃* χ.range := MonoidHom.ofInjective hχinj with hedef
  set κ : Multiplicative (Fin n → ZMod 3) →* A :=
    e.symm.toMonoidHom.comp (J.codRestrict χ.range hJmem) with hκdef
  have hκ : ∀ s, χ (κ s) = J s := fun s =>
    MonoidHom.apply_ofInjective_symm hχinj (J.codRestrict χ.range hJmem s)
  have hκinj : Function.Injective κ := fun s s' h => hJinj (by rw [← hκ s, ← hκ s', h])
  have hκsurj : ∀ a : A, ∃ s, κ s = a := by
    intro a
    have ha : χ a ∈ χ.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
    rw [hc] at ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
    refine ⟨s, hχinj ?_⟩
    rw [hκ s]
    exact hxa
  set ι : Multiplicative (Fin n → ZMod 3) →* MulAut L' := A.subtype.comp κ with hιdef
  have hι : Function.Injective ι := fun s s' h => hκinj (Subtype.ext h)
  have hιrange : ι.range = A := by
    ext a
    constructor
    · rintro ⟨s, rfl⟩
      exact (κ s).2
    · intro ha
      obtain ⟨s, hs⟩ := hκsurj ⟨a, ha⟩
      exact ⟨s, congrArg Subtype.val hs⟩
  set αA : MulAut A := A.normalizerMonoidHom α with hαAdef
  have hαAcoe : ∀ b : A, ((αA b : A) : MulAut L') =
      (α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹ := fun b => rfl
  have hαinv : ∀ l, (α : MulAut L') ((α : MulAut L')⁻¹ l) = l := fun l => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hφinv : ∀ l, φ (ψ ((α : MulAut L')⁻¹ l)) = ψ l := fun l => by
    rw [hφ, hαinv]
  have hequiv : ∀ b : A, χ (αA b) = φ (χ b) := by
    intro b
    refine huniq _ _ _ (hχ (αA b)) (fun l => ?_)
    calc ψ (((αA b : A) : MulAut L') l)
        = ψ ((α : MulAut L') (((b : A) : MulAut L') ((α : MulAut L')⁻¹ l))) := by
          rw [hαAcoe, MulAut.mul_apply, MulAut.mul_apply]
      _ = φ (ψ (((b : A) : MulAut L') ((α : MulAut L')⁻¹ l))) := (hφ _).symm
      _ = φ (χ b * ψ ((α : MulAut L')⁻¹ l) * (χ b)⁻¹) := by rw [hχ b]
      _ = φ (χ b) * φ (ψ ((α : MulAut L')⁻¹ l)) * (φ (χ b))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = φ (χ b) * ψ l * (φ (χ b))⁻¹ := by rw [hφinv l]
  have hφE : ∀ y ∈ χ.range, φ y ∈ χ.range := by
    intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← hequiv a]
    exact MonoidHom.mem_range.mpr ⟨αA a, rfl⟩
  set g' : R := c⁻¹ * g₀ * c with hg'def
  have hψ'app : ∀ x : R, g' * x * g'⁻¹ = c⁻¹ * φ (c * x * c⁻¹) * c := fun x => by
    rw [hφdef, MulAut.conj_apply, hg'def]
    group
  have hψ'T : ∀ x ∈ t.range, g' * x * g'⁻¹ ∈ t.range := by
    intro x hx
    have h1 : c * x * c⁻¹ ∈ χ.range := by
      rw [hc]
      exact Subgroup.mem_map_of_mem _ hx
    have h2 : φ (c * x * c⁻¹) ∈ χ.range := hφE _ h1
    rw [hc] at h2
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp h2
    have hψz : g' * x * g'⁻¹ = z := by
      rw [hψ'app, ← hzeq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hψz]
    exact hz
  obtain ⟨M, hMψ, hMiso⟩ := hK g' hψ'T
  have hφJ : ∀ s : Fin n → ZMod 3,
      φ (J (Multiplicative.ofAdd s)) = J (Multiplicative.ofAdd (M s)) := by
    intro s
    have h1 := hMψ s
    rw [hψ'app] at h1
    show φ (c * t (Multiplicative.ofAdd s) * c⁻¹) = c * t (Multiplicative.ofAdd (M s)) * c⁻¹
    rw [← h1]
    group
  have hrel : ∀ (b : A) (s : Fin n → ZMod 3), (b : MulAut L') = ι (Multiplicative.ofAdd s) →
      ((αA b : A) : MulAut L') = ι (Multiplicative.ofAdd (M s)) := by
    intro b s hb
    have hbκ : b = κ (Multiplicative.ofAdd s) := Subtype.ext hb
    have hχb : χ b = J (Multiplicative.ofAdd s) := by rw [hbκ, hκ]
    have hχα : χ (αA b) = J (Multiplicative.ofAdd (M s)) := by
      rw [hequiv b, hχb, hφJ]
    have hαAκ : αA b = κ (Multiplicative.ofAdd (M s)) := hχinj (hχα.trans (hκ _).symm)
    show ((αA b : A) : MulAut L') = ((κ (Multiplicative.ofAdd (M s)) : A) : MulAut L')
    rw [hαAκ]
  obtain ⟨hcardfix, hNfix⟩ := NoTvAut.transvection_coords (p := 3) hι hιrange (t := ⇑M) hrel htv
  exact NoTvAut.false_of_isTransvection_similitude (p := 3) (by norm_num) (S := 1)
    Matrix.transpose_one (by simp) M 1 (fun x y => by simp [hMiso x y]) hcardfix hNfix

theorem ggNoTransvectionSCrJ_of_frameTorus {n r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime 3 R)
    (hOut : ∀ φ : MulAut R, φ ^ 2 ∈ Set.range (MulAut.conj : R →* MulAut R))
    {t : Multiplicative (Fin n → ZMod 3) →* R} (ht : Function.Injective t)
    (hT : ∀ E : Subgroup R, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      (∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
      (∃ e ∈ E, e ≠ 1 ∧ ¬ Group.IsSolvable (Subgroup.centralizer ({e} : Set R))) →
        ∃ c : R, E = t.range.map (MulAut.conj c).toMonoidHom)
    (hK : ∀ g : R, (∀ x ∈ t.range, g * x * g⁻¹ ∈ t.range) →
      ∃ M : (Fin n → ZMod 3) →+ (Fin n → ZMod 3),
        (∀ v, g * t (Multiplicative.ofAdd v) * g⁻¹ = t (Multiplicative.ofAdd (M v))) ∧
          ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w) :
    GGNoTransvectionSCrJ 3 r R I := by
  have := Fact.mk Nat.prime_three
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc hJ α hα htv
  obtain ⟨φ, hφ⟩ := hα
  obtain ⟨g, hg⟩ := hOut φ
  have htv2 : GGIsTransvection 3 (A.normalizerMonoidHom (α ^ 2)) := by
    rw [map_pow]
    exact NoTvAut.ggIsTransvection_pow_two Nat.prime_three (by norm_num) hA htv
  have hα2 : ((α ^ 2 : Subgroup.normalizer (A : Set (MulAut L'))) : MulAut L') =
      (α : MulAut L') ^ 2 := rfl
  refine not_isTransvection_of_frameTorus_inner hI hZ hcp ht hT hK ψ hψ hker hperf A hA hAI hr hsc
    hJ (α ^ 2) ⟨g, fun l => ?_⟩ htv2
  calc ψ (((α ^ 2 : Subgroup.normalizer (A : Set (MulAut L'))) : MulAut L') l)
      = ψ ((α : MulAut L') ((α : MulAut L') l)) := by rw [hα2, pow_two]; rfl
    _ = φ (ψ ((α : MulAut L') l)) := (hφ _).symm
    _ = φ (φ (ψ l)) := by rw [hφ l]
    _ = (φ ^ 2) (ψ l) := by rw [pow_two]; rfl
    _ = g * ψ l * g⁻¹ := by rw [← hg]; rfl

end TableBF4TwoTB

end CFSG.StandardType

end
