module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c11_big_lift_range_inclusion {H K : Subgroup G} (h : H ≤ K) :
    (Subgroup.inclusion h).range = H.subgroupOf K := by
  ext x
  rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, rfl⟩
    exact m.2
  · intro hx
    exact ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩

private theorem s16c11_big_lift_perfect_le_map_derivedSeries {X Y : Type*} [Group X] [Group Y]
    (ψ : X →* Y) {R : Subgroup Y} (hR : R ≤ ψ.range) (hRp : ⁅R, R⁆ = R) (n : ℕ) :
    R ≤ (derivedSeries X n).map ψ := by
  induction n with
  | zero => rwa [derivedSeries_zero, ← MonoidHom.range_eq_map]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, ← hRp]
    exact Subgroup.commutator_mono ih ih

theorem s16c11_le_barSub_centralizer_of_perfect (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4)
    {Q : Subgroup (MulAut (Vtil V₀ V hV))} (hQM : Q ≤ Mbar D.M V₀ V hV) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ barSub V₀ V hV (D.M ⊓ centralizer (V₀ : Set G)) := by
  classical
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let ρ : ↥D.M →* MulAut ↥V₀ :=
    (Subgroup.normalizerMonoidHom V₀).comp
      (Subgroup.inclusion h.pairFacts.le_normalizer₀)
  have hker : ρ.ker = (centralizer (V₀ : Set G)).subgroupOf D.M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (Subgroup.normalizerMonoidHom V₀)
        (Subgroup.inclusion h.pairFacts.le_normalizer₀ m) = 1 ↔
      (m : G) ∈ centralizer (V₀ : Set G)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker V₀,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  haveI hsolPerm : Group.IsSolvable (Equiv.Perm ↥V₀) := Equiv.Perm.isSolvable h4
  haveI hsolAut : Group.IsSolvable (MulAut ↥V₀) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm (M := ↥V₀))
      (fun _ _ hab => MulEquiv.toEquiv_injective hab)
  obtain ⟨k, hk⟩ := (inferInstance : Group.IsSolvable ρ.range).solvable
  have hder_le_ker : derivedSeries ↥D.M k ≤ ρ.ker := by
    have hmap := map_derivedSeries_eq ρ.rangeRestrict_surjective k
    rw [hk] at hmap
    rw [← MonoidHom.ker_rangeRestrict (f := ρ)]
    exact (Subgroup.map_eq_bot_iff (derivedSeries ↥D.M k)).1 hmap
  let πM : ↥D.M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hMS)
  have hπrange : πM.range = Mbar D.M V₀ V hV := by
    change ((actTil V₀ V hV).comp (Subgroup.inclusion hMS)).range = barSub V₀ V hV D.M
    simp only [barSub, MonoidHom.range_comp, s16c11_big_lift_range_inclusion hMS]
  intro q hq
  have hqder : q ∈ (derivedSeries ↥D.M k).map πM :=
    s16c11_big_lift_perfect_le_map_derivedSeries πM (by rw [hπrange]; exact hQM) hQ k hq
  obtain ⟨m, hm, rfl⟩ := hqder
  have hmker : (m : G) ∈ centralizer (V₀ : Set G) := by
    have hm' := hder_le_ker hm
    rwa [hker, Subgroup.mem_subgroupOf] at hm'
  refine (mem_barSub V₀ V hV (D.M ⊓ centralizer (V₀ : Set G)) (πM m)).2
    ⟨⟨(m : G), hMS m.2⟩, ⟨m.2, hmker⟩, ?_⟩
  show actTil V₀ V hV ⟨(m : G), hMS m.2⟩ = πM m
  rw [show πM m = actTil V₀ V hV (Subgroup.inclusion hMS m) from rfl]
  exact congrArg (actTil V₀ V hV)
    (Subtype.ext (Subgroup.coe_inclusion hMS m).symm)

theorem s16c11_exists_pGroup_lift (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {Q : Subgroup (MulAut (Vtil V₀ V hV))}
    (hQM : Q ≤ Mbar D.M V₀ V hV) (hQ : ⁅Q, Q⁆ = Q) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEQ : E ≤ Q) (hE : IsPGroup p ↥E) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup p ↥B ∧ V₀ ≤ centralizer (B : Set G) ∧
      barSub V₀ V hV B = E ∧ (¬ IsCyclic ↥E → ¬ IsCyclic ↥B) := by
  classical
  haveI : Fact p.Prime := Fact.mk hp
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let C : Subgroup G := D.M ⊓ centralizer (V₀ : Set G)
  have hCS : C ≤ stabTil V₀ V := inf_le_left.trans hMS
  have hQC : Q ≤ barSub V₀ V hV C :=
    s16c11_le_barSub_centralizer_of_perfect D hV h h4 hQM hQ
  let Csub : Subgroup ↥(stabTil V₀ V) := C.subgroupOf (stabTil V₀ V)
  let f : ↥Csub →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp Csub.subtype
  have hfrange : f.range = barSub V₀ V hV C := by
    change ((actTil V₀ V hV).comp Csub.subtype).range = barSub V₀ V hV C
    simp only [barSub, Csub, MonoidHom.range_comp, Subgroup.range_subtype]
  have hEf : E ≤ f.range := by
    rw [hfrange]
    exact hEQ.trans hQC
  obtain ⟨P, hPp, hPmap⟩ := exists_pGroup_map_eq f E hE hEf
  let g : ↥Csub →* G := (stabTil V₀ V).subtype.comp Csub.subtype
  let B : Subgroup G := P.map g
  have hBM : B ≤ D.M := by
    change P.map g ≤ D.M
    intro b hb
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hb
    exact x.2.1
  have hBp : IsPGroup p ↥B := by
    change IsPGroup p (P.map g)
    exact hPp.map g
  have hBcent : B ≤ centralizer (V₀ : Set G) := by
    change P.map g ≤ centralizer (V₀ : Set G)
    intro b hb
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hb
    exact x.2.2
  have hV₀B : V₀ ≤ centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hBcent hb) v hv).symm
  have hBsub : B.subgroupOf (stabTil V₀ V) = P.map Csub.subtype := by
    change (P.map g).subgroupOf (stabTil V₀ V) = P.map Csub.subtype
    ext s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hxP, hx⟩
      exact ⟨x, hxP, Subtype.ext hx⟩
    · rintro ⟨x, hxP, rfl⟩
      exact ⟨x, hxP, rfl⟩
  have hbar : barSub V₀ V hV B = E := by
    change (B.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) = E
    rw [hBsub, Subgroup.map_map]
    change P.map f = E
    exact hPmap
  have hnoncyc : ¬ IsCyclic ↥E → ¬ IsCyclic ↥B := by
    intro hEcyc hBcyc
    haveI : IsCyclic ↥B := hBcyc
    have hBS : B ≤ stabTil V₀ V := hBM.trans hMS
    let ψ : ↥B →* MulAut (Vtil V₀ V hV) :=
      (actTil V₀ V hV).comp (Subgroup.inclusion hBS)
    have hψrange : ψ.range = barSub V₀ V hV B := by
      change ((actTil V₀ V hV).comp (Subgroup.inclusion hBS)).range = barSub V₀ V hV B
      simp only [barSub, MonoidHom.range_comp, s16c11_big_lift_range_inclusion hBS]
    let φ : ↥B →* ↥E := ψ.codRestrict E fun b => by
      rw [← hbar, ← hψrange]
      exact MonoidHom.mem_range.2 ⟨b, rfl⟩
    refine hEcyc (isCyclic_of_surjective φ fun e => ?_)
    have he : (e : MulAut (Vtil V₀ V hV)) ∈ ψ.range := by
      rw [hψrange, hbar]
      exact e.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 he
    exact ⟨b, Subtype.ext hb⟩
  exact ⟨B, hBM, hBp, hV₀B, hbar, hnoncyc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
