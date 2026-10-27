module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular

public section

namespace CFSG.StandardType

namespace SevOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

section FrameFacts

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

namespace Frame

theorem pow_p (F : Frame Q p A r) (s : Multiplicative (Fin r → ZMod p)) : F.ι s ^ p = 1 := by
  rw [← map_pow]
  have : s ^ p = 1 := by
    apply toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp
  rw [this, map_one]

theorem mem (F : Frame Q p A r) (s : Multiplicative (Fin r → ZMod p)) : F.ι s ∈ A := by
  have h : F.ι s ∈ F.ι.range := ⟨s, rfl⟩
  rwa [F.range] at h

theorem exists_eq (F : Frame Q p A r) {c : V ≃ₗ[K] V} (hc : c ∈ A) :
    ∃ s, F.ι s = c := by
  rw [← F.range] at hc
  exact hc

theorem inf_eq_bot (F : Frame Q p A r) {i j : Fin r} (hij : i ≠ j) : F.U i ⊓ F.U j = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun u hu => F.nondeg j u hu.2 fun v hv => ?_
  rw [QuadraticMap.polar_comm]
  exact F.orth i j hij u hu.1 v hv

theorem iSupIndep_pieces (F : Frame Q p A r) : iSupIndep F.U := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hM
  refine F.nondeg i x hx ?_
  intro y hy
  refine Submodule.iSup_induction (p := fun j => ⨆ (_ : j ≠ i), F.U j)
    (motive := fun z => QuadraticMap.polar Q y z = 0) hM ?_ ?_ ?_
  · intro j z hz
    refine Submodule.iSup_induction (p := fun (_ : j ≠ i) => F.U j)
      (motive := fun z => QuadraticMap.polar Q y z = 0) hz ?_ ?_ ?_
    · intro hj z' hz'
      rw [QuadraticMap.polar_comm]
      exact F.orth j i hj z' hz' y hy
    · simp
    · intro a b ha hb
      rw [QuadraticMap.polar_add_right, ha, hb, add_zero]
  · simp
  · intro a b ha hb
    rw [QuadraticMap.polar_add_right, ha, hb, add_zero]

theorem le_fixedSpace (F : Frame Q p A r) {s : Multiplicative (Fin r → ZMod p)} {k : Fin r}
    (hk : toAdd s k = 0) : F.U k ≤ fixedSpace (F.ι s) := fun u hu =>
  mem_fixedSpace.mpr (F.triv s k hk u hu)

theorem supp_of_fix (F : Frame Q p A r) {s t : Multiplicative (Fin r → ZMod p)}
    (h : ∀ w ∈ fixedSpace (F.ι s), F.ι t w = w) {k : Fin r} (hk : toAdd t k ≠ 0) :
    toAdd s k ≠ 0 := by
  intro hs
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot k)
  exact hu0 (F.fpf t k hk u hu (h u (F.le_fixedSpace hs hu)))

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

omit [Finite K] in
theorem two_le_finrank (F : Frame Q p A r) (i : Fin r) : 2 ≤ finrank K (F.U i) := by
  by_contra h
  have hpos : 0 < finrank K (F.U i) := by
    have : Nontrivial (F.U i) := Submodule.nontrivial_iff_ne_bot.mpr (F.ne_bot i)
    exact Module.finrank_pos
  have h1 : finrank K (F.U i) = 1 := by omega
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot i)
  apply hu0
  refine F.nondeg i u hu fun v hv => ?_
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u, hu⟩ : F.U i)
    (fun h0 => hu0 (congrArg Subtype.val h0))).mp h1 ⟨v, hv⟩
  have hv' : v = c • u := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  rw [hv', QuadraticMap.polar_smul_left, QuadraticMap.polar_self, two_nsmul,
    CharTwo.add_self_eq_zero, smul_zero]

omit [Finite K] [CharP K 2] in
theorem finrank_add_le (F : Frame Q p A r) {i j : Fin r} (hij : i ≠ j) {W : Submodule K V}
    (hi : F.U i ≤ W) (hj : F.U j ≤ W) :
    finrank K (F.U i) + finrank K (F.U j) ≤ finrank K W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (F.U i) (F.U j)
  rw [F.inf_eq_bot hij, finrank_bot, add_zero] at h
  rw [← h]
  exact Submodule.finrank_mono (sup_le hi hj)

omit [Finite K] [CharP K 2] in
theorem finrank_add_add_le (F : Frame Q p A r) {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {W : Submodule K V} (hi : F.U i ≤ W) (hj : F.U j ≤ W) (hk : F.U k ≤ W) :
    finrank K (F.U i) + finrank K (F.U j) + finrank K (F.U k) ≤ finrank K W := by
  have hdisj : (F.U i ⊔ F.U j) ⊓ F.U k = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => F.nondeg k w hw.2 fun v hv => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw.1
    rw [QuadraticMap.polar_add_right, F.orth k i (Ne.symm hik) v hv a ha,
      F.orth k j (Ne.symm hjk) v hv b hb, add_zero]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (F.U i) (F.U j)
  rw [F.inf_eq_bot hij, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F.U i ⊔ F.U j) (F.U k)
  rw [hdisj, finrank_bot, add_zero, h1] at h2
  rw [← h2]
  exact Submodule.finrank_mono (sup_le (sup_le hi hj) hk)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem card_le (F : Frame Q p A r) [Fact p.Prime] {H : Subgroup (V ≃ₗ[K] V)} (hHA : H ≤ A)
    {j j' : Fin r} (hH : ∀ s, F.ι s ∈ H → ∀ i, toAdd s i ≠ 0 → i = j ∨ i = j') :
    Nat.card H ≤ p ^ 2 := by
  classical
  have hex : ∀ c : H, ∃ s, F.ι s = c := fun c => F.exists_eq (hHA c.2)
  choose σ hσ using hex
  let f : H → ZMod p × ZMod p := fun c => (toAdd (σ c) j, toAdd (σ c) j')
  have hf : Function.Injective f := by
    intro c c' hcc
    have h1 : toAdd (σ c) j = toAdd (σ c') j := congrArg Prod.fst hcc
    have h2 : toAdd (σ c) j' = toAdd (σ c') j' := congrArg Prod.snd hcc
    have hs : σ c = σ c' := by
      apply toAdd.injective
      funext i
      by_cases hi : i = j
      · rw [hi, h1]
      by_cases hi' : i = j'
      · rw [hi', h2]
      have hc0 : toAdd (σ c) i = 0 := by
        by_contra h0
        rcases hH (σ c) (by rw [hσ]; exact c.2) i h0 with h | h
        · exact hi h
        · exact hi' h
      have hc0' : toAdd (σ c') i = 0 := by
        by_contra h0
        rcases hH (σ c') (by rw [hσ]; exact c'.2) i h0 with h | h
        · exact hi h
        · exact hi' h
      rw [hc0, hc0']
    apply Subtype.ext
    rw [← hσ c, ← hσ c', hs]
  calc Nat.card H ≤ Nat.card (ZMod p × ZMod p) := Nat.card_le_card_of_injective f hf
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_zmod, sq]

omit [CharP K 2] in
theorem dvd_card_sub_one (F : Frame Q p A r) [hp : Fact p.Prime] (k : Fin r) :
    p ∣ Nat.card (F.U k) - 1 := by
  classical
  have : Finite (F.U k) := Module.finite_of_finite K
  have hmaps : ∀ a : A, ∀ u ∈ F.U k, (a : V ≃ₗ[K] V) u ∈ F.U k := by
    intro a u hu
    obtain ⟨s, hs⟩ := F.exists_eq a.2
    rw [← hs]
    exact F.mapsTo s k u hu
  let act : MulAction A (F.U k) :=
    { smul := fun a u => ⟨(a : V ≃ₗ[K] V) u, hmaps a u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun a b u => Subtype.ext rfl }
  have hApg : IsPGroup p A := fun c => by
    obtain ⟨t, ht⟩ := F.exists_eq c.2
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← ht, F.pow_p, Subgroup.coe_one])⟩
  have hmod := hApg.card_modEq_card_fixedPoints (F.U k)
  have hsingle : toAdd (ofAdd (Pi.single k (1 : ZMod p)) : Multiplicative (Fin r → ZMod p)) k ≠
      0 := by
    rw [toAdd_ofAdd, Pi.single_eq_same]
    exact one_ne_zero
  have hfix : ∀ u : F.U k, u ∈ MulAction.fixedPoints A (F.U k) ↔ u = 0 := by
    intro u
    constructor
    · intro hu
      have h1 : F.ι (ofAdd (Pi.single k 1)) u = u :=
        congrArg Subtype.val (hu ⟨_, F.mem (ofAdd (Pi.single k 1))⟩)
      exact Subtype.ext (F.fpf _ k hsingle u u.2 h1)
    · rintro rfl a
      exact Subtype.ext (map_zero (a : V ≃ₗ[K] V))
  have hone : Nat.card (MulAction.fixedPoints A (F.U k)) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, (hfix 0).mpr rfl⟩, fun u => Subtype.ext ((hfix u.1).mp u.2)⟩
  rw [hone] at hmod
  have hpos : 1 ≤ Nat.card (F.U k) := Nat.card_pos
  exact (Nat.modEq_iff_dvd' hpos).mp hmod.symm

end Frame

end FrameFacts

section Direct

open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [FiniteDimensional K V] in
theorem Frame.oddOrderIsometry (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp2 : p ≠ 2)
    (hp : p.Prime) (hAΩ : A ≤ orthDerived Q) (F : Frame Q p A r)
    (s : Multiplicative (Fin r → ZMod p)) : OddOrderIsometry Q p (F.ι s) := by
  refine ⟨orthDerived_le_orthogonalGroup (hAΩ (F.mem s)), F.pow_p s, ?_,
    fun v hv => hQ.1 v fun w => by simpa using hv w⟩
  rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
  exact one_ne_zero

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_mem_ne_zero_quad {W : Submodule K V} (hW : W ≠ ⊥)
    (hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) :
    ∃ w ∈ W, Q w ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hW
  apply hw0
  have h1 : (⟨w, hw⟩ : W) = 0 := hWnd.1 ⟨w, hw⟩ fun w' => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply,
      QuadraticMap.comp_apply, QuadraticMap.comp_apply, Submodule.subtype_apply,
      Submodule.subtype_apply, Submodule.subtype_apply, Submodule.coe_add,
      hall _ (W.add_mem hw w'.2), hall w hw, hall _ w'.2, sub_zero, sub_zero]
  exact congrArg Subtype.val h1

theorem direct_of_supp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : Frame Q p A r)
    {s : Multiplicative (Fin r → ZMod p)} {j j' : Fin r}
    (hs : ∀ i, toAdd s i ≠ 0 → i = j ∨ i = j') (h3 : 3 ≤ finrank K (fixedSpace (F.ι s)))
    (hns : ¬ SplitFour (Q.comp (fixedSpace (F.ι s)).subtype)) :
    ∃ L₂ : Subgroup (V ≃ₗ[K] V),
      CFSG.Assembly.IsComponentOf L₂ (orthDerived Q ⊓ Subgroup.centralizer {F.ι s}) ∧
      Nat.card (A ⊓ Subgroup.centralizer (L₂ : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set e := F.ι s with he
  have hx : OddOrderIsometry Q p e := F.oddOrderIsometry hQ hp2 hp hAΩ s
  set W := fixedSpace e with hW
  have hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hq := (LayerPDiv.isQuasisimple_commutator_of_not_split hWnd h3 hns).1
  have hL₂q : CFSG.IsQuasisimple ↥(supportedFixedDerived Q e) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm hq
  have hle : supportedFixedDerived Q e ≤ orthDerived Q ⊓ Subgroup.centralizer {e} :=
    le_inf hx.supportedFixedDerived_le_orthDerived
      (supportedFixedDerived_le_isometryCentralizer.trans inf_le_right)
  refine ⟨supportedFixedDerived Q e, ⟨hle, ggSubnormal_of_normal hle fun u hu g hg =>
    hx.conj_mem_supportedFixedDerived (Subgroup.mem_inf.mpr
      ⟨orthDerived_le_orthogonalGroup (Subgroup.mem_inf.mp hu).1, (Subgroup.mem_inf.mp hu).2⟩) hg,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hL₂q⟩,
    F.card_le inf_le_left (j := j) (j' := j') fun t ht i hi => hs i (F.supp_of_fix ?_ hi)⟩
  set c := F.ι t with hc
  have hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup (hAΩ (Subgroup.mem_inf.mp ht).1)
  have hcomm : ∀ g ∈ supportedDerived Q W, ∀ v, c.toAddEquiv (g v) = g (c.toAddEquiv v) := by
    intro g hg v
    rw [hx.supportedDerived_fixedSpace] at hg
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2 g hg
    exact (LinearEquiv.congr_fun h1 v).symm
  have hFQ : ∀ v, Q (c.toAddEquiv v) = 1 * (RingEquiv.refl K) (Q v) := fun v => by
    rw [one_mul, RingEquiv.refl_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hcO v
  have hsing : ∃ x ∈ W, x ≠ 0 ∧ Q x = 0 :=
    CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_charTwo
      (CharTwo.two_eq_zero) h3
  have hM : ElementaryMapsMem Q W := elementaryMapsMem_of_regular hWnd h3 fun _ h4 => by
    intro U hU
    by_contra hall
    push Not at hall
    exact hns ⟨h4, U, hU, hall⟩
  obtain ⟨-, μ, -, hμ⟩ := scalar_restriction_of_commute c.toAddEquiv (RingEquiv.refl K) 1 hFQ
    hcomm hQ hWnd h3 hsing hM fun a v => by simp
  have hWne : W ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h3
    omega
  obtain ⟨w₀, hw₀, hQw₀⟩ := exists_mem_ne_zero_quad hWne hWnd
  have hμ1 : μ = 1 := by
    have h1 : Q (c w₀) = Q w₀ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hcO w₀
    have h2 : c w₀ = μ • w₀ := hμ w₀ hw₀
    rw [h2, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h3' : (μ - 1) ^ 2 * Q w₀ = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h1 + (Q w₀ - μ * Q w₀) * h2'
    rcases mul_eq_zero.mp h3' with h | h
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    · exact absurd h hQw₀
  intro w hw
  have := hμ w hw
  rw [hμ1, one_smul] at this
  exact this

end Direct

end SevOm

end CFSG.StandardType
