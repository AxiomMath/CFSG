module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_markedWeyl_ggAutomizer {τ : Tag} {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {G : Type} [Group G] (E : Subgroup G)
    (ι : Multiplicative (Fin τ.rank → ZMod p) →* G)
    (hι : Function.Injective ι) (hrange : ι.range = E)
    (n : Fin τ.rank → G)
    (hn : ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p),
      n i * ι (Multiplicative.ofAdd s) * (n i)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s)))
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set G), ∃ v : WeylGroup τ,
      ∀ s : Fin τ.rank → ZMod p,
        g * ι (Multiplicative.ofAdd s) * g⁻¹ =
          ι (Multiplicative.ofAdd (TableBExc.torusAct τ p v s))) :
    ∃ hnN : ∀ i : Fin τ.rank, n i ∈ Subgroup.normalizer (E : Set G),
      ggAutomizer (⊤ : Subgroup G) E =
          Subgroup.closure (Set.range fun i => ggConjAut E (hnN i)) ∧
        ∃ e : WeylGroup τ ≃* ↥(ggAutomizer (⊤ : Subgroup G) E),
          ∀ i : Fin τ.rank,
            (e (simple τ i) : MulAut ↥E) = ggConjAut E (hnN i) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hp
  let V := Multiplicative (Fin τ.rank → ZMod p)
  let eT : V ≃* ↥E :=
    (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  have heT_apply : ∀ s : Fin τ.rank → ZMod p,
      ((eT (Multiplicative.ofAdd s) : ↥E) : G) = ι (Multiplicative.ofAdd s) := by
    intro s
    change (((MulEquiv.subgroupCongr hrange)
      (MonoidHom.ofInjective hι (Multiplicative.ofAdd s)) : ↥E) : G) = _
    rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  let ρ : WeylGroup τ →* MulAut ↥E :=
    (MulAut.congr eT).toMonoidHom.comp (ExcWeylOuter.torusMulAut τ p)
  have hcongr_apply : ∀ (f : MulAut V) (b : ↥E),
      ((MulAut.congr eT f) b : ↥E) = eT (f (eT.symm b)) := fun f b => rfl
  have hρ_apply : ∀ (v : WeylGroup τ) (s : Fin τ.rank → ZMod p),
      ((ρ v (eT (Multiplicative.ofAdd s)) : ↥E) : G) =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p v s)) := by
    intro v s
    change ((MulAut.congr eT (ExcWeylOuter.torusMulAut τ p v)
      (eT (Multiplicative.ofAdd s)) : ↥E) : G) = _
    rw [hcongr_apply, MulEquiv.symm_apply_apply,
      ExcWeylOuter.torusMulAut_apply, heT_apply]
  have hρ_inj : Function.Injective ρ := by
    intro v w hvw
    have h' : ExcWeylOuter.torusMulAut τ p v = ExcWeylOuter.torusMulAut τ p w := by
      apply (MulAut.congr eT).injective
      simpa only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hvw
    exact ExcWeylOuter.torusMulAut_injective (τ := τ) (p := p) hp2 h'
  have hsurj : ∀ i : Fin τ.rank,
      Function.Surjective (TableBExc.torusAct τ p (simple τ i)) := by
    intro i t
    obtain ⟨v, hv⟩ :=
      (ExcWeylOuter.torusMulAut (τ := τ) (p := p) (simple τ i)).surjective
        (Multiplicative.ofAdd t)
    refine ⟨Multiplicative.toAdd v, ?_⟩
    have h := congrArg Multiplicative.toAdd hv
    rw [← ofAdd_toAdd v, ExcWeylOuter.torusMulAut_apply] at h
    simpa using h
  have hnN : ∀ i : Fin τ.rank, n i ∈ Subgroup.normalizer (E : Set G) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : x ∈ ι.range := hrange ▸ hx
      obtain ⟨s, rfl⟩ := hx'
      rw [← ofAdd_toAdd s, hn i (Multiplicative.toAdd s)]
      exact hrange ▸ MonoidHom.mem_range.mpr
        ⟨Multiplicative.ofAdd
          (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s)), rfl⟩
    · intro hx
      have hx' : n i * x * (n i)⁻¹ ∈ ι.range := hrange ▸ hx
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hx'
      obtain ⟨s, hs⟩ := hsurj i (Multiplicative.toAdd t)
      have hιs : ι (Multiplicative.ofAdd s) = x := by
        have h := hn i s
        rw [hs, ofAdd_toAdd, ht] at h
        calc ι (Multiplicative.ofAdd s)
            = (n i)⁻¹ * (n i * ι (Multiplicative.ofAdd s) * (n i)⁻¹) * (n i) := by
              group
          _ = (n i)⁻¹ * (n i * x * (n i)⁻¹) * (n i) := by rw [h]
          _ = x := by group
      exact hrange ▸ MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd s, hιs⟩
  have hρ_simple : ∀ i : Fin τ.rank, ρ (simple τ i) = ggConjAut E (hnN i) := by
    intro i
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    set s : Fin τ.rank → ZMod p := Multiplicative.toAdd (eT.symm b) with hs
    have hb : eT (Multiplicative.ofAdd s) = b := by
      rw [hs, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    rw [← hb, hρ_apply, ggConjAut_apply, heT_apply, hn i s]
  have hAuto_le : ggAutomizer (⊤ : Subgroup G) E ≤ ρ.range := by
    rw [ggAutomizer_eq]
    intro φ hφ
    obtain ⟨g, -, hg, hφg⟩ := hφ
    obtain ⟨v, hv⟩ := hN g hg
    refine ⟨v, ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    set s : Fin τ.rank → ZMod p := Multiplicative.toAdd (eT.symm b) with hs
    have hb : eT (Multiplicative.ofAdd s) = b := by
      rw [hs, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    rw [← hb, hρ_apply, hφg, heT_apply, hv]
  have hgens : ρ.range = Subgroup.closure (Set.range fun i => ρ (simple τ i)) := by
    rw [MonoidHom.range_eq_map, ← (coxeterSystem τ).subgroup_closure_range_simple,
      MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    ext x
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨simple τ i, ⟨i, rfl⟩, rfl⟩
  have hρrange_le : ρ.range ≤ ggAutomizer (⊤ : Subgroup G) E := by
    rw [hgens]
    refine (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr ?_)
    intro i
    rw [hρ_simple i]
    exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top (n i)) (hnN i)
  have hρrange : ρ.range = ggAutomizer (⊤ : Subgroup G) E :=
    le_antisymm hρrange_le hAuto_le
  have hclosure : ggAutomizer (⊤ : Subgroup G) E =
      Subgroup.closure (Set.range fun i => ggConjAut E (hnN i)) := by
    rw [← hρrange, hgens]
    rw [show (fun i => ρ (simple τ i)) = (fun i => ggConjAut E (hnN i)) from
      funext hρ_simple]
  refine ⟨hnN, hclosure, ?_⟩
  refine ⟨(MonoidHom.ofInjective hρ_inj).trans (MulEquiv.subgroupCongr hρrange), ?_⟩
  intro i
  simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]
  exact hρ_simple i


theorem markedWeyl_of_eq {N : ℕ} {M M' : CoxeterMatrix (Fin N)} (hM : M = M')
    {G : Type} [Group G] (E : Subgroup G) (n : Fin N → G)
    (hn : ∀ i, n i ∈ Subgroup.normalizer (E : Set G))
    (ε' : M'.Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) E))
    (hε' : ∀ i, (ε' (M'.simple i) : MulAut ↥E) = ggConjAut E (hn i)) :
    ∃ ε : M.Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) E),
      ∀ i, (ε (M.simple i) : MulAut ↥E) = ggConjAut E (hn i) := by
  subst M'
  exact ⟨ε', hε'⟩

theorem markedWeyl_apply {ι : Type} {M : CoxeterMatrix ι} {G : Type} [Group G]
    {H : Subgroup G} (E : Subgroup G) (ν : M.Group →* G)
    (ε : M.Group ≃* ↥(ggAutomizer H E))
    (hn : ∀ i, ν (M.simple i) ∈ Subgroup.normalizer (E : Set G))
    (hε : ∀ i, (ε (M.simple i) : MulAut ↥E) = ggConjAut E (hn i)) :
    ∀ (w : M.Group) (a : E), ((ε w : MulAut ↥E) a : G) = ν w * (a : G) * (ν w)⁻¹ := by
  intro w
  induction w using M.toCoxeterSystem.simple_induction_left with
  | one =>
      intro a
      simp
  | mul_simple_left w i ih =>
      intro a
      rw [CoxeterMatrix.toCoxeterSystem_simple]
      calc
        ((ε (M.simple i * w) : MulAut ↥E) a : G) =
            (ggConjAut E (hn i) ((ε w : MulAut ↥E) a) : G) := by
          rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, hε i]
        _ = ν (M.simple i) * ((ε w : MulAut ↥E) a : G) * (ν (M.simple i))⁻¹ :=
          ggConjAut_apply E (hn i) _
        _ = ν (M.simple i) * (ν w * (a : G) * (ν w)⁻¹) * (ν (M.simple i))⁻¹ := by rw [ih]
        _ = ν (M.simple i * w) * (a : G) * (ν (M.simple i * w))⁻¹ := by
          rw [map_mul, mul_inv_rev]
          simp only [mul_assoc]

theorem markedWeyl_map {N : ℕ} {M : CoxeterMatrix (Fin N)}
    {G H : Type} [Group G] [Group H] (E : Subgroup G)
    (f : G →* H) (hf : Function.Injective f) {A : Subgroup H} (hA : E.map f = A)
    (n : Fin N → G) (hn : ∀ k, n k ∈ Subgroup.normalizer (E : Set G))
    (eW : M.Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) E))
    (heW : ∀ k, (eW (M.simple k) : MulAut ↥E) = ggConjAut E (hn k)) :
    ∃ hnA : ∀ k, f (n k) ∈ Subgroup.normalizer (A : Set H),
      ∃ eA : M.Group ≃* ↥(ggAutomizer f.range A),
        ∀ k, (eA (M.simple k) : MulAut ↥A) = ggConjAut A (hnA k) := by
  let e : E ≃* A := (E.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hA)
  have hnA : ∀ k, f (n k) ∈ Subgroup.normalizer (A : Set H) := by
    intro k
    rw [← hA]
    exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f (hn k))
  have hAuto : ggAutomizer f.range A =
      (ggAutomizer (⊤ : Subgroup G) E).map (MulAut.congr e).toMonoidHom := by
    have h := F4AutWeyl.ggAutomizer_map_eq hf (⊤ : Subgroup G) E hA
    simpa only [Subgroup.map_top, e] using h
  let eAuto : ↥(ggAutomizer (⊤ : Subgroup G) E) ≃* ↥(ggAutomizer f.range A) :=
    ((ggAutomizer (⊤ : Subgroup G) E).equivMapOfInjective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective).trans (MulEquiv.subgroupCongr hAuto.symm)
  refine ⟨hnA, eW.trans eAuto, fun k => ?_⟩
  change (eAuto (eW (M.simple k)) : MulAut ↥A) = ggConjAut A (hnA k)
  have heAuto : ∀ x : ggAutomizer (⊤ : Subgroup G) E,
      (eAuto x : MulAut ↥A) = MulAut.congr e x := fun _ => rfl
  rw [heAuto, heW]
  exact ggConjAut_map_congr f hf hA (hn k) (hnA k) rfl

theorem markedWeyl_innerImage {N : ℕ} {M : CoxeterMatrix (Fin N)}
    {G : Type} [Group G] (E : Subgroup G)
    (hj : Function.Injective (MulAut.conj : G →* MulAut G))
    (n : Fin N → G) (hn : ∀ k, n k ∈ Subgroup.normalizer (E : Set G))
    (eW : M.Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) E))
    (heW : ∀ k, (eW (M.simple k) : MulAut ↥E) = ggConjAut E (hn k)) :
    ∃ hnA : ∀ k, MulAut.conj (n k) ∈
        Subgroup.normalizer ((E.map (MulAut.conj : G →* MulAut G)) : Set (MulAut G)),
      ∃ eA : M.Group ≃*
          ↥(ggAutomizer (MulAut.conj : G →* MulAut G).range (E.map (MulAut.conj : G →* MulAut G))),
        ∀ k, (eA (M.simple k) : MulAut ↥(E.map (MulAut.conj : G →* MulAut G))) =
          ggConjAut (E.map (MulAut.conj : G →* MulAut G)) (hnA k) :=
  markedWeyl_map E MulAut.conj hj rfl n hn eW heW

theorem exists_markedWeyl_innerHom {τ : Tag} {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {G : Type} [Group G] (E : Subgroup G)
    (hj : Function.Injective (MulAut.conj : G →* MulAut G))
    (ι : Multiplicative (Fin τ.rank → ZMod p) →* G) (hι : Function.Injective ι)
    (hrange : ι.range = E) (n : Fin τ.rank → G)
    (hact : ∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ k) s)))
    (hN : ∀ g ∈ Subgroup.normalizer (E : Set G), ∃ v : WeylGroup τ, ∀ s,
      g * ι (Multiplicative.ofAdd s) * g⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p v s))) :
    ∃ _hnA : ∀ k, MulAut.conj (n k) ∈
        Subgroup.normalizer ((E.map (MulAut.conj : G →* MulAut G)) : Set (MulAut G)),
      ∃ ρ : WeylGroup τ →* MulAut ↥(E.map (MulAut.conj : G →* MulAut G)),
        Function.Injective ρ ∧
        ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range
          (E.map (MulAut.conj : G →* MulAut G)) ∧
        (∀ k (a : ↥(E.map (MulAut.conj : G →* MulAut G))),
          ((ρ (simple τ k) a : ↥(E.map (MulAut.conj : G →* MulAut G))) : MulAut G) =
            MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) := by
  obtain ⟨hnE, -, eW, heW⟩ := exists_markedWeyl_ggAutomizer hp E ι hι hrange n hact hN
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_innerImage E hj n hnE eW heW
  let A := E.map (MulAut.conj : G →* MulAut G)
  let ρ : WeylGroup τ →* MulAut ↥A :=
    (ggAutomizer (MulAut.conj : G →* MulAut G).range A).subtype.comp eA.toMonoidHom
  refine ⟨hnA, ρ, Subtype.val_injective.comp eA.injective, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro hx
      obtain ⟨g, hg⟩ := eA.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  · intro k a
    change (((eA (simple τ k) : MulAut ↥A) a : ↥A) : MulAut G) = _
    have heAk : (eA (simple τ k) : MulAut ↥A) = ggConjAut A (hnA k) := heA k
    rw [heAk, ggConjAut_apply]


end CFSG.StandardType

end
