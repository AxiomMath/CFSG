module

public import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

private lemma inr_mul_inl_eq_iff {E : Type*} [Group E] (a : MulAut E) (e : E) :
    (SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) a *
      SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) e =
     SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) e *
      SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) a) ↔ a e = e := by
  constructor
  · intro h
    have h2 : SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) (a e) =
        SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) e := by
      rw [show SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) (a e) =
          SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) a *
            SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) e *
            (SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) a)⁻¹ by
        simpa using SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut E)) a e]
      rw [h]; group
    exact SemidirectProduct.inl_inj.mp h2
  · intro h
    have h1 : SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) a *
        SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) e =
        SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) (a e) *
        SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) a := by
      ext <;> simp
    rw [h] at h1
    exact h1

private lemma inr_mem_normalizer_inl {E : Type*} [Group E] (c : MulAut E) :
    SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) c ∈
      Subgroup.normalizer (((⊤ : Subgroup E).map
        (SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)))) :
          Set (E ⋊[MonoidHom.id (MulAut E)] MulAut E)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hh
    exact Subgroup.mem_map.mpr ⟨c e, Subgroup.mem_top _, by
      simpa using SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut E)) c e⟩
  · intro hh
    obtain ⟨e, -, he⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨c⁻¹ e, Subgroup.mem_top _, ?_⟩
    calc SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) (c⁻¹ e)
        = (SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) c)⁻¹ *
          SemidirectProduct.inl (φ := MonoidHom.id (MulAut E)) e *
          SemidirectProduct.inr (φ := MonoidHom.id (MulAut E)) c := by
          simpa using SemidirectProduct.inl_aut_inv (φ := MonoidHom.id (MulAut E)) c e
      _ = h := by rw [he]; group

theorem commutator_eq_bot_of_odd_of_fixed_eq {E : Type*} [Group E] [Finite E]
    (hE : IsElemAbelian 2 (⊤ : Subgroup E)) {A Q : Subgroup (MulAut E)}
    (hA : IsElemAbelian 2 A) (hAnc : ¬ IsCyclic A)
    (hAfix : ∀ a ∈ A, a ≠ 1 → ∀ e : E, (∀ b ∈ A, b e = e) ↔ a e = e)
    (hQodd : Odd (Nat.card Q)) (hAQ : A ≤ Subgroup.normalizer (Q : Set (MulAut E))) :
    ⁅Q, A⁆ = ⊥ := by
  classical
  let φ : MulAut E →* MulAut E := MonoidHom.id _
  let Γ := E ⋊[φ] MulAut E
  let ι : E →* Γ := SemidirectProduct.inl (φ := φ)
  let κ : MulAut E →* Γ := SemidirectProduct.inr (φ := φ)
  haveI : Finite Γ :=
    Finite.of_equiv (E × MulAut E) (SemidirectProduct.equivProd (φ := φ)).symm
  have hιinj : Function.Injective ι := SemidirectProduct.inl_injective
  have hκinj : Function.Injective κ := SemidirectProduct.inr_injective
  set E' : Subgroup Γ := (⊤ : Subgroup E).map ι with hE'def
  set A' : Subgroup Γ := A.map κ with hA'def
  set Q' : Subgroup Γ := Q.map κ with hQ'def
  have hE'mem : ∀ e : E, ι e ∈ E' := fun e =>
    Subgroup.mem_map.mpr ⟨e, Subgroup.mem_top e, rfl⟩
  have hA'mem : ∀ a : MulAut E, a ∈ A → κ a ∈ A' := fun a ha =>
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hE' : IsElemAbelian 2 E' := by
    rw [hE'def]; exact hE.map ι
  have hA' : IsElemAbelian 2 A' := by
    rw [hA'def]; exact hA.map κ
  have hAnc' : ¬ IsCyclic A' := by
    rw [hA'def]
    intro hcyc
    haveI := hcyc
    exact hAnc (isCyclic_of_surjective
      ((Subgroup.equivMapOfInjective A κ hκinj).symm : A.map κ →* A)
      (Subgroup.equivMapOfInjective A κ hκinj).symm.surjective)
  have hAE' : A' ≤ Subgroup.normalizer (E' : Set Γ) := by
    rw [hA'def, hE'def]
    intro x hx
    obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact inr_mem_normalizer_inl a
  have hQ'E' : Q' ≤ Subgroup.normalizer (E' : Set Γ) := by
    rw [hQ'def, hE'def]
    intro x hx
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact inr_mem_normalizer_inl q
  have hQodd' : Odd (Nat.card Q') := by
    rw [hQ'def, Subgroup.card_map_of_injective hκinj]
    exact hQodd
  have hA'Q' : A' ≤ Subgroup.normalizer (Q' : Set Γ) := by
    rw [hA'def, hQ'def]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (MulAut.conj (κ a) : Γ →* Γ).comp κ =
        κ.comp (MulAut.conj a : MulAut E →* MulAut E) := by
      apply MonoidHom.ext
      intro z
      simp [MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [Subgroup.map_map Q (MulAut.conj (κ a) : Γ →* Γ) κ, hcomp,
      ← Subgroup.map_map Q κ (MulAut.conj a : MulAut E →* MulAut E),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAQ ha)]
  have hAE0' : ∀ a' ∈ A', a' ≠ 1 →
      E' ⊓ Subgroup.centralizer ({a'} : Set Γ) =
        E' ⊓ Subgroup.centralizer (A' : Set Γ) := by
    intro a' ha' ha'1
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    have ha1 : a ≠ 1 := fun h => ha'1 (by rw [h, map_one])
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxE', hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hxE'
      refine Subgroup.mem_inf.mpr ⟨hE'mem e, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
      rw [inr_mul_inl_eq_iff]
      have hae : a e = e := by
        rw [Subgroup.mem_centralizer_iff] at hxC
        exact (inr_mul_inl_eq_iff a e).mp (hxC (κ a) (Set.mem_singleton (κ a)))
      exact (hAfix a ha ha1 e).mpr hae b hb
    · intro x hx
      obtain ⟨hxE', hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxE', Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hA'mem a ha) hxC⟩
  have hcomm : ⁅Q', A'⁆ ≤ Subgroup.centralizer (E' : Set Γ) :=
    commutator_le_centralizer_of_inf_centralizer_eq hE' hA' hAnc' hAE' hAE0' hQodd' hA'Q' hQ'E'
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  apply MulEquiv.ext
  intro e
  have hc' : κ c ∈ ⁅Q', A'⁆ := by
    rw [hQ'def, hA'def, ← Subgroup.map_commutator]
    exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
  have hcent := hcomm hc'
  rw [Subgroup.mem_centralizer_iff] at hcent
  have hιe : ι e ∈ E' := hE'mem e
  have hcomm' : κ c * ι e = ι e * κ c := (hcent (ι e) hιe).symm
  have h1 : ι (c e) = ι e := by
    have h2 : ι (c e) = κ c * ι e * κ (c⁻¹) :=
      SemidirectProduct.inl_aut (φ := φ) c e
    rw [h2, hcomm', map_inv]; group
  simpa using hιinj h1

variable {G : Type*} [Group G] [Finite G]

private lemma normalizerMonoidHom_apply_eq_iff {E : Subgroup G}
    (x : Subgroup.normalizer (E : Set G)) (e : E) :
    E.normalizerMonoidHom x e = e ↔ (x : G) * (e : G) = (e : G) * (x : G) := by
  constructor
  · intro h
    have h' : (x : G) * (e : G) * (x : G)⁻¹ = (e : G) := by
      rw [← Subgroup.normalizerMonoidHom_apply_apply_coe E x e]
      exact congrArg Subtype.val h
    calc (x : G) * (e : G) = (x : G) * (e : G) * (x : G)⁻¹ * (x : G) := by group
      _ = (e : G) * (x : G) := by rw [h']
  · intro h
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc (x : G) * (e : G) * (x : G)⁻¹ = (e : G) * (x : G) * (x : G)⁻¹ := by rw [h]
      _ = (e : G) := by group

theorem commutator_le_centralizer_of_odd_relIndex {E A Q : Subgroup G}
    (hE : IsElemAbelian 2 E) (hA : IsElemAbelian 2 A) (hAnc : ¬ IsCyclic A)
    (hAE : A ≤ Subgroup.normalizer (E : Set G))
    (hAE0 : ∀ a ∈ A, a ≠ 1 →
      E ⊓ Subgroup.centralizer ({a} : Set G) = E ⊓ Subgroup.centralizer (A : Set G))
    (hQE : Q ≤ Subgroup.normalizer (E : Set G)) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQodd : Odd ((Subgroup.centralizer (E : Set G)).relIndex Q)) :
    ⁅Q, A⁆ ≤ Subgroup.centralizer (E : Set G) := by
  classical
  set C : Subgroup G := Subgroup.centralizer (E : Set G) with hCdef
  set N : Subgroup G := Subgroup.normalizer (E : Set G) with hNdef
  by_cases hcase : ∃ a ∈ A, a ≠ 1 ∧ a ∈ C
  · obtain ⟨a, haA, ha1, haC⟩ := hcase
    have hEa : E ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (Subgroup.mem_centralizer_iff.mp haC x hx).symm
    have hECA : E ≤ Subgroup.centralizer (A : Set G) := by
      have h1 : E ≤ E ⊓ Subgroup.centralizer ({a} : Set G) := le_inf le_rfl hEa
      rw [hAE0 a haA ha1] at h1
      exact h1.trans inf_le_right
    exact commutator_le_centralizer_of_le_centralizer hQE hAE
      (Subgroup.le_centralizer_iff.mpr hECA)
  · have hACbot : A ⊓ C = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      by_contra hx1
      exact hcase ⟨x, hxA, hx1, hxC⟩
    set ψ : N →* MulAut ↥E := E.normalizerMonoidHom with hψdef
    set A₁ : Subgroup N := A.subgroupOf N with hA1def
    set Q₁ : Subgroup N := Q.subgroupOf N with hQ1def
    set Ahat : Subgroup (MulAut ↥E) := A₁.map ψ with hAhatdef
    set Qhat : Subgroup (MulAut ↥E) := Q₁.map ψ with hQhatdef
    have hker : ψ.ker = C.subgroupOf N := by
      rw [hψdef, hCdef]
      exact Subgroup.normalizerMonoidHom_ker (H := E)
    have hkerA : A₁ ⊓ ψ.ker = ⊥ := by
      rw [hker, Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [hA1def, Subgroup.mem_subgroupOf] at hxA
      rw [Subgroup.mem_subgroupOf] at hxC
      exact Subtype.ext (Subgroup.mem_bot.mp (by
        rw [← hACbot]
        exact Subgroup.mem_inf.mpr ⟨hxA, hxC⟩))
    have hA1_norm : A₁ ≤ Subgroup.normalizer (Q₁ : Set N) := by
      intro x hx
      have hxG : (x : G) ∈ A := by
        rw [hA1def, Subgroup.mem_subgroupOf] at hx
        exact hx
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have h := Subgroup.mem_normalizer_iff.mp (hAQ hxG) (q : G)
      simpa [hQ1def, Subgroup.mem_subgroupOf] using h
    have hAQ' : Ahat ≤ Subgroup.normalizer (Qhat : Set (MulAut ↥E)) := by
      rw [hAhatdef, hQhatdef]
      calc A₁.map ψ ≤ (Subgroup.normalizer (Q₁ : Set N)).map ψ :=
            Subgroup.map_mono hA1_norm
        _ ≤ Subgroup.normalizer (Q₁.map ψ) := Subgroup.le_normalizer_map ψ
    have hA' : IsElemAbelian 2 Ahat := by
      rw [hAhatdef, hA1def]
      exact (hA.subgroupOf N).map ψ
    have hE' : IsElemAbelian 2 (⊤ : Subgroup ↥E) := by
      rw [← Subgroup.subgroupOf_self (H := E)]
      exact hE.subgroupOf E
    let ψA : A →* MulAut ↥E := ψ.comp (Subgroup.inclusion hAE)
    have hψAdef : ψA = ψ.comp (Subgroup.inclusion hAE) := rfl
    have hψA_range : ψA.range = Ahat := by
      rw [hAhatdef, hA1def, hψAdef, MonoidHom.range_comp, Subgroup.inclusion_range]
    have hψA_inj : Function.Injective ψA := by
      rw [← MonoidHom.ker_eq_bot_iff ψA, Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker, hψAdef, MonoidHom.comp_apply] at hx
      have hx1 : Subgroup.inclusion hAE x ∈ A₁ ⊓ ψ.ker := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [hA1def, Subgroup.mem_subgroupOf]
          exact x.2
        · rw [MonoidHom.mem_ker]; exact hx
      have hxbot : Subgroup.inclusion hAE x ∈ (⊥ : Subgroup N) := by
        rw [← hkerA]; exact hx1
      exact Subgroup.inclusion_injective hAE (Subgroup.mem_bot.mp hxbot)
    have hAnc' : ¬ IsCyclic Ahat := by
      intro hcyc
      haveI := hcyc
      rw [← hψA_range] at hcyc
      exact hAnc ((ψA.ofInjective hψA_inj).isCyclic.mpr hcyc)
    have hAfix' : ∀ a ∈ Ahat, a ≠ 1 → ∀ e : ↥E,
        (∀ b ∈ Ahat, b e = e) ↔ a e = e := by
      intro a ha ha1 e
      obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.mp ha
      have ha₁A : (a₁ : G) ∈ A := by
        rw [hA1def, Subgroup.mem_subgroupOf] at ha₁
        exact ha₁
      have ha₁1 : (a₁ : G) ≠ 1 := by
        intro h
        have h1 : a₁ = (1 : ↥N) := Subtype.ext (by simpa using h)
        exact ha1 (by rw [h1, map_one])
      have hiff : (∀ b ∈ Ahat, b e = e) ↔
          (e : G) ∈ Subgroup.centralizer (A : Set G) := by
        constructor
        · intro hb
          rw [Subgroup.mem_centralizer_iff]
          intro b hbA
          have hbN : b ∈ N := hAE hbA
          have hb' : (⟨b, hbN⟩ : ↥N) ∈ A₁ := by
            rw [hA1def, Subgroup.mem_subgroupOf]; exact hbA
          have h1 := hb (ψ ⟨b, hbN⟩) (Subgroup.mem_map.mpr ⟨_, hb', rfl⟩)
          have h2 := (normalizerMonoidHom_apply_eq_iff (E := E) ⟨b, hbN⟩ e).mp h1
          simpa using h2
        · intro he b hb
          obtain ⟨b₁, hb₁, rfl⟩ := Subgroup.mem_map.mp hb
          have hb₁A : (b₁ : G) ∈ A := by
            rw [hA1def, Subgroup.mem_subgroupOf] at hb₁
            exact hb₁
          have h2 : (b₁ : G) * (e : G) = (e : G) * (b₁ : G) :=
            Subgroup.mem_centralizer_iff.mp he (b₁ : G) hb₁A
          exact (normalizerMonoidHom_apply_eq_iff (E := E) b₁ e).mpr h2
      have hright : ψ a₁ e = e ↔ (e : G) ∈
          Subgroup.centralizer ({(a₁ : G)} : Set G) := by
        rw [normalizerMonoidHom_apply_eq_iff, Subgroup.mem_centralizer_singleton_iff]
        exact eq_comm
      rw [hiff, hright]
      have hE0 := hAE0 (a₁ : G) ha₁A ha₁1
      constructor
      · intro he
        have hmem : (e : G) ∈ E ⊓ Subgroup.centralizer (A : Set G) :=
          Subgroup.mem_inf.mpr ⟨e.2, he⟩
        rw [← hE0] at hmem
        exact hmem.2
      · intro he
        have hmem : (e : G) ∈ E ⊓ Subgroup.centralizer ({(a₁ : G)} : Set G) :=
          Subgroup.mem_inf.mpr ⟨e.2, he⟩
        rw [hE0] at hmem
        exact hmem.2
    have hQcard : Nat.card Qhat = C.relIndex Q := by
      rw [hQhatdef, hQ1def, ← Subgroup.relIndex_ker (f := ψ), hker]
      exact Subgroup.relIndex_subgroupOf hQE
    have hQodd' : Odd (Nat.card Qhat) := by
      rw [hQcard]; exact hQodd
    have hcomm : ⁅Qhat, Ahat⁆ = ⊥ :=
      commutator_eq_bot_of_odd_of_fixed_eq hE' hA' hAnc' hAfix' hQodd' hAQ'
    have hmap : (⁅Q₁, A₁⁆).map ψ = ⊥ := by
      rw [Subgroup.map_commutator, ← hQhatdef, ← hAhatdef, hcomm]
    have hle : ⁅Q₁, A₁⁆ ≤ ψ.ker :=
      (Subgroup.map_eq_bot_iff (H := ⁅Q₁, A₁⁆) (f := ψ)).mp hmap
    have hmap2 : (⁅Q₁, A₁⁆).map N.subtype = ⁅Q, A⁆ := by
      rw [Subgroup.map_commutator]
      congr 1
      · rw [hQ1def, Subgroup.map_subgroupOf_eq_of_le hQE]
      · rw [hA1def, Subgroup.map_subgroupOf_eq_of_le hAE]
    calc ⁅Q, A⁆ = (⁅Q₁, A₁⁆).map N.subtype := hmap2.symm
      _ ≤ ψ.ker.map N.subtype := Subgroup.map_mono hle
      _ = (C.subgroupOf N).map N.subtype := by rw [hker]
      _ = C := Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer (E : Set G))

end CFSG.LocalAnalysis.WeakClosure81

end
