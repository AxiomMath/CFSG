module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporComp

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.Inn

@[expose] def NoCompAt (X : Type*) [Group X] (t : X) : Prop :=
  ∀ B : Subgroup (centralizer ({t} : Set X)), ¬ CFSG.IsComponent B

theorem map_centralizer_singleton_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (t : X) :
    (centralizer ({t} : Set X)).map e.toMonoidHom = centralizer ({e t} : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * t = t * x := mem_centralizer_singleton_iff.mp hx
    rw [mem_centralizer_singleton_iff]
    change e x * e t = e t * e x
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    have hy' : e x * e t = e t * e x := mem_centralizer_singleton_iff.mp hy
    exact mem_centralizer_singleton_iff.mpr (e.injective (by rw [map_mul, map_mul]; exact hy'))

theorem isComponent_map_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) {L : Subgroup A}
    (hL : CFSG.IsComponent L) : CFSG.IsComponent (L.map e.toMonoidHom) :=
  ⟨isQuasisimple_of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective) hL.1,
    Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective hL.2⟩

theorem NoCompAt.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {t : X}
    (h : NoCompAt Y (e t)) : NoCompAt X t := by
  intro B hB
  let φ : centralizer ({t} : Set X) ≃* centralizer ({e t} : Set Y) :=
    ((centralizer ({t} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_singleton_eq e t))
  exact h _ (isComponent_map_mulEquiv' φ hB)

theorem isSylowTwoOf_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {D : Subgroup X} (hD : IsSylowTwoOf D ⊤) : IsSylowTwoOf (D.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hD.2.1.map e.toMonoidHom, ?_⟩
  have h1 : ((D.map e.toMonoidHom).subgroupOf ⊤).index = (D.map e.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have h2 : (D.subgroupOf ⊤).index = D.index := Subgroup.relIndex_top_right _
  rw [h1, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective D]
  have := hD.2.2
  rwa [h2] at this

theorem Cent2NoComp.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Cent2NoComp Y) : Cent2NoComp X := by
  intro D hD t htD ht2 hcomm
  refine NoCompAt.of_mulEquiv e (t := t) ?_
  refine h _ (isSylowTwoOf_map_mulEquiv e hD) (e t) ⟨t, htD, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ht2) ?_
  rintro _ ⟨d, hd, rfl⟩
  change e d * e t = e t * e d
  rw [← map_mul, ← map_mul, hcomm d hd]

theorem exists_conj_of_isSylowTwoOf {X : Type*} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem eq_one_or_eq_of_mem_zpowers' {X : Type*} [Group X] {z h : X} (hz2 : orderOf z = 2)
    (hh : h ∈ Subgroup.zpowers z) : h = 1 ∨ h = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rw [← zpow_mod_orderOf, hz2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem cent2NoComp_of_centre {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) {z₀ : X} (hz2 : orderOf z₀ = 2)
    (hZ : S ⊓ centralizer (S : Set X) = Subgroup.zpowers z₀) (hcomp : NoCompAt X z₀) :
    Cent2NoComp X := by
  intro D hD t htD ht2 hcomm
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hS hD
  have hDg : ∀ s ∈ S, g * s * g⁻¹ ∈ D := fun s hs => hg ▸ ⟨s, hs, rfl⟩
  obtain ⟨s₀, hs₀, hs₀t⟩ : ∃ s ∈ S, g * s * g⁻¹ = t := by
    rw [← hg] at htD
    obtain ⟨s, hs, hst⟩ := htD
    exact ⟨s, hs, hst⟩
  have hconj : g⁻¹ * t * g = s₀ := by rw [← hs₀t]; group
  have htS : g⁻¹ * t * g ∈ S := hconj ▸ hs₀
  have htc : g⁻¹ * t * g ∈ centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hcomm _ (hDg s hs)
    calc s * (g⁻¹ * t * g) = g⁻¹ * ((g * s * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * s * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * t * g) * s := by group
  have hmem : g⁻¹ * t * g ∈ Subgroup.zpowers z₀ := hZ ▸ Subgroup.mem_inf.mpr ⟨htS, htc⟩
  have hord : orderOf (g⁻¹ * t * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [ht2] at this
    simpa using this
  have heq : g⁻¹ * t * g = z₀ := by
    rcases eq_one_or_eq_of_mem_zpowers' hz2 hmem with h | h
    · rw [h, orderOf_one] at hord
      omega
    · exact h
  refine NoCompAt.of_mulEquiv (MulAut.conj g⁻¹) (t := t) ?_
  have : (MulAut.conj g⁻¹) t = z₀ := by simpa using heq
  rw [this]
  exact hcomp

end CFSG.Quasithin.E6.Spor
