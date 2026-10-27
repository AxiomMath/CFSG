module

public import CFSG.Quasithin.Background.G10SixteenA
public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.G10FifteenRing

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def raU (a : GLV V) (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  U.map (a.toLinearMap - LinearMap.id)

theorem mem_raU {a : GLV V} {U : Submodule (ZMod 2) V} {w : V} :
    w ∈ raU a U ↔ ∃ u ∈ U, a u - u = w := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem raU_le {a : GLV V} {U : Submodule (ZMod 2) V} (hU : conjSub a U = U) : raU a U ≤ U := by
  rintro _ ⟨u, hu, rfl⟩
  have h1 : a u ∈ U := by
    have := apply_mem_conjSub (g := a) hu
    rwa [hU] at this
  exact U.sub_mem h1 hu

theorem raU_top (a : GLV V) : raU a ⊤ = LinearMap.range (a.toLinearMap - LinearMap.id) := by
  unfold raU
  rw [Submodule.map_top]

theorem raU_sup (a : GLV V) (U₁ U₂ : Submodule (ZMod 2) V) :
    raU a (U₁ ⊔ U₂) = raU a U₁ ⊔ raU a U₂ := by
  unfold raU
  rw [Submodule.map_sup]

theorem raU_mono (a : GLV V) {U U' : Submodule (ZMod 2) V} (h : U ≤ U') : raU a U ≤ raU a U' :=
  Submodule.map_mono h

theorem raU_eq_bot_iff {a : GLV V} {U : Submodule (ZMod 2) V} :
    raU a U = ⊥ ↔ ∀ u ∈ U, a u = u := by
  constructor
  · intro h u hu
    have : a u - u ∈ raU a U := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · intro h
    rw [eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    have : a u - u = 0 := sub_eq_zero.2 (h u hu)
    show a u - u ∈ (⊥ : Submodule (ZMod 2) V)
    rw [this]
    exact Submodule.zero_mem _

theorem finrank_raU_sup [Finite V] {a : GLV V} {U₁ U₂ : Submodule (ZMod 2) V}
    (h₁ : conjSub a U₁ = U₁) (h₂ : conjSub a U₂ = U₂) (hdis : U₁ ⊓ U₂ = ⊥) :
    Module.finrank (ZMod 2) ↥(raU a (U₁ ⊔ U₂)) =
      Module.finrank (ZMod 2) ↥(raU a U₁) + Module.finrank (ZMod 2) ↥(raU a U₂) := by
  rw [raU_sup]
  have hinf : raU a U₁ ⊓ raU a U₂ = ⊥ := by
    rw [eq_bot_iff, ← hdis]
    exact inf_le_inf (raU_le h₁) (raU_le h₂)
  have := Submodule.finrank_sup_add_finrank_inf_eq (raU a U₁) (raU a U₂)
  rw [hinf, finrank_bot] at this
  omega

theorem finrank_raU_eq [Finite V] {a : GLV V} {U : Submodule (ZMod 2) V} (h : conjSub a U = U) :
    Module.finrank (ZMod 2) ↥(raU a U) =
      Module.finrank (ZMod 2) ↥(LinearMap.range (commMap a U h)) := by
  have hmap : (LinearMap.range (commMap a U h)).map U.subtype = raU a U := by
    ext w
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨(u : V), u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  rw [← hmap]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective U.subtype U.injective_subtype (LinearMap.range (commMap a U h)))).symm

theorem inducesTransvection_of_finrank_raU [Finite V] {a : GLV V} {J : Submodule (ZMod 2) V}
    (h : conjSub a J = J) (h1 : Module.finrank (ZMod 2) ↥(raU a J) = 1) :
    ∃ c : V, InducesTransvection a J c :=
  (inducesTransvection_iff_finrank h).2 ((finrank_raU_eq h).symm.trans h1)

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem conjSub_eq_of_invariant {a : GLV V} (ha : a ∈ X)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    {U : Submodule (ZMod 2) V} (hU : Invariant (normalClosure Γ L) U) : conjSub a U = U := by
  have hS := sSup_irr_le_eq hyp.sSup_isIrr hU
  have hfixJ : ∀ J ∈ {J | IsIrr (normalClosure Γ L) J ∧ J ≤ U}, conjSub a J = J :=
    fun J hJ => hyp.conj_eq_of_finrank_le ha hrank (hJ.1.irrPlus hyp.fixedSpace_H)
  have himg : conjSub a '' {J | IsIrr (normalClosure Γ L) J ∧ J ≤ U} =
      {J | IsIrr (normalClosure Γ L) J ∧ J ≤ U} := by
    ext J
    constructor
    · rintro ⟨J', hJ', rfl⟩
      rw [hfixJ J' hJ']
      exact hJ'
    · intro hJ
      exact ⟨J, hJ, hfixJ J hJ⟩
  conv_lhs => rw [← hS]
  rw [conjSub_sSup, himg]
  exact hS


theorem faithful_of_irr {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hf : FaithfulOn (normalClosure Γ L) I) {J : Submodule (ZMod 2) V}
    (hJ : IsIrr (normalClosure Γ L) J) : FaithfulOn (normalClosure Γ L) J := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have htop := iSup_conjSub_eq_top hyp.irreducible hirr.ne_bot
  let S : Set (Submodule (ZMod 2) V) := Set.range (fun γ : ↥Γ => conjSub (γ : GLV V) I)
  have hSirr : ∀ K ∈ S, IsIrr (normalClosure Γ L) K := by
    rintro _ ⟨γ, rfl⟩
    exact hirr.conj_of_normal (normalClosure_normal Γ L) γ.2
  have hJS : J ≤ sSup S := by
    rw [sSup_range, htop]
    exact le_top
  obtain ⟨K, ⟨γ, rfl⟩, hJK⟩ := irr_le_sSup hJ hSirr hJS
  unfold FaithfulOn
  rw [centralizerOn_eq_of_hiso hJ.1 (hSirr _ ⟨γ, rfl⟩).1 hJK]
  rw [← FaithfulOn, faithfulOn_iff]
  intro k hk hkI
  have hk' : (γ : GLV V)⁻¹ * k * (γ : GLV V) ∈ normalClosure Γ L := by
    have := normalClosure_normal Γ L (γ : GLV V)⁻¹ (Γ.inv_mem γ.2) k hk
    simpa using this
  have h1 : (γ : GLV V)⁻¹ * k * (γ : GLV V) = 1 := by
    refine faithfulOn_iff.1 hf _ hk' fun u hu => ?_
    have hγu : (γ : GLV V) u ∈ conjSub (γ : GLV V) I := apply_mem_conjSub hu
    show (γ : GLV V)⁻¹ (k ((γ : GLV V) u)) = u
    rw [hkI _ hγu]
    exact LinearEquiv.symm_apply_apply (γ : GLV V) u
  calc k = (γ : GLV V) * ((γ : GLV V)⁻¹ * k * (γ : GLV V)) * (γ : GLV V)⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem raU_ne_bot {a : GLV V} (ha : a ∈ X)
    (hcomm : ∃ h ∈ normalClosure Γ L, a * h ≠ h * a)
    (hfaith : ∀ J, IsIrr (normalClosure Γ L) J → FaithfulOn (normalClosure Γ L) J)
    {U : Submodule (ZMod 2) V} (hU : Invariant (normalClosure Γ L) U) (hU0 : U ≠ ⊥) :
    raU a U ≠ ⊥ := by
  intro hbot
  rw [raU_eq_bot_iff] at hbot
  obtain ⟨J, hJU, hJ⟩ := exists_isIrr_le hU hU0
  obtain ⟨h, hh, hne⟩ := hcomm
  apply hne
  have hk : a * h * a⁻¹ ∈ normalClosure Γ L := normalClosure_normal Γ L a (hyp.X_le ha) h hh
  have hka : ∀ v ∈ J, (a * h * a⁻¹) v = h v := by
    intro v hv
    have e0 : a v = v := hbot v (hJU hv)
    have e1 : a⁻¹ v = v := by
      calc a⁻¹ v = a⁻¹ (a v) := by rw [e0]
        _ = v := LinearEquiv.symm_apply_apply a v
    show a (h (a⁻¹ v)) = h v
    rw [e1]
    exact hbot (h v) (hJU (hJ.1 h hh v hv))
  have h1 : (a * h * a⁻¹)⁻¹ * h = 1 := by
    refine faithfulOn_iff.1 (hfaith J hJ) _
      ((normalClosure Γ L).mul_mem ((normalClosure Γ L).inv_mem hk) hh) fun u hu => ?_
    have e2 := hka u hu
    show (a * h * a⁻¹)⁻¹ (h u) = u
    rw [← e2]
    exact LinearEquiv.symm_apply_apply (a * h * a⁻¹) u
  have h2 : a * h * a⁻¹ = h := inv_mul_eq_one.1 h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem irr_or_two {a : GLV V} (ha : a ∈ X)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    (hcomm : ∃ h ∈ normalClosure Γ L, a * h ≠ h * a)
    (hfaith : ∀ J, IsIrr (normalClosure Γ L) J → FaithfulOn (normalClosure Γ L) J) :
    IsIrr (normalClosure Γ L) ⊤ ∨ ∃ J₁ J₂ : Submodule (ZMod 2) V, IsCompl J₁ J₂ ∧
      IsIrr (normalClosure Γ L) J₁ ∧ IsIrr (normalClosure Γ L) J₂ ∧ conjSub a J₁ = J₁ ∧
      conjSub a J₂ = J₂ ∧ Module.finrank (ZMod 2) ↥(raU a J₁) = 1 ∧
      Module.finrank (ZMod 2) ↥(raU a J₂) = 1 := by
  obtain ⟨J₁, hJ₁⟩ := hyp.exists_isIrr
  obtain ⟨J', hJ'inv, hc⟩ := exists_invariant_compl hyp.sSup_isIrr hJ₁.1
  by_cases hJ'0 : J' = ⊥
  · left
    have : J₁ = ⊤ := by
      have := hc.sup_eq_top
      rwa [hJ'0, sup_bot_eq] at this
    rw [← this]
    exact hJ₁
  · right
    obtain ⟨J₂, hJ₂J', hJ₂⟩ := exists_isIrr_le hJ'inv hJ'0
    have hdis12 : J₁ ⊓ J₂ = ⊥ := by
      rw [eq_bot_iff, ← hc.disjoint.eq_bot]
      exact inf_le_inf_left _ hJ₂J'
    have hsup : Invariant (normalClosure Γ L) (J₁ ⊔ J₂) := hJ₁.1.sup hJ₂.1
    obtain ⟨J'', hJ''inv, hc''⟩ := exists_invariant_compl hyp.sSup_isIrr hsup
    have hf₁ : conjSub a J₁ = J₁ := hyp.conj_eq_of_finrank_le ha hrank
      (hJ₁.irrPlus hyp.fixedSpace_H)
    have hf₂ : conjSub a J₂ = J₂ := hyp.conj_eq_of_finrank_le ha hrank
      (hJ₂.irrPlus hyp.fixedSpace_H)
    have hf₁₂ : conjSub a (J₁ ⊔ J₂) = J₁ ⊔ J₂ := hyp.conjSub_eq_of_invariant ha hrank hsup
    have hn₁ : 1 ≤ Module.finrank (ZMod 2) ↥(raU a J₁) :=
      Submodule.one_le_finrank_iff.2 (hyp.raU_ne_bot ha hcomm hfaith hJ₁.1 hJ₁.ne_bot)
    have hn₂ : 1 ≤ Module.finrank (ZMod 2) ↥(raU a J₂) :=
      Submodule.one_le_finrank_iff.2 (hyp.raU_ne_bot ha hcomm hfaith hJ₂.1 hJ₂.ne_bot)
    have hsum := finrank_raU_sup hf₁ hf₂ hdis12
    by_cases hJ''0 : J'' = ⊥
    · have htop : J₁ ⊔ J₂ = ⊤ := by
        have := hc''.sup_eq_top
        rwa [hJ''0, sup_bot_eq] at this
      rw [htop, raU_top] at hsum
      refine ⟨J₁, J₂, ⟨?_, ?_⟩, hJ₁, hJ₂, hf₁, hf₂, ?_, ?_⟩
      · exact disjoint_iff.2 hdis12
      · rw [codisjoint_iff]
        exact htop
      · omega
      · omega
    · exfalso
      have hf'' : conjSub a J'' = J'' := hyp.conjSub_eq_of_invariant ha hrank hJ''inv
      have hn₃ : 1 ≤ Module.finrank (ZMod 2) ↥(raU a J'') :=
        Submodule.one_le_finrank_iff.2 (hyp.raU_ne_bot ha hcomm hfaith hJ''inv hJ''0)
      have hsum2 := finrank_raU_sup hf₁₂ hf'' hc''.disjoint.eq_bot
      rw [hc''.sup_eq_top, raU_top] at hsum2
      omega

end G108Hyp

end G11

end CFSG.Quasithin
