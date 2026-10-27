module

public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompE
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Milestones.ASVolI.F437.Defs
public import CFSG.Quasithin.H13.U4ParRecog

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section Fix

variable {X : Type} [Group X]

@[expose] def burnsideF437U_fix (γ : X →* X) : Subgroup X where
  carrier := {x | γ x = x}
  mul_mem' {a b} ha hb := by
    change γ (a * b) = a * b
    rw [map_mul, show γ a = a from ha, show γ b = b from hb]
  one_mem' := map_one γ
  inv_mem' {a} ha := by
    change γ a⁻¹ = a⁻¹
    rw [map_inv, show γ a = a from ha]

theorem burnsideF437U_mem_fix {γ : X →* X} {x : X} : x ∈ burnsideF437U_fix γ ↔ γ x = x :=
  Iff.rfl

theorem burnsideF437U_mem_map_conj {H : Subgroup X} {a y : X} :
    y ∈ H.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * y * a ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem burnsideF437U_act_mul_fix (γ : X →* X) {a s : X} (hs : γ s = s) (x : X) :
    (a * s) * γ ((a * s)⁻¹ * x * (a * s)) * (a * s)⁻¹ = a * γ (a⁻¹ * x * a) * a⁻¹ := by
  have e : (a * s)⁻¹ * x * (a * s) = s⁻¹ * (a⁻¹ * x * a) * s := by group
  rw [e, map_mul, map_mul, map_inv, hs]
  group

theorem burnsideF437U_isSylowOf_map {E : Type} [Group E] (φ : X →* E) (hφ : Function.Injective φ)
    {A C : Subgroup X} (h : IsSylowOf 2 A C) : IsSylowOf 2 (A.map φ) (C.map φ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map φ, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective A C hφ]
  exact h.2.2

theorem burnsideF437U_isSylowOf_of_map {E : Type} [Group E] (φ : X →* E)
    (hφ : Function.Injective φ) {A C : Subgroup X} (h : IsSylowOf 2 (A.map φ) (C.map φ)) :
    IsSylowOf 2 A C := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(Subgroup.map_le_map_iff_of_injective hφ).1 h1,
    h2.of_equiv (A.equivMapOfInjective φ hφ).symm, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective A C hφ] at h3

end Fix

section Cen

variable {E : Type} [Group E] {X : Type} [Group X]

theorem burnsideF437U_cenIn_map (φ : X →* E) (hφ : Function.Injective φ) (γ : X →* X) {fb : E}
    {a : X} (hact : ∀ x, fb * φ x * fb⁻¹ = φ (a * γ (a⁻¹ * x * a) * a⁻¹)) (Q : Subgroup X) :
    cenIn (Q.map φ) fb =
      (Q ⊓ (burnsideF437U_fix γ).map (MulAut.conj a).toMonoidHom).map φ := by
  ext e
  rw [cenIn, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc0⟩
    have hc : φ y * fb = fb * φ y := Subgroup.mem_centralizer_singleton_iff.mp hc0
    refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, ?_⟩, rfl⟩
    rw [burnsideF437U_mem_map_conj, burnsideF437U_mem_fix]
    have e1 : fb * φ y * fb⁻¹ = φ y := by
      rw [← hc]
      group
    rw [hact] at e1
    have e2 := hφ e1
    calc γ (a⁻¹ * y * a) = a⁻¹ * (a * γ (a⁻¹ * y * a) * a⁻¹) * a := by group
      _ = a⁻¹ * y * a := by rw [e2]
  · rintro ⟨y, hyQF, rfl⟩
    obtain ⟨hy, hyF⟩ := Subgroup.mem_inf.mp hyQF
    refine ⟨⟨y, hy, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [burnsideF437U_mem_map_conj, burnsideF437U_mem_fix] at hyF
    have e1 : fb * φ y * fb⁻¹ = φ y := by
      rw [hact, hyF]
      congr 1
      group
    calc φ y * fb = (fb * φ y * fb⁻¹) * fb := by rw [e1]
      _ = fb * φ y := by group

theorem burnsideF437U_inf_map_conj (γ : X →* X) {Q : Subgroup X} {c : X} (hc : c ∈ Q) :
    Q ⊓ (burnsideF437U_fix γ).map (MulAut.conj c).toMonoidHom =
      (burnsideF437U_fix γ ⊓ Q).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [Subgroup.mem_inf, burnsideF437U_mem_map_conj, burnsideF437U_mem_map_conj, Subgroup.mem_inf]
  constructor
  · rintro ⟨hyQ, hyF⟩
    exact ⟨hyF, Q.mul_mem (Q.mul_mem (Q.inv_mem hc) hyQ) hc⟩
  · rintro ⟨hyF, hyQ⟩
    refine ⟨?_, hyF⟩
    have := Q.mul_mem (Q.mul_mem hc hyQ) (Q.inv_mem hc)
    simpa [mul_assoc] using this

end Cen

section Reduce

variable {X : Type} [Group X]

theorem burnsideF437U_reduce [Finite X] (γ : X →* X) {P₁ P₂ : Subgroup X} {u₀ : X}
    (hu₀γ : γ u₀ = u₀) (hu₀ : u₀ ∈ pCoreOf 2 (P₁ ⊓ P₂))
    (hreg : ∀ g : X, g * u₀ * g⁻¹ ∈ pCoreOf 2 (P₁ ⊓ P₂) → g ∈ P₁ ⊓ P₂) (a : X)
    (hsyl : IsSylowOf 2
      (pCoreOf 2 (P₁ ⊓ P₂) ⊓ (burnsideF437U_fix γ).map (MulAut.conj a).toMonoidHom)
      ((burnsideF437U_fix γ).map (MulAut.conj a).toMonoidHom)) :
    ∃ s ∈ burnsideF437U_fix γ, a * s ∈ P₁ ⊓ P₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := pCoreOf 2 (P₁ ⊓ P₂) with hUdef
  set F := burnsideF437U_fix γ with hFdef
  have hcomp : ((MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom) =
      MonoidHom.id X := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hR : IsSylowOf 2 ((U ⊓ F.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj a⁻¹).toMonoidHom) F := by
    have := burnsideF437U_isSylowOf_map (MulAut.conj a⁻¹).toMonoidHom
      (MulAut.conj a⁻¹).injective hsyl
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at this
  have hS₀ : IsPGroup 2 ↥(U ⊓ F) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P₁ ⊓ P₂)).to_le inf_le_left
  have hR' : CFSG.QuasithinUnique.IsSylowTwoOf
      ((U ⊓ F.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom) F :=
    ⟨hR.1, hR.2.1, hR.2.2⟩
  obtain ⟨s, hsF, hs⟩ := CFSG.Quasithin.S143.InspW2.exists_conj_le_sylow hR' hS₀ inf_le_right
  refine ⟨s, hsF, hreg _ ?_⟩
  have h1 := hs u₀ ⟨hu₀, hu₀γ⟩
  rw [burnsideF437U_mem_map_conj] at h1
  have e : a * s * u₀ * (a * s)⁻¹ = a⁻¹⁻¹ * (s * u₀ * s⁻¹) * a⁻¹ := by group
  rw [e]
  exact h1.1

end Reduce

section Main

variable {E : Type} [Group E] {X : Type} [Group X]

theorem burnsideF437U_borel_conj [Finite X] {Gp M₁ M₂ : Subgroup E}
    (φ : X →* E) (hφ : Function.Injective φ) (hrange : φ.range = Gp)
    (γ : X →* X) {P₁ P₂ : Subgroup X} (h1 : Gp ⊓ M₁ = P₁.map φ) (h2 : Gp ⊓ M₂ = P₂.map φ)
    {u₀ : X} (hu₀γ : γ u₀ = u₀) (hu₀ : u₀ ∈ pCoreOf 2 (P₁ ⊓ P₂))
    (hreg : ∀ g : X, g * u₀ * g⁻¹ ∈ pCoreOf 2 (P₁ ⊓ P₂) → g ∈ P₁ ⊓ P₂)
    {fb : E} (hinv : burnsideF437_Inv Gp M₁ M₂ fb) (a : X)
    (hact : ∀ x, fb * φ x * fb⁻¹ = φ (a * γ (a⁻¹ * x * a) * a⁻¹)) :
    ∃ c ∈ P₁ ⊓ P₂, ∀ x, fb * φ x * fb⁻¹ = φ (c * γ (c⁻¹ * x * c) * c⁻¹) := by
  have hGp : Gp = (⊤ : Subgroup X).map φ := by rw [← hrange, MonoidHom.range_eq_map]
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (P₁ ⊓ P₂).map φ := by
    rw [show Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) by
      rw [inf_inf_distrib_left], h1, h2, Subgroup.map_inf_eq _ _ _ hφ]
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (pCoreOf 2 (P₁ ⊓ P₂)).map φ := by
    rw [hB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ]
  have hcenGp : cenIn Gp fb =
      ((burnsideF437U_fix γ).map (MulAut.conj a).toMonoidHom).map φ := by
    rw [hGp, burnsideF437U_cenIn_map φ hφ γ hact, top_inf_eq]
  have hcenS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) =
      (pCoreOf 2 (P₁ ⊓ P₂) ⊓
        (burnsideF437U_fix γ).map (MulAut.conj a).toMonoidHom).map φ := by
    rw [← burnsideF437U_cenIn_map φ hφ γ hact, ← hS]
    rfl
  have hsyl := hinv.sylow
  rw [hcenS, hcenGp] at hsyl
  obtain ⟨s, hsF, hc⟩ := burnsideF437U_reduce γ hu₀γ hu₀ hreg a
    (burnsideF437U_isSylowOf_of_map φ hφ hsyl)
  exact ⟨a * s, hc, fun x => by rw [hact, burnsideF437U_act_mul_fix γ hsF]⟩

theorem burnsideF437U_fixedFacts_of_model [Finite E] [Finite X] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (φ : X →* E) (hφ : Function.Injective φ) (hrange : φ.range = Gp)
    (γ : X →* X) {P₁ P₂ : Subgroup X} (h1 : Gp ⊓ M₁ = P₁.map φ) (h2 : Gp ⊓ M₂ = P₂.map φ)
    {u₀ : X} (hu₀γ : γ u₀ = u₀) (hu₀ : u₀ ∈ pCoreOf 2 (P₁ ⊓ P₂))
    (hreg : ∀ g : X, g * u₀ * g⁻¹ ∈ pCoreOf 2 (P₁ ⊓ P₂) → g ∈ P₁ ⊓ P₂)
    (hU : IsSylowOf 2 (pCoreOf 2 (P₁ ⊓ P₂)) ⊤)
    (hpar : IsLieParabolics 2 (burnsideF437U_fix γ) (burnsideF437U_fix γ ⊓ (P₁ ⊓ P₂))
      (burnsideF437U_fix γ ⊓ P₁) (burnsideF437U_fix γ ⊓ P₂))
    (hctr : ∀ z ∈ burnsideF437U_fix γ, (∀ y ∈ burnsideF437U_fix γ, z * y = y * z) → z = 1)
    (hidx : Gp.index = 2)
    {fb : E} (hinv : burnsideF437_Inv Gp M₁ M₂ fb) (a : X)
    (hact : ∀ x, fb * φ x * fb⁻¹ = φ (a * γ (a⁻¹ * x * a) * a⁻¹)) :
    IsLieParabolics 2 (cenIn Gp fb) (cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb) (cenIn (Gp ⊓ M₁) fb)
        (cenIn (Gp ⊓ M₂) fb) ∧
      (∀ S : Subgroup E, IsSylowOf 2 S Gp →
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({fb} : Set E) ≤ S →
          S = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
      Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) ⊓
        Subgroup.centralizer ({fb} : Set E) ≤ Subgroup.zpowers fb := by
  obtain ⟨c, hcB, hact'⟩ := burnsideF437U_borel_conj φ hφ hrange γ h1 h2 hu₀γ hu₀ hreg hinv a hact
  have hGp : Gp = (⊤ : Subgroup X).map φ := by rw [← hrange, MonoidHom.range_eq_map]
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (P₁ ⊓ P₂).map φ := by
    rw [show Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) by
      rw [inf_inf_distrib_left], h1, h2, Subgroup.map_inf_eq _ _ _ hφ]
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (pCoreOf 2 (P₁ ⊓ P₂)).map φ := by
    rw [hB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ]
  set F := burnsideF437U_fix γ with hFdef
  set U := pCoreOf 2 (P₁ ⊓ P₂) with hUdef
  set ψ : X →* E := φ.comp (MulAut.conj c).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := hφ.comp (MulAut.conj c).injective
  have hψx : ∀ y, ψ y = φ (c * y * c⁻¹) := fun y => rfl
  have hmapψ : ∀ H : Subgroup X, H.map ψ = (H.map (MulAut.conj c).toMonoidHom).map φ :=
    fun H => (Subgroup.map_map _ _ _).symm
  have hcP₁ : c ∈ P₁ := hcB.1
  have hcP₂ : c ∈ P₂ := hcB.2
  have hcen : ∀ Q : Subgroup X, c ∈ Q → cenIn (Q.map φ) fb = (F ⊓ Q).map ψ := by
    intro Q hcQ
    rw [burnsideF437U_cenIn_map φ hφ γ hact', burnsideF437U_inf_map_conj γ hcQ, hmapψ]
  have hD : cenIn Gp fb = F.map ψ := by
    rw [hGp, hcen ⊤ (Subgroup.mem_top c), inf_top_eq]
  have hD12 : cenIn (Gp ⊓ (M₁ ⊓ M₂)) fb = (F ⊓ (P₁ ⊓ P₂)).map ψ := by
    rw [hB, hcen _ hcB]
  have hD1 : cenIn (Gp ⊓ M₁) fb = (F ⊓ P₁).map ψ := by rw [h1, hcen _ hcP₁]
  have hD2 : cenIn (Gp ⊓ M₂) fb = (F ⊓ P₂).map ψ := by rw [h2, hcen _ hcP₂]
  have hcu : c * u₀ * c⁻¹ ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P₁ ⊓ P₂) hcB) u₀).mp hu₀
    exact this
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [hD, hD12, hD1, hD2]
    exact burnsideF48_isLieParabolics_map ψ hψ hpar
  ·
    intro S hS2 hle
    have hSbar : IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
      rw [hS, hGp]
      exact burnsideF437U_isSylowOf_map φ hφ hU
    obtain ⟨g, hgGp, hSg⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj
      (⟨hSbar.1, hSbar.2.1, hSbar.2.2⟩ : CFSG.QuasithinUnique.IsSylowTwoOf _ Gp)
      (⟨hS2.1, hS2.2.1, hS2.2.2⟩ : CFSG.QuasithinUnique.IsSylowTwoOf S Gp)
    rw [← hrange] at hgGp
    obtain ⟨g', rfl⟩ := hgGp
    have hmem : φ (c * u₀ * c⁻¹) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓
        Subgroup.centralizer ({fb} : Set E) := by
      refine Subgroup.mem_inf.mpr ⟨by rw [hS]; exact ⟨_, hcu, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : fb * φ (c * u₀ * c⁻¹) * fb⁻¹ = φ (c * u₀ * c⁻¹) := by
        rw [hact']
        congr 1
        rw [show c⁻¹ * (c * u₀ * c⁻¹) * c = u₀ by group, hu₀γ]
      calc φ (c * u₀ * c⁻¹) * fb = (fb * φ (c * u₀ * c⁻¹) * fb⁻¹) * fb := by rw [e1]
        _ = fb * φ (c * u₀ * c⁻¹) := by group
    have hmS := hle hmem
    rw [hSg, hS] at hmS
    obtain ⟨_, ⟨w, hwU, rfl⟩, hw⟩ := hmS
    have hw' : g' * w * g'⁻¹ = c * u₀ * c⁻¹ := by
      apply hφ
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv] using hw
    have hg'c : g'⁻¹ * c ∈ P₁ ⊓ P₂ := by
      refine hreg _ ?_
      have e2 : g'⁻¹ * c * u₀ * (g'⁻¹ * c)⁻¹ = w := by
        calc g'⁻¹ * c * u₀ * (g'⁻¹ * c)⁻¹ = g'⁻¹ * (c * u₀ * c⁻¹) * g' := by group
          _ = g'⁻¹ * (g' * w * g'⁻¹) * g' := by rw [hw']
          _ = w := by group
      rw [e2]
      exact hwU
    have hg' : g' ∈ P₁ ⊓ P₂ := by
      have := (P₁ ⊓ P₂).mul_mem hcB ((P₁ ⊓ P₂).inv_mem hg'c)
      simpa [mul_assoc] using this
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P₁ ⊓ P₂) hg'
    have hNi := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P₁ ⊓ P₂) ((P₁ ⊓ P₂).inv_mem hg')
    have hgU : U.map (MulAut.conj g').toMonoidHom = U := by
      ext y
      rw [burnsideF437U_mem_map_conj]
      constructor
      · intro hy
        have := (Subgroup.mem_normalizer_iff.mp hN (g'⁻¹ * y * g')).mp hy
        simpa [mul_assoc] using this
      · intro hy
        have := (Subgroup.mem_normalizer_iff.mp hNi y).mp hy
        simpa [mul_assoc] using this
    have hcomm : (MulAut.conj (φ g')).toMonoidHom.comp φ = φ.comp (MulAut.conj g').toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [hSg, hS, Subgroup.map_map, hcomm, ← Subgroup.map_map, hgU]
  ·
    have hfbG : fb ∉ Gp := hinv.not_mem
    have key : ∀ e ∈ Gp, e ∈ Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) →
        e ∈ Subgroup.centralizer ({fb} : Set E) → e = 1 := by
      intro e heG heD hefb
      have heC : e ∈ cenIn Gp fb := ⟨heG, hefb⟩
      rw [hD] at heC
      obtain ⟨y', hy'F, rfl⟩ := heC
      have hcen' : ∀ z ∈ F, z * y' = y' * z := by
        intro z hz
        have h1 := (Subgroup.mem_centralizer_iff.mp heD) (ψ z) (by rw [hD]; exact ⟨z, hz, rfl⟩)
        rw [← map_mul, ← map_mul] at h1
        exact hψ h1
      rw [hctr y' hy'F (fun z hz => (hcen' z hz).symm), map_one]
    rintro e ⟨heD, hefb⟩
    by_cases he : e ∈ Gp
    · rw [key e he heD hefb]
      exact Subgroup.one_mem _
    · have hefG : e * fb ∈ Gp := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false he hfbG
      have hfbD : fb ∈ Subgroup.centralizer ((cenIn Gp fb : Subgroup E) : Set E) := by
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact Subgroup.mem_centralizer_singleton_iff.mp hd.2
      have hfbfb : fb ∈ Subgroup.centralizer ({fb} : Set E) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have h1 := key (e * fb) hefG (Subgroup.mul_mem _ heD hfbD) (Subgroup.mul_mem _ hefb hfbfb)
      have h2 : e = fb⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers fb)

end Main

end CFSG.ASVolI
