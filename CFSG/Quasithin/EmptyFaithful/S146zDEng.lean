module

public import CFSG.Quasithin.EmptyFaithful.S146zDBase

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section Conj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_mem_cComp {H L : Subgroup G} {g : G} (hL : L ∈ cComp (conjSub g H)) :
    ∃ J ∈ cComp H, L = conjSub g J := by
  have h := cComp_map_mulEquiv (MulAut.conj g⁻¹) hL
  have e1 : (conjSub g H).map (MulAut.conj g⁻¹).toMonoidHom = H := conjSub_conjSub_inv g H
  rw [e1] at h
  refine ⟨_, h, ?_⟩
  exact (conjSub_inv_conjSub g L).symm

end Conj

section Engine

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem engine (S : Setting146 G T M) (c19 : Conc14619 T M)
    {K Kp U₁ U₂ : Subgroup G} {s : G} (cK : ThreeC.CCtx T M K U₁ U₂ s)
    (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp)
    {g : G} {E A₁ : Subgroup G} (hE : E = conjSub g (uOfL22 T M)) (hA₁ : A₁ = conjSub g Zz)
    (hEH : E ≤ mcOf T) (hEab : IsElemAbelian 2 E)
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hEKp : E ≤ Subgroup.normalizer (Kp : Set G))
    (hA₁c : Nat.card A₁ = 2) (hA₁Z : A₁ ⊓ Zz = ⊥) (hA₁UK : A₁ ≤ U₁ ⊔ U₂)
    (hnt : ¬ E ≤ centralizerMod Zz E (U₁ ⊔ U₂))
    (hJ : Kp ∈ cComp (conjSub g (mcOf T))) : False := by
  classical
  have hK := cK.hKc
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hEp : IsPGroup 2 E := isPGroup_of_isElemAbelian hEab
  have hUKU : U₁ ⊔ U₂ ≤ uOfL22 T M := sup_le cK.hU₁U cK.hU₂U
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKpJ : Kp ≤ conjSub g (mcOf T) := le_of_mem_cComp hJ
  have hKpE : Kp ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact hKpJ.trans (conjSub_le_normalizer hHU)
  obtain ⟨J₀, hJ₀, hKpJ₀⟩ := exists_conj_mem_cComp hJ
  have hZJ₀ : Zz ≤ ⁅uOfL22 T M, J₀⁆ := Setting146.Z_le_commutator_of_mem_cComp S c19 hJ₀
  have hA₁EKp : A₁ ≤ ⁅E, Kp⁆ := by
    rw [hA₁, hE, hKpJ₀, conjSub_commutator]
    exact conjSub_mono g hZJ₀
  have hcommE : ⁅E, Kp⁆ ≤ pCoreOf 2 Kp := by
    rw [Subgroup.commutator_le]
    intro e he k hk
    rw [commutatorElement_def]
    exact comm_mem_pCoreOf_of_mutual hEp hEKp hKpE e he k hk
  have hA₁O : A₁ ≤ pCoreOf 2 Kp := hA₁EKp.trans hcommE
  have hsH : s ∈ mcOf T := hG.1.1 cK.hs
  have hnormKp_K : K ≤ Subgroup.normalizer (Kp : Set G) := by
    have h1 : cCompSpan (mcOf T) ≤ Subgroup.normalizer (Kp : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_cCompSpan hKp)).mp
        (cComp_normal_span_of_le hKp).2
    exact (le_cCompSpan hK).trans h1
  have hs_Kp : s ∈ Subgroup.normalizer (Kp : Set G) := by
    have h1 : conjSub s Kp ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hKp hsH
    rcases hcomps _ h1 with h | h
    · exfalso
      apply hne
      have : conjSub s⁻¹ (conjSub s Kp) = conjSub s⁻¹ K := by rw [h]
      rw [conjSub_conjSub_inv, conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ cK.hsK)] at this
      exact this
    · exact mem_normalizer_of_conjSub_eq h
  set X₀ : Subgroup G := K ⊔ Subgroup.zpowers s with hX₀
  have hX₀Kp : X₀ ≤ Subgroup.normalizer (Kp : Set G) :=
    sup_le hnormKp_K (Subgroup.zpowers_le.mpr hs_Kp)
  have hX₀O : X₀ ≤ Subgroup.normalizer (pCoreOf 2 Kp : Set G) := fun x hx =>
    normalizer_le_normalizer_pCoreOf 2 Kp (hX₀Kp hx)
  have hKZ : K ≤ Subgroup.normalizer (Zz : Set G) := fun k hk => by
    rw [S.normalizer_Z]; exact hKH hk
  have hX₀Z : X₀ ≤ Subgroup.normalizer (Zz : Set G) :=
    sup_le hKZ (Subgroup.zpowers_le.mpr cK.hsZ)
  have hX₀UK : X₀ ≤ Subgroup.normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact cK.mem_normalizer_sup (Subgroup.le_normalizer hk) (hHU (hKH hk)) (hKZ hk)
    · exact cK.mem_normalizer_sup cK.hsK (hHU hsH) cK.hsZ
  set W : Subgroup G := conjClosure A₁ X₀ with hW
  have hWO : W ≤ pCoreOf 2 Kp := conjClosure_le fun x hx a ha =>
    (Subgroup.mem_normalizer_iff.mp (hX₀O hx) a).mp (hA₁O ha)
  have hWUK : W ≤ U₁ ⊔ U₂ := conjClosure_le fun x hx a ha =>
    (Subgroup.mem_normalizer_iff.mp (hX₀UK hx) a).mp (hA₁UK ha)
  have hX₀W : X₀ ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure A₁ X₀
  have hX₀WZ : X₀ ≤ Subgroup.normalizer ((W ⊔ Zz : Subgroup G) : Set G) := by
    intro x hx
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_sup, conjSub_eq_of_mem_normalizer (hX₀W hx),
      conjSub_eq_of_mem_normalizer (hX₀Z hx)]
  have hcases := cK.submodule_cases S (W := W ⊔ Zz) le_sup_right (sup_le hWUK (cK.hSec.le.trans le_sup_left))
    (le_sup_left.trans hX₀WZ)
  have hsWZ : s ∈ Subgroup.normalizer ((W ⊔ Zz : Subgroup G) : Set G) :=
    hX₀WZ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hA₁W : A₁ ≤ W := le_conjClosure A₁ X₀
  have hWZ : W ⊔ Zz = U₁ ⊔ U₂ := by
    rcases hcases with h | h | h | h
    · exfalso
      have hA₁Z' : A₁ ≤ Zz := hA₁W.trans (le_sup_left.trans h.le)
      have : A₁ = ⊥ := by
        rw [← hA₁Z]; exact (le_inf le_rfl hA₁Z').antisymm inf_le_left
      rw [this] at hA₁c
      simp at hA₁c
    · exfalso
      have := conjSub_eq_of_mem_normalizer hsWZ
      rw [h] at this
      exact cK.conjSub_ne this
    · exfalso
      have h1 := conjSub_eq_of_mem_normalizer hsWZ
      rw [h] at h1
      have h2 : conjSub s U₂ = conjSub s U₁ := by rw [h1, ← cK.hU₂]
      exact cK.ne_U₂ ((conjSub_inj s).mp h2).symm
    · exact h
  have h91 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2.toHypF91
  have hUQ : uOfL22 T M ≤ pCoreOf 2 (mcOf T) := h91.conjClosure_Vp_le_pCoreOf
  have hUKp : uOfL22 T M ≤ Subgroup.normalizer (Kp : Set G) :=
    hUQ.trans (P134.pCoreOf_le_normalizer_of_mem_cComp hKp)
  have hKpU : Kp ≤ Subgroup.normalizer (uOfL22 T M : Set G) := hKpH.trans hHU
  have hZKp : Zz ≤ pCoreOf 2 Kp := by
    have h1 := Setting146.Z_le_commutator_of_mem_cComp S c19 hKp
    refine h1.trans ?_
    rw [Subgroup.commutator_le]
    intro u hu k hk
    rw [commutatorElement_def]
    exact comm_mem_pCoreOf_of_mutual hUp hUKp hKpU u hu k hk
  have hUKO : U₁ ⊔ U₂ ≤ pCoreOf 2 Kp := by
    rw [← hWZ]; exact sup_le hWO hZKp
  have hQg : pCoreOf 2 Kp ≤ pCoreOf 2 (conjSub g (mcOf T)) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hJ)
  have hcomm : ∀ w ∈ U₁ ⊔ U₂, ∀ e ∈ E, w * e * w⁻¹ * e⁻¹ ∈ A₁ := by
    intro w hw e he
    have hwQ : w ∈ pCoreOf 2 (conjSub g (mcOf T)) := hQg (hUKO hw)
    rw [pCoreOf_conjSub, mem_conjSub] at hwQ
    have heU : g⁻¹ * e * g ∈ uOfL22 T M := by rw [hE] at he; exact mem_conjSub.mp he
    have h1 := S.comm_mem_Z hG heU hwQ
    rw [hA₁, mem_conjSub]
    have e1 : g⁻¹ * (w * e * w⁻¹ * e⁻¹) * g =
        (g⁻¹ * w * g) * (g⁻¹ * e * g) * (g⁻¹ * w * g)⁻¹ * (g⁻¹ * e * g)⁻¹ := by group
    rw [e1]; exact h1
  have hA₁E : A₁ ≤ E := by
    rw [hA₁, hE]; exact conjSub_mono g (Z_le_conjClosure_VZ T M (mcOf T))
  have hUKc : ∀ x ∈ U₁ ⊔ U₂, ∀ y ∈ U₁ ⊔ U₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hUKU hx) (hUKU hy)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => isElemAbelian_comm hEab hx hy
  have hpair := relIndex_eq_of_commutator_le (X := U₁ ⊔ U₂) (Y := E) (C := A₁) hEab hA₁c
    (Subgroup.commutator_le.mpr fun w hw e he => by
      rw [commutatorElement_def]; exact hcomm w hw e he)
    (fun a ha => Subgroup.mem_centralizer_iff.mpr fun y hy => (hUKc a (hA₁UK ha) y hy).symm)
    (fun a ha => Subgroup.mem_centralizer_iff.mpr fun y hy => (hEc a (hA₁E ha) y hy).symm)
  have hc1 : centralizerMod Zz (U₁ ⊔ U₂) E = (U₁ ⊔ U₂) ⊓ Subgroup.centralizer (E : Set G) := by
    ext u
    constructor
    · rintro ⟨hu, -, h⟩
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
      have h1 := h e he
      have h2 : u * e * u⁻¹ * e⁻¹ ∈ A₁ := hcomm u hu e he
      have h3 : u * e * u⁻¹ * e⁻¹ ∈ A₁ ⊓ Zz := ⟨h2, h1⟩
      rw [hA₁Z, Subgroup.mem_bot] at h3
      calc e * u = (u * e * u⁻¹ * e⁻¹) * (e * u) := by rw [h3]; group
        _ = u * e := by group
    · rintro ⟨hu, hc⟩
      refine ⟨hu, hUN (hUKU hu), fun e he => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hc e he
      have e1 : u * e * u⁻¹ * e⁻¹ = 1 := by
        calc u * e * u⁻¹ * e⁻¹ = (e * u) * u⁻¹ * e⁻¹ := by rw [this]
          _ = 1 := by group
      rw [e1]; exact Subgroup.one_mem _
  have hc2 : centralizerMod Zz E (U₁ ⊔ U₂) = E ⊓ Subgroup.centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    ext e
    constructor
    · rintro ⟨he, -, h⟩
      refine ⟨he, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have h1 := h u hu
      have h2 : u * e * u⁻¹ * e⁻¹ ∈ A₁ := hcomm u hu e he
      have h2' : e * u * e⁻¹ * u⁻¹ ∈ A₁ := by
        have : e * u * e⁻¹ * u⁻¹ = (u * e * u⁻¹ * e⁻¹)⁻¹ := by group
        rw [this]; exact A₁.inv_mem h2
      have h3 : e * u * e⁻¹ * u⁻¹ ∈ A₁ ⊓ Zz := ⟨h2', h1⟩
      rw [hA₁Z, Subgroup.mem_bot] at h3
      calc u * e = (e * u * e⁻¹ * u⁻¹) * (u * e) := by rw [h3]; group
        _ = e * u := by group
    · rintro ⟨he, hc⟩
      refine ⟨he, ?_, fun u hu => ?_⟩
      · rw [S.normalizer_Z]; exact hEH he
      · have := Subgroup.mem_centralizer_iff.mp hc u hu
        have e1 : e * u * e⁻¹ * u⁻¹ = 1 := by
          calc e * u * e⁻¹ * u⁻¹ = (u * e) * e⁻¹ * u⁻¹ := by rw [this]
            _ = 1 := by group
        rw [e1]; exact Subgroup.one_mem _
  have hnff := cK.nff S hEH hEK hEab hnt
  rw [hc1] at hnff
  rw [hc2] at hnff
  unfold mIdx at hnff
  rw [hpair] at hnff
  omega

end Engine

end CFSG.Quasithin.ThreeD
