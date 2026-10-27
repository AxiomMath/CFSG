module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace RFAux

variable {G : Type u} [Group G]

theorem conj_mem_sectionCentralizer {V U : Subgroup G} {g x : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hx : x ∈ sectionCentralizer V U) : g * x * g⁻¹ ∈ sectionCentralizer V U := by
  obtain ⟨hxV, hxU, hcomm⟩ := hx
  refine ⟨mul_mem (mul_mem hgV hxV) (inv_mem hgV), mul_mem (mul_mem hgU hxU) (inv_mem hgU),
    fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgU) y).mp hy
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hgV _).mp (hcomm _ hy')
  have e : ⁅g * x * g⁻¹, y⁆ = g * ⁅x, g⁻¹ * y * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem mem_normalizer_sectionCentralizer {V U : Subgroup G} {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer (sectionCentralizer V U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_sectionCentralizer hgV hgU hx, fun hx => ?_⟩
  have := conj_mem_sectionCentralizer (inv_mem hgV) (inv_mem hgU) hx
  simpa [mul_assoc] using this


theorem exists_pairC {D A U V : Subgroup G}
    (hAU : Admits A U) (hAD : Admits A D)
    (hch : IsChiefFactorOf (U ⊔ D ⊔ A) U V)
    (hnab : ¬ ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ V) :
    ∃ C : Subgroup G, C ≤ U ⊔ D ∧ Admits (U ⊔ D ⊔ A) C ∧ C ⊓ U = V ∧
      IsChiefFactorOf (U ⊔ C ⊔ D ⊔ A) (U ⊔ C) C ∧
      secCenIn (U ⊔ C ⊔ D) (U ⊔ C) C = C := by
  obtain ⟨⟨hVT, hTV⟩, ⟨hUT, hTU⟩, hVU, hmin⟩ := hch
  set T : Subgroup G := U ⊔ D ⊔ A with hT
  have hDT : D ≤ T := le_sup_right.trans le_sup_left
  have hAT : A ≤ T := le_sup_right
  have hUD : U ⊔ D ≤ T := le_sup_left
  set sc : Subgroup G := sectionCentralizer V U with hsc
  set C : Subgroup G := (U ⊔ D) ⊓ sc with hC
  have hCUD : C ≤ U ⊔ D := inf_le_left
  have hCT : C ≤ T := hCUD.trans hUD
  have hscN : ∀ g ∈ T, g ∈ Subgroup.normalizer (sc : Set G) := fun g hg =>
    mem_normalizer_sectionCentralizer (hTV hg) (hTU hg)
  have hUDN : T ≤ Subgroup.normalizer ((U ⊔ D : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (Admits.sup hAU hAD)
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hUDN hg, hscN g hg⟩
  have hZ : U ⊓ sc = V := by
    have hZn : T ≤ Subgroup.normalizer ((U ⊓ sc : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hTU hg, hscN g hg⟩
    have hVZ : V ≤ U ⊓ sc := by
      refine le_inf hVU.le fun x hx =>
        ⟨hTV (hUT (hVU.le hx)), hTU (hUT (hVU.le hx)), fun y hy => ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hTV (hUT hy)) x⁻¹).mp (inv_mem hx)
      have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hx (by simpa using h1)
    rcases hmin (U ⊓ sc) ⟨inf_le_left.trans hUT, hZn⟩ hVZ inf_le_left with h | h
    · exact h
    · exfalso
      apply hnab
      intro x hx y hy
      have : x ∈ U ⊓ sc := by rw [h]; exact hx
      exact this.2.2.2 y hy
  have hCU : C ⊓ U = V := by
    apply le_antisymm
    · rintro x ⟨⟨_, hxsc⟩, hxU⟩
      rw [← hZ]
      exact ⟨hxU, hxsc⟩
    · refine le_inf ?_ hVU.le
      calc V = U ⊓ sc := hZ.symm
        _ ≤ C := inf_le_inf_right sc le_sup_left
  have hVC : V ≤ C := hCU ▸ inf_le_left
  have hCnorm : Admits T C := hCN
  have hUCT : U ⊔ C ≤ T := sup_le hUT hCT
  have hTeq : U ⊔ C ⊔ D ⊔ A = T := by
    apply le_antisymm
    · exact sup_le (sup_le hUCT hDT) hAT
    · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right
  have hchief : IsChiefFactorOf (U ⊔ C ⊔ D ⊔ A) (U ⊔ C) C := by
    rw [hTeq]
    refine ⟨⟨hCT, hCN⟩, ⟨hUCT, Admits.sup hTU hCnorm⟩, ?_, ?_⟩
    · refine lt_of_le_of_ne le_sup_right fun heq => ?_
      have hUC : U ≤ C := heq ▸ le_sup_left
      have hUV : U ≤ V := hCU ▸ le_inf hUC le_rfl
      exact absurd hUV (not_le_of_gt hVU)
    · intro K hK hCK hKUC
      obtain ⟨hKT, hTK⟩ := hK
      have hKUn : T ≤ Subgroup.normalizer ((K ⊓ U : Subgroup G) : Set G) := fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK hg, hTU hg⟩
      have hVKU : V ≤ K ⊓ U := hCU ▸ inf_le_inf_right U hCK
      rcases hmin (K ⊓ U) ⟨inf_le_right.trans hUT, hKUn⟩ hVKU inf_le_right with h | h
      · left
        refine le_antisymm (fun k hk => ?_) hCK
        have hk' : k ∈ ((U ⊔ C : Subgroup G) : Set G) := hKUC hk
        rw [Subgroup.coe_mul_of_left_le_normalizer_right U C (hUT.trans hCN)] at hk'
        obtain ⟨u, hu, c, hc, rfl⟩ := hk'
        have huK : u ∈ K := by
          have := mul_mem hk (inv_mem (hCK hc))
          simpa using this
        have huV : u ∈ V := by
          have : u ∈ K ⊓ U := ⟨huK, hu⟩
          rwa [h] at this
        exact mul_mem (hVC huV) hc
      · right
        have hUK : U ≤ K := by
          calc U = K ⊓ U := h.symm
            _ ≤ K := inf_le_left
        exact le_antisymm hKUC (sup_le hUK hCK)
  have hsec : secCenIn (U ⊔ C ⊔ D) (U ⊔ C) C = C := by
    have hUCD : U ⊔ C ⊔ D ≤ U ⊔ D := sup_le (sup_le le_sup_left hCUD) le_sup_right
    apply le_antisymm
    · intro g hg
      obtain ⟨hgH, hgsc⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨-, -, hgcomm⟩ := hgsc
      have hgUD : g ∈ U ⊔ D := hUCD hgH
      refine Subgroup.mem_inf.mpr ⟨hgUD, ⟨hTV (hUD hgUD), hTU (hUD hgUD), fun y hy => ?_⟩⟩
      have h1 : ⁅g, y⁆ ∈ C := hgcomm y ((le_sup_left : U ≤ U ⊔ C) hy)
      have h2 : ⁅g, y⁆ ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (hTU (hUD hgUD)) y).mp hy
        exact mul_mem this (inv_mem hy)
      have h3 : ⁅g, y⁆ ∈ C ⊓ U := ⟨h1, h2⟩
      rwa [hCU] at h3
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨((le_sup_right : C ≤ U ⊔ C).trans le_sup_left) hx, ?_⟩
      refine ⟨Subgroup.le_normalizer hx,
        Subgroup.le_normalizer (((le_sup_right : C ≤ U ⊔ C) hx : x ∈ U ⊔ C)),
        fun y hy => ?_⟩
      have hyN := hCN (hUCT hy)
      have h1 := (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (inv_mem hx)
      have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hx (by simpa using h1)
  exact ⟨C, hCUD, hCnorm, hCU, hchief, hsec⟩


section Pair

variable [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_pair_above_perfect (hθ : NearFunctor p A θ) {X U N : Subgroup G}
    (hX : X ∈ mtil p A θ) (hU : U ≤ X) (hUadm : Admits (dsub A θ ⊔ A) U)
    (hUp : Group.IsPerfect U) (hNU : N < U) (hNn : IsNormalIn N U)
    (hNadm : Admits (dsub A θ ⊔ A) N) :
    ∃ P ∈ pairsP p A θ, U ≤ P.1 ∧ P.1 ≤ X := by
  classical
  set D : Subgroup G := dsub A θ with hD
  set S : Set (Subgroup G) :=
    {V | N ≤ V ∧ V < U ∧ IsNormalIn V U ∧ Admits (D ⊔ A) V} with hS
  have hNS : N ∈ S := ⟨le_rfl, hNU, hNn, hNadm⟩
  obtain ⟨V, hVS, hVmax⟩ := (Set.toFinite S).exists_maximal ⟨N, hNS⟩
  obtain ⟨hNV, hVU, hVnU, hVadm⟩ := hVS
  have hDT : D ≤ U ⊔ D ⊔ A := le_sup_right.trans le_sup_left
  have hAT : A ≤ U ⊔ D ⊔ A := le_sup_right
  have hUT : U ≤ U ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hDAT : D ⊔ A ≤ U ⊔ D ⊔ A := sup_le hDT hAT
  have hTU : U ⊔ D ⊔ A ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (le_sup_left.trans hUadm)) (le_sup_right.trans hUadm)
  have hTV : U ⊔ D ⊔ A ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (sup_le hVnU.2 (le_sup_left.trans hVadm)) (le_sup_right.trans hVadm)
  have hch : IsChiefFactorOf (U ⊔ D ⊔ A) U V := by
    refine ⟨⟨hVnU.1.trans hUT, hTV⟩, ⟨hUT, hTU⟩, hVU, fun K hK hVK hKU => ?_⟩
    by_cases hKeq : K = U
    · exact Or.inr hKeq
    · left
      have hKlt : K < U := lt_of_le_of_ne hKU hKeq
      have hKS : K ∈ S := ⟨hNV.trans hVK, hKlt, ⟨hKU, hUT.trans hK.2⟩, hDAT.trans hK.2⟩
      exact le_antisymm (hVmax hKS hVK) hVK
  have hnab : ¬ ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ V := by
    intro hall
    have h1 : ⁅U, U⁆ ≤ V := Subgroup.commutator_le.mpr hall
    rw [Subgroup.isPerfect_iff.mp hUp] at h1
    exact absurd h1 (not_le_of_gt hVU)
  obtain ⟨C, hCUD, hCnorm, -, hchiefC, hsecC⟩ :=
    exists_pairC (le_sup_right.trans hUadm) (admits_dsub hθ) hch hnab
  have hDX : D ≤ X := hX.2
  have hCX : C ≤ X := hCUD.trans (sup_le hU hDX)
  have hUCX : U ⊔ C ≤ X := sup_le hU hCX
  have hCadm : Admits (D ⊔ A) C := hCnorm.mono_left hDAT
  refine ⟨(U ⊔ C, C), ⟨mem_mhat_of_le_mtil hθ.prime hX hUCX (Admits.sup hUadm hCadm),
    mem_mhat_of_le_mtil hθ.prime hX hCX hCadm, hchiefC, hsecC⟩, le_sup_left, hUCX⟩

end Pair

end RFAux

end CFSG.SignalizerFunctorTheorem.McBride.Near
