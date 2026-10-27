module

public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.S153D52
public import CFSG.Quasithin.EmptyFaithful.SBd2A5
public import CFSG.Quasithin.EmptyFaithful.SBd2Borel

public section

namespace CFSG.Quasithin

namespace SBd2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 CFSG.LieType.BorelTits
  CFSG.Quasithin.S1417
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem commutator_le_blockU {U L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hU2 : IsPGroup 2 ↥U) : ⁅U, L⁆ ≤ blockU L := by
  set A : Subgroup G := ⁅U, L⁆ with hA
  have hAU : A ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
  have hAL : A ≤ L := by
    rw [hA, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hUL
  have hLA : L ≤ Subgroup.normalizer (A : Set G) := Subgroup.normalizer_commutator_ge_right U L
  have hAQ : A ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 hAL hLA (hU2.to_le hAU)
  set N : Subgroup G := ⁅A, L⁆ with hN
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_right A L
  have hUN : U ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    S153H.mem_normalizer_commutator (Subgroup.normalizer_commutator_ge_left U L hg) (hUL hg)
  have h1 : ⁅⁅L, U⁆, L⁆ ≤ N := by
    rw [Subgroup.commutator_comm L U]
  have h2 : ⁅⁅U, L⁆, L⁆ ≤ N := le_rfl
  have h3 := S153D.commutator_commutator_le_of_rotate hLN hLN hUN h1 h2
  rw [hL, Subgroup.commutator_comm L U] at h3
  exact (h3.trans (Subgroup.commutator_mono hAQ le_rfl))

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_not_commute_V₂ (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    ∀ v ∈ V₂, v ≠ 1 →
      ∃ y ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)), y * v * y⁻¹ ≠ v := by
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, y, hy, hyY, hyL, hyord⟩ := h.exists_mem_Yplus_acts h113 D
  set x' := convI hV ⟨y, hy⟩ with hx'
  have hx'odd : Odd (orderOf x') := by rw [hyord]; decide
  have hx'1 : x' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyord
    exact absurd hyord (by norm_num)
  have hfpf : ∀ u ∈ commV L₂, u ≠ 1 → x' u ≠ u := fun u hu hu1 hxu =>
    hx'1 (eq_one_of_odd_of_fixed hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hyL hx'odd hu hu1
      hxu)
  intro u hu hu1
  refine ⟨y, hyY, fun hyu => ?_⟩
  rw [hV₂] at hu
  obtain ⟨w, hw, rfl⟩ := (mem_map_inclMod_iff hV).1 hu
  refine hfpf w hw (fun hw1 => hu1 (by rw [hw1]; rfl)) (IntMod.val_injective ?_)
  rw [hx', convI_apply_val]
  exact hyu

theorem input30NoA5_proved (h113 : StageLemma14113) : Input30NoA5 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hB hBl hA5
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have D : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
    c25.facts.case_two.2
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c25.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hLM : ¬ L ≤ M := fun h => hLn (le_inf h hLle)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hYI : Yp ≤ I := hYL.trans hLle
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hIU
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hZ : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
    unfold quasithinOmegaOneCenter
    refine Subgroup.closure_mono fun z hz => ?_
    have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
    exact ⟨⟨S153D.VZ_le_Sgp153 hyp hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩
  obtain ⟨hUOC, hUel, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl c25.ctx.charTwo hZ
  have hUO : UI153 T I ≤ pCoreOf 2 I := hUOC.trans inf_le_left
  have hOCU : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUOC.trans inf_le_right)
  have hU2 : IsPGroup 2 ↥(UI153 T I) := (pCoreOf_isPGroup 2 I).to_le hUO
  have hUL : UI153 T I ≤ Subgroup.normalizer (L : Set G) := (hUO.trans (pCoreOf_le 2 I)).trans hIL
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := hA5
  have hOLI : pCoreOf 2 L ≤ pCoreOf 2 I :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hLI)
  have hαU : ∀ ℓ : ↥L, α ℓ = 1 → (ℓ : G) ∈ Subgroup.centralizer (UI153 T I : Set G) := by
    intro ℓ h1
    have hmem : ℓ ∈ CFSG.pCore 2 ↥L := by rw [← hαk]; exact h1
    have hmem' : (ℓ : G) ∈ pCoreOf 2 L := by
      exact (Subgroup.mem_map_iff_mem L.subtype_injective).mpr hmem
    exact hOCU (hOLI hmem')
  have hcent : ∀ ℓ : ↥L, (ℓ : G) ∈ Subgroup.centralizer (UI153 T I : Set G) → (ℓ : G) ∈ M :=
    fun ℓ h => (hF.cent_le ⟨hLle ℓ.2, h⟩).1
  obtain ⟨P, hP, hBP⟩ := hB
  obtain ⟨Q, hQ4, hQN⟩ := exists_sylow_of_borel hLU α hαs hαU hcent hLM hP hBP
  have hcomm : ⁅V₂, Yp⁆ = V₂ := by
    rw [hYp]
    exact hh.commutator_V₂_Yplus h113 D
  have hV₂UI : V₂ ≤ UI153 T I := by
    have := hh.V₂_le_conjClosure_Yplus h113 D
    rw [← hYp] at this
    exact this.trans (conjClosure_mono le_rfl hYI)
  have hV₂U : V₂ ≤ blockU L :=
    calc V₂ = ⁅V₂, Yp⁆ := hcomm.symm
      _ ≤ ⁅UI153 T I, L⁆ := Subgroup.commutator_mono hV₂UI hYL
      _ ≤ blockU L := commutator_le_blockU hLperf hLU hUL hU2
  have hYpM : Yp ≤ M ⊓ Subgroup.centralizer (V₁ : Set G) := by
    rw [hYp]
    exact (oTwoUpper_le _).trans (inf_le_inf_right _ (Y153_le Mc M))
  have hV₂eq : ⁅VZ T M, Yp⁆ = V₂ := by
    apply le_antisymm
    · calc ⁅VZ T M, Yp⁆ ≤ ⁅VZ T M, M ⊓ Subgroup.centralizer (V₁ : Set G)⁆ :=
            Subgroup.commutator_mono le_rfl hYpM
        _ = V₂ := D.comm₂
    · calc V₂ = ⁅V₂, Yp⁆ := hcomm.symm
        _ ≤ ⁅VZ T M, Yp⁆ := Subgroup.commutator_mono D.le₂ le_rfl
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := hh.le_normalizer
  have hMIYp : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hF.norm_eq]
    exact inf_le_right
  have hMN : ∀ m ∈ M ⊓ I, m ∈ Subgroup.normalizer (V₂ : Set G) := fun m hm => by
    rw [← hV₂eq]
    exact S153H.mem_normalizer_commutator (hMV hm.1) (hMIYp hm)
  by_cases hex : ∃ v ∈ V₂, v ≠ 1 ∧ v ∈ blockZ L
  ·
    obtain ⟨v, hv, hv1, hvZ⟩ := hex
    obtain ⟨y, hy, hyne⟩ := exists_not_commute_V₂ h113 hh D v hv hv1
    apply hyne
    have hyL : y ∈ L := hYL (by rw [hYp]; exact hy)
    have := Subgroup.mem_centralizer_iff.mp hvZ.2 y hyL
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  · push Not at hex
    let bv : ↥(blockU L) → (Fin 5 → ZMod 2) := fun u =>
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
    have bv_mul : ∀ u u' : ↥(blockU L), bv (u * u') = bv u + bv u' := fun u u' => by
      simp [bv]
    have bv_one : bv 1 = 0 := by simp [bv]
    have bv_even : ∀ u : ↥(blockU L), isEven (bv u) := fun u =>
      (Multiplicative.toAdd (β u)).2
    have bv_equiv : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
        bv v = pact (α ℓ : Equiv.Perm (Fin 5)) (bv u) := fun ℓ u v h =>
      funext fun i => hβe ℓ u v h i
    have bv_ne : ∀ u : ↥(blockU L), (u : G) ∈ V₂ → (u : G) ≠ 1 → bv u ≠ 0 := by
      intro u hu hu1 h0
      apply hex _ hu hu1
      have : β u = 1 := by
        have h1 : Multiplicative.toAdd (β u) = 0 := Subtype.ext h0
        exact Multiplicative.toAdd.injective h1
      have h2 : u ∈ β.ker := this
      rw [hβk] at h2
      exact Subgroup.mem_subgroupOf.mp h2
    have h4 : ∀ z : Fin 5 → ZMod 2, z + z = 0 := fun z => by
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize z i = a
      revert a
      decide
    have bv_inj : ∀ u u' : ↥(blockU L), (u : G) ∈ V₂ → (u' : G) ∈ V₂ → bv u = bv u' → u = u' := by
      intro u u' hu hu' h
      by_contra hne
      have h2 : bv (u⁻¹) = bv u := by
        have h3 : bv (u⁻¹) + bv u = 0 := by rw [← bv_mul, inv_mul_cancel, bv_one]
        have := congrArg (· + bv u) h3
        simp only [add_assoc, h4, add_zero, zero_add] at this
        exact this
      have h1 : bv (u⁻¹ * u') = 0 := by rw [bv_mul, h2, h, h4]
      have hcoe : ((u⁻¹ * u' : ↥(blockU L)) : G) = (u : G)⁻¹ * u' := rfl
      refine bv_ne (u⁻¹ * u') ?_ ?_ h1
      · rw [hcoe]
        exact V₂.mul_mem (V₂.inv_mem hu) hu'
      · rw [hcoe]
        intro h1
        exact hne (Subtype.ext (inv_mul_eq_one.mp h1))
    have hV₂4 : Nat.card ↥V₂ = 4 := D.card₂
    have hsq : ∀ v ∈ V₂, v * v = 1 := fun v hv => by
      have := hh.elemAbelian.2 v (D.le₂ hv)
      simpa [pow_two] using this
    obtain ⟨u₁, hu₁, hu₁1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : V₂ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hno x hx)
      rw [hbot, Subgroup.card_bot] at hV₂4
      omega
    obtain ⟨u₂, hu₂, hu₂n⟩ : ∃ u ∈ V₂, u ∉ Subgroup.zpowers u₁ := by
      by_contra hno
      push Not at hno
      have hle : V₂ ≤ Subgroup.zpowers u₁ := hno
      have h1 : Nat.card ↥(Subgroup.zpowers u₁) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq u₁ hu₁))
      have h2 := Subgroup.card_le_of_le hle
      omega
    have h21 : u₂ ≠ 1 := fun h => hu₂n (h ▸ Subgroup.one_mem _)
    have h12 : u₁ ≠ u₂ := fun h => hu₂n (h ▸ Subgroup.mem_zpowers u₁)
    have h1_2 : u₁ * u₂ ≠ 1 := fun h => hu₂n (by
      have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u₁))
    have h1_12 : u₁ ≠ u₁ * u₂ := fun h => h21 (by simpa using h)
    have h2_12 : u₂ ≠ u₁ * u₂ := fun h => hu₁1 (by simpa using h)
    have hS4 : ∀ v ∈ V₂, v = 1 ∨ v = u₁ ∨ v = u₂ ∨ v = u₁ * u₂ := by
      have hsub : ({1, u₁, u₂, u₁ * u₂} : Set G) ⊆ (V₂ : Set G) := by
        intro g hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact V₂.one_mem
        · exact hu₁
        · exact hu₂
        · exact V₂.mul_mem hu₁ hu₂
      have hcard : ({1, u₁, u₂, u₁ * u₂} : Set G).ncard = 4 := by
        have e1 : ({u₂, u₁ * u₂} : Set G).ncard = 2 := Set.ncard_pair h2_12
        have e2 : ({u₁, u₂, u₁ * u₂} : Set G).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem, e1]
          simp [h12, h1_12]
        rw [Set.ncard_insert_of_notMem, e2]
        simp [hu₁1.symm, h21.symm, h1_2.symm]
      have hV₂ncard : (V₂ : Set G).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hV₂4
      have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hV₂ncard])
      intro v hv
      have : v ∈ ({1, u₁, u₂, u₁ * u₂} : Set G) := by rw [heq]; exact hv
      simpa using this
    let U₁ : ↥(blockU L) := ⟨u₁, hV₂U hu₁⟩
    let U₂ : ↥(blockU L) := ⟨u₂, hV₂U hu₂⟩
    have hx0 : bv U₁ ≠ 0 := bv_ne U₁ hu₁ hu₁1
    have hy0 : bv U₂ ≠ 0 := bv_ne U₂ hu₂ h21
    have hxy : bv U₁ ≠ bv U₂ := fun h => h12 (congrArg Subtype.val (bv_inj U₁ U₂ hu₁ hu₂ h))
    refine no_invariant_pair hQ4 (bv_even U₁) (bv_even U₂) hx0 hy0 hxy ?_
    intro σ hσ
    obtain ⟨ℓ, hℓM, hℓσ⟩ := hQN σ hσ
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (V₂ : Set G) := hMN _ ⟨hℓM, hLle ℓ.2⟩
    have act : ∀ U : ↥(blockU L), (U : G) ∈ V₂ → bv U ≠ 0 →
        (pact (σ : Equiv.Perm (Fin 5)) (bv U) = bv U₁ ∨ pact (σ : Equiv.Perm (Fin 5)) (bv U) = bv U₂ ∨
          pact (σ : Equiv.Perm (Fin 5)) (bv U) = bv U₁ + bv U₂) := by
      intro U hU hU0
      have hv : (ℓ : G) * (U : G) * (ℓ : G)⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hℓN _).mp hU
      let U' : ↥(blockU L) := ⟨(ℓ : G) * (U : G) * (ℓ : G)⁻¹, hV₂U hv⟩
      have hbv : bv U' = pact (σ : Equiv.Perm (Fin 5)) (bv U) := by
        rw [← hℓσ]
        exact bv_equiv ℓ U U' rfl
      rcases hS4 _ hv with h | h | h | h
      · exfalso
        have : U' = 1 := Subtype.ext h
        rw [this, bv_one] at hbv
        exact hU0 (pact_injective_vec (σ : Equiv.Perm (Fin 5)) (by rw [← hbv, pact_zero_vec]))
      · left
        have : U' = U₁ := Subtype.ext h
        rw [← hbv, this]
      · right; left
        have : U' = U₂ := Subtype.ext h
        rw [← hbv, this]
      · right; right
        have : U' = U₁ * U₂ := Subtype.ext h
        rw [← hbv, this, bv_mul]
    exact ⟨act U₁ hu₁ hx0, act U₂ hu₂ hy0⟩

end Context

end SBd2

end CFSG.Quasithin
