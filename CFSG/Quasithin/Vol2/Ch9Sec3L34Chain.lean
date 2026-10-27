module

public import CFSG.Quasithin.Vol2.Ch3yChain

public section

namespace CFSG.Quasithin.H13.Ch9.L34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F D15Proof

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_conj_pow_le {p r : ℕ} {G₁ V R₂ : Subgroup G}
    (hq : ∀ E₀ : Subgroup G, E₀ ≤ G₁ → IsElemAbelian 2 E₀ → ⁅⁅V, E₀⁆, E₀⁆ = ⊥ →
      ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ p ≤
        ((Subgroup.centralizer (E₀ : Set G)).relIndex V) ^ r)
    (hR₂G₁ : R₂ ≤ G₁) {g : G} (hg : g ∈ Subgroup.normalizer (R₂ : Set G)) {E : Subgroup G}
    (hER₂ : E ≤ R₂) (hE : IsElemAbelian 2 E) (hquad : ⁅⁅cjSub g V, E⁆, E⁆ = ⊥)
    (hnc : ¬ E ≤ Subgroup.centralizer (cjSub g V : Set G)) :
    ((Subgroup.centralizer (cjSub g V : Set G)).relIndex E) ^ p ≤
      ((Subgroup.centralizer (E : Set G)).relIndex (cjSub g V)) ^ r := by
  have hE₀R₂ : cjSub g⁻¹ E ≤ R₂ := cjSub_le (Subgroup.inv_mem _ hg) hER₂
  have hquad₀ : ⁅⁅V, cjSub g⁻¹ E⁆, cjSub g⁻¹ E⁆ = ⊥ := by
    have e : (⁅⁅cjSub g V, E⁆, E⁆).map (MulAut.conj g⁻¹).toMonoidHom =
        ⁅⁅V, cjSub g⁻¹ E⁆, cjSub g⁻¹ E⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
      have h1 : (cjSub g V).map (MulAut.conj g⁻¹).toMonoidHom = V := cjSub_inv_cjSub g V
      rw [h1]
      rfl
    rw [← e, hquad, Subgroup.map_bot]
  have hnc₀ : ¬ cjSub g⁻¹ E ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hnc
    have := cjSub_mono (g := g) hle
    rwa [cjSub_cjSub_inv, cjSub_centralizer] at this
  have h := hq _ (hE₀R₂.trans hR₂G₁) (isElemAbelian_cjSub hE) hquad₀ hnc₀
  have r1 : (cjSub g (Subgroup.centralizer (V : Set G))).relIndex (cjSub g (cjSub g⁻¹ E)) =
      (Subgroup.centralizer (V : Set G)).relIndex (cjSub g⁻¹ E) :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have r2 : (cjSub g (Subgroup.centralizer (cjSub g⁻¹ E : Set G))).relIndex (cjSub g V) =
      (Subgroup.centralizer (cjSub g⁻¹ E : Set G)).relIndex V :=
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  rw [cjSub_centralizer, cjSub_cjSub_inv] at r1 r2
  rw [r1, r2]
  exact h

theorem pow_relIndex_le_nonstrict {p r : ℕ} {V H B : Subgroup G}
    (hQ : ∀ h ∈ H, ∀ E : Subgroup G, E ≤ B → ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) →
      ((Subgroup.centralizer (cjSub h V : Set G)).relIndex E) ^ p ≤
        ((Subgroup.centralizer (E : Set G)).relIndex (cjSub h V)) ^ r) :
    ∀ E : Subgroup G, E ≤ B →
      ((Subgroup.centralizer (conjClosure V H : Set G)).relIndex E) ^ p ≤
        ((Subgroup.centralizer (E : Set G)).relIndex (conjClosure V H)) ^ r := by
  set U := conjClosure V H with hUdef
  intro E
  induction E using WellFoundedLT.induction with
  | _ E ih =>
    intro hEB
    by_cases hEU : E ≤ Subgroup.centralizer (U : Set G)
    · rw [Subgroup.relIndex_eq_one.mpr hEU, one_pow]
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Subgroup.index_ne_zero_of_finite)
    obtain ⟨h, hh, hEW⟩ : ∃ h ∈ H, ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) := by
      by_contra hall
      push Not at hall
      exact hEU (le_centralizer_conjClosure_of_forall hall)
    set W := cjSub h V with hWdef
    set E' := Subgroup.centralizer (W : Set G) ⊓ E with hE'def
    have hWU : W ≤ U := cjSub_le_conjClosure hh
    have hE'E : E' ≤ E := inf_le_right
    have hE'lt : E' < E := lt_of_le_of_ne hE'E fun he => hEW (he ▸ inf_le_left)
    have ih1 := ih E' hE'lt (hE'E.trans hEB)
    have hq := hQ h hh E hEB hEW
    obtain ⟨e1, e2⟩ := Ch3y.relIndex_decomp (U := U) (W := W) (E := E) hWU
    rw [e1, mul_pow]
    calc _ ≤ _ := Nat.mul_le_mul ih1 hq
      _ = _ := (mul_pow _ _ r).symm
      _ ≤ _ := Nat.pow_le_pow_left e2 r

theorem le_one_of_chain {a b c u v : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c)
    (hpow : (a ^ 3) ^ c ≤ u) (hi : u ≤ b * a) (hiii : b ^ 4 ≤ v ^ 3) (hiv : v ≤ u) : u ≤ 1 := by
  have h1 : b ^ 4 ≤ b ^ 3 * a ^ 3 := by
    calc b ^ 4 ≤ v ^ 3 := hiii
      _ ≤ u ^ 3 := Nat.pow_le_pow_left hiv 3
      _ ≤ (b * a) ^ 3 := Nat.pow_le_pow_left hi 3
      _ = b ^ 3 * a ^ 3 := mul_pow b a 3
  have hba : b ≤ a ^ 3 := by
    have hb3 : 0 < b ^ 3 := pow_pos hb 3
    have : b ^ 3 * b ≤ b ^ 3 * a ^ 3 := by rw [← pow_succ]; exact h1
    exact Nat.le_of_mul_le_mul_left this hb3
  have ha1 : a = 1 := by
    by_contra hne
    have ha2 : 2 ≤ a := by omega
    have h6 : a ^ 6 ≤ a ^ 4 := by
      calc a ^ 6 = (a ^ 3) ^ 2 := by rw [← pow_mul]
        _ ≤ (a ^ 3) ^ c := Nat.pow_le_pow_right (pow_pos ha 3) hc
        _ ≤ u := hpow
        _ ≤ b * a := hi
        _ ≤ a ^ 3 * a := Nat.mul_le_mul_right a hba
        _ = a ^ 4 := by rw [← pow_succ]
    have h7 : a ^ 4 < a ^ 6 := Nat.pow_lt_pow_right ha2 (by norm_num)
    omega
  subst ha1
  calc u ≤ b * 1 := hi
    _ ≤ 1 := by simpa using hba

section Chain

variable {G₁ G₂ T V M₂ : Subgroup G}

theorem false_of_chain_cube (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hq : ∀ E₀ : Subgroup G, E₀ ≤ T → IsElemAbelian 2 E₀ → ⁅⁅V, E₀⁆, E₀⁆ = ⊥ →
      ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
      ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ 4 ≤
        ((Subgroup.centralizer (E₀ : Set G)).relIndex V) ^ 3)
    (hcube : ∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N →
      ¬ IsCentralStep G₂ L N → ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → ⁅⁅N, A⁆, A⁆ ≤ L →
        ((centralizerMod L A N).relIndex A) ^ 3 ≤ (centralizerMod L N A).relIndex N)
    {c : ℕ} (hc : 2 ≤ c)
    (hser : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.minParabolic hnff
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hUe : IsElemAbelian 2 U := isElemAbelian_conjClosure h hnff hVR₂
  have hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥ := commutator_ne_bot h
  obtain ⟨A₀, hA₀, hA₀U⟩ : ∃ A₀, IsMaxElemAbelian T A₀ ∧
      ¬ A₀ ≤ Subgroup.centralizer (U : Set G) := by
    by_contra hall
    push Not at hall
    have hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (U : Set G) :=
      iSup₂_le fun A hA => le_inf hA.1 (hall A hA)
    apply h.not_thompsonJ_le_pCoreOf hnff
    rw [← h.thompsonJ_eq hnff]
    exact hJ.trans (inf_centralizer_le_pCoreOf hmp hG₂U hUP le_rfl)
  have hA₀N : A₀ ≤ Subgroup.normalizer (U : Set G) := (hA₀.1.trans hTG₂).trans hG₂U
  obtain ⟨A, hAA₀, hAnc, hAq, hAoff⟩ := exists_quadratic_offender hUe hA₀N hA₀.2.1 hA₀U
    (card_le_relIndex_mul_card hUe hUT hA₀)
  have hAT : A ≤ T := hAA₀.trans hA₀.1
  have hAe : IsElemAbelian 2 A := isElemAbelian_mono hAA₀ hA₀.2.1
  have hAG₂ : A ≤ G₂ := hAT.trans hTG₂
  set B := R₂ ⊓ A with hBdef
  have hBA : B ≤ A := inf_le_right
  have hCAU : A ⊓ Subgroup.centralizer (U : Set G) ≤ R₂ :=
    inf_centralizer_le_pCoreOf hmp hG₂U hUP hAT
  have ha0 : 0 < R₂.relIndex A := Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have hb0 : 0 < (Subgroup.centralizer (U : Set G)).relIndex B :=
    Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have hab : (Subgroup.centralizer (U : Set G)).relIndex A =
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (U : Set G)) R₂ A
    have e : (Subgroup.centralizer (U : Set G) ⊓ R₂).relIndex A =
        (Subgroup.centralizer (U : Set G)).relIndex A := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G) ⊓ R₂),
        ← Subgroup.inf_relIndex_right (Subgroup.centralizer (U : Set G)) A]
      congr 1
      refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left ?_)
        inf_le_right)
      rintro x ⟨hxC, hxA⟩
      exact hCAU ⟨hxA, hxC⟩
    rw [e] at this
    exact this.symm
  have hi : (Subgroup.centralizer (A : Set G)).relIndex U ≤
      (Subgroup.centralizer (U : Set G)).relIndex B * R₂.relIndex A := by
    have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) U
    have hpos : 0 < Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := Nat.card_pos
    have hoff' : Nat.card U ≤ (Subgroup.centralizer (U : Set G)).relIndex A *
        Nat.card (Subgroup.centralizer (A : Set G) ⊓ U : Subgroup G) := by
      rw [Subgroup.inf_relIndex_left] at hAoff
      rwa [inf_comm] at hAoff
    rw [← hab]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e2]
    exact hoff'
  have hk : ∀ L' N' : Subgroup G, IsChiefStep G₂ U L' N' → ¬ IsCentralStep G₂ L' N' →
      (R₂.relIndex A) ^ 3 ≤ (centralizerMod L' N' A).relIndex N' := by
    intro L' N' hstep hnc
    have hquadN : ⁅⁅N', A⁆, A⁆ ≤ L' := by
      have : ⁅⁅N', A⁆, A⁆ ≤ ⁅⁅U, A⁆, A⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono hstep.1.1 le_rfl) le_rfl
      rw [hAq] at this
      exact this.trans bot_le
    refine (Nat.pow_le_pow_left (Subgroup.relIndex_le_of_le_left
      (centralizerMod_le_pCoreOf hmp hUT hstep hnc hAT) (relIndex_ne_zero _ _)) 3).trans ?_
    exact hcube L' N' hstep hnc A hAT hAe hquadN
  have hpow : (R₂.relIndex A ^ 3) ^ c ≤ (Subgroup.centralizer (A : Set G)).relIndex U :=
    pow_le_relIndex hUG₂ hAG₂ hk hser
  have hQ : ∀ k ∈ G₂, ∀ E : Subgroup G, E ≤ B →
      ¬ E ≤ Subgroup.centralizer (cjSub k V : Set G) →
      ((Subgroup.centralizer (cjSub k V : Set G)).relIndex E) ^ 4 ≤
        ((Subgroup.centralizer (E : Set G)).relIndex (cjSub k V)) ^ 3 := by
    intro k hk' E hEB hnc
    have hEA : E ≤ A := hEB.trans hBA
    have hquad : ⁅⁅cjSub k V, E⁆, E⁆ = ⊥ := by
      have : ⁅⁅cjSub k V, E⁆, E⁆ ≤ ⁅⁅U, A⁆, A⁆ := Subgroup.commutator_mono
        (Subgroup.commutator_mono (cjSub_le_conjClosure hk') hEA) hEA
      rw [hAq] at this
      exact le_bot_iff.mp this
    exact relIndex_conj_pow_le hq hR₂T (hG₂R₂ hk') (hEB.trans inf_le_left)
      (isElemAbelian_mono hEA hAe) hquad hnc
  have hiii := pow_relIndex_le_nonstrict (V := V) (H := G₂) (B := B) hQ B le_rfl
  have hiv : (Subgroup.centralizer (B : Set G)).relIndex U ≤
      (Subgroup.centralizer (A : Set G)).relIndex U :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le fun x hx => hBA hx)
      (relIndex_ne_zero _ _)
  have hu1 := le_one_of_chain ha0 hb0 hc hpow hi hiii hiv
  have hu : (Subgroup.centralizer (A : Set G)).relIndex U = 1 :=
    le_antisymm hu1 (Nat.pos_of_ne_zero (relIndex_ne_zero _ _))
  apply hAnc
  have hUA : U ≤ Subgroup.centralizer (A : Set G) := Subgroup.relIndex_eq_one.mp hu
  exact Subgroup.le_centralizer_iff.mp hUA

end Chain

end CFSG.Quasithin.H13.Ch9.L34
