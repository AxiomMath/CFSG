module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistWitness
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusSCFive
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusSCSeven
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveConjSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc

variable (K : Type) [Field K] [Finite K] [CharP K 2]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)

theorem card_normOne {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) :
    Nat.card (CFSG.LieType.Steinberg.normOne θ) = 2 ^ f + 1 := by
  have heq : CFSG.LieType.Steinberg.normOne θ =
      (powMonoidHom (2 ^ f + 1) : Kˣ →* Kˣ).ker := by
    ext u
    change θ (u : K) * (u : K) = 1 ↔ u ^ (2 ^ f + 1) = 1
    have ht : θ (u : K) = (u : K) ^ (2 ^ f) := hθq _
    rw [ht, ← pow_succ, ← Units.val_pow_eq_pow_val, ← Units.val_eq_one]
  rw [heq, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hK]
  have hmul : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    exact (Nat.sq_sub_sq (2 ^ f) 1).trans (by simp [mul_comm])
  rw [hmul, Nat.gcd_mul_right_left]

theorem exists_normOne_prime {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) :
    ∃ ζ : CFSG.LieType.Steinberg.normOne θ, orderOf (ζ : Kˣ) = p := by
  have hd : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpq.trans (TwE6Lang.add_one_dvd_sq_sub_one _)
  obtain ⟨ζ, hζ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.exists_orderOf_eq_of_dvd_card_sub_one
    (F := K) hd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζq : ζ ^ (2 ^ f + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζp, one_pow]
  refine ⟨⟨ζ, ?_⟩, hζ⟩
  change θ (ζ : K) * (ζ : K) = 1
  rw [show θ (ζ : K) = (ζ : K) ^ (2 ^ f) from hθq _, ← pow_succ]
  exact congrArg (fun z : Kˣ => (z : K)) hζq

theorem graph_frame_selfCent {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p) :
    ∀ x : graphFixedRootGroup TwistTag.E6 K θ.toRingHom,
      (∀ e ∈ ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
        (langPFrame K θ hθ l hl ζ hζ)).range, x * e = e * x) → x ^ p = 1 →
      x ∈ ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
        (langPFrame K θ hθ l hl ζ hζ)).range := by
  intro x hx hxp
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
  have hqs : Function.Surjective q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ.toRingHom hθq
  have hqk : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq).le
  apply cover_langTorusHom_torsion K θ hθ l hl hK hθq hp hp3 ζ hζ hζo q hqk
    (cover_centralizer_langPFrame_le K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo q hqs hqk ?_) hxp
  exact Subgroup.mem_centralizer_iff.mpr fun e he => (hx e he).symm

theorem card_eq_six_of_selfCent_five {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (h5 : 5 ∣ 2 ^ f + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.E6 K θ.toRingHom))
    (hE : IsElemAbelian 5 E)
    (hsc : ∀ x, (∀ e ∈ E, x * e = e * x) → x ^ 5 = 1 → x ∈ E) :
    Nat.card E = 5 ^ 6 := by
  obtain ⟨V, hV, hVc, _, hconj⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_elemAbelian_conj_le_six
      Nat.prime_two K hK θ (fun c => hθq c) h5
  obtain ⟨g, hEg⟩ := hconj E hE
  have hVE : V ≤ E.map (MulAut.conj g).toMonoidHom := by
    intro v hv
    have hx : g⁻¹ * v * g ∈ E := by
      apply hsc
      · intro e he
        have hc : v * (g * e * g⁻¹) = (g * e * g⁻¹) * v := by
          exact congrArg Subtype.val (hV.1.is_comm.comm (⟨v, hv⟩ : V)
            (⟨g * e * g⁻¹, hEg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom he)⟩ : V))
        calc (g⁻¹ * v * g) * e = g⁻¹ * (v * (g * e * g⁻¹)) * g := by group
          _ = e * (g⁻¹ * v * g) := by rw [hc]; group
      · change (g⁻¹ * v * (g⁻¹)⁻¹) ^ 5 = 1
        rw [conj_pow, hV.2 v hv]; group
    exact ⟨g⁻¹ * v * g, hx, by change g * (g⁻¹ * v * g) * g⁻¹ = v; group⟩
  have hEq : E.map (MulAut.conj g).toMonoidHom = V := le_antisymm hEg hVE
  have hc : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← hc, hEq, hVc]

theorem exists_graph_frame_conj_of_selfCent {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (E : Subgroup (graphFixedRootGroup TwistTag.E6 K θ.toRingHom)) (hE : IsElemAbelian p E)
    (hsc : ∀ x, (∀ e ∈ E, x * e = e * x) → x ^ p = 1 → x ∈ E) :
    ∃ c : graphFixedRootGroup TwistTag.E6 K θ.toRingHom,
      E.map (MulAut.conj c).toMonoidHom =
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
          (langPFrame K θ hθ l hl ζ hζ)).range := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
  have hqs : Function.Surjective q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ.toRingHom hθq
  have hqc : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq).le
  let ι := q.comp (langPFrame K θ hθ l hl ζ hζ)
  let E₀ := ι.range
  have hζo' : orderOf ζ = p := by rw [← Subgroup.orderOf_coe ζ]; exact hζo
  have hι : Function.Injective ι := cover_langPFrame_injective K θ hθ l hl hK hθq hp hp3 q hqc ζ hζ hζo'
  have hE₀ : IsElemAbelian p E₀ := NoOffE8Five.isElemAbelian_range_of_module ι
  have hE₀c : Nat.card E₀ = p ^ 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, card_multiplicative_fin_zmod]
    rfl
  have hE₀sc := graph_frame_selfCent K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo
  by_cases hpFive : p = 5
  · rcases hpFive with rfl
    have hEc' : 5 ^ 5 ≤ Nat.card E := by
      rw [card_eq_six_of_selfCent_five K θ hK hθq hpq E hE hsc]
      decide
    obtain ⟨c, hc⟩ := ExcFrames.twistedE6SCUnique_five hf hpq K hK θ.toRingHom hθq
      hE (le_trans (Nat.pow_le_pow_right (by decide) (by decide : 4 ≤ 5)) hEc')
      hsc hE₀ (by rw [hE₀c]; decide) hE₀sc
    exact ⟨c, hc.symm⟩
  · have hp7 : 7 ≤ p := by
      have hp6 : p ≠ 6 := by intro h; rw [h] at hp; norm_num at hp
      omega
    let T := (q.comp (langTorusHom K θ hθ l hl)).range
    have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      simpa only [MonoidHom.comp_apply, map_mul] using
        congrArg q (langTorusHom_commute K θ hθ l hl u v).eq
    have hET : E₀ ≤ T := by
      rintro _ ⟨a, rfl⟩
      refine ⟨fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd a i)), ?_⟩
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, langPFrame_apply]
    have hTp : ∀ x ∈ T, x ^ p = 1 → x ∈ E₀ := by
      intro x hx hxp
      exact cover_langTorusHom_torsion K θ hθ l hl hK hθq hp hp3 ζ hζ hζo q hqc hx hxp
    have hcent : ∀ x, (∀ e ∈ E₀, x * e = e * x) → x ∈ T := by
      intro x hx
      exact cover_centralizer_langPFrame_le K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo q hqs hqc
        (Subgroup.mem_centralizer_iff.mpr fun e he => (hx e he).symm)
    obtain ⟨c, hc⟩ := ExcFrames.twistedE6SCUnique_ge_seven hp7 hf hpq K hK θ.toRingHom hθq
      hι hTcomm hET hTp hcent hE hsc
    refine ⟨c⁻¹, ?_⟩
    rw [← hc, Subgroup.map_map]
    have he : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change c⁻¹ * (c * x * c⁻¹) * c = x
      group
    rw [he, Subgroup.map_id]
    rfl

theorem exists_aligned_graph_of_selfCent {r : ℕ} {L : Type} [Group L] [Finite L]
    {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (ψ : L →* TwE6Delta.RecipeR K f) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (TwE6Delta.RecipeR K f) (TwE6Delta.RecipeI K f) L ψ A) :
    ∃ ψa : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom,
      Function.Surjective ψa ∧ ψa.ker ≤ Subgroup.center L ∧
      ∃ Λ : graphFixedRootGroup TwistTag.E6 K θ.toRingHom →* MulAut L,
        Function.Injective Λ ∧ (∀ x : L, Λ (ψa x) = MulAut.conj x) ∧
        (((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
          (langPFrame K θ hθ l hl ζ hζ)).range).map Λ = A := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, -, hsc⟩ := hTB
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, hcard, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (TwE6Delta.center_recipeR_eq_bot hf hK)
      (TwE6Delta.ggOutdiagPrime_twE6 hf hK hp hp3)
      (TwE6Delta.ggCenterPrime_twE6 hf hK hp hp2 hp3)
      ψ hψ hker hperf hA hAI hsc
  let E₀ := A.comap Λ₀
  obtain ⟨ε⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hf hK θ.toRingHom hθq
  let E := E₀.map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ E₀ := by
      apply hEsc (ε.symm g)
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  obtain ⟨c, hc⟩ := exists_graph_frame_conj_of_selfCent K θ hθ l hl hf hK hθq hp hp5 hpq
    ζ hζ hζo E hEg hEgs
  let η : TwE6Delta.RecipeR K f ≃* graphFixedRootGroup TwistTag.E6 K θ.toRingHom :=
    ε.trans (MulAut.conj c)
  have hEg' : E₀.map η.toMonoidHom =
      ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
        (langPFrame K θ hθ l hl ζ hζ)).range := by
    rw [← hc, Subgroup.map_map]
    rfl
  have hEA : E₀.map Λ₀ = A := by
    change (A.comap Λ₀).map Λ₀ = A
    have hle : A ≤ Λ₀.range := fun a ha => hAΛ a ha
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  let ψa := η.toMonoidHom.comp ψ
  have hψa : Function.Surjective ψa := η.surjective.comp hψ
  have hka : ψa.ker ≤ Subgroup.center L := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact η.injective (hx.trans (map_one η).symm)
  let Λ := Λ₀.comp η.symm.toMonoidHom
  have hΛn : ∀ x : L, Λ (ψa x) = MulAut.conj x := by
    intro x
    change Λ₀ (η.symm (η (ψ x))) = MulAut.conj x
    rw [η.symm_apply_apply]
    exact hΛeq rfl
  refine ⟨ψa, hψa, hka, Λ, hΛinj.comp η.symm.injective, hΛn, ?_⟩
  rw [← hEg', Subgroup.map_map]
  have hcomp : Λ.comp η.toMonoidHom = Λ₀ := by
    apply MonoidHom.ext
    intro x
    change Λ₀ (η.symm (η x)) = Λ₀ x
    rw [η.symm_apply_apply]
  rw [hcomp, hEA]

theorem exists_aligned_graph_of_card_or_seven {r : ℕ} {L : Type} [Group L] [Finite L]
    {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (ψ : L →* TwE6Delta.RecipeR K f) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p r (TwE6Delta.RecipeR K f) (TwE6Delta.RecipeI K f) L ψ A)
    (hCard : p ^ 5 ≤ Nat.card A ∨ 7 ≤ p) :
    ∃ ψa : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom,
      Function.Surjective ψa ∧ ψa.ker ≤ Subgroup.center L ∧
      ∃ Λ : graphFixedRootGroup TwistTag.E6 K θ.toRingHom →* MulAut L,
        Function.Injective Λ ∧ (∀ x : L, Λ (ψa x) = MulAut.conj x) ∧
        (((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
          (langPFrame K θ hθ l hl ζ hζ)).range).map Λ = A  := by
  exact exists_aligned_graph_of_selfCent K θ hθ l hl hf hK hθq hp hp5 hpq
    ζ hζ hζo ψ A hTB

theorem exists_aligned_graph {L : Type} [Group L] [Finite L]
    {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (ψ : L →* TwE6Delta.RecipeR K f) (A : Subgroup (MulAut L))
    (hTB : GGTorusTBGroup p 5 (TwE6Delta.RecipeR K f) (TwE6Delta.RecipeI K f) L ψ A) :
    ∃ ψa : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom,
      Function.Surjective ψa ∧ ψa.ker ≤ Subgroup.center L ∧
      ∃ Λ : graphFixedRootGroup TwistTag.E6 K θ.toRingHom →* MulAut L,
        (∀ x : L, Λ (ψa x) = MulAut.conj x) ∧
        (((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq).comp
          (langPFrame K θ hθ l hl ζ hζ)).range).map Λ = A  := by
  obtain ⟨ψa, hψa, hka, Λ, _, hΛn, hA⟩ :=
    exists_aligned_graph_of_card_or_seven K θ hθ l hl hf hK hθq hp hp5 hpq
      ζ hζ hζo ψ A hTB (Or.inl hTB.2.2.2.2.2.1)
  exact ⟨ψa, hψa, hka, Λ, hΛn, hA⟩

theorem ggTorusTorW_recipe_twE6 {f p : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ 2 ^ f + 1) :
    GGTorusTorW p 5 (2 ^ f + 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆
      (TwE6Delta.RecipeR K f) (TwE6Delta.RecipeI K f) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by intro h; rw [h] at hp; norm_num at hp
    have := hp.two_le
    omega
  have hf1 : 1 ≤ f := by omega
  obtain ⟨θ, hθq, hθo, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf1 K hK
  have hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK (fun c => hθq c)
  have hθ1 : θ ≠ 1 := by
    change orderOf θ = 2 at hθo
    intro h
    rw [h, orderOf_one] at hθo
    omega
  have hθ2 : θ * θ = 1 := by
    change orderOf θ = 2 at hθo
    simpa only [hθo, pow_two] using pow_orderOf_eq_one θ
  obtain ⟨l, hl⟩ := CFSG.SeitzReduction.LinearPilot.exists_trace_one_of_involution hθ1 hθ2
  obtain ⟨ζ, hζo⟩ := exists_normOne_prime K θ hf1 hK (fun c => hθq c) hp hpq
  have hζ : ζ ^ p = 1 := by
    apply Subtype.ext
    change (ζ : Kˣ) ^ p = 1
    rw [← hζo, pow_orderOf_eq_one]
  let e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod (2 ^ f + 1)) := by
    have he : CFSG.LieType.Steinberg.normOne θ ≃*
        Multiplicative (ZMod (Nat.card (CFSG.LieType.Steinberg.normOne θ))) :=
      (zmodCyclicMulEquiv inferInstance).symm
    rwa [card_normOne K θ hK (fun c => hθq c)] at he
  intro L _ _ ψ A hTB
  obtain ⟨ψa, hψa, hka, Λ, hΛn, hFA⟩ :=
    exists_aligned_graph K θ hθ l hl hf1 hK (fun c => hθq c) hp hp5 hpq
      ζ hζ hζo ψ A hTB
  obtain ⟨φ, hφs, hφ, hφc⟩ := exists_cover_fixed hf hK θ hθq ψa hψa hka hTB.2.2.1
  obtain ⟨δ, hδ⟩ := exists_diagonal_descent hK θ hθq hθ l hl φ hφs hφc
  have hA : ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range).map
      (MulAut.conj : L →* MulAut L) = A := by
    rw [← hFA, ← MonoidHom.range_comp, ← MonoidHom.range_comp]
    apply congrArg MonoidHom.range
    apply MonoidHom.ext
    intro a
    change MulAut.conj (φ (langPFrame K θ hθ l hl ζ hζ a)) =
      Λ (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf1 hK θ.toRingHom
        (fun c => hθq c) (langPFrame K θ hθ l hl ζ hζ a))
    rw [← hφ, hΛn]
  exact scalar_torData_aligned θ hθ l hl φ δ hf1 hK (fun c => hθq c)
    hp hp2 hp3 ψa hψa hka hφ hφs hφc hδ ζ hζ hζo e A hA

theorem ggTBTorE6IndTwist_holds : GGTBTorE6IndTwist := by
  intro p hp hp2 hp3 lab hlab htag hpm
  obtain ⟨t, r, f⟩ := lab
  have hf : 1 ≤ f := hlab.1
  dsimp only at htag hf hpm ⊢
  subst htag
  have hpq : p ∣ 2 ^ f + 1 := by simpa [ggTorM] using hpm
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    have hpThree : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hpq |>.resolve_left hp.ne_one
    exact hp3 hpThree
  have hEnn : ggTorEnn p ⟨.twE6, r, f⟩ = 1 := by simp [ggTorEnn, hpq]
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, ← pow_mul])
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  rw [hEnn]
  simpa only [ggTorM, LargeEvenLabel.tag, LargeEvenLabel.n, or_true, if_true] using
    ggTorusTorW_recipe_twE6 K hf2 hK hp hp2 hp3 hpq

end CFSG.StandardType.TBE6IndTwist
