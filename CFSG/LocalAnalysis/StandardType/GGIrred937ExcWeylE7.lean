module

public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
public import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
open CFSG.StandardType.ExcWeylOuter

theorem weylIrred_of_index_dvd_two
    {X : Type} [Group X] (J : Subgroup X) (hJ : J.index ∣ 2)
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hodd : Odd τ.rank)
    (ι : Multiplicative (Fin τ.rank → ZMod p) →* X) (hinj : Function.Injective ι)
    (hEJ : ι.range ≤ J) (m : Fin τ.rank → X)
    (hm : ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p),
      m i * ι (Multiplicative.ofAdd s) * (m i)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s)))
    (hirr : ∀ U : AddSubgroup (Fin τ.rank → ZMod p),
      (∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p), x ∈ U →
        TableBExc.torusAct τ p (simple τ i) x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ E' : Subgroup X, E' ≤ ι.range →
      (∀ g ∈ J, g ∈ Subgroup.normalizer (ι.range : Set X) → ∀ e ∈ E', g * e * g⁻¹ ∈ E') →
      E' = ⊥ ∨ E' = ι.range := by
  classical
  have hJcases : J.index = 1 ∨ J.index = 2 := (Nat.dvd_prime Nat.prime_two).1 hJ
  have hJnormal : J.Normal := by
    rcases hJcases with h1 | h2
    · exact Subgroup.normal_of_index_eq_one h1
    · exact Subgroup.normal_of_index_eq_two h2
  intro E' hE' hnorm
  by_cases hbot : E' = ⊥
  · exact Or.inl hbot
  right
  let N : Subgroup X := Subgroup.normalizer (ι.range : Set X)
  let N' : Subgroup X := N ⊓ J
  have hmN : ∀ i : Fin τ.rank, m i ∈ N := by
    intro i
    rw [show N = Subgroup.normalizer (ι.range : Set X) from rfl, Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · rintro ⟨s, rfl⟩
      have h := hm i (Multiplicative.toAdd s)
      rw [ofAdd_toAdd s] at h
      exact ⟨_, h.symm⟩
    · rintro ⟨s, hs⟩
      refine ⟨Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i)
        (Multiplicative.toAdd s)), ?_⟩
      have h := hm i (Multiplicative.toAdd s)
      rw [ofAdd_toAdd s] at h
      have h2 : TableBExc.torusAct τ p (simple τ i)
            (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s)) =
          Multiplicative.toAdd s := by
        rw [← TableBExc.torusAct_mul, simple_mul_simple_self, TableBExc.torusAct_one]
      have h3 := hm i (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s))
      rw [h2, ofAdd_toAdd s] at h3
      have h4 : m i * ι (Multiplicative.ofAdd
            (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s))) * (m i)⁻¹ =
          m i * x * (m i)⁻¹ := by
        rw [h3, hs]
      exact mul_left_cancel (mul_right_cancel h4)
  have hU : GGWeylIrred ι.range := ggWeylIrred_range_of_torusAct ι hinj m hm hirr
  by_cases hNJ : N ≤ J
  · have hstab : ∀ g ∈ N, ∀ e ∈ E', g * e * g⁻¹ ∈ E' :=
      fun g hg => hnorm g (hNJ hg) hg
    rcases hU E' hE' hstab with h | h
    · exact absurd h hbot
    · exact h
  · obtain ⟨γ, hγN, hγJ⟩ := by
      simpa only [SetLike.le_def, not_forall, not_imp] using hNJ
    have hJindex : J.index = 2 := by
      rcases hJcases with h1 | h2
      · exfalso
        exact hNJ (by rw [Subgroup.index_eq_one.mp h1]; exact le_top)
      · exact h2
    have hγ2J : γ ^ 2 ∈ J := Subgroup.sq_mem_of_index_two hJindex γ
    have hγ2N : γ ^ 2 ∈ N := by rw [sq]; exact mul_mem hγN hγN
    have hγ2N' : γ ^ 2 ∈ N' := Subgroup.mem_inf.mpr ⟨hγ2N, hγ2J⟩
    have hdec : ∀ n ∈ N, n ∈ N' ∨ ∃ n' ∈ N', n = γ * n' := by
      intro n hn
      by_cases hnJ : n ∈ J
      · exact Or.inl (Subgroup.mem_inf.mpr ⟨hn, hnJ⟩)
      · refine Or.inr ⟨γ⁻¹ * n, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hγN) hn, ?_⟩, by group⟩
        have hiff : (γ⁻¹ ∈ J) ↔ (n ∈ J) := by
          rw [Subgroup.inv_mem_iff]
          exact ⟨fun h => absurd h hγJ, fun h => absurd h hnJ⟩
        exact (Subgroup.mul_mem_iff_of_index_two hJindex (a := γ⁻¹) (b := n)).mpr hiff
    let H2 : Subgroup X := Subgroup.map (MulAut.conj γ).toMonoidHom E'
    have hH2le : H2 ≤ ι.range := by
      rintro y ⟨e, he, rfl⟩
      change γ * e * γ⁻¹ ∈ ι.range
      exact (Subgroup.mem_set_normalizer_iff.mp hγN e).mp (hE' he)
    have hE'N' : ∀ g ∈ N', ∀ e ∈ E', g * e * g⁻¹ ∈ E' :=
      fun g hg => hnorm g (Subgroup.mem_inf.mp hg).2 (Subgroup.mem_inf.mp hg).1
    have hH2N' : ∀ g ∈ N', ∀ e ∈ H2, g * e * g⁻¹ ∈ H2 := by
      intro g hg e he
      obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.1 he
      refine Subgroup.mem_map.2 ⟨(γ⁻¹ * g * γ) * e0 * (γ⁻¹ * g * γ)⁻¹, ?_, ?_⟩
      · exact hE'N' (γ⁻¹ * g * γ)
          (Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hγN) (Subgroup.mem_inf.mp hg).1) hγN,
            hJnormal.conj_mem' g (Subgroup.mem_inf.mp hg).2 γ⟩) e0 he0
      · change γ * ((γ⁻¹ * g * γ) * e0 * (γ⁻¹ * g * γ)⁻¹) * γ⁻¹ =
          g * (γ * e0 * γ⁻¹) * g⁻¹
        group
    let MA := Multiplicative (Fin τ.rank → ZMod p)
    let W : Subgroup MA := E'.comap ι
    let W2 : Subgroup MA := H2.comap ι
    have hmapW : Subgroup.map ι W = E' := by
      rw [show W = E'.comap ι from rfl, Subgroup.map_comap_eq, inf_eq_right.mpr hE']
    have hmapW2 : Subgroup.map ι W2 = H2 := by
      rw [show W2 = H2.comap ι from rfl, Subgroup.map_comap_eq, inf_eq_right.mpr hH2le]
    have hmapSup : Subgroup.map ι (W ⊔ W2) = E' ⊔ H2 := by
      rw [Subgroup.map_sup, hmapW, hmapW2]
    have hmapInf : Subgroup.map ι (W ⊓ W2) = E' ⊓ H2 := by
      rw [Subgroup.map_inf W W2 ι hinj, hmapW, hmapW2]
    have hτ : ∀ (i : Fin τ.rank) (a : MA),
        ι ((torusMulAut τ p (simple τ i)) a) = m i * ι a * (m i)⁻¹ := by
      intro i a
      have h := hm i (Multiplicative.toAdd a)
      rw [ofAdd_toAdd a] at h
      have h2 : (torusMulAut τ p (simple τ i)) a =
          Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i)
            (Multiplicative.toAdd a)) := by
        conv_lhs => rw [← ofAdd_toAdd a]
        rw [torusMulAut_apply]
      rw [h2]
      exact h.symm
    have hτW : ∀ (i : Fin τ.rank) (a : MA), a ∈ W →
        (torusMulAut τ p (simple τ i)) a ∈ W ⊔ W2 := by
      intro i a ha
      have hai : ι a ∈ E' := Subgroup.mem_comap.mp ha
      rcases hdec (m i) (hmN i) with hm' | ⟨n', hn', hm_eq⟩
      · exact (le_sup_left : W ≤ W ⊔ W2) (by
          change ι ((torusMulAut τ p (simple τ i)) a) ∈ E'
          rw [hτ i a]
          exact hE'N' (m i) hm' (ι a) hai)
      · exact (le_sup_right : W2 ≤ W ⊔ W2) (by
          change ι ((torusMulAut τ p (simple τ i)) a) ∈ H2
          rw [hτ i a, hm_eq]
          refine Subgroup.mem_map.2 ⟨n' * ι a * n'⁻¹, hE'N' n' hn' (ι a) hai, ?_⟩
          change γ * (n' * ι a * n'⁻¹) * γ⁻¹ = γ * n' * ι a * (γ * n')⁻¹
          group)
    have hτW2 : ∀ (i : Fin τ.rank) (a : MA), a ∈ W2 →
        (torusMulAut τ p (simple τ i)) a ∈ W ⊔ W2 := by
      intro i a ha
      have hai : ι a ∈ H2 := Subgroup.mem_comap.mp ha
      rcases hdec (m i) (hmN i) with hm' | ⟨n', hn', hm_eq⟩
      · exact (le_sup_right : W2 ≤ W ⊔ W2) (by
          change ι ((torusMulAut τ p (simple τ i)) a) ∈ H2
          rw [hτ i a]
          exact hH2N' (m i) hm' (ι a) hai)
      · obtain ⟨e, he, hee⟩ := Subgroup.mem_map.1 (hH2N' n' hn' (ι a) hai)
        exact (le_sup_left : W ≤ W ⊔ W2) (by
          change ι ((torusMulAut τ p (simple τ i)) a) ∈ E'
          rw [hτ i a, hm_eq]
          have hsub : n' * ι a * n'⁻¹ = γ * e * γ⁻¹ := by
            rw [← hee]
            exact MulAut.conj_apply γ e
          have h1 : γ * n' * ι a * (γ * n')⁻¹ = γ * γ * e * (γ * γ)⁻¹ := by
            rw [show γ * n' * ι a * (γ * n')⁻¹ =
                γ * (n' * ι a * n'⁻¹) * γ⁻¹ by group, hsub]
            group
          rw [h1]
          simpa [pow_two] using hE'N' (γ ^ 2) hγ2N' e he)
    have hτWinf : ∀ (i : Fin τ.rank) (a : MA), a ∈ W ⊓ W2 →
        (torusMulAut τ p (simple τ i)) a ∈ W := by
      intro i a ha
      rw [Subgroup.mem_inf] at ha
      rcases hdec (m i) (hmN i) with hm' | ⟨n', hn', hm_eq⟩
      · change ι ((torusMulAut τ p (simple τ i)) a) ∈ E'
        rw [hτ i a]
        exact hE'N' (m i) hm' (ι a) (Subgroup.mem_comap.mp ha.1)
      · obtain ⟨e, he, hee⟩ := Subgroup.mem_map.1 (hH2N' n' hn' (ι a) (Subgroup.mem_comap.mp ha.2))
        change ι ((torusMulAut τ p (simple τ i)) a) ∈ E'
        rw [hτ i a, hm_eq]
        have hsub : n' * ι a * n'⁻¹ = γ * e * γ⁻¹ := by
          rw [← hee]
          exact MulAut.conj_apply γ e
        have h1 : γ * n' * ι a * (γ * n')⁻¹ = γ * γ * e * (γ * γ)⁻¹ := by
          rw [show γ * n' * ι a * (γ * n')⁻¹ =
              γ * (n' * ι a * n'⁻¹) * γ⁻¹ by group, hsub]
          group
        rw [h1]
        simpa [pow_two] using hE'N' (γ ^ 2) hγ2N' e he
    have hτW2inf : ∀ (i : Fin τ.rank) (a : MA), a ∈ W ⊓ W2 →
        (torusMulAut τ p (simple τ i)) a ∈ W2 := by
      intro i a ha
      rw [Subgroup.mem_inf] at ha
      rcases hdec (m i) (hmN i) with hm' | ⟨n', hn', hm_eq⟩
      · change ι ((torusMulAut τ p (simple τ i)) a) ∈ H2
        rw [hτ i a]
        exact hH2N' (m i) hm' (ι a) (Subgroup.mem_comap.mp ha.2)
      · change ι ((torusMulAut τ p (simple τ i)) a) ∈ H2
        rw [hτ i a, hm_eq]
        refine Subgroup.mem_map.2 ⟨n' * ι a * n'⁻¹, hE'N' n' hn' (ι a)
          (Subgroup.mem_comap.mp ha.1), ?_⟩
        change γ * (n' * ι a * n'⁻¹) * γ⁻¹ = γ * n' * ι a * (γ * n')⁻¹
        group
    have hsupstab : ∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p),
        x ∈ Subgroup.toAddSubgroup' (W ⊔ W2) →
        TableBExc.torusAct τ p (simple τ i) x ∈ Subgroup.toAddSubgroup' (W ⊔ W2) := by
      intro i x hx
      rw [Subgroup.mem_toAddSubgroup'] at hx ⊢
      rw [← torusMulAut_apply]
      rcases Subgroup.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
      rw [← hab, map_mul]
      exact mul_mem (hτW i a ha) (hτW2 i b hb)
    have hinfstab : ∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p),
        x ∈ Subgroup.toAddSubgroup' (W ⊓ W2) →
        TableBExc.torusAct τ p (simple τ i) x ∈ Subgroup.toAddSubgroup' (W ⊓ W2) := by
      intro i x hx
      rw [Subgroup.mem_toAddSubgroup'] at hx ⊢
      rw [← torusMulAut_apply]
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hτWinf i _ (Subgroup.mem_inf.mpr hx), hτW2inf i _ (Subgroup.mem_inf.mpr hx)⟩
    have hsupW : W ⊔ W2 = ⊥ ∨ W ⊔ W2 = ⊤ := by
      rcases hirr (Subgroup.toAddSubgroup' (W ⊔ W2)) hsupstab with h | h
      · left
        exact Subgroup.toAddSubgroup'.injective (h.trans (map_bot Subgroup.toAddSubgroup').symm)
      · right
        exact Subgroup.toAddSubgroup'.injective (h.trans (map_top Subgroup.toAddSubgroup').symm)
    have hinfW : W ⊓ W2 = ⊥ ∨ W ⊓ W2 = ⊤ := by
      rcases hirr (Subgroup.toAddSubgroup' (W ⊓ W2)) hinfstab with h | h
      · left
        exact Subgroup.toAddSubgroup'.injective (h.trans (map_bot Subgroup.toAddSubgroup').symm)
      · right
        exact Subgroup.toAddSubgroup'.injective (h.trans (map_top Subgroup.toAddSubgroup').symm)
    rcases hsupW with hsupbot | hsuptop
    · exfalso
      have h1 : E' ⊔ H2 = ⊥ := by rw [← hmapSup, hsupbot, Subgroup.map_bot]
      exact hbot (le_bot_iff.mp (h1 ▸ le_sup_left))
    · rcases hinfW with hinfbot | hinftop
      · have hdisj : Disjoint W W2 := disjoint_iff_inf_le.mpr hinfbot.le
        have hisc' : Subgroup.IsComplement (W : Set MA) (W2 : Set MA) := by
          rw [Subgroup.isComplement_iff_existsUnique]
          intro x
          have hx : x ∈ W ⊔ W2 := by rw [hsuptop]; exact Subgroup.mem_top x
          rcases Subgroup.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
          refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab, ?_⟩
          rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab'
          have heq : a' * b' = a * b := hab'.trans hab.symm
          have hthis : a'⁻¹ * a = b' * b⁻¹ := by
            have h := congrArg (fun z => a'⁻¹ * z * b⁻¹) heq
            have hL : a'⁻¹ * (a' * b') * b⁻¹ = b' * b⁻¹ := by
              rw [← mul_assoc a'⁻¹ a' b', inv_mul_cancel, one_mul]
            have hR : a'⁻¹ * (a * b) * b⁻¹ = a'⁻¹ * a := by
              rw [← mul_assoc a'⁻¹ a b, mul_assoc (a'⁻¹ * a) b b⁻¹,
                mul_inv_cancel b, mul_one]
            rw [hL, hR] at h
            exact h.symm
          have hc : a'⁻¹ * a ∈ W ⊓ W2 := by
            refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, ?_⟩
            rw [hthis]
            exact mul_mem hb' (inv_mem hb)
          rw [hinfbot, Subgroup.mem_bot] at hc
          have ha_eq : a = a' := by
            have h : a'⁻¹ * a = a'⁻¹ * a' := by
              rw [hc]
              exact (inv_mul_cancel a').symm
            exact mul_left_cancel h
          have hb_eq : b = b' := by
            have hb'c : b' * b⁻¹ = 1 := by rw [← hthis]; exact hc
            have h : b' * b⁻¹ = b' * b'⁻¹ := by
              rw [hb'c]
              exact (mul_inv_cancel b').symm
            exact inv_injective (mul_left_cancel h)
          exact Prod.ext (Subtype.ext ha_eq.symm) (Subtype.ext hb_eq.symm)
        have hisc : W.IsComplement' W2 := Subgroup.isComplement'_def.mpr hisc'
        have hcard := hisc.card_mul_card
        have hcardW : Nat.card W = Nat.card E' := by
          rw [← hmapW, Subgroup.card_map_of_injective hinj]
        have hcardW2 : Nat.card W2 = Nat.card H2 := by
          rw [← hmapW2, Subgroup.card_map_of_injective hinj]
        have hcardH2 : Nat.card H2 = Nat.card E' := by
          rw [show H2 = Subgroup.map (MulAut.conj γ).toMonoidHom E' from rfl,
            Subgroup.card_map_of_injective (MulAut.conj γ).injective]
        have hcardMA : Nat.card MA = p ^ τ.rank := by
          rw [show MA = Multiplicative (Fin τ.rank → ZMod p) from rfl, Nat.card_eq_fintype_card,
            Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        have hsq : Nat.card E' * Nat.card E' = p ^ τ.rank := by
          have h1 : Nat.card E' * Nat.card E' = Nat.card W * Nat.card W2 := by
            rw [hcardW, hcardW2, hcardH2]
          rw [h1, hcard, hcardMA]
        have hprime : Nat.Prime p := Fact.out
        obtain ⟨k, _hk, hEq⟩ := (Nat.dvd_prime_pow hprime).mp
          (show Nat.card E' ∣ p ^ τ.rank from ⟨Nat.card E', by rw [← hsq]⟩)
        have hrank : τ.rank = 2 * k := by
          refine Nat.pow_right_injective hprime.two_le ?_
          change p ^ τ.rank = p ^ (2 * k)
          rw [← hsq, hEq, ← pow_add, two_mul]
        rcases hodd with ⟨m0, hm0⟩
        omega
      · have h1 : E' ⊓ H2 = ι.range := by rw [← hmapInf, hinftop, Subgroup.map_top]
        exact le_antisymm hE' (h1 ▸ inf_le_left)

theorem weylIrred_of_embedding
    {R X : Type} [Group R] [Group X] (f : R →* X) (hf : Function.Injective f)
    (hidx : f.range.index ∣ 2)
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hodd : Odd τ.rank)
    (E : Subgroup R) (ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* R)
    (hι₀ : Function.Injective ι₀) (hrange : ι₀.range = E)
    (m : Fin τ.rank → X)
    (hm : ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p),
      m i * f (ι₀ (Multiplicative.ofAdd s)) * (m i)⁻¹ =
        f (ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s))))
    (hirr : ∀ U : AddSubgroup (Fin τ.rank → ZMod p),
      (∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p), x ∈ U →
        TableBExc.torusAct τ p (simple τ i) x ∈ U) → U = ⊥ ∨ U = ⊤) :
    GGWeylIrred E := by
  have hframe : ∀ E'' : Subgroup X, E'' ≤ (f.comp ι₀).range →
      (∀ g ∈ f.range, g ∈ Subgroup.normalizer ((f.comp ι₀).range : Set X) →
        ∀ e ∈ E'', g * e * g⁻¹ ∈ E'') →
      E'' = ⊥ ∨ E'' = (f.comp ι₀).range :=
    weylIrred_of_index_dvd_two (τ := τ) (p := p) (hodd := hodd) f.range hidx
      (f.comp ι₀) (hf.comp hι₀) (by rintro y ⟨x, rfl⟩; exact ⟨ι₀ x, rfl⟩) m
      (by intro i s; exact hm i s) hirr
  have hrangeComp : (f.comp ι₀).range = E.map f := by
    rw [MonoidHom.range_comp, hrange]
  intro E' hE' hnorm
  have hE'' : E'.map f ≤ (f.comp ι₀).range := by
    rw [hrangeComp]
    exact Subgroup.map_mono hE'
  have hstab : ∀ g ∈ f.range, g ∈ Subgroup.normalizer ((f.comp ι₀).range : Set X) →
      ∀ e ∈ E'.map f, g * e * g⁻¹ ∈ E'.map f := by
    intro g hg hgN e he
    obtain ⟨c, hgc⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨e', he', hee⟩ := Subgroup.mem_map.mp he
    have hc : c ∈ Subgroup.normalizer (E : Set R) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 := (Subgroup.mem_set_normalizer_iff.mp hgN (f x)).mp
          (show f x ∈ (f.comp ι₀).range from by rw [hrangeComp]; exact ⟨x, hx, rfl⟩)
        rw [← hgc, hrangeComp, ← map_mul, ← map_inv, ← map_mul] at h1
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
        rwa [hf hyeq] at hy
      · intro hx
        have h1 : g * f x * g⁻¹ ∈ (f.comp ι₀).range := by
          rw [← hgc, hrangeComp]
          rw [show f c * f x * (f c)⁻¹ = f (c * x * c⁻¹) by
            rw [← map_mul, ← map_inv, ← map_mul]]
          exact ⟨c * x * c⁻¹, hx, rfl⟩
        have h2 := (Subgroup.mem_set_normalizer_iff.mp hgN (f x)).mpr h1
        rw [hrangeComp] at h2
        obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h2
        rwa [hf hyeq] at hy
    have hce : c * e' * c⁻¹ ∈ E' := hnorm c hc e' he'
    exact Subgroup.mem_map.mpr
      ⟨c * e' * c⁻¹, hce, by rw [← hgc, ← hee, ← map_mul, ← map_inv, ← map_mul]⟩
  rcases hframe (E'.map f) hE'' hstab with hbot | htop
  · left
    exact Subgroup.map_injective hf (by rw [hbot, Subgroup.map_bot])
  · right
    exact Subgroup.map_injective hf (by rw [htop, hrangeComp])

private theorem exists_fixedGroup_of_langData
    {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K 2]
    (w : WeylGroup Tag.E7) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (g0 : ModGL .E7 (AlgebraicClosure K))
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hg0C : g0 ∈ adjointGroup .E7 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) w)
    (hcent : ∀ v : WeylGroup Tag.E7, v * w = w * v) :
    ∃ X : Subgroup (ModGL .E7 (AlgebraicClosure K)),
      Finite X ∧
      ((adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) ≤ X ∧
      ((adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).relIndex X ∣ 2 ∧
      ∀ i : Fin Tag.E7.rank, g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K)
        (simple Tag.E7 i) * g0⁻¹ ∈ X := by
  classical
  let L := AlgebraicClosure K
  let J : Subgroup (ModGL .E7 L) := (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L))
  let n : Fin Tag.E7.rank → ModGL .E7 L := fun i =>
    canonicalRep (coxeterSystem .E7) L (simple Tag.E7 i)
  let x : Fin Tag.E7.rank → ModGL .E7 L := fun i => g0 * n i * g0⁻¹
  let X : Subgroup (ModGL .E7 L) := J ⊔ Subgroup.closure (Set.range x)
  have hCharL : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hn_adj : ∀ i : Fin Tag.E7.rank, n i ∈ adjointGroup .E7 L :=
    fun i => canonicalRep_mem_adjointGroup (coxeterSystem .E7) L (simple Tag.E7 i)
  obtain ⟨Sg, hSg⟩ := CFSG.LieType.Chevalley.exists_finset_descent (τ := Tag.E7) (k := L) hg0C
  have hSn : ∀ i : Fin Tag.E7.rank, ∃ S : Finset L, ∀ N : Subfield L, (S : Set L) ⊆ N →
      ∃ y ∈ adjointGroup .E7 N, baseChangeGL N.subtype y = n i :=
    fun i => CFSG.LieType.Chevalley.exists_finset_descent (τ := Tag.E7) (k := L) (hn_adj i)
  choose Sn hSn' using hSn
  let Sall : Finset L := Sg ∪ Finset.univ.biUnion Sn
  obtain ⟨M, hMfin, hSallM, hrangeKM⟩ := exists_finite_subfield_of_finset (K := K) (L := L) Sall
  haveI : Finite M := hMfin
  have hSgM : (Sg : Set L) ⊆ M := fun a ha =>
    hSallM (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hSnM : ∀ i, (Sn i : Set L) ⊆ M := fun i a ha =>
    hSallM (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ i, Finset.mem_coe.1 ha⟩)))
  obtain ⟨g0M, hg0Madj, hg0M⟩ := hSg M hSgM
  have hnM : ∀ i, ∃ y ∈ adjointGroup .E7 M, baseChangeGL M.subtype y = n i :=
    fun i => hSn' i M (hSnM i)
  have hJM : J ≤ (adjointGroup .E7 M).map (baseChangeGL M.subtype) := by
    change (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) ≤ _
    rw [CFSG.LieType.Chevalley.map_baseChangeGL_adjointGroup (τ := Tag.E7)
          (f := algebraMap K L),
        CFSG.LieType.Chevalley.map_baseChangeGL_adjointGroup (τ := Tag.E7) (f := M.subtype)]
    rw [Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩ <;> rw [hg]
    · refine Subgroup.subset_closure ⟨i, ⟨algebraMap K L c, hrangeKM ⟨c, rfl⟩⟩, Or.inl ?_⟩
      rfl
    · refine Subgroup.subset_closure ⟨i, ⟨algebraMap K L c, hrangeKM ⟨c, rfl⟩⟩, Or.inr ?_⟩
      rfl
  have hxM : ∀ i, x i ∈ (adjointGroup .E7 M).map (baseChangeGL M.subtype) := by
    intro i
    obtain ⟨nMi, hnMi, hnMieq⟩ := hnM i
    exact ⟨g0M * nMi * g0M⁻¹, mul_mem (mul_mem hg0Madj hnMi) (inv_mem hg0Madj),
      by simp only [map_mul, map_inv, hg0M, hnMieq]
         rfl⟩
  have hXM : X ≤ (adjointGroup .E7 M).map (baseChangeGL M.subtype) := by
    refine sup_le hJM ?_
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact hxM i
  haveI hAfin : Finite ((adjointGroup .E7 M).map (baseChangeGL M.subtype)) :=
    Finite.of_surjective
      (fun g : adjointGroup .E7 M =>
        (⟨baseChangeGL M.subtype (g : ModGL .E7 M), ⟨g, g.2, rfl⟩⟩ :
          (adjointGroup .E7 M).map (baseChangeGL M.subtype)))
      (by rintro ⟨y, hy⟩
          obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
          exact ⟨⟨g, hg⟩, rfl⟩)
  haveI hXfin : Finite X :=
    Finite.of_injective (fun y : X =>
        (⟨(y : ModGL .E7 L), hXM y.2⟩ : (adjointGroup .E7 M).map (baseChangeGL M.subtype)))
      (fun a b h => Subtype.ext (congrArg
        (Subtype.val : (adjointGroup .E7 M).map (baseChangeGL M.subtype) → ModGL .E7 L) h))
  let Fix : Subgroup (ModGL .E7 L) :=
    { carrier := {y | Units.map (entrywiseHom Fr) y = y}
      mul_mem' := by
        intro a b ha hb
        change Units.map (entrywiseHom Fr) (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by
        change Units.map (entrywiseHom Fr) 1 = 1
        rw [map_one]
      inv_mem' := by
        intro a ha
        change Units.map (entrywiseHom Fr) a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hJFix : J ≤ Fix := by
    rintro y ⟨g, -, rfl⟩
    exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g
  have hFr_bij : Function.Bijective Fr :=
    frobenius_bijective (k := K) (L := L) Fr hFr
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hFr_bij with hσdef
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hmul : ∀ a b : WeylGroup Tag.E7,
      canonicalRep (coxeterSystem Tag.E7) L (a * b) =
        canonicalRep (coxeterSystem Tag.E7) L a *
          canonicalRep (coxeterSystem Tag.E7) L b :=
    fun a b => RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (τ := Tag.E7)
      (R := L) a b
  have hFr_canon : ∀ v : WeylGroup Tag.E7,
      Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem Tag.E7) L v) =
        canonicalRep (coxeterSystem Tag.E7) L v :=
    fun v => by
      simpa only [hσ] using entrywise_canonicalRep (τ := Tag.E7) σ v
  have hinv : ∀ a : WeylGroup Tag.E7,
      canonicalRep (coxeterSystem Tag.E7) L a⁻¹ =
        (canonicalRep (coxeterSystem Tag.E7) L a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, inv_mul_cancel, canonicalRep_one]
  have hconj_fixed : ∀ v : WeylGroup Tag.E7,
      Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem Tag.E7) L v * g0⁻¹) =
        g0 * canonicalRep (coxeterSystem Tag.E7) L v * g0⁻¹ := by
    intro v
    have hwv : (w * v) * w⁻¹ = v := by
      rw [← hcent v]; group
    have hkey : canonicalRep (coxeterSystem Tag.E7) L w *
        canonicalRep (coxeterSystem Tag.E7) L v *
        (canonicalRep (coxeterSystem Tag.E7) L w)⁻¹ =
        canonicalRep (coxeterSystem Tag.E7) L v := by
      rw [← hinv, ← hmul, ← hmul, hwv]
    calc Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem Tag.E7) L v * g0⁻¹)
        = (g0 * canonicalRep (coxeterSystem Tag.E7) L w) *
            canonicalRep (coxeterSystem Tag.E7) L v *
            (g0 * canonicalRep (coxeterSystem Tag.E7) L w)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg0, hFr_canon v]
      _ = g0 * canonicalRep (coxeterSystem Tag.E7) L v * g0⁻¹ := by
          rw [show (g0 * canonicalRep (coxeterSystem Tag.E7) L w) *
                canonicalRep (coxeterSystem Tag.E7) L v *
                (g0 * canonicalRep (coxeterSystem Tag.E7) L w)⁻¹ =
              g0 * (canonicalRep (coxeterSystem Tag.E7) L w *
                canonicalRep (coxeterSystem Tag.E7) L v *
                (canonicalRep (coxeterSystem Tag.E7) L w)⁻¹) * g0⁻¹ by group,
            hkey]
  have hClFix : Subgroup.closure (Set.range x) ≤ Fix := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact hconj_fixed (simple Tag.E7 i)
  have hXFix : X ≤ Fix := sup_le hJFix hClFix
  have hXC : X ≤ adjointGroup .E7 L :=
    hXM.trans (map_baseChangeGL_adjointGroup_le M.subtype)
  have hXF : ∀ y ∈ X, Units.map (entrywiseHom Fr) y = y := fun y hy => hXFix hy
  have hrel := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect
    (τ := Tag.E7) (K := K) (L := L) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1
  exact ⟨X, hXfin, le_sup_left, hrel, fun i =>
    (show Subgroup.closure (Set.range x) ≤ J ⊔ Subgroup.closure (Set.range x) from
      le_sup_right) (Subgroup.subset_closure ⟨i, rfl⟩)⟩

private noncomputable def e7emb (K : Type) [Field K] :
    ↥(adjointGroup .E7 K) →* ModGL .E7 (AlgebraicClosure K) :=
  (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E7 K).subtype

private theorem e7emb_injective {K : Type} [Field K] :
    Function.Injective (e7emb K) := by
  intro a b h
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h)

private noncomputable def e7embTo (K : Type) [Field K]
    (X : Subgroup (ModGL .E7 (AlgebraicClosure K)))
    (h : (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ≤ X) :
    ↥(adjointGroup .E7 K) →* ↥X :=
  (e7emb K).codRestrict X (fun c => h ⟨(c : ModGL .E7 K), c.2, rfl⟩)

private theorem e7embTo_injective {K : Type} [Field K]
    (X : Subgroup (ModGL .E7 (AlgebraicClosure K)))
    (h : (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ≤ X) :
    Function.Injective (e7embTo K X h) :=
  fun _ _ hab => e7emb_injective (Subtype.ext_iff.mp hab)

private theorem e7embTo_range {K : Type} [Field K]
    (X : Subgroup (ModGL .E7 (AlgebraicClosure K)))
    (h : (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ≤ X) :
    (e7embTo K X h).range =
      ((adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).subgroupOf X := by
  ext y
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(c : ModGL .E7 K), c.2, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

theorem weylIrred_E7_of_langFrame
    {p : ℕ} [Fact p.Prime] (hp35 : p = 3 ∨ p = 5)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hF : LangFrameData .E7 p K E) : GGWeylIrred E := by
  classical
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcent, hζo, hι₀, hrange, hbase⟩ := hF
  let L := AlgebraicClosure K
  obtain ⟨X, hXfin, hJle, hrel, hxmem⟩ :=
    exists_fixedGroup_of_langData (p := p) K w Fr g0 hFr hg0C hg0 hcent
  haveI : Finite X := hXfin
  let n : Fin Tag.E7.rank → ModGL .E7 L :=
    fun i => canonicalRep (coxeterSystem .E7) L (simple Tag.E7 i)
  let m : Fin Tag.E7.rank → ↥X := fun i => ⟨g0 * n i * g0⁻¹, hxmem i⟩
  have hm : ∀ (i : Fin Tag.E7.rank) (s : Fin Tag.E7.rank → ZMod p),
      m i * (e7embTo K X hJle) (ι₀ (Multiplicative.ofAdd s)) * (m i)⁻¹ =
        (e7embTo K X hJle)
          (ι₀ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E7 p (simple Tag.E7 i) s))) := by
    intro i s
    apply Subtype.ext
    change g0 * n i * g0⁻¹ *
        (baseChangeGL (algebraMap K L)
          ((ι₀ (Multiplicative.ofAdd s) : ↥(adjointGroup .E7 K)) : ModGL .E7 K)) *
        (g0 * n i * g0⁻¹)⁻¹ =
      baseChangeGL (algebraMap K L)
        ((ι₀ (Multiplicative.ofAdd (TableBExc.torusAct Tag.E7 p (simple Tag.E7 i) s)) :
          ↥(adjointGroup .E7 K)) : ModGL .E7 K)
    rw [hbase s]
    have hcomp :
        g0 * n i * g0⁻¹ * (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) *
          (g0 * n i * g0⁻¹)⁻¹ =
        g0 * (n i * ExcFrames.frameDiag ζ hζ s * (n i)⁻¹) * g0⁻¹ := by
      group
    rw [hcomp, ExcFrames.canonicalRep_conj_frameDiag]
    exact (hbase (TableBExc.torusAct Tag.E7 p (simple Tag.E7 i) s)).symm
  have hidx : (e7embTo K X hJle).range.index ∣ 2 := by
    rw [e7embTo_range]
    change ((adjointGroup .E7 K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ 2
    exact hrel
  exact weylIrred_of_embedding (e7embTo K X hJle) (e7embTo_injective (K := K) X hJle) hidx
    (by decide) E ι₀ hι₀ hrange m hm
    (fun U hU => latticeIrred_E7 hp35 U hU)

end Irred937

end CFSG.StandardType

end
