module

public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGDepAArith
public import CFSG.LocalAnalysis.StandardType.GGDepARefl
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
public import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nDA1_data {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 11 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hjoin : ∃ c, αa (h c) ≠ 0)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hnH : ha ∉ Submodule.span (ZMod p) (Set.range h)) :
    ∃ (U : Submodule (ZMod p) V) (AU : Subgroup (↥U ≃ₗ[ZMod p] ↥U))
      (ψ : Equiv.Perm (Fin N) →* ↥AU),
      Module.finrank (ZMod p) ↥U = N - 1 ∧ ZS.AbsIrred p AU ∧
        AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t} ∧
        Nat.card ↥AU ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) ∧ Function.Injective ψ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hN5 : 5 ≤ N := by omega
  haveI : NeZero (N - 1) := ⟨by omega⟩
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let U : Submodule (ZMod p) V := H ⊔ Submodule.span (ZMod p) ({ha} : Set V)
  have hhU : ∀ i, h i ∈ U := fun i =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
  have haU : ha ∈ U := Submodule.mem_sup_right (Submodule.mem_span_singleton_self ha)
  have hdimU : Module.finrank (ZMod p) ↥U = N - 1 := by
    have hrel := ggDepA_relation F
    have hdimH : Module.finrank (ZMod p) ↥H = N - 2 := hrel.2.2
    have hinf : H ⊓ Submodule.span (ZMod p) ({ha} : Set V) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvH, hvS⟩ := hv
      rw [Submodule.mem_span_singleton] at hvS
      obtain ⟨c, hc⟩ := hvS
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hc
        exact hc.symm
      · exfalso
        apply hnH
        have hha : ha = c⁻¹ • (c • ha) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hc] at hha
        rw [hha]
        exact H.smul_mem c⁻¹ hvH
    have hspan1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({ha} : Set V)) = 1 := by
      rw [finrank_span_singleton]
      intro hha0
      exact hnH (by rw [hha0]; exact H.zero_mem)
    have h := Submodule.finrank_sup_add_finrank_inf_eq H
      (Submodule.span (ZMod p) ({ha} : Set V))
    rw [hinf, finrank_bot, add_zero, hdimH, hspan1] at h
    change Module.finrank (ZMod p) ↥(H ⊔ Submodule.span (ZMod p) ({ha} : Set V)) = N - 1
    omega
  let S : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hS : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U := by
    intro s hs u hu
    rcases hs with ⟨i, rfl⟩ | rfl
    · rw [hr i u]
      exact U.sub_mem hu (U.smul_mem (α i u) (hhU i))
    · rw [hra u]
      exact U.sub_mem hu (U.smul_mem (αa u) haU)
  obtain ⟨res, he_apply, hcard_res, hrange_res⟩ := ggDepA_restrict U S hS
  have hraS : ra ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  have hrS : ∀ i, r i ∈ Subgroup.closure S := fun i =>
    Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  let gU : Option (Fin (N - 1)) → (↥U ≃ₗ[ZMod p] ↥U) := fun o =>
    match o with
    | none => res ⟨ra, hraS⟩
    | some i => res ⟨r i, hrS i⟩
  have hAU_closure : res.range = Subgroup.closure (Set.range gU) := by
    have hset : Set.range gU = {t | ∃ (s : V ≃ₗ[ZMod p] V) (hs : s ∈ S),
        t = res ⟨s, Subgroup.subset_closure hs⟩} := by
      ext t; constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact ⟨ra, Or.inr rfl, rfl⟩
        | some i => exact ⟨r i, Or.inl ⟨i, rfl⟩, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        rcases hs with ⟨i, rfl⟩ | rfl
        · exact ⟨some i, rfl⟩
        · exact ⟨none, rfl⟩
    rw [hrange_res, hset]
  let sU : Option (Fin (N - 1)) → V := fun o =>
    match o with
    | none => ha
    | some i => h i
  have hsU : ∀ o, sU o ∈ U := by
    intro o; cases o with
    | none => exact haU
    | some i => exact hhU i
  let hU : Option (Fin (N - 1)) → ↥U := fun o => ⟨sU o, hsU o⟩
  let αU : Option (Fin (N - 1)) → Module.Dual (ZMod p) ↥U := fun o =>
    match o with
    | none => αa.comp U.subtype
    | some i => (α i).comp U.subtype
  have hspan_range : Submodule.span (ZMod p) (Set.range sU) = U := by
    have hrange : Set.range sU = Set.range h ∪ ({ha} : Set V) := by
      ext v; constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact Or.inr rfl
        | some i => exact Or.inl ⟨i, rfl⟩
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨some i, rfl⟩
        · exact ⟨none, rfl⟩
    rw [hrange, Submodule.span_union]
  have hspanU : Submodule.span (ZMod p) (Set.range hU) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff U hsU).mpr hspan_range
  have hαdiag : ∀ i, α i (h i) = 2 := by
    intro i
    rw [F.pair i i]
    have hdiag : CartanMatrix.A (N - 1) i i = 2 := by
      simp [CartanMatrix.A, Matrix.of_apply]
    rw [hdiag]
    norm_num
  have hαU : ∀ o, αU o (hU o) = 2 := by
    intro o; cases o with
    | none => exact hαa
    | some i => exact hαdiag i
  have hgUapply : ∀ o u, gU o u = u - αU o u • hU o := by
    intro o u
    cases o with
    | none =>
      apply Subtype.ext
      show (((res ⟨ra, hraS⟩) u : ↥U) : V) = ((u - αU none u • hU none : ↥U) : V)
      rw [he_apply]
      show ra (u : V) = ((u - αU none u • hU none : ↥U) : V)
      rw [hra]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, sU, LinearMap.comp_apply,
        Submodule.subtype_apply]
    | some i =>
      apply Subtype.ext
      show (((res ⟨r i, hrS i⟩) u : ↥U) : V) = ((u - αU (some i) u • hU (some i) : ↥U) : V)
      rw [he_apply]
      show r i (u : V) = ((u - αU (some i) u • hU (some i) : ↥U) : V)
      rw [hr]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, sU, LinearMap.comp_apply,
        Submodule.subtype_apply]
  have hkerU : ∀ w : ↥U, (∀ o, αU o w = 0) → w = 0 := by
    intro w hw0
    have hfix := F.fix (w : V) (fun i => hw0 (some i))
    rw [Submodule.mem_span_singleton] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hcz : c = 0 := by
      have h0 : c * αa x = 0 := by
        have h1 : αa (w : V) = 0 := hw0 none
        rw [← hc, map_smul, smul_eq_mul] at h1
        exact h1
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hw
    apply Subtype.ext
    rw [← hc, hcz, zero_smul]
    rfl
  let R : Option (Fin (N - 1)) → Option (Fin (N - 1)) → Prop :=
    fun a b => αU a (hU b) ≠ 0 ∧ αU b (hU a) ≠ 0
  have hneg1 : (-1 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero]; exact one_ne_zero
  have hA_succ : ∀ i j : Fin (N - 1), i.val + 1 = j.val →
      (CartanMatrix.A (N - 1) i j : ZMod p) = -1 := by
    intro i j hij
    have hne : i ≠ j := by intro hh; have := congrArg Fin.val hh; omega
    have hAi : CartanMatrix.A (N - 1) i j = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inl hij)]
    rw [hAi]; norm_num
  have hA_succ' : ∀ i j : Fin (N - 1), i.val + 1 = j.val →
      (CartanMatrix.A (N - 1) j i : ZMod p) = -1 := by
    intro i j hij
    have hne : j ≠ i := by intro hh; have := congrArg Fin.val hh; omega
    have hAi : CartanMatrix.A (N - 1) j i = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inr hij)]
    rw [hAi]; norm_num
  have hedge : ∀ i j : Fin (N - 1), i.val + 1 = j.val → R (some i) (some j) := by
    intro i j hij
    refine ⟨?_, ?_⟩
    · show α i (h j) ≠ 0
      rw [F.pair i j, hA_succ i j hij]
      exact hneg1
    · show α j (h i) ≠ 0
      rw [F.pair j i, hA_succ' i j hij]
      exact hneg1
  have hchain : ∀ j : Fin (N - 1),
      Relation.ReflTransGen R (some (0 : Fin (N - 1))) (some j) := by
    intro j
    refine Fin.strong_induction_on
      (motive := fun j => Relation.ReflTransGen R (some 0) (some j)) ?_ j
    intro j ih
    by_cases hj : j = 0
    · subst hj; exact Relation.ReflTransGen.refl
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun hh => hj (Fin.ext hh))
      let j' : Fin (N - 1) := ⟨j.val - 1, by omega⟩
      have hlt : j' < j := by
        show j.val - 1 < j.val
        omega
      have hval : j'.val + 1 = j.val := by
        show j.val - 1 + 1 = j.val
        omega
      exact (ih j' hlt).tail (hedge j' j hval)
  obtain ⟨c, hc⟩ := hjoin
  have hRc_none : R (some c) none := by
    refine ⟨?_, ?_⟩
    · show α c ha ≠ 0
      intro h0
      exact hc (ggDepA_pair_zero_symm hp2 (Subgroup.closure S) hnt
        (hrS c) hraS (hr c) hra (hαdiag c) hαa h0)
    · show αa (h c) ≠ 0
      exact hc
  haveI : Std.Symm R := ⟨fun a b hh => ⟨hh.2, hh.1⟩⟩
  have hsymm : ∀ {a b : Option (Fin (N - 1))},
      Relation.ReflTransGen R a b → Relation.ReflTransGen R b a :=
    fun h => Std.Symm.symm _ _ h
  have hnone_c : Relation.ReflTransGen R none (some c) :=
    Relation.ReflTransGen.single ⟨hRc_none.2, hRc_none.1⟩
  have hconnU : ∀ o o' : Option (Fin (N - 1)), Relation.ReflTransGen R o o' := by
    intro o o'
    cases o with
    | none =>
      cases o' with
      | none => exact Relation.ReflTransGen.refl
      | some j => exact hnone_c.trans ((hsymm (hchain c)).trans (hchain j))
    | some i =>
      cases o' with
      | none =>
        exact hsymm (hnone_c.trans ((hsymm (hchain c)).trans (hchain i)))
      | some j =>
        exact (hsymm (hnone_c.trans ((hsymm (hchain c)).trans (hchain i)))).trans
          (hnone_c.trans ((hsymm (hchain c)).trans (hchain j)))
  have hirr : ZS.AbsIrred p res.range :=
    ggRC_absIrred_of_connected hp2 gU hU αU hgUapply hαU hspanU hkerU hconnU res.range hAU_closure
  have hreflU : ∀ o : Option (Fin (N - 1)), GGLinRefl (gU o) := by
    intro o
    rw [ggDepA_linRefl_iff hp2]
    exact ⟨hU o, αU o, hαU o, fun v => hgUapply o v⟩
  have hgen : res.range =
      Subgroup.closure {t : ↥U ≃ₗ[ZMod p] ↥U | t ∈ res.range ∧ GGLinRefl t} := by
    rw [hAU_closure]
    apply le_antisymm
    · apply Subgroup.closure_mono
      intro x hx
      obtain ⟨o, rfl⟩ := hx
      exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hreflU o⟩
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  have hcardAU : Nat.card ↥res.range ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) :=
    le_trans hcard_res hcard
  obtain ⟨ρ, hρr, hρA, hρx, hρf⟩ := ggDepA_perm_embed hp hN5 F r hr
  let ρ' : Equiv.Perm (Fin N) →* ↥(Subgroup.closure S) :=
    { toFun := fun σ => ⟨ρ σ, Subgroup.closure_mono Set.subset_union_left (hρA σ)⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ a b) }
  let ψ : Equiv.Perm (Fin N) →* ↥(res.range) := res.rangeRestrict.comp ρ'
  have hψinj : Function.Injective ψ := by
    intro σ τ hστ
    have hfix : ∀ i, ρ (τ⁻¹ * σ) (h i) = h i := by
      intro i
      have hval : (res (ρ' σ) : ↥U ≃ₗ[ZMod p] ↥U) = res (ρ' τ) := by
        have hh := congrArg Subtype.val hστ
        simpa [ψ, MonoidHom.comp_apply] using hh
      have h1 : (((res (ρ' σ)) (hU (some i)) : ↥U) : V) =
          (((res (ρ' τ)) (hU (some i)) : ↥U) : V) :=
        congrArg (fun (e : ↥U ≃ₗ[ZMod p] ↥U) => ((e (hU (some i)) : ↥U) : V)) hval
      have h3 : ρ σ (h i) = ρ τ (h i) := by
        rw [he_apply, he_apply] at h1
        change ρ σ (h i) = ρ τ (h i) at h1
        exact h1
      calc ρ (τ⁻¹ * σ) (h i)
          = ((ρ τ)⁻¹ * ρ σ) (h i) := by rw [map_mul, map_inv]
        _ = (ρ τ)⁻¹ (ρ σ (h i)) := by rw [LinearEquiv.mul_apply]
        _ = (ρ τ)⁻¹ (ρ τ (h i)) := by rw [h3]
        _ = h i := by simp
    have hone : τ⁻¹ * σ = 1 := hρf (τ⁻¹ * σ) hfix
    exact (inv_mul_eq_one.mp hone).symm
  exact ⟨U, res.range, ψ, hdimU, hirr, hgen, hcardAU, hψinj⟩

private theorem l05nDA1_exclude (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hN : 11 ≤ N) (hpN : p ∣ N) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (hdim : Module.finrank (ZMod p) U = N - 1)
    (AU : Subgroup (U ≃ₗ[ZMod p] U)) (hirr : ZS.AbsIrred p AU)
    (hgen : AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t})
    (hcard : Nat.card ↥AU ≤ p ^ N * (6 * (p - 1) * Nat.factorial N))
    (ψ : Equiv.Perm (Fin N) →* ↥AU) (hψ : Function.Injective ψ) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain himp | hclass | ⟨hndvd, _e1, _he1⟩ | ⟨hdvd, _e2, _he2⟩ :=
    hKG p hp2 U (N - 1) hdim (by omega) AU hirr hgen
  ·
    obtain ⟨b, hmon⟩ :=
      ggRC_monomial_of_imprimitive (p := p) (n := N - 1) hdim AU hirr hgen himp
    obtain ⟨π, _hπ, _hπker, hπcomm, _hπp⟩ := ggRC_monomial_hom b AU hmon
    let π' : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 1)) := π.comp ψ
    have hπ'comm : IsMulCommutative π'.ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hψ
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
        ⟨ψ (a : Equiv.Perm (Fin N)), a.2⟩
        ⟨ψ (b : Equiv.Perm (Fin N)), b.2⟩)
    exact ggRC_perm_not_monomial (N := N) (m := N - 1) (by omega) (by omega) π' hπ'comm
  ·
    have hle : (N - 2) * (N - 3) / 2 ≤ (N - 1) * (N - 1 - 1) / 2 := by
      apply Nat.div_le_div_right
      have h1 : N - 1 - 1 = N - 2 := by omega
      rw [h1]
      calc (N - 2) * (N - 3) ≤ (N - 2) * (N - 1) :=
            Nat.mul_le_mul_left (N - 2) (by omega)
        _ = (N - 1) * (N - 2) := Nat.mul_comm (N - 2) (N - 1)
    have hpow : p ^ ((N - 2) * (N - 3) / 2) ≤ p ^ ((N - 1) * (N - 1 - 1) / 2) :=
      Nat.pow_le_pow_right (by omega) hle
    have hchain : p ^ ((N - 2) * (N - 3) / 2) ≤
        8 * (p ^ N * (6 * (p - 1) * Nat.factorial N)) :=
      hpow.trans (hclass.trans (Nat.mul_le_mul_left 8 hcard))
    exact absurd (lt_of_le_of_lt hchain (ggDepA_order_ineq hp hN)) (lt_irrefl _)
  ·
    have hN1 : N - 1 + 1 = N := by omega
    exact hndvd (hN1.symm ▸ hpN)
  ·
    have hN2 : N - 1 + 2 = N + 1 := by omega
    have hdvd' : p ∣ N + 1 := hN2 ▸ hdvd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpN).mp hdvd'
    have hp1 : ¬ p ∣ 1 := by
      intro h
      have := Nat.le_of_dvd (by norm_num : 0 < 1) h
      omega
    exact hp1 h1

theorem ggDepA_caseI_false (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hN : 11 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hjoin : ∃ c, αa (h c) ≠ 0)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hnH : ha ∉ Submodule.span (ZMod p) (Set.range h)) : False := by
  obtain ⟨U, AU, ψ, hdim, hirr, hgen, hcardU, hψ⟩ :=
    l05nDA1_data hp hN F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH
  haveI : Module.Finite (ZMod p) ↥U :=
    Module.Finite.of_injective (Submodule.subtype U) U.subtype_injective
  exact l05nDA1_exclude hKG hp hN F.dvd hdim AU hirr hgen hcardU ψ hψ

end CFSG.StandardType
