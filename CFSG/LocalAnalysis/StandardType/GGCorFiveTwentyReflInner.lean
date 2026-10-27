module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace ReflInner

section Lift

variable {L' R : Type*} [Group L'] [Group R] {ψ : L' →* R}

theorem conj_eq_conj_of_map_eq (hker : ψ.ker ≤ Subgroup.center L') {x y : L'}
    (h : ψ x = ψ y) : MulAut.conj x = MulAut.conj y := by
  have hk : x⁻¹ * y ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc := Subgroup.mem_center_iff.mp (hker hk)
  ext g
  rw [MulAut.conj_apply, MulAut.conj_apply]
  calc x * g * x⁻¹ = x * (g * (x⁻¹ * y)) * (x⁻¹ * y)⁻¹ * x⁻¹ := by group
    _ = x * ((x⁻¹ * y) * g) * (x⁻¹ * y)⁻¹ * x⁻¹ := by rw [hc g]
    _ = y * g * y⁻¹ := by group

theorem map_eq_of_conj_eq (hψ : Function.Surjective ψ) (hR : Subgroup.center R = ⊥) {x y : L'}
    (h : MulAut.conj x = MulAut.conj y) : ψ x = ψ y := by
  have hc : ∀ g : L', g * (x⁻¹ * y) = (x⁻¹ * y) * g := by
    intro g
    have e : x * g * x⁻¹ = y * g * y⁻¹ := by
      have := congrArg (fun φ : MulAut L' => φ g) h
      simpa only [MulAut.conj_apply] using this
    calc g * (x⁻¹ * y) = x⁻¹ * (x * g * x⁻¹) * y := by group
      _ = x⁻¹ * (y * g * y⁻¹) * y := by rw [e]
      _ = x⁻¹ * y * g := by group
  have hz : ψ (x⁻¹ * y) ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨g, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul, hc g]
  rw [hR, Subgroup.mem_bot, map_mul, map_inv, inv_mul_eq_one] at hz
  exact hz

variable (ψ) in
@[expose] noncomputable def liftConj (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') : R →* MulAut L' where
  toFun e := MulAut.conj (Function.surjInv hψ e)
  map_one' := (conj_eq_conj_of_map_eq hker (y := 1)
    (by rw [Function.surjInv_eq hψ, map_one])).trans (map_one _)
  map_mul' e₁ e₂ := (conj_eq_conj_of_map_eq hker
    (y := Function.surjInv hψ e₁ * Function.surjInv hψ e₂)
    (by rw [map_mul, Function.surjInv_eq hψ, Function.surjInv_eq hψ,
      Function.surjInv_eq hψ])).trans (map_mul _ _ _)

theorem liftConj_eq (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') {e : R}
    {x : L'} (hx : ψ x = e) : liftConj ψ hψ hker e = MulAut.conj x :=
  conj_eq_conj_of_map_eq hker (by rw [Function.surjInv_eq hψ, hx])

theorem map_liftConj_apply (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : R) (l : L') : ψ (liftConj ψ hψ hker e l) = e * ψ l * e⁻¹ := by
  obtain ⟨x, rfl⟩ := hψ e
  rw [liftConj_eq hψ hker rfl, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem liftConj_injective (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hR : Subgroup.center R = ⊥) : Function.Injective (liftConj ψ hψ hker) := by
  intro e₁ e₂ h
  obtain ⟨x, rfl⟩ := hψ e₁
  obtain ⟨y, rfl⟩ := hψ e₂
  rw [liftConj_eq hψ hker rfl, liftConj_eq hψ hker rfl] at h
  exact map_eq_of_conj_eq hψ hR h

theorem mul_liftConj_mul_inv (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {γ : MulAut L'} {γ' : MulAut R} (hγ : ∀ l, γ' (ψ l) = ψ (γ l)) (e : R) :
    γ * liftConj ψ hψ hker e * γ⁻¹ = liftConj ψ hψ hker (γ' e) := by
  obtain ⟨x, rfl⟩ := hψ e
  rw [liftConj_eq hψ hker rfl, liftConj_eq hψ hker (hγ x).symm]
  ext l
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

end Lift

theorem pow_eq_one_of_zmod {p k : ℕ} (f : Fin k → Multiplicative (ZMod p)) : f ^ p = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

section Conj

variable {R : Type*} [Group R] {p k : ℕ}

theorem torusBasis_conj_comp (τ : (Fin k → Multiplicative (ZMod p)) →* R) (x : R) (i : Fin k) :
    TableBSymp.torusBasis ((MulAut.conj x).toMonoidHom.comp τ) i =
      x * TableBSymp.torusBasis τ i * x⁻¹ :=
  rfl

theorem hinv_conj_comp (τ : (Fin k → Multiplicative (ZMod p)) →* R)
    (hinv : ∀ i j : Fin k, ∃ w : R, w * TableBSymp.torusBasis τ i * w⁻¹ =
      (TableBSymp.torusBasis τ i)⁻¹ ∧
      (j ≠ i → w * TableBSymp.torusBasis τ j * w⁻¹ = TableBSymp.torusBasis τ j)) (x : R) :
    ∀ i j : Fin k, ∃ w : R,
      w * TableBSymp.torusBasis ((MulAut.conj x).toMonoidHom.comp τ) i * w⁻¹ =
        (TableBSymp.torusBasis ((MulAut.conj x).toMonoidHom.comp τ) i)⁻¹ ∧
      (j ≠ i → w * TableBSymp.torusBasis ((MulAut.conj x).toMonoidHom.comp τ) j * w⁻¹ =
        TableBSymp.torusBasis ((MulAut.conj x).toMonoidHom.comp τ) j) := by
  intro i j
  obtain ⟨w, hw1, hw2⟩ := hinv i j
  refine ⟨x * w * x⁻¹, ?_, fun hji => ?_⟩
  · rw [torusBasis_conj_comp]
    calc x * w * x⁻¹ * (x * TableBSymp.torusBasis τ i * x⁻¹) * (x * w * x⁻¹)⁻¹ =
          x * (w * TableBSymp.torusBasis τ i * w⁻¹) * x⁻¹ := by group
      _ = (x * TableBSymp.torusBasis τ i * x⁻¹)⁻¹ := by rw [hw1]; group
  · rw [torusBasis_conj_comp]
    calc x * w * x⁻¹ * (x * TableBSymp.torusBasis τ j * x⁻¹) * (x * w * x⁻¹)⁻¹ =
          x * (w * TableBSymp.torusBasis τ j * w⁻¹) * x⁻¹ := by group
      _ = x * TableBSymp.torusBasis τ j * x⁻¹ := by rw [hw2 hji]

end Conj

section Fixed

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_fixed_of_pseudoRefl (hp : 1 < p) {E : Subgroup G} [Finite E]
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {β' : MulAut G} (hβE : ∀ e ∈ E, β' e ∈ E)
    (hfix : Nat.card {e : E // β' e = e} * p = Nat.card E) {m : ℕ}
    (τ : (Fin m → Multiplicative (ZMod p)) →* G) (hτE : ∀ f, τ f ∈ E) {a b : Fin m}
    (hab : a ≠ b) :
    ∃ f : Fin m → Multiplicative (ZMod p), f ≠ 1 ∧ (∀ i, i ≠ a → i ≠ b → f i = 1) ∧
      β' (τ f) = τ f := by
  classical
  set δ : E →* E := MonoidHom.mk' (fun e => ⟨β' e * (e : G)⁻¹, E.mul_mem (hβE _ e.2)
    (E.inv_mem e.2)⟩) (fun x y => by
      apply Subtype.ext
      change β' ((x : G) * y) * ((x : G) * y)⁻¹ = β' x * (x : G)⁻¹ * (β' y * (y : G)⁻¹)
      have hc := hEc _ (E.mul_mem (hβE _ y.2) (E.inv_mem y.2)) _ (E.inv_mem x.2)
      calc β' ((x : G) * y) * ((x : G) * y)⁻¹ = β' x * ((β' y * (y : G)⁻¹) * (x : G)⁻¹) := by
            rw [map_mul]; group
        _ = β' x * ((x : G)⁻¹ * (β' y * (y : G)⁻¹)) := by rw [hc]
        _ = β' x * (x : G)⁻¹ * (β' y * (y : G)⁻¹) := by group) with hδ
  have hδapp : ∀ e : E, ((δ e : E) : G) = β' e * (e : G)⁻¹ := fun e => rfl
  have hker : Nat.card δ.ker = Nat.card {e : E // β' e = e} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, hδapp, Subgroup.coe_one, mul_inv_eq_one]
  have hpos : 0 < Nat.card {e : E // β' e = e} := by
    have : Nonempty {e : E // β' e = e} := ⟨⟨1, by rw [Subgroup.coe_one, map_one]⟩⟩
    exact Nat.card_pos
  have hrange : Nat.card δ.range = p := by
    have h1 := TableB.card_range_mul_card_ker δ
    rw [hker, ← hfix, mul_comm _ p] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  obtain ⟨g, hg⟩ : ∃ g : ZMod p × ZMod p → (Fin m → Multiplicative (ZMod p)), g = fun kl =>
      Pi.mulSingle a (Multiplicative.ofAdd kl.1) * Pi.mulSingle b (Multiplicative.ofAdd kl.2) :=
    ⟨_, rfl⟩
  set F : ZMod p × ZMod p → δ.range := fun kl => δ.rangeRestrict ⟨τ (g kl), hτE _⟩ with hF
  obtain ⟨u, v, huv, hne⟩ : ∃ u v, F u = F v ∧ u ≠ v := by
    by_contra hcon
    push Not at hcon
    have h1 := Nat.card_le_card_of_injective F fun u v h => hcon u v h
    have : NeZero p := ⟨by omega⟩
    rw [hrange, Nat.card_prod, Nat.card_zmod] at h1
    nlinarith
  have hδuv : δ ⟨τ (g u), hτE _⟩ = δ ⟨τ (g v), hτE _⟩ := congrArg Subtype.val huv
  refine ⟨g u * (g v)⁻¹, fun h1 => hne ?_, fun i hia hib => ?_, ?_⟩
  · have hga : ∀ kl : ZMod p × ZMod p, g kl a = Multiplicative.ofAdd kl.1 := fun kl => by
      simp only [hg, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab, mul_one]
    have hgb : ∀ kl : ZMod p × ZMod p, g kl b = Multiplicative.ofAdd kl.2 := fun kl => by
      simp only [hg, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hab),
        one_mul]
    have h2 : g u = g v := mul_inv_eq_one.mp h1
    have h3 := congrFun h2 a
    have h4 := congrFun h2 b
    rw [hga, hga] at h3
    rw [hgb, hgb] at h4
    exact Prod.ext (Multiplicative.ofAdd.injective h3) (Multiplicative.ofAdd.injective h4)
  · simp only [hg, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hia,
      Pi.mulSingle_eq_of_ne hib, mul_one]
    exact mul_inv_cancel _
  · have h1 : δ (⟨τ (g u), hτE _⟩ * (⟨τ (g v), hτE _⟩ : E)⁻¹) = 1 := by
      rw [map_mul, map_inv, hδuv, mul_inv_cancel]
    have h2 := congrArg Subtype.val h1
    rw [hδapp, Subgroup.coe_one, mul_inv_eq_one] at h2
    have h3 : ((⟨τ (g u), hτE _⟩ * (⟨τ (g v), hτE _⟩ : E)⁻¹ : E) : G) = τ (g u * (g v)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul_inv τ (g u) (g v)]
    rw [← h3]
    exact h2

end Fixed

end ReflInner

@[expose] def GGTorusReflCore (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∀ β' : MulAut R, (∀ e ∈ E, β' e ∈ E) → (∀ e ∈ E, (β' ^ (p - 1)) e = e) →
      Nat.card {e : E // β' e = e} * p = Nat.card E →
      ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), (∀ e ∈ E, ∃ f, τ f = e) ∧
        (∀ i j : Fin k, ∃ w : R, w * TableBSymp.torusBasis τ i * w⁻¹ =
          (TableBSymp.torusBasis τ i)⁻¹ ∧
          (j ≠ i → w * TableBSymp.torusBasis τ j * w⁻¹ = TableBSymp.torusBasis τ j)) ∧
        ∃ w : R, ∀ e ∈ E, w * e * w⁻¹ = β' e

theorem ggTorusReflBridge_of_core {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (hR : Subgroup.center R = ⊥)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (h : GGTorusReflCore p r R) :
    GGTorusReflBridge p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 β β' hββ' hN hpow hfix
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hΛconj⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) ∧
      (∀ {γ : MulAut L'} {γ' : MulAut R}, (∀ l, γ' (ψ l) = ψ (γ l)) →
        ∀ e, γ * Λ e * γ⁻¹ = Λ (γ' e)) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hR, ReflInner.map_liftConj_apply hψ hker,
      fun hγ e => ReflInner.mul_liftConj_mul_inv hψ hker hγ e⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hβE : ∀ e ∈ E, β' e ∈ E := fun e he => by
    show Λ (β' e) ∈ A
    rw [← hΛconj hββ']
    exact hN _ he
  have hpowE : ∀ e ∈ E, (β' ^ (p - 1)) e = e := by
    intro e he
    apply hΛinj
    rw [← hΛconj (TypeA.induced_pow ψ hββ' (p - 1))]
    exact hpow _ he
  have hfixE : Nat.card {e : E // β' e = e} * p = Nat.card E := by
    rw [hcardE, ← hfix]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hΦbij) fun e => ?_)
    change β' e = e ↔ β * Λ e * β⁻¹ = Λ e
    rw [hΛconj hββ']
    exact ⟨fun h => by rw [h], fun h => hΛinj h⟩
  obtain ⟨k, τ, hτE, hinv, w, hw⟩ :=
    h E hEab (hcardE ▸ hr) (hcardE ▸ h3) β' hβE hpowE hfixE
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ hker (hp.odd_of_ne_two hp2) τ hinv
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => by rw [← MonoidHom.comp_apply, hσ]
  obtain ⟨n, hn⟩ := hψ w
  have hAσ : ∀ a ∈ A, ∃ f, τ f ∈ E ∧ a = MulAut.conj (σ f) := by
    intro a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have he : e ∈ E := ha
    obtain ⟨f, rfl⟩ := hτE e he
    exact ⟨f, he, hΛeq (hψσ f)⟩
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨n, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨f, hfE, rfl⟩ := hAσ a ha
    obtain ⟨f', hf'⟩ := hτE _ (hβE _ hfE)
    set z := (σ f')⁻¹ * (n * σ f * n⁻¹) with hz
    have hzk : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, hψσ, hψσ, hn,
        hf', hw _ hfE, inv_mul_cancel]
    have hzc := Subgroup.mem_center_iff.mp (hker hzk)
    have hrel : n * (MulAut.conj (σ f) n)⁻¹ = σ (f' * f⁻¹) * z := by
      rw [MulAut.conj_apply, map_mul, map_inv, mul_assoc (σ f'), hzc (σ f)⁻¹, hz]
      group
    have hzp : z ^ p = 1 := by
      have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
        rw [conj_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel]
      have h2 : n * σ f * n⁻¹ = σ f' * z := by rw [hz, mul_inv_cancel_left]
      rw [h2, (show Commute (σ f') z from hzc (σ f')).mul_pow, ← map_pow,
        ReflInner.pow_eq_one_of_zmod, map_one, one_mul] at h1
      exact h1
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [hrel, (show Commute (σ (f' * f⁻¹)) z from hzc _).mul_pow, ← map_pow,
        ReflInner.pow_eq_one_of_zmod, map_one, one_mul, hzp]
    · obtain ⟨g, -, rfl⟩ := hAσ a' ha'
      rw [hrel, MulAut.conj_apply]
      calc σ g * (σ (f' * f⁻¹) * z) * (σ g)⁻¹ = σ (f' * f⁻¹) * (σ g * z) * (σ g)⁻¹ := by
            rw [← mul_assoc, hσc]; group
        _ = σ (f' * f⁻¹) * (z * σ g) * (σ g)⁻¹ := by rw [hzc]
        _ = σ (f' * f⁻¹) * z := by group
  · obtain ⟨e, rfl⟩ := hAΛ a ha
    have he : e ∈ E := ha
    rw [hΛconj hββ']
    obtain ⟨x, rfl⟩ := hψ e
    rw [hΛeq rfl, ← map_inv MulAut.conj n, ← map_mul MulAut.conj, ← map_mul MulAut.conj]
    refine (hΛeq ?_).symm
    rw [map_mul, map_mul, map_inv, hn, hw _ he]

end CFSG.StandardType

end
