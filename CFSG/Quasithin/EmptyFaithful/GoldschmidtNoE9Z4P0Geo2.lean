module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Geo
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Rk

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P P₁ P₂ : Subgroup (MulAut V)}

theorem singular_transitive (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) {v w : V}
    (hv₁ : v ∉ commV P₁) (hv₂ : v ∉ commV P₂) (hw₁ : w ∉ commV P₁) (hw₂ : w ∉ commV P₂) :
    ∃ a ∈ P, a v = w := by
  have hr := h.rk_commV_plane hp
  obtain ⟨hP₁, hP₂, hc₁, hc₂, -, -, hcsup, hf₁, hf₂, -⟩ := hp
  have hv : v ∈ commV P₁ ⊔ commV P₂ := by rw [hcsup]; exact Subgroup.mem_top v
  have hw : w ∈ commV P₁ ⊔ commV P₂ := by rw [hcsup]; exact Subgroup.mem_top w
  obtain ⟨v₁, hv₁', v₂, hv₂', rfl⟩ := Subgroup.mem_sup.mp hv
  obtain ⟨w₁, hw₁', w₂, hw₂', rfl⟩ := Subgroup.mem_sup.mp hw
  have hv₁1 : v₁ ≠ 1 := fun e => hv₂ (by rw [e, one_mul]; exact hv₂')
  have hv₂1 : v₂ ≠ 1 := fun e => hv₁ (by rw [e, mul_one]; exact hv₁')
  have hw₁1 : w₁ ≠ 1 := fun e => hw₂ (by rw [e, one_mul]; exact hw₂')
  have hw₂1 : w₂ ≠ 1 := fun e => hw₁ (by rw [e, mul_one]; exact hw₁')
  obtain ⟨a₁, ha₁, e₁⟩ := h.plane_transitive hc₁ hr.1 hv₁' hw₁' hv₁1 hw₁1
  obtain ⟨a₂, ha₂, e₂⟩ := h.plane_transitive hc₂ hr.2 hv₂' hw₂' hv₂1 hw₂1
  refine ⟨a₁ * a₂, P.mul_mem (hP₁ ha₁) (hP₂ ha₂), ?_⟩
  have h2v₁ : a₂ v₁ = v₁ := hf₁ hv₁' a₂ ha₂
  have h1w₂ : a₁ w₂ = w₂ := hf₂ hw₂' a₁ ha₁
  calc (a₁ * a₂) (v₁ * v₂) = a₁ (a₂ v₁ * a₂ v₂) := by rw [MulAut.mul_apply, map_mul]
    _ = a₁ (v₁ * w₂) := by rw [h2v₁, e₂]
    _ = w₁ * w₂ := by rw [map_mul, e₁, h1w₂]

theorem card_singular (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) :
    Nat.card {v : V // v ∉ commV P₁ ∧ v ∉ commV P₂} = 9 := by
  have hr := h.rk_commV_plane hp
  obtain ⟨-, -, -, -, -, hdisj, hcsup, -⟩ := hp
  have hinf : commV P₁ ⊓ commV P₂ = ⊥ := disjoint_iff.mp hdisj
  have hcardA : Nat.card {c : V // c ∈ commV P₁ ∧ c ≠ 1} = 3 := by
    have := card_ne_one_add_one (commV P₁)
    rw [card_eq_two_pow h.sq, hr.1] at this
    omega
  have hcardB : Nat.card {c : V // c ∈ commV P₂ ∧ c ≠ 1} = 3 := by
    have := card_ne_one_add_one (commV P₂)
    rw [card_eq_two_pow h.sq, hr.2] at this
    omega
  have hn₁ : ∀ a b : V, a ∈ commV P₁ → b ∈ commV P₂ → b ≠ 1 → a * b ∉ commV P₁ := by
    intro a b ha hb hb1 hab
    have : b ∈ commV P₁ ⊓ commV P₂ :=
      ⟨by simpa using (commV P₁).mul_mem ((commV P₁).inv_mem ha) hab, hb⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hb1 this
  have hn₂ : ∀ a b : V, a ∈ commV P₁ → b ∈ commV P₂ → a ≠ 1 → a * b ∉ commV P₂ := by
    intro a b ha hb ha1 hab
    have : a ∈ commV P₁ ⊓ commV P₂ := ⟨ha, by
      simpa using (commV P₂).mul_mem hab ((commV P₂).inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact ha1 this
  let f : {c : V // c ∈ commV P₁ ∧ c ≠ 1} × {c : V // c ∈ commV P₂ ∧ c ≠ 1} →
      {v : V // v ∉ commV P₁ ∧ v ∉ commV P₂} := fun p =>
    ⟨p.1.1 * p.2.1, hn₁ _ _ p.1.2.1 p.2.2.1 p.2.2.2, hn₂ _ _ p.1.2.1 p.2.2.1 p.1.2.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha, ha1⟩, ⟨b, hb, hb1⟩⟩ ⟨⟨a', ha', ha1'⟩, ⟨b', hb', hb1'⟩⟩ e
      have e' : a * b = a' * b' := congrArg Subtype.val e
      have hpair := Subgroup.mul_injective_of_disjoint hdisj
        (a₁ := (⟨a, ha⟩, ⟨b, hb⟩)) (a₂ := (⟨a', ha'⟩, ⟨b', hb'⟩)) e'
      have e₁ : a = a' := congrArg (fun p => (p.1 : V)) hpair
      have e₂ : b = b' := congrArg (fun p => (p.2 : V)) hpair
      subst e₁
      subst e₂
      rfl
    · rintro ⟨v, hv₁, hv₂⟩
      have hv : v ∈ commV P₁ ⊔ commV P₂ := by rw [hcsup]; exact Subgroup.mem_top v
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
      have ha1 : a ≠ 1 := fun e => hv₂ (by rw [e, one_mul]; exact hb)
      have hb1 : b ≠ 1 := fun e => hv₁ (by rw [e, mul_one]; exact ha)
      exact ⟨(⟨a, ha, ha1⟩, ⟨b, hb, hb1⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, hcardA, hcardB]

theorem rk_inf_fixV_of_plane (h : E9Z4Str X Tb P) {t : MulAut V} (ht : t ∈ Tb)
    (ht2 : orderOf t = 2) {Q : Subgroup (MulAut V)} (hQ : Q ≤ P) (hQ3 : Nat.card Q = 3)
    (hrk : rk (commV Q) = 2) : rk ↥(commV Q ⊓ fixV (Subgroup.zpowers t)) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htX : t ∈ X := h.Tb_le_X ht
  have htsq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hn := h.zpowers_le_normalizer_of_le htX ht2 hQ
  have hW : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ commV Q, x w ∈ commV Q := fun x hx w hw =>
    commV_smul_mem (fun p hp => (Subgroup.mem_normalizer_iff.mp (hn hx) p).mp hp) hw
  have hsum := rk_commSub_add_rk_inf_fixV hW
  have hle : commSub (commV Q) (Subgroup.zpowers t) ≤ commV Q ⊓ fixV (Subgroup.zpowers t) :=
    commSub_zpowers_le_inf_fixV h.sq htsq hW
  have hle' := rk_mono hle
  have hne : rk ↥(commV Q ⊓ fixV (Subgroup.zpowers t)) ≠ 2 := by
    intro h2
    have hbot : commSub (commV Q) (Subgroup.zpowers t) = ⊥ :=
      (rk_eq_zero_iff h.sq).mp (by omega)
    have hfix : ∀ v ∈ commV Q, t v = v := fun v hv =>
      (commSub_eq_bot_iff.mp hbot) hv t (Subgroup.mem_zpowers t)
    obtain ⟨g, hgQ, hg1, -, hg3⟩ := exists_generator_of_prime_card hQ3
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ commV Q, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      rw [(Subgroup.eq_bot_iff_forall _).2 hcon, rk_bot] at hrk
      omega
    have hgv : g v ∈ commV Q :=
      commV_smul_mem (fun q hq => Q.mul_mem (Q.mul_mem hgQ hq) (Q.inv_mem hgQ)) hv
    have e1 : t (g v) = g v := hfix _ hgv
    have e2 : t (g v) = g⁻¹ v := by
      have htg : t * g = g⁻¹ * t := by
        calc t * g = (t * g * t⁻¹) * t := by group
          _ = g⁻¹ * t := by rw [h.inverts_of_involution htX ht2 g (hQ hgQ)]
      calc t (g v) = (t * g) v := rfl
        _ = (g⁻¹ * t) v := by rw [htg]
        _ = g⁻¹ (t v) := rfl
        _ = g⁻¹ v := by rw [hfix v hv]
    have e3 : (g * g) v = v := by
      calc (g * g) v = g (g v) := rfl
        _ = g (g⁻¹ v) := by rw [e1.symm.trans e2]
        _ = v := by simp
    have hgg1 : g * g ≠ 1 := by
      intro e
      have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact e
      have := orderOf_dvd_of_pow_eq_one hg2
      rw [hg3] at this
      omega
    exact hv1 (h.eq_one_of_fix_plane hQ3 (Q.mul_mem hgQ hgQ) hgg1 hv e3)
  omega

theorem fixV_Tb (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) :
    rk (fixV Tb) = 1 ∧ ∀ v ∈ fixV Tb, v ≠ 1 → v ∉ commV P₁ ∧ v ∉ commV P₂ := by
  obtain ⟨t, htT, ht2, -⟩ := h.inv
  obtain ⟨g, hgT, hg4, -⟩ := h.exists_gen htT ht2
  have hTb : Subgroup.zpowers g = Tb := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hgT) (by rw [Nat.card_zpowers, hg4, h.card_Tb])
  refine ⟨?_, ?_⟩
  · rw [← hTb]
    exact h.rk_fixV_of_orderOf_four (h.Tb_le_X hgT) hg4
  · obtain ⟨-, -, -, -, -, hdisj, -, -, -, σ, hσ, hσP⟩ := hp
    have hinf : commV P₁ ⊓ commV P₂ = ⊥ := disjoint_iff.mp hdisj
    have hσB : commV P₂ = (commV P₁).map (MulEquiv.toMonoidHom σ) := by
      rw [← hσP, commV_conjBy]
    intro v hv hv1
    have hσv : σ v = v := hv σ hσ
    have hσv' : σ⁻¹ v = v := hv σ⁻¹ (Tb.inv_mem hσ)
    constructor
    · intro h1
      have h2 : v ∈ commV P₂ := by
        rw [hσB]
        exact ⟨v, h1, hσv⟩
      have : v ∈ commV P₁ ⊓ commV P₂ := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact hv1 this
    · intro h2
      have h2' := h2
      rw [hσB] at h2'
      obtain ⟨z, hz, hzv⟩ := h2'
      have hzv' : σ z = v := hzv
      have hz' : z = v := by
        calc z = σ⁻¹ (σ z) := by simp
          _ = σ⁻¹ v := by rw [hzv']
          _ = v := hσv'
      have : v ∈ commV P₁ ⊓ commV P₂ := ⟨hz' ▸ hz, h2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact hv1 this

end E9Z4Str

end CFSG.Quasithin
