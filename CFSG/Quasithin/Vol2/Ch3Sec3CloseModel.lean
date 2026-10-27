module

public import CFSG.Quasithin.Vol2.Ch3Sec3ModelA2
public import CFSG.Quasithin.Vol2.Ch3Sec3Offenders
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Transport

public section

namespace CFSG.Quasithin.H13.CloseModel

open CFSG.Open CFSG.Quasithin A6Coc ModelA2 S6Syl

variable {G : Type} [Group G]

structure Model (T Q : Subgroup G) where
  ρ : ↥T →* Equiv.Perm (Fin 6)
  θ : ↥Q ≃ AltHeart 6
  hQT : Q ≤ T
  hQN : T ≤ Subgroup.normalizer (Q : Set G)
  hker : ∀ t : ↥T, ρ t = 1 ↔ (t : G) ∈ Q
  hθ : ∀ (t : ↥T) (q q' : ↥Q), (q' : G) = t * q * t⁻¹ → θ q' = heartAct 6 (ρ t) (θ q)

variable {T Q : Subgroup G} (D : Model T Q)

namespace Model

@[expose] noncomputable def img (Y : Subgroup G) : Subgroup (Equiv.Perm (Fin 6)) :=
  (Y.subgroupOf T).map D.ρ

theorem mem_img {Y : Subgroup G} {σ : Equiv.Perm (Fin 6)} :
    σ ∈ D.img Y ↔ ∃ t : ↥T, (t : G) ∈ Y ∧ D.ρ t = σ := by
  simp only [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem relIndex_eq {Y : Subgroup G} (hYT : Y ≤ T) :
    Q.relIndex Y = Nat.card (D.img Y) := by
  have hk : D.ρ.ker = Q.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, D.hker, Subgroup.mem_subgroupOf]
  rw [img, ← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf hYT]

include D in
theorem conj_mem (t : ↥T) (q : ↥Q) : (t : G) * q * (t : G)⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (D.hQN t.2) q).mp q.2

theorem comm_iff (t : ↥T) (q : ↥Q) :
    (t : G) * q = q * t ↔ heartAct 6 (D.ρ t) (D.θ q) = D.θ q := by
  rw [← D.hθ t q ⟨_, D.conj_mem t q⟩ rfl, D.θ.injective.eq_iff, Subtype.ext_iff]
  constructor
  · intro h
    show (t : G) * q * (t : G)⁻¹ = q
    rw [h, mul_inv_cancel_right]
  · intro h
    have h' : (t : G) * q * (t : G)⁻¹ = q := h
    calc (t : G) * q = (t : G) * q * (t : G)⁻¹ * t := by group
      _ = q * t := by rw [h']

theorem card_fix (Y : Subgroup G) (hYT : Y ≤ T) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) =
      Nat.card {w : AltHeart 6 // ∀ σ ∈ D.img Y, heartAct 6 σ w = w} := by
  have key : ∀ q : ↥Q, (q : G) ∈ Subgroup.centralizer (Y : Set G) ↔
      ∀ σ ∈ D.img Y, heartAct 6 σ (D.θ q) = D.θ q := by
    intro q
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h σ hσ
      obtain ⟨t, htY, rfl⟩ := D.mem_img.mp hσ
      exact (D.comm_iff t q).mp (h t htY)
    · intro h y hy
      exact (D.comm_iff ⟨y, hYT hy⟩ q).mpr (h _ (D.mem_img.mpr ⟨⟨y, hYT hy⟩, hy, rfl⟩))
  let e : ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) ≃
      {w : AltHeart 6 // ∀ σ ∈ D.img Y, heartAct 6 σ w = w} :=
    { toFun := fun x => ⟨D.θ ⟨x, x.2.1⟩, (key ⟨x, x.2.1⟩).mp x.2.2⟩
      invFun := fun w => ⟨(D.θ.symm w : G), (D.θ.symm w).2,
        (key (D.θ.symm w)).mpr (by rw [Equiv.apply_symm_apply]; exact w.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  exact Nat.card_congr e

theorem card_fix_one (t : ↥T) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({(t : G)} : Set G)) =
      Nat.card {w : AltHeart 6 // heartAct 6 (D.ρ t) w = w} := by
  let e : ↥(Q ⊓ Subgroup.centralizer ({(t : G)} : Set G)) ≃
      {w : AltHeart 6 // heartAct 6 (D.ρ t) w = w} :=
    { toFun := fun x => ⟨D.θ ⟨x, x.2.1⟩, (D.comm_iff t ⟨x, x.2.1⟩).mp
        (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm⟩
      invFun := fun w => ⟨(D.θ.symm w : G), (D.θ.symm w).2,
        Subgroup.mem_centralizer_singleton_iff.mpr ((D.comm_iff t (D.θ.symm w)).mpr
          (by rw [Equiv.apply_symm_apply]; exact w.2)).symm⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  exact Nat.card_congr e

theorem card_fix_conj (S : Subgroup (Equiv.Perm (Fin 6))) (g : Equiv.Perm (Fin 6)) :
    Nat.card {w : AltHeart 6 // ∀ σ ∈ S, heartAct 6 σ w = w} =
      Nat.card (fixU0 (S.map (MulAut.conj g).toMonoidHom)) := by
  let e : {w : AltHeart 6 // ∀ σ ∈ S, heartAct 6 σ w = w} ≃
      fixU0 (S.map (MulAut.conj g).toMonoidHom) :=
    { toFun := fun w => ⟨eps (heartAct 6 g w.1), by
        rintro x ⟨σ, hσ, rfl⟩
        show act (g * σ * g⁻¹) (eps (heartAct 6 g w.1)) = eps (heartAct 6 g w.1)
        rw [← eps_heartAct, ← heartAct_mul, inv_mul_cancel_right, heartAct_mul, w.2 σ hσ]⟩
      invFun := fun v => ⟨heartAct 6 g⁻¹ (epsInv v.1), by
        intro σ hσ
        have h1 := v.2 (g * σ * g⁻¹) ⟨σ, hσ, rfl⟩
        apply eps_injective
        have e1 : σ * g⁻¹ = g⁻¹ * (g * σ * g⁻¹) := by group
        rw [eps_heartAct, eps_heartAct, ← act_mul, e1, act_mul, eps_epsInv, h1]⟩
      left_inv := fun w => Subtype.ext (by
        show heartAct 6 g⁻¹ (epsInv (eps (heartAct 6 g w.1))) = w.1
        rw [epsInv_eps, ← heartAct_mul, inv_mul_cancel, heartAct_one])
      right_inv := fun v => Subtype.ext (by
        show eps (heartAct 6 g (heartAct 6 g⁻¹ (epsInv v.1))) = v.1
        rw [← heartAct_mul, mul_inv_cancel, heartAct_one, eps_epsInv]) }
  exact Nat.card_congr e

theorem card_fix_conj_one (σ g : Equiv.Perm (Fin 6)) :
    Nat.card {w : AltHeart 6 // heartAct 6 σ w = w} =
      Nat.card {v : Vec4 | act (g * σ * g⁻¹) v = v} := by
  let e : {w : AltHeart 6 // heartAct 6 σ w = w} ≃ {v : Vec4 | act (g * σ * g⁻¹) v = v} :=
    { toFun := fun w => ⟨eps (heartAct 6 g w.1), by
        show act (g * σ * g⁻¹) (eps (heartAct 6 g w.1)) = eps (heartAct 6 g w.1)
        rw [← eps_heartAct, ← heartAct_mul, inv_mul_cancel_right, heartAct_mul, w.2]⟩
      invFun := fun v => ⟨heartAct 6 g⁻¹ (epsInv v.1), by
        have h1 : act (g * σ * g⁻¹) v.1 = v.1 := v.2
        apply eps_injective
        have e1 : σ * g⁻¹ = g⁻¹ * (g * σ * g⁻¹) := by group
        rw [eps_heartAct, eps_heartAct, ← act_mul, e1, act_mul, eps_epsInv, h1]⟩
      left_inv := fun w => Subtype.ext (by
        show heartAct 6 g⁻¹ (epsInv (eps (heartAct 6 g w.1))) = w.1
        rw [epsInv_eps, ← heartAct_mul, inv_mul_cancel, heartAct_one])
      right_inv := fun v => Subtype.ext (by
        show eps (heartAct 6 g (heartAct 6 g⁻¹ (epsInv v.1))) = v.1
        rw [← heartAct_mul, mul_inv_cancel, heartAct_one, eps_epsInv]) }
  exact Nat.card_congr e

theorem weight_eq {Y : Subgroup G} (hYT : Y ≤ T) (g : Equiv.Perm (Fin 6)) :
    Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) =
      weight ((D.img Y).map (MulAut.conj g).toMonoidHom) := by
  rw [weight, D.relIndex_eq hYT, D.card_fix Y hYT, card_fix_conj (D.img Y) g,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

include D in
theorem card_Q : Nat.card Q = 16 := by
  rw [Nat.card_congr D.θ]
  exact card_altHeart

theorem eq_of_img_eq {Y Y' : Subgroup G} (hQY : Q ≤ Y) (hYT : Y ≤ T) (hQY' : Q ≤ Y')
    (hY'T : Y' ≤ T) (h : D.img Y = D.img Y') : Y = Y' := by
  have key : ∀ {Y Y' : Subgroup G}, Q ≤ Y' → Y ≤ T → Y' ≤ T → D.img Y = D.img Y' → Y ≤ Y' := by
    intro Y Y' hQY' hYT hY'T h y hy
    obtain ⟨t', ht'Y', he⟩ := D.mem_img.mp (h ▸ D.mem_img.mpr ⟨⟨y, hYT hy⟩, hy, rfl⟩)
    have h1 : D.ρ (t'⁻¹ * ⟨y, hYT hy⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 : (t' : G)⁻¹ * y ∈ Q := (D.hker _).mp h1
    have e : y = t' * ((t' : G)⁻¹ * y) := by group
    rw [e]
    exact Y'.mul_mem ht'Y' (hQY' h2)
  exact le_antisymm (key hQY' hYT hY'T h) (key hQY hY'T hYT h.symm)

theorem offenders [Finite G] (hQe : IsElemAbelian 2 Q) {T₀ : Subgroup G} (hQT₀ : Q ≤ T₀)
    (hT₀ : T₀ ≤ T)
    {g : Equiv.Perm (Fin 6)}
    (himg : ∀ t : ↥T, (t : G) ∈ T₀ → g * D.ρ t * g⁻¹ ∈ aBar2) :
    (∀ B : Subgroup G, B ≤ T₀ → IsElemAbelian 2 B → Nat.card B ≤ Nat.card Q) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian T₀ B → ¬ B ≤ Q →
      ∃ b ∈ B, Q ⊓ Subgroup.centralizer (B : Set G) =
        Q ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ B B' : Subgroup G, IsMaxElemAbelian T₀ B → IsMaxElemAbelian T₀ B' → ¬ B ≤ Q →
      ¬ B' ≤ Q → Nat.card ↥(B ⊔ Q) = Nat.card ↥(B' ⊔ Q) → B ⊔ Q = B' ⊔ Q) := by
  have hQN : T₀ ≤ Subgroup.normalizer (Q : Set G) := hT₀.trans D.hQN
  obtain ⟨w0, w1, w2, w3, wA⟩ := weight_values
  let X : Subgroup G → Subgroup (Equiv.Perm (Fin 6)) := fun Y =>
    (D.img Y).map (MulAut.conj g).toMonoidHom
  have hXle : ∀ Y : Subgroup G, Y ≤ T₀ → X Y ≤ aBar2 := by
    rintro Y hY _ ⟨σ, hσ, rfl⟩
    obtain ⟨t, htY, rfl⟩ := D.mem_img.mp hσ
    exact himg t (hY htY)
  have hW : ∀ Y : Subgroup G, Y ≤ T₀ →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) = weight (X Y) :=
    fun Y hY => D.weight_eq (hY.trans hT₀) g
  have hcardQ := D.card_Q
  have hle16 : ∀ X : Subgroup (Equiv.Perm (Fin 6)), X ≤ aBar2 → weight X ≤ 16 := by
    intro X hX
    rcases subgroup_cases hX with rfl | rfl | rfl | rfl | rfl <;> omega
  have hM1 : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card Q := by
    intro Y _ hY
    rw [hW Y hY, hcardQ]
    exact hle16 _ (hXle Y hY)
  have hXbot : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ → X Y = ⊥ → Y = Q := by
    intro Y hQY hY h
    refine le_antisymm (fun y hy => ?_) hQY
    have h1 : g * D.ρ ⟨y, hT₀ (hY hy)⟩ * g⁻¹ ∈ X Y :=
      ⟨_, D.mem_img.mpr ⟨⟨y, hT₀ (hY hy)⟩, hy, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : D.ρ ⟨y, hT₀ (hY hy)⟩ = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    exact (D.hker _).mp h2
  have hcases : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ → Y ≠ Q →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) = Nat.card Q →
        X Y = Subgroup.zpowers x₂ ∨ X Y = aBar2 := by
    intro Y hQY hY hne heq
    rw [hW Y hY, hcardQ] at heq
    rcases subgroup_cases (hXle Y hY) with h | h | h | h | h
    · exact absurd (hXbot Y hQY hY h) hne
    · rw [h] at heq; omega
    · exact Or.inl h
    · rw [h] at heq; omega
    · exact Or.inr h
  refine ⟨fun B hB hBe => Offend.card_le_of_weight hQe hQN hQT₀ hM1 hB hBe,
    fun B hB hBQ => Offend.exists_centralizer_eq hQe hQN hQT₀ hM1 ?_ hB hBQ,
    fun B B' hB hB' hBQ hB'Q hc => Offend.sup_eq_of_card_eq hQe hQN hQT₀ hM1 ?_ hB hB' hBQ hB'Q hc⟩
  ·
    intro Y hQY hY hne heq
    have hfixY : Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) =
        Nat.card (fixU0 (X Y)) := by
      rw [D.card_fix Y (hY.trans hT₀), card_fix_conj (D.img Y) g]
    obtain ⟨x, hxX, hxfix⟩ : ∃ x ∈ X Y, fixU0 (X Y) = {v | act x v = v} := by
      rcases hcases Y hQY hY hne heq with h | h
      · exact ⟨x₂, h ▸ Subgroup.mem_zpowers x₂, by rw [h, fixU0_zpowers]⟩
      · refine ⟨x₁, h ▸ (aBar2_eq x₁).mpr ((mem_elemsA x₁).mpr (Or.inr (Or.inl rfl))), ?_⟩
        rw [h, fixU0_aBar2]
    obtain ⟨σ, hσ, rfl⟩ := hxX
    obtain ⟨t, htY, rfl⟩ := D.mem_img.mp hσ
    refine ⟨t, htY, ?_⟩
    have hle : Q ⊓ Subgroup.centralizer (Y : Set G) ≤
        Q ⊓ Subgroup.centralizer ({(t : G)} : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htY))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [D.card_fix_one t, hfixY, hxfix, card_fix_conj_one (D.ρ t) g]
    exact le_rfl
  ·
    intro Y Y' hQY hY hQY' hY' hne hne' heq heq' hcard
    have hX : X Y = X Y' := by
      have hc : Nat.card (X Y) = Nat.card (X Y') := by
        have h1 := D.relIndex_eq (hY.trans hT₀)
        have h2 := D.relIndex_eq (hY'.trans hT₀)
        have h3 := Subgroup.relIndex_mul_card (H := Q) (K := Y)
        have h4 := Subgroup.relIndex_mul_card (H := Q) (K := Y')
        rw [inf_of_le_left hQY] at h3
        rw [inf_of_le_left hQY'] at h4
        have hQpos : 0 < Nat.card Q := Nat.card_pos
        have h5 : Q.relIndex Y = Q.relIndex Y' := by
          have : Q.relIndex Y * Nat.card Q = Q.relIndex Y' * Nat.card Q := by
            rw [h3, h4, hcard]
          exact Nat.eq_of_mul_eq_mul_right hQpos this
        simp only [X]
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
          Subgroup.card_map_of_injective (MulAut.conj g).injective, ← h1, ← h2, h5]
      have hz2 : Nat.card (Subgroup.zpowers x₂) = 2 := by
        obtain ⟨-, h2, -, -, n2, -⟩ := x_facts
        exact card_zpowers_of h2 n2
      rcases hcases Y hQY hY hne heq with h | h <;> rcases hcases Y' hQY' hY' hne' heq' with h' | h'
      · rw [h, h']
      · rw [h, h', hz2, card_aBar2] at hc; omega
      · rw [h, h', hz2, card_aBar2] at hc; omega
      · rw [h, h']
    have himg : D.img Y = D.img Y' :=
      Subgroup.map_injective (MulAut.conj g).injective hX
    exact D.eq_of_img_eq hQY (hY.trans hT₀) hQY' (hY'.trans hT₀) himg

end Model

end CFSG.Quasithin.H13.CloseModel
