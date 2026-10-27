module

public import CFSG.Quasithin.Background.Asc81cPfPair
public import CFSG.Quasithin.Background.Asc81cPfTri

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] [Finite W] {G : Subgroup (MulAut W)}

section Galois

variable {X : Subgroup (MulAut W)}

theorem card_dvd_card_inf_centralizer_mul_rk (hW : ∀ w : W, w ^ 2 = 1) (h : Hyp101 G X)
    {Y : Subgroup (MulAut W)} (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) :
    Nat.card Y ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set (MulAut W))) *
      rk (commSub (⊤ : Subgroup W) X) := by
  let _ : Field (singerRing h) := singerField h
  have : Finite (singerRing h) := finite_singerRing h
  have h12 : (2 : singerRing h) = 0 := by
    rw [← one_add_one_eq_two]
    exact one_add_one_singerRing hW h
  have : CharP (singerRing h) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h12
  let _ : Algebra (ZMod 2) (singerRing h) := ZMod.algebra (singerRing h) 2
  have hcomm : ∀ (y : MulAut W) (hy : y ∈ Subgroup.normalizer (X : Set (MulAut W)))
      (r : ZMod 2), conjRingEquiv h hy (algebraMap (ZMod 2) (singerRing h) r) =
        algebraMap (ZMod 2) (singerRing h) r := by
    intro y hy r
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.val, (ZMod.natCast_zmod_val r).symm⟩
    rw [map_natCast]
    exact map_natCast (conjRingEquiv h hy) n
  let σ : Y → Gal(singerRing h/ZMod 2) := fun y => AlgEquiv.ofRingEquiv (hcomm y (hYN y.2))
  let φ : Y →* Gal(singerRing h/ZMod 2) :=
    { toFun := σ
      map_one' := AlgEquiv.ext fun f => Subtype.ext (by
        show resN (hYN (1 : Y).2) * (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) *
          resN (Subgroup.inv_mem _ (hYN (1 : Y).2)) = f
        rw [resN_eq_one _ rfl, resN_eq_one _ inv_one, one_mul, mul_one])
      map_mul' := fun y y' => AlgEquiv.ext fun f => Subtype.ext (by
        show resN (hYN (y * y').2) * (f : AddMonoid.End (Additive (commSub (⊤ : Subgroup W) X))) *
          resN (Subgroup.inv_mem _ (hYN (y * y').2)) =
            resN (hYN y.2) * (resN (hYN y'.2) * f * resN (Subgroup.inv_mem _ (hYN y'.2))) *
              resN (Subgroup.inv_mem _ (hYN y.2))
        rw [resN_mul' (hYN y.2) (hYN y'.2), resN_mul_inv' (hYN y.2) (hYN y'.2)]
        simp only [mul_assoc]) }
  have hker : ∀ y : Y, φ y = 1 → (y : MulAut W) ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := DFunLike.congr_fun hy ⟨rho X ⟨x, hx⟩, rho_mem h _⟩
    have h2 : conjRingEquiv h (hYN y.2) ⟨rho X ⟨x, hx⟩, rho_mem h _⟩ =
        ⟨rho X ⟨x, hx⟩, rho_mem h _⟩ := h1
    rw [conjRingEquiv_rho] at h2
    have h3 : (y : MulAut W) * x * (y : MulAut W)⁻¹ = x :=
      congrArg Subtype.val (rho_injective h (congrArg Subtype.val h2))
    have h4 : (y : MulAut W) * x * (y : MulAut W)⁻¹ * y = x * y := by rw [h3]
    rw [inv_mul_cancel_right] at h4
    exact h4.symm
  have hker' : ∀ y : Y, (y : MulAut W) ∈ Subgroup.centralizer (X : Set (MulAut W)) → φ y = 1 := by
    intro y hy
    refine AlgEquiv.ext fun f => ?_
    show conjRingEquiv h (hYN y.2) f = f
    rcases (mem_singerRing h).1 f.2 with hf | ⟨x, hx⟩
    · have : f = 0 := Subtype.ext hf
      rw [this, map_zero]
    · have hf : f = ⟨rho X x, rho_mem h x⟩ := Subtype.ext hx
      rw [hf, conjRingEquiv_rho]
      congr 2
      apply Subtype.ext
      show (y : MulAut W) * x * (y : MulAut W)⁻¹ = x
      rw [← (Subgroup.mem_centralizer_iff.1 hy) x x.2, mul_assoc, mul_inv_cancel, mul_one]
  have hkereq : φ.ker = (Y ⊓ Subgroup.centralizer (X : Set (MulAut W))).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun hy => ⟨y.2, hker y hy⟩, fun hy => hker' y hy.2⟩
  have hcardker : Nat.card φ.ker = Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set (MulAut W))) := by
    rw [hkereq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hY := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hcardker] at hY
  have hrange : Nat.card φ.range ∣ Nat.card Gal(singerRing h/ZMod 2) :=
    Subgroup.card_subgroup_dvd_card _
  rw [IsGalois.card_aut_eq_finrank] at hrange
  have h2 : Nat.card (singerRing h) = 2 ^ Module.finrank (ZMod 2) (singerRing h) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 : Nat.card (singerRing h) = 2 ^ rk (commSub (⊤ : Subgroup W) X) := by
    rw [card_singerRing h, card_eq_two_pow hW]
  rw [Nat.pow_right_injective (le_refl 2) (h2.symm.trans h3)] at hrange
  rw [hY, mul_comm]
  exact mul_dvd_mul_left _ hrange

end Galois

section Normalize

variable {X Y : Subgroup (MulAut W)}

theorem commSub_le_of_normalizes (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) (hnc : ¬ Commutes X Y) :
    commSub (⊤ : Subgroup W) Y ≤ commSub ⊤ X := by
  obtain ⟨u, hu, y, hy, hyu⟩ : ∃ u ∈ commSub (⊤ : Subgroup W) X, ∃ y ∈ Y, y u ≠ u := by
    by_contra hall
    push Not at hall
    exact hnc (comm_of_fixes_commSub hW hX hYN (fun y hy u hu => hall u hu y hy))
  have hS : ∀ y ∈ Y, ∀ s ∈ commSub (⊤ : Subgroup W) X, y s ∈ commSub (⊤ : Subgroup W) X :=
    fun y hy => normalizer_stable (hYN hy)
  have hwX : y u * u⁻¹ ∈ commSub (⊤ : Subgroup W) X :=
    (commSub ⊤ X).mul_mem (hS y hy u hu) ((commSub ⊤ X).inv_mem hu)
  have hwY : y u * u⁻¹ ∈ commSub (⊤ : Subgroup W) Y :=
    Subgroup.subset_closure ⟨y, hy, u, Subgroup.mem_top u, rfl⟩
  have hw1 : y u * u⁻¹ ≠ 1 := fun h => hyu (mul_inv_eq_one.1 h)
  exact commSub_le_of_invariant' hY hS hwX hwY hw1

theorem fixes_fixV_of_normalizes (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) (hnc : ¬ Commutes X Y) :
    ∀ y ∈ Y, ∀ c ∈ fixV X, y c = c := by
  intro y hy c hc
  have h1 := fixV_stable_of_normalizer (hYN hy) hc
  have h2 : y c * c⁻¹ ∈ fixV X ⊓ commSub ⊤ X :=
    ⟨(fixV X).mul_mem h1 ((fixV X).inv_mem hc), commSub_le_of_normalizes hW hX hY hYN hnc
      (Subgroup.subset_closure ⟨y, hy, c, Subgroup.mem_top c, rfl⟩)⟩
  rw [fixV_inf_commSub_eq_bot' hW hX.2.2.2.1, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.1 h2

end Normalize

section Triples

variable {X Y Y' : Subgroup (MulAut W)}

theorem card_eq_three_or_seven (hW : ∀ w : W, w ^ 2 = 1) {F Z : Subgroup (MulAut W)}
    (hZ : Hyp101 G Z) (hZF : Z ≤ F) (hF : Nat.card F = 21) : Nat.card Z = 3 ∨ Nat.card Z = 7 := by
  have h1 : Nat.card Z ∣ 21 := hF ▸ Subgroup.card_dvd_of_le hZF
  rcases card_eq_three_or_seven_le hW hZ with h3 | h7
  · exact Or.inl h3
  · right
    have h2 : Nat.card Z ≤ 21 := Nat.le_of_dvd (by norm_num) h1
    interval_cases h : Nat.card Z <;> first | rfl | (norm_num at h1)
    exfalso
    have h4 := card_commSub hZ
    rw [card_eq_two_pow hW, h] at h4
    have h5 : rk (commSub (⊤ : Subgroup W) Z) < 5 := by
      by_contra h6
      push Not at h6
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h6
      omega
    interval_cases rk (commSub (⊤ : Subgroup W) Z) <;> omega

theorem le_normalizer_of_card_seven {F P : Subgroup (MulAut W)} (hF : Nat.card F = 21)
    (hPF : P ≤ F) (hP : Nat.card P = 7) : F ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine eq_of_card_seven hF ?_ hPF ?_ hP
  · rintro _ ⟨p, hp, rfl⟩
    exact F.mul_mem (F.mul_mem hg (hPF hp)) (F.inv_mem hg)
  · rw [← hP]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective P _
      (MulEquiv.injective (MulAut.conj g))).toEquiv).symm

theorem triple_seven (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp101 G X) (hY : Hyp101 G Y)
    (hY' : Hyp101 G Y') (hX7 : Nat.card X = 7) (hF : Nat.card ↥(X ⊔ Y) = 21)
    (hF' : Nat.card ↥(X ⊔ Y') = 21) (hXY : ¬ Commutes X Y) (hXY' : ¬ Commutes X Y') :
    X ⊔ Y = X ⊔ Y' := by
  have hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    le_sup_right.trans (le_normalizer_of_card_seven hF le_sup_left hX7)
  have hY'N : Y' ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    le_sup_right.trans (le_normalizer_of_card_seven hF' le_sup_left hX7)
  set K := X ⊔ Y ⊔ Y' with hK
  have hKN : K ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    sup_le (sup_le (Subgroup.le_normalizer) hYN) hY'N
  let S : Subgroup (MulAut W) :=
    { carrier := {g | ∀ c ∈ fixV X, g c = c}
      one_mem' := fun c _ => rfl
      mul_mem' := fun ha hb c hc => by rw [MulAut.mul_apply, hb c hc, ha c hc]
      inv_mem' := fun {g} ha c hc => by
        calc g⁻¹ c = g⁻¹ (g c) := by rw [ha c hc]
          _ = c := MulAut.inv_apply_self _ _ _ }
  have hKS : K ≤ S := sup_le (sup_le (fun x hx c hc => hc x hx)
    (fixes_fixV_of_normalizes hW hX hY hYN hXY))
    (fixes_fixV_of_normalizes hW hX hY' hY'N hXY')
  have hC : K ⊓ Subgroup.centralizer (X : Set (MulAut W)) ≤ X := by
    rintro g ⟨hgK, hgC⟩
    have hcomm : ∀ x ∈ X, g * x = x * g := fun x hx =>
      ((Subgroup.mem_centralizer_iff.1 hgC) x hx).symm
    obtain ⟨x₀, hx₀, hx₀v⟩ := exists_eq_on_commSub hX hcomm
    have hg : g = x₀ := by
      ext v
      have hv : v ∈ fixV X ⊔ commSub ⊤ X := by
        rw [fixV_sup_commSub_eq_top' hW hX.2.2.2.1]
        exact Subgroup.mem_top v
      obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
      rw [map_mul, map_mul, hKS hgK c hc, hc x₀ hx₀, hx₀v w hw]
    rw [hg]
    exact hx₀
  have h3 : rk (commSub (⊤ : Subgroup W) X) = 3 := by
    rw [rk, card_commSub hX, hX7, show (7 + 1 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hdvd := card_dvd_card_inf_centralizer_mul_rk hW hX hKN
  rw [h3] at hdvd
  have h7 : Nat.card ↥(K ⊓ Subgroup.centralizer (X : Set (MulAut W))) ∣ 7 :=
    hX7 ▸ Subgroup.card_dvd_of_le hC
  have hK21 : Nat.card K ≤ 21 :=
    Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.mul_dvd_mul_right h7 3))
  have e1 : X ⊔ Y = K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hF]; exact hK21)
  have e2 : X ⊔ Y' = K := Subgroup.eq_of_le_of_card_ge
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right) (by rw [hF']; exact hK21)
  rw [e1, e2]

theorem triple_three_seven_seven (hW : ∀ w : W, w ^ 2 = 1)
    (hX : Hyp102 G X) (hY : Hyp102 G Y) (hY' : Hyp102 G Y') (hY7 : Nat.card Y = 7)
    (hY'7 : Nat.card Y' = 7) (hF : Nat.card ↥(X ⊔ Y) = 21) (hF' : Nat.card ↥(X ⊔ Y') = 21)
    (hXY : ¬ Commutes X Y) (hXY' : ¬ Commutes X Y') : X ⊔ Y = X ⊔ Y' := by
  by_cases hYY' : Y = Y'
  · rw [hYY']
  exfalso
  have hc : Commutes Y Y' := by
    rcases pair_theorem hW hY hY' with h | h
    · exact h
    · exact absurd (eq_of_card_seven h le_sup_left le_sup_right hY7 hY'7) hYY'
  have hbot := commSub_inf_commSub_eq_bot hW hY.1 hY'.1 hYY' hc
  have hXN := le_sup_left.trans (le_normalizer_of_card_seven hF le_sup_right hY7)
  have hXN' := le_sup_left.trans (le_normalizer_of_card_seven hF' le_sup_right hY'7)
  have h1 := commSub_le_of_normalizes hW hY.1 hX.1 hXN (fun h => hXY h.symm)
  have h2 := commSub_le_of_normalizes hW hY'.1 hX.1 hXN' (fun h => hXY' h.symm)
  have h3 : commSub (⊤ : Subgroup W) X ≤ ⊥ := by
    rw [← hbot]
    exact le_inf h1 h2
  exact commSub_ne_bot hX.1 (le_bot_iff.1 h3)

theorem triple_three_seven_three (hW : ∀ w : W, w ^ 2 = 1)
    (hX : Hyp102 G X) (hY : Hyp102 G Y) (hY' : Hyp102 G Y') (hX3 : Nat.card X = 3)
    (hY7 : Nat.card Y = 7) (hY'3 : Nat.card Y' = 3) (hF : Nat.card ↥(X ⊔ Y) = 21)
    (hF' : Nat.card ↥(X ⊔ Y') = 21) (hXY : ¬ Commutes X Y) (hXY' : ¬ Commutes X Y') :
    X ⊔ Y = X ⊔ Y' := by
  have hXN := le_sup_left.trans (le_normalizer_of_card_seven hF le_sup_right hY7)
  have h1 := commSub_le_of_normalizes hW hY.1 hX.1 hXN (fun h => hXY h.symm)
  by_cases hc : Commutes Y Y'
  ·
    exfalso
    have hYY' : Y ≠ Y' := fun h => by rw [h, hY'3] at hY7; norm_num at hY7
    have h2 := commSub_le_fixV_of_commute hW hY.1 hY'.1 hYY' hc
    have hbot : commSub (⊤ : Subgroup W) X ⊓ commSub ⊤ Y' = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h3 : v ∈ fixV Y' ⊓ commSub ⊤ Y' := ⟨h2 (h1 hv.1), hv.2⟩
      rwa [fixV_inf_commSub_eq_bot' hW hY'.1.2.2.2.1] at h3
    have h4 := card_sup_of_inf_eq_bot hbot
    rw [card_commSub hX.1, card_commSub hY'.1, hX3, hY'3, ← commSub_sup] at h4
    have hna : ∃ a ∈ X ⊔ Y', ∃ b ∈ X ⊔ Y', a * b ≠ b * a := by
      by_contra hall
      push Not at hall
      exact hXY' fun a ha b hb => hall a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)
    have h5 := card_commSub_frob21 hW hF' hna le_sup_left hX3 (by rw [card_commSub hX.1, hX3])
    omega
  ·
    have hF'' : Nat.card ↥(Y ⊔ Y') = 21 := (pair_theorem hW hY hY').resolve_left hc
    have e := triple_seven hW hY.1 hX.1 hY'.1 hY7 (by rw [sup_comm]; exact hF) hF''
      (fun h => hXY h.symm) hc
    have hY'le : Y' ≤ X ⊔ Y := by
      rw [sup_comm X Y, e]
      exact le_sup_right
    have hle : X ⊔ Y' ≤ X ⊔ Y := sup_le le_sup_left hY'le
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF, hF'])).symm

theorem triple_theorem
    (hW : ∀ w : W, w ^ 2 = 1) (hX : Hyp102 G X) (hY : Hyp102 G Y) (hY' : Hyp102 G Y')
    (hXY : ¬ Commutes X Y) (hXY' : ¬ Commutes X Y') : X ⊔ Y = X ⊔ Y' := by
  have hF : Nat.card ↥(X ⊔ Y) = 21 := (pair_theorem hW hX hY).resolve_left hXY
  have hF' : Nat.card ↥(X ⊔ Y') = 21 := (pair_theorem hW hX hY').resolve_left hXY'
  have hXo := card_eq_three_or_seven hW hX.1 le_sup_left hF
  have hYo := card_eq_three_or_seven hW hY.1 le_sup_right hF
  have hY'o := card_eq_three_or_seven hW hY'.1 le_sup_right hF'
  have h77 : ∀ {Z Z' : Subgroup (MulAut W)}, Hyp101 G Z → Hyp101 G Z' → Nat.card Z = 7 →
      Nat.card Z' = 7 → Nat.card ↥(Z ⊔ Z') = 21 → Z = Z' := fun hZ hZ' h7 h7' h21 =>
    eq_of_card_seven h21 le_sup_left le_sup_right h7 h7'
  rcases hXo with hX3 | hX7
  · rcases hYo with hY3 | hY7
    · rcases hY'o with hY'3 | hY'7
      ·
        have := triple333 hW hY hX hY' hY3 hX3 hY'3 (fun h => hXY h.symm) hXY'
        rw [sup_comm, this]
      ·
        exact (triple_three_seven_three hW hX hY' hY hX3 hY'7 hY3 hF' hF hXY' hXY).symm
    · rcases hY'o with hY'3 | hY'7
      · exact triple_three_seven_three hW hX hY hY' hX3 hY7 hY'3 hF hF' hXY hXY'
      · exact triple_three_seven_seven hW hX hY hY' hY7 hY'7 hF hF' hXY hXY'
  ·
    exact triple_seven hW hX.1 hY.1 hY'.1 hX7 hF hF' hXY hXY'

end Triples

end Pf

end Asc81c

end CFSG.Quasithin
