module

public import CFSG.Quasithin.Background.B51SumOffenders
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace A6NatPair

variable {V : Type} [CommGroup V]

theorem card_modEq_card_fix [Finite V] {c : MulAut V} (hc : c ^ 3 = 1) {W : Subgroup V}
    (hW : ∀ w ∈ W, c w ∈ W) :
    Nat.card W ≡ Nat.card ↥(W ⊓ fixV (Subgroup.zpowers c)) [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite ↥W
  let g : Function.End ↥W := fun w => ⟨c w, hW w w.2⟩
  have hg3 : g ^ 3 = 1 := by
    funext w
    apply Subtype.ext
    have h := congrArg (fun φ : MulAut V => φ (w : V)) hc
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
    exact h
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := g) (by simpa using hg3)
  have e : Function.fixedPoints g ≃ ↥(W ⊓ fixV (Subgroup.zpowers c)) :=
    { toFun := fun w => ⟨(w.1 : V), w.1.2, H.mem_fixV_zpowers_iff.2 (congrArg Subtype.val w.2)⟩
      invFun := fun v => ⟨⟨v, v.2.1⟩, Subtype.ext (H.mem_fixV_zpowers_iff.1 v.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Nat.card_congr e] at hmod
  exact hmod

theorem apply_mem_sup {l : MulAut V} {A B : Subgroup V} (hA : ∀ x ∈ A, l x ∈ A)
    (hB : ∀ x ∈ B, l x ∈ B) {x : V} (hx : x ∈ A ⊔ B) : l x ∈ A ⊔ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA a ha) (hB b hb)

theorem two_lt_card_commSub [Finite V] {D : Subgroup (MulAut V)} {A B : Subgroup V}
    (hAB : A ⊓ B = ⊥) (hA : ∀ d ∈ D, ∀ x ∈ A, d x ∈ A) (hB : ∀ d ∈ D, ∀ x ∈ B, d x ∈ B)
    (hfA : ∀ d ∈ D, (∀ x ∈ A, d x = x) → d = 1) (hfB : ∀ d ∈ D, (∀ x ∈ B, d x = x) → d = 1)
    (hD : D ≠ ⊥) (hoff : Nat.card ↥(A ⊔ B) ≤ Nat.card D * Nat.card ↥((A ⊔ B) ⊓ fixV D)) :
    2 < Nat.card (commSub A D) := by
  by_contra hle
  push Not at hle
  have hr := B51Sum.card_le_relIndex hA hfA hle
  have hM := card_sup_mul_card_inf A B
  rw [hAB, Subgroup.card_bot, mul_one] at hM
  have hF := card_sup_mul_card_inf (fixV D ⊓ A) (fixV D ⊓ B)
  have hFle : Nat.card ↥((A ⊔ B) ⊓ fixV D) ≤
      Nat.card ↥(fixV D ⊓ A) * Nat.card ↥(fixV D ⊓ B) := by
    have h1 : Nat.card ↥((A ⊔ B) ⊓ fixV D) ≤ Nat.card ↥(fixV D ⊓ A ⊔ fixV D ⊓ B) :=
      Subgroup.card_le_of_le (by rw [inf_comm]; exact B51Sum.fixV_inf_sup_le hAB hA hB)
    have h2 : 0 < Nat.card ↥(fixV D ⊓ A ⊓ (fixV D ⊓ B)) := Nat.card_pos
    calc _ ≤ Nat.card ↥(fixV D ⊓ A ⊔ fixV D ⊓ B) := h1
      _ ≤ Nat.card ↥(fixV D ⊓ A ⊔ fixV D ⊓ B) * Nat.card ↥(fixV D ⊓ A ⊓ (fixV D ⊓ B)) :=
          Nat.le_mul_of_pos_right _ h2
      _ = _ := hF
  have eA := Subgroup.relIndex_mul_card (fixV D ⊓ A) A
  rw [inf_assoc, inf_idem] at eA
  have hApos : 0 < Nat.card A := Nat.card_pos
  have key : Nat.card A * Nat.card B ≤ Nat.card A * Nat.card ↥(fixV D ⊓ B) := by
    calc Nat.card A * Nat.card B = Nat.card ↥(A ⊔ B) := hM.symm
      _ ≤ Nat.card D * Nat.card ↥((A ⊔ B) ⊓ fixV D) := hoff
      _ ≤ (fixV D ⊓ A).relIndex A * (Nat.card ↥(fixV D ⊓ A) * Nat.card ↥(fixV D ⊓ B)) :=
          Nat.mul_le_mul hr hFle
      _ = Nat.card A * Nat.card ↥(fixV D ⊓ B) := by rw [← mul_assoc, eA]
  have hBle : Nat.card B ≤ Nat.card ↥(fixV D ⊓ B) := Nat.le_of_mul_le_mul_left key hApos
  have hBfix : fixV D ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right hBle
  apply hD
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  refine hfB d hd fun x hx => ?_
  have hx' : x ∈ fixV D ⊓ B := by rw [hBfix]; exact hx
  exact hx'.1 d hd

theorem fix_aux [Finite V] {L X D : Subgroup (MulAut V)} {A B N : Subgroup V}
    (hAB : A ⊓ B = ⊥) (hA : ∀ l ∈ L, ∀ x ∈ A, l x ∈ A) (hB : ∀ l ∈ L, ∀ x ∈ B, l x ∈ B)
    (hiA : ∀ J : Subgroup V, (∀ l ∈ L, ∀ x ∈ J, l x ∈ J) → J ≤ A → J = ⊥ ∨ J = A)
    (hiB : ∀ J : Subgroup V, (∀ l ∈ L, ∀ x ∈ J, l x ∈ J) → J ≤ B → J = ⊥ ∨ J = B)
    (hfA : ∀ l ∈ L, (∀ x ∈ A, l x = x) → l = 1) (hfB : ∀ l ∈ L, (∀ x ∈ B, l x = x) → l = 1)
    (hcA : Nat.card A = 8) (hcB : Nat.card B = 8) (hD : IsFFStarOffender X D) (hDL : D ≤ L)
    (hNL : ∀ l ∈ L, ∀ x ∈ N, l x ∈ N) (hNU : N ≤ A ⊔ B) (hN : N ≠ ⊥) (hNB : N ⊓ B = ⊥)
    {c : MulAut V} (hcL : ∀ l ∈ L, c * l * c⁻¹ ∈ L) (hcN : ∀ x ∈ N, c x ∈ N)
    (hcU : ∀ x ∈ A ⊔ B, c x ∈ A ⊔ B) (hc3 : c ^ 3 = 1)
    (hcD : ∀ x ∈ commSub N D, c x = x) :
    ∀ x ∈ A ⊔ B, c x = x := by
  have hAN : A ≤ N ⊔ B := by
    have hinv : ∀ l ∈ L, ∀ x ∈ (N ⊔ B) ⊓ A, l x ∈ (N ⊔ B) ⊓ A := fun l hl x hx =>
      ⟨apply_mem_sup (hNL l hl) (hB l hl) hx.1, hA l hl x hx.2⟩
    rcases hiA _ hinv inf_le_right with h | h
    · exfalso
      obtain ⟨⟨n, hnN⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hNU hnN)
      have haP : a ∈ (N ⊔ B) ⊓ A := by
        refine ⟨?_, ha⟩
        have e : a = n * b⁻¹ := by rw [← hab, mul_inv_cancel_right]
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN)
          (Subgroup.mem_sup_right (B.inv_mem hb))
      rw [h, Subgroup.mem_bot] at haP
      rw [haP, one_mul] at hab
      have hnB : n ∈ N ⊓ B := ⟨hnN, hab ▸ hb⟩
      rw [hNB, Subgroup.mem_bot] at hnB
      exact hn1 (Subtype.ext hnB)
    · rw [← h]
      exact inf_le_left
  have hNBU : N ⊔ B = A ⊔ B := le_antisymm (sup_le hNU le_sup_right) (sup_le hAN le_sup_right)
  have hcU64 : Nat.card ↥(A ⊔ B) = 64 := by
    have h := card_sup_mul_card_inf A B
    rw [hAB, Subgroup.card_bot, mul_one, hcA, hcB] at h
    exact h
  have hcN8 : Nat.card N = 8 := by
    have h := card_sup_mul_card_inf N B
    rw [hNB, Subgroup.card_bot, mul_one, hNBU, hcU64, hcB] at h
    omega
  have hfN : ∀ l ∈ L, (∀ x ∈ N, l x = x) → l = 1 := by
    intro l hl hlN
    refine hfA l hl fun a ha => ?_
    obtain ⟨n, hn, b, hb, rfl⟩ := Subgroup.mem_sup.1 (hAN ha)
    have h1 : l (n * b) * (n * b)⁻¹ ∈ A ⊓ B := by
      refine ⟨A.mul_mem (hA l hl _ ha) (A.inv_mem ha), ?_⟩
      have e : l (n * b) * (n * b)⁻¹ = l b * b⁻¹ := by
        rw [map_mul, hlN n hn, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rw [e]
      exact B.mul_mem (hB l hl b hb) (B.inv_mem hb)
    rw [hAB, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hDN : ∀ d ∈ D, ∀ x ∈ N, d x ∈ N := fun d hd => hNL d (hDL hd)
  have hDB : ∀ d ∈ D, ∀ x ∈ B, d x ∈ B := fun d hd => hB d (hDL hd)
  have hoff : Nat.card ↥(N ⊔ B) ≤ Nat.card D * Nat.card ↥((N ⊔ B) ⊓ fixV D) := by
    have h := (B1.card_inf_fixV_aux hD (bot_le : (⊥ : Subgroup (MulAut V)) ≤ D) (N ⊔ B)).1
    have hfix : (N ⊔ B) ⊓ fixV (⊥ : Subgroup (MulAut V)) = N ⊔ B := by
      refine inf_eq_left.2 fun v _ x hx => ?_
      rw [Subgroup.mem_bot.1 hx]
      rfl
    rw [Subgroup.card_bot, one_mul, hfix] at h
    exact h
  have hc2 := two_lt_card_commSub hNB hDN hDB (fun d hd => hfN d (hDL hd))
    (fun d hd => hfB d (hDL hd)) hD.2.1 hoff
  have hMQ : commSub N D ≤ N ⊓ fixV (Subgroup.zpowers c) := fun x hx =>
    ⟨commSub_le_of_invariant hDN hx, H.mem_fixV_zpowers_iff.2 (hcD x hx)⟩
  have hQ8 : Nat.card ↥(N ⊓ fixV (Subgroup.zpowers c)) = 8 := by
    have hmod := card_modEq_card_fix hc3 hcN
    have hdvd : Nat.card ↥(N ⊓ fixV (Subgroup.zpowers c)) ∣ 8 :=
      hcN8 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hge : 2 < Nat.card ↥(N ⊓ fixV (Subgroup.zpowers c)) :=
      lt_of_lt_of_le hc2 (Subgroup.card_le_of_le hMQ)
    have hle : Nat.card ↥(N ⊓ fixV (Subgroup.zpowers c)) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    rw [hcN8] at hmod
    unfold Nat.ModEq at hmod
    set q := Nat.card ↥(N ⊓ fixV (Subgroup.zpowers c)) with hq
    interval_cases q <;> omega
  have hcNfix : ∀ x ∈ N, c x = x := by
    have heq : N ⊓ fixV (Subgroup.zpowers c) = N :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hQ8, hcN8])
    intro x hx
    rw [← heq] at hx
    exact H.mem_fixV_zpowers_iff.1 hx.2
  have hcomm : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    have hk : c * l * c⁻¹ * l⁻¹ ∈ L := L.mul_mem (hcL l hl) (L.inv_mem hl)
    have h1 : c * l * c⁻¹ * l⁻¹ = 1 := by
      refine hfN _ hk fun x hx => ?_
      have hx' : l⁻¹ x ∈ N := hNL _ (L.inv_mem hl) x hx
      have h2 : c⁻¹ (l⁻¹ x) = l⁻¹ x := by
        conv_lhs => rw [← hcNfix _ hx']
        exact MulAut.inv_apply_self V c _
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, h2, MulAut.apply_inv_self]
      exact hcNfix x hx
    calc c * l = c * l * c⁻¹ * l⁻¹ * (l * c) := by group
      _ = l * c := by rw [h1, one_mul]
  have hZN : N ≤ (A ⊔ B) ⊓ fixV (Subgroup.zpowers c) := fun x hx =>
    ⟨hNU hx, H.mem_fixV_zpowers_iff.2 (hcNfix x hx)⟩
  have hZne : (A ⊔ B) ⊓ fixV (Subgroup.zpowers c) ≠ N := by
    intro heq
    have hmod := card_modEq_card_fix hc3 hcU
    rw [heq, hcU64, hcN8] at hmod
    exact absurd hmod (by decide)
  obtain ⟨u, hu, huN⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hZN (Ne.symm hZne))
  have hY : B ⊓ fixV (Subgroup.zpowers c) = B := by
    have hinv : ∀ l ∈ L, ∀ y ∈ B ⊓ fixV (Subgroup.zpowers c),
        l y ∈ B ⊓ fixV (Subgroup.zpowers c) := by
      intro l hl y hy
      refine ⟨hB l hl y hy.1, H.mem_fixV_zpowers_iff.2 ?_⟩
      have h1 := H.mem_fixV_zpowers_iff.1 hy.2
      rw [← MulAut.mul_apply, hcomm l hl, MulAut.mul_apply, h1]
    rcases hiB _ hinv inf_le_left with h | h
    · exfalso
      have hu' : u ∈ N ⊔ B := hNBU ▸ hu.1
      obtain ⟨n, hn, y, hy, hny⟩ := Subgroup.mem_sup.1 hu'
      have hcy : c y = y := by
        have hcu := H.mem_fixV_zpowers_iff.1 hu.2
        have e : y = n⁻¹ * u := by rw [← hny, inv_mul_cancel_left]
        rw [e, map_mul, map_inv, hcNfix n hn, hcu]
      have hy1 : y ∈ B ⊓ fixV (Subgroup.zpowers c) := ⟨hy, H.mem_fixV_zpowers_iff.2 hcy⟩
      rw [h, Subgroup.mem_bot] at hy1
      rw [hy1, mul_one] at hny
      exact huN (hny ▸ hn)
    · exact h
  intro x hx
  rw [← hNBU] at hx
  obtain ⟨n, hn, y, hy, rfl⟩ := Subgroup.mem_sup.1 hx
  have hy' : y ∈ B ⊓ fixV (Subgroup.zpowers c) := by rw [hY]; exact hy
  rw [map_mul, hcNfix n hn, H.mem_fixV_zpowers_iff.1 hy'.2]

theorem fix_of_two_nat [Finite V] {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {L X D : Subgroup (MulAut V)} {I : Fin 2 → Subgroup V} {π : ↥(StatedSL 3 F) →* ↥L}
    (hind : iSupIndep I) (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia L (I i) ⊥ π)
    (hD : IsFFStarOffender X D) (hDL : D ≤ L) {N : Subgroup V}
    (hNL : ∀ l ∈ L, ∀ x ∈ N, l x ∈ N) (hNU : N ≤ I 0 ⊔ I 1) (hN : N ≠ ⊥)
    (hUN : ¬ I 0 ⊔ I 1 ≤ N) {c : MulAut V} (hcL : ∀ l ∈ L, c * l * c⁻¹ ∈ L)
    (hcN : ∀ x ∈ N, c x ∈ N) (hcU : ∀ x ∈ I 0 ⊔ I 1, c x ∈ I 0 ⊔ I 1) (hc3 : c ^ 3 = 1)
    (hcD : ∀ x ∈ commSub N D, c x = x) :
    ∀ x ∈ I 0 ⊔ I 1, c x = x := by
  have h01 : I 0 ⊓ I 1 = ⊥ := disjoint_iff.1 (hind.pairwiseDisjoint (by decide))
  have hinv : ∀ i, ∀ l ∈ L, ∀ x ∈ I i, l x ∈ I i := fun i l hl x hx =>
    (hreal i).2.2.2.1 ⟨l, hl⟩ x hx
  have hirr : ∀ i, ∀ J : Subgroup V, (∀ l ∈ L, ∀ x ∈ J, l x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i := fun i J hJ hJI =>
    (B5.isIrr_of_realizes (by norm_num) (hreal i)).2.2 J (fun a x hx => hJ a a.2 x hx) bot_le
      hJI
  have hfaith : ∀ i, ∀ l ∈ L, (∀ x ∈ I i, l x = x) → l = 1 := fun i l hl h =>
    B51Sum.eq_one_of_realizesVia_nat (hreal i) hl h
  have hcard : ∀ i, Nat.card (I i) = 8 := by
    intro i
    obtain ⟨e, -⟩ := B5.exists_linModel (hreal i)
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hF,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hsub : ∀ i, N ⊓ I i ≠ ⊥ → I i ≤ N := by
    intro i hne
    rcases hirr i (N ⊓ I i) (fun l hl x hx => ⟨hNL l hl x hx.1, hinv i l hl x hx.2⟩)
        inf_le_right with h | h
    · exact absurd h hne
    · rw [← h]
      exact inf_le_left
  by_cases h0 : N ⊓ I 0 = ⊥
  · rw [sup_comm] at hNU hcU hUN ⊢
    exact fix_aux (by rw [inf_comm]; exact h01) (hinv 1) (hinv 0) (hirr 1) (hirr 0) (hfaith 1)
      (hfaith 0) (hcard 1) (hcard 0) hD hDL hNL hNU hN h0 hcL hcN hcU hc3 hcD
  · by_cases h1 : N ⊓ I 1 = ⊥
    · exact fix_aux h01 (hinv 0) (hinv 1) (hirr 0) (hirr 1) (hfaith 0) (hfaith 1) (hcard 0)
        (hcard 1) hD hDL hNL hNU hN h1 hcL hcN hcU hc3 hcD
    · exact absurd (sup_le (hsub 0 h0) (hsub 1 h1)) hUN

end A6NatPair

end CFSG.Quasithin.H13.A6
