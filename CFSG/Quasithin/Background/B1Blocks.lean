module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.B1Transvection
import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

namespace IsTransvectionBlocks

variable {J : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))} {H H' : Subgroup (MulAut V)}

theorem le_J (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) : H ≤ J := by
  rw [← hb.iSup_eq]
  exact le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH

theorem le_stabSub (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) :
    H ≤ stabSub (commSub (⊤ : Subgroup V) H) :=
  B1.le_stabSub_of_invariant (hb.stab H hH)

theorem le_centSub (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) (hH' : H' ∈ 𝓗) (hne : H ≠ H') :
    H ≤ centSub (commSub (⊤ : Subgroup V) H') :=
  fun a ha u hu => hb.triv H hH H' hH' hne a ha u hu

theorem J_le_stabSub (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) :
    J ≤ stabSub (commSub (⊤ : Subgroup V) H) := by
  rw [← hb.iSup_eq]
  refine iSup₂_le fun K hK => ?_
  by_cases h : K = H
  · subst h
    exact hb.le_stabSub hK
  · exact (hb.le_centSub hK hH h).trans (centSub_le_stabSub _)

theorem inf_centSub (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗) :
    H ⊓ centSub (commSub (⊤ : Subgroup V) H) = ⊥ := by
  obtain ⟨C, -, hCsup, hC⟩ := hb.exists_compl H hH
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => MulEquiv.ext fun v => ?_
  have hv : v ∈ C ⊔ commSub ⊤ H := by rw [hCsup]; trivial
  obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
  show g (c * m) = c * m
  rw [map_mul, hC g hg.1 c hc, hg.2 m hm]

theorem transitive (hV : ∀ v : V, v ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗) (hH : H ∈ 𝓗)
    {u w : V} (hu : u ∈ commSub (⊤ : Subgroup V) H) (hw : w ∈ commSub (⊤ : Subgroup V) H)
    (hu1 : u ≠ 1) (hw1 : w ≠ 1) : ∃ h ∈ H, h u = w := by
  have := B1.isKleinFour_of_card_four hV (hb.card_comm H hH)
  obtain ⟨φ, hφ⟩ := CFSG.kleinFour_automorphism_transitive (commSub (⊤ : Subgroup V) H)
    ⟨u, hu⟩ ⟨w, hw⟩ (fun h => hu1 (congrArg Subtype.val h)) (fun h => hw1 (congrArg Subtype.val h))
  have hmem : φ ∈ autSub H (commSub (⊤ : Subgroup V) H) := by
    rw [hb.autSub_eq_top H hH]
    trivial
  obtain ⟨g, hgH, hgφ⟩ := mem_autSub.1 hmem
  refine ⟨g, hgH, ?_⟩
  have h1 := congrArg (fun z : commSub (⊤ : Subgroup V) H => (z : V)) hφ
  simp only at h1
  rw [← hgφ, resHom_apply] at h1
  exact h1

theorem tv_centre_mem_commSub {t : MulAut V} {w : V} (h : IsTransvectionWith t w) (ht : t ≠ 1)
    (htH : t ∈ H) : w ∈ commSub (⊤ : Subgroup V) H := by
  obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one ht
  have h1 : t v = v * w := (h.2 v).resolve_left hv
  have hw : w = t v * v⁻¹ := by rw [h1, mul_comm v w, mul_inv_cancel_right]
  rw [hw]
  exact Subgroup.subset_closure ⟨t, htH, v, Subgroup.mem_top v, rfl⟩

theorem invariant_of_centralizes (hV : ∀ v : V, v ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hH : H ∈ 𝓗) {B : Subgroup (MulAut V)} (hBJ : ∀ b ∈ B, ∀ j ∈ J, b * j * b⁻¹ ∈ J)
    {t : MulAut V} {w : V} (htw : IsTransvectionWith t w) (ht1 : t ≠ 1) (htH : t ∈ H)
    (hBt : ∀ b ∈ B, b * t = t * b) :
    ∀ b ∈ B, ∀ u ∈ commSub (⊤ : Subgroup V) H, b u ∈ commSub (⊤ : Subgroup V) H := by
  intro b hb' u hu
  have hwW : w ∈ commSub (⊤ : Subgroup V) H := tv_centre_mem_commSub htw ht1 htH
  have hbw : b w = w := B1.tv_comm_centre htw ht1 (hBt b hb')
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
    exact one_mem _
  · obtain ⟨h, hhH, rfl⟩ := hb.transitive hV hH hwW hu htw.1 hu1
    have hbinv : b⁻¹ w = w := by
      calc b⁻¹ w = b⁻¹ (b w) := by rw [hbw]
        _ = w := by simp
    have hconj : b (h w) = (b * h * b⁻¹) w := by
      show b (h w) = b (h (b⁻¹ w))
      rw [hbinv]
    rw [hconj]
    have hJ' : b * h * b⁻¹ ∈ J := hBJ b hb' h (hb.le_J hH hhH)
    exact (mem_stabSub.1 (hb.J_le_stabSub hH hJ') w).2 hwW

theorem card_autSub_le_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (hH : H ∈ 𝓗) {B : Subgroup (MulAut V)} (hB : IsElemAbelian2 B)
    (hBst : B ≤ stabSub (commSub (⊤ : Subgroup V) H))
    (hmov : ¬ commSub (⊤ : Subgroup V) H ≤ fixV B) :
    Nat.card (autSub B (commSub (⊤ : Subgroup V) H)) ≤ 2 := by
  have hB2 : IsA2 B B :=
    ⟨le_rfl, fun h => hmov (by rw [h, B1.fixV_bot]; exact le_top), hB⟩
  have hA2 := (B1.isA2_autSub hB2 hBst hmov).isElemAbelian2
  have hcard := B1.card_elemAbelian hA2
  have hdvd : Nat.card (autSub B (commSub (⊤ : Subgroup V) H)) ∣ 6 := by
    rw [← B1.card_mulAut_of_card_four hV (hb.card_comm H hH)]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd ⊢
  rcases Nat.lt_or_ge (rk (autSub B (commSub (⊤ : Subgroup V) H))) 2 with hlt | hge
  · interval_cases (rk (autSub B (commSub (⊤ : Subgroup V) H))) <;> simp
  · exfalso
    have h4 : 4 ∣ 2 ^ rk (autSub B (commSub (⊤ : Subgroup V) H)) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge
      rw [hk, pow_add]
      exact Dvd.intro _ rfl
    have := h4.trans hdvd
    omega

end IsTransvectionBlocks

namespace B1

theorem fixV_sup (A D : Subgroup (MulAut V)) : fixV (A ⊔ D) = fixV A ⊓ fixV D :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq A D

theorem card_sup_zpowers {t : MulAut V} (hsq : t * t = 1) {D : Subgroup (MulAut V)}
    (hcomm : ∀ d ∈ D, t * d = d * t) (htD : t ∉ D) :
    Nat.card ↥(Subgroup.zpowers t ⊔ D) = 2 * Nat.card D := by
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
  have hcomm' : ∀ y : MulAut V, y * t ∈ D → t * y = y * t := by
    intro y hy
    calc t * y = t * y * (t * t) := by rw [hsq, mul_one]
      _ = (t * (y * t)) * t := by group
      _ = ((y * t) * t) * t := by rw [hcomm (y * t) hy]
      _ = (y * t) * (t * t) := by group
      _ = y * t := by rw [hsq, mul_one]
  let K : Subgroup (MulAut V) :=
    { carrier := {b | b ∈ D ∨ b * t ∈ D}
      one_mem' := Or.inl D.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (D.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact D.mul_mem hx hy
        · right
          have h1 : x * y * t = (x * t) * y := by
            rw [mul_assoc, ← hcomm y hy, ← mul_assoc]
          rw [h1]
          exact D.mul_mem hx hy
        · left
          have h1 : (x * t) * (y * t) = x * y := by
            calc (x * t) * (y * t) = x * (t * y) * t := by group
              _ = x * (y * t) * t := by rw [hcomm' y hy]
              _ = x * y * (t * t) := by group
              _ = x * y := by rw [hsq, mul_one]
          have h2 := D.mul_mem hx hy
          rwa [h1] at h2
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (D.inv_mem hx)
        · right
          have hxt : t * x = x * t := hcomm' x hx
          have h1 : x⁻¹ * t = t * x⁻¹ := by
            calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt]
              _ = t * x⁻¹ := by group
          have h2 : x⁻¹ * t = (x * t)⁻¹ := by rw [mul_inv_rev, hinv, h1]
          rw [h2]
          exact D.inv_mem hx }
  have hAK : Subgroup.zpowers t ⊔ D ≤ K := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [hsq]; exact D.one_mem)
    · exact fun d hd => Or.inl hd
  have hDA : D ≤ Subgroup.zpowers t ⊔ D := le_sup_right
  have htA : t ∈ Subgroup.zpowers t ⊔ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hidx : (D.subgroupOf (Subgroup.zpowers t ⊔ D)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htA⟩, fun b => ?_⟩
    have hb : (b : MulAut V) ∈ D ∨ (b : MulAut V) * t ∈ D := hAK b.2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | hb
    · right
      refine ⟨hb, fun hp => htD ?_⟩
      have := D.mul_mem (D.inv_mem hb) hp
      simpa using this
    · left
      refine ⟨hb, fun hq => htD ?_⟩
      have := D.mul_mem (D.inv_mem hq) hb
      simpa using this
  have h1 := Subgroup.card_mul_index (D.subgroupOf (Subgroup.zpowers t ⊔ D))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv] at h1
  omega

theorem two_mul_card_fixV_sup [Finite V] {W C : Subgroup V} (hWC : W ⊓ C = ⊥)
    (hWC' : W ⊔ C = ⊤) {t : MulAut V} (htC : ∀ c ∈ C, t c = c)
    (hW : Nat.card ↥(W ⊓ fixV (Subgroup.zpowers t)) * 2 = Nat.card W)
    {D : Subgroup (MulAut V)} (hD : D ≤ centSub W) :
    2 * Nat.card ↥(fixV (Subgroup.zpowers t ⊔ D)) = Nat.card ↥(fixV D) := by
  have hWM : W ≤ fixV D := fun u hu d hd => hD hd u hu
  have hCF : C ≤ fixV (Subgroup.zpowers t) := fun c hc y hy => zpowers_fix (htC c hc) y hy
  have hMdecomp : ∀ v ∈ fixV D, ∃ u ∈ W, ∃ c ∈ fixV D ⊓ C, v = u * c := by
    intro v hv
    have hv' : v ∈ W ⊔ C := by rw [hWC']; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv'
    refine ⟨u, hu, c, ⟨?_, hc⟩, rfl⟩
    have h1 : c = u⁻¹ * (u * c) := by group
    rw [h1]
    exact (fixV D).mul_mem ((fixV D).inv_mem (hWM hu)) hv
  have hcardM : Nat.card ↥(fixV D) = Nat.card ↥W * Nat.card ↥(fixV D ⊓ C) := by
    have hMeq : W ⊔ (fixV D ⊓ C) = fixV D := by
      refine le_antisymm (sup_le hWM inf_le_left) fun v hv => ?_
      obtain ⟨u, hu, c, hc, rfl⟩ := hMdecomp v hv
      exact Subgroup.mul_mem_sup hu hc
    have hinf : W ⊓ (fixV D ⊓ C) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      have h1 : x ∈ W ⊓ C := ⟨hx.1, hx.2.2⟩
      rw [hWC] at h1
      exact h1
    have := card_sup_mul_card_inf W (fixV D ⊓ C)
    rwa [hMeq, hinf, Subgroup.card_bot, mul_one] at this
  have hFM : fixV (Subgroup.zpowers t) ⊓ fixV D =
      (W ⊓ fixV (Subgroup.zpowers t)) ⊔ (fixV D ⊓ C) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro v ⟨hvF, hvM⟩
      obtain ⟨u, hu, c, hc, rfl⟩ := hMdecomp v hvM
      have htc := htC c hc.2
      have htu : t u = u := by
        have h1 : t (u * c) = u * c := hvF t (Subgroup.mem_zpowers t)
        rw [map_mul, htc] at h1
        exact mul_right_cancel h1
      have hu' : u ∈ W ⊓ fixV (Subgroup.zpowers t) := ⟨hu, fun y hy => zpowers_fix htu y hy⟩
      exact Subgroup.mul_mem_sup hu' hc
    · exact fun x hx => ⟨hx.2, hWM hx.1⟩
    · exact fun x hx => ⟨hCF hx.2, hx.1⟩
  have hinf2 : (W ⊓ fixV (Subgroup.zpowers t)) ⊓ (fixV D ⊓ C) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h1 : x ∈ W ⊓ C := ⟨hx.1.1, hx.2.2⟩
    rw [hWC] at h1
    exact h1
  have hcardFM : Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ fixV D) =
      Nat.card ↥(W ⊓ fixV (Subgroup.zpowers t)) * Nat.card ↥(fixV D ⊓ C) := by
    have := card_sup_mul_card_inf (W ⊓ fixV (Subgroup.zpowers t)) (fixV D ⊓ C)
    rwa [hinf2, Subgroup.card_bot, mul_one, ← hFM] at this
  rw [fixV_sup]
  calc 2 * Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ fixV D)
      = 2 * (Nat.card ↥(W ⊓ fixV (Subgroup.zpowers t)) * Nat.card ↥(fixV D ⊓ C)) := by
        rw [hcardFM]
    _ = (Nat.card ↥(W ⊓ fixV (Subgroup.zpowers t)) * 2) * Nat.card ↥(fixV D ⊓ C) := by ring
    _ = Nat.card W * Nat.card ↥(fixV D ⊓ C) := by rw [hW]
    _ = Nat.card ↥(fixV D) := hcardM.symm

theorem peel [Finite V] {W C : Subgroup V} (hWC : W ⊓ C = ⊥) (hWC' : W ⊔ C = ⊤)
    {t : MulAut V} (hsq : t * t = 1) (htC : ∀ c ∈ C, t c = c)
    (hW : Nat.card ↥(W ⊓ fixV (Subgroup.zpowers t)) * 2 = Nat.card W)
    {D : Subgroup (MulAut V)} (hD : D ≤ centSub W) (hcomm : ∀ d ∈ D, t * d = d * t)
    (htD : t ∉ D) :
    Nat.card ↥(Subgroup.zpowers t ⊔ D) * Nat.card ↥(fixV (Subgroup.zpowers t ⊔ D)) =
      Nat.card D * Nat.card ↥(fixV D) := by
  have h1 := two_mul_card_fixV_sup hWC hWC' htC hW hD
  have h2 := card_sup_zpowers hsq hcomm htD
  rw [h2]
  calc 2 * Nat.card D * Nat.card ↥(fixV (Subgroup.zpowers t ⊔ D))
      = Nat.card D * (2 * Nat.card ↥(fixV (Subgroup.zpowers t ⊔ D))) := by ring
    _ = Nat.card D * Nat.card ↥(fixV D) := by rw [h1]

end B1

end CFSG.Quasithin
