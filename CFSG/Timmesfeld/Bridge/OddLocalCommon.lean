module

public import CFSG.Timmesfeld.Bridge.OddLocalCommonA

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

namespace OddLocal

variable {G : Type} [Group G] {D : Set G}

section Blocks

variable (hS : Setup G D) {d x y : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
  (hy : y ∈ D) (hyc : y ∈ Subgroup.closure {d, x}) (hdy : ¬ Commute d y)
  (hno : ∀ e ∈ D, Commute e d → Commute e x → False)
  [Finite G] (hcenter : Subgroup.center G = ⊥) {d₁ : G} {n : ℕ}
  (htri : IsTriangle D d y d₁) (hn : Odd n) (hord : orderOf (d * d₁ * y) = 2 * n)
include hS hd hx hdx hy hyc hdy hno hcenter htri hn hord

theorem false_of_yData (h12 : OddTranspSecondKind) (h16 : OddTranspZStar)
    (IH : CNBelow (Nat.card G)) (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b)
    (hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) (Yd : YData D d d₁ y n) {ℓ : G}
    (hℓ : ℓ ∈ D) (hℓd₁ : Commute ℓ d₁) (hℓx : Commute ℓ x) (hd₁x : ¬ Commute d₁ x) : False := by
  set a := Yd.a with ha
  have haD : a ∈ D := hClass_subset hS.normal hy Yd.a_mem
  have hacomm : Commute a d := Yd.a_comm
  have hd₁ : d₁ ∈ D := htri.2.1
  have hdd₁ : Commute d d₁ := htri.2.2.2.2.1
  have hd₁c : d₁ ∈ commSet D d := ⟨hd₁, hdd₁.symm, fun h => htri.2.2.2.1 h.symm⟩
  have hac : a ∈ commSet D d := ⟨haD, hacomm, Yd.a_ne⟩
  obtain ⟨E', hE'⟩ := exists_isMaxOrbit ⟨d₁, hd₁c⟩
  have hF := isMaxBlock_normSet_diff hS hconn hd hE'
  set F' := normSet D E' \ E' with hF'
  have hblock : MulAction.IsBlock (ConjAct G) F' := hF.2.2.2.1
  have hFD : F' ⊆ D := hF.2.1
  have hdF : d ∈ F' := self_mem_F hS.normal hd hE'
  have hsplit : ∀ {c : G}, c ∈ commSet D d → c ∈ E' ∨ c ∈ F' := by
    intro c hc
    by_cases h : c ∈ E'
    · exact Or.inl h
    · exact Or.inr ⟨mem_normSet_of_commute hS.normal hE' hc.1 hc.2.1, h⟩
  have hmemF : ∀ {t : G}, t ∈ D → Commute t d → (∀ e ∈ E', Commute t e) → t ∈ F' := by
    intro t ht htd htE
    refine ⟨mem_normSet_of_commute hS.normal hE' ht htd, fun htE' => ?_⟩
    obtain ⟨e', he', hne⟩ := exists_not_commute hS hd hE' hconn htE'
    exact hne (htE e' he')
  have hd₁E : d₁ ∈ E' := by
    rcases hsplit hd₁c with h | h
    · exact h
    · exfalso
      have hℓN := mem_normalizer_of_commute_of_isBlock hblock h hℓd₁
      by_cases hℓF : ℓ ∈ F'
      · have hxF : x ∈ F' := mem_of_not_commute hS.oddT hd₁ hx hd₁x h
          (mem_normalizer_of_commute_of_isBlock hblock h (Commute.refl d₁))
          (mem_normalizer_of_commute_of_isBlock hblock hℓF hℓx.symm)
        obtain ⟨e, he⟩ := nonempty hE'
        have he' := subset_commSet hS.normal hE' he
        exact hno e he'.1 he'.2.1 (commute_of_mem_F hS hE' hxF he).symm
      · exact hno ℓ hℓ (commute_of_mem_normalizer_of_not_mem hS.oddT hblock hFD hℓ hℓN hℓF hdF)
          hℓx
  have haF : a ∈ F' := by
    rcases hsplit hac with h | h
    · exfalso
      obtain ⟨e₀, -, hE'eq, -⟩ := id hE'
      rw [hE'eq] at hd₁E h
      rw [← orbitIn_eq_of_mem hd₁E] at h
      obtain ⟨c, hc, hca⟩ := h
      have hcd' : c * d * c⁻¹ = d := by
        rw [(commute_of_mem_closure_commSet hc).eq, mul_inv_cancel_right]
      obtain ⟨-, -, hzd, -, hzy, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
      have hzD : (d * d₁ * y) ^ n ∉ D := fun hz =>
        not_commute_pair hS hd hx hdx hy hyc hdy hno hz hzd hzy
      have htr : IsTriangle D d (c * y * c⁻¹) a := by
        refine ⟨hd, haD, hS.normal c y hy, Yd.a_ne.symm, hacomm.symm, fun h' => hdy ?_,
          fun h' => htri.2.2.2.2.2.2 ?_⟩
        · rw [← Commute.conj_iff c, hcd']
          exact h'
        · rw [← Commute.conj_iff c, ← hca]
          exact h'
      have heq : d * a * (c * y * c⁻¹) = c * (d * d₁ * y) * c⁻¹ := by
        rw [hca]
        calc d * (c * d₁ * c⁻¹) * (c * y * c⁻¹)
            = c * d * c⁻¹ * (c * d₁ * c⁻¹) * (c * y * c⁻¹) := by rw [hcd']
          _ = c * (d * d₁ * y) * c⁻¹ := by group
      refine false_of_thirdKind hS hd hx hdx hy hyc hdy hno hcenter htri hord h16 IH Yd htr hn
        ?_ ?_
      · rw [heq, orderOf_conj_eq]
        exact hord
      · rw [heq, conj_pow]
        intro h'
        exact hzD (by simpa [mul_assoc] using hS.normal c⁻¹ _ h')
    · exact h
  have hdN : d ∈ Subgroup.normalizer F' :=
    mem_normalizer_of_commute_of_isBlock hblock hdF (Commute.refl d)
  have haN : a ∈ Subgroup.normalizer F' :=
    mem_normalizer_of_commute_of_isBlock hblock haF (Commute.refl a)
  have hEda : ∀ e ∈ E', Commute e d ∧ Commute e a := fun e he =>
    ⟨(subset_commSet hS.normal hE' he).2.1, (commute_of_mem_F hS hE' haF he).symm⟩
  have hda1 : d * a ≠ 1 := fun h => Yd.a_ne (hS.oddT.eq_of_mul_eq_one hd h).symm
  have htF : ∀ {t : G}, t ∈ D → Commute t d → Commute t a → d * a * t ∈ D → t ∈ F' := by
    intro t ht htd hta hdat
    refine hmemF ht htd fun e he => ?_
    obtain ⟨hed, hea⟩ := hEda e he
    have heD := (subset_commSet hS.normal hE' he).1
    have hne : t ≠ d * a * t := by
      intro h
      apply hda1
      calc d * a = d * a * t * t⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel]
    have hc : Commute t (d * a * t) := (htd.mul_right hta).mul_right (Commute.refl t)
    have h1 : t * (d * a * t) = d * a := by
      calc t * (d * a * t) = t * (d * a) * t := by group
        _ = d * a * t * t := by rw [(htd.mul_right hta).eq]
        _ = d * a := by rw [mul_assoc (d * a), hS.oddT.mul_self_eq_one ht, mul_one]
    have hep : Commute e (t * (d * a * t)) := by
      rw [h1]
      exact hed.mul_right hea
    exact ((hS.oddT.commute_mul_iff ht hdat heD hne hc).mp hep).1.symm
  have hthird : ∀ {r : G}, IsTriangle D d r a → IsThirdKind d r a →
      ∃ t ∈ F', Commute t d ∧ Commute t r := by
    rintro r htr ⟨k, hk, -, hordk⟩
    obtain ⟨-, -, htd, hta, htr', hdat⟩ := htr.third_kind hS.oddT hS.normal hk hordk
    by_cases htD : (d * a * r) ^ k ∈ D
    · exact ⟨_, htF htD htd hta hdat, htd, htr'⟩
    · exact (false_of_thirdKind hS hd hx hdx hy hyc hdy hno hcenter htri hord h16 IH Yd htr hk
        hordk htD).elim
  have hSK : ∀ {u : G}, u ∈ D → u ∉ Subgroup.normalizer F' → SecondKindStructure d u a := by
    intro u hu huN
    have hdu : ¬ Commute d u := fun h =>
      huN (mem_normalizer_of_commute_of_isBlock hblock hdF h.symm)
    have hau : ¬ Commute a u := fun h =>
      huN (mem_normalizer_of_commute_of_isBlock hblock haF h.symm)
    have htr : IsTriangle D d u a := ⟨hd, haD, hu, Yd.a_ne.symm, hacomm.symm, hdu, hau⟩
    rcases htr.orderOf_cases hS.oddT hS.normal with h | h4 | h3
    · exact absurd (htr.mul_mem_of_odd hS.oddT hS.normal h.1) Yd.mul_not_mem
    · refine h12 G D hS.oddT hS.normal d u a htr h4 fun r hr hrc htr' hthk => ?_
      obtain ⟨t, htF', htd, htr''⟩ := hthird htr' hthk
      have htu := commute_of_commute_of_mem_closure hS.oddT hd hu hdu hr hrc htr'.2.2.2.2.2.1
        (hFD htF') htd htr''
      exact huN (mem_normalizer_of_commute_of_isBlock hblock htF' htu.symm)
    · obtain ⟨t, htF', -, htu⟩ := hthird htr h3
      exact (huN (mem_normalizer_of_commute_of_isBlock hblock htF' htu.symm)).elim
  have hdaQ : ∀ u : G, d * a ∈ conjClosure (Subgroup.closure {d, u}) (d * a) := fun _ =>
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by group⟩
  have hdQ : ∀ {u : G}, SecondKindStructure d u a →
      ∀ q ∈ conjClosure (Subgroup.closure {d, u}) (d * a), q * d * q⁻¹ ∈ F' := by
    intro u hSKu q hq
    have hqc : Commute q (d * a) := hSKu.comm q hq (d * a) (hdaQ u)
    have hd'D : q * d * q⁻¹ ∈ D := hS.normal q d hd
    have ha'D : q * a * q⁻¹ ∈ D := hS.normal q a haD
    have hprod : q * d * q⁻¹ * (q * a * q⁻¹) = d * a := by
      calc q * d * q⁻¹ * (q * a * q⁻¹) = q * (d * a) * q⁻¹ := by group
        _ = d * a := by rw [hqc.eq, mul_inv_cancel_right]
    have hne : q * d * q⁻¹ ≠ q * a * q⁻¹ := fun h =>
      Yd.a_ne (mul_left_cancel (mul_right_cancel h)).symm
    have hc' : Commute (q * d * q⁻¹) (q * a * q⁻¹) := hacomm.symm.conj q
    refine hmemF hd'D ?_ ?_
    · have h1 : Commute d (q * d * q⁻¹ * (q * a * q⁻¹)) := by
        rw [hprod]
        exact (Commute.refl d).mul_right hacomm.symm
      exact ((hS.oddT.commute_mul_iff hd'D ha'D hd hne hc').mp h1).1.symm
    · intro e he
      obtain ⟨hed, hea⟩ := hEda e he
      have heD := (subset_commSet hS.normal hE' he).1
      have h1 : Commute e (q * d * q⁻¹ * (q * a * q⁻¹)) := by
        rw [hprod]
        exact hed.mul_right hea
      exact ((hS.oddT.commute_mul_iff hd'D ha'D heD hne hc').mp h1).1.symm
  have hker : ∀ g : G, g * (d * a) * g⁻¹ ∈ Subgroup.normalizer F' := by
    intro g
    have hdaN : d * a ∈ Subgroup.normalizer F' := Subgroup.mul_mem _ hdN haN
    have hbD : g⁻¹ * d * g ∈ D := by simpa using hS.normal g⁻¹ d hd
    refine isBlock_conj_iff.mp hblock _ d hdF ?_
    by_cases hbN : g⁻¹ * d * g ∈ Subgroup.normalizer F'
    · by_cases hbF : g⁻¹ * d * g ∈ F'
      ·
        have hgN : g⁻¹ ∈ Subgroup.normalizer F' :=
          isBlock_conj_iff.mp hblock g⁻¹ d hdF (by simpa using hbF)
        have hgN' : g ∈ Subgroup.normalizer F' := by simpa using Subgroup.inv_mem _ hgN
        have hk : g * (d * a) * g⁻¹ ∈ Subgroup.normalizer F' :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hdaN) (Subgroup.inv_mem _ hgN')
        exact (Subgroup.mem_set_normalizer_iff.mp hk d).mp hdF
      ·
        have hbd := commute_of_mem_normalizer_of_not_mem hS.oddT hblock hFD hbD hbN hbF hdF
        have hba := commute_of_mem_normalizer_of_not_mem hS.oddT hblock hFD hbD hbN hbF haF
        have hbda : Commute (d * a) (g⁻¹ * d * g) := (hbd.mul_right hba).symm
        have h1 : g * (d * a) * g⁻¹ * d * (g * (d * a) * g⁻¹)⁻¹ = d := by
          calc g * (d * a) * g⁻¹ * d * (g * (d * a) * g⁻¹)⁻¹
              = g * ((d * a) * (g⁻¹ * d * g) * (d * a)⁻¹) * g⁻¹ := by group
            _ = g * (g⁻¹ * d * g) * g⁻¹ := by rw [hbda.eq, mul_inv_cancel_right]
            _ = d := by group
        rw [h1]
        exact hdF
    ·
      have hSKb := hSK hbD hbN
      have hdb : ¬ Commute d (g⁻¹ * d * g) := fun h =>
        hbN (mem_normalizer_of_commute_of_isBlock hblock hdF h.symm)
      obtain ⟨h, hh, hhd⟩ := hS.oddT.exists_conj hd hbD hdb
      have hhK : h⁻¹ ∈ Subgroup.closure {d, g⁻¹ * d * g, a} := by
        refine Subgroup.inv_mem _ (Subgroup.closure_mono ?_ hh)
        rintro w (rfl | rfl)
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      have hn'd := hdQ hSKb _ (hSKb.normal h⁻¹ hhK (d * a) (hdaQ _))
      have hghN : g * h ∈ Subgroup.normalizer F' := by
        refine isBlock_conj_iff.mp hblock _ d hdF ?_
        have h1 : g * h * d * (g * h)⁻¹ = d := by
          calc g * h * d * (g * h)⁻¹ = g * (h * d * h⁻¹) * g⁻¹ := by group
            _ = d := by rw [hhd]; group
        rw [h1]
        exact hdF
      have h1 : g * (d * a) * g⁻¹ * d * (g * (d * a) * g⁻¹)⁻¹ =
          (g * h) * ((h⁻¹ * (d * a) * h⁻¹⁻¹) * d * (h⁻¹ * (d * a) * h⁻¹⁻¹)⁻¹) * (g * h)⁻¹ := by
        calc g * (d * a) * g⁻¹ * d * (g * (d * a) * g⁻¹)⁻¹
            = g * (d * a) * (g⁻¹ * d * g) * (d * a)⁻¹ * g⁻¹ := by group
          _ = g * (d * a) * (h * d * h⁻¹) * (d * a)⁻¹ * g⁻¹ := by rw [hhd]
          _ = _ := by group
      rw [h1]
      exact (Subgroup.mem_set_normalizer_iff.mp hghN _).mp hn'd
  have hdaK : d * a ∈ (Subgroup.normalizer F').normalCore := fun g => hker g
  rcases hsimple _ (Subgroup.normalCore_normal _) with hK | hK
  · rw [hK, Subgroup.mem_bot] at hdaK
    exact hda1 hdaK
  · apply hF.2.2.1
    refine Set.Subset.antisymm hFD fun w hw => ?_
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hd hw)
    have hcN : c ∈ Subgroup.normalizer F' :=
      Subgroup.normalCore_le _ (by rw [hK]; exact Subgroup.mem_top c)
    exact (Subgroup.mem_set_normalizer_iff.mp hcN d).mp hdF

end Blocks

theorem false_of_bad_pair [Finite G] (hS : Setup G D) (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b)
    (hsq : OddTransp.MeetsSq D) (hcenter : Subgroup.center G = ⊥)
    (hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) (h12 : OddTranspSecondKind)
    (h14 : OddTranspThirdKind) (h16 : OddTranspZStar) (hnpc : NPCDischarge)
    (IH : CNBelow (Nat.card G)) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hno : ∀ e ∈ D, Commute e d → Commute e x → False) {d₁ : G} (hd₁ : d₁ ∈ D)
    (hdd₁ : Commute d d₁) (hne : d₁ ≠ d) (hd₁x : ¬ Commute d₁ x) {ℓ : G} (hℓ : ℓ ∈ D)
    (hℓd₁ : Commute ℓ d₁) (hℓx : Commute ℓ x) : False := by
  have htri : IsTriangle D d x d₁ := ⟨hd, hd₁, hx, hne.symm, hdd₁, hdx, hd₁x⟩
  obtain ⟨y, hy, hyc, htriy, n, hn, hn1, hord⟩ : ∃ y ∈ D, y ∈ Subgroup.closure {d, x} ∧
      IsTriangle D d y d₁ ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧ orderOf (d * d₁ * y) = 2 * n := by
    rcases htri.orderOf_cases hS.oddT hS.normal with h | h4 | h3
    ·
      exfalso
      have htri' : IsTriangle D d₁ x d := ⟨hd₁, hd, hx, hne, hdd₁.symm, hd₁x, hdx⟩
      have hodd : Odd (orderOf (d₁ * d * x)) := by
        rw [← hdd₁.eq]
        exact h.1
      have h1 := ((htri'.commute_iff_of_odd hS hodd).2 ℓ hℓ).mp hℓd₁
      exact hno ℓ hℓ ((hS.oddT.commute_mul_iff hd₁ hd hℓ hne hdd₁.symm).mp h1).2 hℓx
    ·
      by_contra hcon
      have hyp : ∀ y ∈ D, y ∈ Subgroup.closure {d, x} → IsTriangle D d y d₁ →
          ¬ IsThirdKind d y d₁ := by
        rintro y hy hyc htr ⟨n, hn, hn1, hord⟩
        exact hcon ⟨y, hy, hyc, htr, n, hn, hn1, hord⟩
      have hSK := h12 G D hS.oddT hS.normal d x d₁ htri h4 hyp
      obtain ⟨g, hg, hgd⟩ := hSK.conj
      have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp (hSK.le_centralizer hg)
      have hd' : g⁻¹ * d₁ * g⁻¹⁻¹ = d := by
        rw [← hgd]
        group
      have hx' : g⁻¹ * x * g⁻¹⁻¹ = x := by
        calc g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * (x * g) := by group
          _ = g⁻¹ * (g * x) := by rw [← hgx.eq]
          _ = x := by group
      have h1 := hℓd₁.conj g⁻¹
      have h2 := hℓx.conj g⁻¹
      rw [hd'] at h1
      rw [hx'] at h2
      exact hno _ (hS.normal g⁻¹ ℓ hℓ) h1 h2
    · obtain ⟨n, hn, hn1, hord⟩ := h3
      exact ⟨x, hx, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton x)), htri,
        n, hn, hn1, hord⟩
  have hdy : ¬ Commute d y := htriy.2.2.2.2.2.1
  obtain ⟨Yd⟩ := exists_yData hS hd hx hdx hy hyc hdy hno hcenter htriy hn hord hn1 h14 h16 hnpc
    IH hsq
  exact false_of_yData hS hd hx hdx hy hyc hdy hno hcenter htriy hn hord h12 h16 IH hconn hsimple
    Yd hℓ hℓd₁ hℓx hd₁x

theorem exists_common_step (h9 : OddTranspSimple) (h12 : OddTranspSecondKind)
    (h14 : OddTranspThirdKind) (h16 : OddTranspZStar) (hnpc : NPCDischarge) [Finite G]
    (IH : CNBelow (Nat.card G)) (hS : Setup G D) (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b)
    (hsq : OddTransp.MeetsSq D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x) :
    ∃ e ∈ D, Commute e d ∧ Commute e x := by
  by_contra hno
  by_cases hZ : zStar G = ⊥
  ·
    obtain ⟨-, hsimpQ⟩ := h9 G D hS hsq
    have hinj : Function.Injective (QuotientGroup.mk' (zStar G)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
    have hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ := by
      intro N hN
      have hNm : (N.map (QuotientGroup.mk' (zStar G))).Normal :=
        hN.map _ (QuotientGroup.mk'_surjective _)
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimpQ _ hNm with h | h
      · exact Or.inl (Subgroup.map_injective hinj (h.trans (Subgroup.map_bot _).symm))
      · exact Or.inr (Subgroup.map_injective hinj
          (h.trans (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)).symm))
    have hcenter : Subgroup.center G = ⊥ := by
      rw [eq_bot_iff, ← hZ]
      intro g hg
      rw [OddTransp.mem_zStar_iff]
      intro h
      rw [commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hg h).symm]
      exact Subgroup.one_mem _
    obtain ⟨d', hd', hd'x, hno', d₁, hd₁, hd'd₁, hne, hd₁x, ℓ, hℓ, hℓd₁, hℓx⟩ :=
      exists_bad_pair hd hdx hno (hconn d hd x hx)
    exact false_of_bad_pair hS hconn hsq hcenter hsimple h12 h14 h16 hnpc IH hd' hx hd'x
      (fun e he h1 h2 => hno' ⟨e, he, h1, h2⟩) hd₁ hd'd₁ hne hd₁x hℓ hℓd₁ hℓx
  ·
    set π := QuotientGroup.mk' (zStar G) with hπ
    have hcomm : ∀ {u v : G}, u ∈ D → v ∈ D → (Commute (π u) (π v) ↔ Commute u v) :=
      fun hu hv => commute_iff_mod_zStar hS.oddT hu hv
    have h1 : ∀ w ∈ D, π w ≠ 1 := by
      intro w hw h
      have hwZ : w ∈ zStar G := by
        rwa [← QuotientGroup.ker_mk' (zStar G), MonoidHom.mem_ker]
      rcases hS.subset_or_disjoint (zStar G) with hsub | hdis
      · apply hdx
        have hd1 : π d = 1 := (QuotientGroup.eq_one_iff d).mpr (hsub hd)
        have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr (hsub hx)
        exact (hcomm hd hx).mp (by rw [hd1, hx1])
      · exact hdis w hw hwZ
    have hcard : Nat.card (G ⧸ zStar G) < Nat.card G := by
      have hlt : 1 < Nat.card (zStar G) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (zStar G)]
      exact lt_mul_of_one_lt_right Nat.card_pos hlt
    have hconnq : ∀ a ∈ π '' D, ∀ b ∈ π '' D, Reach (π '' D) a b := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact reach_map π (hconn a ha b hb)
    obtain ⟨_, ⟨e, he, rfl⟩, hed, hex⟩ := IH (G ⧸ zStar G) (π '' D) hcard
      (hS.map π (QuotientGroup.mk'_surjective _) h1) hconnq (hsq.map hS.oddT π h1) (π d)
      ⟨d, hd, rfl⟩ (π x) ⟨x, hx, rfl⟩ fun h => hdx ((hcomm hd hx).mp h)
    exact hno ⟨e, he, (hcomm he hd).mp hed, (hcomm he hx).mp hex⟩

end OddLocal

theorem commonNeighbour_of (h9 : OddTranspSimple) (h12 : OddTranspSecondKind)
    (h14 : OddTranspThirdKind) (h16 : OddTranspZStar) (hnpc : NPCDischarge) :
    CommonNeighbourStmt := by
  have key : ∀ m, CNBelow m := by
    intro m
    induction m with
    | zero => exact fun _ _ _ _ hcard => absurd hcard (Nat.not_lt_zero _)
    | succ m ih =>
      intro H _ _ E hcard hS hconn hsq d hd x hx hdx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hcard with hlt | heq
      · exact ih H E hlt hS hconn hsq d hd x hx hdx
      · exact OddLocal.exists_common_step h9 h12 h14 h16 hnpc (by rw [heq]; exact ih) hS hconn
          hsq hd hx hdx
  intro G _ _ D hS hconn hsq d hd x hx hdx
  exact key (Nat.card G + 1) G D (Nat.lt_succ_self _) hS hconn hsq d hd x hx hdx

end CFSG.Timmesfeld.Bridge
