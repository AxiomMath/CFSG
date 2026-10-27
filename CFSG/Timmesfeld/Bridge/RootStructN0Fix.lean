module

public import CFSG.Timmesfeld.Bridge.RootStructR2Torus
public import CFSG.Timmesfeld.Bridge.RootStructWTIFrattini

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld RootDegen

variable {G : Type} [Group G] {D : Set G}

theorem mem_rootGroup_of_conj_mem_rootSet (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    {d a e z t : G} (hd : d ∈ D) (ha : a ∈ D) (hda : Commute d a) (hdaD : d * a ∈ D)
    (haT : a ∉ rootSet D d) (he : e ∈ D) (hde : Commute d e) (hdeD : d * e ∈ D)
    (heL : e ∉ rootGroup D d ⊔ rootGroup D a) (hz : z ∈ rootGroup D d ⊔ rootGroup D e)
    (ht : t ∈ D) (htL : t ∈ rootGroup D d ⊔ rootGroup D a) (htT : t ∉ rootSet D d)
    (hzt : z * t * z⁻¹ ∈ rootSet D t) : z ∈ rootGroup D d := by
  have := h.finite
  have hD := h.root
  have hLS : LineSetting G D := ⟨h, hc, hs, hconn, ⟨d, hd, a, ha, hda, hdaD, haT,
    hAll d hd a ha hda hdaD haT⟩⟩
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line he hde hz
  by_cases hγ1 : γ = 1
  · rw [hγ1, mul_one]
    exact hβ
  exfalso
  have hγT : γ ∈ rootSet D e := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc he hγ hγ1
  have hdT : d ∉ rootSet D a := fun h' => haT (mem_rootSet_comm ha h')
  have had : Commute a d := hda.symm
  have hadD : a * d ∈ D := by rw [← hda.eq]; exact hdaD
  have heL' : e ∉ rootGroup D a ⊔ rootGroup D d := by rwa [sup_comm]
  have hae : orderOf (a * e) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line' hD hLS.lineCentralizerEq ha hd had hadD hdT
      (hAll a ha d hd had hadD hdT) he hde heL'
  have htL' : t ∈ rootGroup D a ⊔ rootGroup D d := by rwa [sup_comm]
  have htr : γ * t * γ⁻¹ * t⁻¹ ∈ rootGroup D d :=
    mul_inv_mem_of_special hD hc hs hLS.commLambda ha hd had hadD he hde hdeD hae hγT htL'
  have hγtL : γ * t * γ⁻¹ ∈ rootGroup D d ⊔ rootGroup D a := by
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_left htr) htL
    rwa [inv_mul_cancel_right] at this
  have hβtγ : β * γ * t * (β * γ)⁻¹ = γ * t * γ⁻¹ := by
    have hc' : Commute β (γ * t * γ⁻¹) :=
      commute_of_mem_sup_rootGroup hd ha hda (Subgroup.mem_sup_left hβ) hγtL
    rw [show β * γ * t * (β * γ)⁻¹ = β * (γ * t * γ⁻¹) * β⁻¹ by group, hc'.eq,
      mul_inv_cancel_right]
  rw [hβtγ] at hzt
  have hne : rootSet D t ≠ rootSet D d := fun e' => htT (by
    rw [← e']
    exact mem_rootSet_self ht)
  have hinf := rootGroup_inf_eq_bot_of_rootClosure hD hc ht hd hne
  have htrt : γ * t * γ⁻¹ * t⁻¹ ∈ rootGroup D t :=
    Subgroup.mul_mem _ (rootSet_subset_rootGroup D t hzt)
      (Subgroup.inv_mem _ (rootSet_subset_rootGroup D t (mem_rootSet_self ht)))
  have h1 : γ * t * γ⁻¹ * t⁻¹ ∈ rootGroup D t ⊓ rootGroup D d := ⟨htrt, htr⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
  have hγt : Commute γ t := by
    show γ * t = t * γ
    calc γ * t = γ * t * γ⁻¹ * γ := by group
      _ = t * γ := by rw [h1]
  have hγd : Commute γ d := (hγT.2 d hd).2 hde.symm
  have hdt : Commute d t := commute_of_mem_sup_rootGroup hd ha hda (left_mem_line hd) htL
  have hdt1 : d * t ≠ 1 := fun h' => htT (by
    rw [(eq_inv_of_mul_eq_one_right h').trans (hD.inv_eq hd)]
    exact mem_rootSet_self hd)
  have hdtD : d * t ∈ D := mem_of_mem_sup_rootGroup h hc hs hd ha hda hdaD haT
    (Subgroup.mul_mem _ (left_mem_line hd) htL) hdt1
  have hγL : γ ∈ rootGroup D d ⊔ rootGroup D t :=
    mem_sup_of_commute_of_lineTI h hc hs hconn hd ht hdt hdtD htT (hAll d hd t ht hdt hdtD htT)
      hγT.1 hγd hγt
  have hLeq : rootGroup D d ⊔ rootGroup D t = rootGroup D d ⊔ rootGroup D a :=
    sup_rootGroup_eq_of_mem h hc hs hd ha hda hdaD haT (left_mem_line hd) htL (hD.ne_one hd)
      (hD.ne_one ht) htT
  rw [hLeq] at hγL
  apply heL
  have hle := rootGroup_le_sup_of_mem h hc hs hd ha hda hdaD haT hγL (hD.ne_one hγT.1)
  rw [rootGroup_eq_of_mem hγT] at hle
  exact hle (rootSet_subset_rootGroup D e (mem_rootSet_self he))

theorem existsUnique_conj_mem_rootSet_of_line (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    {d a e g y : G} (hd : d ∈ D) (ha : a ∈ D) (hda : Commute d a) (hdaD : d * a ∈ D)
    (haT : a ∉ rootSet D d) (he : e ∈ D) (hde : Commute d e) (hdeD : d * e ∈ D)
    (heL : e ∉ rootGroup D d ⊔ rootGroup D a) (hp : (orderOf g).Prime) (hp2 : orderOf g ≠ 2)
    (hy : y ∈ D) (hyg : y * g * y⁻¹ = g⁻¹) (hgd : g * d * g⁻¹ ∈ rootSet D d)
    (hgL : ∀ u ∈ rootGroup D d ⊔ rootGroup D a, g * u * g⁻¹ ∈ rootGroup D d ⊔ rootGroup D a)
    (hgN : ∀ u ∈ rootGroup D d ⊔ rootGroup D e, g * u * g⁻¹ ∈ rootGroup D d ⊔ rootGroup D e) :
    (∃ t ∈ D, t ∈ rootGroup D d ⊔ rootGroup D a ∧ t ∉ rootSet D d ∧
        g * t * g⁻¹ ∈ rootSet D t) ∧
      ∀ t ∈ D, t ∈ rootGroup D d ⊔ rootGroup D a → t ∉ rootSet D d →
        g * t * g⁻¹ ∈ rootSet D t →
        ∀ t' ∈ D, t' ∈ rootGroup D d ⊔ rootGroup D a → t' ∉ rootSet D d →
          g * t' * g⁻¹ ∈ rootSet D t' → t' ∈ rootSet D t := by
  classical
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have : Fact (orderOf g).Prime := ⟨hp⟩
  have hLS : LineSetting G D := ⟨h, hc, hs, hconn, ⟨d, hd, a, ha, hda, hdaD, haT,
    hAll d hd a ha hda hdaD haT⟩⟩
  have hNP : Moufang.NoPolar D :=
    noPolar_of_lineTI h hc hs hconn hd ha hda hdaD haT (hAll d hd a ha hda hdaD haT)
  obtain ⟨k, hk⟩ := exists_card_rootGroup_eq_two_pow hD hd
  have hpq : ¬ orderOf g ∣ Nat.card (rootGroup D d) := by
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hgA : (rootGroup D d).map (MulAut.conj g).toMonoidHom = rootGroup D d := by
    rw [← rootGroup_conj hclass, rootGroup_eq_of_mem hgd]
  have hgLm : (rootGroup D d ⊔ rootGroup D a).map (MulAut.conj g).toMonoidHom =
      rootGroup D d ⊔ rootGroup D a := map_conj_eq_of_forall hgL
  have hfix : ∀ {t : G}, t ∈ D → g * t * g⁻¹ ∈ rootSet D t →
      (rootGroup D t).map (MulAut.conj g).toMonoidHom = rootGroup D t := fun ht hgt => by
    rw [← rootGroup_conj hclass, rootGroup_eq_of_mem hgt]
  refine ⟨?_, fun t ht htL htT hgt t' ht' ht'L ht'T hgt' => ?_⟩
  ·
    have hP : IsPGroup (orderOf g) (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one])
    obtain ⟨P, ⟨hPL, hPd⟩, hPfix⟩ := exists_map_conj_eq_of_isPGroup hP
      (S := linePoints D (rootGroup D d ⊔ rootGroup D a) \ {rootGroup D d})
      (fun g' hg' H hH => by
        obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hg'
        obtain ⟨hHL, hHd⟩ := hH
        refine ⟨?_, fun h' => hHd ?_⟩
        · have := map_conj_mem_linePoints hclass hHL (g ^ j)
          rwa [map_conj_pow_eq hgLm j] at this
        · rw [Set.mem_singleton_iff] at h' ⊢
          exact Subgroup.map_injective (f := (MulAut.conj (g ^ j)).toMonoidHom)
            (MulAut.conj (g ^ j)).injective (h'.trans (map_conj_pow_eq hgA j).symm))
      (by
        rw [ncard_linePoints_diff h hc hs hd ha hda hdaD haT]
        exact hpq)
    obtain ⟨t, ht, htL, rfl⟩ := hPL
    have htT : t ∉ rootSet D d := fun h' => hPd (by
      rw [Set.mem_singleton_iff, rootGroup_eq_of_mem h'])
    have hgtA : g * t * g⁻¹ ∈ rootGroup D t := by
      rw [← hPfix g (Subgroup.mem_zpowers g)]
      exact ⟨t, rootSet_subset_rootGroup D t (mem_rootSet_self ht), rfl⟩
    exact ⟨t, ht, htL, htT, mem_rootSet_of_mem_rootGroup hclass ht (conj_mem_of_isClass hclass g ht)
      hgtA⟩
  ·
    by_contra hne
    have hta : t ∉ rootGroup D d := fun h' => htT (mem_rootSet_of_mem_rootGroup hclass hd ht h')
    have ht'a : t' ∉ rootGroup D d := fun h' =>
      ht'T (mem_rootSet_of_mem_rootGroup hclass hd ht' h')
    obtain ⟨m, hm, hmt⟩ := hLS.exists_conj_mem_rootSet hd ha hda hdaD haT he hde hdeD heL
      ht'L ht'a htL hta
    rcases hm with rfl | hmT
    · apply hne
      have : t ∈ rootSet D t' := by simpa using hmt
      exact mem_rootSet_comm ht' this
    have hmN : m ∈ rootGroup D d ⊔ rootGroup D e :=
      Subgroup.mem_sup_right (rootSet_subset_rootGroup D e hmT)
    have hgmN : g * m * g⁻¹ ∈ rootGroup D d ⊔ rootGroup D e := hgN m hmN
    have hzN : m⁻¹ * (g * m * g⁻¹) ∈ rootGroup D d ⊔ rootGroup D e :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) hgmN
    have hgt₀ := hfix ht hgt
    have hgt'₀ := hfix ht' hgt'
    have hmt₀ : (rootGroup D t).map (MulAut.conj m).toMonoidHom = rootGroup D t' := by
      rw [← rootGroup_conj hclass, rootGroup_eq_of_mem hmt]
    have hzt₀ : (rootGroup D t).map (MulAut.conj (m⁻¹ * (g * m * g⁻¹))).toMonoidHom =
        rootGroup D t := by
      have hginv : (rootGroup D t).map (MulAut.conj g⁻¹).toMonoidHom = rootGroup D t := by
        conv_lhs => rw [← hgt₀]
        exact map_conj_inv_map_conj_eq g _
      have hminv : (rootGroup D t').map (MulAut.conj m⁻¹).toMonoidHom = rootGroup D t := by
        rw [← hmt₀]
        exact map_conj_inv_map_conj_eq m _
      rw [show m⁻¹ * (g * m * g⁻¹) = m⁻¹ * g * m * g⁻¹ by group, map_conj_mul_eq_map_map,
        hginv, map_conj_mul_eq_map_map, hmt₀, map_conj_mul_eq_map_map, hgt'₀, hminv]
    have hztT : m⁻¹ * (g * m * g⁻¹) * t * (m⁻¹ * (g * m * g⁻¹))⁻¹ ∈ rootSet D t := by
      refine mem_rootSet_of_mem_rootGroup hclass ht (conj_mem_of_isClass hclass _ ht) ?_
      exact conj_mem_of_map_conj_eq hzt₀ (rootSet_subset_rootGroup D t (mem_rootSet_self ht))
    have hzA : m⁻¹ * (g * m * g⁻¹) ∈ rootGroup D d :=
      mem_rootGroup_of_conj_mem_rootSet h hc hs hconn hAll hd ha hda hdaD haT he hde hdeD heL
        hzN ht htL htT hztT
    have hm2 : m * m = 1 := hD.mul_self_eq_one hmT.1
    have hminv : m⁻¹ = m := hD.inv_eq hmT.1
    set S : Set G := {w | m * w ∈ (rootGroup D d : Set G)} with hSdef
    have hScard : Nat.card S = Nat.card (rootGroup D d) := by
      refine Nat.card_congr
        { toFun := fun w => ⟨m * w.1, w.2⟩
          invFun := fun β => ⟨m * β.1, ?_⟩
          left_inv := fun w => ?_
          right_inv := fun β => ?_ }
      · show m * (m * β.1) ∈ (rootGroup D d : Set G)
        rw [← mul_assoc, hm2, one_mul]
        exact β.2
      · apply Subtype.ext
        show m * (m * w.1) = w.1
        rw [← mul_assoc, hm2, one_mul]
      · apply Subtype.ext
        show m * (m * β.1) = β.1
        rw [← mul_assoc, hm2, one_mul]
    have hgdA : ∀ β ∈ rootGroup D d, g * β * g⁻¹ ∈ rootGroup D d := fun β hβ =>
      conj_mem_of_map_conj_eq hgA hβ
    obtain ⟨w, hwS, hw⟩ := exists_fixed_of_prime (S := S) (f := fun v => g * v * g⁻¹)
      (p := orderOf g)
      (fun v hv => by
        show m * (g * v * g⁻¹) ∈ rootGroup D d
        have e' : m * (g * v * g⁻¹) = m⁻¹ * (g * m * g⁻¹) * (g * (m * v) * g⁻¹) := by
          rw [hminv]
          calc m * (g * v * g⁻¹) = m * (g * ((m * m) * v) * g⁻¹) := by rw [hm2, one_mul]
            _ = m * (g * m * g⁻¹) * (g * (m * v) * g⁻¹) := by group
        rw [e']
        exact Subgroup.mul_mem _ hzA (hgdA _ hv))
      (fun v _ => by
        rw [conj_iterate, pow_orderOf_eq_one, one_mul, inv_one, mul_one])
      (by rwa [hScard])
    have hwA : m * w ∈ rootGroup D d := hwS
    have hwN : w ∈ rootGroup D d ⊔ rootGroup D e := by
      have : w = m * (m * w) := by rw [← mul_assoc, hm2, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ hmN (Subgroup.mem_sup_left hwA)
    have hw1 : w ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hwA
      have hmd : m ∈ rootSet D d := mem_rootSet_of_mem_rootGroup hclass hd hmT.1 hwA
      have heT' : e ∈ rootSet D d := by
        rw [← rootSet_eq_of_mem hmd, rootSet_eq_of_mem hmT]
        exact mem_rootSet_self he
      exact heL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D d heT'))
    have heT : e ∉ rootSet D d := fun h' =>
      heL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D d h'))
    have hwD : w ∈ D := mem_of_mem_sup_rootGroup h hc hs hd he hde hdeD heT hwN hw1
    have hcomm : Commute w g := by
      have : g * w = w * g := by
        calc g * w = g * w * g⁻¹ * g := by group
          _ = w * g := by rw [hw]
      exact this.symm
    have hg1 : g ≠ 1 := fun h' => by
      rw [h', orderOf_one] at hp
      exact Nat.not_prime_one hp
    exact false_of_commute_of_inv hD hclass hNP (hp.odd_of_ne_two hp2) hg1 hwD hy hcomm hyg

end CFSG.Timmesfeld.Bridge
