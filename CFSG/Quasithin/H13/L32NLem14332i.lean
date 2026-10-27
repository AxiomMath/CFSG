module

public import CFSG.Quasithin.EmptyFaithful.S146G1
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Quasithin.H13.L32NLem14332c
public import CFSG.Quasithin.H13.L32NLem14332f
public import CFSG.Quasithin.H13.L32NSet14

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14332

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem card_img_l32nH (hii : Case14323ii T V g D) : Nat.card ↥(D.img (l32nH T V)) = 120 := by
  obtain ⟨e⟩ := hii.iso
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

omit [Finite G] in
theorem not_isSolvable_l32nH (hii : Case14323ii T V g D) :
    ¬ Group.IsSolvable ↥(l32nH T V) := by
  intro hs
  obtain ⟨e⟩ := hii.iso
  have : Group.IsSolvable ↥(D.img (l32nH T V)) :=
    Group.isSolvable_of_surjective (imgHom_surjective D)
  exact Equiv.Perm.not_isSolvable_fin_5
    (Group.isSolvable_of_surjective (f := (e : ↥(D.img (l32nH T V)) →* Equiv.Perm (Fin 5)))
      e.surjective)

theorem exists_mem_cComp (hii : Case14323ii T V g D) : ∃ K, K ∈ cComp (l32nH T V) := by
  have hn : ((l32nH T V).subgroupOf (l32nH T V)).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable le_rfl hn (not_isSolvable_l32nH hii)
  exact ⟨K, hK⟩

section Image

variable {K : Subgroup G}

omit [Finite G] in
theorem imgHom_mem_kd (hKH : K ≤ l32nH T V) {k : G} (hk : k ∈ K) :
    imgHom D ⟨k, hKH hk⟩ ∈ (K.subgroupOf (l32nH T V)).map (imgHom D) :=
  ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

theorem isPGroup_ker (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) :
    ∀ h : ↥(l32nH T V), imgHom D h = 1 → ∃ n : ℕ, (h : G) ^ 2 ^ n = 1 := by
  intro h h1
  have hC : (h : G) ∈ l32nCHat T V := by
    have := congrArg Subtype.val h1
    rw [imgHom_apply] at this
    exact (rho_eq_one_iff_mem h.2 _).mp this
  rw [← hQ] at hC
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V)) ⟨_, hC⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem not_isSolvable_kd (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hK : K ∈ cComp (l32nH T V)) :
    ¬ Group.IsSolvable ↥((K.subgroupOf (l32nH T V)).map (imgHom D)) := by
  intro hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  set fK : ↥K →* ↥(D.img (l32nH T V)) := (imgHom D).comp (Subgroup.inclusion hKH) with hfK
  have hrange : fK.range = (K.subgroupOf (l32nH T V)).map (imgHom D) := by
    rw [hfK, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hs' : Group.IsSolvable ↥fK.range := by rw [hrange]; exact hs
  have hker : IsPGroup 2 ↥fK.ker := by
    rintro ⟨⟨k, hk⟩, hk1⟩
    obtain ⟨n, hn⟩ := isPGroup_ker hQ ⟨k, hKH hk⟩ hk1
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn))⟩
  have : Group.IsNilpotent ↥fK.ker := hker.isNilpotent
  exact not_isSolvable_of_mem_cComp hK
    (Group.isSolvable_of_ker_le_range fK.ker.subtype fK.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]))

omit [Finite G] in
theorem commutator_top_eq_top (hK : K ∈ cComp (l32nH T V)) :
    ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact perfect_of_mem_cComp hK

theorem card_kd (hii : Case14323ii T V g D) (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hK : K ∈ cComp (l32nH T V)) :
    Nat.card ↥((K.subgroupOf (l32nH T V)).map (imgHom D)) = 60 := by
  have := finite_linearEquiv D
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  have h120 := card_img_l32nH hii
  have hdvd : Nat.card ↥Kd ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card Kd
  have h60 : 60 ≤ Nat.card ↥Kd := by
    by_contra hlt
    push Not at hlt
    exact not_isSolvable_kd hQ hK (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt)
  have hne : Nat.card ↥Kd ≠ 120 := by
    intro h
    have htop : Kd = ⊤ := Subgroup.eq_top_of_card_eq Kd (by rw [h, h120])
    obtain ⟨e⟩ := hii.iso
    set s : ↥K →* ℤˣ := Equiv.Perm.sign.comp
      ((e : ↥(D.img (l32nH T V)) →* Equiv.Perm (Fin 5)).comp
        ((imgHom D).comp (Subgroup.inclusion hKH))) with hs
    have hbot : s.range = ⊥ := by
      rw [MonoidHom.range_eq_map, ← commutator_top_eq_top hK, Subgroup.map_commutator]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ =>
        Subgroup.mem_centralizer_iff.mpr fun y _ => mul_comm y x
    obtain ⟨σ, hσ⟩ := Equiv.Perm.sign_surjective (Fin 5) (-1)
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(D.img (l32nH T V)), e γ = σ := e.surjective σ
    have hγK : γ ∈ Kd := htop ▸ Subgroup.mem_top γ
    obtain ⟨⟨k, hkH⟩, hk, hkγ⟩ := hγK
    have hmem : s ⟨k, Subgroup.mem_subgroupOf.mp hk⟩ ∈ s.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have : s ⟨k, Subgroup.mem_subgroupOf.mp hk⟩ = -1 := by
      rw [hs, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
      have e1 : imgHom D (Subgroup.inclusion hKH ⟨k, Subgroup.mem_subgroupOf.mp hk⟩) = γ :=
        hkγ
      rw [e1]
      show Equiv.Perm.sign (e γ) = -1
      rw [hγ, hσ]
    rw [hmem] at this
    exact absurd this (by decide)
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  rcases m with _ | _ | m
  · omega
  · omega
  · have : Nat.card ↥Kd * 2 ≤ 120 := by nlinarith
    omega

theorem kd_eq_bot_of_isSolvable (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V))
    {N : Subgroup ↥(D.img (l32nH T V))} (hNK : N ≤ (K.subgroupOf (l32nH T V)).map (imgHom D))
    (hNn : (N.subgroupOf ((K.subgroupOf (l32nH T V)).map (imgHom D))).Normal)
    (hNs : Group.IsSolvable ↥N) : N = ⊥ := by
  have := finite_linearEquiv D
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  set N' := N.subgroupOf Kd with hN'
  have hc60 := card_kd hii hQ hK
  rw [← Subgroup.card_eq_one]
  by_contra h1
  have hpos : 0 < Nat.card ↥N := Nat.card_pos
  have hN'c : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  rw [hc60, hN'c] at hcard
  have hlt : Nat.card (↥Kd ⧸ N') < 60 := by
    have h2 : 2 ≤ Nat.card ↥N := by omega
    by_contra hge
    push Not at hge
    have : 60 * 2 ≤ Nat.card (↥Kd ⧸ N') * Nat.card ↥N := Nat.mul_le_mul hge h2
    omega
  have : Group.IsSolvable (↥Kd ⧸ N') := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
  have : Group.IsSolvable ↥N' :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNK).injective
  exact not_isSolvable_kd hQ hK (Group.isSolvable_of_subgroup_quotient N')

theorem card_centralizer_kd_le (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V)) :
    Nat.card ↥(Subgroup.centralizer
      (((K.subgroupOf (l32nH T V)).map (imgHom D) : Subgroup ↥(D.img (l32nH T V))) :
        Set ↥(D.img (l32nH T V)))) ≤ 2 := by
  have := finite_linearEquiv D
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  set C := Subgroup.centralizer (Kd : Set ↥(D.img (l32nH T V))) with hC
  have hKdC : Kd ≤ Subgroup.normalizer (C : Set ↥(D.img (l32nH T V))) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro c
    rw [hC, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have h1 := h (k⁻¹ * y * k) (Kd.mul_mem (Kd.mul_mem (Kd.inv_mem hk) hy) hk)
      calc y * (k * c * k⁻¹) = k * ((k⁻¹ * y * k) * c) * k⁻¹ := by group
        _ = k * (c * (k⁻¹ * y * k)) * k⁻¹ := by rw [h1]
        _ = k * c * k⁻¹ * y := by group
    · intro h y hy
      have h1 := h (k * y * k⁻¹) (Kd.mul_mem (Kd.mul_mem hk hy) (Kd.inv_mem hk))
      calc y * c = k⁻¹ * ((k * y * k⁻¹) * (k * c * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * c * k⁻¹) * (k * y * k⁻¹)) * k := by rw [h1]
        _ = c * y := by group
  have hbot : C ⊓ Kd = ⊥ := by
    have hle : C ⊓ Kd ≤ Kd := inf_le_right
    refine kd_eq_bot_of_isSolvable hii hQ hK hle ?_ ?_
    · constructor
      intro n hn k
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnC, hnK⟩ := Subgroup.mem_inf.mp hn
      refine Subgroup.mem_inf.mpr ⟨?_, Kd.mul_mem (Kd.mul_mem k.2 hnK) (Kd.inv_mem k.2)⟩
      have := (Subgroup.mem_normalizer_iff.mp (hKdC k.2) n).mp hnC
      simpa using this
    · refine Group.isSolvable_of_comm fun x y => Subtype.ext ?_
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).1 y
        (Subgroup.mem_inf.mp y.2).2).symm
  have h := L32NSet14.card_sup_mul_card_inf hKdC
  rw [inf_comm, hbot, Subgroup.card_bot, mul_one, card_kd hii hQ hK] at h
  have hle : Nat.card ↥(Kd ⊔ C) ≤ 120 :=
    card_img_l32nH hii ▸ Subgroup.card_le_card_group (Kd ⊔ C)
  omega

theorem index_kd (hii : Case14323ii T V g D) (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hK : K ∈ cComp (l32nH T V)) : ((K.subgroupOf (l32nH T V)).map (imgHom D)).index = 2 := by
  have := finite_linearEquiv D
  have h := Subgroup.card_mul_index ((K.subgroupOf (l32nH T V)).map (imgHom D))
  rw [card_kd hii hQ hK, card_img_l32nH hii] at h
  omega

omit [Finite G] in
theorem exists_mem_of_imgHom_mem {h : G} (hh : h ∈ l32nH T V)
    (hK : imgHom D ⟨h, hh⟩ ∈ (K.subgroupOf (l32nH T V)).map (imgHom D)) :
    ∃ k ∈ K, h * k⁻¹ ∈ l32nCHat T V := by
  obtain ⟨⟨k, hkH⟩, hk, hkh⟩ := hK
  refine ⟨k, Subgroup.mem_subgroupOf.mp hk, ?_⟩
  have h1 : imgHom D (⟨h, hh⟩ * (⟨k, hkH⟩ : ↥(l32nH T V))⁻¹) = 1 := by
    rw [map_mul, map_inv, hkh, mul_inv_cancel]
  have h2 := congrArg Subtype.val h1
  rw [imgHom_apply] at h2
  exact (rho_eq_one_iff_mem (Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hkH)) _).mp h2

theorem le_normalizer_cComp (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hK : K ∈ cComp (l32nH T V)) :
    l32nH T V ≤ Subgroup.normalizer (K : Set G) := by
  have := finite_linearEquiv D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  set Q := pCoreOf 2 (l32nH T V) with hQdef
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  have hKdn : Kd.Normal := Subgroup.normal_of_index_eq_two (index_kd hii hQ hK)
  have hQs : Group.IsSolvable ↥Q := by
    have : Group.IsNilpotent ↥Q :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V)).isNilpotent
    infer_instance
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (l32nH T V))
  obtain ⟨-, hperf⟩ := cComp_commutator_perfectCore hK
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (l32nH T V)) hQs hKQ
  have hQH : Q ≤ l32nH T V := CFSG.LieType.BorelTits.pCoreOf_le 2 (l32nH T V)
  set P : Subgroup G := (Kd.comap (imgHom D)).map (l32nH T V).subtype with hP
  have hPn : (Kd.comap (imgHom D)).Normal := hKdn.comap _
  have hKQP : K ⊔ Q = P := by
    apply le_antisymm
    · refine sup_le (fun k hk => ⟨⟨k, hKH hk⟩, imgHom_mem_kd hKH hk, rfl⟩)
        (fun q hq => ⟨⟨q, hQH hq⟩, ?_, rfl⟩)
      show imgHom D ⟨q, hQH hq⟩ ∈ Kd
      have h1 : imgHom D ⟨q, hQH hq⟩ = 1 := Subtype.ext (by
        rw [imgHom_apply]
        exact (rho_eq_one_iff_mem (hQH hq) _).mpr (hQ ▸ hq))
      rw [h1]
      exact Kd.one_mem
    · rintro _ ⟨⟨y, hyH⟩, hy, rfl⟩
      obtain ⟨k, hk, hyk⟩ := exists_mem_of_imgHom_mem hyH hy
      show y ∈ K ⊔ Q
      have e : y = (y * k⁻¹) * k := by group
      rw [e]
      exact (K ⊔ Q).mul_mem (Subgroup.mem_sup_right (hQ ▸ hyk)) (Subgroup.mem_sup_left hk)
  have hHP : l32nH T V ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ x ∈ l32nH T V, ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
      rintro x hx _ ⟨y, hy, rfl⟩
      exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, hPn.conj_mem y hy ⟨x, hx⟩, rfl⟩
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key h hh y, fun hy => ?_⟩
    have := key h⁻¹ (inv_mem hh) _ hy
    simpa [mul_assoc] using this
  have := hHP.trans (normalizer_le_normalizer_perfectCore P)
  rwa [← hKQP, hperf] at this

theorem eq_sup_T (C : Ctx14332 G T L V V₂ g a D) (hii : Case14323ii T V g D)
    (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V) (hQT : pCoreOf 2 (l32nH T V) ≤ T)
    (hK : K ∈ cComp (l32nH T V)) : l32nH T V = K ⊔ T := by
  have := finite_linearEquiv D
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hTH : T ≤ l32nH T V := C.T_le.trans inf_le_left
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  obtain ⟨t, htT, ht⟩ : ∃ t, ∃ htT : t ∈ T, imgHom D ⟨t, hTH htT⟩ ∉ Kd := by
    by_contra hall
    push Not at hall
    set Td := (D.img T).subgroupOf (D.img (l32nH T V)) with hTd
    have hTdK : Td ≤ Kd := by
      intro γ hγ
      obtain ⟨t, ht, htN, hγt⟩ := (L128A.HatU.mem_img D).mp (Subgroup.mem_subgroupOf.mp hγ)
      have e : γ = imgHom D ⟨t, hTH ht⟩ := Subtype.ext (by rw [imgHom_apply]; exact hγt.symm)
      rw [e]
      exact hall t ht
    have hTle : D.img T ≤ D.img (l32nH T V) := by
      intro γ hγ
      obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
      exact L128A.HatU.rho_mem_img D (hTH hy) hyN
    have hTc : Nat.card ↥Td = Nat.card ↥(D.img T) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv
    obtain ⟨n, hn⟩ := (isPGroup_img_T C).exists_card_eq
    obtain ⟨j, hj⟩ : Odd Td.index := C.T_odd
    have h := Subgroup.card_mul_index Td
    rw [card_img_l32nH hii, hTc, hn, hj] at h
    have hn7 : n < 7 := by
      by_contra hge
      push Not at hge
      have h1 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      have h2 : 2 ^ n ≤ 2 ^ n * (2 * j + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hn3 : n = 3 := by interval_cases n <;> omega
    have hdvd := Subgroup.card_dvd_of_le hTdK
    rw [hTc, hn, hn3, card_kd hii hQ hK] at hdvd
    norm_num at hdvd
  apply le_antisymm _ (sup_le hKH hTH)
  intro h hh
  by_cases hhK : imgHom D ⟨h, hh⟩ ∈ Kd
  · obtain ⟨k, hk, hhk⟩ := exists_mem_of_imgHom_mem hh hhK
    have e : h = (h * k⁻¹) * k := by group
    rw [e]
    exact (K ⊔ T).mul_mem (Subgroup.mem_sup_right (hQT (hQ ▸ hhk))) (Subgroup.mem_sup_left hk)
  · have hidx := index_kd hii hQ hK
    have hhtH : h * t⁻¹ ∈ l32nH T V := mul_mem hh (inv_mem (hTH htT))
    have hht : imgHom D ⟨h * t⁻¹, hhtH⟩ ∈ Kd := by
      rw [show (⟨h * t⁻¹, hhtH⟩ : ↥(l32nH T V)) = ⟨h, hh⟩ * (⟨t, hTH htT⟩)⁻¹ from rfl, map_mul,
        map_inv]
      exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        (iff_of_false hhK fun hm => ht (by simpa using Kd.inv_mem hm))
    obtain ⟨k, hk, hhk⟩ := exists_mem_of_imgHom_mem hhtH hht
    have e : h = (h * t⁻¹ * k⁻¹) * k * t := by group
    rw [e]
    exact (K ⊔ T).mul_mem ((K ⊔ T).mul_mem (Subgroup.mem_sup_right (hQT (hQ ▸ hhk)))
      (Subgroup.mem_sup_left hk)) (Subgroup.mem_sup_right htT)

theorem mem_cComp_of_odd (hii : Case14323ii T V g D) (hQ : pCoreOf 2 (l32nH T V) = l32nCHat T V)
    (hK : K ∈ cComp (l32nH T V)) {y : G} (hy : y ∈ l32nH T V) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) : y ∈ K := by
  have := finite_linearEquiv D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  set Kd := (K.subgroupOf (l32nH T V)).map (imgHom D) with hKd
  have hidx := index_kd hii hQ hK
  have hy1 : (⟨y, hy⟩ : ↥(l32nH T V)) ^ m = 1 := Subtype.ext (by simpa using hym)
  have hyK : imgHom D ⟨y, hy⟩ ∈ Kd := by
    by_contra hyK
    obtain ⟨j, rfl⟩ := hm
    have h2 : (imgHom D ⟨y, hy⟩) ^ 2 ∈ Kd := Subgroup.sq_mem_of_index_two hidx _
    have h1 : (imgHom D ⟨y, hy⟩) ^ (2 * j + 1) ∈ Kd := by
      rw [← map_pow, hy1, map_one]
      exact Kd.one_mem
    rw [pow_succ, pow_mul] at h1
    exact hyK (by simpa using Kd.mul_mem (Kd.inv_mem (Kd.pow_mem h2 j)) h1)
  obtain ⟨k, hk, hyk⟩ := exists_mem_of_imgHom_mem hy hyK
  have hN : (K.subgroupOf (l32nH T V)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_cComp hii hQ hK)
  set π := QuotientGroup.mk' (K.subgroupOf (l32nH T V)) with hπ
  have hyq : π ⟨y, hy⟩ = π ⟨y * k⁻¹, mul_mem hy (inv_mem (hKH hk))⟩ := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show y⁻¹ * (y * k⁻¹) ∈ K
    rw [inv_mul_cancel_left]
    exact inv_mem hk
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V)) ⟨_, hQ ▸ hyk⟩
  have hq1 : (⟨y * k⁻¹, mul_mem hy (inv_mem (hKH hk))⟩ : ↥(l32nH T V)) ^ 2 ^ n = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hn)
  have ho : orderOf (π ⟨y, hy⟩) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n hm.coprime_two_right)
      (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_of_pow_eq_one ?_)
    · rw [← map_pow, hy1, map_one]
    · rw [hyq, ← map_pow, hq1, map_one]
  have h1 := orderOf_eq_one_iff.mp ho
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end Image

end L14332

end CFSG.Quasithin.H13
