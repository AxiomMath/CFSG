module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

private theorem sec31_mul_self_eq_one {T : Subgroup G} (hT : IsElemAbelian 2 T) {t : G}
    (ht : t ∈ T) : t * t = 1 := by
  rw [← pow_two]
  exact hT.2 t ht

private theorem sec31_isElemAbelian_subgroupOf {p : ℕ} {T H : Subgroup G}
    (hT : IsElemAbelian p T) : IsElemAbelian p (T.subgroupOf H) := by
  obtain ⟨hc, h2⟩ := hT
  have hcomm : ∀ a b : ↥(T.subgroupOf H), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have h := hc.is_comm.comm ⟨a.1.1, Subgroup.mem_subgroupOf.mp a.2⟩
      ⟨b.1.1, Subgroup.mem_subgroupOf.mp b.2⟩
    exact congrArg (fun z : ↥T => (z : G)) h
  refine ⟨⟨⟨hcomm⟩⟩, fun x hx => Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  exact h2 _ (Subgroup.mem_subgroupOf.mp hx)

private theorem sec31_isPGroup_subgroupOf {S H : Subgroup G} (hS : IsPGroup 2 S) :
    IsPGroup 2 ↥(S.subgroupOf H) := by
  intro g
  obtain ⟨n, hn⟩ := hS ⟨g.1.1, Subgroup.mem_subgroupOf.mp g.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg (fun z : S => (z : G)) hn
  simpa using h1

private theorem sec31_isTI_subgroupOf [Finite G] {T H : Subgroup G} (hT : IsTI T) :
    IsTI (T.subgroupOf H) := by
  intro g
  by_cases hne : T.subgroupOf H ⊓ conjSubgroup g (T.subgroupOf H) = ⊥
  · exact Or.inl hne
  · right
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hzK, hzQ⟩ := Subgroup.mem_inf.mp z.2
    have hzT : ((z : ↥H) : G) ∈ T := Subgroup.mem_subgroupOf.mp hzK
    have hzQ' : ((g⁻¹ * (z : ↥H) * g : ↥H) : G) ∈ T :=
      Subgroup.mem_subgroupOf.mp (mem_conjSubgroup.mp hzQ)
    have hz0 : ((z : ↥H) : G) ≠ 1 := fun e => hz (Subtype.ext (Subtype.ext e))
    have hne0 : T ⊓ conjSubgroup (g : G) T ≠ ⊥ := by
      intro h0
      have hm : ((z : ↥H) : G) ∈ T ⊓ conjSubgroup (g : G) T :=
        Subgroup.mem_inf.mpr ⟨hzT, mem_conjSubgroup.mpr (by simpa using hzQ')⟩
      rw [h0, Subgroup.mem_bot] at hm
      exact hz0 hm
    have hgN : (g : G) ∈ normalizer (T : Set G) :=
      conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI hT hne0)
    have hginv : (g : G)⁻¹ ∈ normalizer (T : Set G) := inv_mem hgN
    have hle : T.subgroupOf H ≤ conjSubgroup g (T.subgroupOf H) := by
      intro w hw
      rw [mem_conjSubgroup, Subgroup.mem_subgroupOf]
      have hw' : (w : G) ∈ T := Subgroup.mem_subgroupOf.mp hw
      have hconj := (Subgroup.mem_normalizer_iff.mp hginv (w : G)).mp hw'
      simpa [mul_assoc] using hconj
    exact inf_eq_left.mpr hle

private theorem sec31_comm_conj_inf [Finite G] {T H P : Subgroup G} {x s : G}
    (hT : IsElemAbelian 2 T) (hTI : IsTI T) (hP : IsPGroup 2 P) (hPle : T ⊓ H ≤ P)
    (hsP : s ∈ P) (hsH : s ∈ H) (hxT : x ∈ T) (hxH : x ∈ H) (hx1 : x ≠ 1)
    (hx2 : x * x = 1) (hxs : x * s * x⁻¹ = s⁻¹) (hs4 : s ^ 4 = 1) :
    ∀ a ∈ T ⊓ H, ∀ c ∈ conjSubgroup s (T ⊓ H), a * c = c * a := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxs' : x * s⁻¹ * x⁻¹ = s := by
    rw [show x * s⁻¹ * x⁻¹ = (x * s * x⁻¹)⁻¹ by group, hxs, inv_inv]
  have hss : (s * s) * (s * s) = 1 := by
    calc (s * s) * (s * s) = s ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := hs4
  have hinv2 : s⁻¹ * s⁻¹ = s * s := by
    rw [← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right hss
  have hy_mem : s * x * s⁻¹ ∈ conjSubgroup s T := by
    rw [mem_conjSubgroup, show s⁻¹ * (s * x * s⁻¹) * s = x by group]
    exact hxT
  have hy_ne : s * x * s⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  have hxy : x * (s * x * s⁻¹) = (s * x * s⁻¹) * x := by
    calc x * (s * x * s⁻¹) = (x * s * x⁻¹) * s⁻¹ := by rw [hxinv]; group
      _ = s⁻¹ * s⁻¹ := by rw [hxs]
      _ = s * s := hinv2
      _ = s * (x * s⁻¹ * x⁻¹) := by rw [hxs']
      _ = (s * x * s⁻¹) * x := by rw [hxinv]; group
  have hxyx : x * (s * x * s⁻¹) * x = s * x * s⁻¹ := by
    calc x * (s * x * s⁻¹) * x = ((s * x * s⁻¹) * x) * x := by rw [hxy]
      _ = (s * x * s⁻¹) * (x * x) := by group
      _ = s * x * s⁻¹ := by rw [hx2, mul_one]
  have hT' : IsTI (conjSubgroup s T) := isTI_conjSubgroup hTI s
  have hxN' : conjSubgroup x (conjSubgroup s T) = conjSubgroup s T := by
    apply conjSubgroup_eq_of_isTI hT'
    intro h0
    have hm : s * x * s⁻¹ ∈ conjSubgroup s T ⊓ conjSubgroup x (conjSubgroup s T) := by
      refine Subgroup.mem_inf.mpr ⟨hy_mem, ?_⟩
      rw [mem_conjSubgroup, hxinv, hxyx]
      exact hy_mem
    rw [h0] at hm
    exact hy_ne (Subgroup.mem_bot.mp hm)
  have hxN : x ∈ normalizer (conjSubgroup s T : Set G) := conjSubgroup_eq_self_iff.mp hxN'
  have hK_el : IsElemAbelian 2 (T.subgroupOf H) := sec31_isElemAbelian_subgroupOf hT
  have hK_TI : IsTI (T.subgroupOf H) := sec31_isTI_subgroupOf hTI
  have hQ_iff : ∀ n : ↥H, n ∈ conjSubgroup (⟨s, hsH⟩ : ↥H) (T.subgroupOf H) ↔
      (n : G) ∈ conjSubgroup s T := by
    intro n
    rw [mem_conjSubgroup, mem_conjSubgroup]
    exact Subgroup.mem_subgroupOf
  have hPW : IsPGroup 2 ↥(conjSubgroup (1 : ↥H) (T.subgroupOf H) ⊔
      conjSubgroup (⟨s, hsH⟩ : ↥H) (T.subgroupOf H)) := by
    refine IsPGroup.to_le (sec31_isPGroup_subgroupOf (H := H) hP) (sup_le ?_ ?_)
    · rw [conjSubgroup_one]
      intro u hu
      exact Subgroup.mem_subgroupOf.mpr
        (hPle (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hu, u.2⟩))
    · intro w hw
      have hP' : ((((⟨s, hsH⟩ : ↥H)⁻¹ * w * (⟨s, hsH⟩ : ↥H) : ↥H)) : G) ∈ P :=
        hPle (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (mem_conjSubgroup.mp hw),
          (((⟨s, hsH⟩ : ↥H)⁻¹ * w * (⟨s, hsH⟩ : ↥H) : ↥H)).2⟩)
      refine Subgroup.mem_subgroupOf.mpr ?_
      have e : (w : G) = s * ((((⟨s, hsH⟩ : ↥H)⁻¹ * w * (⟨s, hsH⟩ : ↥H) : ↥H)) : G) * s⁻¹ := by
        show (w : G) = s * (s⁻¹ * (w : G) * s) * s⁻¹
        group
      rw [e]
      exact mul_mem (mul_mem hsP hP') (inv_mem hsP)
  have hx'K : (⟨x, hxH⟩ : ↥H) ∈ T.subgroupOf H := Subgroup.mem_subgroupOf.mpr hxT
  have hx'Q : (⟨x, hxH⟩ : ↥H) ∈
      normalizer ((conjSubgroup (⟨s, hsH⟩ : ↥H) (T.subgroupOf H) : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    rw [hQ_iff, hQ_iff]
    exact Subgroup.mem_normalizer_iff.mp hxN (n : G)
  have hNW : normalizerIn (conjSubgroup (1 : ↥H) (T.subgroupOf H))
      (conjSubgroup (⟨s, hsH⟩ : ↥H) (T.subgroupOf H)) ≠ ⊥ := by
    rw [conjSubgroup_one]
    intro h0
    have hm : (⟨x, hxH⟩ : ↥H) ∈
        normalizerIn (T.subgroupOf H) (conjSubgroup (⟨s, hsH⟩ : ↥H) (T.subgroupOf H)) :=
      Subgroup.mem_inf.mpr ⟨hx'K, hx'Q⟩
    rw [h0, Subgroup.mem_bot] at hm
    exact hx1 (congrArg Subtype.val hm)
  have hcomm := commute_of_isPGroup hK_el hK_TI hPW hNW
  intro a ha c hc
  have hcH : c ∈ H := by
    have hk : s * (s⁻¹ * c * s) * s⁻¹ ∈ H :=
      mul_mem (mul_mem hsH (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hc)).2) (inv_mem hsH)
    rwa [show s * (s⁻¹ * c * s) * s⁻¹ = c by group] at hk
  have ha' : (⟨a, (Subgroup.mem_inf.mp ha).2⟩ : ↥H) ∈
      conjSubgroup (1 : ↥H) (T.subgroupOf H) := by
    rw [conjSubgroup_one]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp ha).1
  have hc' : (⟨c, hcH⟩ : ↥H) ∈ conjSubgroup (⟨s, hsH⟩ : ↥H) (T.subgroupOf H) := by
    rw [hQ_iff]
    exact mem_conjSubgroup.mpr (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hc)).1
  exact congrArg Subtype.val (hcomm _ ha' _ hc')

theorem tim77Sec31_holds : Tim77Sec31Statement := by
  intro G _ _ A Abar S₀ B h x hx hx1 b hb _ hn2 hn4
  have hAbel : IsElemAbelian 2 Abar := h.setup.elem_Ab
  have hAbTI : IsTI Abar := h.setup.ti_Ab
  obtain ⟨gB, hgB⟩ := h.nota.conj
  have hBel : IsElemAbelian 2 B := by
    rw [hgB]
    exact isElemAbelian_conj h.hyp.elemAbelian gB
  have hb2 : b * b = 1 := sec31_mul_self_eq_one hBel hb
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbS : b ∈ S₀ := h.b_le_s0 hb
  have hbC : b ∈ centralizer (A : Set G) := h.b_le_centralizer hb
  have hxS : x ∈ S₀ := h.abar0_le_s0 hx
  have hAbar0 : ∀ y ∈ Section3.Abar0 A Abar, y ∈ Abar ∧ y ∈ normalizer (A : Set G) := by
    intro y hy
    rw [Sec3Ctx.abar0_eq h] at hy
    exact Subgroup.mem_inf.mp hy
  have hxAbar : x ∈ Abar := (hAbar0 x hx).1
  have hxN : x ∈ normalizer (A : Set G) := (hAbar0 x hx).2
  have hx2 : x * x = 1 := sec31_mul_self_eq_one hAbel hxAbar
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxbS : x * b ∈ S₀ := mul_mem hxS hbS
  obtain ⟨k, hk⟩ := h.isPGroup_s0 ⟨x * b, hxbS⟩
  have hk' : (x * b) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  have hord1 : orderOf (x * b) ≠ 1 := by
    intro h1
    have hxb1 : x * b = 1 := orderOf_eq_one_iff.mp h1
    have hxb : x = b := by
      calc x = x * b * b := by rw [mul_assoc, hb2, mul_one]
        _ = b := by rw [hxb1, one_mul]
    have hxC : x ∈ centralizer (A : Set G) := by
      rw [hxb]
      exact hbC
    have hAN : A ≤ normalizer (Abar : Set G) := by
      intro a ha
      have hcomm : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a ha
      have hconj : x ∈ conjSubgroup a Abar := by
        rw [mem_conjSubgroup]
        have e : a⁻¹ * x * a = x := by
          calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
            _ = a⁻¹ * (a * x) := by rw [hcomm]
            _ = x := by group
        rw [e]
        exact hxAbar
      have hne : Abar ⊓ conjSubgroup a Abar ≠ ⊥ := by
        intro h0
        have hm : x ∈ Abar ⊓ conjSubgroup a Abar := Subgroup.mem_inf.mpr ⟨hxAbar, hconj⟩
        rw [h0, Subgroup.mem_bot] at hm
        exact hx1 hm
      exact conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI hAbTI hne)
    apply h.a0_ne
    rw [Sec3Ctx.a0_eq h]
    exact inf_eq_left.mpr hAN
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := by
    rcases Nat.lt_or_ge i 3 with hlt | hge
    · interval_cases i
      · exact absurd (show orderOf (x * b) = 1 by simpa using hi) hord1
      · exact absurd (show orderOf (x * b) = 2 by simpa using hi) hn2
      · exact absurd (show orderOf (x * b) = 4 by simpa using hi) hn4
    · exact ⟨i - 3, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : G, s = (x * b) ^ 2 ^ (j + 1) := ⟨_, rfl⟩
  have hords : orderOf s = 4 := by
    have hdvd : 2 ^ (j + 1) ∣ orderOf (x * b) := by
      rw [hi]
      exact pow_dvd_pow 2 (by omega)
    rw [hs, orderOf_pow_of_dvd (by positivity) hdvd, hi,
      show (2 : ℕ) ^ (j + 3) = 4 * 2 ^ (j + 1) by ring]
    exact Nat.mul_div_cancel 4 (by positivity)
  have hs4 : s ^ 4 = 1 := by
    rw [← hords]
    exact pow_orderOf_eq_one s
  have hs_S : s ∈ S₀ := by
    rw [hs]
    exact pow_mem hxbS _
  have hs_cl : s ∈ Subgroup.closure ({x, b} : Set G) := by
    rw [hs]
    exact pow_mem (mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) _
  have hsH : s ∈ normalizer (A : Set G) := h.s0_le_normalizer hs_S
  have hxbx : x * b * x⁻¹ ∈ centralizer (A : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hxN) b).mp hbC
  have hxb2C : (x * b) ^ 2 ∈ centralizer (A : Set G) := by
    have e : (x * b) ^ 2 = (x * b * x⁻¹) * b := by
      rw [hxinv, pow_two]
      group
    rw [e]
    exact mul_mem hxbx hbC
  have hs_C : s ∈ centralizer (A : Set G) := by
    have e : s = ((x * b) ^ 2) ^ 2 ^ j := by
      rw [hs, ← pow_mul]
      congr 1
      ring
    rw [e]
    exact pow_mem hxb2C _
  have hxsx : x * s * x⁻¹ = s⁻¹ := by
    have e1 : x * (x * b) * x⁻¹ = (x * b)⁻¹ := by
      calc x * (x * b) * x⁻¹ = (x * x) * b * x⁻¹ := by group
        _ = b * x⁻¹ := by rw [hx2, one_mul]
        _ = (x * b)⁻¹ := by rw [mul_inv_rev, hbinv, hxinv]
    rw [hs, ← conj_pow, e1, inv_pow]
  have hxs' : x * s⁻¹ * x⁻¹ = s := by
    rw [show x * s⁻¹ * x⁻¹ = (x * s * x⁻¹)⁻¹ by group, hxsx, inv_inv]
  have hxs2 : x * (s⁻¹ * x * s) = s * s := by
    calc x * (s⁻¹ * x * s) = (x * s⁻¹ * x⁻¹) * s := by rw [hxinv]; group
      _ = s * s := by rw [hxs']
  have hbsb : b * s * b⁻¹ = s⁻¹ := by
    have e3 : b * (x * b) * b⁻¹ = (x * b)⁻¹ := by
      calc b * (x * b) * b⁻¹ = b * x := by group
        _ = (x * b)⁻¹ := by rw [mul_inv_rev, hbinv, hxinv]
    rw [hs, ← conj_pow, e3, inv_pow]
  have hsq : s ^ 2 * s ^ 2 = 1 := by
    rw [← pow_add]
    exact hs4
  have hsqinv : (s ^ 2)⁻¹ = s ^ 2 := inv_eq_of_mul_eq_one_right hsq
  have hbs2 : b * s ^ 2 * b⁻¹ = s ^ 2 := by
    calc b * s ^ 2 * b⁻¹ = (b * s * b⁻¹) * (b * s * b⁻¹) := by rw [pow_two]; group
      _ = s⁻¹ * s⁻¹ := by rw [hbsb]
      _ = (s ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      _ = s ^ 2 := hsqinv
  have hne1 : s ^ 2 ≠ 1 := by
    intro h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hords] at hd
    norm_num at hd
  have hne_conj : Section3.Abar0 A Abar ≠ conjSubgroup s (Section3.Abar0 A Abar) := by
    intro heq
    have hxmem : x ∈ conjSubgroup s (Section3.Abar0 A Abar) := by
      rw [← heq]
      exact hx
    have hx'mem : s⁻¹ * x * s ∈ Section3.Abar0 A Abar := mem_conjSubgroup.mp hxmem
    have hs2Abar : s ^ 2 ∈ Abar := by
      rw [pow_two, ← hxs2]
      exact mul_mem hxAbar (hAbar0 _ hx'mem).1
    have hconjb : conjSubgroup b⁻¹ Abar = Abar := by
      apply conjSubgroup_eq_of_isTI hAbTI
      intro h0
      have hm : s ^ 2 ∈ Abar ⊓ conjSubgroup b⁻¹ Abar := by
        refine Subgroup.mem_inf.mpr ⟨hs2Abar, mem_conjSubgroup.mpr ?_⟩
        rw [inv_inv, hbs2]
        exact hs2Abar
      rw [h0, Subgroup.mem_bot] at hm
      exact hne1 hm
    have hxconj : x ∈ conjSubgroup b⁻¹ Abar := by
      rw [hconjb]
      exact hxAbar
    have hbxb : b * x * b⁻¹ ∈ Abar := by
      have hh := mem_conjSubgroup.mp hxconj
      rwa [inv_inv] at hh
    have hxbsq : (x * b) ^ 2 ∈ Abar := by
      have e : (x * b) ^ 2 = x * (b * x * b⁻¹) := by
        rw [hbinv, pow_two]
        group
      rw [e]
      exact mul_mem hxAbar hbxb
    have h4' : (x * b) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
      exact sec31_mul_self_eq_one hAbel hxbsq
    have hd : orderOf (x * b) ∣ 4 := orderOf_dvd_of_pow_eq_one h4'
    rw [hi] at hd
    have hle : 2 ^ (j + 3) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    have h8 : 2 ^ 3 ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h84 : 2 ^ 3 ≤ 4 := le_trans h8 hle
    norm_num at h84
  have hPle : Abar ⊓ normalizer (A : Set G) ≤ S₀ := by
    rw [← Sec3Ctx.abar0_eq h]
    exact h.abar0_le_s0
  refine ⟨s, hs_cl, hs_S, hs_C, hne_conj, ?_, hords⟩
  rw [Sec3Ctx.abar0_eq h]
  exact sec31_comm_conj_inf hAbel hAbTI h.isPGroup_s0 hPle hs_S hsH hxAbar hxN hx1 hx2 hxsx hs4

end CFSG.RankThree.GF2n.Tim77
