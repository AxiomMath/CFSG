module

public import CFSG.Timmesfeld.Bridge.RootSetsConn12
public import CFSG.Timmesfeld.Bridge.RootSetsConn10
public import CFSG.Timmesfeld.Bridge.RootSetsConn11

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem orderOf_mul_eq_four_of_isPGroup (hD : IsRootInvolutionSet D) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) {s ℓ : G} (hs : s ∈ D) (hℓ : ℓ ∈ D) (hsS : s ∈ S) (hℓS : ℓ ∈ S)
    (hsℓ : ¬ Commute s ℓ) : orderOf (s * ℓ) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hs hℓ with h' | h' | ⟨hodd, -⟩
  · exact absurd h' hsℓ
  · exact h'
  · exfalso
    obtain ⟨k, hk⟩ := hS2 ⟨s * ℓ, S.mul_mem hsS hℓS⟩
    have hk' : (s * ℓ) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (s * ℓ) = 1 := by
      have hdvd := orderOf_dvd_of_pow_eq_one hk'
      rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd with ⟨j, -, hj⟩
      rcases j with _ | j
      · simpa using hj
      · rw [hj] at hodd
        exact absurd hodd
          (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩))
    rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq hℓ] at h1
    exact hsℓ (by rw [h1])

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem false_of_mul_conj_eq (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) (hT : ThreeClasses D x P) {c₁ : G}
    (hc₁N : c₁ ∈ Subgroup.normalizer (P : Set G)) {b₁ b₂ : G} (hb₁ : b₁ ∈ D) (hb₂ : b₂ ∈ D)
    (hb₁P : b₁ ∈ P) (hb₂P : b₂ ∈ P) (hne : b₁ ≠ b₂) (hq : b₁ * b₂ ∈ qcore D x P)
    (hcls : b₁ * (c₁ * b₁ * c₁⁻¹) ∉ qcore D x P)
    (heq : b₁ * (c₁ * b₁ * c₁⁻¹) = b₂ * (c₁ * b₂ * c₁⁻¹)) : False := by
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hP : ∀ p, p ∈ P ↔ c₁ * p * c₁⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hc₁N p
  set b₁' := c₁ * b₁ * c₁⁻¹ with hb₁'
  set b₂' := c₁ * b₂ * c₁⁻¹ with hb₂'
  have hb₁'D : b₁' ∈ D := hN c₁ b₁ hb₁
  have hb₂'D : b₂' ∈ D := hN c₁ b₂ hb₂
  have hb₁'P : b₁' ∈ P := (hP b₁).1 hb₁P
  have hb₂'P : b₂' ∈ P := (hP b₂).1 hb₂P
  have hcom : ∀ u v : G, u ∈ D → v ∈ D → u ∈ P → v ∈ P → Commute u v :=
    fun u v hu hv huP hvP => h.commute_of_mem hC hu hv huP hvP
  have hm : b₁ * b₂ = b₁' * b₂' := by
    have h1 : b₂ * (b₁ * b₁') * b₁' = b₂ * (b₂ * b₂') * b₁' := by rw [heq]
    rw [show b₂ * (b₁ * b₁') * b₁' = b₂ * b₁ * (b₁' * b₁') by group, hD.mul_self_eq_one hb₁'D,
      mul_one, show b₂ * (b₂ * b₂') * b₁' = b₂ * b₂ * (b₂' * b₁') by group,
      hD.mul_self_eq_one hb₂, one_mul, (hcom b₂ b₁ hb₂ hb₁ hb₂P hb₁P).eq,
      (hcom b₂' b₁' hb₂'D hb₁'D hb₂'P hb₁'P).eq] at h1
    exact h1
  have hc12 : Commute b₁ b₂ := hcom b₁ b₂ hb₁ hb₂ hb₁P hb₂P
  have hmD : b₁ * b₂ ∉ D := fun h' => h.not_mem_qcore hC h' hq
  obtain ⟨y, hy, hby, n, hn, hord⟩ := hC.exists_thirdKind hb₁ hb₂ hne hc12 hmD
  obtain ⟨hc₂D, -, hc₂₁, hc₂₂⟩ := hC.thirdKind_commute hb₁ hb₂ hne hc12 hy hby hn hord
  have hne' : b₁' ≠ b₂' := fun h' => hne (mul_left_cancel (mul_right_cancel h'))
  have hr1 : Reach D b₁ b₁' := reach_trans (reach_symm (h.reach_of_mem hC hb₁ hb₁P))
    (h.reach_of_mem hC hb₁'D hb₁'P)
  have hby' : ¬ Reach D b₁' y := fun hr => hby (reach_trans hr1 hr)
  have hord' : orderOf (y * (b₁' * b₂')) = 2 * n := by rw [← hm]; exact hord
  obtain ⟨-, -, hc₂₁', -⟩ := hC.thirdKind_commute hb₁'D hb₂'D hne'
    (hcom b₁' b₂' hb₁'D hb₂'D hb₁'P hb₂'P) hy hby' hn hord'
  rw [← hm] at hc₂₁'
  set c₂ := (y * (b₁ * b₂)) ^ n * (b₁ * b₂) with hc₂
  obtain ⟨g, hgB, S, hS2, hPS, hgS⟩ := h.exists_conj_mem_isPGroup hC (B := {b₁, b₂, b₁'})
    (fun β hβ => by
      rcases hβ with h' | h' | h'
      · rw [h']; exact ⟨hb₁, hb₁P⟩
      · rw [h']; exact ⟨hb₂, hb₂P⟩
      · rw [Set.mem_singleton_iff.1 h']; exact ⟨hb₁'D, hb₁'P⟩) (by
      rintro β (rfl | rfl | rfl)
      · exact hc₂₁
      · exact hc₂₂
      · exact hc₂₁') (hD.mul_self_eq_one hc₂D)
  have hg₁ : Commute g b₁ := hgB b₁ (by simp)
  have hg₂ : Commute g b₂ := hgB b₂ (by simp)
  have hg₃ : Commute g b₁' := hgB b₁' (by simp)
  have hgm : g * (b₁ * b₂) * g⁻¹ = b₁ * b₂ := by
    rw [(hg₁.mul_right hg₂).eq, mul_inv_cancel_right]
  have hconj : g * c₂ * g⁻¹ = (g * y * g⁻¹ * (b₁ * b₂)) ^ n * (b₁ * b₂) := by
    rw [hc₂, show g * ((y * (b₁ * b₂)) ^ n * (b₁ * b₂)) * g⁻¹ =
      (g * (y * (b₁ * b₂)) * g⁻¹) ^ n * (g * (b₁ * b₂) * g⁻¹) by rw [conj_pow]; group, hgm,
      show g * (y * (b₁ * b₂)) * g⁻¹ = g * y * g⁻¹ * (g * (b₁ * b₂) * g⁻¹) by group, hgm]
  have hc₂'D : g * c₂ * g⁻¹ ∈ D := hN g c₂ hc₂D
  have hc₂'1 : Commute (g * c₂ * g⁻¹) b₁ := by
    have := (Commute.conj_iff g).2 hc₂₁
    rwa [hg₁.eq, mul_inv_cancel_right] at this
  have hc₂'2 : Commute (g * c₂ * g⁻¹) b₁' := by
    have := (Commute.conj_iff g).2 hc₂₁'
    rwa [hg₃.eq, mul_inv_cancel_right] at this
  have hc₂'P : g * c₂ * g⁻¹ ∈ P :=
    h.mem_of_commute_of_threeClasses hB h3 hC hT hS2 hPS hb₁ hb₁'D hb₁P hb₁'P hcls hc₂'D hgS
      hc₂'1 hc₂'2
  have hy'D : g * y * g⁻¹ ∈ D := hN g y hy
  have hby'' : ¬ Reach D b₁ (g * y * g⁻¹) := fun hr => by
    have := reach_conj hN g⁻¹ hr
    rw [show g⁻¹ * b₁ * g⁻¹⁻¹ = b₁ by
      rw [inv_inv, mul_assoc, ← hg₁.eq, ← mul_assoc, inv_mul_cancel, one_mul]] at this
    exact hby (by simpa [mul_assoc] using this)
  have hord'' : orderOf (g * y * g⁻¹ * (b₁ * b₂)) = 2 * n := by
    rw [show g * y * g⁻¹ * (b₁ * b₂) = g * (y * (b₁ * b₂)) * g⁻¹ by
      rw [show g * (y * (b₁ * b₂)) * g⁻¹ = g * y * g⁻¹ * (g * (b₁ * b₂) * g⁻¹) by group, hgm]]
    have := (MulAut.conj g).orderOf_eq (y * (b₁ * b₂))
    rw [MulAut.conj_apply] at this
    rw [this, hord]
  exact h.false_of_triple (h3 G D a b c x z P hC h) hC hb₁ hb₂ hb₁P hb₂P hne hq hy'D hby'' hn
    hord'' (hconj ▸ hc₂'P)

theorem false_of_threeClasses (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) (hT : ThreeClasses D x P) : False := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have h3X := h3 G D a b c x z P hC h
  obtain ⟨d₀, hd₀D, hd₀P, hd₀a, had₀⟩ := h.exists_pair_mem_qcore hB hC
  have hcad : Commute a d₀ := h.commute_of_mem hC h.ha hd₀D h.haP hd₀P
  have had₀D : a * d₀ ∉ D := fun h' => h.not_mem_qcore hC h' had₀
  have hu2 := hC.mul_mul_self_of_commute h.ha hd₀D hcad
  obtain ⟨y, hy, hay, n, hn, hord⟩ := hC.exists_thirdKind h.ha hd₀D hd₀a.symm hcad had₀D
  obtain ⟨hc₀D, -, hc₀a, hc₀d⟩ := hC.thirdKind_commute h.ha hd₀D hd₀a.symm hcad hy hay hn hord
  obtain ⟨g, hgB, S, hS2, hPS, hgS⟩ := h.exists_conj_mem_isPGroup hC (B := {a, d₀})
    (fun β hβ => by
      rcases hβ with h' | h'
      · rw [h']; exact ⟨h.ha, h.haP⟩
      · rw [Set.mem_singleton_iff.1 h']; exact ⟨hd₀D, hd₀P⟩)
    (fun β hβ => by
      rcases hβ with h' | h'
      · rw [h']; exact hc₀a
      · rw [Set.mem_singleton_iff.1 h']; exact hc₀d) (hD.mul_self_eq_one hc₀D)
  have hga : Commute g a := hgB a (by simp)
  have hgd : Commute g d₀ := hgB d₀ (by simp)
  have hgu : g * (a * d₀) * g⁻¹ = a * d₀ := by rw [(hga.mul_right hgd).eq, mul_inv_cancel_right]
  set y' := g * y * g⁻¹ with hy'
  have hy'D : y' ∈ D := hN g y hy
  have hay' : ¬ Reach D a y' := fun hr => by
    have := reach_conj hN g⁻¹ hr
    rw [show g⁻¹ * a * g⁻¹⁻¹ = a by
      rw [inv_inv, mul_assoc, ← hga.eq, ← mul_assoc, inv_mul_cancel, one_mul]] at this
    exact hay (by simpa [hy', mul_assoc] using this)
  have hyu : y' * (a * d₀) = g * (y * (a * d₀)) * g⁻¹ := by
    rw [show g * (y * (a * d₀)) * g⁻¹ = g * y * g⁻¹ * (g * (a * d₀) * g⁻¹) by group, hgu]
  have hord' : orderOf (y' * (a * d₀)) = 2 * n := by
    have := (MulAut.conj g).orderOf_eq (y * (a * d₀))
    rw [MulAut.conj_apply] at this
    rw [hyu, this, hord]
  set c₁ := (y' * (a * d₀)) ^ n * (a * d₀) with hc₁
  have hc₁eq : c₁ = g * ((y * (a * d₀)) ^ n * (a * d₀)) * g⁻¹ := by
    rw [hc₁, hyu, show g * ((y * (a * d₀)) ^ n * (a * d₀)) * g⁻¹ =
      (g * (y * (a * d₀)) * g⁻¹) ^ n * (g * (a * d₀) * g⁻¹) by rw [conj_pow]; group, hgu]
  have hc₁S : c₁ ∈ S := hc₁eq ▸ hgS
  have hc₁D : c₁ ∈ D := hc₁eq ▸ hN g _ hc₀D
  have hc₁a : Commute c₁ a := by
    have := (Commute.conj_iff g).2 hc₀a
    rwa [← hc₁eq, hga.eq, mul_inv_cancel_right] at this
  have hc₁d : Commute c₁ d₀ := by
    have := (Commute.conj_iff g).2 hc₀d
    rwa [← hc₁eq, hgd.eq, mul_inv_cancel_right] at this
  by_cases hc₁P : c₁ ∈ P
  · exact h.false_of_triple h3X hC h.ha hd₀D h.haP hd₀P hd₀a.symm had₀ hy'D hay' hn hord' hc₁P
  obtain ⟨hnc, hnorm, hthird⟩ :=
    h.final_aux hB h3 hC hT hS2 hPS h.ha h.haP hc₁D hc₁S hc₁a hc₁P
  have hP : ∀ p, p ∈ P ↔ c₁ * p * c₁⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hnorm p
  obtain ⟨b₀, hb₀, hb₀P, hb₀a⟩ := h.exists_not_class hC h.ha
  have haQ : a ∉ qcore D x P := h.not_mem_qcore hC h.ha
  set Cb := {ℓ | ℓ ∈ D ∧ ℓ ∈ P ∧ ℓ * b₀ ∈ qcore D x P} with hCb
  set Ca := {ℓ | ℓ ∈ D ∧ ℓ ∈ P ∧ ℓ * a ∈ qcore D x P} with hCa
  have hnot : ∀ ℓ ∈ Cb, ℓ * a ∉ qcore D x P := fun ℓ hℓ h' =>
    hb₀a (mul_mem_qcore_trans hC hℓ.1 (mul_mem_qcore_comm hC hℓ.1 hb₀ hℓ.2.2) h')
  have hsq : ∀ ℓ ∈ Cb, ℓ * (c₁ * ℓ * c₁⁻¹) = (c₁ * ℓ) ^ 2 := fun ℓ hℓ => by
    have hcm : Commute ℓ (c₁ * ℓ * c₁⁻¹) := h.commute_of_mem hC hℓ.1 (hN c₁ ℓ hℓ.1) hℓ.2.1
      ((hP ℓ).1 hℓ.2.1)
    rw [hcm.eq, pow_two, hD.inv_eq hc₁D]
    group
  have hmaps : ∀ ℓ ∈ Cb, ℓ * (c₁ * ℓ * c₁⁻¹) ∈ Ca := by
    intro ℓ hℓ
    have hℓX : ℓ ∈ lsub D x P := mem_lsub_of_mem hℓ.1 hℓ.2.1
    have h4 := orderOf_mul_eq_four_of_isPGroup hD hS2 hc₁D hℓ.1 hc₁S (hPS hℓ.2.1)
      (hnc ℓ hℓ.1 hℓ.2.1 (hnot ℓ hℓ))
    refine ⟨hsq ℓ hℓ ▸ hD.sq_mem hc₁D hℓ.1 h4,
      P.mul_mem hℓ.2.1 ((hP ℓ).1 hℓ.2.1), ?_⟩
    obtain ⟨m, hm, hme⟩ := hthird ℓ hℓ.1 hℓ.2.1 (hnot ℓ hℓ)
    refine ⟨⟨ℓ, hℓX⟩ * m * ⟨ℓ, hℓX⟩⁻¹, CFSG.pCore_normal.conj_mem m hm _, ?_⟩
    change ℓ * (m : G) * ℓ⁻¹ = ℓ * (c₁ * ℓ * c₁⁻¹) * a
    rw [show (m : G) = c₁ * ℓ * c₁⁻¹ * a * ℓ from hme]
    group
  have hinj : Set.InjOn (fun ℓ => ℓ * (c₁ * ℓ * c₁⁻¹)) Cb := by
    intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ heq
    by_contra hne
    have hq : ℓ₁ * ℓ₂ ∈ qcore D x P :=
      mul_mem_qcore_trans hC hb₀ hℓ₁.2.2 (mul_mem_qcore_comm hC hℓ₂.1 hb₀ hℓ₂.2.2)
    have hcls : ℓ₁ * (c₁ * ℓ₁ * c₁⁻¹) ∉ qcore D x P := by
      intro h'
      obtain ⟨m, hm, hme⟩ := hthird ℓ₁ hℓ₁.1 hℓ₁.2.1 (hnot ℓ₁ hℓ₁)
      have hm' : c₁ * ℓ₁ * c₁⁻¹ * a * ℓ₁ ∈ qcore D x P := ⟨m, hm, hme⟩
      have hcm : Commute ℓ₁ a := h.commute_of_mem hC hℓ₁.1 h.ha hℓ₁.2.1 h.haP
      apply haQ
      have := (qcore D x P).mul_mem h' hm'
      rwa [show ℓ₁ * (c₁ * ℓ₁ * c₁⁻¹) * (c₁ * ℓ₁ * c₁⁻¹ * a * ℓ₁) =
          ℓ₁ * ((c₁ * ℓ₁ * c₁⁻¹) * (c₁ * ℓ₁ * c₁⁻¹)) * a * ℓ₁ by group,
        hD.mul_self_eq_one (hN c₁ ℓ₁ hℓ₁.1), mul_one, hcm.eq, mul_assoc,
        hD.mul_self_eq_one hℓ₁.1, mul_one] at this
    exact h.false_of_mul_conj_eq hB h3 hC hT hnorm hℓ₁.1 hℓ₂.1 hℓ₁.2.1 hℓ₂.2.1 hne hq hcls heq
  have hcard : Ca.ncard ≤ Cb.ncard := h.ncard_class_le hB hC h.ha hb₀ h.haP hb₀P
  have himg : (fun ℓ => ℓ * (c₁ * ℓ * c₁⁻¹)) '' Cb = Ca :=
    Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps)
      (by rw [hinj.ncard_image]; exact hcard) (Set.toFinite _)
  have haCa : a ∈ Ca := ⟨h.ha, h.haP, by rw [hD.mul_self_eq_one h.ha]; exact one_mem _⟩
  rw [← himg] at haCa
  obtain ⟨b', hb'Cb, hb'a⟩ := haCa
  have hsqa : (c₁ * b') ^ 2 = a := by rw [← hsq b' hb'Cb]; exact hb'a
  have hc₁aD : c₁ * a ∈ D := by
    have h1 : c₁ * a = b' * c₁ * b'⁻¹ := by
      rw [← hsqa, pow_two, hD.inv_eq hb'Cb.1,
        show c₁ * (c₁ * b' * (c₁ * b')) = c₁ * c₁ * b' * c₁ * b' by group,
        hD.mul_self_eq_one hc₁D, one_mul]
    rw [h1]
    exact hN b' c₁ hc₁D
  set t := (y' * (a * d₀)) ^ n with ht
  have htc : t = c₁ * a * d₀ := by
    calc t = t * ((a * d₀) * (a * d₀)) := by rw [hu2, mul_one]
      _ = c₁ * a * d₀ := by rw [hc₁]; group
  have hyt : Commute y' t := commute_self_mul_pow (hD.mul_self_eq_one hy'D) hu2 hord'
  have hat : Commute a t := by
    rw [htc]
    exact (hc₁a.symm.mul_right (Commute.refl a)).mul_right hcad
  have ht1 : t ≠ 1 := by
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord'] at hdvd
    have := Nat.le_of_dvd hn.pos hdvd
    have := hn.pos
    omega
  have hne : c₁ * a ≠ d₀ := by
    intro he
    apply ht1
    rw [htc, he, hD.mul_self_eq_one hd₀D]
  have hcd : Commute (c₁ * a) d₀ := hc₁d.mul_left hcad
  have hr1 := hC.reach_of_commute_mul hc₁aD hd₀D hy'D hne hcd (htc ▸ hyt)
  have hr2 := hC.reach_of_commute_mul hc₁aD hd₀D h.ha hne hcd (htc ▸ hat)
  exact hay' (reach_trans hr2 (reach_symm hr1))

end Step6

end CFSG.Timmesfeld.Bridge
