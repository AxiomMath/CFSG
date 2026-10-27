module

public import CFSG.Timmesfeld.Bridge.RootStructN0CycleNear

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

theorem exists_oneOpposite_pair (h : Hyp G D) (hconn : Moufang.ExcCollConnected D) :
    ∃ b ∈ D, ∃ x ∈ D, ¬ Commute b x ∧ Odd (orderOf (b * x)) ∧ OneOpposite D b x := by
  have hD := h.root
  obtain ⟨b, hb, -, -, -⟩ := h.nondeg
  obtain ⟨x, hx, h1x, hoddx⟩ := h.exists_opposite hb
  by_contra hno
  push Not at hno
  set S : Set G := {y | y ∈ D ∧ (Commute b y ∨ orderOf (b * y) = 4)} with hS
  have hclosed : ∀ y ∈ S, ∀ z ∈ D, Commute y z → y * z ∈ D → z ∈ S := by
    intro y hy z hz hyz hyzD
    refine ⟨hz, ?_⟩
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hb hz with h' | h' | ⟨hodd, hnc⟩
    · exact Or.inl h'
    · exact Or.inr h'
    · exfalso
      rcases hy.2 with hby | h4
      · exact not_commute_of_collinear hD hb hy.1 hnc hodd hyz.symm
          (by rw [← hyz.eq]; exact hyzD) hby
      · exact hno z hz b hb (fun h'' => hnc h''.symm) (by rwa [orderOf_mul_comm_eq])
          ⟨y, hy.1, hyz.symm, by rw [← hyz.eq]; exact hyzD, h4⟩
  have hxS := hconn S (fun y hy => hy.1) ⟨b, hb, Or.inl (Commute.refl b)⟩ hclosed hx
  rcases hxS.2 with h' | h'
  · have h2 : (b * x) ^ 2 = 1 :=
      (commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hb) (hD.mul_self_eq_one hx)).1 h'
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    obtain ⟨k, hk⟩ := hoddx
    have : orderOf (b * x) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · rw [h'] at hoddx
    exact absurd hoddx (by decide)

theorem conj_mem_rootSet_of_gate (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hU : UniqueGate D) {b x c t : G} (hb : b ∈ D) (hx : x ∈ D) (hbx : ¬ Commute b x)
    (hoddbx : Odd (orderOf (b * x))) (hcD : c ∈ D) (hbc : Commute b c) (hbcD : b * c ∈ D)
    (h4 : orderOf (x * c) = 4) (htb : t * b * t⁻¹ ∈ rootSet D b)
    (htx : t * x * t⁻¹ ∈ rootSet D x) : t * c * t⁻¹ ∈ rootSet D c := by
  have hclass := h.isClass
  have hD := h.root
  have h4c : orderOf (c * x) = 4 := by rwa [orderOf_mul_comm_eq]
  have hcT : c ∉ rootSet D b := fun h' => by
    have := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hb h' hx).1 h4c
    rw [this] at hoddbx
    exact absurd hoddbx (by decide)
  have htcD : t * c * t⁻¹ ∈ D := conj_mem_of_isClass hclass t hcD
  have htcT : t * c * t⁻¹ ∉ rootSet D b := by
    rw [← rootSet_eq_of_mem htb, rootSet_conj hclass]
    rintro ⟨y, hy, hye⟩
    have : y = c := by
      have := congrArg (fun w => t⁻¹ * w * t) hye
      simpa [mul_assoc] using this
    exact hcT (this ▸ hy)
  obtain ⟨htc1, htc2⟩ := collinear_of_collinear_mem_rootSet h hc hs hb htb htcD
    ((Commute.conj_iff t).2 hbc).symm (by
      have := conj_mem_of_isClass hclass t hbcD
      rwa [show t * (b * c) * t⁻¹ = t * c * t⁻¹ * (t * b * t⁻¹) by
        rw [show b * c = c * b from hbc.eq]; group] at this) htcT
  have h4tc : orderOf (x * (t * c * t⁻¹)) = 4 := by
    have h' : orderOf (t * x * t⁻¹ * (t * c * t⁻¹)) = 4 := by
      rw [show t * x * t⁻¹ * (t * c * t⁻¹) = t * (x * c) * t⁻¹ by group, orderOf_conj_eq]
      exact h4
    exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx htx htcD).1 h'
  exact hU hb hx hbx hoddbx hcD hbc hbcD h4 htcD htc1 htc2 h4tc

theorem conj_mem_sup_of_mem_rootGroup (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {y a d k t : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D) (hay : orderOf (a * y) = 4)
    (hk : k ∈ rootGroup D y) (ht : t ∈ rootGroup D a ⊔ rootGroup D d) :
    k * t * k⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
  have hD := h.root
  have := h.finite
  have hQ : Moufang.CommLambda D :=
    commLambda_of_nCoreCommutatorInRoot h.isClass hD (nCoreCommutatorInRoot_of_hyp h hc)
  rcases (mem_rootGroup_iff_of_rootClosure hD hc hy).1 hk with rfl | hkT
  · simpa using ht
  · have h1 := mul_inv_mem_of_special hD hc hs hQ ha hd had hadD hy hdy hdyD hay hkT ht
    rw [show k * t * k⁻¹ = k * t * k⁻¹ * t⁻¹ * t by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) ht

theorem conj_mem_rootSet_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {μ d e : G}
    (he : e ∈ rootSet D d) : μ * e * μ⁻¹ ∈ rootSet D (μ * d * μ⁻¹) := by
  rw [rootSet_conj hclass]
  exact ⟨e, he, rfl⟩

theorem opposite_conj_self (hD : IsRootInvolutionSet D) {k z : G} (hk : k ∈ D) (hz : z ∈ D)
    (hkz : ¬ Commute k z) (hodd : Odd (orderOf (k * z))) :
    ¬ Commute (k * z * k⁻¹) z ∧ Odd (orderOf (k * z * k⁻¹ * z)) := by
  have e : k * z * k⁻¹ * z = (k * z) ^ 2 := by
    rw [hD.inv_eq hk, sq]
    group
  have ho : orderOf ((k * z) ^ 2) = orderOf (k * z) :=
    Nat.Coprime.orderOf_pow (Nat.coprime_two_right.2 hodd)
  refine ⟨fun hc => ?_, by rw [e, ho]; exact hodd⟩
  have hw2 : k * z * k⁻¹ * (k * z * k⁻¹) = 1 := by
    rw [show k * z * k⁻¹ * (k * z * k⁻¹) = k * (z * z) * k⁻¹ by group, hD.mul_self_eq_one hz,
      mul_one, mul_inv_cancel]
  have h2 := (commute_iff_mul_sq_eq_one hw2 (hD.mul_self_eq_one hz)).1 hc
  rw [e, ← pow_mul] at h2
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  have h1 : orderOf (k * z) = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have : orderOf (k * z) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h' : orderOf (k * z) <;> omega
  rw [orderOf_eq_one_iff] at h1
  apply hkz
  rw [eq_inv_of_mul_eq_one_right h1]
  exact (Commute.refl k).inv_right

namespace TorusPath

variable {g : G} {p : ℤ → G}

theorem false_of_isPeriod_odd (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (h3 : ¬ ThreeLines D)
    (hP : TorusPath D g p) {μ : G} {c : ℤ} (hμ : μ ∈ D)
    (hμp : ∀ i, μ * p (c - i) * μ⁻¹ ∈ rootSet D (p i)) (hcodd : Odd c) {k : ℤ}
    (hk : IsPeriod D p k) (hodd : Odd k) : False := by
  have hclass := h.isClass
  have hD := h.root
  have := h.finite
  obtain ⟨a, ha⟩ := hcodd
  obtain ⟨m, hm⟩ := hodd
  set i₀ := a + m + 1 with hi₀
  have hfix : μ * p i₀ * μ⁻¹ ∈ rootSet D (p i₀) := by
    have h1 := hμp i₀
    rw [show c - i₀ = i₀ - k by omega] at h1
    have h2 : p (i₀ - k + k) ∈ rootSet D (p (i₀ - k)) := hk (i₀ - k)
    rw [sub_add_cancel] at h2
    have h3 := conj_mem_rootSet_conj hclass (μ := μ) h2
    rwa [rootSet_eq_of_mem h1] at h3
  have hswap : μ * p (i₀ + 1) * μ⁻¹ ∈ rootSet D (p (i₀ - 1)) := by
    have h1 := hμp (i₀ - 1)
    rw [show c - (i₀ - 1) = i₀ + 1 - k by omega] at h1
    have h2 : p (i₀ + 1 - k + k) ∈ rootSet D (p (i₀ + 1 - k)) := hk (i₀ + 1 - k)
    rw [sub_add_cancel] at h2
    have h3 := conj_mem_rootSet_conj hclass (μ := μ) h2
    rwa [rootSet_eq_of_mem h1] at h3
  have hfin : p (i₀ + 1) ∈ rootSet D (p (i₀ - 1)) → False := fun h' =>
    hP.turn i₀ (Subgroup.mem_sup_left (rootSet_subset_rootGroup D _ h'))
  have hμd : Commute (p i₀) μ := commute_of_conj_mem_rootSet hclass hD (hP.mem i₀) hμ hfix
  have hNP : Moufang.NoPolar D := noPolar_of_lineTI h hc hs hconn (hP.mem i₀) (hP.mem (i₀ + 1))
    (hP.comm i₀) (hP.mul_mem i₀) (hP.not_mem i₀)
    (hAll _ (hP.mem i₀) _ (hP.mem (i₀ + 1)) (hP.comm i₀) (hP.mul_mem i₀) (hP.not_mem i₀))
  by_cases hμT : μ ∈ rootSet D (p i₀)
  · have hc1 : Commute μ (p (i₀ + 1)) := (hμT.2 _ (hP.mem _)).2 (hP.comm i₀)
    apply hfin
    rw [hc1.eq, mul_inv_cancel_right] at hswap
    exact hswap
  · have hμne : p i₀ ≠ μ := fun h' => hμT (h' ▸ mem_rootSet_self (hP.mem i₀))
    have hpμD := hNP _ (hP.mem i₀) _ hμ hμd hμne
    have hsub := hP.turn_sub h hc hs i₀
    rw [sup_comm] at hsub
    rcases mem_line_or_mem_line_of_not_threeLines h3 (hP.mem i₀) (hP.mem (i₀ + 1))
        (hP.mem (i₀ - 1)) hμ ⟨hP.comm i₀, hP.mul_mem i₀, hP.not_mem i₀⟩
        ⟨(hP.comm_sub i₀).symm, hP.mul_mem_sub i₀, hP.not_mem_sub i₀⟩ ⟨hμd, hpμD, hμT⟩ hsub
      with h' | h'
    · have hc1 : Commute μ (p (i₀ + 1)) := commute_of_mem_sup_rootGroup (hP.mem i₀)
        (hP.mem (i₀ + 1)) (hP.comm i₀) h' (right_mem_line (hP.mem (i₀ + 1)))
      apply hfin
      rw [hc1.eq, mul_inv_cancel_right] at hswap
      exact hswap
    · have hc1 : Commute μ (p (i₀ - 1)) := commute_of_mem_sup_rootGroup (hP.mem i₀)
        (hP.mem (i₀ - 1)) (hP.comm_sub i₀).symm h' (right_mem_line (hP.mem (i₀ - 1)))
      apply hfin
      have h3 := conj_mem_rootSet_conj hclass (μ := μ⁻¹) hswap
      have e1 : μ⁻¹ * (μ * p (i₀ + 1) * μ⁻¹) * μ⁻¹⁻¹ = p (i₀ + 1) := by group
      have e2 : μ⁻¹ * p (i₀ - 1) * μ⁻¹⁻¹ = p (i₀ - 1) := by
        rw [inv_inv, mul_assoc, ← hc1.eq, ← mul_assoc, inv_mul_cancel, one_mul]
      rwa [e1, e2] at h3

theorem reflect (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (h3 : ¬ ThreeLines D)
    (hF : FixUnique D) (hU : UniqueGate D) (hg : InvTorus D g) (hP : TorusPath D g p) {j : ℤ}
    (hopp : ¬ Commute (p j) (p (j + 3))) (hodd : Odd (orderOf (p j * p (j + 3)))) {μ : G}
    (hμg : μ * g * μ⁻¹ = g⁻¹) (hμ1 : μ * p (j + 3) * μ⁻¹ ∈ rootSet D (p j))
    (hμ2 : μ * p j * μ⁻¹ ∈ rootSet D (p (j + 3))) (i : ℤ) :
    μ * p (2 * j + 3 - i) * μ⁻¹ ∈ rootSet D (p i) := by
  have hclass := h.isClass
  have hD := h.root
  have hQ := (hP.reverse h hc hs (2 * j + 3)).conj hclass μ
  rw [hμg] at hQ
  have hQ' := hQ.of_fix fun d hd hgd => conj_mem_rootSet_of_mem_zpowers h hc hd hgd
    (by have := Subgroup.inv_mem _ (Subgroup.mem_zpowers g⁻¹); rwa [inv_inv] at this)
  have h4a : orderOf (p (j + 3) * p (j + 1)) = 4 := by
    rw [orderOf_mul_comm_eq]
    have := orderOf_mul_eq_four_of_path h hc hs hconn hAll (hP.mem (j + 1)) (hP.mem (j + 1 + 1))
      (hP.mem (j + 1 + 1 + 1)) (hP.comm (j + 1)) (hP.mul_mem (j + 1)) (hP.not_mem (j + 1))
      (hP.comm (j + 1 + 1)) (hP.mul_mem (j + 1 + 1))
      (by have := hP.turn (j + 1 + 1); rwa [show j + 1 + 1 - 1 = j + 1 by ring] at this)
    rwa [show j + 1 + 1 + 1 = j + 3 by ring] at this
  have h4b : orderOf (p j * p (j + 2)) = 4 := by
    have := orderOf_mul_eq_four_of_path h hc hs hconn hAll (hP.mem j) (hP.mem (j + 1))
      (hP.mem (j + 1 + 1)) (hP.comm j) (hP.mul_mem j) (hP.not_mem j) (hP.comm (j + 1))
      (hP.mul_mem (j + 1))
      (by have := hP.turn (j + 1); rwa [show j + 1 - 1 = j by ring] at this)
    rwa [show j + 1 + 1 = j + 2 by ring] at this
  have h0 : μ * p (2 * j + 3 - j) * μ⁻¹ ∈ rootSet D (p j) := by
    rwa [show 2 * j + 3 - j = j + 3 by ring]
  have h1 : μ * p (2 * j + 3 - (j + 1)) * μ⁻¹ ∈ rootSet D (p (j + 1)) := by
    rw [show 2 * j + 3 - (j + 1) = j + 2 by ring]
    have hcD : μ * p (j + 2) * μ⁻¹ ∈ D := conj_mem_of_isClass hclass μ (hP.mem _)
    have hcol : Commute (μ * p (j + 2) * μ⁻¹) (μ * p (j + 3) * μ⁻¹) := by
      have := hP.comm (j + 2)
      rw [show j + 2 + 1 = j + 3 by ring] at this
      exact (Commute.conj_iff μ).2 this
    have hcolD : μ * p (j + 2) * μ⁻¹ * (μ * p (j + 3) * μ⁻¹) ∈ D := by
      have := conj_mem_of_isClass hclass μ (hP.mul_mem (j + 2))
      rwa [show j + 2 + 1 = j + 3 by ring, show μ * (p (j + 2) * p (j + 3)) * μ⁻¹ =
        μ * p (j + 2) * μ⁻¹ * (μ * p (j + 3) * μ⁻¹) by group] at this
    have hcT : μ * p (j + 2) * μ⁻¹ ∉ rootSet D (p j) := by
      rw [← rootSet_eq_of_mem hμ1, rootSet_conj hclass]
      rintro ⟨y, hy, hye⟩
      have : y = p (j + 2) := by
        have := congrArg (fun w => μ⁻¹ * w * μ) hye
        simpa [mul_assoc] using this
      have h' := hP.not_mem (j + 2)
      rw [show j + 2 + 1 = j + 3 by ring] at h'
      exact h' (mem_rootSet_comm (hP.mem _) (this ▸ hy))
    obtain ⟨hc1, hc2⟩ := collinear_of_collinear_mem_rootSet h hc hs (hP.mem j) hμ1 hcD hcol hcolD
      hcT
    have h4c : orderOf (p (j + 3) * (μ * p (j + 2) * μ⁻¹)) = 4 := by
      have h' : orderOf (μ * p j * μ⁻¹ * (μ * p (j + 2) * μ⁻¹)) = 4 := by
        rw [show μ * p j * μ⁻¹ * (μ * p (j + 2) * μ⁻¹) = μ * (p j * p (j + 2)) * μ⁻¹ by group,
          orderOf_conj_eq]
        exact h4b
      exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD (hP.mem _) hμ2 hcD).1 h'
    exact hU (hP.mem j) (hP.mem (j + 3)) hopp hodd (hP.mem (j + 1)) (hP.comm j) (hP.mul_mem j) h4a
      hcD hc1 hc2 h4c
  exact rootSet_of_rootSet h hc hs h3 hF hg hP hQ' h0 h1 i

theorem exists_mem_rootSet_of_path3 (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (h3 : ¬ ThreeLines D)
    (hF : FixUnique D) (hU : UniqueGate D) (hg : InvTorus D g) (hP : TorusPath D g p) {i : ℤ}
    {y₁ y₂ z : G} (hy₁ : y₁ ∈ D) (hy₂ : y₂ ∈ D) (hz : z ∈ D) (h01 : Commute (p i) y₁)
    (h01D : p i * y₁ ∈ D) (h12 : (Commute y₁ y₂ ∧ y₁ * y₂ ∈ D) ∨ y₁ = y₂)
    (h2z : Commute y₂ z) (h2zD : y₂ * z ∈ D) (hgz : g * z * g⁻¹ ∈ rootSet D z) :
    ∃ e : ℤ, -3 ≤ e ∧ e ≤ 3 ∧ z ∈ rootSet D (p (i + e)) := by
  have hD := h.root
  have hNP : Moufang.NoPolar D := noPolar_of_lineTI h hc hs hconn (hP.mem i) (hP.mem (i + 1))
    (hP.comm i) (hP.mul_mem i) (hP.not_mem i)
    (hAll _ (hP.mem i) _ (hP.mem (i + 1)) (hP.comm i) (hP.mul_mem i) (hP.not_mem i))
  rcases commute_or_orderOf_mul_eq_four_or_odd hD (hP.mem i) hz with hcz | h4 | ⟨hodd, hnc⟩
  · by_cases hzT : z ∈ rootSet D (p i)
    · exact ⟨0, by norm_num, by norm_num, by simpa using hzT⟩
    · have hne : p i ≠ z := fun h' => hzT (h' ▸ mem_rootSet_self (hP.mem i))
      rcases hP.mem_rootSet_of_collinear h hc hs h3 hF hg hz hcz (hNP _ (hP.mem i) _ hz hcz hne)
          hzT hgz with h' | h'
      · exact ⟨-1, by norm_num, by norm_num, by simpa [sub_eq_add_neg] using h'⟩
      · exact ⟨1, by norm_num, by norm_num, h'⟩
  · rcases hP.mem_rootSet_of_special h hc hs h3 hF hg hz h4 hgz with h' | h'
    · exact ⟨-2, by norm_num, by norm_num, by simpa [sub_eq_add_neg] using h'⟩
    · exact ⟨2, by norm_num, by norm_num, h'⟩
  ·
    have h4 : orderOf (z * y₁) = 4 := by
      rcases commute_or_orderOf_mul_eq_four_or_odd hD hz hy₁ with hc1 | h41 | ⟨hodd1, hnc1⟩
      · exfalso
        have hne : z ≠ y₁ := fun h' => hnc (h' ▸ h01)
        exact not_commute_of_collinear hD (hP.mem i) hy₁ hnc hodd hc1 (hNP _ hz _ hy₁ hc1 hne)
          h01
      · exact h41
      · exfalso
        rcases h12 with ⟨h12c, h12D⟩ | rfl
        · exact not_commute_of_collinear hD hz hy₂ hnc1 hodd1 h12c h12D h2z.symm
        · exact hnc1 h2z.symm
    rcases hP.mem_rootSet_of_oneOpposite h hc hs h3 hF hU hg hz hnc hodd ⟨y₁, hy₁, h01, h01D, h4⟩
        hgz with h' | h'
    · exact ⟨-3, by norm_num, by norm_num, by simpa [sub_eq_add_neg] using h'⟩
    · exact ⟨3, by norm_num, by norm_num, h'⟩

theorem fix_of_mem_zpowers (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D)
    (hTwo : ∀ v ∈ D, ∀ u ∈ D, Commute v u → v * u ∈ D → u ∉ rootSet D v →
      ∃ e ∈ D, Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v ∧ e ∉ rootGroup D v ⊔ rootGroup D u)
    {t : G} (hg : InvTorus D g) (ht : InvTorus D t) (hP : TorusPath D g p) {j : ℤ}
    (ht0 : t * p j * t⁻¹ ∈ rootSet D (p j)) (ht1 : t * p (j + 1) * t⁻¹ ∈ rootSet D (p (j + 1)))
    (hgt : t ∈ Subgroup.zpowers (g * t * g⁻¹)) (i : ℤ) : t * p i * t⁻¹ ∈ rootSet D (p i) := by
  have hclass := h.isClass
  obtain ⟨q, hQ, hq0, hq1⟩ := exists_torusPath h hc hs h3 hF ht hTwo (hP.mem j) (hP.mem (j + 1))
    (hP.comm j) (hP.mul_mem j) (hP.not_mem j) ht0 ht1
  have hQ' := (hQ.conj hclass g).of_fix fun d hd hgd =>
    conj_mem_rootSet_of_mem_zpowers h hc hd hgd hgt
  have h0 : g * q 0 * g⁻¹ ∈ rootSet D (q 0) := by
    rw [hq0]
    exact hP.fix j
  have h1 : g * q (0 + 1) * g⁻¹ ∈ rootSet D (q (0 + 1)) := by
    rw [zero_add, hq1]
    exact hP.fix (j + 1)
  have hgq := rootSet_of_rootSet h hc hs h3 hF ht hQ hQ' h0 h1
  have hQg : TorusPath D g q := ⟨hQ.mem, hQ.comm, hQ.mul_mem, hQ.not_mem, hQ.turn, hgq⟩
  have e0 : q (j + -j) ∈ rootSet D (p j) := by
    rw [add_neg_cancel, hq0]
    exact mem_rootSet_self (hP.mem j)
  have e1 : q (j + 1 + -j) ∈ rootSet D (p (j + 1)) := by
    rw [show j + 1 + -j = 1 by ring, hq1]
    exact mem_rootSet_self (hP.mem _)
  have hqp := rootSet_of_rootSet h hc hs h3 hF hg hP (hQg.shift (-j)) e0 e1 i
  exact conj_mem_rootSet_of_mem_rootSet hclass (hQ.fix (i + -j)) (mem_rootSet_comm (hP.mem i) hqp)

end TorusPath

end CFSG.Timmesfeld.Bridge
