module

public import CFSG.Timmesfeld.Bridge.RootStructR2Torus

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem lt_pow_of_two_le {r n : ℕ} (hr : 1 ≤ r) (hn : 2 ≤ n) : r * n + 1 < (r + 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => nlinarith
  | succ n hn ih =>
    rw [pow_succ]
    have h1 : 1 ≤ (r + 1) ^ n := Nat.one_le_pow _ _ (by omega)
    calc r * (n + 1) + 1 = (r * n + 1) + r := by ring
      _ < (r + 1) ^ n + r := by omega
      _ ≤ (r + 1) ^ n + r * (r + 1) ^ n := by nlinarith
      _ = (r + 1) ^ n * (r + 1) := by ring

theorem exists_prime_dvd_pow_sub_one {q n : ℕ} (hq : 2 ≤ q) (hqe : Even q) (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ q ^ n - 1 ∧ ¬ p ∣ q - 1 := by
  by_contra hall
  push Not at hall
  have hlt : (q - 1) * n < q ^ n - 1 := by
    have := lt_pow_of_two_le (r := q - 1) (by omega) hn
    rw [Nat.sub_add_cancel (by omega)] at this
    omega
  have hpos : 0 < (q - 1) * n := Nat.mul_pos (by omega) (by omega)
  have hdvd : q ^ n - 1 ∣ (q - 1) * n := by
    refine (Nat.factorization_prime_le_iff_dvd (by omega) hpos.ne').1 fun p hp => ?_
    by_cases hpd : p ∣ q ^ n - 1
    · have hpq := hall p hp hpd
      have : Fact p.Prime := ⟨hp⟩
      have hp2 : p ≠ 2 := by
        rintro rfl
        obtain ⟨r, hr⟩ := hqe
        omega
      have hpodd : Odd p := hp.odd_of_ne_two hp2
      have hpnq : ¬ p ∣ q := fun h' => by
        have : p ∣ q - (q - 1) := Nat.dvd_sub h' hpq
        rw [show q - (q - 1) = 1 by omega] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      have hLTE := padicValNat.pow_sub_pow (x := q) (y := 1) (p := p) hpodd (by omega)
        (by simpa using hpq) hpnq (n := n) (by omega)
      rw [one_pow] at hLTE
      rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
        Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp, hLTE]
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Nat.zero_le _
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

theorem commute_of_map_conj_eq_of_mem_line (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hAll : AllLinesTI D) {a c u g : G} (ha : a ∈ D) (hcD : c ∈ D)
    (huD : u ∈ D) (hac : Commute a c) (hacD : a * c ∈ D) (hcT : c ∉ rootSet D a)
    (huL : u ∈ rootGroup D a ⊔ rootGroup D c) (hua : u ∉ rootSet D a) (huc : u ∉ rootSet D c)
    (hga : ∀ s ∈ rootGroup D a, Commute g s)
    (hgc : (rootGroup D c).map (MulAut.conj g).toMonoidHom = rootGroup D c)
    (hgu : (rootGroup D u).map (MulAut.conj g).toMonoidHom = rootGroup D u) {v : G}
    (hv : v ∈ rootGroup D c) : Commute g v := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  set L := rootGroup D a ⊔ rootGroup D c with hLdef
  have hab : ∀ {y z : G}, y ∈ L → z ∈ L → Commute y z := fun hy hz =>
    commute_of_mem_sup_rootGroup ha hcD hac hy hz
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hcD hac huL
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hua huD
    exact hua (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hβ (hD.ne_one huD))
  have hβ1 : β ≠ 1 := by
    rintro rfl
    rw [one_mul] at huc huD
    exact huc (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcD hγ (hD.ne_one huD))
  have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hβ hβ1
  have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcD hγ hγ1
  obtain ⟨τ, hτ, hτa, hτeq⟩ := exists_conj_eq_mul_of_mem_rootSet h hc hs ha hcD hac hacD hcT hβT hγT
  have hLTI := hAll a ha c hcD hac hacD hcT
  have hN := normalizesLine_of_commute h hc hs ha hcD hac hacD hcT hLTI ha (left_mem_line ha) hτ
    hτa
  have hτu : (rootGroup D c).map (MulAut.conj τ).toMonoidHom = rootGroup D (β * γ) := by
    rw [← rootGroup_eq_of_mem hγT, ← rootGroup_conj hclass, ← hτeq]
  rcases (mem_rootGroup_iff_of_rootClosure hD hc hcD).1 hv with rfl | hvT
  · exact Commute.one_right g
  have hvL : v ∈ L := Subgroup.mem_sup_right hv
  obtain ⟨a₁, ha₁, hw⟩ : ∃ a₁ ∈ rootGroup D a, τ * v * τ⁻¹ = a₁ * v := by
    by_cases hτv : Commute τ v
    · exact ⟨1, Subgroup.one_mem _, by rw [hτv.eq, mul_inv_cancel_right, one_mul]⟩
    · obtain ⟨h4, hsq⟩ := sq_mem_rootSet_of_normalizesLine h hc hs ha hcD hac hacD hcT hτ hN ha
        (left_mem_line ha) hvT.1 hvL hτa hτv
      refine ⟨(v * τ) ^ 2, rootSet_subset_rootGroup D a hsq, ?_⟩
      have hv2 := hD.mul_self_eq_one hvT.1
      rw [mul_sq_eq_mul_sq_comm hv2 (hD.mul_self_eq_one hτ) h4, hD.inv_eq hτ, sq]
      calc τ * v * τ = τ * v * τ * (v * v) := by rw [hv2, mul_one]
        _ = τ * v * (τ * v) * v := by simp only [mul_assoc]
  have hwu : τ * v * τ⁻¹ ∈ rootGroup D (β * γ) := by
    rw [← hτu]
    exact ⟨v, hv, rfl⟩
  have hgw : g * (τ * v * τ⁻¹) * g⁻¹ ∈ rootGroup D (β * γ) := by
    rw [← hgu]
    exact ⟨_, hwu, rfl⟩
  have hgv : g * v * g⁻¹ ∈ rootGroup D c := by
    rw [← hgc]
    exact ⟨v, hv, rfl⟩
  have ha₁L : a₁ ∈ L := Subgroup.mem_sup_left ha₁
  have hgvL : g * v * g⁻¹ ∈ L := Subgroup.mem_sup_right hgv
  have hz : g * v * g⁻¹ * v⁻¹ =
      g * (τ * v * τ⁻¹) * g⁻¹ * (τ * v * τ⁻¹)⁻¹ := by
    rw [hw]
    have e1 : g * (a₁ * v) * g⁻¹ = a₁ * (g * v * g⁻¹) := by
      calc g * (a₁ * v) * g⁻¹ = g * a₁ * g⁻¹ * (g * v * g⁻¹) := by group
        _ = a₁ * (g * v * g⁻¹) := by rw [(hga a₁ ha₁).eq, mul_inv_cancel_right]
    rw [e1, mul_inv_rev, (hab ha₁L hgvL).eq]
    calc g * v * g⁻¹ * v⁻¹ = g * v * g⁻¹ * a₁ * a₁⁻¹ * v⁻¹ := by group
      _ = g * v * g⁻¹ * a₁ * (v⁻¹ * a₁⁻¹) := by
        rw [mul_assoc (g * v * g⁻¹ * a₁), (hab (Subgroup.inv_mem _ ha₁L)
          (Subgroup.inv_mem _ hvL)).eq]
  have hzu : g * v * g⁻¹ * v⁻¹ ∈ rootGroup D (β * γ) := by
    rw [hz]
    exact Subgroup.mul_mem _ hgw (Subgroup.inv_mem _ hwu)
  have hzc : g * v * g⁻¹ * v⁻¹ ∈ rootGroup D c := Subgroup.mul_mem _ hgv (Subgroup.inv_mem _ hv)
  have hne : rootSet D (β * γ) ≠ rootSet D c := fun h' => huc (h' ▸ mem_rootSet_self huD)
  have h1 : g * v * g⁻¹ * v⁻¹ = 1 := by
    have : g * v * g⁻¹ * v⁻¹ ∈ rootGroup D (β * γ) ⊓ rootGroup D c := ⟨hzu, hzc⟩
    rwa [rootGroup_inf_eq_bot_of_rootClosure hD hc huD hcD hne, Subgroup.mem_bot] at this
  have h2 : g * v * g⁻¹ = v := mul_inv_eq_one.1 h1
  calc g * v = g * v * g⁻¹ * g := by group
    _ = v * g := by rw [h2]

theorem LineSetting.commute_of_orderOf_eq_prime (hL : LineSetting G D) (hAll : AllLinesTI D)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {a : G} (ha : a ∈ D)
    (hpq : ¬ p ∣ Nat.card (rootGroup D a) - 1) {T : Subgroup G} (hT : T ∈ rootLines D a) {g : G}
    (hg : orderOf g = p) (hga : ∀ s ∈ rootGroup D a, Commute g s)
    (hgT : T.map (MulAut.conj g).toMonoidHom = T) {v : G} (hv : v ∈ T) : Commute g v := by
  have := hL.hyp.finite
  have h := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  have hD := h.root
  have hclass := h.isClass
  have hP : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hPa : ∀ x ∈ Subgroup.zpowers g, (rootGroup D a).map (MulAut.conj x).toMonoidHom =
      rootGroup D a := by
    intro x hx
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hx
    exact map_conj_eq_self_of_commute fun s hs => (hga s hs).pow_left j
  have hPT : ∀ x ∈ Subgroup.zpowers g, T.map (MulAut.conj x).toMonoidHom = T := by
    intro x hx
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hx
    exact map_conj_pow_eq hgT j
  obtain ⟨_, ⟨⟨c, hcD, hcT, rfl⟩, hCa⟩, hCfix⟩ := hL.exists_fixed_linePoints hp2 hP ha hT hPa hPT
  rw [Set.mem_singleton_iff] at hCa
  obtain ⟨hac, hacD, hcTa, hTeq⟩ := collinear_of_mem_rootLines h hc hs ha hcD hT hcT hCa
  set S := linePoints D T \ {rootGroup D a, rootGroup D c} with hSdef
  have hpair : rootGroup D a ≠ rootGroup D c := fun h' => hCa h'.symm
  have hsub : ({rootGroup D a, rootGroup D c} : Set (Subgroup G)) ⊆ linePoints D T := by
    rintro P (rfl | rfl)
    · exact ⟨a, ha, hTeq ▸ left_mem_line ha, rfl⟩
    · exact ⟨c, hcD, hcT, rfl⟩
  have hSn : S.ncard = Nat.card (rootGroup D a) - 1 := by
    rw [hSdef, Set.ncard_sdiff hsub, Set.ncard_pair hpair, ← hTeq,
      ncard_linePoints h hc hs ha hcD hac hacD hcTa]
    omega
  obtain ⟨_, ⟨⟨u, huD, huT, rfl⟩, hU⟩, hUfix⟩ := exists_map_conj_eq_of_isPGroup hP
    (S := S) (fun x hx E hE => ⟨by
      have := map_conj_mem_linePoints hclass hE.1 x
      rwa [hPT x hx] at this, fun h' => hE.2 (by
        rcases h' with h' | h'
        · left
          exact Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom)
            (MulAut.conj x).injective (h'.trans (hPa x hx).symm)
        · right
          exact Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom)
            (MulAut.conj x).injective (h'.trans (hCfix x hx).symm))⟩) (by rwa [hSn])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hU
  have hua : u ∉ rootSet D a := fun h' => hU.1 (rootGroup_eq_of_mem h')
  have huc : u ∉ rootSet D c := fun h' => hU.2 (rootGroup_eq_of_mem h')
  have huL : u ∈ rootGroup D a ⊔ rootGroup D c := by rw [hTeq]; exact huT
  have hgc : ∀ w ∈ rootGroup D c, Commute g w := fun w hw =>
    commute_of_map_conj_eq_of_mem_line h hc hs hAll ha hcD huD hac hacD hcTa huL hua huc hga
      (hCfix g (Subgroup.mem_zpowers g)) (hUfix g (Subgroup.mem_zpowers g)) hw
  have hle : T ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [← hTeq]
    refine sup_le (fun s hs => ?_) (fun s hs => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hga s hs).symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hgc s hs).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hv)).symm

theorem LineSetting.pow_eq_one_of_torus (hL : LineSetting G D) {a d : G} (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    {T T' : Subgroup G} (hT : T ∈ rootLines D a) (hT' : T' ∈ rootLines D a) (hTT' : T ≠ T')
    {h : G} (hh : h ∈ lineGroup D a d) (hord : orderOf h + 2 = (rootLines D a).ncard)
    (hhT : T.map (MulAut.conj h).toMonoidHom = T) (hhT' : T'.map (MulAut.conj h).toMonoidHom = T')
    (htrans : ∀ L ∈ rootLines D a, ∀ L' ∈ rootLines D a, L ≠ T → L ≠ T' → L' ≠ T → L' ≠ T' →
      ∃ i < orderOf h, L.map (MulAut.conj (h ^ i)).toMonoidHom = L')
    {L : Subgroup G} (hL₀ : L ∈ rootLines D a) (hLT : L ≠ T) (hLT' : L ≠ T') {j : ℕ}
    (hj : L.map (MulAut.conj (h ^ j)).toMonoidHom = L) : h ^ j = 1 := by
  have := hL.hyp.finite
  have hcomm : ∀ i : ℕ, ∀ t ∈ rootGroup D a, Commute (h ^ i) t := fun i t ht =>
    hL.commute_of_mem_lineGroup ha hd had hadD hdT (pow_mem hh i) ht
  have hTT'sub : ({T, T'} : Set (Subgroup G)) ⊆ rootLines D a := by
    rintro L (rfl | rfl)
    · exact hT
    · exact hT'
  refine pow_eq_one_of_map_conj_pow_eq (S := rootLines D a \ {T, T'}) ?_ ?_ ?_
    ⟨hL₀, by simp [hLT, hLT']⟩ hj
  · rw [Set.ncard_sdiff hTT'sub, Set.ncard_pair hTT']
    omega
  · intro i L' hL'
    refine ⟨map_conj_mem_rootLines_of_map_eq hL.hyp hL.closure hL.special ha
      (map_conj_eq_self_of_commute (hcomm i)) hL'.1, fun h' => hL'.2 ?_⟩
    rcases h' with h' | h'
    · left
      exact Subgroup.map_injective (f := (MulAut.conj (h ^ i)).toMonoidHom)
        (MulAut.conj (h ^ i)).injective (h'.trans (map_conj_pow_eq hhT i).symm)
    · right
      exact Subgroup.map_injective (f := (MulAut.conj (h ^ i)).toMonoidHom)
        (MulAut.conj (h ^ i)).injective (h'.trans (map_conj_pow_eq hhT' i).symm)
  · intro L₁ hL₁ L₂ hL₂
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hL₁ hL₂
    exact htrans L₁ hL₁.1 L₂ hL₂.1 hL₁.2.1 hL₁.2.2 hL₂.2.1 hL₂.2.2

theorem LineSetting.false_of_prime_dvd_sub_one {G : Type} [Group G] {D : Set G}
    (hL : LineSetting G D) (hAll : AllLinesTI D) (hTor : RootLinesTorusStep) (IH : RootIHStructE G)
    (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) {Q k : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) (hQ2 : 2 ≤ Q)
    (hk : ∀ a ∈ D, ∀ x ∈ D, ¬ Commute a x → Odd (orderOf (a * x)) → OneOpposite D a x →
      (gatedLines D a x).ncard = k)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpQ : p ∣ Q - 1)
    (hpq : ∀ c ∈ D, ¬ p ∣ Nat.card (rootGroup D c) - 1) (hpk : p ∣ k - 1) : False := by
  have := hL.hyp.finite
  have : Fact p.Prime := ⟨hp⟩
  have h := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨a, ha, d, hd, had, hadD, hdT, -⟩ := hL.line
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
  have h3 : 3 ≤ (rootLines D a).ncard := by rw [hQ a ha]; omega
  obtain ⟨h₀, hh, hord, hhT, hhT', htrans⟩ := hTor G D hL a ha d hd had hadD hdT h3 _ hT T' hT'
    hne.symm
  have horder : orderOf h₀ = Q - 1 := by rw [hQ a ha] at hord; omega
  obtain ⟨m, hm⟩ := hpQ
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have horder_u : orderOf (h₀ ^ m) = p := by
    have hdvd : m ∣ orderOf h₀ := ⟨p, by rw [horder, hm, mul_comm]⟩
    rw [orderOf_pow_of_dvd hm0 hdvd, horder, hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hP : IsPGroup p (Subgroup.zpowers (h₀ ^ m)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder_u, pow_one])
  have hPh : Subgroup.zpowers (h₀ ^ m) ≤ Subgroup.zpowers h₀ :=
    Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers h₀) _)
  obtain ⟨x, hx, hax, hoddax, hx1, hTΓ, hgx, hdvd⟩ := hL.exists_fixed_of_torus hAll ha hd had hadD
    hdT hT hT' hne.symm hh hord hhT hhT' htrans hp2 hP hPh
  rw [Nat.card_zpowers, horder_u] at hdvd
  have hkx := hk a ha x hx hax hoddax hx1
  have hT'Γ : T' ∉ gatedLines D a x := by
    intro hT'Γ
    have hsub : ({rootGroup D a ⊔ rootGroup D d, T'} : Set (Subgroup G)) ⊆ gatedLines D a x := by
      rintro L (rfl | rfl)
      · exact hTΓ
      · exact hT'Γ
    have hk2 : 2 ≤ k := by
      rw [← hkx, ← Set.ncard_pair hne.symm]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_sdiff hsub, Set.ncard_pair hne.symm, hkx] at hdvd
    have : p ∣ (k - 1) - (k - 2) := Nat.dvd_sub hpk hdvd
    rw [show k - 1 - (k - 2) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  obtain ⟨d', hd', had', had'D, hd'T, rfl⟩ := hT'
  have hno : ∀ p' ∈ D, p' ∈ rootGroup D a ⊔ rootGroup D d' → orderOf (x * p') ≠ 4 :=
    fun p' hp' hp'T h4 => hT'Γ ⟨⟨d', hd', had', had'D, hd'T, rfl⟩, p', hp', hp'T, h4⟩
  have htop := top_of_forall_not_special h hc hs hL.conn hAll IH hl ha hd' had' had'D hd'T hx hax
    hoddax hx1 hno
  have hua : ∀ s ∈ rootGroup D a, Commute (h₀ ^ m) s := fun s hs =>
    hL.commute_of_mem_lineGroup ha hd had hadD hdT (pow_mem hh m) hs
  have huT' : ∀ v ∈ rootGroup D a ⊔ rootGroup D d', Commute (h₀ ^ m) v := fun v hv =>
    hL.commute_of_orderOf_eq_prime hAll hp2 ha (hpq a ha) ⟨d', hd', had', had'D, hd'T, rfl⟩
      horder_u hua (map_conj_pow_eq hhT' m) hv
  have hux : ∀ v ∈ rootGroup D x, Commute (h₀ ^ m) v := fun v hv =>
    commute_of_conj_mem_rootSet_of_centralizes' h hc hs ha hx hax hoddax hx1
      (fun a' ha' => hua a' (rootSet_subset_rootGroup D a ha'))
      (hgx _ (Subgroup.mem_zpowers _)) hv
  have hcen : ∀ y : G, Commute (h₀ ^ m) y := by
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({h₀ ^ m} : Set G) := by
      rw [← htop]
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (huT' v hv).symm.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hux v hv).symm.eq
    exact fun y => (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top y))).symm
  obtain ⟨L, hL₀, hLne⟩ : ∃ L ∈ rootLines D a,
      L ∉ ({rootGroup D a ⊔ rootGroup D d, rootGroup D a ⊔ rootGroup D d'} :
        Set (Subgroup G)) := by
    by_contra hall
    push Not at hall
    have : (rootLines D a).ncard ≤ 2 := by
      calc (rootLines D a).ncard ≤
            ({rootGroup D a ⊔ rootGroup D d, rootGroup D a ⊔ rootGroup D d'} :
              Set (Subgroup G)).ncard := Set.ncard_le_ncard hall (Set.toFinite _)
        _ ≤ ({rootGroup D a ⊔ rootGroup D d'} : Set (Subgroup G)).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hLne
  have h1 := hL.pow_eq_one_of_torus ha hd had hadD hdT hT ⟨d', hd', had', had'D, hd'T, rfl⟩
    hne.symm hh hord hhT hhT' htrans hL₀ hLne.1 hLne.2 (j := m)
    (map_conj_eq_self_of_commute fun v _ => hcen v)
  rw [← orderOf_eq_one_iff, horder_u] at h1
  exact hp.one_lt.ne' h1

end CFSG.Timmesfeld.Bridge
