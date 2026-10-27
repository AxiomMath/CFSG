module

public import CFSG.Timmesfeld.Bridge.RootClosureLocal
public import CFSG.Timmesfeld.Bridge.RootClosureRankOne
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.BenderSuzuki

section Dihedral

variable {K : Type*} [Group K]

theorem eq_of_commute_of_closure_pair {s t : K} (hs : s * s = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (s * t))) (htop : Subgroup.closure {s, t} = ⊤) {p q : K}
    (hp : p * p = 1) (hq : q * q = 1) (hpq : Commute p q) : p = 1 ∨ q = 1 ∨ p = q := by
  set H := Subgroup.zpowers (s * t)
  have hrot : ∀ g ∈ H, g * g = 1 → g = 1 := by
    intro g hg hg2
    have h1 : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_of_mem_zpowers hg)
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hg2])
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 h1) h2)
  have hmem : ∀ g : K, g ∈ H ∨ s * g ∈ H := fun g =>
    mem_zpowers_or_of_mem_closure hs ht (htop ▸ Subgroup.mem_top g)
  rcases hmem p with hpH | hpH
  · exact Or.inl (hrot p hpH hp)
  rcases hmem q with hqH | hqH
  · exact Or.inr (Or.inl (hrot q hqH hq))
  right; right
  have hpqH : p * q ∈ H := by
    have : p * q = (s * p)⁻¹ * (s * q) := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hp, inv_eq_of_mul_eq_one_right hs,
        show p * s * (s * q) = p * (s * s) * q by group, hs, mul_one]
    rw [this]
    exact H.mul_mem (H.inv_mem hpH) hqH
  have h1 := hrot _ hpqH (by
    rw [show p * q * (p * q) = p * (q * p) * q by group, ← hpq.eq,
      show p * (p * q) * q = (p * p) * (q * q) by group, hp, hq, one_mul])
  rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hq]

end Dihedral

section Bender

variable {K : Type*} [Group K] [Finite K]

theorem conj_eq_of_conj_eq (hK : IsBenderGroup K) (Q : Sylow 2 K) {h u w : K}
    (hh : h ∈ Subgroup.normalizer (Q : Set K)) (hu : u ∈ Q ∧ ∀ q ∈ Q, Commute q u)
    (hu1 : u ≠ 1) (hfix : h * u * h⁻¹ = u) (hw : w ∈ Q ∧ ∀ q ∈ Q, Commute q w) :
    h * w * h⁻¹ = w := by
  by_cases hw1 : w = 1
  · rw [hw1, mul_one, mul_inv_cancel]
  obtain ⟨n, hn, hnw⟩ := Asc72.IsBenderGroup.exists_normalizer_conj hK Q hu hu1 hw hw1
  obtain ⟨q, k, hB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel hK
  obtain ⟨-, ⟨T, hTc, -, -, hsup⟩, -⟩ := hB Q
  have hsup' : ((Q : Subgroup K) ⊔ T : Subgroup K) = Subgroup.normalizer (Q : Set K) := hsup
  have hTN : T ≤ Subgroup.normalizer (Q : Set K) := hsup' ▸ le_sup_right
  have hdec : ∀ g ∈ Subgroup.normalizer (Q : Set K), ∃ p ∈ (Q : Subgroup K), ∃ t ∈ T,
      p * t = g := by
    intro g hg
    have hg' : g ∈ ((Q : Subgroup K) ⊔ T : Subgroup K) := hsup' ▸ hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN] at hg'
    obtain ⟨p, hp, t, ht, rfl⟩ := hg'
    exact ⟨p, hp, t, ht, rfl⟩
  have hTcomm : ∀ t₁ ∈ T, ∀ t₂ ∈ T, Commute t₁ t₂ := by
    intro t₁ ht₁ t₂ ht₂
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨t₁, ht₁⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨t₂, ht₂⟩)
    have h1 : (g : K) ^ i = t₁ := by simpa using congrArg Subtype.val hi
    have h2 : (g : K) ^ j = t₂ := by simpa using congrArg Subtype.val hj
    rw [← h1, ← h2]
    exact Commute.zpow_zpow_self (g : K) i j
  have hQfix : ∀ p ∈ (Q : Subgroup K), ∀ v : K, (∀ q ∈ Q, Commute q v) → p * v * p⁻¹ = v :=
    fun p hp v hv => by rw [(hv p hp).eq, mul_inv_cancel_right]
  have hTcent : ∀ t ∈ T, ∀ v : K, (∀ q ∈ Q, Commute q v) → ∀ q ∈ Q, Commute q (t * v * t⁻¹) := by
    intro t ht v hv q hq
    have htq : t⁻¹ * q * t ∈ (Q : Subgroup K) := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hTN ht)) q).1 hq
      simpa using this
    have h1 := hv _ htq
    have h2 := h1.conj t
    simpa [mul_assoc] using h2
  obtain ⟨p₁, hp₁, t₁, ht₁, rfl⟩ := hdec h hh
  obtain ⟨p₂, hp₂, t₂, ht₂, rfl⟩ := hdec n hn
  have ht₁u : t₁ * u * t₁⁻¹ = u := by
    have h1 := hfix
    rw [mul_inv_rev, show p₁ * t₁ * u * (t₁⁻¹ * p₁⁻¹) = p₁ * (t₁ * u * t₁⁻¹) * p₁⁻¹ by group,
      hQfix p₁ hp₁ _ (hTcent t₁ ht₁ u hu.2)] at h1
    exact h1
  have hwt : w = t₂ * u * t₂⁻¹ := by
    rw [← hnw, mul_inv_rev, show p₂ * t₂ * u * (t₂⁻¹ * p₂⁻¹) = p₂ * (t₂ * u * t₂⁻¹) * p₂⁻¹ by group,
      hQfix p₂ hp₂ _ (hTcent t₂ ht₂ u hu.2)]
  rw [hwt, mul_inv_rev,
    show p₁ * t₁ * (t₂ * u * t₂⁻¹) * (t₁⁻¹ * p₁⁻¹) = p₁ * (t₁ * t₂ * u * (t₁ * t₂)⁻¹) * p₁⁻¹ by
      group,
    (hTcomm t₁ ht₁ t₂ ht₂).eq,
    show t₂ * t₁ * u * (t₂ * t₁)⁻¹ = t₂ * (t₁ * u * t₁⁻¹) * t₂⁻¹ by group, ht₁u,
    hQfix p₁ hp₁ _ (hTcent t₂ ht₂ u hu.2)]

theorem mem_normalizer_of_conj_mem (hK : IsBenderGroup K) (Q : Sylow 2 K) {h t : K}
    (ht : t ∈ Q) (ht1 : t ≠ 1) (hht : h * t * h⁻¹ ∈ Q) :
    h ∈ Subgroup.normalizer (Q : Set K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Q : Set K) with hM
  have hQM : (Q : Subgroup K) ≤ M := Subgroup.le_normalizer
  by_contra hnot
  have hodd := (Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK Q).2.2 h hnot
  have hsmem : h * t * h⁻¹ ∈ M ⊓ M.map (MulAut.conj h).toMonoidHom :=
    ⟨hQM hht, ⟨t, hQM ht, rfl⟩⟩
  have hs1 : h * t * h⁻¹ ≠ 1 := fun h1 => ht1 (by
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1)
  have h2 : 2 ∣ orderOf (h * t * h⁻¹) := by
    have := Q.isPGroup'.dvd_orderOf (g := ⟨h * t * h⁻¹, hht⟩) (fun h1 => hs1 (by
      simpa using congrArg Subtype.val h1))
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf (h * t * h⁻¹) ∣
      Nat.card ((M ⊓ M.map (MulAut.conj h).toMonoidHom : Subgroup K)) := by
    rw [← Subgroup.orderOf_mk _ hsmem]
    exact orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans h3))

end Bender

section Count

variable {G : Type} [Group G] {D : Set G}

theorem rootGroup_le_closure_insert (D : Set G) (d x : G) :
    rootGroup D d ≤ Subgroup.closure (insert x (rootSet D d)) :=
  Subgroup.closure_mono (Set.subset_insert x _)

theorem false_of_isBenderGroup (h : Hyp G D) {Y : Subgroup G} {d x : G} (hd : d ∈ D)
    (hdY : d ∈ Y) (hx : x ∈ D) (hxY : x ∈ Y) (hdx : ¬ Commute d x)
    (hodd : Odd (orderOf (d * x))) (hK : IsBenderGroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) {u : G}
    (hu : u ∈ rootGroup D d) (huY : u ∈ Y) (huT : u ∉ rootSet D d)
    (hu1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨u, huY⟩ ≠ 1)
    (hplus : ∀ t ∈ rootSet D d, t ∈ Y → ∀ g ∈ rootGroup D d, g ∈ Y → g ∉ rootSet D d →
      t * g ∈ rootSet D d) :
    False := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  set K := ↥Y ⧸ CFSG.pCore 2 ↥Y
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have hdT := mem_rootSet_self hd
  have hdc : d ∈ classIn Y x := mem_classIn_of_odd hD hx hd hxY hdY (by
    rw [orderOf_mul_comm_eq]
    exact hodd)
  have hconj : ∀ t ∈ rootSet D d, t ∈ Y → ∃ n ∈ Y, n * d * n⁻¹ = t := by
    intro t ht htY
    have h1 : t ∈ classIn Y d := by
      rw [classIn_eq_of_mem hdc]
      exact mem_classIn_of_odd hD hx ht.1 hxY htY (by
        rw [orderOf_mul_comm_eq]
        exact (odd_orderOf_mul_iff_of_mem_rootSet hD hd ht hx hdx).2 hodd)
    obtain ⟨n, hn, rfl⟩ := h1
    exact ⟨n, hn, rfl⟩
  have hnT : ∀ n t : G, t ∈ rootSet D d → n * d * n⁻¹ = t →
      ∀ s : G, s ∈ rootSet D d ↔ n * s * n⁻¹ ∈ rootSet D d := by
    intro n t ht hnt s
    have e := rootSet_conj hclass n d
    rw [hnt, rootSet_eq_of_mem ht] at e
    constructor
    · intro hs
      rw [e]
      exact ⟨s, hs, rfl⟩
    · intro hs
      rw [e] at hs
      obtain ⟨s', hs', hss'⟩ := hs
      have : s' = s := by simpa using hss'
      rwa [← this]
  have hnE : ∀ n t : G, t ∈ rootSet D d → n * d * n⁻¹ = t →
      ∀ g ∈ rootGroup D d, n * g * n⁻¹ ∈ rootGroup D d := by
    intro n t ht hnt g hg
    have e := rootGroup_conj hclass n d
    rw [hnt, show rootGroup D t = rootGroup D d by rw [rootGroup, rootGroup,
      rootSet_eq_of_mem ht]] at e
    rw [e]
    exact ⟨g, hg, rfl⟩
  have hsq : ∀ g ∈ rootGroup D d, ∀ hg : g ∈ Y, π ⟨g, hg⟩ * π ⟨g, hg⟩ = 1 := by
    intro g hg hgY
    rw [← map_mul, show (⟨g, hgY⟩ : Y) * ⟨g, hgY⟩ = 1 from
      Subtype.ext (mul_self_eq_one_of_mem_rootGroup hD hd hg), map_one]
  set B : Subgroup K := ((rootGroup D d).subgroupOf Y).map π with hB
  have hB2 : IsPGroup 2 B := by
    rintro ⟨y, ⟨g, hg, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [sq]
    exact hsq g hg g.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hBQ⟩ := hB2.exists_le_sylow
  have hmemB : ∀ g ∈ rootGroup D d, ∀ hg : g ∈ Y, π ⟨g, hg⟩ ∈ B := fun g hg hgY =>
    ⟨⟨g, hgY⟩, hg, rfl⟩
  have hcent : ∀ g ∈ rootGroup D d, ∀ hg : g ∈ Y,
      π ⟨g, hg⟩ ∈ Q ∧ ∀ q ∈ Q, Commute q (π ⟨g, hg⟩) := by
    intro g hg hgY
    have hQ := hBQ (hmemB g hg hgY)
    exact ⟨hQ, fun q hq =>
      (Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hQ (hsq g hg hgY) q hq).symm⟩
  have hdE : d ∈ rootGroup D d := rootSet_subset_rootGroup D d hdT
  set db := π ⟨d, hdY⟩ with hdb
  have hdb1 : db ≠ 1 := by
    intro h1
    have hdx' : π ((⟨d, hdY⟩ : Y) * ⟨x, hxY⟩) = π ⟨x, hxY⟩ := by
      rw [map_mul, ← hdb, h1, one_mul]
    have ho := orderOf_mk_eq_of_odd (CFSG.pCore_isPGroup (G := ↥Y) (p := 2))
      (g := (⟨d, hdY⟩ : Y) * ⟨x, hxY⟩) (by rw [← Subgroup.orderOf_coe]; exact hodd)
    rw [← hπ, hdx', ← Subgroup.orderOf_coe] at ho
    have h2 : orderOf (π ⟨x, hxY⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [sq, ← map_mul, show (⟨x, hxY⟩ : Y) * ⟨x, hxY⟩ = 1 from
        Subtype.ext (hD.mul_self_eq_one hx), map_one])
    rw [ho] at h2
    have h3 : orderOf (d * x) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 hodd) h2
    apply hdx
    rw [orderOf_eq_one_iff] at h3
    rw [eq_inv_of_mul_eq_one_left h3]
    exact (Commute.refl x).inv_left
  set ub := π ⟨u, huY⟩ with hub
  have hkey : ∀ t₁ (ht₁ : t₁ ∈ rootSet D d) (ht₁Y : t₁ ∈ Y) t₂ (ht₂ : t₂ ∈ rootSet D d)
      (ht₂Y : t₂ ∈ Y) n₁ (hn₁ : n₁ ∈ Y) n₂ (hn₂ : n₂ ∈ Y), n₁ * d * n₁⁻¹ = t₁ →
      n₂ * d * n₂⁻¹ = t₂ →
      π ⟨n₁, hn₁⟩ * ub * (π ⟨n₁, hn₁⟩)⁻¹ = π ⟨n₂, hn₂⟩ * ub * (π ⟨n₂, hn₂⟩)⁻¹ →
      π ⟨t₁, ht₁Y⟩ = π ⟨t₂, ht₂Y⟩ := by
    intro t₁ ht₁ ht₁Y t₂ ht₂ ht₂Y n₁ hn₁ n₂ hn₂ h₁ h₂ heq
    set k := (π ⟨n₂, hn₂⟩)⁻¹ * π ⟨n₁, hn₁⟩ with hk
    have hkfix : k * ub * k⁻¹ = ub := by
      rw [hk, mul_inv_rev, inv_inv, show (π ⟨n₂, hn₂⟩)⁻¹ * π ⟨n₁, hn₁⟩ * ub *
        ((π ⟨n₁, hn₁⟩)⁻¹ * π ⟨n₂, hn₂⟩) = (π ⟨n₂, hn₂⟩)⁻¹ *
          (π ⟨n₁, hn₁⟩ * ub * (π ⟨n₁, hn₁⟩)⁻¹) * π ⟨n₂, hn₂⟩ by group, heq]
      group
    have hs : n₂⁻¹ * t₁ * n₂ ∈ rootSet D d := by
      rw [hnT n₂ t₂ ht₂ h₂]
      simpa [mul_assoc] using ht₁
    have hsY : n₂⁻¹ * t₁ * n₂ ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hn₂) ht₁Y) hn₂
    have hkd : k * db * k⁻¹ = π ⟨n₂⁻¹ * t₁ * n₂, hsY⟩ := by
      rw [hk, hdb, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h₁]
      group
    have hkQ : k ∈ Subgroup.normalizer (Q : Set K) := by
      refine mem_normalizer_of_conj_mem hK Q (hcent d hdE hdY).1 hdb1 ?_
      rw [hkd]
      exact (hcent _ (rootSet_subset_rootGroup D d hs) _).1
    have hkd' := conj_eq_of_conj_eq hK Q hkQ (hcent u hu huY) hu1 hkfix (hcent d hdE hdY)
    rw [hkd] at hkd'
    have e₁ : (⟨t₁, ht₁Y⟩ : Y) = ⟨n₂, hn₂⟩ * ⟨n₂⁻¹ * t₁ * n₂, hsY⟩ * ⟨n₂, hn₂⟩⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have e₂ : (⟨t₂, ht₂Y⟩ : Y) = ⟨n₂, hn₂⟩ * ⟨d, hdY⟩ * ⟨n₂, hn₂⟩⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact h₂.symm)
    rw [e₁, e₂, map_mul, map_mul, map_mul, map_mul, hkd']
  set Ed : Set K := (fun g : Y => π g) '' {g : Y | (g : G) ∈ rootSet D d} with hEd
  set Ub : Set K := (fun g : Y => π g) ''
    {g : Y | (g : G) ∈ rootGroup D d ∧ (g : G) ∉ rootSet D d} with hUb
  have h1 : Ub.ncard ≤ Ed.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun v => db * v) ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨g, ⟨hgE, hgT⟩, rfl⟩
      refine ⟨⟨d, hdY⟩ * g, ?_, by simp [hdb]⟩
      show d * (g : G) ∈ rootSet D d
      exact hplus d hdT hdY g hgE g.2 hgT
    · intro v₁ _ v₂ _ h12
      exact mul_left_cancel h12
  have hex : ∀ e ∈ Ed, ∃ v, v ∈ Ub \ {1} ∧ ∃ t, ∃ ht : t ∈ rootSet D d, ∃ htY : t ∈ Y, ∃ n,
      ∃ hn : n ∈ Y, n * d * n⁻¹ = t ∧ π ⟨t, htY⟩ = e ∧
        v = π ⟨n, hn⟩ * ub * (π ⟨n, hn⟩)⁻¹ := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨n, hn, hnt⟩ := hconj g hg g.2
    refine ⟨π ⟨n, hn⟩ * ub * (π ⟨n, hn⟩)⁻¹, ⟨?_, ?_⟩, g, hg, g.2, n, hn, hnt, rfl, rfl⟩
    · refine ⟨⟨n, hn⟩ * ⟨u, huY⟩ * ⟨n, hn⟩⁻¹, ⟨?_, ?_⟩, by simp only [map_mul, map_inv, hub]⟩
      · exact hnE n g hg hnt u hu
      · intro hmem
        exact huT ((hnT n g hg hnt u).2 hmem)
    · intro h1'
      apply hu1
      have h1'' := Set.mem_singleton_iff.1 h1'
      rw [mul_inv_eq_one, mul_eq_left] at h1''
      exact h1''
  choose! f hf using hex
  have h2 : Ed.ncard ≤ (Ub \ {1}).ncard := by
    refine Set.ncard_le_ncard_of_injOn f (fun e he => (hf e he).1) ?_ (Set.toFinite _)
    intro e₁ he₁ e₂ he₂ h12
    obtain ⟨-, t₁, ht₁, ht₁Y, n₁, hn₁, hnt₁, he₁', hv₁⟩ := hf e₁ he₁
    obtain ⟨-, t₂, ht₂, ht₂Y, n₂, hn₂, hnt₂, he₂', hv₂⟩ := hf e₂ he₂
    rw [← he₁', ← he₂']
    exact hkey t₁ ht₁ ht₁Y t₂ ht₂ ht₂Y n₁ hn₁ n₂ hn₂ hnt₁ hnt₂ (by rw [← hv₁, ← hv₂, h12])
  have h1U : (1 : K) ∈ Ub :=
    ⟨1, ⟨(rootGroup D d).one_mem, fun h1' => hD.ne_one h1'.1 rfl⟩, map_one π⟩
  have h3 := Set.ncard_sdiff_singleton_of_mem h1U
  have h4 : 0 < Ub.ncard := Set.ncard_pos (Set.toFinite Ub) |>.2 ⟨1, h1U⟩
  omega

theorem false_of_plus (h120 : RootGenQuotientStmt) (h : Hyp G D) (IH : RootIHStruct G)
    {d a b x : G} (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) (hab : a ≠ b)
    (hnD : a * b ∉ D) (hx : x ∈ D) (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x)))
    {m : ℕ} (hm : Odd m) (hxu : orderOf (x * (a * b)) = 2 * m)
    (hplus : ∀ t ∈ rootSet D d, ∀ g ∈ rootGroup D d, g ∉ rootSet D d → t * g ∈ rootSet D d) :
    False := by
  have := h.finite
  have hD := h.root
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact orderOf_mul_ne_two hD hd ha hb hab hx hdx hodd (by rw [hxu])
  set Y := Subgroup.closure (insert x (rootSet D d)) with hY
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  have hne := closure_ne_top_of_twoOdd h hd ha hb hab hx hdx hodd hm hxu (subset_refl _)
  have hshape := rankOneShape_quotient h120 h IH hd hx hdx hodd (subset_refl (rootSet D d))
    (mem_rootSet_self hd) hne
  have hxY : x ∈ Y := Subgroup.subset_closure (Set.mem_insert _ _)
  have hTY : ∀ t ∈ rootSet D d, t ∈ Y := fun t ht =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ ht)
  have hEY := rootGroup_le_closure_insert D d x
  have huE : a * b ∈ rootGroup D d := mul_mem_rootGroup ha hb
  have hu1 : π ⟨a * b, hEY huE⟩ ≠ 1 := by
    intro h1
    set w : Y := (⟨x, hxY⟩ * ⟨a * b, hEY huE⟩) ^ 2 with hw
    have hwo : orderOf w = m := by
      rw [hw, ← Subgroup.orderOf_coe]
      simp only [Subgroup.coe_pow, Subgroup.coe_mul]
      rw [orderOf_pow' _ two_ne_zero, hxu, Nat.gcd_mul_right_left m 2,
        Nat.mul_div_cancel_left _ two_pos]
    have hw1 : π w = 1 := by
      rw [hw, map_pow, map_mul, h1, mul_one, ← map_pow, sq,
        show (⟨x, hxY⟩ : Y) * ⟨x, hxY⟩ = 1 from Subtype.ext (hD.mul_self_eq_one hx), map_one]
    have := orderOf_mk_eq_of_odd (CFSG.pCore_isPGroup (G := Y) (p := 2)) (hwo ▸ hm)
    rw [← hπ, hw1, orderOf_one, hwo] at this
    exact hm1 this.symm
  rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨s, t, hst, hs, ht, ho⟩
  · exact false_of_isBenderGroup h hd (hTY d (mem_rootSet_self hd)) hx hxY hdx hodd
      (.isPSL2 n hn e) huE (hEY huE) (fun hmem => hnD hmem.1) hu1
      (fun t ht _ g hg _ hgT => hplus t ht g hg hgT)
  · exact false_of_isBenderGroup h hd (hTY d (mem_rootSet_self hd)) hx hxY hdx hodd
      (.isSuzuki n hn e) huE (hEY huE) (fun hmem => hnD hmem.1) hu1
      (fun t ht _ g hg _ hgT => hplus t ht g hg hgT)
  ·
    have hgen : Subgroup.closure (subClass Y x) = ⊤ := by
      refine closure_subClass_eq_top (Set.insert_subset (mem_classIn_self Y x) ?_) rfl
      intro t ht
      exact mem_classIn_of_odd hD hx ht.1 hxY (hTY t ht) (by
        rw [orderOf_mul_comm_eq]
        exact (odd_orderOf_mul_iff_of_mem_rootSet hD hd ht hx hdx).2 hodd)
    have hne1 : ∀ t (ht : t ∈ rootSet D d), π ⟨t, hTY t ht⟩ ≠ 1 := by
      intro t ht h1
      refine not_mem_pCore_of_mem_subClass hxY (hTY d (mem_rootSet_self hd)) hdx hodd hgen
        (mem_classIn_of_odd hD hx ht.1 hxY (hTY t ht) (by
          rw [orderOf_mul_comm_eq]
          exact (odd_orderOf_mul_iff_of_mem_rootSet hD hd ht hx hdx).2 hodd))
        ((QuotientGroup.eq_one_iff _).1 h1)
    have hsq : ∀ t (ht : t ∈ rootSet D d), π ⟨t, hTY t ht⟩ * π ⟨t, hTY t ht⟩ = 1 := by
      intro t ht
      rw [← map_mul, show (⟨t, hTY t ht⟩ : Y) * ⟨t, hTY t ht⟩ = 1 from
        Subtype.ext (hD.mul_self_eq_one ht.1), map_one]
    have hs2 : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs, sq] at this
    have ht2 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, sq] at this
    have hcY : Commute (⟨a, hTY a ha⟩ : Y) ⟨b, hTY b hb⟩ :=
      Subtype.ext (commute_of_mem_rootSet hd ha hb).eq
    have hcomm : Commute (π ⟨a, hTY a ha⟩) (π ⟨b, hTY b hb⟩) := hcY.map π
    rcases eq_of_commute_of_closure_pair hs2 ht2 ho hst (hsq a ha) (hsq b hb) hcomm with
      h1 | h1 | h1
    · exact hne1 a ha h1
    · exact hne1 b hb h1
    · apply hu1
      rw [show (⟨a * b, hEY huE⟩ : Y) = ⟨a, hTY a ha⟩ * ⟨b, hTY b hb⟩ from rfl, map_mul, ← h1,
        hsq a ha]

end Count

end CFSG.Timmesfeld.Bridge.RootClosure
