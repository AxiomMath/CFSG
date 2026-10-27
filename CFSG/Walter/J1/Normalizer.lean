module

public import CFSG.Walter.J1.Sylow

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem exists_two_of_card_four {V : Subgroup G} (hV : Nat.card V = 4) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  by_contra hcon
  push Not at hcon
  have hsub : (V : Set G) ⊆ {1} ∪ {x | x ∈ V ∧ x ≠ 1} := fun x hx => by
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr ⟨hx, hx1⟩
  obtain ⟨a, haV, ha1⟩ : ∃ a ∈ V, a ≠ 1 := by
    by_contra h0
    push Not at h0
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr h0
    rw [this, Subgroup.card_bot] at hV
    omega
  have hsub' : (V : Set G) ⊆ {1, a} := fun x hx => by
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (Set.mem_singleton_iff.mpr (hcon a haV x hx ha1 hx1).symm)
  have := Set.ncard_le_ncard hsub' (Set.toFinite _)
  rw [Set.ncard_pair (Ne.symm ha1), ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hV] at this
  omega

theorem mem_of_card_four {V : Subgroup G} (hVF : V ≤ h.F) (hV : Nat.card V = 4) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {x : G} (hx : x ∈ V) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have hab1 : a * b ≠ 1 := by
    intro h1
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h4 : a ^ 4 = 1 := by
      have := pow_card_eq_one' (G := V) (x := ⟨a, ha⟩)
      rw [hV] at this
      have := congrArg Subtype.val this
      simpa using this
    have hsq : a * a = 1 := by
      have h2 := A5Sub.sq_eq_one_of_pow h.iso (hVF ha) (n := 2) (by norm_num; exact h4)
      rwa [pow_two] at h2
    apply hab
    rw [hb', inv_eq_of_mul_eq_one_right hsq]
  have haab : a * b ≠ a := fun h1 => hb1 (by simpa using h1)
  have hbab : a * b ≠ b := fun h1 => ha1 (by simpa using h1)
  have hsub : ({1, a, b, a * b} : Set G) ⊆ V := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact V.one_mem
    · exact ha
    · exact hb
    · exact V.mul_mem ha hb
  have hcard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    have n1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1⟩
    have n2 : a ∉ ({b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, Ne.symm haab⟩
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_pair (Ne.symm hbab)]
  have heq : ({1, a, b, a * b} : Set G) = V := by
    apply Set.eq_of_subset_of_ncard_le hsub
    · rw [hcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hV]
  have hx' : x ∈ (V : Set G) := hx
  rw [← heq] at hx'
  rcases hx' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem exists_three_normalizer {V : Subgroup G} (hVF : V ≤ h.F) (hV : Nat.card V = 4) :
    ∃ c ∈ h.F, orderOf c = 3 ∧ c ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ v ∈ V, c * v * c⁻¹ = v → v = 1 := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_of_card_four hV
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => A5Sub.sq_eq_one_of_pow h.iso (hVF hx) (n := 2)
    (by
      have := pow_card_eq_one' (G := V) (x := ⟨x, hx⟩)
      rw [hV] at this
      have := congrArg Subtype.val this
      norm_num
      simpa using this)
  have hcomm : a * b = b * a := by
    have h1 := hsq _ (V.mul_mem ha hb)
    have ha2 := hsq a ha
    have hb2 := hsq b hb
    rw [pow_two] at h1 ha2 hb2
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right ha2,
      inv_eq_of_mul_eq_one_right hb2]
  obtain ⟨c, hcF, hc3, hca, hcb⟩ := A5Sub.four_group h.iso (hVF ha) (hVF hb) (hsq a ha)
    (hsq b hb) ha1 hb1 hab hcomm
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hab
    simpa using hca
  have hcab : c * (a * b) * c⁻¹ = a := by
    rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group, hca, hcb]
    have hb2 := hsq b hb
    rw [pow_two] at hb2
    rw [hcomm, ← mul_assoc, hb2, one_mul]
  have hcN : c ∈ Subgroup.normalizer (V : Set G) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rcases h.mem_of_card_four hVF hV ha hb ha1 hb1 hab hx with rfl | rfl | rfl | rfl
    · simp
    · rw [hca]; exact hb
    · rw [hcb]; exact V.mul_mem ha hb
    · rw [hcab]; exact ha
  refine ⟨c, hcF, orderOf_eq_prime hc3 hc1, hcN, fun v hv hcv => ?_⟩
  rcases h.mem_of_card_four hVF hV ha hb ha1 hb1 hab hv with h1 | h1 | h1 | h1
  · exact h1
  · rw [h1] at hcv
    exact absurd (hca.symm.trans hcv) (Ne.symm hab)
  · exfalso
    rw [h1, hcb] at hcv
    apply ha1
    have := congrArg (· * b⁻¹) hcv
    simpa using this
  · exfalso
    rw [h1, hcab] at hcv
    apply hb1
    have := congrArg (a⁻¹ * ·) hcv
    simpa using this.symm

theorem card_normalizer_F {V : Subgroup G} (hVF : V ≤ h.F) (hV : Nat.card V = 4) :
    Nat.card (h.F ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) = 12 := by
  set N₀ := h.F ⊓ Subgroup.normalizer (V : Set G)
  have hVN₀ : V ≤ N₀ := le_inf hVF Subgroup.le_normalizer
  obtain ⟨c, hcF, hc3, hcN, -⟩ := h.exists_three_normalizer hVF hV
  have h4 : 4 ∣ Nat.card N₀ := hV ▸ Subgroup.card_dvd_of_le hVN₀
  have h3 : 3 ∣ Nat.card N₀ := hc3 ▸ Subgroup.orderOf_dvd_natCard N₀ ⟨hcF, hcN⟩
  have h60 : Nat.card N₀ ∣ 60 := h.card_F ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card N₀ ≠ 60 := by
    intro h60'
    have hN₀F : N₀ = h.F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h60', h.card_F])
    have : (V.subgroupOf h.F).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVF]
      rw [← hN₀F]
      exact inf_le_right
    have hs := A5Sub.isSimpleGroup h.iso
    rcases this.eq_bot_or_eq_top with hb | ht
    · have : Nat.card (V.subgroupOf h.F) = 1 := by rw [hb, Subgroup.card_bot]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVF).toEquiv, hV] at this
      omega
    · have : Nat.card (V.subgroupOf h.F) = 60 := by
        rw [ht, Subgroup.card_top, h.card_F]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVF).toEquiv, hV] at this
      omega
  have h12 : 12 ∣ Nat.card N₀ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  obtain ⟨k, hk⟩ := h12
  have hk5 : k ∣ 5 := by
    rw [hk] at h60
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 12)).mp (by simpa using h60)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hk5 with rfl | rfl
  · rw [hk]
  · rw [hk] at hne
    omega

theorem mem_normalizer_sylow_of_mem_F (S : Sylow 2 G) (htS : h.t ∈ S) {y : G} (hyF : y ∈ h.F)
    (hyN : y ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun s hs => ?_
  have hc := h.commute_of_mem_F hyF
  rcases h.mem_centralizer_t.mp (h.sylow_le_centralizer S htS hs) with hsF | hsF
  · exact ((Subgroup.mem_normalizer_iff.mp hyN s).mp ⟨hs, hsF⟩).1
  · have h1 := ((Subgroup.mem_normalizer_iff.mp hyN _).mp ⟨(S : Subgroup G).mul_mem htS hs,
      hsF⟩).1
    have : y * s * y⁻¹ = h.t * (y * (h.t * s) * y⁻¹) := by
      calc y * s * y⁻¹ = y * (h.t * (h.t * s)) * y⁻¹ := by
            rw [← mul_assoc h.t, h.t_mul_t, one_mul]
        _ = (y * h.t) * (h.t * s) * y⁻¹ := by group
        _ = h.t * (y * (h.t * s) * y⁻¹) := by rw [hc]; group
    rw [this]
    exact (S : Subgroup G).mul_mem htS h1

theorem mem_normalizer_inf_F_of_mem_F (S : Sylow 2 G) {y : G} (hyF : y ∈ h.F)
    (hyN : y ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ h.F : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp hyN x).mp hx.1,
      h.F.mul_mem (h.F.mul_mem hyF hx.2) (h.F.inv_mem hyF)⟩

theorem card_normalizer_inf_centralizer (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({h.t} : Set G) : Subgroup G) = 24 := by
  set V := (S : Subgroup G) ⊓ h.F
  set N₀ := h.F ⊓ Subgroup.normalizer (V : Set G)
  set M := Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ({h.t} : Set G)
  have hN₀ : Nat.card N₀ = 12 := h.card_normalizer_F inf_le_right (h.card_inf_F S htS)
  have hN₀M : N₀ ≤ M := fun y hy =>
    ⟨h.mem_normalizer_sylow_of_mem_F S htS hy.1 hy.2, h.le_centralizer hy.1⟩
  have htN : h.t ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.le_normalizer htS
  have hidx : N₀.relIndex M = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨h.t, htN, h.t_mem_centralizer⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hbN := b.2.1
    have hbC := b.2.2
    by_cases hbF : (b : G) ∈ h.F
    · refine Or.inr ⟨⟨hbF, h.mem_normalizer_inf_F_of_mem_F S hbF hbN⟩, fun hbt => h.t_not_mem ?_⟩
      have : h.t = (b : G)⁻¹ * (b * h.t) := by group
      rw [this]
      exact h.F.mul_mem (h.F.inv_mem hbF) hbt.1
    · have hbtF : (b : G) * h.t ∈ h.F := by
        rcases h.mem_centralizer_t.mp hbC with hb' | hb'
        · exact absurd hb' hbF
        · rw [h.commute_of_mem hbC]
          exact hb'
      refine Or.inl ⟨⟨hbtF, h.mem_normalizer_inf_F_of_mem_F S hbtF
        (Subgroup.mul_mem _ hbN htN)⟩, fun hb' => hbF hb'.1⟩
  have h1 := Subgroup.relIndex_mul_card N₀ M
  rw [hidx, inf_eq_left.mpr hN₀M, hN₀] at h1
  omega

theorem card_normalizer_sylow (S : Sylow 2 G) (htS : h.t ∈ S) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G)) = 168 := by
  classical
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  let := conjAct N S le_rfl
  set t' : (S : Subgroup G) := ⟨h.t, htS⟩
  have hstab : MulAction.stabilizer N t' =
      (Subgroup.centralizer ({h.t} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hn
      have := congrArg Subtype.val hn
      change (n : G) * h.t * (n : G)⁻¹ = h.t at this
      calc (n : G) * h.t = ((n : G) * h.t * (n : G)⁻¹) * n := by group
        _ = h.t * n := by rw [this]
    · intro hn
      apply Subtype.ext
      change (n : G) * h.t * (n : G)⁻¹ = h.t
      rw [hn, mul_inv_cancel_right]
  have horbit : MulAction.orbit N t' = {z | z ≠ 1} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩ h1
      have := congrArg Subtype.val h1
      change (n : G) * h.t * (n : G)⁻¹ = 1 at this
      apply h.t_ne_one
      have := congrArg (fun w => (n : G)⁻¹ * w * n) this
      simpa [mul_assoc] using this
    · intro hz
      obtain ⟨n, hn, hnz⟩ := h.exists_conj_of_mem_sylow S htS htS h.t_ne_one z.2
        (fun h0 => hz (Subtype.ext h0))
      exact ⟨⟨n, hn⟩, Subtype.ext hnz⟩
  have h7 : (MulAction.orbit N t').ncard = 7 := by
    have : ({z | z ≠ 1} : Set (S : Subgroup G)) = (Set.univ : Set (S : Subgroup G)) \ {1} := by
      ext
      simp
    rw [horbit, this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      h.card_sylow S htS]
  have hidx : (MulAction.stabilizer N t').index = 7 := by
    rw [MulAction.index_stabilizer, h7]
  have hstabcard : Nat.card (MulAction.stabilizer N t') = 24 := by
    rw [hstab, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm,
      h.card_normalizer_inf_centralizer S htS]
  have := (MulAction.stabilizer N t').card_mul_index
  rw [hstabcard, hidx] at this
  exact this.symm

theorem exists_not_mem_sylow_commutator (S : Sylow 2 G) (htS : h.t ∈ S) :
    ∃ a ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      ∃ b ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), (a * b)⁻¹ * (b * a) ∉ S := by
  by_contra hcon
  push Not at hcon
  have hab := h.abelian_sylow S
  obtain ⟨z, hzF, hz3, hzN, -⟩ := h.exists_three_normalizer
    (inf_le_right : (S : Subgroup G) ⊓ h.F ≤ h.F) (h.card_inf_F S htS)
  have hzNS : z ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    h.mem_normalizer_sylow_of_mem_F S htS hzF hzN
  have hzt : z * h.t = h.t * z := h.commute_of_mem_F hzF
  have hzC : z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, mul_one]
    obtain ⟨n, hn, rfl⟩ := h.exists_conj_of_mem_sylow S htS htS h.t_ne_one hs hs1
    set c : G := (n * z)⁻¹ * (z * n)
    have hcS : c ∈ (S : Subgroup G) := hcon n hn z hzNS
    have hzn : z * n = n * z * c := by simp only [c]; group
    have hct : c * h.t = h.t * c :=
      congrArg Subtype.val (hab.is_comm.comm ⟨c, hcS⟩ ⟨h.t, htS⟩)
    symm
    calc z * (n * h.t * n⁻¹) = (z * n) * h.t * n⁻¹ := by group
      _ = (n * z * c) * h.t * n⁻¹ := by rw [hzn]
      _ = n * z * (c * h.t) * n⁻¹ := by group
      _ = n * z * (h.t * c) * n⁻¹ := by rw [hct]
      _ = n * (z * h.t) * c * n⁻¹ := by group
      _ = n * (h.t * z) * c * n⁻¹ := by rw [hzt]
      _ = n * h.t * n⁻¹ * (n * z * c * n⁻¹) := by group
      _ = n * h.t * n⁻¹ * (z * n * n⁻¹) := by rw [← hzn]
      _ = n * h.t * n⁻¹ * z := by group
  have : z ∈ (S : Subgroup G) := by
    rw [← h.centralizer_sylow S htS]
    exact hzC
  have h8 : orderOf z ∣ 8 := h.card_sylow S htS ▸ Subgroup.orderOf_dvd_natCard _ this
  rw [hz3] at h8
  omega

end JankoHyp

end CFSG.Walter.J1
