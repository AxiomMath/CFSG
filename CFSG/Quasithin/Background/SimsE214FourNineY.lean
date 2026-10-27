module

public import CFSG.Quasithin.Background.SimsE214FourSz

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214F

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_of_mem_normalizer_of_pow {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {x : Y}
    (hxN : x ∈ Subgroup.normalizer (S : Set Y)) {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x ∈ S := by
  have hR : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ S) := IsPGroup.to_sup_of_normal_right'
    (E2.isPGroup_zpowers_of_pow hxn) hS.2.1 (Subgroup.zpowers_le.mpr hxN)
  exact le_of_isSylowTwoOf_top hS le_sup_right hR (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem conj_mem_center_iff {S : Subgroup Y} {c₁ c₂ : Y}
    (h : ∀ z, c₁ * z * c₁⁻¹ ∈ S ↔ c₂ * z * c₂⁻¹ ∈ S) (z : Y) :
    c₁ * z * c₁⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set Y) ↔
      c₂ * z * c₂⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set Y) := by
  have key : ∀ c₁ c₂ : Y, (∀ z, c₁ * z * c₁⁻¹ ∈ S ↔ c₂ * z * c₂⁻¹ ∈ S) → ∀ z,
      c₁ * z * c₁⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set Y) →
        c₂ * z * c₂⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set Y) := by
    rintro c₁ c₂ h z ⟨hz1, hz2⟩
    refine ⟨(h z).mp hz1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have e1 : c₂ * (c₂⁻¹ * s * c₂) * c₂⁻¹ = s := by group
    have hs' : c₁ * (c₂⁻¹ * s * c₂) * c₁⁻¹ ∈ S := (h _).mpr (by rw [e1]; exact hs)
    have h2 := (conj_commute_iff (c₂⁻¹ * s * c₂) z c₁).mp
      (Subgroup.mem_centralizer_iff.mp hz2 _ hs')
    have h3 := (conj_commute_iff (c₂⁻¹ * s * c₂) z c₂).mpr h2
    rw [e1] at h3
    exact h3
  exact ⟨key c₁ c₂ h z, key c₂ c₁ (fun z => (h z).symm) z⟩

theorem eq_one_of_mem_inf {S : Subgroup Y} {h z : Y}
    (hgen : (S ⊓ Subgroup.centralizer (S : Set Y)) ⊔
      (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom = ⊤)
    (hcen : Subgroup.center Y = ⊥) (hzS : z ∈ S) (hzS' : h * z * h⁻¹ ∈ S) : z = 1 := by
  have hWz : S ⊓ Subgroup.centralizer (S : Set Y) ≤ Subgroup.centralizer ({z} : Set Y) :=
    fun w hw => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hw.2 z hzS).symm
  have hW'z : (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({z} : Set Y) := fun w hw => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((conj_commute_iff z w h).mp (Subgroup.mem_centralizer_iff.mp hw.2 _ hzS')).symm
  have hzc : z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro u
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hWz hW'z) (hgen ▸ Subgroup.mem_top u))
  rw [hcen] at hzc
  exact hzc

theorem card_eq_sq_of_isSz {k : ℕ} (hSz : IsSz k Y)
    {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) : Nat.card S = (2 ^ k) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hk, hcard⟩ := E2.card_of_isSz hSz
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS.2.1
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have h1 := S.card_mul_index
  rw [ha, hcard] at h1
  have hm : Odd (((2 ^ k) ^ 2 + 1) * (2 ^ k - 1)) := by
    refine Odd.mul ?_ (Ch3E213M.odd_two_pow_sub_one (by omega))
    exact (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩).add_one
  have hc1 : Nat.Coprime (2 ^ a) (((2 ^ k) ^ 2 + 1) * (2 ^ k - 1)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hc2 : Nat.Coprime ((2 ^ k) ^ 2) S.index :=
    (Nat.Coprime.pow_left _ (Nat.Coprime.pow_left k
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)))))
  have hd1 : 2 ^ a ∣ (2 ^ k) ^ 2 := hc1.dvd_of_dvd_mul_right ⟨S.index, by rw [← h1]⟩
  have hd2 : (2 ^ k) ^ 2 ∣ 2 ^ a := hc2.dvd_of_dvd_mul_right ⟨_, h1⟩
  rw [ha]
  exact Nat.dvd_antisymm hd1 hd2

theorem card_mul_card_le {N A B : Subgroup Y} (hA : A ≤ N) (hB : B ≤ N) (hAB : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card N := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun ab => (⟨ab.1 * ab.2, N.mul_mem (hA ab.1.2) (hB ab.2.2)⟩ : N)) ?_
  rintro ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ h
  have h1 : a₁ * b₁ = a₂ * b₂ := congrArg Subtype.val h
  have h2 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h1]
      _ = b₂ * b₁⁻¹ := by group
  have h3 : a₂⁻¹ * a₁ ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha₂) ha₁, h2 ▸ B.mul_mem hb₂ (B.inv_mem hb₁)⟩
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at h3
  subst h3
  have hb : b₁ = b₂ := mul_left_cancel h1
  subst hb
  rfl

theorem eq_one_of_mem_of_odd {S : Subgroup Y} (hS : IsPGroup 2 S) {z : Y} (hz : z ∈ S)
    (hzo : Odd (orderOf z)) : z = 1 := by
  obtain ⟨n, hn⟩ := hS ⟨z, hz⟩
  exact E2.eq_one_of_two_pow_of_odd (by simpa using congrArg Subtype.val hn) hzo

theorem card_sylow_le_of_isSz {k : ℕ} (hSz : IsSz k Y)
    {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {X : Subgroup Y}
    (hXN : X ≤ Subgroup.normalizer (S : Set Y)) (hXc : Nat.card X = 2 ^ k - 1) :
    Nat.card (Sylow 2 Y) ≤ (2 ^ k) ^ 2 + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hk, hcard⟩ := E2.card_of_isSz hSz
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  rw [Sylow.card_eq_index_normalizer (hS.2.1.toSylow hidx)]
  change (Subgroup.normalizer (S : Set Y)).index ≤ _
  have hSX : S ⊓ X = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => (Subgroup.mem_bot).mpr (eq_one_of_mem_of_odd hS.2.1 hz.1 ?_)
    refine Odd.of_dvd_nat ?_ (Subgroup.orderOf_dvd_natCard X hz.2)
    rw [hXc]
    exact Ch3E213M.odd_two_pow_sub_one (by omega)
  have hN := card_mul_card_le Subgroup.le_normalizer hXN hSX
  rw [card_eq_sq_of_isSz hSz hS, hXc] at hN
  have h1 := (Subgroup.normalizer (S : Set Y)).card_mul_index
  rw [hcard] at h1
  have hpos : 0 < (2 ^ k) ^ 2 * (2 ^ k - 1) := by
    have : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
    exact Nat.mul_pos (by positivity) (by omega)
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (2 ^ k) ^ 2 * (2 ^ k - 1) * (Subgroup.normalizer (S : Set Y)).index
      ≤ Nat.card (Subgroup.normalizer (S : Set Y)) * (Subgroup.normalizer (S : Set Y)).index :=
        Nat.mul_le_mul_right _ hN
    _ = (2 ^ k) ^ 2 * (2 ^ k - 1) * ((2 ^ k) ^ 2 + 1) := by rw [h1]; ring

theorem mem_sylow_of_mem_normalizer (Q : Sylow 2 Y) {x : Y}
    (hxN : x ∈ Subgroup.normalizer ((Q : Subgroup Y) : Set Y)) {n : ℕ} (hxn : x ^ 2 ^ n = 1) :
    x ∈ (Q : Subgroup Y) := by
  have hR : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ (Q : Subgroup Y)) := IsPGroup.to_sup_of_normal_right'
    (E2.isPGroup_zpowers_of_pow hxn) Q.isPGroup' (Subgroup.zpowers_le.mpr hxN)
  rw [← Q.is_maximal' hR le_sup_right]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

theorem exists_conj_eq_of_card {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {h : Y}
    (hTI : ∀ z, z ∈ S → h * z * h⁻¹ ∈ S → z = 1) (hhN : h ∉ Subgroup.normalizer (S : Set Y))
    (hcard : Nat.card (Sylow 2 Y) ≤ Nat.card S + 1) {y : Y}
    (hy : y ∉ Subgroup.normalizer (S : Set Y)) :
    ∃ t ∈ S, ∀ z : Y, y⁻¹ * z * y ∈ S ↔ h * (t⁻¹ * z * t) * h⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  set P₀ : Sylow 2 Y := hS.2.1.toSylow hidx with hP₀
  have hmem : ∀ (c : Y) (Q : Sylow 2 Y) (z : Y),
      z ∈ ((c • Q : Sylow 2 Y) : Subgroup Y) ↔ c⁻¹ * z * c ∈ (Q : Subgroup Y) := by
    intro c Q z
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
  set P' : Sylow 2 Y := h⁻¹ • P₀ with hP'
  have hmemP' : ∀ z, z ∈ (P' : Subgroup Y) ↔ h * z * h⁻¹ ∈ S := by
    intro z
    rw [hP', hmem, inv_inv]
    rfl
  let f : ↥S → Sylow 2 Y := fun t => (t : Y) • P'
  have hf : Function.Injective f := by
    intro t₁ t₂ h12
    have h1 : ((t₂ : Y)⁻¹ * t₁) • P' = P' := by
      rw [mul_smul]
      change (t₂ : Y)⁻¹ • ((t₁ : Y) • P') = P'
      rw [show (t₁ : Y) • P' = (t₂ : Y) • P' from h12, inv_smul_smul]
    rw [Sylow.smul_eq_iff_mem_normalizer] at h1
    obtain ⟨n, hn⟩ := hS.2.1 (t₂⁻¹ * t₁)
    have h2 : (t₂ : Y)⁻¹ * t₁ ∈ (P' : Subgroup Y) :=
      mem_sylow_of_mem_normalizer P' h1 (by simpa using congrArg Subtype.val hn)
    have h3 := hTI _ (S.mul_mem (S.inv_mem t₂.2) t₁.2) ((hmemP' _).mp h2)
    rw [inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  have hrange : Set.range f ⊆ {P₀}ᶜ := by
    rintro _ ⟨t, rfl⟩ ht
    rw [Set.mem_singleton_iff] at ht
    have h1 : P' = P₀ := by
      have e1 : P' = (t : Y)⁻¹ • P₀ := by
        rw [← ht]
        exact (inv_smul_smul (t : Y) P').symm
      rw [e1, Sylow.smul_eq_iff_mem_normalizer]
      exact (Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer t.2)
    apply hhN
    have h2 : h⁻¹ • P₀ = P₀ := h1
    rw [Sylow.smul_eq_iff_mem_normalizer] at h2
    have h3 := (Subgroup.normalizer _).inv_mem h2
    rw [inv_inv] at h3
    exact h3
  have heq : Set.range f = {P₀}ᶜ := by
    refine Set.eq_of_subset_of_ncard_le hrange ?_
    rw [Set.ncard_range_of_injective hf, Set.ncard_compl, Set.ncard_singleton]
    omega
  have hyP : y • P₀ ∈ ({P₀}ᶜ : Set (Sylow 2 Y)) := by
    intro hyP
    rw [Set.mem_singleton_iff, Sylow.smul_eq_iff_mem_normalizer] at hyP
    exact hy hyP
  rw [← heq] at hyP
  obtain ⟨t, ht⟩ := hyP
  refine ⟨t, t.2, fun z => ?_⟩
  have h1 : z ∈ ((y • P₀ : Sylow 2 Y) : Subgroup Y) ↔
      z ∈ (((t : Y) • P' : Sylow 2 Y) : Subgroup Y) := by
    rw [show (t : Y) • P' = y • P₀ from ht]
  rw [hmem, hmem, hmemP'] at h1
  exact h1

theorem exists_conj_mem_normalizer {S : Subgroup Y} {h x : Y}
    (hb : ∀ y ∉ Subgroup.normalizer (S : Set Y), ∃ t ∈ S,
      ∀ z : Y, y⁻¹ * z * y ∈ S ↔ h * (t⁻¹ * z * t) * h⁻¹ ∈ S)
    (hhN : h ∉ Subgroup.normalizer (S : Set Y)) (hxN : x ∈ Subgroup.normalizer (S : Set Y))
    (hxC : ∀ s ∈ S, s * x = x * s → s = 1) :
    ∃ t ∈ S, ∀ z : Y, h * z * h⁻¹ ∈ S ↔ h * ((t * x * t⁻¹) * z * (t * x * t⁻¹)⁻¹) * h⁻¹ ∈ S := by
  have hy : x * h⁻¹ ∉ Subgroup.normalizer (S : Set Y) := by
    intro hy
    apply hhN
    have h1 := (Subgroup.normalizer (S : Set Y)).mul_mem
      ((Subgroup.normalizer (S : Set Y)).inv_mem hxN) hy
    rw [inv_mul_cancel_left] at h1
    simpa using (Subgroup.normalizer (S : Set Y)).inv_mem h1
  obtain ⟨t₀, ht₀, hiff⟩ := hb _ hy
  have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hxN s).mp hs
  let ψ : ↥S → ↥S := fun s =>
    ⟨s * (x * s * x⁻¹)⁻¹, S.mul_mem s.2 (S.inv_mem (hxS s s.2))⟩
  have hψ : Function.Injective ψ := by
    intro s₁ s₂ h12
    have h1 : (s₁ : Y) * (x * s₁ * x⁻¹)⁻¹ = s₂ * (x * s₂ * x⁻¹)⁻¹ := congrArg Subtype.val h12
    have e1 : ∀ s : Y, s * (x * s * x⁻¹)⁻¹ * x = s * x * s⁻¹ := fun s => by group
    have h1' : (s₁ : Y) * x * (s₁ : Y)⁻¹ = s₂ * x * (s₂ : Y)⁻¹ := by
      rw [← e1 (s₁ : Y), ← e1 (s₂ : Y), h1]
    have h2 : ((s₂ : Y)⁻¹ * s₁) * x = x * ((s₂ : Y)⁻¹ * s₁) := by
      calc ((s₂ : Y)⁻¹ * s₁) * x = (s₂ : Y)⁻¹ * ((s₁ : Y) * x * (s₁ : Y)⁻¹) * s₁ := by group
        _ = (s₂ : Y)⁻¹ * (s₂ * x * (s₂ : Y)⁻¹) * s₁ := by rw [h1']
        _ = x * ((s₂ : Y)⁻¹ * s₁) := by group
    have h4 := hxC _ (S.mul_mem (S.inv_mem s₂.2) s₁.2) h2
    rw [inv_mul_eq_one] at h4
    exact Subtype.ext h4.symm
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hψ) ⟨t₀⁻¹, S.inv_mem ht₀⟩
  have hs' : (s : Y) * x * (s : Y)⁻¹ = t₀⁻¹ * x := by
    have h1 : (s : Y) * (x * s * x⁻¹)⁻¹ = t₀⁻¹ := congrArg Subtype.val hs
    calc (s : Y) * x * (s : Y)⁻¹ = ((s : Y) * (x * s * x⁻¹)⁻¹) * x := by group
      _ = t₀⁻¹ * x := by rw [h1]
  refine ⟨s, s.2, fun z => ?_⟩
  rw [hs']
  have h1 := hiff (x * z * x⁻¹)
  have e1 : (x * h⁻¹)⁻¹ * (x * z * x⁻¹) * (x * h⁻¹) = h * z * h⁻¹ := by group
  have e2 : t₀⁻¹ * (x * z * x⁻¹) * t₀ = t₀⁻¹ * x * z * (t₀⁻¹ * x)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem eq_one_of_commute_of_isSz {k : ℕ} (hSz : IsSz k Y) {S : Subgroup Y} (hS2 : IsPGroup 2 S)
    {x : Y} (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) {s : Y} (hs : s ∈ S) (hsx : s * x = x * s) :
    s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hs1
  obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : 2 ∣ Nat.card (Subgroup.zpowers s) := by
    rw [Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsn)
    rcases j with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hs1
    · rw [hj, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨⟨u, hu⟩, hu2⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers s) 2 h2
  have hu2' : orderOf u = 2 := by rw [← hu2, Subgroup.orderOf_mk]
  have hux : x ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left hsx j).eq.symm
  obtain ⟨m, hm⟩ := isPGroup_centralizer_of_isSz hSz hu2' ⟨x, hux⟩
  exact hx1 (E2.eq_one_of_two_pow_of_odd (by simpa using congrArg Subtype.val hm) hxo)

theorem exists_involution_inverting {k : ℕ} (hSz : IsSz k Y) {S : Subgroup Y}
    (hS : IsSylowTwoOf S ⊤) {h v : Y}
    (hW2 : ∀ w ∈ S ⊓ Subgroup.centralizer (S : Set Y), w * w = 1)
    (hgen : (S ⊓ Subgroup.centralizer (S : Set Y)) ⊔
      (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom = ⊤)
    (hcen : Subgroup.center Y = ⊥) (hv : v ∈ S ⊓ Subgroup.centralizer (S : Set Y))
    (hv1 : v ≠ 1) :
    ∃ r z : Y, r * r = 1 ∧ z * v * z⁻¹ = r ∧
      ∀ d ∈ Subgroup.normalizer (S : Set Y),
        (∀ y : Y, h * y * h⁻¹ ∈ S ↔ h * (d * y * d⁻¹) * h⁻¹ ∈ S) → r * d * r⁻¹ = d⁻¹ := by
  have hCv : Subgroup.centralizer ({v} : Set Y) ≤ S :=
    centralizer_le_of_isSz hSz hS hv (hW2 v hv) hv1
  have hCvS : ∀ z, z * v = v * z ↔ z ∈ S := fun z =>
    ⟨fun hz => hCv (Subgroup.mem_centralizer_singleton_iff.mpr hz),
      fun hz => Subgroup.mem_centralizer_iff.mp hv.2 z hz⟩
  have hTI : ∀ z, z ∈ S → h * z * h⁻¹ ∈ S → z = 1 := fun z hz hz' =>
    eq_one_of_mem_inf hgen hcen hz hz'
  obtain ⟨e, he⟩ : ∃ e : Y, e = h⁻¹ * v * h := ⟨_, rfl⟩
  have hv2 : v * v = 1 := hW2 v hv
  have hhe : h * e * h⁻¹ = v := by rw [he]; group
  have he2 : e * e = 1 := by
    calc e * e = h⁻¹ * ((h * e * h⁻¹) * (h * e * h⁻¹)) * h := by group
      _ = 1 := by rw [hhe, hv2]; group
  have hCeS : ∀ z, z * e = e * z ↔ h * z * h⁻¹ ∈ S := fun z => by
    rw [← hCvS, ← hhe]
    exact (conj_commute_iff z e h).symm
  have hno : ∀ z : Y, z * z = 1 → z * v = v * z → z * e = e * z → z = 1 := fun z _ hzv hze =>
    hTI z ((hCvS z).mp hzv) ((hCeS z).mp hze)
  obtain ⟨y₀, hy₀, hy₀v⟩ := exists_conj_of_forall_involution hv2 he2 hno
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  obtain ⟨c, hcdef⟩ : ∃ c : Y, c = v * e := ⟨_, rfl⟩
  rw [← hcdef] at hy₀
  have hvc : ∀ j : ℤ, v * c ^ j * v⁻¹ = (c ^ j)⁻¹ := by
    have h1 : v * c * v⁻¹ = c⁻¹ := by
      rw [hcdef, mul_inv_rev, hvinv, heinv]
      calc v * (v * e) * v = (v * v) * e * v := by group
        _ = e * v := by rw [hv2, one_mul]
    intro j
    have h2 := map_zpow (MulAut.conj v) c j
    simp only [MulAut.conj_apply] at h2
    rw [h2, h1, inv_zpow]
  have hec : ∀ j : ℤ, e * c ^ j * e⁻¹ = (c ^ j)⁻¹ := by
    have h1 : e * c * e⁻¹ = c⁻¹ := by
      rw [hcdef, mul_inv_rev, hvinv, heinv]
      calc e * (v * e) * e = e * v * (e * e) := by group
        _ = e * v := by rw [he2, mul_one]
    intro j
    have h2 := map_zpow (MulAut.conj e) c j
    simp only [MulAut.conj_apply] at h2
    rw [h2, h1, inv_zpow]
  have hodd : Odd (orderOf c) := by
    rcases Nat.even_or_odd (orderOf c) with ⟨m, hm⟩ | h0
    · exfalso
      have hc0 : 0 < orderOf c := orderOf_pos c
      set w := c ^ (m : ℤ) with hw
      have hw2 : w * w = 1 := by
        rw [hw, ← zpow_add, ← Nat.cast_add, ← hm, zpow_natCast, pow_orderOf_eq_one]
      have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
      have hwv : w * v = v * w := by
        have h1 := hvc m
        rw [← hw, hwinv] at h1
        calc w * v = (v * w * v⁻¹) * v := by rw [h1]
          _ = v * w := by group
      have hwe : w * e = e * w := by
        have h1 := hec m
        rw [← hw, hwinv] at h1
        calc w * e = (e * w * e⁻¹) * e := by rw [h1]
          _ = e * w := by group
      have h1 := hno w hw2 hwv hwe
      rw [hw, zpow_natCast] at h1
      have := orderOf_le_of_pow_eq_one (by omega : 0 < m) h1
      omega
    · exact h0
  obtain ⟨j₀, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₀
  obtain ⟨r, hr⟩ : ∃ r : Y, r = c ^ j₀ * v := ⟨_, rfl⟩
  have hr2 : r * r = 1 := by
    calc r * r = c ^ j₀ * (v * c ^ j₀ * v⁻¹) * (v * v) := by rw [hr]; group
      _ = 1 := by rw [hvc, hv2]; group
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hrv : r * v * r⁻¹ = e := by
    calc r * v * r⁻¹ = c ^ j₀ * v * (c ^ j₀)⁻¹ := by rw [hr]; group
      _ = e := hy₀v
  obtain ⟨n₀, hn₀⟩ := hodd
  obtain ⟨z, hz⟩ : ∃ z : Y, z = c ^ (j₀ * ((n₀ : ℤ) + 1)) := ⟨_, rfl⟩
  have hzz : z * z = c ^ j₀ := by
    rw [hz, ← zpow_add]
    have hcn : c ^ (orderOf c : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
    have e1 : j₀ * ((n₀ : ℤ) + 1) + j₀ * ((n₀ : ℤ) + 1) = j₀ * (orderOf c : ℤ) + j₀ := by
      rw [hn₀]; push_cast; ring
    rw [e1, zpow_add, zpow_mul', hcn, one_zpow, one_mul]
  have hzr : z * v * z⁻¹ = r := by
    have h1 : v * z⁻¹ * v⁻¹ = z := by
      rw [hz, ← zpow_neg, hvc, ← zpow_neg, neg_neg]
    calc z * v * z⁻¹ = z * (v * z⁻¹ * v⁻¹) * v := by group
      _ = z * z * v := by rw [h1]
      _ = r := by rw [hzz, hr]
  refine ⟨r, z, hr2, hzr, fun d hdN hdS' => ?_⟩
  have hswap : ∀ y, h * y * h⁻¹ ∈ S ↔ r⁻¹ * y * r ∈ S := by
    intro y
    have h1 := conj_commute_iff (r⁻¹ * y * r) v r
    have e1 : r * (r⁻¹ * y * r) * r⁻¹ = y := by group
    rw [e1, hrv] at h1
    exact (hCeS y).symm.trans (h1.trans (hCvS _))
  have hswap' : ∀ y, y ∈ S ↔ h * (r⁻¹ * y * r) * h⁻¹ ∈ S := by
    intro y
    have h1 := hswap (r⁻¹ * y * r)
    have e1 : r⁻¹ * (r⁻¹ * y * r) * r = y := by
      calc r⁻¹ * (r⁻¹ * y * r) * r = (r⁻¹ * r⁻¹) * y * (r * r) := by group
        _ = y := by rw [← mul_inv_rev, hr2, inv_one, one_mul, mul_one]
    rw [e1] at h1
    exact h1.symm
  set S' : Subgroup Y := S.map (MulAut.conj h⁻¹).toMonoidHom with hS'
  have hmemS' : ∀ y, y ∈ S' ↔ h * y * h⁻¹ ∈ S := fun y => by
    rw [hS', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hNS' : ∀ d₁ : Y, d₁ ∈ Subgroup.normalizer (S' : Set Y) ↔
      ∀ y : Y, h * y * h⁻¹ ∈ S ↔ h * (d₁ * y * d₁⁻¹) * h⁻¹ ∈ S := fun d₁ => by
    rw [Subgroup.mem_normalizer_iff]
    exact forall_congr' fun y => by rw [hmemS', hmemS']
  set D := Subgroup.normalizer (S : Set Y) ⊓ Subgroup.normalizer (S' : Set Y) with hD
  have hrD : ∀ d₁ ∈ D, r * d₁ * r⁻¹ ∈ D := by
    intro d₁ hd₁
    obtain ⟨hd₁N, hd₁N'⟩ := Subgroup.mem_inf.mp hd₁
    rw [hNS'] at hd₁N'
    refine Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_normalizer_iff.mpr fun y => ?_, (hNS' _).mpr fun y => ?_⟩
    · have h1 := hswap' y
      have h2 := hd₁N' (r⁻¹ * y * r)
      have h3 := hswap' (r * d₁ * r⁻¹ * y * (r * d₁ * r⁻¹)⁻¹)
      have e1 : r⁻¹ * (r * d₁ * r⁻¹ * y * (r * d₁ * r⁻¹)⁻¹) * r = d₁ * (r⁻¹ * y * r) * d₁⁻¹ := by
        group
      rw [e1] at h3
      exact h1.trans (h2.trans h3.symm)
    · have h1 := hswap y
      have h2 := Subgroup.mem_normalizer_iff.mp hd₁N (r⁻¹ * y * r)
      have h3 := hswap (r * d₁ * r⁻¹ * y * (r * d₁ * r⁻¹)⁻¹)
      have e1 : r⁻¹ * (r * d₁ * r⁻¹ * y * (r * d₁ * r⁻¹)⁻¹) * r = d₁ * (r⁻¹ * y * r) * d₁⁻¹ := by
        group
      rw [e1] at h3
      exact h1.trans (h2.trans h3.symm)
  let σ : ↥D →* ↥D :=
    { toFun := fun d₁ => ⟨r * d₁ * r⁻¹, hrD d₁ d₁.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hσ : ∀ d₁ : ↥D, ((σ d₁ : ↥D) : Y) = r * d₁ * r⁻¹ := fun _ => rfl
  have hr1 : r ≠ 1 := by
    intro hr1
    rw [hr1, one_mul, inv_one, mul_one] at hrv
    apply hv1
    refine hTI v hv.1 ?_
    rw [← hrv] at hhe
    rw [hhe]
    exact hv.1
  have hrord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hfp : MonoidHom.FixedPointFree σ := by
    intro d₁ hd₁
    have h1 : r * d₁ * r⁻¹ = d₁ := congrArg Subtype.val hd₁
    have hd₁C : (d₁ : Y) ∈ Subgroup.centralizer ({r} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (d₁ : Y) * r = (r * d₁ * r⁻¹) * r := by rw [h1]
        _ = r * d₁ := by group
    obtain ⟨n, hn⟩ := isPGroup_centralizer_of_isSz hSz hrord ⟨_, hd₁C⟩
    have hd₁n : (d₁ : Y) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd₁S : (d₁ : Y) ∈ S := mem_of_mem_normalizer_of_pow hS d₁.2.1 hd₁n
    have hd₁S' : h * d₁ * h⁻¹ ∈ S := by
      refine mem_of_mem_normalizer_of_pow hS (Subgroup.mem_normalizer_iff.mpr fun y => ?_)
        (n := n) (by rw [conj_pow, hd₁n]; group)
      have h2 := ((hNS' _).mp d₁.2.2) (h⁻¹ * y * h)
      have e1 : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
      have e2 : h * ((d₁ : Y) * (h⁻¹ * y * h) * (d₁ : Y)⁻¹) * h⁻¹ =
          h * d₁ * h⁻¹ * y * (h * d₁ * h⁻¹)⁻¹ := by group
      rw [e1, e2] at h2
      exact h2
    exact Subtype.ext (hTI _ hd₁S hd₁S')
  have hinvol : Function.Involutive σ := fun d₁ => by
    apply Subtype.ext
    rw [hσ, hσ]
    calc r * (r * d₁ * r⁻¹) * r⁻¹ = (r * r) * d₁ * (r * r)⁻¹ := by group
      _ = d₁ := by rw [hr2]; group
  have hdD : d ∈ D := ⟨hdN, (hNS' d).mpr hdS'⟩
  have h1 := congrFun (hfp.coe_eq_inv_of_involutive hinvol) ⟨d, hdD⟩
  exact congrArg Subtype.val h1

theorem exists_conj_eq_mul_of_isSz {k : ℕ} (hSz : IsSz k Y)
    {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {h v : Y}
    (hW2 : ∀ w ∈ S ⊓ Subgroup.centralizer (S : Set Y), w * w = 1)
    (hgen : (S ⊓ Subgroup.centralizer (S : Set Y)) ⊔
      (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom = ⊤)
    (hcen : Subgroup.center Y = ⊥) (hv : v ∈ S ⊓ Subgroup.centralizer (S : Set Y))
    (hv1 : v ≠ 1) {X : Subgroup Y} (hXN : X ≤ Subgroup.normalizer (S : Set Y))
    (hXc : Nat.card X = 2 ^ k - 1) {x : Y} (hx : x ∈ X) (hx1 : x ≠ 1) :
    ∃ u w : Y, u * x * u⁻¹ = v * (w * v * w⁻¹) ∧
      (S ⊓ Subgroup.centralizer (S : Set Y)) ⊔
        (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj w).toMonoidHom = ⊤ := by
  obtain ⟨hk, -⟩ := E2.card_of_isSz hSz
  have hTI : ∀ z, z ∈ S → h * z * h⁻¹ ∈ S → z = 1 := fun z hz hz' =>
    eq_one_of_mem_inf hgen hcen hz hz'
  have hhN : h ∉ Subgroup.normalizer (S : Set Y) := fun hhN =>
    hv1 (hTI v hv.1 ((Subgroup.mem_normalizer_iff.mp hhN v).mp hv.1))
  have hSyl : Nat.card (Sylow 2 Y) ≤ Nat.card S + 1 := by
    rw [card_eq_sq_of_isSz hSz hS]
    exact card_sylow_le_of_isSz hSz hS hXN hXc
  have hb : ∀ y ∉ Subgroup.normalizer (S : Set Y), ∃ t ∈ S,
      ∀ z : Y, y⁻¹ * z * y ∈ S ↔ h * (t⁻¹ * z * t) * h⁻¹ ∈ S := fun y hy =>
    exists_conj_eq_of_card hS hTI hhN hSyl hy
  have hxo : Odd (orderOf x) := Odd.of_dvd_nat
    (by rw [hXc]; exact Ch3E213M.odd_two_pow_sub_one (by omega)) (Subgroup.orderOf_dvd_natCard X hx)
  have hxC : ∀ s ∈ S, s * x = x * s → s = 1 := fun s hs hsx =>
    eq_one_of_commute_of_isSz hSz hS.2.1 hxo hx1 hs hsx
  obtain ⟨t, htS, htd⟩ := exists_conj_mem_normalizer hb hhN (hXN hx) hxC
  obtain ⟨d, hd⟩ : ∃ d : Y, d = t * x * t⁻¹ := ⟨_, rfl⟩
  rw [← hd] at htd
  have hdN : d ∈ Subgroup.normalizer (S : Set Y) := by
    rw [hd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer htS) (hXN hx))
      (Subgroup.inv_mem _ (Subgroup.le_normalizer htS))
  obtain ⟨r, z, hr2, hzr, hinv⟩ := exists_involution_inverting hSz hS hW2 hgen hcen hv hv1
  have hrd : r * d * r⁻¹ = d⁻¹ := hinv d hdN htd
  have hdo : Odd (orderOf d) := by
    rw [hd, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hxo
  obtain ⟨n₁, hn₁⟩ : Odd (orderOf d⁻¹) := by rw [orderOf_inv]; exact hdo
  obtain ⟨b, hbdef⟩ : ∃ b : Y, b = d⁻¹ ^ (n₁ + 1) := ⟨_, rfl⟩
  have hbb : b * b = d⁻¹ := by
    rw [hbdef, ← pow_add, show n₁ + 1 + (n₁ + 1) = orderOf d⁻¹ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hrb : r * b⁻¹ * r⁻¹ = b := by
    rw [hbdef, ← inv_pow, inv_inv]
    have h2 := map_pow (MulAut.conj r) d (n₁ + 1)
    simp only [MulAut.conj_apply] at h2
    rw [hrd] at h2
    exact h2
  have hrdr : r * d = d⁻¹ * r := by
    calc r * d = (r * d * r⁻¹) * r := by group
      _ = d⁻¹ * r := by rw [hrd]
  have hbr : b * r * b⁻¹ = r * d := by
    calc b * r * b⁻¹ = b * (r * b⁻¹ * r⁻¹) * r := by group
      _ = b * b * r := by rw [hrb]
      _ = r * d := by rw [hbb, hrdr]
  have hdrr : d = r * (b * r * b⁻¹) := by rw [hbr, ← mul_assoc, hr2, one_mul]
  have hux : (z⁻¹ * t) * x * (z⁻¹ * t)⁻¹ = v * ((z⁻¹ * b * z) * v * (z⁻¹ * b * z)⁻¹) := by
    calc (z⁻¹ * t) * x * (z⁻¹ * t)⁻¹ = z⁻¹ * (t * x * t⁻¹) * z := by group
      _ = z⁻¹ * (r * (b * r * b⁻¹)) * z := by rw [← hd, ← hdrr]
      _ = z⁻¹ * ((z * v * z⁻¹) * (b * (z * v * z⁻¹) * b⁻¹)) * z := by rw [hzr]
      _ = v * ((z⁻¹ * b * z) * v * (z⁻¹ * b * z)⁻¹) := by group
  refine ⟨z⁻¹ * t, z⁻¹ * b * z, hux, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w : Y, w = z⁻¹ * b * z := ⟨_, rfl⟩
  rw [← hw] at hux ⊢
  have hwN : w ∉ Subgroup.normalizer (S : Set Y) := by
    intro hwN
    have h1 : (z⁻¹ * t) * x * (z⁻¹ * t)⁻¹ ∈ S := by
      rw [hux]
      exact S.mul_mem hv.1 ((Subgroup.mem_normalizer_iff.mp hwN v).mp hv.1)
    have h2 : Odd (orderOf ((z⁻¹ * t) * x * (z⁻¹ * t)⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hxo
    have h3 := eq_one_of_mem_of_odd hS.2.1 h1 h2
    apply hx1
    calc x = (z⁻¹ * t)⁻¹ * ((z⁻¹ * t) * x * (z⁻¹ * t)⁻¹) * (z⁻¹ * t) := by group
      _ = 1 := by rw [h3]; group
  obtain ⟨t', ht', hiff⟩ := hb w hwN
  have hZ : ∀ y : Y, w⁻¹ * y * w ∈ S ⊓ Subgroup.centralizer (S : Set Y) ↔
      (h * t'⁻¹) * y * (h * t'⁻¹)⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set Y) := by
    have h1 : ∀ y : Y, w⁻¹ * y * w⁻¹⁻¹ ∈ S ↔ (h * t'⁻¹) * y * (h * t'⁻¹)⁻¹ ∈ S := fun y => by
      have e1 : (h * t'⁻¹) * y * (h * t'⁻¹)⁻¹ = h * (t'⁻¹ * y * t') * h⁻¹ := by group
      rw [inv_inv, e1]
      exact hiff y
    intro y
    have h2 := conj_mem_center_iff h1 y
    rw [inv_inv] at h2
    exact h2
  have hWt : ∀ y : Y, t'⁻¹ * y * t' ∈ S ⊓ Subgroup.centralizer (S : Set Y) ↔
      y ∈ S ⊓ Subgroup.centralizer (S : Set Y) := by
    have h1 : ∀ y : Y, t'⁻¹ * y * t'⁻¹⁻¹ ∈ S ↔ 1 * y * 1⁻¹ ∈ S := fun y => by
      rw [inv_inv, one_mul, inv_one, mul_one]
      constructor
      · intro hy
        have := S.mul_mem (S.mul_mem ht' hy) (S.inv_mem ht')
        simpa [mul_assoc] using this
      · intro hy
        exact S.mul_mem (S.mul_mem (S.inv_mem ht') hy) ht'
    intro y
    have h2 := conj_mem_center_iff h1 y
    rw [inv_inv, one_mul, inv_one, mul_one] at h2
    exact h2
  refine eq_top_iff.mpr ?_
  have htop : B6.conjSub t' ((S ⊓ Subgroup.centralizer (S : Set Y)) ⊔
      (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom) = ⊤ := by
    rw [hgen]
    exact map_top (B6.conjSub t')
  rw [← htop, map_sup]
  refine sup_le (fun y hy => ?_) (fun y hy => ?_)
  · rw [B6.mem_conjSub] at hy
    exact Subgroup.mem_sup_left ((hWt y).mp hy)
  · rw [B6.mem_conjSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hy
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    refine (hZ y).mpr ?_
    have e1 : (h * t'⁻¹) * y * (h * t'⁻¹)⁻¹ = h * (t'⁻¹ * y * t') * h⁻¹ := by group
    rw [e1]
    exact hy

end E214F

end CFSG.Quasithin.SimsE2
