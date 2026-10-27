module

public import CFSG.Walter.ReeOrder.WardLocal.CentP

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

section General

variable {G : Type} [Group G]

@[expose] def relCen (P H N : Subgroup G) (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    Subgroup G where
  carrier := {g | g ∈ P ∧ ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨P.mul_mem ha hb, fun h hh => ?_⟩
    have e : a * b * h * (a * b)⁻¹ * h⁻¹ =
        a * (b * h * b⁻¹ * h⁻¹) * a⁻¹ * (a * h * a⁻¹ * h⁻¹) := by group
    rw [e]
    exact N.mul_mem (hN a ha _ (hb' h hh)) (ha' h hh)
  one_mem' := ⟨P.one_mem, fun h _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨P.inv_mem ha, fun h hh => ?_⟩
    have e : a⁻¹ * h * a⁻¹⁻¹ * h⁻¹ = a⁻¹ * (a * h * a⁻¹ * h⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact hN _ (P.inv_mem ha) _ (N.inv_mem (ha' h hh))

theorem mem_relCen {P H N : Subgroup G} {hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N} {g : G} :
    g ∈ relCen P H N hN ↔ g ∈ P ∧ ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ N := Iff.rfl

theorem conj_mem_relCen {P H N : Subgroup G} {hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N}
    {r g : G} (hrP : ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hrH : ∀ x ∈ H, r⁻¹ * x * r ∈ H)
    (hrN : ∀ x ∈ N, r * x * r⁻¹ ∈ N) (hg : g ∈ relCen P H N hN) :
    r * g * r⁻¹ ∈ relCen P H N hN := by
  obtain ⟨hgP, hg'⟩ := hg
  refine ⟨hrP g hgP, fun h hh => ?_⟩
  have := hrN _ (hg' _ (hrH h hh))
  rwa [show r * (g * (r⁻¹ * h * r) * g⁻¹ * (r⁻¹ * h * r)⁻¹) * r⁻¹ =
    r * g * r⁻¹ * h * (r * g * r⁻¹)⁻¹ * h⁻¹ by group] at this

theorem exists_relCen_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {P N : Subgroup G}
    (hP : IsPGroup p P) (hNP : N ≤ P) (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hne : N ≠ P) :
    ∃ g ∈ relCen P P N hN, g ∉ N := by
  set N' := N.subgroupOf P with hN'
  have hNn : N'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : P) : G) ∈ N
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN g g.2 n hn⟩
  have hQp : IsPGroup p (P ⧸ N') := hP.to_quotient N'
  have hQnt : Nontrivial (P ⧸ N') := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    apply hne
    apply le_antisymm hNP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ N' := h ▸ Subgroup.mem_top _
    exact this
  have := hQp.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center (P ⧸ N'))
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨g', ⟨g'.2, fun h hh => ?_⟩, fun hg => hz1 ?_⟩
  · have hc := (Subgroup.mem_center_iff.mp hzc) (QuotientGroup.mk ⟨h, hh⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    have hc' : ((⟨h, hh⟩ * g' : P)⁻¹ * (g' * ⟨h, hh⟩) : P) ∈ N' := hc
    have : ((((⟨h, hh⟩ * g' : P)⁻¹ * (g' * ⟨h, hh⟩) : P)) : G) ∈ N := hc'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    have h2 := hN (h * g') (P.mul_mem hh g'.2) _ this
    rwa [show h * ↑g' * ((h * ↑g')⁻¹ * (↑g' * h)) * (h * ↑g')⁻¹ = ↑g' * h * (↑g')⁻¹ * h⁻¹ by
      group] at h2
  · apply Subtype.ext
    simp only [Subgroup.coe_one]
    exact (QuotientGroup.eq_one_iff g').mpr hg

theorem exists_cube_subgroup [Finite G] {P N : Subgroup G} (hP : IsPGroup 3 P) (hNP : N ≤ P)
    (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hne : N ≠ P)
    (hcomm : ∀ y ∈ P, ∀ z ∈ P, y * z * y⁻¹ * z⁻¹ ∈ N) :
    ∃ K : Subgroup G, N ≤ K ∧ K ≠ P ∧ ∀ g, g ∈ K ↔ g ∈ P ∧ ∃ z ∈ P, g⁻¹ * z ^ 3 ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' := N.subgroupOf P with hN'
  have hNn : N'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : P) : G) ∈ N
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN g g.2 n hn⟩
  have hQcomm : ∀ a b : P ⧸ N', a * b = b * a := by
    intro a b
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    show (((y * z)⁻¹ * (z * y) : P) : G) ∈ N
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have := hcomm _ (P.inv_mem z.2) _ (P.inv_mem y.2)
    have e : ((y : G) * z)⁻¹ * ((z : G) * y) = (z : G)⁻¹ * (y : G)⁻¹ * (z : G)⁻¹⁻¹ * (y : G)⁻¹⁻¹ :=
      by group
    rw [e]; exact this
  let cube : P ⧸ N' →* P ⧸ N' :=
    { toFun := fun a => a ^ 3
      map_one' := one_pow 3
      map_mul' := fun a b => (Commute.mul_pow (hQcomm a b) 3) }
  set K := (cube.range.comap (QuotientGroup.mk' N')).map P.subtype with hK
  have hmem : ∀ g, g ∈ K ↔ g ∈ P ∧ ∃ z ∈ P, g⁻¹ * z ^ 3 ∈ N := by
    intro g
    constructor
    · rintro ⟨g', ⟨x, hx⟩, rfl⟩
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
      refine ⟨g'.2, z, z.2, ?_⟩
      have hx' : (QuotientGroup.mk (z ^ 3) : P ⧸ N') = QuotientGroup.mk g' := hx
      rw [QuotientGroup.eq] at hx'
      have : (((z ^ 3)⁻¹ * g' : P) : G) ∈ N := hx'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at this
      have := N.inv_mem this
      simpa using this
    · rintro ⟨hg, z, hz, hgz⟩
      refine ⟨⟨g, hg⟩, ⟨QuotientGroup.mk ⟨z, hz⟩, ?_⟩, rfl⟩
      show (QuotientGroup.mk ⟨z, hz⟩ : P ⧸ N') ^ 3 = QuotientGroup.mk' N' ⟨g, hg⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show (((⟨z, hz⟩ ^ 3)⁻¹ * ⟨g, hg⟩ : P) : G) ∈ N
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      have := N.inv_mem hgz
      simpa using this
  refine ⟨K, fun n hn => (hmem n).mpr ⟨hNP hn, 1, P.one_mem, by simpa using N.inv_mem hn⟩,
    fun hKP => ?_, hmem⟩
  have hsurj : Function.Surjective cube := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    have hgK : (g : G) ∈ K := by rw [hKP]; exact g.2
    obtain ⟨hg, z, hz, hgz⟩ := (hmem g).mp hgK
    refine ⟨QuotientGroup.mk ⟨z, hz⟩, ?_⟩
    show (QuotientGroup.mk ⟨z, hz⟩ : P ⧸ N') ^ 3 = QuotientGroup.mk g
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq]
    show (((⟨z, hz⟩ ^ 3)⁻¹ * g : P) : G) ∈ N
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    have := N.inv_mem hgz
    simpa using this
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have hQnt : Nontrivial (P ⧸ N') := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    apply hne
    apply le_antisymm hNP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ N' := h ▸ Subgroup.mem_top _
    exact this
  have hQp : IsPGroup 3 (P ⧸ N') := hP.to_quotient N'
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card_iff_nontrivial.mpr hQnt
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ N') 3
    (by rw [hn]; exact dvd_pow_self 3 hn0)
  have h3 : cube x = cube 1 := by
    show x ^ 3 = 1 ^ 3
    rw [one_pow, ← hx, pow_orderOf_eq_one]
  have := hinj h3
  rw [this, orderOf_one] at hx
  omega

theorem surjective_of_card_ker {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A →* B) (h : Nat.card A = Nat.card φ.ker * Nat.card B) : Function.Surjective φ := by
  have hidx := φ.ker.card_mul_index
  rw [Subgroup.index_ker, h] at hidx
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hr : Nat.card φ.range = Nat.card B := by
    have := Nat.eq_of_mul_eq_mul_left hpos hidx
    exact this
  have htop := Subgroup.eq_top_of_card_eq φ.range hr
  exact MonoidHom.range_eq_top.mp htop

end General

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

include B hq hK hG hP1P hPc hPn hN1c in
theorem PP1_normal {g a : G} (hg : g ∈ P) (ha : a ∈ PP1 S) : g * a * g⁻¹ ∈ PP1 S :=
  conj_mem_PP1 hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c
    (Subgroup.le_normalizer hg) ha

omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem zcen_conj {P : Subgroup G} {g c : G} (hg : g ∈ P) (hc : c ∈ zcen P) :
    g * c * g⁻¹ = c := by
  rw [← (mem_zcen.mp hc).2 g hg]; group

include B hq hK hG hP1P hPc hPn in
theorem card_zcen : Nat.card (zcen P) = q := by
  rw [zcen_eq_CC hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG) hP1P hPc hPn,
    card_CC hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)]

include B hq hK hG hP1P hPc hPn in
theorem zcen_le_PP1 : zcen P ≤ PP1 S := by
  rw [zcen_eq_CC hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG) hP1P hPc hPn]
  exact fun x hx => hx.1

include hq hK hPc in
omit [CharP K 3] in
theorem card_RR_inv {H : Subgroup G} (hHP : H ≤ P) (hR : ∀ r ∈ RR S, ∀ x ∈ H, r * x * r⁻¹ ∈ H) :
    ∃ t ≤ 3, Nat.card H = q ^ t := by
  have hRH : RR S ≤ Subgroup.normalizer (H : Set G) := fun r hr =>
    mem_normalizer_of_conj_mem (fun x hx => hR r hr x hx)
  obtain ⟨t, ht⟩ := card_RR_invariant hq hK ((isPGroup_P hq hPc).to_le hHP) hRH
  refine ⟨t, ?_, ht⟩
  have hle := Subgroup.card_le_of_le hHP
  rw [ht, hPc] at hle
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  by_contra h
  have : q ^ 3 < q ^ t := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

include B hq hK hG hPn in
theorem RR_conj_P {r x : G} (hr : r ∈ RR S) (hx : x ∈ P) : r * x * r⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp (RR_le_normalizer_P hq (B.hcT hq hK hG) hPn hr) x).mp hx

include B hq hK hG in
theorem RR_conj_PP1 {r x : G} (hr : r ∈ RR S) (hx : x ∈ PP1 S) : r * x * r⁻¹ ∈ PP1 S :=
  (Subgroup.mem_normalizer_iff.mp (RR_le_normalizer_PP1 hq (B.hcT hq hK hG) hr) x).mp hx

include B hq hK hG hPn in
theorem RR_conj_zcen {r x : G} (hr : r ∈ RR S) (hx : x ∈ zcen P) : r * x * r⁻¹ ∈ zcen P :=
  conj_mem_zcen (RR_le_normalizer_P hq (B.hcT hq hK hG) hPn hr) hx

include B hq hK hG hPn in
theorem RR_conj_P' {r x : G} (hr : r ∈ RR S) (hx : x ∈ P) : r⁻¹ * x * r ∈ P := by
  have := B.RR_conj_P hq hK hG hPn ((RR S).inv_mem hr) hx
  simpa using this

include B hq hK hG in
theorem RR_conj_PP1' {r x : G} (hr : r ∈ RR S) (hx : x ∈ PP1 S) : r⁻¹ * x * r ∈ PP1 S := by
  have := B.RR_conj_PP1 hq hK hG ((RR S).inv_mem hr) hx
  simpa using this

include B hq hK hG hPc in
theorem PP1_ne_P : PP1 S ≠ P := by
  intro h
  have h1 := card_PP1 hq hK (B.hcT hq hK hG) hG
  rw [h, hPc] at h1
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

include B hq hK hG hPc in
theorem eq_of_RR_inv {H : Subgroup G} (hP1H : PP1 S ≤ H) (hHP : H ≤ P)
    (hR : ∀ r ∈ RR S, ∀ x ∈ H, r * x * r⁻¹ ∈ H) : H = PP1 S ∨ H = P := by
  obtain ⟨t, ht3, ht⟩ := card_RR_inv hq hK hPc hHP hR
  have h1 := Subgroup.card_le_of_le hP1H
  rw [card_PP1 hq hK (B.hcT hq hK hG) hG, ht] at h1
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have ht2 : 2 ≤ t := by
    by_contra h
    have : q ^ t < q ^ 2 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  rcases (show t = 2 ∨ t = 3 by omega) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hP1H (by rw [ht, card_PP1 hq hK (B.hcT hq hK hG) hG])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hHP (by rw [ht, hPc])

include B hq hK hG hP1P hPc hPn hN1c in
theorem comm_mem_PP1 {y z : G} (hy : y ∈ P) (hz : z ∈ P) : y * z * y⁻¹ * z⁻¹ ∈ PP1 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ∀ g ∈ P, ∀ a ∈ PP1 S, g * a * g⁻¹ ∈ PP1 S := fun g hg a ha =>
    B.PP1_normal hq hK hG hP1P hPc hPn hN1c hg ha
  set K₁ := relCen P P (PP1 S) hN with hK₁
  have hP1K : PP1 S ≤ K₁ := fun a ha => ⟨hP1P ha, fun h hh => by
    have := hN h hh _ ((PP1 S).inv_mem ha)
    have e : a * h * a⁻¹ * h⁻¹ = a * (h * a⁻¹ * h⁻¹) := by group
    rw [e]; exact (PP1 S).mul_mem ha this⟩
  have hR : ∀ r ∈ RR S, ∀ x ∈ K₁, r * x * r⁻¹ ∈ K₁ := fun r hr x hx =>
    conj_mem_relCen (fun x hx => B.RR_conj_P hq hK hG hPn hr hx)
      (fun x hx => B.RR_conj_P' hq hK hG hPn hr hx) (fun x hx => B.RR_conj_PP1 hq hK hG hr hx) hx
  obtain ⟨g, hg, hgP1⟩ := exists_relCen_not_mem (isPGroup_P hq hPc) hP1P hN
    (B.PP1_ne_P hq hK hG hPc)
  rcases B.eq_of_RR_inv hq hK hG hPc hP1K (fun x hx => hx.1) hR with h | h
  · exact absurd (h ▸ hg) hgP1
  · have hyK : y ∈ K₁ := h ▸ hy
    exact hyK.2 z hz

include B hq hK hG hP1P hPc hPn hN1c in
theorem cube_mem_PP1 {y : G} (hy : y ∈ P) : y ^ 3 ∈ PP1 S := by
  have hN : ∀ g ∈ P, ∀ a ∈ PP1 S, g * a * g⁻¹ ∈ PP1 S := fun g hg a ha =>
    B.PP1_normal hq hK hG hP1P hPc hPn hN1c hg ha
  obtain ⟨K₃, hP1K, hKne, hmem⟩ := exists_cube_subgroup (isPGroup_P hq hPc) hP1P hN
    (B.PP1_ne_P hq hK hG hPc)
    (fun y hy z hz => B.comm_mem_PP1 hq hK hG hP1P hPc hPn hN1c hy hz)
  have hKP : K₃ ≤ P := fun x hx => ((hmem x).mp hx).1
  have hR : ∀ r ∈ RR S, ∀ x ∈ K₃, r * x * r⁻¹ ∈ K₃ := by
    intro r hr x hx
    obtain ⟨hxP, z, hz, hxz⟩ := (hmem x).mp hx
    refine (hmem _).mpr ⟨B.RR_conj_P hq hK hG hPn hr hxP, r * z * r⁻¹,
      B.RR_conj_P hq hK hG hPn hr hz, ?_⟩
    have := B.RR_conj_PP1 hq hK hG hr hxz
    have e3 : (r * z * r⁻¹) ^ 3 = r * z ^ 3 * r⁻¹ := by
      rw [show r * z * r⁻¹ = MulAut.conj r z from rfl, ← map_pow]; rfl
    have e : r * (x⁻¹ * z ^ 3) * r⁻¹ = (r * x * r⁻¹)⁻¹ * (r * z * r⁻¹) ^ 3 := by
      rw [e3]; group
    rwa [e] at this
  rcases B.eq_of_RR_inv hq hK hG hPc hP1K hKP hR with h | h
  · rw [← h]
    exact (hmem _).mpr ⟨P.pow_mem hy 3, y, hy, by simp⟩
  · exact absurd h hKne

include B hq hK hG hP1P hPc hPn in
theorem comm_PP1_mem_zcen {g a : G} (hg : g ∈ P) (ha : a ∈ PP1 S) :
    g * a * g⁻¹ * a⁻¹ ∈ zcen P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcT := B.hcT hq hK hG
  have hZn : ∀ g ∈ P, ∀ c ∈ zcen P, g * c * g⁻¹ ∈ zcen P := fun g hg c hc => by
    rw [zcen_conj hg hc]; exact hc
  have hZP : zcen P ≤ P := fun c hc => (mem_zcen.mp hc).1
  have hZne : zcen P ≠ P := by
    intro h
    have h1 := B.card_zcen hq hK hG hP1P hPc hPn
    rw [h, hPc] at h1
    have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
    have : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one] at this
    omega
  set Zs := relCen P P (zcen P) hZn with hZs
  set N₁ := relCen P (PP1 S) (zcen P) hZn with hN₁
  have hR : ∀ {H : Subgroup G}, (∀ x ∈ H, ∀ r ∈ RR S, r⁻¹ * x * r ∈ H) →
      ∀ r ∈ RR S, ∀ x ∈ relCen P H (zcen P) hZn, r * x * r⁻¹ ∈ relCen P H (zcen P) hZn :=
    fun hH r hr x hx => conj_mem_relCen (fun y hy => B.RR_conj_P hq hK hG hPn hr hy)
      (fun y hy => hH y hy r hr) (fun y hy => B.RR_conj_zcen hq hK hG hPn hr hy) hx
  have hRZs := hR (fun x hx r hr => B.RR_conj_P' hq hK hG hPn hr hx)
  have hRN₁ := hR (fun x hx r hr => B.RR_conj_PP1' hq hK hG hr hx)
  obtain ⟨z, hz, hzZ⟩ := exists_relCen_not_mem (isPGroup_P hq hPc) hZP hZn hZne
  have hZsN₁ : Zs ≤ N₁ := fun x hx => ⟨hx.1, fun h hh => hx.2 h (hP1P hh)⟩
  have hP1N₁ : PP1 S ≤ N₁ := fun b hb => ⟨hP1P hb, fun h hh => by
    rw [PP1_comm hq hK hcT hG hb hh]; simp⟩
  by_cases hsub : Zs ≤ PP1 S
  ·
    have hCZs : zcen P ≤ Zs := fun c hc => ⟨(mem_zcen.mp hc).1, fun h hh => by
      rw [(mem_zcen.mp hc).2 h hh]; simp⟩
    obtain ⟨t, ht3, ht⟩ := card_RR_inv hq hK hPc (fun x hx => hx.1 : Zs ≤ P) hRZs
    have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
    have hgt : q < Nat.card Zs := by
      have hle := Subgroup.card_le_of_le hCZs
      rw [B.card_zcen hq hK hG hP1P hPc hPn] at hle
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd ((Subgroup.eq_of_le_of_card_ge hCZs (by
          rw [B.card_zcen hq hK hG hP1P hPc hPn, h])) ▸ hz) hzZ
    have hle2 := Subgroup.card_le_of_le hsub
    rw [card_PP1 hq hK hcT hG] at hle2
    have heq : Zs = PP1 S := Subgroup.eq_of_le_of_card_ge hsub (by
      rw [card_PP1 hq hK hcT hG, ht]
      rw [ht] at hgt hle2
      have h1 : 1 < t := by
        by_contra h
        have : t ≤ 1 := by omega
        have : q ^ t ≤ q ^ 1 := Nat.pow_le_pow_right (by omega) this
        rw [pow_one] at this; omega
      exact Nat.pow_le_pow_right (by omega) h1)
    have haZ : a ∈ Zs := heq ▸ ha
    have := (zcen P).inv_mem (haZ.2 g hg)
    rwa [show (a * g * a⁻¹ * g⁻¹)⁻¹ = g * a * g⁻¹ * a⁻¹ by group] at this
  ·
    obtain ⟨w, hwZ, hwP1⟩ := Set.not_subset.mp hsub
    rcases B.eq_of_RR_inv hq hK hG hPc hP1N₁ (fun x hx => hx.1) hRN₁ with h | h
    · exact absurd (h ▸ hZsN₁ hwZ) hwP1
    · have hgN : g ∈ N₁ := h ▸ hg
      exact hgN.2 a ha

include B hq hK hG hP1P hPc hPn in
theorem mem_zcen_of_commute_outer {y a : G} (hy : y ∈ P) (hyP1 : y ∉ PP1 S) (ha : a ∈ PP1 S)
    (hay : a * y = y * a) : a ∈ zcen P := by
  by_contra haZ
  have h := B.inf_centralizer_PP1 hq hK hG hP1P hPc hPn ha haZ
  apply hyP1
  rw [← h]
  exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hay.symm⟩

include B hq hK hG hP1P hPc hPn hN1c in
theorem cube_mem_zcen {y : G} (hy : y ∈ P) (hyP1 : y ∉ PP1 S) : y ^ 3 ∈ zcen P :=
  B.mem_zcen_of_commute_outer hq hK hG hP1P hPc hPn hy hyP1
    (B.cube_mem_PP1 hq hK hG hP1P hPc hPn hN1c hy) (by rw [← pow_succ, ← pow_succ'])

include B hq hK hG hP1P hPc hPn in
theorem exists_conj_outer {y c : G} (hy : y ∈ P) (hyP1 : y ∉ PP1 S) (hc : c ∈ zcen P) :
    ∃ a ∈ PP1 S, a * y * a⁻¹ = y * c := by
  have hcomm : ∀ a ∈ PP1 S, a * y * a⁻¹ * y⁻¹ ∈ zcen P := by
    intro a ha
    have hw := B.comm_PP1_mem_zcen hq hK hG hP1P hPc hPn hy ((PP1 S).inv_mem ha)
    have e := zcen_conj (hP1P ha) hw
    rw [show a * (y * a⁻¹ * y⁻¹ * a⁻¹⁻¹) * a⁻¹ = a * y * a⁻¹ * y⁻¹ by group] at e
    rw [e]; exact hw
  have hZcomm : ∀ u ∈ zcen P, ∀ v ∈ zcen P, u * v = v * u := fun u hu v hv =>
    (mem_zcen.mp hu).2 v (mem_zcen.mp hv).1
  let φ : PP1 S →* zcen P :=
    { toFun := fun a => ⟨a * y * (a : G)⁻¹ * y⁻¹, hcomm a a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, mul_inv_rev]
        have hb := hcomm b b.2
        have e1 := zcen_conj (hP1P a.2) hb
        calc (a : G) * b * y * ((b : G)⁻¹ * (a : G)⁻¹) * y⁻¹
            = a * (b * y * (b : G)⁻¹ * y⁻¹) * (a : G)⁻¹ * (a * y * (a : G)⁻¹ * y⁻¹) := by
              group
          _ = (b * y * (b : G)⁻¹ * y⁻¹) * (a * y * (a : G)⁻¹ * y⁻¹) := by rw [e1]
          _ = (a * y * (a : G)⁻¹ * y⁻¹) * (b * y * (b : G)⁻¹ * y⁻¹) :=
              hZcomm _ hb _ (hcomm a a.2) }
  have hker : φ.ker = (zcen P).subgroupOf (PP1 S) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (a : G) * y * (a : G)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h
      apply B.mem_zcen_of_commute_outer hq hK hG hP1P hPc hPn hy hyP1 a.2
      have := congrArg (· * y) h'
      simp only [one_mul] at this
      calc (a : G) * y = (a : G) * y * (a : G)⁻¹ * y⁻¹ * y * a := by group
        _ = y * a := by rw [h']; group
    · intro h
      apply Subtype.ext
      show (a : G) * y * (a : G)⁻¹ * y⁻¹ = 1
      rw [(mem_zcen.mp h).2 y hy]; group
  have hsurj : Function.Surjective φ := by
    apply surjective_of_card_ker
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (B.zcen_le_PP1 hq hK hG hP1P hPc hPn)).toEquiv, B.card_zcen hq hK hG hP1P hPc hPn,
      card_PP1 hq hK (B.hcT hq hK hG) hG]
    ring
  obtain ⟨a, ha⟩ := hsurj ⟨c, hc⟩
  have ha' : (a : G) * y * (a : G)⁻¹ * y⁻¹ = c := congrArg Subtype.val ha
  refine ⟨a, a.2, ?_⟩
  calc (a : G) * y * (a : G)⁻¹ = (a : G) * y * (a : G)⁻¹ * y⁻¹ * y := by group
    _ = c * y := by rw [ha']
    _ = y * c := ((mem_zcen.mp hc).2 y hy)

include B hq hK hG hP1P hPc hPn in
theorem exists_conj_PP1 {a c : G} (ha : a ∈ PP1 S) (haZ : a ∉ zcen P) (hc : c ∈ zcen P) :
    ∃ g ∈ P, g * a * g⁻¹ = a * c := by
  have hcomm : ∀ g ∈ P, g * a * g⁻¹ * a⁻¹ ∈ zcen P := fun g hg =>
    B.comm_PP1_mem_zcen hq hK hG hP1P hPc hPn hg ha
  have hZcomm : ∀ u ∈ zcen P, ∀ v ∈ zcen P, u * v = v * u := fun u hu v hv =>
    (mem_zcen.mp hu).2 v (mem_zcen.mp hv).1
  let φ : P →* zcen P :=
    { toFun := fun g => ⟨g * a * (g : G)⁻¹ * a⁻¹, hcomm g g.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, mul_inv_rev]
        have hh := hcomm h h.2
        have e1 := zcen_conj g.2 hh
        calc (g : G) * h * a * ((h : G)⁻¹ * (g : G)⁻¹) * a⁻¹
            = g * (h * a * (h : G)⁻¹ * a⁻¹) * (g : G)⁻¹ * (g * a * (g : G)⁻¹ * a⁻¹) := by group
          _ = (h * a * (h : G)⁻¹ * a⁻¹) * (g * a * (g : G)⁻¹ * a⁻¹) := by rw [e1]
          _ = (g * a * (g : G)⁻¹ * a⁻¹) * (h * a * (h : G)⁻¹ * a⁻¹) :=
              hZcomm _ hh _ (hcomm g g.2) }
  have hker : φ.ker = (PP1 S).subgroupOf P := by
    rw [← B.inf_centralizer_PP1 hq hK hG hP1P hPc hPn ha haZ]
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (g : G) * a * (g : G)⁻¹ * a⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨g.2, ?_⟩
      calc (g : G) * a = (g : G) * a * (g : G)⁻¹ * a⁻¹ * a * g := by group
        _ = a * g := by rw [h']; group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show (g : G) * a * (g : G)⁻¹ * a⁻¹ = 1
      rw [h]; group
  have hsurj : Function.Surjective φ := by
    apply surjective_of_card_ker
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP1P).toEquiv,
      B.card_zcen hq hK hG hP1P hPc hPn, card_PP1 hq hK (B.hcT hq hK hG) hG, hPc]
    ring
  obtain ⟨g, hg⟩ := hsurj ⟨c, hc⟩
  have hg' : (g : G) * a * (g : G)⁻¹ * a⁻¹ = c := congrArg Subtype.val hg
  refine ⟨g, g.2, ?_⟩
  calc (g : G) * a * (g : G)⁻¹ = (g : G) * a * (g : G)⁻¹ * a⁻¹ * a := by group
    _ = c * a := by rw [hg']
    _ = a * c := ((mem_zcen.mp hc).2 a (hP1P ha))

end Block

end CFSG.Walter.WardLocal
