module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped Pointwise

structure TICountHyp {Y : Type} [Group Y] [Finite Y] (S : Sylow 2 Y) : Prop where
  card_eight : Nat.card (S : Subgroup Y) = 8
  mul_self : ∀ x ∈ (S : Subgroup Y), x * x = 1
  centralizer_spec : ∀ j : Y, orderOf j = 2 →
    Nat.card (centralizer ({j} : Set Y)) = 24 ∧
      ∃ P : Sylow 2 Y, j ∈ (P : Subgroup Y) ∧
        centralizer ({j} : Set Y) ≤ normalizer ((P : Subgroup Y) : Set Y)
  card_normalizer : Nat.card (normalizer ((S : Subgroup Y) : Set Y)) = 168

namespace TICountHyp

variable {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y}


private lemma sylow_mul_self (h : TICountHyp S) (P : Sylow 2 Y) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) : x * x = 1 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S P
  have hxP : x ∈ ((g • S : Sylow 2 Y) : Subgroup Y) := by rw [hg]; exact hx
  rw [Sylow.coe_subgroup_smul] at hxP
  obtain ⟨s, hs, hEq⟩ := Set.mem_smul_set.mp hxP
  have hxeq : x = g * s * g⁻¹ := by rw [← hEq]; simp [MulAut.conj_apply]
  have hss : s * s = 1 := h.mul_self s hs
  calc x * x = g * (s * s) * g⁻¹ := by rw [hxeq]; group
    _ = 1 := by rw [hss]; group

private lemma sylow_mul_comm (h : TICountHyp S) (P : Sylow 2 Y) {x y : Y}
    (hx : x ∈ (P : Subgroup Y)) (hy : y ∈ (P : Subgroup Y)) : x * y = y * x := by
  have hx1 : x * x = 1 := sylow_mul_self h P hx
  have hy1 : y * y = 1 := sylow_mul_self h P hy
  have hxy1 : (x * y) * (x * y) = 1 := sylow_mul_self h P (P.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  have hxyinv : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy1
  calc x * y = (x * y)⁻¹ := hxyinv.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hyinv, hxinv]

omit [Finite Y] in
private lemma sylow_eq_of_le_normalizer {P Q : Sylow 2 Y}
    (hle : (P : Subgroup Y) ≤ normalizer ((Q : Subgroup Y) : Set Y)) : P = Q := by
  have h := IsPGroup.inf_normalizer_sylow (p := 2) (P := (P : Subgroup Y)) (Q := Q)
    P.isPGroup'
  change (P : Subgroup Y) ⊓ normalizer ((Q : Subgroup Y) : Set Y) =
    (P : Subgroup Y) ⊓ (Q : Subgroup Y) at h
  rw [inf_eq_left.mpr hle] at h
  have hPQ : (P : Subgroup Y) ≤ (Q : Subgroup Y) := by
    rw [h]
    exact inf_le_right
  have hQ : (Q : Subgroup Y) = (P : Subgroup Y) := P.is_maximal' Q.isPGroup' hPQ
  exact (Sylow.ext hQ.symm)

omit [Finite Y] in
private lemma mem_sylow_of_isPGroup_two {x : Y}
    (hP : IsPGroup 2 (Subgroup.zpowers x))
    (hxN : x ∈ normalizer ((S : Subgroup Y) : Set Y)) : x ∈ (S : Subgroup Y) := by
  have hzp : Subgroup.zpowers x ≤ normalizer ((S : Subgroup Y) : Set Y) :=
    Subgroup.zpowers_le.mpr hxN
  have h := IsPGroup.inf_normalizer_sylow (p := 2) (P := Subgroup.zpowers x) (Q := S) hP
  change Subgroup.zpowers x ⊓ normalizer ((S : Subgroup Y) : Set Y) =
    Subgroup.zpowers x ⊓ (S : Subgroup Y) at h
  rw [inf_eq_left.mpr hzp] at h
  have hxP : x ∈ Subgroup.zpowers x ⊓ (S : Subgroup Y) := by
    rw [← h]
    exact Subgroup.mem_zpowers x
  exact hxP.2

private lemma centralizer_le_normalizer (h : TICountHyp S) {j : Y} (hj : orderOf j = 2)
    (hjS : j ∈ (S : Subgroup Y)) :
    Subgroup.centralizer ({j} : Set Y) ≤ normalizer ((S : Subgroup Y) : Set Y) := by
  obtain ⟨-, P₀, hjP₀, hCP₀⟩ := h.centralizer_spec j hj
  have hSle : (S : Subgroup Y) ≤ Subgroup.centralizer ({j} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sylow_mul_comm h S hx hjS
  have heq : S = P₀ := sylow_eq_of_le_normalizer (hSle.trans hCP₀)
  have hSP : (S : Subgroup Y) = (P₀ : Subgroup Y) :=
    congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) heq
  rw [hSP]
  exact hCP₀

theorem sylow_eq_of_mem (h : TICountHyp S) {P P' : Sylow 2 Y} {j : Y} (hj : orderOf j = 2)
    (hjP : j ∈ (P : Subgroup Y)) (hjP' : j ∈ (P' : Subgroup Y)) : P = P' := by
  obtain ⟨-, P₀, hjP₀, hCP₀⟩ := h.centralizer_spec j hj
  have hPle : (P : Subgroup Y) ≤ Subgroup.centralizer ({j} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sylow_mul_comm h P hx hjP
  have hP'le : (P' : Subgroup Y) ≤ Subgroup.centralizer ({j} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sylow_mul_comm h P' hx hjP'
  have hPP₀ : P = P₀ := sylow_eq_of_le_normalizer (hPle.trans hCP₀)
  have hP'P₀ : P' = P₀ := sylow_eq_of_le_normalizer (hP'le.trans hCP₀)
  rw [hPP₀, hP'P₀]

theorem mem_of_mem_normalizer (h : TICountHyp S) {x : Y} (hx : orderOf x = 2)
    (hxN : x ∈ normalizer ((S : Subgroup Y) : Set Y)) : x ∈ (S : Subgroup Y) := by
  have hS8 := h.card_eight
  clear hS8
  have hcard : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, hx]
  have hP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  exact mem_sylow_of_isPGroup_two hP hxN

omit [Finite Y] in
private lemma conj_mem_centralizer_singleton {a x z : Y} (ha2 : a * a = 1)
    (hinv : a * x * a⁻¹ = x⁻¹) (hz : z * x = x * z) :
    (a * z * a⁻¹) * x = x * (a * z * a⁻¹) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haix : a⁻¹ * x * a = x⁻¹ := by simpa [hainv] using hinv
  have hax : a * x⁻¹ * a⁻¹ = x := by
    calc a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hinv]
      _ = x := inv_inv x
  have hzx : z * x⁻¹ = x⁻¹ * z := by
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hz]
      _ = x⁻¹ * z := by group
  calc (a * z * a⁻¹) * x = a * z * (a⁻¹ * x * a) * a⁻¹ := by group
    _ = a * z * x⁻¹ * a⁻¹ := by rw [haix]
    _ = a * (z * x⁻¹) * a⁻¹ := by group
    _ = a * (x⁻¹ * z) * a⁻¹ := by rw [hzx]
    _ = (a * x⁻¹ * a⁻¹) * (a * z * a⁻¹) := by group
    _ = x * (a * z * a⁻¹) := by rw [hax]

omit [Finite Y] in
private lemma mem_normalizer_centralizer_of_inverts {a x : Y} (ha2 : a * a = 1)
    (hinv : a * x * a⁻¹ = x⁻¹) :
    a ∈ normalizer (Subgroup.centralizer ({x} : Set Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact conj_mem_centralizer_singleton ha2 hinv hz
  · intro hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have h := conj_mem_centralizer_singleton ha2 hinv hz
    have hz' : a * (a * z * a⁻¹) * a⁻¹ = z := by
      calc a * (a * z * a⁻¹) * a⁻¹ = (a * a) * z * (a⁻¹ * a⁻¹) := by group
        _ = z := by rw [ha2, hainv, ha2]; group
    rwa [hz'] at h

private lemma eq_one_of_mem_isPGroup_two_of_odd {G : Type*} [Group G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {g : G} (hg : g ∈ Q) (ho : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have hev : Even (orderOf g) := by
        rw [hk]
        exact Nat.even_pow.mpr ⟨even_two, h.ne'⟩
      exact (Nat.not_even_iff_odd.mpr ho) hev
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

omit [Finite Y] in
private lemma not_mem_of_inv_odd_normalizer {Q : Subgroup Y} (hQ : IsPGroup 2 Q) {v e : Y}
    (hvN : v ∈ normalizer (Q : Set Y)) (hv : Odd (orderOf v)) (hv1 : orderOf v ≠ 1)
    (hinv : e * v * e = v⁻¹) : e ∉ Q := by
  intro heQ
  have hvQ : ∀ q : Y, q ∈ Q → v * q * v⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hvN q).mp hq
  have hw : v⁻¹ * v⁻¹ ∈ Q := by
    have e1 : v⁻¹ * v⁻¹ = e * (v * e * v⁻¹) := by
      calc v⁻¹ * v⁻¹ = (e * v * e) * v⁻¹ := by rw [hinv]
        _ = e * (v * e * v⁻¹) := by group
    rw [e1]
    exact Q.mul_mem heQ (hvQ e heQ)
  have hodd : Odd (orderOf (v⁻¹ * v⁻¹)) := by
    have hd : orderOf (v⁻¹ * v⁻¹) ∣ orderOf v⁻¹ := by
      rw [← pow_two]
      exact orderOf_pow_dvd 2
    rw [orderOf_inv] at hd
    exact Odd.of_dvd_nat hv hd
  have h1 : v⁻¹ * v⁻¹ = 1 := eq_one_of_mem_isPGroup_two_of_odd hQ hw hodd
  have hv2 : v ^ 2 = 1 := by
    have : (v⁻¹) ^ 2 = 1 := by rw [pow_two]; exact h1
    rwa [inv_pow, inv_eq_one] at this
  have hdvd : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact hv1 h
  · rw [h] at hv
    exact absurd hv (by decide)

private lemma exists_fixed_of_smul_involution {G X : Type*} [Group G] [MulAction G X]
    [Finite X] (a : G) (ha : a * a = 1) (hodd : Odd (Nat.card X)) :
    ∃ x : X, a • x = x := by
  classical
  have : Fintype X := Fintype.ofFinite X
  let σ : Equiv.Perm X := MulAction.toPerm a
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    change a • (a • x) = x
    rw [← mul_smul, ha, one_smul]
  by_contra h
  have hsupp : σ.support = (Finset.univ : Finset X) := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro hfix
    exact h ⟨x, hfix⟩
  have h2 : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support hσ2
  rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

private lemma exists_involution_of_isPGroup_two {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsPGroup 2 H) (hne : H ≠ ⊥) :
    ∃ c : G, c ∈ H ∧ orderOf c = 2 := by
  classical
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hH).mp inferInstance
  have h2dvd : 2 ∣ Nat.card H := by
    rw [hcard]
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨k, rfl⟩
    rw [pow_succ]
    exact dvd_mul_left 2 (2 ^ k)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2dvd
  refine ⟨(c : G), c.2, ?_⟩
  rwa [← Subgroup.orderOf_mk (c : G) c.2]


private lemma false_of_involution_inverts_odd (h : TICountHyp S) {a x c : Y}
    (ha : orderOf a = 2) (hx1 : x ≠ 1) (hxo : Odd (orderOf x))
    (hinv : a * x * a⁻¹ = x⁻¹) (hc : orderOf c = 2) (hcx : c * x = x * c) : False := by
  classical
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha] at this
    simpa [pow_two] using this
  let C : Subgroup Y := Subgroup.centralizer ({x} : Set Y)
  have hcC : c ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcx
  have hdvdC : 2 ∣ Nat.card C := by
    have := Subgroup.orderOf_dvd_natCard C hcC
    rwa [hc] at this
  have haN : a ∈ normalizer (C : Set Y) := mem_normalizer_centralizer_of_inverts ha2 hinv
  let aN : normalizer (C : Set Y) := ⟨a, haN⟩
  have haN2 : aN * aN = 1 := by
    ext
    simp [aN, ha2]
  have haNinv : aN⁻¹ = aN := inv_eq_of_mul_eq_one_right haN2
  have hodd : Odd (Nat.card (Sylow 2 C)) := by
    have hnot : ¬ 2 ∣ Nat.card (Sylow 2 C) := not_dvd_card_sylow (p := 2) (G := C)
    exact Nat.not_even_iff_odd.mp (fun he => hnot (even_iff_two_dvd.mp he))
  obtain ⟨PC, hPCfix⟩ := exists_fixed_of_smul_involution aN haN2 hodd
  have hPCne : (PC : Subgroup C) ≠ ⊥ := Sylow.ne_bot_of_dvd_card PC hdvdC
  obtain ⟨cC, hcPC, hcCorder⟩ := exists_involution_of_isPGroup_two PC.isPGroup' hPCne
  let c₀ : Y := cC
  have hc₀PC : c₀ ∈ (PC : Subgroup C).map C.subtype := Subgroup.mem_map.mpr ⟨cC, hcPC, rfl⟩
  have hc₀C : c₀ ∈ C := cC.2
  have hc₀order : orderOf c₀ = 2 := by
    show orderOf (cC : Y) = 2
    rw [← Subgroup.orderOf_mk (cC : Y) cC.2]
    exact hcCorder
  let PCY : Subgroup Y := (PC : Subgroup C).map C.subtype
  have hPCsmul : ((aN • PC : Sylow 2 C) : Subgroup C) = (PC : Subgroup C) := by rw [hPCfix]
  have hsmul_mem : ∀ p : C, p ∈ (PC : Subgroup C) → aN • p ∈ (PC : Subgroup C) := by
    intro p hp
    have hp' : p ∈ ((aN • PC : Sylow 2 C) : Subgroup C) := by rw [hPCsmul]; exact hp
    rw [Sylow.pointwise_smul_def] at hp'
    have h := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := aN)
      (S := (PC : Subgroup C)) (x := p)).mp hp'
    rwa [haNinv] at h
  have hainva : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haNormPCY : a ∈ normalizer (PCY : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨p, hp, rfl⟩
      have hp' : aN • p ∈ (PC : Subgroup C) := hsmul_mem p hp
      have hcoe : ((aN • p : C) : Y) = a * (p : Y) * a⁻¹ := Subgroup.smul_coe C aN p
      change a * (p : Y) * a⁻¹ ∈ PCY
      rw [← hcoe]
      exact Subgroup.mem_map.mpr ⟨aN • p, hp', rfl⟩
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨q, hq, hqeq⟩
      have hq' : aN • q ∈ (PC : Subgroup C) := hsmul_mem q hq
      have hcoe : ((aN • q : C) : Y) = a * (q : Y) * a⁻¹ := Subgroup.smul_coe C aN q
      have hqeq' : (q : Y) = a * y * a⁻¹ := hqeq
      have hy : ((aN • q : C) : Y) = y := by
        change a * (q : Y) * a⁻¹ = y
        rw [hqeq']
        calc a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a⁻¹ * a⁻¹) := by group
          _ = y := by rw [ha2, hainva, ha2]; group
      rw [← hy]
      exact Subgroup.mem_map.mpr ⟨aN • q, hq', rfl⟩
  have hA_le : Subgroup.zpowers a ≤ normalizer (PCY : Set Y) :=
    Subgroup.zpowers_le.mpr haNormPCY
  have haP2 : IsPGroup 2 (Subgroup.zpowers a) := by
    have hcard : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, ha]
    exact IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hPCY2 : IsPGroup 2 PCY := by
    have hmap := IsPGroup.map (p := 2) (G := C) (H := (PC : Subgroup C)) PC.isPGroup'
      (C.subtype : C →* Y)
    simpa [PCY] using hmap
  have hB2 : IsPGroup 2 ↥(PCY ⊔ Subgroup.zpowers a) :=
    IsPGroup.to_sup_of_normal_left' (G := Y) hPCY2 haP2 hA_le
  obtain ⟨P, hBP⟩ := IsPGroup.exists_le_sylow hB2
  have haP : a ∈ (P : Subgroup Y) :=
    hBP (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hc₀P : c₀ ∈ (P : Subgroup Y) := hBP (Subgroup.mem_sup_left hc₀PC)
  have hx_c₀ : x * c₀ * x⁻¹ = c₀ := by
    have hcx' : c₀ * x = x * c₀ := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc₀C
      exact hc₀C
    calc x * c₀ * x⁻¹ = (c₀ * x) * x⁻¹ := by rw [← hcx']
      _ = c₀ := by group
  have hc₀_xP : c₀ ∈ ((x • P : Sylow 2 Y) : Subgroup Y) := by
    have hco : ((x • P : Sylow 2 Y) : Subgroup Y) =
        (MulAut.conj x • (P : Subgroup Y) : Subgroup Y) :=
      Sylow.coe_subgroup_smul (P := P) (g := x)
    rw [hco]
    exact Set.mem_smul_set.mpr ⟨c₀, hc₀P, by simp [MulAut.conj_apply, hx_c₀]⟩
  have hP_eq : P = x • P :=
    sylow_eq_of_mem h hc₀order hc₀P hc₀_xP
  have hxN : x ∈ normalizer ((P : Subgroup Y) : Set Y) :=
    (Sylow.smul_eq_iff_mem_normalizer).mp hP_eq.symm
  have hxodd1 : orderOf x ≠ 1 := by
    intro h1
    exact hx1 (orderOf_eq_one_iff.mp h1)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hinv' : a * x * a = x⁻¹ := by simpa [hainv] using hinv
  exact not_mem_of_inv_odd_normalizer P.isPGroup' hxN hxo hxodd1 hinv' haP


private lemma ncard_eq_natCard {α : Type*} [Finite α] (s : Set α) :
    s.ncard = Nat.card {x : α // x ∈ s} := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hfin : s.Finite := Set.toFinite s
  rw [Set.ncard_eq_toFinset_card s hfin, Nat.card_eq_card_toFinset s]
  congr 1
  ext x
  rw [Set.Finite.mem_toFinset, Set.mem_toFinset]

private lemma orderOf_eq_two_of_mem_sylow (h : TICountHyp S) {x : Y}
    (hxS : x ∈ (S : Subgroup Y)) (hx1 : x ≠ 1) : orderOf x = 2 := by
  have hx2 : x * x = 1 := h.mul_self x hxS
  exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hx2) hx1

private lemma ncard_involutions_normalizer (h : TICountHyp S) :
    Set.ncard {y : Y | orderOf y = 2 ∧ y ∈ normalizer ((S : Subgroup Y) : Set Y)} = 7 := by
  classical
  have hset : {y : Y | orderOf y = 2 ∧ y ∈ normalizer ((S : Subgroup Y) : Set Y)} =
      ((S : Subgroup Y) : Set Y) \ {1} := by
    ext y
    constructor
    · rintro ⟨hy2, hyN⟩
      refine ⟨mem_of_mem_normalizer h hy2 hyN, ?_⟩
      intro hy1
      rw [Set.mem_singleton_iff] at hy1
      rw [hy1] at hy2
      simp at hy2
    · rintro ⟨hyS, hy1⟩
      refine ⟨orderOf_eq_two_of_mem_sylow h hyS ?_, Subgroup.le_normalizer hyS⟩
      intro hy
      exact hy1 (by simpa using hy)
  rw [hset]
  have hsub : ({1} : Set Y) ⊆ ((S : Subgroup Y) : Set Y) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact S.one_mem
  rw [Set.ncard_sdiff hsub]
  have hScard : ((S : Subgroup Y) : Set Y).ncard = 8 := by
    rw [ncard_eq_natCard]
    exact h.card_eight
  rw [hScard, Set.ncard_singleton]

private lemma centralizer_relIndex_normalizer (h : TICountHyp S) {j₀ : Y}
    (hj₀ : orderOf j₀ = 2) (hj₀S : j₀ ∈ (S : Subgroup Y)) :
    (Subgroup.centralizer ({j₀} : Set Y)).relIndex
        (normalizer ((S : Subgroup Y) : Set Y)) = 7 := by
  have hJ24 : Nat.card (Subgroup.centralizer ({j₀} : Set Y)) = 24 :=
    (h.centralizer_spec j₀ hj₀).1
  have hN168 : Nat.card (normalizer ((S : Subgroup Y) : Set Y)) = 168 := h.card_normalizer
  have hJN : Subgroup.centralizer ({j₀} : Set Y) ≤
      normalizer ((S : Subgroup Y) : Set Y) := centralizer_le_normalizer h hj₀ hj₀S
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer ({j₀} : Set Y))
    (normalizer ((S : Subgroup Y) : Set Y))
  rw [inf_eq_left.mpr hJN, hJ24, hN168] at hmul
  omega

omit [Finite Y] in
private lemma ncard_cosets_in_normalizer {N J : Subgroup Y} :
    Set.ncard {q : Y ⧸ J | ∃ n : N, (n : Y ⧸ J) = q} = (J.subgroupOf N).index := by
  classical
  let Kset : Set (Y ⧸ J) := {q : Y ⧸ J | ∃ n : N, (n : Y ⧸ J) = q}
  let F : (N ⧸ J.subgroupOf N) → (Y ⧸ J) :=
    fun q => ((Quotient.out q : N) : Y ⧸ J)
  have hFmem : ∀ q : (N ⧸ J.subgroupOf N), F q ∈ Kset := fun q => ⟨Quotient.out q, rfl⟩
  have hFinj : Function.Injective F := by
    intro q1 q2 hq
    have hmem : ((Quotient.out q1 : N) : Y)⁻¹ * ((Quotient.out q2 : N) : Y) ∈ J :=
      QuotientGroup.eq.mp hq
    have hmem' : (Quotient.out q1 : N)⁻¹ * (Quotient.out q2 : N) ∈ J.subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr hmem
    have hqeq : QuotientGroup.mk (Quotient.out q1) =
        QuotientGroup.mk (Quotient.out q2) :=
      QuotientGroup.eq.mpr hmem'
    calc q1 = QuotientGroup.mk (Quotient.out q1) := (Quotient.out_eq q1).symm
      _ = QuotientGroup.mk (Quotient.out q2) := hqeq
      _ = q2 := Quotient.out_eq q2
  have hFsurj : ∀ q : Y ⧸ J, q ∈ Kset → ∃ q0 : (N ⧸ J.subgroupOf N), F q0 = q := by
    rintro q ⟨n, hn⟩
    refine ⟨QuotientGroup.mk n, ?_⟩
    have hout : (Quotient.out (QuotientGroup.mk n : N ⧸ J.subgroupOf N) : N)⁻¹ * n ∈
        J.subgroupOf N :=
      QuotientGroup.eq.mp (Quotient.out_eq (QuotientGroup.mk n : N ⧸ J.subgroupOf N))
    have houtJ : ((Quotient.out (QuotientGroup.mk n : N ⧸ J.subgroupOf N) : N) : Y)⁻¹ *
        (n : Y) ∈ J :=
      Subgroup.mem_subgroupOf.mp hout
    have hcos : (((Quotient.out (QuotientGroup.mk n : N ⧸ J.subgroupOf N) : N) : Y) : Y ⧸ J) =
        (n : Y ⧸ J) := by
      rw [QuotientGroup.eq]
      exact houtJ
    exact hcos.trans hn
  have hcard : Kset.ncard = Nat.card (N ⧸ J.subgroupOf N) := by
    have h := Set.ncard_congr (s := (Set.univ : Set (N ⧸ J.subgroupOf N))) (t := Kset)
      (fun q _ => F q) (fun q _ => hFmem q) (fun q1 q2 _ _ h => hFinj h)
      (fun q hq => by
        obtain ⟨q0, hq0⟩ := hFsurj q hq
        exact ⟨q0, trivial, hq0⟩)
    rw [Set.ncard_univ] at h
    exact h.symm
  change Kset.ncard = (J.subgroupOf N).index
  rw [hcard, Subgroup.index_eq_card]

private lemma eq_of_involution_coset_eq (h : TICountHyp S) {j₀ : Y}
    (hj₀ : orderOf j₀ = 2) (hj₀S : j₀ ∈ (S : Subgroup Y))
    {a b : Y} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (haN : a ∉ normalizer ((S : Subgroup Y) : Set Y))
    (hcos : (a : Y ⧸ Subgroup.centralizer ({j₀} : Set Y)) =
      (b : Y ⧸ Subgroup.centralizer ({j₀} : Set Y))) : a = b := by
  classical
  set J : Subgroup Y := Subgroup.centralizer ({j₀} : Set Y) with hJ
  by_contra hab
  have hxJ : a⁻¹ * b ∈ J := QuotientGroup.eq.mp hcos
  have hx1 : a⁻¹ * b ≠ 1 := by
    intro h1
    exact hab (inv_mul_eq_one.mp h1)
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha] at this
    simpa [pow_two] using this
  have hb2 : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rw [hb] at this
    simpa [pow_two] using this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hinv : a * (a⁻¹ * b) * a⁻¹ = (a⁻¹ * b)⁻¹ := by
    calc a * (a⁻¹ * b) * a⁻¹ = (a * a⁻¹) * b * a⁻¹ := by group
      _ = b * a := by rw [hainv, ha2]; group
      _ = (a⁻¹ * b)⁻¹ := by rw [mul_inv_rev, hbinv, inv_inv]
  have hxj : (a⁻¹ * b) * j₀ = j₀ * (a⁻¹ * b) :=
    Subgroup.mem_centralizer_singleton_iff.mp hxJ
  have hxN : a⁻¹ * b ∈ normalizer ((S : Subgroup Y) : Set Y) :=
    (centralizer_le_normalizer h hj₀ hj₀S) hxJ
  obtain ⟨e, m, hm_odd, hxord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (show orderOf (a⁻¹ * b) ≠ 0 from
      (orderOf_pos (a⁻¹ * b)).ne')
  have hdvd : 2 ^ e ∣ orderOf (a⁻¹ * b) := by
    rw [hxord]
    exact dvd_mul_right (2 ^ e) m
  rcases eq_or_ne m 1 with hm1 | hm1
  · have hxord' : orderOf (a⁻¹ * b) = 2 ^ e := by rw [hxord, hm1, mul_one]
    have hP : IsPGroup 2 (Subgroup.zpowers (a⁻¹ * b)) := by
      apply IsPGroup.of_card (n := e)
      rw [Nat.card_zpowers, hxord']
    have hxS : a⁻¹ * b ∈ (S : Subgroup Y) := mem_sylow_of_isPGroup_two hP hxN
    have hx2 : (a⁻¹ * b) * (a⁻¹ * b) = 1 := h.mul_self _ hxS
    have hxorder2 : orderOf (a⁻¹ * b) = 2 :=
      orderOf_eq_prime (p := 2) (by simpa [pow_two] using hx2) hx1
    have haC : a ∈ Subgroup.centralizer ({a⁻¹ * b} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxself : (a⁻¹ * b)⁻¹ = a⁻¹ * b := inv_eq_of_mul_eq_one_right hx2
      have heq : a * (a⁻¹ * b) * a⁻¹ = a⁻¹ * b := by rw [hinv, hxself]
      calc a * (a⁻¹ * b) = (a * (a⁻¹ * b) * a⁻¹) * a := by group
        _ = (a⁻¹ * b) * a := by rw [heq]
    exact haN ((centralizer_le_normalizer h hxorder2 hxS) haC)
  · have hxo_order : orderOf ((a⁻¹ * b) ^ (2 ^ e)) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero e (by norm_num)) hdvd, hxord,
        Nat.mul_div_cancel_left m (pow_pos (by norm_num) e)]
    have hxo_ne : (a⁻¹ * b) ^ (2 ^ e) ≠ 1 := by
      intro h1
      have h1' : orderOf ((a⁻¹ * b) ^ (2 ^ e)) = 1 := orderOf_eq_one_iff.mpr h1
      rw [hxo_order] at h1'
      exact hm1 h1'
    have hxo_odd : Odd (orderOf ((a⁻¹ * b) ^ (2 ^ e))) := by
      rw [hxo_order]; exact hm_odd
    have hconjpow : a * (a⁻¹ * b) ^ (2 ^ e) * a⁻¹ =
        (a * (a⁻¹ * b) * a⁻¹) ^ (2 ^ e) := by
      simpa [MulAut.conj_apply] using map_pow (MulAut.conj a) (a⁻¹ * b) (2 ^ e)
    have hxo_inv : a * (a⁻¹ * b) ^ (2 ^ e) * a⁻¹ =
        ((a⁻¹ * b) ^ (2 ^ e))⁻¹ := by
      rw [hconjpow, hinv, inv_pow]
    have hcomm : Commute (a⁻¹ * b) j₀ := hxj
    have hxo_comm : j₀ * (a⁻¹ * b) ^ (2 ^ e) = (a⁻¹ * b) ^ (2 ^ e) * j₀ :=
      (hcomm.pow_left (2 ^ e)).symm
    exact false_of_involution_inverts_odd h ha hxo_ne hxo_odd hxo_inv hj₀ hxo_comm

private lemma ncard_inv_outside_le (h : TICountHyp S) {j₀ : Y} (hj₀ : orderOf j₀ = 2)
    (hj₀S : j₀ ∈ (S : Subgroup Y)) :
    Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} ≤
      (Subgroup.centralizer ({j₀} : Set Y)).index - 7 := by
  classical
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let J : Subgroup Y := Subgroup.centralizer ({j₀} : Set Y)
  have hJN : J ≤ N := centralizer_le_normalizer h hj₀ hj₀S
  let InvOut : Set Y := {y : Y | orderOf y = 2 ∧ y ∉ N}
  let Kset : Set (Y ⧸ J) := {q : Y ⧸ J | ∃ n : N, (n : Y ⧸ J) = q}
  let CosOut : Set (Y ⧸ J) := Ksetᶜ
  have hKcard : Kset.ncard = 7 := by
    have hKcount := ncard_cosets_in_normalizer (N := N) (J := J)
    have hrel : (J.subgroupOf N).index = 7 := centralizer_relIndex_normalizer h hj₀ hj₀S
    rw [hrel] at hKcount
    exact hKcount
  have hCosOutCard : CosOut.ncard = J.index - 7 := by
    have hcompl : CosOut.ncard = Nat.card (Y ⧸ J) - Kset.ncard := by
      change (Ksetᶜ).ncard = Nat.card (Y ⧸ J) - Kset.ncard
      exact Set.ncard_compl Kset
    rw [hcompl, hKcard]
    congr 1
  have hmaps : ∀ y ∈ InvOut, (y : Y ⧸ J) ∈ CosOut := by
    intro y hy
    simp only [InvOut, Set.mem_setOf_eq] at hy
    simp only [CosOut, Kset, Set.mem_compl_iff, Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    have hmem : (n : Y)⁻¹ * y ∈ J := QuotientGroup.eq.mp hn
    have hmemN : (n : Y)⁻¹ * y ∈ N := hJN hmem
    have hyN : y ∈ N := by
      have h1 : y = (n : Y) * ((n : Y)⁻¹ * y) := by group
      rw [h1]
      exact N.mul_mem n.2 hmemN
    exact hy.2 hyN
  have hinj : Set.InjOn (fun y : Y => (y : Y ⧸ J)) InvOut := by
    intro a ha b hb hab
    simp only [InvOut, Set.mem_setOf_eq] at ha hb
    exact eq_of_involution_coset_eq h hj₀ hj₀S ha.1 hb.1 ha.2 hab
  calc InvOut.ncard ≤ CosOut.ncard :=
        Set.ncard_le_ncard_of_injOn (fun y : Y => (y : Y ⧸ J)) hmaps hinj
    _ = J.index - 7 := hCosOutCard


private lemma index_centralizer_le_ncard_inv_outside_add_seven (h : TICountHyp S) {j₀ : Y}
    (hj₀ : orderOf j₀ = 2) :
    (Subgroup.centralizer ({j₀} : Set Y)).index ≤
      Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} + 7 := by
  classical
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let J : Subgroup Y := Subgroup.centralizer ({j₀} : Set Y)
  let InvOut : Set Y := {y : Y | orderOf y = 2 ∧ y ∉ N}
  let InvN : Set Y := {y : Y | orderOf y = 2 ∧ y ∈ N}
  let Cl : Set Y := conjugatesOf j₀
  have hJindex : J.index = Cl.ncard := Subgroup.index_centralizer_eq_ncard j₀
  have hInvN : InvN.ncard = 7 := ncard_involutions_normalizer h
  have hCl_inv : Cl ⊆ {y : Y | orderOf y = 2} := by
    intro y hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    change orderOf y = 2
    rw [← hc]
    have horder := MulEquiv.orderOf_eq (MulAut.conj c) j₀
    simpa [MulAut.conj_apply] using horder.trans hj₀
  have hClN_sub : Cl ∩ (N : Set Y) ⊆ InvN := by
    intro y hy
    exact ⟨hCl_inv hy.1, hy.2⟩
  have hClOut_sub : Cl \ (N : Set Y) ⊆ InvOut := by
    intro y hy
    exact ⟨hCl_inv hy.1, hy.2⟩
  have hsplit := Set.ncard_inter_add_ncard_diff_eq_ncard Cl (N : Set Y)
  have hClNle : (Cl ∩ (N : Set Y)).ncard ≤ 7 := by
    calc (Cl ∩ (N : Set Y)).ncard ≤ InvN.ncard := Set.ncard_le_ncard hClN_sub
      _ = 7 := hInvN
  have hClOutle : (Cl \ (N : Set Y)).ncard ≤ InvOut.ncard :=
    Set.ncard_le_ncard hClOut_sub
  rw [hJindex]
  change Cl.ncard ≤ InvOut.ncard + 7
  omega

theorem card_inv_outside (h : TICountHyp S) :
    (Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} + 7) * 24 =
      Nat.card Y := by
  classical
  have hSne : (S : Subgroup Y) ≠ ⊥ := by
    intro hbot
    have h8 := h.card_eight
    rw [hbot] at h8
    simp at h8
  obtain ⟨j₀, hj₀S, hj₀⟩ := exists_involution_of_isPGroup_two S.isPGroup' hSne
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let J : Subgroup Y := Subgroup.centralizer ({j₀} : Set Y)
  let i : ℕ := Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)}
  have hupper : i ≤ J.index - 7 := ncard_inv_outside_le h hj₀ hj₀S
  have hlower : J.index ≤ i + 7 :=
    index_centralizer_le_ncard_inv_outside_add_seven h hj₀
  have hJ24 : Nat.card J = 24 := (h.centralizer_spec j₀ hj₀).1
  have hJi : J.index * 24 = Nat.card Y := by
    have := Subgroup.index_mul_card J
    rwa [hJ24] at this
  have hJN : J ≤ N := centralizer_le_normalizer h hj₀ hj₀S
  have hrel : J.relIndex N = 7 := centralizer_relIndex_normalizer h hj₀ hj₀S
  have hJidx7 : J.index = 7 * N.index := by
    have := Subgroup.relIndex_mul_index hJN
    rw [hrel] at this
    exact this.symm
  have hNpos : 0 < N.index := by
    have hmul := Subgroup.index_mul_card N
    have hNcard : Nat.card N = 168 := h.card_normalizer
    by_contra h0
    have hzero : N.index = 0 := Nat.eq_zero_of_not_pos h0
    rw [hzero, zero_mul] at hmul
    have hYpos : 0 < Nat.card Y := Nat.card_pos
    omega
  have hJ7 : 7 ≤ J.index := by
    rw [hJidx7]
    omega
  have hi_eq : i + 7 = J.index := by
    omega
  change (i + 7) * 24 = Nat.card Y
  rw [hi_eq, hJi]

private lemma exists_unique_involution_coset (h : TICountHyp S) {j₀ : Y}
    (hj₀ : orderOf j₀ = 2) (hj₀S : j₀ ∈ (S : Subgroup Y))
    {g : Y} (hgN : g ∉ normalizer ((S : Subgroup Y) : Set Y)) :
    ∃! w : Y, orderOf w = 2 ∧
      (w : Y ⧸ Subgroup.centralizer ({j₀} : Set Y)) =
        (g : Y ⧸ Subgroup.centralizer ({j₀} : Set Y)) := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let J : Subgroup Y := Subgroup.centralizer ({j₀} : Set Y)
  have hJN : J ≤ N := centralizer_le_normalizer h hj₀ hj₀S
  let InvOut : Set Y := {y : Y | orderOf y = 2 ∧ y ∉ N}
  let Kset : Set (Y ⧸ J) := {q : Y ⧸ J | ∃ n : N, (n : Y ⧸ J) = q}
  let CosOut : Set (Y ⧸ J) := Ksetᶜ
  have hKcard : Kset.ncard = 7 := by
    have hKcount := ncard_cosets_in_normalizer (N := N) (J := J)
    have hrel : (J.subgroupOf N).index = 7 := centralizer_relIndex_normalizer h hj₀ hj₀S
    rw [hrel] at hKcount
    exact hKcount
  have hCosOut_card : CosOut.ncard = J.index - 7 := by
    have hcompl : CosOut.ncard = Nat.card (Y ⧸ J) - Kset.ncard := by
      change (Ksetᶜ).ncard = Nat.card (Y ⧸ J) - Kset.ncard
      exact Set.ncard_compl Kset
    rw [hcompl, hKcard]
    congr 1
  have hInvOut_card : InvOut.ncard = J.index - 7 := by
    have hJ24 : Nat.card J = 24 := (h.centralizer_spec j₀ hj₀).1
    have hJi : J.index * 24 = Nat.card Y := by
      have := Subgroup.index_mul_card J
      rwa [hJ24] at this
    have hi7 : InvOut.ncard + 7 = J.index := by
      have hstep := h.card_inv_outside
      change (InvOut.ncard + 7) * 24 = Nat.card Y at hstep
      rw [← hJi] at hstep
      exact Nat.mul_right_cancel (by norm_num : (0 : ℕ) < 24) hstep
    omega
  have hmaps : ∀ y ∈ InvOut, (y : Y ⧸ J) ∈ CosOut := by
    intro y hy
    simp only [InvOut, Set.mem_setOf_eq] at hy
    simp only [CosOut, Kset, Set.mem_compl_iff, Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    have hmem : (n : Y)⁻¹ * y ∈ J := QuotientGroup.eq.mp hn
    have hmemN : (n : Y)⁻¹ * y ∈ N := hJN hmem
    have hyN : y ∈ N := by
      have h1 : y = (n : Y) * ((n : Y)⁻¹ * y) := by group
      rw [h1]
      exact N.mul_mem n.2 hmemN
    exact hy.2 hyN
  have hgCosOut : (g : Y ⧸ J) ∈ CosOut := by
    simp only [CosOut, Kset, Set.mem_compl_iff, Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    have hmem : (n : Y)⁻¹ * g ∈ J := QuotientGroup.eq.mp hn
    have hmemN : (n : Y)⁻¹ * g ∈ N := hJN hmem
    have hgN' : g ∈ N := by
      have h1 : g = (n : Y) * ((n : Y)⁻¹ * g) := by group
      rw [h1]
      exact N.mul_mem n.2 hmemN
    exact hgN hgN'
  let F : {y : Y // y ∈ InvOut} → {q : Y ⧸ J // q ∈ CosOut} :=
    fun y => ⟨(y.1 : Y ⧸ J), hmaps y.1 y.2⟩
  have hFinj : Function.Injective F := by
    intro y1 y2 hy
    have hcos : (y1.1 : Y ⧸ J) = (y2.1 : Y ⧸ J) := congrArg Subtype.val hy
    exact Subtype.ext (eq_of_involution_coset_eq h hj₀ hj₀S y1.2.1 y2.2.1 y1.2.2 hcos)
  have hcard_eq : Fintype.card {y : Y // y ∈ InvOut} =
      Fintype.card {q : Y ⧸ J // q ∈ CosOut} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [← ncard_eq_natCard, ← ncard_eq_natCard, hInvOut_card, hCosOut_card]
  have hbij := (Fintype.bijective_iff_injective_and_card F).mpr ⟨hFinj, hcard_eq⟩
  let q0 : {q : Y ⧸ J // q ∈ CosOut} := ⟨(g : Y ⧸ J), hgCosOut⟩
  obtain ⟨y0, hy0⟩ := hbij.2 q0
  have hy0val : (y0.1 : Y ⧸ J) = (g : Y ⧸ J) := congrArg Subtype.val hy0
  refine ⟨y0.1, ⟨y0.2.1, hy0val⟩, ?_⟩
  intro w hw
  have hwcos : (w : Y ⧸ J) = (y0.1 : Y ⧸ J) := hw.2.trans hy0val.symm
  exact (eq_of_involution_coset_eq h hj₀ hj₀S y0.2.1 hw.1 y0.2.2 hwcos.symm).symm

theorem seven_le_card_inv_coset (h : TICountHyp S) {u : Y} (hu : orderOf u = 2)
    (huN : u ∉ normalizer ((S : Subgroup Y) : Set Y)) :
    7 ≤ Set.ncard {w : Y | orderOf w = 2 ∧ w * u⁻¹ ∈ normalizer ((S : Subgroup Y) : Set Y)} := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  have hSne : (S : Subgroup Y) ≠ ⊥ := by
    intro hbot
    have h8 := h.card_eight
    rw [hbot] at h8
    simp at h8
  obtain ⟨j₀, hj₀S, hj₀⟩ := exists_involution_of_isPGroup_two S.isPGroup' hSne
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let J : Subgroup Y := Subgroup.centralizer ({j₀} : Set Y)
  have hJN : J ≤ N := centralizer_le_normalizer h hj₀ hj₀S
  let Q : Type := N ⧸ J.subgroupOf N
  have hQcard : Nat.card Q = 7 := by
    have hQidx := Subgroup.index_eq_card (J.subgroupOf N)
    have hrel : J.relIndex N = 7 := centralizer_relIndex_normalizer h hj₀ hj₀S
    change (J.subgroupOf N).index = 7 at hrel
    rw [hrel] at hQidx
    exact hQidx.symm
  let R : Set Y := {w : Y | orderOf w = 2 ∧ w * u⁻¹ ∈ N}
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa [pow_two] using this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hex : ∀ q : Q, ∃ w : Y, orderOf w = 2 ∧
      (w : Y ⧸ J) = ((u * (Quotient.out q : N) : Y) : Y ⧸ J) := by
    intro q
    have hgN : u * (Quotient.out q : N) ∉ N := by
      intro hmem
      have huN' : u ∈ N := by
        have h1 : u = (u * (Quotient.out q : N)) * (Quotient.out q : N)⁻¹ := by
          push_cast
          group
        rw [h1]
        exact N.mul_mem hmem (N.inv_mem (Quotient.out q).2)
      exact huN huN'
    obtain ⟨w, hw, -⟩ := exists_unique_involution_coset h hj₀ hj₀S hgN
    exact ⟨w, hw⟩
  let wOf : Q → Y := fun q => Classical.choose (hex q)
  have hwOf : ∀ q : Q, orderOf (wOf q) = 2 ∧
      (wOf q : Y ⧸ J) = ((u * (Quotient.out q : N) : Y) : Y ⧸ J) :=
    fun q => Classical.choose_spec (hex q)
  have hwOf_R : ∀ q : Q, wOf q ∈ R := by
    intro q
    have hspec := hwOf q
    have hcos : (wOf q : Y ⧸ J) = ((u * (Quotient.out q : N) : Y) : Y ⧸ J) := hspec.2
    have hmemJ : (wOf q)⁻¹ * (u * (Quotient.out q : N)) ∈ J := QuotientGroup.eq.mp hcos
    have hw2 : (wOf q) * (wOf q) = 1 := by
      have := pow_orderOf_eq_one (wOf q)
      rw [hspec.1] at this
      simpa [pow_two] using this
    have hwinv : (wOf q)⁻¹ = wOf q := inv_eq_of_mul_eq_one_right hw2
    have hmemN : (wOf q) * u⁻¹ ∈ N := by
      have heq : (wOf q) * u⁻¹ =
          ((wOf q)⁻¹ * (u * (Quotient.out q : N))) * (Quotient.out q : N)⁻¹ := by
        rw [hwinv, huinv]
        push_cast
        group
      rw [heq]
      exact N.mul_mem (hJN hmemJ) (N.inv_mem (Quotient.out q).2)
    exact ⟨hspec.1, hmemN⟩
  have hInj : Set.InjOn wOf Set.univ := by
    intro q1 _ q2 _ heq
    have hspec1 := hwOf q1
    have hspec2 := hwOf q2
    have hcos : ((u * (Quotient.out q1 : N) : Y) : Y ⧸ J) =
        ((u * (Quotient.out q2 : N) : Y) : Y ⧸ J) := by
      rw [← hspec1.2, ← hspec2.2, heq]
    have hmemJ : (u * (Quotient.out q1 : N))⁻¹ * (u * (Quotient.out q2 : N)) ∈ J :=
      QuotientGroup.eq.mp hcos
    have hcoeeq : (((Quotient.out q1 : N)⁻¹ * (Quotient.out q2 : N) : N) : Y) =
        (u * (Quotient.out q1 : N))⁻¹ * (u * (Quotient.out q2 : N)) := by
      push_cast
      rw [mul_inv_rev, huinv]
      calc (↑(Quotient.out q1))⁻¹ * ↑(Quotient.out q2)
          = (↑(Quotient.out q1))⁻¹ * (u * u) * ↑(Quotient.out q2) := by rw [hu2]; group
        _ = (↑(Quotient.out q1))⁻¹ * u * (u * ↑(Quotient.out q2)) := by group
    have hmemJ' : (Quotient.out q1 : N)⁻¹ * (Quotient.out q2 : N) ∈ J.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf, hcoeeq]
      exact hmemJ
    have hqeq : QuotientGroup.mk (Quotient.out q1) = QuotientGroup.mk (Quotient.out q2) :=
      QuotientGroup.eq.mpr hmemJ'
    calc q1 = QuotientGroup.mk (Quotient.out q1) := (Quotient.out_eq q1).symm
      _ = QuotientGroup.mk (Quotient.out q2) := hqeq
      _ = q2 := Quotient.out_eq q2
  have hle : Nat.card Q ≤ R.ncard := by
    have h := Set.ncard_le_ncard_of_injOn wOf (fun q _ => hwOf_R q) hInj
    rwa [Set.ncard_univ] at h
  change 7 ≤ R.ncard
  omega



end TICountHyp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
