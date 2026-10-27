module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

universe u

variable {G : Type u} [Group G]

namespace B2F

theorem mem_of_odd_orderOf_of_pow_mem {N : Subgroup G} {x : G} (hx : Odd (orderOf x)) {k : ℕ}
    (h : x ^ 2 ^ k ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) := (Nat.coprime_two_left.2 hx).pow_left k
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hexp : (((2 ^ k : ℕ) : ℤ) * a + (orderOf x : ℤ) * b) = 1 := by
    rw [← hab]
    ring
  have h1 : x = (x ^ 2 ^ k) ^ a := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ (((2 ^ k : ℕ) : ℤ) * a + (orderOf x : ℤ) * b) := by rw [hexp]
      _ = (x ^ 2 ^ k) ^ a := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
          one_zpow, mul_one]
  rw [h1]
  exact Subgroup.zpow_mem N h a

theorem exists_odd_pow_eq [Finite G] (x j : G) (hx : Odd (orderOf x)) :
    ∃ e : ℕ, x ^ e = x ∧ Odd (orderOf (j ^ e)) := by
  obtain ⟨a, b, hb, hN⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf x) := (Nat.coprime_two_left.2 hx).pow_left a
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hcop 0 1
  have he1' : e % orderOf x = 1 % orderOf x := he1
  refine ⟨e, ?_, ?_⟩
  · calc x ^ e = x ^ (e % orderOf x) := (pow_mod_orderOf x e).symm
      _ = x ^ (1 % orderOf x) := by rw [he1']
      _ = x ^ 1 := pow_mod_orderOf x 1
      _ = x := pow_one x
  · obtain ⟨s, hs⟩ := (Nat.modEq_zero_iff_dvd).1 he0
    have h1 : (j ^ e) ^ b = 1 := by
      rw [← pow_mul, hs, show 2 ^ a * s * b = Nat.card G * s by rw [hN]; ring, pow_mul,
        pow_card_eq_one', one_pow]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one h1)

theorem exists_pow_mul_mem {I : Subgroup G} {i o : G} (hi : i ∈ I)
    (ho : o ∈ Subgroup.normalizer (I : Set G)) (n : ℕ) : ∃ j ∈ I, (i * o) ^ n = j * o ^ n := by
  induction n with
  | zero => exact ⟨1, I.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨j, hj, h⟩ := ih
    refine ⟨j * (o ^ n * i * (o ^ n)⁻¹), I.mul_mem hj ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (I : Set G)).pow_mem ho n) i).1 hi
    · rw [pow_succ, h]
      group

theorem mem_of_odd_orderOf_mul {I : Subgroup G} {i o : G} (hi : i ∈ I)
    (ho : o ∈ Subgroup.normalizer (I : Set G)) (ho2 : ∃ a : ℕ, o ^ 2 ^ a = 1)
    (hx : Odd (orderOf (i * o))) : i * o ∈ I := by
  obtain ⟨a, ha⟩ := ho2
  obtain ⟨j, hj, h⟩ := exists_pow_mul_mem hi ho (2 ^ a)
  rw [ha, mul_one] at h
  exact mem_of_odd_orderOf_of_pow_mem hx (k := a) (h ▸ hj)

theorem normal_closure_odd : (Subgroup.closure {x : G | Odd (orderOf x)}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    show Odd (orderOf (g * x * g⁻¹))
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    rw [show g * x * g⁻¹ = (MulAut.conj g).toMonoidHom x from rfl, this]
    exact hx
  | one => simp
  | mul x y hx hy ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x hx ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih

theorem pResidualOf_top_eq_closure_odd [Finite G] :
    pResidualOf 2 (⊤ : Subgroup G) = Subgroup.closure {x : G | Odd (orderOf x)} := by
  set K := Subgroup.closure {x : G | Odd (orderOf x)} with hK
  have : K.Normal := normal_closure_odd
  apply le_antisymm
  · have h1 : pResidual 2 (⊤ : Subgroup G) ≤ K.comap (⊤ : Subgroup G).subtype := by
      refine pResidual_le fun x => ?_
      obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
      refine ⟨k, Subgroup.mem_comap.2 (Subgroup.subset_closure ?_)⟩
      show Odd (orderOf ((x : G) ^ 2 ^ k))
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hk⟩, hk]
      simpa using hm
    exact (Subgroup.map_mono h1).trans (Subgroup.map_comap_le _ _)
  · rw [Subgroup.closure_le]
    intro x hx
    refine Subgroup.mem_map.2 ⟨⟨x, Subgroup.mem_top x⟩, ?_, rfl⟩
    rw [pResidual, Subgroup.mem_iInf]
    intro N
    rw [Subgroup.mem_iInf]
    intro hN
    rw [Subgroup.mem_iInf]
    intro hpow
    obtain ⟨k, hk⟩ := hpow ⟨x, Subgroup.mem_top x⟩
    refine mem_of_odd_orderOf_of_pow_mem ?_ hk
    rw [← Subgroup.orderOf_coe]
    exact hx

theorem normal_pResidualOf_top [Finite G] : (pResidualOf 2 (⊤ : Subgroup G)).Normal := by
  rw [pResidualOf_top_eq_closure_odd]
  exact normal_closure_odd

theorem mem_pResidualOf_top_of_odd [Finite G] {x : G} (hx : Odd (orderOf x)) :
    x ∈ pResidualOf 2 (⊤ : Subgroup G) := by
  rw [pResidualOf_top_eq_closure_odd]
  exact Subgroup.subset_closure hx

end B2F

instance instNormalOpenPCore (r : ℕ) (L : Type*) [Group L] : (CFSG.Open.pCore r L).Normal :=
  CFSG.LieType.BorelTits.pCore_normal r

@[expose] noncomputable def oTwoPhi (L : Subgroup G) : Subgroup G :=
  ((frattini (↥L ⧸ CFSG.Open.pCore 2 ↥L)).comap
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L))).map L.subtype

namespace B2F

theorem exists_mul_of_le_sup_oTwoPhi [Finite G] {L K : Subgroup G} (hKL : K ≤ L)
    (h : L ≤ K ⊔ oTwoPhi L) : ∀ l ∈ L, ∃ k ∈ K, ∃ o ∈ pCoreOf 2 L, l = k * o := by
  intro l hl
  set P : Subgroup ↥L := CFSG.Open.pCore 2 ↥L with hP
  have hsurj : Function.Surjective (QuotientGroup.mk' P) := QuotientGroup.mk'_surjective P
  set F : Subgroup ↥L := (frattini (↥L ⧸ P)).comap (QuotientGroup.mk' P) with hF
  have h1 : K.subgroupOf L ⊔ F = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL, Subgroup.map_top,
      Subgroup.range_subtype]
    exact le_antisymm (sup_le hKL (Subgroup.map_subtype_le _)) h
  have h2 : (K.subgroupOf L).map (QuotientGroup.mk' P) ⊔ frattini (↥L ⧸ P) = ⊤ := by
    have h3 := congrArg (Subgroup.map (QuotientGroup.mk' P)) h1
    rwa [Subgroup.map_sup, hF, Subgroup.map_comap_eq_self_of_surjective hsurj, Subgroup.map_top,
      MonoidHom.range_eq_top.2 hsurj] at h3
  have h3 : (K.subgroupOf L).map (QuotientGroup.mk' P) = ⊤ := frattini_nongenerating h2
  have h4 : QuotientGroup.mk' P ⟨l, hl⟩ ∈ (K.subgroupOf L).map (QuotientGroup.mk' P) := by
    rw [h3]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.1 h4
  have h5 : k⁻¹ * ⟨l, hl⟩ ∈ P := QuotientGroup.eq.1 hkl
  refine ⟨k, Subgroup.mem_subgroupOf.1 hk, ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G),
    Subgroup.mem_map.2 ⟨k⁻¹ * ⟨l, hl⟩, h5, rfl⟩, ?_⟩
  simp

end B2F

end CFSG.Quasithin
