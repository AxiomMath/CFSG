module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups Pointwise

section CartanRel

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem rankOne_cartan_spec
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) {t : G}
    (ht : t * t = 1) (htS : t ∉ normalizer (S : Set G)) :
    cartan (S : Subgroup G) t ≤ normalizer (S : Set G) ∧
      (S : Subgroup G) ⊓ cartan (S : Subgroup G) t = ⊥ ∧
      (S : Subgroup G) ⊔ cartan (S : Subgroup G) t = normalizer (S : Set G) ∧
      IsCyclic (cartan (S : Subgroup G) t) ∧ Nat.card (cartan (S : Subgroup G) t) = 2 ^ n - 1 ∧
      (∀ x ∈ cartan (S : Subgroup G) t, t * x * t = x⁻¹) ∧
      ∀ x ∈ cartan (S : Subgroup G) t, x ≠ 1 → ∀ s ∈ (S : Subgroup G), s * x = x * s → s = 1 := by
  obtain ⟨i, hc⟩ := rankOne_benderCore_of_involution hG S ht htS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cartan_le_borel (S : Subgroup G) t
  · exact hc.inf_eq
  · exact hc.sup_eq
  · exact hc.isCyclic
  · simpa using hc.card_cartan
  · intro x hx
    have hx' : x ∈ ⁅cartan (S : Subgroup G) t, Subgroup.zpowers t⁆ := by
      rw [← hc.cartan_eq_commutator rfl]
      exact hx
    exact (hc.mem_commutator_cartan_iff.mp hx').2
  · intro x hxT hx1 s hsS hsx
    by_contra hs1
    have hspos : orderOf s ≠ 0 := (orderOf_pos s).ne'
    obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_orderOf (p := 2) (G := ↥(S : Subgroup G))).mp S.isPGroup' ⟨s, hsS⟩
    have hk' : orderOf s = 2 ^ k := by simpa using hk
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hs1
      have h1 : orderOf s = 1 := by rw [hk', hk0]; norm_num
      exact orderOf_eq_one_iff.mp h1
    have h2dvd : 2 ∣ orderOf s := by
      rw [hk']
      exact dvd_pow_self 2 hk0
    have hzord : orderOf (s ^ (orderOf s / 2)) = 2 :=
      orderOf_pow_orderOf_div hspos h2dvd
    have hz2 : s ^ (orderOf s / 2) * s ^ (orderOf s / 2) = 1 := by
      have h : (s ^ (orderOf s / 2)) ^ orderOf (s ^ (orderOf s / 2)) = 1 :=
        pow_orderOf_eq_one _
      rw [hzord] at h
      simpa [pow_two] using h
    have hz1 : s ^ (orderOf s / 2) ≠ 1 := by
      intro h
      rw [h] at hzord
      simp only [orderOf_one] at hzord
      omega
    have hzS : s ^ (orderOf s / 2) ∈ (S : Subgroup G) := Subgroup.pow_mem _ hsS _
    have hzR : s ^ (orderOf s / 2) ∈ rootCenter (S : Subgroup G) :=
      hc.mem_rootCenter_of_mul_self hzS hz2
    have hCz : centralizer ({s ^ (orderOf s / 2)} : Set G) = (S : Subgroup G) :=
      hc.centralizer_eq_of_e_one hzR hz1
    have hcomm : Commute s x := hsx
    have hzx : s ^ (orderOf s / 2) * x = x * s ^ (orderOf s / 2) :=
      hcomm.pow_left (orderOf s / 2)
    have hxCz : x ∈ centralizer ({s ^ (orderOf s / 2)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hzx
    have hxS : x ∈ (S : Subgroup G) := hCz ▸ hxCz
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hc.inf_eq]
      exact ⟨hxS, hxT⟩
    exact hx1 (Subgroup.mem_bot.mp hxbot)

theorem le_cartan_of_inverted {P : Subgroup G} {t : G} {T₀ : Subgroup G}
    (hB : T₀ ≤ borel P) (hinv : ∀ x ∈ T₀, t * x * t⁻¹ ∈ borel P) : T₀ ≤ cartan P t := by
  intro x hx
  show x ∈ borel P ⊓ conjugate (borel P) t
  exact ⟨hB hx, mem_conjugate_iff_mul_inv.mpr (hinv x hx)⟩

theorem rankOne_borel_eq_mul
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) (S : Sylow 2 G) {t : G}
    (ht : t * t = 1) (htS : t ∉ normalizer (S : Set G)) {b : G} (hb : b ∈ normalizer (S : Set G)) :
    ∃ s ∈ (S : Subgroup G), ∃ x ∈ cartan (S : Subgroup G) t, b = s * x := by
  have hspec := rankOne_cartan_spec hG S ht htS
  have hTle : cartan (S : Subgroup G) t ≤ normalizer (S : Set G) := hspec.1
  have hsup : (S : Subgroup G) ⊔ cartan (S : Subgroup G) t = normalizer (S : Set G) :=
    hspec.2.2.1
  have hcoe : (↑((S : Subgroup G) ⊔ cartan (S : Subgroup G) t) : Set G) =
      ((S : Subgroup G) : Set G) * ((cartan (S : Subgroup G) t) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (S : Subgroup G)
      (cartan (S : Subgroup G) t) hTle
  have hb' : b ∈ (S : Subgroup G) ⊔ cartan (S : Subgroup G) t := by
    rw [hsup]
    exact hb
  have hb'' : b ∈ ((S : Subgroup G) : Set G) * ((cartan (S : Subgroup G) t) : Set G) := by
    rw [← hcoe]
    exact hb'
  obtain ⟨s, hs, x, hx, hbsx⟩ := Set.mem_mul.mp hb''
  exact ⟨s, hs, x, hx, hbsx.symm⟩

theorem rankOne_card_psl (hG : CFSG.Quasithin.IsPSL 2 2 n G) :
    Nat.card G = (2 ^ n + 1) * 2 ^ n * (2 ^ n - 1) := by
  obtain ⟨t, hc⟩ := (rankOne_benderType_psl hG).exists_benderCore (default : Sylow 2 G)
  simpa [pow_one, mul_one, mul_assoc] using hc.card_group

theorem rankOne_card_sz (hG : CFSG.Quasithin.IsSz n G) :
    Nat.card G = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨t, hc⟩ := (rankOne_benderType_sz hG).exists_benderCore (default : Sylow 2 G)
  simpa [mul_one, mul_assoc] using hc.card_group

theorem rankOne_psl_sylow_elemAbelian
    (hG : CFSG.Quasithin.IsPSL 2 2 n G) (S : Sylow 2 G) :
    IsElemAbelian 2 (S : Subgroup G) ∧ Nat.card (S : Subgroup G) = 2 ^ n := by
  obtain ⟨t, hc⟩ := (rankOne_benderType_psl hG).exists_benderCore S
  have hcardS : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [hc.card_eq, pow_one]
  have hcardR : Nat.card (rootCenter (S : Subgroup G)) = 2 ^ n := hc.card_center
  have hEq : rootCenter (S : Subgroup G) = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le (S : Subgroup G)) (by rw [hcardS, hcardR])
  refine ⟨⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩, hcardS⟩
  · have ha : a.1 ∈ rootCenter (S : Subgroup G) := by rw [hEq]; exact a.2
    exact ((mem_rootCenter_iff.mp ha).2 b.1 b.2).symm
  · have hx' : x ∈ rootCenter (S : Subgroup G) := by rw [hEq]; exact hx
    simpa [sq] using hc.center_sq x hx'

theorem rankOne_psl_cartan_regular
    (hG : CFSG.Quasithin.IsPSL 2 2 n G) (S : Sylow 2 G) {t : G} (ht : t * t = 1)
    (htS : t ∉ normalizer (S : Set G)) {s s' : G} (hs : s ∈ (S : Subgroup G))
    (hs' : s' ∈ (S : Subgroup G)) (hs1 : s ≠ 1) (hs'1 : s' ≠ 1) :
    ∃! x : ↥(cartan (S : Subgroup G) t), (x : G) * s * (x : G)⁻¹ = s' := by
  have hspec := rankOne_cartan_spec (Or.inl hG) S ht htS
  have hTle : cartan (S : Subgroup G) t ≤ normalizer (S : Set G) := hspec.1
  have hcardT : Nat.card (cartan (S : Subgroup G) t) = 2 ^ n - 1 := hspec.2.2.2.2.1
  have hfix := hspec.2.2.2.2.2.2
  have hcardS : Nat.card (S : Subgroup G) = 2 ^ n := (rankOne_psl_sylow_elemAbelian hG S).2
  have hcardSstar : Nat.card {y : ↥(S : Subgroup G) // y ≠ 1} = 2 ^ n - 1 := by
    classical
    haveI hF : Fintype ↥(S : Subgroup G) := Fintype.ofFinite _
    haveI hFs : Fintype {y : ↥(S : Subgroup G) // y ≠ 1} := Fintype.ofFinite _
    have hS : Fintype.card ↥(S : Subgroup G) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, hcardS]
    have hstar : Fintype.card {y : ↥(S : Subgroup G) // y ≠ 1} = 2 ^ n - 1 := by
      rw [Fintype.card_subtype_compl (p := fun y : ↥(S : Subgroup G) => y = 1),
        Fintype.card_subtype_eq (1 : ↥(S : Subgroup G)), hS]
    rwa [Nat.card_eq_fintype_card]
  let f : ↥(cartan (S : Subgroup G) t) → {y : ↥(S : Subgroup G) // y ≠ 1} :=
    fun x => ⟨⟨x.1 * s * x.1⁻¹, (Subgroup.mem_normalizer_iff.mp (hTle x.2) s).mp hs⟩, by
      intro h
      apply hs1
      have h1 : x.1 * s * x.1⁻¹ = 1 := congrArg Subtype.val h
      calc s = x.1⁻¹ * (x.1 * s * x.1⁻¹) * x.1 := by group
        _ = x.1⁻¹ * 1 * x.1 := by rw [h1]
        _ = 1 := by group⟩
  have hf : ∀ x : ↥(cartan (S : Subgroup G) t), ((f x).1 : G) = x.1 * s * x.1⁻¹ :=
    fun x => rfl
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hconj : x.1 * s * x.1⁻¹ = y.1 * s * y.1⁻¹ := by
      have h := congrArg (fun w : {y : ↥(S : Subgroup G) // y ≠ 1} =>
          ((w.1 : ↥(S : Subgroup G)) : G)) hxy
      simpa [hf x, hf y] using h
    set z : G := y.1⁻¹ * x.1 with hzdef
    have hzT : z ∈ cartan (S : Subgroup G) t := by
      rw [hzdef]
      exact (cartan (S : Subgroup G) t).mul_mem
        ((cartan (S : Subgroup G) t).inv_mem y.2) x.2
    have hzconj : z * s * z⁻¹ = s := by
      rw [hzdef]
      have h := congrArg (fun w => y.1⁻¹ * w * y.1) hconj
      calc (y.1⁻¹ * x.1) * s * (y.1⁻¹ * x.1)⁻¹
          = y.1⁻¹ * (x.1 * s * x.1⁻¹) * y.1 := by group
        _ = y.1⁻¹ * (y.1 * s * y.1⁻¹) * y.1 := by rw [h]
        _ = s := by group
    have hzs : z * s = s * z := by
      calc z * s = (z * s * z⁻¹) * z := by group
        _ = s * z := by rw [hzconj]
    by_cases hz1 : z = 1
    · apply Subtype.ext
      rw [hzdef] at hz1
      exact (inv_mul_eq_one.mp hz1).symm
    · exfalso
      exact hs1 (hfix z hzT hz1 s hs hzs.symm)
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [hcardSstar, hcardT])
  have hs'ne : (⟨s', hs'⟩ : ↥(S : Subgroup G)) ≠ 1 := fun h => hs'1 (congrArg Subtype.val h)
  obtain ⟨x, hx⟩ := hfbij.2 ⟨⟨s', hs'⟩, hs'ne⟩
  refine ⟨x, ?_, ?_⟩
  · have h := congrArg (fun w : {y : ↥(S : Subgroup G) // y ≠ 1} =>
        ((w.1 : ↥(S : Subgroup G)) : G)) hx
    simpa [hf x] using h
  · intro y hy
    have hyf : f y = ⟨⟨s', hs'⟩, hs'ne⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [hf y] using hy
    exact hfinj (hyf.trans hx.symm)

end CartanRel

end CFSG.LocalAnalysis.WeakClosure81
