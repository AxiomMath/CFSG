module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofCent
public import CFSG.RankThree.PartOne.S11d.Common
public import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem false_of_lZeroUnion_of_triv {A X : Subgroup G} (hX : X ∈ lZeroUnion A)
    (htriv : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X) :
    False := by
  obtain ⟨E, -, hEA, -, S, hS, hSE⟩ := mem_lZeroUnion_iff.mp hX
  apply hSE
  rw [commutator_le]
  intro s hs e he
  have h := htriv e (hEA he) s (hS.1 hs)
  have : ⁅s, e⁆ = (e * s * e⁻¹ * s⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [this]
  exact inv_mem h

theorem triv_of_ne {b : G} {X K : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b)
    (hK : K ∈ thetaComponentsAt 3 b) (hne : X ≠ K) {a z k : G}
    (haN : a ∈ normalizer (X : Set G)) (hz : z ∈ centralizer (X : Set G)) (hk : k ∈ K)
    (hazk : a = z * k) :
    ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
  intro x hx
  have hzN : z ∈ normalizer (X : Set G) := centralizer_le_normalizer _ hz
  have hkN : k ∈ normalizer (X : Set G) := by
    have : k = z⁻¹ * a := by rw [hazk]; group
    rw [this]
    exact mul_mem (inv_mem hzN) haN
  have hkx : k * x * k⁻¹ ∈ X := (mem_normalizer_iff.mp hkN x).mp hx
  have hzc : ∀ y ∈ X, z * y = y * z := fun y hy => ((mem_centralizer_iff.mp hz) y hy).symm
  have heq : a * x * a⁻¹ * x⁻¹ = k * x * k⁻¹ * x⁻¹ := by
    rw [hazk]
    calc z * k * x * (z * k)⁻¹ * x⁻¹ = z * (k * x * k⁻¹) * z⁻¹ * x⁻¹ := by group
      _ = (k * x * k⁻¹) * z * z⁻¹ * x⁻¹ := by rw [hzc _ hkx]
      _ = k * x * k⁻¹ * x⁻¹ := by group
  rw [heq]
  have h1 := PartOne.S11d.commutator_mem_theta_of_ne Nat.prime_three hK hX hne.symm k hk x hx
  have h2 : k * x * k⁻¹ * x⁻¹ ∈ X := mul_mem hkx (inv_mem hx)
  exact Item2110Res3Proof.inSubgroup_theta_inf_le
    (Sec6.le_centralizer_of_mem_thetaComponentsAt hX) ⟨h1, h2⟩

omit [Finite G] in
theorem false_of_normalizes_of_mem {J Y : Subgroup G} {d : G} (hdJ : d ∈ J)
    (hJd : J ≤ centralizer ({d} : Set G)) (hYJ : Y ≤ normalizer (J : Set G))
    (hdY : d ∈ normalizer (Y : Set G)) (hfpf : ∀ y ∈ Y, d * y * d⁻¹ = y → y = 1) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) : False := by
  have ht : y * d * y⁻¹ ∈ J := (mem_normalizer_iff.mp (hYJ hy) d).mp hdJ
  have htd : y * d * y⁻¹ * d = d * (y * d * y⁻¹) := mem_centralizer_singleton_iff.mp (hJd ht)
  set u := y * d * y⁻¹ * d⁻¹ with hu
  have huY : u ∈ Y := by
    have h1 : d * y⁻¹ * d⁻¹ ∈ Y := (mem_normalizer_iff.mp hdY y⁻¹).mp (inv_mem hy)
    have h2 := mul_mem hy h1
    simpa [hu, mul_assoc] using h2
  have hdu : d * u * d⁻¹ = u := by
    calc d * u * d⁻¹ = d * (y * d * y⁻¹) * d⁻¹ * d⁻¹ := by rw [hu]; group
      _ = y * d * y⁻¹ * d * d⁻¹ * d⁻¹ := by rw [← htd]
      _ = u := by rw [hu]; group
  have hu1 := hfpf u huY hdu
  have hyd : d * y * d⁻¹ = y := by
    have h1 : y * d * y⁻¹ = d := by
      calc y * d * y⁻¹ = u * d := by rw [hu]; group
        _ = d := by rw [hu1, one_mul]
    calc d * y * d⁻¹ = (y * d * y⁻¹) * y * d⁻¹ := by rw [h1]
      _ = y := by group
  exact hy1 (hfpf y hy hyd)

omit [Finite G] in
theorem le_of_normalizes {Y K : Subgroup G} {d : G} (hYab : CFSG.Assembly.IsElemAbelian 2 Y)
    (hY4 : Nat.card Y = 4) (hYK : Y ≤ normalizer (K : Set G)) (hdK : d ∈ K)
    (hdY : d ∈ normalizer (Y : Set G)) (hfpf : ∀ y ∈ Y, d * y * d⁻¹ = y → y = 1) : Y ≤ K := by
  have hKl := isKleinFour_of hYab hY4
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  set u := y * d * y⁻¹ * d⁻¹ with hu
  have huY : u ∈ Y := by
    have h1 : d * y⁻¹ * d⁻¹ ∈ Y := (mem_normalizer_iff.mp hdY y⁻¹).mp (inv_mem hy)
    have h2 := mul_mem hy h1
    simpa [hu, mul_assoc] using h2
  have huK : u ∈ K := by
    have h1 : y * d * y⁻¹ ∈ K := (mem_normalizer_iff.mp (hYK hy) d).mp hdK
    exact mul_mem h1 (inv_mem hdK)
  have hu1 : u ≠ 1 := by
    intro h
    apply hy1
    apply hfpf y hy
    have h1 : y * d * y⁻¹ = d := by
      calc y * d * y⁻¹ = u * d := by rw [hu]; group
        _ = d := by rw [h, one_mul]
    calc d * y * d⁻¹ = (y * d * y⁻¹) * y * d⁻¹ := by rw [h1]
      _ = y := by group
  set v := d * u * d⁻¹ with hv
  have hvY : v ∈ Y := (mem_normalizer_iff.mp hdY u).mp huY
  have hvK : v ∈ K := mul_mem (mul_mem hdK huK) (inv_mem hdK)
  have hvu : v ≠ u := fun h => hu1 (hfpf u huY h)
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    calc u = d⁻¹ * v * d := by rw [hv]; group
      _ = 1 := by rw [h]; group
  by_cases hyu : y = u
  · rw [hyu]
    exact huK
  by_cases hyv : y = v
  · rw [hyv]
    exact hvK
  have h := IsKleinFour.eq_mul_of_ne_all (G := Y) (x := ⟨u, huY⟩) (y := ⟨v, hvY⟩)
    (z := ⟨y, hy⟩) (fun h => hu1 (congrArg Subtype.val h))
    (fun h => hv1 (congrArg Subtype.val h)) (fun h => hvu (congrArg Subtype.val h).symm)
    (fun h => hy1 (congrArg Subtype.val h)) (fun h => hyu (congrArg Subtype.val h))
    (fun h => hyv (congrArg Subtype.val h))
  have h' : y = u * v := congrArg Subtype.val h
  rw [h']
  exact mul_mem huK hvK

theorem le_normalizer_of_pCore {A K Y : Subgroup G} {b d : G} (hS : A ∈ partTwoS G)
    (hbA : b ∈ A) (hb1 : b ≠ 1) (hK : K ∈ thetaComponentsAt 3 b)
    (hZ : ∀ g : G, center (lBar (K.map (MulAut.conj g).toMonoidHom)) = ⊥) (hYK : Y ≤ K)
    (hYab : CFSG.Assembly.IsElemAbelian 2 Y) (hdA : d ∈ A) (hdY : d ∈ normalizer (Y : Set G))
    (hfpf : ∀ y ∈ Y, d * y * d⁻¹ = y → y = 1) (hY1 : Y ≠ ⊥) :
    inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) ⊓ centralizer ({b} : Set G) ≤
      normalizer (K : Set G) := by
  intro v hv
  by_contra hvK
  set K' := K.map (MulAut.conj v).toMonoidHom with hK'
  have hK'b : K' ∈ thetaComponentsAt 3 b := Sec6.map_conj_mem_thetaComponentsAt hv.2 hK
  have hne : K ≠ K' := fun h => hvK (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hvY : v ∈ centralizer (Y : Set G) := map_subtype_le _ hv.1
  have hYK' : ∀ y ∈ Y, y ∈ K' := by
    intro y hy
    refine ⟨y, hYK hy, ?_⟩
    change v * y * v⁻¹ = y
    rw [← (mem_centralizer_iff.mp hvY) y hy, mul_inv_cancel_right]
  have hK'C : K' ≤ centralizer ({b} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hK'b
  have hYθ : ∀ y ∈ Y, y ∈ inSubgroup (aschbacherSolvableCore 3)
      (centralizer ({b} : Set G)) := by
    intro y hy
    set N := aschbacherSolvableCore 3 ↥K' with hN
    have hcen : (QuotientGroup.mk' N ⟨y, hYK' y hy⟩ : lBar K') ∈ center (lBar K') := by
      rw [mem_center_iff]
      intro q
      obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective N q
      have h1 := PartOne.S11d.commutator_mem_theta_of_ne Nat.prime_three hK hK'b hne y (hYK hy)
        k' k'.2
      have h2 : y * (k' : G) * y⁻¹ * (k' : G)⁻¹ ∈ K' :=
        mul_mem (mul_mem (mul_mem (hYK' y hy) k'.2) (inv_mem (hYK' y hy))) (inv_mem k'.2)
      obtain ⟨t, ht, hte⟩ := Item2110Res3Proof.inSubgroup_theta_inf_le hK'C ⟨h1, h2⟩
      have htt : t = ⟨y, hYK' y hy⟩ * k' * ⟨y, hYK' y hy⟩⁻¹ * k'⁻¹ := Subtype.ext hte
      have hc : QuotientGroup.mk' N (⟨y, hYK' y hy⟩ * k' * ⟨y, hYK' y hy⟩⁻¹ * k'⁻¹) = 1 := by
        rw [← htt, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact ht
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc
      calc QuotientGroup.mk' N k' * QuotientGroup.mk' N ⟨y, hYK' y hy⟩
          = (QuotientGroup.mk' N ⟨y, hYK' y hy⟩ * QuotientGroup.mk' N k' *
              (QuotientGroup.mk' N ⟨y, hYK' y hy⟩)⁻¹ * (QuotientGroup.mk' N k')⁻¹)⁻¹ *
            (QuotientGroup.mk' N ⟨y, hYK' y hy⟩ * QuotientGroup.mk' N k') := by group
        _ = QuotientGroup.mk' N ⟨y, hYK' y hy⟩ * QuotientGroup.mk' N k' := by
            rw [hc, inv_one, one_mul]
    rw [hZ v, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    exact theta_le_theta_centralizer hK'b ⟨_, hcen, rfl⟩
  obtain ⟨⟨y, hy⟩, hy1⟩ := (ne_bot_iff_exists_ne_one).mp hY1
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  set u := y * d * y⁻¹ * d⁻¹ with hu
  have huY : u ∈ Y := by
    have h1 : d * y⁻¹ * d⁻¹ ∈ Y := (mem_normalizer_iff.mp hdY y⁻¹).mp (inv_mem hy)
    have h2 := mul_mem hy h1
    simpa [hu, mul_assoc] using h2
  have hu1 : u ≠ 1 := by
    intro h
    apply hy1'
    apply hfpf y hy
    have h1 : y * d * y⁻¹ = d := by
      calc y * d * y⁻¹ = u * d := by rw [hu]; group
        _ = d := by rw [h, one_mul]
    calc d * y * d⁻¹ = (y * d * y⁻¹) * y * d⁻¹ := by rw [h1]
      _ = y := by group
  have huc : u ∈ ⁅inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set G)), A⁆ := by
    have := commutator_mem_commutator (hYθ y hy) hdA
    rwa [commutatorElement_def] at this
  have hodd := hS.2.1 b hbA hb1
  have hu2 : u ^ 2 = 1 := hYab.2 u huY
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hdvd := Subgroup.orderOf_dvd_natCard _ huc
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

omit [Finite G] in
theorem commutatorElement_pow_mul {v b l : G} (hvb : v * b = b * v)
    (hwb : v * l * v⁻¹ * l⁻¹ * b = b * (v * l * v⁻¹ * l⁻¹)) (i : ℕ) :
    ⁅v, b ^ i * l⁆ = v * l * v⁻¹ * l⁻¹ := by
  have hvb' : v * b ^ i = b ^ i * v := ((Commute.pow_right hvb i)).eq
  have hwb' : b ^ i * (v * l * v⁻¹ * l⁻¹) = (v * l * v⁻¹ * l⁻¹) * b ^ i :=
    ((Commute.pow_right hwb i)).eq.symm
  rw [commutatorElement_def]
  calc v * (b ^ i * l) * v⁻¹ * (b ^ i * l)⁻¹
      = (v * b ^ i) * l * v⁻¹ * l⁻¹ * (b ^ i)⁻¹ := by group
    _ = b ^ i * (v * l * v⁻¹ * l⁻¹) * (b ^ i)⁻¹ := by rw [hvb']; group
    _ = v * l * v⁻¹ * l⁻¹ := by rw [hwb']; group

omit [Finite G] in
theorem commutator_le_of_dec {V₀ C K : Subgroup G} {b : G}
    (hV₀N : V₀ ≤ normalizer (K : Set G)) (hV₀b : V₀ ≤ centralizer ({b} : Set G))
    (hKb : K ≤ centralizer ({b} : Set G))
    (hdec : ∀ x ∈ C, ∃ i : ℕ, ∃ l ∈ K, x = b ^ i * l) : ⁅V₀, C⁆ ≤ K := by
  rw [commutator_le]
  intro v hv x hx
  obtain ⟨i, l, hl, rfl⟩ := hdec x hx
  have hw : v * l * v⁻¹ * l⁻¹ ∈ K :=
    mul_mem ((mem_normalizer_iff.mp (hV₀N hv) l).mp hl) (inv_mem hl)
  rw [commutatorElement_pow_mul (mem_centralizer_singleton_iff.mp (hV₀b hv))
    (mem_centralizer_singleton_iff.mp (hKb hw)) i]
  exact hw

end CFSG.RankThree.PartTwo.Sec21.Item21Res10Proof
