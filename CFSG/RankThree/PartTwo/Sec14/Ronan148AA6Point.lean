module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Defs
import CFSG.RankThree.PartTwo.Sec14.Ronan148AA6Four
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec18.Item186Three
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148

theorem exists_four_group_of_tripleCover {X : Type} [Group X] {K : Subgroup X}
    (hK6 : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6))) {k : X} (hkK : k ∈ K)
    (hk3 : k ^ 3 = 1) (hkC : k ∉ Subgroup.centralizer (K : Set X)) :
    ∃ v ∈ K, ∃ w ∈ K, v ^ 2 = 1 ∧ w ^ 2 = 1 ∧ v * w = w * v ∧ k * v * k⁻¹ = w ∧
      k * w * k⁻¹ = v * w ∧ v * w ∉ Subgroup.centralizer (K : Set X) := by
  obtain ⟨hZ3, ⟨e⟩⟩ := hK6
  set Z := Subgroup.center ↥K with hZ
  have : Finite ↥Z := Nat.finite_of_card_ne_zero (by omega)
  set π : ↥K →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' Z) with hπdef
  have hπ : ∀ x : ↥K, π x = 1 ↔ x ∈ Z := by
    intro x
    rw [hπdef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hZpow : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hcen : ∀ {x : ↥K}, π x = 1 → ∀ y : ↥K, y * x = x * y := fun hx =>
    Subgroup.mem_center_iff.mp ((hπ _).mp hx)
  set kK : ↥K := ⟨k, hkK⟩ with hkKdef
  have hg1 : π kK ≠ 1 := fun h => hkC (Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (hcen h ⟨y, hy⟩))
  have hg3 : π kK ^ 3 = 1 := by
    rw [← map_pow, show kK ^ 3 = 1 from Subtype.ext (by simpa using hk3), map_one]
  obtain ⟨v, hv2, hwv, hvw, hgw⟩ := a6_exists_four_group (π kK) hg3 hg1
  obtain ⟨v₀, hv₀⟩ := hπs v
  set v₂ : ↥K := v₀ ^ 3 with hv₂
  have hv3 : v ^ 3 = v := by rw [pow_succ, hv2, one_mul]
  have hπv : π v₂ = v := by rw [hv₂, map_pow, hv₀, hv3]
  have hv₂2 : v₂ ^ 2 = 1 := by
    have hc : v₀ ^ 2 ∈ Z := (hπ _).mp (by rw [map_pow, hv₀, hv2])
    rw [hv₂, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul]
    exact Subtype.ext (by simpa using congrArg Subtype.val (hZpow _ hc))
  set w₂ : ↥K := kK * v₂ * kK⁻¹ with hw₂
  have hπw : π w₂ = π kK * v * (π kK)⁻¹ := by rw [hw₂, map_mul, map_mul, map_inv, hπv]
  have hw₂2 : w₂ ^ 2 = 1 := by rw [hw₂, conj_pow, hv₂2, mul_one, mul_inv_cancel]
  have hvinv : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hv₂2])
  have hwinv : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hw₂2])
  set u : ↥K := v₂ * w₂ with hu
  have hπu : π u = v * (π kK * v * (π kK)⁻¹) := by rw [hu, map_mul, hπv, hπw]
  have hu2Z : π (u ^ 2) = 1 := by
    rw [map_pow, hπu, pow_two]
    calc v * (π kK * v * (π kK)⁻¹) * (v * (π kK * v * (π kK)⁻¹))
        = v * ((π kK * v * (π kK)⁻¹) * v) * (π kK * v * (π kK)⁻¹) := by group
      _ = v * (v * (π kK * v * (π kK)⁻¹)) * (π kK * v * (π kK)⁻¹) := by rw [hvw]
      _ = (v * v) * ((π kK * v * (π kK)⁻¹) * (π kK * v * (π kK)⁻¹)) := by group
      _ = 1 := by
        rw [← pow_two, hv2, one_mul, ← pow_two, conj_pow, hv2, mul_one, mul_inv_cancel]
  have hvu : v₂ * u * v₂⁻¹ = u⁻¹ := by
    rw [hu, mul_inv_rev, hvinv, hwinv, ← mul_assoc, ← pow_two, hv₂2, one_mul]
  have hu4 : u ^ 4 = 1 := by
    have h1 : v₂ * u ^ 2 * v₂⁻¹ = u ^ 2 := by rw [hcen hu2Z v₂, mul_inv_cancel_right]
    have h2 : v₂ * u ^ 2 * v₂⁻¹ = (u ^ 2)⁻¹ := by rw [← conj_pow, hvu, inv_pow]
    have h3 : u ^ 2 * u ^ 2 = 1 := by
      calc u ^ 2 * u ^ 2 = (u ^ 2)⁻¹⁻¹ * u ^ 2 := by rw [inv_inv]
        _ = (v₂ * u ^ 2 * v₂⁻¹)⁻¹ * u ^ 2 := by rw [h2]
        _ = 1 := by rw [h1, inv_mul_cancel]
    rw [show 4 = 2 + 2 by norm_num, pow_add, h3]
  have hu6 : u ^ 6 = 1 := by
    rw [show 6 = 2 * 3 by norm_num, pow_mul]
    exact Subtype.ext (by simpa using congrArg Subtype.val (hZpow _ ((hπ _).mp hu2Z)))
  have hu2 : u ^ 2 = 1 := by
    have h : u ^ Nat.gcd 4 6 = 1 := pow_gcd_eq_one.mpr ⟨hu4, hu6⟩
    rwa [show Nat.gcd 4 6 = 2 by norm_num] at h
  have hcomm : v₂ * w₂ = w₂ * v₂ := by
    have h : u = u⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_two, hu2])).symm
    rw [hu, mul_inv_rev, hvinv, hwinv] at h
    exact h
  have ht : kK * w₂ * kK⁻¹ = u := by
    set t := kK * w₂ * kK⁻¹ with htdef
    set z := t * u⁻¹ with hz
    have hπz : π z = 1 := by
      rw [hz, map_mul, map_inv, htdef, map_mul, map_mul, map_inv, hπw, hπu, hgw]
      group
    have hzc := hcen hπz
    have ht2 : t ^ 2 = 1 := by rw [htdef, conj_pow, hw₂2, mul_one, mul_inv_cancel]
    have htu : t = z * u := by rw [hz, inv_mul_cancel_right]
    have hz2 : z ^ 2 = 1 := by
      have h : (z * u) ^ 2 = z ^ 2 * u ^ 2 := (Commute.mul_pow (hzc u).symm 2)
      rw [← htu, ht2, hu2, mul_one] at h
      exact h.symm
    have hz3 : z ^ 3 = 1 := hZpow _ ((hπ _).mp hπz)
    have hz1 : z = 1 := by
      have h : z ^ Nat.gcd 2 3 = 1 := pow_gcd_eq_one.mpr ⟨hz2, hz3⟩
      rwa [show Nat.gcd 2 3 = 1 by norm_num, pow_one] at h
    rw [htu, hz1, one_mul]
  refine ⟨v₂, v₂.2, w₂, w₂.2, by simpa using congrArg Subtype.val hv₂2,
    by simpa using congrArg Subtype.val hw₂2, congrArg Subtype.val hcomm,
    by simp [hw₂, kK], ?_, ?_⟩
  · have h := congrArg Subtype.val ht
    simpa [hu, kK] using h
  · intro hC
    have h1 : π u = 1 := (hπ u).mpr (Subgroup.mem_center_iff.mpr fun y => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp hC y y.2))
    rw [hπu] at h1
    apply hwv
    calc π kK * v * (π kK)⁻¹ = v⁻¹ * (v * (π kK * v * (π kK)⁻¹)) := by group
      _ = v := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right (by rw [← pow_two, hv2])]

variable {G : Type} [Group G] [Finite G]

theorem step148A6PointQ_holds (h142 : Concl142S14) : Ronan148B.Step148A6PointQ := by
  intro G _ _ A c L hS Y hY J hJ _ hJ6 hX K hKc hKJ hK6 hKY k hkA hkK hkC hAeq a ha haΩ haK
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  have hAE := img148_isE27 (Y := Y) hA
  have hk3 : k ^ 3 = 1 := hAE.1.2 k hkA
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have h3J : 3 ∣ Nat.card J := by
    have h := card_img148_dvd (A := A) (Y := Y) hJM
    rw [Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hJ6] at h
    exact (by norm_num : 3 ∣ 1080).trans h
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  obtain ⟨v, hvK, w, hwK, hv2, hw2, hvw, hkv, hkw, hvwC⟩ :=
    exists_four_group_of_tripleCover hK6 hkK hk3 hkC
  set V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) := Subgroup.zpowers v ⊔ Subgroup.zpowers w with hV
  have hVK : V ≤ K := sup_le (Subgroup.zpowers_le.mpr hvK) (Subgroup.zpowers_le.mpr hwK)
  have hV3 : ¬ 3 ∣ Nat.card V := by
    have hvn : Subgroup.zpowers v ≤
        Subgroup.normalizer (Subgroup.zpowers w : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute w v from hvw.symm) n).eq
    have h := Sec6.card_sup_mul_card_inf hvn
    have hv : Nat.card (Subgroup.zpowers v) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hv2
    have hw : Nat.card (Subgroup.zpowers w) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hw2
    intro h3
    have h1 : Nat.card V ∣ Nat.card (Subgroup.zpowers v) * Nat.card (Subgroup.zpowers w) :=
      ⟨_, h.symm⟩
    have h4 : 3 ∣ 2 * 2 := (h3.trans h1).trans (Nat.mul_dvd_mul hv hw)
    omega
  have hkV : k ∈ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    apply Sec18.Item186Proof.mem_normalizer_of_map_conj_le
    rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hkv]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hkw]
      exact V.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have hAV : img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [← hAeq]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hkV)
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hx.2 y (hVK hy)
  have hVa : V ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({a} : Set G)) := fun x hx =>
    Item148Rank.mem_img148_centralizer_of_commute148 hY.2 ha (hA.1.2 a ha) le_rfl
      (hKY (hVK hx)) (Subgroup.mem_centralizer_iff.mp haK x (hVK hx)).symm
  have hc := Ronan148J.commutator_le_img148_deltaZero_of_point h142 hS hY haΩ V hVa hV3 hAV
  rw [hX] at hc
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hw2])
  have hvwJ : v * w ∈ img148 A Y J := by
    have hmem := Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers v) : v ∈ V) hkA
    rw [commutatorElement_def] at hmem
    have heq : v * k * v⁻¹ * k⁻¹ = v * w := by
      calc v * k * v⁻¹ * k⁻¹ = v * (k * v * k⁻¹)⁻¹ := by group
        _ = v * w := by rw [hkv, hwinv]
    rw [heq] at hmem
    exact hc hmem
  exact hvwC (Res2LBal.mem_centralizer_of_mem_of_ne hKc hJc hKJ hvwJ)

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
