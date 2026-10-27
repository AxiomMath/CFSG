module

public import CFSG.Quasithin.Vol2.Ch11SecO8E
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Quasithin CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

namespace O8S

variable {W : Type} [CommGroup W] [Finite W] {Hs Ks : Subgroup (MulAut W)} {F : Type} [Field F]
  [Finite F] {n : ℕ} (hW : ∀ w : W, w ^ 2 = 1) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
  (hHN : Hs ≤ Subgroup.normalizer (Ks : Set (MulAut W))) (e : ↥Ks ≃* SL(2, F))
  (hKH : Ks ≤ Hs) (h2 : ∀ h ∈ Hs, ∃ k : ℕ, h ^ 2 ^ k ∈ Ks) (hO : CFSG.pCore 2 ↥Hs = ⊥)

omit [Finite W] in
include hF e in
theorem sq_eq_one_of_commute {u k : MulAut W} (huK : u ∈ Ks) (hkK : k ∈ Ks) (hu1 : u ≠ 1)
    (hu2 : u * u = 1) (hku : k * u = u * k) : k * k = 1 := by
  have : CharP F 2 := char_two_of_card hF
  have h1 : e ⟨u, huK⟩ * e ⟨k, hkK⟩ = e ⟨k, hkK⟩ * e ⟨u, huK⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hku.symm)
  have hu1' : e ⟨u, huK⟩ ≠ 1 := fun h =>
    hu1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
  have hu2' : e ⟨u, huK⟩ * e ⟨u, huK⟩ = 1 := by
    rw [← map_mul]
    exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hu2)
  have h3 := CFSG.Walter.sl2_mul_self_eq_one_of_commute hu1' hu2' h1
  rw [← map_mul, map_eq_one_iff e e.injective] at h3
  exact congrArg Subtype.val h3

include hW hKH h2 hO in
theorem not_outer_two {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 Hs) (hn2 : n = 2)
    (h4 : Nat.card ↥A = 4) {t u : MulAut W} (htA : t ∈ A) (htK : t ∉ Ks) (huA : u ∈ A)
    (huK : u ∈ Ks) (hu1 : u ≠ 1) {x : SL(2, F)}
    (hx : centralizerS (phi hn hF hHN e ⟨t, hA.1 htA⟩) =
      (fixedSL2 (phi hn hF hHN e ⟨t, hA.1 htA⟩).right).map (MulAut.conj x).toMonoidHom) :
    False := by
  have : CharP F 2 := char_two_of_card hF
  have hA2 : IsElemAbelian2 A := hA.2.2.1
  have hyC : MulAut.conj x ord3 ∈ centralizerS (phi hn hF hHN e ⟨t, hA.1 htA⟩) := by
    rw [hx]
    exact ⟨ord3, ord3_mem_fixedSL2 _, rfl⟩
  set k : ↥Ks := e.symm (MulAut.conj x ord3) with hkdef
  have hk' : phi hn hF hHN e ⟨k, hKH k.2⟩ = SemidirectProduct.inl (MulAut.conj x ord3) := by
    rw [phi_of_mem hn hF hHN e hKH, hkdef, MulEquiv.apply_symm_apply]
  have hkt : (k : MulAut W) * t = t * k := by
    rw [mem_centralizerS_iff, ← hk', ← map_mul, ← map_mul] at hyC
    exact congrArg Subtype.val (phi_injective hn hF hHN e h2 hO hyC)
  have hk3 : (k : MulAut W) ^ 3 = 1 := by
    have : k ^ 3 = 1 := by rw [hkdef, ← map_pow, ← map_pow, ord3_pow_three, map_one, map_one]
    simpa using congrArg Subtype.val this
  have hk1 : (k : MulAut W) ≠ 1 := by
    intro h
    have h' : k = 1 := Subtype.ext h
    rw [hkdef, map_eq_one_iff _ e.symm.injective,
      map_eq_one_iff _ (MulAut.conj x).injective] at h'
    exact ord3_ne_one h'
  have ht1 : t ≠ 1 := fun h => htK (h ▸ Ks.one_mem)
  have hut : ∀ w, u w = w ↔ t w = w := fun w => by
    rw [← mem_fixV_zpowers, ← mem_fixV_zpowers, fixV_zpowers_eq hA h4 huA hu1,
      fixV_zpowers_eq hA h4 htA ht1]
  set v := (k : MulAut W) * u * (k : MulAut W)⁻¹ with hv
  have hvt : ∀ w, v w = w ↔ t w = w := fix_conj_iff hkt hut
  have hu2 : u * u = 1 := by rw [← sq]; exact hA2.2 u huA
  have hv2 : v * v = 1 := by
    rw [hv, show (k : MulAut W) * u * (k : MulAut W)⁻¹ * ((k : MulAut W) * u * (k : MulAut W)⁻¹)
      = (k : MulAut W) * (u * u) * (k : MulAut W)⁻¹ by group, hu2, mul_one, mul_inv_cancel]
  have huv : u * v = v * u :=
    commute_of_fix_iff hW hu2 hv2 fun w => (hut w).trans (hvt w).symm
  have hvK : v ∈ Ks := Ks.mul_mem (Ks.mul_mem k.2 huK) (Ks.inv_mem k.2)
  have hvu : v ≠ u := by
    intro h
    have hku : (k : MulAut W) * u = u * k := by
      calc (k : MulAut W) * u = v * k := by rw [hv]; group
        _ = u * k := by rw [h]
    have hk2 := sq_eq_one_of_commute hF e huK k.2 hu1 hu2 hku
    apply hk1
    calc (k : MulAut W) = (k : MulAut W) ^ 3 * ((k : MulAut W) * k)⁻¹ := by group
      _ = 1 := by rw [hk3, hk2, inv_one, one_mul]
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    have : u = (k : MulAut W)⁻¹ * v * k := by rw [hv]; group
    rw [this, h, mul_one, inv_mul_cancel]
  have htu : t * u = u * t := hA2.1 t htA u huA
  have htv : t * v = v * t := by
    rw [hv]
    have hkt' : (k : MulAut W) * t * (k : MulAut W)⁻¹ = t := by rw [hkt]; group
    calc t * ((k : MulAut W) * u * (k : MulAut W)⁻¹)
        = (t * k) * u * (k : MulAut W)⁻¹ := by group
      _ = (k * t) * u * (k : MulAut W)⁻¹ := by rw [← hkt]
      _ = k * (t * u) * (k : MulAut W)⁻¹ := by group
      _ = k * (u * t) * (k : MulAut W)⁻¹ := by rw [htu]
      _ = (k : MulAut W) * u * (k : MulAut W)⁻¹ * ((k : MulAut W) * t * (k : MulAut W)⁻¹) := by
          group
      _ = (k : MulAut W) * u * (k : MulAut W)⁻¹ * t := by rw [hkt']
  have hsq : ∀ a ∈ ({t, u, v} : Set (MulAut W)), a ^ 2 = 1 := by
    rintro a (rfl | rfl | rfl)
    · exact hA2.2 _ htA
    · exact hA2.2 _ huA
    · rw [sq]; exact hv2
  have hcomm : ∀ a ∈ ({t, u, v} : Set (MulAut W)), ∀ b ∈ ({t, u, v} : Set (MulAut W)),
      a * b = b * a := by
    rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) <;> first | rfl | assumption | exact Eq.symm ‹_›
  have hBH : Subgroup.closure ({t, u, v} : Set (MulAut W)) ≤ Hs := by
    rw [Subgroup.closure_le]
    rintro a (rfl | rfl | rfl)
    · exact hA.1 htA
    · exact hKH huK
    · exact hKH hvK
  obtain ⟨s, -, hns, -, -, hI, -⟩ := rank_data hn hF hHN e hKH h2 hO hBH
    (isElemAbelian2_closure hcomm hsq) (Subgroup.subset_closure (by simp)) htK
  have hmem : ∀ z (hz : z ∈ Ks), z ∈ ({t, u, v} : Set (MulAut W)) →
      e ⟨z, hz⟩ ∈ intersectionS (img hn hF hHN e (Subgroup.closure {t, u, v})) := by
    intro z hz hzS
    change SemidirectProduct.inl (e ⟨z, hz⟩) ∈ img hn hF hHN e (Subgroup.closure {t, u, v})
    rw [← phi_of_mem hn hF hHN e hKH ⟨z, hz⟩]
    exact phi_mem_img hn hF hHN e (Subgroup.subset_closure hzS)
  have hne : ∀ (z : MulAut W) (hz : z ∈ Ks), z ≠ 1 → e ⟨z, hz⟩ ≠ 1 := fun z hz hz1 h =>
    hz1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
  have h3 := three_le_card (hmem u huK (by simp)) (hmem v hvK (by simp)) (hne u huK hu1)
    (hne v hvK hv1) (fun h => hvu (congrArg Subtype.val (e.injective h)).symm)
  have : 2 ^ s = 2 := by
    rw [show s = 1 by omega, pow_one]
  omega

include hW hn hF hHN e hKH h2 hO in
theorem le_of_mem_aSet {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet n Hs) : A ≤ Ks := by
  have hA2 : IsElemAbelian2 A := hA.2.2.1
  by_contra hAK
  obtain ⟨t, htA, htK⟩ := Set.not_subset.mp hAK
  have hcard := two_pow_le_card hA
  obtain ⟨s, hs1, hns, hAs, hfac, -, -, x, hx⟩ :=
    rank_data hn hF hHN e hKH h2 hO hA.1 hA2 htA htK
  have hs : s = 1 := by
    have h1 := hcard.trans hAs
    rw [hns] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  subst hs
  have hn2 : n = 2 := by omega
  have h4 : Nat.card ↥A = 4 := by
    rw [hn2] at hcard
    norm_num at hAs hcard
    omega
  have hI2 : Nat.card ↥(intersectionS (img hn hF hHN e A)) = 2 := by omega
  have hIne : intersectionS (img hn hF hHN e A) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hI2
    omega
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIne
  obtain ⟨b, hbA, hb⟩ := Subgroup.mem_map.mp
    (show SemidirectProduct.inl g ∈ img hn hF hHN e A from hg)
  have hbK : (b : MulAut W) ∈ Ks := mem_of_phi_mem hn hF hHN e hKH h2 hO b (by
    rw [hb, mem_linearKernel_iff]
    rfl)
  have hb1 : (b : MulAut W) ≠ 1 := by
    intro h
    have hb' : b = 1 := Subtype.ext h
    rw [hb', map_one] at hb
    exact hg1 (Subtype.ext (SemidirectProduct.inl_injective (hb.symm.trans
      (map_one SemidirectProduct.inl).symm)))
  rw [hn2] at hA
  exact not_outer_two hW hn hF hHN e hKH h2 hO hA hn2 h4 htA htK
    (Subgroup.mem_subgroupOf.mp hbA) hbK hb1 hx

end O8S

end CFSG.Quasithin.Vol2.Ch11.SecC
