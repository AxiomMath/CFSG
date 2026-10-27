module

import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec8.Hering611SImg

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_fuse {K D : Subgroup G} (hDK : D ≤ K) (hD3 : IsPGroup 3 D) {k a : G}
    (hkD : k ∈ D) (haD : a ∈ D) {m : ℕ}
    (hfuse : ∃ gb ∈ Subgroup.normalizer
        (imageSub K D : Set (K ⧸ aschbacherSolvableCore 3 K)),
      gb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hDK hkD⟩ * gb⁻¹ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hDK hkD⟩ *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, hDK haD⟩) ^ m) :
    ∃ g ∈ K, g ∈ Subgroup.normalizer (D : Set G) ∧ g * k * g⁻¹ = k * a ^ m := by
  obtain ⟨gb, hgb, hconj⟩ := hfuse
  obtain ⟨w, hwN, hwgb⟩ := exists_lift_normalizer hDK hD3 hgb
  have hkK : k ∈ K := hDK hkD
  have haK : a ∈ K := hDK haD
  have hgkK : (w : G) * k * (w : G)⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem w.2 hkK) (K.inv_mem w.2)
  have hkaK : k * a ^ m ∈ K := K.mul_mem hkK (K.pow_mem haK m)
  have hgkD : (w : G) * k * (w : G)⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp hwN k).mp hkD
  have hkaD : k * a ^ m ∈ D := D.mul_mem hkD (D.pow_mem haD m)
  have hsub : (⟨(w : G) * k * (w : G)⁻¹, hgkK⟩ : K) = w * ⟨k, hkK⟩ * w⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])
  have hpow : (⟨k * a ^ m, hkaK⟩ : K) = ⟨k, hkK⟩ * ⟨a, haK⟩ ^ m :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_pow])
  have hmk : QuotientGroup.mk' (aschbacherSolvableCore 3 K)
      (⟨(w : G) * k * (w : G)⁻¹, hgkK⟩ : K) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨k * a ^ m, hkaK⟩ : K) := by
    rw [hsub, hpow]
    simp only [map_mul, map_inv, map_pow]
    rw [hwgb]
    exact hconj
  have hxy : (⟨(w : G) * k * (w : G)⁻¹, hgkK⟩ : K) = ⟨k * a ^ m, hkaK⟩ :=
    eq_of_mk_eq_of_isPGroup hD3 hgkD hkaD hmk
  exact ⟨(w : G), w.2, hwN, congrArg Subtype.val hxy⟩

theorem thetaQuot_conj_equiv (L : Subgroup G) (g : G) :
    Nonempty ((L.map (MulAut.conj g).toMonoidHom) ⧸
      aschbacherSolvableCore 3 (L.map (MulAut.conj g).toMonoidHom) ≃*
        L ⧸ aschbacherSolvableCore 3 L) := by
  let e : L.map (MulAut.conj g).toMonoidHom ≃* L :=
    (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  exact ⟨QuotientGroup.congr _ _ e
    (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)⟩

theorem conj_config {A L : Subgroup G} {c : G} (hL : L ∈ thetaComponentsAt 3 c) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    L.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 (g * c * g⁻¹) ∧
      A ≤ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  refine ⟨CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt
    Nat.prime_three hL g, fun x hx => ?_⟩
  have hy : g⁻¹ * x * g ∈ A := by
    apply (Subgroup.mem_normalizer_iff.mp hgA (g⁻¹ * x * g)).mpr
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  have hyN : g⁻¹ * x * g ∈ Subgroup.normalizer (L : Set G) := hAL hy
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hn' : n ∈ L.map (MulAut.conj g).toMonoidHom := hn
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hn'
  have hlL : (g⁻¹ * x * g) * l * (g⁻¹ * x * g)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hyN l).mp hl
  refine Subgroup.mem_map.mpr ⟨(g⁻¹ * x * g) * l * (g⁻¹ * x * g)⁻¹, hlL, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conj_dec {A L : Subgroup G} {c d g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgd : g * d * g⁻¹ = d)
    (hdec : A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ (A ⊓ L)) :
    A ≤ Subgroup.zpowers (g * c * g⁻¹) ⊔ Subgroup.zpowers d ⊔
      (A ⊓ L.map (MulAut.conj g).toMonoidHom) := by
  intro x hx
  have hy : g⁻¹ * x * g ∈ A := by
    apply (Subgroup.mem_normalizer_iff.mp hgA (g⁻¹ * x * g)).mpr
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  have hxy : (MulAut.conj g).toMonoidHom (g⁻¹ * x * g) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hfd : (MulAut.conj g).toMonoidHom d = d := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hgd
  have hAL' : Subgroup.map (MulAut.conj g).toMonoidHom (A ⊓ L) ≤
      A ⊓ L.map (MulAut.conj g).toMonoidHom := by
    intro z hz
    obtain ⟨z₀, ⟨hz₀A, hz₀L⟩, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨(Subgroup.mem_normalizer_iff.mp hgA z₀).mp hz₀A,
      Subgroup.mem_map_of_mem _ hz₀L⟩
  have hle : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ (A ⊓ L)) ≤
      Subgroup.zpowers (g * c * g⁻¹) ⊔ Subgroup.zpowers d ⊔
        (A ⊓ L.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      hfd]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
      (hAL'.trans le_sup_right)
  have hmem := hle (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hdec hy))
  rwa [hxy] at hmem

theorem not_mem_cd_fm {A L : Subgroup G} {c d a : G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hdA : d ∈ A) (haA : a ∈ A) (haL : a ∈ L) (ha1 : a ≠ 1)
    (hcd : (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊓ L = ⊥)
    (hcd9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9) (m : ℕ) :
    a ∉ Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d := by
  intro haF
  have hA' : IsMulCommutative A ∧ ∀ x ∈ A, x ^ 3 = 1 := hA
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA'.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hxA : c * a ^ m ∈ A := A.mul_mem hcA (A.pow_mem haA m)
  have hx3 : (c * a ^ m) ^ 3 = 1 := hA'.2 _ hxA
  have hd3 : d ^ 3 = 1 := hA'.2 d hdA
  have hzxA : Subgroup.zpowers (c * a ^ m) ≤ A := Subgroup.zpowers_le.mpr hxA
  have hzdA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hcF : c ∈ Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d := by
    have key : c * a ^ m * (a ^ m)⁻¹ ∈ Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d :=
      (Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d).mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        ((Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d).inv_mem
          ((Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d).pow_mem haF m))
    have e1 : c * a ^ m * (a ^ m)⁻¹ = c := by group
    rwa [e1] at key
  have hPF : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤
      Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d :=
    sup_le (Subgroup.zpowers_le.mpr hcF) le_sup_right
  have hcomm : ∀ u ∈ Subgroup.zpowers (c * a ^ m), ∀ v ∈ Subgroup.zpowers d,
      u * v = v * u := fun u hu v hv => hAc u (hzxA hu) v (hzdA hv)
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers (c * a ^ m)) (Subgroup.zpowers d) hcomm
  have hpos : 0 < Nat.card (Subgroup.zpowers (c * a ^ m) ⊓ Subgroup.zpowers d : Subgroup G) :=
    Nat.card_pos
  have hz3 : ∀ z : G, z ^ 3 = 1 → Nat.card (Subgroup.zpowers z) ≤ 3 := fun z hz => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz)
  have hcard : Nat.card (Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d : Subgroup G) ≤ 9 := by
    calc Nat.card (Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d : Subgroup G)
        ≤ Nat.card (Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d : Subgroup G) *
            Nat.card (Subgroup.zpowers (c * a ^ m) ⊓ Subgroup.zpowers d : Subgroup G) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card (Subgroup.zpowers (c * a ^ m)) * Nat.card (Subgroup.zpowers d) := hprod
      _ ≤ 3 * 3 := Nat.mul_le_mul (hz3 _ hx3) (hz3 _ hd3)
      _ = 9 := by norm_num
  have heq : Subgroup.zpowers c ⊔ Subgroup.zpowers d =
      Subgroup.zpowers (c * a ^ m) ⊔ Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hPF (by rw [hcd9]; exact hcard)
  have haP : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [heq]
    exact haF
  have haP1 : a ∈ (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊓ L := ⟨haP, haL⟩
  rw [hcd, Subgroup.mem_bot] at haP1
  exact ha1 haP1

theorem exists_b {A L' : Subgroup G} {y d a : G} (hAc : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x)
    (hyA : y ∈ A) (hdA : d ∈ A) (haA : a ∈ A)
    (hdec : A ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers d ⊔ (A ⊓ L'))
    (hna : a ∉ Subgroup.zpowers y ⊔ Subgroup.zpowers d) :
    ∃ b ∈ A ⊓ L', b ≠ 1 ∧ b ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ∧
      a ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers b := by
  have hP'A : Subgroup.zpowers y ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hyA) (Subgroup.zpowers_le.mpr hdA)
  have hcomm : ∀ x ∈ A ⊓ L', ∀ z ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers d,
      x * z = z * x :=
    fun x hx z hz => (hAc z (hP'A hz) x (Subgroup.mem_inf.mp hx).1).symm
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (A ⊓ L')
    (Subgroup.zpowers y ⊔ Subgroup.zpowers d) hcomm
  open scoped Pointwise in
  have haK : a ∈ ((A ⊓ L' : Subgroup G) : Set G) *
      ((Subgroup.zpowers y ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [← hset, sup_comm (A ⊓ L')]
    exact hdec haA
  obtain ⟨ℓ, hℓ, p, hp, hℓp⟩ := Set.mem_mul.mp haK
  have hℓK : ℓ ∈ A ⊓ L' := hℓ
  have hpP : p ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers d := hp
  have hℓ1 : ℓ ≠ 1 := by
    intro h1
    apply hna
    rw [← hℓp, h1, one_mul]
    exact hpP
  refine ⟨ℓ, hℓK, hℓ1, ?_, ?_⟩
  ·
    have hℓeq : ℓ = a * p⁻¹ := by rw [← hℓp, mul_inv_cancel_right]
    rw [hℓeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ hpP))
  ·
    rw [← hℓp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ))
      (Subgroup.mem_sup_left hpP)

end CFSG.RankThree.PartTwo.Sec8.Hering611
