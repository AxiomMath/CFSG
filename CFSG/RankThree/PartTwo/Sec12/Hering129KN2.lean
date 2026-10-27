module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob

public section

namespace CFSG.RankThree.PartTwo.Sec12

structure SLFactor {X : Type} [Group X] (U : Subgroup X) (a z : X) : Prop where
  ha : a ∈ U
  hz : z ∈ U
  ha3 : a ^ 3 = 1
  hz3 : z ^ 3 = 1
  hz1 : z ≠ 1
  haz : a ∉ Subgroup.zpowers z
  hzc : ∀ u ∈ U, u * z = z * u
  hcomm : ∀ u ∈ U, u * a = a * u → ∀ v ∈ U, v * a = a * v → u * v = v * u
  hw : ∃ w ∈ U, w ^ 3 = 1 ∧ w * a * w⁻¹ = z * a
  hR : ∃ R : Subgroup X, R ≤ U ∧ (∀ r ∈ R, r * a = a * r) ∧ ¬ 3 ∣ Nat.card R ∧
    ∀ u ∈ U, u * a = a * u →
      ∃ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers z, ∃ r ∈ R, u = v * r

namespace Hering129KN2

theorem nine_le_card {G : Type*} [Group G] [Finite G] {a z : G} (ha3 : a ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (haz : a ∉ Subgroup.zpowers z) (S : Subgroup G) (haS : a ∈ S)
    (hzS : z ∈ S) : 9 ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha1 : a ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hinf : ∀ x ∈ Subgroup.zpowers a, x ∈ Subgroup.zpowers z → x = 1 := by
    intro x hxa hxz
    by_contra hx1
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := hxa
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    have heq : Subgroup.zpowers x = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxa)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, orderOf_eq_prime hx3 hx1])
    exact haz (Subgroup.zpowers_le.mpr hxz (heq ▸ Subgroup.mem_zpowers a))
  let F : Fin 3 × Fin 3 → S := fun ij =>
    ⟨a ^ (ij.1 : ℕ) * z ^ (ij.2 : ℕ), mul_mem (pow_mem haS _) (pow_mem hzS _)⟩
  have hF : Function.Injective F := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h' : a ^ (i : ℕ) * z ^ (j : ℕ) = a ^ (k : ℕ) * z ^ (l : ℕ) := congrArg Subtype.val h
    have h1 : (a ^ (k : ℕ))⁻¹ * a ^ (i : ℕ) = z ^ (l : ℕ) * (z ^ (j : ℕ))⁻¹ := by
      calc (a ^ (k : ℕ))⁻¹ * a ^ (i : ℕ)
          = (a ^ (k : ℕ))⁻¹ * (a ^ (i : ℕ) * z ^ (j : ℕ)) * (z ^ (j : ℕ))⁻¹ := by group
        _ = (a ^ (k : ℕ))⁻¹ * (a ^ (k : ℕ) * z ^ (l : ℕ)) * (z ^ (j : ℕ))⁻¹ := by rw [h']
        _ = z ^ (l : ℕ) * (z ^ (j : ℕ))⁻¹ := by group
    have h2 := hinf _
      (mul_mem (inv_mem (Subgroup.npow_mem_zpowers a k)) (Subgroup.npow_mem_zpowers a i))
      (h1 ▸ mul_mem (Subgroup.npow_mem_zpowers z l) (inv_mem (Subgroup.npow_mem_zpowers z j)))
    have hik : a ^ (i : ℕ) = a ^ (k : ℕ) := by
      rw [← one_mul (a ^ (i : ℕ)), ← mul_inv_cancel (a ^ (k : ℕ)), mul_assoc, h2, mul_one]
    have hjl : z ^ (j : ℕ) = z ^ (l : ℕ) := by
      rw [h2] at h1
      exact (mul_inv_eq_one.mp h1.symm).symm
    have hi := pow_injOn_Iio_orderOf (by rw [hao]; exact i.2) (by rw [hao]; exact k.2) hik
    have hj := pow_injOn_Iio_orderOf (by rw [hzo]; exact j.2) (by rw [hzo]; exact l.2) hjl
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have := Nat.card_le_card_of_injective F hF
  simpa using this

open Sec4

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_torusHom_of_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {M : GL (Fin 3) K}
    (hM : M ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) :
    ∃ x y : Kˣ, x ^ qSubPi π (p ^ f) = 1 ∧ y ^ qSubPi π (p ^ f) = 1 ∧ M = torusHom (x, y) := by
  rw [centralizer_diagTau_eq hK hq hτ hτ1] at hM
  obtain ⟨⟨x, y⟩, rfl⟩ := hM
  exact ⟨x, y, (mem_rootsOfUnity _ _).mp x.2, (mem_rootsOfUnity _ _).mp y.2, rfl⟩

theorem commute_of_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {M M' : GL (Fin 3) K}
    (hM : M ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ})
    (hM' : M' ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) :
    M * M' = M' * M := by
  obtain ⟨x, y, -, -, rfl⟩ := exists_torusHom_of_mem hK hq hτ hτ1 hM
  obtain ⟨x', y', -, -, rfl⟩ := exists_torusHom_of_mem hK hq hτ hτ1 hM'
  rw [← map_mul, ← map_mul, mul_comm]

theorem pow_qSubPi_eq_one_of_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {M : GL (Fin 3) K}
    (hM : M ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) :
    M ^ qSubPi π (p ^ f) = 1 := by
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_torusHom_of_mem hK hq hτ hτ1 hM
  rw [← map_pow, Prod.pow_mk, hx, hy]
  exact map_one _

theorem card_le_nine_of_le (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {T : Subgroup (GL (Fin 3) K)}
    (hT : T ≤ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ})
    (hT3 : ∀ M ∈ T, M ^ 3 = 1) : Nat.card T ≤ 9 := by
  have := hK.finite
  set μ := rootsOfUnity 3 K
  have hle : T ≤ (μ.prod μ).map torusHom := by
    intro M hM
    obtain ⟨x, y, -, -, hxy⟩ := exists_torusHom_of_mem hK hq hτ hτ1 (hT hM)
    have h3 : torusHom (x ^ 3, y ^ 3) = torusHom 1 := by
      rw [← Prod.pow_mk, map_pow, ← hxy, hT3 _ hM, map_one]
    obtain ⟨hx3, hy3⟩ := Prod.mk_eq_one.mp (torusHom_injective h3)
    exact ⟨(x, y), ⟨(mem_rootsOfUnity _ _).mpr hx3, (mem_rootsOfUnity _ _).mpr hy3⟩, hxy.symm⟩
  calc Nat.card T ≤ Nat.card ((μ.prod μ).map torusHom) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (μ.prod μ) :=
        Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective torusHom _)
    _ = Nat.card μ * Nat.card μ := by
        rw [Nat.card_congr (Subgroup.prodEquiv μ μ).toEquiv, Nat.card_prod]
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 3) (card_rootsOfUnity K 3)

end Hering129KN2

theorem slFactor_of_slPi {X : Type} [Group X] {U : Subgroup X} {π : Bool} {p f : ℕ} {K : Type}
    [Field K] (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (h9 : ¬ Sec4.ModNine π (p ^ f)) (e : ↥U ≃* Sec4.slPi π 3 (p ^ f) K) {a z : X} (ha : a ∈ U)
    (hz : z ∈ U) (hz1 : z ≠ 1) (hzc : ∀ u ∈ U, u * z = z * u) (ha3 : a ^ 3 = 1)
    (haz : a ∉ Subgroup.zpowers z) : SLFactor U a z := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by subst h; exact hq
  have : Finite K := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite U := Finite.of_equiv _ e.symm.toEquiv
  have hdet1 : ∀ M ∈ Sec4.slPi π 3 (p ^ f) K, (M : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    fun M hM => ((Sec4.mem_slPi_iff hπ).mp hM).2
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨a', rfl⟩ : ∃ a' : U, (a' : X) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨z', rfl⟩ : ∃ z' : U, (z' : X) = z := ⟨⟨z, hz⟩, rfl⟩
  have hzc' : ∀ u : U, u * z' = z' * u := fun u => Subtype.ext (hzc u u.2)
  have hsc := Sec4.mem_statedScalars_of_commute hπ hq' hτ hτ1 (g := (e z' : GL (Fin 3) K))
    fun M hM => by
      obtain ⟨u, hu⟩ := e.surjective ⟨M, hM⟩
      have h1 : e z' * e u = e u * e z' := by rw [← map_mul, ← map_mul, hzc' u]
      rw [hu] at h1
      exact congrArg Subtype.val h1
  obtain ⟨ζ, hζ⟩ := hsc
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    rw [← Sec4.det_scalar, hζ]
    exact hdet1 _ (e z').2
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζ3', Units.val_one])
  have hz'1 : z' ≠ 1 := fun h => hz1 (by rw [h]; rfl)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    apply hz'1
    have h1 : e z' = 1 := Subtype.ext (by rw [← hζ, map_one]; rfl)
    exact e.injective (h1.trans (map_one e).symm)
  have hζ1' : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  have hz'3 : z' ^ 3 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, SubgroupClass.coe_pow, ← hζ, ← map_pow, hζ3, map_one, map_one]
    rfl
  have hz3 : (z' : X) ^ 3 = 1 := by simpa using congrArg Subtype.val hz'3
  have ha'3 : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have ha'z : a' ∉ Subgroup.zpowers z' := by
    rintro ⟨k, hk⟩
    exact haz ⟨k, by simpa using congrArg Subtype.val hk⟩
  have ha'1 : a' ≠ 1 := fun h => ha'z (h ▸ Subgroup.one_mem _)
  have hA3 : (e a' : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, ← map_pow, ha'3, map_one]
    rfl
  have hA1 : (e a' : GL (Fin 3) K) ≠ 1 := by
    intro h
    apply ha'1
    have h1 : e a' = 1 := Subtype.ext (by rw [h]; rfl)
    exact e.injective (h1.trans (map_one e).symm)
  have hAo : orderOf (e a' : GL (Fin 3) K) = 3 := orderOf_eq_prime hA3 hA1
  have hAZ : (e a' : GL (Fin 3) K) ∉ Sec4.zPi π 3 (p ^ f) K := by
    intro hA
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hA
    obtain ⟨-, s, hs⟩ := Subgroup.mem_inf.mp hA
    have hs3' : (s : K) ^ 3 = 1 := by
      rw [← Sec4.det_scalar, hs]
      exact hdet1 _ (e a').2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = ζ ^ k := by
      rcases Sec4.cube_root_cases hζ3' hζ1' hs3' with h | h | h
      · exact ⟨0, Units.ext (by rw [h]; simp)⟩
      · exact ⟨1, Units.ext (by rw [h]; simp)⟩
      · exact ⟨2, Units.ext (by rw [h]; simp)⟩
    apply ha'z
    have : a' = z' ^ k := by
      apply e.injective
      apply Subtype.ext
      rw [map_pow, SubgroupClass.coe_pow, ← hζ, ← map_pow, ← hk, hs]
    rw [this]
    exact pow_mem (Subgroup.mem_zpowers z') k
  obtain ⟨g, hg, hgA⟩ := Sec4.rank3II_4_10_three hK hq hτ hτ1 (e a').2 hAZ hAo
  set d := Sec4.diagTau hτ with hd
  set φ : U →* GL (Fin 3) K := (MulAut.conj g⁻¹).toMonoidHom.comp
    ((Sec4.slPi π 3 (p ^ f) K).subtype.comp e.toMonoidHom)
  have hφ : ∀ u, φ u = g⁻¹ * (e u : GL (Fin 3) K) * g := fun u => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := by
    intro u v h
    rw [hφ, hφ] at h
    have h' : (e u : GL (Fin 3) K) = e v := by
      have := congrArg (fun x => g * x * g⁻¹) h
      simpa [mul_assoc] using this
    exact e.injective (Subtype.ext h')
  have hφL : ∀ u, φ u ∈ Sec4.slPi π 3 (p ^ f) K := fun u => by
    rw [hφ]
    have := Sec4.conj_mem_slPi hπ (inv_mem hg) (e u).2
    rwa [inv_inv] at this
  have hφsurj : ∀ M ∈ Sec4.slPi π 3 (p ^ f) K, ∃ u, φ u = M := fun M hM =>
    ⟨e.symm ⟨g * M * g⁻¹, Sec4.conj_mem_slPi hπ hg hM⟩, by
      rw [hφ, MulEquiv.apply_symm_apply]
      group⟩
  have hφa : φ a' = d := by rw [hφ, hgA]
  have hφz : φ z' = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ := by
    rw [hφ, ← hζ, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g⁻¹).eq,
      inv_mul_cancel_right]
  have hφC : ∀ u : U, u * a' = a' * u →
      φ u ∈ Sec4.slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {d} := by
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨hφL u, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hφa, ← map_mul, ← map_mul, hu]
  have hcommU : ∀ u v : U, u * a' = a' * u → v * a' = a' * v → u * v = v * u := by
    intro u v hu hv
    apply hφinj
    rw [map_mul, map_mul]
    exact Hering129KN2.commute_of_mem hK hq hτ hτ1 (hφC u hu) (hφC v hv)
  have hcomm : ∀ u ∈ U, u * a' = a' * u → ∀ v ∈ U, v * a' = a' * v → u * v = v * u := by
    intro u hu hua v hv hva
    exact congrArg Subtype.val (hcommU ⟨u, hu⟩ ⟨v, hv⟩ (Subtype.ext hua) (Subtype.ext hva))
  have hw : ∃ w ∈ U, w ^ 3 = 1 ∧ w * a' * w⁻¹ = z' * a' := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Units.mk0 τ hτ0 ^ (2 * k) = ζ := by
      rcases Sec4.cube_root_cases hτ hτ1 hζ3' with h | h | h
      · exact absurd h hζ1'
      · refine ⟨2, Units.ext ?_⟩
        rw [h, Units.val_pow_eq_pow_val, Units.val_mk0]
        calc τ ^ (2 * 2) = τ ^ 3 * τ := by ring
          _ = τ := by rw [hτ, one_mul]
      · exact ⟨1, Units.ext (by rw [h, Units.val_pow_eq_pow_val, Units.val_mk0])⟩
    have hcyc3 : (Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    have hcL : Sec4.cycThree ^ k ∈ Sec4.slPi π 3 (p ^ f) K :=
      pow_mem (Sec4.cycThree_mem_slPi hπ) k
    have hc3 : (Sec4.cycThree ^ k : GL (Fin 3) K) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hcyc3, one_pow]
    have hcd : Sec4.cycThree ^ k * d * (Sec4.cycThree ^ k)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * d := by
      rw [hd, Sec4.cycThree_pow_conj_diagTau hτ hτ0 k, hk]
    obtain ⟨w, hw⟩ := hφsurj _ hcL
    refine ⟨w, w.2, ?_, ?_⟩
    · have : w ^ 3 = 1 := hφinj (by rw [map_pow, hw, hc3, map_one])
      simpa using congrArg Subtype.val this
    · have : w * a' * w⁻¹ = z' * a' := hφinj (by
        simp only [map_mul, map_inv, hw, hφa, hφz]
        exact hcd)
      simpa using congrArg Subtype.val this
  let E : Subgroup U :=
    { carrier := {x | x * a' = a' * x ∧ x ^ 3 = 1}
      mul_mem' := by
        rintro x y ⟨hxa, hx3⟩ ⟨hya, hy3⟩
        refine ⟨by rw [mul_assoc, hya, ← mul_assoc, hxa, mul_assoc], ?_⟩
        rw [(show Commute x y from hcommU x y hxa hya).mul_pow, hx3, hy3, one_mul]
      one_mem' := ⟨by rw [one_mul, mul_one], one_pow 3⟩
      inv_mem' := by
        rintro x ⟨hxa, hx3⟩
        refine ⟨?_, by rw [inv_pow, hx3, inv_one]⟩
        calc x⁻¹ * a' = x⁻¹ * (a' * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * a') * x⁻¹ := by rw [hxa]
          _ = a' * x⁻¹ := by group }
  have hE9 : Nat.card E ≤ 9 := by
    rw [← Subgroup.card_map_of_injective hφinj]
    refine Hering129KN2.card_le_nine_of_le hK hq hτ hτ1 ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact hφC u hu.1
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow, hu.2, map_one]
  have hSE : (Subgroup.zpowers a' ⊔ Subgroup.zpowers z' : Subgroup U) = E :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr ⟨rfl, ha'3⟩)
        (Subgroup.zpowers_le.mpr ⟨(hzc' a').symm, hz'3⟩))
      (hE9.trans (Hering129KN2.nine_le_card ha'3 hz'3 hz'1 ha'z _
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a'))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z'))))
  have hF2 : ∀ x ∈ U, x * a' = a' * x → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers (a' : X) ⊔ Subgroup.zpowers (z' : X) := by
    intro x hx hxa hx3
    have hxE : (⟨x, hx⟩ : U) ∈ E := ⟨Subtype.ext hxa, Subtype.ext (by simpa using hx3)⟩
    rw [← hSE] at hxE
    have := Subgroup.mem_map_of_mem U.subtype hxE
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
    exact this
  obtain ⟨m, hm⟩ := Sec4.three_dvd_qSubPi hq
  have hm3 : ¬ 3 ∣ m := by
    rintro ⟨k, rfl⟩
    apply h9
    rw [Sec4.modNine_iff (Nat.one_le_pow _ _ hK.prime.pos)]
    exact ⟨k, by rw [hm]; ring⟩
  have hexp : ∀ x ∈ U, x * a' = a' * x → x ^ (3 * m) = 1 := by
    intro x hx hxa
    have h1 :=
      Hering129KN2.pow_qSubPi_eq_one_of_mem hK hq hτ hτ1 (hφC ⟨x, hx⟩ (Subtype.ext hxa))
    rw [hm, ← map_pow] at h1
    have : (⟨x, hx⟩ : U) ^ (3 * m) = 1 := hφinj (by rw [h1, map_one])
    simpa using congrArg Subtype.val this
  let R : Subgroup X :=
    { carrier := {r | r ∈ U ∧ r * a' = a' * r ∧ r ^ m = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxa, hxm⟩ ⟨hy, hya, hym⟩
        refine ⟨mul_mem hx hy, by rw [mul_assoc, hya, ← mul_assoc, hxa, mul_assoc], ?_⟩
        rw [(show Commute x y from hcomm x hx hxa y hy hya).mul_pow, hxm, hym, one_mul]
      one_mem' := ⟨one_mem U, by rw [one_mul, mul_one], one_pow m⟩
      inv_mem' := by
        rintro x ⟨hx, hxa, hxm⟩
        refine ⟨inv_mem hx, ?_, by rw [inv_pow, hxm, inv_one]⟩
        calc x⁻¹ * a' = x⁻¹ * ((a' : X) * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * a') * x⁻¹ := by rw [hxa]
          _ = a' * x⁻¹ := by group }
  have hRU : R ≤ U := fun r hr => hr.1
  refine ⟨a'.2, z'.2, ha3, hz3, hz1, haz, hzc, hcomm, hw, R, hRU, fun r hr => hr.2.1, ?_, ?_⟩
  ·
    intro h3
    have : Finite R :=
      Finite.of_injective (Subgroup.inclusion hRU) (Subgroup.inclusion_injective hRU)
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hrm : r ^ m = 1 := Subtype.ext (by simpa using r.2.2.2)
    exact hm3 (hr ▸ orderOf_dvd_of_pow_eq_one hrm)
  ·
    intro u hu hua
    have hu3m := hexp u hu hua
    have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    have hbez : (3 : ℤ) * Nat.gcdA 3 m + m * Nat.gcdB 3 m = 1 := by
      have := Nat.gcd_eq_gcd_ab 3 m
      rw [hcop.gcd_eq_one] at this
      push_cast at this
      linarith
    have hpow : ∀ k : ℤ, (u ^ ((3 * m : ℕ) : ℤ)) ^ k = 1 := fun k => by
      rw [zpow_natCast, hu3m, one_zpow]
    refine ⟨u ^ ((m : ℤ) * Nat.gcdB 3 m), hF2 _ (zpow_mem hu _)
      (Commute.zpow_left (show Commute u a' from hua) _).eq ?_, u ^ ((3 : ℤ) * Nat.gcdA 3 m),
      ⟨zpow_mem hu _, (Commute.zpow_left (show Commute u a' from hua) _).eq, ?_⟩, ?_⟩
    · rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * Nat.gcdB 3 m * ((3 : ℕ) : ℤ) =
        ((3 * m : ℕ) : ℤ) * Nat.gcdB 3 m by push_cast; ring, zpow_mul, hpow]
    · rw [← zpow_natCast, ← zpow_mul, show (3 : ℤ) * Nat.gcdA 3 m * (m : ℤ) =
        ((3 * m : ℕ) : ℤ) * Nat.gcdA 3 m by push_cast; ring, zpow_mul, hpow]
    · rw [← zpow_add, show (m : ℤ) * Nat.gcdB 3 m + 3 * Nat.gcdA 3 m = 1 by linarith, zpow_one]

end CFSG.RankThree.PartTwo.Sec12
