module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3TorusFrame
import CFSG.ClassicalGroups.UnitaryFlag.SU3TwoGroupCyclic
import CFSG.ClassicalGroups.UnitaryFlag.ThreeRootGroups
import CFSG.Quasithin.Background.RonanF610Sylow

public section

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrred

variable {n : ℕ} {K : Type} [Field K] {T H : Subgroup (unitarySU 2 n K 3)}

private theorem smul_span_singleton (g : unitarySU 2 n K 3) (x : Fin 3 → K) :
    g • (K ∙ x) = K ∙ (g • x) := by
  change (g : GL (Fin 3) K) • (K ∙ x) = K ∙ ((g : GL (Fin 3) K) • x)
  rw [smul_eq_map, Submodule.map_span, Set.image_singleton]
  rfl

private theorem mem_span_v_of_orthogonal {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    {x : Fin 3 → K} (he : stdHermForm h 3 F.e x = 0) (hf : stdHermForm h 3 F.f x = 0) :
    x ∈ K ∙ F.v := by
  have hxmem : x ∈ (K ∙ F.e ⊔ K ∙ F.v) ⊔ K ∙ F.f := by
    rw [F.sup_eq_top]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hxmem
  obtain ⟨y, hy, z, hz, rfl⟩ := hxmem
  rw [Submodule.mem_sup] at hy
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy₂
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc0 : c = 0 := by
    have h1 := he
    simp only [map_add, map_smul, F.stdHermForm_e_e,
      F.stdHermForm_e_v, F.stdHermForm_e_f, mul_zero, smul_eq_mul, mul_one, add_zero,
      zero_add] at h1
    exact h1
  have ha0 : a = 0 := by
    have h1 := hf
    have hfe : stdHermForm h 3 F.f F.e = 1 := F.stdHermForm_f_e
    simp only [map_add, map_smul, F.stdHermForm_f_f,
      F.stdHermForm_f_v, hfe, mul_zero, smul_eq_mul, mul_one, add_zero] at h1
    exact h1
  subst c
  subst a
  simpa using Submodule.smul_mem (K ∙ F.v) b (Submodule.mem_span_singleton_self F.v)

private theorem range_subOne_eq_of_mem_isPGroup (h : UnitaryFieldData 2 n K)
    {P : Subgroup (unitarySU 2 n K 3)} (hP : IsPGroup 2 P)
    {i j : unitarySU 2 n K 3} (hiP : i ∈ P) (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1)
    (hjP : j ∈ P) (hj2 : j ^ 2 = 1) (hj1 : j ≠ 1) :
    LinearMap.range (subOne j) = LinearMap.range (subOne i) := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hodd : Odd (orderOf (i * j)) :=
    odd_orderOf_mul_of_range_subOne_ne h hi2 hi1 hj2 hj1 (fun he => hne he.symm)
  have hmem : i * j ∈ P := P.mul_mem hiP hjP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : orderOf (i * j) ∣ 2 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard P hmem
  have h1 : orderOf (i * j) = 1 := by
    have hcop : (orderOf (i * j)).Coprime (2 ^ k) :=
      (Odd.coprime_two_right hodd).pow_right k
    exact Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd
  have hij : i * j = 1 := orderOf_eq_one_iff.mp h1
  have hji : j = i := by
    calc j = 1 * j := (one_mul j).symm
      _ = (i * j) * j := by rw [hij]
      _ = i * (j * j) := by rw [mul_assoc]
      _ = i := by rw [← pow_two, hj2, mul_one]
  exact hne (by rw [hji])

private theorem smul_range_subOne_eq_of_mem_normalizer (h : UnitaryFieldData 2 n K)
    {P : Subgroup (unitarySU 2 n K 3)} {i : unitarySU 2 n K 3}
    (hiP : i ∈ P) (hi2 : i ^ 2 = 1) (hi1 : i ≠ 1) {z : unitarySU 2 n K 3}
    (hzP : z ∈ Subgroup.normalizer (P : Set (unitarySU 2 n K 3)))
    (hsame : ∀ j ∈ P, j ^ 2 = 1 → j ≠ 1 →
      LinearMap.range (subOne j) = LinearMap.range (subOne i)) :
    z • LinearMap.range (subOne i) = LinearMap.range (subOne i) := by
  have hconjP : z * i * z⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hzP i).mp hiP
  have hconj2 : (z * i * z⁻¹) ^ 2 = 1 := by
    rw [show z * i * z⁻¹ = MulAut.conj z i from (MulAut.conj_apply z i).symm, ← map_pow, hi2,
      map_one]
  have hconj1 : z * i * z⁻¹ ≠ 1 := by
    intro ht
    apply hi1
    apply (MulAut.conj z).injective
    rw [map_one]
    rwa [MulAut.conj_apply]
  have hrange := hsame (z * i * z⁻¹) hconjP hconj2 hconj1
  rwa [range_subOne_conj h z i] at hrange

private theorem false_of_isotropicLine_fixed {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    (hT1 : T ≠ ⊥) {z : unitarySU 2 n K 3} (hze : z • F.e ∈ K ∙ F.f)
    {Y : Submodule K (Fin 3 → K)} (hY : Y ∈ isotropicLines h 3)
    (hTY : ∀ t ∈ T, t • Y = Y) (hzY : z • Y = Y) : False := by
  have he0 := F.e_ne_zero
  have hf0 := F.f_ne_zero
  have hKe_ne_Kf : (K ∙ F.e) ≠ (K ∙ F.f) := by
    intro heq
    exact F.e_notMem_span_f (heq ▸ Submodule.mem_span_singleton_self F.e)
  have hze0 : z • F.e ≠ 0 := (smul_ne_zero_iff_ne z).2 F.e_ne_zero
  have hzeq : K ∙ (z • F.e) = K ∙ F.f :=
    (eq_span_singleton_of_mem_of_finrank_eq_one (S := K ∙ F.f) (w := z • F.e)
      (finrank_span_singleton hf0) hze hze0).symm
  have hzE : z • (K ∙ F.e) = K ∙ F.f := by
    rw [smul_span_singleton, hzeq]
  rcases F.eq_or_eq_of_smul_eq hT1 hY hTY with hY' | hY'
  · have h1 : z • (K ∙ F.e) = K ∙ F.e := by
      calc z • (K ∙ F.e) = z • Y := by rw [hY']
        _ = Y := hzY
        _ = K ∙ F.e := hY'
    exact hKe_ne_Kf (h1.symm.trans hzE)
  · have h1 : z • (K ∙ F.e) = z • (K ∙ F.f) := by
      calc z • (K ∙ F.e) = K ∙ F.f := hzE
        _ = Y := hY'.symm
        _ = z • Y := hzY.symm
        _ = z • (K ∙ F.f) := by rw [hY']
    have h2 : K ∙ F.e = K ∙ F.f := by
      have h3 := congrArg (fun L => z⁻¹ • L) h1
      simpa using h3
    exact hKe_ne_Kf h2

theorem eq_bot_of_isPGroup_of_le_normalizer {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    (hT1 : T ≠ ⊥) {z : unitarySU 2 n K 3} (hze : z • F.e ∈ K ∙ F.f)
    {P : Subgroup (unitarySU 2 n K 3)} (hP : IsPGroup 2 P)
    (hTP : T ≤ Subgroup.normalizer (P : Set (unitarySU 2 n K 3)))
    (hzP : z ∈ Subgroup.normalizer (P : Set (unitarySU 2 n K 3))) : P = ⊥ := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hPne
  have hcardP : Nat.card P ≠ 1 := fun hc => hPne (Subgroup.eq_bot_of_card_eq P hc)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hcardP (by simpa using hk)
  have h2dvd : 2 ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨i₀, hi₀⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  set i : unitarySU 2 n K 3 := (i₀ : unitarySU 2 n K 3) with hidef
  have hiP : i ∈ P := i₀.2
  have hi2 : i ^ 2 = 1 := by
    have h : i₀ ^ 2 = 1 := by simpa [hi₀] using pow_orderOf_eq_one i₀
    simpa using congrArg (fun x : ↥P => (x : unitarySU 2 n K 3)) h
  have hi1 : i ≠ 1 := by
    intro h
    have h' : i₀ = 1 := Subtype.ext (show (i₀ : unitarySU 2 n K 3) = 1 from h)
    rw [h', orderOf_one] at hi₀
    omega
  have hsame : ∀ j ∈ P, j ^ 2 = 1 → j ≠ 1 →
      LinearMap.range (subOne j) = LinearMap.range (subOne i) :=
    fun j hjP hj2 hj1 => range_subOne_eq_of_mem_isPGroup h hP hiP hi2 hi1 hjP hj2 hj1
  have hYfix : ∀ t ∈ T, t • LinearMap.range (subOne i) = LinearMap.range (subOne i) :=
    fun t ht => smul_range_subOne_eq_of_mem_normalizer h hiP hi2 hi1 (hTP ht) hsame
  exact false_of_isotropicLine_fixed F hT1 hze
    (involution_mem_isotropicTransvectionGroup h hi2 hi1).1 hYfix
    (smul_range_subOne_eq_of_mem_normalizer h hiP hi2 hi1 hzP hsame)

private theorem le_stabilizer_isotropicTransvectionGroup_range_subOne
    {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T) {z : unitarySU 2 n K 3}
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzv : z • F.v = F.v) :
    isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)) ≤
      MulAction.stabilizer (unitarySU 2 n K 3) F.v := by
  have hzdata := involution_mem_isotropicTransvectionGroup h hz2 hz1
  have hx₀ : LinearMap.range (subOne z) ∈ isotropicLines h 3 := hzdata.1
  have hkerz : LinearMap.ker (subOne z) = hermPerp h (LinearMap.range (subOne z)) := hzdata.2.2
  have hvper : F.v ∈ hermPerp h (LinearMap.range (subOne z)) := by
    rw [← hkerz, LinearMap.mem_ker, subOne_apply h, hzv, sub_self]
  intro u hu
  rw [MulAction.mem_stabilizer_iff]
  by_cases hu1 : u = 1
  · rw [hu1, one_smul]
  · have hkeru := ker_subOne_of_mem_isotropicTransvectionGroup hx₀ hu hu1
    have hmem : F.v ∈ LinearMap.ker (subOne u) := by rw [hkeru]; exact hvper
    rw [LinearMap.mem_ker, subOne_apply h] at hmem
    exact sub_eq_zero.mp hmem

private theorem inf_le_pair_of_le_normalizer {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    (hT1 : T ≠ ⊥)
    (hle : H ⊓ MulAction.stabilizer (unitarySU 2 n K 3) F.v ≤
      Subgroup.normalizer (T : Set (unitarySU 2 n K 3)))
    {z : unitarySU 2 n K 3} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzv : z • F.v = F.v)
    (hze : z • F.e ∈ K ∙ F.f) (hzf : z • F.f ∈ K ∙ F.e) :
    ∀ u ∈ H ⊓ isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)), u = 1 ∨ u = z := by
  have hx₀ : LinearMap.range (subOne z) ∈ isotropicLines h 3 :=
    (involution_mem_isotropicTransvectionGroup h hz2 hz1).1
  have hRle := le_stabilizer_isotropicTransvectionGroup_range_subOne F hz2 hz1 hzv
  intro u hu
  obtain ⟨huH, huR⟩ := Subgroup.mem_inf.mp hu
  have huN : u ∈ Subgroup.normalizer (T : Set (unitarySU 2 n K 3)) :=
    hle (Subgroup.mem_inf.mpr ⟨huH, hRle huR⟩)
  obtain ⟨hu_v, hu_ef⟩ := F.smul_mem_of_mem_normalizer hT1 huN
  obtain ⟨k, huk⟩ := (isPGroup_isotropicTransvectionGroup h hx₀).exists_pow_pow_eq_one
    (⟨u, huR⟩ : isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)))
  have huk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val huk
  rcases hu_ef with ⟨hue, huf⟩ | ⟨hue, huf⟩
  · exact Or.inl (F.eq_one_of_pow_two_pow_eq_one huk' hue hu_v huf)
  · right
    have huz_e : (u * z) • F.e ∈ K ∙ F.e := by
      rw [mul_smul]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hze
      rw [← hc, smul_comm]
      exact Submodule.smul_mem _ c huf
    have huz_f : (u * z) • F.f ∈ K ∙ F.f := by
      rw [mul_smul]
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hzf
      rw [← hd, smul_comm]
      exact Submodule.smul_mem _ d hue
    have huz_v : (u * z) • F.v ∈ K ∙ F.v := by
      rw [mul_smul, hzv]
      exact hu_v
    have huzR : u * z ∈ isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)) :=
      (isotropicTransvectionGroup h 3 (LinearMap.range (subOne z))).mul_mem huR
        (involution_mem_isotropicTransvectionGroup h hz2 hz1).2.1
    obtain ⟨m, huzm⟩ := (isPGroup_isotropicTransvectionGroup h hx₀).exists_pow_pow_eq_one
      (⟨u * z, huzR⟩ : isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)))
    have huzm' : (u * z) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val huzm
    have huz1 : u * z = 1 := F.eq_one_of_pow_two_pow_eq_one huzm' huz_e huz_v huz_f
    calc u = u * (z * z) := by rw [← pow_two, hz2, mul_one]
      _ = (u * z) * z := by rw [mul_assoc]
      _ = z := by rw [huz1, one_mul]

private theorem false_of_sylow_two_unique_involution {h : UnitaryFieldData 2 n K} (hne : Even n)
    (hH : Group.IsPerfect H) {z : unitarySU 2 n K 3} (hzH : z ∈ H) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1)
    (hpair : ∀ u ∈ H ⊓ isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)),
      u = 1 ∨ u = z) : False := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf (⟨z, hzH⟩ : ↥H) = 2 :=
    orderOf_eq_prime (by simpa using hz2) (by simpa using hz1)
  have hzp : IsPGroup 2 (Subgroup.zpowers (⟨z, hzH⟩ : ↥H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one])
  obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
  have hzS_mem : (⟨z, hzH⟩ : ↥H) ∈ (S : Subgroup ↥H) := hzS (Subgroup.mem_zpowers _)
  set S' : Subgroup (unitarySU 2 n K 3) := (S : Subgroup ↥H).map H.subtype with hS'def
  have hzS' : z ∈ S' := by
    rw [hS'def, Subgroup.mem_map]
    exact ⟨⟨z, hzH⟩, hzS_mem, rfl⟩
  have hS'p : IsPGroup 2 S' := S.isPGroup'.map H.subtype
  have hS'inv : ∀ t ∈ S', t ^ 2 = 1 → t = 1 ∨ t = z := by
    intro t htS' ht2
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · right
      have hrange : LinearMap.range (subOne t) = LinearMap.range (subOne z) :=
        range_subOne_eq_of_mem_isPGroup h hS'p hzS' hz2 hz1 htS' ht2 ht1
      have htR : t ∈ isotropicTransvectionGroup h 3 (LinearMap.range (subOne z)) := by
        have := (involution_mem_isotropicTransvectionGroup h ht2 ht1).2.1
        rwa [hrange] at this
      have htH : t ∈ H := by
        obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp htS'
        rw [← hx]
        exact x.2
      rcases hpair t (Subgroup.mem_inf.mpr ⟨htH, htR⟩) with h1 | h1
      · exact absurd h1 ht1
      · exact h1
  have : IsCyclic ↥S' := isCyclic_of_isPGroup_of_forall_sq_eq_one h hne hS'p z hS'inv
  have hcycS : IsCyclic ↥(S : Subgroup ↥H) :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (S : Subgroup ↥H) H.subtype H.subtype_injective).symm
      (Subgroup.equivMapOfInjective (S : Subgroup ↥H) H.subtype H.subtype_injective).symm.surjective
  have hcardS : Nat.card ↥(S : Subgroup ↥H) ≠ 1 := by
    intro hc
    have hbot : (S : Subgroup ↥H) = ⊥ := Subgroup.eq_bot_of_card_eq (S : Subgroup ↥H) hc
    have hzbot : (⟨z, hzH⟩ : ↥H) ∈ (⊥ : Subgroup ↥H) := hbot ▸ hzS_mem
    rw [Subgroup.mem_bot] at hzbot
    exact hz1 (Subtype.ext_iff.mp hzbot)
  exact CFSG.Quasithin.RonanF610.not_isCyclic_sylow_two_of_isPerfect hH S hcardS hcycS

theorem not_inf_stabilizer_le_normalizer {h : UnitaryFieldData 2 n K} (hne : Even n)
    (F : SU3TorusFrame h T) (hT1 : T ≠ ⊥) (hH : Group.IsPerfect H) {z : unitarySU 2 n K 3}
    (hzH : z ∈ H) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzv : z • F.v = F.v)
    (hze : z • F.e ∈ K ∙ F.f) (hzf : z • F.f ∈ K ∙ F.e) :
    ¬ H ⊓ MulAction.stabilizer (unitarySU 2 n K 3) F.v ≤
      Subgroup.normalizer (T : Set (unitarySU 2 n K 3)) := by
  intro hle
  exact false_of_sylow_two_unique_involution hne hH hzH hz2 hz1
    (inf_le_pair_of_le_normalizer F hT1 hle hz2 hz1 hzv hze hzf)

private theorem exists_smul_v_not_mem_span {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ H, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ g ∈ H, g • F.v ∉ K ∙ F.v := by
  have hv0 := F.v_ne_zero
  have hne_bot : (K ∙ F.v) ≠ ⊥ := by
    intro hbot
    have hmem : F.v ∈ (⊥ : Submodule K (Fin 3 → K)) :=
      hbot ▸ Submodule.mem_span_singleton_self F.v
    exact hv0 (by simpa using hmem)
  have hne_top : (K ∙ F.v) ≠ ⊤ := by
    intro htop
    have hfr : Module.finrank K ↥(K ∙ F.v) = 1 := finrank_span_singleton hv0
    rw [htop, finrank_top,
      show Module.finrank K (Fin 3 → K) = 3 from Module.finrank_fin_fun K] at hfr
    omega
  by_contra hcon
  push Not at hcon
  have hinv : ∀ g ∈ H, ∀ w ∈ (K ∙ F.v), g • w ∈ K ∙ F.v := by
    intro g hg w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [smul_comm]
    exact Submodule.smul_mem _ a (hcon g hg)
  rcases hirr (K ∙ F.v) hinv with hbot | htop
  · exact hne_bot hbot
  · exact hne_top htop

private theorem exists_smul_line_not_mem_sup {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    {g : unitarySU 2 n K 3} (hgv : g • F.v ∉ K ∙ F.v) :
    ∃ x ∈ ({F.e, F.f} : Set (Fin 3 → K)), g • x ∉ K ∙ F.e ⊔ K ∙ F.f := by
  have he0 := F.e_ne_zero
  have hf0 := F.f_ne_zero
  by_contra hcon
  push Not at hcon
  have hge : g • F.e ∈ K ∙ F.e ⊔ K ∙ F.f := hcon F.e (by simp)
  have hgf : g • F.f ∈ K ∙ F.e ⊔ K ∙ F.f := hcon F.f (by simp)
  set W : Submodule K (Fin 3 → K) := K ∙ F.e ⊔ K ∙ F.f with hWdef
  have hgW_le : g • W ≤ W := by
    rw [hWdef, unitarySU_smul_sup h g (K ∙ F.e) (K ∙ F.f)]
    refine sup_le ?_ ?_
    · rw [smul_span_singleton]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hge
    · rw [smul_span_singleton]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hgf
  have hfr : Module.finrank K ↥(g • W) = Module.finrank K ↥W :=
    LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K (Fin 3 → K) g) W
  have hgW : g • W = W := Submodule.eq_of_le_of_finrank_eq hgW_le hfr
  have hgWmap : g • W = W.map (Matrix.mulVecLin (g : GL (Fin 3) K)) := by
    change (g : GL (Fin 3) K) • W = W.map (Matrix.mulVecLin (g : GL (Fin 3) K))
    exact smul_eq_map (g : GL (Fin 3) K) W
  have hvW : F.v ∈ hermPerp h W := by
    rw [mem_hermPerp]
    intro a ha
    rw [hWdef, Submodule.mem_sup] at ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha₁
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ha₂
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂,
      F.stdHermForm_e_v, F.stdHermForm_f_v, smul_eq_mul, mul_zero, add_zero]
  have hgv_perp : g • F.v ∈ hermPerp h W := by
    rw [mem_hermPerp]
    intro a ha
    have haW : a ∈ W.map (Matrix.mulVecLin (g : GL (Fin 3) K)) := by
      have h1 : a ∈ g • W := by
        rw [hgW]
        exact ha
      rwa [hgWmap] at h1
    obtain ⟨b, hb, hbval⟩ := Submodule.mem_map.mp haW
    have hgb : g • b = a := by
      rw [unitarySU_smul_def h g b]
      exact hbval
    rw [← hgb, stdHermForm_smul_smul h g b F.v]
    exact (mem_hermPerp.mp hvW) b hb
  have hle : hermPerp h W ≤ K ∙ F.v := by
    intro x hx
    exact mem_span_v_of_orthogonal F
      ((mem_hermPerp.mp hx) F.e (by
        rw [hWdef]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self F.e)))
      ((mem_hermPerp.mp hx) F.f (by
        rw [hWdef]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self F.f)))
  exact hgv (hle hgv_perp)

private theorem sup_three_lines_eq_top {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    {g : unitarySU 2 n K 3} {x : Fin 3 → K} (hx12 : x = F.e ∨ x = F.f)
    (hgx : g • x ∉ K ∙ F.e ⊔ K ∙ F.f) :
    (K ∙ F.e) ⊔ (K ∙ F.f) ⊔ (K ∙ (g • x)) = ⊤ := by
  have he0 := F.e_ne_zero
  have hf0 := F.f_ne_zero
  have hx0 : x ≠ 0 := by
    rcases hx12 with rfl | rfl
    · exact he0
    · exact hf0
  have hw0 : g • x ≠ 0 := (smul_ne_zero_iff_ne g).2 hx0
  have hA : Module.finrank K ↥((K ∙ F.e) ⊔ (K ∙ F.f)) = 2 := by
    have h1 : Module.finrank K ↥(K ∙ F.e) = 1 := finrank_span_singleton he0
    have h2 : Module.finrank K ↥(K ∙ F.f) = 1 := finrank_span_singleton hf0
    have hinf : (K ∙ F.e) ⊓ (K ∙ F.f) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv1
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv2
      have hb0 : b = 0 := by
        have hh := congrArg (stdHermForm h 3 F.e) hb
        simp only [map_smul, F.stdHermForm_e_e,
          F.stdHermForm_e_f, smul_eq_mul, mul_one, mul_zero] at hh
        exact hh
      have : a • F.e = 0 := by rw [← hb, hb0, zero_smul]
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ F.e) (K ∙ F.f)
    rw [hinf, h1, h2, finrank_bot] at h
    omega
  have hfinW : Module.finrank K ↥(K ∙ (g • x)) = 1 := finrank_span_singleton hw0
  have hdisj : ((K ∙ F.e) ⊔ (K ∙ F.f)) ⊓ (K ∙ (g • x)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvA, hvB⟩ := Submodule.mem_inf.mp hv
    by_contra hv0
    have hvspan : K ∙ v = K ∙ (g • x) :=
      (eq_span_singleton_of_mem_of_finrank_eq_one (S := K ∙ (g • x)) (w := v)
        hfinW hvB hv0).symm
    have hle : K ∙ v ≤ (K ∙ F.e) ⊔ (K ∙ F.f) := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hvA
    have hmemv : g • x ∈ K ∙ v := by
      rw [hvspan]
      exact Submodule.mem_span_singleton_self (g • x)
    exact hgx (hle hmemv)
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq ((K ∙ F.e) ⊔ (K ∙ F.f)) (K ∙ (g • x))
  rw [hdisj, hA, hfinW, finrank_bot] at h
  rw [Module.finrank_fin_fun]
  omega

private theorem isotropicTransvectionGroup_span_le_stabilizer {h : UnitaryFieldData 2 n K}
    (F : SU3TorusFrame h T) {x : Fin 3 → K} (hxorth : stdHermForm h 3 x F.v = 0)
    (hLx : K ∙ x ∈ isotropicLines h 3) :
    isotropicTransvectionGroup h 3 (K ∙ x) ≤
      MulAction.stabilizer (unitarySU 2 n K 3) F.v := by
  intro u hu
  rw [MulAction.mem_stabilizer_iff]
  by_cases hu1 : u = 1
  · rw [hu1, one_smul]
  · have hker := ker_subOne_of_mem_isotropicTransvectionGroup hLx hu hu1
    have hv : F.v ∈ hermPerp h (K ∙ x) := by
      rw [mem_hermPerp]
      intro a ha
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [LinearMap.map_smulₛₗ₂, hxorth, smul_zero]
    have hmem : F.v ∈ LinearMap.ker (subOne u) := by rw [hker]; exact hv
    rw [LinearMap.mem_ker, subOne_apply h] at hmem
    exact sub_eq_zero.mp hmem

private theorem isotropicTransvectionGroup_span_smul_le {h : UnitaryFieldData 2 n K}
    (F : SU3TorusFrame h T) (hL : MulAction.stabilizer (unitarySU 2 n K 3) F.v ≤ H)
    {g : unitarySU 2 n K 3} {x : Fin 3 → K} (hgH : g ∈ H)
    (hxorth : stdHermForm h 3 x F.v = 0) (hLx : K ∙ (g • x) ∈ isotropicLines h 3) :
    isotropicTransvectionGroup h 3 (K ∙ (g • x)) ≤ H := by
  intro u hu
  have hgu : g⁻¹ * u * g ∈ H := by
    apply hL
    rw [MulAction.mem_stabilizer_iff]
    by_cases hu1 : u = 1
    · rw [hu1]
      simp
    · have hker := ker_subOne_of_mem_isotropicTransvectionGroup hLx hu hu1
      have hwv : g • F.v ∈ hermPerp h (K ∙ (g • x)) := by
        rw [mem_hermPerp]
        intro a ha
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
        calc stdHermForm h 3 (c • (g • x)) (g • F.v)
            = h.bar c * stdHermForm h 3 (g • x) (g • F.v) := by
              rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
          _ = h.bar c * stdHermForm h 3 x F.v := by rw [stdHermForm_smul_smul]
          _ = 0 := by rw [hxorth, mul_zero]
      have hmem : g • F.v ∈ LinearMap.ker (subOne u) := by rw [hker]; exact hwv
      rw [LinearMap.mem_ker, subOne_apply h] at hmem
      have hfix : u • (g • F.v) = g • F.v := sub_eq_zero.mp hmem
      calc (g⁻¹ * u * g) • F.v = g⁻¹ • (u • (g • F.v)) := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • F.v) := by rw [hfix]
        _ = F.v := by rw [inv_smul_smul]
  have hu_eq : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
  rw [hu_eq]
  exact H.mul_mem (H.mul_mem hgH hgu) (H.inv_mem hgH)

theorem eq_top_of_stabilizer_le {h : UnitaryFieldData 2 n K} (hn : 2 ≤ n)
    (F : SU3TorusFrame h T) (hL : MulAction.stabilizer (unitarySU 2 n K 3) F.v ≤ H)
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ g ∈ H, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    H = ⊤ := by
  obtain ⟨g, hgH, hgv⟩ := exists_smul_v_not_mem_span F hirr
  obtain ⟨x, hx, hgx⟩ := exists_smul_line_not_mem_sup F hgv
  have hx12 : x = F.e ∨ x = F.f := by simpa using hx
  have he0 := F.e_ne_zero
  have hf0 := F.f_ne_zero
  have hx0 : x ≠ 0 := by
    rcases hx12 with rfl | rfl
    · exact he0
    · exact hf0
  have hxorth : stdHermForm h 3 x F.v = 0 := by
    rcases hx12 with rfl | rfl
    · exact F.stdHermForm_e_v
    · exact F.stdHermForm_f_v
  have hxself : stdHermForm h 3 x x = 0 := by
    rcases hx12 with rfl | rfl
    · exact F.stdHermForm_e_e
    · exact F.stdHermForm_f_f
  have hw0 : g • x ≠ 0 := (smul_ne_zero_iff_ne g).2 hx0
  have hwself : stdHermForm h 3 (g • x) (g • x) = 0 := by
    rw [stdHermForm_smul_smul h g x x]
    exact hxself
  have hLe : K ∙ F.e ∈ isotropicLines h 3 :=
    span_singleton_mem_isotropicLines h he0 F.stdHermForm_e_e
  have hLf : K ∙ F.f ∈ isotropicLines h 3 :=
    span_singleton_mem_isotropicLines h hf0 F.stdHermForm_f_f
  have hLw : K ∙ (g • x) ∈ isotropicLines h 3 :=
    span_singleton_mem_isotropicLines h hw0 hwself
  have hT1 : isotropicTransvectionGroup h 3 (K ∙ F.e) ≤ H :=
    (isotropicTransvectionGroup_span_le_stabilizer F F.stdHermForm_e_v hLe).trans hL
  have hT2 : isotropicTransvectionGroup h 3 (K ∙ F.f) ≤ H :=
    (isotropicTransvectionGroup_span_le_stabilizer F F.stdHermForm_f_v hLf).trans hL
  have hT3 : isotropicTransvectionGroup h 3 (K ∙ (g • x)) ≤ H :=
    isotropicTransvectionGroup_span_smul_le F hL hgH hxorth hLw
  have hspan := sup_three_lines_eq_top F hx12 hgx
  have hsup := sup_three_isotropicTransvectionGroup_eq_top h hn hLe hLf hLw hspan
  rw [eq_top_iff]
  calc ⊤ = isotropicTransvectionGroup h 3 (K ∙ F.e) ⊔
        isotropicTransvectionGroup h 3 (K ∙ F.f) ⊔
        isotropicTransvectionGroup h 3 (K ∙ (g • x)) := hsup.symm
    _ ≤ H := sup_le (sup_le hT1 hT2) hT3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrred
