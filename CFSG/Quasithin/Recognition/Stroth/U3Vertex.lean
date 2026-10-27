module

public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Alt2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F1
  CFSG.LieType.Universal.Unitary
open scoped commutatorElement

private theorem ne_three_two_of_two_le {k : ℕ} (hk : 2 ≤ k) : ((3 : ℕ), 2 ^ k) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ k = 2 := (Prod.mk.inj h).2
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem le_sup_pCoreOf_of_map_eq_top {G : Type} [Group G] {L N : Subgroup G}
    (h : (N.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) = ⊤) :
    L ≤ N ⊔ pCoreOf 2 L := by
  intro x hx
  have hmem : (QuotientGroup.mk' (pCore 2 ↥L) (⟨x, hx⟩ : ↥L) : oTwoQuot ↥L) ∈
      (N.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hmem
  have h1 : (n⁻¹ * ⟨x, hx⟩ : ↥L) ∈ pCore 2 ↥L := by
    have h0 : (QuotientGroup.mk (s := pCore 2 ↥L) (n⁻¹ * ⟨x, hx⟩) : oTwoQuot ↥L) = 1 := by
      change (QuotientGroup.mk' (pCore 2 ↥L) (n⁻¹ * ⟨x, hx⟩) : oTwoQuot ↥L) = 1
      rw [map_mul, map_inv, hnx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (n⁻¹ * ⟨x, hx⟩)).mp h0
  have hx' : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by
    simp
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hn) (Subgroup.mem_map_of_mem _ h1)

private theorem conj_mem_inf_of_le_normalizer {G : Type} [Group G] {L K : Subgroup G}
    (hKL : K ≤ Subgroup.normalizer (L : Set G))
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) {t : G} (ht : t ∈ K) {l : G} (hl : l ∈ L) :
    l⁻¹ * t * l * t⁻¹ ∈ L ⊓ K := by
  have hcL : t * l * t⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKL ht) l).mp hl) (L.inv_mem hl)
  have hcK : t * l * t⁻¹ * l⁻¹ ∈ K := by
    have h1 : l * t⁻¹ * l⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hLK hl) t⁻¹).mp (K.inv_mem ht)
    simpa [mul_assoc] using K.mul_mem ht h1
  have hcN : t * l * t⁻¹ * l⁻¹ ∈ L ⊓ K := ⟨hcL, hcK⟩
  have hN : ((L ⊓ K).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (le_normalizer_inf_of_le hLK)
  have hconj := hN.conj_mem ⟨t * l * t⁻¹ * l⁻¹, hcL⟩ (by exact hcN) ⟨l⁻¹, L.inv_mem hl⟩
  have hmem : l⁻¹ * (t * l * t⁻¹ * l⁻¹) * l ∈ L ⊓ K := by
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  have heq : l⁻¹ * (t * l * t⁻¹ * l⁻¹) * l = l⁻¹ * t * l * t⁻¹ := by group
  rwa [heq] at hmem

private theorem isPerfect_statedProj_statedSU_three {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2) :
    Group.IsPerfect (StatedProj (StatedSU 3 (2 ^ k) F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect (StatedSU 3 (2 ^ k) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) (by norm_num)
      (ne_three_two_of_two_le hk)
  exact Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F)))
    (QuotientGroup.mk'_surjective _)

private theorem isQuasisimple_statedProj_statedSU_three {k : ℕ} (hk : 2 ≤ k) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2) :
    CFSG.IsQuasisimple (StatedProj (StatedSU 3 (2 ^ k) F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 k hF 3 le_rfl
      (ne_three_two_of_two_le hk)
  haveI : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) := hsimple
  haveI : Group.IsPerfect (StatedProj (StatedSU 3 (2 ^ k) F)) :=
    isPerfect_statedProj_statedSU_three hk hF
  have hna : ∃ a b : StatedProj (StatedSU 3 (2 ^ k) F), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨h⟩⟩
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1

private theorem index_normalizer_mk'_eq_of_central_odd {A : Type*} [Group A] [Finite A]
    {Z : Subgroup A} [Z.Normal] (hZ : Z ≤ Subgroup.center A) (hZodd : Odd (Nat.card Z))
    {T : Subgroup A} (hT : IsPGroup 2 T) :
    (Subgroup.normalizer (T : Set A)).index =
      (Subgroup.normalizer (((T.map (QuotientGroup.mk' Z)) :
        Subgroup (A ⧸ Z)) : Set (A ⧸ Z))).index := by
  have hcop : Nat.Coprime (Nat.card Z) 2 := (Nat.coprime_two_left.mpr hZodd).symm
  rw [CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map Z hZ hcop hT,
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)]

private theorem map_inf_subgroupOf_le_center {G : Type} [Group G] [Finite G]
    {L K : Subgroup G} (hq : CFSG.IsQuasisimple (oTwoQuot ↥L))
    (hKL : K ≤ Subgroup.normalizer (L : Set G))
    (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (hprop : (L ⊓ K) ⊔ pCoreOf 2 L < L) :
    (((L ⊓ K).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))) ≤
      Subgroup.center (oTwoQuot ↥L) := by
  classical
  have hNnormal : ((L ⊓ K).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (le_normalizer_inf_of_le hLK)
  have hmapNormal : (((L ⊓ K).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 ↥L))).Normal :=
    hNnormal.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hmapNormal with htop | hcen
  · exfalso
    have hle : L ≤ (L ⊓ K) ⊔ pCoreOf 2 L :=
      le_sup_pCoreOf_of_map_eq_top (L := L) (N := L ⊓ K) (by simpa using htop)
    exact (ne_of_lt hprop) (le_antisymm hprop.le hle)
  · exact hcen

theorem isQuasisimple_oTwoQuot_of_u3 {L : Type} [Group L] [Finite L] {k : ℕ} (hk : 2 ≤ k)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot L ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot L ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    CFSG.IsQuasisimple (oTwoQuot L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hU3 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (isQuasisimple_statedSU_of_card (p := 2) (f := k) (n := 3) hF (by norm_num)
        (ne_three_two_of_two_le hk)).1
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (isQuasisimple_statedProj_statedSU_three hk hF)

theorem comm_mem_pCoreOf_of_isQuasisimple {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    (hq : CFSG.IsQuasisimple (oTwoQuot ↥L))
    (hKL : K ≤ Subgroup.normalizer (L : Set G))
    (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (hprop : (L ⊓ K) ⊔ pCoreOf 2 L < L) :
    ∀ t ∈ K, ∀ l ∈ L, l * t * l⁻¹ * t⁻¹ ∈ pCoreOf 2 L := by
  classical
  intro t ht l hl
  have hcenter := map_inf_subgroupOf_le_center hq hKL hLK hprop
  have hα : CFSG.GroupTheory.conjModPCore 2 L K hKL ⟨t, ht⟩ = 1 := by
    refine CFSG.Quasithin.L3Aut.eq_one_of_central_quotient hq.1.commutator_eq_top _ ?_
    intro x
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective x
    have hu : l'⁻¹ * t * l' * t⁻¹ ∈ L ⊓ K :=
      conj_mem_inf_of_le_normalizer hKL hLK ht l'.2
    have hmem : (QuotientGroup.mk' (pCore 2 ↥L) (⟨l'⁻¹ * t * l' * t⁻¹, hu.1⟩ : ↥L)) ∈
        ((L ⊓ K).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) :=
      Subgroup.mem_map.mpr ⟨⟨_, hu.1⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have hc : (QuotientGroup.mk' (pCore 2 ↥L) (⟨l'⁻¹ * t * l' * t⁻¹, hu.1⟩ : ↥L)) ∈
        Subgroup.center (oTwoQuot ↥L) := hcenter hmem
    have hEq : (QuotientGroup.mk l')⁻¹ *
        CFSG.GroupTheory.conjModPCore 2 L K hKL ⟨t, ht⟩ (QuotientGroup.mk l') =
        QuotientGroup.mk' (pCore 2 ↥L) (⟨l'⁻¹ * t * l' * t⁻¹, hu.1⟩ : ↥L) := by
      rw [CFSG.GroupTheory.conjModPCore_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
    rw [hEq]
    exact hc
  have htker : (⟨t, ht⟩ : ↥K) ∈ (CFSG.GroupTheory.conjModPCore 2 L K hKL).ker := by
    rw [MonoidHom.mem_ker]
    exact hα
  have htmap : t ∈ (CFSG.GroupTheory.conjModPCore 2 L K hKL).ker.map K.subtype :=
    Subgroup.mem_map.mpr ⟨⟨t, ht⟩, htker, rfl⟩
  have hcomm := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L K hKL).mp htmap |>.2
  have hgoal : t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 L := hcomm l hl
  simpa [mul_assoc] using (pCoreOf 2 L).inv_mem hgoal

theorem mem_borelOf_of_mk_mem_center {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L) L) {l : ↥L}
    (hl : QuotientGroup.mk' (pCore 2 ↥L) l ∈ Subgroup.center (oTwoQuot ↥L)) :
    (l : G) ∈ borelOf L S := by
  classical
  obtain ⟨-, -, hmap⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  set Tb : Subgroup (oTwoQuot ↥L) := ((S ⊓ L).subgroupOf L).map π with hTb
  have hmap' : ((borelOf L S).subgroupOf L).map π =
      Subgroup.normalizer (Tb : Set (oTwoQuot ↥L)) := by
    simpa [hπ, hTb] using hmap
  have hnorm : π l ∈ Subgroup.normalizer (Tb : Set (oTwoQuot ↥L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc : π l * x = x * π l := (Subgroup.mem_center_iff.mp hl x).symm
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have hc : π l * x = x * π l := (Subgroup.mem_center_iff.mp hl x).symm
      rw [hc, mul_assoc, mul_inv_cancel, mul_one] at hx
      exact hx
  have hmem : π l ∈ ((borelOf L S).subgroupOf L).map π := by
    rw [hmap']
    exact hnorm
  obtain ⟨b, hb, hbl⟩ := Subgroup.mem_map.mp hmem
  have hpc : pCore 2 ↥L ≤ (borelOf L S).subgroupOf L := by
    intro x hx
    exact sylow_le_borelOf L S
      (isSylowTwoOf_pCoreOf_le hsyl ((mem_pCore_iff_coe x).mp hx))
  have hsub : b⁻¹ * l ∈ (borelOf L S).subgroupOf L := by
    apply hpc
    have h0 : (QuotientGroup.mk (s := pCore 2 ↥L) (b⁻¹ * l) : oTwoQuot ↥L) = 1 := by
      change (QuotientGroup.mk' (pCore 2 ↥L) (b⁻¹ * l) : oTwoQuot ↥L) = 1
      rw [map_mul, map_inv, hbl, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (b⁻¹ * l)).mp h0
  have hbB : (b : G) ∈ borelOf L S := Subgroup.mem_subgroupOf.mp hb
  have hsubB : ((b⁻¹ * l : ↥L) : G) ∈ borelOf L S := Subgroup.mem_subgroupOf.mp hsub
  have heq : (l : G) = (b : G) * ((b⁻¹ * l : ↥L) : G) := by simp
  rw [heq]
  exact (borelOf L S).mul_mem hbB hsubB

theorem index_borelOf_of_u3 {G : Type} [Group G] [Finite G] {L S : Subgroup G} {k : ℕ}
    (hk : 2 ≤ k) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hU3 : Nonempty (oTwoQuot ↥L ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    ((borelOf L S).subgroupOf L).index = (2 ^ k) ^ 3 + 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq := ne_three_two_of_two_le hk
  have hSCM : StatedClassicalModel (StatedProj (StatedSU 3 (2 ^ k) F)) .PSU 3 2 k :=
    ⟨⟨Nat.prime_two, by omega, by norm_num, hnq⟩, F, inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hp, hodd, hmap⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ (borelOf L S).subgroupOf L := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (mem_pCore_iff_coe x).mp hx
    exact sylow_le_borelOf L S (isSylowTwoOf_pCoreOf_le hsyl h1)
  rw [← Subgroup.index_map_eq _ hsurj hker, hmap]
  set Tb : Subgroup (oTwoQuot ↥L) := Subgroup.map π ((S ⊓ L).subgroupOf L) with hTb
  rcases hU3 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    let ZA : Subgroup (StatedSU 3 (2 ^ k) F) :=
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F)
    set T' : Subgroup (StatedSU 3 (2 ^ k) F) := Tb.map e.toMonoidHom with hT'
    have hp' : IsPGroup 2 T' := hp.map e.toMonoidHom
    have hodd' : ¬ 2 ∣ T'.index := by
      rw [hT', show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl,
        Subgroup.index_map_equiv]
      exact hodd
    have hZAc : ZA ≤ Subgroup.center (StatedSU 3 (2 ^ k) F) :=
      (isQuasisimple_statedSU_of_card (p := 2) (f := k) (n := 3) hF (by norm_num) hnq).2.ge
    have hZAodd : Odd (Nat.card ZA) := by
      have hcard : Nat.card ZA = Nat.gcd 3 ((2 ^ k) + 1) :=
        (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 3) (by norm_num)).2.2
      rw [hcard]
      exact Odd.of_dvd_nat (by norm_num : Odd 3) (Nat.gcd_dvd_left _ _)
    have hQodd : ¬ 2 ∣ (T'.map (QuotientGroup.mk' ZA)).index := fun h2 =>
      hodd' (h2.trans (Subgroup.index_map_dvd (H := T') (QuotientGroup.mk'_surjective ZA)))
    let P : Sylow 2 (StatedProj (StatedSU 3 (2 ^ k) F)) := (hp'.map _).toSylow hQodd
    have hcard : (Subgroup.normalizer (T'.map (QuotientGroup.mk' ZA) :
        Set (StatedProj (StatedSU 3 (2 ^ k) F)))).index = (2 ^ k) ^ 3 + 1 := by
      refine (Sylow.card_eq_index_normalizer P).symm.trans ?_
      rw [CFSG.CGT.Timmesfeld75.card_sylow_psu3 hSCM, ← pow_mul, Nat.mul_comm 3 k]
    have h5 : (Subgroup.normalizer (T' : Set (StatedSU 3 (2 ^ k) F))).index =
        (2 ^ k) ^ 3 + 1 := by
      rw [index_normalizer_mk'_eq_of_central_odd hZAc hZAodd hp']
      exact hcard
    rw [← Subgroup.map_normalizer_eq_of_bijective Tb e.bijective,
      show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv] at h5
    exact h5
  ·
    set T' : Subgroup (StatedProj (StatedSU 3 (2 ^ k) F)) := Tb.map e.toMonoidHom with hT'
    have hp' : IsPGroup 2 T' := hp.map e.toMonoidHom
    have hodd' : ¬ 2 ∣ T'.index := by
      rw [hT', show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl,
        Subgroup.index_map_equiv]
      exact hodd
    let P : Sylow 2 (StatedProj (StatedSU 3 (2 ^ k) F)) := hp'.toSylow hodd'
    have h5 : (Subgroup.normalizer (T' : Set (StatedProj (StatedSU 3 (2 ^ k) F)))).index =
        (2 ^ k) ^ 3 + 1 := by
      refine (Sylow.card_eq_index_normalizer P).symm.trans ?_
      rw [CFSG.CGT.Timmesfeld75.card_sylow_psu3 hSCM, ← pow_mul, Nat.mul_comm 3 k]
    rw [← Subgroup.map_normalizer_eq_of_bijective Tb e.bijective,
      show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv] at h5
    exact h5

theorem nonempty_quotient_equiv_psu3 {G : Type} [Group G] [Finite G] {L N : Subgroup G}
    {k : ℕ} (hk : 2 ≤ k) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hNL : N ≤ L) (hN : (N.subgroupOf L).Normal) (hON : pCoreOf 2 L ≤ N) (hNlt : N < L)
    (hZN : ∀ l : ↥L, QuotientGroup.mk' (pCore 2 ↥L) l ∈ Subgroup.center (oTwoQuot ↥L) →
      (l : G) ∈ N) :
    Nonempty (↥L ⧸ N.subgroupOf L ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq := ne_three_two_of_two_le hk
  haveI : (N.subgroupOf L).Normal := hN
  have hq := isQuasisimple_oTwoQuot_of_u3 hk hF hU3
  have hprop : (L ⊓ N) ⊔ pCoreOf 2 L < L := by
    rwa [inf_eq_right.mpr hNL, sup_eq_left.mpr hON]
  have hKL : N ≤ Subgroup.normalizer (L : Set G) := hNL.trans Subgroup.le_normalizer
  have hLK : L ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hN
  have hNbarLeZ : (N.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) ≤
      Subgroup.center (oTwoQuot ↥L) := by
    have h := map_inf_subgroupOf_le_center hq hKL hLK hprop
    rwa [inf_eq_right.mpr hNL] at h
  have hZleNbar : Subgroup.center (oTwoQuot ↥L) ≤
      (N.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) := by
    intro z hz
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr (hZN l hz), rfl⟩
  have hNbarEq : (N.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) =
      Subgroup.center (oTwoQuot ↥L) := le_antisymm hNbarLeZ hZleNbar
  have hpc_le : pCore 2 ↥L ≤ N.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hON (Subgroup.mem_map_of_mem _ hx)
  let eL : oTwoQuot ↥L ⧸ (N.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) ≃*
      ↥L ⧸ N.subgroupOf L :=
    QuotientGroup.quotientQuotientEquivQuotient (pCore 2 ↥L) (N.subgroupOf L) hpc_le
  have hbase : Nonempty (oTwoQuot ↥L ⧸ (N.subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 ↥L)) ≃* StatedProj (StatedSU 3 (2 ^ k) F)) := by
    rcases hU3 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    ·
      let ZA : Subgroup (StatedSU 3 (2 ^ k) F) :=
        (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ k) F)
      have hcenterSU : Subgroup.center (StatedSU 3 (2 ^ k) F) = ZA :=
        (isQuasisimple_statedSU_of_card (p := 2) (f := k) (n := 3) hF (by norm_num) hnq).2
      have eZ : oTwoQuot ↥L ⧸ Subgroup.center (oTwoQuot ↥L) ≃*
          StatedSU 3 (2 ^ k) F ⧸ Subgroup.center (StatedSU 3 (2 ^ k) F) :=
        QuotientGroup.congr (Subgroup.center (oTwoQuot ↥L))
          (Subgroup.center (StatedSU 3 (2 ^ k) F)) e
          (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hNbarEq).trans
        (eZ.trans (QuotientGroup.quotientMulEquivOfEq hcenterSU))⟩
    ·
      have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) :=
        CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 k hF 3 le_rfl hnq
      haveI : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ k) F)) := hsimple
      haveI : Group.IsPerfect (StatedProj (StatedSU 3 (2 ^ k) F)) :=
        isPerfect_statedProj_statedSU_three hk hF
      have hna : ∃ a b : StatedProj (StatedSU 3 (2 ^ k) F), a * b ≠ b * a := by
        by_contra h
        push Not at h
        exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨h⟩⟩
      have hcenterP : Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F)) = ⊥ :=
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).2
      have hZbot : Subgroup.center (oTwoQuot ↥L) = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have h1 : e z ∈ Subgroup.center (StatedProj (StatedSU 3 (2 ^ k) F)) := by
          rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv e]
          exact Subgroup.mem_map_of_mem _ hz
        rw [hcenterP, Subgroup.mem_bot] at h1
        exact e.injective (by simpa using h1)
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hNbarEq).trans
        ((QuotientGroup.quotientMulEquivOfEq hZbot).trans
          (QuotientGroup.quotientBot.trans e))⟩
  obtain ⟨eX⟩ := hbase
  exact ⟨eL.symm.trans eX⟩

end CFSG.Quasithin.Stroth
