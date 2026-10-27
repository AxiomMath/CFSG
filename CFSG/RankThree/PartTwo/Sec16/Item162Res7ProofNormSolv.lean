module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res6ProofHJ
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree.PartTwo

namespace Res162Seven

section Model

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.Fischer CFSG.RankThree.Asc83Table

theorem mulCode4_lt : ∀ a < 4, ∀ b < 4, mulCode4 a b < 4 := by
  decide

theorem card_mulCode4_eq_zero :
    Nat.card {p : F4 × F4 × F4 // mulCode4 (p.1.code : ℕ) (p.2.1.code : ℕ) = 0 ∧
      ¬ ((p.1.code : ℕ) = 0 ∧ (p.2.1.code : ℕ) = 0 ∧ (p.2.2.code : ℕ) = 0)} = 27 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_mulCode4_ne_zero :
    Nat.card {p : F4 × F4 × F4 // mulCode4 (p.1.code : ℕ) (p.2.1.code : ℕ) ≠ 0} = 36 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem phiE_sq {a b c : ℕ}
    (ha : a < 4) (hb : b < 4) (hc : c < 4) : phiE a b c ^ 2 = phiE 0 0 (mulCode4 a b) := by
  rw [pow_two, phiE_mul ha hb hc ha hb hc, Nat.xor_self, Nat.xor_self, Nat.xor_self,
    Nat.zero_xor]

theorem phiE_eq_one_iff
    {a b c : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4) :
    phiE a b c = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [← phiE_zero] at h
    exact phiE_injective ha hb hc (by norm_num) (by norm_num) (by norm_num) h
  · rintro ⟨rfl, rfl, rfl⟩
    exact phiE_zero

theorem phiS_eq_one_iff
    (p : F4 × F4 × F4) : phiS p = 1 ↔
      (p.1.code : ℕ) = 0 ∧ (p.2.1.code : ℕ) = 0 ∧ (p.2.2.code : ℕ) = 0 := by
  rw [← Subtype.val_inj, Subgroup.coe_one]
  exact phiE_eq_one_iff p.1.code.2 p.2.1.code.2 p.2.2.code.2

theorem phiS_sq_eq_one_iff
    (p : F4 × F4 × F4) : phiS p ^ 2 = 1 ↔ mulCode4 (p.1.code : ℕ) (p.2.1.code : ℕ) = 0 := by
  rw [← Subtype.val_inj, Subgroup.coe_pow, Subgroup.coe_one]
  change phiE p.1.code p.2.1.code p.2.2.code ^ 2 = 1 ↔ _
  rw [phiE_sq p.1.code.2 p.2.1.code.2 p.2.2.code.2,
    phiE_eq_one_iff (by norm_num) (by norm_num) (mulCode4_lt _ p.1.code.2 _ p.2.1.code.2)]
  simp

theorem card_inv_S0 :
    Nat.card {s : SJ 0 // s ^ 2 = 1 ∧ s ≠ 1} = 27 := by
  rw [← card_mulCode4_eq_zero]
  refine (Nat.card_congr (phiEquiv.subtypeEquiv fun p => ?_)).symm
  change _ ↔ phiS p ^ 2 = 1 ∧ phiS p ≠ 1
  rw [phiS_sq_eq_one_iff, ne_eq, phiS_eq_one_iff]

theorem card_four_S0 :
    Nat.card {s : SJ 0 // s ^ 2 ≠ 1} = 36 := by
  rw [← card_mulCode4_ne_zero]
  refine (Nat.card_congr (phiEquiv.subtypeEquiv fun p => ?_)).symm
  change _ ↔ phiS p ^ 2 ≠ 1
  simp only [ne_eq]
  rw [phiS_sq_eq_one_iff]

theorem pow_four_S0 (s : SJ 0) :
    s ^ 4 = 1 := by
  obtain ⟨p, rfl⟩ := phiEquiv.surjective s
  rw [← Subtype.val_inj, Subgroup.coe_pow, Subgroup.coe_one]
  change phiE p.1.code p.2.1.code p.2.2.code ^ 4 = 1
  have hm := mulCode4_lt _ p.1.code.2 _ p.2.1.code.2
  have e4 : ∀ g : GJ, g ^ 4 = (g ^ 2) ^ 2 := fun g => by rw [← pow_mul]
  rw [e4, phiE_sq p.1.code.2 p.2.1.code.2 p.2.2.code.2, phiE_sq (by norm_num) (by norm_num) hm,
    phiE_eq_one_iff (by norm_num) (by norm_num) (mulCode4_lt _ (by norm_num) _ (by norm_num))]
  decide

end Model

theorem nonempty_mulEquiv_S0
    {X : Type} [Group X]
    [Finite X] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup X}
    (hE9 : Nat.card E = 9) {S : Subgroup X} (hS : S ∈ maxInvariantPiSubgroups ⊤ E (piOf 2)) :
    Nonempty (S ≃* Sec4.Sporadic.J2.SJ 0) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  obtain ⟨-, -, -, -, h5⟩ := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  obtain ⟨S₀, -, hset, -, ⟨T, ⟨eT⟩⟩, -⟩ := h5 E ⟨hEP, hE9⟩
  rw [hset] at hS
  obtain ⟨p, -, rfl⟩ := hS
  obtain ⟨T', ⟨eT'⟩⟩ := Sec4.Sporadic.J2.exists_sylow_equiv
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 2)) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  exact ⟨((S₀.equivMapOfInjective _ (MulAut.conj p⁻¹).injective).symm.trans eT).trans
    ((Sylow.equiv T T').trans eT'.symm)⟩

section Perm

open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel
  CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.M12Cover (centralizerInConjEquiv conjClass_conj)

theorem exists_conj_of_orderOf_two
    {t : Equiv.Perm (Fin 315)} (htP : t ∈ P) (ht : orderOf t = 2) :
    ∃ r ∈ [permA, permTwoA], ∃ c ∈ P, t = c * r * c⁻¹ := by
  obtain ⟨-, -, hcl, -⟩ :=
    ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups
  obtain ⟨r, hr, c, hc, htr⟩ := hcl t (P_le_R htP) ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨permA, by simp, c, hc, htr⟩
  · exact ⟨permTwoA, by simp, c, hc, htr⟩
  · exfalso
    apply permU_not_mem
    have e : permU = c⁻¹ * t * c := by rw [htr]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hc) htP) hc

theorem card_centralizerIn_of_orderOf_two
    {t : Equiv.Perm (Fin 315)} (htP : t ∈ P) (ht : orderOf t = 2) :
    Nat.card (centralizerIn P t) = 240 ∨ Nat.card (centralizerIn P t) = 1920 := by
  obtain ⟨r, hr, c, hc, rfl⟩ := exists_conj_of_orderOf_two htP ht
  rw [← Nat.card_congr (centralizerInConjEquiv P hc r).toEquiv]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl centralizerIn_P_permA.2.1
  · exact Or.inr centralizerIn_P_permTwoA.2.1

theorem not_five_dvd_card_centralizerIn_of_four
    {x : Equiv.Perm (Fin 315)} (hxP : x ∈ P) (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) :
    ¬ 5 ∣ Nat.card (centralizerIn P x) := by
  classical
  have ht : orderOf (x ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact h4) h2
  obtain ⟨r, hr, c, hc, htr⟩ := exists_conj_of_orderOf_two (pow_mem hxP 2) ht
  set y := MulAut.conj c⁻¹ x with hy
  have hxy : x = c * y * c⁻¹ := by
    rw [hy, MulAut.conj_apply]
    group
  have hyP : y ∈ P := by
    rw [hy, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hc) hxP) hc
  have hy2 : y ^ 2 = r := by
    rw [hy, ← map_pow, htr, MulAut.conj_apply]
    group
  have hy4 : orderOf y = 4 := by
    refine CFSG.ComponentClassification.M12Cover.orderOf_eq_four ?_ ?_
    · rw [hy, ← map_pow, h4, map_one]
    · rw [hy, ← map_pow]
      intro h1
      exact h2 ((MulAut.conj c⁻¹).injective (h1.trans (map_one _).symm))
  set K := centralizerIn P r with hK
  have hyK : y ∈ K := by
    rw [hK, mem_centralizerIn]
    refine ⟨hyP, ?_⟩
    rw [← hy2, pow_two]
    group
  have hCy : centralizerIn P y = centralizerIn K y := by
    ext z
    simp only [hK, mem_centralizerIn]
    constructor
    · rintro ⟨hzP, hzy⟩
      refine ⟨⟨hzP, ?_⟩, hzy⟩
      rw [← hy2, pow_two]
      calc z * (y * y) = z * y * y := by group
        _ = y * z * y := by rw [hzy]
        _ = y * (z * y) := by group
        _ = y * (y * z) := by rw [hzy]
        _ = y * y * z := by group
    · rintro ⟨⟨hzP, -⟩, hzy⟩
      exact ⟨hzP, hzy⟩
  have hcard : Nat.card (centralizerIn P x) = Nat.card (centralizerIn P y) := by
    rw [hxy]
    exact (Nat.card_congr (centralizerInConjEquiv P hc y).toEquiv).symm
  rw [hcard, hCy]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    exfalso
    obtain ⟨reps, -, hcov, -, hmap⟩ := centralizerIn_P_permA.2.2
    have hnil : reps = [] := List.map_eq_nil_iff.mp hmap
    obtain ⟨r', hr', -⟩ := hcov y hyK hy4
    rw [hnil] at hr'
    simp at hr'
  ·
    obtain ⟨-, hKcard, reps, -, hcov, -, hmap⟩ := centralizerIn_P_permTwoA
    obtain ⟨r', hr', d, hd, hyr'⟩ := hcov y hyK hy4
    have hcl : conjClass K y = conjClass K r' := by
      rw [hyr']
      exact conjClass_conj K hd r'
    have hsz : (conjClass K r').ncard = 20 ∨ (conjClass K r').ncard = 120 := by
      have hm : (conjClass K r').ncard ∈ reps.map (fun r => (conjClass K r).ncard) :=
        List.mem_map_of_mem hr'
      rw [hmap] at hm
      simpa using hm
    have hos := ncard_conjClass_mul_card K y
    rw [hcl, hKcard] at hos
    rcases hsz with h | h <;> rw [h] at hos <;> omega

theorem card_centralizer_eq_centralizerIn {X : Type} [Group X] (e : X ≃* ↥P) (x : X) :
    Nat.card (Subgroup.centralizer ({x} : Set X)) =
      Nat.card (centralizerIn P ((e x : ↥P) : Equiv.Perm (Fin 315))) :=
  (Nat.card_congr (CFSG.ComponentClassification.M12Cover.centralizerEquiv e x).toEquiv).trans
    (Nat.card_congr (CFSG.ComponentClassification.M12Cover.centralizerSubgroupEquiv P
      (e x)).toEquiv)

theorem not_seven_dvd_card_centralizer_of_j2
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {t : X} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t} : Set X)) := by
  obtain ⟨φ⟩ := hX
  set e : X ≃* ↥P := φ.trans nativeEquivP with he
  have hord : orderOf ((e t : ↥P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ht2 ht1
  rw [card_centralizer_eq_centralizerIn e t]
  rcases card_centralizerIn_of_orderOf_two (e t).2 hord with h | h <;> rw [h] <;> norm_num

theorem not_five_dvd_card_centralizer_of_j2
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {x : X} (h4 : x ^ 4 = 1)
    (h2 : x ^ 2 ≠ 1) : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨φ⟩ := hX
  set e : X ≃* ↥P := φ.trans nativeEquivP with he
  rw [card_centralizer_eq_centralizerIn e x]
  refine not_five_dvd_card_centralizerIn_of_four (e x).2 ?_ ?_
  · rw [← Subgroup.coe_pow, ← map_pow, h4, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ← map_pow]
    intro h1
    exact h2 (e.injective (Subtype.ext (h1.trans (by rw [map_one, Subgroup.coe_one]))))

end Perm

theorem exists_commute_of_not_dvd {X : Type} [Group X] [Finite X] {S : Subgroup X} {g : X}
    {p : ℕ} [Fact p.Prime] (hgp : orderOf g = p) (hgS : g ∈ Subgroup.normalizer (S : Set X))
    (Q : X → Prop) (hQ : ∀ y x : X, Q x → Q (y * x * y⁻¹))
    (hcard : ¬ p ∣ Nat.card {x : X // x ∈ S ∧ Q x}) : ∃ x ∈ S, Q x ∧ g * x = x * g := by
  classical
  set H := Subgroup.zpowers g with hH
  have hHS : H ≤ Subgroup.normalizer (S : Set X) := Subgroup.zpowers_le.mpr hgS
  set Y := {x : X // x ∈ S ∧ Q x} with hYdef
  have hact : ∀ (h : H) (y : Y), (h : X) * y.1 * (h : X)⁻¹ ∈ S ∧ Q ((h : X) * y.1 * (h : X)⁻¹) :=
    fun h y => ⟨(Subgroup.mem_normalizer_iff.mp (hHS h.2) y.1).mp y.2.1, hQ _ _ y.2.2⟩
  let _ : MulAction H Y :=
    { smul := fun h y => ⟨(h : X) * y.1 * (h : X)⁻¹, hact h y⟩
      one_smul := fun y => by
        apply Subtype.ext
        change (1 : X) * y.1 * (1 : X)⁻¹ = y.1
        group
      mul_smul := fun h k y => by
        apply Subtype.ext
        change ((h : X) * k) * y.1 * ((h : X) * k)⁻¹ =
          (h : X) * ((k : X) * y.1 * (k : X)⁻¹) * (h : X)⁻¹
        group }
  have hHp : IsPGroup p H := IsPGroup.of_card (n := 1) (by rw [hH, Nat.card_zpowers, hgp, pow_one])
  have hfinY : Finite Y := Subtype.finite
  obtain ⟨y, hyfix⟩ := hHp.nonempty_fixed_point_of_prime_not_dvd_card Y hcard
  refine ⟨y.1, y.2.1, y.2.2, ?_⟩
  have h := congrArg Subtype.val (hyfix ⟨g, Subgroup.mem_zpowers g⟩)
  change g * y.1 * g⁻¹ = y.1 at h
  calc g * y.1 = (g * y.1 * g⁻¹) * g := by group
    _ = y.1 * g := by rw [h]

theorem dvd_card_centralizer_of_dvd {X : Type} [Group X] [Finite X] {S : Subgroup X} {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Nat.card (Subgroup.normalizer (S : Set X))) (Q : X → Prop)
    (hQ : ∀ y x : X, Q x → Q (y * x * y⁻¹))
    (hcard : ¬ p ∣ Nat.card {x : X // x ∈ S ∧ Q x}) :
    ∃ x ∈ S, Q x ∧ p ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hp
  have hgp : orderOf (g : X) = p := by rw [Subgroup.orderOf_coe, hg]
  obtain ⟨x, hxS, hQx, hgx⟩ := exists_commute_of_not_dvd hgp g.2 Q hQ hcard
  refine ⟨x, hxS, hQx, ?_⟩
  rw [← hgp]
  exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_centralizer_singleton_iff.mpr hgx)

theorem card_of_mulEquiv_S0
    {X : Type} [Group X] {S : Subgroup X} (eS : S ≃* Sec4.Sporadic.J2.SJ 0) :
    Nat.card {x : X // x ∈ S ∧ (x ^ 2 = 1 ∧ x ≠ 1)} = 27 ∧
      Nat.card {x : X // x ∈ S ∧ x ^ 2 ≠ 1} = 36 := by
  have e1 : ∀ R : X → Prop, Nat.card {x : X // x ∈ S ∧ R x} = Nat.card {s : S // R (s : X)} :=
    fun R => Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun s => ⟨s.1.1, s.1.2, s.2⟩
        left_inv := fun x => rfl
        right_inv := fun s => rfl }
  have hsq : ∀ s : S, (s : X) ^ 2 = 1 ↔ s ^ 2 = 1 := fun s => by
    rw [← Subgroup.coe_pow, ← Subgroup.coe_one, Subtype.val_inj]
  have hone : ∀ s : S, (s : X) ≠ 1 ↔ s ≠ 1 := fun s => by
    rw [ne_eq, ne_eq, ← Subgroup.coe_one, Subtype.val_inj]
  refine ⟨?_, ?_⟩
  · rw [e1, ← card_inv_S0]
    refine Nat.card_congr (eS.toEquiv.subtypeEquiv fun s => ?_)
    change (s : X) ^ 2 = 1 ∧ (s : X) ≠ 1 ↔ eS s ^ 2 = 1 ∧ eS s ≠ 1
    rw [hsq, hone, ← map_pow]
    simp only [ne_eq, MulEquiv.map_eq_one_iff]
  · rw [e1, ← card_four_S0]
    refine Nat.card_congr (eS.toEquiv.subtypeEquiv fun s => ?_)
    change (s : X) ^ 2 ≠ 1 ↔ eS s ^ 2 ≠ 1
    rw [← map_pow]
    simp only [ne_eq, MulEquiv.map_eq_one_iff, hsq]

theorem eq_of_prime_dvd_card_j2 {r : ℕ} (hr : r.Prime) (h : r ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp (hr.dvd_of_dvd_pow h))))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)))

end Res162Seven

open Res162Seven in
theorem ks162J2NormSolv :
    KS162J2NormSolv := by
  intro X _ hX E hE9 S hS
  classical
  have hfinX : Finite X := Nat.finite_of_card_ne_zero (by
    rw [KFacts.KS14.card_eq_of_j2 hX]
    norm_num)
  obtain ⟨eS⟩ := nonempty_mulEquiv_S0 hX hE9 hS
  obtain ⟨h27, h36⟩ := card_of_mulEquiv_S0 eS
  have h4 : ∀ x ∈ S, x ^ 4 = 1 := by
    intro x hx
    have h1 : eS (⟨x, hx⟩ ^ 4) = 1 := by
      rw [map_pow]
      exact pow_four_S0 _
    rw [MulEquiv.map_eq_one_iff] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  set N := Subgroup.normalizer (S : Set X) with hN
  have h7 : ¬ 7 ∣ Nat.card N := by
    intro h7
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨x, -, ⟨hx2, hx1⟩, hdvd⟩ := dvd_card_centralizer_of_dvd h7
      (fun x => x ^ 2 = 1 ∧ x ≠ 1)
      (fun y x hx => ⟨by rw [conj_pow, hx.1, mul_one, mul_inv_cancel],
        fun h => hx.2 (conj_eq_one_iff.mp h)⟩)
      (by rw [h27]; norm_num)
    exact not_seven_dvd_card_centralizer_of_j2 hX hx2 hx1 hdvd
  have h5 : ¬ 5 ∣ Nat.card N := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hxS, hx2, hdvd⟩ := dvd_card_centralizer_of_dvd h5 (fun x => x ^ 2 ≠ 1)
      (fun y x hx h => hx (by rwa [conj_pow, conj_eq_one_iff] at h))
      (by rw [h36]; norm_num)
    exact not_five_dvd_card_centralizer_of_j2 hX (h4 x hxS) hx2 hdvd
  have hdvd : Nat.card N ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := by
    have h1 := Subgroup.card_subgroup_dvd_card N
    rwa [KFacts.KS14.card_eq_of_j2 hX] at h1
  apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
  have hsub : (Nat.card N).primeFactors ⊆ {2, 3} := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrN := Nat.dvd_of_mem_primeFactors hr
    rcases eq_of_prime_dvd_card_j2 hrp (hrN.trans hdvd) with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd hrN h5
    · exact absurd hrN h7
  exact (Finset.card_le_card hsub).trans (by decide)

end CFSG.RankThree.PartTwo.Sec16
