module

public import CFSG.Quasithin.Vol2.Ch1Sec3Solvable
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem kzEqOnePowThreeMem_kz3 {X : Type} [Group X] {N : Subgroup X} (hN : IsPGroup 2 N)
    {g : X} (hg3 : g ^ 3 = 1) (hgN : g ∈ N) : g = 1 := by
  obtain ⟨n, hn⟩ := hN ⟨g, hgN⟩
  have h2 : g ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hdvd : orderOf g ∣ Nat.gcd 3 (2 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg3) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem kzLiftPowThree_kz3 {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : IsPGroup 2 N) (A : Subgroup (X ⧸ N)) (k : ℕ) (hA : Nat.card A = 3 ^ k) :
    ∃ S : Subgroup X, Nat.card S = 3 ^ k ∧ S ⊓ N = ⊥ ∧ S.map (QuotientGroup.mk' N) = A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup X := A.comap (QuotientGroup.mk' N) with hR
  have hRN : N ≤ R := fun x hx => by
    rw [hR, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact A.one_mem
  have hfA : ∀ r : R, (QuotientGroup.mk' N) (r : X) ∈ A := fun r => r.2
  let f' : R →* A := (QuotientGroup.mk' N).comp R.subtype |>.codRestrict A hfA
  have hf'surj : Function.Surjective f' := by
    intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (a : X ⧸ N)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [hR, Subgroup.mem_comap, hx]
      exact a.2
    · apply Subtype.ext
      exact hx
  have hf'ker : f'.ker = N.subgroupOf R := by
    ext ⟨x, hx⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' N) x = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff x).mp h1
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff x).mpr h
  have hcardR : Nat.card R = Nat.card A * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf R)]
    congr 1
    · exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hf'ker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f' hf'surj)).toEquiv
    · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
  have hdvd : 3 ^ k ∣ Nat.card R := ⟨Nat.card N, by rw [hcardR, hA]⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set S : Subgroup X := K.map R.subtype with hS
  have hSc : Nat.card S = 3 ^ k := by
    rw [hS, Subgroup.card_map_of_injective (Subtype.val_injective), hK]
  have hS3 : IsPGroup 3 S := IsPGroup.of_card hSc
  have hSN : S ⊓ N = ⊥ := (IsPGroup.disjoint_of_ne 3 2 (by norm_num) S N hS3 hN).eq_bot
  refine ⟨S, hSc, hSN, ?_⟩
  have hsub : S.map (QuotientGroup.mk' N) ≤ A := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨r, -, rfl⟩ := hs
    exact r.2
  have hcard : Nat.card (S.map (QuotientGroup.mk' N)) = Nat.card S := by
    apply Ch1Sec3.card_map_of_inf_ker_eq_bot
    rw [QuotientGroup.ker_mk']
    exact hSN
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hSc, hA])

theorem kzRankContra_kz3 {Γ : Type} [Group Γ] [Finite Γ]
    (hrk : CFSG.Open.SQTKTauCeti.StronglyQuasithin Γ) (E : Subgroup Γ)
    (hE : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 3 = 1) (hcard : 9 < Nat.card E) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hp
  have hm2 : 2 < m := by
    by_contra h
    have h' : m ≤ 2 := Nat.le_of_not_lt h
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h'
    omega
  have hmem : m ∈ {k | ∃ E' : Subgroup Γ, E' ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ k} :=
    ⟨E, le_top, ⟨hE, hexp⟩, hm⟩
  have hbdd : BddAbove {k | ∃ E' : Subgroup Γ, E' ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E' ∧
      Nat.card E' = 3 ^ k} := by
    refine ⟨Nat.card Γ, ?_⟩
    rintro k ⟨E', -, -, hk⟩
    have h1 : Nat.card E' ≤ Nat.card Γ := Subgroup.card_le_card_group E'
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have hle : m ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Γ) := le_csSup hbdd hmem
  have h2 := hrk 3 Nat.prime_three (by norm_num)
  omega

theorem kzClosureCommExp_kz3 {Γ : Type} [Group Γ] {s : Set Γ}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hexp : ∀ x ∈ s, x ^ 3 = 1) :
    IsMulCommutative (Subgroup.closure s) ∧ (∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s,
      a * b = b * a) ∧ ∀ e ∈ Subgroup.closure s, e ^ 3 = 1 := by
  letI : CommGroup (Subgroup.closure s) :=
    Subgroup.closureCommGroupOfComm (fun x hx y hy _ => hcomm x hx y hy)
  refine ⟨inferInstance, fun a ha b hb => ?_, ?_⟩
  · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Subgroup.closure s) ⟨b, hb⟩)
  intro e he
  have hle : Subgroup.closure (Subtype.val ⁻¹' s : Set (Subgroup.closure s)) ≤
      (powMonoidHom 3 : Subgroup.closure s →* Subgroup.closure s).ker := by
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : (x : Γ) ∈ s := hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hexp _ hx'
  have htop : (⊤ : Subgroup (Subgroup.closure s)) ≤
      (powMonoidHom 3 : Subgroup.closure s →* Subgroup.closure s).ker := by
    rw [← Subgroup.closure_closure_coe_preimage (k := s)]
    exact hle
  have h := htop (Subgroup.mem_top (⟨e, he⟩ : Subgroup.closure s))
  rw [MonoidHom.mem_ker, powMonoidHom_apply] at h
  have h' := congrArg Subtype.val h
  simpa using h'

theorem kzThreeRank2OfAlt6OrHat_kz3 {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Quasithin.IsAlt 6 Q ∨ CFSG.Quasithin.IsHat Q (alternatingGroup (Fin 6))) :
    FFC.ThreeRank2 Q := by
  rcases hQ with hA | hH
  · obtain ⟨e⟩ : Nonempty (Q ≃* alternatingGroup (Fin 6)) := hA
    exact FFC.ThreeRank2.of_mulEquiv e.symm (FFC.threeRank2_alt (le_refl 6))
  · obtain ⟨-, hc, he⟩ : CFSG.IsQuasisimple Q ∧ Nat.card (Subgroup.center Q) = 3 ∧
        Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) := hH
    obtain ⟨e⟩ := he
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let φ : Q →* alternatingGroup (Fin 6) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
    have hsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : φ.ker = Subgroup.center Q := by
      ext q
      rw [MonoidHom.mem_ker]
      change e (QuotientGroup.mk' (Subgroup.center Q) q) = 1 ↔ q ∈ Subgroup.center Q
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hp : IsPGroup 3 φ.ker := by
      rw [hker]
      exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
    exact FFC.ThreeRank2.of_surjective_pgroup_ker φ hsurj hp (FFC.threeRank2_alt (le_refl 6))

theorem kzCardCenterLeThree_kz3 {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Quasithin.IsAlt 6 Q ∨ CFSG.Quasithin.IsHat Q (alternatingGroup (Fin 6))) :
    Nat.card (Subgroup.center Q) ≤ 3 := by
  rcases hQ with hA | hH
  · obtain ⟨e⟩ : Nonempty (Q ≃* alternatingGroup (Fin 6)) := hA
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup Q := MulEquiv.isSimpleGroup e
    have hcardQ : Nat.card Q = 360 := by
      have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
      have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]
        simp [Nat.factorial]
      rw [Nat.card_congr e.toEquiv]
      omega
    have hnp : ¬ (Nat.card Q).Prime := by
      rw [hcardQ]
      norm_num
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := Q) (Subgroup.center Q) with h | h
    · rw [h, Subgroup.card_bot]
      norm_num
    · exfalso
      apply res822_nonabelian_of_not_prime hnp
      intro a b
      have ha : a ∈ Subgroup.center Q := by
        rw [h]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  · obtain ⟨-, hc, -⟩ : CFSG.IsQuasisimple Q ∧ Nat.card (Subgroup.center Q) = 3 ∧
        Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) := hH
    exact le_of_eq hc

@[expose] def KzAutE9Perfect_kz3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A], Nat.card A = 9 → (∀ a : A, a ^ 3 = 1) →
    ∀ R : Subgroup (MulAut A), ⁅R, R⁆ = R → R = ⊥

theorem kzHomTrivialOfPerfect_kz3 {K M : Type} [Group K] [Group M] (f : K →* M)
    (hK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (hM : ∀ R : Subgroup M, ⁅R, R⁆ = R → R = ⊥) (k : K) :
    f k = 1 := by
  have hR : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hK]
  have h := hM f.range hR
  have hk : f k ∈ f.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
  rw [h, Subgroup.mem_bot] at hk
  exact hk

theorem kzTopCommutatorOfPerfect_kz3 {G : Type} [Group G] {K' : Subgroup G}
    (hK : ⁅K', K'⁆ = K') : ⁅(⊤ : Subgroup K'), (⊤ : Subgroup K')⁆ = ⊤ := by
  have hmap : Subgroup.map K'.subtype (⊤ : Subgroup K') = K' := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (Subgroup.subtype_injective K')
  rw [Subgroup.map_commutator, hmap]
  exact hK

end CFSG.Quasithin.H13
