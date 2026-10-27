module

public import CFSG.Quasithin.H13.L32AC41c
public import CFSG.Quasithin.H13.L32ACSk12
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Two
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
public import CFSG.Quasithin.H13.L32ACSk11
public import CFSG.Quasithin.H13.L32ACSk6

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem alt3_comm {a b : Equiv.Perm (Fin 3)} (ha : a ∈ alternatingGroup (Fin 3))
    (hb : b ∈ alternatingGroup (Fin 3)) : a * b = b * a := by
  have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := isCyclic_of_prime_card h3
  exact congrArg Subtype.val ((IsCyclic.commGroup (α := alternatingGroup (Fin 3))).mul_comm
    ⟨a, ha⟩ ⟨b, hb⟩)

theorem isAlt_five_of_isPSL {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hodd : Odd (Nat.card (Subgroup.center X))) (h : IsPSL 2 2 2 (X ⧸ Subgroup.center X)) :
    IsAlt 5 X := by
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isPSL_two_two_two h
  have h60 : Nat.card (X ⧸ Subgroup.center X) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hZ : Subgroup.center X = ⊥ := by
    refine CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes
      hperf.commutator_eq_top _ rfl hodd ?_
    intro r _ _ hr2 P
    have hrp : r.Prime := Fact.out
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hdvd : r ^ k ∣ 60 := by
      rw [← hk, ← h60]
      exact Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have h2 : r ^ 2 ∣ 60 := (pow_dvd_pow r (by omega)).trans hdvd
      have hr8 : r < 8 := by
        have := Nat.le_of_dvd (by norm_num) h2
        nlinarith
      interval_cases r <;> revert hrp hr2 h2 <;> decide
    interval_cases k
    · have : Subsingleton (P : Subgroup (X ⧸ Subgroup.center X)) :=
        Finite.card_le_one_iff_subsingleton.mp (by rw [hk, pow_zero])
      infer_instance
    · exact isCyclic_of_prime_card (by rw [hk, pow_one])
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    e⟩

variable {G : Type} [Group G] [Finite G]

theorem isAlt5_of_s5s3 {H K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hne : Nontrivial (cStar K))
    {ρ : ↥H →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)} (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = CFSG.Open.pCore 2 ↥H) : IsAlt 5 (cStar K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  set N := CFSG.pCore 2 ↥H with hN
  have hk : ρ.ker = N := by rw [hρk, hN]
  let φb : (↥H ⧸ N) ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  set K' := K.subgroupOf H with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hK'p : ⁅K', K'⁆ = K' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le hKH,
      perfect_of_mem_cComp hK]
  set A := K'.map ρ with hA
  have hAn : A.Normal := hK'n.map ρ hρs
  have hAp : ⁅A, A⁆ = A := by rw [hA, ← Subgroup.map_commutator, hK'p]
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  have hKbA : (modO2Image H K).map φb.toMonoidHom = A := by
    rw [modO2Image, Subgroup.map_map, hA]
    try rfl
  let eA : cStar K ≃* ↥A :=
    ((cStarEquiv K).trans e).trans
      ((φb.subgroupMap (modO2Image H K)).trans (MulEquiv.subgroupCongr hKbA))
  set A₂ := A.map (MonoidHom.snd (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))) with hA₂
  have hA₂p : ⁅A₂, A₂⁆ = A₂ := by rw [hA₂, ← Subgroup.map_commutator, hAp]
  have hA₂le : A₂ ≤ alternatingGroup (Fin 3) := by
    rw [← hA₂p]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hA₂bot : A₂ = ⊥ := by
    rw [← hA₂p, eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact alt3_comm (hA₂le h₁) (hA₂le h₂)
  have hsnd : ∀ a ∈ A, a.2 = 1 := fun a ha => by
    have : a.2 ∈ A₂ := ⟨a, ha, rfl⟩
    rwa [hA₂bot, Subgroup.mem_bot] at this
  set A₁ := A.map (MonoidHom.fst (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))) with hA₁
  let f := (MonoidHom.fst (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3))).subgroupMap A
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (Prod.ext ?_ ?_), MonoidHom.subgroupMap_surjective _ _⟩
    · exact congrArg Subtype.val hab
    · rw [hsnd _ a.2, hsnd _ b.2]
  have hA₁n : A₁.Normal := hAn.map _ fun x => ⟨(x, 1), rfl⟩
  have hA₁p : ⁅A₁, A₁⁆ = A₁ := by rw [hA₁, ← Subgroup.map_commutator, hAp]
  have hA₁bot : A₁ ≠ ⊥ := by
    intro hbot
    have : Subsingleton ↥A₁ := by
      rw [hbot]
      infer_instance
    obtain ⟨a, b, hab⟩ := hne.exists_pair_ne
    exact hab (eA.injective (hf.1 (Subsingleton.elim _ _)))
  have h5 := eq_alt5_of_normal_perfect hA₁n hA₁p hA₁bot
  exact ⟨(eA.trans (MulEquiv.ofBijective f hf)).trans (MulEquiv.subgroupCongr h5)⟩

theorem lemma14_7_45_a5_of (hN1 : LieSylowOver3) (hN2 : LieBorelInvert3) (h29 : Thm14_7_29)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h30 : Lemma14_7_30)
    (h32 : Lemma14_7_32) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h42 : Lemma14_7_42_S5S3)
    (h43 : Lemma14_7_43) (h44 : Lemma14_7_44) : Lemma14_7_45_A5 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie
  have hq := (h30 G T L V H S K hK).1
  have hKn := le_normalizer_of_setting hA37 hA38 S hK (h32 G T L V H S K hK)
  by_cases hl1K : l1 T L V ≤ K
  · rcases lemma14_7_41_two hN1 hN2 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K with
      h | h | h
    · exact isAlt_five_of_isPSL hq.1 (odd_card_center_cStar K) h
    · exact absurd h (h43 G T L V H S K hK hHeq n hn hLie)
    · exact absurd h (h44 G T L V H S K hK hHeq n hn hLie)
  · obtain ⟨ρ, hρs, hρk⟩ := h42 G T L V H S K hK hHeq n hn hLie hl1K
    have := hq.2.1
    have : Nontrivial (cStar K) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (cStar K))).nontrivial
    exact isAlt5_of_s5s3 hK hKn this hρs hρk

end CFSG.Quasithin.H13.L32A.C
