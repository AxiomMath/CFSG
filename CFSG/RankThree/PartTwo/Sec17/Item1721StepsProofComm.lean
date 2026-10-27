module

import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.Quasithin.Background.A318PC7
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.Asc83Table.M22
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaSTransfer
public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Claim1721SCommL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      omegaA A = {Subgroup.zpowers c} →
        ∀ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)) → A ≤ T →
          ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L

@[expose] def InnThreeSylow (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (σ : MulAut X) (k : ℕ), σ ^ 3 ^ k = 1 → ∀ Sb : Sylow 3 X,
    (Sb : Subgroup X).map σ.toMonoidHom = Sb → σ ∈ (MulAut.conj : X →* MulAut X).range

namespace Proof1721

theorem innThreeSylow_alt7 {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* alternatingGroup (Fin 7))) : InnThreeSylow X := by
  intro σ k hσ _ _
  obtain ⟨e⟩ := hX
  set A7 := alternatingGroup (Fin 7) with hA7
  set σ' : MulAut A7 := (MulAut.congr e) σ with hσ'
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 σ'
  have hσ'k : σ' ^ 3 ^ k = 1 := by rw [hσ', ← map_pow, hσ, map_one]
  have hπk : π ^ 3 ^ k = 1 :=
    (CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by norm_num))
      (by rw [map_pow, hπ, hσ'k, map_one])
  have hsign : Equiv.Perm.sign π = 1 := by
    have h1 : Equiv.Perm.sign π ^ 3 ^ k = 1 := by rw [← map_pow, hπk, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      have hodd : Odd (3 ^ k) := Odd.pow (by decide)
      rw [hodd.neg_one_pow] at h1
      exact absurd h1 (by decide)
  have hπA : π ∈ A7 := Equiv.Perm.mem_alternatingGroup.mpr hsign
  refine ⟨e.symm ⟨π, hπA⟩, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut A7 => φ (e x)) hπ
  simp only [hσ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h1]
  apply Subtype.ext
  rfl

theorem innThreeSylow_m22
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    InnThreeSylow X := by
  intro σ k hσ Sb hSb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hX
  have hB9 : Nat.card (Sb : Subgroup X) = 9 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      Asc83Table.M22.factorization_card]
    norm_num
  have h8 : ∀ b ∈ (Sb : Subgroup X), (σ ^ 8) b = b := fun b hb =>
    KFacts.KP4.m22_aut_pow_eight ⟨e⟩ hB9 hSb hb
  have hcop : Nat.gcd 8 (orderOf σ) = 1 := by
    have hdvd : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hσ
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hm]
    exact Nat.Coprime.pow_right m (by norm_num)
  have hmem : σ ∈ Subgroup.zpowers (σ ^ 8) := mem_zpowers_pow_iff.mpr hcop
  have hfix : ∀ b ∈ (Sb : Subgroup X), σ b = b := by
    intro b hb
    have hstab : σ ^ 8 ∈ MulAction.stabilizer (MulAut X) b := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact h8 b hb
    have hσstab : σ ∈ MulAction.stabilizer (MulAut X) b :=
      (Subgroup.zpowers_le.mpr hstab) hmem
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hσstab
    exact hσstab
  obtain ⟨c, -, hc⟩ := KFacts.KP4.m22_aut_fix_eq_conj ⟨e⟩ hB9 hfix
  exact ⟨c, hc.symm⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_mul_mem_thetaQuotCentralizer_of_inn {L : Subgroup G}
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hInn : InnThreeSylow (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    {S : Subgroup G} (hS : IsSylowOf 3 S L) {ρ : G}
    (hρL : ρ ∈ Subgroup.normalizer (L : Set G)) (hρS : ρ ∈ Subgroup.normalizer (S : Set G))
    {k : ℕ} (hρ : ρ ^ 3 ^ k = 1) :
    ∃ s ∈ S, s⁻¹ * ρ ∈ Sec4.thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S', rfl⟩ := hS
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set ρ' : Subgroup.normalizer (L : Set G) := ⟨ρ, hρL⟩ with hρ'
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ρ') with hσ
  have hσk : σ ^ 3 ^ k = 1 := by
    have h1 : ρ' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hρ)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσapp : ∀ x : ↥L, σ (π x) = π (L.normalizerMonoidHom ρ' x) := fun x => rfl
  have hρS' : ∀ x ∈ (S' : Subgroup ↥L), L.normalizerMonoidHom ρ' x ∈ (S' : Subgroup ↥L) := by
    intro x hx
    have h1 : ρ * (x : G) * ρ⁻¹ ∈ (S' : Subgroup ↥L).map L.subtype :=
      (Subgroup.mem_normalizer_iff.mp hρS x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = L.normalizerMonoidHom ρ' x := Subtype.ext hyx
    exact this ▸ hy
  set Sb : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    S'.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup _) = (S' : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  have hσSb : (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)).map σ.toMonoidHom = Sb := by
    have hle : (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)).map σ.toMonoidHom ≤ Sb := by
      rw [hSb]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hσapp]
      exact Subgroup.mem_map_of_mem π (hρS' x hx)
    have hc : Nat.card ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)).map σ.toMonoidHom) =
        Nat.card (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
      Subgroup.card_map_of_injective σ.injective
    exact Subgroup.eq_of_le_of_card_ge hle hc.ge
  obtain ⟨q, hq⟩ := hInn σ k hσk Sb hσSb
  have hqapp : ∀ y, q * y * q⁻¹ = σ y := fun y => by rw [← hq]; rfl
  have hqN : q ∈ Subgroup.normalizer ((Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
      Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hqapp]
    rw [SetLike.mem_coe, hSb] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hσapp]
    exact Subgroup.mem_map_of_mem π (hρS' x hx)
  have hq3 : q ^ 3 ^ k = 1 := by
    have hc : q ^ 3 ^ k ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : MulAut.conj (q ^ 3 ^ k) = 1 := by rw [map_pow, hq, hσk]
      have h2 := congrArg (fun φ : MulAut _ => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * q ^ 3 ^ k = q ^ 3 ^ k * y * (q ^ 3 ^ k)⁻¹ * q ^ 3 ^ k := by rw [h2]
        _ = q ^ 3 ^ k * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hqS : q ∈ (Sb : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    have hdvd : orderOf q ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hq3
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hp : IsPGroup 3 (Subgroup.zpowers q) :=
      IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
    have hsup := hp.to_sup_of_normal_right' Sb.isPGroup' (Subgroup.zpowers_le.mpr hqN)
    have heq := Sb.3 hsup le_sup_right
    exact heq ▸ (le_sup_left : Subgroup.zpowers q ≤ _) (Subgroup.mem_zpowers q)
  rw [hSb] at hqS
  obtain ⟨s₁, hs₁, hs₁q⟩ := hqS
  refine ⟨(s₁ : G), ⟨s₁, hs₁, rfl⟩, ?_⟩
  have hs₁N : (s₁ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer s₁.2
  have hmemN : (s₁ : G)⁻¹ * ρ ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hs₁N) hρL
  refine mem_thetaQuotCentralizer_iff.mpr ⟨hmemN, fun x => ?_⟩
  have heq : L.normalizerMonoidHom ⟨(s₁ : G)⁻¹ * ρ, hmemN⟩ x =
      s₁⁻¹ * L.normalizerMonoidHom ρ' x * s₁ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
    show (s₁ : G)⁻¹ * ρ * (x : G) * ((s₁ : G)⁻¹ * ρ)⁻¹ = (s₁ : G)⁻¹ * (ρ * (x : G) * ρ⁻¹) * s₁
    group
  rw [heq, map_mul, map_mul, map_inv, ← hσapp, ← hqapp, hs₁q]
  group
  rfl

theorem commutator_mem_of_inn {L : Subgroup G}
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hInn : InnThreeSylow (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    {A T : Subgroup G} {c : G} (hAF : A ∈ partTwoF G)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hc : orderOf c = 3) (hT3 : IsPGroup 3 T) (hAT : A ≤ T)
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowOf 3 (T ⊓ L) L) :
    ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Y := T ⊓ Sec4.thetaQuotCentralizer L with hYdef
  have hcA : c ∈ A := hAeq ▸ (le_sup_left : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  have hcL : ∀ x ∈ L, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hx)).symm
  have hcY : c ∈ Y := ⟨hAT hcA, mem_thetaQuotCentralizer_of_commute hcL⟩
  set S' := (T ⊓ L).subgroupOf L with hS'
  have hS'3 : IsPGroup 3 S' := (hT3.to_le inf_le_left).comap_of_injective L.subtype
    L.subtype_injective
  have hinj : Set.InjOn π (S' : Set ↥L) := injOn_mk_of_isPGroup Nat.prime_three hS'3
  have hYS : ∀ y ∈ Y, ∀ s ∈ T ⊓ L, y * s = s * y := by
    intro y hy s hs
    obtain ⟨hyN, hytriv⟩ := mem_thetaQuotCentralizer_iff.mp hy.2
    have hysT : y * s * y⁻¹ ∈ T := mul_mem (mul_mem hy.1 hs.1) (inv_mem hy.1)
    have hysL : y * s * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN s).mp hs.2
    have h1 : (⟨y * s * y⁻¹, hysL⟩ : ↥L) = L.normalizerMonoidHom ⟨y, hyN⟩ ⟨s, hs.2⟩ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨y, hyN⟩ ⟨s, hs.2⟩).symm
    have h2 : (⟨y * s * y⁻¹, hysL⟩ : ↥L) = ⟨s, hs.2⟩ := by
      refine hinj (show (⟨y * s * y⁻¹, hysL⟩ : ↥L) ∈ S' from ⟨hysT, hysL⟩)
        (show (⟨s, hs.2⟩ : ↥L) ∈ S' from hs) ?_
      rw [h1]
      exact hytriv ⟨s, hs.2⟩
    have h3 : y * s * y⁻¹ = s := congrArg Subtype.val h2
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h3]
  have hAL : A ⊓ L ≤ T ⊓ L := inf_le_inf_right L hAT
  have hY3 : ∀ z ∈ Y, z ^ 3 = 1 → z ∈ Subgroup.zpowers c := by
    intro z hz hz3
    have hAz : A ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun e he => ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hTc hz.1)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hYS z hz e (hAL he)).symm
    have hzA : z ∈ A := mem_of_mem_partTwoF hAF hz3 hAz
    have hcAL : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun e he => (hcL e he.2).symm
    rw [hAeq] at hzA
    obtain ⟨k, e, he, rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcAL hzA
    have heY : e ∈ Y := by
      have : e = (c ^ k)⁻¹ * (c ^ k * e) := by group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem hcY k)) hz
    obtain ⟨heN, hetriv⟩ := mem_thetaQuotCentralizer_iff.mp heY.2
    have hecen : π ⟨e, he.2⟩ ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        have h1 : L.normalizerMonoidHom ⟨e, heN⟩ x = ⟨e, he.2⟩ * x * ⟨e, he.2⟩⁻¹ :=
          Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; rfl)
        have h2 := hetriv x
        rw [h1, map_mul, map_mul, map_inv] at h2
        change π x * π ⟨e, he.2⟩ = π ⟨e, he.2⟩ * π x
        calc π x * π ⟨e, he.2⟩ = π ⟨e, he.2⟩ * π x * (π ⟨e, he.2⟩)⁻¹ * π ⟨e, he.2⟩ := by
              rw [h2]
          _ = π ⟨e, he.2⟩ * π x := by group
    rw [hZ, Subgroup.mem_bot] at hecen
    have he1 : (⟨e, he.2⟩ : ↥L) = 1 :=
      hinj (show (⟨e, he.2⟩ : ↥L) ∈ S' from hAL he) (one_mem S') (by rw [hecen, map_one])
    have he1' : e = 1 := congrArg Subtype.val he1
    rw [he1', mul_one]
    exact zpow_mem (Subgroup.mem_zpowers c) k
  have hY3' : IsPGroup 3 Y := hT3.to_le inf_le_left
  have hYcyc : IsCyclic Y := by
    refine CFSG.Quasithin.A318P.isCyclic_of_unique_three hY3' (Z := Subgroup.zpowers c)
      (by rw [Nat.card_zpowers, hc]) fun r hr hr3 => hY3 r hr ?_
    rw [← hr3]
    exact pow_orderOf_eq_one r
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    Sec13.mul_comm_of_isCyclic (P := Y) ha hb
  have hdecomp : ∀ t ∈ T, ∃ s ∈ T ⊓ L, s⁻¹ * t ∈ Y := by
    intro t ht
    obtain ⟨k, hk⟩ := hT3 ⟨t, ht⟩
    have htk : t ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have htS : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      le_normalizer_inf (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer ht))
        (Subgroup.zpowers_le.mpr (hTL ht)) (Subgroup.mem_zpowers t)
    obtain ⟨s, hs, hsY⟩ :=
      exists_inv_mul_mem_thetaQuotCentralizer_of_inn hZ hInn hS (hTL ht) htS htk
    exact ⟨s, hs, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hs).1) ht, hsY⟩⟩
  intro x hx y hy
  obtain ⟨a, ha, hb⟩ := hdecomp x hx
  obtain ⟨c', hc', hd⟩ := hdecomp y hy
  set b := a⁻¹ * x with hbdef
  set d := c'⁻¹ * y with hddef
  have hx' : x = a * b := by rw [hbdef]; group
  have hy' : y = c' * d := by rw [hddef]; group
  have hbc : b * c' = c' * b := hYS b hb c' hc'
  have hbd : b * d = d * b := hYcomm b hb d hd
  have hda : d * a = a * d := hYS d hd a ha
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (show Commute d a from hda)).eq
  have heq : x * y * x⁻¹ * y⁻¹ = a * c' * a⁻¹ * c'⁻¹ := by
    rw [hx', hy']
    calc a * b * (c' * d) * (a * b)⁻¹ * (c' * d)⁻¹
        = a * (b * c') * d * b⁻¹ * a⁻¹ * d⁻¹ * c'⁻¹ := by group
      _ = a * c' * (b * d) * b⁻¹ * a⁻¹ * d⁻¹ * c'⁻¹ := by rw [hbc]; group
      _ = a * c' * d * a⁻¹ * d⁻¹ * c'⁻¹ := by rw [hbd]; group
      _ = a * c' * (d * a⁻¹) * d⁻¹ * c'⁻¹ := by group
      _ = a * c' * a⁻¹ * c'⁻¹ := by rw [hda']; group
  rw [heq]
  exact mul_mem (mul_mem (mul_mem ha.2 hc'.2) (inv_mem ha.2)) (inv_mem hc'.2)

end Proof1721

end CFSG.RankThree.PartTwo.Sec17
