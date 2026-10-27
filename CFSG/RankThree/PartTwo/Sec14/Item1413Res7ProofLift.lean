module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec10.Item101
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofXPtTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Proof1413Res7

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_thetaPre {A L : Subgroup G} {eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hA3 : IsPGroup 3 A) (hAΘ : A ≤ Subgroup.normalizer (thetaPre L eb : Set G))
    (h2 : 2 ∣ Nat.card (Res8Hess.thetaC eb)) :
    ∃ S : Subgroup G, S ≤ thetaPre L eb ∧ IsPGroup 2 S ∧
      A ≤ Subgroup.normalizer (S : Set G) ∧
      ∃ s : ↥L, (s : G) ∈ S ∧ QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  obtain ⟨P, hAP⟩ := Res8Hess.exists_invariant_sylow hA3 (not_three_dvd_card_thetaPre L eb) hAΘ 2
  set φ : ↥(thetaPre L eb) →* ↥(Res8Hess.thetaC eb) :=
    (π.comp (Subgroup.inclusion (thetaPre_le L eb))).codRestrict (Res8Hess.thetaC eb)
      (fun x => (mem_thetaPre_iff.mp x.2).2) with hφ
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) (z : _)
    have hlΘ : (l : G) ∈ thetaPre L eb := mem_thetaPre_iff.mpr ⟨l.2, by
      change π l ∈ Res8Hess.thetaC eb
      rw [hπ, hl]
      exact z.2⟩
    exact ⟨⟨l, hlΘ⟩, Subtype.ext hl⟩
  set Q := P.mapSurjective hφs with hQ
  have hQ1 := Res8Hess.map_sylow_ne_bot Q h2
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
  obtain ⟨q, hq, rfl⟩ := hy
  have hqQ : q ∈ (P : Subgroup ↥(thetaPre L eb)).map φ := by
    rw [← Sylow.coe_mapSurjective hφs]
    exact hq
  obtain ⟨t, ht, rfl⟩ := hqQ
  refine ⟨(P : Subgroup ↥(thetaPre L eb)).map (thetaPre L eb).subtype,
    Subgroup.map_subtype_le _, P.isPGroup'.map _, hAP,
    Subgroup.inclusion (thetaPre_le L eb) t, ⟨t, ht, rfl⟩, ?_⟩
  intro h
  apply hy1
  apply Subtype.ext
  exact h

theorem exists_sylow_thetaPre_centralizer {A L : Subgroup G}
    {eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L} (hA3 : IsPGroup 3 A)
    (hAΘ : A ≤ Subgroup.normalizer (thetaPre L eb : Set G)) {r : G}
    (hAr : A ≤ Subgroup.centralizer ({r} : Set G)) (hr2 : r ^ 2 = 1)
    (hrΘ : r ∈ Subgroup.normalizer (thetaPre L eb : Set G)) (h2 : 2 ∣ Nat.card (thetaPre L eb))
    (hθ2 : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :
    ∃ S : Subgroup G, S ≤ thetaPre L eb ⊓ Subgroup.centralizer ({r} : Set G) ∧ IsPGroup 2 S ∧
      A ≤ Subgroup.normalizer (S : Set G) ∧
      ∃ s : ↥L, (s : G) ∈ S ∧ QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Θr := thetaPre L eb ⊓ Subgroup.centralizer ({r} : Set G) with hΘr
  have h2r : 2 ∣ Nat.card Θr := two_dvd_card_inf_centralizer hr2 hrΘ h2
  have hAΘr : A ≤ Subgroup.normalizer (Θr : Set G) :=
    le_normalizer_inf hAΘ (hAr.trans Subgroup.le_normalizer)
  have hΘr3 : ¬ 3 ∣ Nat.card Θr := fun h3 =>
    not_three_dvd_card_thetaPre L eb (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨P, hAP⟩ := Res8Hess.exists_invariant_sylow hA3 hΘr3 hAΘr 2
  set S := (P : Subgroup ↥Θr).map Θr.subtype with hS
  have hS2 : IsPGroup 2 S := P.isPGroup'.map _
  have hS1 : S ≠ ⊥ := Res8Hess.map_sylow_ne_bot P h2r
  obtain ⟨⟨s, hsS⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS1
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hsΘr : s ∈ Θr := Subgroup.map_subtype_le _ hsS
  have hsL : s ∈ L := thetaPre_le L eb hsΘr.1
  refine ⟨S, Subgroup.map_subtype_le _, hS2, hAP, ⟨s, hsL⟩, hsS, fun h => hs1' ?_⟩
  have hsθ : s ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨⟨s, hsL⟩, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
  obtain ⟨k, hk⟩ := hS2 ⟨s, hsS⟩
  have hsk : orderOf s ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk s hsS]
    exact orderOf_dvd_of_pow_eq_one hk
  have hsodd : orderOf s ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) :=
    Subgroup.orderOf_dvd_natCard _ hsθ
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hθ2)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hsk hsodd)

theorem not_isConjIn_of_types {A L V : Subgroup G} {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hp3 : 3 < p) (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hEe : CFSG.Assembly.IsElemAbelian 3
      ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))))
    (hE9 : Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9)
    (htr : ∀ y₀ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      y₀ ≠ 1 → ∀ y₁ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
        y₁ ≠ 1 → ∃ w ∈ Subgroup.normalizer
          (((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
            Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
              Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)), w * y₀ * w⁻¹ = y₁)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hXL : xA A ≤ Subgroup.normalizer (L : Set G)) {a₁ a₂ : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (ha₁ : a₁ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    (ha₁1 : a₁ ≠ 1)
    (ha₂ : a₂ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    (ha₂n : a₂ ∉ Subgroup.zpowers a₁) {S₁ S₂ : Subgroup G} {s₁ s₂ : ↥L} (hs₁ : (s₁ : G) ∈ S₁)
    (hs₁θ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₁ ∈ Res8Hess.thetaC a₁)
    (hs₁1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₁ ≠ 1) (hs₂ : (s₂ : G) ∈ S₂)
    (hs₂θ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₂ ∈ Res8Hess.thetaC a₂)
    (hs₂1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₂ ≠ 1) {S T : Subgroup G}
    (hS₁S : S₁ ≤ S) (hT : T ∈ scriptQPiStar A (lB A) V (piOf 2)) (hS₂T : S₂ ≤ T) :
    ¬ IsConjIn (xA A ⊓ V) S T := by
  rintro ⟨x, hx, rfl⟩
  have hxX : x ∈ xA A := (Subgroup.mem_inf.mp hx).1
  have hxA : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hxX
  obtain ⟨s₁', hs₁'eq, hs₁'θ, hs₁'1⟩ := conj_mem_thetaC hxA (hXL hxX) ha₁ hs₁θ hs₁1
  have hs₁'T : (s₁' : G) ∈ S.map (MulAut.conj x).toMonoidHom := by
    rw [hs₁'eq]
    exact ⟨s₁, hS₁S hs₁, rfl⟩
  exact ha₂n (mem_zpowers_of_types he hp3 hiso hEe hE9 htr hAL hT.prop.1.1.1.2.2
    (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop) ha₁ ha₁1 ha₂ hs₁'T (hS₂T hs₂) hs₁'θ
    hs₁'1 hs₂θ hs₂1)

theorem le_theta_of_two {A L : Subgroup G} {e : ℕ} [Fact (Nat.Prime 2)] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 e)
    (hEe : CFSG.Assembly.IsElemAbelian 3
      ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))))
    (hE9 : Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9)
    (htr : ∀ y₀ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      y₀ ≠ 1 → ∀ y₁ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
        y₁ ≠ 1 → ∃ w ∈ Subgroup.normalizer
          (((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
            Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
              Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)), w * y₀ * w⁻¹ = y₁)
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (hVL : V ≤ L)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Vbar := (V.subgroupOf L).map π with hVbar
  have hVb2 : IsPGroup 2 Vbar := (hV2.comap_of_injective L.subtype L.subtype_injective).map π
  have hEV : (A.subgroupOf L).map π ≤
      Subgroup.normalizer (Vbar : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := hy
    have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp hw
    have h1 : (b : G) * w * (b : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV (Subgroup.mem_subgroupOf.mp hb)) _).mp hwV
    refine ⟨b * w * b⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hVb := Proof1413Res6.eq_bot_of_isPGroup_two_of_hess hEe hE9
    (fun z hz hz1 => Proof1413Res6.odd_card_centralizer_of_two he hiso hEe hE9 htr hz hz1)
    hVb2 hEV
  intro v hv
  have h1 : π ⟨v, hVL hv⟩ ∈ Vbar := ⟨⟨v, hVL hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  rw [hVb, Subgroup.mem_bot] at h1
  exact ⟨⟨v, hVL hv⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem le_theta_sup_xA (h142 : Item142AllS14) (hbot : Item145BotS14) {A L : Subgroup G}
    {a : G} (h' : Sec14Std G A a L) (hAa : A = Subgroup.zpowers a ⊔ (A ⊓ L))
    (hL2 : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ L → A ≤ Subgroup.normalizer (V : Set G) →
      V ≤ inSubgroup (aschbacherSolvableCore 3) L)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSa : S ≤ Subgroup.centralizer ({a} : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ inSubgroup (aschbacherSolvableCore 3) L ⊔ xA A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h'.toSec13Data
  have hA27 : IsE27 A := h'.isE27
  have hA3 : IsPGroup 3 A := hA27.isPGroup
  set θG := inSubgroup (aschbacherSolvableCore 3) L with hθG
  have hθ3 : ¬ 3 ∣ Nat.card θG := (Sec6.theta_solvable_and_not_dvd L).2
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h'.chosen136.2 a hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' h3L
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := hSa.trans hCN
  have hAθ : A ≤ Subgroup.normalizer (θG : Set G) :=
    hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L)
  have hSθ : S ≤ Subgroup.normalizer (θG : Set G) :=
    hSN.trans (Sec6.normalizer_le_normalizer_theta L)
  have hVθ : S ⊓ L ≤ θG :=
    hL2 _ (hS2.to_le inf_le_left) inf_le_right (le_normalizer_inf hAS hD.le_normalizer)
  set U := S ⊔ θG with hU
  have hU3 : ¬ 3 ∣ Nat.card U :=
    (isPiSubgroup_piCompl_iff Nat.prime_three U).mp
      (isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_three_of_piOf_two
        ((isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2))
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hθ3) hSθ)
  have hUa : U ≤ Subgroup.centralizer ({a} : Set G) :=
    sup_le hSa ((Sec6.theta_le L).trans hD.le_centralizer)
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA27.1.1
  set UA := U ⊓ Subgroup.centralizer (A : Set G) with hUA
  have hUAq : UA ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_point h142 h'
      (inf_le_left.trans (hUa.trans (centralizer_singleton_le_normalizer_zpowers a)))
      (fun h => hU3 (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
      (le_normalizer_inf (le_normalizer_sup hAS hAθ) (hAC.trans Subgroup.le_normalizer))
  have hUAX : UA ≤ xA A := le_pPrimeCoreOf_centralizer (hbot G A a L h') hUAq inf_le_right
  have hcomA : ∀ z ∈ A ⊓ L, z * a = a * z := fun z hz => hD.commute hz.1 hD.mem_A
  have hsb : ∀ s ∈ S, ∀ b ∈ A, s⁻¹ * (b * s * b⁻¹) ∈ θG := by
    intro s hs b hb
    rw [hAa] at hb
    obtain ⟨i, d, hd, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers hcomA hb
    have hdsd : d * s * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS hd.1) s).mp hs
    have hca : Commute (a ^ i) (d * s * d⁻¹) :=
      Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hSa hdsd)).symm i
    have heq : a ^ i * d * s * (a ^ i * d)⁻¹ = d * s * d⁻¹ := by
      calc a ^ i * d * s * (a ^ i * d)⁻¹ = a ^ i * (d * s * d⁻¹) * (a ^ i)⁻¹ := by group
        _ = d * s * d⁻¹ := by rw [hca.eq, mul_inv_cancel_right]
    rw [heq]
    refine hVθ (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hs) hdsd, ?_⟩)
    have h1 : s⁻¹ * d * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (inv_mem hs)) d).mp hd.2
      simpa using this
    rw [show s⁻¹ * (d * s * d⁻¹) = s⁻¹ * d * s * d⁻¹ by group]
    exact mul_mem h1 (inv_mem hd.2)
  intro s hs
  set α : ↥A →* MulAut G := MulAut.conj.comp A.subtype with hα
  obtain ⟨c', hc', hcfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA3 α θG hθ3 s).2 (by
      intro b x hx
      change s⁻¹ * ((b : G) * x * (b : G)⁻¹) ∈ θG
      have h1 := hsb s hs b b.2
      have h2 : (b : G) * (s⁻¹ * x) * (b : G)⁻¹ ∈ θG :=
        (Subgroup.mem_normalizer_iff.mp (hAθ b.2) _).mp hx
      have h3 := θG.mul_mem h1 h2
      rwa [show s⁻¹ * ((b : G) * s * (b : G)⁻¹) * ((b : G) * (s⁻¹ * x) * (b : G)⁻¹) =
        s⁻¹ * ((b : G) * x * (b : G)⁻¹) by group] at h3)
  have hcA : c' ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : b * c' * b⁻¹ = c' := hcfix ⟨b, hb⟩
    calc b * c' = b * c' * b⁻¹ * b := by group
      _ = c' * b := by rw [h1]
  have hcU : c' ∈ U := by
    rw [show c' = s * (s⁻¹ * c') by group]
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hc')
  have hcX : c' ∈ xA A := hUAX ⟨hcU, hcA⟩
  rw [show s = c' * (s⁻¹ * c')⁻¹ by group]
  exact mul_mem (Subgroup.mem_sup_right hcX) (Subgroup.mem_sup_left (inv_mem hc'))

end Proof1413Res7

end CFSG.RankThree.PartTwo.Sec14
