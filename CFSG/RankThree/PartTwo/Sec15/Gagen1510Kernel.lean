module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1510Setup
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem pow_mem_sectionCentralizer {P L : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) {k : G}
    (hk : k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L)) (m : ℕ) :
    k ^ m ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) := by
  have hkP : k ∈ P := hk.1
  have hkPm : k ^ m ∈ P := P.pow_mem hkP m
  have hkN : k ∈ Subgroup.normalizer (L : Set G) := hPN hkP
  have hkNm : k ^ m ∈ Subgroup.normalizer (L : Set G) := hPN hkPm
  refine (mem_sectionCentralizer_iff hkNm).mpr ⟨hkPm, ?_⟩
  have hkey : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨k ^ m, hkNm⟩) =
      (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨k, hkN⟩)) ^ m := by
    rw [show (⟨k ^ m, hkNm⟩ : Subgroup.normalizer (L : Set G)) = ⟨k, hkN⟩ ^ m from
      Subtype.ext rfl]
    rw [map_pow, map_pow]
  rw [hkey, (mem_sectionCentralizer_iff hkN).mp hk |>.2, one_pow]

private theorem pow_three_mem_sectionCentralizer {P L : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hP3 : IsPGroup 3 P)
    (hexp : ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      IsPGroup 3 (Subgroup.zpowers α) → α ^ 3 = 1)
    {u : G} (hu : u ∈ P) :
    u ^ 3 ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) := by
  let η : P →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  let ρ : P →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) := (Sec4.thetaQuotMulAut ↥L).comp η
  have h3 : IsPGroup 3 (Subgroup.zpowers (ρ ⟨u, hu⟩)) := by
    have h := IsPGroup.map (hP3.to_subgroup (Subgroup.zpowers (⟨u, hu⟩ : P))) ρ
    rwa [MonoidHom.map_zpowers] at h
  have hcube : ρ ⟨u, hu⟩ ^ 3 = 1 := hexp (ρ ⟨u, hu⟩) h3
  have hu3P : u ^ 3 ∈ P := P.pow_mem hu 3
  refine (mem_sectionCentralizer_iff (hPN hu3P)).mpr ⟨hu3P, ?_⟩
  change ρ ⟨u ^ 3, hu3P⟩ = 1
  have hp : (⟨u, hu⟩ : P) ^ 3 = ⟨u ^ 3, hu3P⟩ := Subtype.ext rfl
  have h2 : ρ ⟨u ^ 3, hu3P⟩ = ρ ⟨u, hu⟩ ^ 3 := by
    rw [← hp, map_pow]
  rw [h2, hcube]

private theorem le_normalizer_of_le_centralizer {B L P : Subgroup G} {c : G}
    (hcB : c ∈ B) (hPB : P ≤ Subgroup.centralizer (B : Set G))
    (hC : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    P ≤ Subgroup.normalizer (L : Set G) :=
  hPB.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)).trans hC)

private theorem inf_theta_eq_bot {L P : Subgroup G} (hP3 : IsPGroup 3 P) :
    P ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ :=
  Proof1510Steps.inf_eq_bot_of_coprime hP3 (Proof1510Steps.not_three_dvd_card_theta L)

private theorem pow_orderOf_div_three {P L : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hP3 : IsPGroup 3 P) {g : G} (hgP : g ∈ P)
    (hg1 : g ≠ 1)
    (hgK : g ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L)) :
    orderOf (g ^ (orderOf g / 3)) = 3 ∧
      g ^ (orderOf g / 3) ∈
        Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hP3.exists_orderOf_eq_pow (⟨g, hgP⟩ : P)
  have hord : orderOf g = 3 ^ n := by
    rw [← Subgroup.orderOf_mk g hgP]
    exact hn
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hord
      exact hg1 (orderOf_eq_one_iff.mp hord)
    · exact hpos
  refine ⟨?_, pow_mem_sectionCentralizer hPN hgK _⟩
  exact orderOf_pow_orderOf_div (by rw [hord]; exact pow_ne_zero n (by norm_num))
    (by rw [hord]; exact dvd_pow_self 3 (Nat.ne_of_gt hnpos))

private theorem mem_zpowers_of_mem_sectionCentralizer {A L P B : Subgroup G} {c : G}
    (hA : A ∈ partTwoF G) (hAP : A ≤ P) (hcB : c ∈ B) (hPB : P ≤ Subgroup.centralizer (B : Set G))
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hPθ : P ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥)
    (hsc : Late.sectionCentralizer A L (inSubgroup (aschbacherSolvableCore 3) L) =
      (Subgroup.zpowers c : Set G))
    {k : G} (hk : k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L))
    (hk3 : k ^ 3 = 1) :
    k ∈ Subgroup.zpowers c := by
  have hkA : k ∈ A := by
    refine mem_of_mem_partTwoF hA hk3 ?_
    rw [hAeq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hPB hk.1) c hcB
    · intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hmem : k * s * k⁻¹ * s⁻¹ ∈ P ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
        ⟨P.mul_mem (P.mul_mem (P.mul_mem hk.1 (hAP hs.1)) (P.inv_mem hk.1))
          (P.inv_mem (hAP hs.1)), hk.2 s hs.2⟩
      rw [hPθ, Subgroup.mem_bot] at hmem
      have h1 : k * s * k⁻¹ = s := by
        calc k * s * k⁻¹ = (k * s * k⁻¹ * s⁻¹) * s := by group
          _ = s := by rw [hmem, one_mul]
      have h2 : k * s = s * k := by
        calc k * s = (k * s * k⁻¹) * k := by group
          _ = s * k := by rw [h1]
      exact h2.symm
  have hkSC : k ∈ Late.sectionCentralizer A L (inSubgroup (aschbacherSolvableCore 3) L) :=
    ⟨hkA, hk.2⟩
  rwa [hsc] at hkSC

private theorem zpowers_eq_zpowers_c {A L P B : Subgroup G} {c k : G}
    (hA : A ∈ partTwoF G) (hAP : A ≤ P) (hcB : c ∈ B)
    (hPB : P ≤ Subgroup.centralizer (B : Set G))
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hPθ : P ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥)
    (hsc : Late.sectionCentralizer A L (inSubgroup (aschbacherSolvableCore 3) L) =
      (Subgroup.zpowers c : Set G))
    (hcz : orderOf c = 3)
    (hk : k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L))
    (hkord : orderOf k = 3) :
    Subgroup.zpowers k = Subgroup.zpowers c := by
  have hk3 : k ^ 3 = 1 := by
    rw [← hkord]
    exact pow_orderOf_eq_one k
  refine Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr
      (mem_zpowers_of_mem_sectionCentralizer hA hAP hcB hPB hAeq hPθ hsc hk hk3)) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hkord, hcz]

private theorem pow_three_eq_one {A L P B : Subgroup G} {c : G}
    (hA : A ∈ partTwoF G) (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hsc : Late.sectionCentralizer A L (inSubgroup (aschbacherSolvableCore 3) L) =
      (Subgroup.zpowers c : Set G))
    (hcz : orderOf c = 3)
    (hP3 : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hPθ : P ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥)
    (hAP : A ≤ P) (hcB : c ∈ B) (hPB : P ≤ Subgroup.centralizer (B : Set G))
    {x : G} (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hxc : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ≠ Subgroup.zpowers c)
    (hexp : ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      IsPGroup 3 (Subgroup.zpowers α) → α ^ 3 = 1) :
    ∀ u ∈ P, u ^ 3 = 1 := by
  intro u hu
  by_contra hu3
  have hmem : u ^ 3 ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) :=
    pow_three_mem_sectionCentralizer hPN hP3 hexp hu
  have h3 := pow_orderOf_div_three hPN hP3 (P.pow_mem hu 3) hu3 hmem
  have hzw : Subgroup.zpowers ((u ^ 3) ^ (orderOf (u ^ 3) / 3)) = Subgroup.zpowers c :=
    zpowers_eq_zpowers_c hA hAP hcB hPB hAeq hPθ hsc hcz h3.2 h3.1
  have hyP : x * u * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxP u).mp hu
  have hy3eq : (x * u * x⁻¹) ^ 3 = x * u ^ 3 * x⁻¹ := by
    rw [show x * u * x⁻¹ = (MulAut.conj x).toMonoidHom u by simp, ← map_pow]
    simp
  have hy3ne : (x * u * x⁻¹) ^ 3 ≠ 1 := by
    rw [hy3eq]
    intro h1
    exact hu3 (by
      calc u ^ 3 = x⁻¹ * (x * u ^ 3 * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group)
  have horde : orderOf ((x * u * x⁻¹) ^ 3) = orderOf (u ^ 3) := by
    rw [hy3eq]
    exact MulEquiv.orderOf_eq (MulAut.conj x) (u ^ 3)
  have hy3mem : (x * u * x⁻¹) ^ 3 ∈
      Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) :=
    pow_three_mem_sectionCentralizer hPN hP3 hexp hyP
  have h3' := pow_orderOf_div_three hPN hP3 (P.pow_mem hyP 3) hy3ne hy3mem
  have hw'mem : ((x * u * x⁻¹) ^ 3) ^ (orderOf (u ^ 3) / 3) ∈
      Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [← horde]
    exact h3'.2
  have hw'3 : orderOf (((x * u * x⁻¹) ^ 3) ^ (orderOf (u ^ 3) / 3)) = 3 := by
    rw [← horde]
    exact h3'.1
  have hzw' : Subgroup.zpowers (((x * u * x⁻¹) ^ 3) ^ (orderOf (u ^ 3) / 3)) =
      Subgroup.zpowers c :=
    zpowers_eq_zpowers_c hA hAP hcB hPB hAeq hPθ hsc hcz hw'mem hw'3
  have hconj : ((x * u * x⁻¹) ^ 3) ^ (orderOf (u ^ 3) / 3) =
      x * ((u ^ 3) ^ (orderOf (u ^ 3) / 3)) * x⁻¹ := by
    rw [hy3eq, show x * u ^ 3 * x⁻¹ = (MulAut.conj x).toMonoidHom (u ^ 3) by simp, ← map_pow]
    simp
  have hmap : Subgroup.zpowers (((x * u * x⁻¹) ^ 3) ^ (orderOf (u ^ 3) / 3)) =
      (Subgroup.zpowers ((u ^ 3) ^ (orderOf (u ^ 3) / 3))).map
        (MulAut.conj x).toMonoidHom := by
    rw [MonoidHom.map_zpowers, hconj]
    congr 1
  rw [hmap, hzw] at hzw'
  exact hxc hzw'

theorem exponent_and_kernel {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hall : All1510 A) {B : Subgroup G} (hcB : c ∈ B) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G))) (hAP : A ≤ P)
    {x : G} (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hxc : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ≠ Subgroup.zpowers c)
    (hexp : ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      IsPGroup 3 (Subgroup.zpowers α) → α ^ 3 = 1) :
    (∀ u ∈ P, u ^ 3 = 1) ∧
      ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
        k ∈ Subgroup.zpowers c := by
  have hD := h.toSec13Data
  obtain ⟨-, -, -, hAeq, hC⟩ := setting h hall
  have hPN : P ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_le_centralizer hcB hP.le hC
  have hPθ : P ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := inf_theta_eq_bot hP.isPGroup
  have hexp3 : ∀ u ∈ P, u ^ 3 = 1 :=
    pow_three_eq_one hD.mem_partTwoF hAeq hD.sectionCentralizer_eq hD.orderOf_eq hP.isPGroup
      hPN hPθ hAP hcB hP.le hxP hxc hexp
  refine ⟨hexp3, fun k hk => ?_⟩
  exact mem_zpowers_of_mem_sectionCentralizer hD.mem_partTwoF hAP hcB hP.le hAeq hPθ
    hD.sectionCentralizer_eq hk (hexp3 k hk.1)

private theorem isPGroup_autThetaQuot_of_isPGroup {P L : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hP3 : IsPGroup 3 P) :
    IsPGroup 3 (Sec4.autThetaQuot P L) := by
  let η : P →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  let ρ : P →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) := (Sec4.thetaQuotMulAut ↥L).comp η
  have hρapply : ∀ (g : G) (hg : g ∈ P), ρ ⟨g, hg⟩ =
      Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨g, hPN hg⟩) := fun _ _ => rfl
  rw [isPGroup_iff_pow_pow_eq_one]
  intro σ
  obtain ⟨g, hgN, hgP, hσ⟩ := Sec4.mem_autThetaQuot_iff.mp σ.2
  rw [isPGroup_iff_pow_pow_eq_one] at hP3
  obtain ⟨n, hn⟩ := hP3 ⟨g, hgP⟩
  refine ⟨n, Subtype.ext ?_⟩
  show (σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ^ 3 ^ n = 1
  rw [← hσ]
  rw [show (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) = ⟨g, hPN hgP⟩ from Subtype.ext rfl,
    ← hρapply g hgP, ← map_pow, show (⟨g, hgP⟩ : P) ^ 3 ^ n = 1 from hn, map_one]

private theorem conj_basic {A B P : Subgroup G} {x c : G}
    (hAP : A ≤ P) (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hB : IsHyperplane A B) (hxB : x ∈ Subgroup.normalizer (B : Set G)) (hcB : c ∈ B)
    (hAcard : Nat.card A = 27) (hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) :
    A.map (MulAut.conj x⁻¹).toMonoidHom ≤ P ∧
      B ≤ A.map (MulAut.conj x⁻¹).toMonoidHom ∧
      c ∈ A.map (MulAut.conj x⁻¹).toMonoidHom ∧
      Nat.card (A.map (MulAut.conj x⁻¹).toMonoidHom) = 27 ∧
      (∀ u ∈ A.map (MulAut.conj x⁻¹).toMonoidHom,
        ∀ v ∈ A.map (MulAut.conj x⁻¹).toMonoidHom, u * v = v * u) := by
  have hHP : A.map (MulAut.conj x⁻¹).toMonoidHom ≤ P := by
    have h1 : P.map (MulAut.conj x⁻¹).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hxP)
    calc A.map (MulAut.conj x⁻¹).toMonoidHom ≤ P.map (MulAut.conj x⁻¹).toMonoidHom :=
          Subgroup.map_mono hAP
      _ = P := h1
  have hBH : B ≤ A.map (MulAut.conj x⁻¹).toMonoidHom := by
    have h1 : B.map (MulAut.conj x⁻¹).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hxB)
    calc B = B.map (MulAut.conj x⁻¹).toMonoidHom := h1.symm
      _ ≤ A.map (MulAut.conj x⁻¹).toMonoidHom := Subgroup.map_mono hB.1
  refine ⟨hHP, hBH, hBH hcB, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hAcard]
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_mul, ← map_mul, hAcomm u' hu' v' hv']

private theorem card_autThetaQuot_conj {A L H P : Subgroup G} {c : G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hHN : H ≤ Subgroup.normalizer (L : Set G))
    (hsc : Late.sectionCentralizer A L (inSubgroup (aschbacherSolvableCore 3) L) =
      (Subgroup.zpowers c : Set G))
    (hHcard : Nat.card H = 27) (hcH : c ∈ H) (hHP : H ≤ P)
    (hcz : Nat.card (Subgroup.zpowers c) = 3)
    (hK : ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
      k ∈ Subgroup.zpowers c) :
    Nat.card (Sec4.autThetaQuot H L) = 9 := by
  have hcθ : c ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : c ∈ (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
      change c ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G)
      rw [← Sec13.sectionCentralizer_eq_inf hAN]
      change c ∈ Late.sectionCentralizer A L (inSubgroup (aschbacherSolvableCore 3) L)
      rw [hsc]
      exact Subgroup.mem_zpowers c
    exact h1.2
  have hinf : H ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    refine le_antisymm ?_ ?_
    · intro g hg
      have hgSC : g ∈ Late.sectionCentralizer H L (inSubgroup (aschbacherSolvableCore 3) L) := by
        change g ∈ Late.sectionCentralizer H L ((aschbacherSolvableCore 3 ↥L).map L.subtype)
        rw [Sec13.sectionCentralizer_eq_inf hHN]
        exact hg
      exact hK g ⟨hHP hgSC.1, hgSC.2⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨hcH, hcθ⟩
  have hcardinf : Nat.card (H ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    rw [hinf, hcz]
  have h1 := Sec13.card_inf_mul_card_autThetaQuot (A := H) (L := L) hHN
  rw [hcardinf, hHcard] at h1
  omega

private theorem conj_mem_autThetaQuot {L H : Subgroup G} {b : G}
    {β : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hbH : b ∈ H)
    (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hβeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨b, hbN⟩) = β) :
    β ∈ Sec4.autThetaQuot H L :=
  Sec4.mem_autThetaQuot_iff.mpr ⟨b, hbN, hbH, hβeq⟩

private theorem autThetaQuot_le_centralizer_conj {L H : Subgroup G} {b : G}
    {β : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)} (hbH : b ∈ H)
    (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hβeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨b, hbN⟩) = β)
    (hHcomm : ∀ u ∈ H, ∀ v ∈ H, u * v = v * u) :
    Sec4.autThetaQuot H L ≤ Subgroup.centralizer {β} := by
  intro τ hτ
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨g, hgN, hgH, hgτ⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  rw [← hgτ, ← hβeq]
  simp only [← map_mul]
  rw [show (⟨g, hgN⟩ * ⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) =
    ⟨b, hbN⟩ * ⟨g, hgN⟩ from Subtype.ext (hHcomm g hgH b hbH)]

private theorem comap_autThetaQuot_eq_image {A L P : Subgroup G}
    (hAP : A ≤ P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hPN3 : IsPGroup 3 (Sec4.autThetaQuot P L))
    (hconj_inj : Function.Injective (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hsyl : ∀ Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsPGroup 3 Q → Nat.card Q ∣ 9) :
    (Sec4.autThetaQuot P L).comap (MulAut.conj :
        (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) =
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
  set Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec4.autThetaQuot P L).comap (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    with hQdef
  set Sbar : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) with hSbardef
  have hQ3 : IsPGroup 3 Q := hPN3.comap_of_injective _ hconj_inj
  have hQ9 : Nat.card Q ∣ 9 := hsyl Q hQ3
  have hSbar9 : Nat.card Sbar = 9 :=
    Proof1510Steps.card_map_mk_of_card_nine (L := L) (S := A ⊓ L) inf_le_right h9
  have hSbarQ : Sbar ≤ Q := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyS : (y : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hy
    have hyP : (y : G) ∈ P := hAP hyS.1
    have hyN : (y : G) ∈ Subgroup.normalizer (L : Set G) := hPN hyP
    change MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) y) ∈
      Sec4.autThetaQuot P L
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨(y : G), hyN, hyP,
      KFacts.thetaQuotMulAut_compAction_of_mem y.2 hyN⟩
  have h9dvd : 9 ∣ Nat.card Q := hSbar9 ▸ Subgroup.card_dvd_of_le hSbarQ
  have hQcard : Nat.card Q = 9 := Nat.dvd_antisymm hQ9 h9dvd
  exact (Subgroup.eq_of_le_of_card_ge hSbarQ (by rw [hQcard, hSbar9])).symm

private theorem le_of_isInner_autThetaQuot {A L P H : Subgroup G} {c : G}
    (hAP : A ≤ P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hcA : c ∈ A) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hHP : H ≤ P)
    (hPN3 : IsPGroup 3 (Sec4.autThetaQuot P L))
    (hconj_inj : Function.Injective (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hinner : ∀ τ ∈ Sec4.autThetaQuot H L,
      τ ∈ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range)
    (hK : ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
      k ∈ Subgroup.zpowers c)
    (hsyl : ∀ Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsPGroup 3 Q → Nat.card Q ∣ 9) :
    H ≤ A := by
  let η : P →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  let ρ : P →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) := (Sec4.thetaQuotMulAut ↥L).comp η
  have hρapply : ∀ (g : G) (hg : g ∈ P), ρ ⟨g, hg⟩ =
      Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨g, hPN hg⟩) := fun _ _ => rfl
  have hQeq := comap_autThetaQuot_eq_image hAP hPN h9 hPN3 hconj_inj hsyl
  intro a ha
  have haP : a ∈ P := hHP ha
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hPN haP
  have haM : ρ ⟨a, haP⟩ ∈ Sec4.autThetaQuot H L := by
    rw [hρapply a haP]
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, ha, rfl⟩
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hinner _ haM)
  have hzS : z ∈ ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
    rw [← hQeq]
    change MulAut.conj z ∈ Sec4.autThetaQuot P L
    rw [hz]
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, haP, rfl⟩
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzS
  have hyS : (y : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hy
  have hyP : (y : G) ∈ P := hAP hyS.1
  have hmemP : (y : G)⁻¹ * a ∈ P := P.mul_mem (P.inv_mem hyP) haP
  have hρy : ρ ⟨(y : G), hyP⟩ = ρ ⟨a, haP⟩ := by
    have hstep : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨(y : G), hPN hyP⟩) =
        MulAut.conj z := by
      change Sec4.thetaQuotMulAut ↥L ((Sec4.compAction L) ⟨(y : G), hPN hyP⟩) = MulAut.conj z
      rw [KFacts.thetaQuotMulAut_compAction_of_mem y.2 (hPN hyP)]
      exact congrArg MulAut.conj hyz
    rw [hρapply (y : G) hyP, hstep]
    exact hz
  have hρ1 : ρ ⟨(y : G)⁻¹ * a, hmemP⟩ = 1 := by
    have hsplit : (⟨(y : G)⁻¹ * a, hmemP⟩ : P) = (⟨(y : G), hyP⟩)⁻¹ * ⟨a, haP⟩ :=
      Subtype.ext rfl
    rw [hsplit, map_mul, map_inv, hρy, inv_mul_cancel]
  have hk : (y : G)⁻¹ * a ∈
      Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) :=
    (mem_sectionCentralizer_iff (hPN hmemP)).mpr ⟨hmemP, hρ1⟩
  have hzc : (y : G)⁻¹ * a ∈ Subgroup.zpowers c := hK _ hk
  have heq : a = (y : G) * ((y : G)⁻¹ * a) := by group
  rw [heq]
  exact A.mul_mem (Subgroup.mem_inf.mp hyS).1 (Subgroup.zpowers_le.mpr hcA hzc)

private theorem exists_outer_autThetaQuot {A L P H : Subgroup G} {c : G}
    (hne : H ≠ A) (hAcard : Nat.card A = 27) (hHcard : Nat.card H = 27)
    (hAP : A ≤ P) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hcA : c ∈ A) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hHP : H ≤ P)
    (hPN3 : IsPGroup 3 (Sec4.autThetaQuot P L))
    (hconj_inj : Function.Injective (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hK : ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
      k ∈ Subgroup.zpowers c)
    (hsyl : ∀ Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsPGroup 3 Q → Nat.card Q ∣ 9) :
    ∃ α ∈ Sec4.autThetaQuot H L,
      α ∉ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range := by
  by_contra hcon
  have hinner : ∀ τ ∈ Sec4.autThetaQuot H L,
      τ ∈ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range := by
    intro τ hτ
    by_contra hτout
    exact hcon ⟨τ, hτ, hτout⟩
  have hHA : H ≤ A :=
    le_of_isInner_autThetaQuot hAP hPN hcA h9 hHP hPN3 hconj_inj hinner hK hsyl
  exact hne (Subgroup.eq_of_le_of_card_ge hHA (by rw [hAcard, hHcard]))

theorem autThetaQuot_conj_props {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hall : All1510 A) {B : Subgroup G} (hB : IsHyperplane A B) (hcB : c ∈ B) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G))) (hAP : A ≤ P)
    {x : G} (hx : x ∈ Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G))
    (hK : ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
      k ∈ Subgroup.zpowers c)
    (hsyl : ∀ Q : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsPGroup 3 Q → Nat.card Q ∣ 9)
    {b : G} (hbB : b ∈ B) (hbL : b ∈ L)
    (hne : A.map (MulAut.conj x⁻¹).toMonoidHom ≠ A) :
    Nat.card (Sec4.autThetaQuot (A.map (MulAut.conj x⁻¹).toMonoidHom) L) = 9 ∧
      MulAut.conj ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈
        Sec4.autThetaQuot (A.map (MulAut.conj x⁻¹).toMonoidHom) L ∧
      Sec4.autThetaQuot (A.map (MulAut.conj x⁻¹).toMonoidHom) L ≤
        Subgroup.centralizer
          {MulAut.conj ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)} ∧
      ∃ α ∈ Sec4.autThetaQuot (A.map (MulAut.conj x⁻¹).toMonoidHom) L,
        α ∉ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
          MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range := by
  have hD := h.toSec13Data
  obtain ⟨⟨χ⟩, h9, -, -, hC⟩ := setting h hall
  have hPN : P ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_le_centralizer hcB hP.le hC
  obtain ⟨hHP, hBH, -, hHcard, hHcomm⟩ :=
    conj_basic hAP hx.2 hB hx.1 hcB hD.card_eq (fun u hu v hv => hD.commute hu hv)
  have hHN : A.map (MulAut.conj x⁻¹).toMonoidHom ≤ Subgroup.normalizer (L : Set G) :=
    hHP.trans hPN
  have hPN3 : IsPGroup 3 (Sec4.autThetaQuot P L) :=
    isPGroup_autThetaQuot_of_isPGroup hPN hP.isPGroup
  have hconj_inj : Function.Injective
      (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [← MonoidHom.ker_eq_bot_iff (MulAut.conj :
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
      eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzc : z ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := congrArg (fun f : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) => f w) hz
      simp only [MulAut.one_apply, MulAut.conj_apply] at h
      calc w * z = (z * w * z⁻¹) * z := by rw [h]
        _ = z * w := by group
    rw [center_eq_bot_of_mulEquiv χ, Subgroup.mem_bot] at hzc
    exact hzc
  have hbH : b ∈ A.map (MulAut.conj x⁻¹).toMonoidHom := hBH hbB
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer (hB.1 hbB)
  have hβeq : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨b, hbN⟩) =
      MulAut.conj ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    KFacts.thetaQuotMulAut_compAction_of_mem hbL hbN
  exact ⟨card_autThetaQuot_conj hD.le_normalizer hHN hD.sectionCentralizer_eq hHcard
      (hBH hcB) hHP hD.card_zpowers hK,
    conj_mem_autThetaQuot hbH hbN hβeq,
    autThetaQuot_le_centralizer_conj hbH hbN hβeq hHcomm,
    exists_outer_autThetaQuot hne hD.card_eq hHcard hAP hPN hD.mem_A h9 hHP hPN3 hconj_inj hK hsyl⟩

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse
