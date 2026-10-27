module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTTools
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofX
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152ConfThetaLe (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype

@[expose] def Step152ConfThetaNorm (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
        ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal

@[expose] noncomputable def Step152ConfThetaLeR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfThetaLe A (lB A)

@[expose] noncomputable def Step152ConfThetaNormR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfThetaNorm A (lB A)

namespace Proof152ConfA

theorem le_theta_of_normal_sup {K P : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hn : ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal) :
    P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 K with hO
  have hOK : O ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hPO : P ≤ Subgroup.normalizer (O : Set G) :=
    hPK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  set N := P ⊔ O with hN
  have hNK : N ≤ K := sup_le hPK hOK
  have hNcard : Nat.card N ∣ Nat.card O * Nat.card P := by
    rw [hN, sup_comm]
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O P hPO
      (by
        rw [disjoint_iff]
        exact (Proof152ConfA.inf_eq_bot_of_isPGroup (p := p) hp2 hO2 hPp))
    rw [h]
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hO2
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hPp
    have h := h3.trans hNcard
    rw [ha, hb] at h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hNs : Group.IsSolvable N := by
    have hON : O ≤ N := le_sup_right
    have hOn : (O.subgroupOf N).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hON]
      exact sup_le hPO Subgroup.le_normalizer
    have : Group.IsNilpotent (O.subgroupOf N) :=
      (hO2.comap_subtype (K := N)).isNilpotent
    have hsurj : Function.Surjective ((QuotientGroup.mk' (O.subgroupOf N)).comp
        (Subgroup.inclusion (le_sup_left : P ≤ N))) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      have hy : (y : G) ∈ ((P ⊔ O : Subgroup G) : Set G) := y.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPO] at hy
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy
      refine ⟨⟨a, ha⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : ((Subgroup.inclusion (le_sup_left : P ≤ N) ⟨a, ha⟩)⁻¹ * y : N).val = b := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        rw [← hab]
        group
      rw [this]
      exact hb
    have : Group.IsNilpotent P := hPp.isNilpotent
    have : Group.IsSolvable (↥N ⧸ O.subgroupOf N) := Group.isSolvable_of_surjective hsurj
    exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion (le_refl _) |>.comp
      (O.subgroupOf N).subtype) (QuotientGroup.mk' (O.subgroupOf N)) (by
        intro x hx
        rw [QuotientGroup.ker_mk'] at hx
        exact ⟨⟨x, hx⟩, rfl⟩)
  have hle := Sec6.le_theta_of_normal hNK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hn) hNs hN3
  exact le_sup_left.trans hle

theorem PData152.ne_three
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G} {p : ℕ}
    {P : Subgroup G} (hctx : Ctx152 A LB Y M X) (hPd : PData152 A X p P) : p ≠ 3 := by
  rintro rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨R, hR, hPR, -⟩ := hPd.char_p
  have hPθ := le_theta_of_le_sylow (by norm_num) hXs hX60 hR hPR
  obtain ⟨-, hθ3⟩ := Sec6.theta_solvable_and_not_dvd X
  have hdvd : Nat.card P ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) X) :=
    Subgroup.card_dvd_of_le hPθ
  apply hθ3
  rcases hPd.type_p with ⟨-, h⟩ | ⟨-, h⟩
  · rw [h] at hdvd
    exact (dvd_pow_self 3 (by norm_num)).trans hdvd
  · rw [h] at hdvd
    exact (dvd_pow_self 3 (by norm_num)).trans hdvd

end Proof152ConfA

theorem step152ConfTheta_of {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hle : Step152ConfThetaLe A LB) (hnorm : Step152ConfThetaNorm A LB) :
    Step152ConfTheta A LB := fun Y M X c' L' p P T K S hpt hPd hTd hKd =>
  ⟨hle Y M X c' L' p P T K S hpt hPd hTd hKd,
    hnorm Y M X c' L' p P T K S hpt hPd hTd hKd (hle Y M X c' L' p P T K S hpt hPd hTd hKd)⟩

theorem step152ConfThetaR_of (hle : Step152ConfThetaLeR) (hnorm : Step152ConfThetaNormR) :
    Step152ConfThetaR :=
  fun G _ _ A c L hR => step152ConfTheta_of (hle G A c L hR) (hnorm G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
