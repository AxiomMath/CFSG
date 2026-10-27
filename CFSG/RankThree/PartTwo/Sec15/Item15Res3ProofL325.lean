module

public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofLA7
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofM22Gen
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515L325Image : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ _ : Fact (Nat.Prime 5),
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2)) →
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
    ∀ T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2),
      64 ∣ Nat.card (((T ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))

@[expose] def KL325SubgroupOrder : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (_ : Fact (Nat.Prime 5)),
    Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2)) →
    ∀ H : Subgroup X, 20160 ∣ Nat.card H → H = ⊤

namespace Proof15Res3L325

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_pCore_two_dvd {K Y : Subgroup G} (hKY : K ≤ Y)
    (hY : Y = K ⊔ CFSG.Open.pCoreOf 2 Y) :
    Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣ Nat.card K := by
  set g := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY) with hg
  have hKN : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) q
    have hy : (y : G) ∈ ((K ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hY]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN] at hy
    obtain ⟨k, hk, n, hn, hkn⟩ := Set.mem_mul.mp hy
    obtain ⟨n', hn', rfl⟩ := hn
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hyn : (Subgroup.inclusion hKY ⟨k, hk⟩)⁻¹ * y = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hkn, Subgroup.coe_subtype]
      group
    rw [hyn]
    exact hn'
  have h1 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = Nat.card (↥K ⧸ g.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgs).toEquiv).symm
  rw [h1]
  exact Subgroup.card_quotient_dvd_card _

theorem odd_dvd_card_map {L K : Subgroup G} (hKL : K ≤ L) {N : Subgroup ↥L} [N.Normal]
    (hN : IsPGroup 2 N) {m : ℕ} (hm : Nat.Coprime m 2) (hmK : m ∣ Nat.card K) :
    m ∣ Nat.card ((K.subgroupOf L).map (QuotientGroup.mk' N)) := by
  set f := (QuotientGroup.mk' N).comp (Subgroup.inclusion hKL) with hf
  have hrange : f.range = (K.subgroupOf L).map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hK : Nat.card K = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hker : Nat.card f.ker ∣ Nat.card N := by
    have hmap : f.ker.map (Subgroup.inclusion hKL) ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKL)]
    exact Subgroup.card_dvd_of_le hmap
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  rw [hn] at hker
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hker
  rw [hK, hk] at hmK
  rw [← hrange]
  exact (Nat.Coprime.pow_right k hm).dvd_of_dvd_mul_right hmK

end Proof15Res3L325

open Proof15Res3L325 Proof1515 Proof1515Res

theorem step1515LA7L325Gen_of
    (h135 : Item135) (h142 : Item142R) (h1511 : Item1511R)
    (himg : Step1515L325Image) (hK : KL325SubgroupOrder) : Step1515LA7L325Gen := by
  intro G _ _ A c L h hΩ Y hY hm hYL hY7 hf5 hL25 T hT
  obtain ⟨φY⟩ := hY7
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hiso : Sec4.IsoLThreePi (↥L ⧸ θ) 5 2 := Or.inl ⟨by norm_num, hL25⟩
  have hL3 : IsLThreePi (↥L ⧸ θ) := ⟨5, 2, hf5, by norm_num, hiso⟩
  have hAHY : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) :=
    le_inf (hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
      hY.prop.1.1.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le hAHY hA3
  obtain ⟨hprod, -⟩ := h1511 G A c L h 5 2 (by norm_num) hiso Y hY.prop hm P hAP hP
  have hθ : θ = CFSG.pCore 2 ↥L :=
    Sec19.theta_eq_pCore_two_of_mult KFacts.KS14.ks18Mult (h135 G A c L hD h.hypS_or_hypT)
      (Or.inl hL3)
  have h3L : 3 ∣ Nat.card L :=
    (Proof1514.three_dvd_card_inf_of_meetsY4 hm).trans (Subgroup.card_dvd_of_le inf_le_left)
  have hOT := pCoreOf_two_le_of_mem_scriptQPiStar h (h142 G A c L h) h3L hT
  have hθT : θ ≤ (T ⊓ L).subgroupOf L := by
    intro x hx
    rw [hθ] at hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hOT ⟨x, hx, rfl⟩, x.2⟩
  have hθ2 : IsPGroup 2 θ := by
    rw [hθ]
    exact CFSG.pCore_isPGroup
  set X := ((L ⊓ Y).subgroupOf L).map π with hX
  have hYL' : Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := hYL
  have h2520 : 2520 ∣ Nat.card (L ⊓ Y : Subgroup G) := by
    have := card_quot_pCore_two_dvd (inf_le_right : L ⊓ Y ≤ Y) hYL'
    rwa [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven] at this
  have hX315 : 315 ∣ Nat.card X :=
    odd_dvd_card_map inf_le_left hθ2 (by norm_num) ((by norm_num : 315 ∣ 2520).trans h2520)
  set R := ((T ⊓ L).subgroupOf L).map π with hR
  have hR64 : 64 ∣ Nat.card R := himg G A c L h hf5 hL25 hprod T hT
  have htop : R ⊔ X = ⊤ := by
    refine hK _ hf5 hL25 _ ?_
    have h64 : 64 ∣ Nat.card (R ⊔ X : Subgroup (↥L ⧸ θ)) :=
      hR64.trans (Subgroup.card_dvd_of_le le_sup_left)
    have h315 : 315 ∣ Nat.card (R ⊔ X : Subgroup (↥L ⧸ θ)) :=
      hX315.trans (Subgroup.card_dvd_of_le le_sup_right)
    exact (show (20160 : ℕ) = 64 * 315 by norm_num) ▸
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h315
  set M := ((T ⊓ L) ⊔ (L ⊓ Y)).subgroupOf L with hM
  have hMtop : M = ⊤ := by
    have h1 : R ⊔ X ≤ M.map π := sup_le
      (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
      (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
    have h2 : M.map π = ⊤ := top_le_iff.mp (htop ▸ h1)
    have h3 := Subgroup.comap_map_eq π M
    rw [h2, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h3
    have hθM : θ ≤ M := hθT.trans fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    rw [sup_eq_left.mpr hθM] at h3
    exact h3.symm
  intro l hl
  have hlM : (⟨l, hl⟩ : ↥L) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hlM

end CFSG.RankThree.PartTwo.Sec15
