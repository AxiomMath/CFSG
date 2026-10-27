module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofM22Gen
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1515

variable {G : Type} [Group G] [Finite G]

theorem le_of_mem_scriptQPiStar {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h142 : Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A) {T U : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2))
    (hU2 : IsPGroup 2 U) (hUH : U ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  obtain ⟨⟨hTq, hTH⟩, hT2⟩ := hT.prop
  have hT2' : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT2
  have hTU2 : IsPGroup 2 (T ⊔ U : Subgroup G) := IsPGroup.to_sup_of_normal_right' hT2' hU2 hTU
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTq.1.2.2
  have hATU : A ≤ Subgroup.normalizer ((T ⊔ U : Subgroup G) : Set G) :=
    le_normalizer_sup hAT hAU
  have hTUH : T ⊔ U ≤ H := sup_le hTH hUH
  have h3' : ¬ 3 ∣ Nat.card (T ⊔ U : Subgroup G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTU2
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hinv : T ⊔ U ∈ invariantPiSubgroups H A (piCompl 3) :=
    (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mpr ⟨hTUH, h3', hATU⟩
  obtain ⟨Q, hQle, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hinv
  let := ker142_normal (LB := lB A) h.isElemAbelian.1 h.mem_A
  obtain ⟨hQq, -⟩ := h142 Q hQ
  have hTUq : T ⊔ U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQq.1 hQle hATU
  have hmem : T ⊔ U ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨hTUq, hTUH⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hTU2⟩
  have heq := hT.eq_of_ge hmem le_sup_left
  rw [← heq]
  exact le_sup_right

theorem conj_injective_of_center_trivial {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : g * z * g⁻¹ = z := by
      have := congrArg (fun φ : MulAut Q => φ z) hg
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc z * g = g * z * g⁻¹ * g := by rw [hz]
      _ = g * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem center_eq_bot_of_mulEquiv_M22
    {Q : Type*} [Group Q]
    (φ : Q ≃* CFSG.Blueprint.NativeSporadic.M22) : Subgroup.center Q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : φ z ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.M22 := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro m
    obtain ⟨g, rfl⟩ := φ.surjective m
    rw [← map_mul, ← map_mul, hz g]
  rw [CFSG.Sporadic.Schreier.m22_center_eq_bot', Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact φ.injective (hz'.trans φ.map_one.symm)

theorem thetaQuotMulAut_normalizerMonoidHom_of_mem {L : Subgroup G} {a : G} (haL : a ∈ L)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨a, haN⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨a, haL⟩) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg (fun y : ↥L => (y : ↥L ⧸ aschbacherSolvableCore 3 ↥L))
      (Subtype.ext (Sec4.normalizerMonoidHom_apply_coe haN x))

end Proof1515

open Proof1515

theorem ks15M22GenImage_of
    (h142 : Item142R) (h131 : Item131) (h135 : Item135) :
    KS15M22GenImage := by
  intro G _ _ A c L h hL22 T hT
  obtain ⟨φL⟩ := hL22
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hL443 : Nat.card (↥L ⧸ θ) = 443520 := by
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_thetaQuot (by rw [hL443]; norm_num)
  have : Nontrivial (↥L ⧸ θ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hL443]
    norm_num
  have : Nontrivial CFSG.Blueprint.NativeSporadic.M22 := φL.symm.surjective.nontrivial
  have hθ : θ = CFSG.pCore 2 ↥L :=
    theta_eq_pCore_two_of_multFree (h135 G A c L h.toSec13Data h.hypS_or_hypT) ⟨φL⟩ multFree_M22
  obtain ⟨-, h9, -⟩ := facts_of_a7_or_m22 h131 h (Or.inr ⟨φL⟩)
  set B := ((A ⊓ L).subgroupOf L).map π with hB
  have hBp : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hB'p : IsPGroup 3 ((A ⊓ L).subgroupOf L) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hB9 : Nat.card B = 9 := by
    rw [← Nat.card_congr (mkEquivOfIsPGroup hB'p).toEquiv, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  set N := Subgroup.normalizer (L : Set G) with hN
  set ψ : N →* MulAut (↥L ⧸ θ) := (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom with hψ
  have hψL : ∀ (a : G) (haL : a ∈ L) (haN : a ∈ N), ψ ⟨a, haN⟩ = MulAut.conj (π ⟨a, haL⟩) :=
    fun _ haL haN => thetaQuotMulAut_normalizerMonoidHom_of_mem haL haN
  have hψπ : ∀ (t : G) (htN : t ∈ N) (x : ↥L),
      ψ ⟨t, htN⟩ (π x) = π (L.normalizerMonoidHom ⟨t, htN⟩ x) := fun _ _ _ => rfl
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hHL : H ≤ N := Sec16.normalizer_zpowers_le_normalizer_L h h3L
  have hLH : L ≤ H := (le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1).trans
    (centralizer_singleton_le_normalizer_zpowers c)
  obtain ⟨⟨hTq, hTH⟩, hT2⟩ := hT.prop
  have hTN : T ≤ N := hTH.trans hHL
  have hT2' : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTq.1.2.2
  have hAN : A ≤ N := h.toSec13Data.le_normalizer
  set P := (T.subgroupOf N).map ψ with hP
  have hP2 : IsPGroup 2 P := (hT2'.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map ψ
  have hP3 : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hTnorm : ∀ a ∈ A, ∀ haN : a ∈ N,
      (⟨a, haN⟩ : N) ∈ Subgroup.normalizer ((T.subgroupOf N : Subgroup N) : Set N) := by
    intro a ha haN
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hAT ha) y
  have hPB : B.map (MulAut.conj : ↥L ⧸ θ →* MulAut (↥L ⧸ θ)) ≤
      Subgroup.normalizer (P : Set (MulAut (↥L ⧸ θ))) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have haA : (a : G) ∈ A := (Subgroup.mem_subgroupOf.mp ha).1
    have haN : (a : G) ∈ N := hAN haA
    have h1 : MulAut.conj (π a) = ψ ⟨a, haN⟩ := (hψL a a.2 haN).symm
    rw [h1]
    exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ (hTnorm a haA haN))
  have hPinn : P ≤ (MulAut.conj : ↥L ⧸ θ →* MulAut (↥L ⧸ θ)).range :=
    KFacts.KP4.m22_aut_threePrime_le_range ⟨φL⟩ hB9 hP3 hPB
  have hinj := conj_injective_of_center_trivial (center_eq_bot_of_mulEquiv_M22 φL)
  set Pb := P.comap (MulAut.conj : ↥L ⧸ θ →* MulAut (↥L ⧸ θ)) with hPb
  have hPb2 : IsPGroup 2 Pb := hP2.comap_of_injective _ hinj
  have hPbB : B ≤ Subgroup.normalizer (Pb : Set (↥L ⧸ θ)) :=
    (Subgroup.map_le_iff_le_comap.mp hPB).trans (Subgroup.le_normalizer_comap _)
  have hPb3 : ¬ 3 ∣ Nat.card Pb := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPb2
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hPbinv : Pb ∈ invariantPiSubgroups ⊤ B (piCompl 3) :=
    (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mpr ⟨le_top, hPb3, hPbB⟩
  obtain ⟨Rb, hPbR, hRmax⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups ⊤ B (piCompl 3))) hPbinv
  have hRmax' : Rb ∈ maxInvariantPiSubgroups ⊤ B (piCompl 3) := hRmax
  have hR16 : Nat.card Rb = 16 := (KFacts.KP4.m22_maxInvariant_structure ⟨φL⟩ hB9 hRmax').2.1
  have hRb2 : IsPGroup 2 Rb := IsPGroup.of_card (n := 4) (by rw [hR16]; norm_num)
  have hBR : B ≤ Subgroup.normalizer (Rb : Set (↥L ⧸ θ)) :=
    ((mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp hRmax.prop).2.2
  set R := (Rb.comap π).map L.subtype with hRdef
  have hRL : R ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR2 : IsPGroup 2 R := by
    have hker : IsPGroup 2 π.ker := by
      rw [hπ, QuotientGroup.ker_mk', hθ]
      exact CFSG.pCore_isPGroup
    exact (hRb2.comap_of_ker_isPGroup π hker).map L.subtype
  have hconjR : ∀ (t : G) (htN : t ∈ N) (n : ↥L ⧸ θ),
      n ∈ Subgroup.normalizer (Rb : Set (↥L ⧸ θ)) → ψ ⟨t, htN⟩ = MulAut.conj n →
        ∀ x ∈ R, t * x * t⁻¹ ∈ R := by
    rintro t htN n hn hψt _ ⟨x, hx, rfl⟩
    refine ⟨L.normalizerMonoidHom ⟨t, htN⟩ x, ?_, Sec4.normalizerMonoidHom_apply_coe htN x⟩
    change π (L.normalizerMonoidHom ⟨t, htN⟩ x) ∈ Rb
    have h1 : π (L.normalizerMonoidHom ⟨t, htN⟩ x) = n * π x * n⁻¹ := by
      rw [← hψπ t htN x, hψt, MulAut.conj_apply]
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hn (π x)).mp (Subgroup.mem_comap.mp hx)
  have hnormR : ∀ t : G, (∀ x ∈ R, t * x * t⁻¹ ∈ R) → (∀ x ∈ R, t⁻¹ * x * t⁻¹⁻¹ ∈ R) →
      t ∈ Subgroup.normalizer (R : Set G) := by
    intro t h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨h1 x, fun hx => ?_⟩
    have := h2 _ hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at this
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ t ∈ T, ∀ x ∈ R, t * x * t⁻¹ ∈ R := by
      intro t ht
      have hmem : ψ ⟨t, hTN ht⟩ ∈ P :=
        Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr ht)
      obtain ⟨n, hn⟩ := hPinn hmem
      have hnPb : n ∈ Pb := by
        rw [Subgroup.mem_comap, hn]
        exact hmem
      exact hconjR t (hTN ht) n (Subgroup.le_normalizer (hPbR hnPb)) hn.symm
    intro t ht
    exact hnormR t (key t ht) (key t⁻¹ (T.inv_mem ht))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    have hAab : IsMulCommutative ↥A := h.isElemAbelian.1
    have key : ∀ a ∈ A, ∀ x ∈ R, a * x * a⁻¹ ∈ R := by
      intro a ha
      have hfix : ∀ b ∈ B, ψ ⟨a, hAN ha⟩ b = b := by
        rintro _ ⟨b, hb, rfl⟩
        have hbA : (b : G) ∈ A := (Subgroup.mem_subgroupOf.mp hb).1
        have hcomm : a * (b : G) = b * a :=
          congrArg Subtype.val (hAab.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hbA⟩)
        rw [hψπ a (hAN ha) b]
        exact congrArg π (Subtype.ext (by
          rw [Sec4.normalizerMonoidHom_apply_coe, hcomm, mul_inv_cancel_right]))
      obtain ⟨n, hnB, hn⟩ := KFacts.KP4.m22_aut_fix_eq_conj ⟨φL⟩ hB9 hfix
      exact hconjR a (hAN ha) n (hBR hnB) hn
    intro a ha
    exact hnormR a (key a ha) (key a⁻¹ (A.inv_mem ha))
  have hRleT : R ≤ T := le_of_mem_scriptQPiStar h (h142 G A c L h) hT hR2 (hRL.trans hLH) hTR hAR
  set RT := ((T ⊓ L).subgroupOf L).map π with hRT
  have h1 : RT ≤ Pb := by
    rintro _ ⟨x, hx, rfl⟩
    have hxT : (x : G) ∈ T := (Subgroup.mem_subgroupOf.mp hx).1
    have hx1 : MulAut.conj (π x) = ψ ⟨x, hTN hxT⟩ := (hψL x x.2 (hTN hxT)).symm
    rw [Subgroup.mem_comap, hx1]
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hxT)
  have h2 : Rb ≤ RT := by
    intro r hr
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ r
    have hxR : (x : G) ∈ R := ⟨x, hr, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hRleT hxR, x.2⟩, rfl⟩
  have heq : RT = Rb := le_antisymm (h1.trans hPbR) h2
  rw [heq, hR16]


theorem ks15M22Gen_of_items
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h131 : Item131)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h135 : Item135) : KS15M22Gen :=
  ks15M22Gen_of h148 hbot h142 h131 h134 h48 h135 (ks15M22GenImage_of h142 h131 h135)

end CFSG.RankThree.PartTwo.Sec15
