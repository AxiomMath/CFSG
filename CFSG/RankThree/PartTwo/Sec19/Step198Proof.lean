module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec19.Step196Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PerfectCover.SubnormalSolvableSupplement
import CFSG.Sporadic.Bridge.M22
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartTwo.KFacts.AutTrialityOrderThree
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open scoped MatrixGroups

namespace Step198Proof

section Orders

theorem card_quot_center_cases {X : Type} [Group X] [Finite X] (hXq : IsQuasisimple X)
    (htype : Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22) :
    Nat.card (X ⧸ Subgroup.center X) = 2520 ∨ 20160 ≤ Nat.card (X ⧸ Subgroup.center X) := by
  rcases htype with hSL | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · right
    have hZ := Sec12.card_center_eq_three_of_isSLThreePi hSL
    have hcard := (Subgroup.center X).card_eq_card_quotient_mul_card_subgroup
    rw [hZ] at hcard
    obtain ⟨π, p, f, K, _, hK, hq, h2, ⟨e⟩⟩ := Sec4.exists_slPi_model (L := (⊤ : Subgroup X))
      (Sec13.isSLThreePi_of_mulEquiv Subgroup.topEquiv.symm hSL)
      (LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq)
    have := hK.finite
    have hX : 60480 ≤ Nat.card X := by
      rw [← Nat.card_congr (Subgroup.topEquiv (G := X)).toEquiv, Nat.card_congr e.toEquiv]
      cases π
      · have hq' : (p ^ f) % 3 = 2 := hq
        rw [Nat.card_congr (Sec4.slPiFalseEquiv p f K).toEquiv,
          KFacts.card_unitarySU_three hK.unitary]
        obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ f := ⟨_, rfl⟩
        rw [← hqdef] at hq' h2 ⊢
        have hq5 : 5 ≤ q := by omega
        have h1 : 125 ≤ q ^ 3 := by
          calc 125 = 5 ^ 3 := by norm_num
            _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
        have h3 : 24 ≤ q ^ 2 - 1 := by
          have : 25 ≤ q ^ 2 := by
            calc 25 = 5 ^ 2 := by norm_num
              _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
          omega
        have h4 : 126 ≤ q ^ 3 + 1 := by omega
        have := Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4
        omega
      · have hq' : (p ^ f) % 3 = 1 := hq
        let _ := Fintype.ofFinite K
        rw [Nat.card_congr (Sec4.slPiTrueEquiv (p ^ f) K).toEquiv, KFacts.card_SL_three,
          Fintype.card_eq_nat_card, hK.card]
        change 60480 ≤ (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)
        obtain ⟨q, hqdef⟩ : ∃ q, q = p ^ f := ⟨_, rfl⟩
        rw [← hqdef] at hq' h2 ⊢
        have hq4 : 4 ≤ q := by omega
        have h1 : 64 ≤ q ^ 3 := by
          calc 64 = 4 ^ 3 := by norm_num
            _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
        have h3 : 15 ≤ q ^ 2 - 1 := by
          have : 16 ≤ q ^ 2 := by
            calc 16 = 4 ^ 2 := by norm_num
              _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
          omega
        have h4 : 63 ≤ q ^ 3 - 1 := by omega
        have := Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4
        omega
    omega
  · left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · right
    rw [Nat.card_congr e.toEquiv]
    exact le_trans (by norm_num) CFSG.Sporadic.Bridge.M22.le_card_native

end Orders

section Sections

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_center_dvd {K L : Subgroup G} (hLK : L ≤ K)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) (R : Subgroup K) [R.Normal]
    (hR : Group.IsSolvable R) :
    Nat.card ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) ∣ Nat.card (K ⧸ R) := by
  set θL := aschbacherSolvableCore 3 L with hθL
  set μ : L →* K ⧸ R := (QuotientGroup.mk' R).comp (Subgroup.inclusion hLK) with hμ
  set Z : Subgroup L := (Subgroup.center (L ⧸ θL)).comap (QuotientGroup.mk' θL) with hZ
  have : Z.Normal := Subgroup.Normal.comap inferInstance _
  have hker : μ.ker ≤ Z := by
    have hsol : Group.IsSolvable μ.ker := by
      have := hR
      refine Group.isSolvable_of_isSolvable_injective
        (f := MonoidHom.codRestrict ((Subgroup.inclusion hLK).comp μ.ker.subtype) R
          (fun x => (QuotientGroup.eq_one_iff _).mp x.2)) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subgroup.inclusion_injective hLK
      exact congrArg Subtype.val hxy
    have hn : (μ.ker.map (QuotientGroup.mk' θL)).Normal :=
      (MonoidHom.normal_ker μ).map _ (QuotientGroup.mk'_surjective _)
    rcases LocalCores.quasisimple_normal_subgroups hLq hn with htop | hle
    · exfalso
      have hs : Group.IsSolvable (L ⧸ θL) := by
        refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' θL).comp μ.ker.subtype) ?_
        intro q
        have hq : q ∈ μ.ker.map (QuotientGroup.mk' θL) := htop ▸ Subgroup.mem_top q
        obtain ⟨x, hx, rfl⟩ := hq
        exact ⟨⟨x, hx⟩, rfl⟩
      have : Nontrivial (L ⧸ θL) := LocalCores.isQuasisimple_nontrivial hLq
      have : Group.IsPerfect (L ⧸ θL) := hLq.1
      exact Group.IsPerfect.not_isSolvable (L ⧸ θL) hs
    · intro x hx
      exact hle ⟨x, hx, rfl⟩
  have h1 : Nat.card ((L ⧸ θL) ⧸ Subgroup.center (L ⧸ θL)) = Z.index :=
    (Nat.card_congr (Sec4.Census.quotientComapEquiv θL (Subgroup.center (L ⧸ θL))).toEquiv).symm
  rw [h1]
  refine (Subgroup.index_dvd_of_le hker).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem false_of_sl2 {K F : Subgroup G} (hFK : F ≤ K)
    (hF9 : Nat.card F = 9) (hF3 : ∀ x ∈ F, x ^ 3 = 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (e : K ⧸ Sec4.oTwoP p K ≃* SL(2, ZMod p)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Sec4.oTwoP p K with hR
  have hR3 : ∀ z ∈ R, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have hz' : QuotientGroup.mk' (CFSG.pCore 2 K) z ∈ CFSG.pCore p (K ⧸ CFSG.pCore 2 K) := hz
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup p (CFSG.pCore p (K ⧸ CFSG.pCore 2 K)))
      ⟨_, hz'⟩
    have ha' : z ^ p ^ a ∈ CFSG.pCore 2 K := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 K) z) ^ p ^ a = 1 := by
        simpa using congrArg Subtype.val ha
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, ha'⟩
    have hb' : z ^ (p ^ a * 2 ^ b) = 1 := by
      rw [pow_mul]
      simpa using congrArg Subtype.val hb
    have h3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
    have hcop : Nat.Coprime 3 (p ^ a * 2 ^ b) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_right a h3p) (Nat.Coprime.pow_right b (by norm_num))
    have := (pow_gcd_eq_one (a := z)).mpr ⟨hz3, hb'⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  set F' : Subgroup K := F.subgroupOf K with hF'
  set π := QuotientGroup.mk' R with hπ
  have hinj : Set.InjOn π (F' : Set K) := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ R := QuotientGroup.eq.mp hxy
    have h2 : (x⁻¹ * y) ^ 3 = 1 := by
      apply Subtype.ext
      have := hF3 _ (F.mul_mem (F.inv_mem (Subgroup.mem_subgroupOf.mp hx))
        (Subgroup.mem_subgroupOf.mp hy))
      simpa using this
    exact (inv_mul_eq_one.mp (hR3 _ h1 h2))
  set T : Subgroup (K ⧸ R) := F'.map π with hT
  have hT9 : Nat.card T = 9 := by
    rw [hT, Step198DProof.card_map_of_injOn π hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv, hF9]
  have hTexp : Monoid.exponent T ∣ 3 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, x, hx, rfl⟩
    apply Subtype.ext
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hF3 _ (Subgroup.mem_subgroupOf.mp hx))
    simp [← map_pow, hx3]
  exact Sec4.false_of_surjective_of_isCyclic_sylow e.symm.toMonoidHom e.symm.surjective
    (fun S => Sec4.Census.isCyclic_sylow_SL2 (by norm_num) (by omega) S) hTexp hT9

theorem pCore_three_le_center {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X)) :
    CFSG.pCore 3 (X ⧸ CFSG.pCore 2 X) ≤ Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 X with hP
  set θ := aschbacherSolvableCore 3 X with hθ
  have hPθ : P ≤ θ := (solvable_prime_complement_core_characterization (H := X)
    Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
  set ρ : X ⧸ P →* X ⧸ θ := QuotientGroup.map P θ (MonoidHom.id X) hPθ with hρ
  have hρs : Function.Surjective ρ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨(x : X ⧸ P), rfl⟩
  set O := CFSG.pCore 3 (X ⧸ P) with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hO3 : IsPGroup 3 O := CFSG.pCore_isPGroup
  have hmap : O.map ρ ≤ Subgroup.center (X ⧸ θ) := by
    rcases LocalCores.quasisimple_normal_subgroups hq (hOn.map ρ hρs) with htop | hle
    · exfalso
      have h3 : IsPGroup 3 (X ⧸ θ) := by
        intro y
        have hy : y ∈ O.map ρ := htop ▸ Subgroup.mem_top y
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨k, hk⟩ := hO3 ⟨z, hz⟩
        refine ⟨k, ?_⟩
        rw [← map_pow]
        have : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [this, map_one]
      have : Group.IsNilpotent (X ⧸ θ) := h3.isNilpotent
      have : Nontrivial (X ⧸ θ) := LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect (X ⧸ θ) := hq.1
      exact Group.IsPerfect.not_isSolvable (X ⧸ θ) inferInstance
    · exact hle
  have hker : ∀ z ∈ O, ρ z = 1 → z = 1 := by
    intro z hzO hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have hxθ : x ∈ θ := by
      have h1 : ρ (x : X ⧸ P) = (x : X ⧸ θ) := rfl
      rw [h1, QuotientGroup.eq_one_iff] at hz
      exact hz
    obtain ⟨k, hk⟩ := hO3 ⟨_, hzO⟩
    have h1 : orderOf (x : X ⧸ P) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (x : X ⧸ P) ∣ Nat.card θ := by
      refine (orderOf_map_dvd (QuotientGroup.mk' P) x).trans ?_
      have := orderOf_dvd_natCard (⟨x, hxθ⟩ : θ)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ k) (Nat.card θ) := Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        three_not_dvd_card_aschbacherSolvableCore)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro z
  have hcO : z * y * z⁻¹ * y⁻¹ ∈ O := O.mul_mem (hOn.conj_mem y hy z) (O.inv_mem hy)
  have hcρ : ρ (z * y * z⁻¹ * y⁻¹) = 1 := by
    have hc := Subgroup.mem_center_iff.mp (hmap ⟨y, hy, rfl⟩) (ρ z)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact Step1910O2Proof.mul_comm_of_commutator_eq_one (hker _ hcO hcρ)

theorem pCore_two_ne_bot (hchar : CFSG.Assembly.IsCharTwoType G) {M K : Subgroup G}
    (hM2 : CFSG.Assembly.IsTwoLocal M) (hKM : K ≤ M) (hsn : (K.subgroupOf M).IsSubnormal)
    (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥) : CFSG.pCore 2 K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  set V := CFSG.Open.pCoreOf 2 M with hV
  have hVM : V ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  set Y := K ⊔ V with hY
  have hKY : K ≤ Y := le_sup_left
  have hVY : V ≤ Y := le_sup_right
  have hYM : Y ≤ M := sup_le hKM hVM
  have hPerf : Group.IsPerfect (K.subgroupOf Y) := by
    have := hKp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKY).symm.toMonoidHom) (MulEquiv.surjective _)
  have hPsn : (K.subgroupOf Y).IsSubnormal := Sec18.isSubnormal_subgroupOf_of_le hsn hYM
  have hNn : (V.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVY).mpr (hYM.trans hMV)
  have hNs : Group.IsSolvable (V.subgroupOf Y) := by
    have h2 : IsPGroup 2 (V.subgroupOf Y) := hV2.comap_subtype
    have := h2.isNilpotent
    infer_instance
  have hsup : K.subgroupOf Y ⊔ V.subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKY hVY, Subgroup.subgroupOf_self]
  obtain ⟨hKn, -⟩ :=
    PerfectCover.perfect_subnormal_solvable_supplement_residual hPerf hPsn hNn hNs hsup
  have hO1 : ∀ x ∈ CFSG.Open.pCoreOf 2 K, x = 1 := by
    intro x hx
    have hxK : x ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hx
    have : (⟨x, hxK⟩ : K) ∈ CFSG.pCore 2 K := (Sec18.mem_pCore_iff_mem_pCoreOf _).mpr hx
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hKV : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k := by
    intro k hk v hv
    have h1 : v * k * v⁻¹ ∈ K := by
      have := hKn.conj_mem ⟨k, hKY hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨v, hVY hv⟩
      exact Subgroup.mem_subgroupOf.mp this
    have h2 : k * v * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hMV (hKM hk)) v).mp hv
    have hcK : k * v * k⁻¹ * v⁻¹ ∈ K := by
      rw [show k * v * k⁻¹ * v⁻¹ = k * (v * k * v⁻¹)⁻¹ by group]
      exact K.mul_mem hk (K.inv_mem h1)
    have hcV : k * v * k⁻¹ * v⁻¹ ∈ V := V.mul_mem h2 (V.inv_mem hv)
    have hO : k * v * k⁻¹ * v⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left : K ⊓ V ≤ K) ?_
        (hV2.to_le inf_le_right) ⟨hcK, hcV⟩
      exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hMV (hKM hx)⟩
    exact Step1910O2Proof.mul_comm_of_commutator_eq_one (hO1 _ hO)
  have hKV' : K ≤ V := by
    intro k hk
    have hkC : k ∈ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 M : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hKV k hk v hv).symm
    exact hchar M hM2 ⟨hKM hk, hkC⟩
  have hK2 : IsPGroup 2 K := hV2.to_le hKV'
  have : Group.IsSolvable K := by
    have := hK2.isNilpotent
    infer_instance
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  exact Group.IsPerfect.not_isSolvable K inferInstance

end Sections

section FourFour

open CFSG.RankThree.PartTwo.Sec4.Census in
theorem quasisimple_or_linear {X : Type} [Group X] [Finite X]
    (hG : SectionFourHyp X) [Group.IsPerfect X] {N : Subgroup X} [N.Normal]
    (hN : Group.IsSolvable N) [IsSimpleGroup (X ⧸ N)] (hO2 : CFSG.pCore 2 X ≠ ⊥)
    (h3 : ¬ Subgroup.centralizer (CFSG.pCore 3 (X ⧸ CFSG.pCore 2 X) : Set (X ⧸ CFSG.pCore 2 X)) ≤
      N.map (QuotientGroup.mk' (CFSG.pCore 2 X))) :
    IsQuasisimple (X ⧸ CFSG.pCore 2 X) ∨
      Nonempty (X ⧸ Sec4.oTwoFitting X ≃* SL(2, ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧ Nonempty (X ⧸ Sec4.oTwoP p X ≃* SL(2, ZMod p))) ∨
      Nonempty (X ⧸ Sec4.oTwoP 3 X ≃* SL(3, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 X with hPdef
  have : P.Normal := CFSG.pCore_normal
  have hPK : P ≤ N := pCore_le 2
  set KX := N.map (QuotientGroup.mk' P) with hKXdef
  have : KX.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective P)
  have hKX : Group.IsSolvable KX := by
    have := hN
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' P).subgroupMap_surjective N)
  have : IsSimpleGroup ((X ⧸ P) ⧸ KX) :=
    (QuotientGroup.quotientQuotientEquivQuotient P N hPK).isSimpleGroup
  by_cases hq : IsQuasisimple (X ⧸ P)
  · exact Or.inl hq
  obtain ⟨p₀, hp₀, hS₀⟩ := exists_centralizer_pCore_le hKX hq
  have hO2X : CFSG.pCore 2 (X ⧸ P) = ⊥ := ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hlin : ∀ p : ℕ, p.Prime →
      Subgroup.centralizer (CFSG.pCore p (X ⧸ P) : Set (X ⧸ P)) ≤ KX →
      ∃ (M : Subgroup (X ⧸ P)) (_ : M.Normal), LinearOutcome (X ⧸ P) p M := by
    intro p hp hpS
    have : Fact p.Prime := ⟨hp⟩
    have hPne : CFSG.pCore p (X ⧸ P) ≠ ⊥ := by
      intro h
      have htop : (⊤ : Subgroup (X ⧸ P)) ≤
          Subgroup.centralizer (CFSG.pCore p (X ⧸ P) : Set (X ⧸ P)) := by
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [h] at hx
        rw [(Subgroup.mem_bot).mp hx, one_mul, mul_one]
      exact (QuotientGroup.nontrivial_iff.mp inferInstance) (top_le_iff.mp (htop.trans hpS))
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hPne hO2X
    rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
    · exact absurd hpS h3
    · obtain ⟨D, hD⟩ := exists_criticalAt hp2 hPne
      have hrank : CFSG.pRank p D ≤ 2 := by
        have h1 := pRank_le_pRank_top hp D
        rw [pRank_quotient_pCore_two hO2 hp hp2] at h1
        have h2 := hG.localRank_lt p hp hp3
        omega
      exact linearOutcome_of_criticalAt hKX hp3 hpS hD hrank
  rcases linear_endgame hKX hO2X hp₀ hS₀ hlin with ⟨⟨e⟩⟩ | ⟨p, hp, hp3, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inr (Or.inl ⟨(quotientComapEquiv P (fittingSubgroup (X ⧸ P))).trans e⟩)
  · have : Fact p.Prime := ⟨hp⟩
    exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp3,
      ⟨(quotientComapEquiv P (CFSG.pCore p (X ⧸ P))).trans e⟩⟩))
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Or.inr (Or.inr (Or.inr ⟨(quotientComapEquiv P (CFSG.pCore 3 (X ⧸ P))).trans e⟩))

end FourFour

section Components

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_mem_thetaComponentsAt {M L : Subgroup G} {c : G}
    (hL : L ∈ thetaComponentsAt 3 c) (hLM : L ≤ M) (hcM : c ∈ M) :
    L.subgroupOf M ∈ thetaComponentsAt 3 (⟨c, hcM⟩ : M) := by
  set C := Subgroup.centralizer ({(⟨c, hcM⟩ : M)} : Set M) with hC
  obtain ⟨hLC, hL'⟩ := PartOne.mem_thetaComponentsAt_iff.mp hL
  have hLMC : L.subgroupOf M ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC (Subgroup.mem_subgroupOf.mp hx))
  refine PartOne.mem_thetaComponentsAt_iff.mpr ⟨hLMC, ?_, ?_, ?_⟩
  · have := Sec6.isPerfect_of_mem_thetaComponentsAt hL
    exact Group.IsPerfect.ofSurjective
      (f := ((Subgroup.subgroupOfEquivOfLe hLMC).trans
        (Subgroup.subgroupOfEquivOfLe hLM)).symm.toMonoidHom) (MulEquiv.surjective _)
  · set ι : C →* Subgroup.centralizer ({c} : Set G) :=
      MonoidHom.codRestrict (M.subtype.comp C.subtype) _ (fun x => by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp x.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val h1) with hι
    have h := hL'.2.1.comap ι
    convert h using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  · set e := (Subgroup.subgroupOfEquivOfLe hLMC).trans (Subgroup.subgroupOfEquivOfLe hLM)
    exact LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e.symm
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e.symm))
      (Sec12.isQuasisimple_thetaQuot_of_mem hL)

theorem le_normalizer_map_of_isE27 (h45 : Sec4.Item4_5) {M X : Subgroup G}
    (hM4 : SectionFourHyp M) (hX : IsE27 X) (hXM : X ≤ M) {L' : Subgroup M}
    (hL' : L' ∈ thetaComponents 3 M) :
    X ≤ Subgroup.normalizer ((L'.map M.subtype : Subgroup G) : Set G) := by
  have hres := h45 M hM4 (X.subgroupOf M) hX.isPGroup.comap_subtype
    (Or.inr ⟨Step198DProof.isElemAbelian_subgroupOf hX.1 M, 3, le_rfl, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hX.2]; norm_num⟩) L' hL'
  intro x hx
  exact (Sec13.coe_mem_normalizer_map_iff M (h := ⟨x, hXM hx⟩)).mpr
    (hres (Subgroup.mem_subgroupOf.mpr hx))

theorem mem_oTwoComponentsIn (hG : TheoremFourHyp G)
    {M K L F : Subgroup G} (hM2 : CFSG.Assembly.IsTwoLocal M) (hMtop : M ≠ ⊤)
    (hK : K ∈ thetaComponentsIn M) (hLK : L ≤ K)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (htype : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    (hFL : F ≤ L) (hF9 : Nat.card F = 9) (hF3 : ∀ x ∈ F, x ^ 3 = 1) :
    K ∈ oTwoComponentsIn M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hsn : (K.subgroupOf M).IsSubnormal := hK'.2.1
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKtop : K ≠ ⊤ := fun h => hMtop (top_le_iff.mp (h ▸ hKM))
  have hK4 : SectionFourHyp K := hG.sectionFourHyp hKtop
  have hKq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
    set e := Subgroup.subgroupOfEquivOfLe hKM
    exact LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hK'.2.2
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := LocalCores.isQuasisimple_nontrivial hLq
    obtain ⟨u, v, huv⟩ := exists_pair_ne (L ⧸ aschbacherSolvableCore 3 L)
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    have : Subsingleton L := by
      rw [h]
      infer_instance
    rw [Subsingleton.elim u v]
  have hK1 : K ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLK))
  have hO2 : CFSG.pCore 2 K ≠ ⊥ := pCore_two_ne_bot hG.charTwoType hM2 hKM hsn hKp hK1
  have := hKp
  set θK := aschbacherSolvableCore 3 K with hθK
  set N : Subgroup K := (Subgroup.center (K ⧸ θK)).comap (QuotientGroup.mk' θK) with hN
  have : N.Normal := Subgroup.Normal.comap inferInstance _
  have hNs : Group.IsSolvable N :=
    Sec4.isSolvable_comap_mk' (solvable_prime_complement_core_characterization (H := K)
      Nat.prime_three).1 inferInstance
  have : IsSimpleGroup ((K ⧸ θK) ⧸ Subgroup.center (K ⧸ θK)) := hKq.2.1
  have : IsSimpleGroup (K ⧸ N) :=
    (Sec4.Census.quotientComapEquiv θK (Subgroup.center (K ⧸ θK))).isSimpleGroup
  have hPN : CFSG.pCore 2 K ≤ N := by
    intro x hx
    have hxθ : x ∈ θK := (solvable_prime_complement_core_characterization (H := K)
      Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num) hx
    rw [hN, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hxθ]
    exact Subgroup.one_mem _
  have h3 : ¬ Subgroup.centralizer (CFSG.pCore 3 (K ⧸ CFSG.pCore 2 K) :
      Set (K ⧸ CFSG.pCore 2 K)) ≤ N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    intro hle
    have hcen := pCore_three_le_center hKq
    have htop : N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊤ := by
      refine eq_top_iff.mpr (le_trans ?_ hle)
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.mp (hcen hx) g).symm
    have hNtop : N = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      have hx : QuotientGroup.mk' (CFSG.pCore 2 K) x ∈
          N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have h1 : n⁻¹ * x ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp hnx
      have := N.mul_mem hn (hPN h1)
      simpa using this
    have : Nontrivial (K ⧸ N) := IsSimpleGroup.toNontrivial
    exact (QuotientGroup.nontrivial_iff.mp this) hNtop
  rcases quasisimple_or_linear hK4 hNs hO2 h3 with hq | ⟨⟨e2⟩⟩ | ⟨p, hp, hp3, ⟨e3⟩⟩ | ⟨⟨e4⟩⟩
  · exact Sec18.mem_oTwoComponentsIn_of_quasisimple hKM hsn (Subgroup.isPerfect_iff.mp hKp) hq
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hdvd := card_quot_center_dvd hLK hLq (Sec4.oTwoFitting K) Sec4.isSolvable_oTwoFitting
    rw [Nat.card_congr e2.toEquiv, Sec4.Census.card_SL2] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases card_quot_center_cases hLq htype with h | h <;> omega
  · exact (false_of_sl2 (hFL.trans hLK) hF9 hF3 hp hp3 e3).elim
  · exfalso
    have hdvd := card_quot_center_dvd hLK hLq (Sec4.oTwoP 3 K) (Sec4.isSolvable_oTwoP 3)
    rw [Nat.card_congr e4.toEquiv, Sec4.Census.card_SL3_three] at hdvd
    rcases card_quot_center_cases hLq htype with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · have := Nat.le_of_dvd (by norm_num) hdvd
      omega

end Components

section Faithful

variable {G : Type} [Group G] [Finite G]

theorem faithful_or_central (hst : PartTwoStanding G) (hS : partTwoS G = ∅)
    {A K D : Subgroup G} {c : G} (hAE : A ∈ partTwoE G)
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hDexp : ∀ d ∈ D, d ^ 3 = 1)
    (hDA : ∀ d ∈ D, d ∈ A → d ∈ Subgroup.zpowers c) (hc3 : orderOf c = 3) :
    (∀ d ∈ D, (∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → d = 1) ∨
      ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hf : ∀ d ∈ D, (∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → d = 1
  · exact Or.inl hf
  right
  push Not at hf
  obtain ⟨d, hdD, hdK, hd1⟩ := hf
  set O := CFSG.Open.pCoreOf 2 K with hO
  have hNO : ∀ g ∈ Subgroup.normalizer (K : Set G), g ∈ Subgroup.normalizer (O : Set G) :=
    fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hg
  have hKO : ∀ k ∈ K, k ∈ Subgroup.normalizer (O : Set G) :=
    fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
  let S : Subgroup G :=
    { carrier := {x | x ∈ D ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O}
      mul_mem' := by
        rintro x y ⟨hxD, hx⟩ ⟨hyD, hy⟩
        refine ⟨D.mul_mem hxD hyD, fun k hk => ?_⟩
        have h1 : x * (y * k * y⁻¹ * k⁻¹) * x⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hNO x (hDK hxD)) _).mp (hy k hk)
        rw [show x * y * k * (x * y)⁻¹ * k⁻¹ =
          x * (y * k * y⁻¹ * k⁻¹) * x⁻¹ * (x * k * x⁻¹ * k⁻¹) by group]
        exact O.mul_mem h1 (hx k hk)
      one_mem' := ⟨D.one_mem, fun k _ => by simp [O.one_mem]⟩
      inv_mem' := by
        rintro x ⟨hxD, hx⟩
        refine ⟨D.inv_mem hxD, fun k hk => ?_⟩
        have h1 := hx k⁻¹ (K.inv_mem hk)
        have h2 : x⁻¹ * (x * k⁻¹ * x⁻¹ * k⁻¹⁻¹) * x⁻¹⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hNO _ (Subgroup.inv_mem _ (hDK hxD))) _).mp h1
        have h3 : k * (x⁻¹ * (x * k⁻¹ * x⁻¹ * k⁻¹⁻¹) * x⁻¹⁻¹) * k⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hKO k hk) _).mp h2
        rwa [show k * (x⁻¹ * (x * k⁻¹ * x⁻¹ * k⁻¹⁻¹) * x⁻¹⁻¹) * k⁻¹ =
          x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ by group] at h3 }
  have hdS : d ∈ S := ⟨hdD, hdK⟩
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, fun k hk => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAD ha) x).mp hx.1
    · have hk' : a⁻¹ * k * a⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAK ha)) k).mp hk
      have h1 := hx.2 _ hk'
      have h2 : a * (x * (a⁻¹ * k * a⁻¹⁻¹) * x⁻¹ * (a⁻¹ * k * a⁻¹⁻¹)⁻¹) * a⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hNO a (hAK ha)) _).mp h1
      rwa [show a * (x * (a⁻¹ * k * a⁻¹⁻¹) * x⁻¹ * (a⁻¹ * k * a⁻¹⁻¹)⁻¹) * a⁻¹ =
        a * x * a⁻¹ * k * (a * x * a⁻¹)⁻¹ * k⁻¹ by group] at h2
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hDexp d hdD) hd1
  have h3S : 3 ∣ Nat.card S := by
    have := orderOf_dvd_natCard (⟨d, hdS⟩ : S)
    rwa [Subgroup.orderOf_mk, hd3] at this
  have hA3 : IsPGroup 3 A := (isE27_of_mem_partTwoE hAE).isPGroup
  obtain ⟨y, hyS, hy1, hy3, hyA⟩ := Step1910Proof.exists_mem_of_le_normalizer hA3 hAS h3S
  have hyAmem : y ∈ A := mem_of_le_centralizer hst hS hAE hy3 fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hyA a ha)
  have hyc : y ∈ Subgroup.zpowers c := hDA y hyS.1 hyAmem
  have hcy : c ∈ Subgroup.zpowers y := by
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have heq : Subgroup.zpowers y = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyc)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hc3])
    rw [heq]
    exact Subgroup.mem_zpowers c
  exact ((Subgroup.zpowers_le.mpr hyS) hcy).2

theorem eq_sup_of_central {K L : Subgroup G} {c : G}
    (hKq : IsQuasisimple (K ⧸ CFSG.pCore 2 K)) (hLK : L ≤ K) (hcK : c ∈ K)
    (hc3 : orderOf c = 3) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).IsSubnormal)
    (hLp : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    (hcen : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    K = L ⊔ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.pCore 2 K with hP
  set π := QuotientGroup.mk' P with hπ
  set c' : K := ⟨c, hcK⟩ with hc'
  have hc'Z : π c' ∈ Subgroup.center (K ⧸ P) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective P q
    have h1 : (c' * k * c'⁻¹ * k⁻¹ : K) ∈ P :=
      (Sec18.mem_pCore_iff_mem_pCoreOf _).mpr (hcen k k.2)
    have h2 : π (c' * k * c'⁻¹ * k⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (Step1910O2Proof.mul_comm_of_commutator_eq_one h2).symm
  have hc'3 : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact hc3
  have hZ3 : IsPGroup 3 (Subgroup.zpowers c') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3, pow_one])
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hmap :=
    RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      3 Nat.prime_three π (QuotientGroup.mk'_surjective P) hker (Subgroup.zpowers c') hZ3
  have hsurj : ∀ q : K ⧸ P, ∃ x : K, (x : G) ∈ Subgroup.centralizer ({c} : Set G) ∧ π x = q := by
    intro q
    have hq : q ∈ Subgroup.centralizer ((Subgroup.zpowers c').map π : Set (K ⧸ P)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcq : Commute (π c') q := (Subgroup.mem_center_iff.mp hc'Z q).symm
      rw [map_zpow]
      exact (hcq.zpow_left n).eq
    rw [← hmap] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp hx c' (Subgroup.mem_zpowers c')
    exact (congrArg Subtype.val this).symm
  set C' : Subgroup K := (Subgroup.centralizer ({c} : Set G)).subgroupOf K with hC'
  set L' : Subgroup K := L.subgroupOf K with hL'
  have hL'C' : L' ≤ C' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hLc (Subgroup.mem_subgroupOf.mp hx))
  set ι : C' →* Subgroup.centralizer ({c} : Set G) :=
    MonoidHom.codRestrict (K.subtype.comp C'.subtype) _
      (fun x => Subgroup.mem_subgroupOf.mp x.2) with hι
  have hsn' : (L'.subgroupOf C').IsSubnormal := by
    have h := hLsn.comap ι
    convert h using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  set φ : C' →* K ⧸ P := π.comp C'.subtype with hφ
  have hφs : Function.Surjective φ := fun q => by
    obtain ⟨x, hx, hxq⟩ := hsurj q
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr hx⟩, hxq⟩
  have heq : (L'.subgroupOf C').map φ = L'.map π := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hL'C' hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hsn'' : (L'.map π).IsSubnormal := heq ▸ hsn'.map hφs
  have hL'p : Group.IsPerfect L' := by
    have := hLp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom) (MulEquiv.surjective _)
  have hperf : Group.IsPerfect (L'.map π) :=
    Group.IsPerfect.ofSurjective (f := π.subgroupMap L') (π.subgroupMap_surjective L')
  have hne : L'.map π ≠ ⊥ := by
    intro h
    have hL'P : L' ≤ P := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
      exact h
    have hL2 : IsPGroup 2 L' := (CFSG.pCore_isPGroup (p := 2) (G := K)).to_le hL'P
    have : Group.IsSolvable L' := by
      have := hL2.isNilpotent
      infer_instance
    have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
    have : Nontrivial L' := (Subgroup.subgroupOfEquivOfLe hLK).toEquiv.nontrivial
    exact Group.IsPerfect.not_isSolvable L' inferInstance
  have htop := Sec4.Item426.eq_top_of_isPerfect_of_isSubnormal hKq hperf hsn'' hne
  apply le_antisymm
  · intro k hk
    have hq : π ⟨k, hk⟩ ∈ L'.map π := htop ▸ Subgroup.mem_top _
    obtain ⟨l, hl, hlk⟩ := hq
    have h1 : l⁻¹ * ⟨k, hk⟩ ∈ P := QuotientGroup.eq.mp hlk
    have h2 : ((l⁻¹ * ⟨k, hk⟩ : K) : G) ∈ CFSG.Open.pCoreOf 2 K :=
      (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
    have e : k = (l : G) * ((l⁻¹ * ⟨k, hk⟩ : K) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) h2
  · exact sup_le hLK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)

end Faithful

section Config

variable {G : Type} [Group G] [Finite G] {A L E M : Subgroup G} {c : G}

theorem mem_E_of_ctx195 (hctx : Ctx195 G A c L E M) : c ∈ E := by
  have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  exact mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hctx.mem_partTwoT.1
    (hA.1.2 c hcA) ((hctx.le_sup.trans inf_le_left).trans
      (sup_le (Sec6.le_centralizer_of_mem_thetaComponentsAt hctx.mem_lA.1)
        (le_centralizer_of_mem hA.1.1 hcA)))

theorem mem_zpowers_of_mem_A (hctx : Ctx195 G A c L E M) {d : G}
    (hd : d ∈ E ⊓ Sec4.thetaQuotCentralizer L) (hdA : d ∈ A) : d ∈ Subgroup.zpowers c := by
  have hsec : d ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨hdA, fun l hl => ?_⟩
    have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hd.2).2 l hl
    have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hl) _).mp h1
    have e : l * (l⁻¹ * (d * l * d⁻¹)) * l⁻¹ = d * l * d⁻¹ * l⁻¹ := by group
    rw [e] at h2
    exact h2
  rw [hctx.mem_lA.2.2.1] at hsec
  exact hsec

theorem card_facts (h131 : Item131) (hspor : SporadicModels131) (hctx : Ctx195 G A c L E M) :
    Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 ∧
      Nat.card (E ⊓ L : Subgroup G) = 9 ∧
      Nat.card ((E ⊓ L) ⊓ (E ⊓ Sec4.thetaQuotCentralizer L) : Subgroup G) ≤ 3 := by
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD13 : Sec13Data G A c L :=
    ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT,
      hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hE : IsE27 E := hctx.isE27
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hE3 : IsPGroup 3 E := hE.isPGroup
  have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases Step1910O2Proof.type_of_mem h131 hspor hD13 hctx.mem_L with hSL | hA7 | hM22
    · exact Sec12.card_center_eq_three_of_isSLThreePi hSL
    · exact hA7.1
    · exact hM22.1
  set D := E ⊓ Sec4.thetaQuotCentralizer L with hDdef
  have hDE : D ≤ E := inf_le_left
  have hdvd27 : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS' => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hS'
  have hD9' : 9 ≤ Nat.card D :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hEexp x hx.1)
      hctx.centralizer_noncyclic
  have hEL9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G) :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hEexp x hx.1) hctx.inf_noncyclic
  have hTD : Nat.card ((E ⊓ L) ⊓ D : Subgroup G) ≤ 3 := by
    have h := Step1910O2Proof.card_le_card_center_thetaQuot (S := (E ⊓ L) ⊓ D)
      (hE3.to_le (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right)
    rwa [hZ3] at h
  refine ⟨?_, ?_, hTD⟩
  · obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd27 D hDE)
    interval_cases k
    · rw [hk] at hD9'
      norm_num at hD9'
    · rw [hk] at hD9'
      norm_num at hD9'
    · rw [hk]
      norm_num
    · exfalso
      have hDE' : D = E := Subgroup.eq_of_le_of_card_ge hDE (by rw [hk, hE.2]; norm_num)
      have h1 : (E ⊓ L) ⊓ D = E ⊓ L := inf_eq_left.mpr (inf_le_left.trans hDE'.ge)
      rw [h1] at hTD
      omega
  · obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd27 _ inf_le_left)
    interval_cases k
    · rw [hk] at hEL9
      norm_num at hEL9
    · rw [hk] at hEL9
      norm_num at hEL9
    · rw [hk]
      norm_num
    · exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE.2]; norm_num)
      have hDL : D ≤ L := fun b hb => by
        have hb' : b ∈ E ⊓ L := by
          rw [hEL']
          exact hb.1
        exact hb'.2
      have h := Step1910O2Proof.card_le_card_center_thetaQuot (hE3.to_le hDE) hDL inf_le_right
      rw [hZ3] at h
      have := hD9'
      omega

end Config

end Step198Proof

open Step198Proof

@[expose] def Census198 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L D : Subgroup G) (c : G),
    SectionFourHyp ↥(K ⊔ D) → CFSG.Open.pCoreOf 2 K ≠ ⊥ → Group.IsPerfect K →
    IsQuasisimple (K ⧸ CFSG.pCore 2 K) → D ≤ Subgroup.normalizer (K : Set G) →
    CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    (∀ d ∈ D, (∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → d = 1) →
    L ≤ K → c ∈ L → c ∈ D → orderOf c = 3 → L ≤ Subgroup.centralizer ({c} : Set G) →
    (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal →
    Group.IsPerfect L → IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    D ≤ Sec4.thetaQuotCentralizer L →
    (∃ p f : ℕ, CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 p f) ∧
      ∃ (f : ℕ) (_ : 1 ≤ f) (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (2 ^ f) ^ 3 ∧ ∃ σ : F ≃+* F, (∀ x, σ x = x ^ 2 ^ f) ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
            CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 F
              σ.toRingHom) ∧
          ∃ e ∈ D, Sec4.InducesOuterTheta e K

theorem step198_of
    (h131 : Item131)
    (hspor : SporadicModels131) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hC : Census198) :
    Step198 := by
  intro G _ _ A c L E M hctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hS := hctx.partTwoS_eq
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  have hD13 : Sec13Data G A c L :=
    ⟨hst, hS, hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA,
      hctx.mem_lA⟩
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hE : IsE27 E := hctx.isE27
  have hAE : A ∈ partTwoE G := hctx.mem_partTwoE
  have hA := isE27_of_mem_partTwoE hAE
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc3
    norm_num at hc3
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcE : c ∈ E := mem_E_of_ctx195 hctx
  have hcL : c ∈ L := hctx.mem_L
  have hLA : A ≤ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1
  have hLq := Sec12.isQuasisimple_thetaQuot_of_mem hL
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).IsSubnormal :=
    PartOne.isSubnormal_of_mem_thetaComponentsAt hL
  have hL1 : L ≠ ⊥ := fun h => hc1 (by
    have : c ∈ (⊥ : Subgroup G) := h ▸ hcL
    exact Subgroup.mem_bot.mp this)
  have hLM : L ≤ M := le_of_ctx195 hctx
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  have hAM : A ≤ M := hctx.le_normalizer.trans
    ((normalizer_le_gamma le_rfl (by rw [hE.pRank_eq]; norm_num)).trans hctx.mem_scriptM.2)
  have hcM : c ∈ M := hEM hcE
  have hM2 : CFSG.Assembly.IsTwoLocal M := hctx.mem_scriptM.1.1
  have hMtop : M ≠ ⊤ := by
    have : IsSimpleGroup G := hst.isSimpleGroup
    exact ne_top_of_pCoreOf_ne_bot hst.nonabelian
      (pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1)
  have hM4 : SectionFourHyp M := hst.toTheoremFourHyp.sectionFourHyp hMtop
  have htype := Step1910O2Proof.type_of_mem h131 hspor hD13 hcL
  obtain ⟨hD9, hELcard, -⟩ := card_facts h131 hspor hctx
  set D := E ⊓ Sec4.thetaQuotCentralizer L with hDdef
  have hDE : D ≤ E := inf_le_left
  obtain ⟨L', hL', hLL'⟩ := h48 M hM4 (E.subgroupOf M)
    (Step198DProof.isElemAbelian_subgroupOf hE.1 M)
    ⟨3, le_rfl, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE.2]; norm_num⟩
    ⟨c, hcM⟩ (Subgroup.mem_subgroupOf.mpr hcE) (fun h => hc1 (congrArg Subtype.val h))
    (L.subgroupOf M) (subgroupOf_mem_thetaComponentsAt hL hLM hcM)
  set K := L'.map M.subtype with hKdef
  have hKθ : K ∈ thetaComponentsIn M := ⟨L', hL', rfl⟩
  have hLK : L ≤ K := fun l hl =>
    ⟨⟨l, hLM hl⟩, hLL' (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := le_normalizer_map_of_isE27 h45 hM4 hE hEM hL'
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_map_of_isE27 h45 hM4 hA hAM hL'
  have hK : K ∈ oTwoComponentsIn M :=
    mem_oTwoComponentsIn hst.toTheoremFourHyp hM2 hMtop hKθ hLK hLq htype
      (inf_le_right : E ⊓ L ≤ L) hELcard (fun x hx => hEexp x hx.1)
  refine ⟨K, hK, hLK, ?_⟩
  have hcD : c ∈ D := ⟨hcE, Sec12.mem_thetaQuotCentralizer_of_central hcL hLc⟩
  have hDab : CFSG.Assembly.IsElemAbelian 3 D := isElemAbelian_of_le hE.1 hDE
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := hDE.trans hEK
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hctx.le_normalizer ha,
      Subgroup.mem_normalizer_fintype fun x hx => Sec6.conj_mem_thetaQuotCentralizer hx (hLA ha)⟩
  rcases faithful_or_central hst hS hAE hDK hAK hAD (fun d hd => hEexp d hd.1)
      (fun d hd hdA => mem_zpowers_of_mem_A hctx hd hdA) hc3 with hfaith | hcen
  ·
    right
    have hKD : K ⊔ D ≤ M := sup_le (le_of_mem_oTwoComponentsIn hK) (hDE.trans hEM)
    have hKD4 : SectionFourHyp ↥(K ⊔ D) :=
      hst.toTheoremFourHyp.sectionFourHyp (fun h => hMtop (top_le_iff.mp (h ▸ hKD)))
    obtain ⟨hmodel, f, hf, F, _, _, hF, σ, hσ, ⟨iso⟩, e, heD, hout⟩ :=
      hC G K L D c hKD4 (pCoreOf_ne_bot_of_mem_oTwoComponentsIn hst.charTwoType hM2 hK)
        (isPerfect_of_mem_oTwoComponentsIn hK) (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK)
        hDK hDab hD9 hfaith hLK hcL hcD hc3 hLc
        (Sec18.isSubnormal_subgroupOf_of_le hLsn inf_le_right) hLp hLq htype inf_le_right
    exact ⟨hmodel, e, heD, KFacts.InducesStdKind.triality f hf F hF σ hσ
      (KFacts.inducesKindTriality_graphField hf hF hσ K (hEexp e heD.1) hout iso)⟩
  ·
    left
    exact eq_sup_of_central (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK) hLK (hLK hcL) hc3
      hLc hLsn hLp hL1 hcen

end CFSG.RankThree.PartTwo.Sec19
