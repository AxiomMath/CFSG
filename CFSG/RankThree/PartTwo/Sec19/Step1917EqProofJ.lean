module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsJ
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofPar
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofInv
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step1918ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec19.Step1919O2
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projImage)
open Matrix

@[expose] def KSJParSubfield :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L : Subgroup G) (hLK : L ≤ K) (c : G) (e : ℕ),
    1 ≤ e → 2 ^ e % 3 = 1 →
    Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 (3 * e))) →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 e)) →
    Group.IsPerfect L → c ∈ Subgroup.normalizer (K : Set G) → orderOf c = 3 →
    KFacts.InducesStdKind K c .field → L ≤ Subgroup.centralizer ({c} : Set G) →
    ∀ P : Subgroup (K ⧸ CFSG.pCore 2 K), IsProperParabolic P →
      (∀ k k' : K, (k' : G) = c * k * c⁻¹ → (k : K ⧸ CFSG.pCore 2 K) ∈ P →
        (k' : K ⧸ CFSG.pCore 2 K) ∈ P) →
      IsProperParabolic ((P.comap (Step1911EndProof.phiL hLK)).map
        (QuotientGroup.mk' (CFSG.pCore 2 L)))

namespace Step1917EqProof

variable {G : Type} [Group G] [Finite G]

theorem false_of_inducesTypeOn_three {L : Subgroup G} {x : G} (h : Sec4.InducesTypeOn L x 3)
    {n : ℕ} (hn : 1 ≤ n)
    (hY : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)))
    {Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hQ : IsProperParabolic Q)
    (hxQ : ∀ l l' : L, (l' : G) = x * l * x⁻¹ → (l : L ⧸ aschbacherSolvableCore 3 L) ∈ Q →
      (l' : L ⧸ aschbacherSolvableCore 3 L) ∈ Q) : False := by
  obtain ⟨hx, π, p, f, K', _, hK, hq, e, y, -, hy3, hact⟩ := h
  have hcard := card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, -⟩ := eq_two_of_card hK.prime hK.one_le hn hq hcard (card_kStar hn hY)
  have : Finite K' := hK.finite
  let _ := Fintype.ofFinite K'
  have hK'card : Nat.card K' = 2 ^ f := hK.card
  have : CharP K' 2 := by
    obtain ⟨k, hkp, hk⟩ := FiniteField.card K' (ringChar K')
    rw [Fintype.card_eq_nat_card, hK'card] at hk
    have h2 : 2 ∣ ringChar K' ^ (k : ℕ) := hk ▸ dvd_pow_self 2 (by have := hK.one_le; omega)
    exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hkp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hQ' := Step1910Proof.isProperParabolic_map e hQ
  refine false_of_type3 hQ' hy3 ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  have hl' : x * (l : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx l).mp l.2
  refine ⟨e.toMonoidHom ((⟨x * l * x⁻¹, hl'⟩ : L) : L ⧸ aschbacherSolvableCore 3 L),
    Subgroup.mem_map_of_mem _ (hxQ l ⟨_, hl'⟩ rfl hz), ?_⟩
  have h1 := hact (l : L ⧸ aschbacherSolvableCore 3 L)
  rw [Sec4.thetaQuotMulAut_mk] at h1
  have h2 : (L.normalizerMonoidHom ⟨x, hx⟩) l = ⟨x * l * x⁻¹, hl'⟩ := by
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom]
    rfl
  rw [h2] at h1
  exact h1

theorem exists_orderOf_eq_four {X : Type} [Group X]
    (h : Nonempty (X ≃* QuaternionGroup 2) ∨
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∃ σ : X, orderOf σ = 4 := by
  rcases h with h | h
  · obtain ⟨φ⟩ := h
    exact ⟨φ.symm (QuaternionGroup.xa 0), by
      rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]⟩
  · obtain ⟨φ⟩ := h
    set S : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨!![0, 1; -1, 0], by decide⟩
    have h1 : ¬ S ^ 2 ^ 1 = 1 := by decide
    have h2 : S ^ 2 ^ (1 + 1) = 1 := by decide
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨φ.symm S, by rw [MulEquiv.orderOf_eq]; exact orderOf_eq_prime_pow h1 h2⟩

theorem exists_inv_of_star {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hstar : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    ∃ l ∈ L, ∀ b ∈ A ⊓ L, l ^ 2 * b * (l ^ 2)⁻¹ = b⁻¹ := by
  have hA := Step1916Proof2.isE27_A hctx
  have hcA := Step1916Proof2.mem_A hctx
  have hcL := Step1916Proof2.not_mem_L hctx
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hctx.mem_lA.1 |>
    Sec6.le_centralizer_of_mem_thetaComponentsAt
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3
      (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
      (fun b hb => hA.1.2 b hb.1) (fun b hb => hAcomm c hcA b hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hA.2, hcard])).symm
  obtain ⟨⟨σ, hσmem⟩, hσ4⟩ := exists_orderOf_eq_four hstar
  rw [Subgroup.orderOf_mk] at hσ4
  obtain ⟨l, hlN, hlL, hlσ⟩ := Sec4.mem_autIn_iff.mp hσmem
  have hσpow : ∀ k : ℕ, ∀ a : A, ((σ ^ k) a : G) = l ^ k * a * (l ^ k)⁻¹ := by
    intro k a
    rw [← hlσ, ← map_pow]
    have : ((⟨l, hlN⟩ : Subgroup.normalizer (A : Set G)) ^ k : Subgroup.normalizer (A : Set G)) =
        ⟨l ^ k, Subgroup.pow_mem _ hlN k⟩ := rfl
    rw [this]
    simp [Subgroup.normalizerMonoidHom]
    rfl
  have hlB : ∀ b ∈ A ⊓ L, l * b * l⁻¹ ∈ A ⊓ L := fun b hb =>
    ⟨(Subgroup.mem_normalizer_iff.mp hlN b).mp hb.1, L.mul_mem (L.mul_mem hlL hb.2) (L.inv_mem hlL)⟩
  have hl4 : ∀ b ∈ A ⊓ L, l ^ 4 * b * (l ^ 4)⁻¹ = b := by
    intro b hb
    have h1 := hσpow 4 ⟨b, hb.1⟩
    rw [show σ ^ 4 = 1 from hσ4 ▸ pow_orderOf_eq_one σ, MulAut.one_apply] at h1
    exact h1.symm
  have hl2 : ∃ b ∈ A ⊓ L, l ^ 2 * b * (l ^ 2)⁻¹ ≠ b := by
    by_contra hcon
    push Not at hcon
    have hcl : l ^ 2 * c * (l ^ 2)⁻¹ = c := by
      have : l ^ 2 ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.pow_mem _ (hLc hlL) 2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      rw [this, mul_inv_cancel_right]
    have hAC : A ≤ Subgroup.centralizer ({l ^ 2} : Set G) := by
      rw [hAB, sup_le_iff]
      refine ⟨Subgroup.zpowers_le.mpr ?_, fun b hb => ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp hcl).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp (hcon b hb)).symm
    have hσ2 : σ ^ 2 = 1 := by
      ext a
      rw [hσpow 2 a, MulAut.one_apply]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hAC a.2)
      rw [← this, mul_inv_cancel_right]
    have := orderOf_le_of_pow_eq_one (by norm_num) hσ2
    omega
  exact ⟨l, hlL, inv_of_orderFour (Late.isElemAbelian_of_le hA.1 inf_le_left) h9 hlB hl4 hl2⟩

theorem false_of_inv_of_mulEquiv {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 1 ≤ n)
    (hn3 : 2 ^ n % 3 = 1) (ψ : Q ≃* projSL 3 (GaloisField 2 n)) {P : Subgroup Q}
    (hP : IsProperParabolic P) {B : Subgroup Q} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hBP : ∀ b ∈ B, ∀ p ∈ P, b * p * b⁻¹ ∈ P) {t : Q}
    (ht : ∀ b ∈ B, t * b * t⁻¹ = b⁻¹) : False := by
  refine ksJParInvert n hn hn3 (P.map ψ.toMonoidHom) (Step1910Proof.isProperParabolic_map ψ hP)
    (B.map ψ.toMonoidHom) ?_ ?_ ?_ (ψ t) ?_
  · refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      change (x : projSL 3 (GaloisField 2 n)) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hB.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective ψ.injective, hB9]
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨p, hp, rfl⟩
    exact ⟨b * p * b⁻¹, hBP b hb p hp, by simp⟩
  · rintro _ ⟨b, hb, rfl⟩
    change ψ t * ψ b * (ψ t)⁻¹ = (ψ b)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ht b hb, map_inv]

theorem false_of_star {A L E M K : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M) (hLK : L ≤ K) {n : ℕ} (hn : 1 ≤ n)
    (hKiso : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) (hn3 : 2 ^ n % 3 = 1)
    {P : Subgroup (K ⧸ CFSG.pCore 2 K)} (hP : IsProperParabolic P)
    (hAP : ∀ a ∈ A, ∀ k k' : K, (k' : G) = a * k * a⁻¹ →
      (k : K ⧸ CFSG.pCore 2 K) ∈ P → (k' : K ⧸ CFSG.pCore 2 K) ∈ P)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hstar : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hlL, hlinv⟩ := exists_inv_of_star hctx h9 hstar
  have hA := Step1916Proof2.isE27_A hctx
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set φ := Step1911EndProof.phiL hLK with hφ
  set S : Subgroup L := (A ⊓ L).subgroupOf L with hS
  set B := S.map φ with hB
  have hinj : ∀ a : L, (a : G) ∈ A ⊓ L → φ a = 1 → a = 1 := by
    intro a ha h1
    have hO := (Step1911EndProof.phiL_eq_one_iff hLK a).mp h1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hO⟩
    have h2 : (a : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : (a : G) ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hA.1.2 _ ha.1
    exact Subtype.ext (eq_one_of_pow_two_pow_of_pow_three_pow h2 h3)
  have hB9 : Nat.card B = 9 := by
    have hbij : Function.Bijective (φ.subgroupMap S) := by
      refine ⟨fun x y hxy => ?_, φ.subgroupMap_surjective S⟩
      have h1 : φ ((x : L)⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, inv_mul_eq_one]
        exact congrArg Subtype.val hxy
      have h2 := hinj _ (Subgroup.mem_subgroupOf.mp (S.mul_mem (S.inv_mem x.2) y.2)) h1
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    rw [← Nat.card_eq_of_bijective _ hbij, hS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      change (x : K ⧸ CFSG.pCore 2 K) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAcomm _ (Subgroup.mem_subgroupOf.mp ha).1 _
        (Subgroup.mem_subgroupOf.mp hb).1)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hA.1.2 _ (Subgroup.mem_subgroupOf.mp ha).1)
      rw [this, map_one]
  have hBP : ∀ b ∈ B, ∀ p ∈ P, b * p * b⁻¹ ∈ P := by
    rintro _ ⟨a, ha, rfl⟩ p hp
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective p
    have hk' : (a : G) * k * (a : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem (hLK a.2) k.2)
      (K.inv_mem (hLK a.2))
    have h1 := hAP a (Subgroup.mem_subgroupOf.mp ha).1 k ⟨_, hk'⟩ rfl hp
    convert h1 using 1
    rw [Step1911EndProof.phiL_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
  have hl2L : l ^ 2 ∈ L := L.pow_mem hlL 2
  obtain ⟨ψ⟩ := hKiso
  refine false_of_inv_of_mulEquiv hn hn3 ψ hP hBab hB9 hBP (t := φ ⟨l ^ 2, hl2L⟩) ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hlinv _ (Subgroup.mem_subgroupOf.mp ha)

theorem false_of_typeThree
    (hSub : KSJParSubfield) {A L E M K : Subgroup G} {c x : G} (hctx : Ctx1912 G A c L E M)
    (hθ : aschbacherSolvableCore 3 L = CFSG.pCore 2 L) (hLK : L ≤ K)
    (halt : K = L ⊔ CFSG.Open.pCoreOf 2 K ∨
      ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
        Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p (3 * e) ∧ KFacts.InducesStdKind K c .field)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 1 ≤ n)
    (hKiso : Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)))
    {P : Subgroup (K ⧸ CFSG.pCore 2 K)} (hP : IsProperParabolic P)
    (hAP : ∀ a ∈ A, ∀ k k' : K, (k' : G) = a * k * a⁻¹ →
      (k : K ⧸ CFSG.pCore 2 K) ∈ P → (k' : K ⧸ CFSG.pCore 2 K) ∈ P)
    (hxA : x ∈ A) (hx3 : Sec4.InducesTypeOn L x 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hθO := QuotientGroup.quotientMulEquivOfEq hθ with hθOdef
  have hθO_mk : ∀ m : L, hθO (m : L ⧸ aschbacherSolvableCore 3 L) = (m : L ⧸ CFSG.pCore 2 L) :=
    fun m => QuotientGroup.quotientMulEquivOfEq_mk hθ m
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1 hxA
  rcases halt with hKL | ⟨p, e, hp, he, hLiso, hKiso', hfield⟩
  ·
    obtain ⟨ι, hι⟩ := Step1918Proof.exists_quotientEquiv hLK hKL
    set κ := hθO.trans ι with hκ
    have hκ_mk : ∀ m : L, κ (m : L ⧸ aschbacherSolvableCore 3 L) =
        ((Subgroup.inclusion hLK m : K) : K ⧸ CFSG.pCore 2 K) := fun m => by
      rw [hκ, MulEquiv.trans_apply, hθO_mk, hι]
    have hY : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) := by
      rcases hKiso with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
      · exact Or.inl ⟨κ.trans ψ⟩
      · exact Or.inr ⟨κ.trans ψ⟩
    refine false_of_inducesTypeOn_three hx3 hn hY (Q := P.map κ.symm.toMonoidHom)
      (Step1910Proof.isProperParabolic_map κ.symm hP) ?_
    intro l l' hll' hl
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, hκ_mk] at hl ⊢
    exact hAP x hxA (Subgroup.inclusion hLK l) (Subgroup.inclusion hLK l') hll' hl
  ·
    have he3 : 1 ≤ 3 * e := by omega
    rcases Step1917Steps.three_mul_card_of_isoLThreePi he3 hKiso' with
      ⟨hq1, hf, ⟨φK⟩⟩ | ⟨hq2, hf⟩
    swap
    · obtain ⟨h, -, -⟩ := eq_two_of_card (π := false) hp.out he3 hn hq2
        (by rw [mul_comm]; exact hf.symm) (card_kStar hn hKiso)
      exact Bool.false_ne_true h
    obtain ⟨-, hp2, -⟩ := eq_two_of_card (π := true) hp.out he3 hn hq1
      (by rw [mul_comm]; exact hf.symm) (card_kStar hn hKiso)
    subst hp2
    have h2e : 2 ^ e % 3 = 1 := by
      have e1 : 2 ^ (3 * e) = (2 ^ e) ^ 3 := by rw [mul_comm, pow_mul]
      rw [e1, Nat.pow_mod] at hq1
      obtain ⟨r, hr⟩ : ∃ r, r = 2 ^ e % 3 := ⟨_, rfl⟩
      rw [← hr] at hq1 ⊢
      have : r < 3 := hr ▸ Nat.mod_lt _ (by norm_num)
      interval_cases r <;> first | rfl | (norm_num at hq1)
    obtain ⟨ψL⟩ : Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 e)) := by
      rcases hLiso with ⟨-, hψ⟩ | ⟨h2, -⟩
      · exact hψ
      · omega
    have hcA := Step1916Proof2.mem_A hctx
    have hc3 := Step1916Proof2.orderOf_eq hctx
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      Sec6.le_centralizer_of_mem_thetaComponentsAt hctx.mem_lA.1
    have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hctx.mem_lA.1
    have hQ₀ := hSub G K L hLK c e he h2e ⟨φK⟩ ⟨ψL⟩ hLp (hAK hcA) hc3 hfield hLc P hP
      (hAP c hcA)
    refine false_of_inducesTypeOn_three hx3 he (Or.inr ⟨hθO.trans ψL⟩)
      (Q := ((P.comap (Step1911EndProof.phiL hLK)).map
        (QuotientGroup.mk' (CFSG.pCore 2 L))).map hθO.symm.toMonoidHom)
      (Step1910Proof.isProperParabolic_map hθO.symm hQ₀) ?_
    intro l l' hll' hl
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, hθO_mk] at hl ⊢
    obtain ⟨l₀, hl₀, hl₀l⟩ := hl
    have hl₀' : x * (l₀ : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL l₀).mp l₀.2
    refine ⟨⟨_, hl₀'⟩, ?_, ?_⟩
    ·
      change Step1911EndProof.phiL hLK ⟨_, hl₀'⟩ ∈ P
      rw [Step1911EndProof.phiL_apply]
      have h1 := Subgroup.mem_comap.mp hl₀
      rw [Step1911EndProof.phiL_apply] at h1
      exact hAP x hxA _ _ rfl h1
    ·
      rw [QuotientGroup.mk'_apply] at hl₀l ⊢
      rw [QuotientGroup.eq] at hl₀l ⊢
      rw [Sec18.mem_pCore_iff_mem_pCoreOf] at hl₀l ⊢
      have hxO : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxL
      have h1 := (Subgroup.mem_normalizer_iff.mp hxO _).mp hl₀l
      convert h1 using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hll']
      group

end Step1917EqProof

open Step1917EqProof in
theorem step1917JPar_of
    (h1913 : Step1913) (h131 : Item131) (hSub : KSJParSubfield) :
    Step1917JPar := by
  intro G _ _ A c L E M hctx hLM K hK hLK halt hAK n hn hKiso P hP hAP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hcL : c ∉ L := Step1916Proof2.not_mem_L hctx
  obtain ⟨hθ, -, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  set hθO := QuotientGroup.quotientMulEquivOfEq hθ with hθOdef
  have halt' : K = L ⊔ CFSG.Open.pCoreOf 2 K ∨
      ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
        Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p (3 * e) ∧ KFacts.InducesStdKind K c .field := by
    rcases halt with h | h | ⟨n', -, -, hD4, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      refine Step1911Proof.not_isList194_of_trialityD4 (Or.inl ⟨n, hn, ?_⟩) hD4
      rcases hKiso with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rcases h1913 G A c L E M hctx with ⟨p₀, e₀, hp₀, he₀, hL₀⟩ | ⟨⟨ψ12⟩⟩
  swap
  · have hc12 : Nat.card (L ⧸ CFSG.pCore 2 L) = 95040 := by
      rw [Nat.card_congr ψ12.toEquiv, KFacts.KS14.card_nativeM12]
    rcases halt' with hKL | ⟨p, e, hp, he, hLiso, -, -⟩
    · obtain ⟨ι, -⟩ := Step1918Proof.exists_quotientEquiv hLK hKL
      refine false_of_kStar_card hn ?_ (Or.inr (Or.inr (Or.inl hc12)))
      rcases hKiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact Or.inl ⟨ι.trans φ⟩
      · exact Or.inr ⟨ι.trans φ⟩
    · exact false_of_isoLThreePi_card he hLiso (Or.inr (Or.inr (Or.inl hc12)))
  have hKpsl : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)) ∧ 2 ^ n % 3 = 1 := by
    obtain ⟨π, p, f, hp, hf, hq, h3⟩ : ∃ (π : Bool) (p f : ℕ), p.Prime ∧ 1 ≤ f ∧
        Sec4.ModThree π (p ^ f) ∧ Nat.card (K ⧸ CFSG.pCore 2 K) * 3 =
          (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
      rcases halt' with hKL | ⟨p, e, hp, he, -, hKiso', -⟩
      · obtain ⟨ι, -⟩ := Step1918Proof.exists_quotientEquiv hLK hKL
        rw [← Nat.card_congr ι.toEquiv]
        rcases Step1917Steps.three_mul_card_of_isoLThreePi he₀ hL₀ with ⟨hq, hf, -⟩ | ⟨hq, hf⟩
        · exact ⟨true, p₀, e₀, hp₀.out, he₀, hq, by rw [Bool.cond_true, hf, mul_comm]⟩
        · exact ⟨false, p₀, e₀, hp₀.out, he₀, hq, by rw [Bool.cond_false, hf, mul_comm]⟩
      · have he3 : 1 ≤ 3 * e := by omega
        rcases Step1917Steps.three_mul_card_of_isoLThreePi he3 hKiso' with
          ⟨hq, hf, -⟩ | ⟨hq, hf⟩
        · exact ⟨true, p, 3 * e, hp.out, he3, hq, by rw [Bool.cond_true, hf, mul_comm]⟩
        · exact ⟨false, p, 3 * e, hp.out, he3, hq, by rw [Bool.cond_false, hf, mul_comm]⟩
    exact psl_of_card hp hf hn hq h3 hKiso
  obtain ⟨⟨-, -⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := Sec13.sporadicModels131
  rcases cases131 h131 Sec13.sporadicModels131 Sec13.slTwoCenter hD with
    ⟨-, h9, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, -, -, x, hxA, hx3⟩ | ⟨hcL', -⟩
  · rcases hcase with ⟨-, hstar⟩ | ⟨⟨φ7⟩, -⟩ | ⟨⟨φ22⟩, -⟩
    ·
      exact false_of_star hctx hLK hn hKpsl.1 hKpsl.2 hP hAP h9 hstar
    · refine false_of_isoLThreePi_card he₀ hL₀ (Or.inl ?_)
      rw [Nat.card_congr (hθO.symm.trans φ7).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    · refine false_of_isoLThreePi_card he₀ hL₀ (Or.inr (Or.inl ?_))
      rw [Nat.card_congr (hθO.symm.trans φ22).toEquiv, KFacts.KS14.card_nativeM22]
  · rcases hcase with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      refine false_of_isoLThreePi_card he₀ hL₀ (Or.inr (Or.inr (Or.inl ?_)))
      rw [Nat.card_congr (hθO.symm.trans ψ).toEquiv, KFacts.KS14.card_nativeM12]
    · obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      refine false_of_isoLThreePi_card he₀ hL₀ (Or.inr (Or.inr (Or.inr ?_)))
      rw [Nat.card_congr (hθO.symm.trans ψ).toEquiv, KFacts.KS14.card_nativeJ2]
  ·
    exact false_of_typeThree hSub hctx hθ hLK halt' hAK hn hKiso hP hAP hxA hx3
  · exact hcL hcL'

end CFSG.RankThree.PartTwo.Sec19
