module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

@[expose] def KS142J2Sig : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 → ∀ Y : Subgroup X, ¬ 3 ∣ Nat.card Y →
      E ≤ Subgroup.normalizer (Y : Set X) → IsPGroup 2 Y

namespace Res5TypesHJ

theorem perm6_order15 : ∀ g : Equiv.Perm (Fin 6), g ^ 15 = 1 → g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem perm3_facts : ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 →
    ∃ h : Equiv.Perm (Fin 3), (h * t * h⁻¹ * t) ^ 3 = 1 ∧ h * t * h⁻¹ * t ≠ 1 := by
  decide +kernel

theorem commute_of_conj_eq_pow {H : Type*} [Group H] {x r : H} (hx : x ^ 3 = 1)
    (hr : r ^ 5 = 1) {k : ℕ} (hk : x * r * x⁻¹ = r ^ k) : x * r = r * x := by
  have hpow : ∀ m : ℕ, x * r ^ m * x⁻¹ = r ^ (k * m) := by
    intro m
    rw [← conj_pow, hk, ← pow_mul]
  have h2 : x ^ 2 * r * (x ^ 2)⁻¹ = r ^ (k * k) := by
    rw [show x ^ 2 * r * (x ^ 2)⁻¹ = x * (x * r * x⁻¹) * x⁻¹ by
      rw [pow_two, mul_inv_rev]; simp only [mul_assoc], hk, hpow]
  have h3 : x ^ 3 * r * (x ^ 3)⁻¹ = r ^ (k * (k * k)) := by
    rw [show x ^ 3 * r * (x ^ 3)⁻¹ = x * (x ^ 2 * r * (x ^ 2)⁻¹) * x⁻¹ by
      rw [pow_succ' x 2, mul_inv_rev]; simp only [mul_assoc], h2, hpow]
  rw [hx, one_mul, inv_one, mul_one] at h3
  have hmod : k * (k * k) ≡ 1 [MOD orderOf r] := by
    rw [← pow_eq_pow_iff_modEq, pow_one]
    exact h3.symm
  have hk1 : k ≡ 1 [MOD orderOf r] := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hr) with
      h | h
    · rw [h]
      exact Nat.modEq_one
    · rw [h] at hmod ⊢
      have hz : ∀ z : ZMod 5, z * (z * z) = 1 → z = 1 := by decide
      have h1 : ((k * (k * k) : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      push_cast at h1
      exact (ZMod.natCast_eq_natCast_iff k 1 5).mp (by push_cast; exact hz _ h1)
  have hrk : r ^ k = r ^ 1 := pow_eq_pow_iff_modEq.mpr hk1
  rw [pow_one] at hrk
  rw [hrk] at hk
  calc x * r = x * r * x⁻¹ * x := by group
    _ = r * x := by rw [hk]

theorem exists_sylow_normalized {K : Type*} [Group K] [Finite K] (r : ℕ) [Fact r.Prime]
    {W E : Subgroup K} (hE : IsPGroup 3 E) (hEW : E ≤ Subgroup.normalizer (W : Set K))
    (hW : ¬ 3 ∣ Nat.card W) :
    ∃ T : Sylow r W, E ≤ Subgroup.normalizer
      (((T : Subgroup W).map W.subtype : Subgroup K) : Set K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : E →* MulAut W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hEW)
  let _inst : MulDistribMulAction E W := MulDistribMulAction.compHom W φ
  have hcard : ¬ 3 ∣ Nat.card (Sylow r W) := by
    intro h
    apply hW
    obtain P : Sylow r W := default
    exact h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r W) hcard
  have key : ∀ g ∈ E, ∀ y ∈ (P : Subgroup W).map W.subtype,
      g * y * g⁻¹ ∈ (P : Subgroup W).map W.subtype := by
    intro g hg y hy
    obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : (⟨g, hg⟩ : E) • P = P := hP ⟨g, hg⟩
    have h2 : ((⟨g, hg⟩ : E) • x : W) ∈ ((⟨g, hg⟩ : E) • (P : Subgroup W)) :=
      Subgroup.smul_mem_pointwise_smul x _ _ hxP
    have h3 : ((⟨g, hg⟩ : E) • (P : Subgroup W)) = (P : Subgroup W) := by
      rw [← Sylow.pointwise_smul_def, h1]
    rw [h3] at h2
    exact ⟨_, h2, rfl⟩
  refine ⟨P, fun g hg => Subgroup.mem_normalizer_fintype fun y hy => key g hg y hy⟩

theorem card_le_four_of_normal
    {K : Subgroup (Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4)))} (hK : K.Normal)
    (h2 : IsPGroup 2 K) : Nat.card K ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := MonoidHom.fst (Equiv.Perm (Fin 3)) ↥(alternatingGroup (Fin 4)) with hf
  have hfK : ∀ k ∈ K, (k : Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4))).1 = 1 := by
    intro k hk
    by_contra hne
    obtain ⟨n, hn⟩ := h2 ⟨k, hk⟩
    have hk2 : k.1 ^ 2 ^ n = 1 := by
      have := congrArg (fun y : K => ((y : Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4))).1)) hn
      simpa using this
    have hinv : k.1 ^ 2 = 1 := by
      have hdiv : orderOf k.1 ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hk2
      have h6 : orderOf k.1 ∣ 6 := by
        have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
          rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
          rfl
        exact hc ▸ orderOf_dvd_natCard k.1
      have h2' : orderOf k.1 ∣ 2 := by
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
        rw [hm] at h6 ⊢
        rcases m with _ | _ | m
        · simp
        · simp
        · exfalso
          have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans h6
          omega
      exact orderOf_dvd_iff_pow_eq_one.mp h2'
    obtain ⟨h, h3, h1⟩ := perm3_facts k.1 hinv hne
    set k' : Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4)) := (h, 1) * k * (h, 1)⁻¹ * k
    have hk' : k' ∈ K := mul_mem (hK.conj_mem k hk (h, 1)) hk
    obtain ⟨m, hm⟩ := h2 ⟨k', hk'⟩
    have hm' : (h * k.1 * h⁻¹ * k.1) ^ 2 ^ m = 1 := by
      have := congrArg (fun y : K => ((y : Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4))).1)) hm
      simpa [k'] using this
    have ho : orderOf (h * k.1 * h⁻¹ * k.1) = 3 := orderOf_eq_prime h3 h1
    have hd : 3 ∣ 2 ^ m := ho ▸ orderOf_dvd_of_pow_eq_one hm'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  set g := MonoidHom.snd (Equiv.Perm (Fin 3)) ↥(alternatingGroup (Fin 4)) with hg
  have hinj : Function.Injective (g.comp K.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · rw [hfK x x.2, hfK y y.2]
    · exact hxy
  have hcard : Nat.card K ∣ 12 := by
    have h1 := Subgroup.card_subgroup_dvd_card (g.comp K.subtype).range
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm] at h1
    have h12 : Nat.card ↥(alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rwa [h12] at h1
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  rw [hm] at hcard ⊢
  rcases m with _ | _ | _ | m
  · norm_num
  · norm_num
  · norm_num
  · exfalso
    have : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hcard
    omega

theorem theta_eq_pCore_two {C : Type*} [Group C] [Finite C] (hC : Nat.card C ∣ 8 * 9) :
    aschbacherSolvableCore 3 C = CFSG.pCore 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hchar, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization (H := C)
    Nat.prime_three
  apply le_antisymm
  · have hdvd : Nat.card (aschbacherSolvableCore 3 C) ∣ 8 := by
      have hcop : Nat.Coprime (Nat.card (aschbacherSolvableCore 3 C)) 9 :=
        (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)).symm
      exact hcop.dvd_of_dvd_mul_right ((Subgroup.card_subgroup_dvd_card _).trans hC)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (aschbacherSolvableCore 3 C) ∣ 2 ^ 3 from hdvd)
    have hp : IsPGroup 2 (aschbacherSolvableCore 3 C) := IsPGroup.of_card hm
    have := hchar
    exact le_sSup ⟨inferInstance, hp⟩
  · have hp : IsPGroup 2 (CFSG.pCore 2 C) := CFSG.pCore_isPGroup
    have hn : (CFSG.pCore 2 C).Normal := CFSG.pCore_normal
    have hs : Group.IsSolvable (CFSG.pCore 2 C) := by
      have := hp.isNilpotent
      infer_instance
    refine hmax _ hn hs fun h3 => ?_
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    rw [hm] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

section Setup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem inf_centralizer_eq (P : Subgroup X) :
    P ⊓ Subgroup.centralizer (P : Set X) = (Subgroup.center ↥P).map P.subtype := by
  ext x
  constructor
  · rintro ⟨hxP, hxC⟩
    exact ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)⟩

omit [Finite X] in
theorem card_inf_centralizer {P : Subgroup X} (hP : Sec4.IsHeisThree ↥P) :
    Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set X)) = 3 := by
  rw [inf_centralizer_eq, Subgroup.card_map_of_injective P.subtype_injective]
  exact hP.1.2.2.2

theorem inf_centralizer_le {P E : Subgroup X} (hP : Sec4.IsHeisThree ↥P) (hEP : E ≤ P)
    (hE9 : Nat.card E = 9) : P ⊓ Subgroup.centralizer (P : Set X) ≤ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := P ⊓ Subgroup.centralizer (P : Set X) with hZ
  have hZ3 : Nat.card Z = 3 := card_inf_centralizer hP
  by_contra hne
  have hinf : E ⊓ Z = ⊥ := by
    have h1 : Nat.card (E ⊓ Z : Subgroup X) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hne
      have h2 : E ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZ3])
      rw [← h2]
      exact inf_le_left
  have hcomm : ∀ x ∈ E, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x (hEP hx)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E Z hcomm
  rw [hinf, Subgroup.card_bot, mul_one, hE9, hZ3] at hcard
  have hsup : E ⊔ Z = P :=
    Subgroup.eq_of_le_of_card_ge (sup_le hEP inf_le_left) (by rw [hP.2.1, hcard])
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := E)
      (by rw [hE9]; norm_num)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPE : E ⊔ Z ≤ Subgroup.centralizer (E : Set X) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hEab y hy x hx)
      (fun z hz => Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy z hz)
  rw [hsup] at hPE
  have hEC : E ≤ Subgroup.centralizer (P : Set X) := Subgroup.le_centralizer_iff.mp hPE
  have hPC : E ⊔ Z ≤ Subgroup.centralizer (P : Set X) := sup_le hEC inf_le_right
  rw [hsup] at hPC
  have hZP : Z = P := inf_eq_left.mpr hPC
  rw [hZP, hP.2.1] at hZ3
  norm_num at hZ3

theorem conj_mem_of_mem {P E : Subgroup X} (hP : Sec4.IsHeisThree ↥P) (hEP : E ≤ P)
    (hE9 : Nat.card E = 9) {x : X} (hx : x ∈ P) {e : X} (he : e ∈ E) : x * e * x⁻¹ ∈ E := by
  have hZE := inf_centralizer_le hP hEP hE9
  have hc : ⁅(⟨x, hx⟩ : P), (⟨e, hEP he⟩ : P)⁆ ∈ Subgroup.center ↥P := by
    rw [← hP.1.2.1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcZ : ⁅x, e⁆ ∈ P ⊓ Subgroup.centralizer (P : Set X) := by
    rw [inf_centralizer_eq]
    exact ⟨_, hc, rfl⟩
  have h1 : x * e * x⁻¹ = ⁅x, e⁆ * e := by
    rw [commutatorElement_def]
    group
  rw [h1]
  exact mul_mem (hZE hcZ) he

omit [Finite X] in
theorem isElemAbelian_of_le {P E : Subgroup X} (hP : Sec4.IsHeisThree ↥P) (hEP : E ≤ P)
    (hE9 : Nat.card E = 9) : CFSG.Assembly.IsElemAbelian 3 E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE9]; norm_num),
    fun e he => ?_⟩
  have h := Monoid.pow_exponent_eq_one (⟨e, hEP he⟩ : P)
  rw [hP.2.2] at h
  exact congrArg Subtype.val h

omit [Finite X] in
theorem centralizer_le_normalizer_zpowers (e : X) :
    Subgroup.centralizer ({e} : Set X) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup X) : Set X) := by
  rw [show Subgroup.centralizer ({e} : Set X) =
      Subgroup.centralizer ((Subgroup.zpowers e : Subgroup X) : Set X) by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]]
  exact Subgroup.centralizer_le_normalizer _

omit [Finite X] in
theorem card_centralizer_dvd {e : X}
    (hN : Nonempty (Subgroup.normalizer ((Subgroup.zpowers e : Subgroup X) : Set X) ≃*
      Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4)))) :
    Nat.card (Subgroup.centralizer ({e} : Set X)) ∣ 8 * 9 := by
  obtain ⟨ι⟩ := hN
  have h72 : Nat.card (Subgroup.normalizer ((Subgroup.zpowers e : Subgroup X) : Set X)) =
      8 * 9 := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [← h72]
  exact Subgroup.card_dvd_of_le (centralizer_le_normalizer_zpowers e)

theorem centralizer_eq_of_mem {Z : Subgroup X} (hZ3 : Nat.card Z = 3) {z : X} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : Subgroup.centralizer ({z} : Set X) = Subgroup.centralizer (Z : Set X) := by
  have hzZ : Subgroup.zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hZ3, Nat.card_zpowers]
    have hd : orderOf z ∣ 3 := hZ3 ▸ Subgroup.orderOf_dvd_natCard Z hz
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h.ge
  rw [← hzZ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem card_of_isExtOf {C : Type*} [Group C] [Finite C]
    (hext : Sec4.IsExtOf C (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))) :
    Nat.card C = 8 * 135 := by
  obtain ⟨K, _, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr eQ.toEquiv,
    Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rfl

theorem pCore_two_eq_bot_of_isExtOf {C : Type*} [Group C] [Finite C]
    (hext : Sec4.IsExtOf C (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))) :
    CFSG.pCore 2 C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  set O := CFSG.pCore 2 C with hO
  have hOn : O.Normal := CFSG.pCore_normal
  have hOp : IsPGroup 2 O := CFSG.pCore_isPGroup
  set π : C →* ↥(alternatingGroup (Fin 6)) := eQ.toMonoidHom.comp (QuotientGroup.mk' K) with hπ
  have hπs : Function.Surjective π := eQ.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : π.ker = K := by
    ext g
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hS : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hmap : O.map π = ⊥ := by
    rcases (hOn.map π hπs).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (O.map π) := hOp.map π
      rw [h] at hp
      obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at hn
      have h3 : 3 ∣ 2 ^ n := by
        rw [← hn]
        decide
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  have hOK : O ≤ K := by
    rw [Subgroup.map_eq_bot_iff, hker] at hmap
    exact hmap
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  obtain ⟨n, hn⟩ := hOp.exists_card_eq
  have hd : 2 ^ n ∣ 3 := hn ▸ hK3 ▸ Subgroup.card_dvd_of_le hOK
  rcases n with _ | n
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero])
  · exfalso
    have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hd
    omega

theorem false_of_isExtOf {C : Type*} [Group C] [Finite C]
    (hext : Sec4.IsExtOf C (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)))
    {U F : Subgroup C} (hU : Nat.card U = 5) (hF : Nat.card F = 9) (hF3 : ∀ f ∈ F, f ^ 3 = 1)
    (hFU : F ≤ Subgroup.normalizer (U : Set C)) : False := by
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  set π : C →* ↥(alternatingGroup (Fin 6)) := eQ.toMonoidHom.comp (QuotientGroup.mk' K) with hπ
  have hker : π.ker = K := by
    ext g
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  obtain ⟨f, hfF, hfK⟩ : ∃ f ∈ F, f ∉ K := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (H := F) (K := K) h
    rw [hF, hK3] at h1
    norm_num at h1
  obtain ⟨u, huU, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left fun h => by
    rw [h, Subgroup.card_bot] at hU
    norm_num at hU
  have hu5 : u ^ 5 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hU ▸ Subgroup.orderOf_dvd_natCard U huU)
  have huZ : Subgroup.zpowers u = U := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huU) ?_
    rw [hU, Nat.card_zpowers]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hu5) with
      h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h.ge
  have hfu : f * u * f⁻¹ ∈ Subgroup.zpowers u := by
    rw [huZ]
    exact (Subgroup.mem_normalizer_iff.mp (hFU hfF) u).mp huU
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hfu)
  set x := π f with hx
  set r := π u with hr
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hF3 f hfF, map_one]
  have hx1 : x ≠ 1 := fun h => hfK (by rw [← hker]; exact h)
  have hr5 : r ^ 5 = 1 := by rw [hr, ← map_pow, hu5, map_one]
  have key : ∀ m : ℕ, m ∣ 3 → m ∣ 5 → m = 1 := fun m h1 h2 => by
    have h := Nat.dvd_gcd h1 h2
    norm_num at h
    exact h
  have hr1 : r ≠ 1 := by
    intro h
    have huK : u ∈ K := by rw [← hker]; exact h
    have h1 : orderOf u ∣ 3 := hK3 ▸ Subgroup.orderOf_dvd_natCard K huK
    have h2 : orderOf u ∣ 5 := orderOf_dvd_of_pow_eq_one hu5
    exact hu1 (orderOf_eq_one_iff.mp (key _ h1 h2))
  have hxr : x * r * x⁻¹ = r ^ k := by
    rw [hx, hr, ← map_inv, ← map_mul, ← map_mul, ← hk, map_pow]
  have hc : x * r = r * x := commute_of_conj_eq_pow hx3 hr5 hxr
  have h15 := perm6_order15 ((x * r : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) (by
    rw [← Subgroup.coe_pow, (Commute.mul_pow hc 15),
      show (15 : ℕ) = 3 * 5 by rfl, pow_mul, hx3, one_pow, one_mul, pow_mul', hr5, one_pow]
    rfl)
  rcases h15 with h | h
  · apply hr1
    have h1 : (x * r) ^ 3 = 1 := Subtype.ext h
    rw [Commute.mul_pow hc, hx3, one_mul] at h1
    have h2 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf r ∣ 5 := orderOf_dvd_of_pow_eq_one hr5
    exact orderOf_eq_one_iff.mp (key _ h2 h3)
  · apply hx1
    have h1 : (x * r) ^ 5 = 1 := Subtype.ext h
    rw [Commute.mul_pow hc, hr5, mul_one] at h1
    have h2 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    exact orderOf_eq_one_iff.mp (key _ h3 h2)

end Setup

theorem prime_dvd_72 {q : ℕ} (hq : q.Prime) (h : q ∣ 8 * 9) : q = 2 ∨ q = 3 := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow (show q ∣ 2 ^ 3 from h)))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
      (hq.dvd_of_dvd_pow (show q ∣ 3 ^ 2 from h)))

theorem prime_dvd_1080 {q : ℕ} (hq : q.Prime) (h : q ∣ 8 * 135) : q = 2 ∨ q = 3 ∨ q = 5 := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow (show q ∣ 2 ^ 3 from h)))
  · rcases (Nat.Prime.dvd_mul hq).mp (show q ∣ 3 ^ 3 * 5 from h) with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (hq.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h))

theorem eq_bot_of_isPGroup_of_dvd {G : Type*} [Group G] [Finite G] {q m : ℕ} [Fact q.Prime]
    {H : Subgroup G} (hH : IsPGroup q H) (hm : Nat.card H ∣ m) (hq : ¬ q ∣ m) : H = ⊥ := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd ((dvd_pow_self q (Nat.succ_ne_zero k)).trans (hk ▸ hm)) hq

theorem not_three_dvd_of_isPGroup_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsPGroup 2 H) : ¬ 3 ∣ Nat.card H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

section Sig

variable {X : Type} [Group X] [Finite X]

theorem ks142J2Sig_of (h415 : Sec4.Item4_15) : KS142J2Sig := by
  intro X _ _ hX E hE9 Y hY3 hYE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, h4, -⟩ := h415 X hX P Z rfl _ rfl
  have hEΔ : E ∈ {B : Subgroup X | B ≤ P ∧ Nat.card B = 9} := ⟨hEP, hE9⟩
  have hZ3 : Nat.card Z = 3 := card_inf_centralizer hHeis
  have hEab := isElemAbelian_of_le hHeis hEP hE9
  have hEC : E ≤ Subgroup.centralizer (Z : Set X) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 e (hEP he)).symm
  refine IsPGroup.of_card (n := (Nat.card Y).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqY => ?_)
  by_contra hq2
  have hq3 : q ≠ 3 := fun h => hY3 (h ▸ hqY)
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T, hT⟩ := exists_sylow_normalized q hE3 hYE hY3
  set R := (T : Subgroup Y).map Y.subtype with hR
  have hRq : q ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective Y.subtype_injective]
    have h1 := T.pow_dvd_card_of_pow_dvd_card (n := 1) (by rwa [pow_one])
    rwa [pow_one] at h1
  have hRp : IsPGroup q R := T.isPGroup'.map Y.subtype
  have hR3 : Nat.Coprime 3 (Nat.card R) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => hY3 (h.trans ?_)
    rw [hR, Subgroup.card_map_of_injective Y.subtype_injective]
    exact Subgroup.card_subgroup_dvd_card _
  have hRbot : R ≤ ⊥ := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hEab (by rw [hE9]; norm_num) hT
      hR3 fun e he he1 => ?_
    have hRCp : IsPGroup q (R ⊓ Subgroup.centralizer ({e} : Set X) : Subgroup X) :=
      hRp.to_le inf_le_left
    by_cases heZ : e ∈ Z
    · rw [centralizer_eq_of_mem hZ3 heZ he1]
      set H := R ⊓ Subgroup.centralizer (Z : Set X) with hH
      have hHp : IsPGroup q H := hRp.to_le inf_le_left
      have hHd : Nat.card H ∣ 8 * 135 := (Subgroup.card_dvd_of_le inf_le_right).trans
        (card_of_isExtOf hext).dvd
      by_cases hq5 : q = 5
      · subst hq5
        obtain ⟨k, hk⟩ := hHp.exists_card_eq
        rcases k with _ | _ | k
        · exact (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])).le
        · exfalso
          have hHC : H ≤ Subgroup.centralizer (Z : Set X) := inf_le_right
          have hEH : E ≤ Subgroup.normalizer (H : Set X) :=
            Late.le_normalizer_inf hT (hEC.trans Subgroup.le_normalizer)
          refine false_of_isExtOf hext (U := H.subgroupOf _) (F := E.subgroupOf _) ?_ ?_ ?_ ?_
          · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv, hk, pow_one]
          · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hE9]
          · intro f hf
            exact Subtype.ext (hEab.2 _ (Subgroup.mem_subgroupOf.mp hf))
          · intro f hf
            refine Subgroup.mem_normalizer_fintype fun u hu => ?_
            rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
            exact (Subgroup.mem_normalizer_iff.mp (hEH (Subgroup.mem_subgroupOf.mp hf)) _).mp hu
        · exfalso
          have h25 : 5 ^ 2 ∣ 8 * 135 :=
            (pow_dvd_pow 5 (by omega)).trans (hk ▸ hHd)
          omega
      · refine (eq_bot_of_isPGroup_of_dvd hHp hHd fun h => ?_).le
        rcases prime_dvd_1080 hq h with h | h | h
        · exact hq2 h
        · exact hq3 h
        · exact hq5 h
    · refine (eq_bot_of_isPGroup_of_dvd hRCp ((Subgroup.card_dvd_of_le inf_le_right).trans
        (card_centralizer_dvd (h4 E hEΔ e he heZ).2.1)) fun h => ?_).le
      rcases prime_dvd_72 hq h with h | h
      · exact hq2 h
      · exact hq3 h
  have h1 : Nat.card R = 1 := by
    rw [le_bot_iff.mp hRbot, Subgroup.card_bot]
  rw [h1] at hRq
  exact hq.one_lt.ne' (Nat.dvd_one.mp hRq)

end Sig

section List

variable {X : Type} [Group X] [Finite X]

theorem map_conj_centralizer_eq {v n : X}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup X) : Set X)) :
    (Subgroup.centralizer ({v} : Set X)).map (MulAut.conj n).toMonoidHom =
      Subgroup.centralizer ({v} : Set X) := by
  have hle : (Subgroup.centralizer ({v} : Set X)).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.centralizer ({v} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    have hv' : n⁻¹ * v * n⁻¹⁻¹ ∈ Subgroup.zpowers v :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hn) v).mp (Subgroup.mem_zpowers v)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv'
    have hyv : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hyk : y * v ^ k = v ^ k * y := ((Commute.zpow_right hyv k)).eq
    have hv : n * v ^ k * n⁻¹ = v := by
      rw [hk]
      group
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * y * n⁻¹ * v = n * y * n⁻¹ * (n * v ^ k * n⁻¹) := by rw [hv]
      _ = n * (y * v ^ k) * n⁻¹ := by group
      _ = n * (v ^ k * y) * n⁻¹ := by rw [hyk]
      _ = (n * v ^ k * n⁻¹) * (n * y * n⁻¹) := by group
      _ = v * (n * y * n⁻¹) := by rw [hv]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])

theorem card_pCore_two_le {v : X}
    (hN : Nonempty (Subgroup.normalizer ((Subgroup.zpowers v : Subgroup X) : Set X) ≃*
      Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 4)))) :
    Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({v} : Set X))) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := hN
  set N := Subgroup.normalizer ((Subgroup.zpowers v : Subgroup X) : Set X) with hNdef
  set O := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({v} : Set X)) with hO
  have hOC : O ≤ Subgroup.centralizer ({v} : Set X) := Subgroup.map_subtype_le _
  have hON : O ≤ N := hOC.trans (centralizer_le_normalizer_zpowers v)
  have hOp : IsPGroup 2 O := CFSG.pCore_isPGroup.map _
  have hNO : N ≤ Subgroup.normalizer (O : Set X) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change O.map (MulAut.conj n).toMonoidHom = O
    rw [hO, KFacts.KS14.map_inSubgroup_pCore_two, map_conj_centralizer_eq hn]
  have hn : (O.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mpr hNO
  have hKn : ((O.subgroupOf N).map ι.toMonoidHom).Normal := hn.map _ ι.surjective
  have hKp : IsPGroup 2 ((O.subgroupOf N).map ι.toMonoidHom) :=
    (hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hON).symm).map _
  have h4 := card_le_four_of_normal hKn hKp
  rwa [Subgroup.card_map_of_injective ι.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv] at h4

theorem ks142J2List_of (h415 : Sec4.Item4_15) (hsig : KS142J2Sig) : KS142J2List := by
  intro X _ _ hX E hE9 Y hY3 hYE hYmax
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 Y := hsig X hX E hE9 Y hY3 hYE
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, h4, h5⟩ := h415 X hX P Z rfl _ rfl
  have hEΔ : E ∈ {B : Subgroup X | B ≤ P ∧ Nat.card B = 9} := ⟨hEP, hE9⟩
  obtain ⟨S, -, hSset, -, ⟨T, ⟨eT⟩⟩, a, b, hab, hprod⟩ := h5 E hEΔ
  have hZ3 : Nat.card Z = 3 := card_inf_centralizer hHeis
  have hZE : Z ≤ E := inf_centralizer_le hHeis hEP hE9
  have hEab := isElemAbelian_of_le hHeis hEP hE9
  have hYmem : Y ∈ maxInvariantPiSubgroups ⊤ E (piOf 2) := by
    refine ⟨(mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hY2, hYE⟩,
      fun Y' hY' hYY' => ?_⟩
    obtain ⟨-, hY'2, hY'E⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hY'
    exact (hYmax Y' (not_three_dvd_of_isPGroup_two hY'2) hY'E hYY').le
  rw [hSset] at hYmem
  obtain ⟨x, hxP, hxY⟩ := hYmem
  set f := MulAut.conj x⁻¹ with hf
  have hYS : Y = S.map f.toMonoidHom := hxY.symm
  have hxinv : x⁻¹ ∈ (P : Subgroup X) := inv_mem hxP
  have hfZ : ∀ z ∈ Z, f z = z := by
    intro z hz
    change x⁻¹ * z * x⁻¹⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hz.2 x⁻¹ hxinv]
    group
  have hfE : ∀ e ∈ E, f e ∈ E := fun e he => conj_mem_of_mem hHeis hEP hE9 hxinv he
  have hfCZ : (Subgroup.centralizer (Z : Set X)).map f.toMonoidHom =
      Subgroup.centralizer (Z : Set X) := by
    have hle : (Subgroup.centralizer (Z : Set X)).map f.toMonoidHom ≤
        Subgroup.centralizer (Z : Set X) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [← hfZ z hz]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy z hz]
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective f.injective])
  have e1 : f '' ((S ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) : Set X) =
      ((Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) : Set X) := by
    rw [← MulEquiv.coe_toMonoidHom, ← Subgroup.coe_map,
      Subgroup.map_inf_eq _ _ _ f.injective, hfCZ, ← hYS]
  have e2 : ∀ g : X, f '' (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({g} : Set X)) :
      Set X) = (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({f g} : Set X)) : Set X) := by
    intro g
    rw [← MulEquiv.coe_toMonoidHom, ← Subgroup.coe_map, KFacts.KS14.map_inSubgroup_pCore_two,
      CFSG.RankThree.PartTwo.map_centralizer_singleton]
    rfl
  have e3 : f '' (S : Set X) = (Y : Set X) := by
    rw [hYS, ← MulEquiv.coe_toMonoidHom, Subgroup.coe_map]
  have hpieces : ((Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) : Set X) *
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({f a} : Set X)) : Set X) *
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({f b} : Set X)) : Set X) = Y := by
    have h1 := congrArg (fun s : Set X => f '' s) hprod
    simp only [Set.image_mul] at h1
    rw [e1, e2, e2, e3] at h1
    exact h1
  have haE : a ∈ E := hab ▸ Subgroup.subset_closure (Set.mem_insert a {b})
  have hbE : b ∈ E := hab ▸ Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  set a' := f a with ha'
  set b' := f b with hb'
  have ha'E : a' ∈ E := hfE a haE
  have hb'E : b' ∈ E := hfE b hbE
  have hab' : Subgroup.closure {a', b'} = E := by
    have h1 : (Subgroup.closure {a, b}).map f.toMonoidHom = Subgroup.closure {a', b'} := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← h1, hab]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Subgroup.card_map_of_injective f.injective])
    rintro _ ⟨e, he, rfl⟩
    exact hfE e he
  have eY : ↥Y ≃* ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) :=
    (MulEquiv.subgroupCongr hYS).trans ((S.equivMapOfInjective _ f.injective).symm.trans eT)
  have hY64 : Nat.card Y = 2 ^ 6 := by
    rw [Nat.card_congr eY.toEquiv, Sylow.card_eq_multiplicity, KFacts.KS14.card_projSL_three_four,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_two
        (show 20160 = 2 ^ 6 * 315 by norm_num) (by norm_num)]
  have hYZ8 : Nat.card (Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) ≤ 8 := by
    have hp : IsPGroup 2 (Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) :=
      hY2.to_le inf_le_left
    have hd : Nat.card (Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) ∣ 8 * 135 :=
      (Subgroup.card_dvd_of_le inf_le_right).trans (card_of_isExtOf hext).dvd
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at hd ⊢
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have : 2 ^ 4 ∣ 8 * 135 := (pow_dvd_pow 2 (by omega)).trans hd
      omega
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hO2Z : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (Z : Set X)) = ⊥ := by
    rw [inSubgroup, pCore_two_eq_bot_of_isExtOf hext, Subgroup.map_bot]
  have hcl : ∀ u v : X, u ∈ Z → v ∈ Z → Subgroup.closure {u, v} ≠ E := by
    intro u v hu hv h
    have hEZ : E ≤ Z := h ▸ (Subgroup.closure_le _).mpr (by
      rintro _ (rfl | rfl)
      · exact hu
      · exact hv)
    have h1 := Subgroup.card_le_of_le hEZ
    rw [hE9, hZ3] at h1
    norm_num at h1
  have hne1 : ∀ u v : X, v ∈ E → Subgroup.closure {u, v} = E → u ≠ 1 := by
    intro u v hv h hu
    rw [hu, Subgroup.closure_insert_one, ← Subgroup.zpowers_eq_closure] at h
    have h1 : Nat.card (Subgroup.zpowers v) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (hEab.2 v hv)
    rw [h, hE9] at h1
    norm_num at h1
  have hYle : Nat.card Y ≤ Nat.card (Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) *
      Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a'} : Set X))) *
      Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b'} : Set X))) := by
    have e : Nat.card Y = Nat.card ↥(((Y ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) :
        Set X) * (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a'} : Set X)) : Set X) *
        (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b'} : Set X)) : Set X)) := by
      rw [hpieces]
      rfl
    rw [e]
    exact Set.natCard_mul_le.trans (Nat.mul_le_mul_right _ Set.natCard_mul_le)
  have ha'Z : a' ∉ Z := by
    intro ha'Z
    have hb'Z : b' ∉ Z := fun h => hcl a' b' ha'Z h hab'
    rw [centralizer_eq_of_mem hZ3 ha'Z (hne1 a' b' hb'E hab'), hO2Z, Subgroup.card_bot,
      mul_one] at hYle
    have h1 := hYle.trans (Nat.mul_le_mul hYZ8 (card_pCore_two_le (h4 E hEΔ b' hb'E hb'Z).2.1))
    rw [hY64] at h1
    norm_num at h1
  have hb'Z : b' ∉ Z := by
    intro hb'Z
    have hab'' : Subgroup.closure {b', a'} = E := by rw [Set.pair_comm]; exact hab'
    rw [centralizer_eq_of_mem hZ3 hb'Z (hne1 b' a' ha'E hab''), hO2Z, Subgroup.card_bot,
      mul_one] at hYle
    have h1 := hYle.trans (Nat.mul_le_mul hYZ8 (card_pCore_two_le (h4 E hEΔ a' ha'E ha'Z).2.1))
    rw [hY64] at h1
    norm_num at h1
  have hθ : ∀ u ∈ E, u ∉ Z → inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({u} : Set X)) =
        inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({u} : Set X)) := by
    intro u hu huZ
    rw [inSubgroup, inSubgroup,
      theta_eq_pCore_two (card_centralizer_dvd (h4 E hEΔ u hu huZ).2.1)]
  obtain ⟨d, hdZ, hd1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left fun h => by
    rw [h, Subgroup.card_bot] at hZ3
    norm_num at hZ3
  have hzp : ∀ u : X, u ∉ Z → Subgroup.zpowers u ≠ Subgroup.zpowers d := by
    intro u huZ h
    apply huZ
    have hu : u ∈ Subgroup.zpowers d := h ▸ Subgroup.mem_zpowers u
    exact Subgroup.zpowers_le.mpr hdZ hu
  refine ⟨⟨T, ⟨eY⟩⟩, a', ha'E, b', hb'E, d, hZE hdZ, hab', hd1,
    ⟨P, hdZ.1, fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdZ.2 p hp)⟩, hzp a' ha'Z, hzp b' hb'Z, ?_⟩
  rw [hθ a' ha'E ha'Z, hθ b' hb'E hb'Z, centralizer_eq_of_mem hZ3 hdZ hd1]
  set O1 := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a'} : Set X)) with hO1
  set O2 := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b'} : Set X)) with hO2
  set W := Y ⊓ Subgroup.centralizer (Z : Set X) with hW
  have hmem : ∀ y : X, y ∈ Y ↔ y ∈ ((W : Set X) * (O1 : Set X) * (O2 : Set X)) := by
    intro y
    rw [hpieces]
    rfl
  apply le_antisymm
  · intro y hy
    obtain ⟨_, ⟨w, hw, o, ho, rfl⟩, o', ho', rfl⟩ := (hmem y).mp hy
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hw)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ho)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ho'))
  · refine sup_le (sup_le (fun o ho => (hmem o).mpr ?_) (fun o ho => (hmem o).mpr ?_))
      inf_le_left
    · exact ⟨o, ⟨1, one_mem W, o, ho, one_mul o⟩, 1, one_mem O2, mul_one o⟩
    · exact ⟨1, ⟨1, one_mem W, 1, one_mem O1, mul_one 1⟩, o, ho, one_mul o⟩

end List

theorem step142TypesHJ_of_rigid
    (h131 : Item131) (hrig : KS142J2Rigid) : Step142TypesHJ :=
  step142TypesHJ_of h131 hrig
    (ks142J2List_of Sec4.Sporadic.rank3II_4_15 (ks142J2Sig_of Sec4.Sporadic.rank3II_4_15))

end Res5TypesHJ

end CFSG.RankThree.PartTwo.Sec14
