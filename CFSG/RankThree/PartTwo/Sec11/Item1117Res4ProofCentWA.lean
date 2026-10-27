module

public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSylow
import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofSpor
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofCenter
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofCube
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.Sporadic.He.Simple
import CFSG.LieType.HighestRoot.CentG2
public import CFSG.RankThree.PartTwo.Sec11.RFacts

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

namespace Item1117Res4Proof

theorem isPerfect_center_of_mulEquiv {W : Type} [Group W] (hP : Group.IsPerfect W)
    (hZ : Subgroup.center W = ⊥) {X : Type} [Group X] (e : X ≃* W) :
    Group.IsPerfect X ∧ Subgroup.center X = ⊥ :=
  ⟨CFSG.LieType.HighestRoot.isPerfect_of_mulEquiv e hP,
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e hZ⟩

section Groups

theorem center_eq_bot_of_lie_trialityD4 {X : Type} [Group X] (hX : Group.IsPerfect X)
    {q : TauCeti.PrimePower} {hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) : Subgroup.center X = ⊥ := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (3 * q.exponent)) =
      q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [GaloisField.card q.p _ (by have := q.exponent_pos; omega), TauCeti.PrimePower.card_def]
    change q.p ^ (3 * q.exponent) = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hq
    (GaloisField q.p (3 * q.exponent)) hK
    (iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent)
    (fun x => by rw [TauCeti.PrimePower.card_def]; rfl)
  have e' := e.trans b.symm
  have hP := Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
    (Item1119StepsProof.center_quotient_center_eq_bot_of_isPerfect hP)

theorem isPerfect_center_of_isList119 {X : Type} [Group X] (hX : IsList119 X)
    (hP : ¬ ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
      Sec4.ModThree π (p ^ f) ∧ Nonempty (X ≃* projImage (Sec4.glPi π 3 (p ^ f) K)))
    (hns : ¬ Group.IsSolvable (_root_.commutator X)) :
    Group.IsPerfect X ∧ Subgroup.center X = ⊥ := by
  rcases hX with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩ | ⟨p, f, hp, hf, ⟨hpf, ⟨e⟩⟩ | ⟨hpf, ⟨e⟩⟩⟩ |
      hPGL | hM24 | hHe
  · have := SetUp1118Proof.isPerfect_lie_G2 q hq
    have hXp : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact ⟨hXp, Item1119StepsProof.center_eq_bot_of_isoGTwo hXp ⟨hq, ⟨e⟩⟩⟩
  · have := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    have hXp : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact ⟨hXp, center_eq_bot_of_lie_trialityD4 hXp e⟩
  · obtain ⟨hP1, hZ1⟩ := Sec13.isPerfect_center_projSL p f hf hpf
    have := hP1
    exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
      KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e hZ1⟩
  · by_cases h2 : p ^ f = 2
    · exfalso
      obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
      have hsolU := Sec13.isSolvable_projSU_two
      have hsol : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact hns (Group.isSolvable_of_isSolvable_injective
        (f := (_root_.commutator X).subtype) (_root_.commutator X).subtype_injective)
    · have hq2 : 2 < p ^ f := by
        have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.out.one_lt
        omega
      obtain ⟨hP1, hZ1⟩ := Sec13.isPerfect_center_projSU p f hf hpf hq2
      have := hP1
      exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
        KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e hZ1⟩
  · exact (hP hPGL).elim
  · obtain ⟨e⟩ := hM24
    obtain ⟨x, y, -, -, -, hz, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact isPerfect_center_of_mulEquiv (KS11Lie2Proof.isPerfect_of_isSimpleGroup hz)
      (KS11Lie2Proof.center_eq_bot_of_isSimpleGroup hz) e
  · obtain ⟨e⟩ := hHe
    obtain ⟨x, y, -, -, -, hz, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.He := CFSG.Sporadic.He.isSimpleGroup_He
    exact isPerfect_center_of_mulEquiv (KS11Lie2Proof.isPerfect_of_isSimpleGroup hz)
      (KS11Lie2Proof.center_eq_bot_of_isSimpleGroup hz) e

end Groups

theorem commute_of_mem_of_prod_equiv {Q : Type*} [Group Q] {M N : Subgroup Q} {X : Type}
    [Group X] (φ : M ≃* Multiplicative (ZMod 3) × X) (hX : Group.IsPerfect X)
    (hZ : Subgroup.center X = ⊥) (hMN : ⁅M, M⁆ ≤ N) {w z : Q}
    (hwN : ∀ n ∈ N, w * n = n * w) (hzM : z ∈ M) (hzc : ∀ m ∈ M, z * m = m * z) (hz1 : z ≠ 1)
    (hwz : w * z = z * w) {m : Q} (hm : m ∈ M) : w * m = m * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set zM : M := ⟨z, hzM⟩ with hzMdef
  set mM : M := ⟨m, hm⟩ with hmMdef
  have hzcen : φ zM ∈ Subgroup.center (Multiplicative (ZMod 3) × X) := by
    rw [Subgroup.mem_center_iff]
    intro p
    obtain ⟨n, rfl⟩ := φ.surjective p
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc n n.2).symm
  have hz2 : (φ zM).2 = 1 := by
    have hmem : (φ zM).2 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact congrArg Prod.snd (Subgroup.mem_center_iff.mp hzcen ((1 : Multiplicative (ZMod 3)), y))
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hz1' : (φ zM).1 ≠ 1 := by
    intro h1
    apply hz1
    have h2 : φ zM = 1 := Prod.ext h1 hz2
    have h3 : zM = 1 := φ.injective (h2.trans (map_one φ).symm)
    exact congrArg Subtype.val h3
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (φ zM).1 ^ k = (φ mM).1 := by
    have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
    have htop := zpowers_eq_top_of_prime_card hcard hz1'
    exact Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top _)
  set m₁ : M := φ.symm ((1 : Multiplicative (ZMod 3)), (φ mM).2) with hm₁def
  have hm₁N : (m₁ : Q) ∈ N := by
    apply hMN
    have h1 := KS11Lie3Proof.one_prod_mem_commutator hX (φ mM).2
    have hec : (_root_.commutator (Multiplicative (ZMod 3) × X)).map φ.symm.toMonoidHom =
        _root_.commutator M := by
      rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ φ.symm.surjective,
        commutator_def]
    have h2 : m₁ ∈ _root_.commutator M := by
      rw [← hec]
      exact ⟨_, h1, rfl⟩
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨m₁, h2, rfl⟩
  have hdec : mM = zM ^ k * m₁ := by
    apply φ.injective
    have h1 : (φ (zM ^ k)).1 = (φ zM).1 ^ k := by
      have h := map_zpow ((MonoidHom.fst (Multiplicative (ZMod 3)) X).comp φ.toMonoidHom) zM k
      simp only [MonoidHom.coe_comp, MonoidHom.coe_fst, Function.comp_apply,
        MulEquiv.coe_toMonoidHom] at h
      exact h
    have h2 : (φ (zM ^ k)).2 = 1 := by
      have h := map_zpow ((MonoidHom.snd (Multiplicative (ZMod 3)) X).comp φ.toMonoidHom) zM k
      simp only [MonoidHom.coe_comp, MonoidHom.coe_snd, Function.comp_apply,
        MulEquiv.coe_toMonoidHom] at h
      rw [h, hz2, one_zpow]
    rw [map_mul, hm₁def, MulEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, h1, hk, mul_one]
    · rw [Prod.snd_mul, h2, one_mul]
  have hm' : m = z ^ k * (m₁ : Q) := by
    have h1 := congrArg Subtype.val hdec
    simpa [hzMdef, hmMdef] using h1
  rw [hm']
  have h1 : w * z ^ k = z ^ k * w := (Commute.zpow_right hwz k).eq
  have h2 : w * (m₁ : Q) = (m₁ : Q) * w := hwN _ hm₁N
  calc w * (z ^ k * (m₁ : Q)) = z ^ k * (w * (m₁ : Q)) := by rw [← mul_assoc, h1, mul_assoc]
    _ = z ^ k * (m₁ : Q) * w := by rw [h2, mul_assoc]

section Config

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_sec11YA (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hA : A ∈ partTwoF G) {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    {Y' : Subgroup G} (hY' : Y' ∈ thetaComponentsAt 3 e) {X : Type} [Group X]
    (φ : sec11YA e Y' A ≃* Multiplicative (ZMod 3) × X) (hX : Group.IsPerfect X)
    (hZ : Subgroup.center X = ⊥) {v : G} (hve : v ∈ Subgroup.centralizer ({e} : Set G))
    (hvY : v ∈ Sec4.thetaQuotCentralizer Y') (hvA : v ∈ Subgroup.normalizer (A : Set G)) :
    v ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({e} : Set G) with hC
  set π : C →* C ⧸ aschbacherSolvableCore 3 C := QuotientGroup.mk' _ with hπ
  have hAe := hA.1
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have hAC : A ≤ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hYC : Y' ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hY'
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe heA he1 Y' hY'
  set Y₁ := Y'.subgroupOf C with hY₁
  set A₁ := A.subgroupOf C with hA₁
  have hM : sec11YA e Y' A = (Y₁ ⊔ A₁).map π := by
    rw [sec11YA, Subgroup.subgroupOf_sup hYC hAC]
  have hA₁Y₁ : A₁ ≤ Subgroup.normalizer (Y₁ : Set C) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp hu)) (z : G)
  have hA₁c : ∀ u ∈ A₁, ∀ w ∈ A₁, u * w = w * u := fun u hu w hw =>
    Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hw))
  have hcommle : ⁅sec11YA e Y' A, sec11YA e Y' A⁆ ≤ Y₁.map π := by
    rw [hM, ← Subgroup.map_commutator]
    exact Subgroup.map_mono (Item1116Proof.commutator_sup_le_of_comm hA₁Y₁ hA₁c)
  set w : C ⧸ aschbacherSolvableCore 3 C := π ⟨v, hve⟩ with hw
  have hθ := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY'
  have hconj : ∀ y : C, (y : G) ∈ Y' → π ⟨v, hve⟩ * π y = π y * π ⟨v, hve⟩ := by
    intro y hy
    have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hvY).2 y hy
    rw [hθ] at h1
    obtain ⟨t, ht, hteq⟩ := h1.2
    have ht' : t = y⁻¹ * (⟨v, hve⟩ * y * (⟨v, hve⟩ : C)⁻¹) := Subtype.ext hteq
    have hπt : π t = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ht
    rw [ht', map_mul, map_inv, map_mul, map_mul, map_inv] at hπt
    calc π ⟨v, hve⟩ * π y = π y * (π y)⁻¹ * (π ⟨v, hve⟩ * π y * (π ⟨v, hve⟩)⁻¹) *
          π ⟨v, hve⟩ := by group
      _ = π y * π ⟨v, hve⟩ := by rw [mul_assoc (π y), hπt, mul_one]
  have hwN : ∀ n ∈ Y₁.map π, w * n = n * w := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y (Subgroup.mem_subgroupOf.mp hy)
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set z : C ⧸ aschbacherSolvableCore 3 C := π ⟨e, heC⟩ with hz
  have hzcen : ∀ q : C ⧸ aschbacherSolvableCore 3 C, z * q = q * z := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 C) q
    rw [hz, hπ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  have hzM : z ∈ sec11YA e Y' A := by
    rw [hM]
    exact ⟨⟨e, heC⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr heA), rfl⟩
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hz, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact he1 (eq_one_of_mem_R_of_mem_theta hA3 heA ⟨⟨e, heC⟩, h1, rfl⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbC : b ∈ C := hAC hb
  have hbM : π ⟨b, hbC⟩ ∈ sec11YA e Y' A := by
    rw [hM]
    exact ⟨⟨b, hbC⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hcomm := commute_of_mem_of_prod_equiv φ hX hZ hcommle hwN hzM
    (fun m _ => hzcen m) hz1 (hzcen w).symm hbM
  have hvb : v * b * v⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hvA b).mp hb
  have hcA : v * b * v⁻¹ * b⁻¹ ∈ A := A.mul_mem hvb (A.inv_mem hb)
  have hcC : v * b * v⁻¹ * b⁻¹ ∈ C :=
    C.mul_mem (C.mul_mem (C.mul_mem hve hbC) (C.inv_mem hve)) (C.inv_mem hbC)
  have hcθ : (⟨v * b * v⁻¹ * b⁻¹, hcC⟩ : C) ∈ aschbacherSolvableCore 3 C := by
    rw [← QuotientGroup.eq_one_iff]
    have e1 : (⟨v * b * v⁻¹ * b⁻¹, hcC⟩ : C) =
        ⟨v, hve⟩ * ⟨b, hbC⟩ * (⟨v, hve⟩ : C)⁻¹ * (⟨b, hbC⟩ : C)⁻¹ := rfl
    rw [e1]
    change π _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc π ⟨v, hve⟩ * π ⟨b, hbC⟩ * (π ⟨v, hve⟩)⁻¹ * (π ⟨b, hbC⟩)⁻¹ =
        π ⟨b, hbC⟩ * π ⟨v, hve⟩ * (π ⟨v, hve⟩)⁻¹ * (π ⟨b, hbC⟩)⁻¹ := by rw [← hw, hcomm]
      _ = 1 := by group
  have h1 := eq_one_of_mem_R_of_mem_theta hA3 hcA ⟨_, hcθ, rfl⟩
  calc b * v = (v * b * v⁻¹ * b⁻¹)⁻¹ * (v * b) := by group
    _ = v * b := by rw [h1, inv_one, one_mul]

end Config

end Item1117Res4Proof

section Main

open Item1117Res4Proof in
theorem sylow11LocalCentWA_of (h45 : Sec4.Item4_5) : Sylow11LocalCentWA := by
  intro G _ _ A c L a R Y d x s r g e Y' h heA hecd hY' _ _ _ X _ hX hXe hPGL Q hQ _ v hv
  obtain ⟨φ⟩ := hXe
  have he1 : e ≠ 1 := fun he => hecd (he ▸ Subgroup.one_mem _)
  have hAe := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy e heA)
  have hAY : A ≤ Subgroup.normalizer (Y' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Y' hY'
  have hns : ¬ Group.IsSolvable (_root_.commutator X) := by
    intro hsol
    obtain ⟨ψ⟩ := Item1116Proof.nonempty_thetaQuot_equiv_commutator hY' hAC hAY hAc φ
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY'
    have : Group.IsSolvable (Y' ⧸ aschbacherSolvableCore 3 Y') :=
      Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
    have : Group.IsPerfect (Y' ⧸ aschbacherSolvableCore 3 Y') := hq.1
    have : Nontrivial (Y' ⧸ aschbacherSolvableCore 3 Y') := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      obtain ⟨u, w, huw⟩ := hq.2.2
      exact huw (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable _ ‹_›
  have hP : ¬ ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
      Sec4.ModThree π (p ^ f) ∧ Nonempty (X ≃* projImage (Sec4.glPi π 3 (p ^ f) K)) := by
    rintro ⟨π, p, f, K, hK, hPF, hmod, ⟨ψ⟩⟩
    exact hPGL ⟨π, p, f, K, hK, hPF, hmod, ⟨φ.trans (MulEquiv.prodCongr (MulEquiv.refl _) ψ)⟩⟩
  obtain ⟨hXp, hXZ⟩ := isPerfect_center_of_isList119 hX hP hns
  exact mem_centralizer_of_sec11YA h45 h.toTheoremFourHyp h.mem_partTwoF heA he1 hY' φ hXp hXZ
    (hQ.le hv.1.1) hv.1.2 hv.2

end Main

end CFSG.RankThree.PartTwo.Sec11
