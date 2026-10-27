module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
import CFSG.RankThree.PartTwo.Sec19.Step197Proof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Census.Exceptional.TrialityD4
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Seitz199 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup (MulAut X)),
    (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 →
    ((CFSG.IsQuasisimple X ∧ Sec4.IsSLThreePi X ∧
        ¬ (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
          D ≤ (MulAut.conj : X →* MulAut X).range)) ∨
      ∃ p f : ℕ, p ≠ 3 ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p f) →
    Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x = x} = ⊤

namespace Step199Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mem_coset {B N : Subgroup G} (hB3 : IsPGroup 3 B) (hN3 : ¬ 3 ∣ Nat.card N)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) {k : G}
    (hk : ∀ b ∈ B, k⁻¹ * (b * k * b⁻¹) ∈ N) :
    ∃ y : G, k⁻¹ * y ∈ N ∧ ∀ b ∈ B, b * y = y * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set α : B →* MulAut G := MulAut.conj.comp B.subtype
  obtain ⟨y, hy, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB3 α N
    hN3 k).2 (by
      intro a x hx
      change k⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ N
      have h1 := hk a a.2
      have h2 : (a : G) * (k⁻¹ * x) * (a : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hBN a.2) _).mp hx
      have h3 := N.mul_mem h1 h2
      rwa [show k⁻¹ * ((a : G) * k * (a : G)⁻¹) * ((a : G) * (k⁻¹ * x) * (a : G)⁻¹) =
        k⁻¹ * ((a : G) * x * (a : G)⁻¹) by group] at h3)
  refine ⟨y, hy, fun b hb => ?_⟩
  have h1 : b * y * b⁻¹ = y := hyfix ⟨b, hb⟩
  calc b * y = (b * y * b⁻¹) * b := by group
    _ = y * b := by rw [h1]

theorem le_inf_centralizer_sup {K N B : Subgroup G} (hNK : N ≤ K) (hB3 : IsPGroup 3 B)
    (hN3 : ¬ 3 ∣ Nat.card N) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hBK : ∀ b ∈ B, ∀ k ∈ K, k⁻¹ * (b * k * b⁻¹) ∈ N) :
    K ≤ (K ⊓ Subgroup.centralizer (B : Set G)) ⊔ N := by
  intro k hk
  obtain ⟨y, hy, hyB⟩ := exists_fixed_mem_coset hB3 hN3 hBN (fun b hb => hBK b hb k hk)
  have hyK : y ∈ K := by
    have := K.mul_mem hk (hNK hy)
    simpa using this
  have hyC : y ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hyB b hb
  rw [show k = y * (y⁻¹ * k) by group]
  refine Subgroup.mul_mem_sup ⟨hyK, hyC⟩ ?_
  have := inv_mem hy
  simpa using this

theorem le_closure_sup_of_closure_eq_top {K : Subgroup G} {Nq : Subgroup K} [Nq.Normal]
    (hN3 : ¬ 3 ∣ Nat.card Nq) {D : Subgroup G} (hD3 : IsPGroup 3 D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDN : D ≤ Subgroup.normalizer ((Nq.map K.subtype : Subgroup G) : Set G))
    (ρ : D →* MulAut (K ⧸ Nq))
    (hρ : ∀ (d : D) (k k' : K), (k' : G) = d * k * (d : G)⁻¹ →
      ρ d (k : K ⧸ Nq) = (k' : K ⧸ Nq))
    (htop : Subgroup.closure {x : K ⧸ Nq | ∃ d : D, d ≠ 1 ∧ ρ d x = x} = ⊤) :
    K ≤ Subgroup.closure {y : G | y ∈ K ∧ ∃ d ∈ D, d ≠ 1 ∧ d * y = y * d} ⊔
      Nq.map K.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Nq.map K.subtype with hN
  set S : Set G := {y : G | y ∈ K ∧ ∃ d ∈ D, d ≠ 1 ∧ d * y = y * d} with hS
  set H : Subgroup G := Subgroup.closure S ⊔ N with hH
  have hNcard : ¬ 3 ∣ Nat.card N := by
    rwa [hN, Subgroup.card_map_of_injective K.subtype_injective]
  set Hq : Subgroup (K ⧸ Nq) := (H.subgroupOf K).map (QuotientGroup.mk' Nq) with hHq
  have hfix : {x : K ⧸ Nq | ∃ d : D, d ≠ 1 ∧ ρ d x = x} ⊆ Hq := by
    rintro x ⟨d, hd1, hdx⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hstab : ρ d ∈ MulAction.stabilizer (MulAut (K ⧸ Nq)) (k : K ⧸ Nq) := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hdx
    have hcoset : ∀ b ∈ Subgroup.zpowers (d : G), (k : G)⁻¹ * (b * k * b⁻¹) ∈ N := by
      rintro _ ⟨n, rfl⟩
      have hfixn : ρ (d ^ n) (k : K ⧸ Nq) = (k : K ⧸ Nq) := by
        have h := (MulAction.stabilizer (MulAut (K ⧸ Nq)) (k : K ⧸ Nq)).zpow_mem hstab n
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
        rwa [map_zpow]
      have hmem : (d : G) ^ n * k * ((d : G) ^ n)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hDK (D.zpow_mem d.2 n)) _).mp k.2
      have h1 := hρ (d ^ n) k ⟨_, hmem⟩ (by simp)
      rw [hfixn] at h1
      have h2 : k⁻¹ * ⟨_, hmem⟩ ∈ Nq := QuotientGroup.eq.mp h1
      exact ⟨_, h2, by simp⟩
    have hz3 : IsPGroup 3 (Subgroup.zpowers (d : G)) :=
      hD3.to_le ((Subgroup.zpowers_le).mpr d.2)
    obtain ⟨y, hy, hyd⟩ := exists_fixed_mem_coset hz3 hNcard
      ((Subgroup.zpowers_le).mpr (hDN d.2)) hcoset
    have hyK : y ∈ K := by
      have hyN : (k : G)⁻¹ * y ∈ K := Subgroup.map_subtype_le _ hy
      have := K.mul_mem k.2 hyN
      simpa using this
    have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hyS : y ∈ S := ⟨hyK, d, d.2, hd1', hyd d (Subgroup.mem_zpowers _)⟩
    refine ⟨⟨y, hyK⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.subset_closure hyS)), ?_⟩
    change ((⟨y, hyK⟩ : K) : K ⧸ Nq) = (k : K ⧸ Nq)
    apply QuotientGroup.eq.mpr
    obtain ⟨n, hn, hny⟩ := hy
    have hn' : n = k⁻¹ * ⟨y, hyK⟩ := Subtype.ext (by simpa using hny)
    have := Nq.inv_mem hn
    rwa [hn', show (k⁻¹ * ⟨y, hyK⟩ : K)⁻¹ = (⟨y, hyK⟩ : K)⁻¹ * k by group] at this
  have hHtop : Hq = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    exact hfix
  intro k hk
  have hmk : ((⟨k, hk⟩ : K) : K ⧸ Nq) ∈ Hq := hHtop ▸ Subgroup.mem_top _
  obtain ⟨h, hhH, hhk⟩ := hmk
  have h1 : h⁻¹ * ⟨k, hk⟩ ∈ Nq := QuotientGroup.eq.mp hhk
  have hk' : k = (h : G) * ((h⁻¹ * ⟨k, hk⟩ : K) : G) := by simp
  rw [hk']
  exact H.mul_mem (Subgroup.mem_subgroupOf.mp hhH) (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)

omit [Finite G] in
theorem mem_map_conj_iff {X : Subgroup G} {y z : G} :
    z ∈ X.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨y⁻¹ * z * y, h, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
theorem map_conj_map_conj (X : Subgroup G) (x y : G) :
    (X.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      X.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem map_conj_one (X : Subgroup G) : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext g
  simp

variable {A L E M : Subgroup G} {c : G}

theorem A_le_of_ctx195 (hctx : Ctx195 G A c L E M) : A ≤ M :=
  hctx.le_normalizer.trans
    ((normalizer_le_gamma le_rfl (by rw [hctx.isE27.pRank_eq]; norm_num)).trans
      hctx.mem_scriptM.2)

theorem ne_bot_of_ctx195 (hctx : Ctx195 G A c L E M) : L ≠ ⊥ := by
  have hL := hctx.mem_lA.1
  intro h
  have hq := Sec12.isQuasisimple_thetaQuot_of_mem hL
  have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨u, v, huv⟩ := exists_pair_ne (L ⧸ aschbacherSolvableCore 3 L)
  apply huv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  have hu : u = 1 := Subtype.ext (by
    change (u : G) = 1
    rw [← Subgroup.mem_bot, ← h]
    exact u.2)
  have hv : v = 1 := Subtype.ext (by
    change (v : G) = 1
    rw [← Subgroup.mem_bot, ← h]
    exact v.2)
  rw [hu, hv]

theorem A_le_normalizer_of_mem (hctx : Ctx195 G A c L E M) {K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) : A ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM := A_le_of_ctx195 hctx
  have hL := hctx.mem_lA.1
  have hLA : A ≤ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1
  have hLne := ne_bot_of_ctx195 hctx
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (isPerfect_of_mem_thetaComponentsIn hL)
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hKa := Sec18.map_conj_mem_oTwoComponentsIn hK (hAM ha)
  have hLKa : L ≤ K.map (MulAut.conj a).toMonoidHom := by
    intro l hl
    refine ⟨a⁻¹ * l * a, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hLA (Subgroup.inv_mem _ ha)) l).mp hl
    exact hLK (by simpa using this)
  have hLQ : L ≤ CFSG.Open.pCoreOf 2 M := by
    rw [← hLperf, Subgroup.commutator_le]
    intro l hl l' hl'
    rw [commutatorElement_def]
    exact Step1910Proof.commutator_mem_pCoreOf hK hKa (Ne.symm hne) (hLK hl) (hLKa hl')
  have hL2 : IsPGroup 2 L := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hLQ
  have : Group.IsSolvable L := by
    have := hL2.isNilpotent
    infer_instance
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLne
  have : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hL
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem isSLThreePi_of_ctx195 (h197 : Step197) (hctx : Ctx195 G A c L E M) :
    Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) := by
  have hD := Step197Proof.sec13Data_of_ctx195 hctx
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData (h197 G A c L E M hctx)
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
  exact isSLThreePi_of_mulEquiv
    (((MulEquiv.subgroupCongr hL₀).trans (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA)).trans
      η.symm) (Sec4.isSLThreePi_of_equiv D.piField D.modThree D.e)

theorem mem_normalizer_of_pow_three_eq_one (hctx : Ctx195 G A c L E M)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K) {a : G} (haM : a ∈ M)
    (ha3 : a ^ 3 = 1) : a ∈ Subgroup.normalizer (K : Set G) := by
  by_contra haK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hE := hctx.isE27
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have hLM : L ≤ M := hLK.trans hKM
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEL9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G) :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun e he => hEe e he.1) hctx.inf_noncyclic
  obtain ⟨y, hyEL, hyC⟩ : ∃ y ∈ E ⊓ L, y ∉ Sec4.thetaQuotCentralizer L := by
    by_contra hall
    push Not at hall
    have h := Step1910O2Proof.card_le_card_center_thetaQuot (hE.isPGroup.to_le inf_le_left)
      inf_le_right (fun x hx => hall x hx)
    rw [hZ3] at h
    omega
  have hyL : y ∈ L := hyEL.2
  obtain ⟨l, hl, hyl⟩ : ∃ l ∈ L,
      l⁻¹ * (y * l * y⁻¹) ∉ inSubgroup (aschbacherSolvableCore 3) L := by
    by_contra hall
    push Not at hall
    exact hyC (Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer hyL, hall⟩)
  have hcomm : y * l * y⁻¹ * l⁻¹ ∉ Q := by
    intro h
    apply hyl
    have hmemL : y * l * y⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hyL hl) (L.inv_mem hyL)) (L.inv_mem hl)
    have hθ : y * l * y⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L :=
      Step1910Proof.inf_pCoreOf_le_theta hLM ⟨hmemL, h⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L (L.inv_mem hl)) _).mp hθ
    have e : l⁻¹ * (y * l * y⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (y * l * y⁻¹) := by group
    rwa [e] at h2
  set J := K.map (MulAut.conj a).toMonoidHom with hJ
  set J₂ := K.map (MulAut.conj (a * a)).toMonoidHom with hJ₂
  have hJM : J ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hK haM
  have hJ₂M : J₂ ∈ oTwoComponentsIn M :=
    Sec18.map_conj_mem_oTwoComponentsIn hK (M.mul_mem haM haM)
  have hJK : J ≠ K := fun h => haK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hJ₂K : J₂ ≠ K := by
    intro h
    have h2 : a * a ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    apply haK
    have e : a = (a * a) * (a * a) := by
      calc a = a ^ 3 * a := by rw [ha3, one_mul]
        _ = (a * a) * (a * a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ h2 h2
  have hJJ₂ : J ≠ J₂ := by
    intro h
    apply hJK
    have h1 := congrArg (Subgroup.map (MulAut.conj a⁻¹).toMonoidHom) h
    rw [hJ, hJ₂, map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one,
      show a⁻¹ * (a * a) = a by group] at h1
    exact h1.symm
  have haQ : ∀ b ∈ M, b ∈ Subgroup.normalizer (Q : Set G) := fun b hb =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hb
  have hx3 : ∀ b ∈ M, (b * y * b⁻¹) ^ 3 ∈ Q := by
    intro b _
    rw [conj_pow, hEe y hyEL.1, mul_one, mul_inv_cancel]
    exact Q.one_mem
  have hxnc : ∀ b ∈ M, ∃ j ∈ K.map (MulAut.conj b).toMonoidHom,
      (b * y * b⁻¹) * j * (b * y * b⁻¹)⁻¹ * j⁻¹ ∉ Q := by
    intro b hb
    refine ⟨b * l * b⁻¹, ⟨l, hLK hl, rfl⟩, fun h => hcomm ?_⟩
    have e : (b * y * b⁻¹) * (b * l * b⁻¹) * (b * y * b⁻¹)⁻¹ * (b * l * b⁻¹)⁻¹ =
        b * (y * l * y⁻¹ * l⁻¹) * b⁻¹ := by group
    rw [e] at h
    exact (Subgroup.mem_normalizer_iff.mp (haQ b hb) _).mpr h
  have h4 := Step1910Proof.four_le_localRank hQ hK hJM hJ₂M hJK hJ₂K hJJ₂
    (inf_le_right.trans hLK) (fun e he => hEe e he.1)
    (fun e he f hf => congrArg Subtype.val (hE.1.1.is_comm.comm ⟨e, he.1⟩ ⟨f, hf.1⟩))
    hEL9 (x := a * y * a⁻¹) (x₂ := (a * a) * y * (a * a)⁻¹) ⟨y, hLK hyL, rfl⟩ ⟨y, hLK hyL, rfl⟩
    (hx3 a haM) (hx3 _ (M.mul_mem haM haM)) (hxnc a haM) (hxnc _ (M.mul_mem haM haM))
  rw [hst.toTheoremFourHyp.localRank_three] at h4
  omega

theorem exists_thetaQuot_mulEquiv {K L : Subgroup G} (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) :
    ∃ ι : (L ⧸ aschbacherSolvableCore 3 L) ≃* (K ⧸ aschbacherSolvableCore 3 K),
      ∀ l : L, ι (l : L ⧸ aschbacherSolvableCore 3 L) =
        ((Subgroup.inclusion hLK l : K) : K ⧸ aschbacherSolvableCore 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θK := aschbacherSolvableCore 3 K with hθK
  set θL := aschbacherSolvableCore 3 L with hθL
  obtain ⟨hθKs, -, hθK3, -, -, -, hθKp⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  obtain ⟨hθLs, -, hθL3, hθLmax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set φ : L →* K ⧸ θK := (QuotientGroup.mk' θK).comp (Subgroup.inclusion hLK) with hφ
  have hO : CFSG.pCore 2 K ≤ θK := hθKp 2 Nat.prime_two (by norm_num)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨l, hl⟩ := Step1911EndProof.phiL_surjective hLK hKL (k : K ⧸ CFSG.pCore 2 K)
    refine ⟨l, ?_⟩
    rw [Step1911EndProof.phiL_apply, QuotientGroup.eq] at hl
    exact QuotientGroup.eq.mpr (hO hl)
  have hφmem : ∀ x : L, x ∈ φ.ker ↔ (Subgroup.inclusion hLK x : K) ∈ θK := fun x => by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hker : φ.ker = θL := by
    apply le_antisymm
    · set ψ : φ.ker →* θK := ((Subgroup.inclusion hLK).comp φ.ker.subtype).codRestrict θK
        (fun x => (hφmem x).mp x.2) with hψ
      have hψinj : Function.Injective ψ := by
        intro x y hxy
        apply Subtype.ext
        apply Subgroup.inclusion_injective hLK
        exact congrArg Subtype.val hxy
      have : Group.IsSolvable θK := hθKs
      have hs : Group.IsSolvable φ.ker := Group.isSolvable_of_isSolvable_injective hψinj
      have h3 : ¬ 3 ∣ Nat.card φ.ker := fun h =>
        hθK3 (h.trans (Subgroup.card_dvd_of_injective ψ hψinj))
      exact hθLmax _ inferInstance hs h3
    · set I : Subgroup (K ⧸ θK) := θL.map φ with hI
      have hIn : I.Normal := (aschbacherSolvableCore_normal 3 L).map φ hsurj
      have : Group.IsSolvable θL := hθLs
      have hIs : Group.IsSolvable I := by
        set f : θL →* I := (φ.comp θL.subtype).codRestrict I (fun x => ⟨x, x.2, rfl⟩) with hf
        refine Group.isSolvable_of_surjective (f := f) ?_
        rintro ⟨_, ⟨t, ht, rfl⟩⟩
        exact ⟨⟨t, ht⟩, rfl⟩
      have hI3 : ¬ 3 ∣ Nat.card I := fun h => hθL3 (h.trans (Subgroup.card_map_dvd θL φ))
      have hθX : aschbacherSolvableCore 3 (K ⧸ θK) = ⊥ :=
        (solvable_prime_complement_core_quotient_centralizers (G := K) Nat.prime_three θK hθKs
          hθK3).2.2.1
      have hIle : I ≤ aschbacherSolvableCore 3 (K ⧸ θK) :=
        (solvable_prime_complement_core_characterization (H := K ⧸ θK) Nat.prime_three).2.2.2.1
          I hIn hIs hI3
      rw [hθX] at hIle
      intro t ht
      have h1 : φ t ∈ (⊥ : Subgroup (K ⧸ θK)) := hIle ⟨t, ht, rfl⟩
      rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker] at h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj), fun l => rfl⟩

noncomputable def thetaAct (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
  (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom

omit [Finite G] in
noncomputable def pCoreAct (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ CFSG.pCore 2 K) :=
  (Step1910Proof.pCoreQuotMulAut K).comp K.normalizerMonoidHom

theorem thetaAct_mk {K : Subgroup G} (x : Subgroup.normalizer (K : Set G)) (k k' : K)
    (h : (k' : G) = x * k * (x : G)⁻¹) :
    thetaAct K x (k : K ⧸ aschbacherSolvableCore 3 K) = (k' : K ⧸ aschbacherSolvableCore 3 K) := by
  have e : K.normalizerMonoidHom x k = k' := Subtype.ext h.symm
  rw [thetaAct, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk, e]

omit [Finite G] in
theorem pCoreAct_mk {K : Subgroup G} (x : Subgroup.normalizer (K : Set G)) (k k' : K)
    (h : (k' : G) = x * k * (x : G)⁻¹) :
    pCoreAct K x (k : K ⧸ CFSG.pCore 2 K) = (k' : K ⧸ CFSG.pCore 2 K) := by
  have e : K.normalizerMonoidHom x k = k' := Subtype.ext h.symm
  change ((K.normalizerMonoidHom x k : K) : K ⧸ CFSG.pCore 2 K) = _
  rw [e]

theorem le_of_centralizer_le {N D M' : Subgroup G} (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N)
    (hCM : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M') : N ≤ M' := by
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three D N hD (by rw [hD9]; norm_num) hDN hcop
  rw [← hgen]
  refine iSup₂_le fun F hF => ?_
  have hFD : F ≤ D := hF.1
  have hF1 : F ≠ ⊥ := by
    intro h
    have := hF.2
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨⟨d, hdF⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  exact inf_le_right.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdF)).trans
    (hCM d (hFD hdF) hd1'))

theorem le_of_closure_fixed_eq_top {K : Subgroup G} {Nq : Subgroup K} [Nq.Normal]
    (hN3 : ¬ 3 ∣ Nat.card Nq) {D : Subgroup G} (hD3 : IsPGroup 3 D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDN : D ≤ Subgroup.normalizer ((Nq.map K.subtype : Subgroup G) : Set G))
    (ρ : D →* MulAut (K ⧸ Nq))
    (hρ : ∀ (d : D) (k k' : K), (k' : G) = d * k * (d : G)⁻¹ →
      ρ d (k : K ⧸ Nq) = (k' : K ⧸ Nq))
    {M' : Subgroup G} (hNM : Nq.map K.subtype ≤ M')
    (hCM : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M')
    (hgen : Function.Injective ρ →
      Subgroup.closure {x : K ⧸ Nq | ∃ d : D, d ≠ 1 ∧ ρ d x = x} = ⊤) :
    K ≤ M' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hinj : Function.Injective ρ
  · refine (le_closure_sup_of_closure_eq_top hN3 hD3 hDK hDN ρ hρ (hgen hinj)).trans
      (sup_le ((Subgroup.closure_le _).mpr ?_) hNM)
    rintro y ⟨-, d, hd, hd1, hdy⟩
    exact hCM d hd hd1 (Subgroup.mem_centralizer_singleton_iff.mpr hdy.symm)
  · rw [injective_iff_map_eq_one] at hinj
    push Not at hinj
    obtain ⟨d, hdρ, hd1⟩ := hinj
    have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hB3 : IsPGroup 3 (Subgroup.zpowers (d : G)) :=
      hD3.to_le ((Subgroup.zpowers_le).mpr d.2)
    have hNcard : ¬ 3 ∣ Nat.card (Nq.map K.subtype) := by
      rwa [Subgroup.card_map_of_injective K.subtype_injective]
    refine (le_inf_centralizer_sup (Subgroup.map_subtype_le _) hB3 hNcard
      ((Subgroup.zpowers_le).mpr (hDN d.2)) ?_).trans (sup_le ?_ hNM)
    · rintro _ ⟨n, rfl⟩ k hk
      have hmem : (d : G) ^ n * k * ((d : G) ^ n)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hDK (D.zpow_mem d.2 n)) _).mp hk
      have h1 := hρ (d ^ n) ⟨k, hk⟩ ⟨_, hmem⟩ (by simp)
      rw [map_zpow, hdρ, one_zpow, MulAut.one_apply] at h1
      have h2 : (⟨k, hk⟩ : K)⁻¹ * ⟨_, hmem⟩ ∈ Nq := QuotientGroup.eq.mp h1
      exact ⟨_, h2, by simp⟩
    · exact inf_le_right.trans ((Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers _))).trans (hCM d d.2 hd1'))

theorem card_le_nine_of_SL34 {X : Type} [Group X] [Finite X]
    (ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) {W : Subgroup (MulAut X)}
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWe : ∀ a ∈ W, a ^ 3 = 1) :
    Nat.card W ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : Finite (MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 2))) :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.L34.card_mulAut hk]; norm_num)
  set φ : MulAut X →* MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 2)) :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.descendAut 3 (GaloisField 2 2)).comp
      (MulAut.congr ψ).toMonoidHom with hφ
  have hφinj : Function.Injective φ :=
    (Sec4.descendAut_three_injective).comp (MulAut.congr ψ).injective
  set W' := W.map φ with hW'
  have hW'card : Nat.card W' = Nat.card W := Subgroup.card_map_of_injective hφinj
  have hW3 : IsPGroup 3 W := fun w => ⟨1, Subtype.ext (by simpa using hWe w w.2)⟩
  obtain ⟨n, hn⟩ := hW3.exists_card_eq
  have hW'ea : CFSG.IsElementaryAbelian 3 W' :=
    { is_comm := ⟨fun a b => by
        obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
        apply Subtype.ext
        change φ x * φ y = φ y * φ x
        rw [← map_mul, ← map_mul, hWc x hx y hy]⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
        apply Subtype.ext
        change φ x ^ 3 = 1
        rw [← map_pow, hWe x hx, map_one] }
  have hle := CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (by norm_num) hW'ea
    (k := n) (by rw [hW'card, hn])
  rw [KFacts.L34.pRank_three_mulAut hk] at hle
  rw [hn]
  calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 9 := by norm_num

theorem thetaAct_of_mem {K : Subgroup G} {t : G} (ht : t ∈ K) :
    thetaAct K ⟨t, Subgroup.le_normalizer ht⟩ =
      MulAut.conj ((⟨t, ht⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := by
  ext x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [thetaAct_mk _ k ⟨t * k * t⁻¹, K.mul_mem (K.mul_mem ht k.2) (K.inv_mem ht)⟩ rfl,
    MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem thetaAct_eq_one {K L : Subgroup G} (hLK : L ≤ K)
    (ι : (L ⧸ aschbacherSolvableCore 3 L) ≃* (K ⧸ aschbacherSolvableCore 3 K))
    (hι : ∀ l : L, ι (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((Subgroup.inclusion hLK l : K) : K ⧸ aschbacherSolvableCore 3 K))
    {b : G} (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbC : b ∈ Sec4.thetaQuotCentralizer L) : thetaAct K ⟨b, hbK⟩ = 1 := by
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := (Sec6.mem_thetaQuotCentralizer_iff.mp hbC).1
  ext x
  rw [MulAut.one_apply]
  obtain ⟨q, rfl⟩ := ι.surjective x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : b * (m : G) * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hbL m).mp m.2
  rw [hι, thetaAct_mk ⟨b, hbK⟩ (Subgroup.inclusion hLK m) (Subgroup.inclusion hLK ⟨_, hmem⟩)
    rfl, ← hι, ← hι]
  congr 1
  apply QuotientGroup.eq.mpr
  obtain ⟨y, hy, hye⟩ := (Sec6.mem_thetaQuotCentralizer_iff.mp hbC).2 m m.2
  have e : m⁻¹ * ⟨_, hmem⟩ = y :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact hye.symm)
  have e' : (⟨_, hmem⟩ : L)⁻¹ * m = y⁻¹ := by
    rw [← e]
    group
  rw [e']
  exact inv_mem hy

theorem exists_mul_eq_of_mem (hctx : Ctx195 G A c L E M)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) {e : G}
    (he : e ∈ E) : ∃ t ∈ E ⊓ L, ∃ b ∈ E ⊓ Sec4.thetaQuotCentralizer L, e = t * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := hctx.isE27
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  set T := E ⊓ L with hT
  set B₀ := E ⊓ Sec4.thetaQuotCentralizer L with hB₀
  have hT9 : 9 ≤ Nat.card T :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hEe x hx.1) hctx.inf_noncyclic
  have hB9 : 9 ≤ Nat.card B₀ :=
    Step198DProof.nine_le_card_of_not_isCyclic (fun x hx => hEe x hx.1)
      hctx.centralizer_noncyclic
  have hTB : Nat.card (T ⊓ B₀ : Subgroup G) ≤ 3 := by
    have h := Step1910O2Proof.card_le_card_center_thetaQuot (S := T ⊓ B₀)
      (hE.isPGroup.to_le (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right)
    rwa [hZ3] at h
  have hTN : T ≤ Subgroup.normalizer (B₀ : Set G) := fun t ht =>
    Subgroup.mem_normalizer_fintype fun b hb => by
      rw [hEab t ht.1 b hb.1, mul_inv_cancel_right]
      exact hb
  have hsup : T ⊔ B₀ = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    have h1 := Sec6.card_sup_mul_card_inf hTN
    have h81 : 9 * 9 ≤ Nat.card T * Nat.card B₀ := Nat.mul_le_mul hT9 hB9
    rw [hE.2]
    nlinarith
  have he' : e ∈ ((T ⊔ B₀ : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hsup]
    exact he
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at he'
  obtain ⟨t, ht, b, hb, rfl⟩ := he'
  exact ⟨t, ht, b, hb, rfl⟩

theorem thetaAct_mem_range_of_mem (hctx : Ctx195 G A c L E M)
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) {K : Subgroup G}
    (hLK : L ≤ K) (ι : (L ⧸ aschbacherSolvableCore 3 L) ≃* (K ⧸ aschbacherSolvableCore 3 K))
    (hι : ∀ l : L, ι (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((Subgroup.inclusion hLK l : K) : K ⧸ aschbacherSolvableCore 3 K))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) {e : G} (he : e ∈ E) :
    thetaAct K ⟨e, hEK he⟩ ∈
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _).range := by
  obtain ⟨t, ht, b, hb, rfl⟩ := exists_mul_eq_of_mem hctx hZ3 he
  have htK : t ∈ K := hLK ht.2
  have hsplit : (⟨t * b, hEK he⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨t, Subgroup.le_normalizer htK⟩ * ⟨b, hEK hb.1⟩ := rfl
  rw [hsplit, map_mul, thetaAct_eq_one hLK ι hι (hEK hb.1) hb.2, mul_one]
  exact ⟨_, (thetaAct_of_mem htK).symm⟩

theorem exists_not_inner (h197 : Step197) (hctx : Ctx195 G A c L E M) {K : Subgroup G}
    (hLK : L ≤ K) (ι : (L ⧸ aschbacherSolvableCore 3 L) ≃* (K ⧸ aschbacherSolvableCore 3 K))
    (hι : ∀ l : L, ι (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((Subgroup.inclusion hLK l : K) : K ⧸ aschbacherSolvableCore 3 K))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (a : G) (ha : a ∈ A), thetaAct K ⟨a, hAK ha⟩ ∉
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _).range := by
  by_contra hall
  push Not at hall
  have hD := Step197Proof.sec13Data_of_ctx195 hctx
  obtain ⟨π, p, f, F, _, ⟨D⟩⟩ := exists_sLTwoData (h197 G A c L E M hctx)
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  have hLA : A ≤ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1
  have hAΛ : (aBarHom hD).range ≤ Λ ⊔ Subgroup.centralizer (Λ : Set (lBarA c L A)) := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨x, hx⟩ := hall a ha
    obtain ⟨lq, hlq⟩ := ι.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lq
    have key : ∀ m : L, Step1911EndProof.mkX hD ⟨a * m * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLA ha) m).mp m.2⟩ =
          Step1911EndProof.mkX hD (l * m * l⁻¹) := by
      intro m
      have hmem : a * (m : G) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hLA ha) m).mp m.2
      have h1 : ι ((⟨a * m * a⁻¹, hmem⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
          ι ((l * m * l⁻¹ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
        rw [hι, hι, ← thetaAct_mk ⟨a, hAK ha⟩ (Subgroup.inclusion hLK m) _ rfl, ← hx,
          MulAut.conj_apply, ← hlq, hι, map_mul, map_mul, map_inv, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h2 := QuotientGroup.eq.mp (ι.injective h1)
      have h3 := (Step1911EndProof.mkX_eq_one_iff hD _).mpr h2
      rw [map_mul, map_inv, inv_mul_eq_one] at h3
      exact h3
    set W := Step1911EndProof.mkX hD l with hW
    have hC : aBarHom hD ⟨a, ha⟩ * W⁻¹ ∈ Subgroup.centralizer (Λ : Set (lBarA c L A)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨m, rfl⟩ := Step1911EndProof.exists_mkX_eq hD hv
      have h1 := key (l⁻¹ * m * l)
      rw [Step1911EndProof.mkX_conj hD ha] at h1
      have e1 : l * (l⁻¹ * m * l) * l⁻¹ = m := by group
      rw [e1] at h1
      simp only [map_mul, map_inv] at h1
      rw [← hW] at h1
      calc Step1911EndProof.mkX hD m * (aBarHom hD ⟨a, ha⟩ * W⁻¹)
          = aBarHom hD ⟨a, ha⟩ * (W⁻¹ * Step1911EndProof.mkX hD m * W) *
              (aBarHom hD ⟨a, ha⟩)⁻¹ * (aBarHom hD ⟨a, ha⟩ * W⁻¹) := by rw [h1]
        _ = aBarHom hD ⟨a, ha⟩ * W⁻¹ * Step1911EndProof.mkX hD m := by group
    have hWΛ : W ∈ Λ := Step1911EndProof.mkX_mem hD l
    rw [show aBarHom hD ⟨a, ha⟩ = (aBarHom hD ⟨a, ha⟩ * W⁻¹) * W by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hC) (Subgroup.mem_sup_left hWΛ)
  have htop : (⊤ : Subgroup (lBarA c L A)) ≤ Λ ⊔ Subgroup.centralizer (Λ : Set _) := by
    rw [← lBar_sup_range_aBarHom hD]
    exact sup_le le_sup_left hAΛ
  apply D.a_not_mem_sup
  rw [hL₀]
  exact htop (Subgroup.mem_top _)

theorem eq_of_inner_SL34 (h197 : Step197) (hctx : Ctx195 G A c L E M)
    (hD9 : Nat.card (E ⊓ A : Subgroup G) = 9)
    {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (ψ : (K ⧸ aschbacherSolvableCore 3 K) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    {A' : Subgroup G} (hA'K : A' ≤ Subgroup.normalizer (K : Set G))
    (hA'c : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) (hA'e : ∀ a ∈ A', a ^ 3 = 1)
    {D' : Subgroup G} (hD'A' : D' ≤ A') (hD'9 : Nat.card D' = 9)
    (hinj : Function.Injective ((thetaAct K).comp (Subgroup.inclusion (hD'A'.trans hA'K))))
    (hinn : ((thetaAct K).comp (Subgroup.inclusion (hD'A'.trans hA'K))).range ≤
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _).range)
    {B : Subgroup G} (hBA : B ≤ A) (hBA' : B ≤ A') (hB9 : 9 ≤ Nat.card B) :
    B = E ⊓ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hZ3 := Sec12.card_center_eq_three_of_isSLThreePi (isSLThreePi_of_ctx195 h197 hctx)
  have hAK := A_le_normalizer_of_mem hctx hK hLK
  have hEK : E ≤ Subgroup.normalizer (K : Set G) :=
    (hctx.le_sup.trans inf_le_left).trans
      (sup_le (hLK.trans (Subgroup.le_normalizer)) hAK)
  obtain ⟨ι, hι⟩ := exists_thetaQuot_mulEquiv hLK hKL
  set ρA' := (thetaAct K).comp (Subgroup.inclusion hA'K) with hρA'
  set ρD' := (thetaAct K).comp (Subgroup.inclusion (hD'A'.trans hA'K)) with hρD'
  have hD'le : ρD'.range ≤ ρA'.range := by
    rintro _ ⟨d, rfl⟩
    exact ⟨⟨d, hD'A' d.2⟩, rfl⟩
  have hD'X9 : Nat.card ρD'.range = 9 := by
    rw [← hD'9]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hA'X : Nat.card ρA'.range ≤ 9 := by
    refine card_le_nine_of_SL34 ψ ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA'c a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA'e a a.2)
      rw [← map_pow, ha3, map_one]
  have hrange : ρA'.range = ρD'.range :=
    (Subgroup.eq_of_le_of_card_ge hD'le (by omega)).symm
  set Ainn : Subgroup G := ((MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _).range.comap
    ((thetaAct K).comp (Subgroup.inclusion hAK))).map A.subtype with hAinn
  have hmemAinn : ∀ a (ha : a ∈ A), thetaAct K ⟨a, hAK ha⟩ ∈
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _).range → a ∈ Ainn :=
    fun a ha h => ⟨⟨a, ha⟩, h, rfl⟩
  have hBinn : B ≤ Ainn := by
    intro b hb
    refine hmemAinn b (hBA hb) ?_
    have h1 : thetaAct K ⟨b, hAK (hBA hb)⟩ ∈ ρA'.range := ⟨⟨b, hBA' hb⟩, rfl⟩
    rw [hrange] at h1
    exact hinn h1
  have hDinn : E ⊓ A ≤ Ainn := fun d hd =>
    hmemAinn d hd.2 (thetaAct_mem_range_of_mem hctx hZ3 hLK ι hι hEK hd.1)
  have hAinnA : Ainn ≤ A := Subgroup.map_subtype_le _
  have hAinne : Ainn ≠ A := by
    intro h
    obtain ⟨a, ha, hna⟩ := exists_not_inner h197 hctx hLK ι hι hAK
    have haAinn : a ∈ Ainn := h ▸ ha
    obtain ⟨a', ha', ha'e⟩ := haAinn
    have : a' = ⟨a, ha⟩ := Subtype.ext ha'e
    subst this
    exact hna ha'
  have hcard : Nat.card Ainn ≤ 9 := by
    have hdvd : Nat.card Ainn ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le hAinnA
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hk]; norm_num
    · rw [hk]; norm_num
    · rw [hk]; norm_num
    · exact absurd (Subgroup.eq_of_le_of_card_ge hAinnA (by rw [hk, hA.2]; norm_num)) hAinne
  have hDeq : E ⊓ A = Ainn := Subgroup.eq_of_le_of_card_ge hDinn (by omega)
  exact Subgroup.eq_of_le_of_card_ge (hBinn.trans hDeq.ge) (by omega)

theorem localRank_quot_le_three (hctx : Ctx195 G A c L E M) {K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) :
    CFSG.Assembly.RankThreeEven.localRank 3 (K ⧸ CFSG.pCore 2 K) ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have hE : ∀ (E₀ : Subgroup (K ⧸ CFSG.pCore 2 K)) (k : ℕ),
      CFSG.Assembly.IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ k → k ≤ 3 := by
    intro E₀ k hEab hEk
    have hE3 : IsPGroup 3 E₀ := IsPGroup.of_card hEk
    set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
    have hker : Nat.Coprime 3 (Nat.card π.ker) := by
      rw [hπ, QuotientGroup.ker_mk']
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
      rw [hj]
      exact Nat.Coprime.pow_right _ (by norm_num)
    obtain ⟨R, -, ⟨eR⟩⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
      Nat.prime_three π (QuotientGroup.mk'_surjective _) hker E₀ hE3
    have hRcomm : ∀ a b : R, a * b = b * a := fun a b => eR.injective (by
      rw [map_mul, map_mul]
      exact Subtype.ext (congrArg Subtype.val (hEab.1.is_comm.comm (eR a) (eR b))))
    have hRe : ∀ a : R, a ^ 3 = 1 := fun a => eR.injective (by
      rw [map_pow, map_one]
      exact Subtype.ext (hEab.2 _ (eR a).2))
    set W := (R.map K.subtype) with hW
    have hWcard : Nat.card W = 3 ^ k := by
      rw [hW, Subgroup.card_map_of_injective K.subtype_injective, Nat.card_congr eR.toEquiv,
        hEk]
    have hWmem : ∀ w ∈ W, ∃ r : R, ((r : K) : G) = w := by
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
    have hWc : IsMulCommutative W := ⟨⟨fun a b => Subtype.ext (by
      obtain ⟨a', ha'⟩ := hWmem a a.2
      obtain ⟨b', hb'⟩ := hWmem b b.2
      change (a : G) * b = b * a
      rw [← ha', ← hb']
      exact congrArg (fun z : R => ((z : K) : G)) (hRcomm a' b'))⟩⟩
    have hWe : ∀ w ∈ W, w ^ 3 = 1 := by
      intro w hw
      obtain ⟨r, hr⟩ := hWmem w hw
      rw [← hr]
      exact congrArg (fun z : R => ((z : K) : G)) (hRe r)
    have hWN : W ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.map_subtype_le _).trans
        (hKM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    have h := Theta.le_localRank_of_le_normalizer (by norm_num) hQ
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hWc hWe hWcard hWN
    rwa [hst.toTheoremFourHyp.localRank_three] at h
  refine csSup_le' ?_
  rintro m ⟨H, -, rfl⟩
  refine csSup_le' ?_
  rintro k ⟨E₀, -, hEab, hEk⟩
  exact hE E₀ k hEab hEk

theorem false_of_trialityD4_three
    (hctx : Ctx195 G A c L E M) {K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) {f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 3 f) :
    False := by
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨F, _, _, hFcard, σ, hσ, ⟨e⟩⟩ := h.2
  have hF : Nat.card F = 3 ^ (3 * f) := by
    rw [hFcard, ← pow_mul, mul_comm]
    rfl
  set σ' : F ≃+* F := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩ with hσ'
  have hσ'c : ∀ c, σ' c = c ^ (3 ^ f) := hσ
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_three (by omega : 1 ≤ 3 * f) hF
  have hσfr : σ' = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ'c, CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ' = 3 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 3 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  have hσ'3 : σ' ^ 3 = 1 := by
    rw [← hσo]
    exact pow_orderOf_eq_one σ'
  have hk : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ') = 3 ^ f := by
    obtain ⟨-, hσcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_three
      (by omega : 1 ≤ 3 * f) hF σ'
    rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
    exact hσcard
  have : Finite (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup .D4 F σ'.toRingHom)) := Finite.of_equiv _ e.toEquiv
  have h4 := Census.Exceptional.four_le_localRank_derivedCentralQuotient_D4 σ' Nat.prime_three
    (by norm_num) hf hσ'3 hF hk
  have h4' : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (K ⧸ CFSG.pCore 2 K) :=
    h4.trans (Census.localRank_eq_of_mulEquiv e Nat.prime_three).ge
  have := localRank_quot_le_three hctx hK
  omega

end Step199Proof

open Step199Proof in
theorem step199_of
    (h197 : Step197) (h198 : Step198) (hS : Seitz199) : Step199 := by
  intro G _ _ A c L E M hctx hΓ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := hctx.isE27
  have hA := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAe : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set D := E ⊓ A with hDdef
  have hD9 : Nat.card D = 9 := step198D_of h197 G A c L E M hctx
  have hDA : D ≤ A := inf_le_right
  have hD3 : IsPGroup 3 D := hE.isPGroup.to_le inf_le_left
  have hND : ∀ X : Subgroup G, X ≤ D → X ≠ ⊥ → Subgroup.normalizer (X : Set G) ≤ M :=
    (gammaOne_le_iff hD3).mp hΓ
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD9
    norm_num at hD9
  have hSL := isSLThreePi_of_ctx195 h197 hctx
  have hZ3 := Sec12.card_center_eq_three_of_isSLThreePi hSL
  have hΓA : ¬ gamma 2 A ≤ M := fun hle => hctx.not_mem_partTwoT
    (mem_partTwoT_iff.mpr ⟨hctx.mem_partTwoE, M, hctx.mem_scriptM.1, hle⟩)
  rw [gamma_le_iff] at hΓA
  push Not at hΓA
  obtain ⟨B, hBA, hB2, hBM⟩ := hΓA
  have hB9 : 9 ≤ Nat.card B := by
    have hdvd : Nat.card B ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le hBA
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hlog := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three B
    rw [hk, Nat.log_pow (by norm_num)] at hlog
    have hk2 : 2 ≤ k := hB2.trans hlog
    rw [hk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  obtain ⟨g, hgB, hgM⟩ := Set.not_subset.mp hBM
  have hBD : B ⊓ D ≠ ⊥ := by
    intro h
    have hBN : B ≤ Subgroup.normalizer (D : Set G) := fun b hb =>
      (Subgroup.centralizer_le_normalizer (D : Set G))
        (Subgroup.mem_centralizer_iff.mpr fun d hd => (hAc b (hBA hb) d (hDA hd)).symm)
    have h1 := Sec6.card_sup_mul_card_inf hBN
    rw [h, Subgroup.card_bot, mul_one, hD9] at h1
    have h2 : Nat.card (B ⊔ D : Subgroup G) ≤ 27 :=
      hA.2 ▸ Subgroup.card_le_of_le (sup_le hBA hDA)
    omega
  have hBDM : Subgroup.normalizer ((B ⊓ D : Subgroup G) : Set G) ≤ M :=
    hND _ inf_le_right hBD
  have hconjA : ∀ y ∈ Subgroup.normalizer (B : Set G),
      A.map (MulAut.conj y).toMonoidHom ≤ M := by
    intro y hy
    rintro _ ⟨a, ha, rfl⟩
    refine hBDM ((Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr ?_))
    intro z hz
    have hz' : y⁻¹ * z * y ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) z).mp hz.1
      simpa using this
    have hc := hAc a ha _ (hBA hz')
    change z * (y * a * y⁻¹) = (y * a * y⁻¹) * z
    calc z * (y * a * y⁻¹) = y * ((y⁻¹ * z * y) * a) * y⁻¹ := by group
      _ = y * (a * (y⁻¹ * z * y)) * y⁻¹ := by rw [hc]
      _ = (y * a * y⁻¹) * z := by group
  obtain ⟨K, hK, hLK, halt⟩ := h198 G A c L E M hctx
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'def
  set D' := D.map (MulAut.conj g⁻¹).toMonoidHom with hD'def
  set M' := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'def
  have hA'M : A' ≤ M := hconjA g⁻¹ (inv_mem hgB)
  have hA'c : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hA'e : ∀ a ∈ A', a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAe a ha, map_one]
  have hBA' : B ≤ A' := by
    intro b hb
    rw [mem_map_conj_iff, inv_inv]
    exact hBA ((Subgroup.mem_normalizer_iff.mp hgB b).mp hb)
  have hD'A' : D' ≤ A' := Subgroup.map_mono hDA
  have hA'K : A' ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    mem_normalizer_of_pow_three_eq_one hctx hZ3 hK hLK (hA'M ha) (hA'e a ha)
  have hD'K : D' ≤ Subgroup.normalizer (K : Set G) := hD'A'.trans hA'K
  have hD'9 : Nat.card D' = 9 := by
    rw [hD'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD9]
  have hD'3 : IsPGroup 3 D' := hD3.map _
  have hD'ab : CFSG.Assembly.IsElemAbelian 3 D' :=
    ⟨⟨⟨fun a b => Subtype.ext (hA'c _ (hD'A' a.2) _ (hD'A' b.2))⟩⟩,
      fun x hx => hA'e x (hD'A' hx)⟩
  have hCM' : ∀ d ∈ D', d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ M' := by
    rintro _ ⟨d₀, hd₀, rfl⟩ hd1 x hx
    have hd₀1 : d₀ ≠ 1 := by
      rintro rfl
      exact hd1 (map_one _)
    have hX : Subgroup.zpowers d₀ ≠ ⊥ := by
      rwa [Ne, Subgroup.zpowers_eq_bot]
    rw [mem_map_conj_iff, inv_inv]
    apply hND _ ((Subgroup.zpowers_le).mpr hd₀) hX
    apply Sec12.mem_normalizer_zpowers_of_commute
    have hx' : x * (g⁻¹ * d₀ * g) = (g⁻¹ * d₀ * g) * x := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx
      simpa [MulAut.conj_apply] using this
    calc g * x * g⁻¹ * d₀ = g * (x * (g⁻¹ * d₀ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d₀ * g) * x) * g⁻¹ := by rw [hx']
      _ = d₀ * (g * x * g⁻¹) := by group
  have hKM' : K ≤ M' := by
    rcases halt with hKL | ⟨⟨p, f, hmodel⟩, -⟩
    ·
      obtain ⟨ι, -⟩ := exists_thetaQuot_mulEquiv hLK hKL
      have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
        (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
      have hDθ : D' ≤ Subgroup.normalizer
          (((aschbacherSolvableCore 3 K).map K.subtype : Subgroup G) : Set G) :=
        hD'K.trans (Sec6.normalizer_le_normalizer_theta K)
      have hθM : (aschbacherSolvableCore 3 K).map K.subtype ≤ M' :=
        le_of_centralizer_le hD'ab hD'9 hDθ
          (by rwa [Subgroup.card_map_of_injective K.subtype_injective]) hCM'
      refine le_of_closure_fixed_eq_top hθ3 hD'3 hD'K hDθ
        ((thetaAct K).comp (Subgroup.inclusion hD'K)) (fun d k k' h => thetaAct_mk _ k k' h)
        hθM hCM' ?_
      intro hinj
      set ρ := (thetaAct K).comp (Subgroup.inclusion hD'K) with hρ
      have hq : CFSG.IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
        LocalCores.isQuasisimple_of_mulEquiv ι
          (Sec12.isQuasisimple_thetaQuot_of_mem hctx.mem_lA.1)
      have hSLK : Sec4.IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K) :=
        isSLThreePi_of_mulEquiv ι hSL
      have hexp : ∀ φ ∈ ρ.range, φ ^ 3 = 1 := by
        rintro _ ⟨d, rfl⟩
        have hd3 : d ^ 3 = 1 := Subtype.ext (by simpa using hA'e d (hD'A' d.2))
        rw [← map_pow, hd3, map_one]
      have hcard : Nat.card ρ.range = 9 := by
        rw [← hD'9]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      by_cases hexc : Nonempty ((K ⧸ aschbacherSolvableCore 3 K) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
          ρ.range ≤ (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _).range
      · exfalso
        obtain ⟨⟨ψ⟩, hinn⟩ := hexc
        have hBD' := eq_of_inner_SL34 h197 hctx hD9 hK hLK hKL ψ hA'K hA'c hA'e hD'A' hD'9
          hinj hinn hBA hBA' hB9
        exact hBM (hBD' ▸ hND D le_rfl hD1)
      · have htop := hS _ ρ.range hexp hcard (Or.inl ⟨hq, hSLK, hexc⟩)
        rw [eq_top_iff, ← htop]
        apply Subgroup.closure_mono
        rintro x ⟨φ, ⟨d, rfl⟩, hφ1, hφx⟩
        exact ⟨d, fun h => hφ1 (by rw [h, map_one]), hφx⟩
    ·
      by_cases hp3 : p = 3
      · subst hp3
        exact (false_of_trialityD4_three hctx hK hmodel).elim
      have hO3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 K) := by
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
        rw [hk]
        intro h
        have := Nat.prime_three.dvd_of_dvd_pow h
        norm_num at this
      have hOeq : (CFSG.pCore 2 K).map K.subtype = CFSG.Open.pCoreOf 2 K := by
        rfl
      have hDO : D' ≤ Subgroup.normalizer
          (((CFSG.pCore 2 K).map K.subtype : Subgroup G) : Set G) := by
        rw [hOeq]
        exact hD'K.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
      have hOM : (CFSG.pCore 2 K).map K.subtype ≤ M' :=
        le_of_centralizer_le hD'ab hD'9 hDO
          (by rwa [Subgroup.card_map_of_injective K.subtype_injective]) hCM'
      refine le_of_closure_fixed_eq_top hO3 hD'3 hD'K hDO
        ((pCoreAct K).comp (Subgroup.inclusion hD'K)) (fun d k k' h => pCoreAct_mk _ k k' h)
        hOM hCM' ?_
      intro hinj
      set ρ := (pCoreAct K).comp (Subgroup.inclusion hD'K) with hρ
      have hexp : ∀ φ ∈ ρ.range, φ ^ 3 = 1 := by
        rintro _ ⟨d, rfl⟩
        have hd3 : d ^ 3 = 1 := Subtype.ext (by simpa using hA'e d (hD'A' d.2))
        rw [← map_pow, hd3, map_one]
      have hcard : Nat.card ρ.range = 9 := by
        rw [← hD'9]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have htop := hS _ ρ.range hexp hcard (Or.inr ⟨p, f, hp3, hmodel⟩)
      rw [eq_top_iff, ← htop]
      apply Subgroup.closure_mono
      rintro x ⟨φ, ⟨d, rfl⟩, hφ1, hφx⟩
      exact ⟨d, fun h => hφ1 (by rw [h, map_one]), hφx⟩
  have hgK : K.map (MulAut.conj g).toMonoidHom ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 := hKM' hk
    rw [hM'def, mem_map_conj_iff, inv_inv] at h1
    exact h1
  have hgE : E.map (MulAut.conj g).toMonoidHom ≤ M := by
    have hELA : E ≤ L ⊔ A := hctx.le_sup.trans inf_le_left
    refine (Subgroup.map_mono hELA).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le ((Subgroup.map_mono hLK).trans hgK) (hconjA g hgB)
  exact hgM (mem_of_map_conj_le hctx.hyp191 hE hctx.mem_scriptM hgE)

end CFSG.RankThree.PartTwo.Sec19
