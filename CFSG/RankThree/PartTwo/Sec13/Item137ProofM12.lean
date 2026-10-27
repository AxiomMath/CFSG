module

public import CFSG.RankThree.PartTwo.KFacts.KS18M12
import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_of_pow_three_pow' {N : Subgroup G} (hN : ¬ 3 ∣ Nat.card N) {g : G}
    (hg : g ∈ N) {k : ℕ} (hk : g ^ 3 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hg
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem le_zpowers_sup_of_inner {K E P : Subgroup G} {e : G}
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hinner : ∀ σ : MulAut (K ⧸ aschbacherSolvableCore 3 K), σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* _).range)
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hEdec : E = Subgroup.zpowers e ⊔ (E ⊓ K)) (hKe : K ≤ Subgroup.centralizer ({e} : Set G))
    (hEP : E ≤ P) (hP3 : IsPGroup 3 P) (hPexp : ∀ x ∈ P, x ^ 3 = 1)
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) (hPe : ∀ x ∈ P, x * e = e * x) :
    P ≤ Subgroup.zpowers e ⊔ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hθ3⟩ := Sec6.theta_solvable_and_not_dvd K
  set N := Subgroup.normalizer (K : Set G) with hNdef
  set ρ : N →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hρ
  set X := P ⊔ K with hX
  have hXN : X ≤ N := sup_le hPN Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := X)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup X).map X.subtype with hTdef
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T X := ⟨Q, rfl⟩
  have hPT : P ≤ T := fun x hx =>
    ⟨⟨x, (le_sup_left : P ≤ X) hx⟩, hQ (show (⟨x, _⟩ : X) ∈ P.subgroupOf X from hx), rfl⟩
  have hT3 : IsPGroup 3 T := hTsyl.isPGroup
  have hTN : T ≤ N := hTsyl.le.trans hXN
  obtain ⟨SK, hSK⟩ := hTsyl.inf_of_le_normalizer (le_sup_right : K ≤ X) hXN
  have hSKmem : ∀ q : K, q ∈ (SK : Subgroup K) ↔ (q : G) ∈ T ⊓ K := by
    intro q
    constructor
    · intro hq
      rw [← hSK]
      exact ⟨q, hq, rfl⟩
    · intro hq
      rw [← hSK] at hq
      obtain ⟨q', hq', hqq'⟩ := hq
      rwa [← Subtype.ext hqq']
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set Qb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    SK.mapSurjective (QuotientGroup.mk'_surjective _) with hQbdef
  have hQb : (Qb : Subgroup _) = (SK : Subgroup K).map π := Sylow.coe_mapSurjective _ _
  have hconj : Function.Injective
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _) :=
    KFacts.KS14.conj_injective_of_center_eq_bot hZ
  set Sh : Subgroup (K ⧸ aschbacherSolvableCore 3 K) :=
    ((T.subgroupOf N).map ρ).comap MulAut.conj with hShdef
  have hSh3 : IsPGroup 3 Sh :=
    ((hT3.comap_subtype (K := N)).map ρ).comap_of_injective _ hconj
  have hQbSh : (Qb : Subgroup _) ≤ Sh := by
    rw [hQb]
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨q, Subgroup.le_normalizer q.2⟩, ?_, ?_⟩
    · exact ((hSKmem q).mp hq).1
    · exact Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem q
  have hShQb : Sh = Qb := Qb.3 hSh3 hQbSh
  intro x hx
  have hxN : x ∈ N := hPN hx
  have hρ3 : ρ ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : N) ^ 3 = 1 := Subtype.ext (hPexp x hx)
    rw [this, map_one]
  obtain ⟨y, hy⟩ := hinner _ hρ3
  have hySh : y ∈ Sh := ⟨⟨x, hxN⟩, hPT hx, hy.symm⟩
  rw [hShQb, hQb] at hySh
  obtain ⟨q, hqSK, rfl⟩ := hySh
  have hqTK : (q : G) ∈ T ⊓ K := (hSKmem q).mp hqSK
  set r := (q : G)⁻¹ * x with hrdef
  have hqN : (q : G) ∈ N := Subgroup.le_normalizer q.2
  have hrN : r ∈ N := mul_mem (inv_mem hqN) hxN
  have hrD : r ∈ Sec4.thetaQuotCentralizer K := by
    refine Subgroup.mem_map.mpr ⟨⟨r, hrN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have he : (⟨r, hrN⟩ : N) = (⟨q, hqN⟩ : N)⁻¹ * ⟨x, hxN⟩ := rfl
    rw [he, map_mul, map_inv]
    change (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨q, hqN⟩))⁻¹ * ρ ⟨x, hxN⟩ = 1
    rw [Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem q, ← hy]
    exact inv_mul_cancel _
  have hrT : r ∈ T := mul_mem (inv_mem hqTK.1) (hPT hx)
  have hrQ : ∀ w ∈ T ⊓ K, r * w = w * r := by
    intro w hw
    have h1 : r * w * r⁻¹ ∈ T ⊓ K :=
      Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem hrT hw.1) (T.inv_mem hrT),
        (Subgroup.mem_normalizer_iff.mp hrN w).mp hw.2⟩
    have h2 := (Sec6.mem_thetaQuotCentralizer_iff.mp hrD).2 w hw.2
    have h3 : w⁻¹ * (r * w * r⁻¹) ∈ T := T.mul_mem (T.inv_mem hw.1) h1.1
    obtain ⟨k, hk⟩ := hT3 ⟨_, h3⟩
    have h4 := eq_one_of_mem_of_pow_three_pow' hθ3 h2 (k := k)
      (by simpa using congrArg Subtype.val hk)
    rw [inv_mul_eq_one] at h4
    calc r * w = r * w * r⁻¹ * r := by group
      _ = w * r := by rw [← h4]
  have hqr : (q : G) * r = r * (q : G) := (hrQ _ hqTK).symm
  have hxqr : x = (q : G) * r := by rw [hrdef, mul_inv_cancel_left]
  have hr3 : r ^ 3 = 1 := by
    have hx3 := hPexp x hx
    rw [hxqr, (show Commute (q : G) r from hqr).mul_pow] at hx3
    have hr3K : r ^ 3 ∈ K := by
      have : r ^ 3 = ((q : G) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hx3
      rw [this]
      exact inv_mem (pow_mem q.2 3)
    have hr3θ := Sec17.inf_thetaQuotCentralizer_le hZ ⟨hr3K, pow_mem hrD 3⟩
    obtain ⟨k, hk⟩ := hT3 ⟨_, pow_mem hrT 3⟩
    exact eq_one_of_mem_of_pow_three_pow' hθ3 hr3θ (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hre : r * e = e * r := by
    have h1 : (q : G) * e = e * q := Subgroup.mem_centralizer_singleton_iff.mp (hKe q.2)
    have h2 := hPe x hx
    calc r * e = (q : G)⁻¹ * (x * e) := by rw [hrdef, mul_assoc]
      _ = (q : G)⁻¹ * (e * x) := by rw [h2]
      _ = (q : G)⁻¹ * e * (q : G) * ((q : G)⁻¹ * x) := by group
      _ = e * r := by
        rw [show (q : G)⁻¹ * e * (q : G) = e by
          rw [mul_assoc, ← h1, inv_mul_cancel_left]]
  have hrE : ∀ y ∈ E, y * r = r * y := by
    have hle : E ≤ Subgroup.centralizer ({r} : Set G) := by
      rw [hEdec]
      refine sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hre.symm)) fun y hy => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hrQ y ⟨hPT (hEP hy.1), hy.2⟩).symm
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hrmem : r ∈ E := by
    have hsup := Sec15.isElemAbelian_sup_zpowers hE hr3 hrE
    rw [← hEmax _ hsup le_sup_left]
    exact (le_sup_right : Subgroup.zpowers r ≤ E ⊔ Subgroup.zpowers r) (Subgroup.mem_zpowers r)
  rw [hxqr]
  have hEle : E ≤ Subgroup.zpowers e ⊔ K := hEdec ▸ sup_le_sup_left inf_le_right _
  exact mul_mem (Subgroup.mem_sup_right q.2) (hEle hrmem)

theorem exists_zpow_mul_of_mem_zpowers_sup {K : Subgroup G} {e x : G}
    (hKe : K ≤ Subgroup.centralizer ({e} : Set G)) (hx : x ∈ Subgroup.zpowers e ⊔ K) :
    ∃ (i : ℤ) (k : G), k ∈ K ∧ x = e ^ i * k := by
  have hcomm : ∀ y ∈ Subgroup.zpowers e, ∀ k ∈ K, y * k = k * y := by
    intro y hy k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)).symm j).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hx' : x ∈ ((Subgroup.zpowers e ⊔ K : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, k, hk, hak⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨i, k, hk, hak.symm⟩

theorem exists_inverting_of_m12 (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (hK18 : KFacts.KS18M12) {A L P E F K : Subgroup G}
    {c t e : G} (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hcfg : Config137 A c L P E F t) (hST : HypS E ∨ HypT E)
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heZ : e ∈ Subgroup.centralizer (P : Set G))
    (hφ : Nonempty (lBarA e K E ≃*
      Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12)) :
    ∃ s ∈ K ⊓ Subgroup.normalizer (P : Set G), ∀ z ∈ ⁅P, P⁆, s * z * s⁻¹ = z⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hφ
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hspor' := hspor
  obtain ⟨-, ⟨hM12p, hM12z⟩, -⟩ := hspor'
  obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hM12p φ
  have hKM : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    ⟨φK⟩
  obtain ⟨heK, h9, -⟩ := facts_of_m12 h131 hspor hD hKM
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    center_eq_bot_of_mulEquiv φK hM12z
  have he3 : e ^ 3 = 1 := hD.isElemAbelian.2 e hD.mem_A
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := hD.le_centralizer
  have hKc : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)
  have hE3 := hD.isElemAbelian
  have hE27 := hD.card_eq
  have hEdec : E = Subgroup.zpowers e ⊔ (E ⊓ K) := by
    have hle : Subgroup.zpowers e ⊔ (E ⊓ K) ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr hD.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine he3
      (fun heB : e ∈ E ⊓ K => heK heB.2) le_rfl h9
      (fun b hb => hE3.2 b hb.1) (fun b hb => hD.commute hD.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hE27, hcard])).symm
  have hEle : E ≤ Subgroup.zpowers e ⊔ K := hEdec ▸ sup_le_sup_left inf_le_right _
  have hcfg' := hcfg
  obtain ⟨hP, hAP, -, -, hΔ, -⟩ := hcfg'
  obtain ⟨-, -, -, -, -, -, -, hP81, hPexp⟩ :=
    exists_commutator_eq_zpowers_of_isSylowOf h131 hspor h414 h hM hP hAP
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [hP81]; norm_num)
  have hEP : E ≤ P := by
    have hmem : E ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
        Nat.card B = 27} := by
      rw [hΔ]
      exact Or.inr (Or.inr (Or.inl rfl))
    exact hmem.1
  have hPe : ∀ x ∈ P, x * e = e * x := fun x hx => Subgroup.mem_centralizer_iff.mp heZ x hx
  have hPNE : P ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_card hEP hE27 hP81
  have h3K := three_dvd_card_of_sec13Data h131 hspor hD
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxe : x * e * x⁻¹ = e := by rw [hPe x hx, mul_inv_cancel_right]
    have hKx : K.map (MulAut.conj x).toMonoidHom ∈ lA E e := by
      have := (map_conj_mem_lA_iff (hPNE hx)).mpr hK
      rwa [hxe] at this
    have heq := eq_of_mem_thetaComponentsAt_of_maximal hD.orderOf_eq hD.mem_thetaComponentsAt
      hZK hEle hE3 (fun F' hF' hXF' => (hXF.2.1 F' hF' hXF') ▸ le_rfl) hKx.1
      (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]; exact h3K)
    exact map_conj_eq_iff_mem_normalizer.mp heq
  have hinner : ∀ σ : MulAut (K ⧸ aschbacherSolvableCore 3 K), σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* _).range := by
    intro σ hσ
    obtain ⟨-, -, hinn, -⟩ := hK18 (K ⧸ aschbacherSolvableCore 3 K) hKM
    obtain ⟨y, hy⟩ := hinn σ ⟨1, by rw [pow_one]; exact hσ⟩
    exact ⟨y, hy.symm⟩
  have hPeK := le_zpowers_sup_of_inner hZK hinner hE3 hXF.2.1 hEdec hKe hEP hP3 hPexp hPNK hPe
  have heP : e ∈ P := hEP hD.mem_A
  have hPeq : P = Subgroup.zpowers e ⊔ (P ⊓ K) := by
    refine le_antisymm (fun x hx => ?_)
      (sup_le (Subgroup.zpowers_le.mpr heP) inf_le_left)
    obtain ⟨i, k, hk, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup hKe (hPeK hx)
    have hkP : k ∈ P := by
      have := P.mul_mem (P.inv_mem (P.zpow_mem heP i)) hx
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers e i))
      (Subgroup.mem_sup_right ⟨hkP, hk⟩)
  have hPK27 : Nat.card (P ⊓ K : Subgroup G) = 27 := by
    have hcomm : ∀ y ∈ Subgroup.zpowers e, ∀ k ∈ P ⊓ K, y * k = k * y := by
      intro y hy k hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hKc k hk.2).symm j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have he1 : e ≠ 1 := hD.ne_one
    rw [← hPeq, hP81, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot he3 heK).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three he3 he1] at hcard
    omega
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 K))
  have hS₀ : Nat.card (S₀ : Subgroup K) = 27 := by
    set Qb₀ : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
      S₀.mapSurjective (QuotientGroup.mk'_surjective _)
    have hQb₀ : (Qb₀ : Subgroup _) =
        (S₀ : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
      Sylow.coe_mapSurjective _ _
    obtain ⟨hHeis₀, -⟩ := h414 _ hKM Qb₀
    rw [← card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three S₀.isPGroup'), ← hQb₀]
    exact hHeis₀.2.1
  have hSylPK : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ K) K := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right ?_
    rw [hPK27, ← hS₀, Sylow.card_eq_multiplicity]
  obtain ⟨SK, hSK⟩ := hSylPK
  have hS3 : IsPGroup 3 (SK : Subgroup K) := SK.isPGroup'
  set Qb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    SK.mapSurjective (QuotientGroup.mk'_surjective _) with hQbdef
  have hQb : (Qb : Subgroup _) =
      (SK : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hHeis, -, -, -, -, t₁, ht₁, hinv, -⟩ := h414 _ hKM Qb
  rw [hQb] at hHeis ht₁ hinv
  rw [normalizer_map_mk_eq hS3] at ht₁
  obtain ⟨t', ht', rfl⟩ := ht₁
  have hPeq' : P = Subgroup.zpowers e ⊔ (SK : Subgroup K).map K.subtype := by
    rw [hSK]
    exact hPeq
  refine ⟨(t' : G), Subgroup.mem_inf.mpr ⟨t'.2, ?_⟩, ?_⟩
  · rw [hPeq']
    exact mem_normalizer_zpowers_sup hKc ht'
  · rw [hPeq']
    exact inv_of_mem_commutator hKc hS3 hHeis ht' hinv

end CFSG.RankThree.PartTwo.Sec13
