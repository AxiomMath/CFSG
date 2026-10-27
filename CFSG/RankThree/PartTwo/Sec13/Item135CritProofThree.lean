module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofA7
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def KS135A7TwoLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) →
    c ∉ L → Nat.card (A ⊓ L : Subgroup G) = 9 →
    ∃ (R : Subgroup G) (b : G), R ≤ L ∧ IsPGroup 2 R ∧
      ¬ R ≤ (aschbacherSolvableCore 3 L).map L.subtype ∧
      b ∈ A ⊓ L ∧ b ≠ 1 ∧ b ∈ Subgroup.centralizer (R : Set G) ∧
      ∀ x ∈ L ⊓ Subgroup.centralizer (R : Set G),
        x * b * x⁻¹ * b⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype

@[expose] def Item135A7ThreeTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → c ∉ L → Nat.card (A ⊓ L : Subgroup G) = 9 →
    Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
    CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) → Nat.card (oThreeWStar A) = 9 →
    wStar A = oThreeWStar A ⊔ Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A →
    omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) →
    (omegaA A).ncard = 9 →
    ∀ B : Subgroup G, B ≤ A → c ∈ B → Nat.card B = 9 →
      ∀ F : Subgroup G, F ≤ B → Nat.card F = 3 → ¬ F ≤ L →
        ∃ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (B : Set G) ∧
          F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom

namespace ThreeProof

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_centralizes {c x : G} {L R : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) (hRL : R ≤ L)
    (hRθ : ¬ R ≤ (aschbacherSolvableCore 3 L).map L.subtype)
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G))
    (hxR : x ∈ Subgroup.centralizer (R : Set G)) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  set L' := L.map (MulAut.conj x).toMonoidHom with hL'def
  have hxc' : (MulAut.conj x) c = c := by
    rw [MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    rw [hxc, mul_inv_cancel_right]
  have hL' : L' ∈ thetaComponentsAt 3 c := by
    have h := map_mem_thetaComponentsAt (MulAut.conj x) hL
    rwa [hxc'] at h
  by_cases hne : L' = L
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hne
  exfalso
  apply hRθ
  intro r hr
  have hrL : r ∈ L := hRL hr
  have hrL' : r ∈ L' := by
    refine ⟨r, hrL, ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hxR r hr
    change x * r * x⁻¹ = r
    rw [← this, mul_inv_cancel_right]
  have hrN : r ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hrL
  have hrC := mem_thetaQuotCentralizer_of_ne_mem_thetaComponentsAt hL' hL hne hrL' hrN
  obtain ⟨-, hcomm⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hrC
  set θ := aschbacherSolvableCore 3 L with hθ
  have hcen : ((⟨r, hrL⟩ : L) : L ⧸ θ) ∈ Subgroup.center (L ⧸ θ) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := hcomm (l : G) l.2
    obtain ⟨t, ht, hteq⟩ := h1
    have ht' : (l⁻¹ * (⟨r, hrL⟩ * l * (⟨r, hrL⟩ : L)⁻¹) : L) = t := by
      apply Subtype.ext
      change _ = L.subtype t
      rw [hteq]
      simp
    have h2 : ((l⁻¹ * (⟨r, hrL⟩ * l * (⟨r, hrL⟩ : L)⁻¹) : L) : L ⧸ θ) = 1 := by
      rw [ht', QuotientGroup.eq_one_iff]
      exact ht
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    have h3 := congrArg (fun y => (l : L ⧸ θ) * y * ((⟨r, hrL⟩ : L) : L ⧸ θ)) h2
    simp only [mul_one, mul_inv_cancel_left, mul_assoc, inv_mul_cancel] at h3
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h3 ⊢
    exact h3.symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  exact ⟨⟨r, hrL⟩, hcen, rfl⟩

theorem card_inf_eq_three_and_sup_eq {A B L : Subgroup G} {c : G} (hA27 : Nat.card A = 27)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hcB : c ∈ B)
    (hcL : c ∉ L) :
    Nat.card (B ⊓ L : Subgroup G) = 3 ∧ Subgroup.zpowers c ⊔ (B ⊓ L) = B := by
  have hA := Subgroup.relIndex_mul_card (H := L) (K := A)
  have hB := Subgroup.relIndex_mul_card (H := L) (K := B)
  rw [inf_comm, h9, hA27] at hA
  rw [hB9] at hB
  have hLA : L.relIndex A = 3 := by omega
  have hLB : L.relIndex B ≤ 3 :=
    hLA ▸ Subgroup.relIndex_le_of_le_right hBA (by rw [hLA]; norm_num)
  have hLB1 : L.relIndex B ≠ 1 := by
    intro h
    exact hcL (Subgroup.relIndex_eq_one.mp h hcB)
  have hcard : Nat.card (B ⊓ L : Subgroup G) = 3 := by
    rw [inf_comm]
    set k := L.relIndex B with hk
    have h0 : k ≠ 0 := by
      intro h
      rw [h, zero_mul] at hB
      omega
    have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with h | h
    · rw [h] at hB
      omega
    · rw [h] at hB
      omega
  refine ⟨hcard, ?_⟩
  set M := Subgroup.zpowers c ⊔ (B ⊓ L) with hM
  have hle : M ≤ B := sup_le (Subgroup.zpowers_le.mpr hcB) inf_le_left
  have hd1 : Nat.card (B ⊓ L : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le le_sup_right
  have hd2 : Nat.card M ∣ Nat.card B := Subgroup.card_dvd_of_le hle
  have hne : Nat.card M ≠ 3 := by
    intro h3
    have hMeq : B ⊓ L = M :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, hcard])
    have hcM : c ∈ M := le_sup_left (a := Subgroup.zpowers c) (Subgroup.mem_zpowers c)
    rw [← hMeq] at hcM
    exact hcL hcM.2
  rw [hcard] at hd1
  rw [hB9] at hd2
  have h9M : Nat.card M = 9 := by
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hle9 : Nat.card M ≤ 9 := Nat.le_of_dvd (by norm_num) hd2
    interval_cases h : Nat.card M <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h9M, hB9])

omit [Finite G] in
theorem commutator_zpow_mem {L : Subgroup G} {u b : G} (hu : u ∈ L) (hb : b ∈ L)
    (h : u * b * u⁻¹ * b⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype) (k : ℤ) :
    u * b ^ k * u⁻¹ * (b ^ k)⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype := by
  set θ := aschbacherSolvableCore 3 L with hθ
  set uL : L := ⟨u, hu⟩
  set bL : L := ⟨b, hb⟩
  obtain ⟨t, ht, hte⟩ := h
  have ht' : uL * bL * uL⁻¹ * bL⁻¹ = t := Subtype.ext (by
    change _ = L.subtype t
    rw [hte]
    rfl)
  have hc : (uL : L ⧸ θ) * bL = bL * uL := by
    have h1 : ((uL * bL * uL⁻¹ * bL⁻¹ : L) : L ⧸ θ) = 1 := by
      rw [ht', QuotientGroup.eq_one_iff]
      exact ht
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (uL : L ⧸ θ) * bL = ((uL : L ⧸ θ) * bL * (uL : L ⧸ θ)⁻¹ * (bL : L ⧸ θ)⁻¹) *
          ((bL : L ⧸ θ) * uL) := by group
      _ = bL * uL := by rw [h1, one_mul]
  have hck : (uL : L ⧸ θ) * (bL : L ⧸ θ) ^ k = (bL : L ⧸ θ) ^ k * uL :=
    ((Commute.zpow_right (hc : Commute (uL : L ⧸ θ) bL) k)).eq
  refine ⟨uL * bL ^ k * uL⁻¹ * (bL ^ k)⁻¹, ?_, rfl⟩
  change uL * bL ^ k * uL⁻¹ * (bL ^ k)⁻¹ ∈ θ
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, hck]
  group

omit [Finite G] in
theorem eq_one_of_mem_of_odd {P O : Subgroup G} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O))
    {z : G} (hzP : z ∈ P) (hzO : z ∈ O) : z = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨z, hzP⟩
  have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hd2 : orderOf z ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk _ hzO]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

end ThreeProof

open ThreeProof in
theorem item135A7Three_of_inputs (hR : KS135A7TwoLocal) (hT : Item135A7ThreeTrans) :
    Item135A7Three := by
  intro G _ _ A c L hD hST hnq hO2 hm hO hA7 hprod hstar hcL h9 hirr hN hO3 hO9 hW hΩ hΩ9 hL
  obtain ⟨R, b₀, hRL, hR2, hRθ, hb₀AL, hb₀1, hb₀R, hRab⟩ := hR G A c L hD hA7 hcL h9
  obtain ⟨e⟩ := hA7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [isPerfect_center_alt7.2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hLc := hD.mem_thetaComponentsAt
  have hcR : c ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hRL hr)))
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers b₀ with hBdef
  have hBA : B ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hD.mem_A) (Subgroup.zpowers_le.mpr hb₀AL.1)
  have hBR : B ≤ Subgroup.centralizer (R : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcR) (Subgroup.zpowers_le.mpr hb₀R)
  have hcB : c ∈ B := le_sup_left (a := Subgroup.zpowers c) (Subgroup.mem_zpowers c)
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => hD.isElemAbelian.2 b (hBA hb)
  have hBel : CFSG.Assembly.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, hB3⟩
    exact hD.commute (hBA x.2) (hBA y.2)
  have hB9 : Nat.card B = 9 := by
    have hle9 : Nat.card B ≤ 9 := by
      have hcl : B = Subgroup.closure ({c, b₀} : Set G) := by
        rw [hBdef, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
          ← Subgroup.closure_union, Set.singleton_union]
      rw [hcl]
      exact Sec10.card_closure_pair_le (hD.commute hD.mem_A hb₀AL.1)
        (hD.isElemAbelian.2 c hD.mem_A) (hD.isElemAbelian.2 b₀ hb₀AL.1)
    have hd27 : Nat.card B ∣ 27 := hD.card_eq ▸ Subgroup.card_dvd_of_le hBA
    have hb₀3 : Nat.card (Subgroup.zpowers b₀) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hD.isElemAbelian.2 b₀ hb₀AL.1) hb₀1
    have hd3 : 3 ∣ Nat.card B := hb₀3 ▸ Subgroup.card_dvd_of_le le_sup_right
    have hne3 : Nat.card B ≠ 3 := by
      intro h3
      have hBeq : Subgroup.zpowers b₀ = B :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3, hb₀3])
      have hcz : c ∈ Subgroup.zpowers b₀ := hBeq ▸ hcB
      exact hcL (Subgroup.zpowers_le.mpr hb₀AL.2 hcz)
    have hpos : 0 < Nat.card B := Nat.card_pos
    interval_cases h : Nat.card B <;> omega
  obtain ⟨hBL3, hBsup⟩ := card_inf_eq_three_and_sup_eq hD.card_eq h9 hBA hB9 hcB hcL
  have hBL1 : B ⊓ L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBL3
    omega
  have hR1 : R ≠ ⊥ := fun h => hRθ (h ▸ bot_le)
  have hRC : R ≤ Subgroup.centralizer (B : Set G) := Subgroup.le_centralizer_iff.mp hBR
  set CB := Subgroup.centralizer (B : Set G) with hCB
  have hR2' : IsPGroup 2 (R.subgroupOf CB) := hR2.comap_subtype
  obtain ⟨S, hRS⟩ := hR2'.exists_le_sylow
  set SG : Subgroup G := (S : Subgroup CB).map CB.subtype with hSGdef
  have hSG2 : IsPGroup 2 SG := S.isPGroup'.map _
  have hRSG : R ≤ SG := fun r hr => ⟨⟨r, hRC hr⟩, hRS hr, rfl⟩
  have hSG1 : SG ≠ ⊥ := fun h => hR1 (le_bot_iff.mp (h ▸ hRSG))
  have hSGB : SG ≤ CB := Subgroup.map_subtype_le _
  have hBSG : B ≤ Subgroup.centralizer (SG : Set G) := Subgroup.le_centralizer_iff.mp hSGB
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (SG : Set G)) with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hQS : Q ≤ Subgroup.centralizer (SG : Set G) := Subgroup.map_subtype_le _
  obtain ⟨b, hbB, hb1, hbQ⟩ := Sec6.exists_commutator_inf_centralizer_ne_bot
    hD.charTwoType hSG2 hSG1 hBel (by omega) hBSG inf_le_left hBL1
  have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hB3 b hbB) hb1
  have hbL : b ∉ L := by
    intro hbL
    apply hbQ
    have hzle : Subgroup.zpowers b ≤ B ⊓ L := Subgroup.zpowers_le.mpr ⟨hbB, hbL⟩
    have hBLz : B ⊓ L = Subgroup.zpowers b :=
      (Subgroup.eq_of_le_of_card_ge hzle (by rw [hbcard, hBL3])).symm
    rw [hBLz, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hyb : Commute y b := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact (hyb.symm.zpow_left k).eq
  obtain ⟨w, -, hwB, hwF⟩ := hT G A c L hD hcL h9 hirr hN hO3 hO9 hW hΩ hΩ9 B hBA hcB hB9
    (Subgroup.zpowers b) (Subgroup.zpowers_le.mpr hbB) hbcard
    (fun h => hbL (h (Subgroup.mem_zpowers b)))
  have hwC : w ∈ Subgroup.normalizer (CB : Set G) := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer B hwB
  obtain ⟨r, hr, hrw⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.exists_mul_mem_normalizer_sylow S hwC
  set n := r * w with hn
  have hnS : n ∈ Subgroup.normalizer (SG : Set G) := hrw
  have hnB : n ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hr) hwB
  have hwc : w * c * w⁻¹ ∈ Subgroup.zpowers b := by
    rw [hwF]
    exact ⟨c, Subgroup.mem_zpowers c, rfl⟩
  have hnc : n * c * n⁻¹ ∈ Subgroup.zpowers b := by
    have hwcB : w * c * w⁻¹ ∈ B := Subgroup.zpowers_le.mpr hbB hwc
    have h1 : r * (w * c * w⁻¹) * r⁻¹ = w * c * w⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hr _ hwcB
      rw [← this, mul_inv_cancel_right]
    have h2 : n * c * n⁻¹ = r * (w * c * w⁻¹) * r⁻¹ := by rw [hn]; group
    rw [h2, h1]
    exact hwc
  have hnQ : n ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 (Subgroup.centralizer (SG : Set G)))
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer SG hnS)
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBSG.trans
    (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (SG : Set G)))))
  obtain ⟨x, hx, a, ha, hxa⟩ : ∃ x ∈ Q ⊓ Subgroup.centralizer {b}, ∃ a ∈ B ⊓ L,
      x * a * x⁻¹ * a⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hbQ
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx a ha
    rw [Subgroup.mem_bot, commutatorElement_def]
    exact hcon x hx a ha
  set x' := n⁻¹ * x * n with hx'
  set a' := n⁻¹ * a * n with ha'
  have hx'Q : x' ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnQ) x).mp hx.1
    rw [inv_inv] at h
    exact h
  have hx'c : x' ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnc
    have hxb : Commute x b := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have h1 : x * (n * c * n⁻¹) = (n * c * n⁻¹) * x := by
      rw [← hk]
      exact (hxb.zpow_right k).eq
    calc x' * c = n⁻¹ * (x * (n * c * n⁻¹)) * n := by rw [hx']; group
      _ = n⁻¹ * ((n * c * n⁻¹) * x) * n := by rw [h1]
      _ = c * x' := by rw [hx']; group
  have ha'B : a' ∈ B := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnB) a).mp ha.1
    rw [inv_inv] at h
    exact h
  have hx'a' : x' * a' * x'⁻¹ * a'⁻¹ ≠ 1 := by
    intro h
    apply hxa
    have h1 : x' * a' * x'⁻¹ * a'⁻¹ = n⁻¹ * (x * a * x⁻¹ * a⁻¹) * n := by
      rw [hx', ha']
      group
    rw [h1] at h
    calc x * a * x⁻¹ * a⁻¹ = n * (n⁻¹ * (x * a * x⁻¹ * a⁻¹) * n) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨a'', ha'', hx'a''⟩ : ∃ a'' ∈ B ⊓ L, x' * a'' * x'⁻¹ * a''⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hx'a'
    have hle : Subgroup.zpowers c ⊔ (B ⊓ L) ≤ Subgroup.centralizer ({x'} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hx'c).symm
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc := hcon z hz
        calc z * x' = (x' * z * x'⁻¹ * z⁻¹)⁻¹ * (x' * z) := by group
          _ = x' * z := by rw [hc, inv_one, one_mul]
    rw [hBsup] at hle
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle ha'B)
    calc x' * a' * x'⁻¹ * a'⁻¹ = x' * a' * (a' * x')⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  set X := Q ⊓ Subgroup.centralizer ({c} : Set G) with hXdef
  set U := ⁅X, B ⊓ L⁆ with hUdef
  have hx'X : x' ∈ X := ⟨hx'Q, hx'c⟩
  have hmemU : x' * a'' * x'⁻¹ * a''⁻¹ ∈ U := by
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hx'X ha''
  have hXQ : X ≤ Q := inf_le_left
  have hX2 : IsPGroup 2 X := hQ2.to_le hXQ
  have hBLX : B ⊓ L ≤ Subgroup.normalizer (X : Set G) := by
    intro z hz
    have hzB := (Subgroup.mem_inf.mp hz).1
    have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute (hBA hzB) hD.mem_A)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hBQ hzB, Subgroup.le_normalizer hzc⟩
  have hUX : U ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hBLX
  have hU2 : IsPGroup 2 U := hX2.to_le hUX
  have hBL3' : IsPGroup 3 (B ⊓ L : Subgroup G) := IsPGroup.of_card (n := 1) (by rw [hBL3]; norm_num)
  have hX3 : ¬ 3 ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hidem : ⁅U, B ⊓ L⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
      Nat.prime_three (B ⊓ L) X hBL3' hX3 hBLX
  have hQR : Q ≤ Subgroup.centralizer (R : Set G) :=
    hQS.trans (Subgroup.centralizer_le hRSG)
  have hUL : U ≤ L := by
    rw [hUdef, Subgroup.commutator_le]
    intro y hy z hz
    have hyN : y ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_centralizes hLc hZ hRL hRθ hy.2 (hQR hy.1)
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN z).mp hz.2) (L.inv_mem hz.2)
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := e.isSimpleGroup
  have hOθ : CFSG.oddCore L ≤ aschbacherSolvableCore 3 L := oddCore_le_of_isQuasisimple hθs hO
  have hZO := center_quotient_oddCore_eq_map hθs hZ hO hOθ
  have hθcen : ∀ v ∈ (aschbacherSolvableCore 3 L).map L.subtype, ∀ z ∈ L,
      v * z * v⁻¹ * z⁻¹ ∈ (CFSG.oddCore L).map L.subtype := by
    rintro _ ⟨v, hv, rfl⟩ z hz
    have hvc : QuotientGroup.mk' (CFSG.oddCore L) v ∈
        Subgroup.center (L ⧸ CFSG.oddCore L) := by
      rw [hZO]
      exact ⟨v, hv, rfl⟩
    have h1 := Subgroup.mem_center_iff.mp hvc (QuotientGroup.mk' (CFSG.oddCore L) ⟨z, hz⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    refine ⟨v * ⟨z, hz⟩ * v⁻¹ * (⟨z, hz⟩ : L)⁻¹, ?_, by simp⟩
    have e2 : (v * ⟨z, hz⟩ * v⁻¹ * (⟨z, hz⟩ : L)⁻¹ : L) =
        ((⟨z, hz⟩ : L) * v) * ((⟨z, hz⟩ * v)⁻¹ * (v * ⟨z, hz⟩)) * ((⟨z, hz⟩ : L) * v)⁻¹ := by
      group
    rw [e2]
    exact (inferInstance : (CFSG.oddCore L).Normal).conj_mem _ h1 _
  have hOodd : Odd (Nat.card ((CFSG.oddCore L).map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.ABGDGroups.odd_card_oddCore L
  have hb₀BL : B ⊓ L = Subgroup.zpowers b₀ := by
    have hb₀3 : Nat.card (Subgroup.zpowers b₀) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hD.isElemAbelian.2 b₀ hb₀AL.1) hb₀1
    have hle : Subgroup.zpowers b₀ ≤ B ⊓ L :=
      Subgroup.zpowers_le.mpr ⟨le_sup_right (a := Subgroup.zpowers c) (Subgroup.mem_zpowers b₀),
        hb₀AL.2⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hBL3, hb₀3])).symm
  have hU1' : ⁅U, B ⊓ L⁆ ≤ (aschbacherSolvableCore 3 L).map L.subtype ⊓ U := by
    rw [Subgroup.commutator_le]
    intro u hu z hz
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      rw [hb₀BL] at hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact commutator_zpow_mem (hUL hu) hb₀AL.2 (hRab u ⟨hUL hu, hQR (hXQ (hUX hu))⟩) k
    · rw [← hidem]
      exact Subgroup.commutator_mem_commutator hu hz
  have hU2' : ⁅⁅U, B ⊓ L⁆, B ⊓ L⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hvθ, hvU⟩ := hU1' hv
    have h1 := hθcen v hvθ z hz.2
    have h2 : ⁅v, z⁆ ∈ U := by
      rw [← hidem]
      exact Subgroup.commutator_mem_commutator hvU hz
    rw [commutatorElement_def] at h2 ⊢
    exact eq_one_of_mem_of_odd hU2 hOodd h2 h1
  have hU1 : U = ⊥ := by
    rw [← hidem, ← hidem]
    exact hU2'
  rw [hU1, Subgroup.mem_bot] at hmemU
  exact hx'a'' hmemU

end CFSG.RankThree.PartTwo.Sec13
