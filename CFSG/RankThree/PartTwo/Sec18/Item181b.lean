module

public import CFSG.RankThree.PartTwo.Sec18.Item181
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.KFacts.KS18Basic
import CFSG.RankThree.CentralCover.FourGroupWitness

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_pow_three_of_pow_two_pow {x : G} (h3 : x ^ 3 = 1) {k : ℕ}
    (h2 : x ^ (2 ^ k) = 1) : x = 1 := by
  have hd : orderOf x ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  have hg : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

omit [Finite G] in
theorem inf_eq_bot_of_elemAbelian_three {A R : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hR : IsPGroup 2 R) : A ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hR ⟨x, hx.2⟩
  exact eq_one_of_pow_three_of_pow_two_pow (hA.2 x hx.1)
    (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {K : Subgroup G} {g : G}
    (h : ∀ x ∈ K, g * x * g⁻¹ ∈ K) (h' : ∀ x ∈ K, g⁻¹ * x * g⁻¹⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

theorem perfectResidual_le_of_commutator_le {A M H B : Subgroup G} (h : Sec18Std G A M)
    (hAH : A ≤ H) (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hcomm : ∀ l ∈ inSubgroup perfectResidual H, ∀ b ∈ B,
      l * b * l⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 H) :
    inSubgroup perfectResidual H ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hBH : B ≤ H := hBA.trans hAH
  have hRM : R ≤ M := le_of_le_normalizer_of_isPGroup_two h hR2 (hAH.trans hHR)
  have hBE : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le hA.1 hBA
  have hNB : Subgroup.normalizer (B : Set G) ≤ M :=
    (normalizer_le_gamma hBA (two_le_pRank_of_elemAbelian hBE hB9.ge)).trans h.mem_scriptM.2
  have hconj : ∀ l ∈ L, ∀ x ∈ B ⊔ R, l * x * l⁻¹ ∈ B ⊔ R := by
    intro l hl
    have hle : B ⊔ R ≤ (B ⊔ R).comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_comap]
        change l * b * l⁻¹ ∈ B ⊔ R
        have h1 : l * b * l⁻¹ = (l * b * l⁻¹ * b⁻¹) * b := by group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm l hl b hb))
          (Subgroup.mem_sup_left hb)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hHR (hLH hl)) r).mp hr)
    intro x hx
    exact hle hx
  have hLN : L ≤ Subgroup.normalizer ((B ⊔ R : Subgroup G) : Set G) := fun l hl =>
    mem_normalizer_of_conj_mem (hconj l hl) (by simpa using hconj l⁻¹ (inv_mem hl))
  have hBR : B ⊓ R = ⊥ := inf_eq_bot_of_elemAbelian_three hBE hR2
  have hBN : B ≤ Subgroup.normalizer (R : Set G) := hBH.trans hHR
  have hcard : Nat.card (B ⊔ R : Subgroup G) = Nat.card B * Nat.card R := by
    rw [sup_comm, CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hBN
      (by rw [inf_comm]; exact hBR), mul_comm]
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (B ⊔ R) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num), ?_⟩
    have hrel : B.relIndex (B ⊔ R) = Nat.card R := by
      have h1 := Subgroup.relIndex_mul_card B (B ⊔ R)
      rw [inf_eq_left.mpr le_sup_left, hcard] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1, mul_comm])
    rw [hrel]
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hfr := le_sup_normalizer_of_isSylowOf hsyl hLN
  exact hfr.trans (sup_le (sup_le (hBA.trans (sec18Std_le h)) hRM) hNB)

theorem perfectResidual_not_le_of_mem_scriptH {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) : ¬ inSubgroup perfectResidual H ≤ M := by
  intro hLM
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  apply inf_ne_of_mem_scriptH₀ hH₀
  refine inf_eq_left.mpr ?_
  rw [hH₀.1]
  exact sup_le (sup_le hLM (sec18Std_le h))
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)

theorem pCoreOf_inf_eq_of_concl4442 (hK : KFacts.KS18OuterInvolution) {A M H : Subgroup G}
    (h : Sec18Std G A M) (hH : H ∈ scriptH A M) {s : G} (hs : Sec4.Concl4442 A M H s) :
    CFSG.Open.pCoreOf 2 (H ⊓ M) = Subgroup.zpowers s ⊔ CFSG.Open.pCoreOf 2 H ∧
      (CFSG.Open.pCoreOf 2 H).relIndex (CFSG.Open.pCoreOf 2 (H ⊓ M)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨hsS, hsA, -, hsH, X, hXn, hX, hXt, htX⟩ := hs
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set t : H ⧸ CFSG.pCore 2 H := π ⟨s, hsH⟩ with ht
  have hRS : R ≤ S := pCoreOf_le_pCoreOf_inf h hAH
  have hSH : S ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRdef, CFSG.Open.pCoreOf]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
  set T : Subgroup (H ⧸ CFSG.pCore 2 H) := (S.subgroupOf H).map π with hT
  have hT2 : IsPGroup 2 T := (hS2.comap_subtype (K := H)).map π
  have htT : t ∈ T := ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := hT2.to_le (Subgroup.zpowers_le.mpr htT)
  set f : A.subgroupOf H →* H ⧸ CFSG.pCore 2 H := π.comp (A.subgroupOf H).subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, hmemR] at ha
    have hbot := inf_eq_bot_of_elemAbelian_three hA.1 hR2
    have : ((a : H) : G) ∈ A ⊓ R := ⟨Subgroup.mem_subgroupOf.mp a.2, ha⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
  set E : Subgroup (H ⧸ CFSG.pCore 2 H) := f.range with hE
  have hE27 : Nat.card E = 27 := by
    rw [hE, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, ← hA.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      change f a * f b = f b * f a
      rw [← map_mul, ← map_mul, (isE27_subgroupOf hA hAH).1.1.is_comm.comm a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using (isE27_subgroupOf hA hAH).1.2 (a : H) a.2)
      rw [this, map_one]
  have hEmem : ∀ a ∈ A, ∀ ha : a ∈ H, π ⟨a, ha⟩ ∈ E := fun a haA ha =>
    ⟨⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr haA⟩, rfl⟩
  have hEX : E ≤ X := by
    rintro _ ⟨a, rfl⟩
    have hq : IsPGroup 2 ((H ⧸ CFSG.pCore 2 H) ⧸ X) := by
      have h1 := ht2.map (QuotientGroup.mk' X)
      have h2 : (Subgroup.zpowers t).map (QuotientGroup.mk' X) = ⊤ := by
        rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' X)
          (QuotientGroup.mk'_surjective X), ← hXt, Subgroup.map_sup,
          (QuotientGroup.map_mk'_self X), bot_sup_eq]
      rw [h2] at h1
      exact h1.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := hq (QuotientGroup.mk' X (f a))
    have h3 : (QuotientGroup.mk' X (f a)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, ← map_one (QuotientGroup.mk' X), ← map_one f]
      congr 2
      exact Subtype.ext ((isE27_subgroupOf hA hAH).1.2 a a.2)
    have := eq_one_of_pow_three_of_pow_two_pow h3 hk
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hEt : E ≤ Subgroup.centralizer ({t} : Set (H ⧸ CFSG.pCore 2 H)) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (a : H) * ⟨s, hsH⟩ = ⟨s, hsH⟩ * (a : H) := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hsA _ (Subgroup.mem_subgroupOf.mp a.2)
    change π (a : H) * π ⟨s, hsH⟩ = π ⟨s, hsH⟩ * π (a : H)
    rw [← map_mul, ← map_mul, hc]
  have hET : E ≤ Subgroup.normalizer (T : Set (H ⧸ CFSG.pCore 2 H)) := by
    rintro _ ⟨a, rfl⟩
    have haS : (a : H) ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have haN : ((a : H) : G) ∈ Subgroup.normalizer (S : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
          ⟨hAH (Subgroup.mem_subgroupOf.mp a.2), sec18Std_le h (Subgroup.mem_subgroupOf.mp a.2)⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp haN _)
    exact Subgroup.le_normalizer_map π ⟨_, haS, rfl⟩
  have hnoB : ∀ B : Subgroup (H ⧸ CFSG.pCore 2 H), B ≤ E → Nat.card B = 9 →
      ¬ perfectResidual (H ⧸ CFSG.pCore 2 H) ≤ Subgroup.centralizer (B : Set _) := by
    intro B hBE hB9 hcen
    set B' : Subgroup (A.subgroupOf H) := B.comap f
    set B₀ : Subgroup G := (B'.map (A.subgroupOf H).subtype).map H.subtype with hB₀
    have hB'card : Nat.card B' = 9 := by
      rw [← hB9]
      have : B'.map f = B := by
        rw [Subgroup.map_comap_eq, inf_eq_right.mpr hBE]
      rw [← this, Subgroup.card_map_of_injective hfinj]
    have hB₀A : B₀ ≤ A := by
      rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mp b.2
    have hB₀9 : Nat.card B₀ = 9 := by
      rw [hB₀, Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hB'card]
    apply perfectResidual_not_le_of_mem_scriptH h hH
    refine perfectResidual_le_of_commutator_le h hAH hB₀A hB₀9 fun l hl b hb => ?_
    obtain ⟨l', hl', rfl⟩ := hl
    obtain ⟨_, ⟨b', hb', rfl⟩, rfl⟩ := hb
    have hlπ : π l' ∈ perfectResidual (H ⧸ CFSG.pCore 2 H) :=
      map_perfectResidual_le π ⟨l', hl', rfl⟩
    have hbπ : π (b' : H) ∈ B := hb'
    have hc := Subgroup.mem_centralizer_iff.mp (hcen hlπ) _ hbπ
    have h1 : π (l' * (b' : H) * l'⁻¹ * (b' : H)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    have h2 := (hmemR _).mp h1
    simpa using h2
  have hO2 : CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := pCore_quotient_pCore_eq_bot 2
  obtain ⟨htt, hTeq⟩ := hK _ X t E hO2 hXn hX htX hXt ht2 hEX hEab hE27 hEt hnoB
  have hTt := hTeq T hT2 hET htT
  have hSeq : S = Subgroup.zpowers s ⊔ R := by
    refine le_antisymm (fun x hx => ?_) (sup_le (Subgroup.zpowers_le.mpr hsS) hRS)
    have hxT : π ⟨x, hSH hx⟩ ∈ T := ⟨⟨x, hSH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hTt] at hxT
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxT
    have h1 : π ((⟨s, hsH⟩ : H) ^ k)⁻¹ * π ⟨x, hSH hx⟩ = 1 := by
      rw [map_inv, map_zpow, ← ht, hk, inv_mul_cancel]
    rw [← map_mul, hmemR] at h1
    have h2 : x = s ^ k * ((((⟨s, hsH⟩ : H) ^ k)⁻¹ * ⟨x, hSH hx⟩ : H) : G) := by
      simp
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers s k))
      (Subgroup.mem_sup_right h1)
  refine ⟨hSeq, ?_⟩
  have ht1 : t ≠ 1 := fun h1 => htX (h1 ▸ X.one_mem)
  have hTcard : Nat.card T = 2 := by
    rw [hTt, Nat.card_zpowers]
    exact orderOf_eq_prime htt ht1
  set g : S.subgroupOf H →* H ⧸ CFSG.pCore 2 H := π.comp (S.subgroupOf H).subtype with hg
  have hgrange : g.range = T := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hgker : Nat.card g.ker = Nat.card R := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(((x : S.subgroupOf H) : H) : G),
          (hmemR ((x : S.subgroupOf H) : H)).mp (MonoidHom.mem_ker.mp x.2)⟩
        invFun := fun r => ⟨⟨⟨r, (CFSG.LieType.BorelTits.pCoreOf_le 2 H) r.2⟩,
            Subgroup.mem_subgroupOf.mpr (hRS r.2)⟩,
          MonoidHom.mem_ker.mpr ((hmemR _).mpr r.2)⟩
        left_inv := fun x => rfl
        right_inv := fun r => rfl }
  have hcardS : Nat.card S = 2 * Nat.card R := by
    have h1 := Subgroup.card_mul_index g.ker
    rw [Subgroup.index_ker, hgrange, hTcard, hgker] at h1
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, ← h1, mul_comm]
  have h2 := Subgroup.relIndex_mul_card R S
  rw [inf_eq_left.mpr hRS, hcardS] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h2, mul_comm])

theorem rank3II_18_1_2_of (h444 : Sec4.Item4_44_2) (hK : KFacts.KS18OuterInvolution) :
    Item181_2 := by
  intro G _ _ A M h H hH
  obtain ⟨s, hs⟩ := exists_concl4442_of h444 h hH
  exact ⟨s, hs, pCoreOf_inf_eq_of_concl4442 hK h hH hs⟩

end CFSG.RankThree.PartTwo.Sec18
