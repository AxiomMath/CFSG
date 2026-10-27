module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Inner

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem three_not_dvd_index {n ε : ℕ} (hε : ε = 1 ∨ ε = 2) (hn : Odd n) :
    ¬ 3 ∣ ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε := by
  have h2 : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hn
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h1 : ((2 ^ n) ^ 2 + 2 ^ n + 1) % 3 = 1 := by
    simp [Nat.add_mod, Nat.pow_mod, h2]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, h1]
  rcases hε with rfl | rfl <;> norm_num

private theorem relIndex_eq_relIndex_inf_of_sup {L T N : Subgroup G} (hLN : L ≤ N)
    (hNn : N ≤ Subgroup.normalizer (L : Set G)) (hTN : T ≤ N) (hsup : L ⊔ T = N) :
    T.relIndex N = (L ⊓ T).relIndex L := by
  have hL' : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNn
  have key := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (L.subgroupOf N)
    (T.subgroupOf N)
  have htop : L.subgroupOf N ⊔ T.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLN hTN, hsup, Subgroup.subgroupOf_self]
  rw [htop, Subgroup.relIndex_top_right] at key
  calc T.relIndex N = (T.subgroupOf N).index := rfl
    _ = (T.subgroupOf N).relIndex (L.subgroupOf N) := key
    _ = T.relIndex L := Subgroup.relIndex_subgroupOf hLN
    _ = (L ⊓ T).relIndex L := (Subgroup.inf_relIndex_left L T).symm

private theorem relIndex_eq_of_card_eq {H H' K : Subgroup G} (hH : H ≤ K) (hH' : H' ≤ K)
    (hc : Nat.card H = Nat.card H') : H'.relIndex K = H.relIndex K := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  have h2 := Subgroup.relIndex_mul_card (H := H') (K := K)
  rw [inf_eq_left.mpr hH] at h1
  rw [inf_eq_left.mpr hH'] at h2
  have h3 : H'.relIndex K * Nat.card H' = H.relIndex K * Nat.card H' := by
    rw [h2, ← hc, h1]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3

private theorem isSylowOf_three_N (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    {P : Subgroup G} (hP : IsSylowOf 3 P (M ⊓ N)) : IsSylowOf 3 P N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPMN, hP3, hPnd⟩ := isSylowOf_iff.mp hP
  have hsup : L ⊔ (M ⊓ N) = N := by
    rw [inf_comm]
    exact hF.sup_inf_eq
  have hrel : (M ⊓ N).relIndex N = (L ⊓ (M ⊓ N)).relIndex L :=
    relIndex_eq_relIndex_inf_of_sup h.L_le_N hF.normal inf_le_right hsup
  have hBLT : A ⊓ L ≤ L ⊓ (M ⊓ N) :=
    le_inf inf_le_right (le_inf (inf_le_left.trans h.le_M) (inf_le_left.trans h.le_N))
  have hBnd : ¬ 3 ∣ (L ⊓ (M ⊓ N)).relIndex L := by
    obtain ⟨-, -, hB⟩ := isSylowOf_iff.mp hF.sylow
    rw [← Subgroup.relIndex_mul_relIndex (A ⊓ L) (L ⊓ (M ⊓ N)) L hBLT inf_le_left] at hB
    exact fun hd => hB (dvd_mul_of_dvd_right hd _)
  refine isSylowOf_iff.mpr ⟨hPMN.trans inf_le_right, hP3, fun hd => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P (M ⊓ N) N hPMN inf_le_right, hrel] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h1 | h1
  · exact hPnd h1
  · exact hBnd h1

theorem item1923_six_sylow (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    {n ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hidx : (M ⊓ N).relIndex M = ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε)
    (hn : Odd n) {P : Subgroup G} (hP : IsSylowOf 3 P (M ⊓ N)) (hAP : A ≤ P) :
    IsSylowOf 3 P M ∧ IsSylowOf 3 P N ∧ Sec18.omegaOneThree P = A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPMN, hP3, hPnd⟩ := isSylowOf_iff.mp hP
  have hPM : IsSylowOf 3 P M := by
    refine isSylowOf_iff.mpr ⟨hPMN.trans inf_le_left, hP3, fun hd => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P (M ⊓ N) M hPMN inf_le_left] at hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h1 | h1
    · exact hPnd h1
    · rw [hidx] at h1
      exact three_not_dvd_index hε hn h1
  have hPN : IsSylowOf 3 P N := isSylowOf_three_N h hF hP
  exact ⟨hPM, hPN, hF.omega P hPN hAP⟩

private theorem center_eq_bot_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [hY, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [h1, map_one])

private theorem center_projSL_eq_bot (n : ℕ) :
    Subgroup.center (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) = ⊥ :=
  center_eq_bot_of_mulEquiv
    (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
    Sec3.Sims321.center_projectiveSL_eq_bot

private theorem mem_pCore_iff {K : Subgroup G} {x : G} (hx : x ∈ K) :
    (⟨x, hx⟩ : K) ∈ CFSG.pCore 2 K ↔ x ∈ CFSG.Open.pCoreOf 2 K := by
  unfold CFSG.Open.pCoreOf
  constructor
  · intro hmem
    exact Subgroup.mem_map_of_mem K.subtype hmem
  · intro hmem
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hyeq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← hyeq]
    exact hy

private theorem conj_mem_pCoreOf {K : Subgroup G} {g w : G} (hg : g ∈ K)
    (hw : w ∈ CFSG.Open.pCoreOf 2 K) : g * w * g⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hg) w).mp hw

private theorem pCoreOf_le_of_normalizes {K M : Subgroup G} (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM)
    (hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

private theorem mem_normalizer_inf {S T : Subgroup G} {g : G}
    (hS : g ∈ Subgroup.normalizer (S : Set G)) (hT : g ∈ Subgroup.normalizer (T : Set G)) :
    g ∈ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hS hT ⊢
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  rw [hS x, hT x]

private theorem inf_pCoreOf_eq {K M : Subgroup G} (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ CFSG.Open.pCoreOf 2 M = CFSG.Open.pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hnorm : K ≤ Subgroup.normalizer ((K ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
      fun k hk => mem_normalizer_inf (Subgroup.le_normalizer hk)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk))
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_right
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) (pCoreOf_le_of_normalizes hKM hMK)

private theorem comm_mem_pCoreOf_iff {K M : Subgroup G} (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) {m k : G} (hm : m ∈ M) (hk : k ∈ K) :
    m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M ↔ m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  constructor
  · intro h
    have hK : m * k * m⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMK hm) k).mp hk) (K.inv_mem hk)
    rw [← inf_pCoreOf_eq hKM hMK]
    exact ⟨hK, h⟩
  · intro h
    exact pCoreOf_le_of_normalizes hKM hMK h

private theorem mem_pCoreOf_of_comm {K : Subgroup G}
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) {x : G} (hxK : x ∈ K)
    (hcomm : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    x ∈ CFSG.Open.pCoreOf 2 K := by
  have hy : (QuotientGroup.mk (⟨x, hxK⟩ : K) : K ⧸ CFSG.pCore 2 K) ∈
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hk : (g' : G) ∈ K := g'.2
    have h0 : x * (g' : G)⁻¹ * x⁻¹ * ((g' : G)⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      hcomm _ (K.inv_mem hk)
    have hw : x⁻¹ * (g' : G)⁻¹ * x * (g' : G) ∈ CFSG.Open.pCoreOf 2 K := by
      have := conj_mem_pCoreOf (K.inv_mem hxK) ((CFSG.Open.pCoreOf 2 K).inv_mem h0)
      convert this using 1
      group
    have hz : x⁻¹ * (g' : G)⁻¹ * x * (g' : G) ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hxK) (K.inv_mem hk)) hxK) hk
    have key : (g' * (⟨x, hxK⟩ : K))⁻¹ * ((⟨x, hxK⟩ : K) * g') =
        (⟨x⁻¹ * (g' : G)⁻¹ * x * (g' : G), hz⟩ : K) :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [key]
    exact (mem_pCore_iff hz).mpr hw
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hy
  exact (mem_pCore_iff hxK).mp hy

private noncomputable def barM (K M : Subgroup G) (hKM : M ≤ Subgroup.normalizer (K : Set G)) :
    M →* MulAut (K ⧸ CFSG.pCore 2 K) :=
  (Sec3.Sims321.barAut K).comp (Subgroup.inclusion hKM)

private theorem mem_sup_of_normalizes {S T : Subgroup G}
    (hT : ∀ t ∈ T, ∀ s ∈ S, t * s * t⁻¹ ∈ S) {x : G} (hx : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, s * t = x := by
  let U : Subgroup G :=
    { carrier := {x | ∃ s ∈ S, ∃ t ∈ T, s * t = x}
      mul_mem' := by
        rintro _ _ ⟨s₁, hs₁, t₁, ht₁, rfl⟩ ⟨s₂, hs₂, t₂, ht₂, rfl⟩
        exact ⟨s₁ * (t₁ * s₂ * t₁⁻¹), S.mul_mem hs₁ (hT t₁ ht₁ s₂ hs₂), t₁ * t₂,
          T.mul_mem ht₁ ht₂, by group⟩
      one_mem' := ⟨1, S.one_mem, 1, T.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨s, hs, t, ht, rfl⟩
        exact ⟨t⁻¹ * s⁻¹ * t⁻¹⁻¹, hT t⁻¹ (T.inv_mem ht) s⁻¹ (S.inv_mem hs), t⁻¹,
          T.inv_mem ht, by group⟩ }
  have hSU : S ≤ U := fun s hs => ⟨s, hs, 1, T.one_mem, by simp⟩
  have hTU : T ≤ U := fun t ht => ⟨1, S.one_mem, t, ht, by simp⟩
  obtain ⟨s, hs, t, ht, hst⟩ := (sup_le hSU hTU) hx
  exact ⟨s, hs, t, ht, hst⟩

private theorem barAut_eq_conj_of_mem {K : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (K : Set G)) (hmK : m ∈ K) :
    Sec3.Sims321.barAut K ⟨m, hm⟩ = MulAut.conj ((⟨m, hmK⟩ : K) : K ⧸ CFSG.pCore 2 K) := by
  ext y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Sec3.Sims321.barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

private theorem barM_eq_conj {K M : Subgroup G} (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hKM' : K ≤ M) (l : K) :
    barM K M hKM ⟨(l : G), hKM' l.2⟩ = MulAut.conj ((l : K) : K ⧸ CFSG.pCore 2 K) :=
  barAut_eq_conj_of_mem (hKM (hKM' l.2)) l.2

private theorem barM_mk {K M : Subgroup G} (hKM : M ≤ Subgroup.normalizer (K : Set G)) {m : G}
    (hm : m ∈ M) (l : K) :
    barM K M hKM ⟨m, hm⟩ (QuotientGroup.mk l) =
      QuotientGroup.mk ⟨m * l * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hKM hm) (l : G)).mp l.2⟩ :=
  rfl

private theorem barM_eq_one_iff {K M : Subgroup G} (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hKM' : K ≤ M) {m : G} (hm : m ∈ M) :
    barM K M hKM ⟨m, hm⟩ = 1 ↔ ∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  constructor
  · intro h k hk
    have hy : barM K M hKM ⟨m, hm⟩ (QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)) =
        QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K) := by
      rw [h]; rfl
    rw [barM_mk] at hy
    have h2 := QuotientGroup.eq.mp hy
    have hz : m * k * m⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKM hm) k).mp hk) (K.inv_mem hk)
    have key : (⟨m * k⁻¹ * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hKM hm) k⁻¹).mp
        (K.inv_mem hk)⟩ : K)⁻¹ * (⟨k⁻¹, K.inv_mem hk⟩ : K) =
        (⟨m * k * m⁻¹ * k⁻¹, hz⟩ : K) :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [key] at h2
    exact (mem_pCore_iff hz).mp h2
  · intro h
    ext y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.one_apply, barM_mk]
    apply QuotientGroup.eq.mpr
    have hl := h (l⁻¹ : G) (K.inv_mem l.2)
    have hz : m * (l : G)⁻¹ * m⁻¹ * ((l : G)⁻¹)⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKM hm) (l : G)⁻¹).mp (K.inv_mem l.2))
        (K.inv_mem (K.inv_mem l.2))
    have key : (⟨m * (l : G) * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hKM hm) (l : G)).mp l.2⟩ : K)⁻¹
        * l = (⟨m * (l : G)⁻¹ * m⁻¹ * ((l : G)⁻¹)⁻¹, hz⟩ : K) :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [key]
    exact (mem_pCore_iff hz).mpr hl

private theorem barM_mem_inner_of_mem_KC {K C M : Subgroup G}
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) (hKM' : K ≤ M) (hCM : C ≤ M)
    (hCone : ∀ m (hm : m ∈ M), m ∈ C → barM K M hKM ⟨m, hm⟩ = 1)
    {m : G} (hm : m ∈ M) (hmKC : m ∈ K ⊔ C) :
    barM K M hKM ⟨m, hm⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) := by
  obtain ⟨s, hs, t, ht, rfl⟩ := mem_sup_of_normalizes (S := K) (T := C)
    (fun t ht s hs => (Subgroup.mem_normalizer_iff.mp (hKM (hCM ht)) s).mp hs) hmKC
  have hsM : s ∈ M := hKM' hs
  have htM : t ∈ M := hCM ht
  have hsplit : (⟨s * t, hm⟩ : M) = ⟨s, hsM⟩ * ⟨t, htM⟩ := rfl
  rw [hsplit, map_mul, hCone t htM ht, mul_one]
  have hsconj : barM K M hKM ⟨s, hsM⟩ = MulAut.conj ((⟨s, hs⟩ : K) : K ⧸ CFSG.pCore 2 K) :=
    barAut_eq_conj_of_mem (hKM hsM) hs
  rw [hsconj]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem mem_KC_of_barM_mem_inner {K C M : Subgroup G}
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) (hKM' : K ≤ M)
    (hCiff : ∀ m (hm : m ∈ M), m ∈ C ↔ barM K M hKM ⟨m, hm⟩ = 1)
    {m : G} (hm : m ∈ M) (hmi : barM K M hKM ⟨m, hm⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K)) :
    m ∈ K ⊔ C := by
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hmi
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective t
  have hl : barM K M hKM ⟨(l : G), hKM' l.2⟩ = barM K M hKM ⟨m, hm⟩ := by
    rw [barM_eq_conj hKM hKM' l, ht]
  have hM' : (l : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (hKM' l.2)) hm
  have hlm : (l : G)⁻¹ * m ∈ C := by
    rw [hCiff _ hM']
    have hsplit : (⟨(l : G)⁻¹ * m, hM'⟩ : M) = (⟨(l : G), hKM' l.2⟩ : M)⁻¹ * ⟨m, hm⟩ := rfl
    rw [hsplit, map_mul, map_inv, hl, inv_mul_cancel]
  have := Subgroup.mul_mem_sup l.2 hlm
  simpa only [mul_inv_cancel_left] using this

private theorem eq_one_of_mem_two_three {P Q : Subgroup G} (hP : IsPGroup 3 P)
    (hQ : IsPGroup 2 Q) {x : G} (hxP : x ∈ P) (hxQ : x ∈ Q) : x = 1 := by
  obtain ⟨a, ha⟩ := hP ⟨x, hxP⟩
  obtain ⟨b, hb⟩ := hQ ⟨x, hxQ⟩
  have h1 : x ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have h2 : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hd : orderOf x ∣ Nat.gcd (3 ^ a) (2 ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.gcd (3 ^ a) (2 ^ b) = 1 := Nat.Coprime.pow _ _ (by norm_num)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

private theorem exists_sylow_three_ge {D M : Subgroup G} (hD : IsPGroup 3 D) (hDM : D ≤ M) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ D ≤ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDM' : IsPGroup 3 (D.subgroupOf M) := hD.comap_subtype
  obtain ⟨Q, hQ⟩ := hDM'.exists_le_sylow
  refine ⟨(Q : Subgroup M).map M.subtype, ⟨Q, rfl⟩, ?_⟩
  intro d hd
  have hdM : (⟨d, hDM hd⟩ : M) ∈ D.subgroupOf M := hd
  have hQd : (⟨d, hDM hd⟩ : M) ∈ (Q : Subgroup M) := hQ hdM
  exact ⟨⟨d, hDM hd⟩, hQd, rfl⟩

private theorem isCyclic_inf_of_pRank {K Q : Subgroup G}
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤ 1)
    (hQK : Q ≤ K) (hQ3 : IsPGroup 3 Q) (hQO : Q ⊓ CFSG.Open.pCoreOf 2 K = ⊥) :
    IsCyclic ↥Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let g : Q →* (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hQK)
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion hQK x ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : G) ∈ CFSG.Open.pCoreOf 2 K := (mem_pCore_iff (hQK x.2)).mp h1
    have h3 : (x : G) ∈ Q ⊓ CFSG.Open.pCoreOf 2 K := ⟨x.2, h2⟩
    rw [hQO, Subgroup.mem_bot] at h3
    exact Subtype.ext (by simpa using h3)
  have hRpg : IsPGroup 3 g.range := hQ3.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  haveI : IsCyclic g.range := CFSG.RankThree.PartTwo.Sec20.Res5.isCyclic_of_pRank_le_one hr hRpg
  exact isCyclic_of_surjective (MonoidHom.ofInjective hginj).symm (MulEquiv.surjective _)

private theorem relIndex_sup_eq_of_normalizes {K C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (K : Set G)) : K.relIndex (K ⊔ C) = K.relIndex C := by
  have hX : K ⊔ C ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hC
  have hKX : K ≤ K ⊔ C := le_sup_left
  have hCX : C ≤ K ⊔ C := le_sup_right
  have hK' : (K.subgroupOf (K ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hX
  have key := Subgroup.relIndex_sup_right (C.subgroupOf (K ⊔ C)) (K.subgroupOf (K ⊔ C))
  have htop : C.subgroupOf (K ⊔ C) ⊔ K.subgroupOf (K ⊔ C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCX hKX, sup_comm, Subgroup.subgroupOf_self]
  rw [htop, Subgroup.relIndex_top_right] at key
  calc K.relIndex (K ⊔ C) = (K.subgroupOf (K ⊔ C)).index := rfl
    _ = (K.subgroupOf (K ⊔ C)).relIndex (C.subgroupOf (K ⊔ C)) := key
    _ = K.relIndex C := Subgroup.relIndex_subgroupOf hCX

private theorem le_sup_of_three_group {K C B Y : Subgroup G}
    (hCN : C ≤ Subgroup.normalizer (K : Set G)) (hKC2 : IsPGroup 2 (K ⊓ C : Subgroup G))
    (hBC : CFSG.ABGLocalTools.IsSylowOf 3 B C) (hB9 : Nat.card B = 9) (hBK : K ⊓ B = ⊥)
    (hY3 : IsPGroup 3 Y) (hYX : Y ≤ K ⊔ C) (hBY : B ≤ Y) : Y ≤ K ⊔ B := by
  classical
  obtain ⟨hBC', -, h3B⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hBC
  have hXN : K ⊔ C ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hCN
  have he : K.relIndex (K ⊔ C) = K.relIndex C := relIndex_sup_eq_of_normalizes hCN
  have hm3 : ¬ 3 ∣ Nat.card (K ⊓ C : Subgroup G) := by
    obtain ⟨j, hj⟩ := hKC2.exists_card_dvd_pow
    intro h3
    have h32 : 3 ∣ 2 ^ j := h3.trans hj
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    norm_num at this
  have hmul1 : K.relIndex C * Nat.card (K ⊓ C : Subgroup G) = Nat.card C :=
    Subgroup.relIndex_mul_card (H := K) (K := C)
  have hmul2 : B.relIndex C * Nat.card B = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := B) (K := C)
    rwa [inf_eq_left.mpr hBC'] at this
  have hkey : K.relIndex C * Nat.card (K ⊓ C : Subgroup G) = B.relIndex C * 9 := by
    rw [hmul1, ← hmul2, hB9]
  have hcop : Nat.Coprime 9 (Nat.card (K ⊓ C : Subgroup G)) := by
    have h3m : Nat.Coprime 3 (Nat.card (K ⊓ C : Subgroup G)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    simpa using Nat.Coprime.pow_left 2 h3m
  have h9e : 9 ∣ K.relIndex C := by
    have h1 : 9 ∣ K.relIndex C * Nat.card (K ⊓ C : Subgroup G) := by
      rw [hkey]; exact Dvd.intro_left _ rfl
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop h1
  have h27 : ¬ 27 ∣ K.relIndex C := by
    intro h
    have h1 : 27 ∣ K.relIndex C * Nat.card (K ⊓ C : Subgroup G) := dvd_mul_of_dvd_left h _
    rw [hkey] at h1
    have h2 : 3 * 9 ∣ B.relIndex C * 9 := by norm_num; exact h1
    exact h3B (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2)
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := hYX.trans hXN
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBC'.trans hCN
  have hZW : K ⊔ B ≤ K ⊔ Y := sup_le le_sup_left (hBY.trans le_sup_right)
  have hWX : K ⊔ Y ≤ K ⊔ C := sup_le le_sup_left hYX
  have hWK : K.relIndex (K ⊔ Y) = K.relIndex Y := relIndex_sup_eq_of_normalizes hYN
  have hZK : K.relIndex (K ⊔ B) = 9 := by
    rw [relIndex_sup_eq_of_normalizes hBN]
    have := Subgroup.relIndex_mul_card (H := K) (K := B)
    rw [hBK, Subgroup.card_bot, mul_one, hB9] at this
    exact this
  obtain ⟨n₀, hn₀⟩ := hY3.exists_card_dvd_pow
  have hdivY : K.relIndex Y ∣ 3 ^ n₀ := by
    have h1 : K.relIndex Y * Nat.card (K ⊓ Y : Subgroup G) = Nat.card Y :=
      Subgroup.relIndex_mul_card (H := K) (K := Y)
    exact (Dvd.intro _ h1).trans hn₀
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdivY
  have hfac : K.relIndex (K ⊔ Y) = K.relIndex (K ⊔ B) * (K ⊔ B).relIndex (K ⊔ Y) :=
    (Subgroup.relIndex_mul_relIndex K (K ⊔ B) (K ⊔ Y) le_sup_left hZW).symm
  have hdE : K.relIndex (K ⊔ Y) ∣ K.relIndex C := by
    have h1 : K.relIndex (K ⊔ C) = K.relIndex (K ⊔ Y) * (K ⊔ Y).relIndex (K ⊔ C) :=
      (Subgroup.relIndex_mul_relIndex K (K ⊔ Y) (K ⊔ C) le_sup_left hWX).symm
    rw [he] at h1
    exact Dvd.intro _ h1.symm
  have hd : K.relIndex (K ⊔ Y) = 3 ^ i := hWK.trans hi
  have hi2 : i ≤ 2 := by
    by_contra hcon
    have hcon' : 3 ≤ i := by omega
    apply h27
    have h3i : 27 ∣ K.relIndex (K ⊔ Y) := by
      rw [hd]; exact (pow_dvd_pow 3 hcon' : 3 ^ 3 ∣ 3 ^ i)
    exact h3i.trans hdE
  have h9d : 9 ∣ K.relIndex (K ⊔ Y) := by
    rw [hfac, hZK]; exact dvd_mul_right 9 _
  have hi3 : 2 ≤ i := by
    have h9' : 3 ^ 2 ∣ 3 ^ i := by rw [← hd]; norm_num; exact h9d
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h9'
  have hd9 : K.relIndex (K ⊔ Y) = 9 := by
    rw [hd, show i = 2 by omega]; norm_num
  have hZW1 : (K ⊔ B).relIndex (K ⊔ Y) = 1 := by
    have h1 : K.relIndex (K ⊔ B) * (K ⊔ B).relIndex (K ⊔ Y) = 9 * 1 := by
      rw [← hfac, hd9, mul_one]
    rw [hZK] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  exact (le_sup_right : Y ≤ K ⊔ Y).trans (Subgroup.relIndex_eq_one.mp hZW1)

private theorem mem_zpowers_three {c s : G} (hc : orderOf c = 3) (hs : s ∈ Subgroup.zpowers c) :
    s = 1 ∨ s = c ∨ s = c⁻¹ := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hmod : c ^ i = c ^ (i % 3) := by
    have := zpow_mod_orderOf c i
    rw [hc] at this
    simpa using this.symm
  have h3 : c ^ 3 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · left
    rw [hmod, h, zpow_zero]
  · right
    left
    rw [hmod, h, zpow_one]
  · right
    right
    rw [hmod, h]
    have h2 : c ^ (2 : ℤ) * c = 1 := by
      rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
    exact eq_inv_of_mul_eq_one_left h2

private noncomputable def sectionKer (K M : Subgroup G)
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) : Subgroup G :=
  ((barM K M hKM).ker).map M.subtype

private theorem mem_sectionKer {K M : Subgroup G} (hKM : M ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ M) :
    x ∈ sectionKer K M hKM ↔ barM K M hKM ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyeq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← hyeq]
    exact MonoidHom.mem_ker.mp hy
  · intro h1
    exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr h1, rfl⟩

private theorem coe_sectionKer {K M : Subgroup G} (hKM' : K ≤ M)
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) :
    (sectionKer K M hKM : Set G) = sectionCentralizer M K (CFSG.Open.pCoreOf 2 M) := by
  ext x
  constructor
  · intro hx
    have hxM : x ∈ M := Subgroup.map_subtype_le _ hx
    refine ⟨hxM, fun k hk => ?_⟩
    have h1 := (mem_sectionKer hKM hxM).mp hx
    exact pCoreOf_le_of_normalizes hKM' hKM ((barM_eq_one_iff hKM hKM' hxM).mp h1 k hk)
  · rintro ⟨hxM, hx⟩
    rw [SetLike.mem_coe, mem_sectionKer hKM hxM, barM_eq_one_iff hKM hKM' hxM]
    intro k hk
    exact (comm_mem_pCoreOf_iff hKM' hKM hxM hk).mp (hx k hk)

private theorem isSylowOf_sectionKer_of_sylow {K M P B : Subgroup G} (hKM' : K ≤ M)
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) (hPM : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hPC : P ⊓ sectionKer K M hKM = B) (hBC : B ≤ sectionKer K M hKM) (hB3 : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) : CFSG.ABGLocalTools.IsSylowOf 3 B (sectionKer K M hKM) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hBR⟩ := exists_sylow_three_ge hB3 hBC
  have hRC : R ≤ sectionKer K M hKM := (CFSG.ABGLocalTools.isSylowOf_iff.mp hR).1
  have hRM : R ≤ M := hRC.trans (Subgroup.map_subtype_le _)
  obtain ⟨Q, hQ, hRQ⟩ := exists_sylow_three_ge (CFSG.ABGLocalTools.isSylowOf_iff.mp hR).2.1 hRM
  obtain ⟨g, hgM, hg⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPM hQ
  have hmap : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hPC]
    have hxM : x ∈ M := hRM hx
    have hgx : g⁻¹ * x * g ∈ P := by
      have := (hg x).mp (hRQ hx)
      simpa using this
    refine ⟨?_, ?_⟩
    · simpa using hgx
    · have hg' : g⁻¹ ∈ M := M.inv_mem hgM
      have hmem := (mem_sectionKer hKM (M.mul_mem (M.mul_mem hg' hxM) (M.inv_mem hg'))).mpr
        (by
          have hsplit : (⟨g⁻¹ * x * g⁻¹⁻¹, M.mul_mem (M.mul_mem hg' hxM) (M.inv_mem hg')⟩ : M) =
              (⟨g⁻¹, hg'⟩ : M) * ⟨x, hxM⟩ * (⟨g⁻¹, hg'⟩ : M)⁻¹ := rfl
          rw [hsplit, map_mul, map_mul, map_inv, (mem_sectionKer hKM hxM).mp (hRC hx), mul_one,
            mul_inv_cancel])
      simpa using hmem
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hcard : Nat.card R ≤ Nat.card B := by
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_le_of_le hmap
  have hBR_eq : B = R := Subgroup.eq_of_le_of_card_ge hBR hcard
  rw [hBR_eq]
  exact hR

theorem item1923_six_C (kf5 : KF5) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N) (hcK : c ∈ K) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    {P : Subgroup G} (hP : IsSylowOf 3 P (M ⊓ N)) (hAP : A ≤ P) (hPM : IsSylowOf 3 P M)
    (hΩ : Sec18.omegaOneThree P = A) :
    ∃ C : Subgroup G, (C : Set G) = sectionCentralizer M K (CFSG.Open.pCoreOf 2 M) ∧
      P ⊓ C = A ⊓ L ∧ IsSylowOf 3 (A ⊓ L) C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM' : K ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hLN : L ≤ N := h.L_le_N
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hF.normal
  have hAM : A ≤ M := h.le_M
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hcA : c ∈ A := by
    rw [hF.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hBA : A ⊓ L ≤ A := inf_le_left
  have hBP : A ⊓ L ≤ P := inf_le_left.trans hAP
  have hPN : P ≤ N := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).1.trans inf_le_right
  have hPM3 : IsPGroup 3 P := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.1
  have hZK : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ := by
    obtain ⟨nK, -, ⟨φK⟩⟩ := hL3
    exact center_eq_bot_of_mulEquiv φK (center_projSL_eq_bot nK)
  obtain ⟨φL⟩ := h.quotient_iso
  have hZL : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φL (center_projSL_eq_bot 2)
  have hOKpg : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hBC0 : A ⊓ L ≤ sectionKer K M hKM := by
    intro b hb
    have hbM : b ∈ M := hAM (hBA hb)
    exact (mem_sectionKer hKM hbM).mpr
      ((barM_eq_one_iff hKM hKM' hbM).mpr (fun k hk => hone b hb k hk))
  have hcC0 : c ∉ sectionKer K M hKM := by
    intro hc
    have hcM : c ∈ M := hKM' hcK
    have hcOK : c ∈ CFSG.Open.pCoreOf 2 K := mem_pCoreOf_of_comm hZK hcK (fun k hk =>
      ((barM_eq_one_iff hKM hKM' hcM).mp ((mem_sectionKer hKM hcM).mp hc)) k hk)
    have hc1 : c = 1 := eq_one_of_mem_two_three hPM3 hOKpg (hAP hcA) hcOK
    have h3 := hF.orderOf_c
    rw [hc1, orderOf_one] at h3
    norm_num at h3
  have hK1 : ∀ x (hx : x ∈ P ⊓ sectionKer K M hKM),
      barM L N hNL ⟨x, hPN hx.1⟩ = 1 → x = 1 := by
    intro x hx h1
    by_contra hx1
    obtain ⟨N₀, hN₀⟩ := hPM3 ⟨x, hx.1⟩
    have hxN₀ : x ^ 3 ^ N₀ = 1 := by simpa using congrArg Subtype.val hN₀
    obtain ⟨a, -, ha⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hxN₀)
    have ha1 : a ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by rw [ha, pow_zero]))
    have hyord : orderOf (x ^ 3 ^ (a - 1)) = 3 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
        (by rw [ha]; exact pow_dvd_pow 3 (by omega)), ha, Nat.pow_div (by omega) (by norm_num),
        show a - (a - 1) = 1 by omega, pow_one]
    set y : G := x ^ 3 ^ (a - 1) with hy
    have hyP : y ∈ P := P.pow_mem hx.1 _
    have hyC : y ∈ sectionKer K M hKM := (sectionKer K M hKM).pow_mem hx.2 _
    have hy3 : y ^ 3 = 1 := by
      rw [← hyord]
      exact pow_orderOf_eq_one y
    have hyA : y ∈ A := by
      have hmem : y ∈ Sec18.omegaOneThree P := Subgroup.subset_closure ⟨hyP, hy3⟩
      rwa [hΩ] at hmem
    have hyN : y ∈ N := hPN hyP
    have h1y : barM L N hNL ⟨y, hyN⟩ = 1 := by
      have hs : (⟨y, hyN⟩ : N) = ⟨x, hPN hx.1⟩ ^ 3 ^ (a - 1) := rfl
      rw [hs, map_pow, h1, one_pow]
    have hyL : y ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) :=
      ⟨hyA, fun l hl => (barM_eq_one_iff hNL hLN hyN).mp h1y l hl⟩
    have hyz : y ∈ Subgroup.zpowers c := by
      rw [← SetLike.mem_coe, ← hF.centralizer_eq]
      exact hyL
    rcases mem_zpowers_three hF.orderOf_c hyz with h0 | h0 | h0
    · rw [h0, orderOf_one] at hyord
      norm_num at hyord
    · exact hcC0 (by rw [← h0]; exact hyC)
    · apply hcC0
      have hc' : c = y⁻¹ := by rw [h0, inv_inv]
      rw [hc']
      exact (sectionKer K M hKM).inv_mem hyC
  have hK2 : ∀ x ∈ P ⊓ sectionKer K M hKM, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨N₁, hN₁⟩ := hPM3 ⟨x, hx.1⟩
    have hxN₁ : x ^ 3 ^ N₁ = 1 := by simpa using congrArg Subtype.val hN₁
    have hρ : IsPGroup 3 (Subgroup.zpowers (barM L N hNL ⟨x, hPN hx.1⟩)) := by
      apply IsPGroup.of_card_dvd_pow (n := N₁)
      rw [Nat.card_zpowers]
      apply orderOf_dvd_of_pow_eq_one
      have hs : (⟨x, hPN hx.1⟩ : N) ^ 3 ^ N₁ = 1 := Subtype.ext (by simpa using hxN₁)
      rw [← map_pow, hs, map_one]
    have hkf := kf5 (L ⧸ CFSG.pCore 2 L) ⟨φL⟩ _ hρ
    have hx3 : x ^ 3 ∈ P ⊓ sectionKer K M hKM :=
      ⟨P.pow_mem hx.1 3, (sectionKer K M hKM).pow_mem hx.2 3⟩
    apply hK1 (x ^ 3) hx3
    have hs : (⟨x ^ 3, hPN hx3.1⟩ : N) = ⟨x, hPN hx.1⟩ ^ 3 := rfl
    rw [hs, map_pow]
    exact hkf
  have hK3 : ∀ x ∈ P ⊓ sectionKer K M hKM, x ∈ A ⊓ L := by
    intro x hx
    have hxA : x ∈ A := by
      have hmem : x ∈ Sec18.omegaOneThree P := Subgroup.subset_closure ⟨hx.1, hK2 x hx⟩
      rwa [hΩ] at hmem
    have hT : ∀ t ∈ A ⊓ L, ∀ s ∈ Subgroup.zpowers c, t * s * t⁻¹ ∈ Subgroup.zpowers c := by
      intro t ht s hs
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      have htc : Commute t c := hAab t (hBA ht) c hcA
      have : t * c ^ i * t⁻¹ = c ^ i := by
        rw [(htc.zpow_right i).eq]
        group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i
    have hAx : x ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by
      rw [← hF.eq_sup]
      exact hxA
    obtain ⟨s, hs, t, ht, hst⟩ := mem_sup_of_normalizes hT hAx
    have hsC : s ∈ sectionKer K M hKM := by
      have hsx : s = x * t⁻¹ := by
        rw [← hst]
        group
      rw [hsx]
      exact (sectionKer K M hKM).mul_mem hx.2 ((sectionKer K M hKM).inv_mem (hBC0 ht))
    rcases mem_zpowers_three hF.orderOf_c hs with h0 | h0 | h0
    · have hxt : x = t := by
        rw [← hst, h0, one_mul]
      rw [hxt]
      exact ht
    · exact absurd (by rw [← h0]; exact hsC) hcC0
    · exact absurd (by
        have hc' : c = s⁻¹ := by rw [h0, inv_inv]
        rw [hc']
        exact (sectionKer K M hKM).inv_mem hsC) hcC0
  have hPC : P ⊓ sectionKer K M hKM = A ⊓ L :=
    le_antisymm (fun x hx => hK3 x hx) (le_inf hBP hBC0)
  refine ⟨sectionKer K M hKM, coe_sectionKer hKM' hKM, hPC, ?_⟩
  exact isSylowOf_sectionKer_of_sylow hKM' hKM hPM hPC hBC0
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.1 hF.card

theorem item1923_six_BO2 (h : Hyp1921 G A M N L)
    (hET : partTwoE G ⊆ partTwoT G) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hC : ∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N)
    {P : Subgroup G} (hP : IsSylowOf 3 P (M ⊓ N)) (hAP : A ≤ P) {C : Subgroup G}
    (hCe : (C : Set G) = sectionCentralizer M K (CFSG.Open.pCoreOf 2 M))
    (hPC : P ⊓ C = A ⊓ L) (hCs : IsSylowOf 3 (A ⊓ L) C) :
    M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM' : K ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hF.normal
  have hAM : A ≤ M := h.le_M
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hBC : A ⊓ L ≤ C := by
    rw [← hPC]
    exact inf_le_right
  have hBP : A ⊓ L ≤ P := inf_le_left.trans hAP
  have hPM3 : IsPGroup 3 P := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.1
  have hPN : CFSG.ABGLocalTools.IsSylowOf 3 P N := isSylowOf_three_N h hF hP
  have hPL : P ⊓ L = A ⊓ L :=
    hF.sylow.eq_of_le (le_inf hBP hBL) inf_le_right hPM3.to_inf_left
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hF.sylow.isPGroup
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := hF.card
  have hBLrel : ¬ 3 ∣ (A ⊓ L).relIndex L :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.2
  have hBCrel : ¬ 3 ∣ (A ⊓ L).relIndex C := (CFSG.ABGLocalTools.isSylowOf_iff.mp hCs).2.2
  have hCmem : ∀ x, x ∈ C ↔ x ∈ M ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    fun x => by
      rw [← SetLike.mem_coe, hCe]
      exact Iff.rfl
  have hCM' : C ≤ M := fun x hx => ((hCmem x).mp hx).1
  have hCN : C ≤ N := fun x hx => hC x ((hCmem x).mp hx).1 ((hCmem x).mp hx).2
  have hCnormM : ∀ m ∈ M, ∀ x ∈ C, m * x * m⁻¹ ∈ C := by
    intro m hm x hx
    obtain ⟨hxM, hxK⟩ := (hCmem x).mp hx
    rw [hCmem]
    refine ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun k hk => ?_⟩
    have hk' : m⁻¹ * k * m⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKM (M.inv_mem hm)) k).mp hk
    have h1 := conj_mem_pCoreOf (K := M) hm (hxK _ hk')
    have hid : m * (x * (m⁻¹ * k * m⁻¹⁻¹) * x⁻¹ * (m⁻¹ * k * m⁻¹⁻¹)⁻¹) * m⁻¹ =
        m * x * m⁻¹ * k * (m * x * m⁻¹)⁻¹ * k⁻¹ := by
      group
    rw [hid] at h1
    exact h1
  have hCnorm : M ≤ Subgroup.normalizer (C : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hCnormM m hm x hx
    · intro hx
      have h1 := hCnormM m⁻¹ (M.inv_mem hm) _ hx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h1
  have hOnorm : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hQO : C ⊓ CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 M := by
    have hQ2 : IsPGroup 2 (C ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
    have hfwd : ∀ c ∈ C, ∀ q ∈ (C ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G),
        c * q * c⁻¹ ∈ (C ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G) := by
      intro c hc q hq
      obtain ⟨hqC, hqO⟩ := Subgroup.mem_inf.mp hq
      refine Subgroup.mem_inf.mpr ⟨C.mul_mem (C.mul_mem hc hqC) (C.inv_mem hc), ?_⟩
      have hcnorm : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hNL (hCN hc))
      exact (Subgroup.mem_normalizer_iff.mp hcnorm q).mp hqO
    have hCQ : C ≤ Subgroup.normalizer ((C ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        exact hfwd c hc q hq
      · intro hq
        have h1 := hfwd c⁻¹ (C.inv_mem hc) _ hq
        rwa [show c⁻¹ * (c * q * c⁻¹) * c⁻¹⁻¹ = q by group] at h1
    have h1 : C ⊓ CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 C :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCQ hQ2
    have h2 : CFSG.Open.pCoreOf 2 C ≤ CFSG.Open.pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 C).trans hCM')
        (hCnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C)
    exact h1.trans h2
  have hkey : ∀ x ∈ C, ∀ b ∈ A ⊓ L,
      x * b * x⁻¹ ∈ ((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
    intro x hx b hb
    have hxM : x ∈ M := hCM' hx
    have hxN : x ∈ N := hCN hx
    have hBxL : (A ⊓ L).map (MulAut.conj x).toMonoidHom ≤ L := by
      rintro _ ⟨b', hb', rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hNL hxN) b').mp hb'.2
    have hinjx : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
    have hcL : Nat.card ((A ⊓ L).map (MulAut.conj x).toMonoidHom : Subgroup G) =
        Nat.card (A ⊓ L : Subgroup G) :=
      Subgroup.card_map_of_injective hinjx
    have hBx : CFSG.ABGLocalTools.IsSylowOf 3 ((A ⊓ L).map (MulAut.conj x).toMonoidHom) L := by
      refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hBxL, hB3.map _, ?_⟩
      rw [relIndex_eq_of_card_eq hBL hBxL hcL.symm]
      exact hBLrel
    obtain ⟨y, hyL, hy⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hF.sylow hBx
    have hz : y⁻¹ * x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b'
      constructor
      · intro hb'
        have hmem : x * b' * x⁻¹ ∈ (A ⊓ L).map (MulAut.conj x).toMonoidHom := ⟨b', hb', rfl⟩
        have h1 := (hy (x * b' * x⁻¹)).mp hmem
        rwa [show y⁻¹ * x * b' * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * b' * x⁻¹) * y by group]
      · intro hb'
        have hu : x * b' * x⁻¹ ∈ (A ⊓ L).map (MulAut.conj x).toMonoidHom := by
          refine (hy (x * b' * x⁻¹)).mpr ?_
          rwa [show y⁻¹ * (x * b' * x⁻¹) * y = y⁻¹ * x * b' * (y⁻¹ * x)⁻¹ by group]
        obtain ⟨b'', hb'', hb''eq⟩ := Subgroup.mem_map.mp hu
        have hbb : b'' = b' := by
          simpa [MulAut.conj_apply] using hb''eq
        rwa [hbb] at hb''
    have hzM : y⁻¹ * x ∈ M := hF.normalizer_le_M hz
    have hyM : y ∈ M := by
      have hyx : y = x * (y⁻¹ * x)⁻¹ := by group
      rw [hyx]
      exact M.mul_mem hxM (M.inv_mem hzM)
    have hmap := Hyp1921.map_inf_eq_normalizer hET h hPN hAP
    rw [hPL] at hmap
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨y, hyL⟩ : L) ∈
        ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hyL, hyM⟩)
    rw [hmap] at hmem
    have hβB : y⁻¹ * (x * b * x⁻¹) * y ∈ A ⊓ L :=
      (hy (x * b * x⁻¹)).mp ⟨b, hb, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β, β = y⁻¹ * (x * b * x⁻¹) * y := ⟨_, rfl⟩
    rw [← hβ] at hβB
    have hxb : x * b * x⁻¹ = y * β * y⁻¹ := by
      rw [hβ]
      group
    have hβL : β ∈ L := hβB.2
    have hmemβ : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨β, hβL⟩ : L) ∈
        ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hβB)
    have hconj := (Subgroup.mem_normalizer_iff.mp hmem _).mp hmemβ
    obtain ⟨s, hs, hsβ⟩ := Subgroup.mem_map.mp hconj
    have hQmem : s⁻¹ * (⟨y, hyL⟩ * ⟨β, hβL⟩ * (⟨y, hyL⟩ : L)⁻¹) ∈ CFSG.pCore 2 ↥L := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) s =
          QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨y, hyL⟩ * ⟨β, hβL⟩ * (⟨y, hyL⟩ : L)⁻¹) := by
        rw [hsβ, map_mul, map_mul, map_inv]
      exact QuotientGroup.eq.mp h1
    have ho : ((s : L) : G)⁻¹ * (y * β * y⁻¹) ∈ CFSG.Open.pCoreOf 2 L := by
      have := (mem_pCore_iff (s⁻¹ * (⟨y, hyL⟩ * ⟨β, hβL⟩ * (⟨y, hyL⟩ : L)⁻¹)).2).mp hQmem
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hsA : ((s : L) : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hs
    have hoC : ((s : L) : G)⁻¹ * (y * β * y⁻¹) ∈ C := by
      rw [← hxb]
      exact C.mul_mem (C.inv_mem (hBC hsA)) (hCnormM x hxM b (hBC hb))
    have hoO : ((s : L) : G)⁻¹ * (y * β * y⁻¹) ∈ CFSG.Open.pCoreOf 2 M :=
      hQO (Subgroup.mem_inf.mpr ⟨hoC, ho⟩)
    have hfin := Subgroup.mul_mem_sup hsA hoO
    have heq : ((s : L) : G) * (((s : L) : G)⁻¹ * (y * β * y⁻¹)) = x * b * x⁻¹ := by
      rw [mul_inv_cancel_left, hxb]
    rw [heq] at hfin
    exact hfin
  have hstep : ∀ m ∈ M, ∀ b ∈ A ⊓ L,
      m * b * m⁻¹ ∈ ((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
    intro m hm b hb
    have hBm_le : (A ⊓ L).map (MulAut.conj m).toMonoidHom ≤ C := by
      rintro _ ⟨b', hb', rfl⟩
      exact hCnormM m hm b' (hBC hb')
    have hinjm : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
    have hc : Nat.card ((A ⊓ L).map (MulAut.conj m).toMonoidHom : Subgroup G) =
        Nat.card (A ⊓ L : Subgroup G) :=
      Subgroup.card_map_of_injective hinjm
    have hBm : CFSG.ABGLocalTools.IsSylowOf 3 ((A ⊓ L).map (MulAut.conj m).toMonoidHom) C := by
      refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hBm_le, hB3.map _, ?_⟩
      rw [relIndex_eq_of_card_eq hBC hBm_le hc.symm]
      exact hBCrel
    obtain ⟨k, hkC, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hCs hBm
    have hmem : m * b * m⁻¹ ∈ (A ⊓ L).map (MulAut.conj m).toMonoidHom := ⟨b, hb, rfl⟩
    have hβ : k⁻¹ * (m * b * m⁻¹) * k ∈ A ⊓ L := (hk _).mp hmem
    have hid : m * b * m⁻¹ = k * (k⁻¹ * (m * b * m⁻¹) * k) * k⁻¹ := by
      group
    rw [hid]
    exact hkey k hkC _ hβ
  have hTnorm : ∀ m ∈ M, ∀ t ∈ ((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G),
      m * t * m⁻¹ ∈ ((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
    intro m hm t ht
    have hT' : ∀ b ∈ A ⊓ L, ∀ o ∈ CFSG.Open.pCoreOf 2 M,
        b * o * b⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun b hb o ho =>
      (Subgroup.mem_normalizer_iff.mp (hOnorm (hAM (Subgroup.mem_inf.mp hb).1)) o).mp ho
    rw [sup_comm] at ht
    obtain ⟨o, ho, b, hb, hob⟩ := mem_sup_of_normalizes hT' ht
    have hmo : m * o * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (hOnorm hm) o).mp ho
    have hmb := hstep m hm b hb
    have hsplit : m * t * m⁻¹ = (m * o * m⁻¹) * (m * b * m⁻¹) := by
      rw [← hob]
      group
    rw [hsplit]
    exact ((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G).mul_mem (Subgroup.mem_sup_right hmo) hmb
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact hTnorm m hm t ht
  · intro ht
    have h1 := hTnorm m⁻¹ (M.inv_mem hm) _ ht
    rwa [show m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t by group] at h1

theorem item1923_six_abelian (kf5 : KF5) (kfl3aut3 : KFL3Aut3) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) (hK : K ∈ scriptJ M N) (hcK : c ∈ K)
    (hAK : A ⊓ K = Subgroup.zpowers c) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hBO2 : M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
    {P : Subgroup G} (hP : IsSylowOf 3 P (M ⊓ N)) (hAP : A ≤ P) (hPM : IsSylowOf 3 P M)
    (hΩ : Sec18.omegaOneThree P = A) {C : Subgroup G}
    (hCe : (C : Set G) = sectionCentralizer M K (CFSG.Open.pCoreOf 2 M))
    (hPC : P ⊓ C = A ⊓ L) (hCs : IsSylowOf 3 (A ⊓ L) C) :
    P = (P ⊓ K) ⊔ (A ⊓ L) ∧ Disjoint (P ⊓ K) (A ⊓ L) ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      IsCyclic ↥(P ⊓ K) ∧ (∀ x ∈ P ⊓ K, x ^ 3 = 1 → x ∈ Subgroup.zpowers c) ∧
      P ⊓ (K ⊔ C) = (P ⊓ K) ⊔ (A ⊓ L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM' : K ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hAM : A ≤ M := h.le_M
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hF.normal
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => h.isE27.1.2 x hx
  have hcA : c ∈ A := by
    rw [hF.eq_sup]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hBA : A ⊓ L ≤ A := inf_le_left
  have hBC : A ⊓ L ≤ C := by rw [← hPC]; exact inf_le_right
  have hBP : A ⊓ L ≤ P := inf_le_left.trans hAP
  have hPle : P ≤ M ⊓ N := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).1
  have hPM3 : IsPGroup 3 P := hPM.isPGroup
  have hPMle : P ≤ M := (CFSG.ABGLocalTools.isSylowOf_iff.mp hPM).1
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := hF.card
  have hAKC : A ≤ K ⊔ C := by
    rw [hF.eq_sup]
    exact sup_le ((Subgroup.zpowers_le.mpr hcK).trans le_sup_left) (hBC.trans le_sup_right)
  have hZK : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ := by
    obtain ⟨nK, -, ⟨φK⟩⟩ := hL3
    exact center_eq_bot_of_mulEquiv φK (center_projSL_eq_bot nK)
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤ 1 := by
    obtain ⟨nK, hnK, ⟨φK⟩⟩ := hL3
    exact CFSG.RankThree.PartTwo.Sec20.kFactL3OddThreeRank nK hnK _ ⟨φK⟩
  obtain ⟨φL⟩ := h.quotient_iso
  have hZL : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φL (center_projSL_eq_bot 2)
  have hOKpg : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hCmem : ∀ x, x ∈ C ↔ x ∈ M ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    fun x => by rw [← SetLike.mem_coe, hCe]; exact Iff.rfl
  have hCiff : ∀ m (hm : m ∈ M), m ∈ C ↔ barM K M hKM ⟨m, hm⟩ = 1 := by
    intro m hm
    rw [hCmem m, barM_eq_one_iff hKM hKM' hm]
    constructor
    · rintro ⟨-, h1⟩ k hk
      exact (comm_mem_pCoreOf_iff hKM' hKM hm hk).mp (h1 k hk)
    · intro h1
      exact ⟨hm, fun k hk => (comm_mem_pCoreOf_iff hKM' hKM hm hk).mpr (h1 k hk)⟩
  have hCM : C ≤ M := fun x hx => ((hCmem x).mp hx).1
  have hCN : C ≤ Subgroup.normalizer (K : Set G) := fun x hx => hKM (hCM hx)
  have hCone : ∀ m (hm : m ∈ M), m ∈ C → barM K M hKM ⟨m, hm⟩ = 1 :=
    fun m hm hmC => (hCiff m hm).mp hmC
  have hKC_OK : K ⊓ C ≤ CFSG.Open.pCoreOf 2 K := by
    rintro x ⟨hxK, hxC⟩
    exact mem_pCoreOf_of_comm hZK hxK (fun k hk =>
      (comm_mem_pCoreOf_iff hKM' hKM (hCM hxC) hk).mp (((hCmem x).mp hxC).2 k hk))
  have hKC2 : IsPGroup 2 (K ⊓ C : Subgroup G) := hOKpg.to_le hKC_OK
  have hBK : K ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxB⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_two_three hPM3 hOKpg (hBP hxB) (hKC_OK ⟨hxK, hBC hxB⟩)
  have hXP : P ≤ K ⊔ C := by
    intro x hxP
    by_contra hxX
    have hxM : x ∈ M := hPMle hxP
    have hex : ∃ j : ℕ, barM K M hKM ((⟨x, hxM⟩ : M) ^ 3 ^ j) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) := by
      obtain ⟨j, hj⟩ := hPM3 ⟨x, hxP⟩
      refine ⟨j, ?_⟩
      have h1 : (⟨x, hxM⟩ : M) ^ 3 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
      rw [h1, map_one]
      exact Subgroup.one_mem _
    have hfind := Nat.find_spec hex
    have hk₀0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hxX
      have h1 : barM K M hKM ((⟨x, hxM⟩ : M) ^ 3 ^ Nat.find hex) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) :=
        hfind
      rw [h0, pow_zero, pow_one] at h1
      exact mem_KC_of_barM_mem_inner hKM hKM' hCiff hxM h1
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk₀0
    have hjn : barM K M hKM ((⟨x, hxM⟩ : M) ^ 3 ^ j) ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) := by
      intro hmem
      have hlt : j < Nat.find hex := by omega
      exact Nat.find_min hex hlt hmem
    have hpow_eq : (3 : ℕ) ^ (j + 1) = 3 ^ Nat.find hex := by rw [hj]
    have hcube : barM K M hKM ((⟨x, hxM⟩ : M) ^ 3 ^ j) ^ 3 ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) := by
      have h1 : barM K M hKM ((⟨x, hxM⟩ : M) ^ 3 ^ j) ^ 3 =
          barM K M hKM ((⟨x, hxM⟩ : M) ^ 3 ^ Nat.find hex) := by
        rw [← map_pow, ← pow_mul, ← pow_succ, hpow_eq]
      rw [h1]
      exact hfind
    obtain ⟨t, β, hβ3, hαβ⟩ := kfl3aut3 (K ⧸ CFSG.pCore 2 K) hL3 _ hjn hcube
    obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : M,
        u₀ = (⟨(k₁ : G), hKM' k₁.2⟩ : M)⁻¹ * ((⟨x, hxM⟩ : M) ^ 3 ^ j) := ⟨_, rfl⟩
    have hu₀ : barM K M hKM u₀ = β := by
      rw [hu₀def, map_mul, map_inv, barM_eq_conj hKM hKM' k₁, hαβ, inv_mul_cancel_left]
    obtain ⟨e₃, r, hr3, hN⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u₀).ne' 3 (by norm_num)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hr3 (dvd_zero 3)
    obtain ⟨u, hudef⟩ : ∃ u : M, u = u₀ ^ r := ⟨_, rfl⟩
    have hordu : orderOf u = 3 ^ e₃ := by
      rw [hudef, orderOf_pow_of_dvd hr0 (Dvd.intro_left _ hN.symm), hN,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]
    have hγ : barM K M hKM u = β ^ r := by rw [hudef, map_pow, hu₀]
    set uG : G := (u : G) with huGdef
    have huG_ord : orderOf uG = 3 ^ e₃ := by rw [huGdef, Subgroup.orderOf_coe, hordu]
    have hu3 : IsPGroup 3 (Subgroup.zpowers uG) :=
      IsPGroup.of_card (n := e₃) (by rw [Nat.card_zpowers, huG_ord])
    have huM : Subgroup.zpowers uG ≤ M := Subgroup.zpowers_le.mpr u.2
    obtain ⟨R, hR, huR⟩ := exists_sylow_three_ge hu3 huM
    obtain ⟨k, hkM, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPM hR
    have hpP : k⁻¹ * uG * k ∈ P := (hk uG).mp (huR (Subgroup.mem_zpowers uG))
    have hpM : k⁻¹ * uG * k ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hkM) u.2) hkM
    set p : G := k⁻¹ * uG * k with hpdef
    have hbarp : barM K M hKM ⟨p, hpM⟩ =
        (barM K M hKM ⟨k, hkM⟩)⁻¹ * barM K M hKM u * barM K M hKM ⟨k, hkM⟩ := by
      have hsplit : (⟨p, hpM⟩ : M) = (⟨k, hkM⟩ : M)⁻¹ * u * ⟨k, hkM⟩ := rfl
      rw [hsplit, map_mul, map_mul, map_inv]
    have hβ1 : β ^ 3 = 1 := by
      rw [← hβ3]
      exact pow_orderOf_eq_one β
    have hβn : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (K ⧸ CFSG.pCore 2 K) := by
      intro hb
      apply hjn
      rw [hαβ]
      exact (CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K)).mul_mem
        (MonoidHom.mem_range.mpr ⟨_, rfl⟩) hb
    have hγn : β ^ r ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (K ⧸ CFSG.pCore 2 K) := by
      intro hg
      apply hβn
      have hmod : r * r % 3 = 1 := by
        have : r % 3 = 1 ∨ r % 3 = 2 := by omega
        rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
      have hrr : β ^ (r * r) = β := by
        rw [pow_eq_pow_mod (r * r) hβ1, hmod, pow_one]
      have hβeq : β = (β ^ r) ^ r := by rw [← pow_mul, hrr]
      rw [hβeq]
      exact (CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K)).pow_mem
        hg r
    have hγ3 : (β ^ r) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hβ1, one_pow]
    have hpout : barM K M hKM ⟨p, hpM⟩ ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ CFSG.pCore 2 K) := by
      intro hp
      apply hγn
      rw [← hγ]
      have hγeq : barM K M hKM u = barM K M hKM ⟨k, hkM⟩ * barM K M hKM ⟨p, hpM⟩ *
          (barM K M hKM ⟨k, hkM⟩)⁻¹ := by
        rw [hbarp]
        group
      rw [hγeq]
      exact (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
        (K ⧸ CFSG.pCore 2 K)).conj_mem _ hp _
    have hconjpow : ∀ a b : MulAut (K ⧸ CFSG.pCore 2 K), (a⁻¹ * b * a) ^ 3 = a⁻¹ * b ^ 3 * a := by
      intro a b
      have := conj_pow (a := a⁻¹) (b := b) (i := 3)
      rwa [inv_inv] at this
    have hpow3 : barM K M hKM ⟨p, hpM⟩ ^ 3 = 1 := by
      rw [hbarp, hconjpow, hγ, hγ3, mul_one, inv_mul_cancel]
    by_cases hp3 : p ^ 3 = 1
    ·
      have hpA : p ∈ A := by
        have hmem : p ∈ Sec18.omegaOneThree P := Subgroup.subset_closure ⟨hpP, hp3⟩
        rwa [hΩ] at hmem
      exact hpout (barM_mem_inner_of_mem_KC hKM hKM' hCM hCone hpM (hAKC hpA))
    ·
      have hbP : p ^ 3 ∈ P := P.pow_mem hpP 3
      have hbM : barM K M hKM ⟨p ^ 3, M.pow_mem hpM 3⟩ = 1 := by
        have hsplit : (⟨p ^ 3, M.pow_mem hpM 3⟩ : M) = ⟨p, hpM⟩ ^ 3 := rfl
        rw [hsplit, map_pow, hpow3]
      have hbC : p ^ 3 ∈ C := (hCiff _ (M.pow_mem hpM 3)).mpr hbM
      have hbB : p ^ 3 ∈ A ⊓ L := by
        rw [← hPC]
        exact ⟨hbP, hbC⟩
      have hpN : p ∈ Subgroup.normalizer (L : Set G) := hNL (hPle hpP).2
      have hρ3 : (Sec3.Sims321.barAut L ⟨p, hpN⟩) ^ 3 =
          MulAut.conj ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) := by
        rw [← map_pow]
        exact barAut_eq_conj_of_mem (hNL (hPle hbP).2) hbB.2
      have hρ1 : MulAut.conj ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) ≠ 1 := by
        intro h1
        have hcen : ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) ∈
            Subgroup.center (L ⧸ CFSG.pCore 2 L) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hg := congrArg (fun f : MulAut (L ⧸ CFSG.pCore 2 L) => f g) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at hg
          calc g * ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L)
              = ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) * g *
                  ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L)⁻¹ *
                  ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) := by rw [hg]
            _ = ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) * g := by group
        rw [hZL, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
        have hpc : p ^ 3 ∈ CFSG.Open.pCoreOf 2 L := (mem_pCore_iff hbB.2).mp hcen
        exact hp3 (eq_one_of_mem_two_three hPM3 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
          hbP hpc)
      have hρ9 : (Sec3.Sims321.barAut L ⟨p, hpN⟩) ^ 9 = 1 := by
        have h9 : (Sec3.Sims321.barAut L ⟨p, hpN⟩) ^ 9 =
            ((Sec3.Sims321.barAut L ⟨p, hpN⟩) ^ 3) ^ 3 := by rw [← pow_mul]
        have hz3 : ((⟨p ^ 3, hbB.2⟩ : L) : L ⧸ CFSG.pCore 2 L) ^ 3 = 1 := by
          have h3 : (⟨p ^ 3, hbB.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hA3 _ hbB.1)
          rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
        rw [h9, hρ3, ← map_pow, hz3, map_one]
      have hρpg : IsPGroup 3 (Subgroup.zpowers (Sec3.Sims321.barAut L ⟨p, hpN⟩)) := by
        apply IsPGroup.of_card_dvd_pow (n := 2)
        rw [Nat.card_zpowers]
        simpa using orderOf_dvd_of_pow_eq_one hρ9
      have hkf := kf5 (L ⧸ CFSG.pCore 2 L) ⟨φL⟩ _ hρpg
      exact hρ1 (hρ3.symm.trans hkf)
  have hPBK : P ≤ K ⊔ (A ⊓ L) :=
    le_sup_of_three_group hCN hKC2 hCs hB9 hBK hPM3 hXP hBP
  have hT : ∀ t ∈ A ⊓ L, ∀ s ∈ K, t * s * t⁻¹ ∈ K := fun t ht s hs =>
    (Subgroup.mem_normalizer_iff.mp (hKM (hAM (hBA ht))) s).mp hs
  have hdec : P = (P ⊓ K) ⊔ (A ⊓ L) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨s, hs, t, ht, hst⟩ := mem_sup_of_normalizes hT (hPBK hx)
      have hsP : s ∈ P := by
        have hs' : s = x * t⁻¹ := by
          rw [← hst]
          group
        rw [hs']
        exact P.mul_mem hx (P.inv_mem (hBP ht))
      rw [← hst]
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hsP, hs⟩) ht
    · exact sup_le inf_le_left hBP
  have hdisj : Disjoint (P ⊓ K) (A ⊓ L) := by
    rw [Subgroup.disjoint_def]
    intro x hx hxB
    exact eq_one_of_mem_two_three hPM3 hOKpg hx.1 (hKC_OK ⟨hx.2, hBC hxB⟩)
  have hBQ : ∀ b ∈ A ⊓ L, ∀ q ∈ P ⊓ K, b * q = q * b := by
    intro b hb q hq
    have hbM : b ∈ M := hAM (hBA hb)
    have hcomm : b * q * b⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (comm_mem_pCoreOf_iff hKM' hKM hbM hq.2).mp (((hCmem b).mp (hBC hb)).2 q hq.2)
    have hPc : b * q * b⁻¹ * q⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (hBP hb) hq.1) (P.inv_mem (hBP hb))) (P.inv_mem hq.1)
    have h1 : b * q * b⁻¹ * q⁻¹ = 1 := eq_one_of_mem_two_three hPM3 hOKpg hPc hcomm
    calc b * q = (b * q * b⁻¹ * q⁻¹) * (q * b) := by group
      _ = q * b := by rw [h1, one_mul]
  have hQO : (P ⊓ K) ⊓ CFSG.Open.pCoreOf 2 K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxPK, hxO⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_two_three hPM3 hOKpg hxPK.1 hxO
  have hcyc : IsCyclic ↥(P ⊓ K) :=
    isCyclic_inf_of_pRank hr inf_le_right hPM3.to_inf_left hQO
  have hQcomm : ∀ x ∈ P ⊓ K, ∀ y ∈ P ⊓ K, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := ↥(P ⊓ K))).is_comm.comm
      (⟨x, hx⟩ : ↥(P ⊓ K)) ⟨y, hy⟩)
  have hPabel : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ (P ⊓ K) ⊔ (A ⊓ L) := by
      rw [← hdec]
      exact hx
    have hy' : y ∈ (P ⊓ K) ⊔ (A ⊓ L) := by
      rw [← hdec]
      exact hy
    have hT' : ∀ t ∈ A ⊓ L, ∀ s ∈ P ⊓ K, t * s * t⁻¹ ∈ P ⊓ K := fun t ht s hs =>
      Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem (hBP ht) hs.1) (P.inv_mem (hBP ht)),
        hT t ht s hs.2⟩
    obtain ⟨q₁, hq₁, t₁, ht₁, rfl⟩ := mem_sup_of_normalizes hT' hx'
    obtain ⟨q₂, hq₂, t₂, ht₂, rfl⟩ := mem_sup_of_normalizes hT' hy'
    have e1 : t₁ * q₂ = q₂ * t₁ := hBQ t₁ ht₁ q₂ hq₂
    have e2 : t₂ * q₁ = q₁ * t₂ := hBQ t₂ ht₂ q₁ hq₁
    have e3 : t₁ * t₂ = t₂ * t₁ := hAab t₁ (hBA ht₁) t₂ (hBA ht₂)
    have e4 : q₁ * q₂ = q₂ * q₁ := hQcomm q₁ hq₁ q₂ hq₂
    calc q₁ * t₁ * (q₂ * t₂) = q₁ * (t₁ * q₂) * t₂ := by group
      _ = q₁ * (q₂ * t₁) * t₂ := by rw [e1]
      _ = (q₁ * q₂) * (t₁ * t₂) := by group
      _ = (q₂ * q₁) * (t₂ * t₁) := by rw [e4, e3]
      _ = q₂ * (q₁ * t₂) * t₁ := by group
      _ = q₂ * (t₂ * q₁) * t₁ := by rw [e2]
      _ = q₂ * t₂ * (q₁ * t₁) := by group
  have hpow : ∀ x ∈ P ⊓ K, x ^ 3 = 1 → x ∈ Subgroup.zpowers c := by
    intro x hx hx3
    have hxΩ : x ∈ Sec18.omegaOneThree P := Subgroup.subset_closure ⟨hx.1, hx3⟩
    rw [hΩ] at hxΩ
    have hxA : x ∈ A ⊓ K := ⟨hxΩ, hx.2⟩
    rwa [hAK] at hxA
  have hXPeq : P ⊓ (K ⊔ C) = (P ⊓ K) ⊔ (A ⊓ L) := by
    rw [inf_eq_left.mpr hXP]
    exact hdec
  exact ⟨hdec, hdisj, hPabel, hcyc, hpow, hXPeq⟩

end CFSG.RankThree.PartTwo.Late
