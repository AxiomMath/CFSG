module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.LieType.Simplicity.Classical
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure312Nonquasi
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.DicksonA312
public import CFSG.Quasithin.H13.A7Coordinates
public import CFSG.Quasithin.Vol2.Ch1List

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

section Groups

variable {G : Type} [Group G]

theorem exists_surj_autOn {K V : Subgroup G} (hKV : K ≤ normalizer (V : Set G))
    {S : Subgroup (MulAut ↥V)} (hKS : autOn K V = S) :
    ∃ θ : ↥K →* ↥S, Function.Surjective θ ∧
      ∀ k : ↥K, θ k = 1 ↔ (k : G) ∈ centralizer (V : Set G) := by
  have hθ₀ : ∀ k : ↥K, A4.actionOn V K hKV k ∈ S := fun k =>
    hKS ▸ (A4.mem_autOn_iff hKV).2 ⟨k, rfl⟩
  refine ⟨(A4.actionOn V K hKV).codRestrict S hθ₀, ?_, fun k => ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := (A4.mem_autOn_iff hKV).1 (hKS.symm ▸ hs)
    exact ⟨k, Subtype.ext hk⟩
  · rw [← A4.actionOn_eq_one_iff hKV k]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h

theorem isSimpleGroup_of_isPSL_two {X : Type} [Group X] {p e : ℕ} (hX : IsPSL 2 p e X) :
    IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ hX).2

theorem card_statedProj_statedSL_two_pow {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    Nat.card (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2), hF]
  have h1 : 2 * (2 - 1) / 2 = 1 := by norm_num
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  rw [h1, pow_one, Finset.Icc_self, Finset.prod_singleton, hg, Nat.div_one]

theorem mul_sq_sub_one_ne_168 {q : ℕ} (hq : 2 ∣ q) : q * (q ^ 2 - 1) ≠ 168 := by
  intro h
  rcases Nat.lt_or_ge q 6 with h6 | h6
  · interval_cases q <;> omega
  · have h1 : 36 ≤ q ^ 2 := by nlinarith
    have h2 : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h6 (by omega)
    omega

theorem false_of_isPSL_two_two_of_surj {X S : Type} [Group X] [Group S] {n : ℕ}
    (hX : IsPSL 2 2 n X) (θ : X →* S) (hθ : Function.Surjective θ) (hS : Nat.card S = 168) :
    False := by
  have := isSimpleGroup_of_isPSL_two hX
  have hinj : Function.Injective θ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff θ).1 h
    · exfalso
      have h1 : ∀ s : S, s = 1 := fun s => by
        obtain ⟨x, rfl⟩ := hθ s
        exact (MonoidHom.mem_ker).1 (h ▸ mem_top x)
      have h2 : Nat.card S = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, inferInstance⟩
      omega
  have hcard : Nat.card X = 168 := by
    rw [← hS]
    exact Nat.card_congr (Equiv.ofBijective θ ⟨hinj, hθ⟩)
  obtain ⟨⟨-, hn, -⟩, F, hF, hFfin, hFc, ⟨ι⟩⟩ := hX
  rw [Nat.card_congr ι.toEquiv, card_statedProj_statedSL_two_pow hn hFc] at hcard
  exact mul_sq_sub_one_ne_168 (dvd_pow_self 2 (by omega)) hcard

theorem false_of_isSL2_five_of_surj' {Q K S : Type} [Group Q] [Group K] [Group S] [Finite S]
    [IsSimpleGroup S] (hS : Nat.card S = 168) {B O : Subgroup Q}
    (hBO : B ≤ normalizer (O : Set Q)) (hO : Odd (Nat.card O)) (N : Subgroup ↥(B ⊔ O))
    [N.Normal] (hN : N = O.subgroupOf (B ⊔ O)) (hSL : IsSL2 5 (↥(B ⊔ O) ⧸ N)) (π : K →* Q)
    (hπB : ∀ k, π k ∈ B) (hπs : ∀ b ∈ B, ∃ k, π k = b) (ρ : K →* S)
    (hρ : Function.Surjective ρ) (hρπ : ∀ k, π k = 1 → ρ k = 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfX : ∀ k, π k ∈ B ⊔ O := fun k => (le_sup_left : B ≤ B ⊔ O) (hπB k)
  let f : K →* ↥(B ⊔ O) := π.codRestrict (B ⊔ O) hfX
  let φ : K →* ↥(B ⊔ O) ⧸ N := (QuotientGroup.mk' N).comp f
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hx' : x ∈ O ⊔ B := by
      rw [sup_comm]
      exact hx
    obtain ⟨o, ho, b, hb, rfl⟩ := Setup.Family.mem_sup_of_le_normalizer hBO hx'
    obtain ⟨k, rfl⟩ := hπs b hb
    refine ⟨k, ?_⟩
    have hoN : (⟨o, (le_sup_right : O ≤ B ⊔ O) ho⟩ : ↥(B ⊔ O)) ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact ho
    have hsplit : (⟨o * π k, hx⟩ : ↥(B ⊔ O)) = ⟨o, (le_sup_right : O ≤ B ⊔ O) ho⟩ * f k := rfl
    show (QuotientGroup.mk (f k) : ↥(B ⊔ O) ⧸ N) = QuotientGroup.mk ⟨o * π k, hx⟩
    rw [hsplit, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hoN, one_mul]
  have hXN : Nat.card (↥(B ⊔ O) ⧸ N) = 120 := by
    obtain ⟨e⟩ := hSL
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hidx : φ.ker.index = 120 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hφs, Subgroup.card_top, hXN]
  have hNn : ((φ.ker).map ρ).Normal := φ.normal_ker.map ρ hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((φ.ker).map ρ) with h | h
  ·
    have h1 := Subgroup.index_dvd_of_le ((Subgroup.map_eq_bot_iff _).1 h)
    rw [hidx, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ρ hρ, Subgroup.card_top,
      hS] at h1
    norm_num at h1
  ·
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hS]; norm_num)
    have hsk : s ∈ (φ.ker).map ρ := h ▸ mem_top s
    obtain ⟨k, hk, rfl⟩ := hsk
    have hfk : f k ∈ N := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hk)
    rw [hN, Subgroup.mem_subgroupOf] at hfk
    have hpow : π k ^ Nat.card O = 1 := by
      have := pow_card_eq_one' (G := ↥O) (x := ⟨π k, hfk⟩)
      exact congrArg Subtype.val this
    have h1 : ρ k ^ Nat.card O = 1 := by
      rw [← map_pow]
      exact hρπ _ (by rw [map_pow]; exact hpow)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hs] at h2
    exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 h2)

end Groups

variable {G : Type} [Group G] [Finite G]

theorem false_of_isSL2_five_of_surj {H K₀ Ke : Subgroup G} (hKeK₀ : Ke ≤ K₀) (hK₀H : K₀ ≤ H)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hS : Nat.card S = 168)
    (ρ : ↥Ke →* S) (hρ : Function.Surjective ρ)
    (hρP : ∀ k : ↥Ke, (k : G) ∈ pCoreOf 2 H → ρ k = 1)
    (N : Subgroup ↥(modO2Image H Ke ⊔
      (CFSG.oddCore ↥(modO2Image H K₀)).map (modO2Image H K₀).subtype)) [N.Normal]
    (hN : N = ((CFSG.oddCore ↥(modO2Image H K₀)).map (modO2Image H K₀).subtype).subgroupOf
      (modO2Image H Ke ⊔ (CFSG.oddCore ↥(modO2Image H K₀)).map (modO2Image H K₀).subtype))
    (hSL : IsSL2 5 (↥(modO2Image H Ke ⊔
      (CFSG.oddCore ↥(modO2Image H K₀)).map (modO2Image H K₀).subtype) ⧸ N)) : False := by
  have hKeH : Ke ≤ H := hKeK₀.trans hK₀H
  have hBL : modO2Image H Ke ≤ modO2Image H K₀ := Subgroup.map_mono fun x hx => hKeK₀ hx
  refine false_of_isSL2_five_of_surj' hS (hBL.trans (A312.le_normalizer_oddCoreSub _)) ?_ N hN
    hSL ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hKeH))
    (fun k => ⟨Subgroup.inclusion hKeH k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩) ?_ ρ hρ ?_
  · rw [Subgroup.card_map_of_injective (modO2Image H K₀).subtype_injective]
    exact A312.odd_card_oddCore _
  · rintro b ⟨y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  · intro k hk
    refine hρP k ?_
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    rw [pCoreOf_eq_map_cfsgPCore]
    exact ⟨_, hk, rfl⟩

theorem a312Nonquasi_of_isLocal
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) {T K₀ Ke : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀) (hKe : Ke ∈ lFamily T)
    (hKeK₀ : Ke ≤ K₀) (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    A312Nonquasi (modO2Image (K₀ ⊔ T) Ke) (modO2Image (K₀ ⊔ T) K₀) := by
  have : IsSimpleGroup G := hs
  set H := K₀ ⊔ T with hH
  set P := CFSG.pCore 2 ↥H with hP
  have hK₀H : K₀ ≤ H := le_sup_left
  have hLocal : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hSQ : Vol2Native.SQTKHypCat (↥H ⧸ P) :=
    Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hLocal hK₀.2.2.2
  have hSH : IsSylowTwoOf T H := ⟨le_sup_right, hT.1, fun h2 => hT.2 (h2.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le
      (le_sup_right : T ≤ H)))⟩
  have hTbar : IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' P)) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSH) _
      (QuotientGroup.mk'_surjective P)
  have hK₀c : K₀ ∈ cComp H := hK₀.2.1
  have hLc : modO2Image H K₀ ∈ cComp (⊤ : Subgroup (↥H ⧸ P)) := modO2Image_mem_cComp hK₀c
  have hBl : modO2Image H Ke ∈ lFamily ((T.subgroupOf H).map (QuotientGroup.mk' P)) :=
    modO2Image_mem_lFamily hSH (hKeK₀.trans hK₀H) hKe
  have hBL : modO2Image H Ke ≤ modO2Image H K₀ := Subgroup.map_mono fun x hx => hKeK₀ hx
  have hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image H K₀) := by
    intro h
    obtain ⟨e⟩ := modO2_mulEquiv hK₀c
    exact hq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h)
  have h36 : A36Strong (modO2Image H K₀) :=
    (Vol2Native.a36CoreForSQTKCat_proved (↥H ⧸ P) hSQ _ hLc).toStrong hnq
  exact A312.nonquasi_of_lFamily a312SL2Fact hTbar hLc hBL hBl h36 hnq

end CFSG.Quasithin.H13.A7
