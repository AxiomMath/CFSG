module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Coord
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E6
import CFSG.LocalAnalysis.UniquenessCase.UC6K36StrongEmb
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.RankThree.PartOne.KF.U4Ambient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

private theorem k335sdv_S_le_normalizer_L {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) : S ≤ Subgroup.normalizer (L : Set G) :=
  h.normal.trans ((k335_normalizer_le_gamma h.elem h.card).trans h.gamma)

private noncomputable def k335sdv_rho' {G : Type} [Group G] {L S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    ↥S →* MulAut (L.subgroupOf (Subgroup.normalizer (L : Set G))) :=
  (MulAut.conjNormal (H := L.subgroupOf (Subgroup.normalizer (L : Set G)))).comp
    (Subgroup.inclusion hSN)

private theorem k335sdv_rho'_conj {G : Type} [Group G] {L S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (s : ↥S)
    (hs : k335sdv_rho' hSN s = 1) {x : G} (hx : x ∈ L) :
    (s : G) * x * (s : G)⁻¹ = x := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  let y : L.subgroupOf N := ⟨⟨x, hLN hx⟩, hx⟩
  have hy : MulAut.conjNormal (Subgroup.inclusion hSN s) y = y := by
    have := congrArg (fun f : MulAut (L.subgroupOf N) => f y) hs
    simpa [k335sdv_rho'] using this
  have hyN : ((MulAut.conjNormal (Subgroup.inclusion hSN s) y : L.subgroupOf N) : N) = (y : N) :=
    congrArg (fun z : L.subgroupOf N => (z : N)) hy
  have hyG := congrArg (fun z : N => (z : G)) hyN
  rw [MulAut.conjNormal_apply] at hyG
  simpa [y, Subgroup.inclusion] using hyG

private theorem k335sdv_center_L_eq_bot {G : Type} [Group G] {L : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) : Subgroup.center ↥L = ⊥ := by
  have : IsSimpleGroup ↥L := k335_simple_L hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hbot | htop
  · exact hbot
  · exfalso
    have : IsMulCommutative ↥L := IsMulCommutative.of_comm (fun a b => by
      have ha : a ∈ Subgroup.center ↥L := by rw [htop]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm)
    have hp : (Nat.card ↥L).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [k335_card_L hL] at hp
    norm_num at hp

private theorem k335sdv_rho'_injective {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2)
    (three_le : ∀ {H : Type} [Group H] [Finite H] {Q : Subgroup H},
      CFSG.Open.IsElemAbelian 3 Q → Nat.card Q = 9 →
      ∀ {t : H}, t ^ 3 = 1 → t ∉ Q → (∀ x ∈ Q, x * t = t * x) →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H)) :
    Function.Injective (k335sdv_rho' (k335sdv_S_le_normalizer_L h)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let hSN : S ≤ Subgroup.normalizer (L : Set G) := k335sdv_S_le_normalizer_L h
  have hkerP : IsPGroup 3 ↥(MonoidHom.ker (k335sdv_rho' hSN)) :=
    h.sylow.isPGroup.of_injective (MonoidHom.ker (k335sdv_rho' hSN)).subtype
      Subtype.coe_injective
  apply (MonoidHom.ker_eq_bot_iff (k335sdv_rho' hSN)).mp
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx1' : (⟨x, hx⟩ : ↥(MonoidHom.ker (k335sdv_rho' hSN))) ≠ 1 := by
    intro h1
    exact hx1 (Subtype.ext_iff.mp h1)
  have h3 : 3 ∣ orderOf (⟨x, hx⟩ : ↥(MonoidHom.ker (k335sdv_rho' hSN))) :=
    hkerP.dvd_orderOf hx1'
  have h3card : 3 ∣ Nat.card ↥(MonoidHom.ker (k335sdv_rho' hSN)) :=
    h3.trans (orderOf_dvd_natCard _)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 h3card
  let s : ↥S := t.1
  have hρ : k335sdv_rho' hSN s = 1 := MonoidHom.mem_ker.mp t.2
  have hs3 : (s : G) ^ 3 = 1 := by
    have h1 : t ^ 3 = 1 := by rw [← ht, pow_orderOf_eq_one]
    have h2 : s ^ 3 = 1 := by
      have := congrArg (fun z : ↥(MonoidHom.ker (k335sdv_rho' hSN)) => (z : ↥S)) h1
      simpa [s, Subgroup.coe_pow] using this
    have h3 := congrArg (fun z : ↥S => (z : G)) h2
    simpa [Subgroup.coe_pow] using h3
  have hsne : s ≠ 1 := by
    intro h1
    have ht1 : t = 1 := Subtype.ext (by simpa [s] using h1)
    rw [ht1, orderOf_one] at ht
    omega
  by_cases hP : (s : G) ∈ P
  · have hsL : (s : G) ∈ L := h.sylowL.le hP
    have hZ : (⟨(s : G), hsL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := k335sdv_rho'_conj hSN s hρ z.2
      have h2 : (s : G) * z = z * (s : G) := by
        calc (s : G) * z = ((s : G) * z * (s : G)⁻¹) * (s : G) := by group
          _ = z * (s : G) := by rw [h1]
      exact Subtype.ext h2.symm
    rw [k335sdv_center_L_eq_bot h.lie] at hZ
    have hsg : (s : G) = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hZ)
    exact hsne (Subtype.ext hsg)
  · have hcomm : ∀ x ∈ P, x * (s : G) = (s : G) * x := by
      intro x hx
      have h1 := k335sdv_rho'_conj hSN s hρ (h.sylowL.le hx)
      have h2 : (s : G) * x = x * (s : G) := by
        calc (s : G) * x = ((s : G) * x * (s : G)⁻¹) * (s : G) := by group
          _ = x * (s : G) := by rw [h1]
      exact h2.symm
    have := three_le h.elem h.card hs3 hP hcomm
    omega

private theorem k335sdv_card_mulAut {G : Type} [Group G] {L : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) : Nat.card (MulAut ↥L) = 241920 := by
  obtain ⟨K, hK, hfin, hcardK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  let : Field K := hK
  let : Finite K := hfin
  have hk : Nat.card K = 4 := by rw [hcardK]; norm_num
  calc Nat.card (MulAut ↥L)
      = Nat.card (MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K)) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ = 241920 := CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hk

private theorem k335sdv_core {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2)
    (three_le : ∀ {H : Type} [Group H] [Finite H] {Q : Subgroup H},
      CFSG.Open.IsElemAbelian 3 Q → Nat.card Q = 9 →
      ∀ {t : H}, t ^ 3 = 1 → t ∉ Q → (∀ x ∈ Q, x * t = t * x) →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H)) :
    Nat.card S ∣ 27 := by
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := k335sdv_S_le_normalizer_L h
  have hinj : Function.Injective (k335sdv_rho' hSN) := k335sdv_rho'_injective h hr three_le
  let e : L.subgroupOf (Subgroup.normalizer (L : Set G)) ≃* L :=
    Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := L))
  let ρ : ↥S →* MulAut ↥L := (MulAut.congr e).toMonoidHom.comp (k335sdv_rho' hSN)
  have hρinj : Function.Injective ρ := by
    have hc : Function.Injective (MulAut.congr e) := (MulAut.congr e).injective
    simpa [ρ, Function.comp_def] using hc.comp hinj
  have hdvd : Nat.card S ∣ Nat.card (MulAut ↥L) := Subgroup.card_dvd_of_injective ρ hρinj
  rw [k335sdv_card_mulAut h.lie] at hdvd
  rw [h.sylow.card_eq, Subgroup.card_top] at hdvd
  have hm : (Nat.card G).factorization 3 ≤ 3 := by
    by_contra hm
    have hm4 : 4 ≤ (Nat.card G).factorization 3 := by omega
    have h4 : 3 ^ 4 ∣ 241920 := (Nat.pow_dvd_pow 3 hm4).trans hdvd
    norm_num at h4
  rw [h.sylow.card_eq, Subgroup.card_top]
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27]
  exact Nat.pow_dvd_pow 3 hm

theorem k335_card_S_dvd {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2) :
    Nat.card S ∣ 27 :=
  k335sdv_core h hr k335_three_le_pRank

theorem k335_center_eq_bot {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2) :
    Subgroup.center G = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h.center.card_eq_or_dvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have ht3 : (t : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
    have ht1 : (t : G) ≠ 1 := by
      intro h1
      rw [show t = 1 from Subtype.ext h1, orderOf_one] at ht
      omega
    have htP : (t : G) ∉ P := fun htP => by
      have hm : (t : G) ∈ P ⊓ Subgroup.center G := Subgroup.mem_inf.2 ⟨htP, t.2⟩
      rw [h.disjoint] at hm
      exact ht1 (Subgroup.mem_bot.1 hm)
    have h3 := k335_three_le_pRank h.elem h.card ht3 htP fun x _ =>
      Subgroup.mem_center_iff.1 t.2 x
    omega

theorem k335_center_eq_bot_of_not_dvd {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center G)) :
    Subgroup.center G = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Subgroup.eq_bot_of_card_eq _ (h.center.card_eq_or_dvd.resolve_right h3)

theorem k335_odd_card_center {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) : Odd (Nat.card (Subgroup.center G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h.center.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem k335_mulEquiv_of_center {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) :
    Nonempty (G ⧸ Subgroup.center G ≃* G) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem k335_isSimpleGroup {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hZ : Subgroup.center G = ⊥) : IsSimpleGroup G := by
  have := h.quasi.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem k335_nonabelian_quot {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := by
  by_contra hab'
  have hab : ∀ a b : G ⧸ Subgroup.center G, a * b = b * a := fun a b =>
    by_contra fun hne => hab' ⟨a, b, hne⟩
  have hle : commutator G ≤ Subgroup.center G := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hab (x : G ⧸ Subgroup.center G) (y : G ⧸ Subgroup.center G)]
    group
  have hZ : Subgroup.center G = ⊤ := top_le_iff.1 (h.quasi.1 ▸ hle)
  apply k335_ne_bot h.card
  rw [← h.disjoint, hZ, inf_top_eq]

theorem k335_isCatalog {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) : CFSG.Open.IsCatalogGroup (G ⧸ Subgroup.center G) := by
  have := h.quasi.2
  refine h.kGroup.isCatalogGroup_of_surjective ⊤ (k335_nonabelian_quot h)
    ((QuotientGroup.mk' _).comp (⊤ : Subgroup G).subtype) fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩

theorem k335_eq_of_card {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hS9 : Nat.card S = 9) : P = S :=
  Subgroup.eq_of_le_of_card_ge h.le (by rw [hS9, h.card])

theorem k335_eq_of_not_dvd {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (h27 : ¬ 27 ∣ Nat.card G) : P = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine k335_eq_of_card h ?_
  have h2 : 9 ∣ Nat.card S := h.card ▸ Subgroup.card_dvd_of_le h.le
  rw [h.sylow.card_eq, Subgroup.card_top] at h2 ⊢
  rw [show (27 : ℕ) = 3 ^ 3 by norm_num,
    Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne'] at h27
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h2
  have hv : (Nat.card G).factorization 3 = 2 := by omega
  exact (congrArg (3 ^ ·) hv).trans (by norm_num)

theorem k335_card_S_cases {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2) :
    Nat.card S = 9 ∨ Nat.card S = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := k335_card_S_dvd h hr
  have h2 : 9 ∣ Nat.card S := h.card ▸ Subgroup.card_dvd_of_le h.le
  rw [h.sylow.card_eq] at h1 h2 ⊢
  rw [show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h1
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h2
  rcases (by omega : (Nat.card (⊤ : Subgroup G)).factorization 3 = 2 ∨
      (Nat.card (⊤ : Subgroup G)).factorization 3 = 3) with hv | hv
  · exact Or.inl ((congrArg (3 ^ ·) hv).trans (by norm_num))
  · exact Or.inr ((congrArg (3 ^ ·) hv).trans (by norm_num))

theorem k335_eq_of_even {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2)
    (he : Even ((Nat.card G).factorization 3)) : P = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases k335_card_S_cases h hr with h9 | h27
  · exact k335_eq_of_card h h9
  · exfalso
    rw [h.sylow.card_eq, Subgroup.card_top] at h27
    have hv : (Nat.card G).factorization 3 = 3 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h27.trans (by norm_num : (27 : ℕ) = 3 ^ 3))
    rw [hv] at he
    exact (by decide : ¬ Even 3) he

theorem k335_sylow_false (hΩ : CFSG.LocalAnalysis.UniquenessCase.UCK.K35Ω)
    (hSO : K335SporadicOrders) {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hZ : Subgroup.center G = ⊥) (hPS : P = S) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  subst hPS
  have : IsSimpleGroup G := k335_isSimpleGroup h hZ
  have h3 : 3 ∣ Nat.card G :=
    dvd_trans (by norm_num : 3 ∣ 9) (h.card ▸ Subgroup.card_subgroup_dvd_card P)
  have hcore : CFSG.pPrimeCore 3 G = ⊥ := by
    rcases (CFSG.pPrimeCore_normal (p := 3) (G := G)).eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exfalso
      have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := G)
      rw [h0, Subgroup.card_top] at hc
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc h3
  have hopp : CFSG.LocalAnalysis.UniquenessCase.UC22.Opp 3 (⊤ : Subgroup G) = ⊤ := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      omega
    exact CFSG.RankThree.PartOne.KFU.pElementSubgroup_eq_of_simple
      Subgroup.topEquiv.isSimpleGroup (Subgroup.mem_top z) hz hz1
  have hemb := CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_of_rankThreeGamma_le_sylow
    h.sylow (k335_ne_bot h.card) h.gamma h.ne_top
  obtain ⟨-, hX⟩ := hΩ G h.kGroup 3 Nat.prime_three (by norm_num) hopp hcore _ hemb P P h.sylow
    le_rfl h.elem (h.card.trans (by norm_num)) (fun x hx _ => hx)
    (fun b hb y hy => isMulCommutative_iff_of_setLike.mp h.elem.1 b hb y hy)
  have hdvd := k335_card_dvd h.lie
  rcases hX with hX | hX | ⟨-, hX | hX⟩ | ⟨h35, -⟩
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine
      (hX.statedClassicalModel (by decide))] at hdvd
    norm_num at hdvd
  · have h2 := k335_two_mul_card_alt hX (by norm_num)
    norm_num [Nat.factorial] at h2
    rw [show Nat.card G = 360 by omega] at hdvd
    norm_num at hdvd
  · rw [(hSO G).1 hX] at hdvd
    norm_num at hdvd
  · have hG := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
      (hX.statedClassicalModel (by decide))
    have hL : L = ⊤ := (Subgroup.card_eq_iff_eq_top L).1 (by rw [k335_card_L h.lie, hG])
    refine h.ne_top (eq_top_iff.2 fun g _ => Subgroup.mem_normalizer_iff.2 fun x => ?_)
    rw [hL]
    simp
  · omega

theorem k335_spor_false (hSN : K335SporadicNormalizer) {G : Type} [Group G] [Finite G]
    {L P S : Subgroup G} (h : K335Quasi G L P S)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic G .M24 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .He ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .Ru ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J4) : False := by
  obtain ⟨g, hg, x, hx, hgx⟩ := hSN G hs S P h.sylow h.le h.card
  refine hgx (h.closed x hx g ?_)
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem hg
  have hmem := (Subgroup.mem_normalizer_iff.1 hg' x).1 (h.le hx)
  rwa [inv_inv] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
