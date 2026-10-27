module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Section14Aut
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bRank
public import CFSG.Quasithin.Background.SmithB45ExcHSRuDisp

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.GH74.Uniqueness
open CFSG.GH74.Uniqueness.Bender
open CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X5

private theorem center_eq_bot_of_sz_quotient {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    [Finite ↥L] (hperf : Group.IsPerfect ↥L) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    {a : ℕ} (ha : 1 ≤ a) (α : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Open.Sz a) :
    Subgroup.center ↥L = ⊥ := by
  let α' : ↥L ⧸ Subgroup.center ↥L ≃* ↥(CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    α.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)
  let π : ↥L →* ↥(CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    α'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := α'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := CFSG.SectionRank.center_eq_ker_of_mulEquiv α'
  have hodd : Odd (Nat.card ↥π.ker) := by
    rw [hker]
    exact hZ
  have hbot : π.ker = ⊥ :=
    CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a ha π hπ hker.le hodd
  rwa [hker] at hbot

private theorem mem_of_sq_eq_one_of_le_normalizer
    {V : Type} [CommGroup V] {X L : Subgroup (MulAut V)} [Finite ↥L]
    {a : ℕ} (hB : BenderType ↥L (2 * a + 1) 2 1)
    (hLX : L ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hC : X ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    {b : MulAut V} (hbX : b ∈ X) (hb2 : b * b = 1) : b ∈ L := by
  have hbN : b ∈ Subgroup.normalizer (L : Set (MulAut V)) := hXL hbX
  let gN : ↥(Subgroup.normalizer (L : Set (MulAut V))) := ⟨b, hbN⟩
  have hσ2 : conjAut L gN * conjAut L gN = 1 := by
    rw [← map_mul]
    have hgg : gN * gN = 1 := Subtype.ext (by simpa using hb2)
    rw [hgg, map_one]
  obtain ⟨g, hg⟩ := hB.not_outer_involution_suzuki (conjAut L gN) hσ2
  have hconj : ∀ x ∈ L, b * x * b⁻¹ = (g : MulAut V) * x * (g : MulAut V)⁻¹ := by
    intro x hx
    have h1 := congrArg (fun y : ↥L => (y : MulAut V)) (hg ⟨x, hx⟩)
    simpa [conjAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hmemC : (g : MulAut V)⁻¹ * b ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hconj x hx
    have hstep : ((g : MulAut V)⁻¹ * b) * x = x * ((g : MulAut V)⁻¹ * b) := by
      calc ((g : MulAut V)⁻¹ * b) * x
          = (g : MulAut V)⁻¹ * (b * x * b⁻¹) * b := by group
        _ = (g : MulAut V)⁻¹ * ((g : MulAut V) * x * (g : MulAut V)⁻¹) * b := by rw [h1]
        _ = x * ((g : MulAut V)⁻¹ * b) := by group
    exact hstep.symm
  have hmemX : (g : MulAut V)⁻¹ * b ∈ X := X.mul_mem (X.inv_mem (hLX g.2)) hbX
  have hmemL : (g : MulAut V)⁻¹ * b ∈ L := hC (Subgroup.mem_inf.mpr ⟨hmemX, hmemC⟩)
  have hb : b = (g : MulAut V) * ((g : MulAut V)⁻¹ * b) := by group
  rw [hb]
  exact L.mul_mem g.2 hmemL

private theorem fixV_inf_inf_le_of_closure_eq {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {s₁ s₂ s₃ : MulAut W}
    (hcl : Subgroup.closure ({s₁, s₂, s₃} : Set (MulAut W)) = L) :
    fixV (Subgroup.zpowers s₁) ⊓ fixV (Subgroup.zpowers s₂) ⊓ fixV (Subgroup.zpowers s₃) ≤
      fixV L := by
  intro v hv
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hv
  obtain ⟨⟨hv₁, hv₂⟩, hv₃⟩ := hv
  rw [mem_fixV] at hv₁ hv₂ hv₃ ⊢
  intro x hx
  rw [← hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases Set.mem_insert_iff.mp hy with h | hy
    · rw [h]; exact hv₁ s₁ (Subgroup.mem_zpowers s₁)
    rcases Set.mem_insert_iff.mp hy with h | hy
    · rw [h]; exact hv₂ s₂ (Subgroup.mem_zpowers s₂)
    rw [Set.mem_singleton_iff.mp hy]
    exact hv₃ s₃ (Subgroup.mem_zpowers s₃)
  | one => simp
  | mul y z _ _ ihy ihz => rw [MulAut.mul_apply, ihz, ihy]
  | inv y _ ihy =>
    calc y⁻¹ v = y⁻¹ (y v) := by rw [ihy]
      _ = v := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private theorem index_fixV_zpowers_eq_of_isConj {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {s b : ↥L} (h : IsConj s b) :
    (fixV (Subgroup.zpowers (b : MulAut W))).index =
      (fixV (Subgroup.zpowers (s : MulAut W))).index := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hc' : (b : MulAut W) = (c : MulAut W) * (s : MulAut W) * (c : MulAut W)⁻¹ := by
    have h1 := congrArg (fun y : ↥L => (y : MulAut W)) hc.symm
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  rw [hc']
  exact index_fixV_conj (c : MulAut W) (s : MulAut W)

private theorem two_pow_four_mul_le_index_fixV {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1)
    {L : Subgroup (MulAut V)} [Finite ↥L] {a : ℕ}
    (hppd : ∀ (K : Type) [Group K] [Finite K] (n : ℕ), BenderType K n 2 1 →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf (2 : ZMod p) = 4 * n ∧ p ∣ Nat.card K)
    (hB : BenderType ↥L (2 * a + 1) 2 1) :
    2 ^ (4 * (2 * a + 1)) ≤ (fixV L).index := by
  obtain ⟨p, hp, hp2, hord, hpdvd⟩ := hppd ↥L (2 * a + 1) hB
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hpdvd
  let c : MulAut V := (x : MulAut V)
  have hcpow : c ^ p = 1 := by
    have h1 : x ^ p = 1 := by rw [← hx, pow_orderOf_eq_one]
    have h2 := congrArg (fun y : ↥L => (y : MulAut V)) h1
    simpa [c, Subgroup.coe_pow] using h2
  have hc1 : c ≠ 1 := by
    intro hc
    apply hp.ne_one
    have hx1 : x = 1 := Subtype.ext (by simpa [c] using hc)
    rw [hx1, orderOf_one] at hx
    exact hx.symm
  have hmain := two_pow_orderOf_le_index_fixV (W := V) hV (ℓ := p) hp2 hcpow hc1
  have hle : (fixV (Subgroup.zpowers c)).index ≤ (fixV L).index :=
    index_fixV_antitone (Subgroup.zpowers_le.mpr x.2)
  rw [hord] at hmain
  exact le_trans hmain hle

private theorem two_pow_lt_index_fixV_of_involution
    {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} [Finite ↥L] {a : ℕ}
    (hgen : ∀ (K : Type) [Group K] [Finite K] (n : ℕ), BenderType K n 2 1 →
      ∃ s₁ s₂ s₃ : K, s₁ * s₁ = 1 ∧ s₁ ≠ 1 ∧ s₂ * s₂ = 1 ∧ s₂ ≠ 1 ∧ s₃ * s₃ = 1 ∧ s₃ ≠ 1 ∧
        Subgroup.closure ({s₁, s₂, s₃} : Set K) = ⊤)
    (hB : BenderType ↥L (2 * a + 1) 2 1)
    (h4 : 2 ^ (4 * (2 * a + 1)) ≤ (fixV L).index)
    {b : ↥L} (hb2 : b * b = 1) (hb1 : b ≠ 1) :
    2 ^ (2 * a + 1) < (fixV (Subgroup.zpowers (b : MulAut V))).index := by
  obtain ⟨s₁, s₂, s₃, hs₁, hs₁1, hs₂, hs₂1, hs₃, hs₃1, hcl⟩ := hgen ↥L (2 * a + 1) hB
  have hcl' : Subgroup.closure
      ({((s₁ : ↥L) : MulAut V), ((s₂ : ↥L) : MulAut V), ((s₃ : ↥L) : MulAut V)} :
        Set (MulAut V)) = L := by
    have h := congrArg (Subgroup.map L.subtype) hcl
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at h
    simpa using h
  have hfix := fixV_inf_inf_le_of_closure_eq hcl'
  set I := (fixV (Subgroup.zpowers (b : MulAut V))).index with hI
  have hI₁ : (fixV (Subgroup.zpowers ((s₁ : ↥L) : MulAut V))).index = I := by
    rw [hI]
    exact (index_fixV_zpowers_eq_of_isConj
      (hB.lemma_3_4_a hs₁ hs₁1 hb2 hb1)).symm
  have hI₂ : (fixV (Subgroup.zpowers ((s₂ : ↥L) : MulAut V))).index = I := by
    rw [hI]
    exact (index_fixV_zpowers_eq_of_isConj
      (hB.lemma_3_4_a hs₂ hs₂1 hb2 hb1)).symm
  have hI₃ : (fixV (Subgroup.zpowers ((s₃ : ↥L) : MulAut V))).index = I := by
    rw [hI]
    exact (index_fixV_zpowers_eq_of_isConj
      (hB.lemma_3_4_a hs₃ hs₃1 hb2 hb1)).symm
  have h3 : (fixV L).index ≤ I * I * I := by
    calc (fixV L).index
        ≤ (fixV (Subgroup.zpowers ((s₁ : ↥L) : MulAut V)) ⊓
            fixV (Subgroup.zpowers ((s₂ : ↥L) : MulAut V)) ⊓
            fixV (Subgroup.zpowers ((s₃ : ↥L) : MulAut V))).index :=
          Subgroup.index_antitone hfix
      _ ≤ (fixV (Subgroup.zpowers ((s₁ : ↥L) : MulAut V)) ⊓
            fixV (Subgroup.zpowers ((s₂ : ↥L) : MulAut V))).index *
            (fixV (Subgroup.zpowers ((s₃ : ↥L) : MulAut V))).index :=
          Subgroup.index_inf_le
      _ ≤ ((fixV (Subgroup.zpowers ((s₁ : ↥L) : MulAut V))).index *
            (fixV (Subgroup.zpowers ((s₂ : ↥L) : MulAut V))).index) *
            (fixV (Subgroup.zpowers ((s₃ : ↥L) : MulAut V))).index :=
          Nat.mul_le_mul_right _ Subgroup.index_inf_le
      _ = I * I * I := by rw [hI₁, hI₂, hI₃]
  have hmain : 2 ^ (4 * (2 * a + 1)) ≤ I * I * I := le_trans h4 h3
  by_contra hcon
  have hcon : I ≤ 2 ^ (2 * a + 1) := Nat.le_of_not_lt hcon
  have hcube : I * I * I ≤ (2 ^ (2 * a + 1)) ^ 3 := by
    calc I * I * I = I ^ 3 := by ring
      _ ≤ (2 ^ (2 * a + 1)) ^ 3 := Nat.pow_le_pow_left hcon 3
  have hle : 2 ^ (4 * (2 * a + 1)) ≤ 2 ^ (3 * (2 * a + 1)) := by
    refine le_trans hmain ?_
    calc I * I * I ≤ (2 ^ (2 * a + 1)) ^ 3 := hcube
      _ = 2 ^ (3 * (2 * a + 1)) := by
        rw [← pow_mul]
        congr 1
        ring
  have hlt : 2 ^ (3 * (2 * a + 1)) < 2 ^ (4 * (2 * a + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact absurd hle (not_le.mpr hlt)

theorem two_mul_card_lt_index_fixV_sz_of
    (hgen : ∀ (K : Type) [Group K] [Finite K] (n : ℕ), BenderType K n 2 1 →
      ∃ s₁ s₂ s₃ : K, s₁ * s₁ = 1 ∧ s₁ ≠ 1 ∧ s₂ * s₂ = 1 ∧ s₂ ≠ 1 ∧ s₃ * s₃ = 1 ∧ s₃ ≠ 1 ∧
        Subgroup.closure ({s₁, s₂, s₃} : Set K) = ⊤)
    (hconj : ∀ (K : Type) [Group K] [Finite K] (n : ℕ), BenderType K n 2 1 →
      ∀ A : Subgroup K, (∀ x ∈ A, x * x = 1) → Nat.card A = 2 ^ n →
        ∃ g : K, A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤)
    (hppd : ∀ (K : Type) [Group K] [Finite K] (n : ℕ), BenderType K n 2 1 →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf (2 : ZMod p) = 4 * n ∧ p ∣ Nat.card K)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {X L : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hperf : Group.IsPerfect ↥L) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    (hC : X ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    {a : ℕ} (ha : 1 ≤ a) (α : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Open.Sz a)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    2 * Nat.card A < (fixV A).index := by
  haveI : Finite ↥L := inferInstance
  have hZbot : Subgroup.center ↥L = ⊥ := center_eq_bot_of_sz_quotient hperf hZ ha α
  let eL : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
  have hB : BenderType ↥L (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha
      ((eL.symm.trans α).trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hAL : A ≤ L := by
    intro b hbA
    refine mem_of_sq_eq_one_of_le_normalizer hB hLX hXL hC (hAX hbA) ?_
    have h := hAe.2 b hbA
    rwa [pow_two] at h
  have hAcard_le : Nat.card A ≤ 2 ^ (2 * a + 1) := by
    have hsq : ∀ x ∈ A.subgroupOf L, x * x = 1 := by
      intro x hx
      have hxA : (x : MulAut V) ∈ A := Subgroup.mem_subgroupOf.mp hx
      exact Subtype.ext (by
        have h := hAe.2 (x : MulAut V) hxA
        rwa [pow_two] at h)
    have h := hB.card_le_of_sq_eq_one (A.subgroupOf L) hsq
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv] at h
  have h4 : 2 ^ (4 * (2 * a + 1)) ≤ (fixV L).index :=
    two_pow_four_mul_le_index_fixV hV hppd hB
  have h5 : ∀ {b : ↥L}, b * b = 1 → b ≠ 1 →
      2 ^ (2 * a + 1) < (fixV (Subgroup.zpowers (b : MulAut V))).index :=
    fun hb2 hb1 => two_pow_lt_index_fixV_of_involution hgen hB h4 hb2 hb1
  rcases lt_or_eq_of_le hAcard_le with hlt | heq
  ·
    have hsqA : ∀ x ∈ A, x * x = 1 := by
      intro x hx
      have h := hAe.2 x hx
      rwa [pow_two] at h
    have hAp : IsPGroup 2 ↥A := isPGroup_two_of_mul_self_eq_one (A := A) hsqA
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
    have hklt : k < 2 * a + 1 := by
      by_contra hcon
      have hle : 2 ^ (2 * a + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2A : 2 * Nat.card A ≤ 2 ^ (2 * a + 1) := by
      rw [hk]
      rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [mul_comm, ← pow_succ]]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    have hbL : (b : MulAut V) ∈ L := hAL b.2
    have hb2 : (⟨(b : MulAut V), hbL⟩ : ↥L) * ⟨(b : MulAut V), hbL⟩ = 1 :=
      Subtype.ext (by
        have h := hAe.2 (b : MulAut V) b.2
        rwa [pow_two] at h)
    have hb1' : (⟨(b : MulAut V), hbL⟩ : ↥L) ≠ 1 := by
      intro h
      exact hb1 (by simpa using congrArg (fun y : ↥L => (y : MulAut V)) h)
    have hb := h5 hb2 hb1'
    have hle : (fixV (Subgroup.zpowers (b : MulAut V))).index ≤ (fixV A).index :=
      index_fixV_antitone (Subgroup.zpowers_le.mpr b.2)
    exact lt_of_le_of_lt h2A (lt_of_lt_of_le hb hle)
  ·
    have hA'card : Nat.card (A.subgroupOf L) = 2 ^ (2 * a + 1) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
      exact heq
    have hA'sq : ∀ x ∈ A.subgroupOf L, x * x = 1 := by
      intro x hx
      have hxA : (x : MulAut V) ∈ A := Subgroup.mem_subgroupOf.mp hx
      exact Subtype.ext (by
        have h := hAe.2 (x : MulAut V) hxA
        rwa [pow_two] at h)
    obtain ⟨g, hg⟩ := hconj ↥L (2 * a + 1) hB (A.subgroupOf L) hA'sq hA'card
    let g' : MulAut V := (g : ↥L)
    have hcomp : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g').toMonoidHom.comp L.subtype := by
      refine MonoidHom.ext fun y => ?_
      change ((MulAut.conj g) y : MulAut V) = MulAut.conj g' ((y : ↥L) : MulAut V)
      rw [MulAut.conj_apply, MulAut.conj_apply]
      simp [Subgroup.coe_mul, Subgroup.coe_inv, g']
    have hBmap : Subgroup.map L.subtype
        ((A.subgroupOf L).map (MulAut.conj g).toMonoidHom) =
        A.map (MulAut.conj g').toMonoidHom := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAL]
    have hLsup : L = A ⊔ A.map (MulAut.conj g').toMonoidHom := by
      have h := congrArg (Subgroup.map L.subtype) hg
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, hBmap,
        Subgroup.map_subgroupOf_eq_of_le hAL] at h
      exact h.symm
    have h7 : (fixV L).index ≤ (fixV A).index ^ 2 := by
      rw [hLsup]
      exact CFSG.Quasithin.B45Exc.HSRu.index_fixV_sup_conj_le A g'
    have h4' : 2 ^ (4 * (2 * a + 1)) ≤ (fixV A).index ^ 2 := le_trans h4 h7
    have hindex : 2 ^ (2 * (2 * a + 1)) ≤ (fixV A).index := by
      by_contra hcon
      have hcon : (fixV A).index < 2 ^ (2 * (2 * a + 1)) := Nat.lt_of_not_le hcon
      have hlt : (fixV A).index ^ 2 < (2 ^ (2 * (2 * a + 1))) ^ 2 :=
        Nat.pow_lt_pow_left hcon (by norm_num)
      have heq2 : (2 ^ (2 * (2 * a + 1))) ^ 2 = 2 ^ (4 * (2 * a + 1)) := by
        rw [← pow_mul]
        congr 1
        ring
      have hcontr : 2 ^ (4 * (2 * a + 1)) < 2 ^ (4 * (2 * a + 1)) := by
        calc 2 ^ (4 * (2 * a + 1)) ≤ (fixV A).index ^ 2 := h4'
          _ < (2 ^ (2 * (2 * a + 1))) ^ 2 := hlt
          _ = 2 ^ (4 * (2 * a + 1)) := heq2
      exact lt_irrefl _ hcontr
    have hfin : 2 * 2 ^ (2 * a + 1) < 2 ^ (2 * (2 * a + 1)) := by
      rw [mul_comm, ← pow_succ]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    calc 2 * Nat.card A = 2 * 2 ^ (2 * a + 1) := by rw [heq]
      _ < 2 ^ (2 * (2 * a + 1)) := hfin
      _ ≤ (fixV A).index := hindex

end CFSG.Quasithin.F112Crit.APrime

end
