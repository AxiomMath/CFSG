module

public import CFSG.Quasithin.Vol2.Ch4Sec4W443
public import CFSG.Quasithin.Vol2.Ch4Sec3L43L34
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Background.C2Nine
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.C2Nine
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pRank_type_eq_open_pRank (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p ↥H = CFSG.Open.pRank p H := CFSG.SectionRank.pRank_coe_eq_openPRank p H

theorem pRank_le_card {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ Nat.card G := by
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, -, -, hE⟩ := hk
  have h1 : k < p ^ k := Nat.lt_pow_self hp
  have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  omega

theorem le_pRank_of_isElemAbelian {p : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H := by
  refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨E, hEH, hE, hk⟩
  obtain ⟨E', -, -, hE'⟩ := hj
  have h1 : j < p ^ j := Nat.lt_pow_self hp
  have h2 : Nat.card E' ≤ Nat.card G := Subgroup.card_le_card_group E'
  omega

theorem pRank_le_two_of_isTwoLocal (hqtke : quasithinIsQTKECat G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup G} (hX : CFSG.Open.IsTwoLocal X) : CFSG.Open.pRank p X ≤ 2 := by
  refine le_trans ?_ hqtke.2.2
  refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨p, X, hp, hp2, hX, rfl⟩
  obtain ⟨q, Y, hq, -, -, hY⟩ := hj
  rw [← hY]
  exact pRank_le_card hq.one_lt Y

theorem commutator_mem_of_perfect_of_index_le_four {L V W : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hVW : V ≤ Subgroup.normalizer (W : Set G)) (hidx : (W.subgroupOf V).index ≤ 4) :
    ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ * v⁻¹ ∈ W := by
  classical
  have hconjV : ∀ (l : ↥L) (v : ↥V), (l : G) * v * (l : G)⁻¹ ∈ V := fun l v =>
    (Subgroup.mem_normalizer_iff.mp (hLV l.2) v).mp v.2
  let _ : MulAction ↥L ↥V :=
    { smul := fun l v => ⟨(l : G) * v * (l : G)⁻¹, hconjV l v⟩
      one_smul := fun v => Subtype.ext (by
        show ((1 : ↥L) : G) * v * ((1 : ↥L) : G)⁻¹ = v
        simp)
      mul_smul := fun l l' v => Subtype.ext (by
        show ((l * l' : ↥L) : G) * v * ((l * l' : ↥L) : G)⁻¹ =
          (l : G) * ((l' : G) * v * (l' : G)⁻¹) * (l : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hsmul : ∀ (l : ↥L) (v : ↥V), ((l • v : ↥V) : G) = (l : G) * v * (l : G)⁻¹ :=
    fun _ _ => rfl
  have : MulAction.QuotientAction ↥L (W.subgroupOf V) := ⟨fun l a a' h => by
    rw [Subgroup.mem_subgroupOf] at h ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, hsmul]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hLW l.2) _).mp h
    have e : ((l : G) * a * (l : G)⁻¹)⁻¹ * ((l : G) * a' * (l : G)⁻¹) =
        (l : G) * ((a⁻¹ * a' : ↥V) : G) * (l : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1⟩
  set φ := MulAction.toPermHom ↥L (↥V ⧸ W.subgroupOf V) with hφ
  have hsolv : Group.IsSolvable (Equiv.Perm (↥V ⧸ W.subgroupOf V)) := by
    have : Finite (↥V ⧸ W.subgroupOf V) := inferInstance
    exact Equiv.Perm.isSolvable (by rw [← Subgroup.index]; exact hidx)
  have hLperf : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subtype_commutator, hL, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hR : ⁅φ.range, φ.range⁆ = φ.range := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) φ
    rw [← commutator_def, hLperf, ← MonoidHom.range_eq_map] at h1
    exact h1.symm
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ↥φ.range := by
      refine ⟨?_⟩
      apply Subgroup.map_injective φ.range.subtype_injective
      rw [Subgroup.map_subtype_commutator, hR, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have : Group.IsSolvable ↥φ.range := subgroup_solvable_of_solvable _
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro l hl v hv
  have h1 : φ ⟨l, hl⟩ = 1 := by
    have : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot] at this
    exact this
  have h2 : ((⟨l, hl⟩ : ↥L) • (QuotientGroup.mk (⟨v, hv⟩ : ↥V) : ↥V ⧸ W.subgroupOf V)) =
      QuotientGroup.mk (⟨v, hv⟩ : ↥V) := by
    have := congrArg (fun σ : Equiv.Perm (↥V ⧸ W.subgroupOf V) =>
      σ (QuotientGroup.mk (⟨v, hv⟩ : ↥V))) h1
    simpa [hφ] using this
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    Subgroup.coe_inv, hsmul] at h2
  have h3 := (Subgroup.mem_normalizer_iff.mp (hVW hv) _).mp (W.inv_mem h2)
  have e : v * (((l : G) * v * (l : G)⁻¹)⁻¹ * v)⁻¹ * v⁻¹ = l * v * l⁻¹ * v⁻¹ := by group
  rwa [e] at h3

theorem eq_bot_or_eq_of_card_eight {L V : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV8 : Nat.card V = 8) (hVL : ⁅V, L⁆ = V) (W : Subgroup G) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  by_contra hne
  push Not at hne
  obtain ⟨hW1, hWV'⟩ := hne
  have hVW : V ≤ Subgroup.normalizer (W : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hVcomm v hv w (hWV hw), mul_inv_cancel_right]
      exact hw
    · intro hw
      have hwV : w ∈ V := by
        have := V.mul_mem (V.mul_mem (V.inv_mem hv) (hWV hw)) hv
        simpa [mul_assoc] using this
      rwa [hVcomm v hv w hwV, mul_inv_cancel_right] at hw
  have hcard : Nat.card W * (W.subgroupOf V).index = 8 := by
    rw [← hV8, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv,
      Subgroup.card_mul_index]
  have hW2 : 2 ≤ Nat.card W := by
    rcases Nat.lt_or_ge (Nat.card W) 2 with h | h
    · exfalso
      have h1 : Nat.card W = 1 := by
        have := Nat.card_pos (α := W)
        omega
      exact hW1 (Subgroup.card_eq_one.mp h1)
    · exact h
  have hidx2 : 2 ≤ (W.subgroupOf V).index := by
    rcases Nat.lt_or_ge (W.subgroupOf V).index 2 with h | h
    · exfalso
      have h0 : (W.subgroupOf V).index ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hcard
        omega
      have h1 : (W.subgroupOf V).index = 1 := by omega
      apply hWV'
      apply le_antisymm hWV
      intro v hv
      have := Subgroup.index_eq_one.mp h1
      have hv' : (⟨v, hv⟩ : ↥V) ∈ W.subgroupOf V := by rw [this]; exact Subgroup.mem_top _
      exact hv'
    · exact h
  have hidx4 : (W.subgroupOf V).index ≤ 4 := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul hW2 h
    omega
  have hW4 : Nat.card W ≤ 4 := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul h hidx2
    omega
  have h1 := commutator_mem_of_perfect_of_index_le_four hL hLV hLW hVW hidx4
  have hbot : (⊥ : Subgroup G).subgroupOf W = ⊥ := Subgroup.bot_subgroupOf W
  have h2 := commutator_mem_of_perfect_of_index_le_four (V := W) (W := ⊥) hL hLW
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun _ => by simp)
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun _ => by simp)
    (by rw [hbot, Subgroup.index_bot]; exact hW4)
  have hLVW : ⁅L, V⁆ ≤ W := Subgroup.commutator_le.mpr fun l hl v hv => h1 l hl v hv
  have hLW1 : ⁅L, W⁆ = ⊥ :=
    le_bot_iff.mp (Subgroup.commutator_le.mpr fun l hl w hw => h2 l hl w hw)
  have hc1 : ⁅⁅L, V⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hLVW).trans hLW1.le)
  have hc2 : ⁅⁅V, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm V L]
    exact hc1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc1 hc2
  rw [hL] at h3
  have hV : V = ⊥ := by rw [← hVL, Subgroup.commutator_comm, h3]
  rw [hV, Subgroup.card_bot] at hV8
  omega

omit [Finite G] in
theorem le_normalizer_map_subtype {H : Subgroup G} (N : Subgroup ↥H) [N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨h, hh⟩ * x * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance x hx _, rfl⟩
  · rintro ⟨x, hx, hxg⟩
    refine ⟨⟨h, hh⟩⁻¹ * x * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem inferInstance x hx ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hxg ⊢
      rw [hxg]
      group

omit [Finite G] in
theorem mem_fusionZStar_of_commutator_mem_oddCoreIn {H : Subgroup G} {g : G} (hg : g ∈ H)
    (hc : ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ oddCoreIn H) : (⟨g, hg⟩ : ↥H) ∈ fusionZStar ↥H := by
  show QuotientGroup.mk' (fusionOddCore ↥H) ⟨g, hg⟩ ∈ Subgroup.center _
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore ↥H) z
  obtain ⟨x, hx, hxe⟩ := hc h h.2
  have hx' : (⟨g, hg⟩ : ↥H) * h * (⟨g, hg⟩ : ↥H)⁻¹ * h⁻¹ ∈ fusionOddCore ↥H := by
    have e : x = (⟨g, hg⟩ : ↥H) * h * (⟨g, hg⟩ : ↥H)⁻¹ * h⁻¹ :=
      Subtype.ext (by simpa using hxe)
    rwa [← e]
  have h1 := (QuotientGroup.eq_one_iff _).mpr hx'
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  simp only [QuotientGroup.mk'_apply]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

namespace Setting443

variable {T M L B Tp VB : Subgroup G} (s : Setting443 G T M L B Tp VB)
include s

theorem VB_eq_commutator_LB :
    VB = ⁅VB, perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))⁆ := by
  set Mp := conjClosure L T with hMp
  set LB := perfectCore (Mp ⊓ Subgroup.centralizer (B : Set G)) with hLB
  have h445 := lemma_4_4_5_orbit s.hyp.toHyp4_4_1TwoOrbit
  have hLBMp : LB ≤ Mp := (perfectCore_le _).trans inf_le_left
  have hLBV : LB ≤ Subgroup.normalizer (VB : Set G) :=
    hLBMp.trans (le_sup_left.trans s.hyp.VB_normalized)
  have hO2 : pCoreOf 2 Mp ≤ pCoreOf 2 (Mp ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Mp).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 Mp)
    exact _root_.sup_le (le_normalizer_pCoreOf 2 Mp)
      ((le_normalizer_conjClosure L T).trans (normalizer_le_normalizer_pCoreOf 2 Mp))
  have hqv : ∀ q ∈ pCoreOf 2 Mp, ∀ v ∈ VB, q * v = v * q := fun q hq v hv =>
    Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).2.1 q
      (hO2 hq)
  have hLBN : LB ≤ Subgroup.normalizer ((pCoreOf 2 Mp : Subgroup G) : Set G) :=
    hLBMp.trans (le_normalizer_pCoreOf 2 Mp)
  refine le_antisymm ?_ (commutator_le_left_of_le_normalizer hLBV)
  conv_lhs => rw [s.hyp.VB_eq]
  rw [Subgroup.commutator_le]
  intro v hv g hg
  rw [h445] at hg
  have hg' : g ∈ (LB : Set G) * (pCoreOf 2 Mp : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right LB (pCoreOf 2 Mp) hLBN]
    exact hg
  obtain ⟨a, ha, q, hq, rfl⟩ := hg'
  have h1 : q * v⁻¹ = v⁻¹ * q := by
    have := hqv q hq v hv
    calc q * v⁻¹ = v⁻¹ * (v * q) * v⁻¹ := by group
      _ = v⁻¹ * (q * v) * v⁻¹ := by rw [this]
      _ = v⁻¹ * q := by group
  have e : ⁅v, a * q⁆ = ⁅v, a⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc v * (a * q) * v⁻¹ * (a * q)⁻¹ = v * a * (q * v⁻¹) * q⁻¹ * a⁻¹ := by group
      _ = v * a * (v⁻¹ * q) * q⁻¹ * a⁻¹ := by rw [h1]
      _ = v * a * v⁻¹ * a⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hv ha

end Setting443

theorem lemma448_holds (h128 : CFSG.Quasithin.ASInputs.AS_A_1_28) : Lemma448 := by
  intro G _ _ T M L B Tp VB s hU
  classical
  set Mp := conjClosure L T with hMp
  set LB := perfectCore (Mp ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set GB := Subgroup.normalizer (B : Set G) with hGB
  set O := oddCoreIn GB with hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLBperf : ⁅LB, LB⁆ = LB := perfectCore_perfect _
  have hLBGB : LB ≤ GB :=
    (perfectCore_le _).trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hVBC : VB ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp s.hyp.VB_centralizes
  have hVBGB : VB ≤ GB := hVBC.trans (Subgroup.centralizer_le_normalizer _)
  have hVBcomm : ∀ a ∈ VB, ∀ b ∈ VB, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hb)).2.1 a
      (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le ha)).1
  have hVBel : CFSG.Open.IsElemAbelian 2 VB :=
    ⟨⟨⟨fun x y => Subtype.ext (hVBcomm _ x.2 _ y.2)⟩⟩, fun v hv =>
      (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).2.2⟩
  have hVB2 : IsPGroup 2 VB := isPGroup_two_of_isElemAbelian hVBel
  have hLBV : LB ≤ Subgroup.normalizer (VB : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans (le_sup_left.trans s.hyp.VB_normalized))
  have hVBeq : ⁅VB, LB⁆ = VB := s.VB_eq_commutator_LB.symm
  have hVB1 : VB ≠ ⊥ := s.hyp.VB_ne_bot
  have hnontriv : ¬ ∀ l ∈ LB, ∀ v ∈ VB, l * v * l⁻¹ * v⁻¹ = 1 := by
    intro h
    apply hVB1
    rw [← hVBeq, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    have h1 := h l hl v hv
    rw [Subgroup.mem_bot, commutatorElement_def]
    have e : v * l * v⁻¹ * l⁻¹ = (l * v * l⁻¹ * v⁻¹)⁻¹ := by group
    rw [e, h1, inv_one]
  have hbotN : ∀ X : Subgroup G, X ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
    fun X x _ => Subgroup.mem_normalizer_iff.mpr fun y => by
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro hy
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = 1 := by rw [hy]; group
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVB2
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    apply hnontriv
    have h4 : ((⊥ : Subgroup G).subgroupOf VB).index ≤ 4 := by
      rw [Subgroup.bot_subgroupOf VB, Subgroup.index_bot, hm]
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    intro l hl v hv
    exact (commutator_mem_of_perfect_of_index_le_four hLBperf hLBV (hbotN LB) (hbotN VB) h4)
      l hl v hv
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p GB) ≤ 2 := by
    intro p hp hp2
    by_contra hgt
    push Not at hgt
    obtain ⟨h3, hZ⟩ := h128 G p hp hp2
      (fun P hP hP2 => by
        rw [pRank_type_eq_open_pRank]
        exact pRank_le_two_of_isTwoLocal s.hyp.qtke hp hp2 ⟨P, hP, hP2, rfl⟩)
      GB (by rw [pRank_type_eq_open_pRank]; exact hgt)
    rw [pRank_type_eq_open_pRank] at h3
    have hmle : m ≤ CFSG.Open.pRank 2 GB :=
      le_pRank_of_isElemAbelian (by norm_num) hVBGB hVBel hm
    have hm3' : m = 3 := by omega
    have hV8 : Nat.card VB = 8 := by rw [hm, hm3']; norm_num
    obtain ⟨w₀', hw₀GB, hw₀o, hw₀c'⟩ := hZ (by rw [pRank_type_eq_open_pRank]; omega)
    set ZS := fusionZStar ↥GB with hZS
    set OC := fusionOddCore ↥GB with hOC
    have hOZ : OC ≤ ZS := by
      intro x hx
      rw [hZS, fusionZStar, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx]
      exact Subgroup.one_mem _
    have hw₀ZS : (⟨w₀', hw₀GB⟩ : ↥GB) ∈ ZS :=
      mem_fusionZStar_of_commutator_mem_oddCoreIn hw₀GB hw₀c'
    have hZSc : ∀ g : ↥GB, g ∈ ZS → ∀ h ∈ GB, h * g * h⁻¹ * (g : G)⁻¹ ∈ O := by
      intro g hg h hh
      have hc : QuotientGroup.mk' OC g ∈ Subgroup.center (↥GB ⧸ OC) := hg
      have h1 := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' OC ⟨h, hh⟩)
      have h2 : (⟨h, hh⟩ : ↥GB) * g * (⟨h, hh⟩ : ↥GB)⁻¹ * g⁻¹ ∈ OC := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        simp only [QuotientGroup.mk'_apply] at h1
        rw [h1]
        group
      exact ⟨_, h2, by simp⟩
    have hw₀sq : w₀' ^ 2 = 1 := by
      rw [← hw₀o]
      exact pow_orderOf_eq_one w₀'
    have hw₀c : ∀ h ∈ GB, h * w₀' * h⁻¹ * w₀'⁻¹ ∈ O := fun h hh => hZSc _ hw₀ZS h hh
    have hOodd : ¬ 2 ∣ Nat.card O :=
      Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp (C2Nine.odd_card_oddCoreIn GB))
    have hw₀O : w₀' ∉ O := by
      intro h
      have h2 := orderOf_dvd_natCard (⟨w₀', h⟩ : ↥O)
      rw [Subgroup.orderOf_mk, hw₀o] at h2
      exact hOodd h2
    have hVBO : VB ≤ Subgroup.normalizer (O : Set G) :=
      hVBGB.trans (C2Nine.le_normalizer_oddCoreIn GB)
    have ha : ∀ x ∈ VB, w₀'⁻¹ * (x * w₀' * x⁻¹) ∈ O := by
      intro x hx
      have h2 := (Subgroup.mem_normalizer_iff.mp
        (C2Nine.le_normalizer_oddCoreIn GB (GB.inv_mem hw₀GB)) _).mp (hw₀c x (hVBGB hx))
      have e : w₀'⁻¹ * (x * w₀' * x⁻¹ * w₀'⁻¹) * w₀'⁻¹⁻¹ = w₀'⁻¹ * (x * w₀' * x⁻¹) := by group
      rwa [e] at h2
    obtain ⟨o, hoO, hfix⟩ := exists_mul_fixed_of_isPGroup hVB2 hOodd hVBO ha
    have hoGB : o ∈ GB := C2Nine.oddCoreIn_le_self GB hoO
    set w₁ := w₀' * o with hw₁
    have hw₁GB : w₁ ∈ GB := GB.mul_mem hw₀GB hoGB
    have hw₁sq : w₁ ^ 2 ∈ O := by
      have hw₀inv : w₀'⁻¹ = w₀' := by
        rw [inv_eq_iff_mul_eq_one, ← sq, hw₀sq]
      have e : w₁ ^ 2 = (w₀' * o * w₀'⁻¹) * o := by
        rw [hw₁, sq, hw₀inv]
        group
      rw [e]
      exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp
        (C2Nine.le_normalizer_oddCoreIn GB hw₀GB) o).mp hoO) hoO
    obtain ⟨k, hk⟩ := C2Nine.odd_card_oddCoreIn GB
    set w := w₁ ^ Nat.card O with hw
    have hwsq : w ^ 2 = 1 := by
      have h1 : (⟨w₁ ^ 2, hw₁sq⟩ : ↥O) ^ Nat.card O = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
      rw [hw, ← pow_mul, mul_comm, pow_mul, h2]
    have hwO : w ∉ O := by
      intro h
      have e : w = (w₁ ^ 2) ^ k * w₁ := by rw [hw, hk, pow_succ, pow_mul]
      have hw₁O : w₁ ∈ O := by
        have : w₁ = ((w₁ ^ 2) ^ k)⁻¹ * w := by rw [e]; group
        rw [this]
        exact O.mul_mem (O.inv_mem (O.pow_mem hw₁sq k)) h
      apply hw₀O
      have : w₀' = w₁ * o⁻¹ := by rw [hw₁]; group
      rw [this]
      exact O.mul_mem hw₁O (O.inv_mem hoO)
    have hwGB : w ∈ GB := GB.pow_mem hw₁GB _
    have hwVB : ∀ x ∈ VB, x * w = w * x := by
      intro x hx
      have h1 : x * w * x⁻¹ = w := by rw [hw, ← conj_pow, hfix x hx]
      calc x * w = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [h1]
    have hw₁ZS : (⟨w₁, hw₁GB⟩ : ↥GB) ∈ ZS := by
      obtain ⟨o', ho', he⟩ := hoO
      have : (⟨w₁, hw₁GB⟩ : ↥GB) = (⟨w₀', hw₀GB⟩ : ↥GB) * o' := Subtype.ext (by
        show w₀' * o = w₀' * (o' : G)
        rw [show (o' : G) = o from he])
      rw [this]
      exact ZS.mul_mem hw₀ZS (hOZ ho')
    have hwZS : (⟨w, hwGB⟩ : ↥GB) ∈ ZS := by
      have : (⟨w, hwGB⟩ : ↥GB) = (⟨w₁, hw₁GB⟩ : ↥GB) ^ Nat.card O :=
        Subtype.ext (by simp [hw])
      rw [this]
      exact ZS.pow_mem hw₁ZS _
    by_cases hwV : w ∈ VB
    ·
      set J := VB ⊓ ZS.map GB.subtype with hJ
      have hLBJ : LB ≤ Subgroup.normalizer (J : Set G) := fun l hl =>
        A4.mem_normalizer_inf (hLBV hl) (le_normalizer_map_subtype ZS (hLBGB hl))
      rcases eq_bot_or_eq_of_card_eight hLBperf hLBV hVBcomm hV8 hVBeq J inf_le_left hLBJ with
        hJ0 | hJV
      · have hwJ : w ∈ J := ⟨hwV, ⟨⟨w, hwGB⟩, hwZS, rfl⟩⟩
        rw [hJ0, Subgroup.mem_bot] at hwJ
        exact hwO (hwJ ▸ O.one_mem)
      · apply hnontriv
        intro l hl v hv
        have hvJ : v ∈ J := by rw [hJV]; exact hv
        obtain ⟨v', hv', hvv⟩ := hvJ.2
        have h1 := hZSc v' hv' l (hLBGB hl)
        rw [show ((v' : ↥GB) : G) = v from hvv] at h1
        have h2 : l * v * l⁻¹ * v⁻¹ ∈ VB :=
          VB.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLBV hl) v).mp hv) (VB.inv_mem hv)
        have h3 : l * v * l⁻¹ * v⁻¹ ∈ O ⊓ VB := ⟨h1, h2⟩
        rw [C2Nine.oddCoreIn_inf_eq_bot hVB2 GB] at h3
        exact h3
    ·
      have hwne : w ≠ 1 := fun h => hwO (h ▸ O.one_mem)
      have hwo : orderOf w = 2 := orderOf_eq_prime hwsq hwne
      have hcv : ∀ v ∈ VB, Commute w v := fun v hv => (hwVB v hv).symm
      have hVBw : VB ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
        intro x hx
        refine Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((hcv x hx).zpow_left j).eq
      have hinf : Subgroup.zpowers w ⊓ VB = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨hy, hyV⟩
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [Subgroup.mem_bot, ← zpow_mod_orderOf, hwo]
        rw [← zpow_mod_orderOf, hwo] at hyV
        have : j % ((2 : ℕ) : ℤ) = 0 ∨ j % ((2 : ℕ) : ℤ) = 1 := by omega
        rcases this with h0 | h1
        · rw [h0, zpow_zero]
        · exfalso
          rw [h1, zpow_one] at hyV
          exact hwV hyV
      have hcardE := card_sup_mul_card_inf_of_le_normalizer hVBw
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hwo, hV8] at hcardE
      have hEcl : Subgroup.zpowers w ⊔ VB = Subgroup.closure (({w} : Set G) ∪ VB) := by
        rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, Subgroup.closure_eq]
      have hEcomm : IsMulCommutative ↥(Subgroup.zpowers w ⊔ VB) := by
        rw [hEcl]
        refine Subgroup.isMulCommutative_closure fun x hx y hy _ => ?_
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · rw [Set.mem_singleton_iff] at hx hy
          rw [hx, hy]
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hcv y hy
        · rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (hcv x hx).symm
        · exact hVBcomm x hx y hy
      have hEmem : ∀ e ∈ Subgroup.zpowers w ⊔ VB, ∃ i : ℤ, ∃ v ∈ VB, e = w ^ i * v := by
        intro e he
        have he' : e ∈ ((Subgroup.zpowers w : Subgroup G) : Set G) * (VB : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ VB hVBw]
          exact he
        obtain ⟨a, ha, v, hv, rfl⟩ := he'
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact ⟨i, v, hv, rfl⟩
      have hE : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers w ⊔ VB) := by
        refine ⟨hEcomm, fun e he => ?_⟩
        obtain ⟨i, v, hv, rfl⟩ := hEmem e he
        have hc : Commute (w ^ i) v := (hcv v hv).zpow_left i
        have h1 : (w ^ i) ^ 2 = (w ^ 2) ^ i := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        rw [hc.mul_pow, h1, hwsq, one_zpow, one_mul]
        exact (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).2.2
      have hE4 : 4 ≤ CFSG.Open.pRank 2 GB :=
        le_pRank_of_isElemAbelian (by norm_num)
          (_root_.sup_le (Subgroup.zpowers_le.mpr hwGB) hVBGB) hE (by rw [hcardE]; norm_num)
      omega
  have hcent := a126_one hLBGB (opResidual_eq_of_perfect hLBperf) hVBGB hVB2 hVBeq hrank
    (frattiniIn_eq_bot_of_isElemAbelian hVBel)
  intro y hy
  refine ⟨?_, C2Nine.oddCoreIn_le_self GB hy⟩
  apply s.normalizer_VB_le hU
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.mp (hcent hv)) y hy).symm

end CFSG.Quasithin.H13.Ch4
