module

public import CFSG.Quasithin.H13.L32A721b
public import CFSG.Quasithin.H13.L32A720e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_pCoreOf_oTwoUpper (H₀ : Subgroup G) :
    H₀ ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H₀) : Set G) := by
  intro g hg
  rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
  exact mem_normalizer_inf_of_mem (le_normalizer_oTwoUpper _ hg) (le_normalizer_pCoreOf 2 _ hg)

omit [Finite G] in
theorem le_normalizer_inf_centralizer {P H₀ : Subgroup G}
    (hP : H₀ ≤ Subgroup.normalizer (P : Set G)) :
    H₀ ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_forall_conj (R := P ⊓ Subgroup.centralizer (P : Set G))
    (fun x hx c hc => ?_) hg
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hP hx) c).mp
    (Subgroup.mem_inf.mp hc).1, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have hp' : x⁻¹ * p * x ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (hP (inv_mem hx)) p).mp hp
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hp'
  calc p * (x * c * x⁻¹) = x * ((x⁻¹ * p * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * p * x)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * p := by group

end General

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

omit E in
theorem commutator_le_bot_of_le_v1 {Y : Subgroup G} (hYQ : Y ≤ pCoreOf 2 (hz T V))
    (hYn : hz T V ≤ Subgroup.normalizer (Y : Set G))
    (h1 : ⁅Y, oTwoUpper (hz T V)⁆ ≤ fsuV1 T V) : ⁅Y, oTwoUpper (hz T V)⁆ ≤ ⊥ := by
  have hN : hz T V ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  refine commutator_le_of_series (Y₀ := Y ⊓ fsuV1 T V) inf_le_left hYQ hN hYn
    (le_inf (commutator_le_self hYn) h1) ?_
  rw [Subgroup.commutator_le]
  intro a ha c hc
  have hca : a * c = c * a :=
    Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ hc) a (Subgroup.mem_inf.mp ha).2
  rw [Subgroup.mem_bot, commutatorElement_def, hca]
  group

variable (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include hF

theorem exists_pow_mul {x : G} (hxL : x ∈ l1 T L V) (hxH : x ∈ hz T V) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {l : G} (hl : l ∈ l1 T L V) :
    ∃ j : ℕ, (x ^ j)⁻¹ * l ∈ pCoreOf 2 (oTwoUpper (hz T V)) := by
  have hzp := E.zpowers_eq_l1dot hxL hxH hx3 hx1
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  subst hH
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hlH : l ∈ hz T V := oTwoUpper_le _ (hL1K hl)
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨l, hlH⟩ : ↥(hz T V)) ∈
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) (⟨x, hxH⟩ : ↥(hz T V))) := by
    rw [hzp]
    exact mem_modO2Image_iff.mpr ⟨⟨l, hlH⟩, hl, rfl⟩
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  refine ⟨j, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hj
  have hq : (x ^ j)⁻¹ * l ∈ pCoreOf 2 (hz T V) := by
    have := C2Six.mem_pCore_two_iff.mp hj
    simpa using this
  rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
  exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (pow_mem (hL1K hxL) j)) (hL1K hl), hq⟩

theorem false_of_cover (h13314 : A6.Stmt13_3_14) (hC137 : U3.C137Statement)
    {W₁ W₂ : Subgroup G} (hW₂W₁ : W₂ ≤ W₁)
    (hW₁n : hz T V ≤ Subgroup.normalizer (W₁ : Set G))
    (hW₂n : hz T V ≤ Subgroup.normalizer (W₂ : Set G)) (h64 : W₂.relIndex W₁ = 64)
    (hsec' : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₂ ∧ x ^ 2 ∈ W₂)
    (hirr : ∀ X : Subgroup G, W₂ ≤ X → X ≤ W₁ →
      oTwoUpper (hz T V) ≤ Subgroup.normalizer (X : Set G) → X = W₂ ∨ X = W₁)
    (hfaith : ∀ x ∈ hz T V, (∀ w ∈ W₁, x * w * x⁻¹ * w⁻¹ ∈ W₂) → x ∈ pCoreOf 2 (hz T V))
    (hW₂K : ⁅W₂, oTwoUpper (hz T V)⁆ ≤ fsuU T V)
    (hcov : (pCoreOf 2 (oTwoUpper (hz T V)) ⊓
      Subgroup.centralizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G)) ⊓ W₁ ⊔ W₂ = W₁) :
    False := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  have hnot : ¬ hz T V ≤ Subgroup.normalizer (L : Set G) := hH ▸ E.S.hz.2.2
  obtain ⟨x, hxL, hxH, hx3, hx1⟩ := E.exists_three
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hL1H : l1 T L V ≤ hz T V := hL1K.trans E.k_le_hz
  have hxK : x ∈ oTwoUpper (hz T V) := hH ▸ hL1K hxL
  have hsec : IsElemSection W₁ W₂ := ⟨hW₂W₁, hsec'⟩
  have hlt : W₂ < W₁ := lt_of_le_of_ne hW₂W₁ fun e => by
    rw [e, Subgroup.relIndex_self] at h64
    omega
  have hchief : ∀ X : Subgroup G, W₂ ≤ X → X ≤ W₁ →
      hz T V ≤ Subgroup.normalizer (X : Set G) → X = W₂ ∨ X = W₁ := fun X h1 h2 h3 =>
    hirr X h1 h2 fun c hc => h3 (oTwoUpper_le _ hc)
  have hQW : ∀ q ∈ pCoreOf 2 (hz T V), ∀ w ∈ W₁, q * w * q⁻¹ * w⁻¹ ∈ W₂ := fun q hq =>
    (SecW.act_eq_one_iff hsec _).mp (act_eq_one_of_chief hsec hlt hW₁n hW₂n hchief hq)
  set Z₁ := (pCoreOf 2 (oTwoUpper (hz T V)) ⊓
    Subgroup.centralizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G)) ⊓ W₁ with hZ₁
  have hZpn := le_normalizer_inf_centralizer (le_normalizer_pCoreOf_oTwoUpper (hz T V))
  have hZ₁n : hz T V ≤ Subgroup.normalizer (Z₁ : Set G) := fun g hg =>
    mem_normalizer_inf_of_mem (hZpn hg) (hW₁n hg)
  have hZ₁c : ∀ a ∈ Z₁, ∀ b ∈ Z₁, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2 a
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1
  have hZ₁Q : Z₁ ≤ pCoreOf 2 (hz T V) := fun z hz =>
    pCoreOf_oTwoUpper_le _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).1).1
  have hZ₁2 : IsPGroup 2 ↥Z₁ := (pCoreOf_isPGroup 2 _).to_le hZ₁Q
  have hxZ₁ := hZ₁n hxH
  set V' := ⁅Z₁, l1 T L V⁆ with hV'
  have hV'Z : V' ≤ Z₁ := by
    rw [hV', Subgroup.commutator_le]
    intro z hz l hl
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc l]
    exact mul_mem hz ((Subgroup.mem_normalizer_iff.mp (hZ₁n (hL1H hl)) _).mp (inv_mem hz))
  have hV'W₁ : V' ≤ W₁ := hV'Z.trans inf_le_right
  have hV'n : hz T V ≤ Subgroup.normalizer (V' : Set G) := fun g hg =>
    mem_normalizer_commutator (hZ₁n hg) (E.hz_le_normalizer_l1 hg)
  set δ := commHom hZ₁c hxZ₁ with hδ
  have hrep : ∀ j : ℕ, ∀ w ∈ Z₁, x ^ j * w * (x ^ j)⁻¹ * w⁻¹ ∈ δ.range.map Z₁.subtype := by
    intro j
    induction j with
    | zero =>
      intro w _
      rw [pow_zero, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    | succ j ih =>
      intro w hw
      have hu : x ^ j * w * (x ^ j)⁻¹ ∈ Z₁ :=
        (Subgroup.mem_normalizer_iff.mp (pow_mem hxZ₁ j) w).mp hw
      have h1 : x * (x ^ j * w * (x ^ j)⁻¹) * x⁻¹ * (x ^ j * w * (x ^ j)⁻¹)⁻¹ ∈
          δ.range.map Z₁.subtype := ⟨δ ⟨_, hu⟩, ⟨_, rfl⟩, rfl⟩
      have e : x ^ (j + 1) * w * (x ^ (j + 1))⁻¹ * w⁻¹ =
          (x * (x ^ j * w * (x ^ j)⁻¹) * x⁻¹ * (x ^ j * w * (x ^ j)⁻¹)⁻¹) *
            (x ^ j * w * (x ^ j)⁻¹ * w⁻¹) := by
        rw [pow_succ']
        group
      rw [e]
      exact mul_mem h1 (ih w hw)
  have hV'R : V' ≤ δ.range.map Z₁.subtype := by
    rw [hV', Subgroup.commutator_le]
    intro z hz l hl
    obtain ⟨j, hj⟩ := E.exists_pow_mul hF hxL hxH hx3 hx1 hl
    set q := (x ^ j)⁻¹ * l with hq
    have hl' : l = x ^ j * q := by rw [hq]; group
    have hzq : q * z⁻¹ = z⁻¹ * q :=
      Subgroup.mem_centralizer_iff.mp
        (inv_mem (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).1).2) q hj
    have hw : x ^ j * z⁻¹ * (x ^ j)⁻¹ ∈ Z₁ :=
      (Subgroup.mem_normalizer_iff.mp (pow_mem hxZ₁ j) _).mp (inv_mem hz)
    have e : ⁅z, l⁆ = x ^ j * z⁻¹ * (x ^ j)⁻¹ * z⁻¹⁻¹ := by
      rw [commutatorElement_def, hl']
      calc z * (x ^ j * q) * z⁻¹ * (x ^ j * q)⁻¹ =
          z * (x ^ j * (q * z⁻¹) * q⁻¹ * (x ^ j)⁻¹) := by group
        _ = z * (x ^ j * (z⁻¹ * q) * q⁻¹ * (x ^ j)⁻¹) := by rw [hzq]
        _ = z * (x ^ j * z⁻¹ * (x ^ j)⁻¹) := by group
        _ = (x ^ j * z⁻¹ * (x ^ j)⁻¹) * z := hZ₁c _ hz _ hw
        _ = x ^ j * z⁻¹ * (x ^ j)⁻¹ * z⁻¹⁻¹ := by rw [inv_inv]
    rw [e]
    exact hrep j _ (inv_mem hz)
  have hfpf : ∀ v ∈ V', x * v * x⁻¹ = v → v = 1 := by
    intro v hv hxv
    obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := hV'R hv
    exact comm_eq_one_of_fix_of_isPGroup hZ₁2 hxZ₁ u.2 (by rw [hx3]; group) hxv
  have hV1U : fsuV1 T V ≤ fsuU T V := (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _)
  have hU2 : ∀ a ∈ fsuV1 T V, a * a = 1 := fun a ha => by
    rw [← sq]
    exact F7.isElemAbelian_pow_eq_one (isElemAbelian_fsuU_of E.S.hyp hMod) (hV1U ha)
  have hV'W₂ : ∀ v ∈ V', v ∈ W₂ → v = 1 := by
    intro v hv hvW
    set a := v * x * v⁻¹ * x⁻¹ with ha
    have haU : a ∈ fsuU T V := by
      have := hW₂K (Subgroup.commutator_mem_commutator hvW hxK)
      rwa [commutatorElement_def] at this
    have haV' : a ∈ V' := by
      rw [ha, mul_assoc, mul_assoc, ← mul_assoc x]
      exact mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hV'n hxH) _).mp (inv_mem hv))
    have haV1 : a ∈ fsuV1 T V := by
      have := Subgroup.mem_inf.mpr ⟨haU,
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hV'Z haV')).1).2⟩
      rwa [E.inf_centralizer_p hF h13314] at this
    have hax : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxH a haV1
    have hxa : x * a⁻¹ * x⁻¹ = a⁻¹ := by
      calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
        _ = (a * x * x⁻¹)⁻¹ := by rw [hax]
        _ = a⁻¹ := by group
    have hxv : x * v * x⁻¹ = a⁻¹ * v := by rw [ha]; group
    have h3 : x ^ 3 * v * (x ^ 3)⁻¹ = a⁻¹ * (a⁻¹ * (a⁻¹ * v)) := by
      calc x ^ 3 * v * (x ^ 3)⁻¹ = x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ := by
            rw [pow_three]; group
        _ = x * (x * (a⁻¹ * v) * x⁻¹) * x⁻¹ := by rw [hxv]
        _ = x * ((x * a⁻¹ * x⁻¹) * (x * v * x⁻¹)) * x⁻¹ := by group
        _ = x * (a⁻¹ * (a⁻¹ * v)) * x⁻¹ := by rw [hxa, hxv]
        _ = (x * a⁻¹ * x⁻¹) * ((x * a⁻¹ * x⁻¹) * (x * v * x⁻¹)) := by group
        _ = a⁻¹ * (a⁻¹ * (a⁻¹ * v)) := by rw [hxa, hxv]
    rw [hx3] at h3
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hU2 a haV1)
    have ha1 : a = 1 := by
      have h4 : a * (a * a) = 1 := by
        calc a * (a * a) = a⁻¹ * (a⁻¹ * (a⁻¹ * v)) * v⁻¹ := by rw [hai]; group
          _ = 1 := by rw [← h3]; group
      rwa [hU2 a haV1, mul_one] at h4
    exact hfpf v hv (by rw [hxv, ha1]; group)
  have hV'X : V' ⊔ W₂ = W₁ := by
    rcases hirr (V' ⊔ W₂) le_sup_right (sup_le hV'W₁ hW₂W₁) (fun c hc =>
      mem_normalizer_sup_of (hV'n (oTwoUpper_le _ hc)) (hW₂n (oTwoUpper_le _ hc))) with he | he
    · exfalso
      have hV'W₂' : V' ≤ W₂ := le_sup_left.trans he.le
      have hxW : ∀ w ∈ W₁, x * w * x⁻¹ * w⁻¹ ∈ W₂ :=
        comm_mem_of_sup_eq hsec (hW₁n hxH) (hW₂n hxH) inf_le_right hcov fun f hf => by
          have h1 : ⁅f, x⁆ ∈ V' := Subgroup.commutator_mem_commutator hf hxL
          have h2 := hV'W₂' (inv_mem h1)
          rw [commutatorElement_def] at h2
          have e : (f * x * f⁻¹ * x⁻¹)⁻¹ = x * f * x⁻¹ * f⁻¹ := by group
          rwa [e] at h2
      have hxQ := hfaith x hxH hxW
      obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨x, hxQ⟩
      have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
      have := pow_gcd_eq_one.mpr ⟨hx3, hxn⟩
      rw [hcop.gcd_eq_one, pow_one] at this
      exact hx1 this
    · exact he
  have hV'e : IsElemAbelian 2 V' :=
    ⟨⟨⟨fun u w => Subtype.ext (hZ₁c u (hV'Z u.2) w (hV'Z w.2))⟩⟩, fun v hv =>
      hV'W₂ _ (pow_mem hv 2) (hsec.sq (hV'W₁ hv))⟩
  have hpre : SecW.pre hsec (SecW.img hsec V') = W₁ := by
    refine le_antisymm (SecW.pre_le hsec _) (hV'X.symm.le.trans ?_)
    exact sup_le (fun v hv => (SecW.mem_pre hsec).mpr ⟨hV'W₁ hv, SecW.mk_mem_img hsec hv⟩)
      (SecW.le_pre hsec _)
  have himg : SecW.img hsec V' = ⊤ := by
    rw [← SecW.img_pre hsec (SecW.img hsec V'), hpre]
    exact (SecW.img_eq_top_iff hsec hsec.le le_rfl).mpr rfl
  have hc1 := SecW.card_img hsec hV'W₁
  rw [himg, Subgroup.card_top, SecW.card, h64] at hc1
  have hc2 := Subgroup.relIndex_mul_card W₂ V'
  have hpos : 0 < Nat.card ↥(W₂ ⊓ V') := Nat.card_pos
  rw [← hc1] at hc2
  have hQC : pCoreOf 2 (hz T V) ≤ Subgroup.centralizer (V' : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hQW q hq v (hV'W₁ hv)
    have h2 : q * v * q⁻¹ * v⁻¹ ∈ V' := mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hV'n (pCoreOf_le 2 _ hq)) v).mp hv) (inv_mem hv)
    have h3 := hV'W₂ _ h2 h1
    calc v * q = (q * v * q⁻¹ * v⁻¹)⁻¹ * q * v := by group
      _ = q * v := by rw [h3, inv_one, one_mul]
  have hCQ : hz T V ⊓ Subgroup.centralizer (V' : Set G) ≤ pCoreOf 2 (hz T V) := by
    intro g hg
    obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp hg
    refine hfaith g hgH (comm_mem_of_sup_eq hsec (hW₁n hgH) (hW₂n hgH) hV'W₁ hV'X
      fun f hf => ?_)
    have hfg : f * g = g * f := Subgroup.mem_centralizer_iff.mp hgC f hf
    have e : g * f * g⁻¹ * f⁻¹ = 1 := by rw [← hfg]; group
    rw [e]
    exact one_mem _
  have hV'R₁ : V' ≤ pCoreOf 2 (l1 T L V ⊔ T) := fun v hv => E.qh_le_r1.1 (hZ₁Q (hV'Z hv))
  have hN := E.hz_le_normalizer_baum hxL hxH hx3 hx1 hV'e hV'R₁ (by omega) hV'n hQC hCQ hfpf
  exact hnot (hN.trans (E.normalizer_baum_le hF hC137))

theorem center_p {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k) (h13314 : A6.Stmt13_3_14) (hC137 : U3.C137Statement) :
    ∀ x ∈ pCoreOf 2 (oTwoUpper (hz T V)),
      (∀ y ∈ pCoreOf 2 (oTwoUpper (hz T V)), x * y = y * x) →
        ∀ c ∈ oTwoUpper (hz T V), x * c = c * x := by
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  have hV1n : hz T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hH ▸ E.S.hz.2.1
  set Zp := pCoreOf 2 (oTwoUpper (hz T V)) ⊓
    Subgroup.centralizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G) with hZp
  have hZpn : hz T V ≤ Subgroup.normalizer (Zp : Set G) :=
    le_normalizer_inf_centralizer (le_normalizer_pCoreOf_oTwoUpper (hz T V))
  have hZpQ : Zp ≤ pCoreOf 2 (hz T V) := inf_le_left.trans (pCoreOf_oTwoUpper_le _)
  have hZpC : Zp ≤ hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G) :=
    le_inf (hZpQ.trans (pCoreOf_le 2 _)) fun z hz => Subgroup.mem_centralizer_iff.mpr
      fun u hu => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 u (E.u_le_p hF hu)
  have hU1 : ∀ w ∈ Zp, w ∈ fsuU T V → w ∈ fsuV1 T V := fun w hw hwU => by
    have := Subgroup.mem_inf.mpr ⟨hwU, (Subgroup.mem_inf.mp hw).2⟩
    rwa [E.inf_centralizer_p hF h13314] at this
  have hZK : ⁅Zp, oTwoUpper (hz T V)⁆ ≤ Zp := commutator_le_self hZpn
  have hfin : ⁅Zp, oTwoUpper (hz T V)⁆ ≤ ⊥ := by
    rcases E.cases_720 hF N with hi | ⟨W₁, W₂, -, hW₂W₁, -, hW₁n, hW₂n, h64, hsec', hirr,
      hfaith, hW₂K, hCK⟩
    · exact commutator_le_bot_of_le_v1 hZpQ hZpn fun w hw =>
        hU1 w (hZK hw) (hi (Subgroup.commutator_mono hZpC le_rfl hw))
    · by_cases hcov : Zp ⊓ W₁ ≤ W₂
      · have h1 : ⁅Zp, oTwoUpper (hz T V)⁆ ≤ Zp ⊓ W₂ := le_inf hZK
          ((le_inf hZK (hCK.trans' (Subgroup.commutator_mono hZpC le_rfl))).trans hcov)
        have h2 : ⁅Zp ⊓ W₂, oTwoUpper (hz T V)⁆ ≤ fsuV1 T V := fun w hw =>
          hU1 w (hZK (Subgroup.commutator_mono inf_le_left le_rfl hw))
            (hW₂K (Subgroup.commutator_mono inf_le_right le_rfl hw))
        exact commutator_le_bot_of_le_v1 hZpQ hZpn
          (commutator_le_of_series inf_le_left hZpQ hV1n hZpn h1 h2)
      · exfalso
        refine E.false_of_cover hF h13314 hC137 hW₂W₁ hW₁n hW₂n h64 hsec' hirr hfaith hW₂K ?_
        rcases hirr (Zp ⊓ W₁ ⊔ W₂) le_sup_right (sup_le inf_le_right hW₂W₁) (fun c hc =>
          mem_normalizer_sup_of (mem_normalizer_inf_of_mem (hZpn (oTwoUpper_le _ hc))
            (hW₁n (oTwoUpper_le _ hc))) (hW₂n (oTwoUpper_le _ hc))) with he | he
        · exact absurd (le_sup_left.trans he.le) hcov
        · exact he
  intro z hzP hzc c hc
  have hz : z ∈ Zp := Subgroup.mem_inf.mpr ⟨hzP, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (hzc y hy).symm⟩
  have h1 := hfin (Subgroup.commutator_mem_commutator hz hc)
  rw [Subgroup.mem_bot, commutatorElement_def] at h1
  calc z * c = z * c * z⁻¹ * c⁻¹ * (c * z) := by group
    _ = c * z := by rw [h1, one_mul]

end Ctx7153

end CFSG.Quasithin.H13.L32A
