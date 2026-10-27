module

public import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofKFact
public import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
public import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace Item181ThreeProof

theorem closure_odd_eq_top {P : Type*} [Group P] [Finite P] [Group.IsPerfect P] :
    Subgroup.closure {x : P | Odd (orderOf x)} = ⊤ := by
  set K := Subgroup.closure {x : P | Odd (orderOf x)} with hK
  have hKn : K.Normal := by
    constructor
    intro x hx g
    have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
      rw [hK, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, hy, rfl⟩
      change Odd (orderOf ((MulAut.conj g) y))
      rw [MulEquiv.orderOf_eq]
      exact hy
    exact hle ⟨x, hx, rfl⟩
  have h2 : IsPGroup 2 (P ⧸ K) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply Subgroup.subset_closure
    change Odd (orderOf (x ^ 2 ^ a))
    rw [orderOf_pow' x (by positivity), hord, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  by_contra hne
  have : Nontrivial (P ⧸ K) := QuotientGroup.nontrivial_iff.mpr hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (P ⧸ K) := h2.isNilpotent
  exact Group.IsPerfect.not_isSolvable (P ⧸ K) inferInstance

theorem exists_odd_of_not_centralizes {Ĝ : Type*} [Group Ĝ] [Finite Ĝ] {W : Subgroup Ĝ}
    (h : ∃ l ∈ perfectResidual Ĝ, ∃ w ∈ W, l * w * l⁻¹ ≠ w) :
    ∃ l ∈ perfectResidual Ĝ, Odd (orderOf l) ∧ ∃ w ∈ W, l * w * l⁻¹ ≠ w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨l, hl, w, hw, hlw⟩ := h
  have : Group.IsPerfect (perfectResidual Ĝ) :=
    (CFSG.perfect_residual_characterization (G := Ĝ)).2.2.1
  set C : Subgroup (perfectResidual Ĝ) :=
    (Subgroup.centralizer (W : Set Ĝ)).subgroupOf (perfectResidual Ĝ) with hC
  have hle : Subgroup.closure {x : perfectResidual Ĝ | Odd (orderOf x)} ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro w' hw'
    have hx' : Odd (orderOf (x : Ĝ)) := by rw [Subgroup.orderOf_coe]; exact hx
    have := hcon x x.2 hx' w' hw'
    calc w' * x = x * w' * (x : Ĝ)⁻¹ * x := by rw [this]
      _ = x * w' := by group
  rw [closure_odd_eq_top] at hle
  have hlC : (⟨l, hl⟩ : perfectResidual Ĝ) ∈ C := hle (Subgroup.mem_top _)
  rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hlC
  apply hlw
  have := hlC w hw
  calc l * w * l⁻¹ = w * l * l⁻¹ := by rw [← this]
    _ = w := by group

theorem section_bound {Ĝ : Type} [Group Ĝ] [Finite Ĝ] {Q : Subgroup Ĝ} [Q.Normal] (t : Ĝ)
    (k : ℕ)
    (hmod : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ ρ : Ĝ ⧸ Q →* MulAut V, (∃ l ∈ perfectResidual Ĝ, ρ (l : Ĝ ⧸ Q) ≠ 1) →
        k ≤ Nat.card (Sec3.commHom (ρ (t : Ĝ ⧸ Q))).range)
    (W : Subgroup Ĝ) [W.Normal] (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ w ∈ W, w * w = 1)
    (hA : ∃ l ∈ perfectResidual Ĝ, ∃ w ∈ W, l * w * l⁻¹ * w⁻¹ ∉ ⁅W, Q⁆) :
    k ≤ (Subgroup.centralizer ({t} : Set Ĝ)).relIndex W := by
  classical
  have : (⁅W, Q⁆).Normal := Subgroup.commutator_normal W Q
  set N := (⁅W, Q⁆).subgroupOf W with hN
  let _ : CommGroup (W ⧸ N) := { (inferInstance : Group (W ⧸ N)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hWc a a.2 b b.2) }
  set ρ₀ := Sec3.sectionAction W ⁅W, Q⁆ with hρ₀
  have hQtriv : Q ≤ ρ₀.ker := fun q hq => MonoidHom.mem_ker.mpr
    (Sec3.sectionAction_eq_one W ⁅W, Q⁆ (fun w hw => by
      have hc := Subgroup.commutator_mem_commutator hw hq
      have h2 : q * w * q⁻¹ * w⁻¹ = (⁅w, q⁆)⁻¹ := by rw [commutatorElement_def]; group
      rw [h2]
      exact Subgroup.inv_mem _ hc))
  set ρ : Ĝ ⧸ Q →* MulAut (W ⧸ N) := QuotientGroup.lift Q ρ₀ hQtriv with hρ
  have hρmk : ∀ g : Ĝ, ρ (g : Ĝ ⧸ Q) = ρ₀ g := fun g => QuotientGroup.lift_mk Q hQtriv g
  have hV2 : ∀ v : W ⧸ N, v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
    rw [← QuotientGroup.mk_mul, show w * w = 1 from Subtype.ext (hW2 w w.2),
      QuotientGroup.mk_one]
  have hne : ∃ l ∈ perfectResidual Ĝ, ρ (l : Ĝ ⧸ Q) ≠ 1 := by
    obtain ⟨l, hl, w₀, hw₀, hlw₀⟩ := hA
    refine ⟨l, hl, fun h => hlw₀ ?_⟩
    rw [hρmk] at h
    have h' := congrArg (fun φ : MulAut (W ⧸ N) => φ (QuotientGroup.mk ⟨w₀, hw₀⟩)) h
    simp only [MulAut.one_apply] at h'
    rw [Sec3.sectionAction_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
    change (l * w₀ * l⁻¹)⁻¹ * w₀ ∈ ⁅W, Q⁆ at h'
    have h2 : l * w₀ * l⁻¹ * w₀⁻¹ =
        (l * w₀ * l⁻¹) * ((l * w₀ * l⁻¹)⁻¹ * w₀)⁻¹ * (l * w₀ * l⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ h') _
  have hk := hmod (W ⧸ N) hV2 ρ hne
  rw [hρmk] at hk
  have hrange : Nat.card (Sec3.commHom (ρ₀ t)).range ≤
      (Subgroup.centralizer ({t} : Set Ĝ)).relIndex W := by
    rw [Sec3.relIndex_centralizer_eq_card_range hWc t]
    have hle : (Sec3.commHom (ρ₀ t)).range ≤
        ((Sec3.conjCommHom hWc t).range).map (QuotientGroup.mk' N) := by
      rintro _ ⟨v, rfl⟩
      induction v using QuotientGroup.induction_on with
      | H w =>
      refine ⟨Sec3.conjCommHom hWc t w, ⟨w, rfl⟩, ?_⟩
      rw [QuotientGroup.mk'_apply, Sec3.commHom_apply, Sec3.sectionAction_mk,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
    exact (Subgroup.card_le_of_le hle).trans (Sec3.card_map_le_card _ _)
  exact hk.trans hrange

theorem le_relIndex_of_quotient_bound {Ĝ : Type} [Group Ĝ] [Finite Ĝ] {Q : Subgroup Ĝ}
    [Q.Normal] (hQ : IsPGroup 2 Q) (t : Ĝ) (k : ℕ)
    (hmod : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ ρ : Ĝ ⧸ Q →* MulAut V, (∃ l ∈ perfectResidual Ĝ, ρ (l : Ĝ ⧸ Q) ≠ 1) →
        k ≤ Nat.card (Sec3.commHom (ρ (t : Ĝ ⧸ Q))).range)
    (W : Subgroup Ĝ) (hWn : W.Normal) (hWQ : W ≤ Q) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ w ∈ W, w * w = 1)
    (hLW : ∃ l ∈ perfectResidual Ĝ, Odd (orderOf l) ∧ ∃ w ∈ W, l * w * l⁻¹ ≠ w) :
    k ≤ (Subgroup.centralizer ({t} : Set Ĝ)).relIndex W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hn : Nat.card W using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  by_cases hA : ∃ l ∈ perfectResidual Ĝ, ∃ w ∈ W, l * w * l⁻¹ * w⁻¹ ∉ ⁅W, Q⁆
  · exact section_bound t k hmod W hWc hW2 hA
  push Not at hA
  obtain ⟨l, hlL, hlodd, w, hw, hlw⟩ := hLW
  have hW'W : ⁅W, Q⁆ ≤ W := Subgroup.commutator_le_left W Q
  have hBW' : ∃ w ∈ ⁅W, Q⁆, l * w * l⁻¹ ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hlw (Sec3.commute_of_odd_of_stabilizes (hQ.to_le hWQ) hW'W hlodd
      (fun p hp => hA l hlL p hp) (fun w hw => hcon w hw) hw)
  have hW1 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hw
    exact hlw (by rw [hw, mul_one, mul_inv_cancel])
  have hlt : ⁅W, Q⁆ < W := Sec3.commutator_lt_self hQ hWQ hW1
  have hcard : Nat.card ↥⁅W, Q⁆ < n := hn ▸ Subgroup.card_lt_of_lt hlt
  have := ih _ hcard ⁅W, Q⁆ (Subgroup.commutator_normal W Q) (hW'W.trans hWQ)
    (fun a ha b hb => hWc a (hW'W ha) b (hW'W hb)) (fun w hw => hW2 w (hW'W hw))
    ⟨l, hlL, hlodd, hBW'⟩ rfl
  exact this.trans (Subgroup.relIndex_le_of_le_right hW'W (Sec3.relIndex_ne_zero_of_finite _ _))

variable {G : Type} [Group G] [Finite G]

theorem map_perfectResidual_eq' {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {f : X →* Y} (hf : Function.Surjective f) :
    (perfectResidual X).map f = perfectResidual Y := by
  refine le_antisymm (map_perfectResidual_le f) ?_
  have hXc := CFSG.perfect_residual_characterization (G := X)
  have : (perfectResidual X).Characteristic := hXc.2.1
  have hn : ((perfectResidual X).map f).Normal :=
    (inferInstance : (perfectResidual X).Normal).map f hf
  have hs : Group.IsSolvable (Y ⧸ (perfectResidual X).map f) := by
    have := hXc.2.2.2.1
    refine Group.isSolvable_of_surjective
      (f := QuotientGroup.map _ _ f (Subgroup.le_comap_map f (perfectResidual X))) ?_
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩
  exact ((CFSG.perfect_residual_characterization (G := Y)).2.2.2.2.1 _).mp hs

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf' {p : ℕ} {X : Subgroup G} (x : X) :
    x ∈ CFSG.pCore p X ↔ (x : G) ∈ CFSG.Open.pCoreOf p X := (CFSG.mem_openPCoreOf_iff x).symm

theorem nonempty_quotient_mulEquiv_perfectResidual (H : Subgroup G) :
    Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
      perfectResidual (H ⧸ CFSG.pCore 2 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hLdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set φ : L →* H ⧸ CFSG.pCore 2 H := π.comp (Subgroup.inclusion hLH) with hφ
  have hmem : ∀ x : L, φ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 H := by
    intro x
    rw [hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_pCoreOf']
    rfl
  have hLsub : L.subgroupOf H = perfectResidual H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hrange : φ.range = perfectResidual (H ⧸ CFSG.pCore 2 H) := by
    rw [← map_perfectResidual_eq' (QuotientGroup.mk'_surjective (CFSG.pCore 2 H)), ← hLsub]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLH x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 L := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, ?_⟩
      have himg : φ.ker.map L.subtype ≤ CFSG.Open.pCoreOf 2 H := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hmem x).mp hx
      exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le himg).of_equiv
        (φ.ker.equivMapOfInjective _ L.subtype_injective).symm
    · intro x hx
      rw [MonoidHom.mem_ker, hmem]
      exact hO ((mem_pCore_iff_mem_pCoreOf' x).mp hx)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem quotient_bound
    (hK : KFacts.KS181GraphFieldModule) {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) {s : G} (hs : Sec4.Concl4442 A M H s) (hsH : s ∈ H)
    (V : Type) [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1)
    (ρ : H ⧸ CFSG.pCore 2 H →* MulAut V)
    (hρ : ∃ y ∈ perfectResidual (H ⧸ CFSG.pCore 2 H), ρ y ≠ 1) :
    4 ≤ Nat.card (Sec3.commHom (ρ (QuotientGroup.mk' (CFSG.pCore 2 H) ⟨s, hsH⟩))).range ∧
      (Nonempty (perfectResidual (H ⧸ CFSG.pCore 2 H) ≃* projSL 3 (GaloisField 2 2)) →
        16 ≤ Nat.card (Sec3.commHom (ρ (QuotientGroup.mk' (CFSG.pCore 2 H) ⟨s, hsH⟩))).range) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨hsS, hsA, -, hsH', X, hXn, hX, hXt, htX⟩ := hs
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set t : H ⧸ CFSG.pCore 2 H := π ⟨s, hsH⟩ with ht
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
      have : a ^ 3 = 1 :=
        Subtype.ext (by simpa using (isE27_subgroupOf hA hAH).1.2 (a : H) a.2)
      rw [this, map_one]
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
  exact hK _ X t E hO2 hXn hX htX hXt ht2 hEX hEab hE27 hEt hnoB V hV2 ρ hρ

omit [Finite G] in
theorem relIndex_centralizer_subgroupOf {H W : Subgroup G} (hWH : W ≤ H) {a : G} (ha : a ∈ H) :
    (Subgroup.centralizer ({(⟨a, ha⟩ : H)} : Set H)).relIndex (W.subgroupOf H) =
      (Subgroup.centralizer ({a} : Set G)).relIndex W := by
  have hC : Subgroup.centralizer ({(⟨a, ha⟩ : H)} : Set H) =
      (Subgroup.centralizer ({a} : Set G)).subgroupOf H := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  rw [hC, Subgroup.relIndex_subgroupOf hWH]

theorem moduleBound_of_kfact
    (hK : KFacts.KS181GraphFieldModule) {A M H : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) {s : G} (hs : Sec4.Concl4442 A M H s)
    (hrel : (CFSG.Open.pCoreOf 2 H).relIndex (CFSG.Open.pCoreOf 2 (H ⊓ M)) = 2) :
    ModuleBound H (CFSG.Open.pCoreOf 2 H) (CFSG.Open.pCoreOf 2 (H ⊓ M))
        (inSubgroup perfectResidual H) 4 ∧
      (Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
          projSL 3 (GaloisField 2 2)) →
        ModuleBound H (CFSG.Open.pCoreOf 2 H) (CFSG.Open.pCoreOf 2 (H ⊓ M))
          (inSubgroup perfectResidual H) 16) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsS := hs.1
  obtain ⟨hsH, X, -, -, -, htX⟩ := hs.2.2.2
  set Q := CFSG.Open.pCoreOf 2 H with hQdef
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  have hSH : S ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hsQ : s ∉ Q := by
    intro hsQ'
    apply htX
    have : QuotientGroup.mk' (CFSG.pCore 2 H) (⟨s, hsH⟩ : H) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf']
      exact hsQ'
    rw [this]
    exact X.one_mem
  have key : ∀ k : ℕ, (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ ρ : H ⧸ CFSG.pCore 2 H →* MulAut V,
        (∃ y ∈ perfectResidual (H ⧸ CFSG.pCore 2 H), ρ y ≠ 1) →
        k ≤ Nat.card (Sec3.commHom (ρ (QuotientGroup.mk' (CFSG.pCore 2 H) ⟨s, hsH⟩))).range) →
      ModuleBound H Q S (inSubgroup perfectResidual H) k := by
    intro k hk W hWQ hHW hW hLW a haS haQ
    have haH : a ∈ H := hSH haS
    have hsa : a⁻¹ * s ∈ Q := inv_mul_mem_of_relIndex_eq_two hrel haS hsS haQ hsQ
    have himg : ((⟨a, haH⟩ : H) : H ⧸ CFSG.pCore 2 H) =
        QuotientGroup.mk' (CFSG.pCore 2 H) ⟨s, hsH⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf']
      exact hsa
    set Ŵ := W.subgroupOf H with hŴ
    have hWH : W ≤ H := hWQ.trans hQH
    have hŴn : Ŵ.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr fun x hx =>
        Sec3.mem_normalizer_of_conj_mem fun w hw => hHW x hx w hw
    have hŴQ : Ŵ ≤ CFSG.pCore 2 H := fun x hx =>
      (mem_pCore_iff_mem_pCoreOf' x).mpr (hWQ (Subgroup.mem_subgroupOf.mp hx))
    have hŴc : ∀ x ∈ Ŵ, ∀ y ∈ Ŵ, x * y = y * x := fun x hx y hy =>
      Subtype.ext (hW.1 _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
    have hŴ2 : ∀ x ∈ Ŵ, x * x = 1 := fun x hx =>
      Subtype.ext (hW.2 _ (Subgroup.mem_subgroupOf.mp hx))
    have hLŴ : ∃ l ∈ perfectResidual H, ∃ w ∈ Ŵ, l * w * l⁻¹ ≠ w := by
      obtain ⟨l, ⟨l', hl', rfl⟩, w, hw, hlw⟩ := hLW
      refine ⟨l', hl', ⟨w, hWH hw⟩, Subgroup.mem_subgroupOf.mpr hw, fun h' => hlw ?_⟩
      exact congrArg Subtype.val h'
    have hQ2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
    have hmod : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
        ∀ ρ : H ⧸ CFSG.pCore 2 H →* MulAut V,
          (∃ l ∈ perfectResidual H, ρ (l : H ⧸ CFSG.pCore 2 H) ≠ 1) →
          k ≤ Nat.card (Sec3.commHom (ρ ((⟨a, haH⟩ : H) : H ⧸ CFSG.pCore 2 H))).range := by
      intro V _ _ hV2 ρ hρ
      obtain ⟨l, hl, hρl⟩ := hρ
      rw [himg]
      exact hk V hV2 ρ ⟨_, map_perfectResidual_le (QuotientGroup.mk' (CFSG.pCore 2 H))
        ⟨l, hl, rfl⟩, hρl⟩
    have := le_relIndex_of_quotient_bound hQ2 ⟨a, haH⟩ k hmod Ŵ hŴn hŴQ hŴc hŴ2
      (exists_odd_of_not_centralizes hLŴ)
    rwa [relIndex_centralizer_subgroupOf hWH haH] at this
  refine ⟨key 4 fun V _ _ hV2 ρ hρ => (quotient_bound hK h hH hs hsH V hV2 ρ hρ).1,
    fun hL => key 16 fun V _ _ hV2 ρ hρ => (quotient_bound hK h hH hs hsH V hV2 ρ hρ).2 ?_⟩
  obtain ⟨e⟩ := hL
  obtain ⟨e'⟩ := nonempty_quotient_mulEquiv_perfectResidual H
  exact ⟨e'.symm.trans e⟩

end Item181ThreeProof

end CFSG.RankThree.PartTwo.Sec18
