module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerModel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIso
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSU
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClMarking
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRootBig
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Root
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.RankThree.GF2n.Tim79a34SpFacts
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.SpPlacement
  CFSG.StandardType.GGQ2Frame.SpBlocks Matrix
open CFSG.Open (StatedSp StatedSU IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem component_mulEquiv_ycode {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (ctx : SpCtx H E hEN K m ζ) (hZ : Subgroup.center ↥H = ⊥) {c : PlaneRaw.Code m}
    (hc : PlaneRaw.admissible .symplectic c) :
    Nonempty (↥(ctx.fr.component c) ≃* ↥(Ycode ζ m c)) := by
  classical
  let π : ↥H →* ↥(StatedSp m K) := ctx.fr.π
  let Y : Subgroup ↥(StatedSp m K) := Ycode ζ m c
  let D : Subgroup ↥H := ⁅Y.comap π, Y.comap π⁆
  have hY : ⁅Y, Y⁆ = Y := ycode_perfect spIsQuasisimpleYcode_holds ctx.hK ctx.hζ hc
  have hDmap : D.map π = Y := (derived_comap_perfect π ctx.fr.surj ctx.fr.ker_le hY).1
  let f : ↥D →* ↥Y := (π.comp D.subtype).codRestrict Y fun x => by
    have hx : π (x : ↥H) ∈ D.map π := Subgroup.mem_map_of_mem _ x.2
    rwa [hDmap] at hx
  have hfval : ∀ x : ↥D, (f x : ↥(StatedSp m K)) = π (x : ↥H) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have hπ : π (x : ↥H) = π (y : ↥H) := by
      rw [← hfval x, ← hfval y]
      exact congrArg Subtype.val hxy
    have hmem : (x : ↥H) * (y : ↥H)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, mul_inv_cancel]
    have hz : (x : ↥H) * (y : ↥H)⁻¹ ∈ Subgroup.center ↥H := ctx.fr.ker_le hmem
    rw [hZ, Subgroup.mem_bot] at hz
    exact Subtype.ext (mul_inv_eq_one.mp hz)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : ↥(StatedSp m K)) ∈ D.map π := by rw [hDmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine ⟨(D.equivMapOfInjective H.subtype H.subtype_injective).symm.trans
    (MulEquiv.ofBijective f ⟨hinj, hsurj⟩)⟩

private theorem ycode_zero_mulEquiv_commutator {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {S : Finset (Fin m)} (hS : S.Nonempty) :
    Nonempty (↥(Ycode ζ m (.zero S)) ≃* ↥(commutator (StatedSp S.card K))) := by
  obtain ⟨e⟩ := nonempty_blockGroup_zero_mulEquiv ζ m hK hζ hS
  obtain ⟨c₁⟩ := nonempty_commutator_subgroup_equiv (blockGroup ζ m (.zero S))
  obtain ⟨c₂⟩ := nonempty_commutator_equiv e
  exact ⟨c₁.trans c₂⟩

private theorem ycode_extension_mulEquiv_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {e : PlaneRaw.V m} (he : e ≠ 0)
    (h4 : (PlaneRaw.Code.extSupport e).card = 4) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = 4 ∧
      Nonempty (↥(Ycode ζ m (.extension e)) ≃* ↥(StatedSU 4 2 E)) := by
  obtain ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨e₂⟩⟩ :=
    exists_blockGroup_extension_mulEquiv ζ m hK hζ he
  let : Field E := hEfield
  let : Finite E := hEfin
  let : CharP E 2 := hEchar
  obtain ⟨c₁⟩ := nonempty_commutator_subgroup_equiv (blockGroup ζ m (.extension e))
  obtain ⟨c₂⟩ := nonempty_commutator_equiv e₂
  obtain ⟨c₃⟩ := nonempty_commutator_subgroup_equiv
    (ClassicalBlocks.GUFull (PlaneRaw.Code.extSupport e).card 2 E)
  have hSU : ⁅ClassicalBlocks.GUFull (PlaneRaw.Code.extSupport e).card 2 E,
      ClassicalBlocks.GUFull (PlaneRaw.Code.extSupport e).card 2 E⁆ =
      StatedSU (PlaneRaw.Code.extSupport e).card 2 E :=
    commutator_guFull_eq_statedSU (E := E) hEcard (k := (PlaneRaw.Code.extSupport e).card)
      (by omega)
  refine ⟨E, inferInstance, inferInstance, inferInstance, by rw [hEcard]; norm_num, ?_⟩
  rw [← h4]
  exact ⟨c₁.trans (c₂.trans (c₃.symm.trans (MulEquiv.subgroupCongr hSU)))⟩

private theorem component_small_of_label {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (ctx : SpCtx H E hEN K m ζ) (hZ : Subgroup.center ↥H = ⊥) {c : PlaneRaw.Code m}
    (hc : PlaneRaw.admissible .symplectic c)
    (hlab : PlaneRaw.label .symplectic c = ⟨.B2der, 0, 1⟩ ∨
      PlaneRaw.label .symplectic c = ⟨.twA, 3, 1⟩) :
    LargeEvenSmall (ctx.fr.component c) := by
  obtain ⟨e₁⟩ := component_mulEquiv_ycode ctx hZ hc
  cases c with
  | zero S =>
      rcases hlab with hlab | hlab
      · by_cases h2 : S.card = 2
        · have hS : S.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨e₂⟩ := ycode_zero_mulEquiv_commutator ζ m ctx.hK ctx.hζ hS
          rw [h2] at e₂
          exact Or.inr ⟨e₁.trans (e₂.trans
            (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv ctx.hK))⟩
        · exfalso
          have htag := congrArg LargeEvenLabel.tag hlab
          simp [PlaneRaw.label, h2] at htag
      · exfalso
        have htag := congrArg LargeEvenLabel.tag hlab
        by_cases h2 : S.card = 2
        · simp [PlaneRaw.label, h2] at htag
        · simp [PlaneRaw.label, h2] at htag
  | extension e =>
      rcases hlab with hlab | hlab
      · exfalso
        have htag := congrArg LargeEvenLabel.tag hlab
        simp [PlaneRaw.label] at htag
      · have hrank : (PlaneRaw.Code.extSupport e).card - 1 = 3 :=
          congrArg LargeEvenLabel.rank hlab
        have hcard4 : (PlaneRaw.Code.extSupport e).card = 4 := by omega
        obtain ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨e₂⟩⟩ :=
          ycode_extension_mulEquiv_four ζ m ctx.hK ctx.hζ hc.1 hcard4
        let : Field E := hEfield
        let : Finite E := hEfin
        let : CharP E 2 := hEchar
        have hEcard' : Nat.card E = (2 ^ 1) ^ 2 := by simpa using hEcard
        exact Or.inl (CFSG.StandardType.IOneU52.isU42_of_mulEquiv (e₁.trans e₂)
          (CFSG.StandardType.IOneU52.unitarySU_four_isU42 hEcard'))

private theorem seven_dvd_component_zero {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (ctx : SpCtx H E hEN K m ζ) (hZ : Subgroup.center ↥H = ⊥) {S : Finset (Fin m)}
    (hS : 3 ≤ S.card) :
    7 ∣ Nat.card (ctx.fr.component (.zero S)) := by
  have hadm : PlaneRaw.admissible .symplectic (.zero S) := by
    show 2 ≤ S.card
    omega
  obtain ⟨e₁⟩ := component_mulEquiv_ycode ctx hZ hadm
  obtain ⟨e₂⟩ := ycode_zero_mulEquiv_commutator ζ m ctx.hK ctx.hζ
    (Finset.card_pos.mp (Nat.lt_of_lt_of_le (by norm_num) hS))
  have hcomm : commutator (StatedSp S.card K) = ⊤ :=
    CFSG.RankThree.GF2n.Tim79a.commutator_statedSp_eq_top (n := S.card) hS ctx.hK
  let e₃ : ↥(commutator (StatedSp S.card K)) ≃* StatedSp S.card K :=
    (MulEquiv.subgroupCongr hcomm).trans Subgroup.topEquiv
  have hcard : Nat.card (ctx.fr.component (.zero S)) = Nat.card (StatedSp S.card K) :=
    Nat.card_congr (e₁.trans (e₂.trans e₃)).toEquiv
  rw [hcard]
  exact SpRootBig.seven_dvd_card_statedSp K hS

private theorem axis_of_fixed {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {b : ↥Bs} (hfix : ∀ ψ ∈ ggAutomizer L Bs, ψ b = b) :
    ∀ k, k ≠ i0 → eta b k = 1 := by
  have haxis : ∀ u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom,
      u (eta b) = eta b := by
    rintro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    rw [show (MulAut.congr eta).toMonoidHom v (eta b) = eta (v b) by simp, hfix v hv]
  rw [hb] at haxis
  exact (forall_bCoordinateBlock_fix_iff (p := 3) (by norm_num) (by norm_num) i0 (eta b)).mp haxis

private theorem inf_centralizer_eq_zpowers {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G}
    {L : Subgroup G} {n : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hBle : B ≤ Bs) (hxB : x ∈ B) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact ⟨hBle hxB, hxL⟩
  · have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
    rw [hcardx]
    have hfix : ∀ (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
        ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨(c : G), c.2.1⟩ = ⟨(c : G), c.2.1⟩ := by
      intro c ψ hψ
      exact ggAutomizer_apply_eq_of_le_centralizer (H := L)
        (fun l hl => by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (Subgroup.mem_centralizer_iff.mp c.2.2 l hl).symm) hψ
    have hinj : Function.Injective
        (fun c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) => eta ⟨(c : G), c.2.1⟩ i0) := by
      intro c d hcd
      apply Subtype.ext
      have hfun : ∀ k, eta ⟨(c : G), c.2.1⟩ k = eta ⟨(d : G), d.2.1⟩ k := by
        intro k
        by_cases hk : k = i0
        · subst hk
          exact hcd
        · rw [axis_of_fixed eta hb (hfix c) k hk, axis_of_fixed eta hb (hfix d) k hk]
      exact congrArg (fun z : ↥Bs => (z : G)) (eta.injective (funext hfun))
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [show Nat.card (Multiplicative (ZMod 3)) = 3 by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]] at hle

private theorem card_subgroupOf_eq {G : Type} [Group G] (Bs L : Subgroup G) :
    Nat.card ↥(Bs.subgroupOf L) = Nat.card ↥(Bs ⊓ L) := by
  have h := Subgroup.card_subtype L (Bs.subgroupOf L)
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.symm


private theorem corner_x_mem_centralizer {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G}
    {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) : x ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨-, -, -, hcomp, -⟩ := hC.1.2.2.2.2.2.2.1
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact ((Subgroup.mem_centralizer_iff.mp (hcomp.1 hl)) x (Set.mem_singleton x)).symm

private theorem corner_center_eq_bot
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) :
    Subgroup.center ↥L = ⊥ := by
  obtain ⟨φ, ρ, hφ, hφL, hact, hρrange, hρker⟩ := exists_spPlaneTorus_model hC hn eta hb hM
  let ψ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* ↥L :=
    φ.codRestrict L fun g => hφL ▸ (φ.mem_range).2 ⟨g, rfl⟩
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact hφ (by simpa [ψ] using congrArg Subtype.val hab)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : G) ∈ φ.range := by rw [hφL]; exact y.2
    obtain ⟨g, hg⟩ := (φ.mem_range).1 hy
    exact ⟨g, Subtype.ext hg⟩
  let e : CFSG.Open.StatedSp (n - 1) (ZMod 2) ≃* ↥L := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have h := Subgroup.map_center_eq e
  rw [CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n - 1)
    (by omega), Subgroup.map_bot] at h
  exact h.symm

private theorem corner_zpowers_inf_eq_bot {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G}
    {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hZ : Subgroup.center ↥L = ⊥) :
    Subgroup.zpowers x ⊓ L = ⊥ := by
  have hxL := corner_x_mem_centralizer hC
  rw [inf_comm, eq_bot_iff]
  rintro y ⟨hyL, hyx⟩
  rw [Subgroup.mem_bot]
  have hyc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
    have hcomm : Commute x (l : G) :=
      (Subgroup.mem_centralizer_iff.mp hxL (l : G) l.2).symm
    have hyl : y * (l : G) = (l : G) * y := by
      rw [← hk]
      exact (hcomm.zpow_left k).eq
    simpa using hyl.symm
  rw [hZ] at hyc
  have h1 : (⟨y, hyL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hyc
  simpa using congrArg Subtype.val h1

private theorem corner_split_mul
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) :
    (∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) ∧
      ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = a * c := by
  obtain ⟨-, hxB, hx1, -, -⟩ := hC.1.2.2.2.2.2.2.1
  have hBle : B ≤ Bs := hC.2.1.1
  have hBsElem : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hxL := corner_x_mem_centralizer hC
  have hx3 : x ^ 3 = 1 := hBsElem.2 x (hBle hxB)
  have hlab : GGInnerDiagOnLabel (fun _ lab => GGQTwoClLabel lab) 3 Bs L :=
    hM.mono_label (fun lab h => ⟨by rw [h.2.2]; norm_num,
      h.1.elim (fun hB => Or.inr (Or.inl hB)) (fun hC => Or.inr (Or.inr hC))⟩)
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
    not_three_dvd_card_center_of_qTwoCl hlab
  have hsplit := exists_mul_of_qTwoCl hC.2.1 hlab hZ3
  have hCeq := inf_centralizer_eq_zpowers eta hb hBle hxB hx1 hx3 hxL
  refine ⟨?_, hsplit⟩
  intro b hb
  obtain ⟨a, ha, c, hc, rfl⟩ := hsplit b hb
  have hcC : c ∈ Subgroup.zpowers x := by
    have hmem : c ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hc.1, hc.2⟩
    rwa [hCeq] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcC
  exact ⟨a, ha, k, by rw [← hk]⟩

private theorem corner_card_subgroupOf {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hsp : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (hzp : Subgroup.zpowers x ⊓ L = ⊥) :
    Nat.card ↥(Bs.subgroupOf L) = 3 ^ (n - 1) := by
  obtain ⟨-, hxB, hx1, -, -⟩ := hC.1.2.2.2.2.2.2.1
  have hBle : B ≤ Bs := hC.2.1.1
  have hBsElem : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hZs : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr (hBle hxB)
  have hx3 : x ^ 3 = 1 := hBsElem.2 x (hBle hxB)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcardz : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hBsCard : Nat.card ↥Bs = 3 ^ n := by
    calc Nat.card ↥Bs = Nat.card (Fin n → Multiplicative (ZMod 3)) := Nat.card_congr eta.toEquiv
      _ = 3 ^ n := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun]
        simp
  have hsup : Bs ⊓ L ⊔ Subgroup.zpowers x = Bs := by
    refine le_antisymm (sup_le inf_le_left hZs) ?_
    intro b hb
    obtain ⟨a, ha, k, hk⟩ := hsp b hb
    rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
  have hinf : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ L ⊓ Subgroup.zpowers x := ⟨(Subgroup.mem_inf.mp hy.1).2, hy.2⟩
    rw [inf_comm, hzp] at hy'
    simpa using hy'
  have hcommBL : ∀ a ∈ Bs ⊓ L, ∀ d ∈ Subgroup.zpowers x, a * d = d * a := by
    intro a ha d hd
    exact congrArg Subtype.val (hBsElem.1.is_comm.comm ⟨a, ha.1⟩ ⟨d, hZs hd⟩)
  have hprod := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
    (C := Bs ⊓ L) (D := Subgroup.zpowers x) hcommBL
  have hcardBL : Nat.card ↥(Bs ⊓ L) = 3 ^ (n - 1) := by
    have h := hprod
    rw [hsup, hinf, Subgroup.card_bot, hcardz, hBsCard, mul_one] at h
    have h3n : 3 ^ n = 3 ^ (n - 1) * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    exact mul_right_cancel₀ (by norm_num : (3 : ℕ) ≠ 0) (h.symm.trans h3n)
  rw [card_subgroupOf_eq, hcardBL]


private theorem center_top_eq_bot {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) :
    Subgroup.center ↥(⊤ : Subgroup G) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro y hy
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hy' : (y : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, Subgroup.mem_top g⟩)
  rw [hZ] at hy'
  simpa using hy'




private theorem exists_symplectic_label {K₀ : Type} [Group K₀] {E : Subgroup K₀}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab.n < 2 ∧ (lab.tag = .B ∨ lab.tag = .C)) 3 E ⊤) :
    ∃ r : ℕ, GGInnerDiagOnLabel (fun _ l => l = planeAmbientLabel .symplectic r) 3 E ⊤ := by
  obtain ⟨lab, hlab2, hhas, R₀, _, I, F, θ, hpred⟩ := largeEvenMarking_exists_hasLabel hInn
  obtain ⟨⟨hn2, htag⟩, -⟩ := hpred
  obtain ⟨t, r, n⟩ := lab
  have hn2' : n < 2 := hn2
  have htag' : t = .B ∨ t = .C := htag
  have hn1 : n = 1 := by
    have h1 : 1 ≤ n := hlab2.1
    omega
  subst hn1
  have hlabC2 : LargeEvenInLambda2 ⟨.C, r, 1⟩ := inLambda2_C_of_BC htag' hlab2
  have hhasC : GGHasLabel ⟨.C, r, 1⟩
      (↥(⊤ : Subgroup K₀) ⧸ Subgroup.center ↥(⊤ : Subgroup K₀)) :=
    hasLabel_C_of_BC htag' hhas
  have hHmark : GGInnerDiagOn E (⊤ : Subgroup K₀) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hInn
  exact ⟨r, ggInnerDiagOn_relabel ggLabelRigidInput_holds hHmark hlabC2 hhasC⟩

private theorem exists_spCtx_and_normalizer {K₀ : Type} [Group K₀] [Finite K₀] {E : Subgroup K₀}
    {m : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab.n < 2 ∧ (lab.tag = .B ∨ lab.tag = .C)) 3 E ⊤)
    (hEab : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set K₀), g ^ 3 = 1 → g ∈ E)
    (hZ : Subgroup.center K₀ = ⊥) (hcard : Nat.card E = 3 ^ m) (hm : 4 ≤ m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
      (hEN : E ≤ Subgroup.normalizer ((⊤ : Subgroup K₀) : Set K₀))
      (ctx : SpCtx (⊤ : Subgroup K₀) E hEN K m ζ),
      (∀ c : PlaneRaw.Code m, PlaneRaw.admissible .symplectic c →
        (ggAutomizer (ctx.fr.component c) E).map (ggLin (p := 3) ctx.fr.coord) =
          PlaneRaw.normalizerOf .symplectic m c) ∧
      (ggAutomizer (⊤ : Subgroup K₀) E).map (ggLin (p := 3) ctx.fr.coord) =
        PlaneRaw.ambientNormalizer .symplectic m := by
  classical
  obtain ⟨r, hInnC⟩ := exists_symplectic_label hInn
  have hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((⊤ : Subgroup K₀) : Set K₀)) := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]
    simp
  have hcard3 : 3 ^ 3 ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ :=
    spCtx_of_pieces spInnerDiagData_holds exists_spFrame_holds spEleH_holds hInnC hEab hSC hC3
      hcard3
  have hN := spNormalizerEqs_of_pieces CoverComponents.automizerCoverEq_holds
    spAmbientTorusAut_holds (spComponentTorusAut_of_parts spZeroTorusAut_holds spExtTorusAut_holds)
    spIsQuasisimpleYcode_holds ctx
  have hEc : Nat.card E = 3 ^ r := by
    rw [← Nat.card_congr ctx.fr.τ.toEquiv, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hrm : r = m := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hEc.symm.trans hcard)
  subst hrm
  exact ⟨K, inferInstance, inferInstance, inferInstance, ζ, hEN, ctx, hN.1, hN.2⟩

theorem exists_spRealization_of_marking {K₀ : Type} [Group K₀] [Finite K₀] {E : Subgroup K₀}
    {m : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab.n < 2 ∧ (lab.tag = .B ∨ lab.tag = .C)) 3 E ⊤)
    (hEab : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set K₀), g ^ 3 = 1 → g ∈ E)
    (hZ : Subgroup.center K₀ = ⊥) (hcard : Nat.card E = 3 ^ m) (hm : 4 ≤ m) :
    ∃ R : Realization (⊤ : Subgroup K₀) E (planeEntry .symplectic m),
      (ggAutomizer (⊤ : Subgroup K₀) E).map (ggLin (p := 3) R.coord) =
          PlaneRaw.signedPermGroup m ∧
        (∀ c, PlaneRaw.admissible .symplectic c →
          (PlaneRaw.label .symplectic c = ⟨.B2der, 0, 1⟩ ∨
            PlaneRaw.label .symplectic c = ⟨.twA, 3, 1⟩) →
          LargeEvenSmall (R.component c)) ∧
        ∀ S : Finset (Fin m), 3 ≤ S.card → 7 ∣ Nat.card (R.component (.zero S)) := by
  classical
  obtain ⟨K, _, _, _, ζ, hEN, ctx, hN⟩ :=
    exists_spCtx_and_normalizer hInn hEab hSC hZ hcard hm
  have hZtop : Subgroup.center ↥(⊤ : Subgroup K₀) = ⊥ := center_top_eq_bot hZ
  refine ⟨Realization.ofCore (spRealizationCore spComponentOccursIff_holds spComponentCentEq_holds
    spComponentInsideEq_holds spComponentMarked_holds hm ctx)
    ⟨fun c hc => hN.1 c hc.2, hN.2⟩, hN.2, ?_, ?_⟩
  · intro c hc hlab
    exact component_small_of_label ctx hZtop hc hlab
  · intro S hS
    exact seven_dvd_component_zero ctx hZtop hS

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.exists_cornerRealization {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) :
    Subgroup.zpowers x ⊓ L = ⊥ ∧ (∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) ∧
      Nat.card ↥(Bs.subgroupOf L) = 3 ^ (n - 1) ∧
      ∃ R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)),
        (ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord) =
            PlaneRaw.signedPermGroup (n - 1) ∧
          (∀ c, PlaneRaw.admissible .symplectic c →
            (PlaneRaw.label .symplectic c = ⟨.B2der, 0, 1⟩ ∨
              PlaneRaw.label .symplectic c = ⟨.twA, 3, 1⟩) →
            LargeEvenSmall (R.component c)) ∧
          ∀ S : Finset (Fin (n - 1)), 3 ≤ S.card → 7 ∣ Nat.card (R.component (.zero S)) := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := corner_center_eq_bot hC hn eta hb hM
  have hzp : Subgroup.zpowers x ⊓ L = ⊥ := corner_zpowers_inf_eq_bot hC hZ
  obtain ⟨hsp, hsplit⟩ := corner_split_mul hC eta hb hM
  have hcard : Nat.card ↥(Bs.subgroupOf L) = 3 ^ (n - 1) :=
    corner_card_subgroupOf hC hn eta hsp hzp
  have hBsElem : IsElemAbelian 3 Bs := hC.2.1.2.1
  refine ⟨hzp, hsp, hcard, ?_⟩
  obtain ⟨R, hR1, hR2, hR3⟩ := exists_spRealization_of_marking
    ((hM.subgroupOf).mono_label (fun lab h => ⟨by rw [h.2.2]; norm_num, h.1⟩))
    (hBsElem.subgroupOf L)
    (mem_subgroupOf_of_mem_centralizer_subgroupOf hC.2.1.2.2.2 hsplit)
    hZ hcard (by omega)
  exact ⟨R, hR1, hR2, hR3⟩

end CFSG.StandardType

end
