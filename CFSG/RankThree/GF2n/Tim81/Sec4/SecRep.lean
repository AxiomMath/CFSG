module

public import CFSG.Timmesfeld.Bridge.RootStructWTINatSum
public import CFSG.GroupTheory.CommutatorMemSubgroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.RankThree.GF2n.Tim81.HBar
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.GroupTheory
open CFSG.QuasithinUnique.Setup.X7
open CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.QuotMod
open scoped commutatorElement

variable {G : Type} [Group G] {V H : Subgroup G} {N N₀ : Subgroup G}
variable [(N₀.subgroupOf N).Normal]

abbrev SecMod (hs : QuotMod.Hyp H N N₀) : Type :=
  Additive (↥N ⧸ N₀.subgroupOf N)

namespace SecMod

variable (hs : QuotMod.Hyp H N N₀)

@[reducible] noncomputable instance instAddCommGroup : AddCommGroup (SecMod hs) :=
  { (inferInstance : AddGroup (SecMod hs)) with
    add_comm := fun a b => by
      obtain ⟨n, rfl⟩ := QuotMod.mk_surjective (N := N) (N₀ := N₀) a
      obtain ⟨m, rfl⟩ := QuotMod.mk_surjective (N := N) (N₀ := N₀) b
      rw [← QuotMod.mk_mul, ← QuotMod.mk_mul]
      refine (QuotMod.mk_eq_mk_iff (N := N) (N₀ := N₀) _ _).2 ?_
      have h := hs.comm (n⁻¹) (N.inv_mem n.2) (m⁻¹) (N.inv_mem m.2)
      have h' := N₀.inv_mem h
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc] using h' }

abbrev mk (n : ↥N) : SecMod hs :=
  QuotMod.mk N₀ n

theorem mk_mul (n n' : ↥N) : mk hs (n * n') = mk hs n + mk hs n' :=
  QuotMod.mk_mul n n'

theorem mk_inv (n : ↥N) : mk hs n⁻¹ = -mk hs n :=
  QuotMod.mk_inv n

theorem mk_one : mk hs (1 : ↥N) = 0 :=
  QuotMod.mk_one

theorem mk_eq_zero_iff (n : ↥N) : mk hs n = 0 ↔ (n : G) ∈ N₀ :=
  QuotMod.mk_eq_zero_iff n

theorem mk_surjective : Function.Surjective (mk hs) :=
  QuotMod.mk_surjective

theorem mk_conj_sub_mk (hs : QuotMod.Hyp H N N₀) (z : ↥H) (n : ↥N) :
    mk hs ⟨(z : G) * n * (z : G)⁻¹, hs.conj z z.2 n n.2⟩ - mk hs n =
      mk hs ⟨(z : G) * n * (z : G)⁻¹ * n⁻¹,
        N.mul_mem (hs.conj z z.2 n n.2) (N.inv_mem n.2)⟩ := by
  rw [sub_eq_add_neg, ← mk_inv hs, ← mk_mul hs]
  congr 1

end SecMod

@[reducible] noncomputable def SecMod.module (hs : QuotMod.Hyp H N N₀)
    (hsq : ∀ n ∈ N, n * n ∈ N₀) : Module (ZMod 2) (SecMod hs) :=
  AddCommGroup.zmodModule (fun v => by
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
    rw [two_nsmul, ← SecMod.mk_mul hs, SecMod.mk_eq_zero_iff hs]
    exact hsq n n.2)

@[expose] noncomputable def secConjAdd (hs : QuotMod.Hyp H N N₀) (g : G) (hg : g ∈ H) :
    SecMod hs →+ SecMod hs :=
  (QuotMod.conjQ hs g hg).toAdditive

namespace SecMod

theorem secConjAdd_mk (hs : QuotMod.Hyp H N N₀) (g : G) (hg : g ∈ H) (n : ↥N) :
    secConjAdd hs g hg (SecMod.mk hs n) =
      SecMod.mk hs ⟨g * n * g⁻¹, hs.conj g hg n n.2⟩ := by
  unfold secConjAdd SecMod.mk
  rfl

end SecMod

section Representation

variable (hs : QuotMod.Hyp H N N₀)
variable [Module (ZMod 2) (SecMod hs)]

namespace SecMod

@[expose] noncomputable def secConj :
    ↥H →* (SecMod hs →ₗ[ZMod 2] SecMod hs) where
  toFun z := (secConjAdd hs (z : G) z.2).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
    change secConjAdd hs (1 : G) H.one_mem (SecMod.mk hs n) = SecMod.mk hs n
    rw [SecMod.secConjAdd_mk]
    congr 1
    ext
    simp
  map_mul' z z' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
    change secConjAdd hs ((z * z' : ↥H) : G) (z * z').2 (SecMod.mk hs n) =
      secConjAdd hs (z : G) z.2 (secConjAdd hs (z' : G) z'.2 (SecMod.mk hs n))
    rw [SecMod.secConjAdd_mk, SecMod.secConjAdd_mk, SecMod.secConjAdd_mk]
    congr 1
    ext
    simp [QuotMod.conjN, mul_assoc]

end SecMod

@[simp] theorem secConj_apply (z : ↥H) (v : SecMod hs) :
    SecMod.secConj hs z v = secConjAdd hs (z : G) z.2 v := rfl

theorem secConj_mk (z : ↥H) (x : ↥N) :
    SecMod.secConj hs z (SecMod.mk hs x) =
      SecMod.mk hs ⟨(z : G) * x * (z : G)⁻¹, hs.conj z z.2 x x.2⟩ := by
  rw [secConj_apply, SecMod.secConjAdd_mk]

theorem secConj_eq_one {z : ↥H}
    (hz : ∀ x ∈ N, (z : G) * x * (z : G)⁻¹ * x⁻¹ ∈ N₀) : SecMod.secConj hs z = 1 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
  change secConjAdd hs (z : G) z.2 (SecMod.mk hs n) = SecMod.mk hs n
  rw [SecMod.secConjAdd_mk]
  have hzero : SecMod.mk hs ⟨(z : G) * n * (z : G)⁻¹ * n⁻¹,
      N.mul_mem (hs.conj z z.2 n n.2) (N.inv_mem n.2)⟩ = 0 :=
    (SecMod.mk_eq_zero_iff hs _).2 (hz n n.2)
  have h := SecMod.mk_conj_sub_mk hs z n
  rw [hzero] at h
  exact sub_eq_zero.mp h

noncomputable def secDescend {K : Type} [Group K] (φ : ↥H →* K)
    (hφ : Function.Surjective φ)
    (hker : ∀ z, φ z = 1 → SecMod.secConj hs z = 1) : Representation (ZMod 2) K (SecMod hs) :=
  (QuotientGroup.lift φ.ker (SecMod.secConj hs) fun z hz => hker z hz).comp
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom

theorem secDescend_apply {K : Type} [Group K] (φ : ↥H →* K)
    (hφ : Function.Surjective φ) (hker : ∀ z, φ z = 1 → SecMod.secConj hs z = 1) (z : ↥H) :
    secDescend hs φ hφ hker (φ z) = SecMod.secConj hs z := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ z) =
      (z : ↥H ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change (QuotientGroup.lift φ.ker (SecMod.secConj hs) (fun z hz => hker z hz))
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ z)) = SecMod.secConj hs z
  rw [he]
  exact QuotientGroup.lift_mk (N := φ.ker) (φ := SecMod.secConj hs)
    (HN := fun z hz => hker z hz) z

private noncomputable def conjSecBar
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀) :
    HBar V H →* (SecMod hs →ₗ[ZMod 2] SecMod hs) :=
  secDescend hs (piK V H) (piK_surjective V H) fun z hz =>
    secConj_eq_one hs fun n hn =>
      hK (z : G) ((piK_eq_one_iff z).mp hz) n hn

private theorem conjSecBar_piK
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀) (z : ↥H) :
    conjSecBar hs hK (piK V H z) = SecMod.secConj hs z :=
  secDescend_apply hs (piK V H) (piK_surjective V H) _ z

noncomputable def repSec (hs : QuotMod.Hyp H N N₀)
    [Module (ZMod 2) (SecMod hs)]
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀)
    (X : Type) [Group X] (ψ : HBar V H ≃* X) :
    Representation (ZMod 2) X (SecMod hs) :=
  (conjSecBar hs hK).comp ψ.symm.toMonoidHom

theorem repSec_apply_piK_mk (hs : QuotMod.Hyp H N N₀)
    [Module (ZMod 2) (SecMod hs)]
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀)
    (X : Type) [Group X] (ψ : HBar V H ≃* X) (z : ↥H) (n : ↥N) :
    repSec hs hK X ψ (ψ (piK V H z)) (SecMod.mk hs n) =
      SecMod.mk hs ⟨(z : G) * n * (z : G)⁻¹, hs.conj z z.2 n n.2⟩ := by
  change (conjSecBar hs hK (ψ.symm (ψ (piK V H z)))) (SecMod.mk hs n) = _
  rw [MulEquiv.symm_apply_apply, conjSecBar_piK, secConj_apply, SecMod.secConjAdd_mk]

end Representation

section Lattice

variable (hs : QuotMod.Hyp H N N₀)
variable [Module (ZMod 2) (SecMod hs)]

noncomputable def subSec (E : Subgroup G) : Submodule (ZMod 2) (SecMod hs) :=
  AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup ((E.subgroupOf N).map (QuotientGroup.mk' (N₀.subgroupOf N))))

theorem mem_subSec_iff {E : Subgroup G} {v : SecMod hs} :
    v ∈ subSec hs E ↔ ∃ n : ↥(E ⊓ N),
      SecMod.mk hs (Subgroup.inclusion inf_le_right n) = v := by
  change Additive.toMul v ∈ (E.subgroupOf N).map (QuotientGroup.mk' (N₀.subgroupOf N)) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, Subgroup.mem_subgroupOf.mp ha, a.2⟩, ?_⟩
    have h' : Additive.ofMul (QuotientGroup.mk a) = v := by
      calc Additive.ofMul (QuotientGroup.mk a)
          = Additive.ofMul (QuotientGroup.mk' (N₀.subgroupOf N) a) := rfl
        _ = Additive.ofMul (Additive.toMul v) := congrArg Additive.ofMul h
        _ = v := ofMul_toMul v
    exact h'
  · rintro ⟨n, h⟩
    refine ⟨Subgroup.inclusion inf_le_right n, Subgroup.mem_subgroupOf.mpr n.2.1, ?_⟩
    rw [← h]
    rfl

theorem mk_mem_subSec_iff {E : Subgroup G} (hN₀E : N₀ ≤ E) {n : ↥N} :
    SecMod.mk hs n ∈ subSec hs E ↔ (n : G) ∈ E := by
  change QuotientGroup.mk' (N₀.subgroupOf N) n ∈
    (E.subgroupOf N).map (QuotientGroup.mk' (N₀.subgroupOf N)) ↔ (n : G) ∈ E
  rw [← Subgroup.mem_comap, QuotientGroup.comap_map_mk',
    sup_eq_right.mpr (Subgroup.subgroupOf_mono N hN₀E), Subgroup.mem_subgroupOf]

theorem subSec_mono {E F : Subgroup G} (hEF : E ≤ F) : subSec hs E ≤ subSec hs F :=
  (AddSubgroup.toZModSubmodule 2).monotone <|
    (Subgroup.toAddSubgroup).monotone <| Subgroup.map_mono (Subgroup.subgroupOf_mono N hEF)

theorem subSec_self : subSec hs N = ⊤ := by
  rw [subSec, Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  simp

theorem subSec_le_subSec_iff {E F : Subgroup G}
    (hEN : E ≤ N) (hN₀F : N₀ ≤ F) : subSec hs E ≤ subSec hs F ↔ E ≤ F := by
  rw [subSec, subSec, (AddSubgroup.toZModSubmodule 2).le_iff_le,
    (Subgroup.toAddSubgroup).le_iff_le, Subgroup.map_le_map_iff', QuotientGroup.ker_mk']
  have hsup : F.subgroupOf N ⊔ N₀.subgroupOf N = F.subgroupOf N :=
    sup_eq_left.mpr (Subgroup.subgroupOf_mono N hN₀F)
  constructor
  · intro h x hx
    rw [hsup] at h
    exact Subgroup.mem_subgroupOf.mp
      (h (Subgroup.mem_sup_left
        (show (⟨x, hEN hx⟩ : ↥N) ∈ E.subgroupOf N from Subgroup.mem_subgroupOf.mpr hx)))
  · intro hEF
    rw [hsup]
    exact sup_le (Subgroup.subgroupOf_mono N hEF) (Subgroup.subgroupOf_mono N hN₀F)

theorem subSec_inj {E F : Subgroup G}
    (hEN : E ≤ N) (hN₀E : N₀ ≤ E) (hFN : F ≤ N) (hN₀F : N₀ ≤ F) :
    subSec hs E = subSec hs F ↔ E = F := by
  constructor
  · intro h
    exact le_antisymm ((subSec_le_subSec_iff hs hEN hN₀F).1 (le_of_eq h))
      ((subSec_le_subSec_iff hs hFN hN₀E).1 (le_of_eq h.symm))
  · rintro rfl
    rfl

theorem subSec_sup {E F : Subgroup G} (hEN : E ≤ N) (hFN : F ≤ N) :
    subSec hs (E ⊔ F) = subSec hs E ⊔ subSec hs F := by
  rw [subSec, subSec, subSec, Subgroup.subgroupOf_sup hEN hFN, Subgroup.map_sup]
  simp

noncomputable def subgroupOfSubSec (U : Submodule (ZMod 2) (SecMod hs)) : Subgroup G :=
  ((AddSubgroup.toSubgroup' ((AddSubgroup.toZModSubmodule 2).symm U)).comap
    (QuotientGroup.mk' (N₀.subgroupOf N))).map N.subtype

private theorem mem_subgroupOfSubSec {U : Submodule (ZMod 2) (SecMod hs)} {g : G} :
    g ∈ subgroupOfSubSec hs U ↔ ∃ hg : g ∈ N, SecMod.mk hs ⟨g, hg⟩ ∈ U := by
  simp [subgroupOfSubSec, SecMod.mk, QuotMod.mk, Subgroup.mem_map, Subgroup.mem_comap,
    Submodule.mem_toAddSubgroup]

theorem subSec_subgroupOfSubSec (U : Submodule (ZMod 2) (SecMod hs)) :
    subSec hs (subgroupOfSubSec hs U) = U := by
  ext v
  rw [mem_subSec_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hmem : (n : G) ∈ subgroupOfSubSec hs U := n.2.1
    obtain ⟨hgN, hgU⟩ := (mem_subgroupOfSubSec hs).1 hmem
    have hEq : SecMod.mk hs ⟨(n : G), hgN⟩ =
        SecMod.mk hs (Subgroup.inclusion inf_le_right n) :=
      congrArg (SecMod.mk hs) (Subtype.ext rfl)
    rwa [hEq, hn] at hgU
  · intro hv
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
    let n' : ↥(subgroupOfSubSec hs U ⊓ N) :=
      ⟨n, ⟨(mem_subgroupOfSubSec hs).2 ⟨n.2, hv⟩, n.2⟩⟩
    exact ⟨n', congrArg (SecMod.mk hs) (Subtype.ext rfl)⟩

private theorem le_normalizer_N₀ (hs : QuotMod.Hyp H N N₀) :
    N ≤ Subgroup.normalizer (N₀ : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact hs.conj_mem hn
  · intro hm
    have := hs.conj_mem (N.inv_mem hn) hm
    have h : n⁻¹ * (n * m * n⁻¹) * n = m := by group
    simpa only [inv_inv, h] using this

noncomputable def secCent (hs : QuotMod.Hyp H N N₀) (S : Subgroup G) (hS : S ≤ H) :
    Subgroup G :=
  ⨅ s ∈ S, commMemSubgroup N N₀ (le_normalizer_N₀ hs) s

theorem mem_secCent (hs : QuotMod.Hyp H N N₀) {S : Subgroup G} (hS : S ≤ H) {n : G} :
    n ∈ secCent hs S hS ↔ n ∈ N ∧ ∀ s ∈ S, ⁅n, s⁆ ∈ N₀ := by
  simp only [secCent, Subgroup.mem_iInf, mem_commMemSubgroup]
  constructor
  · intro h
    exact ⟨(h 1 S.one_mem).1, fun s hsS => (h s hsS).2⟩
  · rintro ⟨hn, h⟩ s hsS
    exact ⟨hn, h s hsS⟩

theorem le_secCent (hs : QuotMod.Hyp H N N₀) {S : Subgroup G} (hS : S ≤ H) :
    N₀ ≤ secCent hs S hS := by
  intro n hn
  refine (mem_secCent hs hS).2 ⟨hs.le hn, fun s hsS => ?_⟩
  have h : s * n * s⁻¹ * n⁻¹ ∈ N₀ :=
    N₀.mul_mem (hs.conj₀ s (hS hsS) n hn) (N₀.inv_mem hn)
  rw [show ⁅n, s⁆ = (s * n * s⁻¹ * n⁻¹)⁻¹ from by
    rw [commutatorElement_def]
    group]
  exact N₀.inv_mem h

theorem natCard_subSec {E : Subgroup G} (hN₀E : N₀ ≤ E) (hEN : E ≤ N) :
    Nat.card (subSec hs E) * Nat.card N₀ = Nat.card E := by
  let φ : ↥E →* Multiplicative (subSec hs E) :=
    { toFun := fun e => Multiplicative.ofAdd
        ⟨SecMod.mk hs ⟨e, hEN e.2⟩,
          (mem_subSec_iff hs).2 ⟨⟨e, ⟨e.2, hEN e.2⟩⟩, rfl⟩⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact SecMod.mk_one hs
      map_mul' e e' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        change SecMod.mk hs ⟨(e * e' : ↥E), hEN (e * e').2⟩ =
          SecMod.mk hs ⟨e, hEN e.2⟩ + SecMod.mk hs ⟨e', hEN e'.2⟩
        rw [← SecMod.mk_mul hs]
        rfl }
  have hker : φ.ker = N₀.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (Multiplicative.toAdd (φ e) : subSec hs E) = 0 := by
        simpa using congrArg Multiplicative.toAdd h
      exact (SecMod.mk_eq_zero_iff hs _).1 (congrArg Subtype.val h')
    · intro h
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (SecMod.mk_eq_zero_iff hs _).2 h
  have hsurj : Function.Surjective φ := by
    intro x
    have hxmem : ((Multiplicative.toAdd x : subSec hs E) : SecMod hs) ∈ subSec hs E :=
      (Multiplicative.toAdd x).2
    obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hxmem
    refine ⟨⟨(n : G), n.2.1⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change SecMod.mk hs ⟨(n : G), hEN n.2.1⟩ =
      ((Multiplicative.toAdd x : subSec hs E) : SecMod hs)
    rw [show (⟨(n : G), hEN n.2.1⟩ : ↥N) =
      Subgroup.inclusion inf_le_right n from Subtype.ext rfl]
    exact hn
  have hiso : Nat.card (↥E ⧸ N₀.subgroupOf E) = Nat.card (subSec hs E) := by
    rw [← hker]
    refine (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv).trans ?_
    exact Nat.card_congr Multiplicative.toAdd
  rw [← hiso, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀E).toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (N₀.subgroupOf E)]

theorem subSec_inf {E F : Subgroup G} (hF : N₀ ≤ F) :
    subSec hs (E ⊓ F) = subSec hs E ⊓ subSec hs F := by
  refine le_antisymm (le_inf (subSec_mono hs inf_le_left) (subSec_mono hs inf_le_right)) ?_
  intro v hv
  obtain ⟨hvE, hvF⟩ := Submodule.mem_inf.mp hv
  obtain ⟨nE, rfl⟩ := (mem_subSec_iff hs).1 hvE
  obtain ⟨nF, hnF⟩ := (mem_subSec_iff hs).1 hvF
  set e : ↥N := Subgroup.inclusion inf_le_right nE
  set f : ↥N := Subgroup.inclusion inf_le_right nF
  have heq : SecMod.mk hs e = SecMod.mk hs f := hnF.symm
  have hmem : (e : G) ∈ F := by
    have h1 : (e : G)⁻¹ * (f : G) ∈ N₀ :=
      (QuotMod.mk_eq_mk_iff (N := N) (N₀ := N₀) e f).mp heq
    have h2 : (f : G)⁻¹ * (e : G) ∈ N₀ := by
      simpa only [mul_inv_rev, inv_inv] using N₀.inv_mem h1
    have h3 : (f : G)⁻¹ * (e : G) ∈ F := hF h2
    have h4 : (f : G) ∈ F := nF.2.1
    have heq2 : (e : G) = (f : G) * ((f : G)⁻¹ * (e : G)) := by group
    rw [heq2]
    exact F.mul_mem h4 h3
  exact (mem_subSec_iff hs).2 ⟨⟨e, ⟨nE.2.1, hmem⟩, nE.2.2⟩, rfl⟩

theorem subSec_eq_bot_of_le {E : Subgroup G} (hEN₀ : E ≤ N₀) :
    subSec hs E = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  obtain ⟨n, hn⟩ := (mem_subSec_iff hs).1 hv
  rw [← hn, (SecMod.mk_eq_zero_iff hs _).mpr (hEN₀ n.2.1)]
  exact Submodule.zero_mem _

theorem natCard_secMod : Nat.card (SecMod hs) * Nat.card N₀ = Nat.card N := by
  have h := natCard_subSec hs hs.le (le_refl N) (E := N)
  rw [subSec_self hs] at h
  rwa [Nat.card_congr
    (Submodule.topEquiv (R := ZMod 2) (M := SecMod hs)).toEquiv] at h

theorem card_subSec_eq_two_pow [Finite G] (E : Subgroup G) :
    Nat.card (subSec hs E) = 2 ^ Module.finrank (ZMod 2) (subSec hs E) := by
  letI : Fintype (subSec hs E) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := subSec hs E)
  rw [ZMod.card] at h
  rw [Nat.card_eq_fintype_card]
  exact h

theorem map_secConj_subSec_le {E : Subgroup G} (z : ↥H)
    (hz : (z : G) ∈ Subgroup.normalizer (E : Set G)) :
    (subSec hs E).map (SecMod.secConj hs z) ≤ subSec hs E := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  obtain ⟨n, rfl⟩ := (mem_subSec_iff hs).1 hw
  rw [secConj_mk]
  refine (mem_subSec_iff hs).2 ⟨⟨(z : G) * n * (z : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp hz _).mp n.2.1, hs.conj z z.2 n n.2.2⟩, rfl⟩

theorem span_secConj_eq {S : Subgroup G} (hSH : S ≤ H) :
    Submodule.span (ZMod 2) {u | ∃ z : ↥H, (z : G) ∈ S ∧ ∃ w, u = SecMod.secConj hs z w - w} =
      subSec hs (⁅N, S⁆ ⊔ N₀) := by
  have hcomm_mem : ∀ n ∈ N, ∀ s ∈ S, ⁅n, s⁆ ∈ N := by
    intro n hn s hsS
    have h1 : s * n⁻¹ * s⁻¹ ∈ N := hs.conj s (hSH hsS) n⁻¹ (N.inv_mem hn)
    have h2 : n * (s * n⁻¹ * s⁻¹) ∈ N := N.mul_mem hn h1
    rwa [show n * (s * n⁻¹ * s⁻¹) = ⁅n, s⁆ by
      rw [commutatorElement_def]
      group] at h2
  have hNS : ⁅N, S⁆ ≤ N := Subgroup.commutator_le.mpr hcomm_mem
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro u ⟨z, hzS, w, rfl⟩
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs w
    rw [secConj_mk, SecMod.mk_conj_sub_mk hs z n]
    refine (mk_mem_subSec_iff hs le_sup_right).2 (Subgroup.mem_sup_left ?_)
    have hmem : ⁅(n : G), (z : G)⁆ ∈ ⁅N, S⁆ :=
      Subgroup.commutator_mem_commutator n.2 hzS
    have e : (z : G) * (n : G) * (z : G)⁻¹ * (n : G)⁻¹ = ⁅(n : G), (z : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    change (z : G) * (n : G) * (z : G)⁻¹ * (n : G)⁻¹ ∈ ⁅N, S⁆
    rw [e]
    exact (⁅N, S⁆).inv_mem hmem
  · let W : Submodule (ZMod 2) (SecMod hs) :=
      Submodule.span (ZMod 2) {u | ∃ z : ↥H, (z : G) ∈ S ∧ ∃ w, u = SecMod.secConj hs z w - w}
    have hW : ⁅N, S⁆ ≤ subgroupOfSubSec hs W := by
      rw [Subgroup.commutator_le]
      intro n hn s hsS
      rw [mem_subgroupOfSubSec]
      refine ⟨hcomm_mem n hn s hsS, ?_⟩
      have hgen : SecMod.secConj hs ⟨s, hSH hsS⟩ (SecMod.mk hs ⟨n, hn⟩) -
          SecMod.mk hs ⟨n, hn⟩ ∈ W :=
        Submodule.subset_span ⟨⟨s, hSH hsS⟩, hsS, SecMod.mk hs ⟨n, hn⟩, rfl⟩
      have hneg : SecMod.mk hs ⟨⁅n, s⁆, hcomm_mem n hn s hsS⟩ =
          -(SecMod.secConj hs ⟨s, hSH hsS⟩ (SecMod.mk hs ⟨n, hn⟩) -
            SecMod.mk hs ⟨n, hn⟩) := by
        rw [secConj_mk, SecMod.mk_conj_sub_mk hs]
        conv_rhs => rw [← SecMod.mk_inv]
        congr 1
        ext
        change (⁅n, s⁆ : G) = ((s : G) * (n : G) * (s : G)⁻¹ * (n : G)⁻¹)⁻¹
        rw [commutatorElement_def]
        group
      rw [hneg]
      exact W.neg_mem hgen
    have hsup : subSec hs (⁅N, S⁆ ⊔ N₀) = subSec hs ⁅N, S⁆ := by
      rw [subSec_sup hs hNS hs.le, subSec_eq_bot_of_le hs le_rfl, sup_bot_eq]
    rw [hsup]
    calc
      subSec hs ⁅N, S⁆ ≤ subSec hs (subgroupOfSubSec hs W) := subSec_mono hs hW
      _ ≤ W := by rw [subSec_subgroupOfSubSec hs W]

end Lattice

section Fixed

variable (hs : QuotMod.Hyp H N N₀)
variable [Module (ZMod 2) (SecMod hs)]

private theorem piK_mem_subSec_iff
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀)
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {E : Subgroup G} (hN₀E : N₀ ≤ E)
    (z : ↥H) (n : ↥N) :
    repSec hs hK X ψ (ψ (piK V H z)) (SecMod.mk hs n) ∈ subSec hs E ↔
      (z : G) * n * (z : G)⁻¹ ∈ E := by
  rw [repSec_apply_piK_mk hs hK X ψ z n, mk_mem_subSec_iff hs hN₀E]

theorem fixedSub_repSec
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀)
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {S : Subgroup G} (hS : S ≤ H) :
    fixedSub (repSec hs hK X ψ) ((imgK V H S).map ψ) =
      subSec hs (secCent hs S hS) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n, rfl⟩ := SecMod.mk_surjective hs v
    refine (mk_mem_subSec_iff hs (le_secCent hs hS)).2 ?_
    refine (mem_secCent hs hS).2 ⟨n.2, fun s hsS => ?_⟩
    let z : ↥H := ⟨s, hS hsS⟩
    have hx : ψ (piK V H z) ∈ (imgK V H S).map ψ := by
      refine Subgroup.mem_map.mpr ⟨piK V H z, ?_, rfl⟩
      exact (mem_imgK_iff).mpr ⟨z, hsS, rfl⟩
    have h := hv _ hx
    rw [repSec_apply_piK_mk hs hK X ψ z n] at h
    have hconj : (z : G) * n * (z : G)⁻¹ * n⁻¹ ∈ N₀ := by
      have := SecMod.mk_conj_sub_mk hs z n
      rw [h, sub_self] at this
      exact (SecMod.mk_eq_zero_iff hs _).1 this.symm
    rw [show ⁅(n : G), (z : G)⁆ = ((z : G) * n * (z : G)⁻¹ * n⁻¹)⁻¹ from by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group]
    exact N₀.inv_mem hconj
  · intro hv
    obtain ⟨n, rfl⟩ := (mem_subSec_iff hs).1 hv
    let nN : ↥N := Subgroup.inclusion inf_le_right n
    change SecMod.mk hs nN ∈ fixedSub (repSec hs hK X ψ) ((imgK V H S).map ψ)
    refine mem_fixedSub.mpr fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hzS, rfl⟩ := (mem_imgK_iff).mp hy
    change repSec hs hK X ψ (ψ (piK V H z)) (SecMod.mk hs nN) = SecMod.mk hs nN
    rw [repSec_apply_piK_mk hs hK X ψ z nN]
    have hcomm : ⁅(n : G), (z : G)⁆ ∈ N₀ := ((mem_secCent hs hS).1 n.2.1).2 z hzS
    have hconj : (z : G) * nN * (z : G)⁻¹ * nN⁻¹ ∈ N₀ := by
      rw [show (z : G) * nN * (z : G)⁻¹ * nN⁻¹ = ⁅(n : G), (z : G)⁆⁻¹ from by
        rw [commutatorElement_def]
        simp [nN]
        group]
      exact N₀.inv_mem hcomm
    rw [← sub_eq_zero, SecMod.mk_conj_sub_mk hs z nN, SecMod.mk_eq_zero_iff hs]
    exact hconj

theorem normalizer_subSec_iff (hs : QuotMod.Hyp H N N₀)
    [Module (ZMod 2) (SecMod hs)]
    (hK : ∀ k ∈ kOf V H, ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ N₀)
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {E : Subgroup G}
    (hN₀E : N₀ ≤ E) (hEN : E ≤ N) :
    H ≤ Subgroup.normalizer (E : Set G) ↔
      ∀ x : X, ∀ v ∈ subSec hs E, repSec hs hK X ψ x v ∈ subSec hs E := by
  constructor
  · intro hN x v hv
    obtain ⟨z, hz⟩ := piK_surjective V H (ψ.symm x)
    have hx : x = ψ (piK V H z) := by
      rw [← (show ψ (piK V H z) = x from by rw [hz, MulEquiv.apply_symm_apply])]
    obtain ⟨n, rfl⟩ := (mem_subSec_iff hs).1 hv
    rw [hx, piK_mem_subSec_iff hs hK ψ hN₀E z (Subgroup.inclusion inf_le_right n)]
    exact (Subgroup.mem_normalizer_iff.mp (hN z.2) _).mp n.2.1
  · intro hinv z hz
    refine Subgroup.mem_normalizer_iff.mpr fun e => ⟨fun he => ?_, fun he => ?_⟩
    · let n : ↥N := ⟨e, hEN he⟩
      have hv : SecMod.mk hs n ∈ subSec hs E := (mk_mem_subSec_iff hs hN₀E).2 he
      have h := hinv (ψ (piK V H ⟨z, hz⟩)) _ hv
      rwa [piK_mem_subSec_iff hs hK ψ hN₀E ⟨z, hz⟩ n] at h
    · let n : ↥N := ⟨(z : G) * e * (z : G)⁻¹, hEN he⟩
      have hv : SecMod.mk hs n ∈ subSec hs E := (mk_mem_subSec_iff hs hN₀E).2 he
      have h := hinv (ψ (piK V H ⟨z⁻¹, H.inv_mem hz⟩)) _ hv
      rw [piK_mem_subSec_iff hs hK ψ hN₀E ⟨z⁻¹, H.inv_mem hz⟩ n] at h
      have h' : (z : G)⁻¹ * ((z : G) * e * (z : G)⁻¹) * (z : G) ∈ E := by
        simpa [n] using h
      simpa [show (z : G)⁻¹ * ((z : G) * e * (z : G)⁻¹) * (z : G) = e by group] using h'

end Fixed

end CFSG.RankThree.GF2n.Tim81
