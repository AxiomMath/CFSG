module

public import CFSG.RankThree.PartOne.S15K.KtData
public import CFSG.RankThree.PartOne.S15K.ThetaMerge
import CFSG.RankThree.PartOne.S12.Sec158
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_sup_zpowers_eq {p : ℕ} (hp : p.Prime) {D C : Subgroup G} (hDC : D ≤ C)
    (hDcard : Nat.card D = p ^ 2) (hCcard : Nat.card C = p ^ 3) (hpow : ∀ x ∈ C, x ^ p = 1) :
    ∃ y ∈ C, y ∉ D ∧ orderOf y = p ∧ D ⊔ Subgroup.zpowers y = C := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyC, hyD⟩ : ∃ y ∈ C, y ∉ D := by
    by_contra hcon
    push Not at hcon
    have hle : C ≤ D := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    rw [hDcard, hCcard] at this
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hy1 : y ≠ 1 := fun h => hyD (h ▸ D.one_mem)
  refine ⟨y, hyC, hyD, orderOf_eq_prime (hpow y hyC) hy1, ?_⟩
  set M := D ⊔ Subgroup.zpowers y with hM
  have hMC : M ≤ C := sup_le hDC (Subgroup.zpowers_le.2 hyC)
  have hDM : D ≤ M := le_sup_left
  have hdvd : Nat.card ↥M ∣ p ^ 3 := hCcard ▸ Subgroup.card_dvd_of_le hMC
  obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hle1 : p ^ 2 ≤ Nat.card ↥M := hDcard ▸ Subgroup.card_le_of_le hDM
  have hyM : y ∈ M := (le_sup_right : Subgroup.zpowers y ≤ M) (Subgroup.mem_zpowers y)
  have hk3 : k = 3 := by
    by_contra hne
    have hk2 : k = 2 := by
      have h2 : 2 ≤ k := by
        by_contra hlt
        have : k ≤ 1 := by omega
        have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
        have h3 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      omega
    subst hk2
    have : D = M := Subgroup.eq_of_le_of_card_ge hDM (by rw [hMk, hDcard])
    exact hyD (this ▸ hyM)
  subst hk3
  exact Subgroup.eq_of_le_of_card_ge hMC (by rw [hMk, hCcard])

omit [Finite G] in
theorem map_centralizer_singleton_eq_of_sup {D C : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.centralizer (D : Set G)) (hsup : D ⊔ Subgroup.zpowers y = C) :
    (Subgroup.centralizer
        ({(⟨y, hy⟩ : ↥(Subgroup.centralizer (D : Set G)))} : Set ↥(Subgroup.centralizer (D : Set G)))).map
        (Subgroup.centralizer (D : Set G)).subtype = Subgroup.centralizer (C : Set G) := by
  ext g
  rw [← hsup]
  constructor
  · rintro ⟨hh, hhc, rfl⟩
    rw [Sec158.mem_centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    refine ⟨hh.2, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 hhc
    exact congrArg Subtype.val this
  · intro hg
    rw [Sec158.mem_centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff] at hg
    have hy' : (⟨g, hg.1⟩ : ↥(Subgroup.centralizer (D : Set G))) ∈
        Subgroup.centralizer ({(⟨y, hy⟩ : ↥(Subgroup.centralizer (D : Set G)))} :
          Set ↥(Subgroup.centralizer (D : Set G))) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hg.2)
    exact ⟨_, hy', rfl⟩

theorem exists_thetaComp_of_kZero (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {f : ℕ} {t : MulAut E} (hAt : KFAt p E f t)
    {D : Subgroup G} (hDt : D ≤ autFixedInG E t) (hD1 : D ≠ ⊥)
    {y : G} (hyt : y ∈ autFixedInG E t) (hyord : orderOf y = p)
    (hsup : D ⊔ Subgroup.zpowers y = autFixedInG E t) :
    ∃ M ∈ thetaComponents p ↥(Subgroup.centralizer (D : Set G)),
      (kZero p E t).subgroupOf (Subgroup.centralizer (D : Set G)) ≤ M := by
  have hp := h.prime
  have hp3 := h.three_lt
  have hEab : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hDE : D ≤ E := hDt.trans (Subgroup.map_subtype_le _)
  have hyE : y ∈ E := (Subgroup.map_subtype_le _) hyt
  set C : Subgroup G := Subgroup.centralizer (D : Set G) with hC
  have hyC : y ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro d hd
    exact hEab d (hDE hd) y hyE
  obtain ⟨hne, hmod, hcent, hmov, -⟩ := hAt
  have hKθ : kZero p E t ∈ thetaCompCentralizer p (autFixedInG E t) :=
    kZero_mem_thetaCompCentralizer hp (isQuasisimple_of_model hmod) rfl
  obtain ⟨hKC', hKθ'⟩ := mem_image_map_subtype_iff_of_le.1 hKθ
  have hDC := map_centralizer_singleton_eq_of_sup hyC hsup
  have hKy : (kZero p E t).subgroupOf C ∈ thetaComponentsAt p (⟨y, hyC⟩ : ↥C) :=
    Sec158.mem_thetaComponentsAt_subgroupOf_of_centralizer hp (⟨y, hyC⟩ : ↥C) hDC hKC' hKθ'
  obtain ⟨b, hbD, hb1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hD1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  have hsimple : IsSimpleGroup G := h.setup.1
  have hCne : C ≠ ⊤ := by
    intro htop
    have hb : Subgroup.centralizer ({b} : Set G) ≠ ⊤ :=
      EmbeddingFixedResidual.centralizer_ne_top_of_simple h.setup.2.1 hb1
    apply hb
    rw [eq_top_iff, ← htop]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbD)
  have hHK : CFSG.IsKGroup ↥C := h.setup.2.2.1 _ hCne
  have hHE : evenRank ↥C ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  have hyord' : orderOf (⟨y, hyC⟩ : ↥C) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hyord
  exact h82 hS ↥C hHK hHE p hp hp3 ⟨y, hyC⟩ hyord' _ hKy

omit [Finite G] in
theorem kZero_le_centralizer_of_le {p : ℕ} {E : Subgroup G} {t : MulAut E} {D : Subgroup G}
    (hD : D ≤ autFixedInG E t) : kZero p E t ≤ Subgroup.centralizer (D : Set G) :=
  (kZero_le_centralizer p E t).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hD))

omit [Finite G] in
theorem isPerfect_subgroupOf {X C : Subgroup G} (hXC : X ≤ C) (h : Group.IsPerfect ↥X) :
    Group.IsPerfect ↥(X.subgroupOf C) :=
  Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXC).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hXC).symm.surjective

omit [Finite G] in
theorem subgroupOf_ne_bot {X C : Subgroup G} (hXC : X ≤ C) (h : X ≠ ⊥) : X.subgroupOf C ≠ ⊥ := by
  intro hbot
  apply h
  rw [eq_bot_iff]
  intro z hz
  have : (⟨z, hXC hz⟩ : ↥C) ∈ X.subgroupOf C := Subgroup.mem_subgroupOf.2 hz
  rw [hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem exists_thetaComp_pair (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {f f' : ℕ} {t s : MulAut E}
    (hAt : KFAt p E f t) (hAs : KFAt p E f s) (hf' : 2 ≤ f')
    (hU : CentrallyUThree f' ↥(kZero p E t ⊔ kZero p E s)) (hts : t * s ≠ s * t)
    {D : Subgroup G} (hD : D = autFixedInG E t ⊓ autFixedInG E s) (hDcard : Nat.card D = p ^ 2)
    (hCt : Nat.card (autFixedInG E t) = p ^ 3) (hCs : Nat.card (autFixedInG E s) = p ^ 3) :
    ∃ M ∈ thetaComponents p ↥(Subgroup.centralizer (D : Set G)),
      (kZero p E t).subgroupOf (Subgroup.centralizer (D : Set G)) ≤ M ∧
      (kZero p E s).subgroupOf (Subgroup.centralizer (D : Set G)) ≤ M := by
  have hp := h.prime
  set C : Subgroup G := Subgroup.centralizer (D : Set G) with hC
  have hDt : D ≤ autFixedInG E t := hD ▸ inf_le_left
  have hDs : D ≤ autFixedInG E s := hD ▸ inf_le_right
  have hD1 : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hpowt : ∀ x ∈ autFixedInG E t, x ^ p = 1 := fun x hx =>
    Sec12Three.pow_eq_one_of_mem_E h ((Subgroup.map_subtype_le _) hx)
  have hpows : ∀ x ∈ autFixedInG E s, x ^ p = 1 := fun x hx =>
    Sec12Three.pow_eq_one_of_mem_E h ((Subgroup.map_subtype_le _) hx)
  obtain ⟨y₁, hy₁C, -, hy₁ord, hsup₁⟩ := exists_sup_zpowers_eq hp hDt hDcard hCt hpowt
  obtain ⟨y₂, hy₂C, -, hy₂ord, hsup₂⟩ := exists_sup_zpowers_eq hp hDs hDcard hCs hpows
  obtain ⟨M₁, hM₁, hKM₁⟩ := exists_thetaComp_of_kZero hS h82 h hAt hDt hD1 hy₁C hy₁ord hsup₁
  obtain ⟨M₂, hM₂, hKM₂⟩ := exists_thetaComp_of_kZero hS h82 h hAs hDs hD1 hy₂C hy₂ord hsup₂
  have hK1C : kZero p E t ≤ C := kZero_le_centralizer_of_le hDt
  have hK2C : kZero p E s ≤ C := kZero_le_centralizer_of_le hDs
  obtain ⟨-, hmod, -, -, hlift⟩ := hAt
  obtain ⟨-, hmods, -, -, hlifts⟩ := hAs
  have hq := isQuasisimple_of_model hmod
  have hperf : Group.IsPerfect ↥(kZero p E t) := hq.1
  have hne : kZero p E t ≠ ⊥ := by
    intro hbot
    have : Subsingleton ↥(kZero p E t) := by
      rw [hbot]
      infer_instance
    have h2 := hq.2.1.toNontrivial
    have : Subsingleton (↥(kZero p E t) ⧸ Subgroup.center ↥(kZero p E t)) := inferInstance
    exact (not_subsingleton _) this
  have hsupeq : (kZero p E t).subgroupOf C ⊔ (kZero p E s).subgroupOf C =
      (kZero p E t ⊔ kZero p E s).subgroupOf C := (Subgroup.subgroupOf_sup hK1C hK2C).symm
  have hU' : CentrallyUThree f' ↥((kZero p E t).subgroupOf C ⊔ (kZero p E s).subgroupOf C) :=
    centrallyUThree_of_equiv
      ((MulEquiv.subgroupCongr hsupeq).trans
        (Subgroup.subgroupOfEquivOfLe (sup_le hK1C hK2C))).symm hU
  rcases eq_or_commute_of_thetaComponents hp hM₁ hM₂ hKM₁ hKM₂
      (isPerfect_subgroupOf hK1C hperf) (subgroupOf_ne_bot hK1C hne) hf' hU' with heq | hcomm
  · exact ⟨M₁, hM₁, hKM₁, heq ▸ hKM₂⟩
  · exfalso
    obtain ⟨kt, hkt, hktK, hktt⟩ := hlift
    obtain ⟨ks, hks, hksK, hkss⟩ := hlifts
    have h1 : (⟨kt, hK1C hktK⟩ : ↥C) ∈ (kZero p E t).subgroupOf C := Subgroup.mem_subgroupOf.2 hktK
    have h2 : (⟨ks, hK2C hksK⟩ : ↥C) ∈ (kZero p E s).subgroupOf C := Subgroup.mem_subgroupOf.2 hksK
    have h3 := hcomm _ h1 _ h2
    have h4 : kt * ks = ks * kt := congrArg Subtype.val h3
    apply hts
    rw [← hktt, ← hkss, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h4

end CFSG.RankThree.PartOne.S15K
