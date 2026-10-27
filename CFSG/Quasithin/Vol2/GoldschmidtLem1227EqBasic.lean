module

public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

namespace Lem1227Eq

variable {G : Type} [Group G]

theorem cjSub_eq_of_mem_normalizer {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) : cjSub t K = K := by
  ext x
  rw [mem_cjSub]
  simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ht) x).symm

theorem not_exists_cjSub_ne {T K : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ¬ ∃ t ∈ T, cjSub t K ≠ K := by
  rintro ⟨t, ht, hne⟩
  exact hne (cjSub_eq_of_mem_normalizer (hTK ht))

section Cores

variable [Finite G] {T K H M₀ : Subgroup G}

theorem pCoreOf_le_pCoreOf_of_normal (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 K).trans hKH) ?_ (LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact hHK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)

theorem inf_pCoreOf_le (hKH : K ≤ H) : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  intro k hk
  have hkQ : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk),
      (Subgroup.mem_normalizer_iff.1 hkQ x).1 hx.2⟩
  · intro hx
    have hxK : x ∈ K := by
      simpa [mul_assoc] using K.mul_mem (K.mul_mem (K.inv_mem hk) hx.1) hk
    exact ⟨hxK, (Subgroup.mem_normalizer_iff.1 hkQ x).2 hx.2⟩

end Cores

theorem mem_pCore_iff_coe {K : Subgroup G} (x : ↥K) :
    x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff x).symm

theorem mk_comm_iff {X : Type*} [Group X] (N : Subgroup X) [N.Normal] (a b : X) :
    (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a ↔
      a * b * a⁻¹ * b⁻¹ ∈ N := by
  have h1 : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : X ⧸ N) =
      ⁅(QuotientGroup.mk a : X ⧸ N), (QuotientGroup.mk b : X ⧸ N)⁆ := by
    rw [commutatorElement_def]
    rfl
  rw [← QuotientGroup.eq_one_iff, h1, commutatorElement_eq_one_iff_mul_comm]

section Kernel

variable [Finite G] {T K H M₀ : Subgroup G}

@[expose] def KerChar (M₀ H K : Subgroup G) : Prop :=
  ∀ x : G, x ∈ kerIn M₀ H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
    ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H

theorem mem_kerIn_iff_central (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hker : KerChar M₀ H K) (k : ↥K) :
    (k : G) ∈ kerIn M₀ H ↔
      (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hQH : pCoreOf 2 H ≤ H := LieType.BorelTits.pCoreOf_le 2 H
  rw [hker (k : G)]
  have key : ∀ y : ↥K, ((k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H) ↔
      (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk k := by
    intro y
    rw [mk_comm_iff, mem_pCore_iff_coe]
    have hc : (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem k.2 y.2) (K.inv_mem k.2)) (K.inv_mem y.2)
    constructor
    · intro h
      exact inf_pCoreOf_le hKH ⟨hc, h⟩
    · intro h
      exact pCoreOf_le_pCoreOf_of_normal hKH hHK h
  constructor
  · rintro ⟨-, hk⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H y => exact ((key y).1 (hk y (Subgroup.mem_sup_left y.2))).symm
  · intro hc
    refine ⟨Subgroup.mem_sup_left k.2, ?_⟩
    have hcen : ∀ y : ↥K, ((k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H) := fun y =>
      (key y).2 (Subgroup.mem_center_iff.1 hc (QuotientGroup.mk y)).symm
    have hQN : ((pCoreOf 2 H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2
        (LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    let π : ↥H →* ↥H ⧸ (pCoreOf 2 H).subgroupOf H := QuotientGroup.mk' _
    let k' : ↥H := ⟨k, hKH k.2⟩
    let S₁ : Subgroup ↥H :=
      (Subgroup.centralizer ({π k'} : Set (↥H ⧸ (pCoreOf 2 H).subgroupOf H))).comap π
    have hS₁ : ∀ y : ↥H, y ∈ S₁ ↔ ((k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H) := by
      intro y
      have h1 := mk_comm_iff ((pCoreOf 2 H).subgroupOf H) k' y
      rw [Subgroup.mem_subgroupOf] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← h1]
      show π y ∈ Subgroup.centralizer _ ↔ _
      rw [Subgroup.mem_centralizer_iff]
      simp only [Set.mem_singleton_iff, forall_eq]
      exact Iff.rfl
    have hKS : K ≤ S₁.map H.subtype := fun y hy =>
      ⟨⟨y, hKH hy⟩, (hS₁ _).2 (hcen ⟨y, hy⟩), rfl⟩
    have hQS : pCoreOf 2 H ≤ S₁.map H.subtype := fun q hq =>
      ⟨⟨q, hQH hq⟩, (hS₁ _).2 (by
        have : (k : G) * q * (k : G)⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 H
            (hKH k.2)) q).1 hq
        exact (pCoreOf 2 H).mul_mem this ((pCoreOf 2 H).inv_mem hq)), rfl⟩
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (sup_le hKS hQS) hy
    exact (hS₁ y').1 hy'

end Kernel

section Star

variable [Finite G] {T K H M₀ : Subgroup G}

abbrev starMk (M H : Subgroup G) (h : ↥H) : E2.StarQuot M H := QuotientGroup.mk h

omit [Finite G] in
theorem mem_star_iff {M X : Subgroup G} {y : E2.StarQuot M H} :
    y ∈ E2.star M H X ↔ ∃ h : ↥H, (h : G) ∈ X ∧ starMk M H h = y := by
  unfold E2.star
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  exact ⟨fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩, fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩⟩

theorem nonempty_mulEquiv_star (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      ↥(E2.star M₀ H K)) := by
  have hOK : pCoreOf 2 K ≤ kerIn M₀ H :=
    (pCoreOf_le_pCoreOf_of_normal hKH hHK).trans hmin.pCoreOf_le_kerIn
  obtain ⟨φ, hφs, hφk⟩ := Vol2.Ch11.SecB.exists_starHom hKH hOK
  let e₂ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ CFSG.Open.pCore 2 ↥K :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)
  let φ' : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(E2.star M₀ H K) := φ.comp e₂.toMonoidHom
  have hφ's : Function.Surjective φ' := hφs.comp e₂.surjective
  have hker' : φ'.ker = Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MonoidHom.mem_ker, ← mem_kerIn_iff_central hKH hHK hker k]
      have h1 := hφk k
      have h2 : φ' (QuotientGroup.mk k) = φ (QuotientGroup.mk k) := rfl
      rw [h2, ← OneMemClass.coe_eq_one, h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's)⟩

omit [Finite G] in
theorem conj_mem_star {M X : Subgroup G} {t : G} (htH : t ∈ H)
    (htX : t ∈ Subgroup.normalizer (X : Set G)) {y : E2.StarQuot M H}
    (hy : y ∈ E2.star M H X) :
    starMk M H ⟨t, htH⟩ * y * (starMk M H ⟨t, htH⟩)⁻¹ ∈ E2.star M H X := by
  obtain ⟨h, hh, rfl⟩ := mem_star_iff.1 hy
  refine mem_star_iff.2 ⟨⟨t, htH⟩ * h * ⟨t, htH⟩⁻¹, ?_, rfl⟩
  simpa using (Subgroup.mem_normalizer_iff.1 htX h).1 hh

omit [Finite G] in
theorem star_le_normalizer_star {M X : Subgroup G}
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    E2.star M H T ≤ Subgroup.normalizer (E2.star M H X : Set (E2.StarQuot M H)) := by
  intro d hd
  obtain ⟨h, hh, rfl⟩ := mem_star_iff.1 hd
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_star (h.2) (hTX hh) hy
  · intro hy
    have h1 := conj_mem_star (M := M) (X := X) (t := (h : G)⁻¹) (H.inv_mem h.2)
      (Subgroup.inv_mem _ (hTX hh)) hy
    have h2 : starMk M H ⟨(h : G)⁻¹, H.inv_mem h.2⟩ = (starMk M H h)⁻¹ := rfl
    rw [h2] at h1
    simpa [mul_assoc] using h1

omit [Finite G] in
theorem star_le_normalizer (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    E2.star M₀ H T ≤ Subgroup.normalizer (E2.star M₀ H K : Set (E2.StarQuot M₀ H)) :=
  star_le_normalizer_star hTK

theorem isSylowTwoOf_star (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) :
    IsPGroup 2 ↥(E2.star M₀ H T) ∧
      IsSylowTwoOf (E2.star M₀ H (T ⊓ K)) (E2.star M₀ H K) := by
  let J' := (kerIn M₀ H).subgroupOf H
  let π : ↥H →* E2.StarQuot M₀ H := QuotientGroup.mk' J'
  have hT := Setup.Wreath.isSylowTwoOf_map_hom hmin.isSylow π
  have hTK : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hmin.isSylow hKH hHK
  let ρ : ↥K →* E2.StarQuot M₀ H := π.comp (Subgroup.inclusion hKH)
  have hS := Setup.Wreath.isSylowTwoOf_map_hom hTK ρ
  have e1 : (T.subgroupOf H).map π = E2.star M₀ H T := rfl
  have e2 : ρ.range = E2.star M₀ H K := by
    ext y
    rw [MonoidHom.mem_range, mem_star_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKH k, k.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have e3 : ((T ⊓ K).subgroupOf K).map ρ = E2.star M₀ H (T ⊓ K) := by
    ext y
    rw [mem_star_iff, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.1 hk, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh.2⟩, Subgroup.mem_subgroupOf.2 hh, rfl⟩
  rw [e1] at hT
  rw [e2, e3] at hS
  exact ⟨hT.2.1, hS⟩

omit [Finite G] in
theorem inner_star {M₀ : Subgroup G} (hKH : K ≤ H)
    (hinner : ∀ t ∈ T, ∃ k ∈ K, ∀ x ∈ K, (k⁻¹ * t) * x * (k⁻¹ * t)⁻¹ * x⁻¹ ∈ kerIn M₀ H) :
    ∀ d ∈ E2.star M₀ H T, ∃ k ∈ E2.star M₀ H K, ∀ x ∈ E2.star M₀ H K,
      d * x * d⁻¹ = k * x * k⁻¹ := by
  intro d hd
  obtain ⟨h, hh, rfl⟩ := mem_star_iff.1 hd
  obtain ⟨k, hkK, hk⟩ := hinner h hh
  refine ⟨starMk M₀ H ⟨k, hKH hkK⟩, mem_star_iff.2 ⟨⟨k, hKH hkK⟩, hkK, rfl⟩, fun x hx => ?_⟩
  obtain ⟨x₀, hx₀, rfl⟩ := mem_star_iff.1 hx
  set k' : ↥H := ⟨k, hKH hkK⟩ with hk'
  set c : ↥H := k'⁻¹ * h with hcdef
  have hcomm : starMk M₀ H c * starMk M₀ H x₀ = starMk M₀ H x₀ * starMk M₀ H c := by
    refine (mk_comm_iff ((kerIn M₀ H).subgroupOf H) c x₀).2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [hcdef, hk'] using hk x₀ hx₀
  have hh' : h = k' * c := by simp [hcdef]
  have hmk : starMk M₀ H h = starMk M₀ H k' * starMk M₀ H c := by
    rw [hh']
    rfl
  rw [hmk]
  calc starMk M₀ H k' * starMk M₀ H c * starMk M₀ H x₀ * (starMk M₀ H k' * starMk M₀ H c)⁻¹
      = starMk M₀ H k' * (starMk M₀ H c * starMk M₀ H x₀) * (starMk M₀ H c)⁻¹ *
          (starMk M₀ H k')⁻¹ := by group
    _ = starMk M₀ H k' * (starMk M₀ H x₀ * starMk M₀ H c) * (starMk M₀ H c)⁻¹ *
          (starMk M₀ H k')⁻¹ := by rw [hcomm]
    _ = starMk M₀ H k' * starMk M₀ H x₀ * (starMk M₀ H k')⁻¹ := by group

omit [Finite G] in
theorem star_mono {M X Y : Subgroup G} (h : X ≤ Y) : E2.star M H X ≤ E2.star M H Y := by
  intro y hy
  obtain ⟨h', hh, rfl⟩ := mem_star_iff.1 hy
  exact mem_star_iff.2 ⟨h', h hh, rfl⟩

@[expose] noncomputable def starHom (M : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M H K) :=
  ((QuotientGroup.mk' ((kerIn M H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict _
    fun k => mem_star_iff.2 ⟨Subgroup.inclusion hKH k, k.2, rfl⟩

omit [Finite G] in
theorem starHom_surjective (M : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starHom M hKH) := by
  rintro ⟨y, hy⟩
  obtain ⟨h, hh, rfl⟩ := mem_star_iff.1 hy
  exact ⟨⟨h, hh⟩, rfl⟩

end Star

section Hyp

variable [Finite G]

theorem reducedAggregate_elem_central (X : Subgroup G) :
    (∀ v ∈ reducedAggregate X, v ^ 2 = 1) ∧
      pCoreOf 2 X ≤ Subgroup.centralizer (reducedAggregate X : Set G) := by
  obtain ⟨-, -, hle⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  have key : ∀ a ∈ primeReducedAggregate ↥X 2, a ∈ CFSG.pCore 2 ↥X ∧
      (∀ k ∈ CFSG.pCore 2 ↥X, k * a = a * k) ∧ a ^ 2 = 1 := fun a ha =>
    BlueprintB2.mem_centerTorsion_iff.1 (hle ha)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (key a ha).2.2
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hc' : c ∈ CFSG.pCore 2 ↥X := by exact hc
    exact (congrArg Subtype.val ((key a ha).2.1 c hc')).symm

theorem hyp_facts {T K V : Subgroup G} (h : Hyp1223 G T K V) :
    (∀ v ∈ V, v ^ 2 = 1) ∧ pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := by
  have hV : V ≤ reducedAggregate (K ⊔ T) := h.irrPlus.1
  obtain ⟨h1, h2⟩ := reducedAggregate_elem_central (K ⊔ T)
  refine ⟨fun v hv => h1 v (hV hv), ?_⟩
  have hle : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
    pCoreOf_le_pCoreOf_of_normal le_sup_left (sup_le Subgroup.le_normalizer h.normalizes)
  exact fun x hx => Subgroup.centralizer_le (show (V : Set G) ⊆ reducedAggregate (K ⊔ T) from hV)
    (h2 (hle hx))

end Hyp

end Lem1227Eq

end CFSG.Quasithin.H13
