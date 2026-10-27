module

public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7Rep
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec16.Item162Res7PushA7
import CFSG.RankThree.PartTwo.KFacts.KP2KleinOffenderGroup
import CFSG.GroupTheory.ChiefFactors.OddElement
import CFSG.Quasithin.Background.B2Factorization
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OffenderB10

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG
open CFSG.Open
open CFSG.Quasithin
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

private theorem a7Rep_comp_inclusion_mem_alternatingGroup (K S : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    (hJN : K ⊔ S ≤ Subgroup.normalizer (K : Set G)) (x : ↥(K ⊔ S)) :
    ((KFacts.KP2.a7Rep K φ).comp (Subgroup.inclusion hJN)) x ∈
      alternatingGroup (Fin 7) := by
  let f : ↥(K ⊔ S) →* Equiv.Perm (Fin 7) :=
    (KFacts.KP2.a7Rep K φ).comp (Subgroup.inclusion hJN)
  have hK : K.subgroupOf (K ⊔ S) ≤ (alternatingGroup (Fin 7)).comap f := by
    intro y hy
    change KFacts.KP2.a7Rep K φ (Subgroup.inclusion hJN y) ∈ alternatingGroup (Fin 7)
    have hk : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
    have h1 : (Subgroup.inclusion hJN y : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨(y : G), Subgroup.le_normalizer hk⟩ :
          ↥(Subgroup.normalizer (K : Set G))) := Subtype.ext rfl
    rw [h1]
    have h2 : (⟨(y : G), Subgroup.le_normalizer hk⟩ :
        ↥(Subgroup.normalizer (K : Set G))) =
        (⟨(⟨(y : G), hk⟩ : ↥K), Subgroup.le_normalizer hk⟩ :
          ↥(Subgroup.normalizer (K : Set G))) := Subtype.ext rfl
    rw [h2, KFacts.KP2.a7Rep_of_mem]
    exact (φ _).2
  have hS : S.subgroupOf (K ⊔ S) ≤ (alternatingGroup (Fin 7)).comap f := by
    intro y hy
    change KFacts.KP2.a7Rep K φ (Subgroup.inclusion hJN y) ∈ alternatingGroup (Fin 7)
    have h1 : (Subgroup.inclusion hJN y : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨(y : G), hSK hy⟩ : ↥(Subgroup.normalizer (K : Set G))) := Subtype.ext rfl
    have hmem : (⟨(y : G), hSK hy⟩ :
        ↥(Subgroup.normalizer (K : Set G))) ∈
        S.subgroupOf (Subgroup.normalizer (K : Set G)) := hy
    rw [h1]
    exact KFacts.KP2.map_vTwo_le_alternatingGroup g
      (hSV (Subgroup.mem_map_of_mem _ hmem))
  have htop : (⊤ : Subgroup ↥(K ⊔ S)) ≤ (alternatingGroup (Fin 7)).comap f := by
    have hsup : (⊤ : Subgroup ↥(K ⊔ S)) =
        K.subgroupOf (K ⊔ S) ⊔ S.subgroupOf (K ⊔ S) := by
      rw [← Subgroup.subgroupOf_self (K ⊔ S),
        Subgroup.subgroupOf_sup (A := K) (A' := S) (B := K ⊔ S) le_sup_left le_sup_right]
    rw [hsup]
    exact sup_le hK hS
  exact htop (Subgroup.mem_top x)

private noncomputable def theta (K S : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom) :
    ↥(K ⊔ S) →* alternatingGroup (Fin 7) :=
  MonoidHom.codRestrict
    ((KFacts.KP2.a7Rep K φ).comp
      (Subgroup.inclusion (sup_le Subgroup.le_normalizer hSK)))
    (alternatingGroup (Fin 7))
    (fun x => a7Rep_comp_inclusion_mem_alternatingGroup K S hSK φ hSV
      (sup_le Subgroup.le_normalizer hSK) x)

private theorem theta_apply (K S : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    (x : ↥(K ⊔ S)) :
    ((theta K S hSK φ hSV x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      KFacts.KP2.a7Rep K φ
        ⟨(x : G), (sup_le Subgroup.le_normalizer hSK) x.2⟩ :=
  rfl

private theorem theta_eq_one_iff (K S : Subgroup G) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {x : G} (hx : x ∈ K ⊔ S) :
    theta K S hSK φ hSV ⟨x, hx⟩ = 1 ↔ x ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := by
  have h := a7Rep_eq_one_iff_mem_pCoreOf_sup hS hSK hZ φ hx
    ((sup_le Subgroup.le_normalizer hSK) hx)
  have hincl : (Subgroup.inclusion (sup_le Subgroup.le_normalizer hSK) ⟨x, hx⟩ :
      ↥(Subgroup.normalizer (K : Set G))) =
      (⟨x, (sup_le Subgroup.le_normalizer hSK) hx⟩ :
        ↥(Subgroup.normalizer (K : Set G))) := Subtype.ext rfl
  constructor
  · intro h1
    apply h.mp
    have h2 : KFacts.KP2.a7Rep K φ
        (Subgroup.inclusion (sup_le Subgroup.le_normalizer hSK) ⟨x, hx⟩) = 1 := by
      simpa [theta] using
        congrArg (fun z : ↥(alternatingGroup (Fin 7)) => (z : Equiv.Perm (Fin 7))) h1
    simpa [hincl] using h2
  · intro h1
    apply Subtype.ext
    have h2 : KFacts.KP2.a7Rep K φ
        (Subgroup.inclusion (sup_le Subgroup.le_normalizer hSK) ⟨x, hx⟩) = 1 := by
      simpa [hincl] using h.mpr h1
    simpa [theta] using h2

private theorem theta_surjective (K S : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom) :
    Function.Surjective (theta K S hSK φ hSV) := by
  intro v
  obtain ⟨y, hy⟩ := exists_a7Rep_eq_of_mem_alternating φ v.2
  refine ⟨⟨(y : G), Subgroup.mem_sup_left (S := K) (T := S) y.2⟩, ?_⟩
  apply Subtype.ext
  have hy' : (⟨y, (sup_le Subgroup.le_normalizer hSK)
      (Subgroup.mem_sup_left (S := K) (T := S) y.2)⟩ :
        ↥(Subgroup.normalizer (K : Set G))) =
      (⟨y, Subgroup.le_normalizer y.2⟩ : ↥(Subgroup.normalizer (K : Set G))) :=
    Subtype.ext rfl
  rw [theta_apply]
  rw [hy']
  exact hy

private theorem theta_ker (K S : Subgroup G) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom) :
    (theta K S hSK φ hSV).ker =
      (CFSG.Open.pCoreOf 2 (K ⊔ S)).subgroupOf (K ⊔ S) := by
  ext x
  rw [MonoidHom.mem_ker, theta_eq_one_iff K S hS hSK hZ φ hSV x.2]
  exact Iff.rfl

private theorem relIndex_eq_card_map_theta (K S : Subgroup G) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {F : Subgroup G} (hFJ : F ≤ K ⊔ S) :
    Nat.card ((F.subgroupOf (K ⊔ S)).map (theta K S hSK φ hSV)) =
      (CFSG.Open.pCoreOf 2 (K ⊔ S)).relIndex F := by
  rw [← Subgroup.relIndex_ker (theta K S hSK φ hSV)
    (K := F.subgroupOf (K ⊔ S))]
  rw [theta_ker K S hS hSK hZ φ hSV]
  exact Subgroup.relIndex_subgroupOf hFJ

theorem le_normalizer_sup_zpowers {K S : Subgroup G} {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G)) :
    K ⊔ S ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) := by
  have htJ : t ∈ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup K S ⟨htK, htS⟩
  exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htJ)

theorem le_normalizer_pCoreOf_sup {K S : Subgroup G} {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G)) :
    K ⊔ S ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ S) : Set G) :=
  (le_normalizer_sup_zpowers htK htS).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ S))

private theorem le_normalizer_omegaOneCenterOf_pCoreOf_sup {K S : Subgroup G} {t : G}
    (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G)) :
    K ⊔ S ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer
        (Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 (K ⊔ S)) : Set G) := by
  have hQ := le_normalizer_pCoreOf_sup (K := K) (S := S) htK htS
  have hZ := CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf
    (CFSG.Open.pCoreOf 2 (K ⊔ S))
  have hU := CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneOf
    (CFSG.Quasithin.centerOf (CFSG.Open.pCoreOf 2 (K ⊔ S)))
  simpa [CFSG.Quasithin.omegaOneCenterOf] using hQ.trans (hZ.trans hU)

private theorem theta_conj (K S : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G)) (x : ↥(K ⊔ S))
    (htJ : t ∈ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G)) :
    ((theta K S hSK φ hSV ⟨t * (x : G) * t⁻¹,
        (Subgroup.mem_normalizer_iff.mp htJ x).mp x.2⟩ : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) =
      KFacts.KP2.a7Rep K φ ⟨t, htK⟩ * (theta K S hSK φ hSV x :
        Equiv.Perm (Fin 7)) * (KFacts.KP2.a7Rep K φ ⟨t, htK⟩)⁻¹ := by
  rw [theta_apply]
  have harg : (⟨t * (x : G) * t⁻¹,
      (sup_le Subgroup.le_normalizer hSK)
        ((Subgroup.mem_normalizer_iff.mp htJ x).mp x.2)⟩ :
        ↥(Subgroup.normalizer (K : Set G))) =
      (⟨t, htK⟩ : ↥(Subgroup.normalizer (K : Set G))) *
        ⟨(x : G), (sup_le Subgroup.le_normalizer hSK) x.2⟩ *
        (⟨t, htK⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ :=
    Subtype.ext rfl
  rw [harg, map_mul, map_mul, map_inv, theta_apply]

private theorem theta_mem_vTwo (K S F : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    (hFS : F ≤ S) :
    ∀ f (hf : f ∈ F),
      ((theta K S hSK φ hSV ⟨f, hFS.trans le_sup_right hf⟩ :
        alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ∈
        KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom := by
  intro f hf
  have hmem : (⟨f, hSK (hFS hf)⟩ :
      ↥(Subgroup.normalizer (K : Set G))) ∈
      S.subgroupOf (Subgroup.normalizer (K : Set G)) := hFS hf
  have hmap := hSV (Subgroup.mem_map_of_mem (KFacts.KP2.a7Rep K φ) hmem)
  have h1 : ((theta K S hSK φ hSV ⟨f, hFS.trans le_sup_right hf⟩ :
      alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
      KFacts.KP2.a7Rep K φ ⟨f, hSK (hFS hf)⟩ := by
    rw [theta_apply]
  rw [h1]
  exact hmap

private theorem theta_ne_one_of_not_le (K S F : Subgroup G) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    (hFS : F ≤ S) (hFQ : ¬ F ≤ CFSG.Open.pCoreOf 2 (K ⊔ S)) :
    ∃ f, ∃ hf : f ∈ F,
      theta K S hSK φ hSV ⟨f, hFS.trans le_sup_right hf⟩ ≠ 1 := by
  obtain ⟨f, hfF, hfQ⟩ := Set.not_subset.mp hFQ
  refine ⟨f, hfF, ?_⟩
  intro h1
  exact hfQ ((theta_eq_one_iff K S hS hSK hZ φ hSV
    (hFS.trans le_sup_right hfF)).mp h1)

private theorem card_mul_card_lt_of_chief_factor {K S R₁ R₂ F X : Subgroup G}
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (K ⊔ S) ≤ S)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G))
    (ht : KFacts.KP2.a7Rep K φ ⟨t, htK⟩ ∉ alternatingGroup (Fin 7))
    (hR₁Q : R₁ ≤ CFSG.Open.pCoreOf 2 (K ⊔ S)) (hRlt : R₂ < R₁)
    (hNR₁ : K ⊔ S ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (R₁ : Set G))
    (hNR₂ : K ⊔ S ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (R₂ : Set G))
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G))
    (hchief : ∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ R₁ →
      K ⊔ S ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (Y : Set G) →
      Y = R₂ ∨ Y = R₁)
    {j : G} (hjK : j ∈ K) (hj : Odd (orderOf j))
    (hwit : ∃ r ∈ R₁, j * r * j⁻¹ * r⁻¹ ∉ R₂)
    (hFS : F ≤ S) (hFQ : ¬ F ≤ CFSG.Open.pCoreOf 2 (K ⊔ S))
    (hX₂ : R₂ ≤ X) (hX₁ : X ≤ R₁)
    (hFX : ∀ x ∈ X, ∀ f ∈ F, f * x * f⁻¹ * x⁻¹ ∈ R₂) :
    (CFSG.Open.pCoreOf 2 (K ⊔ S)).relIndex F * Nat.card X < Nat.card R₁ := by
  classical
  let Q := CFSG.Open.pCoreOf 2 (K ⊔ S)
  let J₀ := K ⊔ S
  let H := J₀ ⊔ Subgroup.zpowers t
  have hQ2 : IsPGroup 2 Q :=
    hS.of_injective (Subgroup.inclusion hQS) (Subgroup.inclusion_injective hQS)
  have hQH : Q ≤ H := hQS.trans (le_sup_right.trans le_sup_left)
  have hHNQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf_sup htK htS
  have hR₁2 : IsPGroup 2 R₁ :=
    hS.of_injective (Subgroup.inclusion (hR₁Q.trans hQS))
      (Subgroup.inclusion_injective (hR₁Q.trans hQS))
  have hkerQ : ∀ p ∈ Q, ∀ r ∈ R₁, p * r * p⁻¹ * r⁻¹ ∈ R₂ :=
    CFSG.GroupTheory.commutator_mem_of_chief hQ2 hQH hHNQ hR₁2 hRlt hNR₁ hNR₂ hR₁₂ hchief
  let θ := theta K S hSK φ hSV
  have hθ : Function.Surjective θ := theta_surjective K S hSK φ hSV
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    (KFacts.KS14.a7_facts (↥K ⧸ CFSG.pCore 2 ↥K) ⟨φ⟩).2.1
  have hker : ∀ x : ↥J₀, θ x = 1 → ∀ r ∈ R₁,
      (x : G) * r * (x : G)⁻¹ * r⁻¹ ∈ R₂ := by
    intro x hx r hr
    exact hkerQ (x : G) ((theta_eq_one_iff K S hS hSK hZ φ hSV x.2).mp hx) r hr
  have hHNJ : H ≤ Subgroup.normalizer (J₀ : Set G) := le_normalizer_sup_zpowers htK htS
  have htH : t ∈ H := Subgroup.mem_sup_right (S := J₀) (T := Subgroup.zpowers t)
    (Subgroup.mem_zpowers t)
  have hfix : ∀ r ∈ R₁, (∀ x ∈ J₀, x * r * x⁻¹ * r⁻¹ ∈ R₂) → r ∈ R₂ := by
    intro r hr hcent
    obtain ⟨r₀, hr₀, hnr₀⟩ := hwit
    exact CFSG.GroupTheory.mem_of_commutator_mem_of_chief
      (N := H) (K := J₀) le_sup_left hHNJ hRlt hNR₁ hNR₂ hR₁₂ hchief
      ⟨j, Subgroup.mem_sup_left (S := K) (T := S) hjK, r₀, hr₀, hnr₀⟩ hr hcent
  have hJ₀R₁ : J₀ ≤ Subgroup.normalizer (R₁ : Set G) := le_sup_left.trans hNR₁
  have hJ₀R₂ : J₀ ≤ Subgroup.normalizer (R₂ : Set G) := le_sup_left.trans hNR₂
  have hlt := KFacts.KP2.card_mul_card_lt_of_section
    (J := J₀) (R₁ := R₁) (R₂ := R₂) (F := F) (X := X) θ hθ hR₁2 hRlt hR₁₂
    hJ₀R₁ hJ₀R₂ hker hfix (hNR₁ htH) (hNR₂ htH) (hHNJ htH) ht
    (fun x => theta_conj K S hSK φ hSV htK x (hHNJ htH)) (hFS.trans le_sup_right) g
    (theta_mem_vTwo K S F hSK φ hSV hFS)
    (theta_ne_one_of_not_le K S F hS hSK hZ φ hSV hFS hFQ)
    hX₂ hX₁ hFX
  have hcard : Nat.card ((F.subgroupOf J₀).map θ) = Q.relIndex F :=
    relIndex_eq_card_map_theta K S hS hSK hZ φ hSV (hFS.trans le_sup_right)
  rwa [hcard] at hlt

theorem exists_chief_factor_card_lt_of_a7 {K S W : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (K ⊔ S) ≤ S)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G))
    (ht : KFacts.KP2.a7Rep K φ ⟨t, htK⟩ ∉ alternatingGroup (Fin 7))
    (hWQ : W ≤ CFSG.Open.pCoreOf 2 (K ⊔ S))
    (hWN : K ⊔ S ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (W : Set G))
    {j : G} (hjK : j ∈ K) (hj : Odd (orderOf j))
    (hjW : ∃ w ∈ W, j * w * j⁻¹ * w⁻¹ ≠ 1) :
    ∃ R₁ R₂ : Subgroup G, R₂ < R₁ ∧ R₁ ≤ W ∧
      R₁ ≤ Subgroup.normalizer (R₂ : Set G) ∧
      K ⊔ S ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (R₁ : Set G) ∧
      K ⊔ S ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (R₂ : Set G) ∧
      ∀ F X : Subgroup G, F ≤ S → ¬ F ≤ CFSG.Open.pCoreOf 2 (K ⊔ S) →
        R₂ ≤ X → X ≤ R₁ →
        (∀ x ∈ X, ∀ f ∈ F, f * x * f⁻¹ * x⁻¹ ∈ R₂) →
        (CFSG.Open.pCoreOf 2 (K ⊔ S)).relIndex F * Nat.card X < Nat.card R₁ := by
  classical
  let Q := CFSG.Open.pCoreOf 2 (K ⊔ S)
  let J₀ := K ⊔ S
  let H := J₀ ⊔ Subgroup.zpowers t
  have hW2 : IsPGroup 2 W :=
    hS.of_injective (Subgroup.inclusion (hWQ.trans hQS))
      (Subgroup.inclusion_injective (hWQ.trans hQS))
  have hWH : W ≤ H := hWQ.trans (hQS.trans (le_sup_right.trans le_sup_left))
  have hjH : j ∈ H :=
    Subgroup.mem_sup_left (S := J₀) (T := Subgroup.zpowers t)
      (Subgroup.mem_sup_left (S := K) (T := S) hjK)
  obtain ⟨R₁, R₂, hRlt, hR₁W, hNR₁, hNR₂, hR₁₂, hchief, hwit⟩ :=
    CFSG.GroupTheory.exists_chief_factor_of_odd hW2 hWH hWN hjH hj hjW
  refine ⟨R₁, R₂, hRlt, hR₁W, hR₁₂, hNR₁, hNR₂, ?_⟩
  intro F X hFS hFQ hX₂ hX₁ hFX
  exact card_mul_card_lt_of_chief_factor hS hSK hQS φ hSV htK htS ht
    (hR₁W.trans hWQ) hRlt hNR₁ hNR₂ hR₁₂ hchief hjK hj hwit hFS hFQ hX₂ hX₁ hFX

private theorem card_le_card_relIndex_mul_card {Q U R₁ 𝔈 X S : Subgroup G}
    (hUel : IsElemAbelian 2 U) (hUS : U ≤ S) (h𝔈max : IsMaxElemAbelian S 𝔈)
    (hQcentU : Q ≤ Subgroup.centralizer (U : Set G)) (hR₁U : R₁ ≤ U)
    (hlo : R₁ ⊓ Subgroup.centralizer (𝔈 : Set G) ≤ X) (hhi : X ≤ R₁) :
    Nat.card R₁ ≤ Q.relIndex 𝔈 * Nat.card X := by
  let C := Subgroup.centralizer (𝔈 : Set G)
  have hrel : ∀ (A B : Subgroup G), A.relIndex B ≠ 0 := by
    intro A B
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h1 : X.relIndex R₁ ≤ (R₁ ⊓ C).relIndex R₁ :=
    Subgroup.relIndex_le_of_le_left hlo (hrel (R₁ ⊓ C) R₁)
  have h2 : (R₁ ⊓ C).relIndex R₁ ≤ (U ⊓ C).relIndex U := by
    rw [Subgroup.inf_relIndex_left (H := R₁) (K := C), inf_comm U C,
      Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right hR₁U (hrel C U)
  have h3 : (U ⊓ C).relIndex U ≤
      (𝔈 ⊓ Subgroup.centralizer (U : Set G)).relIndex 𝔈 :=
    offender_index_le_of_isMaxElemAbelian h𝔈max hUS hUel
  have h4 : (𝔈 ⊓ Subgroup.centralizer (U : Set G)).relIndex 𝔈 ≤
      (𝔈 ⊓ Q).relIndex 𝔈 :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf le_rfl hQcentU) (hrel (𝔈 ⊓ Q) 𝔈)
  have hchain : X.relIndex R₁ ≤ (𝔈 ⊓ Q).relIndex 𝔈 :=
    h1.trans (h2.trans (h3.trans h4))
  have hcard : Nat.card R₁ = X.relIndex R₁ * Nat.card X := by
    rw [← Subgroup.relIndex_mul_card (H := X) (K := R₁), inf_eq_left.mpr hhi]
  calc
    Nat.card R₁ = X.relIndex R₁ * Nat.card X := hcard
    _ ≤ (𝔈 ⊓ Q).relIndex 𝔈 * Nat.card X := Nat.mul_le_mul_right _ hchain
    _ = Q.relIndex 𝔈 * Nat.card X := by rw [Subgroup.inf_relIndex_left]

theorem commutator_mem_of_mem_sup_centralizer {R₁ R₂ A X : Subgroup G}
    (hRlt : R₂ < R₁) (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G))
    (hNA : A ≤ Subgroup.normalizer (R₂ : Set G))
    (hX : X = (R₁ ⊓ Subgroup.centralizer (A : Set G)) ⊔ R₂) :
    ∀ x ∈ X, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ R₂ := by
  intro x hx a ha
  let C := Subgroup.centralizer (A : Set G)
  haveI hN : (R₂.subgroupOf R₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRlt.le).mpr hR₁₂
  have hxR₁ : x ∈ R₁ := by
    rw [hX] at hx
    exact (sup_le inf_le_left hRlt.le) hx
  have hxsub : (⟨x, hxR₁⟩ : ↥R₁) ∈
      (R₁ ⊓ C).subgroupOf R₁ ⊔ R₂.subgroupOf R₁ := by
    have h : (⟨x, hxR₁⟩ : ↥R₁) ∈ X.subgroupOf R₁ := hx
    rwa [show X.subgroupOf R₁ =
      (R₁ ⊓ C).subgroupOf R₁ ⊔ R₂.subgroupOf R₁ by
        rw [hX, Subgroup.subgroupOf_sup (A := R₁ ⊓ C) (A' := R₂) (B := R₁)
          inf_le_left hRlt.le]] at h
  obtain ⟨b, hb, c, hc, hbc⟩ := Subgroup.mem_sup_of_normal_right.mp hxsub
  have hbR₁ : (b : G) ∈ R₁ := b.2
  have hbC : (b : G) ∈ C := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).2
  have hcR₂ : (c : G) ∈ R₂ := Subgroup.mem_subgroupOf.mp hc
  have hbc' : (b : G) * (c : G) = x := by
    have := congrArg Subtype.val hbc
    simpa using this
  have hba : a * (b : G) = (b : G) * a :=
    Subgroup.mem_centralizer_iff.mp hbC a ha
  have hac : a * (c : G) * a⁻¹ ∈ R₂ :=
    (Subgroup.mem_normalizer_iff.mp (hNA ha) (c : G)).mp hcR₂
  have hcomm : a * (c : G) * a⁻¹ * (c : G)⁻¹ ∈ R₂ :=
    R₂.mul_mem hac (R₂.inv_mem hcR₂)
  have hid : a * ((b : G) * (c : G)) * a⁻¹ * ((b : G) * (c : G))⁻¹ =
      (b : G) * (a * (c : G) * a⁻¹ * (c : G)⁻¹) * (b : G)⁻¹ := by
    rw [show a * ((b : G) * (c : G)) = (a * (b : G)) * (c : G) by group, hba]
    group
  rw [← hbc', hid]
  exact (Subgroup.mem_normalizer_iff.mp (hR₁₂ hbR₁) _).mp hcomm

theorem thompsonJ_le_pCoreOf_sup_of_a7 {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (K ⊔ S) ≤ S)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G))
    (ht : KFacts.KP2.a7Rep K φ ⟨t, htK⟩ ∉ alternatingGroup (Fin 7))
    {j : G} (hjK : j ∈ K) (hj : Odd (orderOf j))
    (hjU : ∃ u ∈ Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 (K ⊔ S)),
      j * u * j⁻¹ * u⁻¹ ≠ 1) :
    Quasithin.thompsonJ S ≤ CFSG.Open.pCoreOf 2 (K ⊔ S) := by
  classical
  let Q := CFSG.Open.pCoreOf 2 (K ⊔ S)
  let U := Quasithin.omegaOneCenterOf Q
  let J₀ := K ⊔ S
  let H := J₀ ⊔ Subgroup.zpowers t
  by_contra hJ
  obtain ⟨𝔈, h𝔈max, h𝔈Q⟩ : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q := by
    by_contra h
    apply hJ
    refine iSup₂_le fun A hA => ?_
    by_contra hAQ
    exact h ⟨A, hA, hAQ⟩
  have h𝔈S : 𝔈 ≤ S := h𝔈max.1
  have hUQ : U ≤ Q := CFSG.Quasithin.A4.omegaOneCenterOf_le Q
  have hUS : U ≤ S := hUQ.trans hQS
  have hUel : IsElemAbelian 2 U :=
    ⟨⟨⟨fun a b => Subtype.ext
        (CFSG.Quasithin.A4.mul_comm_of_mem_omegaOneCenterOf a.2 b.2)⟩⟩,
      fun x hx => CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩
  have hQcentU : Q ≤ Subgroup.centralizer (U : Set G) :=
    (Subgroup.le_centralizer_iff).mpr
      ((CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf Q).trans
        (CFSG.Quasithin.A4.centerOf_le_centralizer Q))
  have hWN : H ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_omegaOneCenterOf_pCoreOf_sup (K := K) (S := S) htK htS
  obtain ⟨R₁, R₂, hRlt, hR₁U, hR₁₂, hNR₁, hNR₂, hFF⟩ :=
    exists_chief_factor_card_lt_of_a7 hS hSK hQS φ hSV htK htS ht hUQ hWN hjK hj hjU
  let C := Subgroup.centralizer (𝔈 : Set G)
  let X := (R₁ ⊓ C) ⊔ R₂
  have hX₂ : R₂ ≤ X := le_sup_right
  have hX₁ : X ≤ R₁ := sup_le inf_le_left hRlt.le
  have hNA : 𝔈 ≤ Subgroup.normalizer (R₂ : Set G) :=
    (h𝔈S.trans (le_sup_right.trans le_sup_left)).trans hNR₂
  have hFX : ∀ x ∈ X, ∀ f ∈ 𝔈, f * x * f⁻¹ * x⁻¹ ∈ R₂ :=
    commutator_mem_of_mem_sup_centralizer hRlt hR₁₂ hNA (X := X)
      (A := 𝔈) (by rfl)
  have hlt := hFF 𝔈 X h𝔈S h𝔈Q hX₂ hX₁ hFX
  have hge : Nat.card R₁ ≤ Q.relIndex 𝔈 * Nat.card X :=
    card_le_card_relIndex_mul_card (S := S) hUel hUS h𝔈max hQcentU hR₁U
      (show R₁ ⊓ Subgroup.centralizer (𝔈 : Set G) ≤ X from le_sup_left) hX₁
  exact absurd hlt (not_lt.mpr hge)

theorem le_normalizer_thompsonJ_of_a7 {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (K ⊔ S) ≤ S)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {g : Equiv.Perm (Fin 7)}
    (hSV : (S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (KFacts.KP2.a7Rep K φ) ≤ KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom)
    {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G))
    (ht : KFacts.KP2.a7Rep K φ ⟨t, htK⟩ ∉ alternatingGroup (Fin 7))
    {j : G} (hjK : j ∈ K) (hj : Odd (orderOf j))
    (hjU : ∃ u ∈ Quasithin.omegaOneCenterOf (CFSG.Open.pCoreOf 2 (K ⊔ S)),
      j * u * j⁻¹ * u⁻¹ ≠ 1) :
    K ⊔ S ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer (Quasithin.thompsonJ S : Set G) := by
  let Q := CFSG.Open.pCoreOf 2 (K ⊔ S)
  have hJ : Quasithin.thompsonJ S ≤ Q :=
    thompsonJ_le_pCoreOf_sup_of_a7 hS hSK hQS φ hSV htK htS ht hjK hj hjU
  have hJeq : Quasithin.thompsonJ S = Quasithin.thompsonJ Q :=
    Quasithin.thompsonJ_eq_of_le hJ hQS
  have hHNQ : K ⊔ S ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer (Q : Set G) :=
    le_normalizer_pCoreOf_sup (K := K) (S := S) htK htS
  rw [hJeq]
  exact hHNQ.trans (Quasithin.normalizer_le_normalizer_thompsonJ Q)

end CFSG.RankThree.PartTwo.Sec16

end
