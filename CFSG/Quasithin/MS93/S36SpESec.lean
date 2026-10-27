module

public import CFSG.Quasithin.MS93.S36SpEBase
public import CFSG.Quasithin.MS93.S38EFFHyp

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

section SecMod

variable {M A B : Subgroup G}

structure SecData (M A B : Subgroup G) (S : Type) [CommGroup S] (p : ↥A →* S)
    (ρ : ↥M →* MulAut S) : Prop where
  hMA : M ≤ Subgroup.normalizer (A : Set G)
  surj : Function.Surjective p
  ker : ∀ a : ↥A, p a = 1 ↔ (a : G) ∈ B
  conj : ∀ (m : ↥M) (a : ↥A) (h : (m : G) * a * (m : G)⁻¹ ∈ A), ρ m (p a) = p ⟨_, h⟩

theorem exists_secMod (hBA : B ≤ A) (hMA : M ≤ Subgroup.normalizer (A : Set G))
    (hMB : M ≤ Subgroup.normalizer (B : Set G)) (hAA : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) :
    ∃ (S : Type) (_ : CommGroup S) (p : ↥A →* S) (ρ : ↥M →* MulAut S), SecData M A B S p ρ := by
  have hN : (B.subgroupOf A).Normal := ⟨fun b hb a => by
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    have h := hAA a a.2 b (hBA hb)
    have he : ((a * b * a⁻¹ : ↥A) : G) = ⁅(a : G), (b : G)⁆ * b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [he]
    exact B.mul_mem h hb⟩
  let inst : CommGroup (↥A ⧸ B.subgroupOf A) :=
    { (QuotientGroup.Quotient.group (B.subgroupOf A)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
              Subgroup.mem_subgroupOf]
            have h := hAA _ (A.inv_mem b.2) _ (A.inv_mem a.2)
            have he : (((a * b)⁻¹ * (b * a) : ↥A) : G) = ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
              group
            rw [he]
            exact h }
  let c : ↥M → ↥A ≃* ↥A := fun m =>
    { toFun := fun a => ⟨(m : G) * a * (m : G)⁻¹, conj_mem hMA m.2 a.2⟩
      invFun := fun a => ⟨(m : G)⁻¹ * a * (m : G), conj_inv_mem hMA m.2 a.2⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hc : ∀ m : ↥M, (B.subgroupOf A).map (c m).toMonoidHom = B.subgroupOf A := by
    intro m
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb
      rw [Subgroup.mem_subgroupOf]
      exact conj_mem hMB m.2 hb
    · intro ha
      refine ⟨(c m).symm a, ?_, (c m).apply_symm_apply a⟩
      rw [Subgroup.mem_subgroupOf] at ha
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact conj_inv_mem hMB m.2 ha
  let ρ : ↥M →* MulAut (↥A ⧸ B.subgroupOf A) :=
    { toFun := fun m => QuotientGroup.congr _ _ (c m) (hc m)
      map_one' := by
        ext y
        induction y using QuotientGroup.induction_on with
        | H a =>
          apply congrArg (QuotientGroup.mk (s := B.subgroupOf A))
          exact Subtype.ext (by simp [c])
      map_mul' := fun m n => by
        ext y
        induction y using QuotientGroup.induction_on with
        | H a =>
          apply congrArg (QuotientGroup.mk (s := B.subgroupOf A))
          exact Subtype.ext (by simp [c, mul_assoc]) }
  refine ⟨↥A ⧸ B.subgroupOf A, inst, QuotientGroup.mk' _, ρ, hMA,
    QuotientGroup.mk'_surjective _, fun a => ?_, fun m a h => rfl⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

variable {S : Type} [CommGroup S] {p : ↥A →* S} {ρ : ↥M →* MulAut S}

namespace SecData

variable (hs : SecData M A B S p ρ)
include hs

theorem eq_iff (a a' : ↥A) : p a = p a' ↔ (a : G) * (a' : G)⁻¹ ∈ B := by
  have h := hs.ker (a * a'⁻¹)
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  simpa using h

theorem rho_eq_one_iff (m : ↥M) :
    ρ m = 1 ↔ ∀ a ∈ A, (m : G) * a * (m : G)⁻¹ * a⁻¹ ∈ B := by
  constructor
  · intro h1 a ha
    have h2 := hs.conj m ⟨a, ha⟩ (conj_mem hs.hMA m.2 ha)
    rw [h1, MulAut.one_apply, eq_comm, hs.eq_iff] at h2
    exact h2
  · intro h
    refine MulEquiv.ext fun s => ?_
    obtain ⟨a, rfl⟩ := hs.surj s
    rw [hs.conj m a (conj_mem hs.hMA m.2 a.2), MulAut.one_apply, hs.eq_iff]
    exact h a a.2

end SecData

@[expose] def fixSec (A B E : Subgroup G) (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup G where
  carrier := {a | a ∈ A ∧ ∀ e ∈ E, e * a * e⁻¹ * a⁻¹ ∈ B}
  one_mem' := ⟨A.one_mem, fun e _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.mul_mem ha hb, fun e he => ?_⟩
    have e1 : e * (a * b) * e⁻¹ * (a * b)⁻¹ =
        (e * a * e⁻¹ * a⁻¹) * (a * (e * b * e⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e1]
    exact B.mul_mem (ha' e he) (conj_mem hAB ha (hb' e he))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨A.inv_mem ha, fun e he => ?_⟩
    have e1 : e * a⁻¹ * e⁻¹ * a⁻¹⁻¹ = a⁻¹ * (e * a * e⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e1]
    exact conj_mem hAB (A.inv_mem ha) (B.inv_mem (ha' e he))

theorem mem_fixSec {A B E : Subgroup G} {hAB : A ≤ Subgroup.normalizer (B : Set G)} {a : G} :
    a ∈ fixSec A B E hAB ↔ a ∈ A ∧ ∀ e ∈ E, e * a * e⁻¹ * a⁻¹ ∈ B := Iff.rfl

theorem fixSec_le {A B E : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    fixSec A B E hAB ≤ A := fun _ ha => ha.1

namespace SecData

variable {S : Type} [CommGroup S] {p : ↥A →* S} {ρ : ↥M →* MulAut S}
variable (hs : SecData M A B S p ρ)
include hs

theorem mem_fixV_iff {E : Subgroup G} (hEM : E ≤ M) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (a : ↥A) : p a ∈ fixV ((E.subgroupOf M).map ρ) ↔ (a : G) ∈ fixSec A B E hAB := by
  rw [mem_fixV, mem_fixSec]
  constructor
  · intro h
    refine ⟨a.2, fun e he => ?_⟩
    have h1 := h (ρ ⟨e, hEM he⟩) ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    rw [hs.conj ⟨e, hEM he⟩ a (conj_mem hs.hMA (hEM he) a.2), hs.eq_iff] at h1
    exact h1
  · rintro ⟨-, h⟩ _ ⟨m, hm, rfl⟩
    rw [hs.conj m a (conj_mem hs.hMA m.2 a.2), hs.eq_iff]
    exact h _ (Subgroup.mem_subgroupOf.1 hm)

theorem index_fixV {E : Subgroup G} (hEM : E ≤ M) (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    (fixV ((E.subgroupOf M).map ρ)).index = (fixSec A B E hAB).relIndex A := by
  rw [← Subgroup.index_comap_of_surjective _ hs.surj]
  congr 1
  ext a
  rw [Subgroup.mem_comap, hs.mem_fixV_iff hEM hAB, Subgroup.mem_subgroupOf]

omit hs in
theorem card_map {E : Subgroup G} (hEM : E ≤ M) {D : Subgroup G}
    (hD : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ D) :
    Nat.card ((E.subgroupOf M).map ρ) = D.relIndex E := by
  rw [← Subgroup.relIndex_ker]
  have hker : ρ.ker = D.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, hD, Subgroup.mem_subgroupOf]
  rw [hker, Subgroup.relIndex_subgroupOf hEM]

theorem isIrrRep (hBA : B ≤ A) {L : Subgroup G} (hLM : L ≤ M) (hsq : ∀ a ∈ A, a ^ 2 ∈ B)
    (hQ : ∀ q ∈ pCoreOf 2 M, ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ B)
    (hmax : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → B ≤ J → J ≤ A →
      J = B ∨ J = A)
    (hL : ∃ l ∈ L, ∃ a ∈ A, l * a * l⁻¹ * a⁻¹ ∉ B) : S38E.IsIrrRep L ρ where
  sq v := by
    obtain ⟨a, rfl⟩ := hs.surj v
    rw [← map_pow, hs.ker]
    exact hsq a a.2
  pCore m hm := (hs.rho_eq_one_iff m).2 fun a ha => hQ m hm a ha
  irr W hW := by
    set J : Subgroup G := (W.comap p).map A.subtype with hJ
    have hmemJ : ∀ a : ↥A, (a : G) ∈ J ↔ p a ∈ W := by
      intro a
      constructor
      · rintro ⟨a', ha', he⟩
        have : a' = a := Subtype.ext he
        rw [← this]
        exact ha'
      · intro ha
        exact ⟨a, ha, rfl⟩
    have hJA : J ≤ A := Subgroup.map_subtype_le _
    have hBJ : B ≤ J := fun b hb => (hmemJ ⟨b, hBA hb⟩).2 (by
      rw [(hs.ker ⟨b, hBA hb⟩).2 hb]
      exact W.one_mem)
    have hJn : M ≤ Subgroup.normalizer (J : Set G) := by
      have key : ∀ m : ↥M, ∀ x ∈ J, (m : G) * x * (m : G)⁻¹ ∈ J := by
        intro m x hx
        have hxA := hJA hx
        rw [show x = ((⟨x, hxA⟩ : ↥A) : G) from rfl, hmemJ] at hx
        rw [hmemJ ⟨_, conj_mem hs.hMA m.2 hxA⟩, ← hs.conj m ⟨x, hxA⟩]
        exact hW m _ hx
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key ⟨m, hm⟩ x, fun hx => ?_⟩
      have := key ⟨m, hm⟩⁻¹ _ hx
      simpa [mul_assoc] using this
    rcases hmax J hJn hBJ hJA with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨a, rfl⟩ := hs.surj w
      have : (a : G) ∈ J := (hmemJ a).2 hw
      rw [h] at this
      rw [Subgroup.mem_bot, hs.ker]
      exact this
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨a, rfl⟩ := hs.surj w
      have : (a : G) ∈ J := by rw [h]; exact a.2
      exact (hmemJ a).1 this
  ne := by
    obtain ⟨l, hl, a, ha, hla⟩ := hL
    exact ⟨⟨l, hLM hl⟩, hl, fun h1 => hla ((hs.rho_eq_one_iff _).1 h1 a ha)⟩

end SecData

theorem commutator_le_of_centralizes {A B L : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (h : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ * a⁻¹ ∈ B) : ⁅A, L⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro a ha l hl
  have e : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹ * a⁻¹⁻¹) * a⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact conj_mem hAB ha (h l hl a⁻¹ (A.inv_mem ha))

end SecMod

end CFSG.Quasithin.MS93.S36E
