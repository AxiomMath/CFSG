module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecBHBBorel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) a]
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hz', map_one])

theorem dvd_card_normalizer_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B)
    {m : ℕ} (h : ∀ S : Subgroup B, IsSylowTwoOf S ⊤ →
      m ∣ Nat.card ↥(Subgroup.normalizer (S : Set B))) :
    ∀ S : Subgroup A, IsSylowTwoOf S ⊤ → m ∣ Nat.card ↥(Subgroup.normalizer (S : Set A)) := by
  intro S hS
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hS.2.1.map _, ?_⟩
    show ¬ 2 ∣ (S.map e.toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    have := hS.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  have h1 := h _ hS'
  rw [← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective e.injective] at h1
  exact h1

theorem card_normalizer_subgroupOf {Γ : Type*} [Group Γ] {Ks S : Subgroup Γ} (hS : S ≤ Ks) :
    Nat.card ↥(Subgroup.normalizer ((S.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks)) =
      Nat.card ↥(Ks ⊓ Subgroup.normalizer (S : Set Γ)) := by
  have heq : (Subgroup.normalizer ((S.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks)).map Ks.subtype =
      Ks ⊓ Subgroup.normalizer (S : Set Γ) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      have hg' : g ∈ Subgroup.normalizer ((S.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks) := hg
      show (g : Γ) ∈ Subgroup.normalizer (S : Set Γ)
      rw [Subgroup.mem_normalizer_iff] at hg' ⊢
      intro x
      by_cases hx : x ∈ Ks
      · have := hg' ⟨x, hx⟩
        simpa [Subgroup.mem_subgroupOf] using this
      · have h1 : x ∉ S := fun h => hx (hS h)
        have h2 : (g : Γ) * x * (g : Γ)⁻¹ ∉ S := by
          intro h
          apply hx
          have := Ks.mul_mem (Ks.mul_mem (Ks.inv_mem g.2) (hS h)) g.2
          simpa [mul_assoc] using this
        exact iff_of_false h1 h2
    · rintro x ⟨hxK, hxN⟩
      exact ⟨⟨x, hxK⟩, mem_normalizer_subgroupOf hxN, rfl⟩
  rw [← heq, Subgroup.card_map_of_injective Ks.subtype_injective]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_starHom {H X K : Subgroup G} (hKH : K ≤ H) (hOK : pCoreOf 2 K ≤ kerIn X H) :
    ∃ φ : ↥K ⧸ CFSG.Open.pCore 2 ↥K →* ↥(E2.star X H K), Function.Surjective φ ∧
      ∀ k : ↥K, ((φ (k : ↥K ⧸ CFSG.Open.pCore 2 ↥K) : ↥(E2.star X H K)) : E2.StarQuot X H) =
        QuotientGroup.mk' ((kerIn X H).subgroupOf H) (Subgroup.inclusion hKH k) := by
  set π : ↥H →* E2.StarQuot X H := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hπdef
  have hmem : ∀ k : ↥K, π (Subgroup.inclusion hKH k) ∈ E2.star X H K := fun k =>
    ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  set ψ : ↥K →* ↥(E2.star X H K) := (π.comp (Subgroup.inclusion hKH)).codRestrict _ hmem
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, h, hh, rfl⟩
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, Subtype.ext rfl⟩
  have hOKψ : CFSG.Open.pCore 2 ↥K ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show π (Subgroup.inclusion hKH k) = 1
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hOK ⟨k, hk, rfl⟩
  refine ⟨QuotientGroup.lift _ ψ hOKψ, fun y => ?_, fun k => rfl⟩
  obtain ⟨k, rfl⟩ := hψs y
  exact ⟨k, rfl⟩

omit [Finite G] in
theorem nonempty_mulEquiv_star {H X K : Subgroup G} (hKH : K ≤ H)
    (hOK : pCoreOf 2 K ≤ kerIn X H) (hKJ : K ⊓ kerIn X H ≤ pCoreOf 2 K) {Y : Type*} [Group Y]
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Y) : Nonempty (↥(E2.star X H K) ≃* Y) := by
  obtain ⟨φ, hφs, hφk⟩ := exists_starHom hKH hOK
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    rw [hφk, QuotientGroup.mk'_apply, OneMemClass.coe_one, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    obtain ⟨k', hk', hkk'⟩ := hKJ ⟨k.2, h1⟩
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff,
      show k = k' from Subtype.ext hkk'.symm]
    exact hk'
  have e1 : ↥K ⧸ CFSG.Open.pCore 2 ↥K ≃* ↥(E2.star X H K) := MulEquiv.ofBijective φ ⟨hφi, hφs⟩
  have e2 : ↥K ⧸ CFSG.Open.pCore 2 ↥K ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2).symm
  exact ⟨(e1.symm.trans e2).trans e⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
