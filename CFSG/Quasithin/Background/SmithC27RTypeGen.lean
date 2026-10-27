module

public import CFSG.Quasithin.Background.SmithC27Star
public import CFSG.Quasithin.Background.SmithC27OTwoZ

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Center

variable {P Q : Type*} [Group P] [Group Q]

private theorem mem_center_of_commutator_mem_center' [Group.IsPerfect P] {y : P}
    (h : ∀ g : P, ⁅y, g⁆ ∈ Subgroup.center P) : y ∈ Subgroup.center P := by
  let φ : P →* ↥(Subgroup.center P) :=
    { toFun := fun g => ⟨⁅y, g⁆, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆
        have hb := Subgroup.mem_center_iff.1 (h b) a
        have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hb, mul_inv_cancel_right]) }
  have hker : commutator P ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have h1 : φ g = 1 := hker (Subgroup.mem_top g)
  have h2 : ⁅y, g⁆ = 1 := congrArg Subtype.val h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem comap_center_eq_of_perfect [Group.IsPerfect P] (π : P →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P) :
    (Subgroup.center Q).comap π = Subgroup.center P := by
  apply le_antisymm
  · intro y hy
    refine mem_center_of_commutator_mem_center' fun g => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hy (π g)).symm
  · intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := hπ q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hy g]

noncomputable def quotCenterEquivOfSurjective [Group.IsPerfect P] (π : P →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center P) :
    P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        comap_center_eq_of_perfect π hπ hker])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (Subgroup.center Q)).comp π)
      ((QuotientGroup.mk'_surjective _).comp hπ))

theorem map_center_of_mulEquiv (e : P ≃* Q) :
    (Subgroup.center P).map e.toMonoidHom = Subgroup.center Q := by
  ext q
  obtain ⟨p, rfl⟩ := e.surjective q
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hp r
    obtain ⟨s, rfl⟩ := e.surjective r
    rw [← map_mul, ← map_mul, hp s]
  · intro hp s
    apply e.injective
    rw [map_mul, map_mul, hp (e s)]

noncomputable def quotCenterCongr (e : P ≃* Q) :
    P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q :=
  QuotientGroup.congr _ _ e (map_center_of_mulEquiv e)

end Center

section Star

variable {G : Type} [Group G] [Finite G] {R K V : Subgroup G}

theorem StarHyp.nonempty_quotCenterEquiv (hs : StarHyp R K V) :
    Nonempty (((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
      (↥(autOn K V) ⧸ Subgroup.center ↥(autOn K V))) := by
  have hKV := hs.K_le_normalizer_V
  have hle := InternalSec.pCore_le_ker_autOnHom hKV hs.pCore_K_eq_bot
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hs.quasi.1
  let ρ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autOn K V) := QuotientGroup.lift _ _ hle
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hKV y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : ρ.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro p hp
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective p
    have h1 : InternalSec.autOnHom hKV l = 1 := hp
    have h2 : (l : G) ∈ Subgroup.centralizer (V : Set G) :=
      (InternalSec.mem_ker_autOnHom hKV l).1 h1
    exact mk_mem_center_of_mem_oTwoZIn (hs.inf_centralizer_le ⟨l.2, h2⟩)
  exact ⟨quotCenterEquivOfSurjective ρ hρ hker⟩

theorem StarHyp.oTwoZIn_le_centralizer (hs : StarHyp R K V)
    (hZ : Subgroup.center ↥(autOn K V) = ⊥) :
    oTwoZIn K ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have hKV := hs.K_le_normalizer_V
  have hxK : x ∈ K := oTwoZIn_le K hx
  set ρ := InternalSec.autOnHom hKV with hρ
  have hc : ρ ⟨x, hxK⟩ ∈ Subgroup.center ↥(autOn K V) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := InternalSec.autOnHom_surjective hKV y
    have hw : (⁅(⟨x, hxK⟩ : ↥K), w⁆ : ↥K) ∈ ρ.ker := by
      rw [InternalSec.mem_ker_autOnHom]
      apply hs.pCore_K_le_centralizer
      have := ((mem_oTwoZIn_iff (K := K)).1 hx).2 w w.2
      simpa [commutatorElement_def] using this
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hw
    exact hw.symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact (InternalSec.mem_ker_autOnHom hKV ⟨x, hxK⟩).1 hc

omit [Finite G] in
private theorem card_comap_of_surjective'' {A B : Type*} [Group A] [Group B] [Finite A]
    {f : A →* B} (hf : Function.Surjective f) (S : Subgroup B) :
    Nat.card (S.comap f) = Nat.card S * Nat.card f.ker := by
  have hB : Finite B := Finite.of_surjective f hf
  have h1 := (S.comap f).card_mul_index
  have h2 := S.card_mul_index
  rw [Subgroup.index_comap_of_surjective S hf] at h1
  have h3 : Nat.card A = Nat.card B * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hpos : 0 < S.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h3, ← h2]
  ring

theorem card_oTwoZIn (K : Subgroup G) :
    Nat.card ↥(oTwoZIn K) =
      Nat.card ↥(pCoreOf 2 K) * Nat.card ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have he : (oTwoZIn K).subgroupOf K =
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    exact ⟨mk_mem_center_of_mem_oTwoZIn, mem_oTwoZIn_of_mk_mem_center⟩
  have h1 : Nat.card ↥((oTwoZIn K).subgroupOf K) = Nat.card ↥(oTwoZIn K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oTwoZIn_le K)).toEquiv
  have h2 : Nat.card ↥(pCoreOf 2 K) = Nat.card ↥(CFSG.pCore 2 ↥K) := by
    rw [C124.pCoreOf_eq_map_pCore, Subgroup.card_map_of_injective K.subtype_injective]
  rw [← h1, he, card_comap_of_surjective'' (QuotientGroup.mk'_surjective _), QuotientGroup.ker_mk',
    h2, mul_comm]

theorem StarHyp.card_autOn_mul_card_center (hs : StarHyp R K V)
    (hZ : Subgroup.center ↥(autOn K V) = ⊥) :
    Nat.card ↥(autOn K V) * Nat.card ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hKC : K ⊓ Subgroup.centralizer (V : Set G) = oTwoZIn K :=
    le_antisymm hs.inf_centralizer_le (le_inf (oTwoZIn_le K) (hs.oTwoZIn_le_centralizer hZ))
  have e1 := card_eq_card_autOn_mul hs.K_le_normalizer_V
  rw [hKC, card_oTwoZIn] at e1
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have h2 : Nat.card ↥(pCoreOf 2 K) = Nat.card ↥(CFSG.pCore 2 ↥K) := by
    rw [C124.pCoreOf_eq_map_pCore, Subgroup.card_map_of_injective K.subtype_injective]
  have hpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥K) := Nat.card_pos
  rw [h2] at e1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← e2, e1]
  ring

end Star

section Perfect

variable {Γ Δ : Type*} [Group Γ] [Group Δ]

theorem eq_of_le_of_isSimpleGroup {N D : Subgroup Γ} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hND : N ≤ D) [IsSimpleGroup ↥D] : N = D := by
  have : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf D) with h | h
  · exact absurd (disjoint_self.1 ((Subgroup.subgroupOf_eq_bot.1 h).mono_right hND)) hN1
  · exact le_antisymm hND (Subgroup.subgroupOf_eq_top.1 h)

theorem eq_map_of_bijective (π : Δ →* Γ) (hπ : Function.Bijective π) {L : Subgroup Γ}
    (hL : L.Normal) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) {D : Subgroup Δ}
    (hD : ∀ a b : Δ, ⁅a, b⁆ ∈ D) [IsSimpleGroup ↥D] : L = D.map π := by
  set N := L.comap π with hNdef
  have hLN : N.map π = L := Subgroup.map_comap_eq_self_of_surjective hπ.2 L
  have hNn : N.Normal := hL.comap π
  have hNperf : ⁅N, N⁆ = N := by
    apply Subgroup.map_injective hπ.1
    rw [Subgroup.map_commutator, hLN, hperf]
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hL1
    rw [← hLN, h, Subgroup.map_bot]
  have hND : N ≤ D := by
    rw [← hNperf, Subgroup.commutator_le]
    intro a _ b _
    exact hD a b
  rw [← hLN, eq_of_le_of_isSimpleGroup hNn hN1 hND]

theorem eq_map_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (π : Equiv.Perm (Fin n) →* Γ)
    (hπ : Function.Bijective π) {L : Subgroup Γ} (hL : L.Normal) (hperf : ⁅L, L⁆ = L)
    (hL1 : L ≠ ⊥) : L = (alternatingGroup (Fin n)).map π := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  refine eq_map_of_bijective π hπ hL hperf hL1 fun a b => ?_
  rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

end Perfect

end CFSG.Quasithin.SmithC27
