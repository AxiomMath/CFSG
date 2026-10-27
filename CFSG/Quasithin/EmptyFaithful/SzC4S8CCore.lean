module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8CComm
public import CFSG.Quasithin.EmptyFaithful.SzC4S8CMod

public section

namespace CFSG.Quasithin.SzC4S8C

open CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {F : Type} [Field F] [Fintype F]

theorem rigid_core (hF : Fintype.card F = 2) {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α)
    (hΦ : IsSumOfNaturalModulesVia L (frattiniIn Q) (centerOf Q) α true 1)
    (hQ₂ : IsSumOfNaturalModulesVia L (Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G))
      (frattiniIn Q) α true 2)
    (hQ : IsSumOfNaturalModulesVia L Q (Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G)) α
      false 2)
    (hZ : centerOf (Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G)) ≤ frattiniIn Q)
    {c : G} (hc2 : c * c = 1) (hcQ : ∀ q ∈ Q, q * c * q⁻¹ = c)
    (hcL : ∀ l ∈ L, l * c * l⁻¹ = c) {x : G} (hxQ : x ∈ Q)
    (hx : ∀ q ∈ Q, ⁅x, q⁆ = 1 ∨ ⁅x, q⁆ = c) : ∀ q ∈ Q, x * q = q * x := by
  classical
  by_cases hc1 : c = 1
  · intro q hq
    rcases hx q hq with h | h
    · exact commutatorElement_eq_one_iff_mul_comm.mp h
    · rw [hc1] at h
      exact commutatorElement_eq_one_iff_mul_comm.mp h
  set Φ := frattiniIn Q with hΦdef
  set Q₂ := Q ⊓ Subgroup.centralizer (Φ : Set G) with hQ₂def
  set Z := centerOf Q with hZdef
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
  have hQ₂Q : Q₂ ≤ Q := inf_le_left
  have hZQ : Z ≤ Q := inf_le_left
  have hcΦ : ∀ h ∈ Φ, h * c * h⁻¹ = c := fun h hh => hcQ h (hΦQ hh)
  have hQ₂Φ : ∀ u ∈ Q₂, ∀ w ∈ Φ, ⁅u, w⁆ = 1 := fun u hu w hw =>
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hu.2 w hw).symm
  have hLQ : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := fun l hl q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQ.1 hl) q).mp hq
  have hLQ₂ : ∀ l ∈ L, ∀ q ∈ Q₂, l * q * l⁻¹ ∈ Q₂ := fun l hl q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQ₂.1 hl) q).mp hq
  have hxΦ : ∀ f ∈ Φ, ⁅x, f⁆ = 1 := by
    intro f hf
    obtain ⟨f', hf', rfl⟩ := hf
    have hker := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 2)
      (commHomR Q c x hcQ hx) (zpowers_comm c) (zpowers_sq hc2)
    have h1 := hker hf'
    rw [MonoidHom.mem_ker] at h1
    exact congrArg Subtype.val h1
  have hxQ₂ : x ∈ Q₂ := ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun f hf =>
    (commutatorElement_eq_one_iff_mul_comm.mp (hxΦ f hf)).symm⟩
  obtain ⟨u, hu⟩ := exists_gl hF
  obtain ⟨g, hg⟩ := hα ⟨u, S1567.mem_statedSL_of_card_two hF u⟩
  have hgN : moduleAct true (α g : Matrix.GeneralLinearGroup (Fin 3) F) = cmF hF := by
    rw [hg]
    exact hu
  have hxz : ∀ z ∈ Q₂, ⁅x, z⁆ = 1 := fun z hz =>
    comm_eq_one_of_recur hc2 hcQ hcL g.2 hΦQ hQ₂Q hQ₂Φ hLQ hLQ₂
      (rel_dual hF hQ₂ g hgN) hxQ₂ hx hz
  have hxZ₂ : x ∈ centerOf Q₂ := ⟨hxQ₂, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (commutatorElement_eq_one_iff_mul_comm.mp (hxz z hz)).symm⟩
  have hxΦ' : x ∈ Φ := hZ hxZ₂
  have hxZ : x ∈ Z := by
    by_contra hxZ
    have hΦY : ∀ f ∈ Φ, ∀ q ∈ Q, ⁅f, q⁆ = 1 ∨ ⁅f, q⁆ = c := by
      intro f hf q hq
      by_cases hfZ : f ∈ Z
      · left
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp hfZ.2 q hq).symm
      · obtain ⟨n, hn⟩ := orbit_dual hF hΦ g hgN x hxΦ' hxZ f hf hfZ
        have hpow : ∀ m : ℕ, (g : G) ^ m ∈ L := fun m => L.pow_mem g.2 m
        have hQn : ∀ m : ℕ, ∀ q ∈ Q, ((g : G) ^ m)⁻¹ * q * (g : G) ^ m ∈ Q := fun m q hq => by
          have := hLQ _ (L.inv_mem (hpow m)) q hq
          simpa using this
        have hxn := commMod_conj hx (hcL _ (hpow n)) (hQn n)
        have hfe : f = (f * ((g : G) ^ n * x * ((g : G) ^ n)⁻¹)⁻¹) *
            ((g : G) ^ n * x * ((g : G) ^ n)⁻¹) := by group
        rw [hfe, comm_mul_left_eq (c := c) hcQ (hZQ hn) (hxn q hq),
          commutatorElement_eq_one_iff_mul_comm.mpr
            (Subgroup.mem_centralizer_iff.mp hn.2 q hq).symm, mul_one]
        exact hxn q hq
    obtain ⟨-, -, β₃, hβ₃s, hβ₃k, -⟩ := hΦ
    obtain ⟨-, -, β₁, hβ₁s, hβ₁k, -⟩ := hQ
    have hqf : ∀ q ∈ Q, ∀ f ∈ Φ, ⁅q, f⁆ = 1 ∨ ⁅q, f⁆ = c := by
      intro q hq f hf
      rw [← commutatorElement_inv]
      rcases hΦY f hf q hq with h | h
      · left
        rw [h]
        simp
      · right
        rw [h]
        exact inv_eq_of_mul_eq_one_right hc2
    have hker : ∀ (q : G) (hq : q ∈ Q), β₃.ker ≤ (commHomR Φ c q hcΦ (hqf q hq)).ker := by
      intro q hq f hf
      rw [hβ₃k, Subgroup.mem_subgroupOf] at hf
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show ⁅q, (f : G)⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hf.2 q hq)
    let H : ∀ q : G, q ∈ Q →
        (Multiplicative (Fin 1 → Fin 3 → F) →* ↥(Subgroup.zpowers c)) := fun q hq =>
      MonoidHom.liftOfSurjective β₃ hβ₃s ⟨commHomR Φ c q hcΦ (hqf q hq), hker q hq⟩
    have hH : ∀ (q : G) (hq : q ∈ Q) (f : ↥Φ),
        ((H q hq (β₃ f) : ↥(Subgroup.zpowers c)) : G) = ⁅q, (f : G)⁆ := by
      intro q hq f
      simp only [H, MonoidHom.liftOfRightInverse_comp_apply]
      rfl
    let sI : Multiplicative (Fin 2 → Fin 3 → F) → ↥Q := Function.surjInv hβ₁s
    let Ξ : Multiplicative (Fin 2 → Fin 3 → F) →
        (Multiplicative (Fin 1 → Fin 3 → F) →* ↥(Subgroup.zpowers c)) := fun w =>
      H ((sI w : ↥Q) : G) (sI w).2
    have hΞ : Function.Injective Ξ := by
      intro w w' hww
      set t : ↥Q := sI w with ht
      set t' : ↥Q := sI w' with ht'
      have htw : β₁ t = w := Function.surjInv_eq hβ₁s w
      have htw' : β₁ t' = w' := Function.surjInv_eq hβ₁s w'
      have hcomm : ∀ f ∈ Φ, ⁅(t : G), f⁆ = ⁅(t' : G), f⁆ := by
        intro f hf
        have h1 := hH t t.2 ⟨f, hf⟩
        have h2 := hH t' t'.2 ⟨f, hf⟩
        have h3 : (H t t.2 (β₃ ⟨f, hf⟩) : G) = (H t' t'.2 (β₃ ⟨f, hf⟩) : G) :=
          congrArg (fun φ => ((φ (β₃ ⟨f, hf⟩) : ↥(Subgroup.zpowers c)) : G)) hww
        rw [h1, h2] at h3
        exact h3
      have hZ1 : ∀ f ∈ Φ, ⁅f, ((t * t'⁻¹ : ↥Q) : G)⁆ = 1 := by
        intro f hf
        have e : commHomR Q c f hcQ (hΦY f hf) t = commHomR Q c f hcQ (hΦY f hf) t' := by
          apply Subtype.ext
          show ⁅f, (t : G)⁆ = ⁅f, (t' : G)⁆
          rw [← commutatorElement_inv (t : G) f, ← commutatorElement_inv (t' : G) f, hcomm f hf]
        have e1 : commHomR Q c f hcQ (hΦY f hf) (t * t'⁻¹) = 1 := by
          rw [map_mul, map_inv, e, mul_inv_cancel]
        exact congrArg Subtype.val e1
      have hQ2mem : (t * t'⁻¹ : ↥Q) ∈ Q₂.subgroupOf Q := by
        rw [Subgroup.mem_subgroupOf]
        refine ⟨(t * t'⁻¹ : ↥Q).2, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
        exact commutatorElement_eq_one_iff_mul_comm.mp (hZ1 f hf)
      rw [← hβ₁k, MonoidHom.mem_ker, map_mul, map_inv, htw, htw', mul_inv_eq_one] at hQ2mem
      exact hQ2mem
    have h64 : Nat.card (Multiplicative (Fin 2 → Fin 3 → F)) = 64 := by
      rw [natCard_mult hF]
      norm_num
    have h8 : Nat.card (Multiplicative (Fin 1 → Fin 3 → F)) = 8 := by
      rw [natCard_mult hF]
      norm_num
    have hfin : Finite (Multiplicative (Fin 1 → Fin 3 → F) →* ↥(Subgroup.zpowers c)) :=
      Finite.of_injective (fun f => (f : Multiplicative (Fin 1 → Fin 3 → F) →
        ↥(Subgroup.zpowers c))) DFunLike.coe_injective
    have hle := Nat.card_le_card_of_injective Ξ hΞ
    have hle2 : Nat.card (Multiplicative (Fin 1 → Fin 3 → F) →* ↥(Subgroup.zpowers c)) ≤
        Nat.card (Multiplicative (Fin 1 → Fin 3 → F)) :=
      card_monoidHom_le (p := 2) (fun a b => mul_comm a b)
        (fun a => by rw [pow_two]; exact mul_self_eq_one hF a)
        (card_zpowers_two hc2 hc1)
    omega
  intro q hq
  exact (Subgroup.mem_centralizer_iff.mp hxZ.2 q hq).symm

end Core

end CFSG.Quasithin.SzC4S8C
