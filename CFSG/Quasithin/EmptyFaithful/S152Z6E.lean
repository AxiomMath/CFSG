module

public import CFSG.Quasithin.EmptyFaithful.S152Z6B
public import CFSG.Quasithin.EmptyFaithful.S152Z6C
public import CFSG.Quasithin.EmptyFaithful.S152Z6D
public import CFSG.Quasithin.EmptyFaithful.S152UOff

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S152Z6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_mul_le_of_isMaxElemAbelian {H U A B₁ : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H) (hB₁A : B₁ ≤ A) :
    Nat.card B₁ * Nat.card ↥(U ⊓ Subgroup.centralizer (B₁ : Set G)) ≤
      Nat.card A * Nat.card ↥(B₁ ⊓ U) := by
  set C := U ⊓ Subgroup.centralizer (B₁ : Set G) with hC
  have hB₁e : IsElemAbelian 2 B₁ := B2F.isElemAbelian_mono hB₁A hA.2.1
  have hCe : IsElemAbelian 2 C := B2F.isElemAbelian_mono inf_le_left hU
  have hcomm : ∀ b ∈ B₁, ∀ c ∈ C, b * c = c * b := fun b hb c hc =>
    Subgroup.mem_centralizer_iff.1 hc.2 b hb
  have hDe : IsElemAbelian 2 (B₁ ⊔ C) := B2F.isElemAbelian_sup_of_commute hB₁e hCe hcomm
  have hDH : B₁ ⊔ C ≤ H := sup_le (hB₁A.trans hA.1) (inf_le_left.trans hUH)
  have hDcard : Nat.card ↥(B₁ ⊔ C) * Nat.card ↥(B₁ ⊓ C) = Nat.card B₁ * Nat.card C :=
    B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : B₁ ⊓ C = B₁ ⊓ U := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_left
    · intro x hx
      refine ⟨hx.1, hx.2, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
      exact B2F.isElemAbelian_comm hA.2.1 (hB₁A hb) (hB₁A hx.1)
  rw [hinf] at hDcard
  have hle : Nat.card ↥(B₁ ⊔ C) ≤ Nat.card A := hA.2.2 _ hDH hDe
  calc Nat.card B₁ * Nat.card C = Nat.card ↥(B₁ ⊔ C) * Nat.card ↥(B₁ ⊓ U) := hDcard.symm
    _ ≤ Nat.card A * Nat.card ↥(B₁ ⊓ U) := Nat.mul_le_mul_right _ hle

omit [Finite G] in
theorem card_sup_zpowers_of_involution {C : Subgroup G} {y : G} (hcomm : ∀ c ∈ C, c * y = y * c)
    (hy2 : y * y = 1) (hyC : y ∉ C) : Nat.card ↥(C ⊔ Subgroup.zpowers y) = 2 * Nat.card ↥C := by
  have hcomm' : ∀ c ∈ C, ∀ z ∈ Subgroup.zpowers y, c * z = z * c := by
    intro c hc z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (hcomm c hc) k)
  have hy1 : y ≠ 1 := fun h => hyC (h ▸ C.one_mem)
  have hP : Nat.card ↥(Subgroup.zpowers y) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hinf : C ⊓ Subgroup.zpowers y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rcases S152O4.eq_one_or_eq_of_mem_zpowers_two hy2 hz.2 with h | h
    · exact h
    · exact absurd (h ▸ hz.1) hyC
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm'
  rw [hinf, Subgroup.card_bot, hP] at hcard
  omega

theorem offender_of_data4 {T Mc M H A : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h15201 : Lemma15201Concl T Mc M) (φ : OTwoQuot H ≃* S152N.W3)
    (hD : Data4 (V154 T Mc M) H A) :
    ∃ B₁ : Subgroup G, B₁ ≤ A ∧ (B₁ ⊓ pCoreOf 2 H).relIndex B₁ = 2 ∧
      Nat.card B₁ *
          Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (B₁ : Set G)) =
        Nat.card A * Nat.card ↥(B₁ ⊓ conjClosure (V154 T Mc M) H) := by
  classical
  set V := V154 T Mc M with hVdef
  set Q := pCoreOf 2 H with hQ
  set B := A ⊓ Q with hB
  set U := conjClosure V H with hU
  have hV16 : Nat.card ↥V = 16 := h15201.card
  have hAH : A ≤ H := hD.maxA.1
  have hAel : IsElemAbelian 2 A := hD.maxA.2.1
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hAel ha hb
  have hreg : ∀ S : Finset (Subgroup G), (∀ V' ∈ S, (∃ h ∈ H, V' = conjSubgroup V h) ∧
      A ⊓ Subgroup.normalizer (V' : Set G) ≤ Q) → S.card ≤ 4 := fun S hS =>
    regular_conj_card_le_four hs hH φ hAH hAel hD.rel S hS
  obtain ⟨h, hh, hact, x, hxA, hxQ, hxN⟩ := exists_active_stabilized_of_reg hs hH hV16 hD hreg
  obtain ⟨hB2, hC4⟩ := active_facts hs hH hV16 hD hh hact
  set X := conjSubgroup V h with hX
  have hXU : X ≤ U := conjSubgroup_le_conjClosure hh
  have hcomm : ⁅X, Subgroup.zpowers x⁆ ≤ X ⊓ Subgroup.centralizer (B : Set G) := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact commutator_le_of_le_normalizer' (Subgroup.zpowers_le.2 hxN) le_rfl
    · have h1 : ⁅X, Subgroup.zpowers x⁆ ≤ ⁅U, A⁆ :=
        Subgroup.commutator_mono hXU (Subgroup.zpowers_le.2 hxA)
      have h2 := (h1.trans (commutator_conjClosure_le hD))
      rw [hD.fix] at h2
      exact h2.trans inf_le_right
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hAel.2 x hxA
  obtain ⟨b₀, hb₀, hxb₀⟩ :=
    tau_lemma hs hH h15201 φ (inf_le_right : B ≤ Q) hh hB2 hC4 (hAH hxA) hxN hx2 hcomm
  have hb₀A : b₀ ∈ A := hb₀.1
  have hb₀Q : b₀ ∈ Q := hb₀.2
  set x' := x * b₀ with hx'
  have hx'A : x' ∈ A := A.mul_mem hxA hb₀A
  have hx'Q : x' ∉ Q := fun hq => hxQ (by
    have := Q.mul_mem hq (Q.inv_mem hb₀Q)
    simpa [hx', mul_assoc] using this)
  have hx'2 : x' * x' = 1 := by rw [← pow_two]; exact hAel.2 x' hx'A
  set UB := U ⊓ Subgroup.centralizer (A : Set G) with hUB
  set K := B ⊓ Subgroup.centralizer (U : Set G) with hK
  set CB := B ⊓ Subgroup.centralizer (X : Set G) with hCB
  have hB4 : Nat.card ↥B = 4 * Nat.card ↥K := hD.idxB
  have hKCB : K ≤ CB := le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hXU))
  have hUBK : UB ≤ K := by
    intro y hy
    have hyAU : y ∈ A ⊓ U := by rw [← hD.AU]; exact hy
    have hyC : y ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun u hu => B2F.isElemAbelian_comm hD.uElem hu hy.1
    exact ⟨⟨hyAU.1, hD.cA ⟨hyAU.1, hyC⟩⟩, hyC⟩
  have hCBc : Nat.card ↥CB = 2 * Nat.card ↥K := by
    have hB2' : CB.relIndex B = 2 := hB2
    have h1 : 2 * Nat.card ↥CB = Nat.card ↥B := by
      have := Subgroup.relIndex_mul_card CB B
      rw [inf_eq_left.2 inf_le_left, hB2'] at this
      exact this
    omega
  have hA16 : Nat.card ↥A = 16 * Nat.card ↥K := by
    have hrelB : B.relIndex A = 4 := hD.rel
    have h1 : 4 * Nat.card ↥B = Nat.card ↥A := by
      have := Subgroup.relIndex_mul_card B A
      rw [hrelB, inf_eq_left.2 inf_le_left] at this
      exact this
    omega
  set B₁ := CB ⊔ Subgroup.zpowers x' with hB₁
  have hCBA : CB ≤ A := inf_le_left.trans inf_le_left
  have hB₁A : B₁ ≤ A := sup_le hCBA (Subgroup.zpowers_le.2 hx'A)
  have hx'CB : x' ∉ CB := fun hc => hx'Q hc.1.2
  have hB₁card : Nat.card ↥B₁ = 2 * Nat.card ↥CB :=
    card_sup_zpowers_of_involution (fun c hc => hAcomm c (hCBA hc) x' hx'A) hx'2 hx'CB
  have hrel : (B₁ ⊓ Q).relIndex B₁ = 2 := by
    have h1 : CB.relIndex B₁ = 2 := by
      have := Subgroup.relIndex_mul_card CB B₁
      rw [inf_eq_left.2 le_sup_left] at this
      refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥CB)) ?_
      rw [this, hB₁card]
    have hCBle : CB ≤ B₁ ⊓ Q := le_inf le_sup_left (inf_le_left.trans inf_le_right)
    have hdvd : (B₁ ⊓ Q).relIndex B₁ ∣ CB.relIndex B₁ := Subgroup.relIndex_dvd_of_le_left B₁ hCBle
    rw [h1] at hdvd
    have hne1 : (B₁ ⊓ Q).relIndex B₁ ≠ 1 := fun h =>
      hx'Q ((Subgroup.relIndex_eq_one.1 h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x'))).2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hB₁U : B₁ ⊓ U = UB := by
    refine le_antisymm (fun y hy => ?_) (le_inf (hUBK.trans (hKCB.trans le_sup_left)) inf_le_left)
    have hyAU : y ∈ A ⊓ U := ⟨hB₁A hy.1, hy.2⟩
    rw [← hD.AU] at hyAU
    exact hyAU
  have hB₁C : B₁ ≤ Subgroup.centralizer (X : Set G) :=
    sup_le inf_le_right (Subgroup.zpowers_le.2 hxb₀)
  have hXC : X ≤ Subgroup.centralizer (B₁ : Set G) := Subgroup.le_centralizer_iff.2 hB₁C
  have hUBC : UB ≤ Subgroup.centralizer (B₁ : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hB₁A)
  have hCle : X ⊔ UB ≤ U ⊓ Subgroup.centralizer (B₁ : Set G) :=
    sup_le (le_inf hXU hXC) (le_inf inf_le_left hUBC)
  have hsup : Nat.card ↥(X ⊔ UB) = 4 * Nat.card ↥UB :=
    card_conjSubgroup_sup_UB hs hH hV16 hD hh hact
  have hCcard : 4 * Nat.card ↥UB ≤ Nat.card ↥(U ⊓ Subgroup.centralizer (B₁ : Set G)) := by
    rw [← hsup]
    exact Subgroup.card_le_of_le hCle
  refine ⟨B₁, hB₁A, hrel, le_antisymm ?_ ?_⟩
  · exact card_mul_le_of_isMaxElemAbelian hD.maxA hD.uElem hD.uLe hB₁A
  · rw [hB₁U, hA16]
    have h4 : Nat.card ↥B₁ = 4 * Nat.card ↥K := by omega
    rw [h4]
    nlinarith [hCcard]

theorem input15209Offender_proved (h15201 : StageLemma15201) : Input15209Offender := by
  intro G _ _ T Mc M hs H hH hc hW A hA
  obtain ⟨φ⟩ := hW
  rcases relIndex_delta_two_or_four ⟨φ⟩ hA with h2 | h4
  · have hVH : V154 T Mc M ≤ H := (S152N.V154_le_T hs).trans hH.1.1
    have hUH : conjClosure (V154 T Mc M) H ≤ H :=
      conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh)
    refine ⟨A, le_rfl, h2, ?_⟩
    rw [S152U.card_inf_centralizer_eq hA.1 hc.elemAbelian hUH]
  · exact offender_of_data4 hs hH (h15201 G T Mc M hs) φ (data4_of_delta hs hH hc hA h4)

theorem input15209Lift_proved (h15201 : StageLemma15201) (h1511one : StageLemma15111One) :
    Input15209Lift :=
  input15209Lift_of_offender h1511one (input15209Offender_proved h15201)

end S152Z6

end CFSG.Quasithin
