module

public import CFSG.Quasithin.Background.B1More13B
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreElevenE

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B55

section Comp

variable {V : Type} [CommGroup V] [Finite V]

theorem normalizes_comp (hP4 : AsB15Part4) (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hJ : G = ffJ G) (hL : CFSG.Open.IsComponentOf L G) :
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  calc G = ffJ G := hJ
    _ ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
      B113.ffJ_le_normalizer_comps hP4 hV (le_refl G) hL

theorem commutator_comp_eq {G L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L G)
    (hn : G ≤ Subgroup.normalizer (L : Set (MulAut V))) : ⁅L, G⁆ = L := by
  have hLG : ∀ b ∈ G, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hn hb hl
  rcases B1Red.commutator_eq_or_commute (Or.inl hL.2.2) hLG with h | h
  · exact h
  · exfalso
    obtain ⟨hperf, -⟩ := hL.2.2
    have hab : IsMulCommutative ↥L := ⟨⟨fun a b => Subtype.ext (h a (hL.1 a.2) b b.2)⟩⟩
    have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
    have hperf' : Group.IsPerfect ↥L := ⟨hperf⟩
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance

theorem exists_offender (hP4 : AsB15Part4) (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hJ : G = ffJ G) (hL : CFSG.Open.IsComponentOf L G) :
    ∃ A, IsFFStarOffender G A ∧ ⁅L, A⁆ = L := by
  have hn := normalizes_comp hP4 hV hJ hL
  have hLJ : ⁅L, ffJ G⁆ = L := by
    rw [← hJ]
    exact commutator_comp_eq hL hn
  obtain ⟨A, hA, -, hLA⟩ := B113.exists_offender_commutator_eq (le_refl G) hLJ
    (B113.ne_bot_of_quasisimple_or_card_three (Or.inl hL.2.2)) (Or.inl hL.2.2)
  exact ⟨A, hA, hLA⟩

end Comp

section Faithful

variable {V : Type} [CommGroup V] [Finite V]

theorem faithful_on_fixV (hV : ∀ v : V, v ^ 2 = 1) {G L A : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 G = ⊥) (hL : CFSG.Open.IsComponentOf L G) (hA : IsFFStarOffender G A)
    (hLA : ⁅L, A⁆ = L) :
    L ⊓ centSub (fixV (pCoreOf 2 (L ⊔ A))) = ⊥ ∧
      A ⊓ centSub (fixV (pCoreOf 2 (L ⊔ A))) = A ⊓ Subgroup.centralizer (L : Set (MulAut V)) ∧
      IsFFStarOffender (autSub G (fixV (pCoreOf 2 (L ⊔ A))))
        (autSub A (fixV (pCoreOf 2 (L ⊔ A)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := ⟨hLo.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have hLG : L ≤ G := hL.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  set H₀ := L ⊔ A with hH₀def
  have hH₀G : H₀ ≤ G := sup_le hLG hA.1
  have hH₀n : ∀ x ∈ H₀, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro x hx l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hx
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq : ∀ x ∈ H₀, x ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  set Q := pCoreOf 2 H₀ with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀
  have hQH : Q ≤ H₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 H₀
  have hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l = l * q := by
    refine B1Red.commute_of_normal_not_le hLo (fun q hq l hl => hH₀n q (hQH hq) l hl)
      (fun l hl q hq => B1Red.conj_mem_pCoreOf (Subgroup.mem_sup_left hl) hq) ?_
    intro hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hle).isNilpotent
  have hker : H₀ ⊓ centSub (fixV Q) = Q :=
    B1Red.kernel_eq_pCoreOf hV (D := L)
      (fun x hx ho => B1Red.mem_of_sq_mem_of_odd (hsq x hx) ho)
      (fun x hx q hq => (hQL q hq x hx).symm)
  have hLQ : L ⊓ Q = ⊥ := by
    set N := L ⊓ Q with hN
    have hN2 : IsPGroup 2 ↥N := hQ2.to_le inf_le_right
    have hNL : N ≤ L := inf_le_left
    have hnorm : L ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
      refine le_normalizer_of_conj fun l hl n hn => ⟨L.mul_mem (L.mul_mem hl hn.1) (L.inv_mem hl),
        B1Red.conj_mem_pCoreOf (Subgroup.mem_sup_left hl) hn.2⟩
    have h1 : N ≤ pCoreOf 2 L := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNL hnorm hN2
    have h2 : pCoreOf 2 L ≤ pCoreOf 2 G := A4.pCoreOf_le_of_subnormal 2 hL.2.1
    rw [hO2] at h2
    exact le_bot_iff.1 (h1.trans h2)
  have hLC : L ⊓ centSub (fixV Q) = ⊥ := by
    rw [eq_bot_iff, ← hLQ]
    intro x hx
    exact ⟨hx.1, by rw [← hker]; exact ⟨hH₀def ▸ Subgroup.mem_sup_left hx.1, hx.2⟩⟩
  have hAC : A ⊓ centSub (fixV Q) = A ⊓ Subgroup.centralizer (L : Set (MulAut V)) := by
    apply le_antisymm
    · intro a ha
      have haQ : a ∈ Q := by
        rw [← hker]
        exact ⟨hH₀def ▸ Subgroup.mem_sup_right ha.1, ha.2⟩
      exact ⟨ha.1, Subgroup.mem_centralizer_iff.2 fun l hl => (hQL a haQ l hl).symm⟩
    ·
      intro a ha
      have hcomm : ∀ x ∈ H₀, a * x = x * a := by
        intro x hx
        obtain ⟨l', hl', a', ha', rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hx
        have h1 : a * l' = l' * a := (Subgroup.mem_centralizer_iff.1 ha.2 l' hl').symm
        have h2 : a * a' = a' * a := hAel.1 a ha.1 a' ha'
        calc a * (l' * a') = (a * l') * a' := by group
          _ = l' * (a * a') := by rw [h1]; group
          _ = l' * (a' * a) := by rw [h2]
          _ = (l' * a') * a := by group
      have hz2 : IsPGroup 2 ↥(Subgroup.zpowers a) :=
        hAel.isPGroup.to_le (Subgroup.zpowers_le.2 ha.1)
      have hzH : Subgroup.zpowers a ≤ H₀ := Subgroup.zpowers_le.2 (hH₀def ▸ Subgroup.mem_sup_right ha.1)
      have hzn : H₀ ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup (MulAut V)) : Set (MulAut V)) := by
        refine le_normalizer_of_conj fun x hx y hy => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hc : Commute x a := (hcomm x hx).symm
        rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k
      have haQ : a ∈ Q :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hzH hzn hz2 (Subgroup.mem_zpowers a)
      exact ⟨ha.1, fun u hu => hu a haQ⟩
  have hst : H₀ ≤ stabSub (fixV Q) := B1Red.le_stabSub_fixV_pCoreOf H₀
  have hAnc : ¬ A ≤ centSub (fixV Q) := by
    intro hle
    have hAC' : A ≤ Subgroup.centralizer (L : Set (MulAut V)) := fun a ha => by
      have : a ∈ A ⊓ centSub (fixV Q) := ⟨ha, hle ha⟩
      rw [hAC] at this
      exact this.2
    have h0 : ⁅L, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l hl a ha
      show ⁅l, a⁆ ∈ (⊥ : Subgroup (MulAut V))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 (hAC' ha) l hl
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt (hLA ▸ h0)
  have hAH₀ : IsFFStarOffender G A := hA
  refine ⟨hLC, hAC, ?_⟩
  exact B1Red.isFFStarOffender_autSub hAH₀
    (fun a ha w hw => (hst (Subgroup.mem_sup_right ha) w).2 hw) hAnc

end Faithful

end B55

end CFSG.Quasithin
