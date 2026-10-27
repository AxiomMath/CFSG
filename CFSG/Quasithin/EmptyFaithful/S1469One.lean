module

public import CFSG.Quasithin.EmptyFaithful.S146R4
public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.EmptyFaithful.S146Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.card_pCoreOf_ge (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) ^ 2 * 2 ≤
      Nat.card (pCoreOf 2 H) := by
  set Q := pCoreOf 2 H with hQ
  set U := conjClosure (VZ T M) H with hU
  have hUQ : U ≤ Q := S.conjClosure_le_pCoreOf hH
  have hUab : IsElemAbelian 2 U := S.lemma_14_5_15_two hH
  have hdual :
      (Q ⊓ Subgroup.centralizer (U : Set G)).relIndex Q =
        (U ⊓ Subgroup.centralizer (Q : Set G)).relIndex U :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.F97_relIndex hUab
  set A := Q ⊓ Subgroup.centralizer (U : Set G) with hA
  set B := U ⊓ Subgroup.centralizer (Q : Set G) with hB
  have hUA : U ≤ A := by
    refine le_inf hUQ fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact congrArg Subtype.val (hUab.1.is_comm.comm (⟨y, hy⟩ : U) ⟨x, hx⟩)
  have hZB : quasithinOmegaOneCenter T ≤ B :=
    le_inf (Z_le_conjClosure_VZ T M H)
      (Subgroup.le_centralizer_iff.mp
        ((S.pCoreOf_le_T hH).trans (le_centralizer_quasithinOmegaOneCenter T)))
  have h2B : 2 ≤ Nat.card B := by
    have := Subgroup.card_le_of_le hZB
    rwa [S.card_Z] at this
  have hUB : B ≤ U := inf_le_left
  have hAQ : A ≤ Q := inf_le_left
  have hQcard : A.relIndex Q * Nat.card A = Nat.card Q := by
    have := Subgroup.relIndex_mul_card (H := A) (K := Q)
    rwa [inf_eq_left.mpr hAQ] at this
  have hUcard : B.relIndex U * Nat.card B = Nat.card U := by
    have := Subgroup.relIndex_mul_card (H := B) (K := U)
    rwa [inf_eq_left.mpr hUB] at this
  have hrel : (Subgroup.centralizer (Q : Set G)).relIndex U = B.relIndex U := by
    rw [hB, inf_comm, Subgroup.inf_relIndex_right]
  have hUA' : Nat.card U ≤ Nat.card A := Subgroup.card_le_of_le hUA
  rw [hrel, ← hQcard, hdual]
  set N := B.relIndex U with hN
  calc N ^ 2 * 2 = N * (N * 2) := by ring
    _ ≤ N * (N * Nat.card B) := by gcongr
    _ = N * Nat.card U := by rw [← hUcard]
    _ ≤ N * Nat.card A := by gcongr

theorem Setting146.two_pow_eleven_lt_card (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    (h4 : 4 < (pCoreOf 2 H).relIndex T)
    (hr : 4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G))) :
    2 ^ 11 < Nat.card T := by
  set Q := pCoreOf 2 H with hQ
  have hQT : Q ≤ T := S.pCoreOf_le_T hH
  have hcard := S.card_pCoreOf_ge hH
  have hN16 : 2 ^ 4 ≤ (Subgroup.centralizer (Q : Set G)).relIndex (conjClosure (VZ T M) H) := by
    have hne : (Subgroup.centralizer (Q : Set G)).relIndex (conjClosure (VZ T M) H) ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (Q : Set G))
        (K := conjClosure (VZ T M) H)
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne this
    unfold mIdx at hr
    have hdvd : 2 ^ 4 ∣ (Subgroup.centralizer (Q : Set G)).relIndex (conjClosure (VZ T M) H) :=
      (padicValNat_dvd_iff_le hne).mpr hr
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have hQ9 : 2 ^ 9 ≤ Nat.card Q := by
    refine le_trans ?_ hcard
    calc 2 ^ 9 = (2 ^ 4) ^ 2 * 2 := by norm_num
      _ ≤ _ := by gcongr
  have hTcard : Q.relIndex T * Nat.card Q = Nat.card T := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := T)
    rwa [inf_eq_left.mpr hQT] at this
  rw [← hTcard]
  calc 2 ^ 11 = 4 * 2 ^ 9 := by norm_num
    _ < Q.relIndex T * 2 ^ 9 := by gcongr
    _ ≤ Q.relIndex T * Nat.card Q := by gcongr

open CFSG.LieType.BorelTits in
@[expose] def Stage1469W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      2 ^ 11 < Nat.card T →
      4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) →
        yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)

open CFSG.LieType.BorelTits in
@[expose] def Stage14610FiveW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      2 ^ 11 < Nat.card T →
      4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ∀ I₂ : Subgroup G, T ⊓ I ≤ I₂ → I₂ ≤ H → Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3)) →
        I = (lI T M I ⊔ (T ⊓ I)) ⊔ I₂ →
        (T ⊓ I = tU T u → I ≤ Subgroup.centralizer ({u} : Set G)) →
          Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

theorem stage1469_of_W (h : Stage1469W) : Stage1469 := by
  intro G _ _ T M H u S hH hu I hI hindex hrank
  have hbig : 2 ^ 11 < Nat.card T := S.two_pow_eleven_lt_card hH hindex hrank
  exact ⟨hbig, h G T M H u S hH hu I hI hbig hrank⟩

theorem stage14610Five_of_W (h : Stage14610FiveW) : Stage14610Five := by
  intro G _ _ T M H u S hH hu I hIs hindex hrank I₂ hI₂ hI₂H hS3 hIeq hcent
  exact h G T M H u S hH hu I hIs (S.two_pow_eleven_lt_card hH hindex hrank) hrank I₂ hI₂ hI₂H hS3
    hIeq hcent

end CFSG.Quasithin
