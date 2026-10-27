module

public import CFSG.Quasithin.H13.U3S13473B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_thompsonJ_ne_bot (S : A6.Setting134 G T L V) : thompsonJ T ≠ ⊥ :=
  S1414.thompsonJ_ne_bot S.h13.sylow.1 fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ S.V_le_T))

theorem s1347_thompsonJ_not_le_pCoreOf (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H₁ H₂ : Subgroup G}
    (hK₂L : oTwoRes H₂ = l2Of S) (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)) {Y : Subgroup G} (hTY : T ≤ Y)
    (hL1Y : L₁Of L (fsuV1 T V) ≤ Y) : ¬ thompsonJ T ≤ pCoreOf 2 Y := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 Y ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hTY)
  have hJeq : thompsonJ (pCoreOf 2 Y) = thompsonJ T := B6.thompsonJ_eq_of_le hle hOT
  have hYJ : Y ≤ normalizer (thompsonJ T : Set G) := by
    rw [← hJeq]
    exact (le_normalizer_pCoreOf 2 Y).trans (normalizer_le_normalizer_thompsonJ _)
  have hL2 : l2Of S ≤ normalizer (thompsonJ T : Set G) := by
    rw [← hK₂L]
    exact ((oTwoRes_le _).trans le_sup_right).trans hJ
  have hTJ : T ≤ normalizer (thompsonJ T : Set G) := hTY.trans hYJ
  have hLJ : L ⊔ T ≤ normalizer (thompsonJ T : Set G) :=
    sup_le ((s134_L_le_sup S he).trans (sup_le (sup_le (hL1Y.trans hYJ) hTJ) (sup_le hL2 hTJ)))
      hTJ
  exact hH₀M (hJ.trans (s134_normalizer_le_M S (s134_thompsonJ_ne_bot S)
    (S.h13.sylow.1.to_le (B6.thompsonJ_le T)) hLJ))

theorem s1347_thompsonJ_not_le_R (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H₁ H₂ : Subgroup G}
    (hK₂L : oTwoRes H₂ = l2Of S) (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)) (hTH : T ≤ H₁ ⊔ H₂) {Y₂ : Subgroup G}
    (hY₂H : Y₂ ≤ H₁ ⊔ H₂) : ¬ thompsonJ T ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJeq : thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = thompsonJ T :=
    B6.thompsonJ_eq_of_le hle (NQS134.s134_R_le_T S)
  have h1 : L₁Of L (fsuV1 T V) ⊔ T ≤ normalizer (thompsonJ T : Set G) := by
    rw [← hJeq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_thompsonJ _)
  have hYJ : (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T) ≤ normalizer (thompsonJ T : Set G) :=
    sup_le h1 ((sup_le hY₂H hTH).trans hJ)
  have hTY : T ≤ (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T) := le_sup_right.trans le_sup_left
  exact s1347_thompsonJ_not_le_pCoreOf S he hK₂L hH₀M hJ hTY (le_sup_left.trans le_sup_left)
    (le_pCoreOf_of_le_normalizer 2 ((B6.thompsonJ_le T).trans hTY) hYJ
      (S.h13.sylow.1.to_le (B6.thompsonJ_le T)))

theorem s1347_iii_pCoreOf_ne (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H₁ H₂ : Subgroup G}
    (hK₂L : oTwoRes H₂ = l2Of S) (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)) (hTH : T ≤ H₁ ⊔ H₂) {Y₂ : Subgroup G}
    (hY₂H : Y₂ ≤ H₁ ⊔ H₂) : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≠ pCoreOf 2 (Y₂ ⊔ T) := by
  intro heq
  apply s1347_thompsonJ_not_le_R S he hK₂L hH₀M hJ hTH hY₂H
  rw [heq]
  exact le_pCoreOf_of_le_normalizer 2 ((B6.thompsonJ_le T).trans le_sup_right)
    ((sup_le hY₂H hTH).trans hJ) (S.h13.sylow.1.to_le (B6.thompsonJ_le T))

omit [Finite G] in
theorem mem_normalizer_sup_u3 {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ normalizer (A : Set G) → h ∈ normalizer (B : Set G) →
      ∀ x ∈ A ⊔ B, h * x * h⁻¹ ∈ A ⊔ B := by
    intro h hA' hB' x hx
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · show h * a * h⁻¹ ∈ A ⊔ B
        exact mem_sup_left ((mem_normalizer_iff.1 hA' a).1 ha)
      · show h * b * h⁻¹ ∈ A ⊔ B
        exact mem_sup_right ((mem_normalizer_iff.1 hB' b).1 hb)
    exact hle hx
  exact B6.mem_normalizer_of_forall_mem (key g hA hB) fun x hx => by
    have := key g⁻¹ (inv_mem hA) (inv_mem hB) x hx
    simpa using this

theorem s134_comm_thompsonJ_L1 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hJR : ¬ thompsonJ T ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ = L₁Of L (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h3, hO, -⟩ := s134_L1T_a6 S he
  have h3' : (pCoreOf 2 (L₁Of L (fsuV1 T V))).relIndex (L₁Of L (fsuV1 T V)) = 3 := by
    rw [← hO]
    exact h3
  have hOT : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ T := hO ▸ inf_le_right
  have hTL : T ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := s134_T_le_normalizer_L1 S
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hJL : thompsonJ T ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := hJT.trans hTL
  have hCL : ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ ≤ L₁Of L (fsuV1 T V) := by
    rw [commutator_le]
    intro l hl a ha
    rw [commutatorElement_def]
    have h1 : a * l⁻¹ * a⁻¹ ∈ L₁Of L (fsuV1 T V) :=
      (mem_normalizer_iff.1 (hJL ha) _).1 (inv_mem hl)
    have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem hl h1
  have hCO : ¬ ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ ≤ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
    intro hle
    apply hJR
    have hP2 : IsPGroup 2 ↥(thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V))) :=
      S.h13.sylow.1.to_le (sup_le hJT hOT)
    have key : ∀ g ∈ L₁Of L (fsuV1 T V), ∀ x ∈ thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V)),
        g * x * g⁻¹ ∈ thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
      intro g hg x hx
      have hle' : thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤
          (thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V))).comap (MulAut.conj g).toMonoidHom := by
        refine sup_le (fun a ha => ?_) (fun o ho => ?_)
        · show g * a * g⁻¹ ∈ thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V))
          have h1 : g * a * g⁻¹ * a⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) :=
            hle (commutator_mem_commutator hg ha)
          have e : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
          rw [e]
          exact mul_mem (mem_sup_right h1) (mem_sup_left ha)
        · show g * o * g⁻¹ ∈ thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V))
          exact mem_sup_right ((mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hg) o).1 ho)
      exact hle' hx
    have hPN : L₁Of L (fsuV1 T V) ⊔ T ≤
        normalizer ((thompsonJ T ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V)) : Subgroup G) : Set G) := by
      refine sup_le (fun l hl => ?_) (fun t ht => ?_)
      · exact B6.mem_normalizer_of_forall_mem (key l hl) fun x hx => by
          have := key l⁻¹ (inv_mem hl) x hx
          simpa using this
      · exact mem_normalizer_sup_u3
          (normalizer_le_normalizer_thompsonJ T (le_normalizer ht))
          (normalizer_le_normalizer_pCoreOf 2 _ (hTL ht))
    exact le_sup_left.trans (le_pCoreOf_of_le_normalizer 2
      (sup_le (hJT.trans le_sup_right) ((pCoreOf_le 2 _).trans le_sup_left)) hPN hP2)
  have hsup : L₁Of L (fsuV1 T V) ≤
      ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
    have hm := relIndex_mul_relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V)))
      (⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V)))
      (L₁Of L (fsuV1 T V)) le_sup_right (sup_le hCL (pCoreOf_le 2 _))
    rw [h3'] at hm
    rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hm) with h1 | h1
    · exact absurd (le_sup_left.trans (relIndex_eq_one.1 h1)) hCO
    · rw [h1] at hm
      exact relIndex_eq_one.1 (by omega)
  have hON : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤
      normalizer ((⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ : Subgroup G) : Set G) :=
    (pCoreOf_le 2 _).trans (le_normalizer_commutator_left' _ _)
  refine le_antisymm hCL ?_
  calc L₁Of L (fsuV1 T V) = oTwoRes (L₁Of L (fsuV1 T V)) := (S14.oTwoRes_idem _).symm
    _ ≤ oTwoRes (⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V))) :=
      oTwoRes_mono' hsup
    _ ≤ ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ := oTwoRes_sup_le' (pCoreOf_isPGroup 2 _) hON

theorem s1347_not_comm_of (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H₁ H₂ : Subgroup G}
    (hK₂L : oTwoRes H₂ = l2Of S) (hTH : T ≤ H₁ ⊔ H₂) {Y₂ : Subgroup G} (hY₂ : oTwoRes Y₂ = Y₂)
    (hH₀N : H₁ ⊔ H₂ ≤ normalizer (Y₂ : Set G)) (hY₂M : ¬ Y₂ ≤ normalizer (L : Set G))
    (hcyc : pCoreOf 2 Y₂ = ⊥ → IsCyclic ↥Y₂) {Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q) (hQT : Q ≤ T)
    (hL₁Q : L₁Of L (fsuV1 T V) ≤ normalizer (Q : Set G)) :
    ¬ ∀ y ∈ Y₂, ∀ l ∈ L₁Of L (fsuV1 T V), y * l * y⁻¹ * l⁻¹ ∈ Q := by
  intro hcomm
  have hTN : T ≤ normalizer (Y₂ : Set G) := hTH.trans hH₀N
  have key : ∀ g ∈ L₁Of L (fsuV1 T V), ∀ x ∈ Y₂ ⊔ Q, g * x * g⁻¹ ∈ Y₂ ⊔ Q := by
    intro g hg x hx
    have hle : Y₂ ⊔ Q ≤ (Y₂ ⊔ Q).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun o ho => ?_)
      · show g * y * g⁻¹ ∈ Y₂ ⊔ Q
        have e : g * y * g⁻¹ = y * (y⁻¹ * g * y⁻¹⁻¹ * g⁻¹) := by group
        rw [e]
        exact mul_mem (mem_sup_left hy) (mem_sup_right (hcomm y⁻¹ (inv_mem hy) g hg))
      · show g * o * g⁻¹ ∈ Y₂ ⊔ Q
        exact mem_sup_right ((mem_normalizer_iff.1 (hL₁Q hg) o).1 ho)
    exact hle hx
  have hL₁N : L₁Of L (fsuV1 T V) ≤ normalizer ((Y₂ ⊔ Q : Subgroup G) : Set G) := fun l hl =>
    B6.mem_normalizer_of_forall_mem (key l hl) fun x hx => by
      have := key l⁻¹ (inv_mem hl) x hx
      simpa using this
  have hres : oTwoRes (Y₂ ⊔ Q) = Y₂ := by
    refine le_antisymm (oTwoRes_sup_le' hQ2 (hQT.trans hTN)) ?_
    calc Y₂ = oTwoRes Y₂ := hY₂.symm
      _ ≤ oTwoRes (Y₂ ⊔ Q) := oTwoRes_mono' le_sup_left
  have hL₁Y : L₁Of L (fsuV1 T V) ≤ normalizer (Y₂ : Set G) := by
    have := hL₁N.trans (normalizer_le_normalizer_oTwoRes _)
    rwa [hres] at this
  have hL₂ : l2Of S ≤ normalizer (Y₂ : Set G) := by
    rw [← hK₂L]
    exact ((oTwoRes_le _).trans le_sup_right).trans hH₀N
  have hLN : L ≤ normalizer (Y₂ : Set G) :=
    (s134_L_le_sup S he).trans (sup_le (sup_le hL₁Y hTN) (sup_le hL₂ hTN))
  exact s134_false_of_normalizer S hY₂M hcyc hLN hTN

end CFSG.Quasithin.H13.U3
