module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaChief
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem relIndex_cjSub {A B : Subgroup G} (g : G) :
    (cjSub g A).relIndex (cjSub g B) = A.relIndex B := by
  unfold cjSub
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective

private theorem relIndex_mul_relIndex_of_inf_eq {A B B1 : Subgroup G}
    (hB1B : B1 ≤ B) (h : A ⊓ B1 = A ⊓ B) :
    A.relIndex B = A.relIndex B1 * B1.relIndex B := by
  calc A.relIndex B = (A ⊓ B).relIndex B :=
        (Subgroup.inf_relIndex_right A B).symm
    _ = (A ⊓ B1).relIndex B := by rw [← h]
    _ = (A ⊓ B1).relIndex B1 * B1.relIndex B :=
        (Subgroup.relIndex_mul_relIndex (A ⊓ B1) B1 B inf_le_right hB1B).symm
    _ = A.relIndex B1 * B1.relIndex B := by rw [Subgroup.inf_relIndex_right]

private theorem index_gain {U Z B B1 : Subgroup G}
    (hU : IsElemAbelian 2 U) (hZU : Z ≤ U) (hB1B : B1 ≤ B)
    (hB1Z : B1 ≤ Subgroup.centralizer (Z : Set G)) :
    (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z *
        (Subgroup.centralizer (B1 : Set G)).relIndex U ≤
      (Subgroup.centralizer (B : Set G)).relIndex U := by
  let C0 : Subgroup G := Subgroup.centralizer (B : Set G) ⊓ U
  let C1 : Subgroup G := Subgroup.centralizer (B1 : Set G) ⊓ U
  have hC0U : C0.relIndex U = (Subgroup.centralizer (B : Set G)).relIndex U :=
    Subgroup.inf_relIndex_right (Subgroup.centralizer (B : Set G)) U
  have hC1U : C1.relIndex U = (Subgroup.centralizer (B1 : Set G)).relIndex U :=
    Subgroup.inf_relIndex_right (Subgroup.centralizer (B1 : Set G)) U
  have hC0C1 : C0 ≤ C1 :=
    inf_le_inf_right U (Subgroup.centralizer_le hB1B)
  have hC1Ule : C1 ≤ U := inf_le_right
  have hZleC1 : Z ≤ C1 := by
    refine le_inf ?_ hZU
    rw [Subgroup.le_centralizer_iff]
    exact hB1Z
  have hZsup : Z ⊔ C0 ≤ C1 := sup_le hZleC1 hC0C1
  have hZN : Z ≤ Subgroup.normalizer (C0 : Set G) := by
    have hZC : Z ≤ Subgroup.centralizer (C0 : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact IsElemAbelian.comm hU hc.2 (hZU hz)
    exact hZC.trans (Subgroup.centralizer_le_normalizer (C0 : Set G))
  have hC0Z : C0.relIndex Z = (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z := by
    calc C0.relIndex Z = (C0 ⊓ Z).relIndex Z :=
          (Subgroup.inf_relIndex_right C0 Z).symm
      _ = (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z := by
          congr 1
          ext x
          simp only [C0, Subgroup.mem_inf]
          constructor
          · rintro ⟨⟨hxC, hxU⟩, hxZ⟩
            exact ⟨hxZ, hxC⟩
          · rintro ⟨hxZ, hxC⟩
            exact ⟨⟨hxC, hZU hxZ⟩, hxZ⟩
  have hC0sup : C0.relIndex (Z ⊔ C0) = C0.relIndex Z :=
    A4.relIndex_sup_eq_of_le_normalizer' hZN
  have hC0C1rel : C0.relIndex (Z ⊔ C0) ≤ C0.relIndex C1 :=
    Subgroup.relIndex_le_of_le_right hZsup (Subgroup.index_ne_zero_of_finite)
  calc (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z *
        (Subgroup.centralizer (B1 : Set G)).relIndex U
      = C0.relIndex Z * C1.relIndex U := by rw [← hC0Z, ← hC1U]
    _ = C0.relIndex (Z ⊔ C0) * C1.relIndex U := by rw [← hC0sup]
    _ ≤ C0.relIndex C1 * C1.relIndex U := Nat.mul_le_mul_right _ hC0C1rel
    _ = C0.relIndex U := Subgroup.relIndex_mul_relIndex C0 C1 U hC0C1 hC1Ule
    _ = (Subgroup.centralizer (B : Set G)).relIndex U := hC0U

private theorem sq_le_index_gain {U Z B B1 : Subgroup G} {q : ℕ}
    (hU : IsElemAbelian 2 U) (hZU : Z ≤ U) (hB1B : B1 ≤ B)
    (hB1Z : B1 ≤ Subgroup.centralizer (Z : Set G))
    (hZrel : q ^ 2 ≤ (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z) :
    q ^ 2 ≤ (Subgroup.centralizer (B : Set G) ⊓ U).relIndex
      (Subgroup.centralizer (B1 : Set G) ⊓ U) := by
  let C0 : Subgroup G := Subgroup.centralizer (B : Set G) ⊓ U
  let C1 : Subgroup G := Subgroup.centralizer (B1 : Set G) ⊓ U
  have hC0C1 : C0 ≤ C1 :=
    inf_le_inf_right U (Subgroup.centralizer_le hB1B)
  have hZleC1 : Z ≤ C1 := by
    refine le_inf ?_ hZU
    rw [Subgroup.le_centralizer_iff]
    exact hB1Z
  have hZsup : Z ⊔ C0 ≤ C1 := sup_le hZleC1 hC0C1
  have hZN : Z ≤ Subgroup.normalizer (C0 : Set G) := by
    have hZC : Z ≤ Subgroup.centralizer (C0 : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact IsElemAbelian.comm hU hc.2 (hZU hz)
    exact hZC.trans (Subgroup.centralizer_le_normalizer (C0 : Set G))
  have hC0Z : C0.relIndex Z = (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z := by
    calc C0.relIndex Z = (C0 ⊓ Z).relIndex Z :=
          (Subgroup.inf_relIndex_right C0 Z).symm
      _ = (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z := by
          congr 1
          ext x
          simp only [C0, Subgroup.mem_inf]
          constructor
          · rintro ⟨⟨hxC, hxU⟩, hxZ⟩
            exact ⟨hxZ, hxC⟩
          · rintro ⟨hxZ, hxC⟩
            exact ⟨⟨hxC, hZU hxZ⟩, hxZ⟩
  have hC0sup : C0.relIndex (Z ⊔ C0) = C0.relIndex Z :=
    A4.relIndex_sup_eq_of_le_normalizer' hZN
  have hC0C1rel : C0.relIndex (Z ⊔ C0) ≤ C0.relIndex C1 :=
    Subgroup.relIndex_le_of_le_right hZsup (Subgroup.index_ne_zero_of_finite)
  calc q ^ 2 ≤ (Z ⊓ Subgroup.centralizer (B : Set G)).relIndex Z := hZrel
    _ = C0.relIndex Z := hC0Z.symm
    _ = C0.relIndex (Z ⊔ C0) := hC0sup.symm
    _ ≤ C0.relIndex C1 := hC0C1rel

private theorem exchange_induction
    {U Z H Q1 Q2 S : Subgroup G} {q : ℕ}
    (hUeq : U = conjClosure Z H) (hUe : IsElemAbelian 2 U)
    (hZU : Z ≤ U) (hQ2S : Q2 ≤ S)
    (hC : S ⊓ Subgroup.centralizer (Z : Set G) = Q1)
    (hM5 : ∀ A : Subgroup G, A ≤ S → (∀ a ∈ A, a ^ 2 ∈ Q1) →
      (A ⊓ Q1).relIndex A ≤ q)
    (hM6 : ∀ t : G, t ∈ S → t * t ∈ Q1 → t ∉ Q1 →
      q ^ 2 ≤ (Z ⊓ Subgroup.centralizer ({t} : Set G)).relIndex Z)
    (hQ2inv : ∀ g ∈ H, cjSub g Q2 = Q2) :
    ∀ B : Subgroup G, B ≤ Q2 → IsElemAbelian 2 B →
      (Subgroup.centralizer (U : Set G)).relIndex B ^ 2 ≤
        (Subgroup.centralizer (B : Set G)).relIndex U := by
  have hUinv : ∀ g ∈ H, cjSub g U = U := by
    intro g hg
    rw [hUeq]
    exact B2F.cjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Z H hg)
  have hmainStep : ∀ n : ℕ, ∀ B : Subgroup G, B ≤ Q2 → IsElemAbelian 2 B →
      (Subgroup.centralizer (U : Set G)).relIndex B = n →
      (Subgroup.centralizer (U : Set G)).relIndex B ^ 2 ≤
        (Subgroup.centralizer (B : Set G)).relIndex U := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hBQ2 hBe hn
      by_cases hBC : B ≤ Subgroup.centralizer (U : Set G)
      · have hrel : (Subgroup.centralizer (U : Set G)).relIndex B = 1 :=
          Subgroup.relIndex_eq_one.mpr hBC
        rw [hrel]
        have hpos : 0 < (Subgroup.centralizer (B : Set G)).relIndex U :=
          Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        norm_num
        exact hpos
      · have hex : ∃ g ∈ H,
            ¬ B ≤ Subgroup.centralizer (cjSub g Z : Set G) := by
          by_contra h
          have hall : ∀ g ∈ H, B ≤ Subgroup.centralizer (cjSub g Z : Set G) := by
            intro g hg
            by_contra hg'
            exact h ⟨g, hg, hg'⟩
          have hUC : U ≤ Subgroup.centralizer (B : Set G) := by
            rw [hUeq]
            refine conjClosure_le fun g hg z hz => ?_
            have hz' : g * z * g⁻¹ ∈ cjSub g Z := by
              rw [mem_cjSub]
              simpa [mul_assoc] using hz
            exact (Subgroup.le_centralizer_iff.mp (hall g hg)) hz'
          exact hBC (Subgroup.le_centralizer_iff.mp hUC)
        obtain ⟨g, hgH, hBnot⟩ := hex
        let B' : Subgroup G := cjSub g⁻¹ B
        have hB'Q2 : B' ≤ Q2 := (cjSub_mono hBQ2).trans (le_of_eq (hQ2inv g⁻¹
          (H.inv_mem hgH)))
        have hB'e : IsElemAbelian 2 B' := isElemAbelian_cjSub hBe
        have hB'S : B' ≤ S := hB'Q2.trans hQ2S
        have hB'notC : ¬ B' ≤ Subgroup.centralizer (Z : Set G) := by
          intro hle
          have hconj : cjSub g B' ≤ Subgroup.centralizer (cjSub g Z : Set G) := by
            rw [← B2F.cjSub_centralizer g Z]
            exact cjSub_mono hle
          have hBeq : cjSub g B' = B := cjSub_cjSub_inv g B
          rw [hBeq] at hconj
          exact hBnot hconj
        have hB'notQ1 : ¬ B' ≤ Q1 := fun hle =>
          hB'notC (hle.trans (by
            rw [← hC]
            exact inf_le_right))
        obtain ⟨t, htB', htQ1⟩ := Set.not_subset.mp hB'notQ1
        let B1 : Subgroup G := B' ⊓ Q1
        have hB1B' : B1 ≤ B' := inf_le_left
        have hB1Q2 : B1 ≤ Q2 := hB1B'.trans hB'Q2
        have hB1e : IsElemAbelian 2 B1 := hB'e.mono hB1B'
        have hB1eq : B1 = B' ⊓ Subgroup.centralizer (Z : Set G) := by
          calc B1 = B' ⊓ Q1 := rfl
            _ = B' ⊓ (S ⊓ Subgroup.centralizer (Z : Set G)) := by rw [hC]
            _ = (B' ⊓ S) ⊓ Subgroup.centralizer (Z : Set G) := by rw [inf_assoc]
            _ = B' ⊓ Subgroup.centralizer (Z : Set G) := by
                rw [inf_eq_left.mpr hB'S]
        have hB1lt : B1 < B' := by
          refine lt_of_le_of_ne hB1B' ?_
          intro heq
          exact hB'notC (heq.symm ▸ (hB1eq ▸ inf_le_right))
        have hCUB1 : Subgroup.centralizer (U : Set G) ⊓ B1 =
            Subgroup.centralizer (U : Set G) ⊓ B' := by
          refine le_antisymm (inf_le_inf_left _ hB1B') ?_
          intro x hx
          have hxZ : x ∈ Subgroup.centralizer (Z : Set G) :=
            Subgroup.centralizer_le hZU hx.1
          have hxQ1 : x ∈ Q1 := by
            have hxSC : x ∈ S ⊓ Subgroup.centralizer (Z : Set G) :=
              ⟨hB'S hx.2, hxZ⟩
            rwa [hC] at hxSC
          exact ⟨hx.1, hx.2, hxQ1⟩
        have hCUinv : cjSub g⁻¹ (Subgroup.centralizer (U : Set G)) =
            Subgroup.centralizer (U : Set G) := by
          rw [B2F.cjSub_centralizer, hUinv g⁻¹ (H.inv_mem hgH)]
        have hnB' : (Subgroup.centralizer (U : Set G)).relIndex B' = n := by
          calc (Subgroup.centralizer (U : Set G)).relIndex B'
              = (Subgroup.centralizer (U : Set G)).relIndex (cjSub g⁻¹ B) := rfl
            _ = (cjSub g⁻¹ (Subgroup.centralizer (U : Set G))).relIndex
                  (cjSub g⁻¹ B) := by rw [hCUinv]
            _ = (Subgroup.centralizer (U : Set G)).relIndex B :=
                relIndex_cjSub (A := Subgroup.centralizer (U : Set G)) (B := B) g⁻¹
            _ = n := hn
        have hleB1 : (Subgroup.centralizer (U : Set G)).relIndex B1 ≤ n := by
          rw [← hnB']
          exact Subgroup.relIndex_le_of_le_right hB1B'
            (Subgroup.index_ne_zero_of_finite)
        have hneB1 : (Subgroup.centralizer (U : Set G)).relIndex B1 ≠ n := by
          intro heq
          have hcard : Nat.card B1 = Nat.card B' := by
            have h1 := Subgroup.relIndex_mul_card
              (Subgroup.centralizer (U : Set G)) B1
            have h2 := Subgroup.relIndex_mul_card
              (Subgroup.centralizer (U : Set G)) B'
            rw [heq] at h1
            rw [hCUB1] at h1
            rw [hnB'] at h2
            rw [← h1, h2]
          have hBeq : B1 = B' :=
            Subgroup.eq_of_le_of_card_ge hB1B' (le_of_eq hcard.symm)
          exact (ne_of_lt hB1lt) hBeq
        have hn1lt : (Subgroup.centralizer (U : Set G)).relIndex B1 < n :=
          lt_of_le_of_ne hleB1 hneB1
        have hIH := ih ((Subgroup.centralizer (U : Set G)).relIndex B1) hn1lt
          B1 hB1Q2 hB1e rfl
        have hB1rel : B1.relIndex B' ≤ q := by
          have hsq : ∀ a ∈ B', a ^ 2 ∈ Q1 := by
            intro a ha
            rw [hB'e.2 a ha]
            exact Q1.one_mem
          have h := hM5 B' hB'S hsq
          show (B' ⊓ Q1).relIndex B' ≤ q
          exact h
        have hZrel : q ^ 2 ≤
            (Z ⊓ Subgroup.centralizer (B' : Set G)).relIndex Z := by
          have hm6 := hM6 t (hB'S htB') (by
            rw [← pow_two, hB'e.2 t htB']
            exact Q1.one_mem) htQ1
          refine hm6.trans ?_
          exact Subgroup.relIndex_le_of_le_left
            (inf_le_inf_left _ (Subgroup.centralizer_le (by
              intro x hx
              rw [Set.mem_singleton_iff] at hx
              subst hx
              exact htB')))
            (Subgroup.index_ne_zero_of_finite)
        have hB1Z : B1 ≤ Subgroup.centralizer (Z : Set G) := by
          rw [hB1eq]
          exact inf_le_right
        have hsqgain := sq_le_index_gain hUe hZU hB1B' hB1Z hZrel
        have hgain := index_gain hUe hZU hB1B' hB1Z
        have hnmul : (Subgroup.centralizer (U : Set G)).relIndex B1 *
            B1.relIndex B' = n := by
          calc (Subgroup.centralizer (U : Set G)).relIndex B1 * B1.relIndex B'
              = ((Subgroup.centralizer (U : Set G) ⊓ B1).relIndex B1) *
                  B1.relIndex B' := by rw [Subgroup.inf_relIndex_right]
            _ = (Subgroup.centralizer (U : Set G) ⊓ B1).relIndex B' :=
                Subgroup.relIndex_mul_relIndex (Subgroup.centralizer (U : Set G) ⊓ B1)
                  B1 B' inf_le_right hB1B'
            _ = (Subgroup.centralizer (U : Set G) ⊓ B').relIndex B' := by rw [hCUB1]
            _ = (Subgroup.centralizer (U : Set G)).relIndex B' :=
                Subgroup.inf_relIndex_right _ B'
            _ = n := hnB'
        have hfinal : (Subgroup.centralizer (B' : Set G)).relIndex U =
            (Subgroup.centralizer (B : Set G)).relIndex U := by
          have hCB : cjSub g⁻¹ (Subgroup.centralizer (B : Set G)) =
              Subgroup.centralizer (B' : Set G) := B2F.cjSub_centralizer g⁻¹ B
          have hCU : cjSub g⁻¹ U = U := hUinv g⁻¹ (H.inv_mem hgH)
          calc (Subgroup.centralizer (B' : Set G)).relIndex U
              = (cjSub g⁻¹ (Subgroup.centralizer (B : Set G))).relIndex
                  (cjSub g⁻¹ U) := by rw [hCB, hCU]
            _ = (Subgroup.centralizer (B : Set G)).relIndex U :=
                relIndex_cjSub (A := Subgroup.centralizer (B : Set G)) (B := U) g⁻¹
        have hmain : n ^ 2 ≤ (Subgroup.centralizer (B' : Set G)).relIndex U := by
          have hIH' : (Subgroup.centralizer (U : Set G)).relIndex B1 ^ 2 ≤
              (Subgroup.centralizer (B1 : Set G) ⊓ U).relIndex U := by
            rw [Subgroup.inf_relIndex_right]
            exact hIH
          calc n ^ 2 = ((Subgroup.centralizer (U : Set G)).relIndex B1) ^ 2 *
                (B1.relIndex B') ^ 2 := by
                rw [← hnmul]
                ring
            _ ≤ ((Subgroup.centralizer (B1 : Set G) ⊓ U).relIndex U) * q ^ 2 :=
                Nat.mul_le_mul hIH' (Nat.pow_le_pow_left hB1rel 2)
            _ = q ^ 2 * ((Subgroup.centralizer (B1 : Set G) ⊓ U).relIndex U) := by
                ring
            _ ≤ (Subgroup.centralizer (B' : Set G) ⊓ U).relIndex
                  (Subgroup.centralizer (B1 : Set G) ⊓ U) *
                ((Subgroup.centralizer (B1 : Set G) ⊓ U).relIndex U) :=
                Nat.mul_le_mul_right _ hsqgain
            _ = (Subgroup.centralizer (B' : Set G) ⊓ U).relIndex U :=
                Subgroup.relIndex_mul_relIndex (Subgroup.centralizer (B' : Set G) ⊓ U)
                  (Subgroup.centralizer (B1 : Set G) ⊓ U) U
                  (inf_le_inf_right U (Subgroup.centralizer_le hB1B')) inf_le_right
            _ = (Subgroup.centralizer (B' : Set G)).relIndex U := by
                rw [Subgroup.inf_relIndex_right]
        rw [hn, ← hfinal]
        exact hmain
  intro B hBQ2 hBe
  exact hmainStep ((Subgroup.centralizer (U : Set G)).relIndex B) B hBQ2 hBe rfl

private theorem exchange_bound_aux
    {L1 L2 S : Subgroup G} {q m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hm : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hUe : IsElemAbelian 2 (str86U L1 L2 S)) :
    ∀ B : Subgroup G, B ≤ Q2 L1 L2 S → IsElemAbelian 2 B →
      (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex B ^ 2 ≤
        (Subgroup.centralizer (B : Set G)).relIndex (str86U L1 L2 S) := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S :=
    (le_sup_right : Q2 L1 L2 S ≤ (S ⊓ L2) ⊔ Q2 L1 L2 S).trans (le_of_eq hS2.symm)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) = Q1 L1 L2 S :=
    pCoreOf_sup_pCoreOf hF.1
  have hpCore1S : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact hpCore1
  have hHZ1 : L1 ⊔ Q1 L1 L2 S ≤
      Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_sup_left : L1 ≤ P1 L1 L2 S).trans
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
    · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
        (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hHZ1S : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [hsup1]
    exact hHZ1
  have hHcS : ¬ L1 ⊔ S ≤
      (L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) ⊔
        pCoreOf 2 (L1 ⊔ S) := by
    intro hle
    have hQ1C : Q1 L1 L2 S ≤
        Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      Q1_le_centralizer_Z1 L1 L2 S
    have hleC : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      hle.trans (sup_le inf_le_right (by rw [hpCore1S]; exact hQ1C))
    exact hII (by rwa [hsup1] at hleC)
  have hqH : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) q :=
    IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1) hq
  have hqS : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
    rw [hsup1]
    exact hqH
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF.toW hB hB1 hII
  have hQ2norm : L2 ⊔ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (sup_le le_sup_left
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hM5 : ∀ A : Subgroup G, A ≤ S → (∀ a ∈ A, a ^ 2 ∈ Q1 L1 L2 S) →
      (A ⊓ Q1 L1 L2 S).relIndex A ≤ q :=
    fun A hAS hA => relIndex_inf_q1_le hF.1 hS1 hq hAS hA
  have hM6 : ∀ t : G, t ∈ S → t * t ∈ Q1 L1 L2 S → t ∉ Q1 L1 L2 S →
      q ^ 2 ≤ (Z1 L1 L2 S ⊓
        Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) := by
    intro t htS ht htO
    exact sq_le_relIndex_centralizer_of_sq_mem (H := L1 ⊔ S)
      (V := Z1 L1 L2 S) (q := q) (t := t) hqS
      (fun v hv => by
        simpa [pow_two] using (SmithC27.isElemAbelian_omegaOneCenterOf
          (Q1 L1 L2 S)).2 v hv) hHZ1S hHcS ((le_sup_right : S ≤ L1 ⊔ S) htS) (by
          rw [hpCore1S]
          exact ht) (by rwa [hpCore1S])
  have hQ2inv : ∀ g ∈ L2 ⊔ S, cjSub g (Q2 L1 L2 S) = Q2 L1 L2 S :=
    fun g hg => B2F.cjSub_eq_of_mem_normalizer (hQ2norm hg)
  exact exchange_induction (U := str86U L1 L2 S) (Z := Z1 L1 L2 S)
    (H := L2 ⊔ S) (Q1 := Q1 L1 L2 S) (Q2 := Q2 L1 L2 S) (S := S) (q := q)
    rfl hUe (le_conjClosure (Z1 L1 L2 S) (L2 ⊔ S)) hQ2S
    hC hM5 hM6 hQ2inv

private theorem exchange_refined_aux
    {L1 L2 S : Subgroup G} {q m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hm : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hUe : IsElemAbelian 2 (str86U L1 L2 S))
    {B0 : Subgroup G} (hB0 : B0 ≤ Q2 L1 L2 S) (hB0e : IsElemAbelian 2 B0) :
    (Subgroup.centralizer (B0 : Set G)).relIndex (Z1 L1 L2 S) *
        (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex B0 ^ 2 ≤
      q ^ 2 * (Subgroup.centralizer (B0 : Set G)).relIndex (str86U L1 L2 S) := by
  let U : Subgroup G := str86U L1 L2 S
  have hUe' : IsElemAbelian 2 U := hUe
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S :=
    (le_sup_right : Q2 L1 L2 S ≤ (S ⊓ L2) ⊔ Q2 L1 L2 S).trans (le_of_eq hS2.symm)
  have hZ1U : Z1 L1 L2 S ≤ U := le_conjClosure (Z1 L1 L2 S) (L2 ⊔ S)
  let B1 : Subgroup G := B0 ⊓ Q1 L1 L2 S
  have hB1B0 : B1 ≤ B0 := inf_le_left
  have hB1Q2 : B1 ≤ Q2 L1 L2 S := hB1B0.trans hB0
  have hB1e : IsElemAbelian 2 B1 := hB0e.mono hB1B0
  have hB1Z : B1 ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (inf_le_right : B1 ≤ Q1 L1 L2 S).trans (Q1_le_centralizer_Z1 L1 L2 S)
  have hB1rel : B1.relIndex B0 ≤ q := by
    have hsq : ∀ x ∈ B0, x ^ 2 ∈ Q1 L1 L2 S := by
      intro x hx
      rw [hB0e.2 x hx]
      exact (Q1 L1 L2 S).one_mem
    have h := relIndex_inf_q1_le hF.1 hS1 hq (hB0.trans hQ2S) hsq
    simpa [B1] using h
  have hfirst : (Subgroup.centralizer (U : Set G)).relIndex B1 ^ 2 ≤
      (Subgroup.centralizer (B1 : Set G)).relIndex U :=
    exchange_bound_aux hF hB hq hm hL2 hII hUe B1 hB1Q2 hB1e
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF.toW hB hB1 hII
  have hCUB0 : Subgroup.centralizer (U : Set G) ⊓ B1 =
      Subgroup.centralizer (U : Set G) ⊓ B0 := by
    refine le_antisymm (inf_le_inf_left _ hB1B0) ?_
    intro x hx
    have hxZ : x ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      Subgroup.centralizer_le hZ1U hx.1
    have hxQ1 : x ∈ Q1 L1 L2 S := by
      have hxSC : x ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨hQ2S (hB0 hx.2), hxZ⟩
      rwa [hC] at hxSC
    exact ⟨hx.1, hx.2, hxQ1⟩
  have hrelB0 : (Subgroup.centralizer (U : Set G)).relIndex B1 *
      B1.relIndex B0 = (Subgroup.centralizer (U : Set G)).relIndex B0 :=
    (relIndex_mul_relIndex_of_inf_eq hB1B0 hCUB0).symm
  have hgain := index_gain hUe' hZ1U hB1B0 hB1Z
  have hZrelB0 : (Subgroup.centralizer (B0 : Set G)).relIndex (Z1 L1 L2 S) =
      (Z1 L1 L2 S ⊓ Subgroup.centralizer (B0 : Set G)).relIndex
        (Z1 L1 L2 S) := by
    calc (Subgroup.centralizer (B0 : Set G)).relIndex (Z1 L1 L2 S)
        = (Subgroup.centralizer (B0 : Set G) ⊓ Z1 L1 L2 S).relIndex
            (Z1 L1 L2 S) :=
          (Subgroup.inf_relIndex_right (Subgroup.centralizer (B0 : Set G))
            (Z1 L1 L2 S)).symm
      _ = (Z1 L1 L2 S ⊓ Subgroup.centralizer (B0 : Set G)).relIndex
            (Z1 L1 L2 S) := by rw [inf_comm]
  calc (Subgroup.centralizer (B0 : Set G)).relIndex (Z1 L1 L2 S) *
        (Subgroup.centralizer (U : Set G)).relIndex B0 ^ 2
      = (Z1 L1 L2 S ⊓ Subgroup.centralizer (B0 : Set G)).relIndex
          (Z1 L1 L2 S) * ((Subgroup.centralizer (U : Set G)).relIndex B1 *
            B1.relIndex B0) ^ 2 := by
          rw [hrelB0, hZrelB0]
    _ = ((Subgroup.centralizer (U : Set G)).relIndex B1) ^ 2 *
          ((Z1 L1 L2 S ⊓ Subgroup.centralizer (B0 : Set G)).relIndex
            (Z1 L1 L2 S) * (B1.relIndex B0) ^ 2) := by ring
    _ ≤ (Subgroup.centralizer (B1 : Set G)).relIndex U *
          ((Z1 L1 L2 S ⊓ Subgroup.centralizer (B0 : Set G)).relIndex
            (Z1 L1 L2 S) * q ^ 2) :=
        Nat.mul_le_mul hfirst
          (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hB1rel 2))
    _ = q ^ 2 * ((Z1 L1 L2 S ⊓ Subgroup.centralizer (B0 : Set G)).relIndex
          (Z1 L1 L2 S) * (Subgroup.centralizer (B1 : Set G)).relIndex U) := by
        ring
    _ ≤ q ^ 2 * (Subgroup.centralizer (B0 : Set G)).relIndex U :=
        Nat.mul_le_mul_left _ hgain

theorem str86_exchange_bound
    {L1 L2 S : Subgroup G} {q m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    {B₀ : Subgroup G} (hB₀ : B₀ ≤ Q2 L1 L2 S) (hB₀e : IsElemAbelian 2 B₀) :
    (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex B₀ ^ 2 ≤
        (Subgroup.centralizer (B₀ : Set G)).relIndex (str86U L1 L2 S) ∧
      (Subgroup.centralizer (B₀ : Set G)).relIndex (Z1 L1 L2 S) *
          (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex B₀ ^ 2 ≤
        q ^ 2 * (Subgroup.centralizer (B₀ : Set G)).relIndex (str86U L1 L2 S) := by
  have hUe : IsElemAbelian 2 (str86U L1 L2 S) :=
    isElemAbelian_str86U_of_caseII hF hB hq hm hL2 hII hZ
  exact ⟨exchange_bound_aux hF hB hq hm hL2 hII hUe B₀ hB₀ hB₀e,
    exchange_refined_aux hF hB hq hm hL2 hII hUe hB₀ hB₀e⟩

theorem str86_caseIIa_chief_le_two
    {L1 L2 S : Subgroup G} {q m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S) {c : ℕ}
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) c) : c ≤ 2 := by
  let U : Subgroup G := str86U L1 L2 S
  have hUe : IsElemAbelian 2 U :=
    isElemAbelian_str86U_of_caseII hF hB hq hm hL2 hII hZ
  have hU2 : IsPGroup 2 U := hUe.isPGroup
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hQ12 : L2 ⊔ Q1 L2 L1 S = L2 ⊔ Q2 L1 L2 S := by
    rw [Q1, Q2, P1, P2, bigB_comm]
  have hL2sup : IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) := by
    obtain ⟨eL2⟩ := hL2
    rw [hsup2, ← hQ12]
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL2⟩
  have hQ2S : Q2 L1 L2 S ≤ S :=
    (le_sup_right : Q2 L1 L2 S ≤ (S ⊓ L2) ⊔ Q2 L1 L2 S).trans (le_of_eq hS2.symm)
  have hQ2norm : L2 ⊔ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (sup_le le_sup_left
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hUQ2 : U ≤ Q2 L1 L2 S := by
    refine conjClosure_le fun g hg z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hQ2norm hg) z).mp (hZ hz)
  have hUS : U ≤ S := hUQ2.trans hQ2S
  have hUH : U ≤ L2 ⊔ S := hUS.trans le_sup_right
  have hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S :=
    not_thompsonJ_le_Q2_of_caseII hF.toW hB hB1 hII
  have hAexists : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q2 L1 L2 S := by
    by_contra h
    have hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → A ≤ Q2 L1 L2 S := by
      intro A hA
      by_contra hAQ
      exact h ⟨A, hA, hAQ⟩
    exact hJQ2 (by
      rw [thompsonJ]
      exact iSup₂_le hall)
  obtain ⟨A, hA, hAQ2⟩ := hAexists
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAS : A ≤ S := hA.1
  have hAH : A ≤ L2 ⊔ S := hAS.trans le_sup_right
  set B0 : Subgroup G := A ⊓ Q2 L1 L2 S with hB0def
  have hB0A : B0 ≤ A := by rw [hB0def]; exact inf_le_left
  have hB0Q2 : B0 ≤ Q2 L1 L2 S := by rw [hB0def]; exact inf_le_right
  have hB0e : IsElemAbelian 2 B0 := hAe.mono hB0A
  set a : ℕ := (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A with hadef
  set b : ℕ := (Subgroup.centralizer (U : Set G)).relIndex B0 with hbdef
  set x : ℕ := (Subgroup.centralizer (A : Set G)).relIndex U with hxdef
  have hCU_A : U ⊓ Subgroup.centralizer (A : Set G) = A ⊓ U := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨hyU, hyC⟩ := hy
      refine ⟨?_, hyU⟩
      have hy2 : y ^ 2 = 1 := by rw [hUe.2 y hyU]
      have hEA : IsElemAbelian 2 (A ⊔ Subgroup.zpowers y) :=
        IsElemAbelian.sup_of_commute hAe (isElemAbelian_zpowers hy2)
          (fun a ha b hb =>
            Subgroup.mem_centralizer_iff.mp
              (Subgroup.zpowers_le.mpr hyC hb) a ha)
      have hEAS : A ⊔ Subgroup.zpowers y ≤ S :=
        sup_le hAS (Subgroup.zpowers_le.mpr (hUS hyU))
      have hmax := hA.2.2 (A ⊔ Subgroup.zpowers y) hEAS hEA
      have heq : A = A ⊔ Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge le_sup_left hmax
      rw [heq]
      exact (le_sup_right : Subgroup.zpowers y ≤ A ⊔ Subgroup.zpowers y)
        (Subgroup.mem_zpowers y)
    · rintro y ⟨hyA, hyU⟩
      exact ⟨hyU, fun a ha => IsElemAbelian.comm hAe ha hyA⟩
  have hxeq : x = A.relIndex U := by
    rw [hxdef]
    calc (Subgroup.centralizer (A : Set G)).relIndex U
        = (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U :=
            (Subgroup.inf_relIndex_left U (Subgroup.centralizer (A : Set G))).symm
      _ = (A ⊓ U).relIndex U := by rw [hCU_A]
      _ = A.relIndex U := Subgroup.inf_relIndex_right A U
  have hTR := card_le_relIndex_mul_card hUe hUS hA
  have hTR' : A.relIndex U * Nat.card ↥(A ⊓ U) ≤ a * Nat.card ↥(A ⊓ U) := by
    calc A.relIndex U * Nat.card ↥(A ⊓ U) = Nat.card U :=
          Subgroup.relIndex_mul_card A U
      _ ≤ (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A *
            Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) := hTR
      _ = a * Nat.card ↥(A ⊓ U) := by rw [hCU_A]
  have hxa : x ≤ a := by
    have h := Nat.le_of_mul_le_mul_right hTR' Nat.card_pos
    rwa [← hxeq] at h
  have hale : a ≤ B0.relIndex A * b := by
    set C : Subgroup G := A ⊓ Subgroup.centralizer (U : Set G) with hCdef
    have hCa : C ≤ A := by rw [hCdef]; exact inf_le_left
    have hsupA : B0 ⊔ C ≤ A := sup_le hB0A hCa
    have hB0le : B0 ≤ B0 ⊔ C := le_sup_left
    have hCle : C ≤ B0 ⊔ C := le_sup_right
    have hCN : B0 ≤ Subgroup.normalizer (C : Set G) := by
      have hB0C : B0 ≤ Subgroup.centralizer (C : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        have hcA : c ∈ A := by rw [hCdef] at hc; exact hc.1
        exact IsElemAbelian.comm hAe hcA (hB0A hb)
      exact hB0C.trans (Subgroup.centralizer_le_normalizer (C : Set G))
    have hsup : C.relIndex (B0 ⊔ C) = C.relIndex B0 :=
      A4.relIndex_sup_eq_of_le_normalizer' hCN
    have hmul : C.relIndex (B0 ⊔ C) * (B0 ⊔ C).relIndex A = C.relIndex A :=
      Subgroup.relIndex_mul_relIndex C (B0 ⊔ C) A hCle hsupA
    have hle : (B0 ⊔ C).relIndex A ≤ B0.relIndex A :=
      Subgroup.relIndex_le_of_le_left hB0le (Subgroup.index_ne_zero_of_finite)
    have hCb : C.relIndex B0 = b := by
      rw [hbdef]
      calc C.relIndex B0 = (C ⊓ B0).relIndex B0 :=
            (Subgroup.inf_relIndex_right C B0).symm
        _ = (Subgroup.centralizer (U : Set G) ⊓ B0).relIndex B0 := by
            congr 1
            ext y
            simp only [hCdef, Subgroup.mem_inf]
            constructor
            · rintro ⟨⟨hyA, hyC⟩, hyB⟩
              exact ⟨hyC, hyB⟩
            · rintro ⟨hyC, hyB⟩
              exact ⟨⟨hB0A hyB, hyC⟩, hyB⟩
        _ = (Subgroup.centralizer (U : Set G)).relIndex B0 :=
            Subgroup.inf_relIndex_right _ B0
    calc a = C.relIndex A := rfl
      _ = C.relIndex (B0 ⊔ C) * (B0 ⊔ C).relIndex A := hmul.symm
      _ = C.relIndex B0 * (B0 ⊔ C).relIndex A := by rw [hsup]
      _ ≤ C.relIndex B0 * B0.relIndex A := Nat.mul_le_mul_left _ hle
      _ = B0.relIndex A * b := by rw [hCb]; ring
  have hB0rel : B0.relIndex A ≤ 2 ^ m := by
    have hpow := relIndex_inf_pCoreOf_le_two_pow hm hL2sup hAH hAe
    rwa [hpCore2, ← hB0def] at hpow
  have hb2x : b ^ 2 ≤ x := by
    have h := (str86_exchange_bound hF hB hq hm hL2 hII hZ hB0Q2 hB0e).1
    rw [hbdef, hxdef]
    refine h.trans ?_
    exact Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le hB0A) (Subgroup.index_ne_zero_of_finite)
  have hbm : b ≤ 2 ^ m := by
    have hbpos : 0 < b := by
      rw [hbdef]
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    refine Nat.le_of_mul_le_mul_right ?_ hbpos
    calc b * b = b ^ 2 := (pow_two b).symm
      _ ≤ x := hb2x
      _ ≤ a := hxa
      _ ≤ B0.relIndex A * b := hale
      _ ≤ 2 ^ m * b := Nat.mul_le_mul_right b hB0rel
  have hx2 : x ≤ (2 ^ m) ^ 2 := by
    calc x ≤ a := hxa
      _ ≤ B0.relIndex A * b := hale
      _ ≤ 2 ^ m * b := Nat.mul_le_mul_right b hB0rel
      _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_left _ hbm
      _ = (2 ^ m) ^ 2 := by ring
  have hnotA : ¬ A ≤ Q2 L1 L2 S := hAQ2
  obtain ⟨t, htA, htQ2⟩ := Set.not_subset.mp hnotA
  have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) (hAS htA)
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hAe.2 t htA
  have htO : t ∉ pCoreOf 2 (L2 ⊔ S) := by
    rwa [hpCore2]
  have htQ : t * t ∈ pCoreOf 2 (L2 ⊔ S) := by
    rw [ht2]
    exact (pCoreOf 2 (L2 ⊔ S)).one_mem
  have hl2 := l2_pow_sq_le_relIndex_centralizer hm hL2sup hU2 hUH hc htH htQ htO
  have hl2x : (Subgroup.centralizer (Subgroup.zpowers t : Set G)).relIndex U ≤ x := by
    rw [hxdef]
    exact Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htA))
      (Subgroup.index_ne_zero_of_finite)
  have hpow : (2 ^ m) ^ c ≤ (2 ^ m) ^ 2 := hl2.trans (hl2x.trans hx2)
  exact (Nat.pow_le_pow_iff_right (Nat.one_lt_pow (by omega) (by norm_num))).mp hpow

end CFSG.Quasithin.Stroth

end
