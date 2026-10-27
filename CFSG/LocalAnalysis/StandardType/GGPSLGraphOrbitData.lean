module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphAlgebra
public import CFSG.LocalAnalysis.StandardType.GGPSLGraphPure
public import CFSG.LocalAnalysis.StandardType.GGBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGLocalFamilyCount

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix

private lemma pslB3b_exists_transversal {α : Type} [DecidableEq α] (P : Finset α) (f : α → α)
    (hfP : ∀ e ∈ P, f e ∈ P) (hff : ∀ e ∈ P, f (f e) = e) :
    ∃ R : Finset α, R ⊆ P ∧ ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = f e) := by
  classical
  have aux : ∀ N, ∀ P : Finset α, P.card ≤ N →
      (∀ e ∈ P, f e ∈ P) → (∀ e ∈ P, f (f e) = e) →
      ∃ R : Finset α, R ⊆ P ∧ ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = f e) := by
    intro N
    induction N with
    | zero =>
      intro P hcard hfP hff
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      intro e he
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at he
      exact absurd he (Finset.notMem_empty e)
    | succ N ih =>
      intro P hcard hfP hff
      by_cases hP : P = ∅
      · subst hP
        refine ⟨∅, Finset.empty_subset _, ?_⟩
        intro e he
        exact absurd he (Finset.notMem_empty e)
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hP
        by_cases hfa : f a = a
        ·
          have hfP' : ∀ e ∈ P.erase a, f e ∈ P.erase a := by
            intro e he
            obtain ⟨hea, heP⟩ := Finset.mem_erase.mp he
            refine Finset.mem_erase.mpr ⟨?_, hfP e heP⟩
            intro hfe
            apply hea
            have h := hff e heP
            rw [hfe, hfa] at h
            exact h.symm
          have hff' : ∀ e ∈ P.erase a, f (f e) = e :=
            fun e he => hff e (Finset.mem_of_mem_erase he)
          have hcard' : (P.erase a).card ≤ N := by
            have h := Finset.card_erase_add_one ha
            omega
          obtain ⟨R', hR'sub, hR'trans⟩ := ih (P.erase a) hcard' hfP' hff'
          have haR' : a ∉ R' := fun h => (Finset.mem_erase.mp (hR'sub h)).1 rfl
          refine ⟨insert a R', ?_, ?_⟩
          · intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact ha
            · exact Finset.mem_of_mem_erase (hR'sub hx)
          · intro e he
            by_cases hea : e = a
            · refine ⟨a, ⟨Finset.mem_insert_self a R', Or.inl hea.symm⟩, ?_⟩
              intro r' hr'
              rcases Finset.mem_insert.mp hr'.1 with hra | hrmem
              · exact hra
              · exfalso
                rcases hr'.2 with h | h
                · rw [h] at hrmem
                  rw [hea] at hrmem
                  exact haR' hrmem
                · rw [h, hea, hfa] at hrmem
                  exact haR' hrmem
            · have heP' : e ∈ P.erase a := Finset.mem_erase.mpr ⟨hea, he⟩
              obtain ⟨r, hr, huniq⟩ := hR'trans e heP'
              refine ⟨r, ⟨Finset.mem_insert_of_mem hr.1, hr.2⟩, ?_⟩
              intro r' hr'
              rcases Finset.mem_insert.mp hr'.1 with hra | hrmem
              · exfalso
                rcases hr'.2 with h | h
                · exact hea (h.symm.trans hra)
                · have h2 : f a = e := by
                    have hh := congrArg f h
                    rw [hff e he] at hh
                    rw [hra] at hh
                    exact hh
                  rw [hfa] at h2
                  exact hea h2.symm
              · exact huniq r' ⟨hrmem, hr'.2⟩
        ·
          have hbP : f a ∈ P := hfP a ha
          have hba : f a ≠ a := fun h => hfa h
          have hbP' : f a ∈ P.erase a := Finset.mem_erase.mpr ⟨hba, hbP⟩
          have hffa : f (f a) = a := hff a ha
          have hfP'' : ∀ e ∈ (P.erase a).erase (f a), f e ∈ (P.erase a).erase (f a) := by
            intro e he
            obtain ⟨hefa, he'⟩ := Finset.mem_erase.mp he
            obtain ⟨hea, heP⟩ := Finset.mem_erase.mp he'
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hfP e heP⟩⟩
            · intro hfe
              apply hea
              have h := congrArg f hfe
              rw [hff e heP, hffa] at h
              exact h
            · intro hfe
              apply hefa
              have h := congrArg f hfe
              rw [hff e heP] at h
              exact h
          have hff'' : ∀ e ∈ (P.erase a).erase (f a), f (f e) = e :=
            fun e he => hff e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))
          have hcard'' : ((P.erase a).erase (f a)).card ≤ N := by
            have h1 := Finset.card_erase_add_one ha
            have h2 := Finset.card_erase_add_one hbP'
            omega
          obtain ⟨R', hR'sub, hR'trans⟩ :=
            ih ((P.erase a).erase (f a)) hcard'' hfP'' hff''
          have haR' : a ∉ R' :=
            fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (hR'sub h)).2).1 rfl
          have hbR' : f a ∉ R' := fun h => (Finset.mem_erase.mp (hR'sub h)).1 rfl
          refine ⟨insert a R', ?_, ?_⟩
          · intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact ha
            · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hR'sub hx))
          · intro e he
            by_cases hea : e = a
            · refine ⟨a, ⟨Finset.mem_insert_self a R', Or.inl hea.symm⟩, ?_⟩
              intro r' hr'
              rcases Finset.mem_insert.mp hr'.1 with hra | hrmem
              · exact hra
              · exfalso
                rcases hr'.2 with h | h
                · have h2 : r' = a := by rw [h, hea]
                  exact haR' (h2 ▸ hrmem)
                · have h2 : r' = f a := by rw [h, hea]
                  exact hbR' (h2 ▸ hrmem)
            · by_cases heb : e = f a
              · refine ⟨a, ⟨Finset.mem_insert_self a R', Or.inr ?_⟩, ?_⟩
                · rw [heb, hffa]
                · intro r' hr'
                  rcases Finset.mem_insert.mp hr'.1 with hra | hrmem
                  · exact hra
                  · exfalso
                    rcases hr'.2 with h | h
                    · have h2 : r' = f a := by rw [h, heb]
                      exact hbR' (h2 ▸ hrmem)
                    · have h2 : r' = a := by rw [h, heb, hffa]
                      exact haR' (h2 ▸ hrmem)
              · have heP' : e ∈ (P.erase a).erase (f a) :=
                  Finset.mem_erase.mpr ⟨heb, Finset.mem_erase.mpr ⟨hea, he⟩⟩
                obtain ⟨r, hr, huniq⟩ := hR'trans e heP'
                refine ⟨r, ⟨Finset.mem_insert_of_mem hr.1, hr.2⟩, ?_⟩
                intro r' hr'
                rcases Finset.mem_insert.mp hr'.1 with hra | hrmem
                · exfalso
                  rcases hr'.2 with h | h
                  · exact hea (h.symm.trans hra)
                  · have h2 : f a = e := by
                      have hh := congrArg f h
                      rw [hff e he] at hh
                      rw [hra] at hh
                      exact hh
                    exact heb h2.symm
                · exact huniq r' ⟨hrmem, hr'.2⟩
  exact aux P.card P le_rfl hfP hff

private lemma pslB3b_sum_transversal {α : Type} [DecidableEq α] (P R : Finset α) (f : α → α)
    (w : α → ℕ) (hfP : ∀ e ∈ P, f e ∈ P) (hff : ∀ e ∈ P, f (f e) = e) (hRsub : R ⊆ P)
    (htrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = f e)) (hw : ∀ e ∈ P, w (f e) = w e) :
    ∑ e ∈ P, w e = ∑ r ∈ R, (if f r = r then 1 else 2) * w r := by
  classical
  have hinner : ∀ e ∈ P, (∑ r ∈ R, (if r = e ∨ r = f e then w e else 0)) = w e := by
    intro e he
    obtain ⟨r0, hr0, huniq⟩ := htrans e he
    have h1 : ∀ b ∈ R, b ≠ r0 → (if b = e ∨ b = f e then w e else 0) = 0 := by
      intro b hb hbr0
      have hc : ¬ (b = e ∨ b = f e) := by
        rintro (h | h)
        · exact hbr0 (huniq b ⟨hb, Or.inl h⟩)
        · exact hbr0 (huniq b ⟨hb, Or.inr h⟩)
      rw [if_neg hc]
    have h2 : r0 ∉ R → (if r0 = e ∨ r0 = f e then w e else 0) = 0 :=
      fun hnot => absurd hr0.1 hnot
    rw [Finset.sum_eq_single r0 h1 h2, if_pos hr0.2]
  calc ∑ e ∈ P, w e
      = ∑ e ∈ P, (∑ r ∈ R, (if r = e ∨ r = f e then w e else 0)) := by
        refine Finset.sum_congr rfl (fun e he => ?_)
        rw [hinner e he]
    _ = ∑ r ∈ R, (∑ e ∈ P, (if r = e ∨ r = f e then w e else 0)) :=
        Finset.sum_comm
    _ = ∑ r ∈ R, (if f r = r then 1 else 2) * w r := by
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrP : r ∈ P := hRsub hr
      have hsubset : ({r, f r} : Finset α) ⊆ P := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hrP
        · exact hfP r hrP
      have hzero : ∀ x ∈ P, x ∉ ({r, f r} : Finset α) →
          (if r = x ∨ r = f x then w x else 0) = 0 := by
        intro x hx hxnot
        have h1 : r ≠ x := fun h => hxnot (by rw [← h]; exact Finset.mem_insert_self _ _)
        have h2 : r ≠ f x := by
          intro h
          apply hxnot
          have hh : f r = f (f x) := congrArg f h
          rw [hff x hx] at hh
          rw [← hh]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hc : ¬ (r = x ∨ r = f x) := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        rw [if_neg hc]
      have hswap : (∑ x ∈ ({r, f r} : Finset α),
          (if r = x ∨ r = f x then w x else 0)) =
          ∑ x ∈ P, (if r = x ∨ r = f x then w x else 0) :=
        Finset.sum_subset hsubset hzero
      rw [← hswap]
      by_cases hfr : f r = r
      · rw [hfr]
        simp
      · rw [Finset.sum_pair (a := r) (b := f r) (Ne.symm hfr), if_pos (Or.inl rfl),
          if_pos (Or.inr (hff r hrP).symm), hw r hrP, if_neg hfr]
        ring

private lemma pslB3b_rank_eq_finrank_range_toLin' {n : ℕ} {K : Type} [Field K]
    (M : Matrix (Fin n) (Fin n) K) :
    M.rank = Module.finrank K (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)),
    Matrix.toLin_eq_toLin']

private lemma pslB3b_rank_formAdj {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (a : Matrix (Fin n) (Fin n) K) :
    Matrix.rank (formAdj (RingHom.id K) G a) = Matrix.rank a := by
  have hid : a.map (RingHom.id K) = a := Matrix.map_id a
  have hX : (G⁻¹ * Matrix.transpose (a.map (RingHom.id K))).rank = Matrix.rank a := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹
      (Matrix.transpose (a.map (RingHom.id K))) (Matrix.isUnit_nonsing_inv_det G hG),
      hid, Matrix.rank_transpose]
  unfold formAdj
  rw [Matrix.rank_mul_eq_left_of_isUnit_det G
    (G⁻¹ * Matrix.transpose (a.map (RingHom.id K))) hG, hX]

private lemma pslB3b_range_add_toLin' {n : ℕ} {K : Type} [Field K]
    {p q : Matrix (Fin n) (Fin n) K} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hpq : p * q = 0) (hqp : q * p = 0) :
    LinearMap.range (Matrix.toLin' (p + q)) =
      LinearMap.range (Matrix.toLin' p) ⊔ LinearMap.range (Matrix.toLin' q) := by
  have hadd : Matrix.toLin' (p + q) = Matrix.toLin' p + Matrix.toLin' q :=
    (Matrix.toLin').map_add p q
  rw [hadd]
  refine le_antisymm (LinearMap.range_add_le _ _) (sup_le ?_ ?_)
  · rintro z ⟨x, rfl⟩
    refine LinearMap.mem_range.mpr ⟨p.mulVec x, ?_⟩
    rw [LinearMap.add_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hp.eq, hqp, Matrix.zero_mulVec, add_zero]
    exact (Matrix.toLin'_apply p x).symm
  · rintro z ⟨x, rfl⟩
    refine LinearMap.mem_range.mpr ⟨q.mulVec x, ?_⟩
    rw [LinearMap.add_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hq.eq, hpq, Matrix.zero_mulVec, zero_add]
    exact (Matrix.toLin'_apply q x).symm

private lemma pslB3b_rank_add_orth {n : ℕ} {K : Type} [Field K]
    {p q : Matrix (Fin n) (Fin n) K} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hpq : p * q = 0) (hqp : q * p = 0) :
    Matrix.rank (p + q) = Matrix.rank p + Matrix.rank q := by
  rw [pslB3b_rank_eq_finrank_range_toLin' (p + q), pslB3b_rank_eq_finrank_range_toLin' p,
    pslB3b_rank_eq_finrank_range_toLin' q]
  have hbot : LinearMap.range (Matrix.toLin' p) ⊓ LinearMap.range (Matrix.toLin' q) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨x, hx⟩ := hz1
    obtain ⟨y, hy⟩ := hz2
    have hpq0 : Matrix.toLin' p z = 0 := by
      rw [← hy]
      change ((Matrix.toLin' p) ∘ₗ (Matrix.toLin' q)) y = 0
      rw [← Matrix.toLin'_mul, hpq, map_zero]
      rfl
    have hpz : Matrix.toLin' p z = z := by
      rw [← hx]
      change ((Matrix.toLin' p) ∘ₗ (Matrix.toLin' p)) x = Matrix.toLin' p x
      rw [← Matrix.toLin'_mul, hp.eq]
    rw [← hpz, hpq0]
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (Matrix.toLin' p)) (LinearMap.range (Matrix.toLin' q))
  rw [hbot, finrank_bot, add_zero, ← pslB3b_range_add_toLin' hp hq hpq hqp] at hfin
  exact hfin

private lemma pslB3b_sum_rank_aux {n : ℕ} {K : Type} [Field K]
    (Q : Finset (Matrix (Fin n) (Fin n) K))
    (hidem : ∀ e ∈ Q, IsIdempotentElem e)
    (horth : ∀ e ∈ Q, ∀ e' ∈ Q, e ≠ e' → e * e' = 0) :
    IsIdempotentElem (∑ e ∈ Q, e) ∧ Matrix.rank (∑ e ∈ Q, e) = ∑ e ∈ Q, Matrix.rank e := by
  classical
  revert hidem horth
  refine Finset.induction_on Q ?_ ?_
  · intro hidem horth
    refine ⟨?_, by simp⟩
    rw [IsIdempotentElem]
    simp
  · intro a Q ha ih hidem horth
    obtain ⟨ihidem, ihrank⟩ := ih
      (fun e he => hidem e (Finset.mem_insert_of_mem he))
      (fun e he e' he' hne => horth e (Finset.mem_insert_of_mem he)
        e' (Finset.mem_insert_of_mem he') hne)
    have ha_idem : IsIdempotentElem a := hidem a (Finset.mem_insert_self a Q)
    have hneq : ∀ e ∈ Q, a ≠ e := by
      intro e he h
      exact ha (h ▸ he)
    have hpq : a * (∑ e ∈ Q, e) = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun e he =>
        horth a (Finset.mem_insert_self a Q) e (Finset.mem_insert_of_mem he) (hneq e he))
    have hqp : (∑ e ∈ Q, e) * a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero (fun e he =>
        horth e (Finset.mem_insert_of_mem he) a (Finset.mem_insert_self a Q)
          (fun h => hneq e he h.symm))
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_insert ha, IsIdempotentElem]
      calc (a + ∑ e ∈ Q, e) * (a + ∑ e ∈ Q, e)
          = a * a + a * (∑ e ∈ Q, e) +
              ((∑ e ∈ Q, e) * a + (∑ e ∈ Q, e) * (∑ e ∈ Q, e)) := by
            noncomm_ring
        _ = a + ∑ e ∈ Q, e := by
            rw [ha_idem.eq, hpq, hqp, ihidem.eq]
            abel
    · have hsplit : (∑ e ∈ insert a Q, e) = a + ∑ e ∈ Q, e := Finset.sum_insert ha
      rw [hsplit, pslB3b_rank_add_orth ha_idem ihidem hpq hqp, ihrank]
      exact (Finset.sum_insert (f := fun e => Matrix.rank e) ha).symm

private lemma pslB3b_sum_rank_P {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    n = ∑ e ∈ P, Matrix.rank e := by
  obtain ⟨-, hsum⟩ := pslB3b_sum_rank_aux P
    (fun e he => ((hP.1 e).1 he).2.1)
    (fun e he e' he' hne => hP.2.1 e he e' he' hne)
  rw [hP.2.2, Matrix.rank_one, Fintype.card_fin] at hsum
  exact hsum

open Classical in
private lemma pslB3b_dim_sum {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e)) :
    n = ∑ r ∈ R, (if formAdj (RingHom.id K) G r = r then 1 else 2) * Matrix.rank r := by
  refine (pslB3b_sum_rank_P P hP).trans ?_
  refine pslB3b_sum_transversal P R (formAdj (RingHom.id K) G) Matrix.rank hstar ?_ hRsub
    hRtrans ?_
  · have hmapid : G.map (RingHom.id K) = G := by ext a b; rfl
    have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by rw [hmapid, S.symm]
    intro e _
    exact Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit hGh e
  · intro e _
    exact pslB3b_rank_formAdj S.det_isUnit e

private lemma pslB3b_formAdj_formAdj {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a) = a := by
  have hmapid : G.map (RingHom.id K) = G := by ext i j; rfl
  have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by rw [hmapid, S.symm]
  exact Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit hGh a

private lemma pslB3b_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ pslAlg B, ∀ b ∈ pslAlg B, a * b = b * a := by
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    rw [hs, ht]
  letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommP
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : pslAlg B) (⟨b, hb⟩ : pslAlg B)
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private noncomputable def pslB3b_formAdjEquiv {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun := formAdj (RingHom.id K) G
  invFun := formAdj (RingHom.id K) G
  left_inv := pslB3b_formAdj_formAdj S
  right_inv := pslB3b_formAdj_formAdj S
  map_add' := Geo.formAdj_add (RingHom.id K) G
  map_smul' := Geo.formAdj_smul (RingHom.id K) G

private lemma pslB3b_blockDegree_star_mem {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ pslAlg B) :
    blockDegree (pslAlg B) (formAdj (RingHom.id K) G e) = blockDegree (pslAlg B) e := by
  have hmemE : formAdj (RingHom.id K) G e ∈ pslAlg B := pslGraph_star_mem S e he
  have hcomm := pslB3b_comm B
  have hS : (Subalgebra.toSubmodule (pslAlg B)).map
        (LinearMap.mulRight K (formAdj (RingHom.id K) G e)) =
      ((Subalgebra.toSubmodule (pslAlg B)).map (LinearMap.mulRight K e)).map
        (pslB3b_formAdjEquiv S).toLinearMap := by
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨formAdj (RingHom.id K) G a * e, ⟨formAdj (RingHom.id K) G a,
        pslGraph_star_mem S a ha, rfl⟩, ?_⟩
      show formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a * e) =
        a * formAdj (RingHom.id K) G e
      rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit,
        pslB3b_formAdj_formAdj S a]
      exact hcomm (formAdj (RingHom.id K) G e) hmemE a ha
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨formAdj (RingHom.id K) G a, pslGraph_star_mem S a ha, ?_⟩
      show formAdj (RingHom.id K) G a * formAdj (RingHom.id K) G e =
        formAdj (RingHom.id K) G (a * e)
      rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit]
      exact hcomm (formAdj (RingHom.id K) G a) (pslGraph_star_mem S a ha)
        (formAdj (RingHom.id K) G e) hmemE
  unfold blockDegree
  rw [hS]
  exact LinearEquiv.finrank_map_eq (pslB3b_formAdjEquiv S) _

private lemma pslB3b_blockDegree_dvd_rank {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    blockDegree (pslAlg B) e ∣ Matrix.rank e := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    -⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  exact ⟨Module.finrank F (LinearMap.range e.mulVecLin), by rw [← hdim, hrank]⟩

private lemma pslB3b_blockDegree_pos {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    1 ≤ blockDegree (pslAlg B) e := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    -⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  haveI : Module.Finite K F := Module.Finite.of_finite
  rw [← hdim]
  exact Module.finrank_pos

private lemma pslB3b_rank_pos {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    0 < Matrix.rank e := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    -⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  haveI : Module.Finite K F := Module.Finite.of_finite
  have hK : 0 < Module.finrank K F := Module.finrank_pos
  rw [hrank]
  exact Nat.mul_pos hK hpos

private lemma pslB3b_formAdj_algebraMap {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) (c : K) :
    formAdj (RingHom.id K) G (algebraMap K (Matrix (Fin n) (Fin n) K) c) =
      algebraMap K (Matrix (Fin n) (Fin n) K) c := by
  rw [Matrix.algebraMap_eq_diagonal]
  change formAdj (RingHom.id K) G (diagonal (fun _ : Fin n => c)) =
    diagonal (fun _ : Fin n => c)
  rw [← Matrix.smul_one_eq_diagonal, Geo.formAdj_smul,
    Geo.formAdj_one (RingHom.id K) S.det_isUnit]
  rfl

private noncomputable def pslB3b_thetaRingHom {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    pslAlg B →+* pslAlg B where
  toFun a := ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
    pslGraph_star_mem S a a.2⟩
  map_one' := Subtype.ext (Geo.formAdj_one (RingHom.id K) S.det_isUnit)
  map_mul' a b := by
    apply Subtype.ext
    have h : formAdj (RingHom.id K) G ((a : Matrix (Fin n) (Fin n) K) *
        (b : Matrix (Fin n) (Fin n) K)) =
        formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) *
          formAdj (RingHom.id K) G (b : Matrix (Fin n) (Fin n) K) := by
      rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit]
      exact pslB3b_comm B (formAdj (RingHom.id K) G (b : Matrix (Fin n) (Fin n) K))
        (pslGraph_star_mem S b b.2) (formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K))
        (pslGraph_star_mem S a a.2)
    exact h
  map_zero' := by
    apply Subtype.ext
    change formAdj (RingHom.id K) G (0 : Matrix (Fin n) (Fin n) K) = 0
    unfold formAdj
    rw [Matrix.map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
    rfl
  map_add' a b := by
    apply Subtype.ext
    have h : formAdj (RingHom.id K) G ((a : Matrix (Fin n) (Fin n) K) +
        (b : Matrix (Fin n) (Fin n) K)) =
        formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) +
          formAdj (RingHom.id K) G (b : Matrix (Fin n) (Fin n) K) :=
      Geo.formAdj_add (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K)
        (b : Matrix (Fin n) (Fin n) K)
    exact h

private noncomputable def pslB3b_thetaAlgHom {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    pslAlg B →ₐ[K] pslAlg B :=
  AlgHom.mk (pslB3b_thetaRingHom S) (fun c => Subtype.ext (pslB3b_formAdj_algebraMap S c))

private lemma pslB3b_typeII_even {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hII : pslTypeII G B e) :
    Even (blockDegree (pslAlg B) e) := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    -⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  haveI : Fintype F := Fintype.ofFinite F
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    rw [hs, ht]
  letI : CommRing (pslAlg B) := Algebra.adjoinCommRingOfComm K hcommP
  let θ := pslB3b_thetaAlgHom S
  have hθθ : ∀ a, θ (θ a) = a := by
    intro a
    apply Subtype.ext
    exact pslB3b_formAdj_formAdj S (a : Matrix (Fin n) (Fin n) K)
  have heA : e ∈ pslAlg B := ((hP.1 e).1 he).1
  have hθe : θ ⟨e, heA⟩ = ⟨e, heA⟩ := Subtype.ext hII.1
  have hH : RingHom.ker π.toRingHom ≤ RingHom.ker (π.comp θ).toRingHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    change π (θ a) = 0
    rw [hker]
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp ha
    have h1 : (θ a : pslAlg B) * ⟨e, heA⟩ = θ (a * ⟨e, heA⟩) := by
      calc (θ a : pslAlg B) * ⟨e, heA⟩ = θ a * θ ⟨e, heA⟩ := by rw [hθe]
        _ = θ (a * ⟨e, heA⟩) := (map_mul θ a ⟨e, heA⟩).symm
    have h2 : a * ⟨e, heA⟩ = 0 := Subtype.ext (by simpa using hae)
    calc ((θ a : pslAlg B) : Matrix (Fin n) (Fin n) K) * e
        = ((θ a * ⟨e, heA⟩ : pslAlg B) : Matrix (Fin n) (Fin n) K) := rfl
      _ = ((θ (a * ⟨e, heA⟩) : pslAlg B) : Matrix (Fin n) (Fin n) K) := by rw [h1]
      _ = 0 := by rw [h2, map_zero]; rfl
  let φ : F →ₐ[K] F := AlgHom.liftOfSurjective π hπ (π.comp θ) hH
  have hφ : ∀ a : pslAlg B, φ (π a) = π (θ a) := fun a =>
    AlgHom.liftOfSurjective_apply π hπ (π.comp θ) hH a
  have hφ2 : φ.comp φ = AlgHom.id K F := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    rw [AlgHom.comp_apply, hφ, hφ, show θ (θ a) = a from hθθ a]
    rfl
  have hφ1 : φ ≠ 1 := by
    intro h
    obtain ⟨a, ha, hne⟩ := hII.2
    have hπeq : π (θ ⟨a, ha⟩) = π ⟨a, ha⟩ := by
      have hh := AlgHom.congr_fun h (π ⟨a, ha⟩)
      rwa [AlgHom.one_apply, hφ] at hh
    have hzero : π (θ ⟨a, ha⟩ - ⟨a, ha⟩) = 0 := by rw [map_sub, hπeq, sub_self]
    have hmemM : ((θ ⟨a, ha⟩ : pslAlg B) : Matrix (Fin n) (Fin n) K) * e =
        ((⟨a, ha⟩ : pslAlg B) : Matrix (Fin n) (Fin n) K) * e := by
      have hh : (↑(θ ⟨a, ha⟩ - ⟨a, ha⟩) : Matrix (Fin n) (Fin n) K) * e = 0 :=
        (hker (θ ⟨a, ha⟩ - ⟨a, ha⟩)).mp hzero
      rw [Subalgebra.coe_sub, Matrix.sub_mul, sub_eq_zero] at hh
      exact hh
    have h3 : formAdj (RingHom.id K) G a * e = formAdj (RingHom.id K) G (a * e) := by
      calc formAdj (RingHom.id K) G a * e
          = formAdj (RingHom.id K) G a * formAdj (RingHom.id K) G e :=
            congrArg (fun x => formAdj (RingHom.id K) G a * x)
              (show e = formAdj (RingHom.id K) G e from hII.1.symm)
        _ = formAdj (RingHom.id K) G e * formAdj (RingHom.id K) G a :=
            pslB3b_comm B (formAdj (RingHom.id K) G a) (pslGraph_star_mem S a ha)
              (formAdj (RingHom.id K) G e) (pslGraph_star_mem S e heA)
        _ = formAdj (RingHom.id K) G (a * e) :=
            (Geo.formAdj_mul (RingHom.id K) S.det_isUnit a e).symm
    exact hne (by
      have h4 : formAdj (RingHom.id K) G a * e =
          ((⟨a, ha⟩ : pslAlg B) : Matrix (Fin n) (Fin n) K) * e := hmemM
      rw [h3] at h4
      exact h4)
  let τ : F ≃ₐ[K] F := AlgEquiv.ofAlgHom φ φ hφ2 hφ2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ2 : τ * τ = 1 := by
    ext x
    change φ (φ x) = x
    exact AlgHom.congr_fun hφ2 x
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hφ1
    ext x
    exact congrArg (fun z : F ≃ₐ[K] F => z x) h
  have horder : orderOf τ = 2 :=
    orderOf_eq_prime (by rwa [sq]) hτ1
  have hdvd1 : orderOf τ ∣ Nat.card (F ≃ₐ[K] F) := orderOf_dvd_natCard τ
  have hdvd2 : Nat.card (F ≃ₐ[K] F) ∣ Module.finrank K F :=
    TauCeti.natCard_algEquiv_dvd_finrank K F
  have h2dvd : 2 ∣ Module.finrank K F := by
    rw [← horder]
    exact dvd_trans hdvd1 hdvd2
  rw [← hdim, even_iff_two_dvd]
  exact h2dvd

private lemma pslB3b_block_data {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    blockDegree (pslAlg B) e ∣ Matrix.rank e ∧ 1 ≤ blockDegree (pslAlg B) e ∧
      0 < Matrix.rank e ∧ (pslTypeII G B e → Even (blockDegree (pslAlg B) e)) := by
  exact ⟨pslB3b_blockDegree_dvd_rank S P hP e he, pslB3b_blockDegree_pos S P hP e he,
    pslB3b_rank_pos S P hP e he, fun hII => pslB3b_typeII_even S P hP e he hII⟩

private lemma pslB3b_norm_mul_kernel_card {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    Nat.card (pslNormImage G B) *
      Nat.card {t : (pslAlg B)ˣ |
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1} =
      Nat.card ((pslAlg B)ˣ) := by
  classical
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    rw [hs, ht]
  letI : CommRing (pslAlg B) := Algebra.adjoinCommRingOfComm K hcommP
  let f : pslAlg B →* pslAlg B := (pslB3b_thetaRingHom S).toMonoidHom
  let Nfun : (pslAlg B)ˣ → (pslAlg B)ˣ := fun t => Units.map f t * t
  have hN : ∀ t : (pslAlg B)ˣ,
      ((Nfun t : (pslAlg B)ˣ) : Matrix (Fin n) (Fin n) K) =
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) := by
    intro t
    change ((Units.map f t * t : (pslAlg B)ˣ) : Matrix (Fin n) (Fin n) K) = _
    rw [Units.val_mul]
    rfl
  let N : (pslAlg B)ˣ →* (pslAlg B)ˣ :=
    { toFun := Nfun
      map_one' := by simp [Nfun]
      map_mul' := by
        intro a b
        change Units.map f (a * b) * (a * b) =
          (Units.map f a * a) * (Units.map f b * b)
        rw [map_mul]
        ac_rfl }
  have hN' : ∀ t : (pslAlg B)ˣ,
      ((N t : (pslAlg B)ˣ) : Matrix (Fin n) (Fin n) K) =
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) := fun t => hN t
  have hkerSet : ∀ t : (pslAlg B)ˣ,
      (N t = 1) ↔ formAdj (RingHom.id K) G
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
        ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1 := by
    intro t
    constructor
    · intro h
      exact (hN' t).symm.trans (by rw [h]; rfl)
    · intro h
      apply Units.ext
      apply Subtype.ext
      simpa using (hN' t).trans h
  have hker : Nat.card N.ker =
      Nat.card {t : (pslAlg B)ˣ |
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1} := by
    apply Nat.card_congr
    exact
      { toFun := fun t => ⟨t.1, (hkerSet t.1).mp t.2⟩
        invFun := fun t => ⟨t.1, (hkerSet t.1).mpr t.2⟩
        left_inv := fun t => rfl
        right_inv := fun t => rfl }
  have hrange : Nat.card N.range = Nat.card (pslNormImage G B) := by
    have hset : (N.range : Set (pslAlg B)ˣ).image
        (fun u : (pslAlg B)ˣ => ((u : pslAlg B) : Matrix (Fin n) (Fin n) K)) =
        pslNormImage G B := by
      ext m
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨t, rfl⟩ := hu
        exact ⟨t, (hN' t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨N t, ⟨t, rfl⟩, (hN' t).symm⟩
    rw [← hset]
    exact (Nat.card_image_of_injective (f := fun u : (pslAlg B)ˣ =>
      ((u : pslAlg B) : Matrix (Fin n) (Fin n) K))
      (fun u v huv => Units.ext (Subtype.ext huv)) (N.range : Set (pslAlg B)ˣ)).symm
  rw [← hrange, ← hker, Nat.mul_comm, ← Subgroup.index_ker N, Subgroup.card_mul_index N.ker]

private lemma pslB3b_units_card {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    Nat.card ((pslAlg B)ˣ) =
      ∏ e ∈ P, (Nat.card K ^ blockDegree (pslAlg B) e - 1) := by
  classical
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    rw [hs, ht]
  letI : CommRing (pslAlg B) := Algebra.adjoinCommRingOfComm K hcommP
  let I := {e : Matrix (Fin n) (Fin n) K // e ∈ P}
  haveI : Fintype I := by dsimp only [I]; infer_instance
  let ee : I → pslAlg B := fun i => ⟨i.1, ((hP.1 i.1).mp i.2).1⟩
  have hIuniv : P.attach = (Finset.univ : Finset I) := by
    apply Finset.eq_univ_of_forall
    intro x
    exact Finset.mem_attach P x
  have horth : OrthogonalIdempotents ee := by
    refine ⟨?_, ?_⟩
    · intro i
      exact Subtype.ext ((hP.1 i.1).mp i.2).2.1.eq
    · intro i j hij
      have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      exact Subtype.ext (hP.2.1 i.1 i.2 j.1 j.2 hne)
  have hsum : ∑ i : I, ee i = 1 := by
    apply Subtype.ext
    change (Subalgebra.val (pslAlg B)) (∑ i : I, ee i) = 1
    rw [map_sum]
    have h1 : (∑ x ∈ P.attach, (x.1 : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [Finset.sum_attach P (fun e => e)]
      exact hP.2.2
    rw [← hIuniv]
    simpa using h1
  have hCO : CompleteOrthogonalIdempotents ee := CompleteOrthogonalIdempotents.mk horth hsum
  let Φ : pslAlg B ≃+* ((i : I) → pslAlg B ⧸ Ideal.span {1 - ee i}) :=
    RingEquiv.ofBijective (RingHom.pi (fun i => Ideal.Quotient.mk (Ideal.span {1 - ee i})))
      (CompleteOrthogonalIdempotents.bijective_pi hCO)
  have hcard1 : Nat.card ((pslAlg B)ˣ) =
      Nat.card ((i : I) → (pslAlg B ⧸ Ideal.span {1 - ee i})ˣ) :=
    Nat.card_eq_of_bijective
      (fun u : (pslAlg B)ˣ => MulEquiv.piUnits (Units.mapEquiv Φ.toMulEquiv u))
      (MulEquiv.piUnits.bijective.comp (Units.mapEquiv Φ.toMulEquiv).bijective)
  rw [hcard1, Nat.card_pi,
    ← Finset.prod_attach P (fun e => Nat.card K ^ blockDegree (pslAlg B) e - 1), hIuniv]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank, hpos,
    -⟩ := exists_blockEmbed S.odd rfl ((hP.1 i.1).mp i.2)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  have hidem : ee i * ee i = ee i := by
    apply Subtype.ext
    exact ((hP.1 i.1).mp i.2).2.1.eq
  have hkerEq : RingHom.ker π.toRingHom = Ideal.span ({1 - ee i} : Set (pslAlg B)) := by
    ext a
    change π a = 0 ↔ a ∈ Ideal.span ({1 - ee i} : Set (pslAlg B))
    rw [hker, Ideal.mem_span_singleton]
    constructor
    · intro ha
      refine ⟨a, ?_⟩
      have h0 : ee i * a = 0 := by
        rw [mul_comm (ee i) a]
        apply Subtype.ext
        simpa [Subalgebra.coe_mul] using ha
      rw [sub_mul, one_mul, h0, sub_zero]
    · rintro ⟨c, rfl⟩
      have h0 : (1 - ee i) * c * ee i = 0 := by
        rw [mul_assoc, mul_comm c (ee i), ← mul_assoc, sub_mul, one_mul,
          hidem, sub_self, zero_mul]
      have hh := congrArg (fun z : pslAlg B => (z : Matrix (Fin n) (Fin n) K)) h0
      simpa [Subalgebra.coe_mul] using hh
  let Ψ : (pslAlg B) ⧸ Ideal.span ({1 - ee i} : Set (pslAlg B)) →+* F :=
    Ideal.Quotient.lift _ π.toRingHom (fun a ha => RingHom.mem_ker.mp (hkerEq.symm ▸ ha))
  have hΨbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      change π a = π b at hxy
      rw [Ideal.Quotient.eq, ← hkerEq, RingHom.mem_ker, map_sub]
      change π a - π b = 0
      rw [sub_eq_zero]
      exact hxy
    · intro y
      obtain ⟨a, ha⟩ := hπ y
      exact ⟨Ideal.Quotient.mk _ a, ha⟩
  let E : (pslAlg B) ⧸ Ideal.span ({1 - ee i} : Set (pslAlg B)) ≃+* F :=
    RingEquiv.ofBijective Ψ hΨbij
  rw [Nat.card_eq_of_bijective (fun u : ((pslAlg B) ⧸
      Ideal.span ({1 - ee i} : Set (pslAlg B)))ˣ => Units.mapEquiv E.toMulEquiv u)
    (Units.mapEquiv E.toMulEquiv).bijective, Nat.card_units F, hcard]

private lemma pslB3bg2_mem_span_one_sub {R : Type*} [CommRing R] {ε : R}
    (hε : IsIdempotentElem ε) (a : R) :
    a * ε = 0 ↔ a ∈ Ideal.span ({1 - ε} : Set R) := by
  constructor
  · intro h
    have ha : a = a * (1 - ε) := by rw [mul_sub, mul_one, h, sub_zero]
    rw [ha]
    exact Ideal.mul_mem_left _ a (Ideal.subset_span (Set.mem_singleton _))
  · intro ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    rw [hc, mul_assoc, mul_comm c, ← mul_assoc, IsIdempotentElem.one_sub_mul_self hε,
      zero_mul]

private lemma pslB3bg2_quot_equiv {R F : Type*} [CommRing R] [Field F]
    (ε : R) (hε : IsIdempotentElem ε) (π : R →+* F) (hsurj : Function.Surjective π)
    (hker : ∀ a, π a = 0 ↔ a * ε = 0) :
    ∃ q : R ⧸ Ideal.span ({1 - ε} : Set R) ≃+* F,
      ∀ a, q (Ideal.Quotient.mk _ a) = π a := by
  classical
  let I : Ideal R := Ideal.span ({1 - ε} : Set R)
  have hzero : ∀ a ∈ I, π a = 0 := by
    intro a ha
    rw [hker a]
    exact (pslB3bg2_mem_span_one_sub hε a).mpr ha
  let f : R ⧸ I →+* F := Ideal.Quotient.lift I π hzero
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hxy
      rw [Ideal.Quotient.eq]
      have h1 : π (a - b) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hker] at h1
      exact (pslB3bg2_mem_span_one_sub hε (a - b)).mp h1
    · intro y
      obtain ⟨a, ha⟩ := hsurj y
      exact ⟨Ideal.Quotient.mk I a, by rw [Ideal.Quotient.lift_mk, ha]⟩
  refine ⟨RingEquiv.ofBijective f hf, ?_⟩
  intro a
  show f (Ideal.Quotient.mk I a) = π a
  rw [Ideal.Quotient.lift_mk]

private lemma pslB3bg2_pairwise_commute {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    (Units.val '' ({B} : Set (GL (Fin n) K)) : Set (Matrix (Fin n) (Fin n) K)).Pairwise
      Commute := by
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
  rw [Set.mem_singleton_iff] at hs ht
  subst hs
  subst ht
  exact Commute.refl _

@[instance_reducible]
private noncomputable def pslB3bg2_commRing {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) : CommRing (pslAlg B) :=
  Algebra.adjoinCommRingOfComm K (pslB3bg2_pairwise_commute B)

private def pslB3bg2_idemFam {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    {e // e ∈ P} → pslAlg B :=
  fun i => ⟨i.1, ((hP.1 i.1).mp i.2).1⟩

private lemma pslB3bg2_orthIdem {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    OrthogonalIdempotents (pslB3bg2_idemFam B P hP) := by
  refine ⟨?_, ?_⟩
  · intro i
    apply Subtype.ext
    show (i.1 : Matrix (Fin n) (Fin n) K) * i.1 = i.1
    exact (((hP.1 i.1).mp i.2).2.1).eq
  · intro i j hij
    apply Subtype.ext
    show (i.1 : Matrix (Fin n) (Fin n) K) * j.1 = 0
    exact hP.2.1 i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))

private lemma pslB3bg2_dag_mul_eq_zero {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a e : Matrix (Fin n) (Fin n) K) (ha : a ∈ pslAlg B) (he : e ∈ pslAlg B) :
    formAdj (RingHom.id K) G a * e = 0 ↔ a * formAdj (RingHom.id K) G e = 0 := by
  have hzero : formAdj (RingHom.id K) G (0 : Matrix (Fin n) (Fin n) K) = 0 := by
    simp [formAdj]
  constructor
  · intro hz
    have h1 : formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a * e) = 0 := by
      rw [hz, hzero]
    rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit, pslB3b_formAdj_formAdj S a] at h1
    rw [pslB3b_comm B (formAdj (RingHom.id K) G e) (pslGraph_star_mem S e he) a ha] at h1
    exact h1
  · intro hz
    have h1 : formAdj (RingHom.id K) G (a * formAdj (RingHom.id K) G e) = 0 := by
      rw [hz, hzero]
    rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit, pslB3b_formAdj_formAdj S e] at h1
    rw [pslB3b_comm B e he (formAdj (RingHom.id K) G a) (pslGraph_star_mem S a ha)] at h1
    exact h1

private lemma pslB3b_block_prod {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    ∃ (F : {e // e ∈ P} → Type) (_ : ∀ e, Field (F e)) (_ : ∀ e, Algebra K (F e))
      (_ : ∀ e, Finite (F e)) (_ : ∀ e, CharP (F e) 2)
      (π : ∀ e, pslAlg B →ₐ[K] F e),
      (∀ e, Function.Surjective (π e)) ∧
      (∀ e (a : pslAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0) ∧
      (∀ e, Module.finrank K (F e) = blockDegree (pslAlg B) e.1) ∧
      (∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (pslAlg B) e.1) ∧
      Function.Bijective (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a) := by
  classical
  letI : CommRing (pslAlg B) := pslB3bg2_commRing B
  have horth : OrthogonalIdempotents (pslB3bg2_idemFam B P hP) := pslB3bg2_orthIdem B P hP
  have hsum : (∑ i : {e // e ∈ P}, pslB3bg2_idemFam B P hP i) = 1 := by
    apply Subtype.ext
    show ((∑ i : {e // e ∈ P}, pslB3bg2_idemFam B P hP i : pslAlg B) :
      Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K)
    have hcoe : ((∑ i : {e // e ∈ P}, pslB3bg2_idemFam B P hP i : pslAlg B) :
        Matrix (Fin n) (Fin n) K) = ∑ i : {e // e ∈ P}, i.1 := by
      change (Subalgebra.val (pslAlg B) (∑ i : {e // e ∈ P},
        pslB3bg2_idemFam B P hP i) : Matrix (Fin n) (Fin n) K) =
        ∑ i : {e // e ∈ P}, i.1
      rw [map_sum (Subalgebra.val (pslAlg B))]
      apply Finset.sum_congr rfl
      intro i _
      rw [Subalgebra.val_apply]
      rfl
    rw [hcoe]
    change (P.attach.sum (fun i : {e // e ∈ P} =>
      (i.1 : Matrix (Fin n) (Fin n) K))) = 1
    exact (Finset.sum_attach P (fun x => x)).trans hP.2.2
  have hCO : CompleteOrthogonalIdempotents (pslB3bg2_idemFam B P hP) :=
    CompleteOrthogonalIdempotents.mk horth hsum
  have key : ∀ e : {e // e ∈ P}, ∃ (F : Type) (_ : Field F) (_ : Algebra K F)
      (_ : Finite F) (_ : CharP F 2) (π : pslAlg B →ₐ[K] F),
      Function.Surjective π ∧
      (∀ a : pslAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0) ∧
      Module.finrank K F = blockDegree (pslAlg B) e.1 ∧
      Nat.card F = Nat.card K ^ blockDegree (pslAlg B) e.1 := by
    intro e
    obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, _⟩ :=
      exists_blockEmbed (A := pslAlg B) S.odd rfl ((hP.1 e.1).mp e.2)
    exact ⟨F, hFld, hAlg, hFin, hChar, π, hπ, hker, hdim, hcard⟩
  choose F fieldF algF finF charF π hdata using key
  have hπ : ∀ e, Function.Surjective (π e) := fun e => (hdata e).1
  have hker : ∀ e (a : pslAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0 :=
    fun e => (hdata e).2.1
  have hdim : ∀ e, Module.finrank K (F e) = blockDegree (pslAlg B) e.1 :=
    fun e => (hdata e).2.2.1
  have hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (pslAlg B) e.1 :=
    fun e => (hdata e).2.2.2
  letI := fieldF
  letI := algF
  letI := finF
  letI := charF
  refine ⟨F, fieldF, algF, finF, charF, π, hπ, hker, hdim, hcard, ?_⟩
  have hker' : ∀ (e : {e // e ∈ P}) (a : pslAlg B),
      π e a = 0 ↔ a * pslB3bg2_idemFam B P hP e = 0 := by
    intro e a
    rw [hker e a]
    constructor
    · intro h
      exact Subtype.ext (by simpa [pslB3bg2_idemFam] using h)
    · intro h
      exact by simpa [pslB3bg2_idemFam] using congrArg Subtype.val h
  let q : ∀ e : {e // e ∈ P},
      pslAlg B ⧸ Ideal.span ({1 - pslB3bg2_idemFam B P hP e} : Set (pslAlg B)) ≃+* F e :=
    fun e => Classical.choose (pslB3bg2_quot_equiv (pslB3bg2_idemFam B P hP e)
      (horth.1 e) (π e).toRingHom (hπ e) (hker' e))
  have hq : ∀ e (a : pslAlg B),
      q e (Ideal.Quotient.mk _ a) = π e a :=
    fun e => Classical.choose_spec (pslB3bg2_quot_equiv (pslB3bg2_idemFam B P hP e)
      (horth.1 e) (π e).toRingHom (hπ e) (hker' e))
  have hbij : Function.Bijective (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a) := by
    have hcomp : (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a) =
        ⇑(RingEquiv.piCongrRight q) ∘
          ⇑(RingHom.pi (fun i : {e // e ∈ P} =>
            Ideal.Quotient.mk (Ideal.span ({1 - pslB3bg2_idemFam B P hP i} :
              Set (pslAlg B))))) := by
      funext a i
      change π i a = (RingEquiv.piCongrRight q
        ((RingHom.pi (fun i : {e // e ∈ P} =>
          Ideal.Quotient.mk (Ideal.span ({1 - pslB3bg2_idemFam B P hP i} :
            Set (pslAlg B))))) a)) i
      rw [RingEquiv.piCongrRight_apply, RingHom.pi_apply]
      exact (hq i a).symm
    rw [hcomp]
    have h1 : Function.Bijective (⇑(RingEquiv.piCongrRight q)) :=
      (RingEquiv.piCongrRight q).toEquiv.bijective
    exact Function.Bijective.comp h1 (CompleteOrthogonalIdempotents.bijective_pi hCO)
  exact hbij

private lemma pslB3b_star_transport {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : pslAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0) :
    ∃ ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e),
      ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
        π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
            pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a) := by
  classical
  letI : CommRing (pslAlg B) := pslB3bg2_commRing B
  have horth : OrthogonalIdempotents (pslB3bg2_idemFam B P hP) := pslB3bg2_orthIdem B P hP
  have hidem : ∀ e : {e // e ∈ P}, IsIdempotentElem (pslB3bg2_idemFam B P hP e) :=
    fun e => horth.1 e
  have hker' : ∀ (e : {e // e ∈ P}) (a : pslAlg B),
      π e a = 0 ↔ a * pslB3bg2_idemFam B P hP e = 0 := by
    intro e a
    rw [hker e a]
    constructor
    · intro h
      exact Subtype.ext (by simpa [pslB3bg2_idemFam] using h)
    · intro h
      exact by simpa [pslB3bg2_idemFam] using congrArg Subtype.val h
  let q : ∀ e' : {e // e ∈ P},
      pslAlg B ⧸ Ideal.span ({1 - pslB3bg2_idemFam B P hP e'} : Set (pslAlg B)) ≃+* F e' :=
    fun e' => Classical.choose (pslB3bg2_quot_equiv (pslB3bg2_idemFam B P hP e')
      (hidem e') (π e').toRingHom (hπ e') (hker' e'))
  have hq : ∀ e' (a : pslAlg B), q e' (Ideal.Quotient.mk _ a) = π e' a :=
    fun e' => Classical.choose_spec (pslB3bg2_quot_equiv (pslB3bg2_idemFam B P hP e')
      (hidem e') (π e').toRingHom (hπ e') (hker' e'))
  let σdag : (e : {e // e ∈ P}) → (pslAlg B →+* F e) :=
    fun e => (π e).toRingHom.comp (pslB3b_thetaRingHom S)
  have hsurj_dag : Function.Surjective (pslB3b_thetaRingHom S : pslAlg B → pslAlg B) := by
    intro y
    refine ⟨⟨formAdj (RingHom.id K) G y.1, (pslGraph_star_mem S y.1 y.2)⟩, ?_⟩
    apply Subtype.ext
    show formAdj (RingHom.id K) G (formAdj (RingHom.id K) G y.1) = y.1
    rw [pslB3b_formAdj_formAdj S]
  have hsurjdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      Function.Surjective (σdag e) := by
    intro e e' he
    show Function.Surjective (fun x : pslAlg B => π e ((pslB3b_thetaRingHom S) x))
    exact Function.Surjective.comp (hπ e) hsurj_dag
  have hkerdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1)
      (a : pslAlg B),
      σdag e a = 0 ↔ a * pslB3bg2_idemFam B P hP e' = 0 := by
    intro e e' he a
    have h1 : σdag e a =
        π e ⟨formAdj (RingHom.id K) G a.1, (pslGraph_star_mem S a.1 a.2)⟩ := rfl
    rw [h1, hker e ⟨formAdj (RingHom.id K) G a.1, (pslGraph_star_mem S a.1 a.2)⟩]
    have h2 : formAdj (RingHom.id K) G a.1 * e.1 = 0 ↔
        a.1 * formAdj (RingHom.id K) G e.1 = 0 :=
      pslB3bg2_dag_mul_eq_zero S a.1 e.1 a.2 ((hP.1 e.1).mp e.2).1
    rw [h2, ← he]
    constructor
    · intro h
      exact Subtype.ext (by simpa [pslB3bg2_idemFam] using h)
    · intro h
      exact by simpa [pslB3bg2_idemFam] using congrArg Subtype.val h
  let qdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      pslAlg B ⧸ Ideal.span ({1 - pslB3bg2_idemFam B P hP e'} : Set (pslAlg B)) ≃+* F e :=
    fun e e' he => Classical.choose (pslB3bg2_quot_equiv (pslB3bg2_idemFam B P hP e')
      (hidem e') (σdag e) (hsurjdag e e' he) (hkerdag e e' he))
  have hqdag : ∀ (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1)
      (a : pslAlg B),
      qdag e e' he (Ideal.Quotient.mk _ a) = σdag e a :=
    fun e e' he => Classical.choose_spec (pslB3bg2_quot_equiv (pslB3bg2_idemFam B P hP e')
      (hidem e') (σdag e) (hsurjdag e e' he) (hkerdag e e' he))
  let ι0 : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e) :=
    fun e e' he => (q e').symm.trans (qdag e e' he)
  refine ⟨ι0, ?_⟩
  · intro a e e' he
    have h1 : (q e').symm (π e' a) = Ideal.Quotient.mk _ a := by
      rw [← hq e' a, RingEquiv.symm_apply_apply]
    have h2 : qdag e e' he (Ideal.Quotient.mk _ a) = σdag e a := hqdag e e' he a
    change π e ⟨formAdj (RingHom.id K) G a.1, (pslGraph_star_mem S a.1 a.2)⟩ =
      (qdag e e' he) ((q e').symm (π e' a))
    rw [h1, h2]
    rfl

private lemma pslB3b_kernel_II {F : Type} [Field F] [Finite F] (θ : F ≃+* F)
    (hθ2 : θ * θ = 1) (hθ1 : θ ≠ 1) :
    ∃ Q : ℕ, Nat.card F = Q * Q ∧
      Nat.card {t : Fˣ | θ (t : F) * (t : F) = 1} = Q + 1 := by
  classical
  obtain ⟨Q, hQ, hRange⟩ := pslGraph_norm_card_II (F := F) θ hθ2 hθ1
  let N : Fˣ →* Fˣ := Units.map θ.toRingHom.toMonoidHom * MonoidHom.id Fˣ
  have hNval : ∀ u : Fˣ, ((N u : Fˣ) : F) = θ (u : F) * (u : F) := by
    intro u
    simp only [N, MonoidHom.mul_apply, Units.val_mul, Units.coe_map, MonoidHom.id_apply]
    rfl
  have hRangeE : Nat.card (Set.range (fun u : Fˣ => ((N u : Fˣ) : F))) = Q - 1 := by
    rw [show (fun u : Fˣ => ((N u : Fˣ) : F)) = (fun u : Fˣ => θ (u : F) * (u : F))
      from funext hNval]
    exact hRange
  have himg : Set.range (fun u : Fˣ => ((N u : Fˣ) : F)) =
      (fun u : Fˣ => (u : F)) '' (Set.range fun u : Fˣ => N u) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨N u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  rw [himg, Nat.card_image_of_injective (fun a b h => Units.ext h)] at hRangeE
  have hRangeKer : Nat.card N.range = Q - 1 := by
    have h := hRangeE
    rw [show Set.range (fun u : Fˣ => N u) = ((N.range : Subgroup Fˣ) : Set Fˣ) from
      (MonoidHom.coe_range N).symm] at h
    exact h
  have hQ2 : 2 ≤ Q := by
    have h2 : 2 ≤ Q * Q := by
      rw [← hQ]
      haveI : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    nlinarith
  have hker : Nat.card N.ker = Q + 1 := by
    have h := Subgroup.card_mul_index N.ker
    rw [Subgroup.index_ker, hRangeKer, Nat.card_units, hQ] at h
    have hsq : Q * Q - 1 = (Q + 1) * (Q - 1) := by
      have h1 : 1 ≤ Q := by omega
      have h2 : 1 ≤ Q * Q := by nlinarith
      nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
    rw [hsq] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  refine ⟨Q, hQ, ?_⟩
  have hset : Nat.card {t : Fˣ | θ (t : F) * (t : F) = 1} = Nat.card N.ker := by
    apply Nat.card_congr
    refine
      { toFun := fun t => ⟨t.1, ?_⟩
        invFun := fun u => ⟨u.1, ?_⟩
        left_inv := fun t => rfl
        right_inv := fun u => rfl }
    · apply Units.ext
      rw [hNval t, Units.val_one]
      exact t.2
    · have h := congrArg (fun z : Fˣ => (z : F)) u.2
      rw [hNval u, Units.val_one] at h
      exact h
  rw [hset, hker]

private def pslB3b_R {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) : {e // e ∈ P} → {e // e ∈ P} → Prop :=
  fun x y => y.1 = formAdj (RingHom.id K) G x.1

private noncomputable def pslB3b_cls {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (e : {e // e ∈ P}) : {r // r ∈ R} :=
  ⟨Classical.choose (hRtrans e.1 e.2), (Classical.choose_spec (hRtrans e.1 e.2)).1.1⟩

private lemma pslB3bkga_star_mem_of_primFamily {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P := by
  obtain ⟨P', hP', hcl⟩ := pslGraph_primFamily S
  intro e he
  exact (hP.1 _).mpr ((hP'.1 _).mp (hcl e ((hP'.1 _).mpr ((hP.1 e).mp he))))

private lemma pslB3bkga_cond_forward {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    (a : pslAlg B) (ha : pslB3b_thetaRingHom S a * a = 1) :
    ∀ (x y : {e // e ∈ P}) (h : pslB3b_R G P x y),
      ι x y h (π y a) * π x a = 1 := by
  intro x y h
  have hstep : π x (pslB3b_thetaRingHom S a) = ι x y h (π y a) := hι a x y h
  rw [← hstep, ← map_mul, ha, map_one]

private lemma pslB3bkga_cond_backward {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e)
    (hbij : Function.Bijective (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    (a : pslAlg B) (H : ∀ (x y : {e // e ∈ P}) (h : pslB3b_R G P x y),
      ι x y h (π y a) * π x a = 1) :
    pslB3b_thetaRingHom S a * a = 1 := by
  apply hbij.1
  funext e
  change π e (pslB3b_thetaRingHom S a * a) = π e 1
  have hy : pslB3b_R G P e ⟨formAdj (RingHom.id K) G e.1, hstar e.1 e.2⟩ := rfl
  have hstep : π e (pslB3b_thetaRingHom S a) =
      ι e ⟨formAdj (RingHom.id K) G e.1, hstar e.1 e.2⟩ hy
        (π ⟨formAdj (RingHom.id K) G e.1, hstar e.1 e.2⟩ a) := hι a e _ hy
  rw [map_mul, hstep, H e ⟨formAdj (RingHom.id K) G e.1, hstar e.1 e.2⟩ hy, map_one]

private noncomputable def pslB3bkga_algEquivFamilies {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K}
    (S : PSLGraphSetting n K G B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e)
    (hbij : Function.Bijective (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a)) :
    {a : pslAlg B // pslB3b_thetaRingHom S a * a = 1} ≃
      LocalFamilies (pslB3b_R G P) ι {e // e ∈ P} (fun x => x) where
  toFun a := ⟨fun e => π e a.1, pslB3bkga_cond_forward S P F π ι hι a.1 a.2⟩
  invFun z := by
    refine ⟨Classical.choose (hbij.2 z.1), ?_⟩
    have hspec := Classical.choose_spec (hbij.2 z.1)
    refine pslB3bkga_cond_backward S P hstar F π hbij ι hι _ ?_
    intro x y h
    have hy : π y (Classical.choose (hbij.2 z.1)) = z.1 y := congrFun hspec y
    have hx : π x (Classical.choose (hbij.2 z.1)) = z.1 x := congrFun hspec x
    rw [hy, hx]
    exact z.2 x y h
  left_inv a := by
    apply Subtype.ext
    exact hbij.1 (Classical.choose_spec (hbij.2 (fun e => π e a.1)))
  right_inv z := by
    apply Subtype.ext
    exact Classical.choose_spec (hbij.2 z.1)

private noncomputable def pslB3bkga_unitsEquivAlg {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K}
    (S : PSLGraphSetting n K G B) :
    {t : (pslAlg B)ˣ // formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
        ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1} ≃
      {a : pslAlg B // pslB3b_thetaRingHom S a * a = 1} where
  toFun t := ⟨(t.1 : pslAlg B), by
    apply Subtype.ext
    show formAdj (RingHom.id K) G ((t.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) *
      ((t.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1
    exact t.2⟩
  invFun a := ⟨⟨a.1, pslB3b_thetaRingHom S a.1, by
      have hc : ((a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((pslB3b_thetaRingHom S a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) =
          ((pslB3b_thetaRingHom S a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) *
            ((a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) :=
        pslB3b_comm B ((a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) a.1.2
          ((pslB3b_thetaRingHom S a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K)
          (pslB3b_thetaRingHom S a.1).2
      apply Subtype.ext
      rw [Subalgebra.coe_mul, hc]
      simpa using congrArg Subtype.val a.2,
      a.2⟩, by
    show formAdj (RingHom.id K) G ((a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) *
      ((a.1 : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1
    exact congrArg Subtype.val a.2⟩
  left_inv t := by
    apply Subtype.ext
    exact Units.ext rfl
  right_inv a := by
    apply Subtype.ext
    rfl

private lemma pslB3b_cls_rel {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (R : Finset (Matrix (Fin n) (Fin n) K))
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (a b : {e // e ∈ P}) (hab : pslB3b_R G P a b) :
    pslB3b_cls G P R hRtrans a = pslB3b_cls G P R hRtrans b := by
  apply Subtype.ext
  have hspec_a := Classical.choose_spec (hRtrans a.1 a.2)
  have hspec_b := Classical.choose_spec (hRtrans b.1 b.2)
  have hab' : b.1 = formAdj (RingHom.id K) G a.1 := hab
  have hff : formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a.1) = a.1 :=
    pslB3b_formAdj_formAdj S a.1
  have hmem : Classical.choose (hRtrans b.1 b.2) ∈ R ∧
      (Classical.choose (hRtrans b.1 b.2) = a.1 ∨
        Classical.choose (hRtrans b.1 b.2) = formAdj (RingHom.id K) G a.1) := by
    refine ⟨hspec_b.1.1, ?_⟩
    rcases hspec_b.1.2 with h | h
    · exact Or.inr (by rw [h, hab'])
    · exact Or.inl (by rw [h, hab', hff])
  exact (hspec_a.2 _ hmem).symm

private lemma pslB3b_card_units_eq_families {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e)
    (hbij : Function.Bijective (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a)) :
    Nat.card {t : (pslAlg B)ˣ |
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1} =
      Nat.card (LocalFamilies (pslB3b_R G P) ι {e // e ∈ P} (fun x => x)) := by
  classical
  have hstar := pslB3bkga_star_mem_of_primFamily S P hP
  exact (Nat.card_congr (pslB3bkga_unitsEquivAlg S)).trans
    (Nat.card_congr (pslB3bkga_algEquivFamilies S P hstar F π hbij ι hι))

private lemma pslB3bg1b_cls_eq_iff {n : ℕ} {K : Type} [Field K]
    (G : Matrix (Fin n) (Fin n) K) (P R : Finset (Matrix (Fin n) (Fin n) K))
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (e : {e // e ∈ P}) (r : {r // r ∈ R}) :
    pslB3b_cls G P R hRtrans e = r ↔
      (r.1 = e.1 ∨ r.1 = formAdj (RingHom.id K) G e.1) := by
  constructor
  · intro h
    have hv : Classical.choose (hRtrans e.1 e.2) = r.1 := congrArg Subtype.val h
    rw [← hv]
    exact (Classical.choose_spec (hRtrans e.1 e.2)).1.2
  · intro h
    apply Subtype.ext
    exact ((Classical.choose_spec (hRtrans e.1 e.2)).2 r.1 ⟨r.2, h⟩).symm

private lemma pslB3bg1b_formAdj_mul_fixed {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : {e // e ∈ P}) (he : formAdj (RingHom.id K) G e.1 = e.1) (a : pslAlg B) :
    formAdj (RingHom.id K) G (a.1 * e.1) = formAdj (RingHom.id K) G a.1 * e.1 := by
  have heA : e.1 ∈ pslAlg B := ((hP.1 e.1).1 e.2).1
  calc formAdj (RingHom.id K) G (a.1 * e.1)
      = formAdj (RingHom.id K) G e.1 * formAdj (RingHom.id K) G a.1 :=
        Geo.formAdj_mul (RingHom.id K) S.det_isUnit a.1 e.1
    _ = e.1 * formAdj (RingHom.id K) G a.1 := by rw [he]
    _ = formAdj (RingHom.id K) G a.1 * e.1 :=
        (pslB3b_comm B (formAdj (RingHom.id K) G a.1)
          (pslGraph_star_mem S a.1 a.2) e.1 heA).symm

private lemma pslB3bg1b_tau_involution {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, pslAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e // e ∈ P},
      e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P})
        (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    (e : {e // e ∈ P}) (h : pslB3b_R G P e e) :
    ι e e h * ι e e h = 1 := by
  ext y
  change ι e e h (ι e e h y) = y
  obtain ⟨a, rfl⟩ := hπ e y
  have h1 : ι e e h (π e a) =
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S a.1 a.2⟩ := (hι a e e h).symm
  have h2 : ι e e h (π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S a.1 a.2⟩) =
      π e ⟨formAdj (RingHom.id K) G
        (formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K)),
        pslGraph_star_mem S (formAdj (RingHom.id K) G a.1)
          (pslGraph_star_mem S a.1 a.2)⟩ :=
    (hι ⟨formAdj (RingHom.id K) G a.1, pslGraph_star_mem S a.1 a.2⟩ e e h).symm
  rw [h1, h2]
  have h3 : (⟨formAdj (RingHom.id K) G
        (formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K)),
        pslGraph_star_mem S (formAdj (RingHom.id K) G a.1)
          (pslGraph_star_mem S a.1 a.2)⟩ : pslAlg B) = a := by
    apply Subtype.ext
    exact pslB3b_formAdj_formAdj S a.1
  rw [h3]

private lemma pslB3bg1b_tau_ne_one {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, pslAlg B →ₐ[K] F e)
    (ι : ∀ e e' : {e // e ∈ P},
      e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P})
        (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    (hker : ∀ e (a : pslAlg B),
      π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (e : {e // e ∈ P}) (h : pslB3b_R G P e e) (hII : pslTypeII G B e.1) :
    ι e e h ≠ 1 := by
  intro hτ
  obtain ⟨a, ha, hne⟩ := hII.2
  have heA : e.1 ∈ pslAlg B := ((hP.1 e.1).1 e.2).1
  let aA : pslAlg B := ⟨a, ha⟩
  have hh : (ι e e h) (π e aA) = π e aA := by
    have h := congrArg (fun z : F e ≃+* F e => z (π e aA)) hτ
    simpa using h
  have hπeq : π e ⟨formAdj (RingHom.id K) G (aA : Matrix (Fin n) (Fin n) K),
      pslGraph_star_mem S aA.1 aA.2⟩ = π e aA := by
    rw [hι aA e e h]
    exact hh
  have hzero : π e (⟨formAdj (RingHom.id K) G (aA : Matrix (Fin n) (Fin n) K),
      pslGraph_star_mem S aA.1 aA.2⟩ - aA) = 0 := by
    rw [map_sub, hπeq, sub_self]
  have hmul : ((⟨formAdj (RingHom.id K) G (aA : Matrix (Fin n) (Fin n) K),
      pslGraph_star_mem S aA.1 aA.2⟩ - aA : pslAlg B) :
      Matrix (Fin n) (Fin n) K) * e.1 = 0 := (hker e _).mp hzero
  rw [Subalgebra.coe_sub, Matrix.sub_mul, sub_eq_zero] at hmul
  have hform : formAdj (RingHom.id K) G (a * e.1) = a * e.1 := by
    calc formAdj (RingHom.id K) G (a * e.1)
        = formAdj (RingHom.id K) G e.1 * formAdj (RingHom.id K) G a :=
          Geo.formAdj_mul (RingHom.id K) S.det_isUnit a e.1
      _ = e.1 * formAdj (RingHom.id K) G a := by rw [hII.1]
      _ = formAdj (RingHom.id K) G a * e.1 :=
          (pslB3b_comm B (formAdj (RingHom.id K) G a)
            (pslGraph_star_mem S a ha) e.1 heA).symm
      _ = a * e.1 := hmul
  exact hne hform

private lemma pslB3bg1b_units_card_eq {F : Type} [Field F] (θ : F ≃+* F) :
    Nat.card {u : F // θ u * u = 1} =
      Nat.card {t : Fˣ | θ (t : F) * (t : F) = 1} := by
  apply Nat.card_congr
  have nz : ∀ u : {u : F // θ u * u = 1}, u.1 ≠ 0 := by
    intro u h0
    have h := u.2
    rw [h0, map_zero, zero_mul] at h
    exact zero_ne_one h
  refine
    { toFun := fun u => ⟨Units.mk0 u.1 (nz u), ?_⟩
      invFun := fun t => ⟨(t.1 : F), t.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · show θ ((Units.mk0 u.1 (nz u) : Fˣ) : F) *
        ((Units.mk0 u.1 (nz u) : Fˣ) : F) = 1
    rw [Units.val_mk0]
    exact u.2
  · intro u
    apply Subtype.ext
    change (↑(Units.mk0 u.1 (nz u)) : F) = u.1
    rw [Units.val_mk0]
  · intro t
    apply Subtype.ext
    apply Units.ext
    change (↑(Units.mk0 (t.1 : F) (nz ⟨(t.1 : F), t.2⟩)) : F) = (t.1 : F)
    rw [Units.val_mk0]

private lemma pslB3bg1b_sq_eq_one_card {F : Type} [Field F] [CharP F 2] :
    Nat.card {u : F // u * u = 1} = 1 := by
  have hsub : Subsingleton {u : F // u * u = 1} :=
    ⟨fun a b => by
      apply Subtype.ext
      have ha : a.1 ^ 2 = b.1 ^ 2 := by
        rw [pow_two, pow_two, a.2, b.2]
      exact CharTwo.sq_injective ha⟩
  haveI : Nonempty {u : F // u * u = 1} := ⟨⟨1, by norm_num⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩

private lemma pslB3bg1b_iota_inv {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    {F : {e // e ∈ P} → Type} [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)]
    (π : ∀ e, pslAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (ι : ∀ e e' : {e // e ∈ P},
      e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P})
        (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    {e e' : {e // e ∈ P}} (he : e'.1 = formAdj (RingHom.id K) G e.1)
    (he' : e.1 = formAdj (RingHom.id K) G e'.1) :
    ι e' e he' = (ι e e' he).symm := by
  let f : F e' ≃+* F e := ι e e' he
  let g : F e ≃+* F e' := ι e' e he'
  have hfg : ∀ y : F e, f (g y) = y := by
    intro y
    obtain ⟨a, rfl⟩ := hπ e y
    let a' : pslAlg B := ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
      pslGraph_star_mem S a.1 a.2⟩
    have h1 : g (π e a) = π e' a' := (hι a e' e he').symm
    have h2 : f (π e' a') = π e ⟨formAdj (RingHom.id K) G (a' : Matrix (Fin n) (Fin n) K),
      pslGraph_star_mem S a'.1 a'.2⟩ := (hι a' e e' he).symm
    have h3 : (⟨formAdj (RingHom.id K) G (a' : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S a'.1 a'.2⟩ : pslAlg B) = a := by
      apply Subtype.ext
      exact pslB3b_formAdj_formAdj S (a : Matrix (Fin n) (Fin n) K)
    rw [h1, h2, h3]
  apply RingEquiv.ext
  intro x
  calc g x = f.symm (f (g x)) := (f.symm_apply_apply (g x)).symm
    _ = f.symm x := by rw [hfg x]

open Classical in
private lemma pslB3b_local_fixed {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : pslAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (pslAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    (r : {r // r ∈ R}) (hr : formAdj (RingHom.id K) G r.1 = r.1) :
    Nat.card (LocalFamilies (pslB3b_R G P) ι
        {e // pslB3b_cls G P R hRtrans e = r} (fun e => e.1)) =
      (if pslTypeII G B r.1 then Nat.card K ^ (blockDegree (pslAlg B) r.1 / 2) + 1 else 1) := by
  classical
  let ιR : {e // e ∈ P} := ⟨r.1, hRsub r.2⟩
  have hclsR : pslB3b_cls G P R hRtrans ιR = r := by
    rw [pslB3bg1b_cls_eq_iff]
    exact Or.inl rfl
  let A := {e : {e // e ∈ P} // pslB3b_cls G P R hRtrans e = r}
  let a : A := ⟨ιR, hclsR⟩
  have hsingle : ∀ x : A, x.1.1 = r.1 := by
    intro x
    have hx := (pslB3bg1b_cls_eq_iff G P R hRtrans x.1 r).mp x.2
    rcases hx with h | h
    · exact h.symm
    · have hh := congrArg (formAdj (RingHom.id K) G) h
      rw [pslB3b_formAdj_formAdj S x.1.1] at hh
      rw [hr] at hh
      exact hh.symm
  have huniq : ∀ x : A, x = a := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact hsingle x
  letI : Unique A := { default := a, uniq := huniq }
  have hRaa : pslB3b_R G P a.1 a.1 := hr.symm
  have hcount := card_localFamilies_unique (pslB3b_R G P) ι A (fun e => e.1) hRaa
  rw [hcount]
  change Nat.card {u : F (a.1) // ι (a.1) (a.1) hRaa u * u = 1} =
    (if pslTypeII G B r.1 then Nat.card K ^ (blockDegree (pslAlg B) r.1 / 2) + 1
      else 1)
  by_cases hII : pslTypeII G B r.1
  · rw [if_pos hII]
    have hτ2 : ι (a.1) (a.1) hRaa * ι (a.1) (a.1) hRaa = 1 :=
      pslB3bg1b_tau_involution S P π hπ ι hι (a.1) hRaa
    have hτ1 : ι (a.1) (a.1) hRaa ≠ 1 :=
      pslB3bg1b_tau_ne_one S P hP π ι hι hker (a.1) hRaa hII
    obtain ⟨Q, hQ, hkerQ⟩ := pslB3b_kernel_II (ι (a.1) (a.1) hRaa) hτ2 hτ1
    have hset := pslB3bg1b_units_card_eq (F := F (a.1)) (ι (a.1) (a.1) hRaa)
    rw [hset, hkerQ]
    congr 1
    refine (Nat.mul_self_inj).mp ?_
    have heven : Even (blockDegree (pslAlg B) r.1) :=
      pslB3b_typeII_even S P hP r.1 (hRsub r.2) hII
    have hpow : Nat.card K ^ (blockDegree (pslAlg B) r.1 / 2) *
        Nat.card K ^ (blockDegree (pslAlg B) r.1 / 2) =
        Nat.card K ^ blockDegree (pslAlg B) r.1 := by
      obtain ⟨k, hk⟩ := heven
      rw [hk, show (k + k) / 2 = k from by omega, ← pow_add]
    calc Q * Q = Nat.card (F (a.1)) := hQ.symm
      _ = Nat.card K ^ blockDegree (pslAlg B) (a.1).1 := hcard (a.1)
      _ = Nat.card K ^ blockDegree (pslAlg B) r.1 := rfl
      _ = Nat.card K ^ (blockDegree (pslAlg B) r.1 / 2) *
            Nat.card K ^ (blockDegree (pslAlg B) r.1 / 2) := hpow.symm
  · rw [if_neg hII]
    have hI : pslTypeI G B r.1 := by
      refine ⟨hr, ?_⟩
      intro a' ha'
      by_contra hne
      exact hII ⟨hr, a', ha', hne⟩
    have hτid : ι (a.1) (a.1) hRaa = 1 := by
      apply RingEquiv.ext
      intro y
      change ι (a.1) (a.1) hRaa y = y
      obtain ⟨a', rfl⟩ := hπ (a.1) y
      rw [← hι a' (a.1) (a.1) hRaa]
      have hzero : π (a.1)
          (⟨formAdj (RingHom.id K) G (a' : Matrix (Fin n) (Fin n) K),
            pslGraph_star_mem S a'.1 a'.2⟩ - a') = 0 := by
        rw [hker (a.1)]
        rw [Subalgebra.coe_sub, Matrix.sub_mul, sub_eq_zero]
        calc (formAdj (RingHom.id K) G (a' : Matrix (Fin n) (Fin n) K)) * (a.1).1
            = formAdj (RingHom.id K) G (a'.1 * (a.1).1) :=
              (pslB3bg1b_formAdj_mul_fixed S P hP (a.1) hr a').symm
          _ = a'.1 * (a.1).1 := hI.2 a'.1 a'.2
      have hπeq : π (a.1) ⟨formAdj (RingHom.id K) G (a' : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a'.1 a'.2⟩ = π (a.1) a' := by
        have h := hzero
        rw [map_sub] at h
        exact sub_eq_zero.mp h
      exact hπeq
    have hsub : Nat.card {u : F (a.1) // ι (a.1) (a.1) hRaa u * u = 1} =
        Nat.card {u : F (a.1) // u * u = 1} := by
      apply Nat.card_congr
      refine Equiv.subtypeEquiv (Equiv.refl _) (fun u => ?_)
      constructor
      · intro hu
        rw [hτid] at hu
        simpa using hu
      · intro hu
        rw [hτid]
        simpa using hu
    rw [hsub, pslB3bg1b_sq_eq_one_card]

private lemma pslB3b_local_pair {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (pslAlg B) e.1)
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a))
    (r : {r // r ∈ R}) (hr : formAdj (RingHom.id K) G r.1 ≠ r.1) :
    Nat.card (LocalFamilies (pslB3b_R G P) ι
        {e // pslB3b_cls G P R hRtrans e = r} (fun e => e.1)) =
      Nat.card K ^ blockDegree (pslAlg B) r.1 - 1 := by
  classical
  let A := {e : {e // e ∈ P} // pslB3b_cls G P R hRtrans e = r}
  let ιR : {e // e ∈ P} := ⟨r.1, hRsub r.2⟩
  let ιS : {e // e ∈ P} := ⟨formAdj (RingHom.id K) G r.1, hstar r.1 (hRsub r.2)⟩
  have hclsR : pslB3b_cls G P R hRtrans ιR = r := by
    rw [pslB3bg1b_cls_eq_iff]
    exact Or.inl rfl
  have hclsS : pslB3b_cls G P R hRtrans ιS = r := by
    rw [pslB3bg1b_cls_eq_iff]
    exact Or.inr (pslB3b_formAdj_formAdj S r.1).symm
  let a : A := ⟨ιR, hclsR⟩
  let b : A := ⟨ιS, hclsS⟩
  have hne : a ≠ b := by
    intro hab
    have h1 : a.1.1 = b.1.1 := congrArg Subtype.val (congrArg Subtype.val hab)
    have h2 : r.1 = formAdj (RingHom.id K) G r.1 := by
      simpa [a, b, ιR, ιS] using h1
    exact hr h2.symm
  have hcover : ∀ x : A, x = a ∨ x = b := by
    intro x
    have hx := (pslB3bg1b_cls_eq_iff G P R hRtrans x.1 r).mp x.2
    have hx' : x.1.1 = r.1 ∨ x.1.1 = formAdj (RingHom.id K) G r.1 := by
      rcases hx with h | h
      · exact Or.inl h.symm
      · right
        have hh := congrArg (formAdj (RingHom.id K) G) h
        rw [pslB3b_formAdj_formAdj S x.1.1] at hh
        exact hh.symm
    rcases hx' with h | h
    · left
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · right
      apply Subtype.ext
      apply Subtype.ext
      exact h
  have hab : pslB3b_R G P a.1 b.1 := rfl
  have hba : pslB3b_R G P b.1 a.1 := (pslB3b_formAdj_formAdj S r.1).symm
  have hinv : ∀ (x y : A) (hxy : pslB3b_R G P x.1 y.1)
      (hyx : pslB3b_R G P y.1 x.1),
      ι (y.1) (x.1) hyx = (ι (x.1) (y.1) hxy).symm :=
    fun x y hxy hyx => pslB3bg1b_iota_inv S P π hπ ι hι hxy hyx
  have hfix : ∀ x : A, ¬ pslB3b_R G P x.1 x.1 := by
    intro x hxx
    have hx := (pslB3bg1b_cls_eq_iff G P R hRtrans x.1 r).mp x.2
    rcases hx with h | h
    · apply hr
      calc formAdj (RingHom.id K) G r.1 = formAdj (RingHom.id K) G x.1.1 := by rw [h]
        _ = x.1.1 := hxx.symm
        _ = r.1 := h.symm
    · apply hr
      calc formAdj (RingHom.id K) G r.1
          = formAdj (RingHom.id K) G (formAdj (RingHom.id K) G x.1.1) := by rw [h]
        _ = x.1.1 := pslB3b_formAdj_formAdj S x.1.1
        _ = r.1 := hxx.trans h.symm
  have hpair := card_localFamilies_pair (pslB3b_R G P) ι A (fun e => e.1) a b hne hcover
    hab hba hinv hfix
  rw [hpair]
  have hFa : Nat.card (F (a.1)) = Nat.card K ^ blockDegree (pslAlg B) r.1 := by
    rw [hcard a.1]
  rw [hFa]

open Classical in
private lemma pslB3b_kernel_prod {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (F : {e // e ∈ P} → Type) [fieldF : ∀ e, Field (F e)]
    [algF : ∀ e, Algebra K (F e)] [finF : ∀ e, Finite (F e)] [charF : ∀ e, CharP (F e) 2]
    (π : ∀ e, pslAlg B →ₐ[K] F e) (hπ : ∀ e, Function.Surjective (π e))
    (hker : ∀ e (a : pslAlg B), π e a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e.1 = 0)
    (hcard : ∀ e, Nat.card (F e) = Nat.card K ^ blockDegree (pslAlg B) e.1)
    (hbij : Function.Bijective (fun (a : pslAlg B) (e : {e // e ∈ P}) => π e a))
    (ι : ∀ e e' : {e // e ∈ P}, e'.1 = formAdj (RingHom.id K) G e.1 → (F e' ≃+* F e))
    (hι : ∀ (a : pslAlg B) (e e' : {e // e ∈ P}) (he : e'.1 = formAdj (RingHom.id K) G e.1),
      π e ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a.1 a.2⟩ = ι e e' he (π e' a)) :
    Nat.card {t : (pslAlg B)ˣ |
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1} =
      ∏ r ∈ R, (if formAdj (RingHom.id K) G r = r
        then (if pslTypeII G B r then Nat.card K ^ (blockDegree (pslAlg B) r / 2) + 1 else 1)
        else Nat.card K ^ blockDegree (pslAlg B) r - 1) := by
  classical
  rw [pslB3b_card_units_eq_families S P hP F π hbij ι hι,
    card_localFamilies_prod (pslB3b_R G P) ι {e // e ∈ P} (fun x => x)
      (pslB3b_cls G P R hRtrans) (pslB3b_cls_rel S P R hRtrans)]
  rw [Finset.prod_subtype (s := R) (p := fun r => r ∈ R) (h := fun x => Iff.rfl)
    (f := fun r => if formAdj (RingHom.id K) G r = r
        then (if pslTypeII G B r then Nat.card K ^ (blockDegree (pslAlg B) r / 2) + 1 else 1)
        else Nat.card K ^ blockDegree (pslAlg B) r - 1)]
  apply Finset.prod_congr rfl
  intro r _
  by_cases hfix : formAdj (RingHom.id K) G r.1 = r.1
  · rw [if_pos hfix]
    exact pslB3b_local_fixed S P hP R hRsub hRtrans F π hπ hker hcard ι hι r hfix
  · rw [if_neg hfix]
    exact pslB3b_local_pair S P hstar R hRsub hRtrans F π hπ hcard ι hι r hfix

open Classical in
private lemma pslB3b_kernelSize_pos {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (r : Matrix (Fin n) (Fin n) K) (hr : r ∈ P) :
    0 < (if formAdj (RingHom.id K) G r = r
      then (if pslTypeII G B r then Nat.card K ^ (blockDegree (pslAlg B) r / 2) + 1 else 1)
      else Nat.card K ^ blockDegree (pslAlg B) r - 1) := by
  classical
  have hd : 1 ≤ blockDegree (pslAlg B) r := (pslB3b_block_data S P hP r hr).2.1
  haveI : Fintype K := Fintype.ofFinite K
  have hK : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  by_cases hfix : formAdj (RingHom.id K) G r = r
  · rw [if_pos hfix]
    by_cases hII : pslTypeII G B r
    · rw [if_pos hII]
      exact Nat.succ_pos _
    · rw [if_neg hII]
      norm_num
  · rw [if_neg hfix]
    have hmono : Nat.card K ^ 1 ≤ Nat.card K ^ blockDegree (pslAlg B) r :=
      Nat.pow_le_pow_right (by omega) hd
    have h2 : 2 ≤ Nat.card K ^ blockDegree (pslAlg B) r := by
      calc 2 ≤ Nat.card K := hK
        _ = Nat.card K ^ 1 := (pow_one _).symm
        _ ≤ Nat.card K ^ blockDegree (pslAlg B) r := hmono
    omega

open Classical in
private lemma pslB3b_kernel_card {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e)) :
    Nat.card {t : (pslAlg B)ˣ |
        formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
          ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) = 1} =
      ∏ r ∈ R, (if formAdj (RingHom.id K) G r = r
        then (if pslTypeII G B r then Nat.card K ^ (blockDegree (pslAlg B) r / 2) + 1 else 1)
        else Nat.card K ^ blockDegree (pslAlg B) r - 1) := by
  classical
  obtain ⟨F, fieldF, algF, finF, charF, π, hsurj, hker, hdim, hcard, hbij⟩ :=
    pslB3b_block_prod S P hP
  letI := fieldF
  letI := algF
  letI := finF
  letI := charF
  obtain ⟨ι, hι⟩ := pslB3b_star_transport S P hP F π hsurj hker
  exact pslB3b_kernel_prod S P hP hstar R hRsub hRtrans F π hsurj hker hcard hbij ι hι

private lemma pslB3b_prod_transversal {α : Type} [DecidableEq α] (P R : Finset α) (f : α → α)
    (w : α → ℕ) (hfP : ∀ e ∈ P, f e ∈ P) (hff : ∀ e ∈ P, f (f e) = e) (hRsub : R ⊆ P)
    (htrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = f e)) :
    ∏ e ∈ P, w e = ∏ r ∈ R, (if f r = r then w r else w r * w (f r)) := by
  classical
  have hinner : ∀ e ∈ P, (∏ r ∈ R, (if r = e ∨ r = f e then w e else 1)) = w e := by
    intro e he
    obtain ⟨r0, hr0, huniq⟩ := htrans e he
    have h1 : ∀ b ∈ R, b ≠ r0 → (if b = e ∨ b = f e then w e else 1) = 1 := by
      intro b hb hbr0
      have hc : ¬ (b = e ∨ b = f e) := by
        rintro (h | h)
        · exact hbr0 (huniq b ⟨hb, Or.inl h⟩)
        · exact hbr0 (huniq b ⟨hb, Or.inr h⟩)
      rw [if_neg hc]
    have h2 : r0 ∉ R → (if r0 = e ∨ r0 = f e then w e else 1) = 1 :=
      fun hnot => absurd hr0.1 hnot
    rw [Finset.prod_eq_single r0 h1 h2, if_pos hr0.2]
  calc ∏ e ∈ P, w e
      = ∏ e ∈ P, (∏ r ∈ R, (if r = e ∨ r = f e then w e else 1)) := by
        refine Finset.prod_congr rfl (fun e he => ?_)
        rw [hinner e he]
    _ = ∏ r ∈ R, (∏ e ∈ P, (if r = e ∨ r = f e then w e else 1)) :=
        Finset.prod_comm
    _ = ∏ r ∈ R, (if f r = r then w r else w r * w (f r)) := by
      refine Finset.prod_congr rfl (fun r hr => ?_)
      have hrP : r ∈ P := hRsub hr
      have hsubset : ({r, f r} : Finset α) ⊆ P := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hrP
        · exact hfP r hrP
      have hzero : ∀ x ∈ P, x ∉ ({r, f r} : Finset α) →
          (if r = x ∨ r = f x then w x else 1) = 1 := by
        intro x hx hxnot
        have h1 : r ≠ x := fun h => hxnot (by rw [← h]; exact Finset.mem_insert_self _ _)
        have h2 : r ≠ f x := by
          intro h
          apply hxnot
          have hh : f r = f (f x) := congrArg f h
          rw [hff x hx] at hh
          rw [← hh]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hc : ¬ (r = x ∨ r = f x) := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        rw [if_neg hc]
      have hswap : (∏ x ∈ ({r, f r} : Finset α),
          (if r = x ∨ r = f x then w x else 1)) =
          ∏ x ∈ P, (if r = x ∨ r = f x then w x else 1) :=
        Finset.prod_subset hsubset hzero
      rw [← hswap]
      by_cases hfr : f r = r
      · rw [hfr]
        simp
      · rw [Finset.prod_pair (a := r) (b := f r) (Ne.symm hfr), if_pos (Or.inl rfl),
          if_pos (Or.inr (hff r hrP).symm), if_neg hfr]

private lemma pslB3b_pow_two_div {q d : ℕ} (hd : Even d) :
    q ^ (d / 2) * q ^ (d / 2) = q ^ d := by
  obtain ⟨k, hk⟩ := hd
  have hdiv : (k + k) / 2 = k := by omega
  rw [hk, hdiv, ← pow_add]

open Classical in
private lemma pslB3b_prod_arith {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K))
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e))
    (hdeg : ∀ e ∈ P, blockDegree (pslAlg B) (formAdj (RingHom.id K) G e) =
      blockDegree (pslAlg B) e)
    (heven : ∀ r ∈ R, pslTypeII G B r → Even (blockDegree (pslAlg B) r)) :
    ∏ e ∈ P, (Nat.card K ^ blockDegree (pslAlg B) e - 1) =
      (∏ r ∈ R, (if formAdj (RingHom.id K) G r = r
        then (if pslTypeII G B r then Nat.card K ^ (blockDegree (pslAlg B) r / 2) + 1 else 1)
        else Nat.card K ^ blockDegree (pslAlg B) r - 1)) *
      ∏ r ∈ R, pslRho G B r := by
  have hff : ∀ e ∈ P, formAdj (RingHom.id K) G (formAdj (RingHom.id K) G e) = e := by
    have hmapid : G.map (RingHom.id K) = G := by ext a b; rfl
    have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by rw [hmapid, S.symm]
    intro e _
    exact Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit hGh e
  rw [pslB3b_prod_transversal P R (formAdj (RingHom.id K) G)
    (fun e => Nat.card K ^ blockDegree (pslAlg B) e - 1) hstar hff hRsub hRtrans]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun r hr => ?_)
  by_cases hfr : formAdj (RingHom.id K) G r = r
  · rw [if_pos hfr, if_pos hfr, pslRho]
    by_cases hII : pslTypeII G B r
    · rw [if_pos hII, if_pos hII]
      have hp : Nat.card K ^ (blockDegree (pslAlg B) r / 2) *
          Nat.card K ^ (blockDegree (pslAlg B) r / 2) =
          Nat.card K ^ blockDegree (pslAlg B) r :=
        pslB3b_pow_two_div (heven r hr hII)
      rw [← Nat.sq_sub_sq (Nat.card K ^ (blockDegree (pslAlg B) r / 2)) 1, one_pow,
        pow_two, hp]
    · rw [if_neg hII, if_neg hII, one_mul]
  · rw [if_neg hfr, if_neg hfr, hdeg r (hRsub hr), pslRho]
    have hnII : ¬ pslTypeII G B r := fun h => hfr h.1
    rw [if_neg hnII]

private lemma pslB3b_norm_card {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P)
    (R : Finset (Matrix (Fin n) (Fin n) K)) (hRsub : R ⊆ P)
    (hRtrans : ∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e)) :
    Nat.card (pslNormImage G B) = ∏ r ∈ R, pslRho G B r := by
  classical
  have h1 := pslB3b_norm_mul_kernel_card S
  have h2 := pslB3b_units_card S P hP
  have h3 := pslB3b_kernel_card S P hP hstar R hRsub hRtrans
  have hdeg : ∀ e ∈ P, blockDegree (pslAlg B) (formAdj (RingHom.id K) G e) =
      blockDegree (pslAlg B) e := fun e he => pslB3b_blockDegree_star_mem S e (hP.1 e |>.1 he).1
  have heven : ∀ r ∈ R, pslTypeII G B r → Even (blockDegree (pslAlg B) r) := fun r hr hII =>
    (pslB3b_block_data S P hP r (hRsub hr)).2.2.2 hII
  have h4 := pslB3b_prod_arith S P hstar R hRsub hRtrans hdeg heven
  have hpos : 0 < ∏ r ∈ R, (if formAdj (RingHom.id K) G r = r
        then (if pslTypeII G B r then Nat.card K ^ (blockDegree (pslAlg B) r / 2) + 1 else 1)
        else Nat.card K ^ blockDegree (pslAlg B) r - 1) :=
    Finset.prod_pos (fun r hr => pslB3b_kernelSize_pos S P hP r (hRsub hr))
  rw [h3] at h1
  rw [h2, h4] at h1
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

open Classical in
theorem pslGraph_orbit_data {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (hstar : ∀ e ∈ P, formAdj (RingHom.id K) G e ∈ P) :
    ∃ R : Finset (Matrix (Fin n) (Fin n) K), R ⊆ P ∧
      (∀ e ∈ P, ∃! r, r ∈ R ∧ (r = e ∨ r = formAdj (RingHom.id K) G e)) ∧
      Nat.card (pslNormImage G B) = ∏ r ∈ R, pslRho G B r ∧
      n = ∑ r ∈ R, (if formAdj (RingHom.id K) G r = r then 1 else 2) * Matrix.rank r ∧
      ∀ r ∈ R, blockDegree (pslAlg B) r ∣ Matrix.rank r ∧ 1 ≤ blockDegree (pslAlg B) r ∧
        0 < Matrix.rank r ∧
        (pslTypeII G B r → Even (blockDegree (pslAlg B) r)) := by
  classical
  have hff : ∀ e ∈ P, formAdj (RingHom.id K) G (formAdj (RingHom.id K) G e) = e := by
    intro e _
    have hmapid : G.map (RingHom.id K) = G := by ext a b; rfl
    have hGh : Matrix.transpose (G.map (RingHom.id K)) = G := by rw [hmapid, S.symm]
    exact Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit hGh e
  obtain ⟨R, hRsub, hRtrans⟩ :=
    pslB3b_exists_transversal P (formAdj (RingHom.id K) G) hstar hff
  exact ⟨R, hRsub, hRtrans, pslB3b_norm_card S P hP hstar R hRsub hRtrans,
    pslB3b_dim_sum S P hP hstar R hRsub hRtrans,
    fun r hr => pslB3b_block_data S P hP r (hRsub hr)⟩

end CFSG.StandardType
