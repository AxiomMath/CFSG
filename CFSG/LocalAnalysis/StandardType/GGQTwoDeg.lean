module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegMLeN
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegCartan
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegLast
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegSpan
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegRM
public import CFSG.LocalAnalysis.StandardType.GGQTwoDegFalse

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwoDeg_eq_N_of_dim_pred
    {Bs L : Subgroup G} {x : G} {k : QTwoRowKind} {m d c : ℕ}
    (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {N : ℕ} (hmN : m ≤ N)
    (hbound : N - 1 - (if 3 ∣ N then 1 else 0) ≤ d) (hd : d = m - 1) : N = m := by
  have hk : k ≠ .prime := by
    intro hk
    have hm_eq : d = m := (hrow.dc.1 hk).1
    omega
  have h3m : 3 ∣ m := hrow.dvd hk
  by_cases h3N : 3 ∣ N
  · rw [if_pos h3N] at hbound
    have hNle : N ≤ m + 1 := by omega
    have hsplit : N = m ∨ N = m + 1 := by omega
    rcases hsplit with h | h
    · exact h
    · exfalso
      subst h
      have hsub := Nat.dvd_sub h3N h3m
      have h31 : 3 ∣ 1 := by simpa using hsub
      exact absurd h31 (by norm_num)
  · rw [if_neg h3N] at hbound
    omega

theorem qTwoDeg_window
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hCartan : 3 ^ (N - 1 - (if 3 ∣ N then 1 else 0)) ≤ Nat.card Bs) :
    m ≤ N ∧ N ≤ m + 2 ∧ (N = m + 2 → 3 ∣ N) := by
  have hmN : m ≤ N := qTwoDeg_m_le_N hcfg hrow hm hP hN hM
  have hbound : N - 1 - (if 3 ∣ N then 1 else 0) ≤ d :=
    qTwoDeg_cartan_bound_le hrow hCartan
  have hdm : d ≤ m := by
    rcases k with _ | _ | _ | _ | _
    · exact le_of_eq (hrow.dc.1 rfl).1
    · exact le_of_eq (hrow.dc.2.1 rfl).1
    · have h := (hrow.dc.2.2.1 rfl).1
      omega
    · have h := (hrow.dc.2.2.2.1 rfl).1
      omega
    · exact le_of_eq (hrow.dc.2.2.2.2 rfl).1
  refine ⟨hmN, ?_, ?_⟩
  · by_cases h3 : 3 ∣ N
    · rw [if_pos h3] at hbound
      omega
    · rw [if_neg h3] at hbound
      omega
  · intro hNm2
    by_contra h3
    rw [if_neg h3] at hbound
    omega

theorem qTwoDeg_weylAt_of_spanning
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (hspan : ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} {e' : Fin (N - 1) ≃ ι} (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hNm : N = m + 1) :
    GGSecFiveWeylAt 3 B Bs x L D J (CoxeterMatrix.A m) := by
  obtain ⟨y, K, hnbr, hA⟩ := hspan
  have h1 : GGSecFiveWeylAt 3 B Bs x L D J M :=
    ggSecFiveWeylAt_of_join_eq hnbr hA e hP
  rw [hM] at h1
  have h2 : GGSecFiveWeylAt 3 B Bs x L D J (CoxeterMatrix.A (N - 1)) :=
    GGSecFiveWeylAt.of_reindex (M := CoxeterMatrix.A (N - 1)) (e := e') h1
  rw [hNm] at h2
  simpa using h2

theorem qTwoDeg_odd_center_of_q2PrimeL
    (hQ2 : GGSecFiveQ2PrimeLInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {d c : ℕ} (hrow : QTwoRowData k 6 d c Bs L x) (hd : d = 6)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {e' : Fin (7 - 1) ≃ ι} (hM : M = (CoxeterMatrix.A (7 - 1)).reindex e')
    (hLie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  have hspan : ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 :=
    qTwoDeg_exists_spanning_neighbour (N := 7) hcfg hrow (by norm_num) hP
      (by norm_num) hM (by norm_num)
  have hcard : Nat.card Bs = 3 ^ 6 := by rw [hrow.card, hd]
  have hWeylAt : GGSecFiveWeylAt 3 B Bs x L D J (CoxeterMatrix.A 6) :=
    qTwoDeg_weylAt_of_spanning (m := 6) (N := 7) hspan hP hM (by norm_num)
  have hWeylL : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) := by
    simpa using hrow.weyl
  exact hQ2 G B Bs x L D J 𝒦 hcfg hcard hLie hWeylAt hWeylL

theorem qTwo_proper_model_of_row
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {k : QTwoRowKind} {m d c : ℕ} (hrow : QTwoRowData k m d c Bs L x) (hm : 5 ≤ m)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    {N : ℕ} (hN : 6 ≤ N) {e' : Fin (N - 1) ≃ ι}
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e')
    (hCart : GGCartanRankLe)
    (hgn : ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
      K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
          n ∈ Subgroup.normalizer (Bs : Set G) ∧
            ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
        J.map (MulAut.conj n).toMonoidHom) :
    (N = m + 1 ∨ (N = m + 2 ∧ 3 ∣ N)) ∧ (k = .prime ∨ k = .suFull) := by
  have hCartan : 3 ^ (N - 1 - (if 3 ∣ N then 1 else 0)) ≤ Nat.card Bs :=
    qTwoDeg_cartan_of_pres hCart hcfg hP hN hM
  obtain ⟨hmN, hNle, hNm2⟩ := qTwoDeg_window hcfg hrow hm hP hN hM hCartan
  have hbound : N - 1 - (if 3 ∣ N then 1 else 0) ≤ d :=
    qTwoDeg_cartan_bound_le hrow hCartan
  have hNm_false : N = m → False := by
    intro hNm
    exact qTwoDeg_false_of_equal_degree hcfg hrow hm hP hN hM hNm
      (qTwoDeg_rm_of_equal_degree hcfg hrow hm hP hN hM hNm) hgn
  have hNconcl : N = m + 1 ∨ (N = m + 2 ∧ 3 ∣ N) := by
    have hsplit : N = m ∨ N = m + 1 ∨ N = m + 2 := by omega
    rcases hsplit with h | h | h
    · exact absurd h hNm_false
    · exact Or.inl h
    · exact Or.inr ⟨h, hNm2 h⟩
  rcases k with _ | _ | _ | _ | _
  · exact ⟨hNconcl, Or.inl rfl⟩
  · exact ⟨hNconcl, Or.inr rfl⟩
  · have hd : d = m - 1 := (hrow.dc.2.2.1 rfl).1
    exact False.elim (hNm_false (qTwoDeg_eq_N_of_dim_pred hrow hm hmN hbound hd))
  · have hd : d = m - 1 := (hrow.dc.2.2.2.1 rfl).1
    exact False.elim (hNm_false (qTwoDeg_eq_N_of_dim_pred hrow hm hmN hbound hd))
  · have hc : c = m - 2 := (hrow.dc.2.2.2.2 rfl).2
    exfalso
    have hsplit : N = m ∨ N = m + 1 ∨ N = m + 2 := by omega
    rcases hsplit with h | h | h
    · exact hNm_false h
    · exact qTwoDeg_not_span_of_last_row hcfg hrow rfl hP hN hM h
    · have h3N : 3 ∣ N := hNm2 h
      have h3m : 3 ∣ m := hrow.dvd (by decide)
      rw [h] at h3N
      have h32 : 3 ∣ 2 := by
        have hsub := Nat.dvd_sub h3N h3m
        simpa using hsub
      exact absurd h32 (by norm_num)

end CFSG.StandardType.QTwo

end
