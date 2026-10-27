module

public import CFSG.Quasithin.Background.Harris.R1.J2VertHom
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Model
public import Certificates.Certificate300205

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.CosetTable CFSG.LargeExtraspecial.S63 CFSG.Quasithin.D4Hex
  CFSG.Quasithin.Background.Harris.R1.J2Vert

theorem d4GenG_mul_self {k : ℕ} (hk : k < 8) :
    d4GenG k * d4GenG k = 1 := by
  have h := Certificates.certificate300205.1
  simp only [gensInvolOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h2 := repE_mul (repE_d4Gens hk) (repE_d4Gens hk)
  rw [h k hk] at h2
  exact eq_of_repE d4E_injective h2 repE_one

theorem d4Word_append (u v : List ℕ) : d4Word (u ++ v) = d4Word u * d4Word v := by
  simp [d4Word]

theorem d4Word_reverse {w : List ℕ} (hw : ∀ k ∈ w, k < 8) :
    (d4Word w)⁻¹ = d4Word w.reverse := by
  induction w with
  | nil => simp [d4Word]
  | cons k w ih =>
    have hk := hw k List.mem_cons_self
    have ih := ih fun k' hk' => hw k' (List.mem_cons_of_mem k hk')
    have hk2 : (d4GenG k)⁻¹ = d4GenG k := inv_eq_of_mul_eq_one_right (d4GenG_mul_self hk)
    have hc : d4Word (k :: w) = d4GenG k * d4Word w := by simp [d4Word]
    rw [hc, mul_inv_rev, ih, hk2, List.reverse_cons, d4Word_append]
    simp [d4Word]

theorem substWord_cons {m : ℕ} (W : List (List ℕ)) (p : Fin m × Bool) (r : List (Fin m × Bool)) :
    substWord W (p :: r) = (if p.2 then W.getD p.1 [] else (W.getD p.1 []).reverse) ++
      substWord W r := by
  simp [substWord]

theorem eval_eq_d4Word {m : ℕ} {W : List (List ℕ)}
    (hW : ∀ i : Fin m, ∀ k ∈ W.getD i.val [], k < 8) (r : List (Fin m × Bool)) :
    (r.map fun p => if p.2 then d4Word (W.getD p.1.val []) else
      (d4Word (W.getD p.1.val []))⁻¹).prod = d4Word (substWord W r) := by
  induction r with
  | nil => simp [d4Word, substWord]
  | cons p r ih =>
    rw [List.map_cons, List.prod_cons, ih, substWord_cons, d4Word_append]
    congr 1
    obtain ⟨i, s⟩ := p
    cases s
    · exact d4Word_reverse (hW i)
    · rfl

theorem relsHold_spec {m : ℕ} {W : List (List ℕ)}
    {rels : List (List (Fin m × Bool))} (hW : ∀ i : Fin m, ∀ k ∈ W.getD i.val [], k < 8)
    (h : relsHold W rels = true) :
    ∀ r ∈ rels, (r.map fun p => if p.2 then d4Word (W.getD p.1.val []) else
      (d4Word (W.getD p.1.val []))⁻¹).prod = 1 := by
  intro r hr
  rw [eval_eq_d4Word hW]
  simp only [relsHold, List.all_eq_true, beq_iff_eq] at h
  have hs : ∀ k ∈ substWord W r, k < 8 := by
    intro k hk
    simp only [substWord, List.mem_flatMap] at hk
    obtain ⟨⟨i, s⟩, -, hk⟩ := hk
    cases s
    · simpa using hW i k (by simpa using hk)
    · exact hW i k (by simpa using hk)
  have hrep := repE_d4Word hs
  rw [h r hr] at hrep
  exact eq_of_repE d4E_injective hrep repE_one

theorem hWords_lt : ∀ i : Fin 4, ∀ k ∈ hWords.getD i.val [], k < 8 := by decide

theorem nWords_lt : ∀ i : Fin 5, ∀ k ∈ nWords.getD i.val [], k < 8 := by decide

@[expose] noncomputable def hModel : PG 4 hRels →* D :=
  pgHom (g := fun i : Fin 4 => d4Word (hWords.getD i.val []))
    (relsHold_spec hWords_lt Certificates.certificate300205.2.1)

theorem hModel_of (i : Fin 4) :
    hModel (PresentedGroup.of i) = d4Word (hWords.getD i.val []) :=
  pgHom_of _ i

@[expose] noncomputable def nModel : PG 5 nRels →* D :=
  pgHom (g := fun i : Fin 5 => d4Word (nWords.getD i.val []))
    (relsHold_spec nWords_lt Certificates.certificate300205.2.2)

theorem nModel_of (i : Fin 5) :
    nModel (PresentedGroup.of i) = d4Word (nWords.getD i.val []) :=
  pgHom_of _ i

end CFSG.Quasithin.Background.Harris.R1.D4Vert
