module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Def

public section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model


abbrev a7 : Fin e7Data.d := ⟨0, by decide⟩

private def fin_NW (a b : Fin e7Data.d) : Prop :=
  ∀ k : Fin 126, pr a ((Tag.rootCertificate .E7).root k) = 1 →
    pr b ((Tag.rootCertificate .E7).root k) = -1 →
      e7Data.wt a = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k)

private instance fin_decNW (a b : Fin e7Data.d) : Decidable (fin_NW a b) := by
  unfold fin_NW; infer_instance

private theorem fin_NW_iff (a b : Fin e7Data.d) : NearW a b ↔ fin_NW a b :=
  nearW_iff a b

theorem phi7_card : ((rootFinset .E7).filter fun γ => pr a7 γ = 1).card = 27 := by
  decide +kernel

private theorem fin_key_unique : ∀ b : Fin e7Data.d, ¬ fin_NW a7 b → e7Data.wt b ≠ -e7Data.wt a7 →
    ∀ k k' : Fin 126, pr a7 ((Tag.rootCertificate .E7).root k) = 1 →
      pr b ((Tag.rootCertificate .E7).root k) = 1 →
      pr a7 ((Tag.rootCertificate .E7).root k') = 1 →
      pr b ((Tag.rootCertificate .E7).root k') = 1 →
      (Tag.rootCertificate .E7).root k = (Tag.rootCertificate .E7).root k' := by
  decide +kernel

theorem spec_unique (b : Fin e7Data.d) (hb : SpecW a7 b) (γ γ' : Fin (Tag.rank .E7) → ℤ)
    (hγ : IsRoot .E7 γ) (hγ' : IsRoot .E7 γ') (h1 : pr a7 γ = 1) (h2 : pr b γ = 1)
    (h3 : pr a7 γ' = 1) (h4 : pr b γ' = 1) : γ = γ' := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hb' : ¬ NearW a7 b ∧ b ≠ opp a7 := hb
  have hwt : e7Data.wt b ≠ -e7Data.wt a7 := fun h => hb'.2 (opp_eq h).symm
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
  obtain ⟨k', hk', rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ'
  exact fin_key_unique b (fun h => hb'.1 ((fin_NW_iff a7 b).2 h)) hwt ⟨k, by omega⟩ ⟨k', by omega⟩
    h1 h2 h3 h4

private def fin_t1 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 2,
    3, 2, 3, 3, 4, 4, 5, 5, 6, 7, 10, 12, 15, 0]

private def fin_t2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 15, 0, 0, 17, 0, 0, 20, 0, 0, 23,
    0, 25, 26, 0, 28, 26, 0, 31, 28, 0, 34, 31, 37, 34,
    31, 37, 34, 37, 34, 37, 34, 37, 37, 37, 37, 37, 37, 0]

private def fin_c1 (b : Fin e7Data.d) : Fin e7Data.d :=
  ⟨fin_t1.getD b.val 0 % e7Data.d, Nat.mod_lt _ (by decide)⟩

private def fin_c2 (b : Fin e7Data.d) : Fin e7Data.d :=
  ⟨fin_t2.getD b.val 0 % e7Data.d, Nat.mod_lt _ (by decide)⟩

private theorem fin_key_witness : ∀ b : Fin e7Data.d, ¬ fin_NW a7 b →
    e7Data.wt b ≠ -e7Data.wt a7 →
      fin_NW a7 (fin_c1 b) ∧ fin_NW a7 (fin_c2 b) ∧ fin_NW b (fin_c1 b) ∧ fin_NW b (fin_c2 b) ∧
        ¬ fin_NW (fin_c1 b) (fin_c2 b) ∧ e7Data.wt (fin_c2 b) ≠ -e7Data.wt (fin_c1 b) := by
  decide +kernel

theorem spec_witness (b : Fin e7Data.d) (hb : SpecW a7 b) :
    ∃ c₁ c₂ : Fin e7Data.d, NearW a7 c₁ ∧ NearW a7 c₂ ∧ NearW b c₁ ∧ NearW b c₂ ∧
      ¬ NearW c₁ c₂ ∧ c₂ ≠ opp c₁ := by
  have hb' : ¬ NearW a7 b ∧ b ≠ opp a7 := hb
  have hwt : e7Data.wt b ≠ -e7Data.wt a7 := fun h => hb'.2 (opp_eq h).symm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    fin_key_witness b (fun h => hb'.1 ((fin_NW_iff a7 b).2 h)) hwt
  refine ⟨fin_c1 b, fin_c2 b, (fin_NW_iff _ _).2 h1, (fin_NW_iff _ _).2 h2,
    (fin_NW_iff _ _).2 h3, (fin_NW_iff _ _).2 h4, fun h => h5 ((fin_NW_iff _ _).1 h), ?_⟩
  intro h
  apply h6
  rw [h, wt_opp]

end CFSG.RankThree.GF2n.Smith81.E7X
