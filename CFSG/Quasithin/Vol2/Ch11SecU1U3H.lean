module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3G
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IP

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.Quasithin.E1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {p : ℕ} [Fact p.Prime] {F : Type}
  [Field F] [Finite F]


theorem inner_nParam (hp7 : 7 ≤ p) (hp4 : p % 4 = 1) (hF : Nat.card F = p ^ 2)
    (hAS : SecE3.AlmostSimple L) (ψ : PSU3F p F ≃* ↥L) :
    ∀ x ∈ L, orderOf x = 2 → nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
  intro x hxL hx2
  obtain ⟨Y, -, hYC, hYn, ⟨e⟩, hCs, -⟩ :=
    exists_levi_data_U3 (by omega) hp4 hF hAS.normal ψ hxL hx2
  exact L3I.nParam_centralizer_le_one_of_sl2 hAS hp7 hYC hYn e hCs

theorem inner_torus (hp5 : 5 ≤ p) (hp4 : p % 4 = 1) (hF : Nat.card F = p ^ 2) (hLn : L.Normal)
    (ψ : PSU3F p F ≃* ↥L) :
    ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
      ∀ Q : Subgroup G, IsPGroup 2 Q →
        Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) →
        ∃ P : Subgroup G, (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
          Q ≤ Subgroup.normalizer (P : Set G) ∧ ¬ P ≤ Subgroup.centralizer ({x} : Set G) := by
  intro x hxL y hyL hx2 hy2 hxy hc Q hQ hQC
  obtain ⟨Y, hYL, hYC, hYn, ⟨e⟩, -, hxY⟩ := exists_levi_data_U3 hp5 hp4 hF hLn ψ hyL hy2
  exact L3I.inner_torus_of_sl2 hp5 hYL hYC hYn e hxL hx2 hc (hxY x hxL hx2 hc hxy) hQ hQC

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
