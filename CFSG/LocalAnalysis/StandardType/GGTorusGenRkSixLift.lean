module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem conjN_eq_self_of_diag {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t v : Fin d → K}
    (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    conjN D hD s = s := by
  refine Subtype.ext ?_
  rw [coe_conjN]
  have hcomm : D * (s : GL (Fin d) K) = (s : GL (Fin d) K) * D := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hDt, hs]
    exact Matrix.commute_diagonal t v
  rw [hcomm]
  group

private theorem normalizerMonoidHom_apply_coe {G : Type*} [Group G] (L : Subgroup G)
    (g : Subgroup.normalizer (L : Set G)) (l : L) :
    ((L.normalizerMonoidHom g l : L) : G) = (g : G) * (l : G) * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe L g l

theorem torus_lift_mem_E_six_one
    {p : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE) (hp : p.Prime)
    (Z : Subgroup L') [Z.Normal]
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1) (hp2 : p ≠ 2)
    {φ : ↥(unitarySU 2 1 K 6) →* L' ⧸ Z}
    (hdiag : ∀ e : E, ∃ (t : Fin 6 → K) (D : GL (Fin 6) K)
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        (D : Matrix (Fin 6) (Fin 6) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K 6)) (l : L'), (QuotientGroup.mk l : L' ⧸ Z) = φ s →
          (QuotientGroup.mk (L'.normalizerMonoidHom ⟨e, hE e.2⟩ l) : L' ⧸ Z) =
            φ (conjN D hD s))
    (s : ↥(unitarySU 2 1 K 6))
    (hs : ∃ v : Fin 6 → K, ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v)
    (hsp : s ^ p = 1) (ℓ : L') (hℓ : (QuotientGroup.mk ℓ : L' ⧸ Z) = φ s)
    (hℓp : ∃ k : ℕ, orderOf ℓ = p ^ k) :
    (ℓ : M) ∈ E := by
  obtain ⟨v, hv⟩ := hs
  haveI : Fact p.Prime := ⟨hp⟩
  have hker_le_center : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact ((hZ z).1 hz).1
  have h2group : IsPGroup 2 Z := by
    intro x
    obtain ⟨k, hk⟩ := ((hZ (x : L')).1 x.2).2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hnotdvd : ¬ p ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    intro hdvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := h2group.exists_card_eq
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hcent : (ℓ : M) ∈ Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨t, D, hD, hDt, hact⟩ := hdiag ⟨e, he⟩
    set ℓ' : L' := L'.normalizerMonoidHom ⟨e, hE he⟩ ℓ with hℓ'def
    have hconj : conjN D hD s = s := conjN_eq_self_of_diag D hD hDt s hv
    have h1 := hact s ℓ hℓ
    rw [hconj] at h1
    have hπ : (QuotientGroup.mk' Z) ℓ' = (QuotientGroup.mk' Z) ℓ := by
      have hπmk : (QuotientGroup.mk ℓ' : L' ⧸ Z) = (QuotientGroup.mk ℓ : L' ⧸ Z) := by
        rw [hℓ'def]
        exact h1.trans hℓ.symm
      simpa only [QuotientGroup.coe_mk'] using hπmk
    have hℓ'p : ∃ n : ℕ, orderOf ℓ' = p ^ n := by
      rw [hℓ'def]
      obtain ⟨k, hk⟩ := hℓp
      obtain ⟨m, -, hm⟩ :=
        (Nat.dvd_prime_pow hp).1
          (hk ▸ orderOf_map_dvd ((L'.normalizerMonoidHom ⟨e, hE he⟩).toMonoidHom) ℓ)
      exact ⟨m, hm⟩
    have heq : ℓ' = ℓ :=
      CFSG.LieType.CentralExt.eq_of_pElement hker_le_center hnotdvd hπ hℓ'p hℓp
    have hcoe : ((ℓ' : L') : M) = e * (ℓ : M) * e⁻¹ :=
      normalizerMonoidHom_apply_coe L' ⟨e, hE he⟩ ℓ
    have hconjE : e * (ℓ : M) * e⁻¹ = (ℓ : M) := by
      rw [← hcoe, heq]
    calc e * (ℓ : M) = (e * (ℓ : M) * e⁻¹) * e := by group
      _ = (ℓ : M) * e := by rw [hconjE]
  have hℓpow : ℓ ^ p = 1 := by
    have hmemZ : ℓ ^ p ∈ Z := by
      have hmemker : ℓ ^ p ∈ (QuotientGroup.mk' Z).ker := by
        rw [MonoidHom.mem_ker]
        show (QuotientGroup.mk' Z) (ℓ ^ p) = 1
        rw [map_pow, QuotientGroup.coe_mk', hℓ, ← map_pow, hsp, map_one]
      rwa [QuotientGroup.ker_mk'] at hmemker
    obtain ⟨k, hk⟩ := ((hZ (ℓ ^ p)).1 hmemZ).2
    obtain ⟨j, hj⟩ := hℓp
    have hpk : (ℓ ^ p) ^ p ^ j = 1 := by
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hj]
      exact dvd_mul_left (p ^ j) p
    have hcop : Nat.Coprime (p ^ j) (2 ^ k) :=
      ((hp.coprime_iff_not_dvd).2
          (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))).pow_left j
        |>.pow_right k
    have hgcd : (ℓ ^ p) ^ (p ^ j).gcd (2 ^ k) = 1 := (pow_gcd_eq_one).2 ⟨hpk, hk⟩
    rw [hcop.gcd_eq_one, pow_one] at hgcd
    exact hgcd
  have hmem : (ℓ : M) ∈ E ⊔ L' := Subgroup.mem_sup_right ℓ.2
  have hpowM : (ℓ : M) ^ p = 1 := by
    calc (ℓ : M) ^ p = ((ℓ ^ p : L') : M) := (map_pow L'.subtype ℓ p).symm
      _ = ((1 : L') : M) := by rw [hℓpow]
      _ = 1 := map_one L'.subtype
  exact hpos.2.2.2.2.2.1 (ℓ : M) hmem hcent hpowM

end CFSG.StandardType
