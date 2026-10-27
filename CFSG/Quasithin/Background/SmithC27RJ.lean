module

public import CFSG.Quasithin.Background.SmithC27RRad
public import CFSG.Quasithin.Background.SmithC27RDefs
public import CFSG.Quasithin.Background.SmithC27Two

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem thompsonJ_le_D_sup_Q (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V) :
    thompsonJ R ≤ (R ⊓ K) ⊔ pCoreOf 2 (K ⊔ R) := by
  have hJD : autOn (thompsonJ R) V ≤ autOn (R ⊓ K) V := by
    rw [← hs.autOn_inf_R]
    exact le_inf (autOn_mono' (thompsonJ_le_self R)) hJ
  intro x hx
  have hxR : x ∈ R := thompsonJ_le_self R hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hs.R_le_normalizer_V hxR
  obtain ⟨n, hnD, hne⟩ := mem_autOn_iff'.1 (hJD (mem_autOn_iff'.2 ⟨⟨x, hxN⟩, hx, rfl⟩))
  have hc : (n : G)⁻¹ * x ∈ pCoreOf 2 (K ⊔ R) := by
    rw [hs.pCore_eq_inf]
    refine ⟨R.mul_mem (R.inv_mem hnD.1) hxR, ?_⟩
    have h1 : conjAct V (n⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hne, inv_mul_cancel]
    exact (conjAct_eq_one_iff' _).1 h1
  have e : x = (n : G) * ((n : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnD) (Subgroup.mem_sup_right hc)

theorem inf_normalizer_D_le_M (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) :
    K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₁ : Subgroup G := (R ⊓ K) ⊔ pCoreOf 2 (K ⊔ R) with hP₁
  have hP₁R : P₁ ≤ R := sup_le inf_le_left hs.core
  have hJP : thompsonJ R = thompsonJ P₁ := thompsonJ_eq_of_le (thompsonJ_le_D_sup_Q hs hJ) hP₁R
  have hnP : K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer (P₁ : Set G) := by
    rintro k ⟨hkK, hkD⟩
    have hkQ : k ∈ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
      le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hkK)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hP₁, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hkD, Subgroup.mem_normalizer_iff_map_conj_eq.1 hkQ]
  refine le_trans ?_ (sup_inf_normalizer_thompsonJ_le h)
  refine le_inf (inf_le_left.trans le_sup_left) ?_
  rw [hJP]
  exact hnP.trans (normalizer_le_normalizer_thompsonJ P₁)

theorem autOn_D_ne_bot (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) : autOn (R ⊓ K) V ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  apply h.not_le
  have hDN : R ⊓ K ≤ Subgroup.normalizer (V : Set G) := inf_le_right.trans hs.K_le_normalizer_V
  have hDC : R ⊓ K ≤ Subgroup.centralizer (V : Set G) :=
    (autI_eq_bot_iff hs.elemAbelian hDN).1 hbot
  have hD : R ⊓ K = pCoreOf 2 K := by
    rw [← pCore_K_eq_inf hs]
    exact (inf_eq_left.2 hDC).symm
  have hKN : K ≤ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) := by
    rw [hD]
    exact le_normalizer_pCoreOf 2 K
  exact (le_inf le_rfl hKN).trans (inf_normalizer_D_le_M h hs hJ)

theorem isSylowTwoOf_R_of_sylow_le (hs : StarHyp R K V) {S : Subgroup (MulAut ↥V)}
    (hS : IsSylowTwoOf S (autOn K V)) (hSR : S ≤ autOn R V) : IsSylowTwoOf R (K ⊔ R) := by
  rw [hs.isSylowTwoOf_iff]
  have hRX : autOn R V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_right
  have hRN : autOn R V ≤ Subgroup.normalizer (autOn K V : Set (MulAut ↥V)) :=
    hRX.trans hs.normalizes
  have hprod := card_sup_mul_card_inf_of_le_normalizer' hRN
  rw [← hs.autOn_sup] at hprod
  have hSKR : S ≤ autOn K V ⊓ autOn R V := le_inf hS.1 hSR
  have i1 := card_eq_index_mul' hRX
  have i2 := card_eq_index_mul' (inf_le_left : autOn K V ⊓ autOn R V ≤ autOn K V)
  have hpos1 : 0 < Nat.card ↥(autOn R V) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(autOn K V ⊓ autOn R V) := Nat.card_pos
  have key : ((autOn R V).subgroupOf (autOn (K ⊔ R) V)).index =
      ((autOn K V ⊓ autOn R V).subgroupOf (autOn K V)).index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos1 hpos2)
    calc ((autOn R V).subgroupOf (autOn (K ⊔ R) V)).index *
          (Nat.card ↥(autOn R V) * Nat.card ↥(autOn K V ⊓ autOn R V))
        = Nat.card ↥(autOn (K ⊔ R) V) * Nat.card ↥(autOn K V ⊓ autOn R V) := by rw [i1]; ring
      _ = Nat.card ↥(autOn K V) * Nat.card ↥(autOn R V) := hprod
      _ = ((autOn K V ⊓ autOn R V).subgroupOf (autOn K V)).index *
          (Nat.card ↥(autOn R V) * Nat.card ↥(autOn K V ⊓ autOn R V)) := by rw [i2]; ring
  refine ⟨hRX, isPGroup_autOn hs.pgroup, fun h2 => ?_⟩
  rw [key] at h2
  exact hS.2.2 (h2.trans (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono _ hSKR)))

theorem parabolic_MK (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hBT : IsRadicalParabolic (autOn K V)) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) :
    IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ ¬ IsBorelIn (autOn K V) (autOn (M ⊓ K) V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDK : autOn (R ⊓ K) V ≤ autOn K V := autOn_mono' inf_le_right
  obtain ⟨-, S, hS, hN⟩ := hBT (autOn (R ⊓ K) V) hDK (autOn_D_ne_bot h hs hJ)
    (isPGroup_autOn (h.isPGroup.to_le inf_le_left)) (pCore_autOn_inf_normalizer_D h hs)
  have hle : autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V)) ≤
      autOn (M ⊓ K) V := by
    rw [← autOn_inf_normalizer_D hs]
    exact autOn_mono' (le_inf (inf_normalizer_D_le_M h hs hJ) inf_le_left)
  refine ⟨⟨autOn_mono' inf_le_right, S, hS, hN.trans hle⟩, ?_⟩
  rintro ⟨S', hS', hB⟩
  apply hnS
  refine isSylowTwoOf_R_of_sylow_le hs hS' ?_
  have h1 : S' ≤ pCoreOf 2 (autOn (M ⊓ K) V) := by
    rw [hB]
    exact le_pCoreOf_of_le_normalizer 2 (le_inf hS'.1 Subgroup.le_normalizer) inf_le_right
      hS'.2.1
  exact h1.trans (pCore_MK_star_le_R_star h hs)

end CFSG.Quasithin.SmithC27
