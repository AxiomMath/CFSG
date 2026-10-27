module

public import CFSG.Quasithin.Recognition.St84.Sec6QQuot
public import CFSG.Quasithin.Recognition.St84.Sec4Setup
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

theorem sq_comm_mem_Q_of_le_L (j : ℤ) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPL : P ≤ X.L j) :
    (∀ x ∈ P, x ^ 2 ∈ X.Q j) ∧ ⁅P, P⁆ ≤ X.Q j := by
  have hNloc : IsLocL2 Γ G (X.vert j) (X.n j) (X.L j) := X.hyp.isLocL2_oTwoPrime (X.vert j)
  have hn1 : 1 ≤ X.n j := (X.hyp.valency (X.vert j)).1
  have hPsub : IsPGroup 2 (P.subgroupOf (X.L j)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hPimg : IsPGroup 2 ((P.subgroupOf (X.L j)).map hNloc.phi) := hPsub.map hNloc.phi
  obtain ⟨U, hUle⟩ := IsPGroup.exists_le_sylow hPimg
  have hsqU : ∀ u ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))), u ^ 2 = 1 :=
    fun u hu => psl2_sylow_sq_eq_one hn1 U hu
  have hUcomm : ∀ a ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))),
      ∀ b ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))), a * b = b * a := by
    intro a ha b hb
    have horder : ∀ u : ↥U, orderOf u ∣ 2 := by
      intro u
      refine orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext ?_)
      simpa using hsqU (u : PSL(2, GaloisField 2 (X.n j))) u.2
    have hc := Commute.of_orderOf_dvd_two horder (⟨a, ha⟩ : ↥U) (⟨b, hb⟩ : ↥U)
    exact congrArg Subtype.val hc
  constructor
  · intro x hx
    have hxL : (⟨x, hPL hx⟩ : ↥(X.L j)) ∈ P.subgroupOf (X.L j) := hx
    have hmem : hNloc.phi ⟨x, hPL hx⟩ ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))) :=
      hUle (Subgroup.mem_map_of_mem hNloc.phi hxL)
    have hsq : (hNloc.phi ⟨x, hPL hx⟩) ^ 2 = 1 := hsqU _ hmem
    have h1 : hNloc.phi ⟨x ^ 2, (X.L j).pow_mem (hPL hx) 2⟩ = 1 := by
      have hmul : (⟨x ^ 2, (X.L j).pow_mem (hPL hx) 2⟩ : ↥(X.L j)) = (⟨x, hPL hx⟩) ^ 2 := rfl
      rw [hmul, map_pow, hsq]
    exact (hNloc.phi_ker ⟨x ^ 2, (X.L j).pow_mem (hPL hx) 2⟩).mp h1
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxL : (⟨x, hPL hx⟩ : ↥(X.L j)) ∈ P.subgroupOf (X.L j) := hx
    have hyL : (⟨y, hPL hy⟩ : ↥(X.L j)) ∈ P.subgroupOf (X.L j) := hy
    have hxU : hNloc.phi ⟨x, hPL hx⟩ ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))) :=
      hUle (Subgroup.mem_map_of_mem hNloc.phi hxL)
    have hyU : hNloc.phi ⟨y, hPL hy⟩ ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))) :=
      hUle (Subgroup.mem_map_of_mem hNloc.phi hyL)
    have hxycomm : hNloc.phi ⟨x, hPL hx⟩ * hNloc.phi ⟨y, hPL hy⟩ =
        hNloc.phi ⟨y, hPL hy⟩ * hNloc.phi ⟨x, hPL hx⟩ := hUcomm _ hxU _ hyU
    have hcommP : ⁅x, y⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
    have hphi1 : hNloc.phi ⟨⁅x, y⁆, hPL hcommP⟩ = 1 := by
      have hcoe : (⟨⁅x, y⁆, hPL hcommP⟩ : ↥(X.L j)) =
          (⟨x, hPL hx⟩ : ↥(X.L j)) * ⟨y, hPL hy⟩ * (⟨x, hPL hx⟩ : ↥(X.L j))⁻¹ *
            (⟨y, hPL hy⟩ : ↥(X.L j))⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      have hmap : hNloc.phi ⟨⁅x, y⁆, hPL hcommP⟩ =
          ⁅hNloc.phi ⟨x, hPL hx⟩, hNloc.phi ⟨y, hPL hy⟩⁆ := by
        rw [hcoe, map_mul, map_mul, map_mul, map_inv, map_inv, commutatorElement_def]
      rw [hmap, commutatorElement_eq_one_iff_mul_comm.mpr hxycomm]
    exact (hNloc.phi_ker ⟨⁅x, y⁆, hPL hcommP⟩).mp hphi1

private theorem A_le_Q (i : ℤ) : X.Q (i - 1) ⊓ X.Q (i + 1) ≤ X.Q i := by
  have h := (X.shift i).Q_neg_one_inf_Q_one_le_Q_zero
  simp only [Setup.shift_Q] at h
  rwa [show (-1 : ℤ) + i = i - 1 by ring, show (1 : ℤ) + i = i + 1 by ring,
    show (0 : ℤ) + i = i by ring] at h

theorem Q_quot (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h4 : 4 ≤ s)
    (i : ℤ) :
    X.Q (i - 1) ⊓ X.Q (i + 1) ≤ X.Q i ∧
      (∀ x ∈ X.Q i, x ^ 2 ∈ X.Q (i - 1) ⊓ X.Q (i + 1)) ∧
      ⁅X.Q i, X.Q i⁆ ≤ X.Q (i - 1) ⊓ X.Q (i + 1) ∧
      (X.Q (i - 1) ⊓ X.Q (i + 1)).relIndex (X.Q i) = 2 ^ (2 * X.n (i + 1)) ∧
      (X.Q (i - 1) ⊓ X.Q (i + 1)).relIndex (X.Q i ⊓ X.Q (i + 1)) = 2 ^ X.n (i + 1) ∧
      X.Q i = (X.Q i ⊓ X.Q (i + 1)) ⊔ (X.Q i ⊓ X.Q (i - 1)) := by
  have hQi_p : IsPGroup 2 (X.Q i) := pCoreOf_isPGroup' (X.Gi i)
  have hQiLp : X.Q i ≤ X.L (i + 1) :=
    le_oTwoPrime_of_isPGroup hQi_p ((X.Q_le_Gi_adj i).trans inf_le_right)
  have hQiLm : X.Q i ≤ X.L (i - 1) :=
    le_oTwoPrime_of_isPGroup hQi_p ((X.Q_le_Gi_adj i).trans inf_le_left)
  have hLp := sq_comm_mem_Q_of_le_L X (i + 1) hQi_p hQiLp
  have hLm := sq_comm_mem_Q_of_le_L X (i - 1) hQi_p hQiLm
  have hsq : ∀ x ∈ X.Q i, x ^ 2 ∈ X.Q (i - 1) ⊓ X.Q (i + 1) :=
    fun x hx => ⟨hLm.1 x hx, hLp.1 x hx⟩
  have hcomm : ⁅X.Q i, X.Q i⁆ ≤ X.Q (i - 1) ⊓ X.Q (i + 1) := le_inf hLm.2 hLp.2
  have hgen := Q_quot_of_normal_general (X.shift i) hc hs h4
  simp only [Setup.shift_Q, Setup.shift_n] at hgen
  rw [show (-1 : ℤ) + i = i - 1 by ring, show (1 : ℤ) + i = i + 1 by ring,
    show (0 : ℤ) + i = i by ring] at hgen
  exact ⟨A_le_Q X i, hsq, hcomm, hgen.2.1, hgen.2.2.1, hgen.1⟩

theorem Q_quot_comm (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s)
    (h4 : 4 ≤ s) (i : ℤ) :
    ¬ ⁅X.Q i ⊓ X.Q (i - 1), X.Q (i + 1)⁆ ≤ X.Q (i - 1) ⊓ X.Q (i + 1) ∧
      X.Q i ⊓ X.Q (i + 1) =
        ⁅X.Q i ⊓ X.Q (i - 1), X.Q (i + 1)⁆ ⊔ (X.Q (i - 1) ⊓ X.Q (i + 1)) := by
  have hgen := Q_quot_of_normal_general (X.shift i) hc hs h4
  simp only [Setup.shift_Q, Setup.shift_n] at hgen
  rw [show (-1 : ℤ) + i = i - 1 by ring, show (1 : ℤ) + i = i + 1 by ring,
    show (0 : ℤ) + i = i by ring] at hgen
  have hquot := Q_quot X hc hs h4 i
  have hA_le_V1 : X.Q (i - 1) ⊓ X.Q (i + 1) ≤ X.Q i ⊓ X.Q (i + 1) :=
    le_inf hquot.1 inf_le_right
  have hne_bot : ¬ ⁅X.Q i ⊓ X.Q (i - 1), X.Q (i + 1)⁆ ≤ X.Q (i - 1) ⊓ X.Q (i + 1) := by
    intro hle
    have hV1le : X.Q i ⊓ X.Q (i + 1) ≤ X.Q (i - 1) ⊓ X.Q (i + 1) :=
      hgen.2.2.2.2.trans (sup_le hle le_rfl)
    have heq : X.Q i ⊓ X.Q (i + 1) = X.Q (i - 1) ⊓ X.Q (i + 1) :=
      le_antisymm hV1le hA_le_V1
    have hone : (X.Q (i - 1) ⊓ X.Q (i + 1)).relIndex (X.Q i ⊓ X.Q (i + 1)) = 1 := by
      rw [heq, Subgroup.relIndex_self]
    rw [hquot.2.2.2.2.1] at hone
    have hpos : 0 < X.n (i + 1) := (X.hyp.valency (X.vert (i + 1))).1
    exact (Nat.one_lt_two_pow (by omega : X.n (i + 1) ≠ 0)).ne' hone
  have hcomm_le : ⁅X.Q i ⊓ X.Q (i - 1), X.Q (i + 1)⁆ ≤ X.Q i ⊓ X.Q (i + 1) := by
    have h1 : ⁅X.Q i, X.Q (i + 1)⁆ ≤ X.Q i := by
      have hN : X.Q (i + 1) ≤ Subgroup.normalizer (X.Q i : Set G) := by
        have hG : X.Q (i + 1) ≤ X.Gi i := by
          have h := (X.Q_le_Gi_adj (i + 1)).trans inf_le_left
          simpa using h
        exact hG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi i))
      exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hN
    have h2 : ⁅X.Q i, X.Q (i + 1)⁆ ≤ X.Q (i + 1) := by
      have hN : X.Q i ≤ Subgroup.normalizer (X.Q (i + 1) : Set G) :=
        ((X.Q_le_Gi_adj i).trans inf_le_right).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi (i + 1)))
      have h := (Subgroup.le_normalizer_iff_commutator_le_left).mp hN
      simpa [Subgroup.commutator_comm] using h
    have hcomm : ⁅X.Q i, X.Q (i + 1)⁆ ≤ X.Q i ⊓ X.Q (i + 1) := le_inf h1 h2
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans hcomm
  exact ⟨hne_bot,
    le_antisymm hgen.2.2.2.2 (sup_le hcomm_le hA_le_V1)⟩

theorem isElemAbelian_Z_of_natQuot (i : ℤ) {n : ℕ}
    (hZ : NatQuot (X.L i) (X.Z i) ⊥ n) : IsElemAbelian 2 (X.Z i) := by
  by_cases hZbot : X.Z i = ⊥
  · rw [hZbot]
    exact CFSG.Open.isElemAbelian_bot 2
  have hZcard : Nat.card (X.Z i) = 2 ^ (2 * n) := by
    simpa using hZ.index
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hZGi : X.Z i ≤ X.Gi i := hZ.E_le.trans (X.L_le_Gi i)
  haveI : Finite ↥(X.Z i) :=
    Finite.of_injective (Subgroup.inclusion hZGi) (Subgroup.inclusion_injective hZGi)
  have hZ2 : IsPGroup 2 (X.Z i) := IsPGroup.of_card (n := 2 * n) hZcard
  haveI : Fact (IsPGroup 2 ↥(X.Z i)) := ⟨hZ2⟩
  let P : Subgroup G := (frattini ↥(X.Z i)).map (X.Z i).subtype
  have hPle : P ≤ X.Z i := Subgroup.map_subtype_le _
  have hLN : X.L i ≤ Subgroup.normalizer (X.Z i : Set G) := fun x hx => (hZ.normal hx).1
  have hPN : X.L i ≤ Subgroup.normalizer (P : Set G) :=
    hLN.trans
      (CFSG.BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        (X.Z i) (frattini ↥(X.Z i)))
  have hP : P = ⊥ ∨ P = X.Z i := hZ.irred P bot_le hPle hPN
  have hfr_bot : frattini ↥(X.Z i) = ⊥ := by
    rcases hP with hb | ht
    · have hb' : Subgroup.map (X.Z i).subtype (frattini ↥(X.Z i)) = ⊥ := by
        simpa [P] using hb
      exact Subgroup.map_injective (X.Z i).subtype_injective (by
        rw [hb', Subgroup.map_bot])
    · exfalso
      have htop : frattini ↥(X.Z i) = ⊤ := by
        apply Subgroup.map_injective (X.Z i).subtype_injective
        have ht' : Subgroup.map (X.Z i).subtype (frattini ↥(X.Z i)) = X.Z i := by
          simpa [P] using ht
        rw [ht']
        exact (show Subgroup.map (X.Z i).subtype (⊤ : Subgroup ↥(X.Z i)) = X.Z i from by
          simpa using Subgroup.subgroupOf_map_subtype (H := (⊤ : Subgroup G)) (K := X.Z i)).symm
      haveI : Finite (Subgroup ↥(X.Z i)) := by infer_instance
      haveI : Nontrivial ↥(X.Z i) := (Subgroup.nontrivial_iff_ne_bot (X.Z i)).mpr hZbot
      have hgen : (⊥ : Subgroup ↥(X.Z i)) ⊔ frattini ↥(X.Z i) = ⊤ := by
        rw [htop, sup_top_eq]
      exact (bot_ne_top : (⊥ : Subgroup ↥(X.Z i)) ≠ ⊤) (frattini_nongenerating hgen)
  haveI hElem : CFSG.IsElementaryAbelian 2 ↥(X.Z i) :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥(X.Z i)) (p := 2)).mp hfr_bot
  exact ⟨inferInstance, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩

end Setup

end CFSG.Quasithin.St84
