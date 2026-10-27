module

public import CFSG.Quasithin.EmptyFaithful.ModHM23a
public import CFSG.Quasithin.EmptyFaithful.ModHM23b
public import CFSG.Quasithin.EmptyFaithful.ModHOut3
public import CFSG.Quasithin.EmptyFaithful.ModHOut4
public import CFSG.Quasithin.EmptyFaithful.ModHRho
public import CFSG.Quasithin.EmptyFaithful.ModHInn
public import CFSG.Quasithin.EmptyFaithful.ModHSolv
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2204
public import Certificates.Certificate4075
public import Certificates.Certificate7118
public import Certificates.Certificate7123

public section

namespace CFSG.Quasithin.ModH.M23c

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.M23b CFSG.Quasithin.E2P.SporB
open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_equiv_map_eq {Γ X : Type} [Group Γ] [Finite Γ] [Group X] [Finite X]
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (e : X ≃* Γ) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem not_configData
    (hns : ¬ Group.IsSolvable G23)
    {Yb : Subgroup G23} (hd : ConfigData G23 m23CtxB.S Yb) : False := by
  have hZs : Group.IsSolvable ↥(Yb ⊔ m23CtxB.S) :=
    isSolvable_sup_of_le_normalizer hd.solvable hd.sylow.2.1 hd.normalizes
  have hSZ : m23CtxB.S ≤ Yb ⊔ m23CtxB.S := le_sup_right
  have h9 : 9 ∣ Nat.card ↥(Yb ⊔ m23CtxB.S) :=
    hd.nine.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hZ15 := eq_Y15 hns hSZ hZs h9
  obtain ⟨φ, hφ⟩ := hd.s3s3
  obtain ⟨l10, l12, l13, n1012, n1013, n1213⟩ := three_members
  have hcard : Nat.card ↥(Yb ⊔ m23CtxB.S) = 1152 := by
    rw [hZ15, m23_card_Y (by norm_num)]
    rfl
  have hY : ∀ {j : ℕ}, j < 16 → Nat.card ↥(m23CtxB.Y j) = m23Ord[j]! := fun hj => m23_card_Y hj
  exact M23a.false_of_index_three_of_le φ hφ hcard (S := m23CtxB.S) (A₁ := m23CtxB.Y 10)
    (A₂ := m23CtxB.Y 12) (A₃ := m23CtxB.Y 13) m23_S_card hSZ
    (m23CtxB.S_le_Y 10) (m23CtxB.S_le_Y 12) (m23CtxB.S_le_Y 13) (l10.trans hZ15.symm.le)
    (l12.trans hZ15.symm.le) (l13.trans hZ15.symm.le) ((hY (by norm_num)).trans rfl)
    ((hY (by norm_num)).trans rfl) ((hY (by norm_num)).trans rfl) n1012 n1013 n1213

theorem not_configData_of_equiv
    {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* G23) (hns : ¬ Group.IsSolvable Q) {Sb Yb : Subgroup Q} (hd : ConfigData Q Sb Yb) :
    False := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_map_eq (m23_S_sylow) e hd.sylow
  have hd' := hd.of_equiv ψ
  rw [hψ] at hd'
  refine not_configData (fun hsolv => hns ?_) hd'
  exact Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective

theorem false_of_m23
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hIeq : I = L ⊔ Sgp153 T V₁) (hYL : Yp ≤ L)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M23) : False := by
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  let qe : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.M23 :=
    (QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e
  have hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := center_quot_eq_bot c
  have hcard :
      Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) ≤ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    have h1 :
        Nat.card (MulAut (↥L ⧸ Subgroup.center ↥L)) = Nat.card (MulAut NativeSporadic.M23) :=
      Nat.card_congr (MulAut.congr qe).toEquiv
    have h2 : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card NativeSporadic.M23 :=
      Nat.card_congr qe.toEquiv
    rw [h1, h2]
    exact m23_mulAut_card
  have hin : inner (↥L ⧸ Subgroup.center ↥L) = ⊤ := inner_eq_top_of_card_le hcen hcard
  have hinn : ∀ α : MulAut (↥L ⧸ Subgroup.center ↥L), ∃ q, MulAut.conj q = α := by
    intro α
    have : α ∈ inner (↥L ⧸ Subgroup.center ↥L) := by rw [hin]; exact Subgroup.mem_top α
    exact this
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  obtain ⟨ρ, -, hρ⟩ := exists_rho hLI hN hinn hcen
  obtain ⟨hns, Sb, Yb, hd⟩ := config_of_ctx c hmin hN hIeq hYL ρ hρ
  exact not_configData_of_equiv qe hns hd

end CFSG.Quasithin.ModH.M23c
