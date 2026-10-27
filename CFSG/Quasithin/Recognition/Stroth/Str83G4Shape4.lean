module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape3
public import CFSG.Quasithin.Recognition.Stroth.Str83G4LemmaW
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5T

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open CFSG.GH74.Uniqueness.Bender
open CFSG.QuasithinUnique.Setup.X7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_fpf_D2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) {δ x : G} (hδ : δ ∈ d.D2) (hδ1 : δ ≠ 1) (hxS : x ∈ S)
    (hcomm : δ * x * δ⁻¹ * x⁻¹ ∈ Q2 L1 L2 S) : x ∈ Q2 L1 L2 S := by
  have hfr' := hfr
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr'
  let H : Subgroup G := u3H L1 L2 S
  have hH : H = L2 ⊔ S := by
    change L2 ⊔ Q2 L1 L2 S = L2 ⊔ S
    exact (sup_eq_of_S_eq_right hS2).symm
  have hSH : IsSylowTwoOf S H := by
    rw [hH]
    exact str83G4_isSylowTwoOf_sup_right hfr'
  have hQ : Q2 L1 L2 S = pCoreOf 2 H := (str86_pCoreOf_u3H hF).symm
  have hDleH : d.D2 ≤ H := by
    rw [hH]
    exact (d.hD2hall.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
  have hBLH : borelOf L2 S ≤ H := (F1.borelOf_le L2 S).trans le_sup_left
  have hNHS : H ⊓ Subgroup.normalizer (S : Set G) = borelOf L2 S ⊔ Q2 L1 L2 S :=
    normalizer_inf_eq_borel_sup_q2 hF hB ha hfr'.2.2.2.1 hL2 H hH
  have hDinfQ : d.D2 ⊓ Q2 L1 L2 S = ⊥ := by
    rw [inf_comm]
    exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P2 L1 L2 S)) d.hD2hall.2.1
  have hBt2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hBT : BenderType (oTwoQuot ↥H) (2 * a + 1) 1 1 :=
    BenderType.of_mulEquiv hBt2 (str86_oTwoQuot_u3H_equiv hF).symm
  exact fixed_point_free_of_bender_quotient (L := L2) hQ hSH hQ2S hS2 hDleH
    d.hD2hall d.hD2sup hBLH hNHS hDinfQ hBT (hDleH hδ) hxS hδ hδ1 hcomm

theorem str83G4_fpf_D1_mod_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {δ x : G} (hδD1 : δ ∈ d.D1) (hδ1 : δ ≠ 1) (hxS : x ∈ S)
    (hcomm : δ * x * δ⁻¹ * x⁻¹ ∈ Q2 L1 L2 S) : x ∈ Q2 L1 L2 S := by
  classical
  have hfr' := hfr
  have hδ := str83G4_d1_inf_h2_eq_bot hfr' d hX hB
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  let H2 : Subgroup G := centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2
  have hD2infH2 : d.D2 ⊓ H2 = ⊥ := str83G4_d2_inf_h2_eq_bot hfr' d
  have hD2supH2 : d.D2 ⊔ H2 = d.D1 ⊔ d.D2 := str83G4_d2_sup_h2_eq hfr' d
  have hBt2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hD2cyc : IsCyclic ↥d.D2 :=
    (card_isCyclic_of_hallTwoPrime (i := 1) hF.1.h2.sylow d.hD2hall d.hD2sup hBt2).2
  have hD1centD2 : d.D1 ≤ Subgroup.centralizer (d.D2 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (d.hcomm y hy z hz).symm
  have hD2centD2 : d.D2 ≤ Subgroup.centralizer (d.D2 : Set G) := by
    letI : CommGroup ↥d.D2 := hD2cyc.commGroup
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (mul_comm (⟨z, hz⟩ : ↥d.D2) ⟨y, hy⟩)
  have hH2centD2 : H2 ≤ Subgroup.centralizer (d.D2 : Set G) :=
    (centralizerMod_le_left _ _ _).trans (sup_le hD1centD2 hD2centD2)
  have hD2NH2 : d.D2 ≤ Subgroup.normalizer (H2 : Set G) :=
    (Subgroup.le_centralizer_iff.mp hH2centD2).trans (Subgroup.centralizer_le_normalizer _)
  have hδmem : δ ∈ d.D2 ⊔ H2 := by
    rw [hD2supH2]
    exact Subgroup.mem_sup_left hδD1
  obtain ⟨δ2, hδ2D2, h, hH2, hδeq⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hD2NH2).mp hδmem
  have hδ2ne : δ2 ≠ 1 := by
    intro h1
    have hm : δ ∈ H2 := by rw [hδeq, h1, one_mul]; exact hH2
    have hbot : δ ∈ d.D1 ⊓ H2 := ⟨hδD1, hm⟩
    rw [hδ] at hbot
    exact hδ1 (Subgroup.mem_bot.mp hbot)
  have hD1B : d.D1 ≤ bigB L1 L2 S :=
    d.hD1hall.1.trans ((le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : borelOf L1 S ⊔ borelOf L2 S ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S))
  have hD2B : d.D2 ≤ bigB L1 L2 S :=
    d.hD2hall.1.trans ((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : borelOf L1 S ⊔ borelOf L2 S ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S))
  have hD1D2B : d.D1 ⊔ d.D2 ≤ bigB L1 L2 S := sup_le hD1B hD2B
  have hhB : h ∈ bigB L1 L2 S :=
    hD1D2B ((centralizerMod_le_left _ _ _) hH2)
  have hhL2 : ∀ l ∈ L2, h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 :=
    (mem_centralizerMod.mp hH2).2.2
  have hhS : ∀ y ∈ S, h * y * h⁻¹ * y⁻¹ ∈ Q2 L1 L2 S := by
    intro y hy
    exact str83G4_trivial_on_sup_right hfr' hhB hhL2 y ((le_sup_right : S ≤ L2 ⊔ S) hy)
  let q : G := h * x * h⁻¹ * x⁻¹
  let y : G := h * x * h⁻¹
  have hqQ : q ∈ Q2 L1 L2 S := hhS x hxS
  have hyq : y = q * x := by dsimp only [q, y]; group
  have hdelx : ⁅δ, x⁆ = ⁅δ2, y⁆ * q := by
    rw [hδeq]
    dsimp only [q, y]
    simp only [commutatorElement_def]
    group
  have hdelxQ : ⁅δ, x⁆ ∈ Q2 L1 L2 S := hcomm
  have hdelyQ : ⁅δ2, y⁆ ∈ Q2 L1 L2 S := by
    have h1 : ⁅δ2, y⁆ = ⁅δ, x⁆ * q⁻¹ := by rw [hdelx]; group
    rw [h1]
    exact (Q2 L1 L2 S).mul_mem hdelxQ ((Q2 L1 L2 S).inv_mem hqQ)
  have hD2NQ2 : d.D2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (d.hD2hall.1.trans (F1.borelOf_le L2 S)).trans
      ((le_sup_left : L2 ≤ P2 L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
  have hdelta2_q : ⁅δ2, q⁆ ∈ Q2 L1 L2 S :=
    (Q2 L1 L2 S).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hD2NQ2 hδ2D2) q).mp hqQ)
      ((Q2 L1 L2 S).inv_mem hqQ)
  have hdelqx : ⁅δ2, q * x⁆ = ⁅δ2, q⁆ * (q * ⁅δ2, x⁆ * q⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hmid : q * ⁅δ2, x⁆ * q⁻¹ ∈ Q2 L1 L2 S := by
    have h1 : ⁅δ2, q⁆ * (q * ⁅δ2, x⁆ * q⁻¹) ∈ Q2 L1 L2 S := by
      rw [← hdelqx, ← hyq]
      exact hdelyQ
    have h2 : ⁅δ2, q⁆⁻¹ * (⁅δ2, q⁆ * (q * ⁅δ2, x⁆ * q⁻¹)) ∈ Q2 L1 L2 S :=
      (Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).inv_mem hdelta2_q) h1
    rwa [show ⁅δ2, q⁆⁻¹ * (⁅δ2, q⁆ * (q * ⁅δ2, x⁆ * q⁻¹)) =
      q * ⁅δ2, x⁆ * q⁻¹ by group] at h2
  have hdel2xQ : ⁅δ2, x⁆ ∈ Q2 L1 L2 S := by
    have hqN : q ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) := Subgroup.le_normalizer hqQ
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hqN) _).mp hmid
    have h1' : q⁻¹ * (q * ⁅δ2, x⁆ * q⁻¹) * q ∈ Q2 L1 L2 S := by
      simpa using h1
    rwa [show q⁻¹ * (q * ⁅δ2, x⁆ * q⁻¹) * q = ⁅δ2, x⁆ by group] at h1'
  exact str83G4_fpf_D2 hfr' d hδ2D2 hδ2ne hxS hdel2xQ

theorem str83G4_z2_inf_centralizer_d1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    Z2 L1 L2 S ⊓ Subgroup.centralizer (d.D1 : Set G) = Z1 L1 L2 S := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hB', ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hZ1eq, hZ1Z2, -, -, hZ2CS⟩ := str83_caseI_basics hF hB' ha hSz hL2 hZI
  have hZ1D1 : Z1 L1 L2 S ≤ Subgroup.centralizer (d.D1 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL1 : y ∈ L1 := (F1.borelOf_le L1 S) (d.hD1hall.1 hy)
    exact (Subgroup.mem_centralizer_iff.mp (hZI (Subgroup.mem_sup_left hyL1)) z hz).symm
  refine le_antisymm ?_ (le_inf hZ1Z2 hZ1D1)
  intro u hu
  obtain ⟨huZ2, huC⟩ := Subgroup.mem_inf.mp hu
  have hD1NS : d.D1 ≤ Subgroup.normalizer (S : Set G) :=
    (d.hD1hall.1.trans ((le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : borelOf L1 S ⊔ borelOf L2 S ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S))).trans hB'
  have hS2 : IsPGroup 2 S := (str83G4_isSylowTwoOf_sup_left hfr').2.1
  have hsolvS : Group.IsSolvable ↥S := by
    letI : Group.IsNilpotent ↥S := hS2.isNilpotent
    exact IsNilpotent.to_isSolvable
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  have hcop : Nat.Coprime (Nat.card ↥d.D1) (Nat.card ↥S) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr d.hD1hall.2.1)
  have hcopAction := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
    (R := S) (A := d.D1) hD1NS hcop hsolvS
  have hfixQ2 : S ⊓ Subgroup.centralizer (d.D1 : Set G) ≤ Q2 L1 L2 S := by
    intro y hy
    obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨d0, hd0D1, hd01⟩ :=
      (Subgroup.bot_or_exists_ne_one d.D1).resolve_left (str83G4Data_D1_ne_bot hfr' d)
    have hcomm0 : d0 * y * d0⁻¹ * y⁻¹ ∈ Q2 L1 L2 S := by
      have hc := Subgroup.mem_centralizer_iff.mp hyC d0 hd0D1
      have h1 : d0 * y * d0⁻¹ * y⁻¹ = 1 := by rw [hc]; group
      rw [h1]
      exact (Q2 L1 L2 S).one_mem
    exact str83G4_fpf_D1_mod_q2 hfr' d hX hB hd0D1 hd01 hyS hcomm0
  have hS_le : S ≤ ⁅S, d.D1⁆ ⊔ Q2 L1 L2 S :=
    hcopAction.trans (sup_le le_sup_left (hfixQ2.trans le_sup_right))
  have hmem : ∀ y : ↥S, ⁅u, (y : G)⁆ ∈ Z1 L1 L2 S := by
    intro y
    have h1 : ⁅u, (y : G)⁆ ∈ ⁅Z2 L1 L2 S, S⁆ :=
      Subgroup.commutator_mem_commutator huZ2 y.2
    rwa [str83G4_commutator_z2_s hfr'] at h1
  let φ : ↥S →* ↥(Z1 L1 L2 S) :=
    { toFun := fun y => ⟨⁅u, (y : G)⁆, hmem y⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := by
        intro y z
        apply Subtype.ext
        change ⁅u, ((y : G) * (z : G))⁆ = ⁅u, (y : G)⁆ * ⁅u, (z : G)⁆
        rw [show ⁅u, (y : G) * (z : G)⁆ =
          ⁅u, (y : G)⁆ * ((y : G) * ⁅u, (z : G)⁆ * (y : G)⁻¹) by
            simp only [commutatorElement_def]; group]
        have hzZ1 : ⁅u, (z : G)⁆ ∈ Z1 L1 L2 S := hmem z
        have hyC : (y : G) ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
          str83G4_sup_le_centralizer_z1 hfr' (Subgroup.mem_sup_right y.2)
        have hconj : (y : G) * ⁅u, (z : G)⁆ * (y : G)⁻¹ = ⁅u, (z : G)⁆ := by
          have hcomm := Subgroup.mem_centralizer_iff.mp hyC ⁅u, (z : G)⁆ hzZ1
          rw [← hcomm]
          group
        rw [hconj] }
  have hcommS : ⁅S, d.D1⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro s hs dd hd
    rw [commutatorElement_def]
    simpa [mul_assoc] using
      S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hD1NS hd) s⁻¹).mp (S.inv_mem hs))
  have hcomm_ker : ⁅S, d.D1⁆ ≤ (φ.ker).map S.subtype := by
    rw [Subgroup.commutator_le]
    intro s hs dd hd
    have hsdS : ⁅s, dd⁆ ∈ S := by
      rw [commutatorElement_def]
      simpa [mul_assoc] using
        S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hD1NS hd) s⁻¹).mp (S.inv_mem hs))
    have hconjS : dd * s * dd⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hD1NS hd) s).mp hs
    refine Subgroup.mem_map.mpr ⟨⟨⁅s, dd⁆, hsdS⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ⁅u, ⁅s, dd⁆⁆ = 1
    have hsd : ⁅s, dd⁆ = s * (dd * s * dd⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hsd]
    have hφs : φ ⟨s, hs⟩ = φ ⟨dd * s * dd⁻¹, hconjS⟩ := by
      apply Subtype.ext
      change ⁅u, s⁆ = ⁅u, dd * s * dd⁻¹⁆
      have h1 : ⁅u, dd * s * dd⁻¹⁆ = dd * ⁅u, s⁆ * dd⁻¹ := by
        have hudd : dd * u = u * dd := Subgroup.mem_centralizer_iff.mp huC dd hd
        have hconj : MulAut.conj dd u = u := by
          rw [MulAut.conj_apply]
          calc dd * u * dd⁻¹ = (u * dd) * dd⁻¹ := by rw [hudd]
            _ = u := by group
        have h := (map_commutatorElement (MulAut.conj dd).toMonoidHom u s).symm
        rw [show (MulEquiv.toMonoidHom (MulAut.conj dd)) u = u from hconj] at h
        have h2s : (MulEquiv.toMonoidHom (MulAut.conj dd)) s = dd * s * dd⁻¹ := rfl
        have h2c : (MulEquiv.toMonoidHom (MulAut.conj dd)) ⁅u, s⁆ =
            dd * ⁅u, s⁆ * dd⁻¹ := rfl
        rw [h2s, h2c] at h
        exact h
      rw [h1]
      have husZ1 : ⁅u, s⁆ ∈ Z1 L1 L2 S := hmem ⟨s, hs⟩
      have hddL1 : dd ∈ L1 := (F1.borelOf_le L1 S) (d.hD1hall.1 hd)
      have hddC : dd ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        hZI (Subgroup.mem_sup_left hddL1)
      have hcomm : dd * ⁅u, s⁆ = ⁅u, s⁆ * dd :=
        (Subgroup.mem_centralizer_iff.mp hddC ⁅u, s⁆ husZ1).symm
      calc ⁅u, s⁆ = (⁅u, s⁆ * dd) * dd⁻¹ := by group
        _ = (dd * ⁅u, s⁆) * dd⁻¹ := by rw [← hcomm]
        _ = dd * ⁅u, s⁆ * dd⁻¹ := by group
    have harg : (⟨s * (dd * s * dd⁻¹)⁻¹, S.mul_mem hs (S.inv_mem hconjS)⟩ : ↥S) =
        ⟨s, hs⟩ * ⟨dd * s * dd⁻¹, hconjS⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hφeq : φ ⟨s * (dd * s * dd⁻¹)⁻¹, S.mul_mem hs (S.inv_mem hconjS)⟩ = 1 := by
      rw [harg, map_mul, map_inv, hφs, mul_inv_cancel]
    simpa [φ] using congrArg Subtype.val hφeq
  have hSNQ2 : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S)).trans
      ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
  have hQ2_ker : Q2 L1 L2 S ≤ (φ.ker).map S.subtype := by
    intro q hq
    have hqS : q ∈ S := str83G4_q2_le_s hfr' hq
    refine Subgroup.mem_map.mpr ⟨⟨q, hqS⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ⁅u, q⁆ = 1
    have hqC : q ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq
    have hcomm : u * q = q * u := Subgroup.mem_centralizer_iff.mp hqC u huZ2
    rw [commutatorElement_def]
    calc u * q * u⁻¹ * q⁻¹ = (q * u) * u⁻¹ * q⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hS_ker : S ≤ (φ.ker).map S.subtype := by
    intro s hs
    have hs_mem : s ∈ ⁅S, d.D1⁆ ⊔ Q2 L1 L2 S := hS_le hs
    have hcommNQ2 : ⁅S, d.D1⁆ ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      hcommS.trans hSNQ2
    obtain ⟨a, ha, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hcommNQ2).mp hs_mem
    exact (φ.ker.map S.subtype).mul_mem (hcomm_ker ha) (hQ2_ker hq)
  have huCS : u ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs_ker : s ∈ (φ.ker).map S.subtype := hS_ker hs
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hs_ker
    have hφy : φ y = 1 := hy
    have hval : ⁅u, (y : G)⁆ = 1 := by
      simpa [φ] using congrArg Subtype.val hφy
    have hyG : (y : G) = s := hyeq
    have hcommy : ⁅u, s⁆ = 1 := by simpa [hyG] using hval
    have h1 : u * s * u⁻¹ * s⁻¹ = 1 := hcommy
    have hcomm : u * s = s * u := by
      calc u * s = (u * s * u⁻¹ * s⁻¹) * (s * u) := by group
        _ = 1 * (s * u) := by rw [h1]
        _ = s * u := by group
    exact hcomm.symm
  have huZ2CS : u ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) := ⟨huZ2, huCS⟩
  rw [hZ2CS] at huZ2CS
  exact huZ2CS

theorem str83G4_z2_inf_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    Z2 L1 L2 S ⊓ str83X1 L1 L2 S = Z1 L1 L2 S := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hB', ha, hSz, hL2, hZI⟩ := hfr
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str83_caseI_basics hF hB' ha hSz hL2 hZI).2.1
  refine le_antisymm ?_ (le_inf hZ1Z2 (str83G4_z1_le_x1 hfr'))
  intro u hu
  obtain ⟨huZ2, huX1⟩ := Subgroup.mem_inf.mp hu
  have huC : u ∈ Subgroup.centralizer (d.D1 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro dd hd
    have hdH : dd ∈ L1 ⊔ S :=
      Subgroup.mem_sup_left ((F1.borelOf_le L1 S) (d.hD1hall.1 hd))
    have hdO2 : dd ∈ oTwoUpper (L1 ⊔ S) :=
      mem_oTwoUpper_of_odd hdH
        (Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 hd))
    have hcomm : ⁅u, dd⁆ = 1 := by
      have h1 : ⁅u, dd⁆ ∈ ⁅str83X1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ :=
        Subgroup.commutator_mem_commutator huX1 hdO2
      rw [str83G4_commutator_x1_oTwo_eq_bot hfr' hX] at h1
      exact Subgroup.mem_bot.mp h1
    have h1 : u * dd * u⁻¹ * dd⁻¹ = 1 := hcomm
    calc dd * u = (dd * u * dd⁻¹ * u⁻¹) * (u * dd) := by group
      _ = (u * dd) * u⁻¹ * dd⁻¹ * (u * dd) := by
        rw [show dd * u * dd⁻¹ * u⁻¹ = (u * dd * u⁻¹ * dd⁻¹)⁻¹ by group, h1]
        group
      _ = u * dd := by
        rw [h1]
        group
  have hZ2D1 : Z2 L1 L2 S ⊓ Subgroup.centralizer (d.D1 : Set G) = Z1 L1 L2 S :=
    str83G4_z2_inf_centralizer_d1 hfr' d hX hB
  have hu' : u ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer (d.D1 : Set G) := ⟨huZ2, huC⟩
  rw [hZ2D1] at hu'
  exact hu'

theorem str83G4_x_eq_commutator_sup_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    str83X L1 L2 S = ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ⊔ Z1 L1 L2 S := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hB', ha, hSz, hL2, hZI⟩ := hfr
  refine le_antisymm ?_ (str83N_le_x hfr')
  have hZ2p : IsPGroup 2 (Z2 L1 L2 S) :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le (omegaOneCenterOf_le (Q2 L1 L2 S))
  have hsolvZ2 : Group.IsSolvable ↥(Z2 L1 L2 S) := by
    letI : Group.IsNilpotent ↥(Z2 L1 L2 S) := hZ2p.isNilpotent
    exact IsNilpotent.to_isSolvable
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2p
  have hcop : Nat.Coprime (Nat.card ↥d.D1) (Nat.card ↥(Z2 L1 L2 S)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr d.hD1hall.2.1)
  have hD1NZ2 : d.D1 ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (d.hD1hall.1.trans ((le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : borelOf L1 S ⊔ borelOf L2 S ≤
        (borelOf L1 S ⊔ borelOf L2 S) ⊔ S))).trans (bigB_le_normalizer_z2 L1 L2 S)
  have hcopAction := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
    (R := Z2 L1 L2 S) (A := d.D1) hD1NZ2 hcop hsolvZ2
  have hZ2D1 : Z2 L1 L2 S ⊓ Subgroup.centralizer (d.D1 : Set G) = Z1 L1 L2 S :=
    str83G4_z2_inf_centralizer_d1 hfr' d hX hB
  have hD1O2 : d.D1 ≤ oTwoUpper (L1 ⊔ S) := by
    intro dd hd
    exact mem_oTwoUpper_of_odd
      (Subgroup.mem_sup_left ((F1.borelOf_le L1 S) (d.hD1hall.1 hd)))
      (Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 hd))
  have hZ2N : Z2 L1 L2 S ≤ str83N L1 L2 S := by
    refine hcopAction.trans (sup_le ?_ ?_)
    · exact (Subgroup.commutator_mono (z2_le_str83X L1 L2 S) hD1O2).trans le_sup_left
    · rw [hZ2D1]
      exact le_sup_right
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hbigB : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR).1
  have hL1N : L1 ≤ Subgroup.normalizer (str83N L1 L2 S : Set G) :=
    (le_sup_left : L1 ≤ L1 ⊔ S).trans
      (D14.le_normalizer_of_isNormalIn (str83N_normal hfr'))
  change conjClosure (Z2 L1 L2 S) (P1 L1 L2 S) ≤ str83N L1 L2 S
  refine conjClosure_le ?_
  intro h hhP1 z hzZ2
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hbigB).mp hhP1
  have hbz : b * z * b⁻¹ ∈ Z2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (bigB_le_normalizer_z2 L1 L2 S hb) z).mp hzZ2
  have hbzN : b * z * b⁻¹ ∈ str83N L1 L2 S := hZ2N hbz
  have h1 := (Subgroup.mem_normalizer_iff.mp (hL1N hl) (b * z * b⁻¹)).mp hbzN
  simpa [mul_assoc] using h1

end CFSG.Quasithin.Stroth

end
