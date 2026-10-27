module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Q1Nat
public import CFSG.Quasithin.Recognition.Stroth.Str83G4NMGen
public import CFSG.Quasithin.Recognition.Stroth.Str83G4X1Z1
public import TauCeti.GroupTheory.Index.Two
public import CFSG.Quasithin.Recognition.Stroth.Str83G4C23
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefFixed

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4SecPart_le_commutator_sup
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S))
    {M : Subgroup G} (hM : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) M)
    (hYM : str83Y L1 L2 S ≤ M)
    {Z' Z'' : Subgroup G} (hZ' : Z' ≤ Z1 L1 L2 S) (hZ''Z' : Z'' ≤ Z')
    (hrel : Z''.relIndex Z' = 2) :
    str83G4SecPart hfr hM.1 Z' ≤
      ⁅str83G4SecPart hfr hM.1 Z', oTwoUpper (L1 ⊔ S)⁆ ⊔ str83G4SecPart hfr hM.1 Z'' := by
  classical
  let H := L1 ⊔ S
  let Q := Q1 L1 L2 S
  let X := str83X L1 L2 S
  let Z := Z1 L1 L2 S
  let Y := str83Y L1 L2 S
  let O := oTwoUpper H
  let M' := str83G4SecPart hfr hM.1 Z'
  let M'' := str83G4SecPart hfr hM.1 Z''
  let A : Subgroup G := ⁅M', O⁆ ⊔ M''
  have hQH : Q ≤ H := (str83G4_q1_le_s hfr).trans le_sup_right
  have hXH : X ≤ H := str83G4_x_le_sup hfr
  have hOH : O ≤ H := oTwoUpper_le H
  have hMleQ : M ≤ Q := hM.1
  have hM'leM : M' ≤ M := str83G4SecPart_le hfr hM.1 Z'
  have hM''leM' : M'' ≤ M' := str83G4SecPart_mono hfr hM.1 hZ''Z'
  have hM'leQ : M' ≤ Q := hM'leM.trans hMleQ
  have hM''leQ : M'' ≤ Q := hM''leM'.trans hM'leQ
  have hM'leH : M' ≤ H := hM'leQ.trans hQH
  have hM''leH : M'' ≤ H := hM''leQ.trans hQH
  have hM'n : IsNormalIn H Q M' := str83G4SecPart_normal hfr hM Z'
  have hM''n : IsNormalIn H Q M'' := str83G4SecPart_normal hfr hM Z''
  have hHM' : H ≤ Subgroup.normalizer (M' : Set G) := D14.le_normalizer_of_isNormalIn hM'n
  have hHM'' : H ≤ Subgroup.normalizer (M'' : Set G) := D14.le_normalizer_of_isNormalIn hM''n
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := CFSG.Quasithin.le_normalizer_oTwoUpper H
  have hcommM'O : ⁅M', O⁆ ≤ M' :=
    F112W.commutator_le_self_of_le_normalizer (hOH.trans hHM')
  have hYleM'' : Y ≤ M'' := by
    have hbot : str83G4SecPart hfr hM.1 (⊥ : Subgroup G) = Y :=
      str83G4SecPart_bot hfr hM.1 hYM
    rw [← hbot]
    exact str83G4SecPart_mono hfr hM.1 bot_le
  have hAleM' : A ≤ M' := sup_le hcommM'O hM''leM'
  have hAleM : A ≤ M := hAleM'.trans hM'leM
  have hAleQ : A ≤ Q := hAleM.trans hMleQ
  have hAleH : A ≤ H := hAleQ.trans hQH
  have hAn : H ≤ Subgroup.normalizer (A : Set G) := by
    have hcomm : H ≤ Subgroup.normalizer (⁅M', O⁆ : Subgroup G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHM' hg),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHO hg)]
    exact D14.le_normalizer_sup hcomm hHM''
  have hXAn : IsNormalIn H X (str83G4XPart hfr hAleQ Z'') :=
    str83G4XPart_normal hfr hAleQ hAn Z''
  have hZleXA : Z ≤ str83G4XPart hfr hAleQ Z'' := by
    intro z hz
    refine (mem_str83G4XPart hfr hAleQ Z'').mpr
      ⟨str83G4_z1_le_x hfr hz, fun u hu => ?_⟩
    have huQ : u ∈ Q := hAleQ hu
    have huH : u ∈ H := hQH huQ
    have hzu : z * u = u * z :=
      Subgroup.mem_centralizer_iff.mp (str83G4_sup_le_centralizer_z1 hfr huH) z hz
    have h1 : ⁅z, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hzu
    rw [h1]
    exact Z''.one_mem
  rcases hXstep.2.2.2 (str83G4XPart hfr hAleQ Z'') hXAn hZleXA
    (str83G4XPart_le hfr hAleQ Z'') with hXA | hXA
  ·
    let NX : Subgroup ↥X := Z.subgroupOf X
    let W := ↥X ⧸ NX
    have hZnorm : (Z.subgroupOf X).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hXH.trans (str83G4_sup_le_normalizer_z1 hfr))
    haveI : NX.Normal := hZnorm
    have hXp : IsPGroup 2 X := (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le (str83X_le_q1 hfr)
    have hE : IsElemAbelian 2 (Ch3z.chiefMod Z X) :=
      CFSG.Quasithin.isElemAbelian_chiefMod hXstep hXH hXp
    have hZnX : X ≤ Subgroup.normalizer (Z : Set G) :=
      hXH.trans (str83G4_sup_le_normalizer_z1 hfr)
    have hXsq : ∀ x : X, ((x : G) ^ 2) ∈ Z := by
      intro x
      have h1 : Ch3z.chiefIota hZnX (x ^ 2) = 1 := by
        rw [map_pow]
        apply Subtype.ext
        simpa using hE.2 _ (Ch3z.chiefIota hZnX x).2
      exact (Ch3z.chiefIota_eq_one_iff hZnX (x ^ 2)).mp h1
    have hW2 : ∀ y : W, y * y = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) y
      rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      simpa [pow_two] using hXsq x
    let NA : Subgroup ↥A := M''.subgroupOf A
    let U := ↥A ⧸ NA
    have hAnorm : (M''.subgroupOf A).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hAleH.trans hHM'')
    haveI : NA.Normal := hAnorm
    have hAsq : ∀ a : A, ((a : G) ^ 2) ∈ M'' := by
      intro a
      have haM' : (a : G) ∈ M' := hAleM' a.2
      have haQ : (a : G) ∈ Q := hM'leQ haM'
      refine (mem_str83G4SecPart hfr hM.1 Z'').mpr
        ⟨by simpa [pow_two] using M.mul_mem (hM'leM haM') (hM'leM haM'), fun x hx => ?_⟩
      have hxa : ⁅(x : G), (a : G)⁆ ∈ Z' :=
        ((mem_str83G4SecPart hfr hM.1 Z').mp haM').2 x hx
      have hsq : ⁅(x : G), ((a : G) ^ 2)⁆ =
          ⁅(x : G), (a : G)⁆ * ⁅(x : G), (a : G)⁆ := by
        simpa [pow_two] using str83G4_phi_mul_right hfr haQ haQ hx
      have hzab : (⁅(x : G), (a : G)⁆) * ⁅(x : G), (a : G)⁆ = 1 := by
        simpa [pow_two] using
          (B2F.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 _ (hZ' hxa)
      change ⁅(x : G), ((a : G) ^ 2)⁆ ∈ Z''
      rw [hsq, hzab]
      exact Z''.one_mem
    have hU2 : ∀ y : U, y * y = 1 := by
      intro y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (M''.subgroupOf A) y
      rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      simpa [pow_two] using hAsq a
    letI : CommGroup W := by
      refine { (inferInstance : Group W) with mul_comm := ?_ }
      intro a b
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
            Subgroup.mem_subgroupOf, Subgroup.coe_div]
          change ((x : G) * (y : G)) / ((y : G) * (x : G)) ∈ Z
          have e : ((x : G) * (y : G)) / ((y : G) * (x : G)) = ⁅(x : G), (y : G)⁆ := by
            simp only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev]
            group
          rw [e]
          exact str83G4_commutator_x_q1_le hfr
            (Subgroup.commutator_mem_commutator x.2 (str83X_le_q1 hfr y.2))
    letI : CommGroup U := by
      refine { (inferInstance : Group U) with mul_comm := ?_ }
      intro a b
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
            Subgroup.mem_subgroupOf, Subgroup.coe_div]
          change ((x : G) * (y : G)) / ((y : G) * (x : G)) ∈ M''
          have e : ((x : G) * (y : G)) / ((y : G) * (x : G)) = ⁅(x : G), (y : G)⁆ := by
            simp only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev]
            group
          rw [e]
          exact hYleM'' (str83G4_commutator_q1_q1_le_y hfr
            (Subgroup.commutator_mem_commutator (hAleQ x.2) (hAleQ y.2)))
    let C2 := Multiplicative (ZMod 2)
    let χ : ↥Z' →* C2 := Subgroup.indexTwoCharacter (Z''.subgroupOf Z') hrel
    let phi (u : ↥M') : ↥X →* C2 :=
      MonoidHom.mk' (fun x => χ ⟨⁅(x : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 x x.2⟩) (by
        intro x y
        have hmul : (⟨⁅((x * y : ↥X) : G), (u : G)⁆,
            ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 (x * y) (x * y).2⟩ : ↥Z') =
            ⟨⁅(x : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 x x.2⟩ *
            ⟨⁅(y : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 y y.2⟩ := by
          apply Subtype.ext
          simpa using str83G4_phi_mul_left hfr (hM'leQ u.2) x.2 y.2
        rw [hmul]
        exact map_mul χ _ _)
    have phi_kill : ∀ u : ↥M', Z.subgroupOf X ≤ (phi u).ker := by
      intro u z hz
      rw [MonoidHom.mem_ker]
      have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
      have huH : (u : G) ∈ H := hM'leH u.2
      have hzu : (z : G) * (u : G) = (u : G) * (z : G) :=
        Subgroup.mem_centralizer_iff.mp (str83G4_sup_le_centralizer_z1 hfr huH) (z : G) hzZ
      have h1 : ⁅(z : G), (u : G)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hzu
      change χ ⟨⁅(z : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 z z.2⟩ = 1
      rw [show (⟨⁅(z : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 z z.2⟩ : ↥Z') = 1 from
        Subtype.ext h1]
      simpa using map_one χ
    let phiLift (u : ↥M') : W →* C2 :=
      QuotientGroup.lift (Z.subgroupOf X) (phi u) (phi_kill u)
    let Θ₀ : ↥M' → (W →* C2) := fun u => phiLift u
    have hM''norm : (M''.subgroupOf M').Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hM'leH.trans hHM'')
    let NM : Subgroup ↥M' := M''.subgroupOf M'
    haveI : NM.Normal := hM''norm
    let V := ↥M' ⧸ NM
    have hΘ₀ker : ∀ u ∈ NM, Θ₀ u = 1 := by
      intro u hu
      have hu'' : (u : G) ∈ M'' := (Subgroup.mem_subgroupOf (H := M'') (K := M')).mp hu
      apply MonoidHom.ext
      intro w
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) w
      change χ ⟨⁅(x : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp u.2).2 x x.2⟩ = 1
      exact (Subgroup.indexTwoCharacter_eq_one_iff hrel).mpr
        (Subgroup.mem_subgroupOf.mpr
          (((mem_str83G4SecPart hfr hM.1 Z'').mp hu'').2 x x.2))
    let Θbar : V → (W →* C2) :=
      Quotient.lift (fun u : ↥M' => Θ₀ u) (by
        intro a b hab
        have hab' : (a : ↥M')⁻¹ * b ∈ NM := (QuotientGroup.leftRel_apply).mp hab
        have hm : ((a : G)⁻¹ * (b : G)) ∈ M'' := by
          have h : ((a : ↥M')⁻¹ * (b : ↥M') : ↥M') ∈ NM := hab'
          simpa [NM, Subgroup.mem_subgroupOf] using h
        let m : ↥M' := ⟨(a : G)⁻¹ * (b : G), hM''leM' hm⟩
        have hmM' : (m : G) ∈ M' := m.2
        have hm'' : (m : G) ∈ M'' := hm
        have hb : b = a * m := Subtype.ext (by simp [m])
        have hEq : Θ₀ a = Θ₀ b := by
          apply MonoidHom.ext
          intro w
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) w
          change χ ⟨⁅(x : G), (a : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp a.2).2 x x.2⟩ =
            χ ⟨⁅(x : G), (b : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp b.2).2 x x.2⟩
          rw [hb]
          change χ ⟨⁅(x : G), (a : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp a.2).2 x x.2⟩ =
            χ ⟨⁅(x : G), ((a * m : ↥M') : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (a * m).2).2 x x.2⟩
          have hma : ⁅(x : G), (a : G)⁆ ∈ Z' :=
            ((mem_str83G4SecPart hfr hM.1 Z').mp a.2).2 x x.2
          have hmm : ⁅(x : G), (m : G)⁆ ∈ Z' :=
            ((mem_str83G4SecPart hfr hM.1 Z').mp hmM').2 x x.2
          have hmul : (⟨⁅(x : G), ((a * m : ↥M') : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (a * m).2).2 x x.2⟩ : ↥Z') =
              ⟨⁅(x : G), (a : G)⁆, hma⟩ * ⟨⁅(x : G), (m : G)⁆, hmm⟩ := by
            apply Subtype.ext
            simpa using str83G4_phi_mul_right hfr (hM'leQ a.2) (hM'leQ m.2) x.2
          rw [hmul, map_mul]
          have hchi : χ ⟨⁅(x : G), (m : G)⁆, hmm⟩ = 1 :=
            (Subgroup.indexTwoCharacter_eq_one_iff hrel).mpr
              (Subgroup.mem_subgroupOf.mpr
                (((mem_str83G4SecPart hfr hM.1 Z'').mp hm'').2 x x.2))
          rw [hchi, mul_one]
        exact hEq)
    have hΘ : Function.Injective Θbar := by
      intro v1 v2 h
      obtain ⟨u1, rfl⟩ := QuotientGroup.mk'_surjective (M''.subgroupOf M') v1
      obtain ⟨u2, rfl⟩ := QuotientGroup.mk'_surjective (M''.subgroupOf M') v2
      change Θ₀ u1 = Θ₀ u2 at h
      change (u1 : V) = (u2 : V)
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      refine (mem_str83G4SecPart hfr hM.1 Z'').mpr ⟨?_, ?_⟩
      · simpa [Subgroup.coe_div, div_eq_mul_inv] using
          M.mul_mem (hM'leM u1.2) (M.inv_mem (hM'leM u2.2))
      · intro x hx
        have hmem1 : ⁅(x : G), (u1 : G)⁆ ∈ Z' :=
          ((mem_str83G4SecPart hfr hM.1 Z').mp u1.2).2 x hx
        have hmem2 : ⁅(x : G), (u2 : G)⁆ ∈ Z' :=
          ((mem_str83G4SecPart hfr hM.1 Z').mp u2.2).2 x hx
        have hχ : χ ⟨⁅(x : G), (u1 : G)⁆, hmem1⟩ =
            χ ⟨⁅(x : G), (u2 : G)⁆, hmem2⟩ := by
          have h1 := congrArg (fun f : W →* C2 =>
            f (QuotientGroup.mk' (Z.subgroupOf X) ⟨x, hx⟩)) h
          change (phi u1) ⟨x, hx⟩ = (phi u2) ⟨x, hx⟩ at h1
          simpa [phi] using h1
        have hprod : χ ⟨⁅(x : G), (u1 : G)⁆ * ⁅(x : G), (u2 : G)⁆⁻¹,
            Z'.mul_mem hmem1 (Z'.inv_mem hmem2)⟩ = 1 := by
          change χ (⟨⁅(x : G), (u1 : G)⁆, hmem1⟩ *
            (⟨⁅(x : G), (u2 : G)⁆, hmem2⟩ : ↥Z')⁻¹) = 1
          rw [map_mul, map_inv, hχ, mul_inv_cancel]
        have hZ'' : ⁅(x : G), (u1 : G)⁆ * ⁅(x : G), (u2 : G)⁆⁻¹ ∈ Z'' := by
          simpa using Subgroup.mem_subgroupOf.mp
            ((Subgroup.indexTwoCharacter_eq_one_iff hrel).mp hprod)
        rw [Subgroup.coe_div, div_eq_mul_inv]
        rw [show ⁅(x : G), (u1 : G) * (u2 : G)⁻¹⁆ =
            ⁅(x : G), (u1 : G)⁆ * ⁅(x : G), (u2 : G)⁆⁻¹ by
          rw [str83G4_phi_mul_right hfr (hM'leQ u1.2) (Q.inv_mem (hM'leQ u2.2)) hx,
            str83G4_phi_inv_right hfr (hM'leQ u2.2) hx]]
        exact hZ''
    let psi (x : ↥X) : ↥A →* C2 :=
      MonoidHom.mk' (fun u => χ ⟨⁅(x : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 x x.2⟩) (by
        intro u v
        have hmul : (⟨⁅(x : G), ((u * v : ↥A) : G)⁆,
            ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' (u * v).2)).2 x x.2⟩ : ↥Z') =
            ⟨⁅(x : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 x x.2⟩ *
            ⟨⁅(x : G), (v : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' v.2)).2 x x.2⟩ := by
          apply Subtype.ext
          simpa using str83G4_phi_mul_right hfr (hAleQ u.2) (hAleQ v.2) x.2
        rw [hmul]
        exact map_mul χ _ _)
    have psi_kill : ∀ x : ↥X, M''.subgroupOf A ≤ (psi x).ker := by
      intro x u hu
      rw [MonoidHom.mem_ker]
      have hu'' : (u : G) ∈ M'' := Subgroup.mem_subgroupOf.mp hu
      change χ ⟨⁅(x : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 x x.2⟩ = 1
      exact (Subgroup.indexTwoCharacter_eq_one_iff hrel).mpr
        (Subgroup.mem_subgroupOf.mpr
          (((mem_str83G4SecPart hfr hM.1 Z'').mp hu'').2 x x.2))
    let psiLift (x : ↥X) : U →* C2 :=
      QuotientGroup.lift (M''.subgroupOf A) (psi x) (psi_kill x)
    let Ψ₀ : ↥X → (U →* C2) := fun x => psiLift x
    have hΨ₀ker : ∀ x ∈ Z.subgroupOf X, Ψ₀ x = 1 := by
      intro x hx
      have hxZ : (x : G) ∈ Z := Subgroup.mem_subgroupOf.mp hx
      apply MonoidHom.ext
      intro w
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (M''.subgroupOf A) w
      change χ ⟨⁅(x : G), (u : G)⁆,
        ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 x x.2⟩ = 1
      have huH : (u : G) ∈ H := hAleH u.2
      have hxu : (x : G) * (u : G) = (u : G) * (x : G) :=
        Subgroup.mem_centralizer_iff.mp (str83G4_sup_le_centralizer_z1 hfr huH) (x : G) hxZ
      have h1 : ⁅(x : G), (u : G)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hxu
      rw [show (⟨⁅(x : G), (u : G)⁆,
          ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 x x.2⟩ : ↥Z') = 1 from
        Subtype.ext h1]
      simpa using map_one χ
    let Ψbar : W → (U →* C2) :=
      Quotient.lift (fun x : ↥X => Ψ₀ x) (by
        intro a b hab
        have hab' : (a : ↥X)⁻¹ * b ∈ Z.subgroupOf X :=
          (QuotientGroup.leftRel_apply).mp hab
        have hz : ((a : G)⁻¹ * (b : G)) ∈ Z := by
          have h : ((a : ↥X)⁻¹ * (b : ↥X) : ↥X) ∈ Z.subgroupOf X := hab'
          simpa [Subgroup.mem_subgroupOf] using h
        let z : ↥X := ⟨(a : G)⁻¹ * (b : G), str83G4_z1_le_x hfr hz⟩
        have hzZ : (z : G) ∈ Z := hz
        have hb : b = a * z := Subtype.ext (by simp [z])
        have hEq : Ψ₀ a = Ψ₀ b := by
          apply MonoidHom.ext
          intro w
          obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (M''.subgroupOf A) w
          change χ ⟨⁅(a : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 a a.2⟩ =
            χ ⟨⁅(b : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 b b.2⟩
          rw [hb]
          change χ ⟨⁅(a : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 a a.2⟩ =
            χ ⟨⁅((a * z : ↥X) : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 (a * z) (a * z).2⟩
          have hma : ⁅(a : G), (u : G)⁆ ∈ Z' :=
            ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 a a.2
          have hmz : ⁅(z : G), (u : G)⁆ ∈ Z' :=
            ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 z z.2
          have hmul : (⟨⁅((a * z : ↥X) : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 (a * z) (a * z).2⟩ :
                ↥Z') = ⟨⁅(a : G), (u : G)⁆, hma⟩ * ⟨⁅(z : G), (u : G)⁆, hmz⟩ := by
            apply Subtype.ext
            simpa using str83G4_phi_mul_left hfr (hAleQ u.2) a.2 z.2
          rw [hmul, map_mul]
          have hzu : ⁅(z : G), (u : G)⁆ = 1 :=
            commutatorElement_eq_one_iff_mul_comm.mpr
              (Subgroup.mem_centralizer_iff.mp
                (str83G4_sup_le_centralizer_z1 hfr (hAleH u.2)) (z : G) hzZ)
          have hchi : χ ⟨⁅(z : G), (u : G)⁆, hmz⟩ = 1 := by
            rw [show (⟨⁅(z : G), (u : G)⁆,
              ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' u.2)).2 z z.2⟩ : ↥Z') = 1 from
              Subtype.ext hzu]
            simpa using map_one χ
          rw [hchi, mul_one]
        exact hEq)
    have hΨ : Function.Injective Ψbar := by
      intro w1 w2 h
      obtain ⟨x1, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) w1
      obtain ⟨x2, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) w2
      change Ψ₀ x1 = Ψ₀ x2 at h
      change (x1 : W) = (x2 : W)
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      have hmemXA : ((x1 : G) / (x2 : G)) ∈ str83G4XPart hfr hAleQ Z'' := by
        refine (mem_str83G4XPart hfr hAleQ Z'').mpr ⟨?_, fun u hu => ?_⟩
        · simpa [div_eq_mul_inv] using X.mul_mem x1.2 (X.inv_mem x2.2)
        · have h1 := congrArg (fun f : U →* C2 =>
            f (QuotientGroup.mk' (M''.subgroupOf A) ⟨u, hu⟩)) h
          have hmem1 : ⁅(x1 : G), (u : G)⁆ ∈ Z' :=
            ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' hu)).2 x1 x1.2
          have hmem2 : ⁅(x2 : G), (u : G)⁆ ∈ Z' :=
            ((mem_str83G4SecPart hfr hM.1 Z').mp (hAleM' hu)).2 x2 x2.2
          have hχ : χ ⟨⁅(x1 : G), (u : G)⁆, hmem1⟩ =
              χ ⟨⁅(x2 : G), (u : G)⁆, hmem2⟩ := by
            change (psi x1) ⟨u, hu⟩ = (psi x2) ⟨u, hu⟩ at h1
            simpa [psi] using h1
          have hprod : χ ⟨⁅(x1 : G), (u : G)⁆ * ⁅(x2 : G), (u : G)⁆⁻¹,
              Z'.mul_mem hmem1 (Z'.inv_mem hmem2)⟩ = 1 := by
            change χ (⟨⁅(x1 : G), (u : G)⁆, hmem1⟩ *
              (⟨⁅(x2 : G), (u : G)⁆, hmem2⟩ : ↥Z')⁻¹) = 1
            rw [map_mul, map_inv, hχ, mul_inv_cancel]
          have hZ'' : ⁅(x1 : G), (u : G)⁆ * ⁅(x2 : G), (u : G)⁆⁻¹ ∈ Z'' := by
            simpa using Subgroup.mem_subgroupOf.mp
              ((Subgroup.indexTwoCharacter_eq_one_iff hrel).mp hprod)
          rw [div_eq_mul_inv]
          rw [show ⁅(x1 : G) * (x2 : G)⁻¹, (u : G)⁆ =
              ⁅(x1 : G), (u : G)⁆ * ⁅(x2 : G), (u : G)⁆⁻¹ by
            rw [str83G4_phi_mul_left hfr (hAleQ hu) x1.2 (X.inv_mem x2.2),
              str83G4_phi_inv_left hfr (hAleQ hu) x2.2]]
          exact hZ''
      have hZmem : ((x1 : G) / (x2 : G)) ∈ Z := by
        have h : ((x1 : G) / (x2 : G)) ∈ str83G4XPart hfr hAleQ Z'' := hmemXA
        rw [hXA] at h
        simpa using h
      simpa [Subgroup.coe_div] using hZmem
    haveI : Finite (W →* C2) := Finite.of_injective _ DFunLike.coe_injective
    haveI : Finite (U →* C2) := Finite.of_injective _ DFunLike.coe_injective
    have hW2' : ∀ x : W, x ^ 2 = 1 := fun x => by simpa [pow_two] using hW2 x
    have hU2' : ∀ x : U, x ^ 2 = 1 := fun x => by simpa [pow_two] using hU2 x
    have hcard : Nat.card V ≤ Nat.card U :=
      ((Nat.card_le_card_of_injective Θbar hΘ).trans
        (CFSG.Quasithin.SteinbergCD.card_monoidHom_le_of_sq_eq_one hW2')).trans
        ((Nat.card_le_card_of_injective Ψbar hΨ).trans
          (CFSG.Quasithin.SteinbergCD.card_monoidHom_le_of_sq_eq_one hU2'))
    have hcardV : Nat.card V = M''.relIndex M' := by
      show Nat.card (↥M' ⧸ (M''.subgroupOf M')) = M''.relIndex M'
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
    have hcardU : Nat.card U = M''.relIndex A := by
      show Nat.card (↥A ⧸ (M''.subgroupOf A)) = M''.relIndex A
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
    have hleIndex : M''.relIndex M' ≤ M''.relIndex A := by
      rw [← hcardV, ← hcardU]
      exact hcard
    have hpos : M''.relIndex M' ≠ 0 := by
      rw [← hcardV]
      exact Nat.card_pos.ne'
    have hgeIndex : M''.relIndex A ≤ M''.relIndex M' :=
      Subgroup.relIndex_le_of_le_right hAleM' hpos
    have hEqIndex : M''.relIndex A = M''.relIndex M' := le_antisymm hgeIndex hleIndex
    have hM''leA : M'' ≤ A := le_sup_right
    have hposA : 0 < M''.relIndex A := by
      rw [← hcardU]
      exact Nat.card_pos
    have hArel : A.relIndex M' = 1 := by
      have htower := Subgroup.relIndex_mul_relIndex M'' A M' hM''leA hAleM'
      have h : M''.relIndex A * A.relIndex M' = M''.relIndex A := by
        rw [htower, hEqIndex]
      exact Nat.eq_of_mul_eq_mul_left hposA (by simpa using h)
    exact Subgroup.relIndex_eq_one.mp hArel
  ·
    have hAleM'' : A ≤ M'' := by
      intro c hc
      refine (mem_str83G4SecPart hfr hM.1 Z'').mpr ⟨hAleM hc, fun x hx => ?_⟩
      have hxXA : x ∈ str83G4XPart hfr hAleQ Z'' := by rw [hXA]; exact hx
      exact ((mem_str83G4XPart hfr hAleQ Z'').mp hxXA).2 c hc
    have hcommM'O_le : ⁅M', O⁆ ≤ M'' := le_sup_left.trans hAleM''
    have hM'leM'' : M' ≤ M'' := by
      intro u hu
      have huM : u ∈ M := hM'leM hu
      have huQ : u ∈ Q := hMleQ huM
      refine (mem_str83G4SecPart hfr hM.1 Z'').mpr ⟨huM, fun x hx => ?_⟩
      let C : Subgroup G := str83G4XFibre hfr huQ Z''
      have hZC : Z ≤ C := by
        intro z hz
        refine (mem_str83G4XFibre hfr huQ Z'').mpr ⟨str83G4_z1_le_x hfr hz, ?_⟩
        have huH : u ∈ H := hQH huQ
        have hzu : z * u = u * z :=
          Subgroup.mem_centralizer_iff.mp (str83G4_sup_le_centralizer_z1 hfr huH) z hz
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hzu]
        exact Z''.one_mem
      have hcommXOC : ⁅X, O⁆ ≤ C := by
        rw [Subgroup.commutator_le]
        intro x hx g hg
        have hgH : g ∈ H := hOH hg
        have hgxX : g * x * g⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (str83G4_sup_le_normalizer_x hfr hgH) x).mp hx
        have hxinvX : x⁻¹ ∈ X := X.inv_mem hx
        have hgx : ⁅g, x⁆ ∈ X := by
          have e : ⁅g, x⁆ = (g * x * g⁻¹) * x⁻¹ := by
            simp only [commutatorElement_def]
          rw [e]
          exact X.mul_mem hgxX hxinvX
        have hgx' : ⁅x, g⁆ ∈ X := by
          rw [show ⁅x, g⁆ = ⁅g, x⁆⁻¹ by
            rw [← commutatorElement_inv x g, inv_inv]]
          exact X.inv_mem hgx
        have hgu : ⁅g, u⁆ ∈ M'' := by
          have h1 : ⁅u, g⁆ ∈ ⁅M', O⁆ := Subgroup.commutator_mem_commutator hu hg
          have h2 := (⁅M', O⁆).inv_mem h1
          rw [commutatorElement_inv] at h2
          exact hcommM'O_le h2
        have hguQ : ⁅g, u⁆ ∈ Q := hM''leQ hgu
        have hkey : ∀ y ∈ X, ⁅g⁻¹ * y * g, u⁆ = ⁅y, ⁅g, u⁆⁆ * ⁅y, u⁆ := by
          intro y hy
          rw [← str83G4_phi_conj hfr hgH (hM'leQ hu) hy]
          rw [show g * u * g⁻¹ = ⁅g, u⁆ * u by
            simp only [commutatorElement_def]
            group]
          rw [str83G4_phi_mul_right hfr hguQ (hM'leQ hu) hy]
        have hconj_rel : ⁅x, u⁆ = ⁅g * x * g⁻¹, ⁅g, u⁆⁆ * ⁅g * x * g⁻¹, u⁆ := by
          have h := hkey (g * x * g⁻¹) hgxX
          rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
        have hzx : ⁅g * x * g⁻¹, ⁅g, u⁆⁆ ∈ Z'' :=
          ((mem_str83G4SecPart hfr hM.1 Z'').mp hgu).2 (g * x * g⁻¹) hgxX
        have hconj_eq : ⁅g * x * g⁻¹, u⁆ = (⁅g * x * g⁻¹, ⁅g, u⁆⁆)⁻¹ * ⁅x, u⁆ := by
          rw [hconj_rel]
          group
        have hcommgx : ⁅⁅g, x⁆, u⁆ = ⁅g * x * g⁻¹, u⁆ * ⁅x⁻¹, u⁆ := by
          rw [show ⁅g, x⁆ = (g * x * g⁻¹) * x⁻¹ by
            simp only [commutatorElement_def]]
          exact str83G4_phi_mul_left hfr (hM'leQ hu) hgxX hxinvX
        have hfinal : ⁅⁅g, x⁆, u⁆ = (⁅g * x * g⁻¹, ⁅g, u⁆⁆)⁻¹ := by
          rw [hcommgx, hconj_eq, str83G4_phi_inv_left hfr (hM'leQ hu) hx]
          group
        have hfin' : ⁅⁅x, g⁆, u⁆ = ⁅g * x * g⁻¹, ⁅g, u⁆⁆ := by
          rw [show ⁅x, g⁆ = ⁅g, x⁆⁻¹ by
              rw [← commutatorElement_inv x g, inv_inv],
            str83G4_phi_inv_left hfr (hM'leQ hu) hgx, hfinal, inv_inv]
        refine (mem_str83G4XFibre hfr huQ Z'').mpr ⟨hgx', ?_⟩
        rw [hfin']
        exact hzx
      have hXeq : X = ⁅X, O⁆ ⊔ Z :=
        (str83N_eq_x_of_isChiefStep hfr hXstep hXnc).symm
      have hXleC : X ≤ C := by
        rw [hXeq]
        exact sup_le hcommXOC hZC
      exact ((mem_str83G4XFibre hfr huQ Z'').mp (hXleC hx)).2
    exact hM'leM''.trans le_sup_right


theorem str83G4_eq_commutator_sup_y_of_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S))
    {M : Subgroup G} (hM : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) M)
    (hYM : str83Y L1 L2 S ≤ M) :
    M = ⁅M, oTwoUpper (L1 ⊔ S)⁆ ⊔ str83Y L1 L2 S := by
  classical
  let H := L1 ⊔ S
  let Q := Q1 L1 L2 S
  let Z := Z1 L1 L2 S
  let Y := str83Y L1 L2 S
  let O := oTwoUpper H
  have hZ1ea : IsElemAbelian 2 Z := B2F.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hZ1p : IsPGroup 2 Z := hZ1ea.isPGroup
  have key : ∀ Z' : Subgroup G, Z' ≤ Z →
      str83G4SecPart hfr hM.1 Z' ≤ ⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔ Y := by
    suffices h : ∀ n : ℕ, ∀ Z' : Subgroup G, Z' ≤ Z → Nat.card Z' = n →
        str83G4SecPart hfr hM.1 Z' ≤ ⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔ Y by
      intro Z' hZ'
      exact h (Nat.card Z') Z' hZ' rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Z' hZ' hcard
      by_cases hbot : Z' = ⊥
      · subst hbot
        have h0 : str83G4SecPart hfr hM.1 (⊥ : Subgroup G) = Y :=
          str83G4SecPart_bot hfr hM.1 hYM
        rw [h0]
        exact le_sup_right
      · haveI : Nontrivial ↥Z' := (Subgroup.nontrivial_iff_ne_bot Z').mpr hbot
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨B, hBidx⟩ :=
          CFSG.SolvableHall.exists_index_eq_prime (p := 2) (A := ↥Z') (hZ1p.to_le hZ')
        let Z'' : Subgroup G := B.map Z'.subtype
        have hZ''Z' : Z'' ≤ Z' := Subgroup.map_subtype_le B
        have hZ'' : Z'' ≤ Z := hZ''Z'.trans hZ'
        have hrel : Z''.relIndex Z' = 2 := by
          have hsub : Z''.subgroupOf Z' = B := by
            rw [← Subgroup.map_subtype_inj (H := Z')]
            rw [Subgroup.map_subgroupOf_eq_of_le hZ''Z']
          rw [Subgroup.relIndex, hsub]
          exact hBidx
        have hcardZ'' : Nat.card Z'' < n := by
          have hmul := Subgroup.relIndex_mul_card Z'' Z'
          rw [hrel, inf_eq_left.mpr hZ''Z', hcard] at hmul
          have hpos : 0 < Nat.card Z'' := Nat.card_pos
          omega
        have hclaim := str83G4SecPart_le_commutator_sup hfr hXstep hXnc hM hYM hZ' hZ''Z' hrel
        have hrec := ih (Nat.card Z'') hcardZ'' Z'' hZ'' rfl
        have hmono : str83G4SecPart hfr hM.1 Z'' ≤
            ⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔ Y :=
          hrec.trans (sup_le
            ((Subgroup.commutator_mono (str83G4SecPart_mono hfr hM.1 hZ''Z') le_rfl).trans
              le_sup_left) le_sup_right)
        calc str83G4SecPart hfr hM.1 Z'
            ≤ ⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔ str83G4SecPart hfr hM.1 Z'' := hclaim
          _ ≤ ⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔
              (⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔ Y) := sup_le_sup le_rfl hmono
          _ = ⁅str83G4SecPart hfr hM.1 Z', O⁆ ⊔ Y := by rw [← sup_assoc, sup_idem]
  have hMZ : str83G4SecPart hfr hM.1 Z = M := str83G4SecPart_z1 hfr hM.1
  have hle : M ≤ ⁅M, O⁆ ⊔ Y := by
    rw [← hMZ]
    exact key Z le_rfl
  refine le_antisymm hle (sup_le ?_ hYM)
  exact F112W.commutator_le_self_of_le_normalizer
    ((oTwoUpper_le H).trans (D14.le_normalizer_of_isNormalIn hM))

theorem str83G4_isChiefStep_q1_y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) (Q1 L1 L2 S) := by
  classical
  have hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S) :=
    str83G4_isChiefStep_x_z1 hfr d hX hB
  have hXnc : ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S) :=
    str83G4_not_twoResidual_le_centralizerMod_z1 hfr d hX hB
  let H := L1 ⊔ S
  let Q := Q1 L1 L2 S
  let Y := str83Y L1 L2 S
  let O := oTwoUpper H
  have hQH : Q ≤ H := (str83G4_q1_le_s hfr).trans le_sup_right
  have hQn : IsNormalIn H Q Q := by
    refine ⟨le_rfl, ?_⟩
    intro g hg u hu
    have hp : Q = pCoreOf 2 H := (str83G4_pCoreOf_sup_left hfr).symm
    rw [hp] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) u).mp hu
  have hYn : IsNormalIn H Q Y := str83G4_isNormalIn_y hfr
  have hYQ : Y ≤ Q := inf_le_left
  have hYlt : Y < Q := by
    refine lt_of_le_of_ne hYQ fun hEq => ?_
    apply str83G4_not_twoResidual_le_centralizerMod_y_q1 hfr d hX
    have hYeqQ : str83Y L1 L2 S = Q := by simpa [Y] using hEq
    rw [hYeqQ]
    intro g hg
    have hgQ : g ∈ Subgroup.normalizer (Q : Set G) :=
      D14.le_normalizer_of_isNormalIn hQn (twoResidual_le H hg)
    refine ⟨twoResidual_le H hg, hgQ, fun u hu => ?_⟩
    have hgu : g * u * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hgQ u).mp hu
    exact Q.mul_mem hgu (Q.inv_mem hu)
  refine ⟨hQn, hYn, hYlt, ?_⟩
  intro K hK hYK hKQ
  by_cases hKY : K = Y
  · exact Or.inl hKY
  · right
    obtain ⟨c, hserYK⟩ := F112W.exists_isChiefSeriesBetween hYn K hK hYK
    obtain ⟨b, hserKQ⟩ := F112W.exists_isChiefSeriesBetween hK Q hQn hKQ
    have hserYQ : F112W.IsChiefSeriesBetween H Q Y Q (c + b) := hserYK.trans hserKQ
    have hcb : c + b = 1 := str83G4_chiefSeriesBetween_y_q1 hfr d hX hB hserYQ
    have hQcore : Q ≤ pCoreOf 2 H := (str83G4_pCoreOf_sup_left hfr).symm.le
    rcases Nat.eq_zero_or_pos c with hc | hc
    · exfalso
      apply hKY
      have hcomm : ⁅K, O⁆ ≤ Y :=
        (F112W.isChiefSeriesBetween_zero_iff hQH hQcore hYn hK hYK).mp (hc ▸ hserYK)
      have heq := str83G4_eq_commutator_sup_y_of_le hfr hXstep hXnc hK hYK
      apply le_antisymm
      · rw [heq]
        exact sup_le hcomm le_rfl
      · exact hYK
    · have hb : b = 0 := by omega
      have hcomm : ⁅Q, O⁆ ≤ K :=
        (F112W.isChiefSeriesBetween_zero_iff hQH hQcore hK hQn hKQ).mp (hb ▸ hserKQ)
      have heq := str83G4_eq_commutator_sup_y_of_le hfr hXstep hXnc hQn hYQ
      have hQleK : Q ≤ K := by
        rw [heq]
        exact sup_le hcomm hYK
      exact le_antisymm hKQ (by simpa [Q] using hQleK)

theorem str83G4_isSzNaturalSection_q1_y
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsSzNaturalSection (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) a := by
  have hstep := str83G4_isChiefStep_q1_y hfr d hX hB
  have hquad := str83G4_commutator_commutator_q1_conjugate_x_le_y hfr d hX
  have hnc := str83G4_not_twoResidual_le_centralizerMod_y_q1 hfr d hX
  exact str83G4_isSzNaturalSection_of_quadratic_chiefStep hfr
    (str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB) le_rfl hstep hquad hnc

theorem str83G4_relIndex_y_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    (str83Y L1 L2 S).relIndex (Q1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 4 :=
  relIndex_eq_of_isSzNaturalSection
    (str83G4_isSzNaturalSection_q1_y hfr d hX hB)

end CFSG.Quasithin.Stroth

end
