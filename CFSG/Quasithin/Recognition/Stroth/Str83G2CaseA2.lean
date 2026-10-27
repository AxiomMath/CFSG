module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseA
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexM6
public import CFSG.Quasithin.MS93.S52iChief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.Ree CFSG.SolvableHall CFSG.LieType.BorelTits
open CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

@[expose] def str83CaseAR (L1 L2 S : Subgroup G) : Subgroup G :=
  Q1 L1 L2 S ⊓ Q2 L1 L2 S

@[expose] def str83CaseAR0 (L1 L2 S : Subgroup G) (w : G) : Subgroup G :=
  str83CaseAR L1 L2 S ⊓ conjugate (str83CaseAR L1 L2 S) w

private theorem caseA_R_eq_centralizer (F : Str83CaseAFrame L1 L2 S a) :
    str83CaseAR L1 L2 S =
      Q2 L1 L2 S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  rw [str83CaseAR]
  symm
  calc Q2 L1 L2 S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)
      = (S ⊓ Q2 L1 L2 S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
        rw [inf_eq_right.mpr F.hQ2S]
    _ = S ⊓ (Q2 L1 L2 S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) := by rw [inf_assoc]
    _ = S ⊓ (Subgroup.centralizer (Z1 L1 L2 S : Set G) ⊓ Q2 L1 L2 S) := by
        rw [inf_comm (Q2 L1 L2 S) (Subgroup.centralizer (Z1 L1 L2 S : Set G))]
    _ = (S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) ⊓ Q2 L1 L2 S := by rw [inf_assoc]
    _ = Q1 L1 L2 S ⊓ Q2 L1 L2 S := by rw [F.hF6]

private theorem conjugate_centralizer_eq (V : Subgroup G) (w : G) :
    conjugate (Subgroup.centralizer (V : Set G)) w =
      Subgroup.centralizer ((conjugate V w : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx y hy
    have hx' : w * x * w⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      (mem_conjugate_iff (Subgroup.centralizer (V : Set G)) w x).mp hx
    have hy' : w * y * w⁻¹ ∈ V := (mem_conjugate_iff V w y).mp hy
    have h1 := (Subgroup.mem_centralizer_iff.mp hx') (w * y * w⁻¹) hy'
    calc y * x = w⁻¹ * ((w * y * w⁻¹) * (w * x * w⁻¹)) * w := by group
      _ = w⁻¹ * ((w * x * w⁻¹) * (w * y * w⁻¹)) * w := by rw [h1]
      _ = x * y := by group
  · intro hx
    rw [mem_conjugate_iff, Subgroup.mem_centralizer_iff]
    intro v hv
    have hy : w⁻¹ * v * w ∈ conjugate V w := by
      apply (mem_conjugate_iff V w (w⁻¹ * v * w)).mpr
      rw [show w * (w⁻¹ * v * w) * w⁻¹ = v by group]
      exact hv
    have h1 := hx (w⁻¹ * v * w) hy
    exact (calc (w * x * w⁻¹) * v = w * (x * (w⁻¹ * v * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * v * w) * x) * w⁻¹ := by rw [← h1]
      _ = v * (w * x * w⁻¹) := by group).symm

private theorem caseA_conjugate_R_eq_centralizer
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    conjugate (str83CaseAR L1 L2 S) D.w =
      Q2 L1 L2 S ⊓
        Subgroup.centralizer ((conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G) := by
  have hQ2norm : D.w ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
    have hQ2eq : Q2 L1 L2 S = pCoreOf 2 (u3H L1 L2 S) := (str86_pCoreOf_u3H F.hF).symm
    have hH : u3H L1 L2 S = L2 ⊔ S := by rw [u3H, ← F.hsup2]
    rw [hQ2eq]
    exact le_normalizer_pCoreOf 2 (u3H L1 L2 S) (hH ▸ D.hwH2)
  rw [caseA_R_eq_centralizer F]
  change (Q2 L1 L2 S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)).map
      (MulAut.conj D.w⁻¹).toMonoidHom =
    Q2 L1 L2 S ⊓
      Subgroup.centralizer ((conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G)
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj D.w⁻¹).injective]
  rw [show Subgroup.map (MulAut.conj D.w⁻¹).toMonoidHom (Q2 L1 L2 S) = Q2 L1 L2 S from by
        simpa [conjugate] using conjugate_eq_self_of_mem_normalizer hQ2norm,
      show Subgroup.map (MulAut.conj D.w⁻¹).toMonoidHom
          (Subgroup.centralizer (Z1 L1 L2 S : Set G)) =
          Subgroup.centralizer ((conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G) from by
        simpa [conjugate] using conjugate_centralizer_eq (Z1 L1 L2 S) D.w]

private theorem centralizer_sup_eq (V W : Subgroup G) :
    Subgroup.centralizer ((V ⊔ W : Subgroup G) : Set G) =
      Subgroup.centralizer (V : Set G) ⊓ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_setOf_eq, SetLike.mem_coe,
    Set.mem_union]
  constructor
  · intro h
    exact ⟨fun v hv => h v (Or.inl hv), fun w hw => h w (Or.inr hw)⟩
  · rintro ⟨hV, hW⟩ z (hz | hz)
    · exact hV z hz
    · exact hW z hz

private theorem caseA_Q2_normal_u3H
    (F : Str83CaseAFrame L1 L2 S a) :
    u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
  have hQ2eq : Q2 L1 L2 S = pCoreOf 2 (u3H L1 L2 S) := (str86_pCoreOf_u3H F.hF).symm
  rw [hQ2eq]
  exact le_normalizer_pCoreOf 2 (u3H L1 L2 S)

private theorem caseA_Q2_normalizes_conjugate_V
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    Q2 L1 L2 S ≤
      Subgroup.normalizer ((conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G) := by
  have hnormmap : conjugate (Subgroup.normalizer (Z1 L1 L2 S : Set G)) D.w =
      Subgroup.normalizer ((conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G) := by
    simpa [conjugate] using
      (Subgroup.map_equiv_normalizer_eq (Z1 L1 L2 S) (MulAut.conj D.w⁻¹))
  rw [← hnormmap]
  have hQ2conj : conjugate (Q2 L1 L2 S) D.w = Q2 L1 L2 S := by
    have hH : u3H L1 L2 S = L2 ⊔ S := by rw [u3H, ← F.hsup2]
    exact conjugate_eq_self_of_mem_normalizer (caseA_Q2_normal_u3H F (hH ▸ D.hwH2))
  calc Q2 L1 L2 S = conjugate (Q2 L1 L2 S) D.w := hQ2conj.symm
    _ ≤ conjugate (Subgroup.normalizer (Z1 L1 L2 S : Set G)) D.w :=
        Subgroup.map_mono (F.hQ2S.trans F.hSnormV)

theorem str83_caseA_sup_conjugate_normal
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    u3H L1 L2 S ≤
      Subgroup.normalizer
        ((Z1 L1 L2 S ⊔ conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G) := by
  classical
  set V : Subgroup G := Z1 L1 L2 S with hV
  set U : Subgroup G := V ⊔ conjugate V D.w with hU
  have hH : u3H L1 L2 S = L2 ⊔ S := by rw [u3H, ← F.hsup2]
  have hQ2conj : conjugate (Q2 L1 L2 S) D.w = Q2 L1 L2 S := by
    exact conjugate_eq_self_of_mem_normalizer (caseA_Q2_normal_u3H F (hH ▸ D.hwH2))
  have hQ2V : Q2 L1 L2 S ≤ Subgroup.normalizer (V : Set G) :=
    F.hQ2S.trans F.hSnormV
  have hQ2U : Q2 L1 L2 S ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hQ2V (caseA_Q2_normalizes_conjugate_V F D)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup V (conjugate V D.w))
  have hUU : U ≤ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer (H := U)
  have hVU : V ≤ U := by rw [hU]; exact le_sup_left
  have hVwU : conjugate V D.w ≤ U := by rw [hU]; exact le_sup_right
  have hUQ2 : U ⊔ Q2 L1 L2 S = u3H L1 L2 S := by
    apply le_antisymm
    · have hVU : V ≤ u3H L1 L2 S := F.hVS.trans (by rw [hH]; exact le_sup_right)
      have hVwU : conjugate V D.w ≤ u3H L1 L2 S :=
        (Subgroup.map_mono F.hVS).trans (by
          rw [hH, ← D.hwTop]
          exact le_sup_right)
      have hQ2U3 : Q2 L1 L2 S ≤ u3H L1 L2 S :=
        F.hQ2S.trans (by rw [hH]; exact le_sup_right)
      exact sup_le (sup_le hVU hVwU) hQ2U3
    · rw [hH, ← D.hwTop]
      refine sup_le ?_ ?_
      · calc S = V ⊔ Q2 L1 L2 S := (str83_caseA_sup_Q2_eq_S F D).symm
          _ ≤ U ⊔ Q2 L1 L2 S := sup_le_sup_right hVU (Q2 L1 L2 S)
      · calc conjugate S D.w = conjugate (V ⊔ Q2 L1 L2 S) D.w := by
              rw [str83_caseA_sup_Q2_eq_S F D]
          _ = conjugate V D.w ⊔ conjugate (Q2 L1 L2 S) D.w := by
              simp only [conjugate]
              rw [Subgroup.map_sup]
          _ = conjugate V D.w ⊔ Q2 L1 L2 S := by rw [hQ2conj]
          _ ≤ U ⊔ Q2 L1 L2 S := sup_le_sup_right hVwU (Q2 L1 L2 S)
  rw [← hUQ2]
  exact sup_le hUU hQ2U

private theorem caseA_w_normalizes_Q2
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    D.w ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
  have hH : u3H L1 L2 S = L2 ⊔ S := by rw [u3H, ← F.hsup2]
  exact caseA_Q2_normal_u3H F (hH ▸ D.hwH2)

theorem str83_caseA_R0_eq_centralizer
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    str83CaseAR0 L1 L2 S D.w =
      Q2 L1 L2 S ⊓
        Subgroup.centralizer
          ((Z1 L1 L2 S ⊔ conjugate (Z1 L1 L2 S) D.w : Subgroup G) : Set G) := by
  rw [str83CaseAR0, caseA_conjugate_R_eq_centralizer F D, caseA_R_eq_centralizer F,
    centralizer_sup_eq]
  ac_rfl

theorem str83_caseA_R0_normal
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    u3H L1 L2 S ≤ Subgroup.normalizer (str83CaseAR0 L1 L2 S D.w : Set G) := by
  rw [str83_caseA_R0_eq_centralizer F D]
  refine Subgroup.le_normalizer_inf (caseA_Q2_normal_u3H F) ?_
  exact (str83_caseA_sup_conjugate_normal F D).trans
    (CFSG.Quasithin.normalizer_le_normalizer_centralizer
      (Z1 L1 L2 S ⊔ conjugate (Z1 L1 L2 S) D.w))

private theorem caseA_R0_le_R (w : G) : str83CaseAR0 L1 L2 S w ≤ str83CaseAR L1 L2 S :=
  inf_le_left

theorem str83_caseA_fixed_point_free_mod_R0
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {q : G}
    (hqQ2 : q ∈ Q2 L1 L2 S)
    (hfix : ∀ d ∈ D.D2, d * q * d⁻¹ * q⁻¹ ∈ str83CaseAR0 L1 L2 S D.w) :
    q ∈ str83CaseAR0 L1 L2 S D.w := by
  classical
  have hwH : D.w ∈ u3H L1 L2 S := by
    rw [show u3H L1 L2 S = L2 ⊔ S by rw [u3H, ← F.hsup2]]
    exact D.hwH2
  obtain ⟨d0, hd0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (str83_caseA_D2_ne_bot F D)
  have hd0D : (d0 : G) ∈ D.D2 := d0.2
  have hd0neG : (d0 : G) ≠ 1 :=
    fun h => hd0ne (Subtype.ext (by simpa using h))
  have hR0leR : str83CaseAR0 L1 L2 S D.w ≤ str83CaseAR L1 L2 S := caseA_R0_le_R D.w
  have hqR : q ∈ str83CaseAR L1 L2 S := by
    exact str83_caseA_centralizer_mod_R F D hd0D hd0neG hqQ2 (hR0leR (hfix (d0 : G) hd0D))
  set q' : G := D.w * q * D.w⁻¹ with hq'def
  have hq'Q2 : q' ∈ Q2 L1 L2 S := by
    have h := (Subgroup.mem_normalizer_iff.mp (caseA_w_normalizes_Q2 F D) q).mp hqQ2
    simpa [hq'def] using h
  have hq'R : q' ∈ str83CaseAR L1 L2 S := by
    have hw1 : D.w⁻¹ ∈ u3H L1 L2 S := (u3H L1 L2 S).inv_mem hwH
    have hd0' : D.w⁻¹ * (d0 : G) * D.w⁻¹⁻¹ ∈ D.D2 := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ D.hwD2) (d0 : G)).mp hd0D
      simpa using this
    have hinner := hfix (D.w⁻¹ * (d0 : G) * D.w⁻¹⁻¹) hd0'
    have hconj := (Subgroup.mem_normalizer_iff.mp
      (str83_caseA_R0_normal F D hwH) _).mp hinner
    change D.w * (D.w⁻¹ * (d0 : G) * D.w⁻¹⁻¹ * q *
      (D.w⁻¹ * (d0 : G) * D.w⁻¹⁻¹)⁻¹ * q⁻¹) * D.w⁻¹ ∈ str83CaseAR0 L1 L2 S D.w at hconj
    have heq : (d0 : G) * q' * (d0 : G)⁻¹ * q'⁻¹ =
        D.w * ((D.w⁻¹ * (d0 : G) * D.w⁻¹⁻¹) * q *
          (D.w⁻¹ * (d0 : G) * D.w⁻¹⁻¹)⁻¹ * q⁻¹) * D.w⁻¹ := by
      rw [hq'def]
      group
    exact str83_caseA_centralizer_mod_R F D hd0D hd0neG hq'Q2 (by rw [heq]; exact hR0leR hconj)
  exact ⟨hqR, (mem_conjugate_iff (str83CaseAR L1 L2 S) D.w q).mpr (by simpa [hq'def] using hq'R)⟩

theorem str83_caseA_chiefStep_noncentral
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {L N : Subgroup G}
    (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L N)
    (hR0L : str83CaseAR0 L1 L2 S D.w ≤ L) :
    ¬ IsCentralStep (u3H L1 L2 S) L N := by
  classical
  intro hcent
  have hD2H : D.D2 ≤ u3H L1 L2 S := by
    rw [show u3H L1 L2 S = L2 ⊔ S by rw [u3H, ← F.hsup2]]
    exact (D.hD2hall.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
  have hQ2H : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hNQ2 : N ≤ Q2 L1 L2 S := hstep.1.1
  have hLQ2 : L ≤ Q2 L1 L2 S := hstep.2.1.1
  have hHN : u3H L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hHL : u3H L1 L2 S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  let A : Type := ↥D.D2
  let G₁ : Type := ↥N
  haveI : Subgroup.Normalizes D.D2 N := ⟨hD2H.trans hHN⟩
  letI : MulDistribMulAction A G₁ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D.D2 N (hD2H.trans hHN)
  let Lsub : Subgroup G₁ := L.subgroupOf N
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hNQ2.trans (hQ2H.trans hHL)
  haveI : Lsub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNL
  have hLinv : CFSG.IsInvariant A G₁ Lsub := by
    apply CFSG.SolvableHall.isInvariant_of_forall_smul_mem
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hHL (hD2H a.2)) (x : G)).mp hx
  have hLp0 : IsPGroup 2 L :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le hLQ2
  have hLp : IsPGroup 2 ↥Lsub :=
    hLp0.of_equiv (Subgroup.subgroupOfEquivOfLe hstep.2.2.1.le).symm
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥Lsub := hLp.isNilpotent
  haveI : Group.IsSolvable ↥Lsub := inferInstance
  obtain ⟨k, hk⟩ := hLp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card ↥Lsub) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Odd.coprime_two_right D.hD2odd)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting
    (A := A) (G := G₁) Lsub hLinv (inferInstance : Group.IsSolvable ↥Lsub) hcop
  have hbot : (fixedPointSubgroup A G₁).map (QuotientGroup.mk' Lsub) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk x = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    apply hR0L
    apply str83_caseA_fixed_point_free_mod_R0 F D (hNQ2 x.2)
    intro d hd
    have hxd := (FixedPoints.mem_subgroup A G₁ x).mp hx ⟨d, hd⟩
    have hxd' : (d : G) * (x : G) * (d : G)⁻¹ = (x : G) := by
      have h := congrArg (fun y : G₁ => (y : G)) hxd
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h
      exact h
    have hcomm : d * (x : G) * d⁻¹ * (x : G)⁻¹ = 1 := by
      rw [hxd', mul_inv_cancel]
    rw [hcomm]
    exact (str83CaseAR0 L1 L2 S D.w).one_mem
  have htop : fixedPointSubgroup A (G₁ ⧸ Lsub) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [FixedPoints.mem_subgroup]
    intro a
    induction x using QuotientGroup.induction_on with
    | H n =>
      rw [MulAction.Quotient.smul_mk]
      have hmemL : ((a • n) * n⁻¹ : G₁) ∈ Lsub := by
        rw [Subgroup.mem_subgroupOf]
        change ((a : G) * (n : G) * (a : G)⁻¹) * (n : G)⁻¹ ∈ L
        exact hcent (a : G) (hD2H a.2) (n : G) n.2
      have hq : QuotientGroup.mk ((a • n) * n⁻¹ : G₁) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmemL
      calc QuotientGroup.mk (a • n)
          = QuotientGroup.mk (((a • n) * n⁻¹) * n : G₁) := by
              rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = QuotientGroup.mk ((a • n) * n⁻¹ : G₁) * QuotientGroup.mk n := by
              rw [QuotientGroup.mk_mul]
        _ = (1 : G₁ ⧸ Lsub) * QuotientGroup.mk n := by rw [hq]
        _ = QuotientGroup.mk n := one_mul (QuotientGroup.mk n)
  have hLsub_ne_top : Lsub ≠ ⊤ := by
    intro h
    have hNL : N ≤ L := by
      intro x hx
      have hmem : (⟨x, hx⟩ : G₁) ∈ Lsub := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    exact (lt_irrefl N) (lt_of_le_of_lt hNL hstep.2.2.1)
  haveI : Nontrivial (G₁ ⧸ Lsub) := QuotientGroup.nontrivial_iff.mpr hLsub_ne_top
  rw [htop, hbot] at hlift
  exact top_ne_bot hlift

private theorem suzukiU_not_isMulCommutative
    {K : Type} [Field K] [Finite K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ IsMulCommutative (suzukiU a K) := by
  intro hcomm
  have hbot : commutator ↥(suzukiU a K) = ⊥ :=
    (commutator_eq_bot_iff (↥(suzukiU a K))).mpr hcomm
  have hz0 : suzukiSElt a K 0 (1 : K) ∈ suzukiZ0 a K :=
    (mem_suzukiZ0_iff hK).mpr ⟨1, rfl⟩
  have hU : suzukiSElt a K 0 (1 : K) ∈ suzukiU a K :=
    suzukiZ0_le_suzukiU hz0
  have hmem : (⟨suzukiSElt a K 0 (1 : K), hU⟩ : suzukiU a K) ∈
      (suzukiZ0 a K).subgroupOf (suzukiU a K) :=
    Subgroup.mem_subgroupOf.mpr hz0
  rw [← commutator_suzukiU hK ha, hbot] at hmem
  have h1 : (⟨suzukiSElt a K 0 (1 : K), hU⟩ : suzukiU a K) = 1 :=
    Subgroup.mem_bot.mp hmem
  have hcoe : suzukiSElt a K 0 (1 : K) = suzukiSElt a K 0 (0 : K) := by
    simpa [suzukiSElt_zero_zero hK] using congrArg Subtype.val h1
  exact one_ne_zero ((suzukiSElt_inj.mp hcoe).2)

private theorem szSbar_comm_of_quotient_comm
    [(Q1 L1 L2 S).subgroupOf S |>.Normal]
    (F : Str83CaseAFrame L1 L2 S a)
    (hcomm : IsMulCommutative (↥S ⧸ (Q1 L1 L2 S).subgroupOf S)) :
    IsMulCommutative (szSbar L1 L2 S) := by
  classical
  let H1 : Subgroup G := L1 ⊔ S
  have hS1 : H1 = L1 ⊔ Q1 L1 L2 S := F.hsup1
  have hpCore : pCoreOf 2 H1 = Q1 L1 L2 S := by
    rw [hS1]
    exact pCoreOf_sup_pCoreOf F.hF.1
  let φ : ↥S →* szSbar L1 L2 S :=
    { toFun := fun s =>
        ⟨QuotientGroup.mk (Subgroup.inclusion (le_sup_right : S ≤ H1) s),
          Subgroup.mem_map_of_mem _
            (Subgroup.mem_subgroupOf.mpr s.2)⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (QuotientGroup.mk' (pCore 2 ↥H1))
      map_mul' := by
        intro x y
        apply Subtype.ext
        simpa [Subgroup.inclusion] using
          (QuotientGroup.mk_mul (pCore 2 ↥H1)
            (Subgroup.inclusion (le_sup_right : S ≤ H1) x)
            (Subgroup.inclusion (le_sup_right : S ≤ H1) y)) }
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    have hSP1 : S ≤ P1 L1 L2 S :=
      (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
    exact hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hker : φ.ker = (Q1 L1 L2 S).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hval : (φ s : oTwoQuot ↥H1) = 1 := congrArg Subtype.val h
      have h' : (Subgroup.inclusion (le_sup_right : S ≤ H1) s) ∈ pCore 2 ↥H1 :=
        (QuotientGroup.eq_one_iff _).mp hval
      rw [← CFSG.openPCoreOf_subgroupOf 2 H1] at h'
      have h'' : (s : G) ∈ pCoreOf 2 H1 := Subgroup.mem_subgroupOf.mp h'
      rwa [hpCore] at h''
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr (by
        rw [← CFSG.openPCoreOf_subgroupOf 2 H1, hpCore]
        exact Subgroup.mem_subgroupOf.mpr h)
  let e1 : (↥S ⧸ φ.ker) ≃* szSbar L1 L2 S :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let e0 : (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) ≃* (↥S ⧸ φ.ker) :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv (e0.trans e1) hcomm

private theorem caseA_Q1_relIndex_S
    (F : Str83CaseAFrame L1 L2 S a) :
    (Q1 L1 L2 S).relIndex S = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨e⟩ := F.hSz
  let Q : Subgroup G := Q1 L1 L2 S
  let P : Subgroup G := P1 L1 L2 S
  let S1 : Subgroup G := S ⊓ L1
  change Q.relIndex S = (2 ^ (2 * a + 1)) ^ 2
  have hS1P : S1 ≤ P := (inf_le_right : S ⊓ L1 ≤ L1).trans le_sup_left
  have hS1N : S1 ≤ Subgroup.normalizer (Q : Set G) :=
    hS1P.trans (le_normalizer_pCoreOf 2 P)
  have hsup : S1 ⊔ Q = S := F.hS1.symm
  have hrel : Q.relIndex S = Q.relIndex S1 := by
    have h := CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
      (A := S1) (B := Q) hS1N
    rwa [hsup] at h
  rw [hrel]
  rw [← Subgroup.inf_relIndex_right Q S1]
  have hinf : Q ⊓ S1 = pCoreOf 2 L1 := by
    have h1 : Q ⊓ S1 = L1 ⊓ Q := by
      change Q ⊓ (S ⊓ L1) = L1 ⊓ Q
      rw [inf_comm Q (S ⊓ L1), inf_assoc,
        inf_eq_right.mpr (show L1 ⊓ Q ≤ S from inf_le_right.trans F.hQ1S)]
    rw [h1]
    exact str86_inf_p1_q1 (L1 := L1) (L2 := L2) (S := S) F.hF
  rw [hinf]
  exact relIndex_pCoreOf_sylow_sz F.ha e F.hF.1.h1.sylow

theorem str83_caseA_R_relIndex_Q2
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    (str83CaseAR L1 L2 S).relIndex (Q2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ2NQ1 : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    F.hQ2S.trans hSNQ1
  rw [str83CaseAR, Subgroup.inf_relIndex_right]
  rw [← CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hQ2NQ1]
  rw [sup_comm, F.hT2, caseA_Q1_relIndex_S F]

private theorem caseA_relIndex_centralizer_le
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {t : G}
    (htV : t ∈ Z1 L1 L2 S) :
    (Subgroup.centralizer (Subgroup.zpowers t)).relIndex (Q2 L1 L2 S) ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
  have hRleC : str83CaseAR L1 L2 S ≤
      Q2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    have hx' : x ∈ Q2 L1 L2 S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
      rwa [← caseA_R_eq_centralizer F]
    refine ⟨hx'.1, ?_⟩
    change x ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.mp hx'.2) t htV
  have hEq : (Subgroup.centralizer (Subgroup.zpowers t)).relIndex (Q2 L1 L2 S) =
      (Q2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Q2 L1 L2 S) := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (Subgroup.zpowers t))
      (Q2 L1 L2 S)]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm]
  rw [hEq]
  exact (Subgroup.relIndex_le_of_le_left hRleC (D15Proof.relIndex_ne_zero _ _)).trans
    (le_of_eq (str83_caseA_R_relIndex_Q2 F D))

theorem str83_caseA_chiefSeries_count_le_two
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {c : ℕ}
    (hser : CFSG.Quasithin.F112W.IsChiefSeriesBetween
      (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) (Q2 L1 L2 S) c) :
    c ≤ 2 := by
  classical
  have ha := F.ha
  obtain ⟨t, htV, htQ2⟩ := Set.not_subset.mp F.hA
  have htS : t ∈ S := F.hVS htV
  have hSleH : S ≤ u3H L1 L2 S := by
    rw [show u3H L1 L2 S = L2 ⊔ S by rw [u3H, ← F.hsup2]]
    exact le_sup_right
  have htH : t ∈ u3H L1 L2 S := hSleH htS
  have hsq : t * t = 1 := by
    simpa [pow_two] using F.hVea.2 t htV
  have ht2 : t * t ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [str86_pCoreOf_u3H F.hF, hsq]
    exact (Q2 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 (u3H L1 L2 S) := by
    rw [str86_pCoreOf_u3H F.hF]
    exact htQ2
  have hQnormal : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) (Q2 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (caseA_Q2_normal_u3H F)
  obtain ⟨cQ, hserQ⟩ := D15Proof.exists_isChiefSeriesFrom
    (H := u3H L1 L2 S) (U := Q2 L1 L2 S) (Q2 L1 L2 S) hQnormal
  have hM6 := l2_pow_sq_le_relIndex_centralizer (H := u3H L1 L2 S)
    (U := Q2 L1 L2 S) (m := 2 * a + 1) (c := cQ) (by omega)
    (str86_isL2Quot_u3H F.hF F.hL2) (pCoreOf_isPGroup 2 (P2 L1 L2 S))
    (q2_le_u3H L1 L2 S) hserQ htH ht2 htO
  have hbound := caseA_relIndex_centralizer_le F D htV
  have hpow : (2 ^ (2 * a + 1)) ^ cQ ≤ (2 ^ (2 * a + 1)) ^ 2 := hM6.trans hbound
  have hq1 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
  have hcQ : cQ ≤ 2 := (Nat.pow_le_pow_iff_right hq1).mp hpow
  have hR0Q2 : str83CaseAR0 L1 L2 S D.w ≤ Q2 L1 L2 S :=
    (caseA_R0_le_R D.w).trans inf_le_right
  have hR0normalIn : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) :=
    F112W.isNormalIn_of_le_normalizer hR0Q2 (str83_caseA_R0_normal F D)
  obtain ⟨c0, hser0⟩ := D15Proof.exists_isChiefSeriesFrom
    (H := u3H L1 L2 S) (U := Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w) hR0normalIn
  have hserFull : IsChiefSeriesFrom (u3H L1 L2 S) (Q2 L1 L2 S) (Q2 L1 L2 S) (c + c0) :=
    hser.append hser0
  have hcEq : c + c0 = cQ :=
    F112W.isChiefSeriesFrom_unique (q2_le_u3H L1 L2 S) hserFull hserQ
  omega

private theorem caseA_lt_R_Q2
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    str83CaseAR L1 L2 S < Q2 L1 L2 S := by
  have ha := F.ha
  refine lt_of_le_of_ne inf_le_right ?_
  intro h
  have h1 : (str83CaseAR L1 L2 S).relIndex (Q2 L1 L2 S) = 1 := by
    rw [h]
    exact Subgroup.relIndex_eq_one.mpr le_rfl
  rw [str83_caseA_R_relIndex_Q2 F D] at h1
  have hq : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
  have hq2 : 1 < (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
  omega

private theorem caseA_single_factor_false
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F)
    (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) (str83CaseAR0 L1 L2 S D.w)
      (Q2 L1 L2 S)) :
    False := by
  classical
  have hR0Q : str83CaseAR0 L1 L2 S D.w ≤ Q2 L1 L2 S :=
    (caseA_R0_le_R D.w).trans inf_le_right
  have hR0ne : str83CaseAR0 L1 L2 S D.w ≠ Q2 L1 L2 S := by
    intro h
    have hlt : str83CaseAR L1 L2 S < Q2 L1 L2 S := caseA_lt_R_Q2 F D
    exact (not_le_of_gt hlt) ((le_of_eq h.symm).trans (caseA_R0_le_R D.w))
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hQ2p : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hch : ∀ J : Subgroup G, u3H L1 L2 S ≤ Subgroup.normalizer (J : Set G) →
      str83CaseAR0 L1 L2 S D.w ≤ J → J ≤ Q2 L1 L2 S →
        J = str83CaseAR0 L1 L2 S D.w ∨ J = Q2 L1 L2 S := by
    intro J hJ hR0J hJQ
    exact hstep.2.2.2 J ⟨hJQ, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hJ hg) x).mp hx⟩ hR0J hJQ
  have hcommut : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ str83CaseAR0 L1 L2 S D.w :=
    CFSG.Quasithin.MS93.S52i.commutator_le_of_chief hQH (str83_caseA_R0_normal F D)
      (caseA_Q2_normal_u3H F) hR0Q hR0ne hQ2p hch
  have hcommR : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ str83CaseAR L1 L2 S :=
    hcommut.trans (caseA_R0_le_R D.w)
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSNQ1 : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hSP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ2NQ1 : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    F.hQ2S.trans hSNQ1
  have hQ2NR : Q2 L1 L2 S ≤ Subgroup.normalizer (str83CaseAR L1 L2 S : Set G) :=
    Subgroup.le_normalizer_inf hQ2NQ1 (Subgroup.le_normalizer (H := Q2 L1 L2 S))
  haveI : (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NR
  have hQcomm : IsMulCommutative
      (↥(Q2 L1 L2 S) ⧸ (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S)) := by
    refine (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S))).mpr ?_
    rw [commutator_def, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    exact hcommR (Subgroup.commutator_mem_commutator x.2 y.2)
  have hsubEq : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S) =
      (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, str83CaseAR, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  haveI : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2NQ1
  haveI : (Q1 L1 L2 S).subgroupOf S |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hSNQ1
  have hQ2Q1NQ1 : Q2 L1 L2 S ⊔ Q1 L1 L2 S ≤
      Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    rw [sup_comm, F.hT2]
    exact hSNQ1
  haveI : (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ2Q1NQ1
  let eY : ↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S) ≃* ↥S :=
    MulEquiv.subgroupCongr (by rw [sup_comm, F.hT2])
  let e3 : (↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S) ⧸
        (Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S)) ≃*
      (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    QuotientGroup.congr ((Q1 L1 L2 S).subgroupOf (Q2 L1 L2 S ⊔ Q1 L1 L2 S))
      ((Q1 L1 L2 S).subgroupOf S) eY (by
        ext y
        constructor
        · rintro ⟨x, hx, hxy⟩
          have hxy' : (x : G) = (y : G) := congrArg Subtype.val hxy
          show (y : G) ∈ Q1 L1 L2 S
          rw [← hxy']
          exact Subgroup.mem_subgroupOf.mp hx
        · intro hy
          refine ⟨eY.symm y, ?_, eY.apply_symm_apply y⟩
          have hcoe : ((eY.symm y : ↥(Q2 L1 L2 S ⊔ Q1 L1 L2 S)) : G) = (y : G) := rfl
          show (eY.symm y : G) ∈ Q1 L1 L2 S
          rw [hcoe]
          exact Subgroup.mem_subgroupOf.mp hy)
  let eQR : (↥(Q2 L1 L2 S) ⧸ (str83CaseAR L1 L2 S).subgroupOf (Q2 L1 L2 S)) ≃*
      (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    (QuotientGroup.quotientMulEquivOfEq hsubEq.symm).trans
      ((QuotientGroup.quotientInfEquivProdNormalizerQuotient (Q2 L1 L2 S) (Q1 L1 L2 S)
        hQ2NQ1).trans e3)
  have hScomm : IsMulCommutative (↥S ⧸ (Q1 L1 L2 S).subgroupOf S) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eQR hQcomm
  haveI : (Q1 L1 L2 S).subgroupOf S |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hSNQ1
  have hszcomm : IsMulCommutative (szSbar L1 L2 S) :=
    szSbar_comm_of_quotient_comm F hScomm
  obtain ⟨X0, e, -, -, -, hSmap, -⟩ := exists_equiv_z1_sylow
    (K := GaloisField 2 (2 * a + 1)) (GaloisField.card 2 (2 * a + 1) (by omega))
    F.hF F.hB F.ha F.hSz F.hL2 F.hII F.hJ
  let eSU : szSbar L1 L2 S ≃* suzukiU a (GaloisField 2 (2 * a + 1)) :=
    (e.subgroupMap (szSbar L1 L2 S)).trans (MulEquiv.subgroupCongr hSmap)
  have hUcomm : IsMulCommutative (suzukiU a (GaloisField 2 (2 * a + 1))) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv eSU hszcomm
  exact suzukiU_not_isMulCommutative F.ha
    (GaloisField.card 2 (2 * a + 1) (by omega)) hUcomm

end CFSG.Quasithin.Stroth

end
