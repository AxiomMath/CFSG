module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoThreeSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleOfW4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFive
public import CFSG.Quasithin.Background.RonanF918FiveDL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3MinDegreeHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem rkIdx_fixV_zpowers_eq_of_fix_sup {k : MulAut W} {U S : Subgroup W}
    (hsup : U ⊔ S = ⊤) (hU : ∀ u ∈ U, k u ∈ U) (hS : ∀ s ∈ S, k s = s)
    {Q : Type} [CommGroup Q] [Finite Q] (j : ↥U ≃* Q) (q : MulAut Q)
    (hq : ∀ u : ↥U, q (j u) = j ⟨k u, hU _ u.2⟩) :
    rkIdx (fixV (Subgroup.zpowers k)) = rkIdx (fixV (Subgroup.zpowers q)) := by
  let δ : W →* W :=
    { toFun := fun w => k w * w⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        show k (v * w) * (v * w)⁻¹ = k v * v⁻¹ * (k w * w⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  let δq : Q →* Q :=
    { toFun := fun x => q x * x⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        show q (v * w) * (v * w)⁻¹ = q v * v⁻¹ * (q w * w⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  let δU : ↥U →* ↥U :=
    { toFun := fun u => ⟨k u * u⁻¹, U.mul_mem (hU _ u.2) (U.inv_mem u.2)⟩
      map_one' := by ext; simp
      map_mul' := fun v w => by
        ext
        show k ((v : W) * w) * ((v : W) * w)⁻¹ = k v * (v : W)⁻¹ * (k w * (w : W)⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hker : δ.ker = fixV (Subgroup.zpowers k) := by
    ext w
    rw [MonoidHom.mem_ker, CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
    exact mul_inv_eq_one
  have hkerq : δq.ker = fixV (Subgroup.zpowers q) := by
    ext w
    rw [MonoidHom.mem_ker, CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
    exact mul_inv_eq_one
  have e1 : δ.range = δU.range.map U.subtype := by
    ext w
    constructor
    · rintro ⟨w', rfl⟩
      have hw : w' ∈ U ⊔ S := hsup ▸ Subgroup.mem_top w'
      obtain ⟨u, hu, t, ht, rfl⟩ := Subgroup.mem_sup.1 hw
      refine ⟨δU ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, ?_⟩
      show k u * u⁻¹ = k (u * t) * (u * t)⁻¹
      rw [map_mul, hS t ht, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  have e2 : δq.range = δU.range.map j.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨u, rfl⟩ := j.surjective y
      refine ⟨δU u, ⟨u, rfl⟩, ?_⟩
      show j (δU u) = q (j u) * (j u)⁻¹
      rw [hq u, ← map_inv, ← map_mul]
      rfl
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨j u, ?_⟩
      show q (j u) * (j u)⁻¹ = j (δU u)
      rw [hq u, ← map_inv, ← map_mul]
      rfl
  have hcard : Nat.card δ.range = Nat.card δq.range := by
    rw [e1, e2, Subgroup.card_map_of_injective U.subtype_injective,
      Subgroup.card_map_of_injective j.injective]
  unfold rkIdx
  rw [← hker, ← hkerq, Subgroup.index_ker, Subgroup.index_ker, hcard]

theorem altTwo_transport {Y K : Subgroup (MulAut W)} {n : ℕ}
    (hKY : K ≤ Y) (hn2 : 2 ≤ n)
    {I : Subgroup W} (hI : I ∈ irrSet K) (hIK : I = commSub (⊤ : Subgroup W) K)
    (hsup : commSub (⊤ : Subgroup W) K ⊔ fixV K = ⊤)
    (hC : fixV (autSub (autQuot K (⊥ : Subgroup W))
      (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) = ⊥)
    (hnat : NatSUn (autQuot (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))
        (fixV (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))) ⊤ ⊥ 3 n) :
    S17.CNatModSU3Sub W (CFSG.Quasithin.commSub (⊤ : Subgroup W) K) K n ∧
      E3.mParam Y ≤ 2 * n := by
  classical
  let Istar : Subgroup (W ⧸ (⊥ : Subgroup W)) := I.map (QuotientGroup.mk' ⊥)
  let Lstar : Subgroup (MulAut ↥Istar) := autSub (autQuot K ⊥) Istar
  let C : Subgroup ↥Istar := fixV Lstar
  let Wq := ↥Istar ⧸ C
  let X : Subgroup (MulAut Wq) := autQuot Lstar C
  have hKZ : K ≤ stabSub (⊥ : Subgroup W) := CFSG.Quasithin.B5.Ln.stabSub_bot_le K
  have hXle : autQuot K ⊥ ≤ stabSub Istar := autQuot_le_stabSub_map hI.2.2.1
  have hLC : Lstar ≤ stabSub C := CFSG.Quasithin.RonanF918.le_stabSub_fixV Lstar
  let ρ : ↥K →* ↥X := (CFSG.Quasithin.D37Lift.toQuot C Lstar hLC).comp
      ((CFSG.Quasithin.F918V6B.resOnto hXle).comp (CFSG.Quasithin.D37Lift.toQuot ⊥ K hKZ))
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  let j : ↥(commSub (⊤ : Subgroup W) K) ≃* Wq :=
    (MulEquiv.subgroupCongr hIK.symm).trans ((I.equivMapOfInjective _ hinj).trans
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hC).symm))
  have hU : ∀ h ∈ K, ∀ u ∈ commSub (⊤ : Subgroup W) K, h u ∈ commSub (⊤ : Subgroup W) K :=
    fun h hh u hu => CFSG.Quasithin.Asc81c.commSub_stable' hh hu
  have hr : ∀ (k : ↥K) (u : ↥(commSub (⊤ : Subgroup W) K)),
      ((ρ k : ↥X) : MulAut Wq) (j u) = j ⟨(k : MulAut W) u, hU _ k.2 _ u.2⟩ :=
    fun _ _ => rfl
  have hρsurj : Function.Surjective ρ :=
    (CFSG.Quasithin.D37Lift.toQuot_surjective C Lstar hLC).comp
      ((CFSG.Quasithin.F918V6B.resOnto_surjective hXle).comp
        (CFSG.Quasithin.D37Lift.toQuot_surjective ⊥ K hKZ))
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    rw [Subgroup.mem_bot]
    have hfixU : ∀ u ∈ commSub (⊤ : Subgroup W) K, (k : MulAut W) u = u := by
      intro u hu
      have h1 : ((ρ k : ↥X) : MulAut Wq) (j ⟨u, hu⟩) = j ⟨u, hu⟩ := by
        rw [hk]
        rfl
      rw [hr k ⟨u, hu⟩] at h1
      exact congrArg Subtype.val (j.injective h1)
    have hfixF : ∀ v ∈ fixV K, (k : MulAut W) v = v := fun v hv => hv k k.2
    exact Subtype.ext (CFSG.Quasithin.E2.eq_one_of_fix_sup hsup hfixU hfixF)
  let r : ↥K ≃* ↥X := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hr' : ∀ (k : ↥K) (u : ↥(commSub (⊤ : Subgroup W) K)),
      ((r k : ↥X) : MulAut Wq) (j u) = j ⟨(k : MulAut W) u, hU _ k.2 _ u.2⟩ := hr
  have hnatK : NatSUn K (commSub (⊤ : Subgroup W) K) ⊥ 3 n := by
    obtain ⟨F, hF, hFfin, hcard, hreal⟩ := hnat
    exact ⟨F, hF, hFfin, hcard, CFSG.Quasithin.H.FFModel.realizes_of_equiv hU j r hr' hreal⟩
  refine ⟨S17.cNatModStructSU3Sub_of_natSUn hnatK rfl, ?_⟩
  have hmX : E3.mParam X = 2 * n :=
    (CFSG.Quasithin.H.H2_SU3 hn2 hnat le_rfl Subgroup.le_normalizer).1
  have hcardWq : Nat.card (⊤ : Subgroup Wq) = 2 ^ (6 * n) :=
    S17.card_of_cNatModSU3Sub (S17.cNatModStructSU3Sub_of_natSUn hnat rfl)
  have heven : Even (Nat.card X) := by
    by_contra hodd
    have h1 : E3.mParam X = rk Wq := by
      unfold E3.mParam
      rw [if_neg hodd]
    have h2 : rk Wq = 6 * n := by
      unfold rk
      rw [← Subgroup.card_top (G := Wq), hcardWq, padicValNat.prime_pow]
    omega
  obtain ⟨t, htX, ht2, htrk⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X heven
  let k : ↥K := r.symm ⟨t, htX⟩
  have hrk : r k = ⟨t, htX⟩ := MulEquiv.apply_symm_apply r _
  have hk2 : orderOf (k : MulAut W) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq r k, hrk, Subgroup.orderOf_mk, ht2]
  have hq : ∀ u : ↥(commSub (⊤ : Subgroup W) K),
      t (j u) = j ⟨(k : MulAut W) u, hU _ k.2 _ u.2⟩ := by
    intro u
    have h := hr' k u
    rw [hrk] at h
    exact h
  have hrkIdx := rkIdx_fixV_zpowers_eq_of_fix_sup (k := (k : MulAut W)) hsup
    (fun u hu => hU _ k.2 _ hu) (fun v hv => hv k k.2) j t hq
  calc E3.mParam Y ≤ rkIdx (fixV (Subgroup.zpowers (k : MulAut W))) :=
        CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two (hKY k.2) hk2
    _ = rkIdx (fixV (Subgroup.zpowers t)) := hrkIdx
    _ = E3.mParam X := htrk
    _ = 2 * n := hmX

theorem k_SU3NaturalModuleAltTwo_holds (h36 : W4Lem3_6) : K_SU3NaturalModuleAltTwo := by
  intro W _ _ hW Y K n hKY hKcomp hKne hSU hn3 hO2 hbasic hfix hmY Z hZ hsum I hI hmn
  subst hZ
  classical
  have : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  have hsupV := commV_sup_fixV_eq_top_of_isDirSumOver hKcomp hsum
  have hinfV := commV_inf_fixV_eq_bot_of_isDirSumOver hKcomp hfix hsum
  have hsup : commSub (⊤ : Subgroup W) K ⊔ fixV K = ⊤ := by
    rwa [← CFSG.Quasithin.commV_eq_commSub]
  have hC := fixV_autSub_autQuot_bot_eq_bot hI hinfV
  obtain ⟨hnat, h2nG, h2nY⟩ := altTwo_three_six hW hKY hKcomp hSU hn3 hsum hI hmn hmY h36
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup W)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hrkI : rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) = rk ↥I := by
    unfold rk
    rw [Subgroup.card_map_of_injective hinj]
  have hrkK : rk ↥(commV (autQuot K (⊥ : Subgroup W))) = rk ↥(commV K) := by
    rw [← map_commV_eq_commV_autQuot K ⊥ (CFSG.Quasithin.B5.Ln.stabSub_bot_le K)]
    unfold rk
    rw [Subgroup.card_map_of_injective hinj]
  have hrk6 : rk ↥(I.map (QuotientGroup.mk' (⊥ : Subgroup W))) = 6 * n := by
    have hcardWq := S17.card_of_cNatModSU3Sub (S17.cNatModStructSU3Sub_of_natSUn hnat rfl)
    rw [Subgroup.card_top] at hcardWq
    have hC1 : Nat.card ↥(fixV (autSub (autQuot K (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))) = 1 := by
      rw [hC]
      exact Subgroup.card_bot
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (fixV (autSub (autQuot K (⊥ : Subgroup W)) (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))
    rw [hC1, mul_one, hcardWq] at hc
    unfold rk
    rw [hc, padicValNat.prime_pow]
  have hI6 : rk ↥I = 6 * n := hrkI ▸ hrk6
  have he6 : rk ↥(commV K) ≤ 6 * n + 6 := by
    rw [hrkK, hrk6] at hmn
    have hpos : (0 : ℚ) < ((6 * n : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 6 * n)
    rw [mul_div_assoc', div_le_iff₀ hpos] at hmn
    have h2 : E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) * rk ↥(commV K) ≤
        E3.mParam Y * (6 * n) := by exact_mod_cast hmn
    have h5 : 2 * n * rk ↥(commV K) ≤ 2 * n * (6 * n + 6) := by
      calc 2 * n * rk ↥(commV K) ≤ E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
            (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) * rk ↥(commV K) :=
            Nat.mul_le_mul_right _ h2nG
        _ ≤ E3.mParam Y * (6 * n) := h2
        _ ≤ (2 * n + 2) * (6 * n) := Nat.mul_le_mul_right _ hmY
        _ = 2 * n * (6 * n + 6) := by ring
    exact Nat.le_of_mul_le_mul_left h5 (by omega)
  have hdK : 6 * n ≤ dMinDeg ↥K := k_SU3MinDegree_holds ↥K n hSU (by omega)
  have hIle : I ≤ commSub (⊤ : Subgroup W) K := by
    calc I = commSub I K := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) K := commSub_mono le_top le_rfl
  have hSK : StableUnder K (commSub (⊤ : Subgroup W) K) :=
    fun x hx u hu => CFSG.Quasithin.Asc81c.commSub_stable' hx hu
  have hle : commSub (commSub (⊤ : Subgroup W) K) K ≤ I :=
    commSub_le_of_rk_lt_dMinDeg hW hIle hSK hI.2.2.1 (by
      rw [← CFSG.Quasithin.commV_eq_commSub]
      omega)
  have hperfS := CFSG.Quasithin.RonanF918.commSub_commSub_eq_of_perfect (L := K)
    (S := (⊤ : Subgroup W)) (fun _ _ _ _ => Subgroup.mem_top _)
  rw [hperfS] at hle
  have hIK : I = commSub (⊤ : Subgroup W) K := le_antisymm hIle hle
  obtain ⟨hCN, hmle⟩ := altTwo_transport hKY (by omega) hI hIK hsup hC hnat
  exact ⟨hCN, le_antisymm hmle h2nY⟩

theorem k_SU3NaturalModule_of_w4_holds (h128 : W4Lem12_8) (h36 : W4Lem3_6) :
    K_SU3NaturalModule :=
  k_SU3NaturalModule_of_w4 h128 h36 k_SU3MinDegree_holds (k_SU3NaturalModuleAltTwo_holds h36)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
