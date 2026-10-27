module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModChief
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat2
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateL2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open CFSG.Quasithin.F53.Stellmacher.S43.Even
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_of_inf_centralizer_le {V N L C : Subgroup G}
    (hNV : N ≤ V) (hLN : L ≤ N) (hCV : C ≤ V) (hCNL : C ⊓ N ≤ L) :
    L.relIndex N ≤ C.relIndex V := by
  classical
  have hCcard : Nat.card ↥C = N.relIndex C * Nat.card ↥(C ⊓ N) := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := C)
    rw [inf_comm] at h
    exact h.symm
  have hrelCN : N.relIndex C ≤ N.relIndex V :=
    Subgroup.relIndex_le_of_le_right hCV (D15Proof.relIndex_ne_zero N V)
  have hcardIn : Nat.card ↥(C ⊓ N) ≤ Nat.card ↥L := Subgroup.card_le_of_le hCNL
  have hineq : Nat.card ↥C ≤ N.relIndex V * Nat.card ↥L := by
    rw [hCcard]
    exact Nat.mul_le_mul hrelCN hcardIn
  have hVcard : C.relIndex V * Nat.card ↥C = Nat.card ↥V := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := V)
    rwa [inf_eq_left.mpr hCV] at h
  have hNcard : N.relIndex V * Nat.card ↥N = Nat.card ↥V := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := V)
    rwa [inf_eq_left.mpr hNV] at h
  have hNLcard : L.relIndex N * Nat.card ↥L = Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := N)
    rwa [inf_eq_left.mpr hLN] at h
  have h1 : Nat.card ↥V ≤ C.relIndex V * (N.relIndex V * Nat.card ↥L) := by
    rw [← hVcard]
    exact Nat.mul_le_mul_left _ hineq
  have h2 : N.relIndex V * (L.relIndex N * Nat.card ↥L) = Nat.card ↥V := by
    rw [hNLcard, hNcard]
  have h3 : L.relIndex N * (N.relIndex V * Nat.card ↥L) ≤
      C.relIndex V * (N.relIndex V * Nat.card ↥L) := by
    calc L.relIndex N * (N.relIndex V * Nat.card ↥L)
        = N.relIndex V * (L.relIndex N * Nat.card ↥L) := by ring
      _ = Nat.card ↥V := h2
      _ ≤ C.relIndex V * (N.relIndex V * Nat.card ↥L) := h1
  exact Nat.le_of_mul_le_mul_right h3
    (Nat.mul_pos (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero N V)) Nat.card_pos)

theorem str86_caseIIb_generation
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {m : ℕ} (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {A : Subgroup G} (hAS : A ≤ S) (hAe : IsElemAbelian 2 A)
    (hAr : (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ m) :
    ∃ g ∈ u3H L1 L2 S, A ⊔ conjSubgroup A g ⊔ Q2 L1 L2 S = u3H L1 L2 S := by
  classical
  set H : Subgroup G := u3H L1 L2 S with hH
  set Q : Subgroup G := Q2 L1 L2 S with hQ
  have hSH : S ≤ H := by
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
    rw [hH]
    change S ≤ L2 ⊔ Q2 L1 L2 S
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hAH : A ≤ H := hAS.trans hSH
  have hQH : Q ≤ H := by
    rw [hH, hQ]
    exact q2_le_u3H L1 L2 S
  have hH2 : IsL2Quot m (oTwoQuot ↥H) := by
    rw [hH]
    exact str86_isL2Quot_u3H hF hL2
  have hQcore : pCore 2 ↥H = Q.subgroupOf H := by
    ext x
    rw [CFSG.Quasithin.F1.mem_pCore_iff_coe,
      show pCoreOf 2 H = Q from by rw [hH, hQ]; exact str86_pCoreOf_u3H hF]
    rfl
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  let B : Subgroup (oTwoQuot ↥H) := (A.subgroupOf H).map π
  have hkerπ : π.ker = Q.subgroupOf H := by
    rw [show π.ker = pCore 2 ↥H from QuotientGroup.ker_mk' (pCore 2 ↥H), hQcore]
  have hBcard : Nat.card B = 2 ^ m := by
    have hrel : Nat.card B = π.ker.relIndex (A.subgroupOf H) := by
      change Nat.card ((A.subgroupOf H).map π) = π.ker.relIndex (A.subgroupOf H)
      exact (Subgroup.relIndex_ker (A.subgroupOf H) π).symm
    rw [hrel, hkerπ, Subgroup.relIndex_subgroupOf hAH,
      ← Subgroup.inf_relIndex_left A Q]
    exact hAr
  have hBgt : 2 < Nat.card B := by
    rw [hBcard]
    calc 2 = 2 ^ 1 := by decide
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hm
  have hBel : IsElemAbelian 2 B :=
    (hAe.subgroupOf H).map π
  obtain ⟨eH⟩ := hH2
  have hPSL : CFSG.Quasithin.IsPSL 2 2 m (oTwoQuot ↥H) := by
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩,
      GaloisField 2 m, inferInstance, inferInstance,
      GaloisField.card 2 m (by omega),
      ⟨eH.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 m))⟩⟩
    · intro h
      have h2 : 2 ^ m = 2 := congrArg Prod.snd h
      have h4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    · intro h
      have h3 : 2 ^ m = 3 := congrArg Prod.snd h
      have h4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
  obtain ⟨gbar, hgen⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.TwoConjL2.twoConjugateGeneration_of_isPSL hPSL hBel hBgt
  obtain ⟨gH, hgH⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥H) gbar
  let g : G := (gH : G)
  have hgHmem : g ∈ H := gH.2
  have hAgH : conjSubgroup A g ≤ H := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    have hxH : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxH]
    exact H.mul_mem (H.mul_mem (H.inv_mem hgHmem) (hAH hx)) hgHmem
  have hconjMap : conjSubgroup B gbar = ((conjSubgroup A g).subgroupOf H).map π := by
    ext y
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    constructor
    · intro hy
      change y ∈ ((conjSubgroup A g).subgroupOf H).map π
      change gbar * y * gbar⁻¹ ∈ (A.subgroupOf H).map π at hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨a, ha, haπ⟩ := hy
      refine Subgroup.mem_map.mpr ⟨gH⁻¹ * a * gH, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.mem_conjSubgroup_iff]
        have hcoe : ((gH⁻¹ * a * gH : ↥H) : G) =
            (gH : G)⁻¹ * (a : G) * (gH : G) := by simp
        rw [hcoe]
        have hgg : (gH : G) = g := rfl
        rw [hgg]
        have hamem : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
        convert hamem using 1
        group
      · rw [map_mul, map_mul, map_inv, hgH, haπ]
        group
    · intro hy
      change gbar * y * gbar⁻¹ ∈ (A.subgroupOf H).map π
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hy
      have hxAg : g * (x : G) * g⁻¹ ∈ A :=
        (CFSG.Quasithin.mem_conjSubgroup_iff).mp (Subgroup.mem_subgroupOf.mp hx)
      refine ⟨gH * x * gH⁻¹, ?_, ?_⟩
      · show ((gH * x * gH⁻¹ : ↥H) : G) ∈ A
        have hcoe : ((gH * x * gH⁻¹ : ↥H) : G) =
            (gH : G) * (x : G) * (gH : G)⁻¹ := by simp
        rw [hcoe]
        have hgg : (gH : G) = g := rfl
        rw [hgg]
        exact hxAg
      · rw [map_mul, map_mul, map_inv, hgH, hxπ]
  have hmapSup : ((A ⊔ conjSubgroup A g).subgroupOf H).map π = ⊤ := by
    rw [Subgroup.subgroupOf_sup hAH hAgH, Subgroup.map_sup]
    simpa [B, hconjMap] using hgen
  have hle : H ≤ (A ⊔ conjSubgroup A g) ⊔ Q := by
    intro h hh
    have hπ : π ⟨h, hh⟩ ∈ ((A ⊔ conjSubgroup A g).subgroupOf H).map π := by
      rw [hmapSup]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hπ
    have hxX : (x : G) ∈ A ⊔ conjSubgroup A g := Subgroup.mem_subgroupOf.mp hx
    have hdiff : (x⁻¹ * ⟨h, hh⟩ : ↥H) ∈ Q.subgroupOf H := by
      rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hxπ]
      simp
    have hdiffG : ((x⁻¹ * ⟨h, hh⟩ : ↥H) : G) ∈ Q :=
      Subgroup.mem_subgroupOf.mp hdiff
    have heq : h = (x : G) * ((x⁻¹ * ⟨h, hh⟩ : ↥H) : G) := by
      rw [show ((x⁻¹ * ⟨h, hh⟩ : ↥H) : G) = (x : G)⁻¹ * h by simp]
      group
    rw [heq]
    exact Subgroup.mul_mem_sup hxX hdiffG
  refine ⟨g, hgHmem, le_antisymm ?_ hle⟩
  exact sup_le (sup_le hAH hAgH) hQH

theorem str86_caseIIb_sq_le_relIndex
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {m : ℕ} (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJZ : ⁅Z2 L1 L2 S, thompsonJ S⁆ ≠ ⊥)
    {K : Subgroup G} (hKQ : K ⊔ Q2 L1 L2 S = u3H L1 L2 S) :
    (2 ^ m) ^ 2 ≤ (Z2 L1 L2 S ⊓ Subgroup.centralizer (K : Set G)).relIndex
      (Z2 L1 L2 S) := by
  classical
  set H : Subgroup G := u3H L1 L2 S with hH
  set Q : Subgroup G := Q2 L1 L2 S with hQ
  set Z : Subgroup G := Z2 L1 L2 S with hZ
  have hQH : Q ≤ H := by
    rw [hH, hQ]
    exact q2_le_u3H L1 L2 S
  have hSH : S ≤ H := by
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
    rw [hH]
    change S ≤ L2 ⊔ Q2 L1 L2 S
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hQZ : Q ≤ Subgroup.centralizer (Z : Set G) := by
    rw [hQ, hZ]
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZH : Z ≤ H := (omegaOneCenterOf_le Q).trans hQH
  have hZnorm : H ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hH, hZ]
    exact str86_z2_normal_u3H L1 L2 S
  have hnotH : ¬ H ≤ Subgroup.centralizer (Z : Set G) := by
    intro hHle
    apply hJZ
    have hJH : thompsonJ S ≤ H := (thompsonJ_le_self S).trans hSH
    have hJC : thompsonJ S ≤ Subgroup.centralizer (Z : Set G) := hJH.trans hHle
    have hcomm : ⁅thompsonJ S, Z⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJC
    rwa [Subgroup.commutator_comm] at hcomm
  have hCeq : H ⊓ Subgroup.centralizer (Z : Set G) = Q := by
    set C : Subgroup G := H ⊓ Subgroup.centralizer (Z : Set G) with hC
    have hCH : C ≤ H := inf_le_left
    have hQC : Q ≤ C := le_inf hQH hQZ
    have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
      intro x hx
      exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
        ((hZnorm.trans (F7.normalizer_le_normalizer_centralizer Z)) hx)
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF hm hL2 (by simpa [hH] using hCH)
      (by simpa [hH] using hCn) hQC with hQeq | hHeq
    · exact hQeq
    · exfalso
      apply hnotH
      rw [hH]
      change L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z : Set G)
      rw [← hHeq]
      exact inf_le_right
  have hHsup : H = oTwoUpper H ⊔ Q := by
    rw [hH, hQ]
    exact str86_u3H_eq_oTwoUpper_sup_q2 hF hm hL2
  have hnotO2 : ¬ oTwoRes H ≤ Subgroup.centralizer (Z : Set G) := by
    intro hO2
    have hO2' : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) := by
      rwa [CFSG.Quasithin.oTwoRes_eq_oTwoUpper] at hO2
    exact hnotH (by rw [hHsup]; exact sup_le hO2' hQZ)
  have hnotcomm : ¬ ⁅Z, oTwoRes H⁆ ≤ ⊥ := by
    intro hcomm
    apply hnotO2
    have hcomm' : ⁅Z, oTwoRes H⁆ = ⊥ := le_bot_iff.mp hcomm
    rw [Subgroup.commutator_comm] at hcomm'
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  have hZea : IsElemAbelian 2 Z := by
    rw [hZ]
    exact SmithC27.isElemAbelian_omegaOneCenterOf Q
  have hZleQ : Z ≤ Q := by
    rw [hZ, hQ]
    exact omegaOneCenterOf_le (Q2 L1 L2 S)
  have hsecZ : CFSG.Quasithin.F53Mod.IsSec H ⊥ Z :=
    { le := bot_le
      normN := hZnorm
      normL := by
        rw [Subgroup.normalizer_eq_top]
        exact le_top
      comm := by
        intro x hx y hy
        have hxy : x * y = y * x := by
          simpa using congrArg Subtype.val (hZea.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        rw [Subgroup.mem_bot, hxy]
        group
      sq := by
        intro x hx
        rw [Subgroup.mem_bot]
        exact hZea.2 x hx }
  obtain ⟨L', N', -, hN'Z, hstep, hnc⟩ :=
    exists_noncentral_of_not_le (X := H) (U := Q) (L := ⊥) (N := Z) hsecZ hZleQ hnotcomm
  have hCN : (Z ⊓ Subgroup.centralizer (H : Set G)) ⊓ N' ≤ L' := by
    refine inf_le_lower_of_noncentral (H := H) (X := Q) (L := L') (N := N')
      (Z := Z ⊓ Subgroup.centralizer (H : Set G)) hQH hstep hnc ?_ ?_ ?_
    · exact inf_le_left.trans hZleQ
    · intro x hx
      exact A4.mem_normalizer_inf (hZnorm hx)
        ((F7.normalizer_le_normalizer_centralizer H) (Subgroup.le_normalizer hx))
    · intro h hh z hz
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 h hh
  have hCeqK : Z ⊓ Subgroup.centralizer (K : Set G) =
      Z ⊓ Subgroup.centralizer (H : Set G) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzZ, hzK⟩ := Subgroup.mem_inf.mp hz
      refine Subgroup.mem_inf.mpr ⟨hzZ, ?_⟩
      have hzQ : z ∈ Subgroup.centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        exact (Subgroup.mem_centralizer_iff.mp (hQZ hq) z hzZ).symm
      rw [← hKQ, Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with hxK | hxQ
      · exact Subgroup.mem_centralizer_iff.mp hzK x hxK
      · exact Subgroup.mem_centralizer_iff.mp hzQ x hxQ
    · exact inf_le_inf_left Z
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hKQ ▸ le_sup_left)))
  have hge : (2 ^ m) ^ 2 ≤ L'.relIndex N' :=
    str86_card_chiefStep_ge hF hm hL2 hstep hnc
  have hidx : L'.relIndex N' ≤ (Z ⊓ Subgroup.centralizer (H : Set G)).relIndex Z :=
    relIndex_le_of_inf_centralizer_le hN'Z hstep.2.2.1.le inf_le_left hCN
  rw [hCeqK]
  exact hge.trans hidx

end CFSG.Quasithin.Stroth

end
