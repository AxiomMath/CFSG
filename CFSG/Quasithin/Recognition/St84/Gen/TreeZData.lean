module

public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.CentralZData
public import CFSG.Quasithin.Recognition.St84.Gen.R1Bridge
import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutKb
public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private noncomputable def sylowCenterCore {G : Type*} [Group G] (X : Subgroup G) : Subgroup G :=
  ⨆ (P : Subgroup G) (_ : IsSylowTwoOf P X), centerOf P ⊓ pCoreOf 2 X

private theorem map_sylowCenterCore {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    (sylowCenterCore (G := A) X).map f = sylowCenterCore (G := B) (X.map f) := by
  unfold sylowCenterCore
  simp only [Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun P => iSup_le fun hP => ?_
    refine le_iSup₂_of_le (P.map f)
      ((CFSG.Quasithin.SimsD1.TransGrp.isSylowTwoOf_map_iff f hf P X).2 hP) ?_
    rw [CFSG.Quasithin.H13.F431.centerOf_map_of_injective f hf P,
      CFSG.Quasithin.St84.pCoreOf_map_injective f hf X,
      Subgroup.map_inf (centerOf P) (pCoreOf 2 X) f hf]
  · refine iSup_le fun Q => iSup_le fun hQ => ?_
    obtain ⟨P, hPQ, hP⟩ :=
      CFSG.Quasithin.SimsD1.TransGrp.exists_isSylowTwoOf_of_map f hf X hQ
    refine le_iSup₂_of_le P hP ?_
    rw [← hPQ, CFSG.Quasithin.H13.F431.centerOf_map_of_injective f hf P,
      CFSG.Quasithin.St84.pCoreOf_map_injective f hf X,
      Subgroup.map_inf (centerOf P) (pCoreOf 2 X) f hf]

private theorem sylowCenterCore_le_pCoreOf {G : Type*} [Group G] (X : Subgroup G) :
    sylowCenterCore X ≤ pCoreOf 2 X := by
  unfold sylowCenterCore
  exact iSup_le fun _ => iSup_le fun _ => inf_le_right

private theorem sylowCenterCore_subgroupOf {X K : Subgroup H} (hX : X ≤ K) :
    (sylowCenterCore X).subgroupOf K = sylowCenterCore (X.subgroupOf K) := by
  refine Subgroup.map_injective K.subtype_injective ?_
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left,
    map_sylowCenterCore K.subtype K.subtype_injective (X.subgroupOf K),
    Subgroup.map_subgroupOf_eq_of_le hX]
  exact (sylowCenterCore_le_pCoreOf X).trans
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hX)

theorem f112_s3L2ZData_of_centralZData_of_hyp111R
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S)
    (hO : oTwoRes L2 ≤ oTwoPrime (f112saP2' L1 L2 S))
    {E : Subgroup (f112Gold L1 L2 S).Universal}
    (hEa : E ⊓ (f112Gold L1 L2 S).ofA.range = f112OfA L1 L2 S (f112saP1' L1 L2 S))
    (hEb : E ⊓ (f112Gold L1 L2 S).ofB.range = f112OfB L1 L2 S (f112saP2' L1 L2 S))
    (hEab : E ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
      f112OfA L1 L2 S (f112saK L1 L2 S))
    (Y : Setup (f112Gold L1 L2 S).treeGraph ↥E)
    (hY0 : Y.vert 0 = baseB (f112Gold L1 L2 S))
    (hY1 : Y.vert 1 = baseA (f112Gold L1 L2 S))
    (hZ : Y.CentralZData) :
    S3L2ZData L1 L2 S (centerOf (pCoreOf 2 (f112saK L1 L2 S))) := by
  classical
  let K := f112saK L1 L2 S
  let P1 := f112P1 L1 L2 S
  let P2 := f112P2 L1 L2 S
  let P1' := f112saP1' L1 L2 S
  let P2' := f112saP2' L1 L2 S
  let Z : Subgroup H := centerOf (pCoreOf 2 K)
  have hK_le_B : K ≤ bigB L1 L2 S := f112sa_K_le_bigB L1 L2 S
  have hB_le_P1 : bigB L1 L2 S ≤ P1 := le_sup_right
  have hB_le_P2 : bigB L1 L2 S ≤ P2 := le_sup_right
  have hK_le_P1 : K ≤ P1 := hK_le_B.trans hB_le_P1
  have hK_le_P2 : K ≤ P2 := hK_le_B.trans hB_le_P2
  have hP1'_le_P1 : P1' ≤ P1 := f112sa_P1'_le_P1 hF.toW
  have hP2'_le_P2 : P2' ≤ P2 := f112sa_P2'_le_P2 hF.toW
  have hZ_le_B : Z ≤ bigB L1 L2 S := by
    show centerOf (pCoreOf 2 K) ≤ bigB L1 L2 S
    exact (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).trans hK_le_B
  have hZ_le_P1 : Z ≤ P1 := hZ_le_B.trans hB_le_P1
  have hZ_le_P2 : Z ≤ P2 := hZ_le_B.trans hB_le_P2
  have hD1a : (Y.Gi 0).map E.subtype = f112OfB L1 L2 S P2' := by
    show (MulAction.stabilizer ↥E (Y.vert 0)).map E.subtype = _
    rw [hY0, f112_stabilizer_baseB_map L1 L2 S E, hEb]
  have hD1b : (Y.Gi 1).map E.subtype = f112OfA L1 L2 S P1' := by
    show (MulAction.stabilizer ↥E (Y.vert 1)).map E.subtype = _
    rw [hY1, f112_stabilizer_baseA_map L1 L2 S E, hEa]
  have hD2 : (Y.Gi 0 ⊓ Y.Gi 1).map E.subtype = f112OfA L1 L2 S K := by
    rw [Subgroup.map_inf (Y.Gi 0) (Y.Gi 1) E.subtype E.subtype_injective, hD1a, hD1b,
      ← hEb, ← hEa]
    calc (E ⊓ (f112Gold L1 L2 S).ofB.range) ⊓ (E ⊓ (f112Gold L1 L2 S).ofA.range)
        = E ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range := by ac_rfl
      _ = f112OfA L1 L2 S K := hEab
  have hD3S : (Y.S).map E.subtype = f112OfA L1 L2 S (pCoreOf 2 K) := by
    show (pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1)).map E.subtype = _
    rw [← pCoreOf_map_injective E.subtype E.subtype_injective, hD2]
    exact f112_ofA_pCoreOf L1 L2 S hK_le_P1
  have hD3 : (Y.Z 0).map E.subtype = f112OfA L1 L2 S Z := by
    rw [← hZ.centerOf_S,
      ← CFSG.Quasithin.H13.F431.centerOf_map_of_injective E.subtype E.subtype_injective, hD3S]
    rw [show f112OfA L1 L2 S (pCoreOf 2 K) =
      ((pCoreOf 2 K).subgroupOf P1).map (f112Gold L1 L2 S).ofA from rfl,
      CFSG.Quasithin.H13.F431.centerOf_map_of_injective (f112Gold L1 L2 S).ofA
        (f112Gold L1 L2 S).ofA_injective,
      CFSG.Quasithin.H13.F431.D4q.Out.centerOf_subgroupOf
        (Kb := P1) (X := pCoreOf 2 K) ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hK_le_P1)]
  have hQ0 : (Y.Q 0).map E.subtype = f112OfB L1 L2 S (pCoreOf 2 P2') := by
    show (pCoreOf 2 (Y.Gi 0)).map E.subtype = _
    rw [← pCoreOf_map_injective E.subtype E.subtype_injective, hD1a]
    exact f112_ofB_pCoreOf L1 L2 S hP2'_le_P2
  have hQ1 : (Y.Q 1).map E.subtype = f112OfA L1 L2 S (pCoreOf 2 P1') := by
    show (pCoreOf 2 (Y.Gi 1)).map E.subtype = _
    rw [← pCoreOf_map_injective E.subtype E.subtype_injective, hD1b]
    exact f112_ofA_pCoreOf L1 L2 S hP1'_le_P1
  have hL0 : (Y.L 0).map E.subtype = f112OfB L1 L2 S (oTwoPrime P2') := by
    show (oTwoPrime (Y.Gi 0)).map E.subtype = _
    rw [← CFSG.Quasithin.oTwoPrime_map E.subtype E.subtype_injective, hD1a]
    exact f112_ofB_oTwoPrime L1 L2 S hP2'_le_P2
  have hL1 : (Y.L 1).map E.subtype = f112OfA L1 L2 S (oTwoPrime P1') := by
    show (oTwoPrime (Y.Gi 1)).map E.subtype = _
    rw [← CFSG.Quasithin.oTwoPrime_map E.subtype E.subtype_injective, hD1b]
    exact f112_ofA_oTwoPrime L1 L2 S hP1'_le_P1
  have hZ_le_inf : Z ≤ P1 ⊓ P2 := by
    rw [f112_inf_eq_bigB_of_hyp111R hR]
    exact hZ_le_B
  have hAZ_eq_BZ : f112OfA L1 L2 S Z = f112OfB L1 L2 S Z :=
    ofA_subgroupOf_eq_ofB_subgroupOf L1 L2 S hZ_le_inf
  have hcardZ : Nat.card ↥Z = 2 := by
    have h := card_of_map_eq (L1 := L1) (L2 := L2) (S := S) (E := E)
      (Y' := Y.Z 0) (Y := Z) hZ_le_P1 hD3
    rw [hZ.card_Z_zero] at h
    exact h.symm
  have hSNK : S ≤ Subgroup.normalizer (K : Set H) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_K hF.toW)
  have hSNQ : S ≤ Subgroup.normalizer (pCoreOf 2 K : Set H) :=
    hSNK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hSNC : S ≤ Subgroup.normalizer
      (Subgroup.centralizer (pCoreOf 2 K : Set H) : Set H) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub s (Subgroup.centralizer (pCoreOf 2 K : Set H)) =
      Subgroup.centralizer (pCoreOf 2 K : Set H)
    rw [← CFSG.Quasithin.conjSub_centralizer]
    rw [show conjSub s (pCoreOf 2 K) = pCoreOf 2 K from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSNQ hs)]
  have hSZ : S ≤ Subgroup.normalizer (Z : Set H) := by
    have h := Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2 K)
      (K := Subgroup.centralizer (pCoreOf 2 K : Set H))
    change S ≤ Subgroup.normalizer
      (pCoreOf 2 K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set H) : Set H)
    exact (le_inf hSNQ hSNC).trans h
  have hZ_cent_S : Z ≤ Subgroup.centralizer (S : Set H) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hconjZ : s * z * s⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hSZ hs) z).mp hz
    by_cases hz1 : z = 1
    · rw [hz1]
      simp
    · obtain ⟨z₀, hz₀ne, hz₀uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).mp hcardZ
      have hz_ne : (⟨z, hz⟩ : ↥Z) ≠ 1 := by
        intro h
        exact hz1 (congrArg Subtype.val h)
      have hw_ne : (⟨s * z * s⁻¹, hconjZ⟩ : ↥Z) ≠ 1 := by
        intro h
        apply hz1
        have hval : s * z * s⁻¹ = 1 := congrArg Subtype.val h
        calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
          _ = 1 := by rw [hval]; group
      have heq : (⟨s * z * s⁻¹, hconjZ⟩ : ↥Z) = ⟨z, hz⟩ :=
        (hz₀uniq _ hw_ne).trans (hz₀uniq _ hz_ne).symm
      have hval : s * z * s⁻¹ = z := congrArg Subtype.val heq
      calc s * z = (s * z * s⁻¹) * s := by group
        _ = z * s := by rw [hval]
  have hZ_le_P1' : Z ≤ pCoreOf 2 P1' := by
    have hmaple : f112OfA L1 L2 S Z ≤ f112OfA L1 L2 S (pCoreOf 2 P1') := by
      rw [← hD3, ← hQ1]
      exact Subgroup.map_mono hZ.Z_zero_le_Q_one
    have h' : Z.subgroupOf P1 ≤ (pCoreOf 2 P1').subgroupOf P1 :=
      (Subgroup.map_le_map_iff_of_injective (f := (f112Gold L1 L2 S).ofA)
        (f112Gold L1 L2 S).ofA_injective).mp hmaple
    intro z hz
    have hz' : (⟨z, hZ_le_P1 hz⟩ : ↥P1) ∈ Z.subgroupOf P1 :=
      Subgroup.mem_subgroupOf.mpr hz
    exact Subgroup.mem_subgroupOf.mp (h' hz')
  have hpCoreOf_P1'_le_pCoreOf_P1 : pCoreOf 2 P1' ≤ pCoreOf 2 P1 := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 P1').trans hP1'_le_P1) ?_ ?_
    · refine ((Subgroup.normal_subgroupOf_iff_le_normalizer hP1'_le_P1).mp
        (f112sa_P1'_normal hF.toW)).trans ?_
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P1'
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P1'
  have hZ_le_pCoreOf_P1 : Z ≤ pCoreOf 2 P1 :=
    hZ_le_P1'.trans hpCoreOf_P1'_le_pCoreOf_P1
  have hL0_cent : (Y.L 0).map E.subtype ≤
      Subgroup.centralizer ((Y.Z 0).map E.subtype :
        Set (f112Gold L1 L2 S).Universal) := by
    refine (Subgroup.map_mono hZ.L_zero_le_centralizer).trans ?_
    have h := Subgroup.map_centralizer_le_centralizer_image (Y.Z 0 : Set ↥E) E.subtype
    simpa [Subgroup.coe_map] using h
  have hO2cent : oTwoPrime P2' ≤ Subgroup.centralizer (Z : Set H) := by
    have hmap : f112OfB L1 L2 S (oTwoPrime P2') ≤
        Subgroup.centralizer (f112OfA L1 L2 S Z :
          Set (f112Gold L1 L2 S).Universal) := by
      rw [← hL0, ← hD3]
      exact hL0_cent
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hxP2' : x ∈ P2' := oTwoPrime_le P2' hx
    have hxP2 : x ∈ P2 := hP2'_le_P2 hxP2'
    have hzP1 : z ∈ P1 := hZ_le_P1 hz
    have hzP2 : z ∈ P2 := hZ_le_P2 hz
    have hxU : (f112Gold L1 L2 S).ofB ⟨x, hxP2⟩ ∈
        f112OfB L1 L2 S (oTwoPrime P2') :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hzU : (f112Gold L1 L2 S).ofA ⟨z, hzP1⟩ ∈ f112OfA L1 L2 S Z :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
    have hcomm : (f112Gold L1 L2 S).ofA ⟨z, hzP1⟩ *
        (f112Gold L1 L2 S).ofB ⟨x, hxP2⟩ =
        (f112Gold L1 L2 S).ofB ⟨x, hxP2⟩ *
          (f112Gold L1 L2 S).ofA ⟨z, hzP1⟩ :=
      (Subgroup.mem_centralizer_iff.mp (hmap hxU)) _ hzU
    have hzEq : (f112Gold L1 L2 S).ofA ⟨z, hzP1⟩ =
        (f112Gold L1 L2 S).ofB ⟨z, hzP2⟩ :=
      f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hzP1, hzP2⟩
    rw [hzEq] at hcomm
    have hzx : z * x = x * z := by
      have h1 : (f112Gold L1 L2 S).ofB (⟨z, hzP2⟩ * ⟨x, hxP2⟩) =
          (f112Gold L1 L2 S).ofB (⟨x, hxP2⟩ * ⟨z, hzP2⟩) := by
        rw [map_mul, map_mul]
        exact hcomm
      exact congrArg Subtype.val ((f112Gold L1 L2 S).ofB_injective h1)
    exact hzx
  have hO2ResCent : oTwoRes L2 ≤ Subgroup.centralizer (Z : Set H) :=
    hO.trans hO2cent
  have hSinfL2Cent : S ⊓ L2 ≤ Subgroup.centralizer (Z : Set H) :=
    inf_le_left.trans (Subgroup.le_centralizer_iff.mpr hZ_cent_S)
  have hL2cent : L2 ≤ Subgroup.centralizer (Z : Set H) :=
    (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h2.sylow).trans
      (sup_le hO2ResCent hSinfL2Cent)
  have hZ1_le_P1' : sylowCenterCore P1' ≤ P1' :=
    (sylowCenterCore_le_pCoreOf P1').trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P1')
  have hZ1_le_P1 : sylowCenterCore P1' ≤ P1 := hZ1_le_P1'.trans hP1'_le_P1
  have hZ1map : f112OfA L1 L2 S (sylowCenterCore P1') = (Y.Z 1).map E.subtype := by
    have h1 : f112OfA L1 L2 S (sylowCenterCore P1') =
        sylowCenterCore (f112OfA L1 L2 S P1') := by
      rw [show f112OfA L1 L2 S (sylowCenterCore P1') =
        ((sylowCenterCore P1').subgroupOf P1).map (f112Gold L1 L2 S).ofA from rfl,
        sylowCenterCore_subgroupOf hP1'_le_P1,
        map_sylowCenterCore (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective
          (P1'.subgroupOf P1)]
    have h2 : (Y.Z 1).map E.subtype = sylowCenterCore (f112OfA L1 L2 S P1') := by
      rw [show Y.Z 1 = sylowCenterCore (Y.Gi 1) from rfl]
      rw [map_sylowCenterCore E.subtype E.subtype_injective]
      rw [hD1b]
    rw [h1, h2]
  have hY0_le_Y1 : Y.Z 0 ≤ Y.Z 1 := by
    rw [← hZ.iSup_conj_L_one]
    have hconj1 : (Y.Z 0).map (MulAut.conj (1 : ↥E)).toMonoidHom = Y.Z 0 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    exact le_iSup₂_of_le (1 : ↥E) (Y.L 1).one_mem (le_of_eq hconj1.symm)
  have hZleZ1 : Z ≤ sylowCenterCore P1' := by
    have hmaple : f112OfA L1 L2 S Z ≤ f112OfA L1 L2 S (sylowCenterCore P1') := by
      rw [← hD3, hZ1map]
      exact Subgroup.map_mono hY0_le_Y1
    have h' : Z.subgroupOf P1 ≤ (sylowCenterCore P1').subgroupOf P1 :=
      (Subgroup.map_le_map_iff_of_injective (f := (f112Gold L1 L2 S).ofA)
        (f112Gold L1 L2 S).ofA_injective).mp hmaple
    intro z hz
    have hz' : (⟨z, hZ_le_P1 hz⟩ : ↥P1) ∈ Z.subgroupOf P1 :=
      Subgroup.mem_subgroupOf.mpr hz
    exact Subgroup.mem_subgroupOf.mp (h' hz')
  have hP1N : P1 ≤ Subgroup.normalizer (P1' : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP1'_le_P1).mp (f112sa_P1'_normal hF.toW)
  have hL1N : L1 ≤ Subgroup.normalizer (sylowCenterCore P1' : Set H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hgP1 : g ∈ P1 := (show L1 ≤ P1 from le_sup_left) hg
    have hconj : conjSub g P1' = P1' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP1N hgP1)
    have h := CFSG.Quasithin.St84.Setup.iSup_sylow_center_conj g P1'
    rw [hconj] at h
    exact h.symm
  have hVleZ1 : conjClosure Z L1 ≤ sylowCenterCore P1' :=
    conjClosure_le fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.mp (hL1N hg) z).mp (hZleZ1 hz)
  have hU1_le : (Y.Z 1).map E.subtype ≤
      f112OfA L1 L2 S K ⊓ f112OfB L1 L2 S (pCoreOf 2 P2') := by
    refine le_inf ?_ ?_
    · rw [← hD2]
      exact Subgroup.map_mono
        (le_inf (hZ.Z_one_le_Q_zero.trans (Y.Q_le_Gi 0)) (Y.Z_le_Gi 1))
    · rw [← hQ0]
      exact Subgroup.map_mono hZ.Z_one_le_Q_zero
  have hU1_le_A : (Y.Z 1).map E.subtype ≤
      f112OfA L1 L2 S (K ⊓ pCoreOf 2 P2') := by
    rw [← ofA_map_inf_ofB_map L1 L2 S hK_le_P1
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 P2').trans hP2'_le_P2)]
    exact hU1_le
  have hZ1_le_pcore : sylowCenterCore P1' ≤ pCoreOf 2 P2' := by
    have hmap : f112OfA L1 L2 S (sylowCenterCore P1') ≤
        f112OfA L1 L2 S (K ⊓ pCoreOf 2 P2') := by
      rw [hZ1map]
      exact hU1_le_A
    have h' : (sylowCenterCore P1').subgroupOf P1 ≤
        (K ⊓ pCoreOf 2 P2').subgroupOf P1 :=
      (Subgroup.map_le_map_iff_of_injective (f := (f112Gold L1 L2 S).ofA)
        (f112Gold L1 L2 S).ofA_injective).mp hmap
    intro z hz
    have hz' : (⟨z, hZ1_le_P1 hz⟩ : ↥P1) ∈ (sylowCenterCore P1').subgroupOf P1 :=
      Subgroup.mem_subgroupOf.mpr hz
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (h' hz'))).2
  have hinf_le_K : P1' ⊓ pCoreOf 2 P2' ≤ K := by
    have h1 : P1' ⊓ pCoreOf 2 P2' ≤ P1' ⊓ P2 :=
      le_inf inf_le_left
        (inf_le_right.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 P2').trans hP2'_le_P2))
    calc P1' ⊓ pCoreOf 2 P2' ≤ P1' ⊓ P2 := h1
      _ = P1' ⊓ bigB L1 L2 S := by
          rw [← f112_inf_eq_bigB_of_hyp111R hR, ← inf_assoc, inf_of_le_left hP1'_le_P1]
      _ = K := f112sa_P1'_inf_bigB hF.toW
  have hZ1_le_K : sylowCenterCore P1' ≤ K :=
    (le_inf hZ1_le_P1' hZ1_le_pcore).trans hinf_le_K
  have hP2N : P2 ≤ Subgroup.normalizer (P2' : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP2'_le_P2).mp (f112sa_P2'_normal hF.toW)
  have hpcoreP2'_le_pcoreP2 : pCoreOf 2 P2' ≤ pCoreOf 2 P2 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 P2').trans hP2'_le_P2)
      (hP2N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P2'))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P2')
  have hVle : conjClosure Z L1 ≤ pCoreOf 2 P2 :=
    hVleZ1.trans (hZ1_le_pcore.trans hpcoreP2'_le_pcoreP2)
  have hcardZ1 : Nat.card ↥(sylowCenterCore P1') = 4 := by
    have h := card_of_map_eq (L1 := L1) (L2 := L2) (S := S) (E := E)
      (Y' := Y.Z 1) (Y := sylowCenterCore P1') hZ1_le_P1 hZ1map.symm
    rw [hZ.card_Z_one] at h
    exact h.symm
  have hVdvd : Nat.card ↥(conjClosure Z L1) ∣ 4 := by
    rw [← hcardZ1]
    exact Subgroup.card_dvd_of_le hVleZ1
  have hVge : 2 ≤ Nat.card ↥(conjClosure Z L1) := by
    have h := Subgroup.card_le_of_le (le_conjClosure Z L1)
    rwa [hcardZ] at h
  have hVle4 : Nat.card ↥(conjClosure Z L1) ≤ 4 := Nat.le_of_dvd (by norm_num) hVdvd
  have hVne3 : Nat.card ↥(conjClosure Z L1) ≠ 3 := by
    intro h3
    rw [h3] at hVdvd
    norm_num at hVdvd
  have hVcases : Nat.card ↥(conjClosure Z L1) = 2 ∨
      Nat.card ↥(conjClosure Z L1) = 4 := by omega
  have hVcard : Nat.card ↥(conjClosure Z L1) = 4 := by
    rcases hVcases with h2 | h4
    · exfalso
      have hVeqZ : Z = conjClosure Z L1 :=
        Subgroup.eq_of_le_of_card_ge (le_conjClosure Z L1) (by rw [h2, hcardZ])
      have hL1NZ : L1 ≤ Subgroup.normalizer (Z : Set H) := by
        intro g hg
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        have hVnorm : g ∈ Subgroup.normalizer (conjClosure Z L1 : Set H) :=
          le_normalizer_conjClosure Z L1 hg
        rw [hVeqZ]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hVnorm
      have hL2NZ : L2 ≤ Subgroup.normalizer (Z : Set H) :=
        hL2cent.trans (Subgroup.centralizer_le_normalizer (Z : Set H))
      have hP1'NZ : P1' ≤ Subgroup.normalizer (Z : Set H) :=
        sup_le ((oTwoRes_le L1).trans hL1NZ)
          ((f112sa_X2_le_oTwoRes L1 L2 S).trans ((oTwoRes_le L2).trans hL2NZ))
      have hP1'NZ_map : f112OfA L1 L2 S P1' ≤
          Subgroup.normalizer (f112OfA L1 L2 S Z :
            Set (f112Gold L1 L2 S).Universal) := by
        have hsub : P1'.subgroupOf P1 ≤
            Subgroup.normalizer ((Z.subgroupOf P1 : Subgroup ↥P1) : Set ↥P1) :=
          CFSG.Quasithin.H13.le_normalizer_subgroupOf (L := P1) (A := P1') (B := Z) hP1'NZ
        have hmap := (Subgroup.map_mono hsub).trans
          (Subgroup.le_normalizer_map (f := (f112Gold L1 L2 S).ofA)
            (H := Z.subgroupOf P1))
        simpa only [f112OfA] using hmap
      have hYLN_U : (Y.L 1).map E.subtype ≤
          Subgroup.normalizer ((Y.Z 0).map E.subtype :
            Set (f112Gold L1 L2 S).Universal) := by
        rw [hL1]
        refine (Subgroup.map_mono (Subgroup.subgroupOf_mono P1 (oTwoPrime_le P1'))).trans ?_
        rw [hD3]
        exact hP1'NZ_map
      have hterm : ∀ g ∈ Y.L 1,
          (Y.Z 0).map (MulAut.conj g).toMonoidHom = Y.Z 0 := by
        intro g hg
        have hgnorm : E.subtype g ∈ Subgroup.normalizer
            ((Y.Z 0).map E.subtype : Set (f112Gold L1 L2 S).Universal) :=
          hYLN_U (Subgroup.mem_map_of_mem E.subtype hg)
        have hmap_eq : ((Y.Z 0).map (MulAut.conj g).toMonoidHom).map E.subtype =
            (Y.Z 0).map E.subtype := by
          calc ((Y.Z 0).map (MulAut.conj g).toMonoidHom).map E.subtype
              = (Y.Z 0).map (E.subtype.comp (MulAut.conj g).toMonoidHom) :=
                Subgroup.map_map (Y.Z 0) E.subtype (MulAut.conj g).toMonoidHom
            _ = (Y.Z 0).map ((MulAut.conj (E.subtype g)).toMonoidHom.comp E.subtype) := by
                rw [show E.subtype.comp (MulAut.conj g).toMonoidHom =
                  (MulAut.conj (E.subtype g)).toMonoidHom.comp E.subtype from by
                    ext y
                    simp [MulAut.conj_apply, map_mul]]
            _ = ((Y.Z 0).map E.subtype).map
                  (MulAut.conj (E.subtype g)).toMonoidHom :=
                (Subgroup.map_map (Y.Z 0) (MulAut.conj (E.subtype g)).toMonoidHom
                  E.subtype).symm
            _ = (Y.Z 0).map E.subtype :=
                Subgroup.mem_normalizer_iff_map_conj_eq.mp hgnorm
        exact Subgroup.map_injective E.subtype_injective hmap_eq
      have hY1eq : Y.Z 1 = Y.Z 0 := by
        rw [← hZ.iSup_conj_L_one]
        refine le_antisymm ?_ ?_
        · refine iSup_le fun g => iSup_le fun hg => ?_
          rw [hterm g hg]
        · refine le_iSup₂_of_le (1 : ↥E) (Y.L 1).one_mem ?_
          have hconj1 : (Y.Z 0).map (MulAut.conj (1 : ↥E)).toMonoidHom = Y.Z 0 := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              simpa using hy
            · intro hx
              exact ⟨x, hx, by simp⟩
          rw [hconj1]
      have hcardY1 : Nat.card (Y.Z 1) = 2 := by
        rw [hY1eq, hZ.card_Z_zero]
      have h24 : (2 : ℕ) = 4 := hcardY1.symm.trans hZ.card_Z_one
      omega
    · exact h4
  exact ⟨hcardZ, hZ_cent_S, hZ_le_pCoreOf_P1, hL2cent, hVle, hVcard⟩

end CFSG.Quasithin.F112R.St84
