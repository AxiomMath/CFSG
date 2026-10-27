module

public import CFSG.CGT.Timmesfeld75.WCBasic
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G]

@[expose] def IsCalH (V H : Subgroup G) : Prop :=
  V ≤ H ∧ CFSG.QuasithinUnique.CharTwo H ∧
    Odd ((H ⊓ Subgroup.normalizer (V : Set G)).relIndex H)

@[expose] def IsCalH0 (V H : Subgroup G) : Prop :=
  IsCalH V H ∧ V ≤ pCoreOf 2 H

@[expose] def eSub (V H T : Subgroup G) : Subgroup G :=
  conjClosure (V ⊓ Subgroup.centralizer (T : Set G)) H

private theorem pCoreOf_isPGroup_two (H : Subgroup G) : IsPGroup 2 (pCoreOf 2 H) := by
  rw [CFSG.openPCoreOf_eq_map_pCore]
  exact (CFSG.pCore_isPGroup (G := ↥H) (p := 2)).map H.subtype

theorem isTI_conjSubgroup {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (g : G) :
    CFSG.CGT.Timmesfeld75.IsTI (CFSG.CGT.Timmesfeld75.conjSubgroup g V) := by
  intro x
  have hinf : CFSG.CGT.Timmesfeld75.conjSubgroup g V ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup x (CFSG.CGT.Timmesfeld75.conjSubgroup g V) =
      CFSG.CGT.Timmesfeld75.conjSubgroup g
        (V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (g⁻¹ * x * g) V) := by
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    rw [show CFSG.CGT.Timmesfeld75.conjSubgroup (x * g) V =
        CFSG.CGT.Timmesfeld75.conjSubgroup g
          (CFSG.CGT.Timmesfeld75.conjSubgroup (g⁻¹ * x * g) V) by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      congr 1
      group]
    exact (Subgroup.map_inf V (CFSG.CGT.Timmesfeld75.conjSubgroup (g⁻¹ * x * g) V)
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  rcases hTI (g⁻¹ * x * g) with h | h
  · left
    rw [hinf, h]
    exact Subgroup.map_bot _
  · right
    rw [hinf, h]

theorem isTI_conjSubgroup_quasithin {V : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (g : G) :
    CFSG.CGT.Timmesfeld75.IsTI (CFSG.Quasithin.conjSubgroup V g) := by
  simpa only [CFSG.Quasithin.conjSubgroup, CFSG.CGT.Timmesfeld75.conjSubgroup] using
    isTI_conjSubgroup hTI g⁻¹

theorem isSylowIn_of_isCalH {V H T : Subgroup G} (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    IsSylowIn 2 T H := by
  refine ⟨hT.le.trans inf_le_left, hT.isPGroup, ?_⟩
  have hmul : T.relIndex (H ⊓ Subgroup.normalizer (V : Set G)) *
      (H ⊓ Subgroup.normalizer (V : Set G)).relIndex H = T.relIndex H :=
    Subgroup.relIndex_mul_relIndex T (H ⊓ Subgroup.normalizer (V : Set G)) H hT.le inf_le_left
  intro h
  exact (Nat.prime_two.not_dvd_mul hT.not_dvd_relIndex hH.2.2.not_two_dvd_nat) (hmul ▸ h)

theorem le_of_isCalH {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    V ≤ T := by
  have hVK : V ≤ H ⊓ Subgroup.normalizer (V : Set G) := le_inf hH.1 Subgroup.le_normalizer
  have hVnorm : (V.subgroupOf (H ⊓ Subgroup.normalizer (V : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).mpr inf_le_right
  exact IsSylowIn.le_of_normal hT hVK hVnorm (CFSG.Open.IsElemAbelian.isPGroup hV)

theorem pCoreOf_le_of_isCalH {V H T : Subgroup G} (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    pCoreOf 2 H ≤ T := by
  have hSyl : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  refine IsSylowIn.le_of_normal hSyl (CFSG.openPCoreOf_le 2 H) ?_ (pCoreOf_isPGroup_two H)
  rw [CFSG.openPCoreOf_subgroupOf]
  exact CFSG.pCore_normal

private theorem inf_centralizer_ne_bot_of_le_normalizer [Finite G] {V T : Subgroup G}
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hT2 : IsPGroup 2 T) (hVne : V ≠ ⊥) :
    V ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ := by
  haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
  haveI : (V.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hVsubne : V.subgroupOf T ≠ ⊥ := by
    intro h
    apply hVne
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, h, Subgroup.map_bot]
  have hZ : V.subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hVsubne
  have hZmap : ((V.subgroupOf T) ⊓ Subgroup.center ↥T).map T.subtype ≠ ⊥ :=
    fun h => hZ ((Subgroup.map_eq_bot_iff_of_injective
      ((V.subgroupOf T) ⊓ Subgroup.center ↥T) T.subtype_injective).1 h)
  refine ne_bot_of_le_ne_bot hZmap ?_
  refine (Subgroup.map_inf_le (V.subgroupOf T) (Subgroup.center ↥T) T.subtype).trans
    (inf_le_inf ?_ ?_)
  · exact (Subgroup.map_subgroupOf_eq_of_le hVT).le
  · rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨q, hq⟩)

theorem inf_centralizer_ne_bot [Finite G] {V H T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVne : V ≠ ⊥) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    V ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ :=
  inf_centralizer_ne_bot_of_le_normalizer (le_of_isCalH hV hH hT) (hT.le.trans inf_le_right)
    hT.isPGroup hVne

theorem isCalH_of_le {V H T X : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hTX : T ≤ X) (hXH : X ≤ H) :
    IsCalH V X := by
  have hSylH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hO2H : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
  refine ⟨(le_of_isCalH hV hH hT).trans hTX, ?_, ?_⟩
  · have hO2HX : pCoreOf 2 H ≤ X := hO2H.trans hTX
    have hO2Hnorm : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hXH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H)
    have hO2Hle : pCoreOf 2 H ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2HX hO2Hnorm
        (pCoreOf_isPGroup_two H)
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.centralizer_le hO2Hle hxC
    exact hO2Hle (hH.2.1 (Subgroup.mem_inf.mpr ⟨hXH hxX, hxC'⟩))
  · have hoddH : Odd (T.relIndex H) :=
      Nat.not_even_iff_odd.mp fun hEven => hSylH.not_dvd_relIndex (even_iff_two_dvd.mp hEven)
    have hdvd1 : (X ⊓ Subgroup.normalizer (V : Set G)).relIndex X ∣ T.relIndex X :=
      Subgroup.relIndex_dvd_of_le_left (L := X)
        (le_inf hTX (hT.le.trans inf_le_right))
    have hdvd2 : T.relIndex X ∣ T.relIndex H :=
      ⟨X.relIndex H, (Subgroup.relIndex_mul_relIndex T X H hTX hXH).symm⟩
    have hdvd : (X ⊓ Subgroup.normalizer (V : Set G)).relIndex X ∣ T.relIndex H :=
      hdvd1.trans hdvd2
    have hnotEvenH : ¬ Even (T.relIndex H) := Nat.not_even_iff_odd.mpr hoddH
    exact Nat.not_even_iff_odd.mp fun hEven =>
      hnotEvenH (even_iff_two_dvd.mpr (hEven.two_dvd.trans hdvd))

theorem eSub_le_omegaOneCenter {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    eSub V H T ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  have hVH : V ≤ H := hH.1
  have hO2T : pCoreOf 2 H ≤ T := pCoreOf_le_of_isCalH hH hT
  have hC : V ⊓ Subgroup.centralizer (T : Set G) ≤ omegaOneCenterOf (pCoreOf 2 H) := by
    intro c hc
    obtain ⟨hcV, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcO2 : c ∈ pCoreOf 2 H :=
      hH.2.1 ⟨hVH hcV, Subgroup.centralizer_le hO2T hcC⟩
    have hcCtr : c ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.centralizer_le hO2T hcC
    exact mem_omegaOneCenterOf hcO2
      (fun y hy => Subgroup.mem_centralizer_iff.mp hcCtr y hy) (hV.2 c hcV)
  rw [eSub]
  refine conjClosure_le fun h hh c hc => ?_
  have hHnorm : H ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H).trans
      (normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H))
  exact (Subgroup.mem_normalizer_iff.mp (hHnorm hh) c).1 (hC hc)

theorem eSub_isElemAbelian {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    IsElemAbelian 2 (eSub V H T) :=
  CFSG.Open.IsElemAbelian.mono (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 H))
    (eSub_le_omegaOneCenter hV hH hT)

theorem eSub_le_pCoreOf {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    eSub V H T ≤ pCoreOf 2 H :=
  (eSub_le_omegaOneCenter hV hH hT).trans (omegaOneCenterOf_le (pCoreOf 2 H))

theorem eSub_centralizes_pCoreOf {V H T : Subgroup G} (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) :
    eSub V H T ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  refine (eSub_le_omegaOneCenter hV hH hT).trans ?_
  intro x hx
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    mem_centralizer_of_mem_omegaOneCenterOf hx hy

theorem eight_one {V U E : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hUV : U ≤ V)
    (hUn : U ≤ Subgroup.normalizer (E : Set G)) (hEV : E ⊓ V = ⊥)
    {u : G} (huU : u ∈ U) (hu1 : u ≠ 1) :
    E ⊓ Subgroup.centralizer (U : Set G) = E ⊓ Subgroup.centralizer ({u} : Set G) := by
  refine le_antisymm ?_ ?_
  · exact inf_le_inf_left E (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU))
  · intro e he
    obtain ⟨heE, heC⟩ := Subgroup.mem_inf.mp he
    have huV : u ∈ V := hUV huU
    have hcomm : u * e = e * u := Subgroup.mem_centralizer_iff.mp heC u (Set.mem_singleton u)
    have hTI_e : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup e V = V := by
      rcases hTI e with h | h
      · exfalso
        have hu : u ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup e V := by
          refine ⟨huV, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_⟩
          have : e⁻¹ * u * e = u := by
            rw [show e⁻¹ * u * e = e⁻¹ * (u * e) by group, hcomm]
            group
          simpa [this] using huV
        rw [h, Subgroup.mem_bot] at hu
        exact hu1 hu
      · exact h
    have hTI_e' : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup e⁻¹ V = V := by
      rcases hTI e⁻¹ with h | h
      · exfalso
        have hu : u ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup e⁻¹ V := by
          refine ⟨huV, CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_⟩
          have : e * u * e⁻¹ = u := by rw [← hcomm]; group
          simpa [this] using huV
        rw [h, Subgroup.mem_bot] at hu
        exact hu1 hu
      · exact h
    have hle_e : V ≤ CFSG.CGT.Timmesfeld75.conjSubgroup e V :=
      (le_of_eq hTI_e.symm).trans inf_le_right
    have hle_e' : V ≤ CFSG.CGT.Timmesfeld75.conjSubgroup e⁻¹ V :=
      (le_of_eq hTI_e'.symm).trans inf_le_right
    have heN : e ∈ Subgroup.normalizer (V : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hxV
        simpa using CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp (hle_e' hxV)
      · intro hx
        have hx'' := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp (hle_e hx)
        have : e⁻¹ * (e * x * e⁻¹) * e = x := by group
        rwa [this] at hx''
    refine Subgroup.mem_inf.mpr ⟨heE, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hxU
    have hxV : x ∈ V := hUV hxU
    have hxN : x ∈ Subgroup.normalizer (E : Set G) := hUn hxU
    have hmemV : e⁻¹ * x * e * x⁻¹ ∈ V := by
      have h1 : e⁻¹ * x * e ∈ V := (Subgroup.mem_normalizer_iff''.mp heN x).1 hxV
      simpa [mul_assoc] using V.mul_mem h1 (V.inv_mem hxV)
    have hmemE : e⁻¹ * x * e * x⁻¹ ∈ E := by
      have h2 : x * e * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxN e).1 heE
      simpa [mul_assoc] using E.mul_mem (E.inv_mem heE) h2
    have h1 : e⁻¹ * x * e * x⁻¹ = 1 := by
      have := Subgroup.mem_bot.mp (hEV ▸ Subgroup.mem_inf.mpr ⟨hmemE, hmemV⟩)
      simpa using this
    have h2 : e⁻¹ * x * e = x := by
      calc e⁻¹ * x * e = (e⁻¹ * x * e * x⁻¹) * x := by group
        _ = 1 * x := by rw [h1]
        _ = x := one_mul x
    calc x * e = e * (e⁻¹ * x * e) := by group
      _ = e * x := by rw [h2]

end CFSG.LocalAnalysis.WeakClosure81

end
