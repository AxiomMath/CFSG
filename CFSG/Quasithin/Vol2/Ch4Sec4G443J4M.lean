module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4C
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4T
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E9Mp
public import CFSG.RankThree.Asc83Table.M22
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4A
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4D
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E1Basic
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem VB_le_centerOf {T M L B Tp VB : Subgroup G} (s : Setting443 G T M L B Tp VB) :
    VB ≤ centerOf (pCoreOf 2 (perfectCore (conjClosure L T ⊓
      Subgroup.centralizer (B : Set G)))) := by
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  have hVT : VB ≤ T := E443.VB_le_T s
  have hVMp : VB ≤ conjClosure L T := by
    rw [s.hyp.VB_eq]
    exact commutator_le_right_of_le_normalizer (hVT.trans (le_normalizer_conjClosure L T))
  have hVN : VB ≤ Subgroup.normalizer (LB : Set G) := fun v hv =>
    normalizer_le_normalizer_perfectCore _
      (Subgroup.le_normalizer (⟨hVMp hv, E443.VB_le_centralizer s hv⟩ :
        v ∈ conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))
  have hVLB : VB ≤ LB := by
    rw [s.VB_eq_commutator_LB]
    exact commutator_le_right_of_le_normalizer hVN
  have hLBV : LB ≤ Subgroup.normalizer (VB : Set G) :=
    (E443.LB_le L T B).trans (le_sup_left.trans s.hyp.VB_normalized)
  exact le_inf (le_pCoreOf_of_le_normalizer 2 hVLB hLBV (s.hyp.sylow.1.to_le hVT))
    (E443.VB_le_centralizer_pCoreOf_LB s)

theorem gap443J4_of
    (h39 : A39ForSQTK) (hA21 : AsA21SQTKSection)
    (hLoc : KG443J4Loc) (hGenM : KG443J4GenM24) (hGenL : KG443J4GenL52) : E443.Gap443J4 := by
  intro G _ _ T M L B Tp VB K s hU hO hKB hNK hq hKM hVK hLK hC hJ hLB
  classical
  set Mp := conjClosure L T with hMp
  set LB := perfectCore (Mp ⊓ Subgroup.centralizer (B : Set G)) with hLBdef
  set X := conjClosure B T with hXdef
  have hT := s.hyp.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKs : IsSimpleGroup ↥K := isSimpleGroup_of_isSporadic_j4 hJ
  have hout := all_inner_of_isSporadic_j4 hJ
  have hKp : ⁅K, K⁆ = K := by
    have h' := congrArg (Subgroup.map K.subtype) (Group.isPerfect_def.1 hq.1)
    rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h'
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer.trans hNK
  have hKC : K ≤ Subgroup.centralizer (B : Set G) :=
    le_centralizer_of_le_normalizer hKs hKp hKB hBK s.hyp.B_comm
  have hcore : perfectCore (Subgroup.normalizer (B : Set G)) = K :=
    perfectCore_eq_of_inner hKB hNK hKp hout (by rw [hC]; exact odd_card_oddCoreIn _)
  have hVT : VB ≤ T := E443.VB_le_T s
  have hTV : T ≤ Subgroup.normalizer (VB : Set G) := le_sup_right.trans s.hyp.VB_normalized
  obtain ⟨z, hzV, hz1, hzT⟩ := exists_mem_center hT.1 hVT hTV s.hyp.VB_ne_bot
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hzV)).2.2
  have hSyl : IsSylowTwoOf (T ⊓ LB) LB := isSylowTwoOf_inf hT (le_normalizer_conjClosure L T)
    (lemma_4_4_5_orbit s.hyp.toHyp4_4_1TwoOrbit)
  have hzS : z ∈ Subgroup.centralizer ((T ⊓ LB : Subgroup G) : Set G) :=
    Subgroup.centralizer_le inf_le_left hzT
  set H := Subgroup.centralizer ({z} : Set G) with hH
  set KZ := perfectCore (K ⊓ H) with hKZdef
  obtain ⟨hhat, hKeq⟩ : IsHat (↥KZ ⧸ CFSG.pCore 2 ↥KZ) (NativeSporadic.Carrier .M22) ∧
      K = LB ⊔ KZ := by
    rcases hLB with h | h
    · exact hGenM G K LB VB (T ⊓ LB) z hJ hLK (perfectCore_perfect _) h (VB_le_centerOf s)
        s.hyp.VB_ne_bot s.VB_eq_commutator_LB hSyl hzV hz1 hzS
    · exact hGenL G K LB VB (T ⊓ LB) z hJ hLK (perfectCore_perfect _) h (VB_le_centerOf s)
        s.hyp.VB_ne_bot s.VB_eq_commutator_LB hSyl hzV hz1 hzS
  have hKZK : KZ ≤ K := (perfectCore_le _).trans inf_le_left
  have hKZH : KZ ≤ H := (perfectCore_le _).trans inf_le_right
  have hKZp : ⁅KZ, KZ⁆ = KZ := perfectCore_perfect _
  obtain ⟨g, hg, hgk⟩ := exists_surj_of_isHat hhat
  have hM22 : 2 ≤ CFSG.pRank 3 (NativeSporadic.Carrier .M22) :=
    (CFSG.RankThree.Asc83Table.M22.table ⟨MulEquiv.refl _⟩).2.1.ge
  have : IsSimpleGroup (NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have : Finite (NativeSporadic.Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  have hBH : B ≤ H := by
    intro b hb
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.mp (E443.VB_le_centralizer s hzV) b hb).symm
  have hTH : T ≤ H := by
    intro t ht
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.mp hzT t ht).symm
  have hBCK : B ≤ Subgroup.centralizer (K : Set G) := Subgroup.le_centralizer_iff.mp hKC
  have hBK1 : B ⊓ K = ⊥ := by
    rw [eq_bot_iff, ← inf_centralizer_eq_bot hKs hKp]
    exact fun x hx => ⟨hx.2, hBCK hx.1⟩
  have hE := two_le_pRank_of_le_ker g hg hM22 KZ.subtype fun k hk => by
    rw [Subgroup.subtype_apply] at hk
    rw [show k = 1 from Subtype.ext hk, map_one]
  rw [Subgroup.range_subtype] at hE
  have hB6 : Nat.Coprime (Nat.card B) 6 :=
    coprime_six s.hyp.qtke hE hKZK hKZH hBH hBCK hBK1 s.hyp.B_odd hz1 hz2
  have hHO : pCoreOf 2 H ≠ ⊥ := by
    have hzH : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have h1 := le_pCoreOf_of_le_normalizer 2 hzH (centralizer_le_normalizer_zpowers z)
      (isPGroup_zpowers hz1 hz2)
    exact fun h => zpowers_ne_bot hz1 (le_bot_iff.mp (h ▸ h1))
  obtain ⟨LZ, hLZ, hKZLZ, hHLZ⟩ := exists_normal_cComp_ge_of s.hyp.qtke s.hyp.simple
    s.hyp.nonabelian h39 hA21 hHO hKZH hKZp g hg hgk hM22
  have hsqtk : IsSQTKIn H :=
    sqtkGroup_of_pCoreOf_ne_bot s.hyp.qtke s.hyp.simple s.hyp.nonabelian hHO
  have hchar : CharTwo H := charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot s.hyp.qtke.2.1
    (isSylowTwoOf_of_le hT le_top) hTH hHO
  have hLZB : ⁅LZ, B⁆ ≤ pCoreOf 2 LZ := hLoc G H LZ KZ B hsqtk hHO hchar hLZ hKZLZ hhat hBH
    (hBH.trans hHLZ) hB6 (hBCK.trans (Subgroup.centralizer_le hKZK))
  have hMpX : Mp ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_conjClosure_of hT s.hyp.B_odd (le_normalizer_conjClosure L T)
      s.hyp.commutator_le
  have hLZX : LZ ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_conjClosure_of hT s.hyp.B_odd (hTH.trans hHLZ) hLZB
  have hKX : K ≤ Subgroup.normalizer (X : Set G) :=
    hKeq.le.trans (sup_le ((E443.LB_le L T B).trans hMpX) (hKZLZ.trans hLZX))
  have hXV : X ≤ Subgroup.centralizer (VB : Set G) := conjClosure_le fun t ht b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : t⁻¹ * v * t ∈ VB := by
      have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem ht)) v).mp hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (E443.VB_le_centralizer s hv') b hb
    calc v * (t * b * t⁻¹) = t * ((t⁻¹ * v * t) * b) * t⁻¹ := by group
      _ = t * (b * (t⁻¹ * v * t)) * t⁻¹ := by rw [← h1]
      _ = t * b * t⁻¹ * v := by group
  have hKCX : K ≤ Subgroup.centralizer (X : Set G) :=
    le_centralizer_of_simple hKs hKX hVK s.hyp.VB_ne_bot hXV
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_le_centralizer hcore hKp hKCX
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hcharM : CharTwo M := s.hyp.qtke.2.1 M s.hyp.maxTwoLocal.1 ⟨S, hS ▸ s.hyp.T_le⟩
  exact false_of_le_normalizer hT hKs hKp hout hTK hU
    (sup_le (hLK.trans le_sup_left) ((inf_le_left.trans s.hyp.Tp_le).trans le_sup_right)) hKM hKC
    s.hyp.B_le s.hyp.B_ne_bot s.hyp.B_odd
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le hT s.hyp.T_le)) hcharM

end CFSG.Quasithin.H13.Ch4.G443J4
