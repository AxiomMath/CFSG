module

public import CFSG.Sporadic.Th.Recog.Setting
public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Max3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev zM : ↥Max3.M := ⟨Max3.z, Max3.z_mem_M⟩

theorem center_M : Subgroup.center (↥Max3.M) = Subgroup.zpowers zM := by
  refine le_antisymm ?_ ?_
  · intro u hu
    have hmem : (u : J) ∈ Subgroup.centralizer (Max3.Q : Set J) ⊓ Max3.M := by
      refine ⟨?_, u.2⟩
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro g hg
      let m : ↥Max3.M := ⟨g, Max3.Q_le_M hg⟩
      have hcomm : m * u = u * m := Subgroup.mem_center_iff.mp hu m
      have h' : ((m * u : ↥Max3.M) : J) = ((u * m : ↥Max3.M) : J) :=
        Subtype.ext_iff.mp hcomm
      simpa [m] using h'
    rw [Max3.centralizer_Q_inf_M] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by simpa [zM] using hk)⟩
  · rw [Subgroup.zpowers_le]
    exact Max3.z_mem_center_M

theorem orderOf_zM : orderOf zM = 2 := by
  change orderOf (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) = 2
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime (by rw [pow_two]; exact Max3.z_mul_self) Max3.z_ne_one

theorem zM_ne_one : zM ≠ 1 := by
  intro h
  have h' : ((zM : ↥Max3.M) : J) = ((1 : ↥Max3.M) : J) := Subtype.ext_iff.mp h
  exact Max3.z_ne_one (by simpa [zM] using h')

theorem zM_mul_self : zM * zM = 1 := Subtype.ext Max3.z_mul_self

@[expose] noncomputable def ThCore.psiG (C : ThCore G) : ↥Max3.M →* G where
  toFun := fun m => (C.ψ m : G)
  map_one' := by simp
  map_mul' := by intro a b; simp

theorem ThCore.psiG_injective (C : ThCore G) : Function.Injective C.psiG := by
  intro a b h
  exact C.ψ.injective (Subtype.ext h)

theorem ThCore.psiG_apply (C : ThCore G) (m : ↥Max3.M) : C.psiG m = (C.ψ m : G) := rfl

theorem ThCore.psiG_range (C : ThCore G) :
    C.psiG.range = Subgroup.centralizer ({C.z} : Set G) := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact (C.ψ m).2
  · intro hy
    exact ⟨C.ψ.symm ⟨y, hy⟩, congrArg Subtype.val (C.ψ.apply_symm_apply ⟨y, hy⟩)⟩

theorem ThCore.orderOf_z (C : ThCore G) : orderOf C.z = 2 := by
  obtain ⟨g, hg⟩ := C.conj (C.ψ zM : G) (by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_zM])
  have hsem : SemiconjBy g C.z (C.ψ zM : G) := by
    show g * C.z = (C.ψ zM : G) * g
    calc g * C.z = (g * C.z * g⁻¹) * g := by group
      _ = (C.ψ zM : G) * g := by rw [hg]
  rw [hsem.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_zM]

theorem ThCore.psi_z (C : ThCore G) : (C.ψ zM : G) = C.z := by
  have hzH : C.z ∈ Subgroup.centralizer ({C.z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by group)
  let u : ↥Max3.M := C.ψ.symm ⟨C.z, hzH⟩
  have hψu : C.ψ u = ⟨C.z, hzH⟩ := C.ψ.apply_symm_apply _
  have hzcentralH : (⟨C.z, hzH⟩ : ↥(Subgroup.centralizer ({C.z} : Set G))) ∈
      Subgroup.center ↥(Subgroup.centralizer ({C.z} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hucenter : u ∈ Subgroup.center (↥Max3.M) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply C.ψ.injective
    change C.ψ (y * u) = C.ψ (u * y)
    rw [map_mul, map_mul, hψu]
    exact Subgroup.mem_center_iff.mp hzcentralH (C.ψ y)
  rw [center_M] at hucenter
  have hzHne : C.z ≠ 1 := by
    intro h
    have hord := C.orderOf_z
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hu1 : u ≠ 1 := by
    intro h
    have hψ1 : C.ψ u = 1 := by rw [h, map_one]
    rw [hψu] at hψ1
    exact hzHne (Subtype.ext_iff.mp hψ1)
  have hu_eq : u = 1 ∨ u = zM := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hucenter
    rw [← hk]
    have h2 : zM ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, zM_mul_self]
    obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
    · left; rw [hn, zpow_mul, h2, one_zpow]
    · right
      rw [hn, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  rcases hu_eq with h | h
  · exact absurd h hu1
  · rw [h] at hψu
    exact congrArg Subtype.val hψu

theorem ThCore.map_centralizer (C : ThCore G) (m : ↥Max3.M) :
    (Subgroup.centralizer ({m} : Set ↥Max3.M)).map C.psiG =
      Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({(C.ψ m : G)} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hx' : x * m = m * x := by
      have h := (Subgroup.mem_centralizer_iff.mp hx) m (by simp)
      exact h.symm
    refine ⟨(C.ψ x).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change C.psiG x * C.psiG m = C.psiG m * C.psiG x
    rw [← map_mul, ← map_mul, hx']
  · intro y hy
    obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyrange : y ∈ C.psiG.range := by
      rw [C.psiG_range]
      exact hyH
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hyrange
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply C.psiG_injective
    change C.psiG (x * m) = C.psiG (m * x)
    rw [map_mul, map_mul]
    have h := (Subgroup.mem_centralizer_iff.mp hyC) (C.ψ m : G) (by simp)
    simpa [C.psiG_apply] using h.symm

theorem ThCore.card_centralizer_inf (C : ThCore G) (m : ↥Max3.M) :
    Nat.card ↥(Subgroup.centralizer ({C.z} : Set G) ⊓
        Subgroup.centralizer ({(C.ψ m : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({m} : Set ↥Max3.M)) := by
  rw [← C.map_centralizer m, Subgroup.card_map_of_injective C.psiG_injective]

theorem ThCore.exists_sylow_eq (C : ThCore G) {tM : ↥Max3.M}
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    (hT : ∃ T : Subgroup ↥Max3.M, T ≤ Subgroup.centralizer ({tM} : Set ↥Max3.M) ∧
      Nat.card ↥T = 64 ∧ ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ (x : J) = Max3.z)
    {P : Subgroup G} (hP : P ≤ Subgroup.centralizer ({C.z} : Set G) ⊓
      Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) (hc : Nat.card ↥P = 64) :
    ∃ S : Sylow 2 ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)),
      (S : Subgroup _).map (Subgroup.centralizer ({(C.ψ tM : G)} : Set G)).subtype = P := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let CH : Subgroup G := H ⊓ CT
  change P ≤ CH at hP
  have hPCT : P ≤ CT := fun x hx => (hP hx).2
  have hCHcard : Nat.card ↥CH = 1728 := by
    have h := C.card_centralizer_inf tM
    rw [hCt] at h
    exact h
  have h2fac : (Nat.card ↥CH).factorization 2 = 6 := by
    rw [hCHcard]
    norm_num [Nat.factorization]
  let PCH : Sylow 2 ↥CH :=
    Sylow.ofCard (P.subgroupOf CH) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, hc, h2fac]
      norm_num)
  obtain ⟨T, hTle, hTcard, hTz⟩ := hT
  let Tψ : Subgroup G := T.map C.psiG
  have hTψcard : Nat.card ↥Tψ = 64 := by
    rw [Subgroup.card_map_of_injective C.psiG_injective, hTcard]
  have hTψH : Tψ ≤ H := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (C.ψ t).2
  have hTψCT : Tψ ≤ CT := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hcomm : t * tM = tM * t := by
      have h := (Subgroup.mem_centralizer_iff.mp (hTle ht)) tM (by simp)
      exact h.symm
    have h' := congrArg C.psiG hcomm
    rw [map_mul, map_mul] at h'
    simpa [C.psiG_apply] using h'.symm
  have hTψCH : Tψ ≤ CH := le_inf hTψH hTψCT
  let TCH : Sylow 2 ↥CH :=
    Sylow.ofCard (Tψ.subgroupOf CH) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTψCH).toEquiv, hTψcard, h2fac]
      norm_num)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥CH TCH PCH
  have hmap : (TCH : Subgroup ↥CH).map (MulAut.conj h).toMonoidHom =
      (PCH : Subgroup ↥CH) := by
    have h' := congrArg (fun R : Sylow 2 ↥CH => (R : Subgroup ↥CH)) hh
    rw [Sylow.coe_subgroup_smul] at h'
    rw [← h']
    ext z
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, by simp [MulAut.smul_def]⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, by simp [MulAut.smul_def]⟩
  have hmap' : (Tψ.subgroupOf CH).map (MulAut.conj h).toMonoidHom =
      P.subgroupOf CH := by
    simpa [TCH, PCH, Sylow.coe_ofCard] using hmap
  have hconj : Tψ.map (MulAut.conj (h : G)).toMonoidHom = P := by
    have hg := congrArg (Subgroup.map CH.subtype) hmap'
    have hcomp : CH.subtype.comp (MulAut.conj h).toMonoidHom =
        ((MulAut.conj (h : G)).toMonoidHom).comp CH.subtype := by
      ext x
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map] at hg
    simpa [Subgroup.map_subgroupOf_eq_of_le hTψCH,
      Subgroup.map_subgroupOf_eq_of_le hP] using hg
  have hhz : (h : G) * C.z = C.z * (h : G) := by
    have hhH : (h : G) ∈ H := (h.2).1
    have := (Subgroup.mem_centralizer_iff.mp hhH) C.z (by simp)
    exact this.symm
  have hZP : ∀ y : ↥P, y ∈ Subgroup.center ↥P → (y : G) = 1 ∨ (y : G) = C.z := by
    intro y hy
    have hyMap : (y : G) ∈ Tψ.map (MulAut.conj (h : G)).toMonoidHom := by
      rw [hconj]
      exact y.2
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hyMap
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hty' : h * C.psiG x * h⁻¹ = (y : G) := by
      simpa [MulAut.conj_apply] using hty
    have hxcent : x ∈ Subgroup.centralizer ({tM} : Set ↥Max3.M) := hTle hx
    have hxcentT : ∀ u ∈ T, x * u = u * x := by
      intro u hu
      have hp_u : h * C.psiG u * h⁻¹ ∈ P := by
        rw [← hconj]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hu)
      have hcomm := Subgroup.mem_center_iff.mp hy ⟨_, hp_u⟩
      have hcommG : (h * C.psiG u * (h : G)⁻¹) * (y : G) =
          (y : G) * (h * C.psiG u * (h : G)⁻¹) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using Subtype.ext_iff.mp hcomm
      have hxeq : C.psiG x = (h : G)⁻¹ * (y : G) * (h : G) := by
        have h' : (h : G) * C.psiG x * (h : G)⁻¹ = (y : G) := hty'
        rw [← h']
        group
      have hpsi : C.psiG x * C.psiG u = C.psiG u * C.psiG x := by
        calc C.psiG x * C.psiG u = ((h : G)⁻¹ * (y : G) * (h : G)) * C.psiG u := by
              rw [hxeq]
          _ = (h : G)⁻¹ * ((y : G) * (h * C.psiG u * (h : G)⁻¹)) * h := by group
          _ = (h : G)⁻¹ * ((h * C.psiG u * (h : G)⁻¹) * (y : G)) * h := by rw [hcommG.symm]
          _ = C.psiG u * ((h : G)⁻¹ * (y : G) * (h : G)) := by group
          _ = C.psiG u * C.psiG x := by rw [hxeq]
      exact C.psiG_injective (by simpa [map_mul] using hpsi)
    rcases hTz x hx hxcentT with hx1 | hxz
    · left
      rw [← hty', hx1]
      simp
    · right
      have hxM : x = (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) := Subtype.ext hxz
      have hpsi_z' : (C.ψ (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) : G) = C.z := by
        simpa [zM] using C.psi_z
      have hxz' : C.psiG x = C.z := by
        rw [C.psiG_apply, hxM, hpsi_z']
      rw [← hty', hxz', hhz]
      show C.z * (h : G) * (h : G)⁻¹ = C.z
      group
  have hzpowers_pair : ∀ {x : G}, x ∈ Subgroup.zpowers C.z → x = 1 ∨ x = C.z := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    have h2 : C.z ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ← C.orderOf_z]
      exact pow_orderOf_eq_one C.z
    · obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
      · left; rw [hn, zpow_mul, h2, one_zpow]
      · right; rw [hn, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card (n := 6) (by rw [hc]; norm_num)
  haveI hPnt : Nontrivial ↥P :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; norm_num)
  have hcenter_nt : Nontrivial ↥(Subgroup.center ↥P) := IsPGroup.center_nontrivial hP2
  obtain ⟨y, hyne⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  have hyz : (((y : ↥(Subgroup.center ↥P)) : ↥P) : G) = C.z := by
    rcases hZP (y : ↥P) y.2 with h | h
    · exfalso
      apply hyne
      exact Subtype.ext (Subtype.ext h)
    · exact h
  have hzP : C.z ∈ P := by
    rw [← hyz]
    exact (y : ↥P).2
  have hzcenter : (⟨C.z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    have hyc : (y : ↥P) ∈ Subgroup.center ↥P := y.2
    have hey : (⟨C.z, hzP⟩ : ↥P) = (y : ↥P) := Subtype.ext hyz.symm
    rw [hey]
    exact hyc
  have hcenter_eq : Subgroup.center ↥P = (Subgroup.zpowers C.z).subgroupOf P := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [Subgroup.mem_subgroupOf]
      rcases hZP z hz with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers C.z
    · intro z hz
      have hz' : (z : G) ∈ Subgroup.zpowers C.z := Subgroup.mem_subgroupOf.mp hz
      rcases hzpowers_pair hz' with h | h
      · have hz1 : z = 1 := by
          apply Subtype.ext
          exact h
        rw [hz1]
        exact Subgroup.one_mem _
      · have heq : z = ⟨C.z, hzP⟩ := Subtype.ext h
        rw [heq]
        exact hzcenter
  have hPsub2 : IsPGroup 2 ↥(P.subgroupOf CT) :=
    IsPGroup.of_card (n := 6) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPCT).toEquiv, hc]
      norm_num)
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow hPsub2
  have hPS_eq : P.subgroupOf CT = (S : Subgroup ↥CT) := by
    by_contra hne
    have hlt : P.subgroupOf CT < (S : Subgroup ↥CT) := lt_of_le_of_ne hPS hne
    let PS : Subgroup ↥S := (P.subgroupOf CT).subgroupOf (S : Subgroup ↥CT)
    have hPSne : PS ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm hPS ?_
      intro z hzS
      have hzPS : (⟨z, hzS⟩ : ↥S) ∈ PS := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hzPS)
    haveI hSnil : Group.IsNilpotent ↥S := IsPGroup.isNilpotent S.isPGroup'
    have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent (G := ↥S)
    have hPSlt : PS < ⊤ := lt_of_le_of_ne le_top hPSne
    have hgrowth : PS < Subgroup.normalizer (PS : Set ↥S) := hnc PS hPSlt
    obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt hgrowth
    let nx : G := (((x : ↥S) : ↥CT) : G)
    have hxCTN : ((x : ↥S) : ↥CT) ∈
        Subgroup.normalizer ((P.subgroupOf CT) : Set ↥CT) := by
      have hsub : x ∈ (Subgroup.normalizer ((P.subgroupOf CT) : Set ↥CT)).subgroupOf
          (S : Subgroup ↥CT) := by
        rw [Subgroup.subgroupOf_normalizer_eq hPS]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp hsub
    have hxnotP : nx ∉ P := by
      intro hxP
      apply hxnot
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_subgroupOf.mpr hxP
    have hxNrm : nx ∈ Subgroup.normalizer (P : Set G) := by
      have hxmap : nx ∈ (Subgroup.normalizer ((P.subgroupOf CT) : Set ↥CT)).map CT.subtype :=
        Subgroup.mem_map_of_mem _ hxCTN
      have hle := Subgroup.le_normalizer_map CT.subtype
        (H := (P.subgroupOf CT))
      rw [Subgroup.map_subgroupOf_eq_of_le hPCT] at hle
      exact hle hxmap
    have hnz : nx * C.z * nx⁻¹ = C.z := by
      have hmemP : nx * C.z * nx⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hxNrm C.z).mp hzP
      have hmemCenter : (⟨nx * C.z * nx⁻¹, hmemP⟩ : ↥P) ∈ Subgroup.center ↥P := by
        rw [Subgroup.mem_center_iff]
        intro p
        have hpInv : nx⁻¹ * (p : G) * nx ∈ P := by
          have hinv : nx⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
            (Subgroup.normalizer (P : Set G)).inv_mem hxNrm
          have h : nx⁻¹ * (p : G) * (nx⁻¹)⁻¹ ∈ P :=
            (Subgroup.mem_normalizer_iff.mp hinv (p : G)).mp p.2
          rwa [inv_inv] at h
        let q : ↥P := ⟨nx⁻¹ * (p : G) * nx, hpInv⟩
        have hqp : nx * (q : G) * nx⁻¹ = (p : G) := by
          dsimp [q]; group
        have hqz : (q : G) * C.z = C.z * (q : G) :=
          Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hzcenter q)
        apply Subtype.ext
        calc ((p : ↥P) : G) * (nx * C.z * nx⁻¹) =
              (nx * (q : G) * nx⁻¹) * (nx * C.z * nx⁻¹) := by rw [hqp]
          _ = nx * ((q : G) * C.z) * nx⁻¹ := by group
          _ = nx * (C.z * (q : G)) * nx⁻¹ := by rw [hqz]
          _ = (nx * C.z * nx⁻¹) * (nx * (q : G) * nx⁻¹) := by group
          _ = (nx * C.z * nx⁻¹) * (p : G) := by rw [hqp]
      have hmemZp : nx * C.z * nx⁻¹ ∈ Subgroup.zpowers C.z := by
        have h' := hcenter_eq ▸ hmemCenter
        exact Subgroup.mem_subgroupOf.mp h'
      rcases hzpowers_pair hmemZp with h | h
      · exfalso
        have hord : orderOf (nx * C.z * nx⁻¹) = 2 := by
          have hsem : SemiconjBy nx C.z (nx * C.z * nx⁻¹) := by
            show nx * C.z = (nx * C.z * nx⁻¹) * nx
            group
          rw [← hsem.orderOf_eq]
          exact C.orderOf_z
        rw [h, orderOf_one] at hord
        norm_num at hord
      · exact h
    have hcommz : nx * C.z = C.z * nx := by
      calc nx * C.z = (nx * C.z * nx⁻¹) * nx := by group
        _ = C.z * nx := by rw [hnz]
    have hnxH : nx ∈ H := by
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hcommz.symm
    have hnxCH : nx ∈ CH := ⟨hnxH, (x : ↥CT).2⟩
    have hsupCH : P ⊔ Subgroup.zpowers nx ≤ CH :=
      sup_le hP (Subgroup.zpowers_le.mpr hnxCH)
    have hleS : P ⊔ Subgroup.zpowers nx ≤ (S : Subgroup ↥CT).map CT.subtype := by
      refine sup_le ?_ ?_
      · rw [← Subgroup.map_subgroupOf_eq_of_le hPCT]
        exact Subgroup.map_mono hPS
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_map_of_mem _ x.2
    have hSmap2 : IsPGroup 2 ↥((S : Subgroup ↥CT).map CT.subtype) :=
      S.isPGroup'.map CT.subtype
    have hsup2 : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers nx) :=
      IsPGroup.to_le hSmap2 hleS
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hsup2
    have hdiv : 2 ^ n ∣ Nat.card ↥CH := by
      have hEq : Nat.card ↥((P ⊔ Subgroup.zpowers nx).subgroupOf CH) =
          Nat.card ↥(P ⊔ Subgroup.zpowers nx) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsupCH).toEquiv
      have hd := Subgroup.card_subgroup_dvd_card ((P ⊔ Subgroup.zpowers nx).subgroupOf CH)
      rwa [hEq, hn] at hd
    have hle6 : n ≤ 6 := by
      have hfac := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (n := Nat.card ↥CH) (k := n) (by rw [hCHcard]; norm_num)).mp hdiv
      rwa [h2fac] at hfac
    have hcardle : Nat.card ↥(P ⊔ Subgroup.zpowers nx) ≤ 64 := by
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hle6
        _ = 64 := by norm_num
    have hcardlt : Nat.card ↥P < Nat.card ↥(P ⊔ Subgroup.zpowers nx) := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) ?_
      intro heq
      have hsup_eq : P ⊔ Subgroup.zpowers nx = P :=
        (Subgroup.eq_of_le_of_card_ge (H := P) (K := P ⊔ Subgroup.zpowers nx)
          le_sup_left (le_of_eq heq.symm)).symm
      have hmem : nx ∈ P ⊔ Subgroup.zpowers nx :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers nx)
      rw [hsup_eq] at hmem
      exact hxnotP hmem
    rw [hc] at hcardlt
    omega
  have hmapS : (S : Subgroup ↥CT).map CT.subtype = P := by
    rw [← hPS_eq, Subgroup.map_subgroupOf_eq_of_le hPCT]
  exact ⟨S, hmapS⟩

theorem ThCore.exists_conj_eq_z (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    (h3 : ∀ x w : ↥Max3.M, orderOf x = 3 → w * w = 1 → w ≠ 1 → (w : J) ≠ Max3.z →
      w * x = x * w → ∃ m : ↥Max3.M, m * x * m⁻¹ = tM)
    {j : G} (hj : j ∈ Subgroup.centralizer ({(C.ψ tM : G)} : Set G))
    (hj2 : orderOf j = 2) :
    ∃ y ∈ Subgroup.centralizer ({(C.ψ tM : G)} : Set G), y * j * y⁻¹ = C.z := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let tG : G := (C.ψ tM : G)
  change j ∈ CT at hj
  have htG3 : orderOf tG = 3 := by
    rw [show tG = (C.ψ tM : G) from rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hz2 : C.z * C.z = 1 := by
    have := pow_orderOf_eq_one C.z
    rwa [C.orderOf_z, pow_two] at this
  have hzCT : C.z ∈ CT := by
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (C.ψ tM).2
  have hzCT' : C.z ∈ CT := hzCT
  have stepA : ∀ {i : G}, i ∈ CT → orderOf i = 2 → i * C.z = C.z * i →
      ∃ y ∈ CT, y * i * y⁻¹ = C.z := by
    intro i hiCT hi2 hicomm
    by_cases hiz : i = C.z
    · exact ⟨1, Subgroup.one_mem _, by rw [hiz]; group⟩
    · obtain ⟨g, hg⟩ := C.conj i hi2
      let t' : G := g⁻¹ * tG * g
      let w : G := g⁻¹ * C.z * g
      have hig : g⁻¹ * i * g = C.z := by
        calc g⁻¹ * i * g = g⁻¹ * (g * C.z * g⁻¹) * g := by rw [← hg]
          _ = C.z := by group
      have hw2 : w * w = 1 := by
        change (g⁻¹ * C.z * g) * (g⁻¹ * C.z * g) = 1
        calc (g⁻¹ * C.z * g) * (g⁻¹ * C.z * g) = g⁻¹ * (C.z * C.z) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hz2]
          _ = 1 := by group
      have hword : orderOf w = 2 := by
        have hsem : SemiconjBy g⁻¹ C.z w := by
          change g⁻¹ * C.z = (g⁻¹ * C.z * g) * g⁻¹
          group
        rw [← hsem.orderOf_eq]
        exact C.orderOf_z
      have hw1 : w ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hword
        norm_num at hword
      have hwz : w ≠ C.z := by
        intro h
        apply hiz
        rw [← hg]
        have h1 : C.z * g = g * C.z := by
          calc C.z * g = g * (g⁻¹ * C.z * g) := by group
            _ = g * C.z := by
              rw [show g⁻¹ * C.z * g = w from rfl, h]
        calc g * C.z * g⁻¹ = (C.z * g) * g⁻¹ := by rw [← h1]
          _ = C.z := by group
      have hwH : w ∈ H := by
        have hcomm : w * (g⁻¹ * i * g) = (g⁻¹ * i * g) * w := by
          change (g⁻¹ * C.z * g) * (g⁻¹ * i * g) =
            (g⁻¹ * i * g) * (g⁻¹ * C.z * g)
          calc (g⁻¹ * C.z * g) * (g⁻¹ * i * g) = g⁻¹ * (C.z * i) * g := by group
            _ = g⁻¹ * (i * C.z) * g := by rw [hicomm]
            _ = (g⁻¹ * i * g) * (g⁻¹ * C.z * g) := by group
        rw [hig] at hcomm
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have htj : tG * i = i * tG :=
        (Subgroup.mem_centralizer_iff.mp hiCT) tG (by rfl)
      have ht'H : t' ∈ H := by
        have hcomm : t' * (g⁻¹ * i * g) = (g⁻¹ * i * g) * t' := by
          change (g⁻¹ * tG * g) * (g⁻¹ * i * g) =
            (g⁻¹ * i * g) * (g⁻¹ * tG * g)
          calc (g⁻¹ * tG * g) * (g⁻¹ * i * g) = g⁻¹ * (tG * i) * g := by group
            _ = g⁻¹ * (i * tG) * g := by rw [htj]
            _ = (g⁻¹ * i * g) * (g⁻¹ * tG * g) := by group
        rw [hig] at hcomm
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have htGz : tG * C.z = C.z * tG :=
        Subgroup.mem_centralizer_singleton_iff.mp (C.ψ tM).2
      have ht'w : t' * w = w * t' := by
        change (g⁻¹ * tG * g) * (g⁻¹ * C.z * g) =
          (g⁻¹ * C.z * g) * (g⁻¹ * tG * g)
        calc (g⁻¹ * tG * g) * (g⁻¹ * C.z * g) = g⁻¹ * (tG * C.z) * g := by group
          _ = g⁻¹ * (C.z * tG) * g := by rw [htGz]
          _ = (g⁻¹ * C.z * g) * (g⁻¹ * tG * g) := by group
      have ht'ord : orderOf t' = 3 := by
        have hsem : SemiconjBy g⁻¹ tG t' := by
          change g⁻¹ * tG = (g⁻¹ * tG * g) * g⁻¹
          group
        rw [← hsem.orderOf_eq]
        exact htG3
      let x : ↥Max3.M := C.ψ.symm ⟨t', ht'H⟩
      have hxval : (C.ψ x : G) = t' := by
        exact congrArg Subtype.val (C.ψ.apply_symm_apply ⟨t', ht'H⟩)
      have hxord : orderOf x = 3 := by
        calc orderOf x = orderOf (C.psiG x) :=
              (orderOf_injective C.psiG C.psiG_injective x).symm
          _ = orderOf t' := by rw [C.psiG_apply, hxval]
          _ = 3 := ht'ord
      let w' : ↥Max3.M := C.ψ.symm ⟨w, hwH⟩
      have hw'val : (C.ψ w' : G) = w := by
        exact congrArg Subtype.val (C.ψ.apply_symm_apply ⟨w, hwH⟩)
      have hw'eq : C.ψ w' = ⟨w, hwH⟩ := C.ψ.apply_symm_apply ⟨w, hwH⟩
      have hw'2 : w' * w' = 1 := by
        apply C.ψ.injective
        rw [map_mul, hw'eq, map_one]
        exact Subtype.ext hw2
      have hw'ord : orderOf w' = 2 := by
        calc orderOf w' = orderOf (C.psiG w') :=
              (orderOf_injective C.psiG C.psiG_injective w').symm
          _ = orderOf w := by rw [C.psiG_apply, hw'val]
          _ = 2 := hword
      have hw'1 : w' ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hw'ord
        norm_num at hw'ord
      have hw'z : (w' : J) ≠ Max3.z := by
        intro h
        have hw'M : w' = zM := Subtype.ext h
        have hzval : (C.ψ zM : G) = C.z := C.psi_z
        have : w = C.z := by
          rw [← hw'val, hw'M, hzval]
        exact hwz this
      have hw'x : w' * x = x * w' := by
        apply C.ψ.injective
        rw [map_mul, map_mul]
        exact Subtype.ext (by simpa [Subgroup.coe_mul, hw'val, hxval] using ht'w.symm)
      obtain ⟨m, hm⟩ := h3 x w' hxord hw'2 hw'1 hw'z hw'x
      let c : G := g * (C.psiG m)⁻¹
      have hψm : C.psiG m * t' * (C.psiG m)⁻¹ = tG := by
        have h := congrArg C.psiG hm
        simpa [map_mul, map_inv, C.psiG_apply, hxval] using h
      have ht'eq : t' = (C.psiG m)⁻¹ * tG * (C.psiG m) := by
        rw [← hψm]
        group
      have hc_conj : c * tG * c⁻¹ = tG := by
        have h : g⁻¹ * tG * g = (C.psiG m)⁻¹ * tG * (C.psiG m) := by
          rw [← ht'eq]
        calc c * tG * c⁻¹ = g * ((C.psiG m)⁻¹ * tG * (C.psiG m)) * g⁻¹ := by
              change (g * (C.psiG m)⁻¹) * tG * (g * (C.psiG m)⁻¹)⁻¹ =
                g * ((C.psiG m)⁻¹ * tG * (C.psiG m)) * g⁻¹
              group
          _ = g * (g⁻¹ * tG * g) * g⁻¹ := by rw [← h]
          _ = tG := by group
      have hcCT : c ∈ CT := by
        refine (Subgroup.mem_centralizer_iff).mpr ?_
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have hc_conj' : c⁻¹ * tG * c = tG := by
          have h2 : c⁻¹ * (c * tG * c⁻¹) * c = c⁻¹ * tG * c := by
            simpa using congrArg (fun x => c⁻¹ * x * c) hc_conj
          have h1 : c⁻¹ * (c * tG * c⁻¹) * c = tG := by group
          rw [← h2]
          exact h1
        have : tG * c = c * tG := by
          calc tG * c = c * (c⁻¹ * tG * c) := by group
            _ = c * tG := by rw [hc_conj']
        simpa [tG] using this
      have hcψz : C.psiG m * C.z * (C.psiG m)⁻¹ = C.z := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp (C.ψ m).2
        change (C.ψ m : G) * C.z * (C.ψ m : G)⁻¹ = C.z
        calc (C.ψ m : G) * C.z * (C.ψ m : G)⁻¹ =
              (C.z * (C.ψ m : G)) * (C.ψ m : G)⁻¹ := by rw [h]
          _ = C.z := by group
      have hcψz' : (C.psiG m)⁻¹ * C.z * (C.psiG m) = C.z := by
        calc (C.psiG m)⁻¹ * C.z * (C.psiG m) =
              (C.psiG m)⁻¹ * ((C.psiG m) * C.z * (C.psiG m)⁻¹) * (C.psiG m) := by
              rw [hcψz]
          _ = C.z := by group
      have hcz : c * C.z * c⁻¹ = i := by
        calc c * C.z * c⁻¹ =
              g * ((C.psiG m)⁻¹ * C.z * (C.psiG m)) * g⁻¹ := by
              change (g * (C.psiG m)⁻¹) * C.z * (g * (C.psiG m)⁻¹)⁻¹ =
                g * ((C.psiG m)⁻¹ * C.z * (C.psiG m)) * g⁻¹
              group
          _ = g * C.z * g⁻¹ := by rw [hcψz']
          _ = i := hg
      refine ⟨c⁻¹, CT.inv_mem hcCT, ?_⟩
      calc c⁻¹ * i * (c⁻¹)⁻¹ = c⁻¹ * i * c := by group
        _ = C.z := by
          rw [← hcz]
          group
  by_cases hcommj : j * C.z = C.z * j
  · obtain ⟨y, hyCT, hyj⟩ := stepA hj hj2 hcommj
    exact ⟨y, hyCT, hyj⟩
  · let r : G := j * C.z
    have hrCT : r ∈ CT := CT.mul_mem hj hzCT
    let n : ℕ := orderOf r
    have hrn : r ^ n = 1 := by
      dsimp [n]
      exact pow_orderOf_eq_one r
    have hjz2 : j * j = 1 := by
      have := pow_orderOf_eq_one j
      rwa [hj2, pow_two] at this
    have hrne1 : r ≠ 1 := by
      intro h
      apply hcommj
      have hjz : j = C.z := by
        calc j = (j * C.z) * C.z := by rw [mul_assoc, hz2, mul_one]
          _ = r * C.z := rfl
          _ = C.z := by rw [h, one_mul]
      rw [hjz]
    have hn0 : n ≠ 0 := by
      intro h
      have h1 : orderOf r = 0 := by simpa [n] using h
      have hpos := orderOf_pos r
      omega
    have hLr : (j * C.z) * C.z * (C.z * j) = j * C.z * j := by
      calc (j * C.z) * C.z * (C.z * j) = j * (C.z * C.z) * (C.z * j) := by group
        _ = j * 1 * (C.z * j) := by rw [hz2]
        _ = j * C.z * j := by group
    have hRr : (j * C.z) * (j * C.z) * C.z = j * C.z * j := by
      calc (j * C.z) * (j * C.z) * C.z = j * C.z * (j * (C.z * C.z)) := by group
        _ = j * C.z * (j * 1) := by rw [hz2]
        _ = j * C.z * j := by group
    have hr2z : r * C.z * r⁻¹ = r ^ 2 * C.z := by
      have hinv : (j * C.z)⁻¹ = C.z * j := by
        rw [show (j * C.z)⁻¹ = C.z⁻¹ * j⁻¹ by group,
          show C.z⁻¹ = C.z from inv_eq_self_of_orderOf_eq_two C.orderOf_z,
          show j⁻¹ = j from inv_eq_self_of_orderOf_eq_two hj2]
      change (j * C.z) * C.z * (j * C.z)⁻¹ = (j * C.z) ^ 2 * C.z
      rw [hinv, pow_two]
      calc (j * C.z) * C.z * (C.z * j) = j * C.z * j := hLr
        _ = (j * C.z) * (j * C.z) * C.z := hRr.symm
    have hzr : C.z * r⁻¹ = r * C.z := by
      calc C.z * r⁻¹ = r⁻¹ * (r * C.z * r⁻¹) := by group
        _ = r⁻¹ * (r ^ 2 * C.z) := by rw [hr2z]
        _ = r * C.z := by group
    have hconjpow : ∀ m : ℕ, r ^ m * C.z * (r ^ m)⁻¹ = r ^ (2 * m) * C.z := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc r ^ (m + 1) * C.z * (r ^ (m + 1))⁻¹
            = r * (r ^ m * C.z * (r ^ m)⁻¹) * r⁻¹ := by group
          _ = r * (r ^ (2 * m) * C.z) * r⁻¹ := by rw [ih]
          _ = r ^ (2 * m + 1) * (C.z * r⁻¹) := by group
          _ = r ^ (2 * m + 1) * (r * C.z) := by rw [hzr]
          _ = r ^ (2 * (m + 1)) * C.z := by ring_nf; group
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · have hkpos : 0 < k := by omega
      let i : G := r ^ k
      have hiCT : i ∈ CT := by
        change r ^ k ∈ CT
        exact CT.pow_mem hrCT k
      have hi2 : i * i = 1 := by
        change (r ^ k) * (r ^ k) = 1
        rw [← pow_two, ← pow_mul, show k * 2 = n by omega, hrn]
      have hi1 : i ≠ 1 := by
        intro h
        have hpow : r ^ k = 1 := by simpa [i] using h
        have hdvd : n ∣ k := by
          rw [show n = orderOf r from rfl]
          exact orderOf_dvd_iff_pow_eq_one.mpr hpow
        obtain ⟨t, ht⟩ := hdvd
        have htpos : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h
          · subst h0
            rw [mul_zero] at ht
            omega
          · exact h
        have hnk : n ≤ k := by
          rw [ht]
          calc n = n * 1 := by ring
            _ ≤ n * t := Nat.mul_le_mul_left n htpos
        omega
      have hcommiz : i * C.z = C.z * i := by
        have hzi : i * C.z * i⁻¹ = C.z := by
          rw [show i = r ^ k from rfl, hconjpow k, show 2 * k = n by omega, hrn, one_mul]
        calc i * C.z = (i * C.z * i⁻¹) * i := by group
          _ = C.z * i := by rw [hzi]
      have hiord : orderOf i = 2 := by
        apply orderOf_eq_prime
        · rwa [pow_two]
        · exact hi1
      obtain ⟨c, hcCT, hci⟩ := stepA hiCT hiord hcommiz
      have hir : i * r = r * i := by
        change (r ^ k) * r = r * (r ^ k)
        rw [← pow_succ, ← pow_succ']
      have hrj : r * C.z = j := by
        change (j * C.z) * C.z = j
        rw [mul_assoc, hz2, mul_one]
      have hij : i * j = j * i := by
        calc i * j = i * (r * C.z) := by rw [hrj]
          _ = (i * r) * C.z := by group
          _ = (r * i) * C.z := by rw [hir]
          _ = r * (i * C.z) := by group
          _ = r * (C.z * i) := by rw [hcommiz]
          _ = (r * C.z) * i := by group
          _ = j * i := by rw [hrj]
      let j' : G := c * j * c⁻¹
      have hj'CT : j' ∈ CT := by
        change c * j * c⁻¹ ∈ CT
        exact CT.mul_mem (CT.mul_mem hcCT hj) (CT.inv_mem hcCT)
      have hj'2 : orderOf j' = 2 := by
        have hsem : SemiconjBy c j j' := by
          change c * j = (c * j * c⁻¹) * c
          group
        rw [← hsem.orderOf_eq]
        exact hj2
      have hj'z : j' * C.z = C.z * j' := by
        have hz_eq : C.z = c * i * c⁻¹ := hci.symm
        change (c * j * c⁻¹) * C.z = C.z * (c * j * c⁻¹)
        rw [hz_eq]
        calc (c * j * c⁻¹) * (c * i * c⁻¹) = c * (j * i) * c⁻¹ := by group
          _ = c * (i * j) * c⁻¹ := by rw [hij]
          _ = (c * i * c⁻¹) * (c * j * c⁻¹) := by group
      obtain ⟨d, hdCT, hdj⟩ := stepA hj'CT hj'2 hj'z
      refine ⟨d * c, CT.mul_mem hdCT hcCT, ?_⟩
      calc (d * c) * j * (d * c)⁻¹ = d * j' * d⁻¹ := by
            change (d * c) * j * (d * c)⁻¹ = d * (c * j * c⁻¹) * d⁻¹
            group
        _ = C.z := hdj
    · have h2m : 2 * (k + 1) = n + 1 := by omega
      have hrj : r * C.z = j := by
        change (j * C.z) * C.z = j
        rw [mul_assoc, hz2, mul_one]
      have hconj_m : r ^ (k + 1) * C.z * (r ^ (k + 1))⁻¹ = j := by
        rw [hconjpow (k + 1), h2m, pow_succ, hrn, one_mul]
        exact hrj
      refine ⟨(r ^ (k + 1))⁻¹, CT.inv_mem (CT.pow_mem hrCT _), ?_⟩
      calc (r ^ (k + 1))⁻¹ * j * ((r ^ (k + 1))⁻¹)⁻¹
          = (r ^ (k + 1))⁻¹ * (r ^ (k + 1) * C.z * (r ^ (k + 1))⁻¹) *
              (r ^ (k + 1)) := by rw [hconj_m, inv_inv]
        _ = C.z := by group

@[expose] def ThCore.zC (C : ThCore G) (tM : ↥Max3.M) :
    ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) :=
  ⟨C.z, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (C.ψ tM).2).symm⟩

theorem ThCore.zC_coe (C : ThCore G) (tM : ↥Max3.M) :
    ((C.zC tM : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G))) : G) = C.z := rfl

theorem ThCore.map_centralizer_z_eq (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    ((Subgroup.centralizer ({C.z} : Set G)).subgroupOf
        (Subgroup.centralizer ({(C.ψ tM : G)} : Set G))).map π =
      Subgroup.centralizer ({π (C.zC tM)} : Set Y) := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let tG : G := (C.ψ tM : G)
  let tCT : ↥CT := ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have htCTord : orderOf tCT = 3 := by
    rw [show tCT = ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ from rfl,
      Subgroup.orderOf_mk]
    rw [show tG = (C.ψ tM : G) from rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hzCT : C.z ∈ CT :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (C.ψ tM).2).symm
  have hzCeq : C.zC tM = ⟨C.z, hzCT⟩ := Subtype.ext rfl
  have hzCord : orderOf (C.zC tM) = 2 := by
    rw [show C.zC tM = ⟨C.z, hzCT⟩ from hzCeq, Subgroup.orderOf_mk]
    exact C.orderOf_z
  have hzC2 : C.zC tM * C.zC tM = 1 := by
    apply Subtype.ext
    change C.z * C.z = 1
    have := pow_orderOf_eq_one C.z
    rwa [C.orderOf_z, pow_two] at this
  have htH : tG ∈ H := (C.ψ tM).2
  have hzt : Commute (C.zC tM) tCT := by
    rw [Commute]
    apply Subtype.ext
    change C.z * tG = tG * C.z
    exact (Subgroup.mem_centralizer_singleton_iff.mp htH).symm
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have hgH : (g : G) ∈ H := Subgroup.mem_subgroupOf.mp hg
    have hgz : (g : G) * C.z = C.z * (g : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hgH
    refine (Subgroup.mem_centralizer_singleton_iff).mpr ?_
    change π g * π (C.zC tM) = π (C.zC tM) * π g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (g : G) * C.z = C.z * (g : G)
    exact hgz
  · intro y hy
    obtain ⟨g, rfl⟩ := hπ y
    have hgy : π g * π (C.zC tM) = π (C.zC tM) * π g :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    let u : ↥CT := g * C.zC tM * g⁻¹
    have hgu : π u = π (C.zC tM) := by
      change π (g * C.zC tM * g⁻¹) = π (C.zC tM)
      calc π (g * C.zC tM * g⁻¹) = π g * π (C.zC tM) * (π g)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = π (C.zC tM) := by rw [hgy]; group
    have hkeru : u * C.zC tM ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      calc π (u * C.zC tM) = π u * π (C.zC tM) := by rw [map_mul]
        _ = π (C.zC tM) * π (C.zC tM) := by rw [hgu]
        _ = 1 := by
            rw [← map_mul, hzC2, map_one]
    rw [hker] at hkeru
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hkeru
    have hu_eq : u = tCT ^ k * C.zC tM := by
      calc u = (u * C.zC tM) * C.zC tM := by
            rw [mul_assoc, hzC2, mul_one]
        _ = tCT ^ k * C.zC tM := by rw [← hk]
    have huord : orderOf u = 2 := by
      have hsem : SemiconjBy g (C.zC tM) u := by
        change g * C.zC tM = (g * C.zC tM * g⁻¹) * g
        group
      rw [← hsem.orderOf_eq]
      exact hzCord
    have hgH : (g : G) ∈ H := by
      have hu_z : u = C.zC tM := by
        by_cases hp1 : tCT ^ k = 1
        · rw [hu_eq, hp1, one_mul]
        · exfalso
          have hdvd : orderOf (tCT ^ k) ∣ 3 := by
            rw [orderOf_zpow, htCTord]
            exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 3 k.natAbs)
          have hpord : orderOf (tCT ^ k) = 3 := by
            rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three
              (orderOf (tCT ^ k)) hdvd with h1 | h3
            · exact absurd (orderOf_eq_one_iff.mp h1) hp1
            · exact h3
          have hcop : (orderOf (C.zC tM)).Coprime (orderOf (tCT ^ k)) := by
            rw [hzCord, hpord]
            norm_num
          have hztk : Commute (C.zC tM) (tCT ^ k) := hzt.zpow_right k
          have hmulord : orderOf (C.zC tM * tCT ^ k) = 2 * 3 := by
            rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hztk hcop, hzCord, hpord]
          have huord6 : orderOf u = 6 := by
            rw [hu_eq]
            rw [show tCT ^ k * C.zC tM = C.zC tM * tCT ^ k from hztk.eq.symm]
            exact hmulord
          omega
      have h2 : (g : G) * C.z * (g : G)⁻¹ = C.z := by
        have h3 : (g : G) * (C.zC tM : G) * (g : G)⁻¹ = (C.zC tM : G) := by
          have := congrArg (fun x : ↥CT => (x : G)) hu_z
          simpa [u, Subgroup.coe_mul, Subgroup.coe_inv] using this
        simpa [zC_coe] using h3
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc (g : G) * C.z = ((g : G) * C.z * (g : G)⁻¹) * (g : G) := by group
        _ = C.z * (g : G) := by rw [h2]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hgH)

theorem ThCore.card_centralizer_zbar (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    Nat.card ↥(Subgroup.centralizer ({π (C.zC tM)} : Set Y)) = 576 := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let tG : G := (C.ψ tM : G)
  let tCT : ↥CT := ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let K : Subgroup ↥CT := H.subgroupOf CT
  have htCTord : orderOf tCT = 3 := by
    rw [show tCT = ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ from rfl,
      Subgroup.orderOf_mk]
    rw [show tG = (C.ψ tM : G) from rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hKcard : Nat.card ↥K = 1728 := by
    have h := C.card_centralizer_inf tM
    rw [hCt] at h
    have hK_eq : K = (H ⊓ CT).subgroupOf CT := by
      ext x
      simp [K, Subgroup.mem_subgroupOf]
    rw [hK_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans h
  have htH : tG ∈ H := (C.ψ tM).2
  have htK : tCT ∈ K := Subgroup.mem_subgroupOf.mpr htH
  have hzpow_le_K : Subgroup.zpowers tCT ≤ K := Subgroup.zpowers_le.mpr htK
  have hkerK : (π.comp K.subtype).ker = (Subgroup.zpowers tCT).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    exact Iff.rfl
  have hkercard : Nat.card ↥(π.comp K.subtype).ker = 3 := by
    rw [hkerK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpow_le_K).toEquiv,
      Nat.card_zpowers, htCTord]
  have hrange : (π.comp K.subtype).range =
      Subgroup.centralizer ({π (C.zC tM)} : Set Y) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact ThCore.map_centralizer_z_eq C htM π hπ hker
  have hprod := Subgroup.card_ker_mul_card_range (π.comp K.subtype)
  rw [hkercard, hrange, hKcard] at hprod
  omega

theorem ThCore.nonempty_centralizer_zbar_mulEquiv (C : ThCore G) {tM : ↥Max3.M}
    (htM : orderOf tM = 3)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    {D : Subgroup ↥Max3.M} (hD : D ≤ Subgroup.centralizer ({tM} : Set ↥Max3.M))
    (htD : tM ∉ D) (hDc : Nat.card ↥D = 576) :
    Nonempty (↥(Subgroup.centralizer ({π (C.zC tM)} : Set Y)) ≃* ↥D) := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let CY : Subgroup Y := Subgroup.centralizer ({π (C.zC tM)} : Set Y)
  let tG : G := (C.ψ tM : G)
  have hCT : ∀ x : ↥D, (C.ψ x : G) ∈ CT := by
    intro x
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hxcomm : (x : ↥Max3.M) * tM = tM * (x : ↥Max3.M) := by
      have h := (Subgroup.mem_centralizer_iff.mp (hD x.2)) tM (by simp)
      exact h.symm
    have h' := congrArg C.psiG hxcomm
    rw [map_mul, map_mul] at h'
    simpa [C.psiG_apply] using h'.symm
  have hCY : ∀ x : ↥D, π ⟨(C.ψ x : G), hCT x⟩ ∈ CY := by
    intro x
    have hxz : (C.ψ x : G) * C.z = C.z * (C.ψ x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (C.ψ x).2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change π ⟨(C.ψ x : G), hCT x⟩ * π (C.zC tM) =
      π (C.zC tM) * π ⟨(C.ψ x : G), hCT x⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (C.ψ x : G) * C.z = C.z * (C.ψ x : G)
    exact hxz
  let φ : ↥D →* ↥CY :=
    { toFun := fun x => ⟨π ⟨(C.ψ x : G), hCT x⟩, hCY x⟩
      map_one' := by
        apply Subtype.ext
        change π (⟨(C.ψ (1 : ↥D) : G), hCT 1⟩ : ↥CT) = 1
        have h1 : (⟨(C.ψ (1 : ↥D) : G), hCT 1⟩ : ↥CT) = 1 := by
          apply Subtype.ext
          simp
        rw [h1, map_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change π (⟨(C.ψ ((a : ↥Max3.M) * (b : ↥Max3.M)) : G), hCT (a * b)⟩ :
            ↥CT) =
          π (⟨(C.ψ (a : ↥Max3.M) : G), hCT a⟩ : ↥CT) *
            π (⟨(C.ψ (b : ↥Max3.M) : G), hCT b⟩ : ↥CT)
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp [map_mul] }
  have htMpow_eq_one : ∀ k : ℤ, tM ^ k ∈ D → tM ^ k = 1 := by
    intro k hk
    by_contra hne
    have hxord : orderOf (tM ^ k) = 3 := by
      have hdvd : orderOf (tM ^ k) ∣ 3 := by
        rw [orderOf_zpow, htM]
        exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 3 k.natAbs)
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three
        (orderOf (tM ^ k)) hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h3
    have hxmem : tM ^ k ∈ Subgroup.zpowers tM :=
      Subgroup.zpow_mem (Subgroup.zpowers tM) (Subgroup.mem_zpowers tM) k
    have hle : Subgroup.zpowers (tM ^ k) ≤ Subgroup.zpowers tM :=
      Subgroup.zpowers_le.mpr hxmem
    have hcardx : Nat.card ↥(Subgroup.zpowers (tM ^ k)) = 3 := by
      rw [Nat.card_zpowers, hxord]
    have hcardt : Nat.card ↥(Subgroup.zpowers tM) = 3 := by
      rw [Nat.card_zpowers, htM]
    have heq : Subgroup.zpowers (tM ^ k) = Subgroup.zpowers tM :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcardt.trans hcardx.symm))
    have htMmem : tM ∈ Subgroup.zpowers (tM ^ k) := by
      rw [heq]
      exact Subgroup.mem_zpowers tM
    exact htD (Subgroup.zpowers_le.mpr hk htMmem)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hπxy : π ⟨(C.ψ x : G), hCT x⟩ = π ⟨(C.ψ y : G), hCT y⟩ :=
      congrArg Subtype.val hxy
    let xCT : ↥CT := ⟨(C.ψ x : G), hCT x⟩
    let yCT : ↥CT := ⟨(C.ψ y : G), hCT y⟩
    let tCT : ↥CT := ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hkeru : xCT * yCT⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      calc π (xCT * yCT⁻¹) = π xCT * (π yCT)⁻¹ := by rw [map_mul, map_inv]
        _ = 1 := by rw [show π xCT = π yCT from hπxy]; group
    rw [hker] at hkeru
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hkeru
    have hkG : (C.ψ ((x : ↥Max3.M) * (y : ↥Max3.M)⁻¹) : G) = (C.ψ tM : G) ^ k := by
      have h := congrArg (fun z : ↥CT => (z : G)) hk
      simpa [xCT, yCT, tCT, tG, Subgroup.coe_mul, Subgroup.coe_inv, map_mul] using h.symm
    have hψ : C.ψ ((x : ↥Max3.M) * (y : ↥Max3.M)⁻¹) = C.ψ (tM ^ k) := by
      rw [map_zpow]
      apply Subtype.ext
      simpa [C.psiG_apply] using hkG
    have hEq : (x : ↥Max3.M) * (y : ↥Max3.M)⁻¹ = tM ^ k :=
      C.ψ.injective hψ
    have hmemD : tM ^ k ∈ D := by
      rw [← hEq]
      exact D.mul_mem x.2 (D.inv_mem y.2)
    have h1 : (x : ↥Max3.M) * (y : ↥Max3.M)⁻¹ = 1 := by
      rw [hEq, htMpow_eq_one k hmemD]
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hCYcard : Nat.card ↥CY = 576 := ThCore.card_centralizer_zbar C htM hCt π hπ hker
  haveI hYfin : Finite Y := Finite.of_surjective π hπ
  haveI : Fintype ↥D := Fintype.ofFinite _
  haveI : Fintype ↥CY := Fintype.ofFinite _
  have hcardF : Fintype.card ↥D = Fintype.card ↥CY := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hDc, hCYcard]
  obtain ⟨e⟩ := Fintype.card_eq.mp hcardF
  have hsurj : Function.Surjective φ := Function.Injective.surjective_of_finite e hinj
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem ThCore.card_sylow_quot (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    (hT : ∃ T : Subgroup ↥Max3.M, T ≤ Subgroup.centralizer ({tM} : Set ↥Max3.M) ∧
      Nat.card ↥T = 64 ∧ ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ (x : J) = Max3.z)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    (S : Sylow 2 Y) : Nat.card ↥S = 64 := by
  classical
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let tG : G := (C.ψ tM : G)
  let tCT : ↥CT := ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  haveI hYfin : Finite Y := Finite.of_surjective π hπ
  have htCTord : orderOf tCT = 3 := by
    rw [show tCT = ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ from rfl,
      Subgroup.orderOf_mk]
    rw [show tG = (C.ψ tM : G) from rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hkercard : Nat.card ↥π.ker = 3 := by
    rw [hker, Nat.card_zpowers, htCTord]
  have hCTcard : Nat.card ↥CT = 3 * Nat.card Y := by
    have h := Subgroup.card_ker_mul_card_range π
    rw [hkercard, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top] at h
    exact h.symm
  obtain ⟨T, hTle, hTcard, hTz⟩ := hT
  let P : Subgroup G := T.map C.psiG
  have hPCT : P ≤ CT := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hcomm : t * tM = tM * t := by
      have h := (Subgroup.mem_centralizer_iff.mp (hTle ht)) tM (by simp)
      exact h.symm
    have h' := congrArg C.psiG hcomm
    rw [map_mul, map_mul] at h'
    simpa [C.psiG_apply] using h'.symm
  have hPH : P ≤ H := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (C.ψ t).2
  have hPCH : P ≤ H ⊓ CT := le_inf hPH hPCT
  have hPcard : Nat.card ↥P = 64 := by
    change Nat.card ↥(T.map C.psiG) = 64
    rw [Subgroup.card_map_of_injective C.psiG_injective, hTcard]
  obtain ⟨SCT, hSCT⟩ := ThCore.exists_sylow_eq C hCt ⟨T, hTle, hTcard, hTz⟩ hPCH hPcard
  have hSCTcard : Nat.card ↥SCT = 64 := by
    have h := congrArg (fun Q : Subgroup G => Nat.card ↥Q) hSCT
    rw [Subgroup.card_map_of_injective CT.subtype_injective, hPcard] at h
    exact h
  have hfacCT : (Nat.card ↥CT).factorization 2 = 6 := by
    have h := SCT.card_eq_multiplicity
    have hSCTcard' : Nat.card ↥(SCT : Subgroup ↥CT) = 64 := hSCTcard
    rw [hSCTcard'] at h
    have hpow : (2 : ℕ) ^ (Nat.card ↥CT).factorization 2 = 2 ^ 6 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hfacY : (Nat.card Y).factorization 2 = 6 := by
    have hYpos : Nat.card Y ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have h2 : (3 * Nat.card Y).factorization 2 =
        (3 : ℕ).factorization 2 + (Nat.card Y).factorization 2 := by
      rw [Nat.factorization_mul (by norm_num) hYpos]
      rfl
    have h3 : (3 : ℕ).factorization 2 = 0 := by norm_num [Nat.factorization]
    rw [h3, zero_add] at h2
    rw [hCTcard] at hfacCT
    rw [h2] at hfacCT
    exact hfacCT
  change Nat.card ↥(S : Subgroup Y) = 64
  rw [S.card_eq_multiplicity, hfacY]
  norm_num

theorem ThCore.exists_conj_zbar (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    (h3 : ∀ x w : ↥Max3.M, orderOf x = 3 → w * w = 1 → w ≠ 1 → (w : J) ≠ Max3.z →
      w * x = x * w → ∃ m : ↥Max3.M, m * x * m⁻¹ = tM)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    {y : Y} (hy : orderOf y = 2) :
    ∃ g : Y, g * y * g⁻¹ = π (C.zC tM) := by
  classical
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let tG : G := (C.ψ tM : G)
  let tCT : ↥CT := ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  haveI hYfin : Finite Y := Finite.of_surjective π hπ
  have htCTord : orderOf tCT = 3 := by
    rw [show tCT = ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ from rfl,
      Subgroup.orderOf_mk]
    rw [show tG = (C.ψ tM : G) from rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hker' : π.ker = Subgroup.zpowers tCT := by
    simpa [tCT, tG] using hker
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  obtain ⟨yt, hyt⟩ := hπ y
  have hyt_ne : yt ≠ 1 := by
    intro h
    apply hy1
    rw [← hyt, h]
    exact map_one π
  have hyt_nonker : yt ∉ Subgroup.zpowers tCT := by
    intro hmem
    rw [← hker'] at hmem
    exact hy1 (by rw [← hyt, (MonoidHom.mem_ker.mp hmem)])
  have hsq : yt ^ 2 ∈ Subgroup.zpowers tCT := by
    rw [← hker']
    rw [MonoidHom.mem_ker, map_pow, hyt, pow_two, hy2]
  have hyt6 : yt ^ 6 = 1 := by
    have hdvd3 : orderOf (yt ^ 2) ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers tCT) hsq
      rwa [Nat.card_zpowers, htCTord] at this
    have h3 : (yt ^ 2) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd3
    calc yt ^ 6 = yt ^ (2 * 3) := by norm_num
      _ = (yt ^ 2) ^ 3 := pow_mul yt 2 3
      _ = 1 := h3
  have hdiv6 : orderOf yt ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hyt6
  have h2dvd : 2 ∣ orderOf yt := by
    have hdvd : orderOf y ∣ orderOf yt := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [← hyt, ← map_pow, pow_orderOf_eq_one, map_one]
    rwa [hy] at hdvd
  let jCT : ↥CT := ⟨yt ^ 3, CT.pow_mem yt.2 3⟩
  have hj2 : jCT * jCT = 1 := by
    apply Subtype.ext
    simp only [jCT, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one]
    calc (yt : G) ^ 3 * (yt : G) ^ 3 = (yt : G) ^ (3 + 3) := by rw [← pow_add]
      _ = (yt : G) ^ 6 := by norm_num
      _ = 1 := by simpa using congrArg Subtype.val hyt6
  have hjne : jCT ≠ 1 := by
    intro h
    have h3 : orderOf yt ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      apply Subtype.ext
      simpa [jCT, Subgroup.coe_pow] using congrArg Subtype.val h
    have h1 : orderOf yt = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
      · exact h1
      · rw [h3'] at h2dvd
        norm_num at h2dvd
    exact hyt_ne (orderOf_eq_one_iff.mp h1)
  have hjord : orderOf jCT = 2 := by
    apply orderOf_eq_prime
    · rwa [pow_two]
    · exact hjne
  have hπj : π jCT = y := by
    have hjpow : jCT = (⟨yt, yt.2⟩ : ↥CT) ^ 3 := Subtype.ext rfl
    rw [hjpow, map_pow, show π ⟨yt, yt.2⟩ = y from hyt]
    calc y ^ (3 : ℕ) = y ^ 2 * y := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
      _ = 1 * y := by rw [pow_two, hy2]
      _ = y := by group
  have hjordG : orderOf (jCT : G) = 2 := by
    rw [Subgroup.orderOf_coe, hjord]
  obtain ⟨c, hcCT, hcj⟩ :=
    ThCore.exists_conj_eq_z C htM h3 jCT.2 hjordG
  let cCT : ↥CT := ⟨c, hcCT⟩
  have hcjCT : (⟨cCT * jCT * cCT⁻¹,
      CT.mul_mem (CT.mul_mem hcCT jCT.2) (CT.inv_mem hcCT)⟩ : ↥CT) = C.zC tM := by
    apply Subtype.ext
    simpa [cCT, zC_coe] using hcj
  refine ⟨π cCT, ?_⟩
  calc π cCT * y * (π cCT)⁻¹ = π cCT * π jCT * (π cCT)⁻¹ := by rw [← hπj]
    _ = π ⟨cCT * jCT * cCT⁻¹,
          CT.mul_mem (CT.mul_mem hcCT jCT.2) (CT.inv_mem hcCT)⟩ := by
          rw [show (⟨cCT * jCT * cCT⁻¹,
            CT.mul_mem (CT.mul_mem hcCT jCT.2) (CT.inv_mem hcCT)⟩ : ↥CT) =
              cCT * jCT * cCT⁻¹ from rfl, map_mul, map_mul, map_inv]
    _ = π (C.zC tM) := by rw [hcjCT]

@[expose] noncomputable def ThCore.barOf (C : ThCore G) {tM : ↥Max3.M} {Y : Type} [Group Y]
    (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y) (K : Subgroup ↥Max3.M) :
    Subgroup Y :=
  ((K.map C.psiG).subgroupOf (Subgroup.centralizer ({(C.ψ tM : G)} : Set G))).map π

structure MG1 (tM : ↥Max3.M) (H₁ H₂ : Subgroup ↥Max3.M) : Prop where
  le_one : H₁ ≤ Subgroup.centralizer ({tM} : Set ↥Max3.M)
  le_two : H₂ ≤ Subgroup.centralizer ({tM} : Set ↥Max3.M)
  normal_one : Subgroup.centralizer ({tM} : Set ↥Max3.M) ≤
    Subgroup.normalizer (H₁ : Set ↥Max3.M)
  normal_two : Subgroup.centralizer ({tM} : Set ↥Max3.M) ≤
    Subgroup.normalizer (H₂ : Set ↥Max3.M)
  iso_one : Nonempty (↥H₁ ≃* SL(2, ZMod 3))
  iso_two : Nonempty (↥H₂ ≃* SL(2, ZMod 3))
  z_mem : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ H₁ ⊓ H₂
  card_inf : Nat.card ↥(H₁ ⊓ H₂) = 2
  not_mem : tM ∉ H₁ ⊔ H₂

theorem ThCore.pi_psi_injective_on (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
    {K : Subgroup ↥Max3.M} (hK : K ≤ Subgroup.centralizer ({tM} : Set ↥Max3.M))
    (htK : tM ∉ K) :
    Function.Injective (fun x : ↥K =>
      π ⟨(C.ψ x : G), by
        refine (Subgroup.mem_centralizer_iff).mpr ?_
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have hxcomm : (x : ↥Max3.M) * tM = tM * (x : ↥Max3.M) := by
          have h := (Subgroup.mem_centralizer_iff.mp (hK x.2)) tM (by simp)
          exact h.symm
        have h' := congrArg C.psiG hxcomm
        rw [map_mul, map_mul] at h'
        simpa [C.psiG_apply] using h'.symm⟩) := by
  classical
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let tG : G := (C.ψ tM : G)
  let tCT : ↥CT := ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have htCTord : orderOf tCT = 3 := by
    rw [show tCT = ⟨tG, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ from rfl,
      Subgroup.orderOf_mk]
    rw [show tG = (C.ψ tM : G) from rfl, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, htM]
  have hker' : π.ker = Subgroup.zpowers tCT := by
    simpa [tCT, tG] using hker
  have htMpow_eq_one : ∀ k : ℤ, tM ^ k ∈ K → tM ^ k = 1 := by
    intro k hk
    by_contra hne
    have hxord : orderOf (tM ^ k) = 3 := by
      have hdvd : orderOf (tM ^ k) ∣ 3 := by
        rw [orderOf_zpow, htM]
        exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 3 k.natAbs)
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three
        (orderOf (tM ^ k)) hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hne
      · exact h3
    have hxmem : tM ^ k ∈ Subgroup.zpowers tM :=
      Subgroup.zpow_mem (Subgroup.zpowers tM) (Subgroup.mem_zpowers tM) k
    have hle : Subgroup.zpowers (tM ^ k) ≤ Subgroup.zpowers tM :=
      Subgroup.zpowers_le.mpr hxmem
    have hcardx : Nat.card ↥(Subgroup.zpowers (tM ^ k)) = 3 := by
      rw [Nat.card_zpowers, hxord]
    have hcardt : Nat.card ↥(Subgroup.zpowers tM) = 3 := by
      rw [Nat.card_zpowers, htM]
    have heq : Subgroup.zpowers (tM ^ k) = Subgroup.zpowers tM :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcardt.trans hcardx.symm))
    have htMmem : tM ∈ Subgroup.zpowers (tM ^ k) := by
      rw [heq]
      exact Subgroup.mem_zpowers tM
    exact htK (Subgroup.zpowers_le.mpr hk htMmem)
  intro x y hxy
  have hCT : ∀ z : ↥K, (C.ψ z : G) ∈ CT := by
    intro z
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hzcomm : (z : ↥Max3.M) * tM = tM * (z : ↥Max3.M) := by
      have h := (Subgroup.mem_centralizer_iff.mp (hK z.2)) tM (by simp)
      exact h.symm
    have h' := congrArg C.psiG hzcomm
    rw [map_mul, map_mul] at h'
    simpa [C.psiG_apply] using h'.symm
  let xCT : ↥CT := ⟨(C.ψ x : G), hCT x⟩
  let yCT : ↥CT := ⟨(C.ψ y : G), hCT y⟩
  have hπxy : π xCT = π yCT := hxy
  have hkeru : xCT * yCT⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    calc π (xCT * yCT⁻¹) = π xCT * (π yCT)⁻¹ := by rw [map_mul, map_inv]
      _ = 1 := by rw [hπxy]; group
  rw [hker'] at hkeru
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hkeru
  have hkG : (C.ψ ((x : ↥Max3.M) * (y : ↥Max3.M)⁻¹) : G) = (C.ψ tM : G) ^ k := by
    have h := congrArg (fun z : ↥CT => (z : G)) hk
    simpa [xCT, yCT, tCT, tG, Subgroup.coe_mul, Subgroup.coe_inv, map_mul] using h.symm
  have hψ : C.ψ ((x : ↥Max3.M) * (y : ↥Max3.M)⁻¹) = C.ψ (tM ^ k) := by
    rw [map_zpow]
    apply Subtype.ext
    simpa [C.psiG_apply] using hkG
  have hEq : (x : ↥Max3.M) * (y : ↥Max3.M)⁻¹ = tM ^ k :=
    C.ψ.injective hψ
  have hmemK : tM ^ k ∈ K := by
    rw [← hEq]
    exact K.mul_mem x.2 (K.inv_mem y.2)
  have h1 : (x : ↥Max3.M) * (y : ↥Max3.M)⁻¹ = 1 := by
    rw [hEq, htMpow_eq_one k hmemK]
  exact Subtype.ext (mul_inv_eq_one.mp h1)

theorem ThCore.g23One_barOf (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    {H₁ H₂ : Subgroup ↥Max3.M} (hH : MG1 tM H₁ H₂)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    CFSG.Quasithin.G23Type.G23One
      (Subgroup.centralizer ({π (C.zC tM)} : Set Y))
      (C.barOf π H₁) (C.barOf π H₂) := by
  classical
  let CM : Subgroup ↥Max3.M := Subgroup.centralizer ({tM} : Set ↥Max3.M)
  let CT : Subgroup G := Subgroup.centralizer ({(C.ψ tM : G)} : Set G)
  let H : Subgroup G := Subgroup.centralizer ({C.z} : Set G)
  let Hb : Subgroup Y := Subgroup.centralizer ({π (C.zC tM)} : Set Y)
  let K1 : Subgroup ↥CT := (H₁.map C.psiG).subgroupOf CT
  let K2 : Subgroup ↥CT := (H₂.map C.psiG).subgroupOf CT
  let H1b : Subgroup Y := C.barOf π H₁
  let H2b : Subgroup Y := C.barOf π H₂
  haveI hYfin : Finite Y := Finite.of_surjective π hπ
  have hCT : ∀ {K : Subgroup ↥Max3.M}, K ≤ CM → ∀ x : ↥K, (C.ψ x : G) ∈ CT := by
    intro K hK x
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hxcomm : (x : ↥Max3.M) * tM = tM * (x : ↥Max3.M) := by
      have h := (Subgroup.mem_centralizer_iff.mp (hK x.2)) tM (by simp)
      exact h.symm
    have h' := congrArg C.psiG hxcomm
    rw [map_mul, map_mul] at h'
    simpa [C.psiG_apply] using h'.symm
  have psiG_mem_CM : ∀ {g : ↥CT}, (g : G) ∈ H → ∃ m : ↥Max3.M,
      C.psiG m = (g : G) ∧ m ∈ CM := by
    intro g hgH
    let m : ↥Max3.M := C.ψ.symm ⟨(g : G), hgH⟩
    have hmψ : C.psiG m = (g : G) :=
      congrArg Subtype.val (C.ψ.apply_symm_apply ⟨(g : G), hgH⟩)
    have hmCM : m ∈ CM := by
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hgCT : (g : G) ∈ CT := g.2
      have hcommG : (g : G) * (C.ψ tM : G) = (C.ψ tM : G) * (g : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hgCT
      apply C.ψ.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      have hmψ' : (C.ψ m : G) = (g : G) := by
        rw [← C.psiG_apply]
        exact hmψ
      simpa [Subgroup.coe_mul, hmψ'] using hcommG.symm
    exact ⟨m, hmψ, hmCM⟩
  have hKH : ∀ {K : Subgroup ↥Max3.M}, K ≤ CM →
      (K.map C.psiG).subgroupOf CT ≤ H.subgroupOf CT := by
    intro K hK x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    rw [← hhx]
    exact (C.ψ h).2
  have conj_mem_K1 : ∀ {K : Subgroup ↥Max3.M}, CM ≤ Subgroup.normalizer (K : Set ↥Max3.M) →
      ∀ {g : ↥CT}, (g : G) ∈ H → ∀ {x : ↥CT},
      x ∈ (K.map C.psiG).subgroupOf CT → g * x * g⁻¹ ∈ (K.map C.psiG).subgroupOf CT := by
    intro K hKn g hgH x hx
    obtain ⟨m, hmψ, hmCM⟩ := psiG_mem_CM hgH
    obtain ⟨h, hhK, hhx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine Subgroup.mem_map.mpr ⟨m * h * m⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hKn hmCM) h).mp hhK
    · calc C.psiG (m * h * m⁻¹) = C.psiG m * C.psiG h * (C.psiG m)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = (g : G) * (x : G) * (g : G)⁻¹ := by rw [hmψ, hhx]
        _ = ((g * x * g⁻¹ : ↥CT) : G) := by simp [Subgroup.coe_mul, Subgroup.coe_inv]
  have normal_bar : ∀ {K : Subgroup ↥Max3.M}, CM ≤ Subgroup.normalizer (K : Set ↥Max3.M) →
      Hb ≤ Subgroup.normalizer (C.barOf π K : Set Y) := by
    intro K hKn
    rw [show Hb = (H.subgroupOf CT).map π from by
      rw [C.map_centralizer_z_eq htM π hπ hker]]
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map π)
    intro g hg
    have hgH : (g : G) ∈ H := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_K1 hKn hgH hx
    · intro hx
      have hginvH : ((g⁻¹ : ↥CT) : G) ∈ H := H.inv_mem hgH
      have h := conj_mem_K1 hKn hginvH hx
      have hx' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
      rwa [hx'] at h
  have barEquiv : ∀ {K : Subgroup ↥Max3.M}, K ≤ CM → tM ∉ K →
      Nonempty (↥K ≃* ↥(C.barOf π K)) := by
    intro K hK htK
    let ψK : ↥K →* ↥CT :=
      { toFun := fun x => ⟨(C.ψ x : G), hCT hK x⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by intro a b; apply Subtype.ext; simp [map_mul] }
    let φK : ↥K →* ↥(C.barOf π K) :=
      { toFun := fun x => ⟨π (ψK x), Subgroup.mem_map_of_mem π
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem C.psiG x.2))⟩
        map_one' := by
          apply Subtype.ext
          change π (ψK 1) = 1
          rw [show ψK 1 = 1 from map_one ψK, map_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          change π (ψK (a * b)) = π (ψK a) * π (ψK b)
          rw [map_mul ψK, map_mul] }
    have hinj : Function.Injective φK := by
      have h := C.pi_psi_injective_on (K := K) htM π hπ hker hK htK
      intro a b hab
      exact h (by simpa [φK, ψK] using hab)
    have hsurj : Function.Surjective φK := by
      intro y
      obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp y.2
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hg)
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      change π (ψK ⟨x, hx⟩) = (y : Y)
      have hψ : ψK ⟨x, hx⟩ = g := Subtype.ext hxg
      rw [hψ, hgy]
    exact ⟨MulEquiv.ofBijective φK ⟨hinj, hsurj⟩⟩
  have hK1H : K1 ≤ H.subgroupOf CT := hKH hH.le_one
  have hK2H : K2 ≤ H.subgroupOf CT := hKH hH.le_two
  have hnot1 : tM ∉ H₁ := by
    intro h
    exact hH.not_mem (Subgroup.mem_sup_left h)
  have hnot2 : tM ∉ H₂ := by
    intro h
    exact hH.not_mem (Subgroup.mem_sup_right h)
  have iso1 : Nonempty (↥H1b ≃* SL(2, ZMod 3)) := by
    obtain ⟨e⟩ := barEquiv hH.le_one hnot1
    exact ⟨e.symm.trans hH.iso_one.some⟩
  have iso2 : Nonempty (↥H2b ≃* SL(2, ZMod 3)) := by
    obtain ⟨e⟩ := barEquiv hH.le_two hnot2
    exact ⟨e.symm.trans hH.iso_two.some⟩
  have hcardSL : Nat.card (SL(2, ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcard1 : Nat.card ↥H1b = 24 := by
    obtain ⟨e⟩ := iso1
    rw [Nat.card_congr e.toEquiv, hcardSL]
  have hcard2 : Nat.card ↥H2b = 24 := by
    obtain ⟨e⟩ := iso2
    rw [Nat.card_congr e.toEquiv, hcardSL]
  have hHbcard : Nat.card ↥Hb = 576 := by
    change Nat.card ↥(Subgroup.centralizer ({π (C.zC tM)} : Set Y)) = 576
    exact C.card_centralizer_zbar htM hCt π hπ hker
  have hnormal1 : Hb ≤ Subgroup.normalizer (H1b : Set Y) := by
    change Hb ≤ Subgroup.normalizer (C.barOf π H₁ : Set Y)
    exact normal_bar hH.normal_one
  have hnormal2 : Hb ≤ Subgroup.normalizer (H2b : Set Y) := by
    change Hb ≤ Subgroup.normalizer (C.barOf π H₂ : Set Y)
    exact normal_bar hH.normal_two
  have hHb_eq : Hb = (H.subgroupOf CT).map π := by
    rw [C.map_centralizer_z_eq htM π hπ hker]
  have barOf_mono : ∀ {K L : Subgroup ↥Max3.M}, K ≤ L → C.barOf π K ≤ C.barOf π L := by
    intro K L hKL
    change ((K.map C.psiG).subgroupOf CT).map π ≤ ((L.map C.psiG).subgroupOf CT).map π
    refine Subgroup.map_mono ?_
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.map_mono hKL hx
  have le1 : H1b ≤ Hb := by
    rw [hHb_eq]
    exact Subgroup.map_mono hK1H
  have le2 : H2b ≤ Hb := by
    rw [hHb_eq]
    exact Subgroup.map_mono hK2H
  have hjoin : H₁ ⊔ H₂ ≤ CM := sup_le hH.le_one hH.le_two
  have hinj_join := C.pi_psi_injective_on (K := H₁ ⊔ H₂) htM π hπ hker hjoin hH.not_mem
  have hK0le : H₁ ⊓ H₂ ≤ CM := inf_le_left.trans hH.le_one
  have hnot0 : tM ∉ H₁ ⊓ H₂ := by
    intro h
    exact hH.not_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mp h).1)
  have hcardBar0 : Nat.card ↥(C.barOf π (H₁ ⊓ H₂)) = 2 := by
    obtain ⟨e⟩ := barEquiv hK0le hnot0
    calc Nat.card ↥(C.barOf π (H₁ ⊓ H₂)) = Nat.card ↥(H₁ ⊓ H₂) :=
          (Nat.card_congr e.toEquiv).symm
      _ = 2 := hH.card_inf
  have hpre1 : ∀ {y : Y}, y ∈ H1b → ∃ x : ↥H₁,
      π ⟨(C.ψ x : G), hCT hH.le_one x⟩ = y := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [← hgy]
    congr 1
    apply Subtype.ext
    exact hxg
  have hpre2 : ∀ {y : Y}, y ∈ H2b → ∃ x : ↥H₂,
      π ⟨(C.ψ x : G), hCT hH.le_two x⟩ = y := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [← hgy]
    congr 1
    apply Subtype.ext
    exact hxg
  have hbar0_ge : H1b ⊓ H2b ≤ C.barOf π (H₁ ⊓ H₂) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x1, hx1⟩ := hpre1 hy1
    obtain ⟨x2, hx2⟩ := hpre2 hy2
    have e1 : (⟨(C.ψ (x1 : ↥Max3.M) : G), hCT hH.le_one x1⟩ : ↥CT) =
        ⟨(C.ψ (x1 : ↥Max3.M) : G),
          hCT hjoin ⟨(x1 : ↥Max3.M), Subgroup.mem_sup_left x1.2⟩⟩ :=
      Subtype.ext rfl
    have e2 : (⟨(C.ψ (x2 : ↥Max3.M) : G), hCT hH.le_two x2⟩ : ↥CT) =
        ⟨(C.ψ (x2 : ↥Max3.M) : G),
          hCT hjoin ⟨(x2 : ↥Max3.M), Subgroup.mem_sup_right x2.2⟩⟩ :=
      Subtype.ext rfl
    have hx1' := hx1
    have hx2' := hx2
    rw [← e1] at hx1'
    rw [← e2] at hx2'
    have hπeq : π ⟨(C.ψ (x1 : ↥Max3.M) : G),
          hCT hjoin ⟨(x1 : ↥Max3.M), Subgroup.mem_sup_left x1.2⟩⟩ =
        π ⟨(C.ψ (x2 : ↥Max3.M) : G),
          hCT hjoin ⟨(x2 : ↥Max3.M), Subgroup.mem_sup_right x2.2⟩⟩ :=
      hx1'.trans hx2'.symm
    have heq : (⟨(x1 : ↥Max3.M), Subgroup.mem_sup_left x1.2⟩ : ↥(H₁ ⊔ H₂)) =
        ⟨(x2 : ↥Max3.M), Subgroup.mem_sup_right x2.2⟩ := by
      apply hinj_join
      simpa using hπeq
    have hx12 : (x1 : ↥Max3.M) = (x2 : ↥Max3.M) := congrArg Subtype.val heq
    rw [← hx1]
    change π ⟨(C.ψ (x1 : ↥Max3.M) : G), hCT hH.le_one x1⟩ ∈
      Subgroup.map π (((H₁ ⊓ H₂).map C.psiG).subgroupOf CT)
    have hx1inf : (x1 : ↥Max3.M) ∈ H₁ ⊓ H₂ :=
      ⟨x1.2, by rw [hx12]; exact x2.2⟩
    have hmem : (⟨(C.ψ (x1 : ↥Max3.M) : G), hCT hK0le ⟨x1, hx1inf⟩⟩ : ↥CT) ∈
        ((H₁ ⊓ H₂).map C.psiG).subgroupOf CT := by
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem C.psiG hx1inf)
    exact Subgroup.mem_map_of_mem π hmem
  have hinf_eq : H1b ⊓ H2b = C.barOf π (H₁ ⊓ H₂) :=
    le_antisymm hbar0_ge (le_inf (barOf_mono inf_le_left) (barOf_mono inf_le_right))
  have hcardinf : Nat.card ↥(H1b ⊓ H2b) = 2 := by
    rw [hinf_eq, hcardBar0]
  have hzbar_mem : π (C.zC tM) ∈ H1b ⊓ H2b := by
    refine ⟨?_, ?_⟩
    · change π (C.zC tM) ∈ ((H₁.map C.psiG).subgroupOf CT).map π
      refine Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ?_)
      have hzM : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ H₁ :=
        (Subgroup.mem_inf.mp hH.z_mem).1
      have hzψ : C.psiG (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) = (C.zC tM : G) := by
        rw [C.psiG_apply]
        exact C.psi_z
      rw [← hzψ]
      exact Subgroup.mem_map_of_mem C.psiG hzM
    · change π (C.zC tM) ∈ ((H₂.map C.psiG).subgroupOf CT).map π
      refine Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ?_)
      have hzM : (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) ∈ H₂ :=
        (Subgroup.mem_inf.mp hH.z_mem).2
      have hzψ : C.psiG (⟨Max3.z, Max3.z_mem_M⟩ : ↥Max3.M) = (C.zC tM : G) := by
        rw [C.psiG_apply]
        exact C.psi_z
      rw [← hzψ]
      exact Subgroup.mem_map_of_mem C.psiG hzM
  have hzbar_ne : π (C.zC tM) ≠ 1 := by
    intro h
    have hzCord : orderOf (C.zC tM) = 2 := by
      rw [show C.zC tM = ⟨C.z, by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        exact (Subgroup.mem_centralizer_singleton_iff.mp (C.ψ tM).2).symm⟩ from rfl,
        Subgroup.orderOf_mk]
      exact C.orderOf_z
    have hmem : C.zC tM ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact h
    rw [hker] at hmem
    have hdvd : orderOf (C.zC tM) ∣ orderOf (⟨(C.ψ tM : G),
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : ↥CT) := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers
        (⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : ↥CT)) hmem
      rwa [Nat.card_zpowers] at this
    have htord : orderOf (⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥CT) = 3 := by
      rw [Subgroup.orderOf_mk]
      rw [show (C.ψ tM : G) = ((C.ψ tM : ↥H) : G) from rfl, Subgroup.orderOf_coe,
        MulEquiv.orderOf_eq, htM]
    rw [hzCord, htord] at hdvd
    norm_num at hdvd
  have hzbar2 : π (C.zC tM) * π (C.zC tM) = 1 := by
    rw [← map_mul]
    have hzC2 : C.zC tM * C.zC tM = 1 := by
      apply Subtype.ext
      change C.z * C.z = 1
      have := pow_orderOf_eq_one C.z
      rwa [C.orderOf_z, pow_two] at this
    rw [hzC2, map_one]
  have hzbarord : orderOf (π (C.zC tM)) = 2 := by
    apply orderOf_eq_prime
    · rwa [pow_two]
    · exact hzbar_ne
  have hzpowers_eq : H1b ⊓ H2b = Subgroup.zpowers (π (C.zC tM)) := by
    have hle : Subgroup.zpowers (π (C.zC tM)) ≤ H1b ⊓ H2b :=
      Subgroup.zpowers_le.mpr hzbar_mem
    have hcardzp : Nat.card ↥(Subgroup.zpowers (π (C.zC tM))) = 2 := by
      rw [Nat.card_zpowers, hzbarord]
    exact (Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (hcardinf.trans hcardzp.symm))).symm
  have hcent_zp : Subgroup.centralizer (Subgroup.zpowers (π (C.zC tM)) : Set Y) =
      Subgroup.centralizer ({π (C.zC tM)} : Set Y) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      exact hx (π (C.zC tM)) (Subgroup.mem_zpowers _)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← hk]
      have hcomm : Commute x (π (C.zC tM)) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx
      exact (hcomm.zpow_right k).eq.symm
  have hHbC : Hb = Subgroup.centralizer ({π (C.zC tM)} : Set Y) :=
    hHb_eq.trans (C.map_centralizer_z_eq htM π hπ hker)
  have hcent_eq : Hb = Subgroup.centralizer ((H1b ⊓ H2b : Subgroup Y) : Set Y) := by
    rw [hzpowers_eq, hcent_zp, ← hHbC]
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := H1b) (K := H2b) (le_trans le1 hnormal2)
  have hsupcard : Nat.card ↥(H1b ⊔ H2b) = 288 := by
    rw [hcardinf, hcard1, hcard2] at hprod
    omega
  have hindex : (H1b ⊔ H2b).relIndex Hb = 2 := by
    have hrel := Subgroup.relIndex_mul_card (H1b ⊔ H2b) Hb
    rw [inf_eq_left.mpr (sup_le le1 le2), hsupcard, hHbcard] at hrel
    omega
  exact
    { le_one := le1
      le_two := le2
      normal_one := hnormal1
      normal_two := hnormal2
      iso_one := iso1
      iso_two := iso2
      index := hindex
      card_inf := hcardinf
      eq_centralizer := hcent_eq }

theorem ThCore.exists_g23One (C : ThCore G) {tM : ↥Max3.M} (htM : orderOf tM = 3)
    (hCt : Nat.card ↥(Subgroup.centralizer ({tM} : Set ↥Max3.M)) = 1728)
    (hG1 : ∃ H₁ H₂ : Subgroup ↥Max3.M, MG1 tM H₁ H₂)
    {Y : Type} [Group Y] (π : ↥(Subgroup.centralizer ({(C.ψ tM : G)} : Set G)) →* Y)
    (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers
      ⟨(C.ψ tM : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    ∃ H H₁ H₂ : Subgroup Y, CFSG.Quasithin.G23Type.G23One H H₁ H₂ := by
  obtain ⟨H₁, H₂, hH⟩ := hG1
  exact ⟨_, _, _, C.g23One_barOf htM hCt hH π hπ hker⟩

end CFSG.Sporadic.Th.Recog
