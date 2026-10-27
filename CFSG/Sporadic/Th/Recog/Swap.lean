module

public import CFSG.Sporadic.Th.Recog.Setting
public import CFSG.Sporadic.Th.Recog.AltNine
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.GF2Type.Entry

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Yardstones.M3aba7dc4b8a8

namespace ThSetting

variable {G : Type} [Group G] [Finite G]

theorem Q_normal (S : ThSetting G) : (S.Q.subgroupOf S.H).Normal := by
  have h := (CFSG.LocalCores.generalized_fitting_characteristic (G := S.H)).2
  have hQ : S.Q.subgroupOf S.H = generalizedFitting S.H := by
    ext x
    simp [Q, coreQ, inSubgroup, Subgroup.mem_subgroupOf]
  rwa [hQ]

theorem centralizer_Q_le (S : ThSetting G) :
    Subgroup.centralizer (S.Q : Set G) ⊓ S.H ≤ S.Q := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxcent, hxH⟩ := hx
  have hmem : (⟨x, hxH⟩ : S.H) ∈
      Subgroup.centralizer (generalizedFitting S.H : Set S.H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyQ : (y : G) ∈ S.Q := by
      change (y : G) ∈ (generalizedFitting S.H).map S.H.subtype
      exact Subgroup.mem_map_of_mem S.H.subtype hy
    exact Subgroup.mem_centralizer_iff.mp hxcent (y : G) hyQ
  have hgen : (⟨x, hxH⟩ : S.H) ∈ generalizedFitting S.H :=
    CFSG.centralizer_generalizedFitting_le S.H hmem
  change x ∈ (generalizedFitting S.H).map S.H.subtype
  exact Subgroup.mem_map_of_mem S.H.subtype hgen

theorem card_centralizer_le (S : ThSetting G)
    {k : G} (hkH : k ∈ S.H) (hkQ : k ∉ S.Q) (h2 : k ^ 2 = 1) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set G) ⊓ S.H) ≤ 2 ^ 8 * 480 := by
  classical
  set T : Subgroup G := Subgroup.centralizer ({k} : Set G) ⊓ S.H
  have hTle : T ≤ S.H := inf_le_right
  let ψ : T →* alternatingGroup (Fin 9) := S.θ.comp (Subgroup.inclusion hTle)
  have hker : ψ.ker = (T ⊓ S.Q).subgroupOf T := by
    ext x
    constructor
    · intro hx
      have hx' : Subgroup.inclusion hTle x ∈ S.θ.ker := MonoidHom.mem_ker.mpr hx
      rw [S.θ_ker] at hx'
      exact ⟨x.2, Subgroup.mem_subgroupOf.mp hx'⟩
    · rintro ⟨-, hxQ⟩
      change Subgroup.inclusion hTle x ∈ S.θ.ker
      rw [S.θ_ker]
      exact Subgroup.mem_subgroupOf.mpr hxQ
  have hcard_ker : Nat.card ↥ψ.ker = Nat.card ↥(T ⊓ S.Q) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hproper : T ⊓ S.Q < S.Q := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    apply hkQ
    have hcent : k ∈ Subgroup.centralizer (S.Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyT : y ∈ T := by
        have : y ∈ T ⊓ S.Q := by rw [heq]; exact hy
        exact this.1
      exact Subgroup.mem_centralizer_singleton_iff.mp hyT.1
    exact S.centralizer_Q_le (Subgroup.mem_inf.mpr ⟨hcent, hkH⟩)
  have hcard_Qt : Nat.card ↥(T ⊓ S.Q) ≤ 2 ^ 8 := by
    have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((T ⊓ S.Q).subgroupOf S.Q)
    have hne : (T ⊓ S.Q).subgroupOf S.Q ≠ ⊤ := by
      intro htop
      apply hproper.ne
      refine le_antisymm inf_le_right fun y hy => ?_
      have hy' : (⟨y, hy⟩ : S.Q) ∈ (T ⊓ S.Q).subgroupOf S.Q := by rw [htop]; trivial
      exact ⟨by simpa using (Subgroup.mem_subgroupOf.mp hy').1, hy⟩
    have hindex : 2 ≤ Nat.card (S.Q ⧸ (T ⊓ S.Q).subgroupOf S.Q) := by
      have h1 : 1 < ((T ⊓ S.Q).subgroupOf S.Q).index :=
        Subgroup.one_lt_index_of_ne_top hne
      rwa [Subgroup.index_eq_card] at h1
    have hcardQ : Nat.card ↥S.Q = 2 ^ 9 := S.card_Q
    have hcardQ' : Nat.card ↥((T ⊓ S.Q).subgroupOf S.Q) = Nat.card ↥(T ⊓ S.Q) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcardQ'] at hquot
    have hle : 2 * Nat.card ↥(T ⊓ S.Q) ≤ 2 ^ 9 := by
      calc 2 * Nat.card ↥(T ⊓ S.Q)
          ≤ Nat.card (S.Q ⧸ (T ⊓ S.Q).subgroupOf S.Q) * Nat.card ↥(T ⊓ S.Q) :=
            Nat.mul_le_mul_right _ hindex
        _ = Nat.card ↥S.Q := hquot.symm
        _ = 2 ^ 9 := hcardQ
    norm_num at hle ⊢
    omega
  have hrange : Nat.card ↥ψ.range ≤ 480 := by
    have hle : ψ.range ≤
        Subgroup.centralizer ({S.θ ⟨k, hkH⟩} : Set (alternatingGroup (Fin 9))) := by
      rintro a ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change S.θ (Subgroup.inclusion hTle x) * S.θ ⟨k, hkH⟩ =
        S.θ ⟨k, hkH⟩ * S.θ (Subgroup.inclusion hTle x)
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp x.2.1
    have hord : orderOf (S.θ ⟨k, hkH⟩) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow]
        have hk2 : (⟨k, hkH⟩ : S.H) ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, h2, OneMemClass.coe_one]
        rw [hk2, map_one]
      · intro h1
        apply hkQ
        have hmem : (⟨k, hkH⟩ : S.H) ∈ S.θ.ker := MonoidHom.mem_ker.mpr h1
        rw [S.θ_ker] at hmem
        exact Subgroup.mem_subgroupOf.mp hmem
    exact (Subgroup.card_le_of_le hle).trans (card_centralizer_le_of_orderOf_eq_two hord)
  have hcard := Subgroup.card_ker_mul_card_range ψ
  calc Nat.card T = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := hcard.symm
    _ ≤ 2 ^ 8 * 480 := Nat.mul_le_mul (hcard_ker.le.trans hcard_Qt) hrange

theorem card_centralizer_h₀_gt (S : ThSetting G) :
    2 ^ 8 * 480 < Nat.card ↥(Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H) := by
  classical
  let h₀H : S.H := ⟨S.h₀, S.Q_le_H S.h₀_mem_Q⟩
  have hsub : (Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H).subgroupOf S.H =
      Subgroup.centralizer ({h₀H} : Set S.H) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx)
    · intro hx
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hx)), x.2⟩
  have hcardC : Nat.card ↥(Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H) =
      Nat.card ↥(MulAction.stabilizer (ConjAct S.H) h₀H) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hsub,
      Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have hprod : Nat.card (MulAction.orbit (ConjAct S.H) h₀H) *
      Nat.card ↥(Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H) = Nat.card S.H := by
    haveI : Finite (ConjAct S.H) := Finite.of_equiv S.H ConjAct.ofConjAct.toEquiv.symm
    let _ : Fintype (ConjAct S.H) := Fintype.ofFinite _
    let _ : Fintype (MulAction.orbit (ConjAct S.H) h₀H) := Fintype.ofFinite _
    let _ : Fintype (MulAction.stabilizer (ConjAct S.H) h₀H) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct S.H) h₀H
    simp only [← Nat.card_eq_fintype_card] at h
    rw [Nat.card_congr ConjAct.ofConjAct.toEquiv, ← hcardC] at h
    exact h
  have horbit : Nat.card (MulAction.orbit (ConjAct S.H) h₀H) ≤ 2 ^ 9 := by
    have hsubQ : (MulAction.orbit (ConjAct S.H) h₀H : Set S.H) ⊆
        {x : S.H | (x : G) ∈ S.Q} := by
      intro x hx
      rw [ConjAct.mem_orbit_conjAct] at hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have hconj : c⁻¹ * h₀H * c ∈ S.Q.subgroupOf S.H := by
        simpa using S.Q_normal.conj_mem h₀H (Subgroup.mem_subgroupOf.mpr S.h₀_mem_Q) c⁻¹
      have hxQ : ((c⁻¹ * h₀H * c : S.H) : G) ∈ S.Q := Subgroup.mem_subgroupOf.mp hconj
      have hx_eq : x = c⁻¹ * h₀H * c := by
        rw [← hc]
        group
      rw [hx_eq]
      exact hxQ
    have hcard : Nat.card {x : S.H // (x : G) ∈ S.Q} = 2 ^ 9 := by
      have e : {x : S.H // (x : G) ∈ S.Q} ≃ S.Q :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun q => ⟨⟨q.1, S.Q_le_H q.2⟩, q.2⟩
          left_inv := fun x => by
            apply Subtype.ext
            apply Subtype.ext
            rfl
          right_inv := fun q => by
            apply Subtype.ext
            rfl }
      rw [Nat.card_congr e, S.card_Q]
    calc Nat.card (MulAction.orbit (ConjAct S.H) h₀H)
        = (MulAction.orbit (ConjAct S.H) h₀H).ncard := Nat.card_coe_set_eq _
      _ ≤ {x : S.H | (x : G) ∈ S.Q}.ncard := Set.ncard_le_ncard hsubQ
      _ = Nat.card {x : S.H // (x : G) ∈ S.Q} := (Nat.card_coe_set_eq _).symm
      _ = 2 ^ 9 := hcard
  by_contra hle
  push Not at hle
  have hHle : Nat.card S.H ≤ 2 ^ 9 * (2 ^ 8 * 480) := by
    calc Nat.card S.H = Nat.card (MulAction.orbit (ConjAct S.H) h₀H) *
          Nat.card ↥(Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H) := hprod.symm
      _ ≤ 2 ^ 9 * (2 ^ 8 * 480) := Nat.mul_le_mul horbit hle
  rw [S.card_H] at hHle
  norm_num at hHle

theorem exists_conj_Q (S : ThSetting G) :
    ∃ y : G, y * S.h₀ * y⁻¹ = S.z ∧ y * S.z * y⁻¹ ∈ S.Q ∧
      y * S.z * y⁻¹ ≠ S.z := by
  refine ⟨S.g₀, ?_, ?_, ?_⟩
  · rw [h₀_def]
    group
  · by_contra hkQ
    have hh₀H : S.h₀ ∈ S.H := S.Q_le_H S.h₀_mem_Q
    have hzh : S.h₀ * S.z = S.z * S.h₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp hh₀H
    have hzh' : S.g₀ * S.h₀ * S.g₀⁻¹ = S.z := by
      rw [h₀_def]
      group
    have hkH : S.g₀ * S.z * S.g₀⁻¹ ∈ S.H := by
      rw [H, Subgroup.mem_centralizer_singleton_iff]
      calc (S.g₀ * S.z * S.g₀⁻¹) * S.z
          = (S.g₀ * S.z * S.g₀⁻¹) * (S.g₀ * S.h₀ * S.g₀⁻¹) := by rw [hzh']
        _ = S.g₀ * (S.z * S.h₀) * S.g₀⁻¹ := by group
        _ = S.g₀ * (S.h₀ * S.z) * S.g₀⁻¹ := by rw [hzh.symm]
        _ = (S.g₀ * S.h₀ * S.g₀⁻¹) * (S.g₀ * S.z * S.g₀⁻¹) := by group
        _ = S.z * (S.g₀ * S.z * S.g₀⁻¹) := by rw [hzh']
    have hk2 : (S.g₀ * S.z * S.g₀⁻¹) ^ 2 = 1 := by
      have hz2 : S.z ^ 2 = 1 := by rw [← S.ord_z, pow_orderOf_eq_one]
      calc (S.g₀ * S.z * S.g₀⁻¹) ^ 2
          = (S.g₀ * S.z * S.g₀⁻¹) * (S.g₀ * S.z * S.g₀⁻¹) := pow_two _
        _ = S.g₀ * (S.z * S.z) * S.g₀⁻¹ := by group
        _ = S.g₀ * S.z ^ 2 * S.g₀⁻¹ := by rw [pow_two]
        _ = 1 := by rw [hz2]; group
    have hbound := S.card_centralizer_le hkH hkQ hk2
    have hmap1 : (Subgroup.centralizer ({S.h₀} : Set G)).map
        (MulAut.conj S.g₀).toMonoidHom = Subgroup.centralizer ({S.z} : Set G) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
      congr 1
      rw [h₀_def]
      group
    have hmap2 : S.H.map (MulAut.conj S.g₀).toMonoidHom =
        Subgroup.centralizer ({S.g₀ * S.z * S.g₀⁻¹} : Set G) := by
      rw [H, CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
    have hcard_eq : Nat.card ↥(Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H) =
        Nat.card ↥(Subgroup.centralizer ({S.g₀ * S.z * S.g₀⁻¹} : Set G) ⊓ S.H) := by
      calc Nat.card ↥(Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H)
          = Nat.card ↥((Subgroup.centralizer ({S.h₀} : Set G) ⊓ S.H).map
              (MulAut.conj S.g₀).toMonoidHom) :=
            Nat.card_congr (Subgroup.equivMapOfInjective _ _
              (MulAut.conj S.g₀).injective).toEquiv
        _ = Nat.card ↥((Subgroup.centralizer ({S.h₀} : Set G)).map
              (MulAut.conj S.g₀).toMonoidHom ⊓ S.H.map
              (MulAut.conj S.g₀).toMonoidHom) := by
            rw [Subgroup.map_inf _ _ _ (MulAut.conj S.g₀).injective]
        _ = Nat.card ↥(Subgroup.centralizer ({S.z} : Set G) ⊓
              Subgroup.centralizer ({S.g₀ * S.z * S.g₀⁻¹} : Set G)) := by
            rw [hmap1, hmap2]
        _ = Nat.card ↥(Subgroup.centralizer ({S.g₀ * S.z * S.g₀⁻¹} : Set G) ⊓ S.H) := by
            rw [inf_comm]
    have hgt := S.card_centralizer_h₀_gt
    rw [hcard_eq] at hgt
    norm_num at hbound hgt
    omega
  · intro hkz
    apply S.h₀_ne_z
    have hg₀H : S.g₀ * S.z = S.z * S.g₀ := by
      calc S.g₀ * S.z = (S.g₀ * S.z * S.g₀⁻¹) * S.g₀ := by group
        _ = S.z * S.g₀ := by rw [hkz]
    rw [h₀_def]
    calc S.g₀⁻¹ * S.z * S.g₀ = S.g₀⁻¹ * (S.z * S.g₀) := by group
      _ = S.g₀⁻¹ * (S.g₀ * S.z) := by rw [← hg₀H]
      _ = S.z := by group

@[expose] noncomputable def toSetting (S : ThSetting G) : CFSG.LargeExtraspecial.Setting G :=
  { CFSG.LargeExtraspecial.Setting.ofFStar S.z S.ord_z
      (CFSG.GF2Type.timmesfeld_hypotheses (w := 4) S.ext (by
        simpa using S.card_Q)).1 with z := S.z }

@[simp] theorem toSetting_z (S : ThSetting G) : S.toSetting.z = S.z := rfl

@[expose] def toSettingE (S : ThSetting G) : S.H →* S.toSetting.M :=
  { toFun := fun h => ⟨h, by
      rw [CFSG.LargeExtraspecial.Setting.M, toSetting_z]
      exact h.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

theorem toSetting_QG (S : ThSetting G) : S.toSetting.QG = S.Q := by
  unfold toSetting
  rw [CFSG.LargeExtraspecial.Setting.QG, CFSG.LargeExtraspecial.Setting.ofFStar_Q,
    CFSG.Adapters.timmesfeldFStar_eq_foundations]
  rfl

theorem toSetting_Q_eq (S : ThSetting G) :
    S.toSetting.Q = S.Q.subgroupOf S.H := by
  unfold toSetting
  ext x
  rw [CFSG.LargeExtraspecial.Setting.ofFStar_Q,
    CFSG.Adapters.timmesfeldFStar_eq_foundations, Subgroup.mem_subgroupOf]
  change x ∈ generalizedFitting S.H ↔
    (x : G) ∈ (generalizedFitting S.H).map S.H.subtype
  exact ⟨Subgroup.mem_map_of_mem S.H.subtype, fun hx => by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rwa [show y = x from Subtype.ext hyx] at hy⟩

theorem card_toSetting_Q (S : ThSetting G) :
    Nat.card ↥S.toSetting.Q = 2 ^ (1 + 2 * 4) := by
  unfold toSetting
  rw [CFSG.LargeExtraspecial.Setting.ofFStar_Q,
    CFSG.Adapters.timmesfeldFStar_eq_foundations,
    show 1 + 2 * 4 = 9 by norm_num,
    ← Subgroup.card_map_of_injective (K := generalizedFitting S.H) (f := S.H.subtype)
      S.H.subtype_injective]
  exact S.card_Q

theorem finrank_Qt (S : ThSetting G) :
    Module.finrank (ZMod 2) S.toSetting.Qt = 8 := by
  rw [S.toSetting.finrank_Qt_eq (n := 4) S.card_toSetting_Q]

@[expose] noncomputable def rho (S : ThSetting G) :
    alternatingGroup (Fin 9) →* (S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) :=
  let g : S.H →* (S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) :=
    S.toSetting.O.subtype.comp (S.toSetting.ρ.comp S.toSettingE)
  MonoidHom.liftOfRightInverse S.θ (Function.surjInv S.θ_surj)
    (Function.rightInverse_surjInv S.θ_surj) ⟨g, by
      intro x hx
      rw [MonoidHom.mem_ker]
      have hxQ : (x : G) ∈ S.Q := by
        rw [S.θ_ker] at hx
        exact Subgroup.mem_subgroupOf.mp hx
      have hxQG : (x : G) ∈ S.toSetting.QG := by
        rw [S.toSetting_QG]
        exact hxQ
      obtain ⟨hxM, hxQm⟩ := S.toSetting.mem_QG_iff.mp hxQG
      have h : S.toSetting.ρ (S.toSettingE x) = 1 := by
        apply S.toSetting.ρ_eq_one_of_mem_Q
        have heq : (⟨(x : G), hxM⟩ : S.toSetting.M) = S.toSettingE x :=
          Subtype.ext rfl
        rwa [← heq]
      simpa [g, MonoidHom.comp_apply] using h⟩

theorem rho_θ (S : ThSetting G) (h : S.H) :
    S.rho (S.θ h) =
      ((S.toSetting.ρ (S.toSettingE h) : S.toSetting.O) :
        S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) := by
  rw [rho, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem rho_injective (S : ThSetting G) : Function.Injective S.rho := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 9)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hsimple.eq_bot_or_eq_top_of_normal S.rho.ker with hker | hker
  · exact hker
  · exfalso
    have htriv : ∀ h : S.H, S.toSetting.ρ (S.toSettingE h) = 1 := by
      intro h
      have hmem : S.θ h ∈ S.rho.ker := by rw [hker]; trivial
      rw [MonoidHom.mem_ker] at hmem
      have hEq := S.rho_θ h
      rw [hmem] at hEq
      exact Subtype.ext (by simpa using hEq.symm)
    have hHQ : S.H ≤ S.Q := by
      intro h hh
      have hmemQ : (⟨h, hh⟩ : S.H) ∈ S.toSetting.Q :=
        S.toSetting.mem_Q_of_ρ_eq_one (htriv ⟨h, hh⟩)
      rw [← S.toSetting_QG]
      exact Subgroup.mem_map_of_mem S.H.subtype hmemQ
    have hcard : Nat.card S.H ≤ Nat.card S.Q := Subgroup.card_le_of_le hHQ
    rw [S.card_H, S.card_Q] at hcard
    norm_num at hcard

end ThSetting

end CFSG.Sporadic.Th.Recog
