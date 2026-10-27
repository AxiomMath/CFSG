module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J1Local17
public import CFSG.Quasithin.Vol2.Ch10SecKIVc
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Walter.J1Props.Factor
public import CFSG.Walter.Models
public import CFSG.Walter.AStar.Basic
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem j1A5Gen_commutator_centralizer_isAlt5_native
    (t : CFSG.Blueprint.NativeSporadic.J1) (ht : orderOf t = 2) :
    Nat.card
      ↥(⁅Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1),
         Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)⁆) = 60 ∧
      IsSimpleGroup
      ↥(⁅Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1),
         Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)⁆) ∧
      (∃ x y : ↥(⁅Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1),
         Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)⁆), x * y ≠ y * x) ∧
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt
      ↥(⁅Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1),
         Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)⁆) 5 := by
  classical
  let C : Subgroup CFSG.Blueprint.NativeSporadic.J1 :=
    Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)
  have hCcard : Nat.card ↥C = 120 :=
    (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free
      (G := CFSG.Blueprint.NativeSporadic.J1) ⟨MulEquiv.refl _⟩ t ht).1
  let K : Subgroup ↥C := Classical.choose
    (CFSG.Sporadic.Schreier.qt_unique_j1_involution_centralizer_normal_simple_subgroup t ht)
  have hKspec := Classical.choose_spec
    (CFSG.Sporadic.Schreier.qt_unique_j1_involution_centralizer_normal_simple_subgroup t ht)
  have hKn : K.Normal := hKspec.1
  have hKsimple : IsSimpleGroup ↥K := hKspec.2.1
  have hK60 : Nat.card ↥K = 60 := hKspec.2.2.1
  have hKnab : ∃ x y : ↥K, x * y ≠ y * x := hKspec.2.2.2.1
  have hKindex : K.index = 2 := by
    have hm := Subgroup.card_mul_index K
    rw [hK60, hCcard] at hm
    omega
  have hquot : Nat.card (↥C ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card, hKindex]
  have hcomm_le : commutator ↥C ≤ K := by
    have : IsCyclic (↥C ⧸ K) := by
      refine isCyclic_of_card_dvd_prime (p := 2) ?_
      rw [hquot]
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mp
      IsCyclic.isMulCommutative
  have hKperf : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hKnab).1.1
  have hK_le_comm : K ≤ commutator ↥C := by
    calc K = ⁅K, K⁆ := hKperf.symm
      _ ≤ ⁅(⊤ : Subgroup ↥C), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator ↥C := (commutator_def (G := ↥C)).symm
  have hcomm_eq : commutator ↥C = K := le_antisymm hcomm_le hK_le_comm
  have hmapC : Subgroup.map C.subtype (commutator ↥C) = ⁅C, C⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hB : ⁅C, C⁆ = K.map C.subtype := by
    rw [← hmapC, hcomm_eq]
  rw [hB]
  have eK := K.equivMapOfInjective C.subtype C.subtype_injective
  have hBcard : Nat.card ↥(K.map C.subtype) = 60 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hK60]
  have hBsimple : IsSimpleGroup ↥(K.map C.subtype) := MulEquiv.isSimpleGroup eK.symm
  have hBnab : ∃ x y : ↥(K.map C.subtype), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hKnab
    refine ⟨eK x, eK y, ?_⟩
    intro h
    apply hxy
    have h' := congrArg eK.symm h
    simpa using h'
  refine ⟨hBcard, hBsimple, hBnab, ?_⟩
  have : IsSimpleGroup ↥(K.map C.subtype) := hBsimple
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hBcard


private theorem j1A5Gen_commutator_centralizer_isAlt5
    {X : Type} [Group X] [Finite X] (hX : IsJ1 X) (t : X) (ht : orderOf t = 2) :
    Nat.card ↥(⁅Subgroup.centralizer ({t} : Set X),
        Subgroup.centralizer ({t} : Set X)⁆) = 60 ∧
      IsSimpleGroup ↥(⁅Subgroup.centralizer ({t} : Set X),
        Subgroup.centralizer ({t} : Set X)⁆) ∧
      (∃ x y : ↥(⁅Subgroup.centralizer ({t} : Set X),
        Subgroup.centralizer ({t} : Set X)⁆), x * y ≠ y * x) ∧
      UC22.IsAlt ↥(⁅Subgroup.centralizer ({t} : Set X),
        Subgroup.centralizer ({t} : Set X)⁆) 5 := by
  classical
  obtain ⟨e⟩ := hX
  let t' : CFSG.Blueprint.NativeSporadic.J1 := e t
  have ht' : orderOf t' = 2 := by
    change orderOf (e t) = 2
    rw [MulEquiv.orderOf_eq, ht]
  let C : Subgroup X := Subgroup.centralizer ({t} : Set X)
  let C' : Subgroup CFSG.Blueprint.NativeSporadic.J1 := Subgroup.centralizer ({t'} : Set _)
  have hCmap : C.map e.toMonoidHom = C' :=
    CFSG.Quasithin.A312S.map_centralizer_equiv e t
  have hBmap : (⁅C, C⁆).map e.toMonoidHom = ⁅C', C'⁆ := by
    rw [Subgroup.map_commutator, hCmap]
    rfl
  let eB : ↥(⁅C, C⁆) ≃* ↥(⁅C', C'⁆) :=
    ((⁅C, C⁆).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hBmap)
  have hnat := j1A5Gen_commutator_centralizer_isAlt5_native t' ht'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eB.toEquiv]
    exact hnat.1
  · have : IsSimpleGroup ↥(⁅C', C'⁆) := hnat.2.1
    exact MulEquiv.isSimpleGroup eB
  · obtain ⟨x, y, hxy⟩ := hnat.2.2.1
    refine ⟨eB.symm x, eB.symm y, ?_⟩
    intro h
    apply hxy
    have h' := congrArg eB h
    simpa using h'
  · exact ⟨eB.trans (Classical.choice hnat.2.2.2)⟩

private theorem j1A5Gen_exists_two_involutions_in_sylow
    {X : Type} [Group X] [Finite X] (hX : IsJ1 X) (P : Sylow 2 X) :
    ∃ t₁ t₂ : X, t₁ ∈ (P : Subgroup X) ∧ t₂ ∈ (P : Subgroup X) ∧
      orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ t₁ ≠ t₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hX
  let f : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  let fh : X →* CFSG.Open.walterJ1 := f
  have hf_surj : Function.Surjective fh := f.surjective
  let P' : Sylow 2 CFSG.Open.walterJ1 := Sylow.mapSurjective (f := fh) hf_surj P
  have hP'coe : (P' : Subgroup CFSG.Open.walterJ1) = (P : Subgroup X).map fh :=
    Sylow.coe_mapSurjective hf_surj P
  let Esub : Subgroup CFSG.Open.walterJ1 :=
    CFSG.Sporadic.Bridge.J1.elemAbelian.subgroupOf CFSG.Open.walterJ1
  have hle : CFSG.Sporadic.Bridge.J1.elemAbelian ≤ CFSG.Open.walterJ1 :=
    CFSG.Walter.J1Recog.walterJ1_eq ▸ CFSG.Sporadic.Bridge.J1.elemAbelian_le
  have hEcard : Nat.card Esub = 8 := by
    dsimp only [Esub]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      CFSG.Sporadic.Bridge.J1.card_elemAbelian]
  have hE2 : IsPGroup 2 Esub := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  have hidx : Esub.index = 21945 := by
    have hm := Esub.card_mul_index
    rw [hEcard, CFSG.Walter.J1Props.card_walterJ1] at hm
    omega
  have hidxodd : ¬ 2 ∣ Esub.index := by rw [hidx]; norm_num
  let E : Sylow 2 CFSG.Open.walterJ1 := hE2.toSylow hidxodd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Open.walterJ1 E P'
  let uElt (i : Fin 8) : CFSG.Sporadic.Bridge.J1.elemAbelian :=
    ⟨⟨CFSG.Sporadic.Bridge.J1.vMat i, CFSG.Sporadic.Bridge.J1.vMat i,
        CFSG.Sporadic.Bridge.J1.vMat_mul_self i,
        CFSG.Sporadic.Bridge.J1.vMat_mul_self i⟩,
      CFSG.Sporadic.Bridge.J1.mem_elemAbelian.mpr ⟨i, rfl⟩⟩
  let vElt (i : Fin 8) : CFSG.Open.walterJ1 :=
    ⟨(uElt i : GL (Fin 7) (ZMod 11)), hle (uElt i).2⟩
  have hvElt_mem (i : Fin 8) : vElt i ∈ Esub := by
    dsimp only [Esub]
    rw [Subgroup.mem_subgroupOf]
    change ((uElt i : GL (Fin 7) (ZMod 11))) ∈ CFSG.Sporadic.Bridge.J1.elemAbelian
    exact (uElt i).2
  have hvElt_sq (i : Fin 8) : vElt i * vElt i = 1 := by
    apply Subtype.ext
    have hsq : uElt i * uElt i = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact CFSG.Sporadic.Bridge.J1.vMat_mul_self i
    change ((uElt i : GL (Fin 7) (ZMod 11)) * (uElt i : GL (Fin 7) (ZMod 11))) = 1
    exact congrArg Subtype.val hsq
  have hvElt_ne {i : Fin 8} (hi : i ≠ 0) : vElt i ≠ 1 := by
    intro h
    have hmat : CFSG.Sporadic.Bridge.J1.vMat i = 1 := by
      have h1 := congrArg (fun y : CFSG.Open.walterJ1 =>
        ((y : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))) h
      simpa [vElt, uElt] using h1
    have h0 : CFSG.Sporadic.Bridge.J1.vMat (0 : Fin 8) = 1 := by
      simp [CFSG.Sporadic.Bridge.J1.vMat]
    have hi0 : i = 0 := CFSG.Sporadic.Bridge.J1.vMat_injective i 0 (by rw [hmat, h0])
    exact hi hi0
  have hvElt_ord {i : Fin 8} (hi : i ≠ 0) : orderOf (vElt i) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hvElt_sq i) (hvElt_ne hi)
  have hmem (i : Fin 8) : g * vElt i * g⁻¹ ∈ (P' : Subgroup CFSG.Open.walterJ1) := by
    rw [← hg]
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
    change g⁻¹ * (g * vElt i * g⁻¹) * g ∈ Esub
    rw [show g⁻¹ * (g * vElt i * g⁻¹) * g = vElt i by group]
    exact hvElt_mem i
  have hord {i : Fin 8} (hi : i ≠ 0) : orderOf (g * vElt i * g⁻¹) = 2 := by
    have hconj : g * vElt i * g⁻¹ = MulAut.conj g (vElt i) := by
      rw [MulAut.conj_apply]
    rw [hconj, MulEquiv.orderOf_eq, hvElt_ord hi]
  have hne : g * vElt 1 * g⁻¹ ≠ g * vElt 2 * g⁻¹ := by
    intro h
    have h' : vElt (1 : Fin 8) = vElt 2 := by
      calc vElt 1 = g⁻¹ * (g * vElt 1 * g⁻¹) * g := by group
        _ = g⁻¹ * (g * vElt 2 * g⁻¹) * g := by rw [h]
        _ = vElt 2 := by group
    have hmat : CFSG.Sporadic.Bridge.J1.vMat (1 : Fin 8) =
        CFSG.Sporadic.Bridge.J1.vMat 2 := by
      have h1 := congrArg (fun y : CFSG.Open.walterJ1 =>
        ((y : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))) h'
      simpa [vElt, uElt] using h1
    have h12 : (1 : Fin 8) = 2 := CFSG.Sporadic.Bridge.J1.vMat_injective 1 2 hmat
    norm_num at h12
  refine ⟨f.symm (g * vElt 1 * g⁻¹), f.symm (g * vElt 2 * g⁻¹), ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : f (f.symm (g * vElt 1 * g⁻¹)) ∈ (P : Subgroup X).map fh := by
      rw [← hP'coe]
      simpa using hmem 1
    exact (Subgroup.mem_map_iff_mem f.injective).mp h1
  · have h1 : f (f.symm (g * vElt 2 * g⁻¹)) ∈ (P : Subgroup X).map fh := by
      rw [← hP'coe]
      simpa using hmem 2
    exact (Subgroup.mem_map_iff_mem f.injective).mp h1
  · exact (MulEquiv.orderOf_eq f.symm (g * vElt 1 * g⁻¹)).trans (hord (by norm_num))
  · exact (MulEquiv.orderOf_eq f.symm (g * vElt 2 * g⁻¹)).trans (hord (by norm_num))
  · intro h
    apply hne
    exact f.symm.injective h


theorem k_J1A5Gen_holds :
    K_J1A5Gen := by
  intro X _ _ hJ1 S hS
  classical
  have hX : IsJ1 X := hJ1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hJ1
  let e : X ≃* CFSG.Blueprint.NativeSporadic.J1 := e₀
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J1 :=
    CFSG.Sporadic.J1.isSimpleGroup_J1
  have hsimpleX : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcardX : Nat.card X = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have hcenterX : Subgroup.center X = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
    · exact h
    · exfalso
      let : IsMulCommutative X :=
        IsMulCommutative.mk ⟨fun a b => by
          have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
          exact (Subgroup.mem_center_iff.mp ha b).symm⟩
      have hprime : (Nat.card X).Prime :=
        (Group.is_simple_iff_prime_card (α := X)).mp hsimpleX
      rw [hcardX] at hprime
      norm_num at hprime
  have hinner : ∀ θ : MulAut X, ∃ x : X, θ = MulAut.conj x := by
    intro θ
    obtain ⟨g, hg⟩ := (CFSG.Sporadic.Schreier.at_j1_schreier).2.1 (MulAut.congr e θ)
    refine ⟨e.symm g, ?_⟩
    have h1 : MulAut.congr e.symm (MulAut.congr e θ) = θ := by
      ext x
      simp [MulAut.congr_apply]
    have h2 := congrArg (MulAut.congr e.symm) hg
    rw [CFSG.mulAut_congr_conj] at h2
    rw [← h1, h2]
  let φ : X →* MulAut X := MulAut.conj
  let T : Subgroup X := S.comap φ
  have hTmap : T.map φ = S := by
    rw [Subgroup.map_comap_eq_self]
    intro s hs
    obtain ⟨x, hx⟩ := hinner s
    exact ⟨x, hx.symm⟩
  have hinjφ : Function.Injective φ :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenterX
  have hT : IsPGroup 2 T := hS.comap_of_injective φ hinjφ
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have hPsyl : CFSG.QuasithinUnique.IsSylowTwoOf (P : Subgroup X) ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨P.isPGroup', P.not_dvd_index⟩
  have hXab : CFSG.Walter.HasAbelianSylowTwo X := by
    let f : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
    let fh : CFSG.Open.walterJ1 →* X := f.symm
    have hfh : Function.Surjective fh := by
      simpa [fh] using f.symm.surjective
    exact CFSG.Walter.HasAbelianSylowTwo.of_surjective (G := CFSG.Open.walterJ1)
      (G' := X) (f := fh) hfh CFSG.Walter.J1Props.hasAbelianSylowTwo
  have hPab : IsMulCommutative (P : Subgroup X) := hXab P
  obtain ⟨t₁, t₂, ht₁P, ht₂P, ht₁, ht₂, hne12⟩ :=
    j1A5Gen_exists_two_involutions_in_sylow hX P
  let C₁ : Subgroup X := Subgroup.centralizer ({t₁} : Set X)
  let C₂ : Subgroup X := Subgroup.centralizer ({t₂} : Set X)
  let B₁ : Subgroup X := ⁅C₁, C₁⁆
  let B₂ : Subgroup X := ⁅C₂, C₂⁆
  have hB₁ : Nat.card ↥B₁ = 60 ∧ IsSimpleGroup ↥B₁ ∧
      (∃ x y : ↥B₁, x * y ≠ y * x) ∧ UC22.IsAlt ↥B₁ 5 := by
    simpa [B₁, C₁] using j1A5Gen_commutator_centralizer_isAlt5 hX t₁ ht₁
  have hB₂ : Nat.card ↥B₂ = 60 ∧ IsSimpleGroup ↥B₂ ∧
      (∃ x y : ↥B₂, x * y ≠ y * x) ∧ UC22.IsAlt ↥B₂ 5 := by
    simpa [B₂, C₂] using j1A5Gen_commutator_centralizer_isAlt5 hX t₂ ht₂
  have hPleC₁ : (P : Subgroup X) ≤ C₁ := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using hPab.is_comm.comm ⟨p, hp⟩ ⟨t₁, ht₁P⟩
  have hPleC₂ : (P : Subgroup X) ≤ C₂ := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using hPab.is_comm.comm ⟨p, hp⟩ ⟨t₂, ht₂P⟩
  have hPnormC₁ : (P : Subgroup X) ≤ Subgroup.normalizer (C₁ : Set X) := by
    intro p hp
    have hpt : MulAut.conj p t₁ = t₁ := by
      have h := hPleC₁ hp
      rw [Subgroup.mem_centralizer_singleton_iff] at h
      calc MulAut.conj p t₁ = p * t₁ * p⁻¹ := rfl
        _ = t₁ * p * p⁻¹ := by rw [h]
        _ = t₁ := by group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.centralizer ({t₁} : Set X)).map
      (MulAut.conj p).toMonoidHom = Subgroup.centralizer ({t₁} : Set X)
    rw [CFSG.Quasithin.A312S.map_centralizer_equiv (MulAut.conj p) t₁, hpt]
  have hPnormC₂ : (P : Subgroup X) ≤ Subgroup.normalizer (C₂ : Set X) := by
    intro p hp
    have hpt : MulAut.conj p t₂ = t₂ := by
      have h := hPleC₂ hp
      rw [Subgroup.mem_centralizer_singleton_iff] at h
      calc MulAut.conj p t₂ = p * t₂ * p⁻¹ := rfl
        _ = t₂ * p * p⁻¹ := by rw [h]
        _ = t₂ := by group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.centralizer ({t₂} : Set X)).map
      (MulAut.conj p).toMonoidHom = Subgroup.centralizer ({t₂} : Set X)
    rw [CFSG.Quasithin.A312S.map_centralizer_equiv (MulAut.conj p) t₂, hpt]
  have hPnormB₁ : (P : Subgroup X) ≤ Subgroup.normalizer (B₁ : Set X) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hCmap : C₁.map (MulAut.conj p).toMonoidHom = C₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPnormC₁ hp)
    have hB₁def : B₁ = ⁅C₁, C₁⁆ := rfl
    rw [hB₁def, Subgroup.map_commutator]
    change ⁅C₁.map (MulAut.conj p).toMonoidHom,
      C₁.map (MulAut.conj p).toMonoidHom⁆ = ⁅C₁, C₁⁆
    rw [hCmap]
  have hPnormB₂ : (P : Subgroup X) ≤ Subgroup.normalizer (B₂ : Set X) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hCmap : C₂.map (MulAut.conj p).toMonoidHom = C₂ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPnormC₂ hp)
    have hB₂def : B₂ = ⁅C₂, C₂⁆ := rfl
    rw [hB₂def, Subgroup.map_commutator]
    change ⁅C₂.map (MulAut.conj p).toMonoidHom,
      C₂.map (MulAut.conj p).toMonoidHom⁆ = ⁅C₂, C₂⁆
    rw [hCmap]
  have hB₁inv : ∀ s ∈ S, B₁.map s.toMonoidHom = B₁ := by
    intro s hs
    rw [← hTmap] at hs
    obtain ⟨t, htT, hts⟩ := Subgroup.mem_map.mp hs
    rw [← hts]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTP.trans hPnormB₁ htT)
  have hB₂inv : ∀ s ∈ S, B₂.map s.toMonoidHom = B₂ := by
    intro s hs
    rw [← hTmap] at hs
    obtain ⟨t, htT, hts⟩ := Subgroup.mem_map.mp hs
    rw [← hts]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTP.trans hPnormB₂ htT)
  have hB₁C : B₁ ≤ C₁ := Subgroup.commutator_le_self C₁
  have hB₂C : B₂ ≤ C₂ := Subgroup.commutator_le_self C₂
  have hmapC₁ : Subgroup.map C₁.subtype (commutator ↥C₁) = B₁ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hmapC₂ : Subgroup.map C₂.subtype (commutator ↥C₂) = B₂ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hB₁sub : (B₁.subgroupOf C₁).Normal := by
    rw [show B₁.subgroupOf C₁ = commutator ↥C₁ from ?_]
    · infer_instance
    · apply Subgroup.map_subtype_inj.mp
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB₁C, hmapC₁]
  have hB₂sub : (B₂.subgroupOf C₂).Normal := by
    rw [show B₂.subgroupOf C₂ = commutator ↥C₂ from ?_]
    · infer_instance
    · apply Subgroup.map_subtype_inj.mp
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hB₂C, hmapC₂]
  have : IsSimpleGroup ↥B₁ := hB₁.2.1
  have hB₁comp : B₁ ∈ CFSG.Quasithin.cComp C₁ :=
    CFSG.Quasithin.RonanD33.mem_cComp_of_isQuasisimple_of_isSubnormal
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hB₁.2.2.1).1
      (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hB₁C hB₁sub)
  have : IsSimpleGroup ↥B₂ := hB₂.2.1
  have hB₂comp : B₂ ∈ CFSG.Quasithin.cComp C₂ :=
    CFSG.Quasithin.RonanD33.mem_cComp_of_isQuasisimple_of_isSubnormal
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hB₂.2.2.1).1
      (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hB₂C hB₂sub)
  have hB₁_lfam : B₁ ∈ CFSG.Quasithin.lFamily (P : Subgroup X) :=
    CFSG.Quasithin.cComp_subset_lFamily hPleC₁ hB₁comp
  have hB₂_lfam : B₂ ∈ CFSG.Quasithin.lFamily (P : Subgroup X) :=
    CFSG.Quasithin.cComp_subset_lFamily hPleC₂ hB₂comp
  have hBne : B₁ ≠ B₂ := by
    intro hBB
    have hsq1 : t₁ * t₁ = 1 := by
      have h := pow_orderOf_eq_one t₁
      rw [ht₁] at h
      simpa [pow_two] using h
    have hsq2 : t₂ * t₂ = 1 := by
      have h := pow_orderOf_eq_one t₂
      rw [ht₂] at h
      simpa [pow_two] using h
    have hcomm : Commute t₁ t₂ :=
      (commute_iff_eq t₁ t₂).mpr (by simpa using hPab.is_comm.comm ⟨t₁, ht₁P⟩ ⟨t₂, ht₂P⟩)
    have ht₁ne : t₁ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht₁
      norm_num at ht₁
    have ht₂ne : t₂ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht₂
      norm_num at ht₂
    let V : Subgroup X :=
      CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions t₁ t₂ hsq1 hsq2 hcomm
    have hVcard : Nat.card V = 4 :=
      (CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
        t₁ t₂ hsq1 hsq2 ht₁ne ht₂ne hne12 hcomm).card_four
    have ht₁CB : t₁ ∈ Subgroup.centralizer (B₁ : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hB₁C hb)
    have ht₂CB : t₂ ∈ Subgroup.centralizer (B₁ : Set X) := by
      have h2 : t₂ ∈ Subgroup.centralizer (B₂ : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mp (hB₂C hb)
      rw [hBB]
      exact h2
    have hVleC : V ≤ Subgroup.centralizer (B₁ : Set X) := by
      intro x hx
      change x ∈ CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions
        t₁ t₂ hsq1 hsq2 hcomm at hx
      simp only [CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (Subgroup.centralizer (B₁ : Set X)).mul_mem ht₁CB ht₂CB
      · exact ht₁CB
      · exact ht₂CB
      · exact Subgroup.one_mem _
    have : IsSimpleGroup ↥B₁ := hB₁.2.1
    have hcenterB : Subgroup.center ↥B₁ = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥B₁) with h | h
      · exact h
      · exfalso
        let : IsMulCommutative ↥B₁ :=
          IsMulCommutative.mk ⟨fun a b => by
            have ha : a ∈ Subgroup.center ↥B₁ := by rw [h]; exact Subgroup.mem_top a
            exact (Subgroup.mem_center_iff.mp ha b).symm⟩
        have hprime : (Nat.card ↥B₁).Prime :=
          (Group.is_simple_iff_prime_card (α := ↥B₁)).mp hB₁.2.1
        rw [hB₁.1] at hprime
        norm_num at hprime
    have hdisj : Disjoint B₁ V := by
      rw [disjoint_iff]
      apply le_bot_iff.mp
      intro x hx
      have hxB : x ∈ B₁ := hx.1
      have hxC : x ∈ Subgroup.centralizer (B₁ : Set X) := hVleC hx.2
      have hxcenter : (⟨x, hxB⟩ : ↥B₁) ∈ Subgroup.center ↥B₁ := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hxC (y : X) y.2
      rw [hcenterB] at hxcenter
      have hx1 : (⟨x, hxB⟩ : ↥B₁) = 1 := Subgroup.mem_bot.mp hxcenter
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx1)
    have hVleN : V ≤ Subgroup.normalizer (B₁ : Set X) :=
      hVleC.trans (Subgroup.centralizer_le_normalizer (B₁ : Set X))
    have hcard_sup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      B₁ V hVleN hdisj
    have h16 : 16 ∣ Nat.card (B₁ ⊔ V : Subgroup X) := by
      rw [hcard_sup, hB₁.1, hVcard]
      norm_num
    have h16X : 16 ∣ Nat.card X :=
      h16.trans (Subgroup.card_subgroup_dvd_card (B₁ ⊔ V))
    rw [hcardX] at h16X
    norm_num at h16X
  have hsup : B₁ ⊔ B₂ = ⊤ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.KIV.sup_eq_top_J1 hX hPsyl
      hB₁_lfam hB₂_lfam hB₁.2.2.2 hB₂.2.2.2 hBne
  refine ⟨{B₁, B₂}, ⟨B₁, by simp⟩, ?_, ?_⟩
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact ⟨hB₁.2.2.2, hB₁inv⟩
    · exact ⟨hB₂.2.2.2, hB₂inv⟩
  · rw [Finset.iSup_insert, Finset.iSup_singleton]
    exact hsup


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
