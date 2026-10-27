module

public import CFSG.RankThree.GF2n.Tim81.Sec5.I6Planes
public import CFSG.RankThree.GF2n.Tim81.Sec5.Stmts
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec41List
public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbEpsilon
public import CFSG.RankThree.GF2n.Tim78S412Reduce

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78 CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

namespace Sec45Shape

theorem conj_Pc_conj_eq_iff (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {p : G}
    (hp : p ∈ Pc M V) :
    conjSubgroup p (conjSubgroup h₀ V) = conjSubgroup h₀ V ↔ p ∈ kOf V H := by
  classical
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hS.Pc_le hS.hH
  have hVyV : conjSubgroup y V ≠ V := by
    intro hEq
    have hh₀M : h₀ ∈ M :=
      h.toHyp.normalizer_eq ▸ conjSubgroup_eq_self_iff.mp (hVy.trans hEq)
    have hle : H ≤ M := by
      rw [hS.hH]
      exact sup_le h.toHyp.Pc_le_M (conjSubgroup_le_of_le_of_mem h.toHyp.Pc_le_M hh₀M)
    exact hS.not_le hle
  constructor
  · intro hEq
    have hEq' : conjSubgroup p (conjSubgroup y V) = conjSubgroup y V := by
      rwa [hVy] at hEq
    have hpN : p ∈ Subgroup.normalizer (conjSubgroup y V : Set G) :=
      conjSubgroup_eq_self_iff.mp hEq'
    have hpMy : p ∈ conjSubgroup y M := by
      rw [normalizer_conjSubgroup, h.toHyp.normalizer_eq] at hpN
      exact hpN
    have hpNPy : p ∈ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) := by
      rw [normalizer_conjSubgroup]
      exact (Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom)
        h.toHyp.le_normalizer_Pc) hpMy
    obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
    letI := hField
    letI := hFintype
    letI := hCharP
    have hpimg : piK V H ⟨p, hS.Pc_le hp⟩ ∈ imgK V H (Pc M V) :=
      Subgroup.mem_map.mpr
        ⟨⟨p, hS.Pc_le hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    have hNimg : piK V H ⟨p, hS.Pc_le hp⟩ ∈ Subgroup.normalizer
        (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) := by
      rw [mem_normalizer_iff_conjSubgroup_eq,
        ← imgK_conjSubgroup (V := V) (H := H) (S := conjSubgroup y (Pc M V))
          (g := p) (hS.Pc_le hp) (conjSubgroup_le_of_le_of_mem hS.Pc_le hyH),
        conjSubgroup_eq_self_iff.mpr hpNPy]
    have hne : imgK V H (conjSubgroup y (Pc M V)) ≠ imgK V H (Pc M V) :=
      (RootHyp.imgK_ne_bot_and_ne_of_sup h hS.Pc_le hHy hS.not_le).2.symm
    have hbot := RootHyp.inf_imgK_normalizer_conj_eq_bot_of_ne h hS.Pc_le hyH hne ψ
    have hmem : piK V H ⟨p, hS.Pc_le hp⟩ ∈ (⊥ : Subgroup (HBar V H)) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hpimg, hNimg⟩
    exact (piK_eq_one_iff _).mp (Subgroup.mem_bot.mp hmem)
  · intro hpK
    have hpC : p ∈ Subgroup.centralizer (conjSubgroup y V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvW : v ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hyH hv
      exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hpK).2 v hvW
    have hpN : p ∈ Subgroup.normalizer (conjSubgroup y V : Set G) :=
      Subgroup.centralizer_le_normalizer _ hpC
    have hconj : conjSubgroup p (conjSubgroup y V) = conjSubgroup y V :=
      conjSubgroup_eq_self_iff.mpr hpN
    simpa [hVy] using hconj

private theorem notMem_borel_of_conjSubgroup_ne
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {y : G} (hy : y ∈ H) (hPy_ne : conjSubgroup y (Pc M V) ≠ Pc M V)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {T : Subgroup SL(2, F)} {c : SL(2, F)} {ybar : HBar V H}
    (hT : T = (imgK V H (Pc M V)).map ψ.toMonoidHom)
    (hybar : ybar = piK V H ⟨y, hy⟩)
    (hcT : conjSubgroup c T = utri F) :
    c * ψ ybar * c⁻¹ ∉ borel F := by
  classical
  intro hb
  have hfix : conjSubgroup (c * ψ ybar * c⁻¹) (utri F) = utri F :=
    mem_normalizer_iff_conjSubgroup_eq.mp (by rwa [normalizer_utri])
  have hcᵢT : T = conjSubgroup c⁻¹ (utri F) := by
    have h := congrArg (conjSubgroup c⁻¹) hcT
    simpa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] using h
  have hUy_c : conjSubgroup (c * ψ ybar * c⁻¹) (utri F) =
      conjSubgroup c (conjSubgroup (ψ ybar) T) := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hcᵢT]
  have hcy' : conjSubgroup (ψ ybar) T = T := by
    have hcy : conjSubgroup c (conjSubgroup (ψ ybar) T) = utri F := by
      rw [← hUy_c, hfix]
    have h := congrArg (conjSubgroup c⁻¹) hcy
    simpa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hcᵢT] using h
  have hUyeq : conjSubgroup ybar (imgK V H (Pc M V)) = imgK V H (Pc M V) := by
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [CGT.Timmesfeld75.map_conjSubgroup_mulEquiv, ← hT]
    exact hcy'
  have himg : imgK V H (conjSubgroup y (Pc M V)) = imgK V H (conjSubgroup 1 (Pc M V)) := by
    rw [conjSubgroup_one, imgK_conjSubgroup hy hS.Pc_le, ← hybar]
    exact hUyeq
  have hPyeq : conjSubgroup y (Pc M V) = Pc M V := by
    simpa [conjSubgroup_one] using
      RootHyp.conjSubgroup_eq_of_imgK_conjSubgroup_eq h hS.Pc_le
        hy H.one_mem himg
  exact hPy_ne hPyeq

private theorem exists_Pc_imgK_eq_of_bruhat
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y y₀ : G}
    (hy : y ∈ H) (hy₀ : y₀ ∈ H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {T T' : Subgroup SL(2, F)} {c : SL(2, F)} {ybar : HBar V H}
    (hT : T = (imgK V H (Pc M V)).map ψ.toMonoidHom)
    (hT' : T' = (imgK V H (conjSubgroup y₀ (Pc M V))).map ψ.toMonoidHom)
    (hybar : ybar = piK V H ⟨y, hy⟩) (hcT : conjSubgroup c T = utri F)
    (hcT' : conjSubgroup c T' = ltri F) (hg' : c * ψ ybar * c⁻¹ ∉ borel F) :
    ∃ p ∈ Pc M V, imgK V H (conjSubgroup y (Pc M V)) =
      imgK V H (conjSubgroup (p * y₀) (Pc M V)) := by
  classical
  set U : Subgroup (HBar V H) := imgK V H (Pc M V) with hUdef
  set U' : Subgroup (HBar V H) := imgK V H (conjSubgroup y₀ (Pc M V)) with hU'def
  set g' : SL(2, F) := c * ψ ybar * c⁻¹ with hg'def
  have hcᵢT : T = conjSubgroup c⁻¹ (utri F) := by
    have h := congrArg (conjSubgroup c⁻¹) hcT
    simpa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] using h
  have hUy_c : conjSubgroup g' (utri F) =
      conjSubgroup c (conjSubgroup (ψ ybar) T) := by
    rw [hg'def, ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hcᵢT]
  have hg'' : g' ∉ borel F := hg'
  obtain ⟨u, hu, hueq⟩ :=
    exists_mem_utri_conj_eq (g := wElt) (g' := g') wElt_not_mem_borel hg''
  set s : SL(2, F) := c⁻¹ * u * c with hsdef
  have hsT : s ∈ T := by
    rw [hcᵢT, mem_conjSubgroup, hsdef]
    rwa [show c⁻¹⁻¹ * (c⁻¹ * u * c) * c⁻¹ = u by group]
  set pbar : HBar V H := ψ.symm s with hpbardef
  have hpbarU : pbar ∈ U :=
    (mem_map_mulEquiv_iff ψ).mp (by simpa [pbar, hT] using hsT)
  have hconj : conjSubgroup s T' = conjSubgroup (ψ ybar) T := by
    rw [hsdef, ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hcT',
      ← CGT.Timmesfeld75.conjSubgroup_wElt_utri, ← hueq, hUy_c]
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hpbar_img : pbar ∈ imgK V H (Pc M V) := by rwa [hUdef] at hpbarU
  obtain ⟨pH, hpP, hpPi⟩ := mem_imgK_iff.mp hpbar_img
  set p : G := (pH : G) with hpdef
  have hpPH : (⟨p, hS.Pc_le hpP⟩ : ↥H) = pH := Subtype.ext rfl
  have hpsi_p : ψ pbar = s := ψ.apply_symm_apply s
  have hpbar_eq : piK V H ⟨p, hS.Pc_le hpP⟩ = pbar := by rw [hpPH, hpPi]
  have hconj' : conjSubgroup pbar U' = conjSubgroup ybar U := by
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [CGT.Timmesfeld75.map_conjSubgroup_mulEquiv,
      CGT.Timmesfeld75.map_conjSubgroup_mulEquiv]
    simpa [hpsi_p, hT, hT', hybar] using hconj
  have hT'_eq : imgK V H (conjSubgroup (p * y₀) (Pc M V)) = conjSubgroup pbar U' := by
    rw [show conjSubgroup (p * y₀) (Pc M V) =
      conjSubgroup p (conjSubgroup y₀ (Pc M V))
        from (CGT.Timmesfeld75.conjSubgroup_conjSubgroup p y₀ _).symm,
      imgK_conjSubgroup (hS.Pc_le hpP) (conjSubgroup_le_of_le_of_mem hS.Pc_le hy₀),
      imgK_conjSubgroup hy₀ hS.Pc_le, hU'def, imgK_conjSubgroup hy₀ hS.Pc_le, hpbar_eq]
  refine ⟨p, hpP, ?_⟩
  rw [imgK_conjSubgroup hy hS.Pc_le, ← hybar, hT'_eq]
  exact hconj'.symm

private theorem exists_Pc_imgK_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {y y₀ : G} (hy : y ∈ H) (hy₀ : y₀ ∈ H)
    (hPy₀ : conjSubgroup y₀ (Pc M V) = conjSubgroup h₀ (Pc M V))
    (hPy_ne : conjSubgroup y (Pc M V) ≠ Pc M V) :
    ∃ p ∈ Pc M V, imgK V H (conjSubgroup y (Pc M V)) =
      imgK V H (conjSubgroup (p * y₀) (Pc M V)) := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  set U : Subgroup (HBar V H) := imgK V H (Pc M V) with hUdef
  set U' : Subgroup (HBar V H) := imgK V H (conjSubgroup y₀ (Pc M V)) with hU'def
  set T : Subgroup SL(2, F) := U.map ψ.toMonoidHom with hTdef
  set T' : Subgroup SL(2, F) := U'.map ψ.toMonoidHom with hT'def
  have hU'eq : U' = imgK V H (conjSubgroup h₀ (Pc M V)) := by rw [hU'def, hPy₀]
  have hne : U ≠ U' := by
    rw [hU'eq]
    exact (RootHyp.imgK_ne_bot_and_ne_of_sup h hS.Pc_le hS.hH hS.not_le).2
  obtain ⟨-, hcard, a, b, hUa, hUb, hneab⟩ :=
    RootHyp.imgK_map_sl2 h hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  have hTmap : T = (imgK V H (Pc M V)).map ψ.toMonoidHom := by
    simpa [hTdef, hUdef]
  have hT'map : T' =
      (imgK V H (conjSubgroup y₀ (Pc M V))).map ψ.toMonoidHom := by
    simpa [hT'def, hU'def]
  have hT : T = conjSubgroup a (utri F) := by
    simpa [hTdef, hUdef] using hUa
  have hT' : T' = conjSubgroup b (utri F) := by
    simpa [hT'def, hU'def, hPy₀] using hUb
  obtain ⟨c, hca, hcb⟩ := exists_conj_pair_normal_form hneab
  have hcT : conjSubgroup c T = utri F := by
    rw [hT, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hca
  have hcT' : conjSubgroup c T' = ltri F := by
    rw [hT', CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hcb
  set ybar : HBar V H := piK V H ⟨y, hy⟩ with hybardef
  have hg' : c * ψ ybar * c⁻¹ ∉ borel F :=
    notMem_borel_of_conjSubgroup_ne h hS hy hPy_ne ψ hTmap hybardef hcT
  exact exists_Pc_imgK_eq_of_bruhat h hS hy hy₀ ψ hTmap hT'map hybardef hcT hcT' hg'

theorem exists_Pc_conj_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    ∃ p ∈ Pc M V, conjSubgroup y V = conjSubgroup p (conjSubgroup h₀ V) := by
  classical
  obtain ⟨y₀, hy₀H, hPy₀, hVy₀, hHy₀⟩ := h.exists_mem_conj_eq_of_eq_sup hS.Pc_le hS.hH
  have hPy_ne : conjSubgroup y (Pc M V) ≠ Pc M V := by
    intro hEq
    have hcent := congrArg (fun S : Subgroup G => Subgroup.centralizer (S : Set G)) hEq
    have h1 : Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G) =
        conjSubgroup y V := by
      rw [centralizer_conjSubgroup_eq, h.toHyp.centralizer_Pc]
    have h2 : Subgroup.centralizer (Pc M V : Set G) = V := h.toHyp.centralizer_Pc
    rw [h1, h2] at hcent
    exact hyV hcent
  obtain ⟨p, hpP, himg⟩ := exists_Pc_imgK_eq h hS hy hy₀H hPy₀.symm hPy_ne
  have hPeq : conjSubgroup y (Pc M V) = conjSubgroup (p * y₀) (Pc M V) :=
    RootHyp.conjSubgroup_eq_of_imgK_conjSubgroup_eq h hS.Pc_le
      hy (H.mul_mem (hS.Pc_le hpP) hy₀H) himg
  have hC : Subgroup.centralizer (Pc M V : Set G) = V := h.toHyp.centralizer_Pc
  have hVeq : conjSubgroup y V = conjSubgroup (p * y₀) V := by
    calc conjSubgroup y V = conjSubgroup y (Subgroup.centralizer (Pc M V : Set G)) := by
          rw [hC]
      _ = Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G) := by
          rw [centralizer_conjSubgroup_eq]
      _ = Subgroup.centralizer (conjSubgroup (p * y₀) (Pc M V) : Set G) := by rw [hPeq]
      _ = conjSubgroup (p * y₀) (Subgroup.centralizer (Pc M V : Set G)) :=
          centralizer_conjSubgroup_eq (p * y₀) (Pc M V)
      _ = conjSubgroup (p * y₀) V := by rw [hC]
  refine ⟨p, hpP, ?_⟩
  calc conjSubgroup y V = conjSubgroup (p * y₀) V := hVeq
    _ = conjSubgroup p (conjSubgroup y₀ V) :=
        (CGT.Timmesfeld75.conjSubgroup_conjSubgroup p y₀ V).symm
    _ = conjSubgroup p (conjSubgroup h₀ V) := by rw [hVy₀]

private theorem commutator_mem_inf_xOf
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V)
    {p : G} (hp : p ∈ Pc M V) :
    ⁅p, v⁆ ∈ Pc M V ⊓ Tim79a.xOf V H := by
  have hmem : ⁅p, v⁆ ∈ ⁅Pc M V, conjSubgroup y V⁆ :=
    Subgroup.commutator_mem_commutator hp hv
  have hEq : ⁅Pc M V, conjSubgroup y V⁆ = Pc M V ⊓ Tim79a.xOf V H :=
    Sec45Shape.commutator_Pc_conj_eq h hS hy hyV
  rwa [hEq] at hmem

private noncomputable def commutatorQuotHom
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V)
    [hN : (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)).Normal] :
    ↥(Pc M V) →*
      (↥(Pc M V ⊓ Tim79a.xOf V H) ⧸ (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H))) :=
  let P : Subgroup G := Pc M V
  let W : Subgroup G := Tim79a.xOf V H
  let hPP : ⁅P, P⁆ = V := hS.commutator_Pc h
  let hVPW : V ≤ P ⊓ W := le_inf h.toHyp.le_Pc (le_xOf_self V H)
  { toFun := fun p => QuotientGroup.mk
      (⟨⁅(p : G), v⁆, commutator_mem_inf_xOf h hS hy hyV hv p.2⟩ : ↥(P ⊓ W))
    map_one' := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [Subgroup.mem_subgroupOf]
      simpa using commutatorElement_one_left v
    map_mul' := fun p₁ p₂ => by
      set a : ↥(P ⊓ W) := ⟨⁅(p₁ : G), v⁆, commutator_mem_inf_xOf h hS hy hyV hv p₁.2⟩
        with ha
      set b : ↥(P ⊓ W) := ⟨⁅(p₂ : G), v⁆, commutator_mem_inf_xOf h hS hy hyV hv p₂.2⟩
        with hb
      have hcV : ⁅(p₁ : G), (b : G)⁆ ∈ V := by
        have hmem : ⁅(p₁ : G), (b : G)⁆ ∈ ⁅P, P⁆ :=
          Subgroup.commutator_mem_commutator p₁.2 (Subgroup.mem_inf.mp b.2).1
        rwa [hPP] at hmem
      set c : ↥(P ⊓ W) := ⟨⁅(p₁ : G), (b : G)⁆, hVPW hcV⟩ with hc
      have hx : (⟨⁅((p₁ * p₂ : ↥P) : G), v⁆,
          commutator_mem_inf_xOf h hS hy hyV hv (p₁ * p₂).2⟩ : ↥(P ⊓ W)) = c * b * a := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        rw [commutatorElement_mul_left_eq_conj_mul,
          show (p₁ : G) * (b : G) * (p₁ : G)⁻¹ = ⁅(p₁ : G), (b : G)⁆ * (b : G) by
            rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]]
      change QuotientGroup.mk (⟨⁅((p₁ * p₂ : ↥P) : G), v⁆,
        commutator_mem_inf_xOf h hS hy hyV hv (p₁ * p₂).2⟩ : ↥(P ⊓ W)) =
        QuotientGroup.mk a * QuotientGroup.mk b
      rw [hx]
      simp only [QuotientGroup.mk_mul]
      have hc1 : (QuotientGroup.mk c : (↥(P ⊓ W) ⧸ (V.subgroupOf (P ⊓ W)))) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcV)
      rw [hc1, one_mul]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      apply QuotientGroup.eq_iff_div_mem.mpr
      rw [Subgroup.mem_subgroupOf]
      have hba : ⁅(b : G), (a : G)⁆ ∈ V := by
        have hmem : ⁅(b : G), (a : G)⁆ ∈ ⁅P, P⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp b.2).1
            (Subgroup.mem_inf.mp a.2).1
        rwa [hPP] at hmem
      simpa [div_eq_mul_inv, commutatorElement_def, mul_assoc] using hba }

private theorem commutatorQuotHom_apply
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V)
    [hN : (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)).Normal] (p : ↥(Pc M V)) :
    commutatorQuotHom h hS hy hyV hv p =
      QuotientGroup.mk (⟨⁅(p : G), v⁆,
        commutator_mem_inf_xOf h hS hy hyV hv p.2⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) := rfl

private theorem commutatorQuotHom_ker
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V)
    (hv1 : v ≠ 1)
    [hN : (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)).Normal] :
    (commutatorQuotHom h hS hy hyV hv).ker =
      (Pc M V ⊓ kOf V H).subgroupOf (Pc M V) := by
  ext p
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hp
    have hmem : (⟨⁅(p : G), v⁆,
        commutator_mem_inf_xOf h hS hy hyV hv p.2⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) ∈
        V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H) := (QuotientGroup.eq_one_iff _).mp hp
    exact Subgroup.mem_inf.mpr ⟨p.2,
      mem_kOf_of_commutator_mem h hS hy hyV hv hv1 p.2 (Subgroup.mem_subgroupOf.mp hmem)⟩
  · intro hpK
    have hvW : v ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy hv
    have hcomm1 : ⁅(p : G), v⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp
          (mem_kOf_iff.mp (Subgroup.mem_inf.mp hpK).2).2 v hvW).symm)
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by
      show ⁅(p : G), v⁆ ∈ V
      rw [hcomm1]
      exact V.one_mem))

private theorem commutatorQuotHom_range_top
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V)
    (hv1 : v ≠ 1)
    [hN : (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)).Normal] :
    (commutatorQuotHom h hS hy hyV hv).range = ⊤ := by
  let φ := commutatorQuotHom h hS hy hyV hv (hN := hN)
  have hrange_card : Nat.card ↥φ.range = Nat.card V ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [commutatorQuotHom_ker h hS hy hyV hv hv1 (hN := hN)] at h1
    have hcardker : Nat.card ↥((Pc M V ⊓ kOf V H).subgroupOf (Pc M V)) =
        Nat.card ↥(Pc M V ⊓ kOf V H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hcardker] at h1
    have h2 : Nat.card ↥(Pc M V ⊓ kOf V H) * Nat.card V ^ 2 = Nat.card ↥(Pc M V) :=
      hS.card_Pc_inf_kOf h
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(Pc M V ⊓ kOf V H))) h1
  have hQcard : Nat.card (↥(Pc M V ⊓ Tim79a.xOf V H) ⧸
      (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H))) = Nat.card V ^ 2 := by
    have hVPW : V ≤ Pc M V ⊓ Tim79a.xOf V H :=
      le_inf h.toHyp.le_Pc (le_xOf_self V H)
    have hVcard : Nat.card ↥(V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVPW).toEquiv
    rw [show Nat.card (↥(Pc M V ⊓ Tim79a.xOf V H) ⧸
        (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H))) =
        (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)).index from
        (Subgroup.index_eq_card _).symm,
      Subgroup.index_eq_card_div, hVcard, hS.card_inf_Pc_xOf h]
    rw [show Nat.card V ^ 3 = Nat.card V ^ 2 * Nat.card V by ring,
      Nat.mul_div_cancel _ (Nat.card_pos (α := ↥V))]
  exact Subgroup.eq_top_of_card_eq (H := φ.range) (by rw [hrange_card, hQcard])

theorem exists_commutator_mul_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {y v : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) (hv : v ∈ conjSubgroup y V)
    (hv1 : v ≠ 1) {w : G} (hw : w ∈ Pc M V ⊓ Tim79a.xOf V H) :
    ∃ p ∈ Pc M V, ∃ z ∈ V, w = ⁅p, v⁆ * z := by
  classical
  have hVP : V ≤ Pc M V := h.toHyp.le_Pc
  have hVW : V ≤ Tim79a.xOf V H := le_xOf_self V H
  have hVPW : V ≤ Pc M V ⊓ Tim79a.xOf V H := le_inf hVP hVW
  have hPW_M : Pc M V ⊓ Tim79a.xOf V H ≤ M :=
    (inf_le_left.trans h.toHyp.Pc_le_M)
  haveI hVnorm : (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVPW).mpr
      (hPW_M.trans h.toHyp.le_normalizer)
  let φ : ↥(Pc M V) →*
      (↥(Pc M V ⊓ Tim79a.xOf V H) ⧸ (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H))) :=
    commutatorQuotHom h hS hy hyV hv
  have hrange_top : φ.range = ⊤ :=
    commutatorQuotHom_range_top h hS hy hyV hv hv1
  have hwQ : (QuotientGroup.mk (⟨w, hw⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) :
      (↥(Pc M V ⊓ Tim79a.xOf V H) ⧸ (V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H)))) ∈
      φ.range := by
    rw [hrange_top]
    exact Subgroup.mem_top _
  obtain ⟨p, hp⟩ := hwQ
  have hclass : (⟨⁅(p : G), v⁆,
      commutator_mem_inf_xOf h hS hy hyV hv p.2⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) /
      (⟨w, hw⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) ∈
      V.subgroupOf (Pc M V ⊓ Tim79a.xOf V H) := by
    rw [commutatorQuotHom_apply] at hp
    exact (QuotientGroup.eq_iff_div_mem).mp hp
  set u : G := ⁅(p : G), v⁆ * w⁻¹ with hu
  have hval : (((⟨⁅(p : G), v⁆,
      commutator_mem_inf_xOf h hS hy hyV hv p.2⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) /
      (⟨w, hw⟩ : ↥(Pc M V ⊓ Tim79a.xOf V H)) : ↥(Pc M V ⊓ Tim79a.xOf V H)) : G) = u := by
    simp [u, div_eq_mul_inv]
  have huV : u ∈ V := by
    rw [← hval]
    exact Subgroup.mem_subgroupOf.mp hclass
  have hzV : u⁻¹ ∈ V := V.inv_mem huV
  have hzu : u⁻¹ * ⁅(p : G), v⁆ = w := by
    rw [hu]
    group
  have hzC : u⁻¹ ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [h.toHyp.centralizer_Pc]
    exact hzV
  have hcommz : u⁻¹ * ⁅(p : G), v⁆ = ⁅(p : G), v⁆ * u⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp hzC _ (commutator_mem_inf_xOf h hS hy hyV hv p.2).1).symm
  exact ⟨p, p.2, u⁻¹, hzV, by rw [← hcommz, hzu]⟩

private theorem inf_conj_Pc_eq_bot_of_mem (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {y : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V) :
    conjSubgroup y V ⊓ Pc M V = ⊥ := by
  have hUyK : conjSubgroup y V ≤ kOf V H :=
    RootHyp.conjSubgroup_le_kOf_of_mem h hS.Pc_le hS.le_pCore hy
  have hUyM : conjSubgroup y V ≤ M := hUyK.trans (hS.kOf_le_M h)
  rcases h.toHyp.conj_le_Pc_or_inf_eq_bot h.rootType hUyM with hle | hbot
  · exact absurd (h.weaklyClosed_P.2 y hle) hyV
  · refine le_antisymm ?_ bot_le
    intro x hx
    have hxQ : x ∈ conjSubgroup y V ⊓ inSubgroup (pCore 2) M :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1⟩
    rw [hbot] at hxQ
    exact Subgroup.mem_bot.mp hxQ

private theorem exists_mem_sup_data
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y d : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hd : d ∈ V ⊔ conjSubgroup y V) (hdD : d ∈ Tim78.classD V)
    (hdV : d ∉ V) (hdU : d ∉ conjSubgroup y V) :
    ∃ v ∈ V, ∃ u ∈ conjSubgroup y V, ∃ p ∈ Pc M V, ∃ u' ∈ conjSubgroup y V,
      v ≠ 1 ∧ u ≠ 1 ∧ v * u = d ∧ p * u' * p⁻¹ = d := by
  classical
  set W : Subgroup G := Tim79a.xOf V H with hW
  have hVW : V ≤ W := by rw [hW]; exact le_xOf_self V H
  have hUyW : conjSubgroup y V ≤ W := by
    rw [hW]; exact conjSubgroup_le_xOf_of_mem hy
  have hWcomm : ∀ a ∈ V, ∀ b ∈ conjSubgroup y V, a * b = b * a := by
    intro a ha b hb
    have hcomm : IsMulCommutative ↥W := (hS.isElemAbelian h).1
    exact congrArg Subtype.val
      (hcomm.is_comm.comm (⟨a, hVW ha⟩ : ↥W) ⟨b, hUyW hb⟩)
  obtain ⟨v, hvV, u, huU, hvu⟩ : ∃ v ∈ V, ∃ u ∈ conjSubgroup y V, v * u = d :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hWcomm hd
  have hv1 : v ≠ 1 := by
    intro h1
    exact hdU (by rwa [← hvu, h1, one_mul])
  have hu1 : u ≠ 1 := by
    intro h1
    exact hdV (by rwa [← hvu, h1, mul_one])
  have hdW : d ∈ W := hvu ▸ W.mul_mem (hVW hvV) (hUyW huU)
  obtain ⟨z, hzH, hdz⟩ := exists_mem_conj_of_mem_classD h hS hdW hdD
  have hzV : conjSubgroup z V ≠ V := by
    intro hz_eq
    exact hdV (hz_eq ▸ hdz)
  obtain ⟨p₁, hp₁P, hp₁⟩ := exists_Pc_conj_eq h hS hzH hzV
  obtain ⟨p₂, hp₂P, hp₂⟩ := exists_Pc_conj_eq h hS hy hyV
  set p : G := p₁ * p₂⁻¹ with hp
  have hpP : p ∈ Pc M V := (Pc M V).mul_mem hp₁P ((Pc M V).inv_mem hp₂P)
  have hpz : conjSubgroup p (conjSubgroup y V) = conjSubgroup z V := by
    calc conjSubgroup p (conjSubgroup y V)
        = conjSubgroup p (conjSubgroup p₂ (conjSubgroup h₀ V)) := by rw [hp₂]
      _ = conjSubgroup (p * p₂) (conjSubgroup h₀ V) :=
          CGT.Timmesfeld75.conjSubgroup_conjSubgroup p p₂ _
      _ = conjSubgroup p₁ (conjSubgroup h₀ V) := by
          rw [hp]
          congr 1
          group
      _ = conjSubgroup z V := hp₁.symm
  obtain ⟨u', hu'U, hdu'⟩ := Subgroup.mem_map.mp (hpz ▸ hdz)
  have hdu'' : p * u' * p⁻¹ = d := by
    rw [← MulAut.conj_apply]
    exact hdu'
  exact ⟨v, hvV, u, huU, p, hpP, u', hu'U, hv1, hu1, hvu, hdu''⟩

private theorem eq_one_of_mem_sup_data
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y v u p u' d : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hvV : v ∈ V) (huU : u ∈ conjSubgroup y V)
    (hpP : p ∈ Pc M V) (hu'U : u' ∈ conjSubgroup y V)
    (hv1 : v ≠ 1) (hu1 : u ≠ 1)
    (hvu : v * u = d) (hpu' : p * u' * p⁻¹ = d) : False := by
  have hEq : p * u' * p⁻¹ = v * u := by rw [hpu', hvu]
  have hcomm_eq : ⁅p, u'⁆ = v * (u * u'⁻¹) := by
    rw [commutatorElement_def, hEq]
    group
  have hcommP : ⁅p, u'⁆ ∈ Pc M V := by
    have hmem : ⁅p, u'⁆ ∈ ⁅Pc M V, conjSubgroup y V⁆ :=
      Subgroup.commutator_mem_commutator hpP hu'U
    rw [Sec45Shape.commutator_Pc_conj_eq h hS hy hyV] at hmem
    exact (Subgroup.mem_inf.mp hmem).1
  have huu'P : u * u'⁻¹ ∈ Pc M V := by
    have h1 : v⁻¹ * ⁅p, u'⁆ ∈ Pc M V :=
      (Pc M V).mul_mem (h.toHyp.le_Pc (V.inv_mem hvV)) hcommP
    rw [hcomm_eq] at h1
    simpa [mul_assoc] using h1
  have huu'bot : u * u'⁻¹ ∈ (⊥ : Subgroup G) := by
    have hmem : u * u'⁻¹ ∈ conjSubgroup y V ⊓ Pc M V :=
      Subgroup.mem_inf.mpr ⟨(conjSubgroup y V).mul_mem huU ((conjSubgroup y V).inv_mem hu'U),
        huu'P⟩
    rwa [inf_conj_Pc_eq_bot_of_mem h hS hy hyV] at hmem
  have huu'1 : u * u'⁻¹ = 1 := Subgroup.mem_bot.mp huu'bot
  have hu_eq : u = u' := by
    calc u = (u * u'⁻¹) * u' := by group
      _ = u' := by rw [huu'1, one_mul]
  have hcommv : ⁅p, u⁆ = v := by
    rw [← hu_eq] at hcomm_eq
    simpa using hcomm_eq
  have hpK : p ∈ kOf V H :=
    mem_kOf_of_commutator_mem h hS hy hyV huU hu1 hpP (by rw [hcommv]; exact hvV)
  have huW : u ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hy huU
  have hcomm1 : ⁅p, u⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hpK).2 u huW).symm)
  rw [hcommv] at hcomm1
  exact hv1 hcomm1

theorem mem_or_mem_of_mem_sup (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y d : G}
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hd : d ∈ V ⊔ conjSubgroup y V) (hdD : d ∈ Tim78.classD V) :
    d ∈ V ∨ d ∈ conjSubgroup y V := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hdV, hdU⟩ := hcon
  obtain ⟨v, hvV, u, huU, p, hpP, u', hu'U, hv1, hu1, hvu, hpu'⟩ :=
    exists_mem_sup_data h hS hy hyV hd hdD hdV hdU
  exact eq_one_of_mem_sup_data h hS hy hyV hvV huU hpP hu'U hv1 hu1 hvu hpu'

private theorem commutator_eq_mul_mod_V (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x u p : G} (hup : x = u * p)
    (huW : u ∈ Tim79a.xOf V H) (hpP : p ∈ Pc M V) :
    ∀ q ∈ Pc M V, ∃ z ∈ V, ⁅q, x⁆ = ⁅q, u⁆ * z := by
  intro q hq
  have hqp : ⁅q, p⁆ ∈ V := by
    have hmem := Subgroup.commutator_mem_commutator hq hpP
    rwa [hS.commutator_Pc h] at hmem
  have hucomm : ⁅q, p⁆ * u = u * ⁅q, p⁆ := by
    have hVcomm : V ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
      have hE := hS.isElemAbelian h
      exact fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1
            (le_xOf_self V H hz)) w hw
    exact (Subgroup.mem_centralizer_iff.mp (hVcomm hqp) u huW).symm
  refine ⟨⁅q, p⁆, hqp, ?_⟩
  rw [hup, commutatorElement_mul_right_eq_mul_conj]
  have hconj : u * ⁅q, p⁆ * u⁻¹ = ⁅q, p⁆ := by
    rw [← hucomm]
    group
  calc ⁅q, u⁆ * u * ⁅q, p⁆ * u⁻¹ = ⁅q, u⁆ * (u * ⁅q, p⁆ * u⁻¹) := by group
    _ = ⁅q, u⁆ * ⁅q, p⁆ := by rw [hconj]

end Sec45Shape

theorem RootHyp.stmtI5a (h : RootHyp M V) : Sec5.StmtI5a M V := by
  intro H h₀ y hSH hy hyV
  exact Sec45Shape.exists_Pc_conj_eq h hSH hy hyV

theorem RootHyp.stmtI5b (h : RootHyp M V) : Sec5.StmtI5b M V := by
  intro H h₀ y d hSH hy hyV hd hdD
  exact Sec45Shape.mem_or_mem_of_mem_sup h hSH hy hyV hd hdD

private theorem stmt53_le_kOf
    (h : RootHyp M V) {g g' y y' : G}
    (hSU : Sec45Shape M V (hOf M V g) g)
    (hSU' : Sec45Shape M V (hOf M V g') g')
    (hyH : y ∈ hOf M V g) (hVy : conjSubgroup g V = conjSubgroup y V)
    (hyV : conjSubgroup y V ≠ V)
    (hy'H : y' ∈ hOf M V g') (hVy' : conjSubgroup g' V = conjSubgroup y' V)
    (hy'V : conjSubgroup y' V ≠ V)
    (hle : ⁅Pc M V, conjSubgroup g V⁆ ≤
      Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, conjSubgroup g' V⁆ : Set G)) :
    ⁅Pc M V, conjSubgroup g V⁆ ≤ Pc M V ⊓ kOf V (hOf M V g') ∧
      ⁅Pc M V, conjSubgroup g' V⁆ ≤ Pc M V ⊓ kOf V (hOf M V g) := by
  have hC' : Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, conjSubgroup g' V⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V (hOf M V g') := by
    rw [hVy']
    exact hSU'.Pc_inf_centralizer_commutator h hy'H hy'V
  have hC : Pc M V ⊓ Subgroup.centralizer
      ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) =
      Pc M V ⊓ kOf V (hOf M V g) := by
    rw [hVy]
    exact hSU.Pc_inf_centralizer_commutator h hyH hyV
  have hEU' : ⁅Pc M V, conjSubgroup g V⁆ ≤ Pc M V ⊓ kOf V (hOf M V g') := by
    have h1 : ⁅Pc M V, conjSubgroup g V⁆ ≤ Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, conjSubgroup g' V⁆ : Subgroup G) : Set G) := hle
    rwa [hC'] at h1
  have hle_symm : ⁅Pc M V, conjSubgroup g' V⁆ ≤
      Subgroup.centralizer ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hle hb)).2 a ha).symm
  have hEU : ⁅Pc M V, conjSubgroup g' V⁆ ≤ Pc M V ⊓ kOf V (hOf M V g) := by
    have hleP : ⁅Pc M V, conjSubgroup g' V⁆ ≤ Pc M V := by
      rw [hVy', Sec45Shape.commutator_Pc_conj_eq h hSU' hy'H hy'V]
      exact inf_le_left
    have h1 : ⁅Pc M V, conjSubgroup g' V⁆ ≤ Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, conjSubgroup g V⁆ : Subgroup G) : Set G) := le_inf hleP hle_symm
    rwa [hC] at h1
  exact ⟨hEU', hEU⟩

private theorem stmt53_centralizes_commutators
    {g g' y y' : G}
    (hyH : y ∈ hOf M V g) (hVy : conjSubgroup g V = conjSubgroup y V)
    (hy'H : y' ∈ hOf M V g') (hVy' : conjSubgroup g' V = conjSubgroup y' V)
    (hEU' : ⁅Pc M V, conjSubgroup g V⁆ ≤ Pc M V ⊓ kOf V (hOf M V g'))
    (hEU : ⁅Pc M V, conjSubgroup g' V⁆ ≤ Pc M V ⊓ kOf V (hOf M V g)) :
    ⁅⁅Pc M V, conjSubgroup g V⁆, conjSubgroup g' V⁆ = ⊥ ∧
      ⁅⁅Pc M V, conjSubgroup g' V⁆, conjSubgroup g V⁆ = ⊥ := by
  have h2 : ⁅⁅Pc M V, conjSubgroup g V⁆, conjSubgroup g' V⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbW : b ∈ Tim79a.xOf V (hOf M V g') := by
      have hb' : b ∈ conjSubgroup y' V := by rwa [hVy'] at hb
      exact conjSubgroup_le_xOf_of_mem hy'H hb'
    exact Subgroup.mem_centralizer_iff.mp
      (mem_kOf_iff.mp (Subgroup.mem_inf.mp (hEU' ha)).2).2 b hbW
  have h1' : ⁅⁅Pc M V, conjSubgroup g' V⁆, conjSubgroup g V⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbW : b ∈ Tim79a.xOf V (hOf M V g) := by
      have hb' : b ∈ conjSubgroup y V := by rwa [hVy] at hb
      exact conjSubgroup_le_xOf_of_mem hyH hb'
    exact Subgroup.mem_centralizer_iff.mp
      (mem_kOf_iff.mp (Subgroup.mem_inf.mp (hEU ha)).2).2 b hbW
  exact ⟨h2, h1'⟩

private theorem stmt53_centralizes (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hle : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) :
    ⁅⁅Pc M V, U⁆, U'⁆ = ⊥ ∧ ⁅⁅Pc M V, U'⁆, U⁆ = ⊥ := by
  classical
  obtain ⟨g, hUg, hHg⟩ := hU
  subst hUg
  obtain ⟨g', hUg', hHg'⟩ := hU'
  subst hUg'
  have h := hS.toRootHyp
  have hUsig : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hU'sig : conjSubgroup g' V ∈ sigmaSet M V := ⟨g', rfl, hHg'⟩
  have hSU := hS.shape hUsig
  have hSU' := hS.shape hU'sig
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU.Pc_le hSU.hH
  obtain ⟨y', hy'H, -, hVy', -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU'.Pc_le hSU'.hH
  have hyV : conjSubgroup y V ≠ V :=
    fun hEq => ne_of_mem_sigmaSet h hUsig (hVy.trans hEq)
  have hy'V : conjSubgroup y' V ≠ V :=
    fun hEq => ne_of_mem_sigmaSet h hU'sig (hVy'.trans hEq)
  obtain ⟨hEU', hEU⟩ :=
    stmt53_le_kOf h hSU hSU' hyH hVy hyV hy'H hVy' hy'V hle
  exact stmt53_centralizes_commutators hyH hVy hy'H hVy' hEU' hEU

private theorem stmt53_commutator_le_V (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hle : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ Subgroup.centralizer (↑⁅Pc M V, U'⁆ : Set G)) :
    ⁅U, U'⁆ ≤ V := by
  classical
  obtain ⟨g, hUg, hHg⟩ := hU
  subst hUg
  obtain ⟨g', hUg', hHg'⟩ := hU'
  subst hUg'
  have h := hS.toRootHyp
  have hUsig : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hU'sig : conjSubgroup g' V ∈ sigmaSet M V := ⟨g', rfl, hHg'⟩
  have hcen := stmt53_centralizes hS hUsig hU'sig hle
  have h1 : ⁅⁅conjSubgroup g' V, Pc M V⁆, conjSubgroup g V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (conjSubgroup g' V) (Pc M V)]
    exact hcen.2
  have hthree : ⁅⁅conjSubgroup g V, conjSubgroup g' V⁆, Pc M V⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 hcen.1
  have h1' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hthree
  rwa [h.toHyp.centralizer_Pc] at h1'

private theorem stmt53_conj_mem
    (h : RootHyp M V) {y u u' : G}
    (hSU : Sec45Shape M V H h₀)
    (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hVy : conjSubgroup h₀ V = conjSubgroup y V)
    {U : Subgroup G} (hU : U = conjSubgroup h₀ V)
    (hu : u ∈ U) (hu'M : u' ∈ M) (hu1 : u ≠ 1)
    (hcomm_mem : ⁅u', u⁆ ∈ V) (hUVbot : U ⊓ V = ⊥) :
    u' * u * u'⁻¹ ∈ U := by
  have hxUy : u ∈ conjSubgroup y V := by rw [hU, hVy] at hu; exact hu
  have hxeq : u' * u * u'⁻¹ = ⁅u', u⁆ * u := by
    rw [commutatorElement_def]
    group
  have hxVU : u' * u * u'⁻¹ ∈ V ⊔ conjSubgroup y V := by
    rw [hxeq]
    exact Subgroup.mul_mem_sup hcomm_mem hxUy
  have hxD : u' * u * u'⁻¹ ∈ Tim78.classD V := by
    obtain ⟨v₀, hv₀V, huv₀⟩ := Subgroup.mem_map.mp hxUy
    have hv₀1 : v₀ ≠ 1 := by
      intro h1
      apply hu1
      rw [← huv₀, h1]
      simp [MulAut.conj_apply]
    refine ⟨u' * y, v₀, hv₀V, hv₀1, ?_⟩
    rw [← huv₀]
    simp [MulAut.conj_apply]
    group
  have hx : u' * u * u'⁻¹ ∈ V ∨ u' * u * u'⁻¹ ∈ conjSubgroup h₀ V := by
    rcases Sec45Shape.mem_or_mem_of_mem_sup (y := y) (d := u' * u * u'⁻¹)
      h hSU hy hyV hxVU hxD with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rwa [← hVy] at hx)
  rcases hx with hxV | hxU
  · exfalso
    have hVN : u' ∈ Subgroup.normalizer (V : Set G) := h.toHyp.le_normalizer hu'M
    have hVNinv : u'⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hVN
    have huV : u ∈ V := by
      have h := (Subgroup.mem_normalizer_iff.mp hVNinv (u' * u * u'⁻¹)).mp hxV
      simpa [mul_assoc] using h
    exact hu1 (Subgroup.mem_bot.mp (hUVbot ▸ Subgroup.mem_inf.mpr ⟨hu, huV⟩))
  · simpa [hU] using hxU

private theorem stmt53_eq_bot (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hleV : ⁅U, U'⁆ ≤ V) : ⁅U, U'⁆ = ⊥ := by
  classical
  obtain ⟨g, hUg, hHg⟩ := hU
  subst hUg
  have h := hS.toRootHyp
  have hUsig : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hSU := hS.shape hUsig
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU.Pc_le hSU.hH
  have hyV : conjSubgroup y V ≠ V := by
    intro hEq
    exact ne_of_mem_sigmaSet h hUsig (hVy.trans hEq)
  have hUV : conjSubgroup g V ≠ V := ne_of_mem_sigmaSet h hUsig
  have hUVbot : conjSubgroup g V ⊓ V = ⊥ := by
    rw [inf_comm]
    exact inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hUV
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr ?_
  intro u hu u' hu'
  by_cases hu1 : u = 1
  · rw [hu1, commutatorElement_one_left]
    rfl
  have hcomm_mem : ⁅u', u⁆ ∈ V := by
    have hmem : ⁅u', u⁆ ∈ ⁅U', conjSubgroup g V⁆ :=
      Subgroup.commutator_mem_commutator hu' hu
    rw [Subgroup.commutator_comm U' (conjSubgroup g V)] at hmem
    exact hleV hmem
  have hxU := stmt53_conj_mem h hSU hyH hyV hVy (U := conjSubgroup g V) rfl hu
    ((hS.le_M_of_mem_sigmaSet hU').1 hu') hu1 hcomm_mem hUVbot
  have hcommU : ⁅u', u⁆ ∈ conjSubgroup g V := by
    have hxeq : ⁅u', u⁆ = (u' * u * u'⁻¹) * u⁻¹ := by
      simp [commutatorElement_def, mul_assoc]
    rw [hxeq]
    exact (conjSubgroup g V).mul_mem hxU ((conjSubgroup g V).inv_mem hu)
  have hcomm1 : ⁅u', u⁆ = 1 :=
    Subgroup.mem_bot.mp (hUVbot ▸ Subgroup.mem_inf.mpr ⟨hcommU, hcomm_mem⟩)
  rw [Subgroup.mem_bot, ← commutatorElement_inv u' u, hcomm1, inv_one]

theorem Sec5Hyp.stmt53 (hS : Sec5Hyp M V) : Sec5.Stmt53 M V := by
  intro U hU U' hU' hle
  exact stmt53_eq_bot hS hU hU' (stmt53_commutator_le_V hS hU hU' hle)

theorem Sec5Hyp.stmt54 (hS : Sec5Hyp M V) : Sec5.Stmt54 M V := by
  classical
  intro U hU U' hU' hU'V hne
  obtain ⟨g, hUg, hHg⟩ := hU
  subst hUg
  have h := hS.toRootHyp
  have hUsig : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hSU := hS.shape hUsig
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU.Pc_le hSU.hH
  have hyV : conjSubgroup y V ≠ V := by
    intro hEq
    exact ne_of_mem_sigmaSet h hUsig (hVy.trans hEq)
  obtain ⟨k, -, hU'k⟩ := hU'
  obtain ⟨xH, hx1H⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set x : G := (xH : G) with hxdef
  have hx : x ∈ U' ⊓ (conjSubgroup g V ⊔ V) := by simpa [hxdef] using xH.2
  have hx1 : x ≠ 1 := by
    intro h1
    exact hx1H (Subtype.ext h1)
  have hxU' : x ∈ conjSubgroup k V := by
    simpa [hU'k] using (Subgroup.mem_inf.mp hx).1
  have hxUV : x ∈ V ⊔ conjSubgroup g V := by
    have := (Subgroup.mem_inf.mp hx).2
    rwa [sup_comm] at this
  have hxD : x ∈ Tim78.classD V :=
    CFSG.RankThree.GF2n.Tim78.mem_classD_of_mem_conjSubgroup hxU' hx1
  have hxVU : x ∈ V ⊔ conjSubgroup y V := by rwa [hVy] at hxUV
  have hmem := Sec45Shape.mem_or_mem_of_mem_sup (y := y) (d := x) h hSU hyH hyV hxVU hxD
  have hUkV : conjSubgroup k V ≠ V := by
    intro hEq
    exact hU'V (hU'k.trans hEq)
  rcases hmem with hxV | hxU
  · exfalso
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hUkV]
      exact Subgroup.mem_inf.mpr ⟨hxV, hxU'⟩
    exact hx1 (Subgroup.mem_bot.mp hxbot)
  · have hxU'' : x ∈ conjSubgroup g V := by rwa [← hVy] at hxU
    have hEq : conjSubgroup k V = conjSubgroup g V := by
      have hneT : conjSubgroup g V ⊓ conjSubgroup (k * g⁻¹) (conjSubgroup g V) ≠ ⊥ := by
        intro hbot
        have hxT : x ∈ conjSubgroup g V ⊓ conjSubgroup (k * g⁻¹) (conjSubgroup g V) := by
          refine Subgroup.mem_inf.mpr ⟨hxU'', ?_⟩
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
            show k * g⁻¹ * g = k by group]
          exact hxU'
        exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxT))
      have hmain := conjSubgroup_eq_of_isTI (isTI_conjSubgroup h.toHyp.ti g) hneT
      rwa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
        show k * g⁻¹ * g = k by group] at hmain
    exact hU'k.trans hEq

private theorem stmt55_decomp
    (h : RootHyp M V) {g k y : G} (hSU : Sec45Shape M V (hOf M V g) g)
    (hyH : y ∈ hOf M V g)
    (hVy : conjSubgroup g V = conjSubgroup y V)
    (hkM : conjSubgroup k V ≤ M) (hkV : conjSubgroup k V ≠ V)
    {x : G} (hx1 : x ≠ 1)
    (hx : x ∈ conjSubgroup k V ⊓ (conjSubgroup g V ⊔ Pc M V)) :
    ∃ u p : G, u ∈ conjSubgroup g V ∧ p ∈ Pc M V ∧ u * p = x ∧
      u ∈ conjSubgroup y V ∧ u ∈ Tim79a.xOf V (hOf M V g) ∧ u ≠ 1 := by
  have hxU' : x ∈ conjSubgroup k V := (Subgroup.mem_inf.mp hx).1
  have hxUP : x ∈ conjSubgroup g V ⊔ Pc M V := (Subgroup.mem_inf.mp hx).2
  have hUN : conjSubgroup g V ≤ Subgroup.normalizer (Pc M V : Set G) := by
    rw [hVy]
    exact (conjSubgroup_le_xOf_of_mem hyH).trans
      (xOf_le_normalizer_Pc h hSU.Pc_le hSU.le_pCore)
  have hxmem : x ∈ ((conjSubgroup g V ⊔ Pc M V : Subgroup G) : Set G) := hxUP
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup g V) (Pc M V) hUN] at hxmem
  obtain ⟨u, huU, p, hpP, hup⟩ := Set.mem_mul.mp hxmem
  have huUy : u ∈ conjSubgroup y V := by rwa [hVy] at huU
  have huW : u ∈ Tim79a.xOf V (hOf M V g) := conjSubgroup_le_xOf_of_mem hyH huUy
  have hu1 : u ≠ 1 := by
    intro hu1
    have hpU' : p ∈ conjSubgroup k V := by
      rw [← hup, hu1, one_mul] at hxU'
      exact hxU'
    have hxP : x ∈ Pc M V := by rw [← hup, hu1, one_mul]; exact hpP
    rcases h.toHyp.conj_le_Pc_or_inf_eq_bot h.rootType hkM with hle | hbot
    · exact hkV (h.weaklyClosed_P.2 k hle)
    · have hxQ : x ∈ conjSubgroup k V ⊓ inSubgroup (pCore 2) M :=
        Subgroup.mem_inf.mpr ⟨hxU', (Subgroup.mem_inf.mp hxP).1⟩
      rw [hbot] at hxQ
      exact hx1 (Subgroup.mem_bot.mp hxQ)
  exact ⟨u, p, huU, hpP, hup, huUy, huW, hu1⟩

private theorem stmt55_comm_kOf
    (h : RootHyp M V) {g : G} (hSU : Sec45Shape M V (hOf M V g) g)
    {y u p x : G} (hyH : y ∈ hOf M V g)
    (hyV : conjSubgroup y V ≠ V)
    (huUy : u ∈ conjSubgroup y V)
    (hu1 : u ≠ 1) (hpP : p ∈ Pc M V) (hup : u * p = x)
    (hx2 : x * x = 1) (hu2 : u * u = 1) (hpV : p * p ∈ V) :
    ⁅p⁻¹, u⁆ ∈ V ∧ p ∈ kOf V (hOf M V g) := by
  have hcommV : ⁅p⁻¹, u⁆ ∈ V := by
    have hup' : u * p * u = p⁻¹ := by
      have h1 : u * p * u * p = 1 := by
        have := hx2
        rw [← hup] at this
        simpa [mul_assoc] using this
      calc u * p * u = (u * p * u * p) * p⁻¹ := by group
        _ = p⁻¹ := by rw [h1, one_mul]
    have h1 : u * p = p⁻¹ * u := by
      calc u * p = (u * p * u) * u := by rw [mul_assoc, mul_assoc, hu2, mul_one]
        _ = p⁻¹ * u := by rw [hup']
    have hcomm_eq : ⁅p⁻¹, u⁆ = p⁻¹ * p⁻¹ := by
      rw [commutatorElement_def, inv_inv]
      calc p⁻¹ * u * p * u⁻¹ = p⁻¹ * (u * p) * u⁻¹ := by group
        _ = p⁻¹ * (p⁻¹ * u) * u⁻¹ := by rw [h1]
        _ = p⁻¹ * p⁻¹ := by group
    rw [hcomm_eq]
    have hpVinv : p⁻¹ * p⁻¹ ∈ V := by
      have h := V.inv_mem hpV
      simpa [mul_inv_rev] using h
    exact hpVinv
  have hpKinv : p⁻¹ ∈ kOf V (hOf M V g) :=
    Sec45Shape.mem_kOf_of_commutator_mem h hSU hyH hyV huUy hu1
      ((Pc M V).inv_mem hpP) hcommV
  exact ⟨hcommV, by simpa using (kOf V (hOf M V g)).inv_mem hpKinv⟩

private theorem stmt55_hWeq
    (h : RootHyp M V) {g k : G} (hSU : Sec45Shape M V (hOf M V g) g)
    (hSU' : Sec45Shape M V (hOf M V k) k)
    {y y' u p x : G}
    (hyH : y ∈ hOf M V g)
    (hyV : conjSubgroup y V ≠ V)
    (hy'H : y' ∈ hOf M V k) (hVy' : conjSubgroup k V = conjSubgroup y' V)
    (hy'V : conjSubgroup y' V ≠ V)
    (huUy : u ∈ conjSubgroup y V) (huW : u ∈ Tim79a.xOf V (hOf M V g))
    (hpP : p ∈ Pc M V) (hxU' : x ∈ conjSubgroup k V) (hx1 : x ≠ 1)
    (hup : u * p = x) (hu1 : u ≠ 1) :
    Pc M V ⊓ Tim79a.xOf V (hOf M V g) =
      Pc M V ⊓ Tim79a.xOf V (hOf M V k) := by
  have hPU : ⁅Pc M V, conjSubgroup y V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g) :=
    Sec45Shape.commutator_Pc_conj_eq h hSU hyH hyV
  have hPU' : ⁅Pc M V, conjSubgroup y' V⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V k) :=
    Sec45Shape.commutator_Pc_conj_eq h hSU' hy'H hy'V
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨q, hqP, z, hzV, hwq⟩ :=
      Sec45Shape.exists_commutator_mul_eq h hSU hyH hyV huUy hu1 hw
    obtain ⟨z', hz'V, hqx⟩ :=
      Sec45Shape.commutator_eq_mul_mod_V h hSU hup.symm huW hpP q hqP
    have hqX : ⁅q, x⁆ ∈ Pc M V ⊓ Tim79a.xOf V (hOf M V k) := by
      have hmem := Subgroup.commutator_mem_commutator hqP hxU'
      have hEq : ⁅Pc M V, conjSubgroup k V⁆ =
          Pc M V ⊓ Tim79a.xOf V (hOf M V k) := by
        rw [hVy']
        exact hPU'
      rwa [hEq] at hmem
    have hz''V : z'⁻¹ * z ∈ V := V.mul_mem (V.inv_mem hz'V) hzV
    have hw' : w = ⁅q, x⁆ * (z'⁻¹ * z) := by
      rw [hwq]
      calc ⁅q, u⁆ * z = (⁅q, x⁆ * z'⁻¹) * z := by rw [hqx]; group
        _ = ⁅q, x⁆ * (z'⁻¹ * z) := by group
    rw [hw']
    exact Subgroup.mul_mem _ hqX
      (le_inf h.toHyp.le_Pc (le_xOf_self V (hOf M V k)) hz''V)
  · intro w hw
    obtain ⟨q, hqP, z, hzV, hwq⟩ :=
      Sec45Shape.exists_commutator_mul_eq h hSU' hy'H hy'V
        (by rwa [hVy'] at hxU') hx1 hw
    obtain ⟨z', hz'V, hqx⟩ :=
      Sec45Shape.commutator_eq_mul_mod_V h hSU hup.symm huW hpP q hqP
    have hqU : ⁅q, u⁆ ∈ Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
      have hmem := Subgroup.commutator_mem_commutator hqP huUy
      rwa [hPU] at hmem
    have hw' : w = ⁅q, u⁆ * (z' * z) := by
      rw [hwq, hqx]
      group
    rw [hw']
    exact Subgroup.mul_mem _ hqU
      (le_inf h.toHyp.le_Pc (le_xOf_self V (hOf M V g)) (V.mul_mem hz'V hzV))

private theorem stmt55_hKeq
    (h : RootHyp M V) {g k : G} (hSU : Sec45Shape M V (hOf M V g) g)
    (hSU' : Sec45Shape M V (hOf M V k) k)
    {y y' : G}
    (hyH : y ∈ hOf M V g)
    (hyV : conjSubgroup y V ≠ V)
    (hy'H : y' ∈ hOf M V k)
    (hy'V : conjSubgroup y' V ≠ V)
    (hWeq : Pc M V ⊓ Tim79a.xOf V (hOf M V g) =
      Pc M V ⊓ Tim79a.xOf V (hOf M V k)) :
    Pc M V ⊓ kOf V (hOf M V g) = Pc M V ⊓ kOf V (hOf M V k) := by
  have h1 := Sec45Shape.Pc_inf_centralizer_commutator h hSU hyH hyV
  have h2 := Sec45Shape.Pc_inf_centralizer_commutator h hSU' hy'H hy'V
  rw [show ⁅Pc M V, conjSubgroup y V⁆ =
      Pc M V ⊓ Tim79a.xOf V (hOf M V g) from
    Sec45Shape.commutator_Pc_conj_eq h hSU hyH hyV] at h1
  rw [show ⁅Pc M V, conjSubgroup y' V⁆ =
      Pc M V ⊓ Tim79a.xOf V (hOf M V k) from
    Sec45Shape.commutator_Pc_conj_eq h hSU' hy'H hy'V] at h2
  rw [hWeq] at h1
  exact h1.symm.trans h2

private theorem stmt55_p_mem_xOf
    {g k : G} (hSU : Sec45Shape M V (hOf M V g) g)
    {y' x u p : G}
    (hy'H : y' ∈ hOf M V k) (hxU'y : x ∈ conjSubgroup y' V)
    (huW : u ∈ Tim79a.xOf V (hOf M V g))
    (hpP : p ∈ Pc M V) (hpK : p ∈ kOf V (hOf M V g))
    (hKeq : Pc M V ⊓ kOf V (hOf M V g) = Pc M V ⊓ kOf V (hOf M V k))
    (hup : u * p = x) :
    p ∈ Tim79a.xOf V (hOf M V g) ∧ x ∈ Tim79a.xOf V (hOf M V g) := by
  have hxWK : x ∈ Tim79a.xOf V (hOf M V k) := conjSubgroup_le_xOf_of_mem hy'H hxU'y
  have hxC : x ∈ Subgroup.centralizer
      ((Pc M V ⊓ kOf V (hOf M V g) : Subgroup G) : Set G) := by
    rw [hKeq]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp
      (mem_kOf_iff.mp (Subgroup.mem_inf.mp hc).2).2 x hxWK).symm
  have huC : u ∈ Subgroup.centralizer
      ((Pc M V ⊓ kOf V (hOf M V g) : Subgroup G) : Set G) := by
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp
      (mem_kOf_iff.mp (Subgroup.mem_inf.mp hc).2).2 u huW).symm
  have hpC : p ∈ Subgroup.centralizer
      ((Pc M V ⊓ kOf V (hOf M V g) : Subgroup G) : Set G) := by
    have hpeq : p = u⁻¹ * x := by rw [← hup]; group
    rw [hpeq]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem huC) hxC
  have hpZ : p ∈ (Pc M V ⊓ kOf V (hOf M V g)) ⊓
      Subgroup.centralizer ((Pc M V ⊓ kOf V (hOf M V g) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hpP, hpK⟩, hpC⟩
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSU.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hpW : p ∈ Tim79a.xOf V (hOf M V g) := by
    have hcenter := hw.center_PK
    rw [hcenter] at hpZ
    exact (Subgroup.mem_inf.mp hpZ).2
  refine ⟨hpW, ?_⟩
  rw [← hup]
  exact (Tim79a.xOf V (hOf M V g)).mul_mem huW hpW

private theorem stmt55_final
    (h : RootHyp M V) {g k x z r : G}
    (hxU' : x ∈ conjSubgroup k V) (hx1 : x ≠ 1)
    (hdz : x ∈ conjSubgroup z V)
    (hrz : conjSubgroup z V = conjSubgroup r (conjSubgroup g V)) :
    conjSubgroup k V = conjSubgroup r (conjSubgroup g V) := by
  have hxr : x ∈ conjSubgroup r (conjSubgroup g V) := by rw [← hrz]; exact hdz
  by_contra hne'
  have hneT : conjSubgroup ((r * g) * k⁻¹) (conjSubgroup k V) ≠ conjSubgroup k V := by
    intro hEq
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hEq
    rw [show (r * g) * k⁻¹ * k = r * g by group] at hEq
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hEq
    exact hne' hEq.symm
  have hbot := inf_conjSubgroup_eq_bot_of_isTI (isTI_conjSubgroup h.toHyp.ti k) hneT
  have hxint : x ∈ conjSubgroup k V ⊓ conjSubgroup ((r * g) * k⁻¹) (conjSubgroup k V) := by
    refine Subgroup.mem_inf.mpr ⟨hxU', ?_⟩
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show (r * g) * k⁻¹ * k = r * g by group,
      ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hxr
  exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxint))

theorem Sec5Hyp.stmt55 (hS : Sec5Hyp M V) : Sec5.Stmt55 M V := by
  classical
  intro U hU U' hU' hne
  obtain ⟨g, hUg, hHg⟩ := hU
  subst hUg
  obtain ⟨k, hUk, hHk⟩ := hU'
  subst hUk
  have h := hS.toRootHyp
  have hUsig : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hU'sig : conjSubgroup k V ∈ sigmaSet M V := ⟨k, rfl, hHk⟩
  have hSU := hS.shape hUsig
  have hSU' := hS.shape hU'sig
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU.Pc_le hSU.hH
  obtain ⟨y', hy'H, -, hVy', -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU'.Pc_le hSU'.hH
  have hyV : conjSubgroup y V ≠ V :=
    fun hEq => ne_of_mem_sigmaSet h hUsig (hVy.trans hEq)
  have hy'V : conjSubgroup y' V ≠ V :=
    fun hEq => ne_of_mem_sigmaSet h hU'sig (hVy'.trans hEq)
  obtain ⟨xH, hx1H⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set x : G := (xH : G) with hxdef
  have hx : x ∈ conjSubgroup k V ⊓ (conjSubgroup g V ⊔ Pc M V) := by
    simpa [hxdef] using xH.2
  have hx1 : x ≠ 1 := by
    intro h1
    exact hx1H (Subtype.ext h1)
  have hxU' : x ∈ conjSubgroup k V := (Subgroup.mem_inf.mp hx).1
  have hxU'y : x ∈ conjSubgroup y' V := by rwa [hVy'] at hxU'
  have hkM : conjSubgroup k V ≤ M := (hS.le_M_of_mem_sigmaSet hU'sig).1
  have hkV : conjSubgroup k V ≠ V := ne_of_mem_sigmaSet h hU'sig
  obtain ⟨u, p, huU, hpP, hup, huUy, huW, hu1⟩ :=
    stmt55_decomp h hSU hyH hVy hkM hkV hx1 hx
  have hx2 : x * x = 1 :=
    elemAbelian_mul_self
      (CFSG.RankThree.GF2n.Tim78.isElemAbelian_conjSubgroup h.toHyp.elem k) hxU'
  have hu2 : u * u = 1 :=
    elemAbelian_mul_self
      (CFSG.RankThree.GF2n.Tim78.isElemAbelian_conjSubgroup h.toHyp.elem y) huUy
  have hpV : p * p ∈ V := h.mul_self_mem_of_mem_Pc hpP
  obtain ⟨-, hpK⟩ :=
    stmt55_comm_kOf h hSU hyH hyV huUy hu1 hpP hup hx2 hu2 hpV
  have hWeq := stmt55_hWeq h hSU hSU' hyH hyV hy'H hVy' hy'V
    huUy huW hpP hxU' hx1 hup hu1
  have hKeq := stmt55_hKeq h hSU hSU' hyH hyV hy'H hy'V hWeq
  obtain ⟨hpW, hxW⟩ :=
    stmt55_p_mem_xOf hSU hy'H hxU'y huW hpP hpK hKeq hup
  have hxD : x ∈ Tim78.classD V :=
    CFSG.RankThree.GF2n.Tim78.mem_classD_of_mem_conjSubgroup hxU' hx1
  obtain ⟨z, hzH, hdz⟩ := Sec45Shape.exists_mem_conj_of_mem_classD h hSU hxW hxD
  have hxV : x ∉ V := by
    intro hxV
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hkV]
      exact Subgroup.mem_inf.mpr ⟨hxV, hxU'⟩
    exact hx1 (Subgroup.mem_bot.mp hxbot)
  have hzV : conjSubgroup z V ≠ V := fun hz => hxV (hz ▸ hdz)
  obtain ⟨r, hrP, hrz⟩ := Sec45Shape.exists_Pc_conj_eq h hSU hzH hzV
  exact ⟨r, hrP, stmt55_final h hxU' hx1 hdz hrz⟩

theorem Sec5Hyp.stmt55e (hS : Sec5Hyp M V) : Sec5.Stmt55e M V := by
  classical
  intro U hU x hxU hx1 m hm hxP
  obtain ⟨p₀, hp₀P, hxp₀⟩ := hxP
  have h := hS.toRootHyp
  have hU' : conjSubgroup m U ∈ sigmaSet M V := hS.conj_mem_sigmaSet hm hU
  set y : G := m * x * m⁻¹ with hydef
  have hy_eq : y = x * p₀ := hxp₀
  have hyU' : y ∈ conjSubgroup m U := by
    rw [hydef]
    exact Subgroup.mem_map.mpr ⟨x, hxU, rfl⟩
  have hyUP : y ∈ U ⊔ Pc M V := by
    rw [hy_eq]
    exact Subgroup.mul_mem_sup hxU hp₀P
  have hy1 : y ≠ 1 := by
    rw [hydef]
    exact fun h1 => hx1 (by
      have := congrArg (fun z => m⁻¹ * z * m) h1
      simpa [mul_assoc] using this)
  have hne : conjSubgroup m U ⊓ (U ⊔ Pc M V) ≠ ⊥ :=
    fun hbot => hy1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hyU', hyUP⟩))
  obtain ⟨r, hrP, hrU⟩ := Sec5Hyp.stmt55 hS U hU (conjSubgroup m U) hU' hne
  have hyr : y ∈ conjSubgroup r U := by rw [← hrU]; exact hyU'
  obtain ⟨x', hx'U, hx'y⟩ := Subgroup.mem_map.mp hyr
  obtain ⟨g, hUg, hHg⟩ := hU
  have hUsig : conjSubgroup g V ∈ sigmaSet M V := ⟨g, rfl, hHg⟩
  have hSU := hS.shape hUsig
  have hUbot : U ⊓ Pc M V = ⊥ := by
    rw [hUg]; exact RootHyp.conjSubgroup_inf_Pc_eq_bot h hSU.hH hSU.not_le
  obtain ⟨yH, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSU.Pc_le hSU.hH
  have hUN : U ≤ Subgroup.normalizer (Pc M V : Set G) := by
    rw [hUg, hVy]
    exact (conjSubgroup_le_xOf_of_mem hyH).trans
      (xOf_le_normalizer_Pc h hSU.Pc_le hSU.le_pCore)
  have hr₁P : x⁻¹ * r * x ∈ Pc M V := by
    have h := (Subgroup.mem_normalizer_iff.mp (hUN (U.inv_mem hxU)) r).mp hrP
    simpa using h
  have hry : r * x' * r⁻¹ = y := by
    rw [← MulAut.conj_apply]
    exact hx'y
  have h1 : (x⁻¹ * r * x) * (x⁻¹ * x') = p₀ * r := by
    calc (x⁻¹ * r * x) * (x⁻¹ * x') = x⁻¹ * r * x' := by group
      _ = x⁻¹ * (r * x' * r⁻¹) * r := by group
      _ = x⁻¹ * (x * p₀) * r := by rw [hry, hy_eq]
      _ = p₀ * r := by group
  have hx'xP : x⁻¹ * x' ∈ Pc M V := by
    have h2 : x⁻¹ * x' = (x⁻¹ * r * x)⁻¹ * (p₀ * r) := by rw [← h1]; group
    rw [h2]
    exact (Pc M V).mul_mem ((Pc M V).inv_mem hr₁P) ((Pc M V).mul_mem hp₀P hrP)
  have hx'xbot : x⁻¹ * x' ∈ (⊥ : Subgroup G) := by
    rw [← hUbot]
    exact Subgroup.mem_inf.mpr ⟨U.mul_mem (U.inv_mem hxU) hx'U, hx'xP⟩
  have hx'x1 : x⁻¹ * x' = 1 := Subgroup.mem_bot.mp hx'xbot
  have hx'eqx : x' = x := by
    simpa [mul_assoc] using congrArg (fun z => x * z) hx'x1
  refine ⟨r, hrP, ?_⟩
  calc m * x * m⁻¹ = y := hydef.symm
    _ = r * x' * r⁻¹ := hry.symm
    _ = r * x * r⁻¹ := by rw [hx'eqx]
end CFSG.RankThree.GF2n.Tim81

end
