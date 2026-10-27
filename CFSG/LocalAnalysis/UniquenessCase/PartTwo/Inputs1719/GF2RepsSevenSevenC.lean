module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Quasithin.Background.E3Restrict
public import CFSG.Quasithin.Background.SmithD321SzK
public import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstar
public import CFSG.GroupTheory.PerfectCentralizer
public import CFSG.RankThree.PGroups.CentralCoprimeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped commutatorElement Pointwise

namespace SevenSevenC

variable {U : Type} [CommGroup U] [Finite U]

theorem stableUnder_fixV_of_le_normalizer {N P : Subgroup (MulAut U)}
    (hNP : N ≤ Subgroup.normalizer (P : Set (MulAut U))) :
    ∀ n ∈ N, ∀ u ∈ fixV P, n u ∈ fixV P :=
  fun n hn u hu => CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hNP hn) hu

theorem range_actOnSub_fixV_ne_bot {L P : Subgroup (MulAut U)}
    (hU : ∀ u : U, u ^ 2 = 1) (hLq : CFSG.IsQuasisimple ↥L) (hP2 : IsPGroup 2 ↥P)
    (hPL : P ≤ Subgroup.centralizer (L : Set (MulAut U)))
    (hPn : L ≤ Subgroup.normalizer (P : Set (MulAut U))) :
    (actOnSub (stableUnder_fixV_of_le_normalizer hPn)).range ≠ ⊥ := by
  classical
  intro hbot
  obtain ⟨x, hxodd, hxnc⟩ := CFSG.Quasithin.SmithD321.exists_odd_not_mem_center hLq
  have hx1 : (x : MulAut U) ≠ 1 := by
    intro h
    apply hxnc
    rw [Subgroup.mem_center_iff]
    intro y
    rw [show x = 1 from Subtype.ext h]
    simp
  have hfx : (actOnSub (stableUnder_fixV_of_le_normalizer hPn)) x = 1 := by
    have hmem : (actOnSub (stableUnder_fixV_of_le_normalizer hPn)) x ∈
        (actOnSub (stableUnder_fixV_of_le_normalizer hPn)).range :=
      MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rw [hbot] at hmem
    simpa using Subgroup.mem_bot.mp hmem
  have hfix : ∀ u ∈ fixV P, (x : MulAut U) u = u := by
    intro u hu
    have h2 := congrArg (fun g : MulAut ↥(fixV P) => g ⟨u, hu⟩) hfx
    simp only [MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val h2
    simpa [actOnSub_apply] using h3
  have hcomm : ∀ s ∈ P, (x : MulAut U) * s = s * (x : MulAut U) := fun s hs =>
    Subgroup.mem_centralizer_iff.mp (hPL hs) (x : MulAut U) x.2
  have hpow : (x : MulAut U) ^ orderOf x = 1 := by
    have h := congrArg (fun z : ↥L => (z : MulAut U)) (pow_orderOf_eq_one x)
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  exact hx1 (CFSG.Quasithin.SmithD39Two.eq_one_of_fix_fixV hU hP2 hxodd hpow hcomm hfix)

theorem ker_actOnSub_fixV_le_center {L P : Subgroup (MulAut U)}
    (hU : ∀ u : U, u ^ 2 = 1) (hLq : CFSG.IsQuasisimple ↥L) (hP2 : IsPGroup 2 ↥P)
    (hPL : P ≤ Subgroup.centralizer (L : Set (MulAut U)))
    (hPn : L ≤ Subgroup.normalizer (P : Set (MulAut U))) :
    (actOnSub (stableUnder_fixV_of_le_normalizer hPn)).ker ≤ Subgroup.center ↥L := by
  classical
  let f : ↥L →* MulAut ↥(fixV P) := actOnSub (stableUnder_fixV_of_le_normalizer hPn)
  change f.ker ≤ Subgroup.center ↥L
  have hN : f.ker.Normal := MonoidHom.normal_ker f
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hN with htop | hle
  · exfalso
    have hbot : f.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨l, rfl⟩
      have hl : l ∈ f.ker := by rw [htop]; exact Subgroup.mem_top l
      exact MonoidHom.mem_ker.mp hl
    exact range_actOnSub_fixV_ne_bot hU hLq hP2 hPL hPn hbot
  · exact hle

theorem isQuasisimple_actOnSub_fixV_range {L P : Subgroup (MulAut U)}
    (hU : ∀ u : U, u ^ 2 = 1) (hLq : CFSG.IsQuasisimple ↥L) (hP2 : IsPGroup 2 ↥P)
    (hPL : P ≤ Subgroup.centralizer (L : Set (MulAut U)))
    (hPn : L ≤ Subgroup.normalizer (P : Set (MulAut U))) :
    CFSG.IsQuasisimple
      ↥(actOnSub (stableUnder_fixV_of_le_normalizer hPn)).range :=
  CFSG.LocalCores.isQuasisimple_of_surjective hLq
    (actOnSub (stableUnder_fixV_of_le_normalizer hPn)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
    (by
      rw [MonoidHom.ker_rangeRestrict]
      exact ker_actOnSub_fixV_le_center hU hLq hP2 hPL hPn)

theorem centralizes_of_commutes_on_fixV {L P G : Subgroup (MulAut U)}
    (hU : ∀ u : U, u ^ 2 = 1) (hLq : CFSG.IsQuasisimple ↥L) (hP2 : IsPGroup 2 ↥P)
    (hPL : P ≤ Subgroup.centralizer (L : Set (MulAut U)))
    (hPn : L ≤ Subgroup.normalizer (P : Set (MulAut U)))
    (hLG : L ≤ G) (hGn : G ≤ Subgroup.normalizer (P : Set (MulAut U)))
    {g : MulAut U} (hgG : g ∈ G)
    (hgN : g ∈ Subgroup.normalizer (L : Set (MulAut U)))
    (hgcent : ∀ (l : MulAut U) (hl : l ∈ L),
      actOnSub (stableUnder_fixV_of_le_normalizer hGn) ⟨g, hgG⟩ *
        actOnSub (stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ =
      actOnSub (stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ *
        actOnSub (stableUnder_fixV_of_le_normalizer hGn) ⟨g, hgG⟩) :
    g ∈ Subgroup.centralizer (L : Set (MulAut U)) := by
  classical
  let fL : ↥L →* MulAut ↥(fixV P) := actOnSub (stableUnder_fixV_of_le_normalizer hPn)
  let fG : ↥G →* MulAut ↥(fixV P) := actOnSub (stableUnder_fixV_of_le_normalizer hGn)
  have hker : fL.ker ≤ Subgroup.center ↥L :=
    ker_actOnSub_fixV_le_center hU hLq hP2 hPL hPn
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
  have hident : ∀ (l : MulAut U) (hl : l ∈ L), fL ⟨l, hl⟩ = fG ⟨l, hLG hl⟩ := by
    intro l hl
    ext u
    rfl
  have hprodmem : ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ L := fun l hl =>
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN l).mp hl) (L.inv_mem hl)
  have hmemker : ∀ (l : MulAut U) (hl : l ∈ L),
      (⟨g * l * g⁻¹ * l⁻¹, hprodmem l hl⟩ : ↥L) ∈ fL.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    change fL ⟨g * l * g⁻¹ * l⁻¹, hprodmem l hl⟩ = 1
    have hGprod : fG ⟨g * l * g⁻¹ * l⁻¹, hLG (hprodmem l hl)⟩ =
        fG ⟨g, hgG⟩ * fG ⟨l, hLG hl⟩ * (fG ⟨g, hgG⟩)⁻¹ * (fG ⟨l, hLG hl⟩)⁻¹ := by
      rw [show (⟨g * l * g⁻¹ * l⁻¹, hLG (hprodmem l hl)⟩ : ↥G) =
        ⟨g, hgG⟩ * ⟨l, hLG hl⟩ * ⟨g, hgG⟩⁻¹ * ⟨l, hLG hl⟩⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv]
    rw [hident (g * l * g⁻¹ * l⁻¹) (hprodmem l hl)]
    rw [hGprod, ← hident l hl, hgcent l hl]
    simp only [fL, fG]
    group
  have hcomm : ∀ l ∈ L, ⁅g, l⁆ ∈ (Subgroup.center ↥L).map L.subtype := by
    intro l hl
    refine Subgroup.mem_map.mpr ⟨⟨g * l * g⁻¹ * l⁻¹, hprodmem l hl⟩,
      hker (hmemker l hl), ?_⟩
    rw [commutatorElement_def]
    rfl
  exact CFSG.GroupTheory.centralizes_of_commutator_mem_center hperf hgN hcomm

theorem fstarSubOf_eq_of_centralizer_le {Y L : Subgroup (MulAut U)} (hLY : L ≤ Y)
    (hLq : CFSG.IsQuasisimple ↥L) (hN : (L.subgroupOf Y).Normal)
    (hcent : Subgroup.centralizer ((L.subgroupOf Y) : Set ↥Y) ≤ L.subgroupOf Y) :
    fstarSubOf Y = L.subgroupOf Y := by
  classical
  have hq : CFSG.IsQuasisimple ↥(L.subgroupOf Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLY).symm hLq
  have hcomp : CFSG.IsComponent (L.subgroupOf Y) := ⟨hq, hN.isSubnormal⟩
  have hgen : CFSG.generalizedFitting ↥Y = L.subgroupOf Y :=
    CFSG.GroupTheory.generalizedFitting_eq_of_isComponent_of_centralizer_le _ hcomp hcent
  rw [fstarSubOf, CFSG.LocalAnalysis.UniquenessCase.PartTwo.fstar_eq_of_generalizedFitting_eq hLY
    hgen]

theorem exists_twoPart_centralizer {L A : Subgroup (MulAut U)}
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut U))) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∃ P : Subgroup (MulAut U), IsPGroup 2 ↥P ∧
      P ≤ Subgroup.centralizer (L : Set (MulAut U)) ⊓ (L ⊔ A) ∧
      (∀ g ∈ L ⊔ A, ∀ s ∈ P, g * s * g⁻¹ ∈ P) ∧
      ∀ g ∈ Subgroup.centralizer (L : Set (MulAut U)) ⊓ (L ⊔ A),
        ∃ z ∈ L, ∃ s ∈ P, g = z * s := by
  classical
  let G : Subgroup (MulAut U) := L ⊔ A
  let C : Subgroup (MulAut U) := Subgroup.centralizer (L : Set (MulAut U)) ⊓ G
  let N : Subgroup ↥C := L.subgroupOf C
  have hCnormL : C ≤ Subgroup.normalizer (L : Set (MulAut U)) :=
    inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  have hNnormal : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCnormL
  have hNZ : N ≤ Subgroup.center ↥C := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2.1 (n : MulAut U)
      (Subgroup.mem_subgroupOf.mp hn)).symm
  have hCN : IsPGroup 2 (↥C ⧸ N) := by
    refine IsPGroup.of_exponent_dvd_pow (p := 2) (n := 1) ?_
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_subgroupOf]
    have hsq : (c : MulAut U) ^ 2 ∈ L := CFSG.Quasithin.B1Red.sq_mem_of_mem_sup hAN hA2 _ c.2.2
    simpa using hsq
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  obtain ⟨hQn, hNQ, hQ2⟩ :=
    CFSG.RankThree.PGroups.sylow_normal_of_le_center_of_isPGroup_quotient
      (p := 2) Nat.prime_two hNZ hCN Q
  let P : Subgroup (MulAut U) := (Q : Subgroup ↥C).map C.subtype
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · show IsPGroup 2 ↥P
    simpa [P] using Q.2.map C.subtype
  · intro x hx
    have hxC : x ∈ C := Subgroup.map_subtype_le (Q : Subgroup ↥C) hx
    exact ⟨hxC.1, hxC.2⟩
  · intro g hg s hs
    obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.mp hs
    have hGnormL : G ≤ Subgroup.normalizer (L : Set (MulAut U)) :=
      sup_le Subgroup.le_normalizer hAN
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut U)) := hGnormL hg
    have hqC : ((q : ↥C) : MulAut U) ∈ C := q.2
    have hmemC : g * (q : MulAut U) * g⁻¹ ∈ C := by
      change g * (q : MulAut U) * g⁻¹ ∈
        Subgroup.centralizer (L : Set (MulAut U)) ⊓ G
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hgl : g⁻¹ * l * g ∈ L :=
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (L : Set (MulAut U))).inv_mem hgN) l).mp hl
        have hqcomm : ((q : ↥C) : MulAut U) * (g⁻¹ * l * g) = (g⁻¹ * l * g) * q :=
          (Subgroup.mem_centralizer_iff.mp hqC.1 (g⁻¹ * l * g) hgl).symm
        have hcomm : (g * (q : MulAut U) * g⁻¹) * l =
            l * (g * (q : MulAut U) * g⁻¹) := by
          calc (g * (q : MulAut U) * g⁻¹) * l
              = g * ((q : MulAut U) * (g⁻¹ * l * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * l * g) * (q : MulAut U)) * g⁻¹ := by rw [hqcomm]
            _ = l * (g * (q : MulAut U) * g⁻¹) := by group
        exact hcomm.symm
      · exact G.mul_mem (G.mul_mem hg hqC.2) (G.inv_mem hg)
    let q' : ↥C := ⟨g * (q : MulAut U) * g⁻¹, hmemC⟩
    have hq'2 : ∃ k, orderOf q' = 2 ^ k := by
      obtain ⟨k, hk⟩ := Q.2.exists_orderOf_eq_pow (⟨q, hqQ⟩ : ↥Q)
      have hqk : orderOf q = 2 ^ k := by
        rw [← Subgroup.orderOf_mk (H := Q) q hqQ]
        exact hk
      refine ⟨k, ?_⟩
      have hord : orderOf (g * (q : MulAut U) * g⁻¹) = orderOf (q : MulAut U) := by
        simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq (q : MulAut U)
      rw [Subgroup.orderOf_mk, hord, Subgroup.orderOf_coe, hqk]
    have hq'Q : q' ∈ Q := hQ2 q' hq'2
    exact Subgroup.mem_map.mpr ⟨q', hq'Q, rfl⟩
  · intro g hg
    let c : ↥C := ⟨g, hg⟩
    have hc : c ∈ (N : Set ↥C) * ((Q : Subgroup ↥C) : Set ↥C) := by
      rw [hNQ]
      exact Set.mem_univ c
    obtain ⟨n, hn, q, hqQ, hnq⟩ := Set.mem_mul.mp hc
    refine ⟨(n : MulAut U), ⟨Subgroup.mem_subgroupOf.mp hn, ?_⟩⟩
    refine ⟨(q : MulAut U), ⟨Subgroup.mem_map.mpr ⟨q, hqQ, rfl⟩, ?_⟩⟩
    have hval : ((n * q : ↥C) : MulAut U) = g := by rw [hnq]
    exact hval.symm.trans (Subgroup.coe_mul C n q)

theorem caseB_data_of_normalizes (hU : ∀ u : U, u ^ 2 = 1) {L A : Subgroup (MulAut U)}
    {k : ℕ} (hLq : CFSG.IsQuasisimple ↥L)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut U)))
    (hA : A ∈ E3.aSet k (L ⊔ A))
    (hAC : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut U))) :
    ∃ (U₁ : Type) (_ : CommGroup U₁) (_ : Finite U₁), (∀ u : U₁, u ^ 2 = 1) ∧
      ∃ (Y₁ : Subgroup (MulAut U₁)) (hLn : (fstarSubOf Y₁).Normal),
        IsQuasisimple ↥(fstarSubOf Y₁) ∧
        (∃ f : ↥L →* ↥(fstarSubOf Y₁), Function.Surjective f) ∧ k ≤ E3.aParam Y₁ := by
  classical
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hA.2.2.1.2 a ha
  obtain ⟨P, hP2, hPC, hPnorm, hCdecomp⟩ := exists_twoPart_centralizer hAN hA2
  let G : Subgroup (MulAut U) := L ⊔ A
  let V : Subgroup U := fixV P
  have hGn : G ≤ Subgroup.normalizer (P : Set (MulAut U)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact hPnorm g hg s hs
    · intro hs
      have h := hPnorm g⁻¹ (G.inv_mem hg) (g * s * g⁻¹) hs
      rwa [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group] at h
  have hGnormL : G ≤ Subgroup.normalizer (L : Set (MulAut U)) :=
    sup_le Subgroup.le_normalizer hAN
  have hPL : P ≤ Subgroup.centralizer (L : Set (MulAut U)) := hPC.trans inf_le_left
  have hPn : L ≤ Subgroup.normalizer (P : Set (MulAut U)) :=
    (le_sup_left : L ≤ L ⊔ A).trans hGn
  have hLV : ∀ l ∈ L, ∀ u ∈ V, l u ∈ V := stableUnder_fixV_of_le_normalizer hPn
  have hAV : ∀ a ∈ A, ∀ u ∈ V, a u ∈ V :=
    stableUnder_fixV_of_le_normalizer ((le_sup_right : A ≤ L ⊔ A).trans hGn)
  let fL : ↥L →* MulAut V := actOnSub hLV
  let fA : ↥A →* MulAut V := actOnSub hAV
  let Y₁ : Subgroup (MulAut V) := fL.range ⊔ fA.range
  have hker : fL.ker ≤ Subgroup.center ↥L :=
    ker_actOnSub_fixV_le_center hU hLq hP2 hPL hPn
  have hL1q : CFSG.IsQuasisimple ↥(fL.range) :=
    isQuasisimple_actOnSub_fixV_range hU hLq hP2 hPL hPn
  have hAnorm : fA.range ≤ Subgroup.normalizer (fL.range : Set (MulAut V)) :=
    E3.actOnSub_range_le_normalizer hLV hAV hAN
  have hYnorm : Y₁ ≤ Subgroup.normalizer (fL.range : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hAnorm
  have hN : (fL.range.subgroupOf Y₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
  let ρ : ↥G →* MulAut V := actOnSub (stableUnder_fixV_of_le_normalizer hGn)
  have hfL_le : fL.range ≤ ρ.range := by
    rintro _ ⟨l, rfl⟩
    exact ⟨⟨(l : MulAut U), (le_sup_left : L ≤ L ⊔ A) l.2⟩, rfl⟩
  have hfA_le : fA.range ≤ ρ.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨(a : MulAut U), (le_sup_right : A ≤ L ⊔ A) a.2⟩, rfl⟩
  have hcent : Subgroup.centralizer ((fL.range).subgroupOf Y₁ : Set ↥Y₁) ≤
      (fL.range).subgroupOf Y₁ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxY : (x : MulAut V) ∈ Y₁ := x.2
    have hxρ : (x : MulAut V) ∈ ρ.range := (sup_le hfL_le hfA_le) hxY
    obtain ⟨g, hgx⟩ := MonoidHom.mem_range.mp hxρ
    have hgcent : ∀ (l : MulAut U) (hl : l ∈ L),
        ρ ⟨g, g.2⟩ * fL ⟨l, hl⟩ = fL ⟨l, hl⟩ * ρ ⟨g, g.2⟩ := by
      intro l hl
      have hmeml : fL ⟨l, hl⟩ ∈ fL.range := MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, rfl⟩
      have hyl : (⟨fL ⟨l, hl⟩, (le_sup_left : fL.range ≤ Y₁) hmeml⟩ : ↥Y₁) ∈
          (fL.range).subgroupOf Y₁ := by
        rw [Subgroup.mem_subgroupOf]
        exact hmeml
      have hcomm := Subgroup.mem_centralizer_iff.mp hx
        ⟨fL ⟨l, hl⟩, (le_sup_left : fL.range ≤ Y₁) hmeml⟩ hyl
      have hval : fL ⟨l, hl⟩ * (x : MulAut V) = (x : MulAut V) * fL ⟨l, hl⟩ := by
        simpa using congrArg Subtype.val hcomm
      rw [← hgx] at hval
      exact hval.symm
    have hgC : (g : MulAut U) ∈ Subgroup.centralizer (L : Set (MulAut U)) :=
      centralizes_of_commutes_on_fixV hU hLq hP2 hPL hPn (le_sup_left : L ≤ L ⊔ A) hGn g.2
        (hGnormL g.2) hgcent
    have hgmemC : (g : MulAut U) ∈ Subgroup.centralizer (L : Set (MulAut U)) ⊓ G :=
      ⟨hgC, g.2⟩
    obtain ⟨z, hzL, s, hsP, hgs⟩ := hCdecomp (g : MulAut U) hgmemC
    have hρg : (x : MulAut V) = fL ⟨z, hzL⟩ := by
      rw [← hgx]
      ext u
      have hsu : (s : MulAut U) (u : U) = (u : U) := (mem_fixV.mp u.2) s hsP
      calc ((ρ ⟨g, g.2⟩) u : U) = (g : MulAut U) (u : U) := actOnSub_apply _ _ _
        _ = ((z * s : MulAut U)) (u : U) := by rw [hgs]
        _ = (z : MulAut U) ((s : MulAut U) (u : U)) := rfl
        _ = (z : MulAut U) (u : U) := by rw [hsu]
        _ = ((fL ⟨z, hzL⟩) u : U) := (actOnSub_apply hLV ⟨z, hzL⟩ u).symm
    rw [hρg]
    exact MonoidHom.mem_range.mpr ⟨⟨z, hzL⟩, rfl⟩
  have hfst : fstarSubOf Y₁ = (fL.range).subgroupOf Y₁ :=
    fstarSubOf_eq_of_centralizer_le (le_sup_left : fL.range ≤ Y₁) hL1q hN hcent
  have hLn : (fstarSubOf Y₁).Normal := by
    rw [hfst]
    exact hN
  have hq : CFSG.IsQuasisimple ↥(fstarSubOf Y₁) := by
    rw [hfst]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : fL.range ≤ Y₁)).symm hL1q
  have hne : fA.range ≠ ⊥ := by
    intro hbot
    apply hAC
    intro a ha
    have hfixa : ∀ u ∈ V, (a : MulAut U) u = u := by
      intro u hu
      have hmem : fA ⟨a, ha⟩ ∈ fA.range := MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
      rw [hbot] at hmem
      have h1 : fA ⟨a, ha⟩ = 1 := by simpa using Subgroup.mem_bot.mp hmem
      have h2 := congrArg (fun h : MulAut V => h ⟨u, hu⟩) h1
      simp only [MulAut.one_apply] at h2
      have h3 := congrArg Subtype.val h2
      simpa [fA, actOnSub_apply] using h3
    have haG : a ∈ G := (le_sup_right : A ≤ L ⊔ A) ha
    have haone : (actOnSub (stableUnder_fixV_of_le_normalizer hGn))
        ⟨(a : MulAut U), haG⟩ = 1 := by
      ext u
      simpa [actOnSub_apply] using hfixa (u : U) u.2
    exact centralizes_of_commutes_on_fixV hU hLq hP2 hPL hPn (le_sup_left : L ≤ L ⊔ A) hGn
      haG (hGnormL haG) fun _ _ => by rw [haone]; group
  have hA1 : fA.range ∈ E3.aSet k Y₁ :=
    E3.mem_aSet_actOnSub (X := L ⊔ A) (A := A) (I := V) (Y := Y₁) hA hAV
      (le_sup_right : fA.range ≤ Y₁) hne
  have hk : k ≤ E3.aParam Y₁ := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      exact Nat.zero_le _
    · exact E3.le_aParam_of_mem_aSet hk0 hA1
  refine ⟨V, inferInstance, inferInstance, ?_, Y₁, hLn, hq, ?_, hk⟩
  · intro u
    apply Subtype.ext
    simpa using hU (u : U)
  · refine ⟨(MulEquiv.subgroupCongr hfst).symm.toMonoidHom.comp
      ((Subgroup.subgroupOfEquivOfLe (le_sup_left : fL.range ≤ Y₁)).symm.toMonoidHom.comp
        fL.rangeRestrict), ?_⟩
    intro y
    obtain ⟨z, rfl⟩ := (MulEquiv.subgroupCongr hfst).symm.surjective y
    obtain ⟨w, rfl⟩ :=
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : fL.range ≤ Y₁)).symm.surjective z
    obtain ⟨v, rfl⟩ := MonoidHom.rangeRestrict_surjective fL w
    exact ⟨v, rfl⟩

end SevenSevenC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
