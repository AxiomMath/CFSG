module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclWeyl
public import CFSG.LocalAnalysis.StandardType.GGRealQFourThree
public import CFSG.LocalAnalysis.StandardType.GGRealKGFiveOffE6
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj
import CFSG.LocalAnalysis.StandardType.GGResNbrFixTor
import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem reflection_image_mem_coordProdStab {G : Type} [Group G] {p n : ℕ}
    {Bs : Subgroup G} {L : Subgroup G} {𝒦 : Finset (Subgroup G)} (hp : p.Prime) (hp2 : p ≠ 2)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {K : Subgroup G} (hKmem : K ∈ 𝒦)
    (hno : ∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
      ∀ i : Fin n, MulAut.congr eta r ≠ SpCoord.sgnAut i)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer K Bs) (hrrefl : GGIsReflection p r) :
    MulAut.congr eta r ∈ coordProdStab n p := by
  have himg : MulAut.congr eta r ∈ bSignedFull n p := by
    rw [← hK]
    exact Subgroup.mem_map.mpr ⟨r, Subgroup.mem_sup_right
      (Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hKmem hrA)), rfl⟩
  have hpow2 : (MulAut.congr eta r) ^ 2 = 1 := by
    rw [← map_pow, hrrefl.1, map_one]
  have hcard := card_fixed_congr eta r
  have hfix : Nat.card {u : Fin n → Multiplicative (ZMod p) //
      MulAut.congr eta r u = u} * p =
      Nat.card (Fin n → Multiplicative (ZMod p)) := by
    rw [hcard, hrrefl.2, Nat.card_congr eta.toEquiv]
  exact mem_coordProdStab_of_isRefl_of_ne_sgnAut hp hp2 himg hpow2 hfix
    fun i hi => hno r hrA hrrefl i hi

theorem sgnAut_apply_of_coord_eq_one {n p : ℕ} {k : Fin n}
    {f : Fin n → Multiplicative (ZMod p)} (hk : f k = 1) :
    SpCoord.sgnAut k f = f := by
  funext i
  by_cases hi : i = k
  · subst hi
    rw [SpCoord.sgnAut_apply, Function.update_self, hk, inv_one]
  · rw [SpCoord.sgnAut_apply, Function.update_of_ne hi]

theorem ggNbr_exists_halfSplit_innerDiagLabel (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥) ∧
        ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K := by
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHalf⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_hyp hraw hiso hcfg hnb hInnK)
  refine ⟨lab, hlab, hHalf, fun S hS => ?_⟩
  refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hInnK hlab hhas)
  rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
  subst h1
  exact ⟨hS, h2, h3⟩

theorem coords_eq_one_of_map_eq_dCoordinateBlock {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hn : 3 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hLD : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      dCoordinateBlock n p i0) :
    ∀ k : Fin n, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 := by
  have hp : p.Prime := hR.1.1.tableB_facts.1
  have hp2 : p ≠ 2 :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G).2.1
  have hfixL : ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    intro φ hφ
    obtain ⟨b, hb, hbval⟩ :=
      Subgroup.mem_map.mp (mem_ggFixG_of_mem_ggAutomizer hxBs hLx hφ)
    have hb' : b = ⟨x, hxBs⟩ := Subtype.ext hbval
    rw [hb'] at hb
    exact mem_ggFix.mp hb
  have h1 : ∀ u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom,
      u (eta ⟨x, hxBs⟩) = eta ⟨x, hxBs⟩ := by
    rintro u ⟨φ, hφ, rfl⟩
    change MulAut.congr eta φ (eta ⟨x, hxBs⟩) = eta ⟨x, hxBs⟩
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      using congrArg eta (hfixL φ hφ)
  rw [hLD] at h1
  exact (forall_dCoordinateBlock_fix_iff hp hp2 hn i0 (eta ⟨x, hxBs⟩)).mp h1

private theorem false_of_sgnAut_eq_of_dCoordinateBlock {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hLD : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      dCoordinateBlock n p i0)
    {t : MulAut ↥Bs} {k : Fin n} (hk : k ≠ i0)
    (ht : MulAut.congr eta t = SpCoord.sgnAut k)
    (hrefl : GGIsReflection p t) (hreal : GGRealized p Bs t) : False := by
  obtain ⟨hp, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨-, -, hxBs, hLx, -⟩ := hR.1.1.tableB_facts
  have hxh := coords_eq_one_of_map_eq_dCoordinateBlock hR hxBs hLx (by omega) eta i0 hLD
  have hfix_t : t ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    apply eta.injective
    have h : eta (t ⟨x, hxBs⟩) = SpCoord.sgnAut k (eta ⟨x, hxBs⟩) := by
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        using congrArg (fun u : MulAut (Fin n → Multiplicative (ZMod p)) =>
          u (eta ⟨x, hxBs⟩)) ht
    rw [h, sgnAut_apply_of_coord_eq_one (hxh k hk)]
  have hfix : x ∈ ggFixG Bs t :=
    Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, mem_ggFix.mpr hfix_t, rfl⟩
  have hP3 := ggFixedRealizedInL_of_config hLB hP hR.1.1 hR.1.2.2.1.1
  have htL := hP3 t hrefl hreal.mem_ggInduced_top hfix hreal
  have hmem : MulAut.congr eta t ∈
      (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom :=
    Subgroup.mem_map_of_mem _ htL
  rw [hLD, ht] at hmem
  exact sgnAut_not_mem_coordProdStab hp hp2 k (dCoordinateBlock_le_coordProdStab i0 hmem)

theorem GGSecFiveRouteCfg.exists_nbr_refl_sgnAut {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hn : 0 < n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p) :
    ∃ y : G, ∃ K ∈ 𝒦, GGNbr p B x D J y K ∧ ∃ r ∈ ggAutomizer K Bs, GGIsReflection p r ∧
      ∃ i : Fin n, MulAut.congr eta r = SpCoord.sgnAut i := by
  by_contra hcon
  obtain ⟨hp, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hno : ∀ (y : G) (K : Subgroup G), K ∈ 𝒦 → GGNbr p B x D J y K →
      ∀ r ∈ ggAutomizer K Bs, GGIsReflection p r →
        ∀ i : Fin n, MulAut.congr eta r ≠ SpCoord.sgnAut i := by
    intro y K hKmem hy r hr hrrefl i hi
    exact hcon ⟨y, K, hKmem, hy, r, hr, hrrefl, i, hi⟩
  have hKle : ∀ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤
      coordProdStab n p := by
    intro K hKmem
    obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hKmem
    have hgen := hR.2.1 y K hy
    rw [hgen]
    refine (Subgroup.map_le_iff_le_comap).mpr ((Subgroup.closure_le _).mpr ?_)
    rintro r ⟨hrA, hrrefl⟩
    exact reflection_image_mem_coordProdStab hp hp2 eta hK hKmem (r := r)
      (fun r hr hrrefl i => hno y K hKmem hy r hr hrrefl i) hrA hrrefl
  have hjoinle : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom ≤
      coordProdStab n p := by
    simp only [ggAutomizerJoin, Subgroup.map_sup, Subgroup.map_iSup]
    exact sup_le hL (iSup₂_le fun K hKmem => hKle K hKmem)
  have hsgn : SpCoord.sgnAut (⟨0, hn⟩ : Fin n) ∈
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
    rw [hK]
    exact Subgroup.subset_closure (Or.inl ⟨⟨0, hn⟩, rfl⟩)
  exact sgnAut_not_mem_coordProdStab hp hp2 ⟨0, hn⟩ (hjoinle hsgn)

theorem GGSecFiveRouteCfg.ne_dCoordinateBlock_of_realized (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {r : MulAut ↥Bs} (hrefl : GGIsReflection p r) {i : Fin n}
    (hri : MulAut.congr eta r = SpCoord.sgnAut i) (hreal : GGRealized p Bs r) :
    (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≠ dCoordinateBlock n p i0 := by
  intro hLD
  obtain ⟨hp, -, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  by_cases hi : i = i0
  · rw [hi] at hri
    have hcard : 1 < Fintype.card (Fin n) := by
      simpa using (by omega : 1 < n)
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i0
    have hmem : SpCoord.permAut (Equiv.swap i0 j) ∈
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
      rw [hK]
      exact Subgroup.subset_closure (Or.inr ⟨i0, j, hji.symm, rfl⟩)
    obtain ⟨w, hwJ, hw⟩ := Subgroup.mem_map.mp hmem
    have hjoinTop : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (⊤ : Subgroup G) Bs :=
      sup_le (ggAutomizer_mono Bs le_top)
        (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top)
    obtain ⟨g, -, hg, rfl⟩ := eq_ggConjAut_of_mem_ggAutomizer (hjoinTop hwJ)
    have hw' : MulAut.congr eta (ggConjAut Bs hg) =
        SpCoord.permAut (Equiv.swap i0 j) := hw
    have hconj : SpCoord.permAut (p := p) (k := n) (Equiv.swap i0 j) *
        SpCoord.sgnAut (p := p) (k := n) i0 *
        (SpCoord.permAut (p := p) (k := n) (Equiv.swap i0 j))⁻¹ =
        SpCoord.sgnAut (p := p) (k := n) j := by
      have h := SpCoord.IsSignedPerm.mul_sgnAut (p := p) (k := n)
        (u := SpCoord.permAut (p := p) (k := n) (Equiv.swap i0 j))
        (π := Equiv.swap i0 j) (ε := fun _ => (1 : ZMod p))
        (by intro f l; rw [SpCoord.permAut_apply]; simp) i0
      rw [h, Equiv.swap_apply_left, mul_assoc, mul_inv_cancel, mul_one]
    have ht : MulAut.congr eta (ggConjAut Bs hg * r * (ggConjAut Bs hg)⁻¹) =
        SpCoord.sgnAut j := by
      rw [map_mul, map_mul, map_inv, hw', hri, hconj]
    exact false_of_sgnAut_eq_of_dCoordinateBlock hLB hP hR hn eta i0 hLD hji ht
      (hrefl.conj' _) (hreal.conj hp hg)
  · exact false_of_sgnAut_eq_of_dCoordinateBlock hLB hP hR hn eta i0 hLD hi hri hrefl hreal

private theorem ggRealized_of_realized_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR5 : GGReflRealizedQFourInputFiveOn fun p lab =>
      ¬ (GGKGRowLabel .e6Nonsplit p lab ∨ GGKGRowLabel .twe6Split p lab))
    (hR3 : GGReflRealizedQFourInputThree) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer K Bs) (hrefl : GGIsReflection p r)
    (hcl : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ (p = 3 ∨
      ¬ (GGKGRowLabel .e6Nonsplit p lab ∨ GGKGRowLabel .twe6Split p lab))) p Bs K) :
    GGRealized p Bs r := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hp3or5 : p = 3 ∨ 5 ≤ p := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have hp2le := hp.two_le
    by_cases h3 : p = 3
    · exact Or.inl h3
    · exact Or.inr (by omega)
  have hRX : GGReflRealizedIn p Bs K := by
    rcases hp3or5 with h3 | h5
    · exact hR3 G p B Bs x L D J hR.1.1 hR.1.2.2.1 hR.1.2.2.2.1 h3 K
        (Or.inr ⟨y, hnb⟩)
        (largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨⟨hq, _⟩, hnorm⟩ => ⟨hq, hnorm⟩) hcl)
    · exact hR5 G p B Bs x L D J hR.1.1 hR.1.2.2.1 hR.1.2.2.2.1 h5 K
        (Or.inr ⟨y, hnb⟩)
        (largeEvenMarking_mono
          (fun _ _ _ _ _ _ ⟨⟨hq, h3or⟩, hnorm⟩ =>
            ⟨⟨hq, h3or.resolve_left (by omega)⟩, hnorm⟩) hcl)
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hnb.1.2.1
  have hKcomp : CFSG.Open.GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ K).mp
      hnb.1.2.2.2.2.1
  exact ggRealized_of_reflRealizedIn hp hyBs hKcomp hRX hr hrefl

private theorem map_le_coordProdStab_of_row {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {y : G} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) (hnb : GGNbr p B x D J y K)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {lab : LargeEvenLabel} (hrow : GGTBTorRowNoFour p lab)
    (key : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  have hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p :=
    map_ggAutomizer_le_bSignedFull_of_join hK𝒦 eta hK
  exact ggNbr_map_le_coordProdStab_of_tbTorRowNoFour hT hLift hR.1.1 hnb eta hAK (key _ hrow)

theorem ggSecFiveBCoordDExclRestOn_of_split {S S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → S₁ p lab ∨ S₂ p lab) (h₁ : GGSecFiveBCoordDExclRestOn S₁)
    (h₂ : GGSecFiveBCoordDExclRestOn S₂) : GGSecFiveBCoordDExclRestOn S := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  rcases (hM.mono_label (T := fun p lab => S₁ p lab ∨ S₂ p lab) (hS p)).elim_or with h | h
  · exact h₁ G p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn h hLD
  · exact h₂ G p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn h hLD

section Certificates


private theorem false_of_not_qFour_of_ne_three (hRig : GGLabelRigidInput)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hHalf : LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥))
    (hq : ¬ GGLabQFour p lab) (hp3 : p ≠ 3)
    (key : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K) : False := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  have hq' : ¬ 2 ≤ lab.n := hq
  have h1 : 1 ≤ lab.n := hlab.1
  have hn1 : lab.n = 1 := by omega
  rcases largeEvenHalfSplit_dvd hlab hHalf with hd | ⟨hp7, hex⟩
  · have hd3 : p ∣ 3 := by
      rw [hn1] at hd
      norm_num at hd
      exact hd
    exact hp3 (by
      rcases Nat.prime_three.eq_one_or_self_of_dvd p hd3 with h | h
      · exact absurd h hp.ne_one
      · exact h)
  · have hSeven : GGSevenLabel lab := by
      rcases hex with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact GGResHyp.false_of_seven hRig hA8 hraw hiso hH hp7 (key _ hSeven)

theorem ggSecFiveBCoordDExclInput_of_rest
    (hDX : GGSecFiveBCoordDExclRestOn GGSecFiveBCoordDExclSplitLabel)
    (hR5 : GGReflRealizedQFourInputFiveOn fun p lab =>
      ¬ (GGKGRowLabel .e6Nonsplit p lab ∨ GGKGRowLabel .twe6Split p lab))
    (hR3 : GGReflRealizedQFourInputThree) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hRig : GGLabelRigidInput)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGSecFiveBCoordDExclInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR n eta i0 hn4 hK hLD
  obtain ⟨hp, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have : Fact p.Prime := ⟨hp⟩
  have hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
    rw [hLD]
    exact dCoordinateBlock_le_coordProdStab i0
  obtain ⟨y, K, hK𝒦, hnb, r, hr, hrefl, i, hri⟩ :=
    GGSecFiveRouteCfg.exists_nbr_refl_sgnAut hR (by omega) eta hK hL
  have hInnK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
  obtain ⟨lab, hlab, hHalf, key⟩ :=
    ggNbr_exists_halfSplit_innerDiagLabel hRig hraw hiso hR.1.1 hnb hInnK
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hnb, hR.2.1 y K hnb, Or.inr hR.2.1⟩
  by_cases hq : GGLabQFour p lab
  · by_cases hreal : p = 3 ∨ ¬ (GGKGRowLabel .e6Nonsplit p lab ∨
        GGKGRowLabel .twe6Split p lab)
    · exact (GGSecFiveRouteCfg.ne_dCoordinateBlock_of_realized hLB hP hR hn4 eta i0 hK hrefl
        hri (ggRealized_of_realized_marking hR5 hR3 hR hnb hr hrefl (key _ ⟨hq, hreal⟩))) hLD
    · have hnp : p ≠ 3 ∧ (GGKGRowLabel .e6Nonsplit p lab ∨
          GGKGRowLabel .twe6Split p lab) := by
        refine ⟨fun h3 => hreal (Or.inl h3), ?_⟩
        by_contra hE
        exact hreal (Or.inr hE)
      exact false_of_sgnAut_mem_map_coordProdStab hp hp2 eta hr hri
        (map_le_coordProdStab_of_row hT hLift hR hK𝒦 hnb eta hK
          (ggTBTorRowNoFour_of_e6Row hnp.1 hnp.2) key)
  · by_cases hrow : GGTBTorRowNoFour p lab
    · exact false_of_sgnAut_mem_map_coordProdStab hp hp2 eta hr hri
        (map_le_coordProdStab_of_row hT hLift hR hK𝒦 hnb eta hK hrow key)
    · by_cases hcl : GGTableBNbrInnerNineClassicalLabel p lab
      · exact (GGResHyp.false_of_classical_rank_vacuity hH (key _ hcl)).elim
      · by_cases hsm : GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨
            lab.tag = .twF4
        · exact (GGResHyp.false_of_small_neighbour hH (key _ hsm)).elim
        · by_cases hp3 : p = 3
          · exact hDX G p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl
              ⟨i, hri⟩ (key _ ⟨hq, hrow, hcl, hsm⟩) hLD
          · exact (false_of_not_qFour_of_ne_three hRig hA8 hraw hiso hH hlab hHalf hq hp3
              key).elim

end Certificates

end CFSG.StandardType

end
