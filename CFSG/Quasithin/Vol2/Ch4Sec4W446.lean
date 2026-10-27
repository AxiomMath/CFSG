module

public import CFSG.Quasithin.Vol2.Ch4Sec4W443
public import CFSG.Quasithin.Vol2.Ch4Sec2W4213
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem444Proved
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Z
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped IsMulCommutative Pointwise commutatorElement

@[expose] def Lemma446Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L VB : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → M ≤ Subgroup.normalizer (L : Set G) →
    VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)) →
    L ⊔ T ≤ Subgroup.normalizer (VB : Set G) → VB = ⁅VB, L⁆ → VB ≠ ⊥ →
    Concl443TwoI G T M L ⁅reducedAggregate (L ⊔ T), L⁆ →
    IrrCase4213 G L ⁅reducedAggregate (L ⊔ T), L⁆ → Concl443TwoI G T M L VB

@[expose] def Lemma446ModOrth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L VB : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → M ≤ Subgroup.normalizer (L : Set G) →
    VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)) →
    L ⊔ T ≤ Subgroup.normalizer (VB : Set G) → VB = ⁅VB, L⁆ → VB ≠ ⊥ →
    Orth4213 G M L ⁅reducedAggregate (L ⊔ T), L⁆ →
      ∃ _ : IsMulCommutative ↥VB, BinaryOrthogonalFour (V := ↥VB) (autOn L VB) ⊤ ⊥ 1

variable {G : Type} [Group G] [Finite G]

namespace Setting443

variable {T M L B Tp VB : Subgroup G} (s : Setting443 G T M L B Tp VB)
include s

theorem hyp421 : Hyp4_2_1 G T M L :=
  ⟨s.hyp.simple, s.hyp.nonabelian, s.hyp.qtke, s.hyp.sylow, s.hyp.maxTwoLocal, s.hyp.T_le,
    s.hyp.maximal, s.hyp.faithful, s.hyp.L_le, s.hyp.quasisimple⟩

theorem mem_normalizer_of_mem_centralizerSection (h37 : A37ForSQTK) (h39 : A39ForSQTK) {q : G}
    (hqT : q ∈ T)
    (hqC : q ∈ centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T))) :
    q ∈ Subgroup.normalizer (L : Set G) := by
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  have hLc : L ∈ cComp M := s.hyp421.mem_cComp h37 h39
  have hO2M : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal s.hyp.maxTwoLocal.1
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_hyp421 s.hyp421 h37 h39
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := le_normalizer_conjClosure L T
  have hqM : q ∈ M := s.hyp.T_le hqT
  have hLq := map_conj_mem_cComp hLc hqM
  by_contra hqN
  have he : L.map (MulAut.conj q).toMonoidHom ≠ L := fun h =>
    hqN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hc := (lemma_1_2_1_two s.hyp.qtke s.hyp.simple s.hyp.nonabelian h37 hO2M hLc hLq
    (Ne.symm he)).1
  have hO2LQ : pCoreOf 2 L ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLMp)
      (hMpN.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hLqMp : L.map (MulAut.conj q).toMonoidHom ≤ Mp := by
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTMp hqT) l).mp (hLMp hl)
  have hLQ : ∀ l ∈ L, l ∈ ((L.map (MulAut.conj q).toMonoidHom : Subgroup G) : Set G) *
      (Q : Set G) := by
    intro l hl
    refine ⟨q * l * q⁻¹, ⟨l, hl, rfl⟩, (q * l * q⁻¹)⁻¹ * l, ?_, by group⟩
    have h1 := hqC.2.2.2 l⁻¹ (Mp.inv_mem (hLMp hl))
    have h2 := Q.inv_mem h1
    have e : (l⁻¹ * q * l⁻¹⁻¹ * q⁻¹)⁻¹ = (q * l * q⁻¹)⁻¹ * l := by group
    rwa [e] at h2
  have hLL : ⁅L, L⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hLQ b hb
    have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Q.mul_mem (hO2LQ ((hc.trans inf_le_left) (Subgroup.commutator_mem_commutator ha hx)))
      ?_
    have h1 : ⁅a, y⁆ ∈ Q := by
      rw [commutatorElement_def]
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mp (hLMp ha)) y).mp hy
      exact Q.mul_mem this (Q.inv_mem hy)
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mp (hLqMp hx)) _).mp h1
  have hLle : L ≤ Q := calc L = ⁅L, L⁆ := s.hyp421.perfect.symm
    _ ≤ Q := hLL
  exact ne_bot_of_mem_cComp hLc (eq_bot_of_commutator_eq_self_of_isPGroup_two
    s.hyp421.perfect ((pCoreOf_isPGroup 2 Mp).to_le hLle))

end Setting443

theorem lemma446One_of (h4213 : Stmt4_2_13FF) (hMod : Lemma446Mod) (hModO : Lemma446ModOrth)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) : Lemma446One := by
  intro G _ _ T M L B Tp VB s
  have hH := s.hyp
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  set LB := perfectCore (Mp ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set TB := Tp ⊓ Subgroup.normalizer (B : Set G) with hTB
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_hyp421 s.hyp421 h37 h39
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := le_normalizer_conjClosure L T
  have hTpT : Tp ≤ T := hH.Tp_le
  have hBMp : B ≤ Subgroup.normalizer (Mp : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_comm B Mp).trans_le (hH.commutator_le.trans (pCoreOf_le 2 Mp)))
  have hMpM : Mp ≤ M := s.hyp421.conjClosure_le
  have hNQ : Subgroup.normalizer (Mp : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Mp
  have h444 := lemma_4_4_4_orbit hH.toHyp4_4_1TwoOrbit
  have h445 := lemma_4_4_5_orbit hH.toHyp4_4_1TwoOrbit
  set X := pCoreOf 2 (Tp ⊔ B) with hX
  have hXBT : ⁅X, B⁆ ≤ Tp := le_sup_left.trans h444.ge
  have hXN : Tp ⊔ B ≤ M ⊓ Subgroup.normalizer (Mp : Set G) :=
    _root_.sup_le (le_inf (hTpT.trans hH.T_le) (hTpT.trans hTMp)) (le_inf hH.B_le hBMp)
  have hBcs : B ≤ centralizerSection M Mp Q := fun b hb =>
    ⟨hH.B_le hb, hBMp hb, hNQ (hBMp hb), fun m hm =>
      hH.commutator_le (Subgroup.commutator_mem_commutator hm hb)⟩
  have hXBcs : ⁅X, B⁆ ≤ centralizerSection M Mp Q := by
    rw [Subgroup.commutator_le]
    intro x hx b hb
    have hxN : x ∈ Subgroup.normalizer (centralizerSection M Mp Q : Set G) :=
      le_normalizer_centralizerSection M Mp (hXN ((pCoreOf_le 2 _) hx))
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxN b).mp (hBcs hb))
      (Subgroup.inv_mem _ (hBcs hb))
  have hXBN : ∀ q ∈ ⁅X, B⁆, q ∈ Subgroup.normalizer (L : Set G) := fun q hq =>
    s.mem_normalizer_of_mem_centralizerSection h37 h39 (hTpT (hXBT hq)) (hXBcs hq)
  have hTBX : TB ≤ Subgroup.normalizer ((⁅X, B⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (le_sup_left.trans (le_normalizer_pCoreOf 2 (Tp ⊔ B)) hx.1) hx.2
  have hTBLB : TB ≤ Subgroup.normalizer (LB : Set G) := fun x hx =>
    normalizer_le_normalizer_perfectCore _ (mem_normalizer_inf (hTMp (hTpT hx.1))
      (mem_normalizer_centralizer_of_mem_normalizer hx.2))
  have hLBQ : LB ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    le_normalizer_pCoreOf 2 Mp ((perfectCore_le _).trans inf_le_left hx)
  have hMpset : (Mp : Set G) = (LB : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLBQ]
    exact congrArg (fun K : Subgroup G => (K : Set G)) h445
  have hconjB : ∀ b ∈ TB, ∀ q ∈ ⁅X, B⁆,
      CFSG.conjugate L (q * b) = CFSG.conjugate L b := by
    intro b _ q hq
    rw [conjugate_mul, conjugate_eq_self_of_normalizes (hXBN q hq)]
  set I := LB ⊔ TB with hI
  have hIM : I ≤ M :=
    _root_.sup_le ((perfectCore_le _).trans (inf_le_left.trans hMpM))
      (inf_le_left.trans (hTpT.trans hH.T_le))
  have hTp' : (Tp : Set G) = ((⁅X, B⁆ : Subgroup G) : Set G) * (TB : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTBX]
    exact congrArg (fun K : Subgroup G => (K : Set G)) h444
  have hI' : (I : Set G) = (LB : Set G) * (TB : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTBLB
  have hTI : ∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i := by
    intro t ht
    obtain ⟨s', hs', hst⟩ := hH.orbit_Tp t ht
    have hs'' : s' ∈ ((⁅X, B⁆ : Subgroup G) : Set G) * (TB : Set G) := by
      rw [← hTp']
      exact hs'
    obtain ⟨q, hq, b, hb, rfl⟩ := hs''
    exact ⟨b, Subgroup.mem_sup_right hb, hst.trans (hconjB b hb q hq)⟩
  have hIT : ∀ i ∈ I, ∃ t ∈ T, CFSG.conjugate L i = CFSG.conjugate L t := by
    intro i hi
    have hi' : i ∈ (LB : Set G) * (TB : Set G) := by
      rw [← hI']
      exact hi
    obtain ⟨l, hl, b, hb, rfl⟩ := hi'
    refine ⟨b, hTpT hb.1, ?_⟩
    rw [conjugate_mul, conjugate_eq_self_of_normalizes
      (hMpN ((perfectCore_le _).trans inf_le_left hl))]
  have hQLT : Q ≤ pCoreOf 2 (L ⊔ T) := by
    have hMpLT : Mp ≤ L ⊔ T := conjClosure_le fun t ht l hl =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right ht)
        (Subgroup.mem_sup_left hl)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right ht))
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Mp).trans hMpLT)
      ((_root_.sup_le (hLMp.trans Subgroup.le_normalizer) hTMp).trans hNQ) (pCoreOf_isPGroup 2 Mp)
  have hLI : (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) := by
    intro l hl
    have hlMp : l ∈ (LB : Set G) * (Q : Set G) := by
      rw [← hMpset]
      exact hLMp hl
    obtain ⟨a, ha, q, hq, rfl⟩ := hlMp
    exact ⟨a, Subgroup.mem_sup_left ha, q, hQLT hq, rfl⟩
  have hVBT : VB ≤ T := fun v hv =>
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le hH.sylow le_sup_right)
      (mem_quasithinOmegaOneCenter_iff.mp (hH.VB_le hv)).1
  have hVBQ : ∀ v ∈ VB, ∀ q ∈ Q, q * v = v * q := by
    intro v hv q hq
    have hQ' : q ∈ pCoreOf 2 (Mp ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Mp).trans le_sup_left)
        ((_root_.sup_le Subgroup.le_normalizer hTMp).trans hNQ) (pCoreOf_isPGroup 2 Mp) hq
    exact Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp
      (hH.VB_le hv)).2.1 q hQ'
  have hVBLB : VB ≤ Subgroup.normalizer (LB : Set G) := fun v hv =>
    normalizer_le_normalizer_perfectCore _ (mem_normalizer_inf (hTMp (hVBT hv))
      (mem_normalizer_centralizer_of_mem_normalizer (by
        have hvC : v ∈ Subgroup.centralizer (B : Set G) := by
          have h := hH.VB_centralizes
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
          exact h hv
        exact Subgroup.centralizer_le_normalizer _ hvC)))
  have hVBle : VB ≤ LB := by
    have h1 : ⁅VB, Mp⁆ ≤ ⁅VB, LB⁆ := by
      rw [Subgroup.commutator_le]
      intro v hv m hm
      have hm' : m ∈ (LB : Set G) * (Q : Set G) := by
        rw [← hMpset]
        exact hm
      obtain ⟨a, ha, q, hq, rfl⟩ := hm'
      have hqv := hVBQ v hv q hq
      have hqv' : q * v⁻¹ = v⁻¹ * q := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, hqv, ← mul_assoc, inv_mul_cancel, one_mul]
      have e : ⁅v, a * q⁆ = ⁅v, a⁆ := by
        simp only [commutatorElement_def]
        calc v * (a * q) * v⁻¹ * (a * q)⁻¹ = v * a * (q * v⁻¹) * q⁻¹ * a⁻¹ := by group
          _ = v * a * (v⁻¹ * q) * q⁻¹ * a⁻¹ := by rw [hqv']
          _ = v * a * v⁻¹ * a⁻¹ := by group
      rw [e]
      exact Subgroup.commutator_mem_commutator hv ha
    calc VB = ⁅VB, Mp⁆ := hH.VB_eq
      _ ≤ ⁅VB, LB⁆ := h1
      _ ≤ LB := commutator_le_right_of_le_normalizer hVBLB
  have hINV : I ≤ Subgroup.normalizer (VB : Set G) :=
    _root_.sup_le ((perfectCore_le _).trans (inf_le_left.trans
      (le_sup_left.trans hH.VB_normalized)))
      (inf_le_left.trans (hTpT.trans (le_sup_right.trans hH.VB_normalized)))
  have hVBO : VB ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 (hVBle.trans le_sup_left) hINV
      (hH.sylow.1.to_le hVBT)
  have hI1 : pCoreOf 2 I ≠ ⊥ := fun h => hH.VB_ne_bot (le_bot_iff.mp (hVBO.trans h.le))
  rcases h4213 G T M L I hH.simple hH.nonabelian hH.qtke hH.sylow hH.maxTwoLocal hH.T_le
      hH.maximal hH.faithful hH.L_le hH.quasisimple hIM hLI hTI hIT hI1 with hU | ⟨hC, hIrr⟩ | hO
  · exact hU
  · exfalso
    have hLn : M ≤ Subgroup.normalizer (L : Set G) := hC.1
    have hcl : conjClosure L T = L := conjClosure_eq_self (hH.T_le.trans hLn)
    have hVB1 : VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)) := by
      have := hH.VB_le
      rwa [hcl] at this
    have hVB2 : L ⊔ T ≤ Subgroup.normalizer (VB : Set G) := by
      have := hH.VB_normalized
      rwa [hcl] at this
    have hVB3 : VB = ⁅VB, L⁆ := by
      have := hH.VB_eq
      rwa [hcl] at this
    have hCB := hMod G T M L VB hH.simple hH.nonabelian hH.qtke hH.sylow hH.maxTwoLocal
      hH.T_le hH.maximal hH.faithful hH.L_le hH.quasisimple hLn hVB1 hVB2 hVB3 hH.VB_ne_bot hC
      hIrr
    exact s.not_concl (Or.inr ⟨hCB.1, hCB.2.1, Or.inl hCB.2.2⟩)
  · exfalso
    have hLn : M ≤ Subgroup.normalizer (L : Set G) := hO.1
    have hcl : conjClosure L T = L := conjClosure_eq_self (hH.T_le.trans hLn)
    have hVB1 : VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)) := by
      have := hH.VB_le
      rwa [hcl] at this
    have hVB2 : L ⊔ T ≤ Subgroup.normalizer (VB : Set G) := by
      have := hH.VB_normalized
      rwa [hcl] at this
    have hVB3 : VB = ⁅VB, L⁆ := by
      have := hH.VB_eq
      rwa [hcl] at this
    obtain ⟨hVBc, hBOF⟩ := hModO G T M L VB hH.simple hH.nonabelian hH.qtke hH.sylow
      hH.maxTwoLocal hH.T_le hH.maximal hH.faithful hH.L_le hH.quasisimple hLn hVB1 hVB2 hVB3
      hH.VB_ne_bot hO
    exact s.not_concl (Or.inr ⟨hLn, Or.inl ⟨2, le_rfl, hO.2.1⟩,
      Or.inr (Or.inl ⟨1, le_rfl, hO.2.1, hVBc, hBOF⟩)⟩)

end CFSG.Quasithin.H13.Ch4
