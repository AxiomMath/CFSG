module

public import CFSG.Quasithin.Vol2.Ch3xD15
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB513Solvable
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD14Proof
public import CFSG.Quasithin.EmptyFaithful.S151Dual
public import CFSG.Quasithin.EmptyFaithful.S1511
public import CFSG.Quasithin.Vol2.Ch3Sec1Cases

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Dual

variable {G : Type} [Group G] [Finite G]

theorem qOf_le_two_of_isSolvable (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (X : Subgroup (MulAut V)) (hsolv : Group.IsSolvable ↥X) (hne : X ≠ ⊥)
    (hO2 : pCoreOf 2 (X.map (dualAct V)) = ⊥)
    (hJ : X.map (dualAct V) =
      @ffJ (V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct V))) :
    qOf X ≤ 2 := by
  have hinj : Function.Injective (dualAct V) := dualAct_injective hV
  have hne' : X.map (dualAct V) ≠ ⊥ := fun h0 =>
    hne ((Subgroup.map_eq_bot_iff_of_injective X hinj).mp h0)
  have hO2' : CFSG.Open.pCore 2 ↥(X.map (dualAct V)) = ⊥ := by
    have h1 : (CFSG.Open.pCore 2 ↥(X.map (dualAct V))).map (X.map (dualAct V)).subtype = ⊥ := hO2
    exact (Subgroup.map_eq_bot_iff_of_injective _ (X.map (dualAct V)).subtype_injective).mp h1
  exact EmptyFaithfulMultiple.inputB513Solvable_holds V hV X hsolv hne' hO2' hJ

theorem qInt_le_two_of_dualFF_of_perfectCore {M₀ V : Subgroup G}
    (hred : IsTwoReducedIn M₀ V) (hperf : perfectCore M₀ ≤ Subgroup.centralizer (V : Set G))
    (hdual : IsDualFFInt M₀ V hred.2.2.1) : qInt M₀ V hred.2.2.1 ≤ 2 := by
  have hV := hred.2.2.1
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [pow_two] using hV.2 v v.2)
  have hinj : Function.Injective (dualAct ↥V) := dualAct_injective hV2
  set A : Subgroup (MulAut ↥V) := autOn M₀ V with hA
  set Xd : Subgroup (MulAut (↥V →* Multiplicative (ZMod 2))) := A.map (dualAct ↥V) with hXd
  set Jd : Subgroup (MulAut (↥V →* Multiplicative (ZMod 2))) :=
    @ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup Xd with hJd
  have hJle : Jd ≤ Xd := B6.ffJ_le Xd
  have hXN : Xd ≤ Subgroup.normalizer (Jd : Set _) := B6.le_normalizer_ffJ Xd
  have hO2A : pCoreOf 2 A = ⊥ := pCoreOf_autOn_eq_bot_of_isTwoReducedIn hred
  have hO2X : pCoreOf 2 Xd = ⊥ := pCoreOf_map_dualAct_eq_bot hV2 hO2A
  have hO2J : pCoreOf 2 Jd = ⊥ :=
    le_bot_iff.mp (hO2X ▸ pCoreOf_le_pCoreOf_of_normal hJle hXN)
  have hJJ : @ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup Jd = Jd :=
    ffJ_ffJ Xd
  set X : Subgroup (MulAut ↥V) := A ⊓ Jd.comap (dualAct ↥V) with hX
  have hXmap : X.map (dualAct ↥V) = Jd := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro j hj
      obtain ⟨a, haA, rfl⟩ := hJle hj
      exact ⟨a, ⟨haA, hj⟩, rfl⟩
  have hXA : X ≤ A := inf_le_left
  have hW'2 : ∀ f : ↥V →* Multiplicative (ZMod 2), f ^ 2 = 1 := by
    intro f
    refine DFunLike.ext _ _ fun v => ?_
    show (f v) ^ 2 = 1
    generalize f v = x
    revert x
    decide
  have hne : Jd ≠ ⊥ := by
    obtain ⟨A₀, hA₀⟩ := ((B1_4_5 hW'2 Xd).out 1 2).mp hdual
    intro hbot
    exact hA₀.2.1 (le_bot_iff.mp (hbot ▸ B6.le_ffJ hA₀))
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hXmap, hbot, Subgroup.map_bot]
  have hfix : X.map (dualAct ↥V) =
      @ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct ↥V)) :=
    hXmap.trans (hJJ.symm.trans (congrArg
      (@ffJ (↥V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup) hXmap).symm)
  have hsolvA : Group.IsSolvable ↥A := isSolvable_autOn_of_perfectCore_le hred.2.1 hperf
  have hsolvX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXA)
  have hq := qOf_le_two_of_isSolvable ↥V hV2 X hsolvX hXne (hXmap ▸ hO2J) hfix
  exact (kq_anti_group hXA 2).trans hq

end Dual

@[expose] def AS316SylowNonsolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M M₀ H V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T → InM T M →
    ∀ h : Hyp315 T M M₀ H V, V ≠ ⊥ →
      (¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) →
      ¬ qInt M₀ V h.reduced.2.2.1 ≤ 1 → ¬ IsDualFFInt M₀ V h.reduced.2.2.1 →
      V ≤ pCoreOf 2 H →
      ((pCoreOf 2 M₀ ⊓ pCoreOf 2 H).subgroupOf H).Normal →
      IsElemAbelian 2 (conjClosure V H) → ¬ Group.IsSolvable H →
      IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀)

section Core

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem theorem316_core (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK) (hE213 : E213Three)
    (hE215 : E215) (hS316 : AS316SylowNonsolvable) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : InM T M) (h : Hyp315 T M M₀ H V)
    (hdualStep : V ≠ ⊥ → IsDualFFInt M₀ V h.reduced.2.2.1 → qInt M₀ V h.reduced.2.2.1 ≤ 2) :
    (∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) ∨
      (¬ V ≤ pCoreOf 2 H ∧ qhatInt M₀ V h.reduced.2.2.1 ≤ 2 ∧
        (IsTISetIn V M → qhatInt M₀ V h.reduced.2.2.1 < 2)) ∨
      qInt M₀ V h.reduced.2.2.1 ≤ 2 := by
  by_cases h1 : ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)
  · exact Or.inl h1
  right
  by_cases hq : qInt M₀ V h.reduced.2.2.1 ≤ 2
  · exact Or.inr hq
  have hV0 : V ≠ ⊥ := by
    intro hV0
    apply h1
    have hRT : pCoreOf 2 M₀ = T := by
      rw [h.centralizer, hV0]
      ext x
      simp [Subgroup.mem_centralizer_iff]
    have hsyl : IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀) := by
      rw [hRT]
      exact B6.isSylowTwoOf_mono (isSylowTwoOf_of_isSylowTwo hT h.hStar.1.1) le_sup_right
        (sup_le (oTwoUpper_le H) h.hStar.1.1)
    exact h.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM hsyl
  have hD : D11Hyp M₀ H T V (H ⊓ M) :=
    h.toHyp315Base.d11Hyp hT hV0 (noNormal_of_not_exists h1)
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    hq (((isFFInt_iff_qInt_le_one _ _ _).mp hff).trans (by norm_num))
  have hsqH : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  by_cases hVH : V ≤ pCoreOf 2 H
  ·
    exfalso
    have hdual : ¬ IsDualFFInt M₀ V h.reduced.2.2.1 := fun hd => hq (hdualStep hV0 hd)
    rcases hD15 G M₀ H T V (H ⊓ M) hD hsqH with h1' | ⟨h2, -⟩ | h3 | ⟨h4, -, -⟩ |
      ⟨h5a, h5b, h5c, -, -, -⟩
    · exact h1' hVH
    · exact hq (h2.trans (by norm_num))
    · exact hdual h3
    · exact hq h4
    ·
      have hsyl : IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀) := by
        by_cases hsolv : Group.IsSolvable H
        · exact EmptyFaithfulMultiple.inputD14Solvable_holds G M₀ H T V (H ⊓ M) hD hVH h5c hdual
            hsolv (charTwo_of_inH' hK hT h.inH_H)
        · exact hS316 G T M M₀ H V hs hnab hK hT hM h hV0 h1
            (fun h1' => hq (h1'.trans (by norm_num))) hdual hVH h5a h5b hsolv
      exact h1 (h.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM hsyl)
  ·
    obtain ⟨h1', h2'⟩ := case_i hE213 hE215 hs hnab hK hT hM h.toHyp315Base hD hnff hVH
    exact Or.inl ⟨hVH, h1', h2'⟩

end Core

@[expose] def Theorem316StatementPerf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315 T M M₀ H V,
      perfectCore M₀ ≤ Subgroup.centralizer (V : Set G) →
      (∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
          M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) ∨
      (¬ V ≤ pCoreOf 2 H ∧ qhatInt M₀ V h.reduced.2.2.1 ≤ 2 ∧
        (IsTISetIn V M → qhatInt M₀ V h.reduced.2.2.1 < 2)) ∨
      qInt M₀ V h.reduced.2.2.1 ≤ 2

theorem theorem316StatementPerf_of_core_inputs (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hE213 : E213Three) (hE215 : E215) (hS316 : AS316SylowNonsolvable) :
    Theorem316StatementPerf := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM h hperf
  exact theorem316_core hC58 hD15 hE213 hE215 hS316 hs hnab hK hT hM h
    (fun _ hd => qInt_le_two_of_dualFF_of_perfectCore h.reduced hperf hd)

theorem theorem316Statement_of_core_inputs (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hB : B513) (hE213 : E213Three) (hE215 : E215) (hS316 : AS316SylowNonsolvable) :
    Theorem316Statement := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM h
  exact theorem316_core hC58 hD15 hE213 hE215 hS316 hs hnab hK hT hM h
    (fun hV0 hd => qInt_le_two_of_dualFF hB hs hnab hK h.reduced hV0 hd)

section Consumer

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_1_two_perf (h316 : Theorem316StatementPerf) (h1416 : StageLemma1416)
    {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    qhatOn M (VZ T M) ≤ 2 ∧ (2 < qOn M (VZ T M) → qhatOn M (VZ T M) < 2) := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hMT : InM (S : Subgroup G) M := hM.1.1
  have hW := isElemAbelian_VZ h hMT
  obtain ⟨H, hH⟩ := exists_isHStar h.inM_mc hMT (Ne.symm hM.2.1)
  obtain ⟨hbase, hII⟩ := lemma_15_1_1_one h hM hH
  have hmax : IsOrdMaximalIn (S : Subgroup G) (InM (S : Subgroup G)) M := hM.1
  obtain ⟨-, -, hauto, huniq⟩ := A57.main h.qtke.2.1 S hmax (Or.inl rfl)
  set M₀ : Subgroup G := M ⊓ Subgroup.normalizer
    (((S : Subgroup G) ⊓ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) : Subgroup G) :
      Set G) with hM₀
  have hyp : Hyp315 (S : Subgroup G) M M₀ H (VZ (S : Subgroup G) M) :=
    { toHyp315Base := hbase, «case» := Or.inr hII }
  have hred : IsTwoReducedIn M (VZ (S : Subgroup G) M) := (isTwoReducedIn_VZ h hMT).1
  have hperf : perfectCore M₀ ≤ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) :=
    (perfectCore_mono inf_le_left).trans ((h1416 G (S : Subgroup G) Mc h).1 M _ hMT hred)
  have hq := h316 G S h.simple h.nonabelian h.qtke h.sylow M M₀ H _ hMT hyp hperf
  have hVn := le_normalizer_VZ (S : Subgroup G) M
  have e1 : qhatOn M (VZ (S : Subgroup G) M) =
      qhatInt M₀ (VZ (S : Subgroup G) M) hyp.reduced.2.2.1 := by
    rw [qhatOn_eq hW]
    exact qhatInt_congr hW hauto
  have e2 : qOn M (VZ (S : Subgroup G) M) = qInt M₀ (VZ (S : Subgroup G) M) hyp.reduced.2.2.1 := by
    rw [qOn_eq hW]
    exact qInt_congr hW hauto
  rcases hq with ⟨R₀, hR₀, hR₀le, hR₀N⟩ | ⟨-, hq2, hTI⟩ | hq3
  · exfalso
    have hR₀p : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 M₀).to_le hR₀le
    obtain ⟨K, hK, hNK⟩ :=
      exists_maxTwoLocal_ge (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀, hR₀p, rfl⟩
    have hKM : K = M := huniq.2 K ⟨hK, (le_sup_left.trans hR₀N).trans hNK⟩
    exact hH.2.1 ((le_sup_right.trans hR₀N).trans (hNK.trans hKM.le))
  · have hTI' : IsTISetIn (VZ (S : Subgroup G) M) M :=
      ⟨VZ_le_self hMT.2, fun g hg hgn => absurd (hVn hg) hgn⟩
    refine ⟨e1 ▸ hq2, fun _ => e1 ▸ hTI hTI'⟩
  · refine ⟨(qhatOn_le_qOn hW).trans (e2 ▸ hq3), fun hlt => ?_⟩
    exact absurd (e2 ▸ hq3) (not_le_of_gt hlt)

theorem stageLemma1511_of_theorem316Perf (h316 : Theorem316StatementPerf) (h1416 : StageLemma1416) :
    StageLemma1511 := by
  intro G _ _ T Mc M h hM
  exact ⟨fun H hH => lemma_15_1_1_one h hM hH, lemma_15_1_1_two_perf h316 h1416 h hM⟩


end Consumer

end CFSG.Quasithin
