module

public import CFSG.LocalAnalysis.StandardType.GGFinModelTorus
public import CFSG.LocalAnalysis.StandardType.GGFinModelTorusMem
public import CFSG.LocalAnalysis.StandardType.GGFinModelAdj
public import CFSG.LocalAnalysis.StandardType.GGFinModelBridge
public import CFSG.LocalAnalysis.StandardType.GGFinModelBridgeE6
public import CFSG.LocalAnalysis.StandardType.GGFinModelTw
public import CFSG.LocalAnalysis.StandardType.GGFinModelRoots
public import CFSG.LocalAnalysis.StandardType.GGFinModelPi
public import CFSG.LocalAnalysis.StandardType.GGFinModelEps
public import CFSG.LocalAnalysis.StandardType.GGLangData

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Input

theorem ggReidx_latPerm {R N : ℕ} (h : R = N) (π : Equiv.Perm (Fin R)) (v : Fin R → ℤ) :
    ggLangReidx h (latPerm π v) =
      fun j => ggLangReidx h v (((finCongr h).permCongr π).symm j) := by
  subst h
  rfl

theorem ggReidx_latPerm_permLattice {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (π : Equiv.Perm (Fin R)) (v : Fin R → ℤ) :
    ggLangReidx h (latPerm π v) = permLattice ((finCongr h).permCongr π) (ggLangReidx h v) :=
  ggReidx_latPerm h π v

theorem ggFixed_reidx {R N p : ℕ} (h : R = N) (π : Equiv.Perm (Fin R)) (z : Fin R → ZMod p)
    (hz : ∀ i, z (π i) = z i) (j : Fin N) :
    (fun k => z (Fin.cast h.symm k)) (((finCongr h).permCongr π) j) =
      (fun k => z (Fin.cast h.symm k)) j := by
  subst h
  exact hz j

@[expose] noncomputable def ggPhi (t : StatedLieTag) (f : ℕ) :
    ModGL (langTag t) GGL →* ModGL (langTag t) GGL :=
  match t with
  | .twistedE6 => twistHom TwistTag.E6 GGL (ggFrobT f)
  | _ => Units.map (entrywiseHom (ggFrobT f))

@[expose] def ggGraphLat (t : StatedLieTag) :
    (Fin (langTag t).rank → ℤ) → (Fin (langTag t).rank → ℤ) :=
  match t with
  | .twistedE6 => permLattice (TwistTag.perm .E6)
  | _ => id

@[expose] def GGWeylLaw (t : StatedLieTag) (p f : ℕ) (ht : GGExcFive t)
    (w : WeylGroup (langTag t)) : Prop :=
  ∀ u : Fin (langTag t).rank → ℤ, w • ggGraphLat t u =
    eps p f • permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) u

@[expose] noncomputable def ggZeta (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : GGLˣ :=
  (exists_zeta GGL hp hp2).choose

theorem ggZeta_order (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : orderOf (ggZeta p hp hp2) = p :=
  (exists_zeta GGL hp hp2).choose_spec

@[expose] noncomputable def ggIota (t : StatedLieTag) (n f : ℕ) (hf : 1 ≤ f) :
    GGKb t n f →* ModGL (langTag t) GGL :=
  match t with
  | .F4 =>
    ((baseChangeGL (ggRatEmb f)).comp (adjointGroup Tag.F4 (GaloisField 2 f)).subtype).comp
      (ggKbEquivF4 n f).toMonoidHom
  | .E6 =>
    ((baseChangeGL (ggRatEmb f)).comp (adjointGroup Tag.E6 (GaloisField 2 f)).subtype).comp
      (ggKbEquivE6 n f).toMonoidHom
  | .E7 =>
    ((baseChangeGL (ggRatEmb f)).comp (adjointGroup Tag.E7 (GaloisField 2 f)).subtype).comp
      (ggKbEquivE7 n f).toMonoidHom
  | .E8 =>
    ((baseChangeGL (ggRatEmb f)).comp (adjointGroup Tag.E8 (GaloisField 2 f)).subtype).comp
      (ggKbEquivE8 n f).toMonoidHom
  | .twistedE6 =>
    ((baseChangeGL (ggRatEmb (2 * f))).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype).comp
      (ggKbEquivTwE6 n f hf).toMonoidHom
  | _ => 1

theorem ggIota_E7_mk (n f : ℕ) (hf : 1 ≤ f) (k : (ggU .E7 n f).K) :
    ggIota .E7 n f hf (QuotientGroup.mk k) =
      baseChangeGL (ggRatEmb f)
        (e7Equiv (K := GaloisField 2 f) k : ModGL Tag.E7 (GaloisField 2 f)) :=
  rfl

theorem ggIota_E6_mk (n f : ℕ) (hf : 1 ≤ f) (k : (ggU .E6 n f).K) :
    ggIota .E6 n f hf (QuotientGroup.mk k) =
      baseChangeGL (ggRatEmb f)
        (e6Isogeny (GaloisField 2 f) k : ModGL Tag.E6 (GaloisField 2 f)) :=
  rfl

theorem ggIota_twistedE6_mk (n f : ℕ) (hf : 1 ≤ f) (k : (ggU .twistedE6 n f).K) :
    ggIota .twistedE6 n f hf (QuotientGroup.mk k) =
      baseChangeGL (ggRatEmb (2 * f))
        ((twistedE6Isogeny 2 f hf k : ↥⁅twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f), twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
  exact congrArg (baseChangeGL (ggRatEmb (2 * f))) (ggKbEquivTwE6_mk n f hf k)

private theorem permLattice_one_aux {τ : Tag} (u : Fin τ.rank → ℤ) :
    permLattice (1 : Equiv.Perm (Fin τ.rank)) u = u :=
  rfl

private theorem permCongr_one_aux {R N : ℕ} (h : R = N) :
    (finCongr h).permCongr (1 : Equiv.Perm (Fin R)) = (1 : Equiv.Perm (Fin N)) := by
  subst h
  rfl

private theorem permLattice_permCongr_one_aux {τ : Tag} {R : ℕ}
    (h : R = τ.rank) (u : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) u = u := by
  rw [permCongr_one_aux, permLattice_one_aux]

theorem ggWeylLaw_exists {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t) (hp : p.Prime)
    (hp2 : p ≠ 2) (hreg : GGExcRegime p f) : ∃ w : WeylGroup (langTag t), GGWeylLaw t p f ht w := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rcases eps_cases p f with he | he
    · refine ⟨1, fun u => ?_⟩
      rw [he, piB_F4, permLattice_permCongr_one_aux, one_smul, one_smul]
      rfl
    · obtain ⟨w, hw⟩ := ggWeylNeg_exists (τ := langTag .F4) (Or.inl rfl)
      refine ⟨w, fun u => ?_⟩
      rw [he, piB_F4, permLattice_permCongr_one_aux, neg_one_smul]
      exact hw u
  · by_cases h : p ∣ 2 ^ f - 1
    · have he : eps p f = 1 := (eps_eq_one_iff p f).2 h
      refine ⟨1, fun u => ?_⟩
      rw [he, piB_E6_of_dvd f h, permLattice_permCongr_one_aux, one_smul, one_smul]
      rfl
    · have he : eps p f = -1 :=
        (eps_eq_neg_one_iff hp hp2 f hreg).2 (hreg.resolve_left h)
      obtain ⟨w, hw⟩ := ggWeylE6_exists
      let w' : WeylGroup (langTag .E6) := w
      refine ⟨w', fun u => ?_⟩
      rw [he, piB_E6_of_not_dvd f h, neg_one_smul]
      exact hw u
  · rcases eps_cases p f with he | he
    · refine ⟨1, fun u => ?_⟩
      rw [he, piB_E7, permLattice_permCongr_one_aux, one_smul, one_smul]
      rfl
    · obtain ⟨w, hw⟩ := ggWeylNeg_exists (τ := langTag .E7) (Or.inr (Or.inl rfl))
      refine ⟨w, fun u => ?_⟩
      rw [he, piB_E7, permLattice_permCongr_one_aux, neg_one_smul]
      exact hw u
  · rcases eps_cases p f with he | he
    · refine ⟨1, fun u => ?_⟩
      rw [he, piB_E8, permLattice_permCongr_one_aux, one_smul, one_smul]
      rfl
    · obtain ⟨w, hw⟩ := ggWeylNeg_exists (τ := langTag .E8) (Or.inr (Or.inr rfl))
      refine ⟨w, fun u => ?_⟩
      rw [he, piB_E8, permLattice_permCongr_one_aux, neg_one_smul]
      exact hw u
  · by_cases h : p ∣ 2 ^ f + 1
    · have he : eps p f = -1 := (eps_eq_neg_one_iff hp hp2 f hreg).2 h
      obtain ⟨w, hw⟩ := ggWeylE6_exists
      let w' : WeylGroup (langTag .twistedE6) := w
      refine ⟨w', fun u => ?_⟩
      rw [he, piB_twistedE6_of_dvd f h, permLattice_permCongr_one_aux, neg_one_smul]
      have hγ2 : permLattice (TwistTag.perm .E6)
          (permLattice (TwistTag.perm .E6) u) = u := by
        ext j
        fin_cases j <;> rfl
      have hγ := hw (permLattice (TwistTag.perm .E6) u)
      rw [hγ2] at hγ
      exact hγ
    · have h1 : p ∣ 2 ^ f - 1 := hreg.resolve_right h
      have he : eps p f = 1 := (eps_eq_one_iff p f).2 h1
      refine ⟨1, fun u => ?_⟩
      rw [he, piB_twistedE6_of_not_dvd f h, one_smul, one_smul]
      rfl

theorem ggTorusData_of_datum {t : StatedLieTag} {n f p : ℕ} [NeZero p] (ht : GGExcFive t)
    (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) (w : WeylGroup (langTag t))
    (hw : GGWeylLaw t p f ht w) (D : LangDatum (langTag t) GGL) (hΦ : D.Φ = ggPhi t f)
    (hn : D.n = canonicalRep (coxeterSystem (langTag t)) GGL w) :
    GGTorusData (rank_eq_langTag f ht) p (piB t p f) D (ggIota t n f hf) (ggZeta p hp hp2) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · let hR : (ggU (absTag .F4) 6 f).D.rank = (langTag .F4).rank :=
      rank_eq_langTag f (Or.inl rfl)
    let π' : Equiv.Perm (Fin (langTag .F4).rank) := (finCongr hR).permCongr (piB .F4 p f)
    refine ⟨?_, ggZeta_order p hp hp2, ?_⟩
    · exact (ggLangPkg_adjoint (Or.inl rfl) hf D hΦ).of_equiv
        (ggKbEquivF4 n f)
    · intro z hz
      exact ggTorusMem_untw D w hΦ hn (ggZeta_order p hp hp2)
        (eps_cases p f) (eps_mul_pow_sub_one_dvd hreg) π' hw
        (fun k => z (Fin.cast hR.symm k)) (ggFixed_reidx hR (piB .F4 p f) z hz)
  · let hR : (ggU (absTag .E6) 6 f).D.rank = (langTag .E6).rank :=
      rank_eq_langTag f (Or.inr (Or.inl rfl))
    let π' : Equiv.Perm (Fin (langTag .E6).rank) := (finCongr hR).permCongr (piB .E6 p f)
    refine ⟨?_, ggZeta_order p hp hp2, ?_⟩
    · exact (ggLangPkg_adjoint (Or.inr (Or.inl rfl)) hf D
        hΦ).of_equiv (ggKbEquivE6 n f)
    · intro z hz
      exact ggTorusMem_untw D w hΦ hn (ggZeta_order p hp hp2)
        (eps_cases p f) (eps_mul_pow_sub_one_dvd hreg) π' hw
        (fun k => z (Fin.cast hR.symm k)) (ggFixed_reidx hR (piB .E6 p f) z hz)
  · let hR : (ggU (absTag .E7) 6 f).D.rank = (langTag .E7).rank :=
      rank_eq_langTag f (Or.inr (Or.inr (Or.inl rfl)))
    let π' : Equiv.Perm (Fin (langTag .E7).rank) := (finCongr hR).permCongr (piB .E7 p f)
    refine ⟨?_, ggZeta_order p hp hp2, ?_⟩
    · exact (ggLangPkg_adjoint (Or.inr (Or.inr (Or.inl rfl))) hf D
        hΦ).of_equiv (ggKbEquivE7 n f)
    · intro z hz
      exact ggTorusMem_untw D w hΦ hn (ggZeta_order p hp hp2)
        (eps_cases p f) (eps_mul_pow_sub_one_dvd hreg) π' hw
        (fun k => z (Fin.cast hR.symm k)) (ggFixed_reidx hR (piB .E7 p f) z hz)
  · let hR : (ggU (absTag .E8) 6 f).D.rank = (langTag .E8).rank :=
      rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    let π' : Equiv.Perm (Fin (langTag .E8).rank) := (finCongr hR).permCongr (piB .E8 p f)
    refine ⟨?_, ggZeta_order p hp hp2, ?_⟩
    · exact (ggLangPkg_adjoint (Or.inr (Or.inr (Or.inr rfl))) hf D
        hΦ).of_equiv (ggKbEquivE8 n f)
    · intro z hz
      exact ggTorusMem_untw D w hΦ hn (ggZeta_order p hp hp2)
        (eps_cases p f) (eps_mul_pow_sub_one_dvd hreg) π' hw
        (fun k => z (Fin.cast hR.symm k)) (ggFixed_reidx hR (piB .E8 p f) z hz)
  · let hR : (ggU (absTag .twistedE6) 6 f).D.rank = (langTag .twistedE6).rank :=
      rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    let π' : Equiv.Perm (Fin (langTag .twistedE6).rank) :=
      (finCongr hR).permCongr (piB .twistedE6 p f)
    refine ⟨?_, ggZeta_order p hp hp2, ?_⟩
    · exact (ggLangPkg_twE6_adjoint hf D
        hΦ).of_equiv
        (ggKbEquivTwE6 n f hf)
    · intro z hz
      exact ggTorusMem_tw D w hΦ hn (ggZeta_order p hp hp2)
        (eps_cases p f) (eps_mul_pow_sub_one_dvd hreg) π' hw
        (fun k => z (Fin.cast hR.symm k)) (ggFixed_reidx hR (piB .twistedE6 p f) z hz)

theorem ggRho_of_datum {t : StatedLieTag} {f p : ℕ} (ht : GGExcFive t)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) (w : WeylGroup (langTag t))
    (hw : GGWeylLaw t p f ht w) (D : LangDatum (langTag t) GGL) (hΦ : D.Φ = ggPhi t f)
    (hn : D.n = canonicalRep (coxeterSystem (langTag t)) GGL w)
    (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)) (hρ : FrobRootMap D ρ) :
    ∀ v ∈ (ggU (absTag t) 6 f).D.roots,
      ρ (ggLangReidx (rank_eq_langTag f ht) v) =
        eps p f • ggLangReidx (rank_eq_langTag f ht) (latPerm (piB t p f) v) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · intro v hv
    let hR : (ggU (absTag .F4) 6 f).D.rank = (langTag .F4).rank :=
      rank_eq_langTag f (Or.inl rfl)
    let π' : Equiv.Perm (Fin (langTag .F4).rank) := (finCongr hR).permCongr (piB .F4 p f)
    have hv' : IsRoot (langTag .F4) (ggLangReidx hR v) :=
      (mem_roots_iff_isRoot f (Or.inl rfl) v).1 hv
    have h := ggRho_untw D w hΦ hn π' hw ρ hρ hv'
    rw [ggReidx_latPerm_permLattice hR (piB .F4 p f) v]
    exact h
  · intro v hv
    let hR : (ggU (absTag .E6) 6 f).D.rank = (langTag .E6).rank :=
      rank_eq_langTag f (Or.inr (Or.inl rfl))
    let π' : Equiv.Perm (Fin (langTag .E6).rank) := (finCongr hR).permCongr (piB .E6 p f)
    have hv' : IsRoot (langTag .E6) (ggLangReidx hR v) :=
      (mem_roots_iff_isRoot f (Or.inr (Or.inl rfl)) v).1 hv
    have h := ggRho_untw D w hΦ hn π' hw ρ hρ hv'
    rw [ggReidx_latPerm_permLattice hR (piB .E6 p f) v]
    exact h
  · intro v hv
    let hR : (ggU (absTag .E7) 6 f).D.rank = (langTag .E7).rank :=
      rank_eq_langTag f (Or.inr (Or.inr (Or.inl rfl)))
    let π' : Equiv.Perm (Fin (langTag .E7).rank) := (finCongr hR).permCongr (piB .E7 p f)
    have hv' : IsRoot (langTag .E7) (ggLangReidx hR v) :=
      (mem_roots_iff_isRoot f (Or.inr (Or.inr (Or.inl rfl))) v).1 hv
    have h := ggRho_untw D w hΦ hn π' hw ρ hρ hv'
    rw [ggReidx_latPerm_permLattice hR (piB .E7 p f) v]
    exact h
  · intro v hv
    let hR : (ggU (absTag .E8) 6 f).D.rank = (langTag .E8).rank :=
      rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    let π' : Equiv.Perm (Fin (langTag .E8).rank) := (finCongr hR).permCongr (piB .E8 p f)
    have hv' : IsRoot (langTag .E8) (ggLangReidx hR v) :=
      (mem_roots_iff_isRoot f (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) v).1 hv
    have h := ggRho_untw D w hΦ hn π' hw ρ hρ hv'
    rw [ggReidx_latPerm_permLattice hR (piB .E8 p f) v]
    exact h
  · intro v hv
    let hR : (ggU (absTag .twistedE6) 6 f).D.rank = (langTag .twistedE6).rank :=
      rank_eq_langTag f (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    let π' : Equiv.Perm (Fin (langTag .twistedE6).rank) :=
      (finCongr hR).permCongr (piB .twistedE6 p f)
    have hv' : IsRoot (langTag .twistedE6) (ggLangReidx hR v) :=
      (mem_roots_iff_isRoot f (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) v).1 hv
    have h := ggRho_tw D w hΦ hn π' hw ρ hρ hv'
    rw [ggReidx_latPerm_permLattice hR (piB .twistedE6 p f) v]
    exact h

end Input

end CFSG.StandardType.GGFinModel
