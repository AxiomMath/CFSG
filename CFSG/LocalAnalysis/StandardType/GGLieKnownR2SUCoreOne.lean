module

import all CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUNC
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.RankThree.GF2n.Tim79aSURootS1
public import CFSG.Timmesfeld.Transvection.ModelSUGen
public import CFSG.Timmesfeld.Transvection.ModelSUGeometry
public import CFSG.Timmesfeld.Transvection.ModelSUTransitiveWitt
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.StandardType.LieKnownR2.PSU

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Timmesfeld.Transvection.ModelRank
open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
open CFSG.LieType.Universal.Unitary

private theorem l10scsub_toStd_neg (n : ℕ) (v : Fin (n / 2) → ℤ) :
    toStd n (-v) = -toStd n v := by
  funext a
  by_cases h : Even n
  · simp only [toStd, h, ite_true, Symplectic.toStd, Pi.neg_apply]
    split_ifs <;> ring
  · simp only [toStd, h, ite_false, Pi.neg_apply]
    split_ifs <;> ring

private theorem l10scsub_uTrans_one_ne_one {F : Type} [Field F] {σ : F ≃+* F}
    {n : ℕ} {v : Fin n → F} (hv : v ≠ 0) : uTrans σ v 1 ≠ 1 := by
  intro h
  have h1 : (1 : Matrix (Fin n) (Fin n) F) + uNil σ v = (1 : Matrix (Fin n) (Fin n) F) := by
    simpa [uTrans] using h
  have hnil : uNil σ v = 0 := add_left_cancel (h1.trans (add_zero 1).symm)
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  obtain ⟨b, hb⟩ := Function.ne_iff.1 (uRow_ne_zero σ hv)
  have h0 : v a * uRow σ v b = 0 := by
    have := congrFun (congrFun hnil a) b
    simpa only [uNil, Matrix.vecMulVec_apply, Matrix.zero_apply] using this
  exact mul_ne_zero ha hb h0

private theorem l10scsub_suGen {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1)) :
    SUGenStmt F f n := by
  intro L hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm3 : (n, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h3 : n = 3 := congrArg Prod.fst h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    have h2' : 2 ^ f = 2 ^ 1 := by rw [h2, pow_one]
    exact hnf ⟨h3, Nat.pow_right_injective (le_refl 2) h2'⟩
  rw [eq_top_iff, ← closure_uTrans_eq_top (p := 2) hF (by omega) hm3, Subgroup.closure_le]
  rintro x ⟨v, c, hv, hc, hx⟩
  obtain ⟨X, hX⟩ := exists_isUTransGroup
    (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF) hv
  exact hL v X hv hX ((hX.1 x).2 ⟨c, hc, hx⟩)

private theorem l10scsub_coreOne_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hl : GGLongRoot (Unitary.rootDatum hF n) β) :
    pCoreOf 2 (Subgroup.normalizer
        ((((Unitary.rootDatum hF n).rootGroup β) :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))) ⊔
      (((Unitary.rootDatum hF n).rootGroup β) ⊔ (Unitary.rootDatum hF n).rootGroup (-β)) = ⊤ := by
  have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
  have htr : ∀ c, unitaryInvolution F 2 f c = c →
      ∃ d, d + unitaryInvolution F 2 f d = c :=
    fun _ hc => CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hF hc
  have hG : SUGenStmt F f n := l10scsub_suGen hF hn hnf
  have hP : SUPartnerStmt (unitaryInvolution F 2 f) n :=
    fun ha haa => exists_isotropic_partner hσ htr ha haa
  have hB : SUBothStmt (unitaryInvolution F 2 f) n :=
    fun ha hu haa huu => exists_isotropic_both hσ htr ha hu haa huu
  have hβ : β ∈ (Unitary.rootDatum hF n).roots := l10su4_mem_roots hF hl
  obtain ⟨i, hi, hβi⟩ := l10su4_exists_weight_of_ggLongRoot hF hβ hl
  let β' : Fin (n / 2) → ℤ := β
  have hβ'i : toStd n β' = 2 • weight n i := hβi
  let v : Fin n → F := Pi.single i 1
  let w : Fin n → F := Pi.single (Fin.rev i) 1
  have hri : Fin.rev i ≠ i := fun h => hi h.symm
  have hrineg : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hi.symm
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [v] at this
  have hw : w ≠ 0 := by
    intro h
    have := congrFun h (Fin.rev i)
    simp [w] at this
  have hvv : uForm (unitaryInvolution F 2 f) v v = 0 :=
    uForm_single_self (σ := unitaryInvolution F 2 f) hi
  have hww : uForm (unitaryInvolution F 2 f) w w = 0 := by
    change uForm (unitaryInvolution F 2 f) (Pi.single (Fin.rev i) 1)
      (Pi.single (Fin.rev i) 1) = 0
    exact uForm_single_self (σ := unitaryInvolution F 2 f) hrineg
  have hT : IsUTransGroup (unitaryInvolution F 2 f) v
      ((Unitary.rootDatum hF n).rootGroup β) := by
    change IsUTransGroup (unitaryInvolution F 2 f) (Pi.single i 1)
      (Unitary.rootGroup (unitaryInvolution F 2 f) hσ n β')
    exact isUTransGroup_rootGroup_long' hσ hi hβ'i
  have hβ'mi : toStd n (-β') = 2 • weight n (Fin.rev i) := by
    rw [l10scsub_toStd_neg, hβ'i, CFSG.LieType.Universal.Unitary.SUExtras.weight_rev',
      smul_neg]
  have hTm : IsUTransGroup (unitaryInvolution F 2 f) w
      ((Unitary.rootDatum hF n).rootGroup (-β)) := by
    change IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (Fin.rev i) 1)
      (Unitary.rootGroup (unitaryInvolution F 2 f) hσ n (-β'))
    exact isUTransGroup_rootGroup_long' hσ hrineg hβ'mi
  have hvw : uForm (unitaryInvolution F 2 f) v w = 1 := by
    change uForm (unitaryInvolution F 2 f) (Pi.single i 1) (Pi.single (Fin.rev i) 1) = 1
    rw [uForm_single_right, Fin.rev_rev, Pi.single_eq_same, map_one]
  have h1tr : (1 : F) + unitaryInvolution F 2 f 1 = 0 := by
    rw [map_one, CharTwo.add_self_eq_zero]
  have hne : ¬ Commuting ((Unitary.rootDatum hF n).rootGroup β)
      ((Unitary.rootDatum hF n).rootGroup (-β)) := by
    intro hc
    rcases IsUTransGroup.uForm_eq_zero hσ one_ne_zero h1tr hT hTm hv hc with h0 | ⟨l, hl'⟩
    · rw [hvw] at h0
      exact one_ne_zero h0
    · rw [hl', uForm_smul_right, hvv, mul_zero] at hvw
      exact one_ne_zero hvw.symm
  obtain ⟨g, hgv⟩ := exists_suMat_mulVec_eq_of_iso (p := 2) hF hn hv hvv hw hww
  have hTg : IsUTransGroup (unitaryInvolution F 2 f) w
      (conjSub ((Unitary.rootDatum hF n).rootGroup β) g) := by
    have h := hT.conjSub g
    rwa [hgv] at h
  have hconj : conjSub ((Unitary.rootDatum hF n).rootGroup β) g =
      (Unitary.rootDatum hF n).rootGroup (-β) := hTg.eq hTm
  obtain ⟨x, hx⟩ := hTm.2 1 h1tr
  have hxmem : x ∈ (Unitary.rootDatum hF n).rootGroup (-β) := (hTm.1 x).2 ⟨1, h1tr, hx⟩
  have hx1 : x ≠ 1 := by
    intro hxeq
    apply l10scsub_uTrans_one_ne_one (σ := unitaryInvolution F 2 f) hw
    rw [← hx, hxeq, map_one]
  have hgen := CFSG.RankThree.GF2n.Tim79a.uRad_sup_zpowers_eq_top hF hG hP hB hv hvv hT
    (by rw [hconj]; exact hne) (by rwa [hconj]) hx1
  have huRad : uRad (unitaryInvolution F 2 f) v ≤ pCoreOf 2 (Subgroup.normalizer
      (((Unitary.rootDatum hF n).rootGroup β :
        Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
        Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))) :=
    uRad_le_pCoreOf hσ hv hT
  refine le_antisymm le_top ?_
  rw [← hgen]
  refine sup_le (huRad.trans le_sup_left) ?_
  exact (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hxmem)).trans le_sup_right

private theorem l10scsub_coreOne_SU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hl : GGLongRoot (Unitary.rootDatum hF n) β)
    (u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
    pCoreOf 2 (Subgroup.normalizer
        ((((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))) ⊔
      (((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom ⊔
        ((Unitary.rootDatum hF n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom) = ⊤ := by
  have h1 := l10scsub_coreOne_one hF hn hnf hl
  have h2 := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) h1
  rw [Subgroup.map_sup, Subgroup.map_sup,
    ← GGRootNorm.pCoreOf_map_mulEquiv (MulAut.conj u)
      (Subgroup.normalizer (((Unitary.rootDatum hF n).rootGroup β :
        Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
        Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))),
    ← GGRootNorm.normalizer_map_mulEquiv (MulAut.conj u) ((Unitary.rootDatum hF n).rootGroup β),
    Subgroup.map_top_of_surjective (MulAut.conj u).toMonoidHom
      (MulAut.conj u).surjective] at h2
  exact h2

private theorem l10scsub_coreOne_of_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    (L : LieUniversal)
    (hL : L = ⟨↥(Unitary.SU (unitaryInvolution F 2 f) n), Unitary.rootDatum hc n⟩)
    {β : Fin L.D.rank → ℤ} (hl : GGLongRoot L.D β) (u : L.K) {Rr Rm Q : Subgroup L.K}
    (hRr : Rr = ggRootSub L.D (MonoidHom.id L.K) β u)
    (hRm : Rm = ggRootSub L.D (MonoidHom.id L.K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set L.K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  subst hL
  subst hRr hRm hQ
  simpa only [ggRootSub, Subgroup.map_id] using l10scsub_coreOne_SU hc hn hnf hl u

private theorem l10scsub_false_of_mem_roots_trivialUniversal (L : LieUniversal)
    (hL : L = trivialUniversal) {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) : False := by
  subst hL
  rcases hβ with ⟨w, i, -⟩ | ⟨w, i, -, -⟩ <;> exact i.elim0

theorem coreOne_PSU_long
    {n f : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hl : GGLongRoot (ggU .PSU n f).D β)
    (u : (ggU .PSU n f).K) {Rr Rm Q : Subgroup (ggU .PSU n f).K}
    (hRr : Rr = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSU n f).D (MonoidHom.id (ggU .PSU n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSU n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hf1 : 1 ≤ f
  · have e : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) n⟩ := by
      simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
    exact l10scsub_coreOne_of_eq (card_galoisField_two_mul 2 f hf1) hn hnf _ e hl u hRr hRm hQ
  · exfalso
    have e : ggU .PSU n f = trivialUniversal := by
      simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
    obtain ⟨w, γ₀, hγ₀, -, -⟩ := hl
    exact l10scsub_false_of_mem_roots_trivialUniversal _ e hγ₀

end CFSG.StandardType.LieKnownR2.PSU
