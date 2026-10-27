module

public import CFSG.Quasithin.Vol2.Ch11SecO11G
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.E2TwoProofSporJ2
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import Certificates.Certificate3029
public import Certificates.Certificate3139
public import Certificates.Certificate3167
public import Certificates.Certificate3172
public import Certificates.Certificate4034
public import Certificates.Certificate4075
public import Certificates.Certificate4102
public import Certificates.Certificate4140
public import Certificates.Certificate4142
public import Certificates.Certificate4143
public import Certificates.Certificate7117
public import Certificates.Certificate7125
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin.E2P.SporB

theorem odd_mul_two_pow_eq {a b k m : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (h : a * 2 ^ k = b * 2 ^ m) : a = b := by
  have key : ∀ {a b k m : ℕ}, a % 2 = 1 → a * 2 ^ k = b * 2 ^ m → ¬ k < m := by
    intro a b k m ha h hkm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkm
    have h' : a * 2 ^ k = (b * 2 ^ (d + 1)) * 2 ^ k := by
      rw [h, show k + d + 1 = (d + 1) + k by ring, pow_add, mul_assoc]
    have h2 := Nat.eq_of_mul_eq_mul_right (by positivity) h'
    rw [h2, pow_succ, ← mul_assoc, Nat.mul_mod_left] at ha
    exact absurd ha (by norm_num)
  rcases lt_trichotomy k m with hkm | rfl | hkm
  · exact absurd hkm (key ha h)
  · exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  · exact absurd hkm (key hb h.symm)

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_member_fifteen {S : Subgroup Γ} {Y : ℕ → Subgroup Γ} {L : Array ℕ} {N k : ℕ}
    (hS2 : IsPGroup 2 S)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k) (hΓ : Nat.card Γ = N * 2 ^ k)
    (hodd : ∀ j < L.size + 1, latSz L N j % 2 = 1) {B : Subgroup Γ} (hB : IsL24Sub S B) :
    ∃ j ≤ L.size, B ⊔ S = memberOrTop L.size Y j ∧ latSz L N j = 15 := by
  obtain ⟨j, hj, hZ⟩ := hall (B ⊔ S) le_sup_right
  obtain ⟨m, hm⟩ := card_sup hS2 hB
  refine ⟨j, hj, hZ, ?_⟩
  have h := list_card hcard hΓ j
  rw [← hZ, hm] at h
  exact odd_mul_two_pow_eq (hodd j (by omega)) (by norm_num) h.symm

theorem l24Unique_of_list {S : Subgroup Γ} {Y : ℕ → Subgroup Γ} {L : Array ℕ} {N k : ℕ}
    (hS2 : IsPGroup 2 S)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k) (hΓ : Nat.card Γ = N * 2 ^ k)
    (hodd : ∀ j < L.size + 1, latSz L N j % 2 = 1)
    (h15 : ∀ i < L.size + 1, ∀ j < L.size + 1, latSz L N i = 15 → latSz L N j = 15 → i = j) :
    L24Unique S := by
  intro B₁ B₂ h₁ h₂
  obtain ⟨j₁, hj₁, e₁, l₁⟩ := exists_member_fifteen hS2 hall hcard hΓ hodd h₁
  obtain ⟨j₂, hj₂, e₂, l₂⟩ := exists_member_fifteen hS2 hall hcard hΓ hodd h₂
  obtain rfl := h15 j₁ (by omega) j₂ (by omega) l₁ l₂
  exact eq_of_sup_eq hS2 h₁ h₂ (e₁.trans e₂.symm)

variable {Q : Type} [Group Q] [Finite Q]

section J2

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB.J2Lat CFSG.Sporadic.J2


noncomputable def j2CtxO : LatCtx ↥J 315 (List ℕ) := j2Ctx

theorem isSylowTwoOf_j2 : IsSylowTwoOf j2CtxO.S ⊤ := by
  have hN : j2CtxO.D.O.lbl.size = 4725 := j2_O_size
  refine K1.isSylowTwoOf_top_iff.mpr ⟨j2CtxO.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index j2CtxO.S
  rw [j2CtxO.S_card, j2CtxO.hΓ, hN] at h1
  have h2 : j2CtxO.S.index = 4725 := by
    have : j2CtxO.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem l24Unique_j2 (hQ : IsSporadic .J2 Q) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) :
    L24Unique S := by
  obtain ⟨e⟩ := hQ
  have hL : j2CtxO.D.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] := j2_Om_size
  have hN : j2CtxO.D.O.lbl.size = 4725 := j2_O_size
  refine l24Unique_of_equiv isSylowTwoOf_j2 ?_ ⟨e.trans nativeEquiv⟩ hS
  exact l24Unique_of_list (N := 4725) j2CtxO.S_isPGroup (lat_all j2CtxO hL) (lat_card j2CtxO hL)
    (by rw [j2CtxO.hΓ, hN]) (by decide +kernel) (by decide +kernel)

end J2

theorem l24Unique_hs
    (hQ : IsSporadic .HS Q) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : L24Unique S := by
  obtain ⟨e⟩ := hQ
  refine l24Unique_of_equiv HS.hs_S_sylow ?_
    ⟨e.trans (CFSG.Sporadic.SmallF2.seedEquiv HS.hs_facts.toBaseFacts)⟩ hS
  exact l24Unique_of_list (L := #[1, 15, 21, 3, 3]) (N := 86625) (k := 9) HS.hsCtx.S_isPGroup
    HS.hs_complete (fun j hj => by rw [HS.hs_member_card j hj]; norm_num)
    (by rw [HS.hs_card]; ring) (by decide +kernel) (by decide +kernel)

theorem l24Unique_ru
    (hQ : IsSporadic .Ru Q) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : L24Unique S := by
  obtain ⟨e⟩ := hQ
  refine l24Unique_of_equiv Ru.ru_S_sylow ?_
    ⟨e.trans (CFSG.Sporadic.SmallF2.seedEquiv Ru.ru_facts.toBaseFacts)⟩ hS
  exact l24Unique_of_list (L := #[1, 15, 21, 3, 3]) (N := 8906625) (k := 14)
    Ru.ruCtx.S_isPGroup Ru.ru_complete (fun j hj => by rw [Ru.ru_member_card j hj]; norm_num)
    (by rw [Ru.ru_card]; ring) (by decide +kernel) (by decide +kernel)

section M22

open CFSG.Quasithin.H.MathieuLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m22a m22b card_M22 m22_hyp)


noncomputable def m22CtxO : LatCtx ↥CFSG.Blueprint.NativeSporadic.M22 22 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful m22_delta_valid m22_ta m22_tb m22_hyp.gen m22_sGens.1
    m22_sGens.2 3465 (by rw [card_M22]; norm_num) Certificates.certificate7117.choose_spec.1

theorem m22CtxO_O_size : m22CtxO.D.O.lbl.size = 3465 := LatFactsK.ctx_O_size ..

theorem isSylowTwoOf_m22 : IsSylowTwoOf m22CtxO.S ⊤ := by
  have hN : m22CtxO.D.O.lbl.size = 3465 := m22CtxO_O_size
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m22CtxO.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m22CtxO.S
  rw [m22CtxO.S_card, m22CtxO.hΓ, hN] at h1
  have h2 : m22CtxO.S.index = 3465 := by
    have : m22CtxO.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem l24Unique_m22 (hQ : IsSporadic .M22 Q) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) :
    L24Unique S := by
  obtain ⟨e⟩ := hQ
  have hL : m22CtxO.D.Om.map (fun o => o.lbl.size) = #[1, 45, 3, 15, 3] :=
    Certificates.certificate7117.choose_spec.2
  have hN : m22CtxO.D.O.lbl.size = 3465 := m22CtxO_O_size
  refine l24Unique_of_equiv isSylowTwoOf_m22 ?_ ⟨e⟩ hS
  exact l24Unique_of_list (N := 3465) m22CtxO.S_isPGroup (lat_all m22CtxO hL)
    (lat_card m22CtxO hL) (by rw [m22CtxO.hΓ, hN]) (by decide +kernel) (by decide +kernel)

theorem l24Unique_hatM22 (hQ : IsHat Q (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) : L24Unique S := by
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (inferInstance : Finite ↥CFSG.Blueprint.NativeSporadic.M22)
  exact l24Unique_of_isHat hQ (fun _ hS' => l24Unique_m22 ⟨MulEquiv.refl _⟩ hS') hS

end M22

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
