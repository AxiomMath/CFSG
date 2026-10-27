module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp8Codes
public import Certificates.Certificate899103
public import Certificates.Certificate899104
public import Certificates.Certificate899105
public import Certificates.Certificate899106
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sm8 sp8Z sp8T sp8E sp8Z0M sp8Z1M sp8Z2M sp8EM sp8TM)
open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb)
open Matrix

section Parts


theorem cert899103_parts : pairsChk899103 = true ∧ e0Chk899103 = true ∧ pChk899103 = true ∧
    cpChk899103 = true ∧ conjChk899103 = true :=
  Certificates.certificate899103

end Parts

section Parts


theorem cert899104_parts : n0Chk899104 = true ∧ fixChk899104 = true ∧ clsChk899104 = true ∧
    normChk899104 = true ∧ prodChk899104 = true :=
  Certificates.certificate899104

end Parts

section Parts


theorem cert899105_parts : czChk899105 = true ∧ colChk899105 = true ∧ e0cChk899105 = true ∧
    hypChk899105 = true ∧ f1Chk899105 = true ∧ e9Chk899105 = true :=
  Certificates.certificate899105

end Parts

section Parts


theorem cert899106_parts : u0Chk899106 = true ∧ zuChk899106 = true ∧ baseChk899106 = true ∧
    covChk899106 = true :=
  Certificates.certificate899106

end Parts

theorem codeS_of_dec8 {g : H8} {M : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hg : matS g = sm8 M)
    {c : List ℕ} (hc : Valid8 c) (h : dec8 c = M) : codeS g = c :=
  codeS_eq_of_decS hc (by rw [hg, decS, h])

theorem codeS_z0 : codeS (sp8Z 0) = z0S :=
  codeS_of_dec8 (M := sp8Z0M) rfl ⟨rfl, by decide⟩ (by decide +kernel)

theorem codeS_z1 : codeS (sp8Z 1) = z1S :=
  codeS_of_dec8 (M := sp8Z1M) rfl ⟨rfl, by decide⟩ (by decide +kernel)

theorem codeS_z2 : codeS (sp8Z 2) = z2S :=
  codeS_of_dec8 (M := sp8Z2M) rfl ⟨rfl, by decide⟩ (by decide +kernel)

theorem codeS_e : codeS sp8E = z3S :=
  codeS_of_dec8 (M := sp8EM) rfl ⟨rfl, by decide⟩ (by decide +kernel)

theorem codeS_t : codeS sp8T = tS :=
  codeS_of_dec8 (M := sp8TM) rfl ⟨rfl, by decide⟩ (by decide +kernel)

@[expose] noncomputable def zz : H8 := sp8Z 0 * sp8Z 1

@[expose] noncomputable def z012 : H8 := zz * sp8Z 2

@[expose] noncomputable def z0123 : H8 := z012 * sp8E

theorem codeS_zz : codeS zz = zzS := by
  rw [zz, codeS_mul, codeS_z0, codeS_z1]
  rfl

theorem codeS_z012 : codeS z012 = z012S := by
  rw [z012, codeS_mul, codeS_zz, codeS_z2]
  rfl

theorem codeS_z0123 : codeS z0123 = z0123S := by
  rw [z0123, codeS_mul, codeS_z012, codeS_e]
  rfl

theorem codeS_e_sq : codeS (sp8E ^ 2) = mulS z3S z3S := by
  rw [pow_two, codeS_mul, codeS_e]

@[expose] noncomputable def zE : Fin 4 → H8 := ![sp8Z 0, sp8Z 1, sp8Z 2, sp8E]

theorem codeS_zE (i : Fin 4) : codeS (zE i) = e0Gens.getD i [] := by
  fin_cases i
  · exact codeS_z0
  · exact codeS_z1
  · exact codeS_z2
  · exact codeS_e

theorem codeS_zE_mem (i : Fin 4) : codeS (zE i) ∈ e0Gens := by
  rw [codeS_zE]
  fin_cases i <;> simp [e0Gens]

theorem factorization_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem card_H8 : Nat.card H8 = 47377612800 :=
  CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.card_H8

theorem factorization_three_H8 : (Nat.card H8).factorization 3 = 5 := by
  rw [card_H8, show (47377612800 : ℕ) = 3 ^ 5 * 194969600 by norm_num]
  exact factorization_pow_mul Nat.prime_three (by norm_num)

theorem factorization_two_H8 : (Nat.card H8).factorization 2 = 16 := by
  rw [card_H8, show (47377612800 : ℕ) = 2 ^ 16 * 722925 by norm_num]
  exact factorization_pow_mul Nat.prime_two (by norm_num)

abbrev E0 : Subgroup H8 := subS e0Gens

abbrev P0 : Subgroup H8 := subS pGens

abbrev N0 : Subgroup H8 := subS n0Gens

abbrev CZ : Subgroup H8 := subS czGens

abbrev U0 : Subgroup H8 := subS u0Gens

theorem zE_mem_E0 (i : Fin 4) : zE i ∈ E0 := mem_subS_of_codeS (codeS_zE_mem i)

theorem sp8Z_mem_E0 (i : Fin 3) : sp8Z i ∈ E0 := by
  have h := zE_mem_E0 (Fin.castSucc i)
  fin_cases i <;> exact h

theorem sp8E_mem_E0 : sp8E ∈ E0 := zE_mem_E0 3

theorem zz_mem_E0 : zz ∈ E0 := mul_mem (sp8Z_mem_E0 0) (sp8Z_mem_E0 1)

theorem z012_mem_E0 : z012 ∈ E0 := mul_mem zz_mem_E0 (sp8Z_mem_E0 2)

theorem z0123_mem_E0 : z0123 ∈ E0 := mul_mem z012_mem_E0 sp8E_mem_E0

theorem zzS_eq : zzS = [16, 32, 4, 8, 17, 34, 64, 128] := by decide +kernel

theorem getD_mulS (A B : List ℕ) {j : ℕ} (hj : j < 8) :
    (mulS A B).getD j 0 = mv8 A (B.getD j 0) := by
  interval_cases j <;> rfl

theorem list_eq_of_getD {c c' : List ℕ} (h : c.length = 8) (h' : c'.length = 8)
    (e : ∀ j < 8, c.getD j 0 = c'.getD j 0) : c = c' := by
  refine List.ext_getElem (h.trans h'.symm) fun j hj hj' => ?_
  have := e j (h ▸ hj)
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this

theorem cols_of_comm_zz {c : List ℕ} (h : mulS c zzS = mulS zzS c) :
    c.getD 4 0 = yS (c.getD 0 0) ∧ c.getD 5 0 = yS (c.getD 1 0) ∧
    c.getD 2 0 = yS (c.getD 2 0) ∧ c.getD 3 0 = yS (c.getD 3 0) ∧
    c.getD 0 0 ^^^ c.getD 4 0 = yS (c.getD 4 0) ∧ c.getD 1 0 ^^^ c.getD 5 0 = yS (c.getD 5 0) ∧
    c.getD 6 0 = yS (c.getD 6 0) ∧ c.getD 7 0 = yS (c.getD 7 0) := by
  have e : ∀ j < 8, mv8 c (zzS.getD j 0) = yS (c.getD j 0) := fun j hj => by
    rw [← getD_mulS c zzS hj, h, getD_mulS zzS c hj]
    rfl
  have e0 := e 0 (by norm_num)
  have e1 := e 1 (by norm_num)
  have e2 := e 2 (by norm_num)
  have e3 := e 3 (by norm_num)
  have e4 := e 4 (by norm_num)
  have e5 := e 5 (by norm_num)
  have e6 := e 6 (by norm_num)
  have e7 := e 7 (by norm_num)
  simp only [zzS_eq, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4 e5 e6 e7
  simp +decide only [mv8, bt, if_true, if_false, Nat.xor_zero, Nat.zero_xor] at e0 e1 e2 e3
  simp +decide only [mv8, bt, if_true, if_false, Nat.xor_zero, Nat.zero_xor] at e4 e5 e6 e7
  exact ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩

theorem spS_getD {c : List ℕ} (h : spS c = true) {i j : ℕ} (hi : i < 8) (hj : j < 8) :
    b4N (c.getD i 0) (c.getD j 0) = (i + 4 == j || j + 4 == i) := by
  simp only [spS, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.2 i hi j hj

theorem codeS_comm {g h : H8} (e : g * h = h * g) : mulS (codeS g) (codeS h) =
    mulS (codeS h) (codeS g) :=
  (commute_iff_codeS g h).mp e

section Tables


theorem e0_parts : tabOK e0Gens (tabS e0Gens 81) 81 = true ∧
    allCheck (fun x => e0Gens.all (commS x)) (tabS e0Gens 81) = true ∧
    allCheck (fun x => mulS x (mulS x x) == one8) (tabS e0Gens 81) = true := by
  have h := cert899103_parts.2.1
  simp only [e0Chk899103, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem p_tabOK : tabOK pGens (tabS pGens 243) 243 = true := cert899103_parts.2.2.1

theorem n0_parts : tabOK n0Gens (tabS n0Gens 31104) 31104 = true ∧
    (n0Gens.all fun g => e0Gens.all fun z =>
      found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) (conjS g z) &&
        mulS g z == mulS (conjS g z) g) = true ∧
    (e0Gens.all fun z => found (tabS n0Gens 31104) (indexMap (tabS n0Gens 31104)) z) = true := by
  have h := cert899104_parts.1
  simp only [n0Chk899104, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cz_parts :
    tabOK czGens (tabS czGens 12960) 12960 = true ∧ czGens.all (commS zzS) = true := by
  have h := cert899105_parts.1
  simp only [czChk899105, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem u0_tabOK : tabOK u0Gens (tabS u0Gens 65536) 65536 = true := cert899106_parts.1

theorem card_E0 : Nat.card E0 = 81 := card_subS e0_parts.1

theorem card_P0 : Nat.card P0 = 243 := card_subS p_tabOK

theorem card_N0 : Nat.card N0 = 31104 := card_subS n0_parts.1

theorem card_CZ : Nat.card CZ = 12960 := card_subS cz_parts.1

theorem card_U0 : Nat.card U0 = 65536 := card_subS u0_tabOK

theorem E0_le_P0 : E0 ≤ P0 :=
  subS_le fun g hg => mem_subS_of_codeS (by
    simp only [e0Gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    simp only [pGens, List.mem_cons, List.not_mem_nil, or_false]
    tauto)

theorem sp8T_mem_P0 : sp8T ∈ P0 := mem_subS_of_codeS (by rw [codeS_t]; simp [pGens])

theorem E0_comm {x : H8} (hx : x ∈ E0) {y : H8} (hy : y ∈ E0) : x * y = y * x := by
  have hc := allCheck_mem e0_parts.1 e0_parts.2.1 hx
  suffices h : Commute x y from h.eq
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    have h := List.all_eq_true.mp hc (codeS g) hg
    exact (commute_iff_codeS x g).mpr (by simpa [commS] using h)
  | one => exact Commute.one_right x
  | mul a b _ _ ha hb => exact ha.mul_right hb
  | inv a _ ha => exact ha.inv_right

theorem E0_pow_three {x : H8} (hx : x ∈ E0) : x ^ 3 = 1 := by
  have hc := allCheck_mem e0_parts.1 e0_parts.2.2 hx
  simp only [beq_iff_eq] at hc
  apply codeS_injective
  rw [codeS_one, pow_three, codeS_mul, codeS_mul, hc]

theorem isElementaryAbelian_E0 : CFSG.IsElementaryAbelian 3 E0 where
  is_comm := ⟨fun a b => Subtype.ext (E0_comm a.2 b.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using E0_pow_three x.2)

theorem fix_parts : fixS one8 = 256 ∧ fixS zzS = 16 ∧ fixS z012S = 4 ∧ fixS z0123S = 1 ∧
    (∀ z ∈ e0Gens, fixS z = 64) ∧ commS tS z012S = true ∧ commS tS z0123S = true := by
  have h := cert899104_parts.2.1
  simp only [fixChk899104, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem fixCount_one : fixCount (1 : H8) = 256 := by
  rw [fixCount_eq_fixS, codeS_one, fix_parts.1]

theorem fixCount_zz : fixCount zz = 16 := by
  rw [fixCount_eq_fixS, codeS_zz, fix_parts.2.1]

theorem fixCount_z012 : fixCount z012 = 4 := by
  rw [fixCount_eq_fixS, codeS_z012, fix_parts.2.2.1]

theorem fixCount_z0123 : fixCount z0123 = 1 := by
  rw [fixCount_eq_fixS, codeS_z0123, fix_parts.2.2.2.1]

theorem fixCount_zE (i : Fin 4) : fixCount (zE i) = 64 := by
  rw [fixCount_eq_fixS]
  exact fix_parts.2.2.2.2.1 _ (codeS_zE_mem i)

theorem fixCount_e : fixCount sp8E = 64 := fixCount_zE 3

theorem sp8T_comm : sp8T * z012 = z012 * sp8T ∧ sp8T * z0123 = z0123 * sp8T := by
  refine ⟨(commute_iff_codeS _ _).mpr ?_, (commute_iff_codeS _ _).mpr ?_⟩
  · rw [codeS_t, codeS_z012]
    simpa [commS] using fix_parts.2.2.2.2.2.1
  · rw [codeS_t, codeS_z0123]
    simpa [commS] using fix_parts.2.2.2.2.2.2

theorem conj_of_cfoundS {gens : List (List ℕ)} {n : ℕ} (h : tabOK gens (tabS gens n) n = true)
    {m : Std.HashMap (List ℕ) ℕ} {a x : H8}
    (hf : cfoundS (tabS gens n) m (codeS a) (codeS x) = true) :
    ∃ g ∈ subS gens, g * a * g⁻¹ = x := by
  obtain ⟨t, ht, e⟩ := cfoundS_spec hf
  obtain ⟨g, hg, hgc⟩ := exists_of_lt h ht
  rw [← hgc] at e
  exact ⟨g, hg, conj_eq_of_mulS e⟩

theorem E0_cases {w : H8} (hw : w ∈ E0) : w = 1 ∨
    (fixCount w = 64 ∧ codeS w ∈ l1S ∧ ∃ n ∈ N0, n * sp8E * n⁻¹ = w ∨ n * sp8E ^ 2 * n⁻¹ = w) ∨
    (fixCount w = 16 ∧ ∃ n ∈ N0, n * zz * n⁻¹ = w) ∨
    (fixCount w = 4 ∧ ∃ n ∈ N0, n * z012 * n⁻¹ = w) ∨
    (fixCount w = 1 ∧ ∃ n ∈ N0, n * z0123 * n⁻¹ = w) := by
  have h := cert899104_parts.2.2.1
  simp only [clsChk899104] at h
  have hc := allCheck_mem e0_parts.1 h hw
  rw [← fixCount_eq_fixS] at hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
  have hT := n0_parts.1
  rcases hc with (((h1 | ⟨⟨h64, hl⟩, hc⟩) | ⟨h16, hc⟩) | ⟨h4, hc⟩) | ⟨h1', hc⟩
  · left
    exact codeS_injective (h1.trans codeS_one.symm)
  · right; left
    refine ⟨h64, hl, ?_⟩
    rcases hc with hc | hc
    · rw [← codeS_e] at hc
      obtain ⟨g, hg, e⟩ := conj_of_cfoundS hT hc
      exact ⟨g, hg, Or.inl e⟩
    · rw [← codeS_e_sq] at hc
      obtain ⟨g, hg, e⟩ := conj_of_cfoundS hT hc
      exact ⟨g, hg, Or.inr e⟩
  · right; right; left
    rw [← codeS_zz] at hc
    obtain ⟨g, hg, e⟩ := conj_of_cfoundS hT hc
    exact ⟨h16, g, hg, e⟩
  · right; right; right; left
    rw [← codeS_z012] at hc
    obtain ⟨g, hg, e⟩ := conj_of_cfoundS hT hc
    exact ⟨h4, g, hg, e⟩
  · right; right; right; right
    rw [← codeS_z0123] at hc
    obtain ⟨g, hg, e⟩ := conj_of_cfoundS hT hc
    exact ⟨h1', g, hg, e⟩

theorem mem_normalizer_of_map_le {K : Subgroup H8} {g : H8}
    (h : K.map (MulAut.conj g).toMonoidHom ≤ K) : g ∈ Subgroup.normalizer (K : Set H8) := by
  have he : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge h
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← he]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← he] at hx
    obtain ⟨y, hy, e⟩ := hx
    have : y = x := by
      simpa [MulAut.conj_apply] using e
    rwa [← this]

theorem N0_le_normalizer : N0 ≤ Subgroup.normalizer (E0 : Set H8) := by
  have hg := n0_parts.2.1
  refine subS_le fun γ hγ => mem_normalizer_of_map_le ?_
  change (Subgroup.closure {g | codeS g ∈ e0Gens}).map _ ≤ E0
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨z, hz, rfl⟩
  have h := List.all_eq_true.mp (List.all_eq_true.mp hg _ hγ) _ hz
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨w, hw, hwc⟩ := exists_of_found e0_parts.1 h.1
  rw [← hwc] at h
  have e := conj_eq_of_mulS h.2
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
  exact hw

@[expose] def colKey (c : List ℕ) : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
  ((c.getD 0 0, c.getD 1 0), (c.getD 2 0, c.getD 3 0, c.getD 6 0, c.getD 7 0))

attribute [local irreducible] cWS cW'S fixW condW condW'

@[expose] noncomputable def keyS (g : H8) : (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) := colKey (codeS g)

theorem card_cen_zz_le : Nat.card (Subgroup.centralizer ({zz} : Set H8)) ≤ 12960 := by
  have hcol := cert899105_parts.2.1
  simp only [colChk899105, Bool.and_eq_true, beq_iff_eq] at hcol
  have hcomm : ∀ g ∈ Subgroup.centralizer ({zz} : Set H8),
      mulS (codeS g) zzS = mulS zzS (codeS g) := fun g hg => by
    rw [← codeS_zz]
    exact codeS_comm (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hmem : ∀ g ∈ Subgroup.centralizer ({zz} : Set H8), keyS g ∈ cWS ×ˢ cW'S := by
    intro g hg
    have hc := cols_of_comm_zz (c := codeS g) (hcomm g hg)
    have r4 := hc.1
    have r5 := hc.2.1
    have r2 := hc.2.2.1
    have r3 := hc.2.2.2.1
    have r04 := hc.2.2.2.2.1
    have r15 := hc.2.2.2.2.2.1
    have r6 := hc.2.2.2.2.2.2.1
    have r7 := hc.2.2.2.2.2.2.2
    have hv := valid8_codeS g
    have hsp := spS_codeS g
    have lt : ∀ j, (codeS g).getD j 0 < 256 := fun j => getD_lt_of_valid8 hv j
    rw [keyS, colKey, Finset.mem_product, cWS, cW'S, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_product, Finset.mem_product, Finset.mem_product, fixW]
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨⟨lt 0, lt 1⟩, ?_⟩,
      ⟨⟨lt 2, r2.symm⟩, ⟨lt 3, r3.symm⟩, ⟨lt 6, r6.symm⟩, ⟨lt 7, r7.symm⟩⟩, ?_⟩
    · rw [condW, ← r4, ← r5, ← r04, ← r15,
        spS_getD hsp (i := 0) (j := 4) (by norm_num) (by norm_num),
        spS_getD hsp (i := 1) (j := 5) (by norm_num) (by norm_num),
        spS_getD hsp (i := 0) (j := 1) (by norm_num) (by norm_num),
        spS_getD hsp (i := 0) (j := 5) (by norm_num) (by norm_num),
        spS_getD hsp (i := 4) (j := 1) (by norm_num) (by norm_num),
        spS_getD hsp (i := 4) (j := 5) (by norm_num) (by norm_num)]
      simp
    · rw [condW', spS_getD hsp (i := 2) (j := 6) (by norm_num) (by norm_num),
        spS_getD hsp (i := 3) (j := 7) (by norm_num) (by norm_num),
        spS_getD hsp (i := 2) (j := 3) (by norm_num) (by norm_num),
        spS_getD hsp (i := 2) (j := 7) (by norm_num) (by norm_num),
        spS_getD hsp (i := 6) (j := 3) (by norm_num) (by norm_num),
        spS_getD hsp (i := 6) (j := 7) (by norm_num) (by norm_num)]
      decide
  have hinj : Set.InjOn keyS (Subgroup.centralizer ({zz} : Set H8) : Set H8) := by
    intro g hg g' hg' e
    simp only [keyS, colKey, Prod.mk.injEq] at e
    obtain ⟨⟨e0, e1⟩, e2, e3, e6, e7⟩ := e
    have hc := cols_of_comm_zz (c := codeS g) (hcomm g hg)
    have hc' := cols_of_comm_zz (c := codeS g') (hcomm g' hg')
    have r4 := hc.1
    have r5 := hc.2.1
    have r4' := hc'.1
    have r5' := hc'.2.1
    refine codeS_injective (list_eq_of_getD (valid8_codeS _).1 (valid8_codeS _).1 ?_)
    intro j hj
    interval_cases j
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · rw [r4, r4', e0]
    · rw [r5, r5', e1]
    · exact e6
    · exact e7
  have hle := Set.ncard_le_ncard_of_injOn keyS (fun g hg => Finset.mem_coe.mpr (hmem g hg)) hinj
    (Finset.finite_toSet (cWS ×ˢ cW'S))
  rw [Set.ncard_coe_finset, Finset.card_product, hcol.1, hcol.2] at hle
  rw [← Nat.card_coe_set_eq] at hle
  exact hle

theorem CZ_le_cen : CZ ≤ Subgroup.centralizer ({zz} : Set H8) := by
  refine subS_le fun γ hγ => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := List.all_eq_true.mp cz_parts.2 _ hγ
  simp only [commS, beq_iff_eq] at h
  rw [← codeS_zz] at h
  exact ((commute_iff_codeS _ _).mpr h).symm

theorem cen_zz_eq : Subgroup.centralizer ({zz} : Set H8) = CZ :=
  (Subgroup.eq_of_le_of_card_ge CZ_le_cen (by rw [card_CZ]; exact card_cen_zz_le)).symm

theorem card_cen_zz : Nat.card (Subgroup.centralizer ({zz} : Set H8)) = 12960 := by
  rw [cen_zz_eq, card_CZ]

theorem E0_le_N0 : E0 ≤ N0 :=
  subS_le fun _ hg => mem_subS_of_found n0_parts.1 (List.all_eq_true.mp n0_parts.2.2 _ hg)

theorem l1S_lines : ∀ a < 8, ∀ b < 8, a / 2 = b / 2 →
    l1S.getD b [] = l1S.getD a [] ∨ l1S.getD b [] = mulS (l1S.getD a []) (l1S.getD a []) := by
  decide +kernel

theorem zS_distinct : ∀ k < 4, ∀ l < 4, k ≠ l → e0Gens.getD l [] ≠ e0Gens.getD k [] ∧
    e0Gens.getD l [] ≠ mulS (e0Gens.getD k []) (e0Gens.getD k []) := by
  decide +kernel

theorem exists_l1S_index {c : List ℕ} (h : c ∈ l1S) : ∃ a < 8, l1S.getD a [] = c := by
  obtain ⟨a, ha, e⟩ := List.getElem_of_mem h
  exact ⟨a, ha, by rw [List.getD_eq_getElem _ _ ha, e]⟩

theorem mem_l1S_of_fix {w : H8} (hw : w ∈ E0) (h : fixCount w = 64) : codeS w ∈ l1S := by
  rcases E0_cases hw with h1 | ⟨-, hl, -⟩ | ⟨h16, -⟩ | ⟨h4, -⟩ | ⟨h1', -⟩
  · rw [h1, fixCount_one] at h
    norm_num at h
  · exact hl
  · rw [h] at h16
    norm_num at h16
  · rw [h] at h4
    norm_num at h4
  · rw [h] at h1'
    norm_num at h1'

theorem conj_zE_ne (g : H8) {k l : Fin 4} (hkl : k ≠ l) {a b : ℕ} (ha : a < 8) (hb : b < 8)
    (hea : l1S.getD a [] = codeS (g * zE k * g⁻¹)) (heb : l1S.getD b [] = codeS (g * zE l * g⁻¹)) :
    a / 2 ≠ b / 2 := by
  intro e
  have hd := zS_distinct k k.2 l l.2 (fun h => hkl (Fin.ext h))
  rcases l1S_lines a ha b hb e with h | h
  · rw [hea, heb] at h
    have h' : zE l = zE k := by
      have := codeS_injective h
      simpa using this
    exact hd.1 (by rw [← codeS_zE, ← codeS_zE, h'])
  · rw [hea, heb, ← codeS_mul] at h
    have h' : zE l = zE k * zE k := by
      have := codeS_injective h
      have e2 : g * zE k * g⁻¹ * (g * zE k * g⁻¹) = g * (zE k * zE k) * g⁻¹ := by group
      rw [e2] at this
      simpa using this
    exact hd.2 (by rw [← codeS_zE, ← codeS_zE, h', codeS_mul])

theorem normalizer_E0_le : Subgroup.normalizer (E0 : Set H8) ≤ N0 := by
  intro g hg
  have hw : ∀ k : Fin 4, g * zE k * g⁻¹ ∈ E0 := fun k =>
    (Subgroup.mem_normalizer_iff.mp hg _).mp (zE_mem_E0 k)
  have hl : ∀ k : Fin 4, ∃ a < 8, l1S.getD a [] = codeS (g * zE k * g⁻¹) := fun k =>
    exists_l1S_index (mem_l1S_of_fix (hw k) (by rw [fixCount_conj, fixCount_zE]))
  choose a ha ea using hl
  have hnd : [a 0 / 2, a 1 / 2, a 2 / 2, a 3 / 2].Nodup := by
    have d := fun k l (hkl : k ≠ l) => conj_zE_ne g hkl (ha k) (ha l) (ea k) (ea l)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨d 0 1 (by decide), d 0 2 (by decide), d 0 3 (by decide)⟩,
      ⟨d 1 2 (by decide), d 1 3 (by decide)⟩, d 2 3 (by decide)⟩
  have hn := cert899104_parts.2.2.2.1
  simp only [normChk899104, List.all_eq_true, List.mem_range] at hn
  have h := hn (a 0) (ha 0) (a 1) (ha 1) (a 2) (ha 2) (a 3) (ha 3)
  simp only [hnd, decide_true, Bool.not_true, Bool.false_or] at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨htlt, h0⟩, h1⟩, h2⟩, h3⟩ := h
    obtain ⟨n, hn0, hnc⟩ := exists_of_lt n0_parts.1 htlt
    rw [← hnc, ea] at h0 h1 h2 h3
    have hc0 : n * zE 0 * n⁻¹ = g * zE 0 * g⁻¹ := conj_eq_of_mulS (by rw [codeS_zE]; exact h0)
    have hc1 : n * zE 1 * n⁻¹ = g * zE 1 * g⁻¹ := conj_eq_of_mulS (by rw [codeS_zE]; exact h1)
    have hc2 : n * zE 2 * n⁻¹ = g * zE 2 * g⁻¹ := conj_eq_of_mulS (by rw [codeS_zE]; exact h2)
    have hc3 : n * zE 3 * n⁻¹ = g * zE 3 * g⁻¹ := conj_eq_of_mulS (by rw [codeS_zE]; exact h3)
    have hc : ∀ k : Fin 4, n * zE k * n⁻¹ = g * zE k * g⁻¹ := by
      intro k
      fin_cases k
      · exact hc0
      · exact hc1
      · exact hc2
      · exact hc3
    have hcomm : ∀ k : Fin 4, n⁻¹ * g * zE k = zE k * (n⁻¹ * g) := by
      intro k
      have e := hc k
      calc n⁻¹ * g * zE k = n⁻¹ * (g * zE k * g⁻¹) * g := by group
        _ = n⁻¹ * (n * zE k * n⁻¹) * g := by rw [e]
        _ = zE k * (n⁻¹ * g) := by group
    have hzz : n⁻¹ * g ∈ CZ := by
      rw [← cen_zz_eq, Subgroup.mem_centralizer_singleton_iff]
      have e0 : n⁻¹ * g * sp8Z 0 = sp8Z 0 * (n⁻¹ * g) := hcomm 0
      have e1 : n⁻¹ * g * sp8Z 1 = sp8Z 1 * (n⁻¹ * g) := hcomm 1
      show n⁻¹ * g * (sp8Z 0 * sp8Z 1) = sp8Z 0 * sp8Z 1 * (n⁻¹ * g)
      rw [← mul_assoc, e0, mul_assoc, e1, ← mul_assoc]
    have he := cert899105_parts.2.2.1
    dsimp only [e0cChk899105] at he
    have hx := allCheck_mem cz_parts.1 he hzz
    have hall : e0Gens.all (commS (codeS (n⁻¹ * g))) = true := by
      refine List.all_eq_true.mpr fun z hz => ?_
      obtain ⟨k, hk, rfl⟩ : ∃ k : Fin 4, codeS (zE k) = z := by
        simp only [e0Gens, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact ⟨0, codeS_z0⟩
        · exact ⟨1, codeS_z1⟩
        · exact ⟨2, codeS_z2⟩
        · exact ⟨3, codeS_e⟩
      simpa [commS] using codeS_comm (hcomm k)
    rw [hall] at hx
    simp only [Bool.not_true, Bool.false_or] at hx
    have hE : n⁻¹ * g ∈ E0 := mem_subS_of_found e0_parts.1 hx
    have e : g = n * (n⁻¹ * g) := by group
    rw [e]
    exact mul_mem hn0 (E0_le_N0 hE)
  · exact absurd h Bool.false_ne_true

theorem normalizer_E0_eq : Subgroup.normalizer (E0 : Set H8) = N0 :=
  le_antisymm normalizer_E0_le N0_le_normalizer

theorem card_normalizer_E0 : Nat.card (Subgroup.normalizer (E0 : Set H8)) = 31104 := by
  rw [normalizer_E0_eq, card_N0]

theorem card_le_filter {gens : List (List ℕ)} {n : ℕ} (h : tabOK gens (tabS gens n) n = true)
    {K : Subgroup H8} (hK : K ≤ subS gens) (q : List ℕ → Bool)
    (hq : ∀ g ∈ K, q (codeS g) = true) :
    Nat.card K ≤
      ((List.range (tabS gens n).size).filter fun s => q ((tabS gens n).getD s [])).length := by
  classical
  set L := (List.range (tabS gens n).size).filter fun s => q ((tabS gens n).getD s [])
  have hidx : ∀ g ∈ (K : Set H8), ∃ s < (tabS gens n).size, (tabS gens n).getD s [] = codeS g :=
    fun g hg => (mem_subS_iff h g).mp (hK hg)
  choose! f hf using hidx
  have hinj : Set.InjOn f (K : Set H8) := fun g hg g' hg' e =>
    codeS_injective (by rw [← (hf g hg).2, ← (hf g' hg').2, e])
  have hmaps : ∀ g ∈ (K : Set H8), f g ∈ (L.toFinset : Set ℕ) := fun g hg => by
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨(hf g hg).1, by rw [(hf g hg).2]; exact hq g hg⟩
  calc Nat.card K = (K : Set H8).ncard := Nat.card_coe_set_eq _
    _ ≤ (L.toFinset : Set ℕ).ncard := Set.ncard_le_ncard_of_injOn f hmaps hinj
        (Finset.finite_toSet _)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le _

theorem isPGroup_P0 : IsPGroup 3 P0 :=
  IsPGroup.of_card (n := 5) (by rw [card_P0]; norm_num)

theorem exists_le_conj_P0 {Q : Subgroup H8} (hQ : IsPGroup 3 Q) :
    ∃ g : H8, Q ≤ P0.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (by rw [card_P0, factorization_three_H8]; norm_num) hQ

theorem cp_parts : allCheck (fun p => found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) p ||
    decide (((List.range (tabS pGens 243).size).filter fun s =>
      commS p ((tabS pGens 243).getD s [])).length < 81)) (tabS pGens 243) = true := by
  have h := cert899103_parts.2.2.2.1
  dsimp only [cpChk899103] at h
  exact h

theorem card_inf_cen_lt {b : H8} (hb : b ∈ P0) (hbE : b ∉ E0) :
    Nat.card ↥(P0 ⊓ Subgroup.centralizer ({b} : Set H8)) < 81 := by
  have hc := allCheck_mem p_tabOK cp_parts hb
  have hf : found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) (codeS b) = false := by
    by_contra hf
    exact hbE (mem_subS_of_found e0_parts.1 (by simpa using hf))
  rw [hf, Bool.false_or, decide_eq_true_eq] at hc
  refine lt_of_le_of_lt (card_le_filter p_tabOK inf_le_left (fun c => commS (codeS b) c) ?_) hc
  intro g hg
  have hgb := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
  simpa [commS] using codeS_comm hgb.symm

theorem eq_E0_of_le_P0 {B : Subgroup H8} (hBP : B ≤ P0) (hB : IsElemAb 3 4 B) : B = E0 := by
  obtain ⟨hab, hcard⟩ := hB
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hle : B ≤ E0 := by
    intro b hb
    by_contra hbE
    have h81 : Nat.card B ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({b} : Set H8)) :=
      Subgroup.card_le_of_le (le_inf hBP fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy b hb))
    have hlt := card_inf_cen_lt (hBP hb) hbE
    have h81' : (81 : ℕ) ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer ({b} : Set H8)) :=
      (show (81 : ℕ) = 3 ^ 4 by norm_num) ▸ hcard ▸ h81
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_E0, hcard]; norm_num)

theorem conj_parts : allCheck (fun p => !(mulS p (mulS p p) == one8) || p == one8 ||
    found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) p ||
    conjL.any fun c => found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) (conjS c p) &&
      mulS c p == mulS (conjS c p) c) (tabS pGens 243) = true := by
  have h := cert899103_parts.2.2.2.2
  dsimp only [conjChk899103] at h
  exact h

theorem exists_conj_E0_of_P0 {p : H8} (hp : p ∈ P0) (h3 : orderOf p = 3) :
    ∃ y : H8, y * p * y⁻¹ ∈ E0 := by
  have hc := allCheck_mem p_tabOK conj_parts hp
  have hp3 : p ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one p
  have hcube : mulS (codeS p) (mulS (codeS p) (codeS p)) = one8 := by
    rw [← codeS_mul, ← codeS_mul, ← codeS_one, ← hp3, pow_three]
  have hp1 : codeS p ≠ one8 := by
    intro e
    rw [← codeS_one] at e
    have := codeS_injective e
    rw [this, orderOf_one] at h3
    norm_num at h3
  simp only [hcube, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne.mpr hp1,
    Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with hf | ⟨c, hc, hf, he⟩
  · exact ⟨1, by simpa using mem_subS_of_found e0_parts.1 hf⟩
  · have hs : spS c = true := by
      have h := cert899103_parts.1
      simp only [pairsChk899103, Bool.and_eq_true, List.all_eq_true] at h
      exact h.2 c hc
    obtain ⟨w, hw, hwc⟩ := exists_of_found e0_parts.1 hf
    rw [← hwc, ← codeS_mkS c hs] at he
    exact ⟨mkS c hs, by rw [conj_eq_of_mulS he]; exact hw⟩

theorem exists_conj_E0 {x : H8} (h3 : orderOf x = 3) : ∃ y : H8, y * x * y⁻¹ ∈ E0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
  obtain ⟨g, hg⟩ := exists_le_conj_P0 hp
  obtain ⟨p, hpP, hpx⟩ := hg (Subgroup.mem_zpowers x)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hpx
  have hp3 : orderOf p = 3 := by
    rw [← h3, ← hpx]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective p).symm
  obtain ⟨y, hy⟩ := exists_conj_E0_of_P0 hpP hp3
  refine ⟨y * g⁻¹, ?_⟩
  rw [← hpx]
  convert hy using 1
  group

theorem exists_ne_one_of_card {H K : Subgroup H8} (hH : H ≤ E0) (hK : K ≤ E0)
    (hcard : Nat.card E0 < Nat.card H * Nat.card K) : ∃ h ∈ H, h ∈ K ∧ h ≠ 1 := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective fun p : H × K =>
      (⟨(p.1 : H8) * p.2, mul_mem (hH p.1.2) (hK p.2.2)⟩ : E0) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ e
    have e' : (a : H8) * b = a' * b' := congrArg Subtype.val e
    have h1 : (a' : H8)⁻¹ * a = b' * (b : H8)⁻¹ := by
      calc (a' : H8)⁻¹ * a = (a' : H8)⁻¹ * (a * b) * (b : H8)⁻¹ := by group
        _ = (a' : H8)⁻¹ * (a' * b') * (b : H8)⁻¹ := by rw [e']
        _ = b' * (b : H8)⁻¹ := by group
    have hm : (a' : H8)⁻¹ * a = 1 :=
      hne _ (mul_mem (inv_mem a'.2) a.2) (h1 ▸ mul_mem b'.2 (inv_mem b.2))
    have ha : (a : H8) = a' := by
      rw [← one_mul (a : H8), ← mul_inv_cancel (a' : H8), mul_assoc, hm, mul_one]
    have hb : (b : H8) = b' := by
      rw [ha] at e'
      exact mul_left_cancel e'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at this
  omega

abbrev E9 (i j : ℕ) : Subgroup H8 := subS [e0Gens.getD i [], e0Gens.getD j []]

theorem e9_parts {i j : ℕ} (hij : (i, j) ∈ [(0, 1), (2, 3), (0, 3)]) :
    tabOK [e0Gens.getD i [], e0Gens.getD j []] (tabS [e0Gens.getD i [], e0Gens.getD j []] 9) 9 =
      true ∧
    allCheck (fun x => x == one8 || l1S.contains x || (w2S i j).contains x)
      (tabS [e0Gens.getD i [], e0Gens.getD j []] 9) = true := by
  have h := cert899105_parts.2.2.2.2.2
  dsimp only [e9Chk899105] at h
  have h' := List.all_eq_true.mp h (i, j) hij
  simp only [Bool.and_eq_true] at h'
  exact h'

theorem getD_mem_e0Gens {i : ℕ} (hi : i < 4) : e0Gens.getD i [] ∈ e0Gens := by
  rw [List.getD_eq_getElem _ _ (by simpa [e0Gens] using hi)]
  exact List.getElem_mem _

theorem E9_le_E0 (i j : ℕ) (hi : i < 4) (hj : j < 4) : E9 i j ≤ E0 := by
  refine subS_le fun g hg => mem_subS_of_codeS ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | hg <;> rw [hg]
  · exact getD_mem_e0Gens hi
  · exact getD_mem_e0Gens hj

theorem card_E9 {i j : ℕ} (hij : (i, j) ∈ [(0, 1), (2, 3), (0, 3)]) : Nat.card (E9 i j) = 9 :=
  card_subS (e9_parts hij).1

theorem E9_cases {i j : ℕ} (hij : (i, j) ∈ [(0, 1), (2, 3), (0, 3)]) {h : H8} (hh : h ∈ E9 i j)
    (h1 : h ≠ 1) : codeS h ∈ l1S ∨ codeS h ∈ w2S i j := by
  have hc := allCheck_mem (e9_parts hij).1 (e9_parts hij).2 hh
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
  rcases hc with (hc | hc) | hc
  · exact absurd (codeS_injective (hc.trans codeS_one.symm)) h1
  · exact Or.inl hc
  · exact Or.inr hc

theorem exists_mem_E9 {H : Subgroup H8} (hHE : H ≤ E0) (hH : Nat.card H = 27) {i j : ℕ}
    (hij : (i, j) ∈ [(0, 1), (2, 3), (0, 3)]) (hi : i < 4) (hj : j < 4) :
    ∃ h ∈ H, h ∈ E9 i j ∧ (codeS h ∈ l1S ∨ codeS h ∈ w2S i j) := by
  obtain ⟨h, hH', hK, h1⟩ := exists_ne_one_of_card hHE (E9_le_E0 i j hi hj)
    (by rw [card_E0, hH, card_E9 hij]; norm_num)
  exact ⟨h, hH', hK, E9_cases hij hK h1⟩

theorem hyp_parts : allCheck (fun x => (w2S 2 3).all fun a => (w2S 0 3).all fun b =>
    !(commS x a && commS x b) || found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) x)
    (tabS czGens 12960) = true := by
  have h := cert899105_parts.2.2.2.1
  dsimp only [hypChk899105] at h
  exact h

theorem f1_parts : spS f1S = true ∧ mulS f1S f1S = one8 ∧ commS f1S z0S = true ∧
    commS f1S z2S = true ∧ commS f1S z3S = true ∧ mulS (mulS f1S z1S) f1S = mulS z1S z1S := by
  have h := cert899105_parts.2.2.2.2.1
  simp only [f1Chk899105, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

@[expose] noncomputable def fl1 : H8 := mkS f1S f1_parts.1

theorem fl1_inv : fl1⁻¹ = fl1 := by
  rw [inv_eq_iff_mul_eq_one]
  apply codeS_injective
  rw [codeS_mul, fl1, codeS_mkS, codeS_one, f1_parts.2.1]

theorem fl1_comm_z0 : fl1 * sp8Z 0 = sp8Z 0 * fl1 :=
  (commute_iff_codeS _ _).mpr (by rw [fl1, codeS_mkS, codeS_z0]; simpa [commS] using f1_parts.2.2.1)

theorem fl1_comm_z2 : fl1 * sp8Z 2 = sp8Z 2 * fl1 :=
  (commute_iff_codeS _ _).mpr (by
    rw [fl1, codeS_mkS, codeS_z2]; simpa [commS] using f1_parts.2.2.2.1)

theorem fl1_comm_e : fl1 * sp8E = sp8E * fl1 :=
  (commute_iff_codeS _ _).mpr (by
    rw [fl1, codeS_mkS, codeS_e]; simpa [commS] using f1_parts.2.2.2.2.1)

theorem fl1_conj_z1 : fl1 * sp8Z 1 * fl1⁻¹ = sp8Z 1 * sp8Z 1 := by
  apply codeS_injective
  rw [fl1_inv, codeS_mul, codeS_mul, codeS_mul, fl1, codeS_mkS, codeS_z1]
  exact f1_parts.2.2.2.2.2

theorem isPGroup_U0 : IsPGroup 2 U0 :=
  IsPGroup.of_card (n := 16) (by rw [card_U0]; norm_num)

theorem exists_le_conj_U0 {Q : Subgroup H8} (hQ : IsPGroup 2 Q) :
    ∃ g : H8, Q ≤ U0.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (by rw [card_U0, factorization_two_H8]; norm_num) hQ

theorem u0Gens_spS : u0Gens.all spS = true := (tabOK_parts u0_tabOK).2.2.2.2

theorem mkS_mem_U0 {g : List ℕ} (hg : g ∈ u0Gens) :
    mkS g (List.all_eq_true.mp u0Gens_spS g hg) ∈ U0 :=
  mem_subS_of_codeS (by rw [codeS_mkS]; exact hg)

theorem zu_parts : allCheck (fun x => !(u0Gens.all (commS x)) || zuS.contains x)
    (tabS u0Gens 65536) = true ∧
    zuS.map (fun z => (fixS z, aTypeS z)) =
      [(256, true), (64, true), (128, false), (64, false)] := by
  have h := cert899106_parts.2.1
  simp only [zuChk899106, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem codeS_mem_zuS {z : H8} (hz : z ∈ U0) (hc : ∀ u ∈ U0, z * u = u * z) : codeS z ∈ zuS := by
  have h := allCheck_mem u0_tabOK zu_parts.1 hz
  have hall : u0Gens.all (commS (codeS z)) = true := List.all_eq_true.mpr fun g hg => by
    have e := codeS_comm (hc _ (mkS_mem_U0 hg))
    rw [codeS_mkS] at e
    simpa [commS] using e
  rw [hall, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
  exact h

theorem eq_of_conj_center {z₁ z₂ : H8} (h1 : z₁ ∈ U0) (h2 : z₂ ∈ U0)
    (hc₁ : ∀ u ∈ U0, z₁ * u = u * z₁) (hc₂ : ∀ u ∈ U0, z₂ * u = u * z₂) {g : H8}
    (hg : g * z₁ * g⁻¹ = z₂) : z₁ = z₂ := by
  have m1 := codeS_mem_zuS h1 hc₁
  have m2 := codeS_mem_zuS h2 hc₂
  have hfix : fixS (codeS z₁) = fixS (codeS z₂) := by
    rw [← fixCount_eq_fixS, ← fixCount_eq_fixS, ← hg, fixCount_conj]
  have hat : aTypeS (codeS z₁) = aTypeS (codeS z₂) := by
    have e := aType_conj z₁ g
    rw [hg, aType_iff, aType_iff] at e
    exact Bool.eq_iff_iff.mpr e.symm
  have hnd : (zuS.map fun z => (fixS z, aTypeS z)).Nodup := by
    rw [zu_parts.2]
    decide
  exact codeS_injective (List.inj_on_of_nodup_map hnd m1 m2 (by rw [hfix, hat]))

theorem cov_parts : (gpS.all fun gg => mulS (gg.take 8) (gg.drop 8) == one8) = true ∧
    allCheck (fun x => !(mulS x x == one8) || x == one8 ||
      match ((List.range ((repS.map fun r => orbS r gpS 256).toArray).size).foldl
          (fun m k => (((repS.map fun r => orbS r gpS 256).toArray).getD k #[]).foldl
            (fun m x => m.insert x k) m) ({} : Std.HashMap (List ℕ) ℕ)).get? x with
      | some k => decide (k < repS.length) &&
          found (((repS.map fun r => orbS r gpS 256).toArray).getD k #[])
            ((((repS.map fun r => orbS r gpS 256).toArray).map indexMap).getD k {}) x
      | none => false) (tabS u0Gens 65536) = true := by
  have h := cert899106_parts.2.2.2
  dsimp only [covChk899106] at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem base_parts : baseG.length = baseW.length ∧ repS.length = repBase.length ∧
    repS.all spS = true ∧
    (∀ j < baseG.length, spS (baseG.getD j []) = true ∧
      mulS (baseG.getD j []) zzS = mulS (baseW.getD j []) (baseG.getD j [])) ∧
    ∀ k < repS.length, repBase.getD k 0 < baseW.length ∧
      commS (repS.getD k []) (baseW.getD (repBase.getD k 0) []) = true := by
  have h := cert899106_parts.2.2.1
  simp only [baseChk899106, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hl1, hl2⟩, hsp⟩, hb⟩, hr⟩ := h
  exact ⟨hl1, hl2, List.all_eq_true.mpr hsp, hb, hr⟩

theorem gpS_spec : ∀ gg ∈ gpS, ∃ a : H8, decS (gg.take 8) = matS a ∧
    decS (gg.drop 8) = matS a⁻¹ := by
  intro gg hgg
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgg
  have hs : spS g = true := List.all_eq_true.mp u0Gens_spS g hg
  have hl : g.length = 8 := (valid8_of_spS hs).1
  have hinv := List.all_eq_true.mp cov_parts.1 _ hgg
  rw [(take_drop_eight hl).1, (take_drop_eight hl).2, beq_iff_eq] at hinv
  refine ⟨mkS g hs, by rw [(take_drop_eight hl).1, matS_mkS], ?_⟩
  rw [(take_drop_eight hl).2]
  have e := congrArg decS hinv
  rw [decS_mulS, decS_one8, ← matS_mkS g hs] at e
  calc decS (invS g) = matS (mkS g hs)⁻¹ * (matS (mkS g hs) * decS (invS g)) := by
        rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    _ = matS (mkS g hs)⁻¹ := by rw [e, Matrix.mul_one]

theorem getD_orbits {k : ℕ} (hk : k < repS.length) :
    ((repS.map fun r => orbS r gpS 256).toArray).getD k #[] = orbS (repS.getD k []) gpS 256 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, List.getD_eq_getElem _ _ hk]

theorem exists_conj_comm_zz {u : H8} (hu : u ∈ U0) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ y : H8, u * (y * zz * y⁻¹) = y * zz * y⁻¹ * u := by
  have hc := allCheck_mem u0_tabOK cov_parts.2 hu
  have hsq : mulS (codeS u) (codeS u) = one8 := by rw [← codeS_mul, hu2, codeS_one]
  have hne : codeS u ≠ one8 := fun e => hu1 (codeS_injective (e.trans codeS_one.symm))
  simp only [hsq, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne.mpr hne]
    at hc
  split at hc
  · rename_i k _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hk, hf⟩ := hc
    rw [getD_orbits hk] at hf
    obtain ⟨t, ht, et⟩ := found_spec hf
    have hmem : codeS u ∈ orbS (repS.getD k []) gpS 256 := by
      rw [← et, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
      exact Array.getElem_mem ht
    have hsr : spS (repS.getD k []) = true := by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.all_eq_true.mp base_parts.2.2.1 _ (List.getElem_mem hk)
    rcases orbS_spec (matS_mkS _ hsr).symm (valid8_of_spS hsr).1 gpS_spec 256 _ hmem with
      hz | ⟨v, hv⟩
    · exfalso
      rw [hz] at hsq
      exact absurd hsq (by decide)
    · rw [decS_codeS] at hv
      have huv : u = v * mkS _ hsr * v⁻¹ := matS_injective hv
      obtain ⟨hj, hcomm⟩ := base_parts.2.2.2.2 k hk
      set j := repBase.getD k 0
      have hjG : j < baseG.length := base_parts.1 ▸ hj
      obtain ⟨hsg, hgw⟩ := base_parts.2.2.2.1 j hjG
      set γ := mkS (baseG.getD j []) hsg
      have hw : decS (baseW.getD j []) = matS (γ * zz * γ⁻¹) := by
        have e := congrArg decS hgw
        rw [decS_mulS, decS_mulS, ← matS_mkS _ hsg, ← codeS_zz, decS_codeS] at e
        rw [map_mul, map_mul, e, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one,
          Matrix.mul_one]
      have hrw : mkS _ hsr * (γ * zz * γ⁻¹) = γ * zz * γ⁻¹ * mkS _ hsr := by
        have e : mulS (repS.getD k []) (baseW.getD j []) =
            mulS (baseW.getD j []) (repS.getD k []) := by
          simpa [commS] using hcomm
        have e' := congrArg decS e
        rw [decS_mulS, decS_mulS, ← matS_mkS _ hsr, hw, ← map_mul, ← map_mul] at e'
        exact matS_injective e'
      refine ⟨v * γ, ?_⟩
      rw [huv]
      calc v * mkS _ hsr * v⁻¹ * (v * γ * zz * (v * γ)⁻¹)
          = v * (mkS _ hsr * (γ * zz * γ⁻¹)) * v⁻¹ := by group
        _ = v * (γ * zz * γ⁻¹ * mkS _ hsr) * v⁻¹ := by rw [hrw]
        _ = v * γ * zz * (v * γ)⁻¹ * (v * mkS _ hsr * v⁻¹) := by group
  · exact absurd hc Bool.false_ne_true

end Tables

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
