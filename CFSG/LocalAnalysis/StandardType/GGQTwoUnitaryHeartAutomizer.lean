module

public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryCav
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.StandardType.QTwoUnitaryCav

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartOne.KFU
open CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.TableBUE
open CFSG.StandardType.TableBUD CFSG.StandardType.UnitTB CFSG.StandardType.UnitAct
open CFSG.StandardType.InndiagSU CFSG.StandardType.QTwoUnitary
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)


variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {h : UnitaryFieldData 2 1 K} {Q : GL (Fin d) K}
  {hQ : Q ∈ primeFormUnitary h (idGram K d)}

theorem qTwoFramePerm_moves_of_weight_ne
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))} (he : e ∈ E)
    {σ : Fin d → Kˣ}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd3 : 3 ≤ d)
    (hdq : (d, 2 ^ 1) ≠ (3, 2))
    (hσn : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1)
    (hfr : TableBUD.FrameAct h Q hQ e σ)
    {i j : Fin d} (hij : i ≠ j) (hσij : σ i ≠ σ j) :
    qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap i j) * e *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap i j))⁻¹ ≠ e := by
  classical
  intro hfixed
  have hfr' : TableBUD.FrameAct h Q hQ e (σ ∘ ⇑(Equiv.swap i j).symm) := by
    have h := frameAct_qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
      (hσn := hσn) (he := hfr) (π := Equiv.swap i j)
    rwa [hfixed] at h
  have hσn' : ∀ k, (((σ ∘ ⇑(Equiv.swap i j).symm) k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 :=
    fun k => hσn ((Equiv.swap i j).symm k)
  obtain ⟨c, hc⟩ := TableBUD.FrameAct.eq_smul (K := K) (n := 1) (d := d)
    (h := h) (Q := Q) (hQ := hQ) hK hd3 hdq (p := 3) Nat.prime_three
    (by norm_num) hσn hσn' hfr hfr'
  have h2lt : ({i, j} : Finset (Fin d)).card < (Finset.univ : Finset (Fin d)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hcard : ({i, j} : Finset (Fin d)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card h2lt
  have hki : k ≠ i := fun hk' => hk (by simp [hk'])
  have hkj : k ≠ j := fun hk' => hk (by simp [hk'])
  have hswap_k : (Equiv.swap i j) k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
  have hsymm_k : (Equiv.swap i j).symm k = k := by
    rw [Equiv.symm_swap]
    exact hswap_k
  have hc1 : c = 1 := by
    have h := hc k
    rw [Function.comp_apply, hsymm_k] at h
    have h1 : (1 : Kˣ) * σ k = c * σ k := by simpa using h
    exact (mul_right_cancel h1).symm
  have hsymm_i : (Equiv.swap i j).symm i = j := by
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hji : σ j = σ i := by
    have h := hc i
    rw [Function.comp_apply, hsymm_i, hc1, one_mul] at h
    exact h
  exact hσij hji.symm


theorem four_dvd_ggAutomizer_frameBlock
    (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hd : 6 ≤ d) (h3d : 3 ∣ d)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))}
    (hfr : ∀ e ∈ E, ∃ σ : Fin d → Kˣ,
      σ ⟨0, by omega⟩ = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct h Q hQ e σ)
    (hinner : ∀ e ∈ E, ∃ u : ↥(unitarySU 2 1 K d),
      e = MulAut.conj (frameMk h Q hQ u))
    (hcardW : Nat.card ↥(TableBUD.frameWeights h Q hQ (by omega) 3 E) = 3 ^ (d - 2))
    (I : Finset (Fin d)) (hI : 4 ≤ I.card) :
    4 ∣ Nat.card ↥(ggAutomizer
      (((TableBUE.blockSU (K := K) (n := 1) I).map (frameMk h Q hQ)).map
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))) E) := by
  classical
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro hcon
    have hd3' : d = 3 := congrArg Prod.fst hcon
    omega
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hpq3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  obtain ⟨T, hTI, hTcard⟩ := Finset.exists_subset_card_eq hI
  obtain ⟨a, b, c, d4, hab, hac, had4, hbc, hbd4, hcd4, hTeq⟩ :=
    Finset.card_eq_four.mp hTcard
  have haI : a ∈ I := hTI (by rw [hTeq]; simp)
  have hbI : b ∈ I := hTI (by rw [hTeq]; simp)
  have hcI : c ∈ I := hTI (by rw [hTeq]; simp)
  have hd4I : d4 ∈ I := hTI (by rw [hTeq]; simp)
  have hcardUnits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
    norm_num
  haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hcardUnitsF : Fintype.card Kˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, hcardUnits]
  have hcardWbig : 1 < Nat.card ↥(TableBUD.frameWeights h Q hQ (by omega) 3 E) := by
    rw [hcardW]
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (d - 2) := pow_le_pow_right' (by norm_num) (by omega)
  have hNontriv : Nontrivial ↥(TableBUD.frameWeights h Q hQ (by omega) 3 E) :=
    (Finite.one_lt_card_iff_nontrivial).mp hcardWbig
  obtain ⟨w0, hw0mem, hw0ne⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one
      (TableBUD.frameWeights h Q hQ (by omega) 3 E)).mp hNontriv
  have hw0' : w0 ∈ TableBUD.frameWeights h Q hQ (by omega) 3 E := hw0mem
  rw [TableBUD.frameWeights, Subgroup.mem_mk] at hw0'
  obtain ⟨hw00, hw03, hw0n, e0, he0, hfr0⟩ := hw0'
  let z : Fin d := ⟨0, by omega⟩
  have hw0z : w0 z = 1 := hw00
  obtain ⟨k, hk⟩ : ∃ k : Fin d, w0 k ≠ 1 := by
    by_contra h
    push Not at h
    exact hw0ne (funext fun i => h i)
  have hkz : k ≠ z := by
    intro h
    exact hk (by rw [h]; exact hw0z)
  let S : Finset (Fin d) := (Finset.univ.erase k).erase z
  have hS_card : 4 ≤ S.card := by
    have hz_mem : z ∈ Finset.univ.erase k := by
      simp [Finset.mem_erase, hkz.symm]
    have hk_mem : k ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ k
    dsimp only [S]
    rw [Finset.card_erase_of_mem hz_mem, Finset.card_erase_of_mem hk_mem,
      Finset.card_univ, Fintype.card_fin]
    omega
  have hImage_lt : (S.image w0).card < S.card := by
    have hle : (S.image w0).card ≤ 3 := by
      calc (S.image w0).card ≤ Fintype.card Kˣ := Finset.card_le_univ _
        _ = 3 := hcardUnitsF
    omega
  obtain ⟨m, hmS, m', hmS', hmm', hval⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt (f := w0) (s := S) hImage_lt
  have hmz : m ≠ z := (Finset.mem_erase.mp hmS).1
  have hmk : m ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hmS).2).1
  have hm'z : m' ≠ z := (Finset.mem_erase.mp hmS').1
  have hm'k : m' ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hmS').2).1
  let f : Fin 4 → Fin d := ![k, z, m, m']
  let g : Fin 4 → Fin d := ![a, b, c, d4]
  have hf : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp [f, hkz, hkz.symm, hmk, hmk.symm,
      hm'k, hm'k.symm, hmz, hmz.symm, hm'z, hm'z.symm, hmm', hmm'.symm] at hxy ⊢
  have hg : Function.Injective g := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp [g, hab, hab.symm, hac, hac.symm,
      had4, had4.symm, hbc, hbc.symm, hbd4, hbd4.symm, hcd4, hcd4.symm] at hxy ⊢
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hτk : τ k = a := by simpa [f, g] using hτ 0
  have hτz : τ z = b := by simpa [f, g] using hτ 1
  have hτm : τ m = c := by simpa [f, g] using hτ 2
  have hτm' : τ m' = d4 := by simpa [f, g] using hτ 3
  let e1 : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) :=
    qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ * e0 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ)⁻¹
  have hNτ : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ ∈
      Subgroup.normalizer (E : Set (MulAut
        (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))) :=
    qTwoFramePerm_mem_normalizer (E := E) hK hd3 hdq hp3 hpq3 hinner hfr h3d hcardW τ
  have he1 : e1 ∈ E := by
    have h := (Subgroup.mem_normalizer_iff.mp hNτ e0).mp he0
    simpa [e1] using h
  have hfr1 : TableBUD.FrameAct h Q hQ e1 (w0 ∘ ⇑τ.symm) := by
    have h := frameAct_qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
      (hσn := hw0n) (he := hfr0) (π := τ)
    simpa [e1] using h
  have hτsymm_a : τ.symm a = k :=
    τ.injective (by rw [τ.apply_symm_apply, ← hτk])
  have hτsymm_b : τ.symm b = z :=
    τ.injective (by rw [τ.apply_symm_apply, ← hτz])
  have hτsymm_c : τ.symm c = m :=
    τ.injective (by rw [τ.apply_symm_apply, ← hτm])
  have hτsymm_d : τ.symm d4 = m' :=
    τ.injective (by rw [τ.apply_symm_apply, ← hτm'])
  have hw1a : (w0 ∘ ⇑τ.symm) a = w0 k := by rw [Function.comp_apply, hτsymm_a]
  have hw1b : (w0 ∘ ⇑τ.symm) b = 1 := by rw [Function.comp_apply, hτsymm_b, hw0z]
  have hw1c : (w0 ∘ ⇑τ.symm) c = w0 m := by rw [Function.comp_apply, hτsymm_c]
  have hw1d : (w0 ∘ ⇑τ.symm) d4 = w0 m' := by rw [Function.comp_apply, hτsymm_d]
  have hw1ab : (w0 ∘ ⇑τ.symm) a ≠ (w0 ∘ ⇑τ.symm) b := by
    rw [hw1a, hw1b]
    exact hk
  have hw1cd : (w0 ∘ ⇑τ.symm) c = (w0 ∘ ⇑τ.symm) d4 := by
    rw [hw1c, hw1d, hval]
  have hw1n : ∀ k, (((w0 ∘ ⇑τ.symm) k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 :=
    fun k => hw0n (τ.symm k)
  have hmoved1 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap a b) * e1 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap a b))⁻¹ ≠ e1 :=
    qTwoFramePerm_moves_of_weight_ne (h := h) (Q := Q) (hQ := hQ) (E := E)
      he1 hK hd3 hdq hw1n hfr1 hab hw1ab
  let g2 : Fin 4 → Fin d := ![c, d4, a, b]
  have hg2 : Function.Injective g2 := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp [g2, hab, hab.symm, hac, hac.symm,
      had4, had4.symm, hbc, hbc.symm, hbd4, hbd4.symm, hcd4, hcd4.symm] at hxy ⊢
  obtain ⟨τ2, hτ2⟩ := Equiv.Perm.exists_extending_pair f g2 hf hg2
  have hτ2k : τ2 k = c := by simpa [f, g2] using hτ2 0
  have hτ2z : τ2 z = d4 := by simpa [f, g2] using hτ2 1
  have hτ2m : τ2 m = a := by simpa [f, g2] using hτ2 2
  have hτ2m' : τ2 m' = b := by simpa [f, g2] using hτ2 3
  let e2 : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) :=
    qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ2 * e0 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ2)⁻¹
  have hNτ2 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) τ2 ∈
      Subgroup.normalizer (E : Set (MulAut
        (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))))) :=
    qTwoFramePerm_mem_normalizer (E := E) hK hd3 hdq hp3 hpq3 hinner hfr h3d hcardW τ2
  have he2 : e2 ∈ E := by
    have h := (Subgroup.mem_normalizer_iff.mp hNτ2 e0).mp he0
    simpa [e2] using h
  have hfr2 : TableBUD.FrameAct h Q hQ e2 (w0 ∘ ⇑τ2.symm) := by
    have h := frameAct_qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
      (hσn := hw0n) (he := hfr0) (π := τ2)
    simpa [e2] using h
  have hτ2symm_c : τ2.symm c = k :=
    τ2.injective (by rw [τ2.apply_symm_apply, ← hτ2k])
  have hτ2symm_d : τ2.symm d4 = z :=
    τ2.injective (by rw [τ2.apply_symm_apply, ← hτ2z])
  have hw2c : (w0 ∘ ⇑τ2.symm) c = w0 k := by rw [Function.comp_apply, hτ2symm_c]
  have hw2d : (w0 ∘ ⇑τ2.symm) d4 = 1 := by rw [Function.comp_apply, hτ2symm_d, hw0z]
  have hw2cd : (w0 ∘ ⇑τ2.symm) c ≠ (w0 ∘ ⇑τ2.symm) d4 := by
    rw [hw2c, hw2d]
    exact hk
  have hw2n : ∀ k, (((w0 ∘ ⇑τ2.symm) k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 :=
    fun k => hw0n (τ2.symm k)
  have hmoved2 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c d4) * e2 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c d4))⁻¹ ≠ e2 :=
    qTwoFramePerm_moves_of_weight_ne (h := h) (Q := Q) (hQ := hQ) (E := E)
      he2 hK hd3 hdq hw2n hfr2 hcd4 hw2cd
  have hw1fix : (w0 ∘ ⇑τ.symm) ∘ ⇑(Equiv.swap c d4).symm = (w0 ∘ ⇑τ.symm) := by
    funext i
    dsimp only [Function.comp_apply]
    by_cases hic : i = c
    · subst hic
      rw [Equiv.symm_swap, Equiv.swap_apply_left]
      exact hw1cd.symm
    · by_cases hid : i = d4
      · subst hid
        rw [Equiv.symm_swap, Equiv.swap_apply_right]
        exact hw1cd
      · have hfix : (Equiv.swap c d4) i = i := Equiv.swap_apply_of_ne_of_ne hic hid
        rw [Equiv.symm_swap, hfix]
  have hfix2 : qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c d4) * e1 *
      (qTwoFramePerm (h := h) (Q := Q) (hQ := hQ) (Equiv.swap c d4))⁻¹ = e1 := by
    have hact := frameAct_qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
      (hσn := hw1n) (he := hfr1) (π := Equiv.swap c d4)
    rw [hw1fix] at hact
    exact TableBUD.FrameAct.unique hw1n hact hfr1
  let q := qTwoFramePerm (h := h) (Q := Q) (hQ := hQ)
  let s1 := q (Equiv.swap a b)
  let s2 := q (Equiv.swap c d4)
  let J0 := ((TableBUE.blockSU (K := K) (n := 1) I).map (frameMk h Q hQ)).map
    (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)) →* MulAut _)
  have hJ1 : s1 ∈ J0 := by
    refine ⟨frameMk h Q hQ (LineU.permSU h (Equiv.swap a b)), ?_, rfl⟩
    refine ⟨LineU.permSU h (Equiv.swap a b), ?_, rfl⟩
    apply UnitAct.permSU_mem_blockSU_of_fixes_compl
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne
      (fun hia => hi (hia.symm ▸ haI)) (fun hib => hi (hib.symm ▸ hbI))
  have hJ2 : s2 ∈ J0 := by
    refine ⟨frameMk h Q hQ (LineU.permSU h (Equiv.swap c d4)), ?_, rfl⟩
    refine ⟨LineU.permSU h (Equiv.swap c d4), ?_, rfl⟩
    apply UnitAct.permSU_mem_blockSU_of_fixes_compl
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne
      (fun hic => hi (hic.symm ▸ hcI)) (fun hid => hi (hid.symm ▸ hd4I))
  have hN1 : s1 ∈ Subgroup.normalizer (E : Set _) :=
    qTwoFramePerm_mem_normalizer (E := E) hK hd3 hdq hp3 hpq3 hinner hfr h3d hcardW
      (Equiv.swap a b)
  have hN2 : s2 ∈ Subgroup.normalizer (E : Set _) :=
    qTwoFramePerm_mem_normalizer (E := E) hK hd3 hdq hp3 hpq3 hinner hfr h3d hcardW
      (Equiv.swap c d4)
  have hsq1 : s1 * s1 = 1 := by
    change q (Equiv.swap a b) * q (Equiv.swap a b) = 1
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hsq2 : s2 * s2 = 1 := by
    change q (Equiv.swap c d4) * q (Equiv.swap c d4) = 1
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hnodup : [a, b, c, d4].Nodup := by simp [hab, hac, had4, hbc, hbd4, hcd4]
  have hπcomm : Equiv.swap a b * Equiv.swap c d4 = Equiv.swap c d4 * Equiv.swap a b :=
    (Equiv.Perm.disjoint_swap_swap hnodup).commute.eq
  have hscomm : s1 * s2 = s2 * s1 := by
    change q (Equiv.swap a b) * q (Equiv.swap c d4) = q (Equiv.swap c d4) * q (Equiv.swap a b)
    rw [← map_mul, ← map_mul, hπcomm]
  have hs1 : s1 ≠ 1 := by
    intro h
    apply hmoved1
    change s1 * e1 * s1⁻¹ = e1
    simp only [h, one_mul, inv_one, mul_one]
  have hs2 : s2 ≠ 1 := by
    intro h
    apply hmoved2
    change s2 * e2 * s2⁻¹ = e2
    simp only [h, one_mul, inv_one, mul_one]
  have hsne : s1 ≠ s2 := by
    intro h
    apply hmoved1
    change s1 * e1 * s1⁻¹ = e1
    rw [h]
    exact hfix2
  have hker : ∀ x ∈ Subgroup.closure ({s1, s2} : Set _),
      (∀ t ∈ E, x * t * x⁻¹ = t) → x = 1 := by
    intro x hx hcent
    have hc := QTwoCav.closure_pair_eq_four hsq1 hsq2 hscomm hs1 hs2 hsne
    change x ∈ (Subgroup.closure ({s1, s2} : Set _) : Set _) at hx
    rw [hc] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · apply False.elim
      apply hmoved1
      have h := hcent e1 he1
      have heq : (s1 * s2) * e1 * (s1 * s2)⁻¹ = s1 * e1 * s1⁻¹ := by
        calc (s1 * s2) * e1 * (s1 * s2)⁻¹ = s1 * (s2 * e1 * s2⁻¹) * s1⁻¹ := by group
          _ = s1 * e1 * s1⁻¹ := by rw [hfix2]
      exact heq.symm.trans h
    · exact False.elim (hmoved1 (hcent e1 he1))
    · exact False.elim (hmoved2 (hcent e2 he2))
    · rfl
  exact QTwoCav.four_dvd_ggAutomizer_of_two_independent_involutions
    hJ1 hJ2 hN1 hN2 hsq1 hsq2 hscomm hs1 hs2 hsne hker

end CFSG.StandardType.QTwoUnitaryCav

end
