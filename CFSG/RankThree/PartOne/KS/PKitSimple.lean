module

public import CFSG.RankThree.PartOne.KS.PKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

section Reps

variable {n : ℕ}

@[expose] def classReps (n : ℕ) (c : ArrCert) : List ℕ :=
  (List.range c.pts.size).foldl (fun reps k =>
    if eqA n c.pts[k]! (idA n) ||
        reps.any (fun r => (List.range c.pts.size).any fun j =>
          eqA n c.pts[k]! (conjA n c.pts[j]! c.pts[r]!)) then reps else reps ++ [k]) []

@[expose] def conjClassCoverOK (n : ℕ) (c : ArrCert) (reps : List ℕ) : Bool :=
  reps.all (fun r => decide (r < c.pts.size)) &&
    allLt c.pts.size fun k => eqA n c.pts[k]! (idA n) ||
      reps.any fun r => (List.range c.pts.size).any fun j =>
        eqA n c.pts[k]! (conjA n c.pts[j]! c.pts[r]!)

@[expose] def conjSimpleRepsOK (n : ℕ) (ps : List ℕ) (c : ArrCert) (reps : List ℕ) : Bool :=
  conjClassCoverOK n c reps && reps.all fun r =>
    conjPointOK n ps c r (enumBfs n (conjGens n c r) ps (c.pts.size + 1))

theorem isSimpleGroup_of_conjSimpleRepsOK {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    {reps : List ℕ} (hps : ∀ p ∈ ps, p < n) (hc : enumOK n gs ps c = true)
    (hnt : 1 < c.pts.size) (h : conjSimpleRepsOK n ps c reps = true) :
    IsSimpleGroup (Subgroup.closure (permsA n gs)) := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps hc
  set D := Subgroup.closure (permsA n gs)
  simp only [conjSimpleRepsOK, conjClassCoverOK, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hrlt, hcover⟩, hreps⟩ := h
  apply isSimpleGroup_of_conj_closure
  · by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hsub : (D : Set (Equiv.Perm (Fin n))) ⊆ {1} := fun g hg => hall g hg
    have h1 : Nat.card D ≤ 1 := by
      calc Nat.card D = (D : Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1} : Set (Equiv.Perm (Fin n))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    omega
  · intro e he he1
    obtain ⟨k, hk, rfl⟩ := (hmem e).1 he
    have hck := allLt_spec hcover hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at hck
    rcases hck with hid | ⟨r, hr, j, hj, hkjr⟩
    · exact absurd ((eqA_iff (rep_of_validA (hval k hk)) rep_idA).1 hid) he1
    · have hrk : r < c.pts.size := hrlt r hr
      have hckr := hreps r hr
      simp only [conjPointOK, Bool.and_eq_true, beq_iff_eq] at hckr
      obtain ⟨hE, hS⟩ := hckr
      obtain ⟨-, hcardk, -⟩ := enumOK_spec hps hE
      set K := Subgroup.closure (permsA n (conjGens n c r))
      have hgen : ∀ i < c.pts.size, permOfArr n (conjGens n c r)[i]! =
          permOfArr n c.pts[i]! * permOfArr n c.pts[r]! * (permOfArr n c.pts[i]!)⁻¹ := by
        intro i hi
        rw [conjGens_get hi]
        exact CFSG.RankThree.Native.permOfArr_eq_of_rep
          (rep_conjA (hval i hi) (rep_of_validA (hval r hrk)))
      have hKD : K ≤ D := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, hi, rfl⟩
        have hi' : i < c.pts.size := by rw [← conjGens_size (n := n) c r]; exact hi
        dsimp only
        rw [SetLike.mem_coe, hgen i hi']
        exact D.mul_mem (D.mul_mem ((hmem _).2 ⟨i, hi', rfl⟩) ((hmem _).2 ⟨r, hrk, rfl⟩))
          (D.inv_mem ((hmem _).2 ⟨i, hi', rfl⟩))
      have hKeq : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [hcardk, hS, hcard])
      have hej : permOfArr n c.pts[k]! =
          permOfArr n c.pts[j]! * permOfArr n c.pts[r]! * (permOfArr n c.pts[j]!)⁻¹ :=
        eq_of_eqA (rep_of_validA (hval k hk))
          (rep_conjA (hval j hj) (rep_of_validA (hval r hrk))) hkjr
      refine le_trans hKeq.symm.le ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < c.pts.size := by rw [← conjGens_size (n := n) c r]; exact hi
      dsimp only
      rw [SetLike.mem_coe]
      have hiD : permOfArr n c.pts[i]! ∈ D := (hmem _).2 ⟨i, hi', rfl⟩
      have hjD : permOfArr n c.pts[j]! ∈ D := (hmem _).2 ⟨j, hj, rfl⟩
      refine Subgroup.subset_closure ⟨permOfArr n c.pts[i]! * (permOfArr n c.pts[j]!)⁻¹,
        D.mul_mem hiD (D.inv_mem hjD), ?_⟩
      rw [hgen i hi', hej]
      group

end Reps

section Derived

variable {n p M : ℕ} {gC gD : Array (Array ℕ)} {ps : List ℕ} {cC cD : ArrCert}

@[expose] def derivedOKQ (p M n : ℕ) (gC gD : Array (Array ℕ)) (ps : List ℕ) (cC cD : ArrCert)
    (c d x : Array ℕ) (PL : Array Level) (Pb : Array ℕ) : Bool :=
  enumOK n gD ps cD && cD.pts.size == M && validA n c && validA n d &&
    cC.pts.toList.any (eqA n c) && cC.pts.toList.any (eqA n d) &&
    eqA n gC[2]! (commutatorA n c d) &&
    allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) &&
    allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!))) &&
    !(commA n gD[0]! gD[1]!) && conjSimpleRepsOK n ps cD (classReps n cD) &&
    allLt cC.pts.size (fun k => !(allLt gD.size fun l => commA n cC.pts[k]! gD[l]!) ||
      (List.range p).any fun e => eqA n cC.pts[k]! (powArr n x e)) &&
    allLt gD.size (fun l => siftA n PL Pb 0 gD[l]!)

theorem derivedOKQ_parts {c d x : Array ℕ} {PL : Array Level} {Pb : Array ℕ}
    (h : derivedOKQ p M n gC gD ps cC cD c d x PL Pb = true) :
    enumOK n gD ps cD = true ∧ cD.pts.size = M ∧ validA n c = true ∧ validA n d = true ∧
    cC.pts.toList.any (eqA n c) = true ∧ cC.pts.toList.any (eqA n d) = true ∧
    eqA n gC[2]! (commutatorA n c d) = true ∧
    allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) = true ∧
    allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!))) = true ∧
    commA n gD[0]! gD[1]! = false ∧ conjSimpleRepsOK n ps cD (classReps n cD) = true ∧
    allLt cC.pts.size (fun k => !(allLt gD.size fun l => commA n cC.pts[k]! gD[l]!) ||
      (List.range p).any fun e => eqA n cC.pts[k]! (powArr n x e)) = true ∧
    allLt gD.size (fun l => siftA n PL Pb 0 gD[l]!) = true := by
  simp only [derivedOKQ, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hDe, hDs⟩, hcv⟩, hdv⟩, hcm⟩, hdm⟩, hb⟩, hnorm⟩, hcomm⟩, hnab⟩,
    hsimple⟩, hcent⟩, hsift⟩ := h
  exact ⟨hDe, hDs, hcv, hdv, hcm, hdm, hb, hnorm, hcomm, hnab, hsimple, hcent, hsift⟩

theorem recordD_eq_commutatorQ {c d x : Array ℕ} {PL : Array Level} {Pb : Array ℕ}
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hD : derivedOKQ p M n gC gD ps cC cD c d x PL Pb = true)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) (h3 : 3 ≤ gC.size) :
    ⁅closure (permsA n gC), closure (permsA n gC)⁆ = closure (permsA n gD) := by
  obtain ⟨hDe, -, hcv, hdv, hcm, hdm, hb, hnorm, hcomm, -⟩ := derivedOKQ_parts hD
  exact derived_kit hps hC hDe h3 hgD hcv hdv hcm hdm hb hnorm hcomm

theorem recordD_specQ {c d x : Array ℕ} {X : Equiv.Perm (Fin n)}
    {PL : Array Level} {Pb : Array ℕ} {P R' : Subgroup (Equiv.Perm (Fin n))}
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hCx : closure (permsA n gC) = centralizer {X} ⊓ R')
    (hD : derivedOKQ p M n gC gD ps cC cD c d x PL Pb = true)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) (h3 : 3 ≤ gC.size) (hM : 1 < M)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P)
    (hx : Rep n x X) (hxz : eqA n gC[0]! x = true) (hord : orderOf X = p) :
    IsSimpleGroup (closure (permsA n gD)) ∧
      (∃ g ∈ closure (permsA n gD), ∃ h ∈ closure (permsA n gD), g * h ≠ h * g) ∧
      Nat.card (closure (permsA n gD)) = M ∧ closure (permsA n gD) ≤ P ∧
      centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) =
        zpowers X ∧
      Nat.card (centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) ⊓
        closure (permsA n gC) : Subgroup (Equiv.Perm (Fin n))) = p := by
  obtain ⟨hDe, hDs, -, -, -, -, -, -, -, hnab, hsimple, hcent, hsift⟩ := derivedOKQ_parts hD
  have hDeq := recordD_eq_commutatorQ hps hC hD hgD h3
  have hDsize : gD.size = 2 := by simp [hgD]
  have hrepD : ∀ l < gD.size, Rep n gD[l]! (permOfArr n gD[l]!) := fun l hl =>
    rep_of_validA (enumOK_gens_valid hDe hl)
  have hcard : Nat.card (closure (permsA n gD)) = M := (enumOK_spec hps hDe).2.1.trans hDs
  have h0 : 0 < gC.size := by omega
  have hxC : X ∈ closure (permsA n gC) := mem_of_gen_zeroG hx h0 (enumOK_gens_valid hC h0) hxz
  have hDC : closure (permsA n gD) ≤ closure (permsA n gC) := by
    rw [← hDeq, commutator_le]
    intro a ha b hb'
    rw [commutatorElement_def]
    exact (closure (permsA n gC)).mul_mem ((closure (permsA n gC)).mul_mem
      ((closure (permsA n gC)).mul_mem ha hb') ((closure (permsA n gC)).inv_mem ha))
      ((closure (permsA n gC)).inv_mem hb')
  have hxcent : X ∈ centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) := by
    rw [mem_centralizer_iff]
    intro a ha
    have : a ∈ centralizer {X} ⊓ R' := hCx ▸ hDC ha
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 this).1
  have hcentD : centralizer (closure (permsA n gD) : Set (Equiv.Perm (Fin n))) ⊓
      closure (permsA n gC) = zpowers X :=
    centralizer_eq_zpowers_kitP hps hC hDe hx hxC hxcent hcent
  refine ⟨?_, ?_, hcard, ?_, hcentD, ?_⟩
  · exact isSimpleGroup_of_conjSimpleRepsOK hps hDe (by rw [hDs]; exact hM) hsimple
  · refine ⟨_, subset_closure (mem_permsA (k := 0) (by rw [hDsize]; norm_num)), _,
      subset_closure (mem_permsA (k := 1) (by rw [hDsize]; norm_num)), fun e => ?_⟩
    have := (commA_iff (hrepD 0 (by rw [hDsize]; norm_num))
      (hrepD 1 (by rw [hDsize]; norm_num))).2 e
    rw [hnab] at this
    exact Bool.false_ne_true this
  · exact closure_le_of_siftG (fun l hl => enumOK_gens_valid hDe hl) hsift hmemP
  · rw [hcentD, Nat.card_zpowers]
    exact hord

theorem recordD_spec_commQ {c d x : Array ℕ} {X : Equiv.Perm (Fin n)}
    {PL : Array Level} {Pb : Array ℕ} {P R' : Subgroup (Equiv.Perm (Fin n))}
    {D : Subgroup (Equiv.Perm (Fin n))}
    (hDc : D = ⁅closure (permsA n gC), closure (permsA n gC)⁆)
    (hps : ∀ q ∈ ps, q < n) (hC : enumOK n gC ps cC = true)
    (hCx : closure (permsA n gC) = centralizer {X} ⊓ R')
    (hD : derivedOKQ p M n gC gD ps cC cD c d x PL Pb = true)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) (h3 : 3 ≤ gC.size) (hM : 1 < M)
    (hmemP : ∀ {g : Array ℕ} {G : Equiv.Perm (Fin n)}, Rep n g G → siftA n PL Pb 0 g = true →
      G ∈ P)
    (hx : Rep n x X) (hxz : eqA n gC[0]! x = true) (hord : orderOf X = p) :
    IsSimpleGroup D ∧ (∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) ∧ Nat.card D = M ∧ D ≤ P ∧
      centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) = zpowers X ∧
      Nat.card (centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ closure (permsA n gC) :
        Subgroup (Equiv.Perm (Fin n))) = p := by
  rw [hDc, recordD_eq_commutatorQ hps hC hD hgD h3]
  exact recordD_specQ hps hC hCx hD hgD h3 hM hmemP hx hxz hord

end Derived

end CFSG.RankThree.PartOne
