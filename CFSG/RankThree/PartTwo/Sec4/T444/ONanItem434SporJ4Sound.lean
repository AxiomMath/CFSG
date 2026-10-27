module

public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Defs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.DerSound
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding.R3
  CFSG.SectionRank.LocalWitness CFSG.RankThree.PartTwo.Sec4.Item434SporGen
  CFSG.RankThree.PartOne.CTP.Fus
open scoped commutatorElement

section Check

variable {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d)
  {sA sB : String} {nregs : ℕ} {prog : List Op} {D : FixSpec}

include Sp in
theorem fixSpec_sound (h : fixCheck O sA sB nregs prog D = true) :
    ∃ x y : (NativeSporadic.seedMonoid c d 1 sA sB)ˣ, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
      Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 ∧
      FixGen (Subgroup.closure ({⁅x, y⁆, x} : Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ)) ∧
      (∃ g, g * ⁅x, y⁆ * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y ^ 2} :
          Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) ∧
        g * x * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y ^ 2} :
          Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ)) ∧
      (∃ g, g * ⁅x, y⁆ * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y} :
          Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) ∧
        g * x * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y} :
          Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ)) ∧
      (∃ g, g * ⁅x, y⁆ * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, y} :
          Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ) ∧
        g * x * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, y} :
          Set (NativeSporadic.seedMonoid c d 1 sA sB)ˣ)) := by
  unfold fixCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hC, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have fordA : MFact.ord D.rA D.oA ∈ D.facts := by simp [FixSpec.facts]
  have fordB : MFact.ord D.rB D.oB ∈ D.facts := by simp [FixSpec.facts]
  have fordx : MFact.ord D.rx 3 ∈ D.facts := by simp [FixSpec.facts]
  have fordy : MFact.ord D.ry 3 ∈ D.facts := by simp [FixSpec.facts]
  have fordz : MFact.ord D.rz 3 ∈ D.facts := by simp [FixSpec.facts]
  have fordxy : MFact.ord D.rxy 3 ∈ D.facts := by simp [FixSpec.facts]
  have fordxy2 : MFact.ord D.rxy2 3 ∈ D.facts := by simp [FixSpec.facts]
  have fez : MFact.eq [(D.rz, 1)] [(D.rx, 1), (D.ry, 1), (D.rx, 2), (D.ry, 2)] ∈ D.facts := by
    simp [FixSpec.facts]
  have fezx : MFact.eq [(D.rz, 1), (D.rx, 1)] [(D.rx, 1), (D.rz, 1)] ∈ D.facts := by
    simp [FixSpec.facts]
  have fezy : MFact.eq [(D.rz, 1), (D.ry, 1)] [(D.ry, 1), (D.rz, 1)] ∈ D.facts := by
    simp [FixSpec.facts]
  have fnez : MFact.ne [(D.rz, 1)] [] D.tz ∈ D.facts := by simp [FixSpec.facts]
  have fexy : MFact.eq [(D.rxy, 1)] [(D.rx, 1), (D.ry, 1)] ∈ D.facts := by simp [FixSpec.facts]
  have fexy2 : MFact.eq [(D.rxy2, 1)] [(D.rx, 1), (D.ry, 2)] ∈ D.facts := by
    simp [FixSpec.facts]
  have feA : MFact.eq [(D.rA, 1)] D.wA ∈ D.facts := by simp [FixSpec.facts]
  have feB : MFact.eq [(D.rB, 1)] D.wB ∈ D.facts := by simp [FixSpec.facts]
  have fgen : ∀ g ∈ D.gens, MFact.ord g.reg g.ord ∈ D.facts ∧ MFact.conj g.reg g.u g.u ∈ D.facts ∧
      MFact.ne g.u [] g.tu ∈ D.facts := by
    intro g hg
    have key : ∀ f ∈ [MFact.ord g.reg g.ord, MFact.conj g.reg g.u g.u, MFact.ne g.u [] g.tu],
        f ∈ D.facts := fun f hf => by
      simp only [FixSpec.facts, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨g, hg, hf⟩))))))
    exact ⟨key _ (by simp), key _ (by simp), key _ (by simp)⟩
  have fder : ∀ e ∈ D.ders, ∀ f ∈ e.facts, f ∈ C.facts := by
    intro e he f hf
    show f ∈ D.facts
    simp only [FixSpec.facts, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨e, he, hf⟩)))))
  have fcj : ∀ cj ∈ [D.c1, D.c2, D.c3], MFact.ord cj.reg cj.ord ∈ D.facts ∧
      MFact.conj cj.reg [(D.rz, 1)] cj.wz ∈ D.facts ∧
      MFact.conj cj.reg [(D.rx, 1)] cj.wx ∈ D.facts := by
    intro cj hcj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcj
    rcases hcj with rfl | rfl | rfl <;> simp [FixSpec.facts, Cj.facts]
  unfold FixSpec.wf at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨hgw, hderwf⟩, hAB⟩, hc1w⟩, hc2w⟩, hc3w⟩ := hwf
  have hgcop : ∀ g ∈ D.gens, g.ord % 3 ≠ 0 := by
    intro g hg
    have := List.all_eq_true.1 hgw g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hgu : ∀ g ∈ D.gens, ∀ q ∈ g.u, q.1 = D.rz ∨ q.1 = D.rx := by
    intro g hg q hq
    have := List.all_eq_true.1 hgw g hg
    simp only [Bool.and_eq_true] at this
    have := List.all_eq_true.1 this.2 q hq
    simpa [Bool.or_eq_true] using this
  have hord3 : ∀ r, (r = D.rx ∨ r = D.ry ∨ r = D.rz ∨ r = D.rxy ∨ r = D.rxy2) →
      HasOrd C [(r, 1)] := by
    intro r hr q hq
    simp only [List.mem_singleton] at hq
    rw [hq]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨3, fordx⟩
    · exact ⟨3, fordy⟩
    · exact ⟨3, fordz⟩
    · exact ⟨3, fordxy⟩
    · exact ⟨3, fordxy2⟩
  have hordw : ∀ (w : Word) (r : ℕ), (r = D.ry ∨ r = D.rxy ∨ r = D.rxy2) →
      (∀ q ∈ w, q.1 = D.rz ∨ q.1 = r) → HasOrd C w := by
    intro w r hr hw q hq
    rcases hw q hq with h1 | h1
    · exact ⟨3, h1 ▸ fordz⟩
    · rcases hr with rfl | rfl | rfl
      · exact ⟨3, h1 ▸ fordy⟩
      · exact ⟨3, h1 ▸ fordxy⟩
      · exact ⟨3, h1 ▸ fordxy2⟩
  let x := regUnit Sp hC' D.rx
  let y := regUnit Sp hC' D.ry
  let z := regUnit Sp hC' D.rz
  have hx : x ^ 3 = 1 := regUnit_pow Sp hC' fordx
  have hy : y ^ 3 = 1 := regUnit_pow Sp hC' fordy
  have hxinv : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)
  have hyinv : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy)
  have hzw : z = x * y * x ^ 2 * y ^ 2 := by
    have := regUnit_eq Sp hC' fez (hord3 D.rz (by simp)) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨3, fordx⟩
      · exact ⟨3, fordy⟩
      · exact ⟨3, fordx⟩
      · exact ⟨3, fordy⟩)
    simpa [wordUnit, mul_assoc] using this
  have hcomm : ⁅x, y⁆ = z := by rw [commutatorElement_def, hxinv, hyinv, hzw]
  have hzx : Commute z x := by
    have := regUnit_eq Sp hC' fezx (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨3, fordz⟩
      · exact ⟨3, fordx⟩) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨3, fordx⟩
      · exact ⟨3, fordz⟩)
    show z * x = x * z
    simpa [wordUnit] using this
  have hzy : Commute z y := by
    have := regUnit_eq Sp hC' fezy (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨3, fordz⟩
      · exact ⟨3, fordy⟩) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨3, fordy⟩
      · exact ⟨3, fordz⟩)
    show z * y = y * z
    simpa [wordUnit] using this
  have hz1 : z ≠ 1 := by
    have := regUnit_ne Sp hC' fnez (hord3 D.rz (by simp)) (hasOrd_nil C)
    simpa [wordUnit] using this
  have hxy : regUnit Sp hC' D.rxy = x * y := by
    have := regUnit_eq Sp hC' fexy (hord3 D.rxy (by simp)) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨3, fordx⟩
      · exact ⟨3, fordy⟩)
    simpa [wordUnit] using this
  have hxy2 : regUnit Sp hC' D.rxy2 = x * y ^ 2 := by
    have := regUnit_eq Sp hC' fexy2 (hord3 D.rxy2 (by simp)) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨3, fordx⟩
      · exact ⟨3, fordy⟩)
    simpa [wordUnit] using this
  let S : Set (certMonoid c d sA sB)ˣ := {g | ∃ gen ∈ D.gens, g = regUnit Sp hC' gen.reg}
  let T : Subgroup (certMonoid c d sA sB)ˣ := Subgroup.closure S
  have hav : ∀ r ∈ D.genRegs, regUnit Sp hC' r ∈ T ∧ ∃ o, MFact.ord r o ∈ C.facts := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    exact ⟨Subgroup.subset_closure ⟨g, hg, rfl⟩, g.ord, (fgen g hg).1⟩
  have hders := der_mem Sp hC' T D.ders D.genRegs fder hav hderwf
  have hseeds : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈ T ∧ ∃ o, MFact.ord q.1 o ∈ C.facts := by
    intro q hq
    have hq' := List.contains_iff_mem.1 (List.all_eq_true.1 hAB q hq)
    rcases List.mem_append.1 hq' with h1 | h1
    · obtain ⟨e, he, he'⟩ := List.mem_map.1 h1
      rw [← he']
      exact hders e he
    · exact hav _ h1
  have hvalA : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rA) =
      NativeSporadic.decode c d 1 sA := by
    rw [val_regUnit Sp hC' fordA, Sp.toMat_eq (reg_ok Sp hC' hrA).1 (Sp.decode_wf sA) hAeq,
      Sp.toMat_decode]
  have hvalB : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rB) =
      NativeSporadic.decode c d 1 sB := by
    rw [val_regUnit Sp hC' fordB, Sp.toMat_eq (reg_ok Sp hC' hrB).1 (Sp.decode_wf sB) hBeq,
      Sp.toMat_decode]
  have htop := closure_pair_units_eq_top (certMonoid c d sA sB) rfl (regUnit Sp hC' D.rA)
    (regUnit Sp hC' D.rB) hvalA hvalB
  have hAw : regUnit Sp hC' D.rA = wordUnit Sp hC' D.wA := by
    have := regUnit_eq Sp hC' feA (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oA, fordA⟩)
      (fun q hq => (hseeds q (List.mem_append.2 (Or.inl hq))).2)
    simpa [wordUnit] using this
  have hBw : regUnit Sp hC' D.rB = wordUnit Sp hC' D.wB := by
    have := regUnit_eq Sp hC' feB (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
      (fun q hq => (hseeds q (List.mem_append.2 (Or.inr hq))).2)
    simpa [wordUnit] using this
  have hT : T = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hAw]
      exact wordUnit_mem_subgroup Sp hC' _ D.wA fun q hq =>
        (hseeds q (List.mem_append.2 (Or.inl hq))).1
    · rw [hBw]
      exact wordUnit_mem_subgroup Sp hC' _ D.wB fun q hq =>
        (hseeds q (List.mem_append.2 (Or.inr hq))).1
  have hzE : z ∈ Subgroup.closure ({z, x} : Set (certMonoid c d sA sB)ˣ) :=
    Subgroup.subset_closure (by simp)
  have hxE : x ∈ Subgroup.closure ({z, x} : Set (certMonoid c d sA sB)ˣ) :=
    Subgroup.subset_closure (by simp)
  have hFix : FixGen (Subgroup.closure ({z, x} : Set (certMonoid c d sA sB)ˣ)) := by
    refine ⟨S, by rw [← hT], ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hord, hconj, hne⟩ := fgen g hg
    have hu : HasOrd C g.u := fun q hq => by
      rcases hgu g hg q hq with h1 | h1
      · exact ⟨3, h1 ▸ fordz⟩
      · exact ⟨3, h1 ▸ fordx⟩
    refine ⟨?_, wordUnit Sp hC' g.u, ?_, ?_, ?_⟩
    · have hdvd : orderOf (regUnit Sp hC' g.reg) ∣ g.ord :=
        orderOf_dvd_of_pow_eq_one (regUnit_pow Sp hC' hord)
      have hcop : Nat.Coprime g.ord 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 =>
          hgcop g hg (Nat.mod_eq_zero_of_dvd h3)).symm
      exact Nat.Coprime.coprime_dvd_left hdvd hcop
    · refine wordUnit_mem_subgroup Sp hC' _ g.u fun q hq => ?_
      rcases hgu g hg q hq with h1 | h1
      · rw [h1]; exact hzE
      · rw [h1]; exact hxE
    · have := regUnit_ne Sp hC' hne hu (hasOrd_nil C)
      simpa [wordUnit] using this
    · have h1 := regUnit_conj Sp hC' hconj hord hu hu
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hCj : ∀ (cj : Cj) (r : ℕ) (Q : Subgroup (certMonoid c d sA sB)ˣ),
      cj ∈ [D.c1, D.c2, D.c3] → (r = D.ry ∨ r = D.rxy ∨ r = D.rxy2) → (∀ q ∈ cj.wz ++ cj.wx,
        q.1 = D.rz ∨ q.1 = r) → z ∈ Q → regUnit Sp hC' r ∈ Q →
      regUnit Sp hC' cj.reg * z * (regUnit Sp hC' cj.reg)⁻¹ ∈ Q ∧
        regUnit Sp hC' cj.reg * x * (regUnit Sp hC' cj.reg)⁻¹ ∈ Q := by
    intro cj r Q hcj hr hw hzQ hrQ
    obtain ⟨hord, hz', hx'⟩ := fcj cj hcj
    have hwz : HasOrd C cj.wz := hordw _ r hr fun q hq => hw q (List.mem_append.2 (Or.inl hq))
    have hwx : HasOrd C cj.wx := hordw _ r hr fun q hq => hw q (List.mem_append.2 (Or.inr hq))
    have hmem : ∀ w : Word, (∀ q ∈ w, q.1 = D.rz ∨ q.1 = r) → wordUnit Sp hC' w ∈ Q := by
      intro w hw'
      refine wordUnit_mem_subgroup Sp hC' Q w fun q hq => ?_
      rcases hw' q hq with h1 | h1
      · rw [h1]; exact hzQ
      · rw [h1]; exact hrQ
    have e1 := regUnit_conj Sp hC' hz' hord (hord3 D.rz (by simp)) hwz
    have e2 := regUnit_conj Sp hC' hx' hord (hord3 D.rx (by simp)) hwx
    have e3 : wordUnit Sp hC' [(D.rz, 1)] = z := by simp [wordUnit, z]
    have e4 : wordUnit Sp hC' [(D.rx, 1)] = x := by simp [wordUnit, x]
    rw [e3] at e1
    rw [e4] at e2
    exact ⟨e1 ▸ hmem _ fun q hq => hw q (List.mem_append.2 (Or.inl hq)),
      e2 ▸ hmem _ fun q hq => hw q (List.mem_append.2 (Or.inr hq))⟩
  have hww : ∀ (cj : Cj) (r : ℕ), Cj.wf D r cj = true → ∀ q ∈ cj.wz ++ cj.wx,
      q.1 = D.rz ∨ q.1 = r := by
    intro cj r hcw q hq
    have := List.all_eq_true.1 hcw q hq
    simpa [Bool.or_eq_true] using this
  have hzm : ∀ (a : (certMonoid c d sA sB)ˣ),
      z ∈ Subgroup.closure ({z, a} : Set (certMonoid c d sA sB)ˣ) :=
    fun a => Subgroup.subset_closure (by simp)
  have hrm : ∀ (a : (certMonoid c d sA sB)ˣ),
      a ∈ Subgroup.closure ({z, a} : Set (certMonoid c d sA sB)ˣ) :=
    fun a => Subgroup.subset_closure (by simp)
  rw [← hcomm] at hFix
  refine ⟨x, y, hx, hy, hcomm ▸ hzx, hcomm ▸ hzy, hcomm ▸ hz1, hFix, ?_, ?_, ?_⟩
  · have := hCj D.c1 D.rxy2 (Subgroup.closure {z, x * y ^ 2}) (by simp) (by simp)
      (hww _ _ hc1w) (hzm _) (by rw [hxy2]; exact hrm _)
    rw [hcomm]
    exact ⟨_, this⟩
  · have := hCj D.c2 D.rxy (Subgroup.closure {z, x * y}) (by simp) (by simp)
      (hww _ _ hc2w) (hzm _) (by rw [hxy]; exact hrm _)
    rw [hcomm]
    exact ⟨_, this⟩
  · have := hCj D.c3 D.ry (Subgroup.closure {z, y}) (by simp) (by simp)
      (hww _ _ hc3w) (hzm _) (hrm _)
    rw [hcomm]
    exact ⟨_, this⟩

end Check

end CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine
