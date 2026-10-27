module

public import CFSG.RankThree.PartOne.CTP.FusionDefs
public import CFSG.RankThree.Asc83Table.MatCert

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.SectionRank.LocalWitness
open scoped commutatorElement

@[expose] def FusionGenerationOf (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ (E : Subgroup G) (Γ : Set G), IsPGroup p E ∧ E ≠ ⊥ ∧ Subgroup.closure Γ = ⊤ ∧
    ∀ g ∈ Γ, ∃ e ∈ E, e ≠ 1 ∧ g * e * g⁻¹ ∈ E

section Group

variable {G : Type*} [Group G]

theorem isPGroup_closure_pair {p : ℕ} (hp : p.Prime) {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) : IsPGroup p (Subgroup.closure ({x, y} : Set G)) := by
  have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy
  intro g
  obtain ⟨i, j, k, -, -, -, hg⟩ := mem_closure_normalForm hp.pos hx hy
    (by rw [hz]; exact Commute.one_left x) (by rw [hz]; exact Commute.one_left y) g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [hz, one_pow, mul_one] at hg
  have hc : Commute (x ^ i) (y ^ j) := Commute.pow_pow hxy i j
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [hg, hc.mul_pow, ← pow_mul, mul_comm i p, pow_mul, hx, one_pow, ← pow_mul, mul_comm j p,
    pow_mul, hy, one_pow, mul_one]

theorem exists_mem_closure_of_mem_closure {M : Type*} [Monoid M] {a b : M}
    (S : Submonoid M) (hS : S = Submonoid.closure ({a, b} : Set M)) (u v : Sˣ)
    (hu : valHom S u = a) (hv : valHom S v = b) :
    ∀ m ∈ S, ∃ n ∈ Subgroup.closure ({u, v} : Set Sˣ), valHom S n = m := by
  subst hS
  intro m hm
  induction hm using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨u, Subgroup.subset_closure (by simp), hu⟩
    · exact ⟨v, Subgroup.subset_closure (by simp), hv⟩
  | one => exact ⟨1, Subgroup.one_mem _, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, rfl⟩ := hx
    obtain ⟨n', hn', rfl⟩ := hy
    exact ⟨n * n', Subgroup.mul_mem _ hn hn', map_mul _ _ _⟩

theorem closure_pair_units_eq_top {M : Type*} [Monoid M] {a b : M} (S : Submonoid M)
    (hS : S = Submonoid.closure ({a, b} : Set M)) (u v : Sˣ) (hu : valHom S u = a)
    (hv : valHom S v = b) : Subgroup.closure ({u, v} : Set Sˣ) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨n, hn, hng⟩ := exists_mem_closure_of_mem_closure S hS u v hu hv (g : S).val
    (g : S).2
  have : n = g := valHom_injective S hng
  rwa [← this]

end Group

section Check

variable {M V : Type} {O : Ops M V} {c d : ℕ} (Sp : OpsSpec O c d) [Inhabited M]
  {sA sB : String} {C : MCert}

theorem wordUnit_mem_subgroup (hC : mcertCheck O sA sB C = true)
    (T : Subgroup (certMonoid c d sA sB)ˣ) :
    ∀ (w : Word), (∀ q ∈ w, regUnit Sp hC q.1 ∈ T) → wordUnit Sp hC w ∈ T
  | [], _ => by rw [wordUnit_nil]; exact T.one_mem
  | q :: w, h => by
    rw [wordUnit_cons]
    exact T.mul_mem (T.pow_mem (h q List.mem_cons_self) _)
      (wordUnit_mem_subgroup hC T w fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

variable {nregs : ℕ} {prog : List Op} {D : Spec}

include Sp in
theorem fusionGenerationOf_of_check (hp : D.p.Prime)
    (h : fusCheck O sA sB nregs prog D = true) :
    FusionGenerationOf (NativeSporadic.seedMonoid c d 1 sA sB)ˣ D.p := by
  unfold fusCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hC, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩, hwf⟩ := h
  let C : MCert := ⟨nregs, prog, D.facts⟩
  have hC' : mcertCheck O sA sB C = true := hC
  have fordA : MFact.ord D.rA D.oA ∈ D.facts := by simp [Spec.facts]
  have fordB : MFact.ord D.rB D.oB ∈ D.facts := by simp [Spec.facts]
  have fordx : MFact.ord D.rx D.p ∈ D.facts := by simp [Spec.facts]
  have fordy : MFact.ord D.ry D.p ∈ D.facts := by simp [Spec.facts]
  have fcomm : MFact.eq [(D.rx, 1), (D.ry, 1)] [(D.ry, 1), (D.rx, 1)] ∈ D.facts := by
    simp [Spec.facts]
  have fnex : MFact.ne [(D.rx, 1)] [] D.tx ∈ D.facts := by simp [Spec.facts]
  have fgen : ∀ g ∈ D.gens, MFact.ord g.reg g.ord ∈ D.facts ∧
      MFact.conj g.reg g.u g.w ∈ D.facts ∧ MFact.ne g.u [] g.tu ∈ D.facts := by
    intro g hg
    have key : ∀ f ∈ [MFact.ord g.reg g.ord, MFact.conj g.reg g.u g.w, MFact.ne g.u [] g.tu],
        f ∈ D.facts := fun f hf => List.mem_append.2 (Or.inl (List.mem_append.2
          (Or.inr (List.mem_flatMap.2 ⟨g, hg, hf⟩))))
    exact ⟨key _ (by simp), key _ (by simp), key _ (by simp)⟩
  have feA : MFact.eq [(D.rA, 1)] D.wA ∈ D.facts := by simp [Spec.facts]
  have feB : MFact.eq [(D.rB, 1)] D.wB ∈ D.facts := by simp [Spec.facts]
  unfold Spec.wf at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨-, hgw⟩, hAB⟩ := hwf
  have hAB' : ∀ q ∈ D.wA ++ D.wB, ∃ g ∈ D.gens, g.reg = q.1 := by
    intro q hq
    obtain ⟨g, hg, hgq⟩ := List.any_eq_true.1 (List.all_eq_true.1 hAB q hq)
    exact ⟨g, hg, by simpa using hgq⟩
  have hgw' : ∀ g ∈ D.gens, ∀ q ∈ g.u ++ g.w, q.1 = D.rx ∨ q.1 = D.ry := by
    intro g hg q hq
    have := List.all_eq_true.1 (List.all_eq_true.1 hgw g hg) q hq
    simpa [Bool.or_eq_true] using this
  have hOrdXY : ∀ w : Word, (∀ q ∈ w, q.1 = D.rx ∨ q.1 = D.ry) → HasOrd C w := by
    intro w hw q hq
    rcases hw q hq with h | h
    · exact ⟨D.p, h ▸ fordx⟩
    · exact ⟨D.p, h ▸ fordy⟩
  have hOrdGens : ∀ w : Word, (∀ q ∈ w, ∃ g ∈ D.gens, g.reg = q.1) → HasOrd C w := by
    intro w hw q hq
    obtain ⟨g, hg, hgq⟩ := hw q hq
    exact ⟨g.ord, hgq ▸ (fgen g hg).1⟩
  let x := regUnit Sp hC' D.rx
  let y := regUnit Sp hC' D.ry
  have hx : x ^ D.p = 1 := regUnit_pow Sp hC' fordx
  have hy : y ^ D.p = 1 := regUnit_pow Sp hC' fordy
  have hw1 : HasOrd C [(D.rx, 1), (D.ry, 1)] := hOrdXY _ (by simp)
  have hw2 : HasOrd C [(D.ry, 1), (D.rx, 1)] := hOrdXY _ (by simp)
  have hxy : x * y = y * x := by
    have := regUnit_eq Sp hC' fcomm hw1 hw2
    simpa [wordUnit] using this
  have hx1 : x ≠ 1 := by
    have := regUnit_ne Sp hC' fnex (hOrdXY [(D.rx, 1)] (by simp)) (hasOrd_nil C)
    simpa [wordUnit] using this
  let E : Subgroup (certMonoid c d sA sB)ˣ := Subgroup.closure ({x, y} : Set _)
  have hEp : IsPGroup D.p E := isPGroup_closure_pair hp hx hy hxy
  have hEx : x ∈ E := Subgroup.subset_closure (by simp)
  have hEy : y ∈ E := Subgroup.subset_closure (by simp)
  have hE1 : E ≠ ⊥ := fun h => hx1 (by simpa [h] using hEx)
  have hxyE : ∀ q : ℕ × ℕ, (q.1 = D.rx ∨ q.1 = D.ry) → regUnit Sp hC' q.1 ∈ E := by
    rintro q (h | h)
    · rw [h]; exact hEx
    · rw [h]; exact hEy
  let Γ : Set (certMonoid c d sA sB)ˣ := {g | ∃ gen ∈ D.gens, g = regUnit Sp hC' gen.reg}
  have hΓreg : ∀ q ∈ D.wA ++ D.wB, regUnit Sp hC' q.1 ∈ Subgroup.closure Γ := by
    intro q hq
    obtain ⟨g, hg, hgq⟩ := hAB' q hq
    exact Subgroup.subset_closure ⟨g, hg, by rw [hgq]⟩
  have hrA' : D.rA < C.nregs := hrA
  have hrB' : D.rB < C.nregs := hrB
  have hvalA : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rA) =
      NativeSporadic.decode c d 1 sA := by
    rw [val_regUnit Sp hC' fordA, Sp.toMat_eq (reg_ok Sp hC' hrA').1 (Sp.decode_wf sA) hAeq,
      Sp.toMat_decode]
  have hvalB : valHom (certMonoid c d sA sB) (regUnit Sp hC' D.rB) =
      NativeSporadic.decode c d 1 sB := by
    rw [val_regUnit Sp hC' fordB, Sp.toMat_eq (reg_ok Sp hC' hrB').1 (Sp.decode_wf sB) hBeq,
      Sp.toMat_decode]
  have htop := closure_pair_units_eq_top (certMonoid c d sA sB) rfl (regUnit Sp hC' D.rA)
    (regUnit Sp hC' D.rB) hvalA hvalB
  have hAw : regUnit Sp hC' D.rA = wordUnit Sp hC' D.wA := by
    have := regUnit_eq Sp hC' feA (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oA, fordA⟩)
      (hOrdGens D.wA fun q hq => hAB' q (List.mem_append.2 (Or.inl hq)))
    simpa [wordUnit] using this
  have hBw : regUnit Sp hC' D.rB = wordUnit Sp hC' D.wB := by
    have := regUnit_eq Sp hC' feB (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨D.oB, fordB⟩)
      (hOrdGens D.wB fun q hq => hAB' q (List.mem_append.2 (Or.inr hq)))
    simpa [wordUnit] using this
  refine ⟨E, Γ, hEp, hE1, ?_, ?_⟩
  · refine eq_top_iff.mpr ?_
    rw [← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hAw]
      exact wordUnit_mem_subgroup Sp hC' _ D.wA fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inl hq))
    · rw [hBw]
      exact wordUnit_mem_subgroup Sp hC' _ D.wB fun q hq =>
        hΓreg q (List.mem_append.2 (Or.inr hq))
  · rintro g ⟨gen, hgen, rfl⟩
    obtain ⟨hord, hconj, hne⟩ := fgen gen hgen
    have hu : HasOrd C gen.u := hOrdXY _ fun q hq => hgw' gen hgen q (List.mem_append.2 (Or.inl hq))
    have hw : HasOrd C gen.w := hOrdXY _ fun q hq => hgw' gen hgen q (List.mem_append.2 (Or.inr hq))
    refine ⟨wordUnit Sp hC' gen.u, wordUnit_mem_subgroup Sp hC' E _ fun q hq =>
      hxyE q (hgw' gen hgen q (List.mem_append.2 (Or.inl hq))), ?_, ?_⟩
    · have := regUnit_ne Sp hC' hne hu (hasOrd_nil C)
      simpa [wordUnit] using this
    · rw [regUnit_conj Sp hC' hconj hord hu hw]
      exact wordUnit_mem_subgroup Sp hC' E _ fun q hq =>
        hxyE q (hgw' gen hgen q (List.mem_append.2 (Or.inr hq)))

end Check

end CFSG.RankThree.PartOne.CTP.Fus
