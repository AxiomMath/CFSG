module

public import Certificates.Certificate899107
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Transv
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalLevi
import CFSG.Certificates.Kernel.Sp62Pk.Sound

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

section OpMap

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ} [Fact p.Prime]

theorem Op_map_of_injective {f : G →* G'} (hf : Function.Injective f) (H : Subgroup G) :
    Op p (H.map f) = (Op p H).map f := by
  apply le_antisymm
  · have hle : Op p (H.map f) ≤ f.range := (L41.Op_le _).trans (Subgroup.map_le_range f H)
    have hN : (Op p (H.map f)).comap f ≤ Op p H := by
      refine L41.le_Op_of_normalized (fun x hx => ?_) (fun h hh x hx => ?_)
        ((L41.Op_isPGroup _).comap_of_injective f hf)
      · exact (Subgroup.mem_map_iff_mem hf).mp (L41.Op_le _ hx)
      · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact L41.Op_conj_mem (Subgroup.mem_map_of_mem f hh) hx
    calc Op p (H.map f) = ((Op p (H.map f)).comap f).map f :=
          (Subgroup.map_comap_eq_self hle).symm
      _ ≤ (Op p H).map f := Subgroup.map_mono hN
  · refine L41.le_Op_of_normalized (Subgroup.map_mono (L41.Op_le H)) ?_
      ((L41.Op_isPGroup H).map f)
    rintro _ ⟨h, hh, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨h * x * h⁻¹, L41.Op_conj_mem hh hx, by rw [map_mul, map_mul, map_inv]⟩

theorem map_cen_inf_cen {f : G →* G'} (hf : Function.Injective f) {R : Subgroup G'}
    (hR : (⊤ : Subgroup G).map f = R) (a b : G) :
    (Cen a ⊓ Cen b).map f = R ⊓ Cen (f a) ⊓ Cen (f b) := by
  rw [map_inf_cen hf, ← top_inf_eq (Cen a), map_inf_cen hf, hR]

end OpMap

section Cert


theorem cert899107_facts : Sp6RefSFacts := Certificates.certificate899107

theorem c7_ok107 : closureOK (c7P.map Prod.fst) (closureT (c7P.map Prod.fst)) 648 = true :=
  cert899107_facts.2.2

theorem pairs107 : nP.all pairCheck = true ∧ c7P.all pairCheck = true :=
  ⟨CFSG.KC.Sp62.all_pairs (by decide +kernel), CFSG.KC.Sp62.all_pairs (by decide +kernel)⟩

private theorem fl2_pair : pairCheck (fl2C, fl2C) = true :=
  CFSG.KC.Sp62.pairCheck_of (by decide +kernel)

noncomputable def fl0E : H6 :=
  ofCode (fl0C, fl0C) (List.all_eq_true.mp pairs107.1 _ (by simp [nP]))

noncomputable def sw01E : H6 :=
  ofCode (sw01C, sw01C) (List.all_eq_true.mp pairs107.1 _ (by simp [nP]))

noncomputable def fl2E : H6 :=
  ofCode (fl2C, fl2C) fl2_pair

noncomputable def c0E : H6 :=
  ofCode (c7Gen0, c7Gen0Inv) (List.all_eq_true.mp pairs107.2 _ (List.mem_cons_self ..))

noncomputable def c1E : H6 :=
  ofCode (c7Gen1, c7Gen1Inv)
    (List.all_eq_true.mp pairs107.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem mat6_fl2E : mat6 fl2E = dec6 fl2C :=
  mat6_ofCode _ _

theorem mat6_sw01E : mat6 sw01E = dec6 sw01C :=
  mat6_ofCode _ _

theorem facts107 : Sp6RefSAt zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH fl0E fl2E sw01E c0E c1E :=
  cert899107_facts.2.1 zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH fl0E fl2E sw01E c0E c1E mat6_zH mat6_tH (mat6_ofCode _ _)
    mat6_fl2E mat6_sw01E (mat6_ofCode _ _) (mat6_ofCode _ _)

noncomputable abbrev nSub : Subgroup H6 :=
  nGrp zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH fl0E sw01E

private theorem zH_zero_mem_nSub : zH 0 ∈ nSub :=
  Subgroup.subset_closure (by simp)

private theorem tH_mem_nSub : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ∈ nSub :=
  Subgroup.subset_closure (by simp)

theorem zH_mem_nSub (i : Fin 3) : zH i ∈ nSub := by
  have h1 : zH 1 ∈ nSub := by
    rw [← show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * zH 0 * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ = zH 1 from tH_conj 0]
    exact nSub.mul_mem (nSub.mul_mem tH_mem_nSub zH_zero_mem_nSub) (nSub.inv_mem tH_mem_nSub)
  have h2 : zH 2 ∈ nSub := by
    rw [← show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * zH 1 * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ = zH 2 from tH_conj 1]
    exact nSub.mul_mem (nSub.mul_mem tH_mem_nSub h1) (nSub.inv_mem tH_mem_nSub)
  fin_cases i
  · exact zH_zero_mem_nSub
  · exact h1
  · exact h2

theorem closure_zH_le_nSub : Subgroup.closure ({zH 0, zH 1, zH 2} : Set H6) ≤ nSub := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact zH_mem_nSub 0
  · exact zH_mem_nSub 1
  · exact zH_mem_nSub 2

theorem mat6_l1 (p : Fin 3) (a : ZMod 3) (ha : a ≠ 0) :
    ∃ k < 6, k / 2 = p.val ∧ mat6 (zH p ^ a.val) = dec6 (l1C.getD k []) := by
  have h1 : ∀ q : Fin 3, mat6 (zH q ^ 1) = dec6 (l1C.getD (2 * q.val) []) := fun q => by
    rw [pow_one, mat6_zH]
    fin_cases q <;> rfl
  have h2 : ∀ q : Fin 3, mat6 (zH q ^ 2) = dec6 (l1C.getD (2 * q.val + 1) []) := fun q => by
    rw [pow_two, map_mul, mat6_zH, ← dec6_mul6]
    fin_cases q <;> rfl
  fin_cases a
  · exact absurd rfl ha
  · exact ⟨2 * p.val, by omega, by omega, h1 p⟩
  · exact ⟨2 * p.val + 1, by omega, by omega, h2 p⟩

theorem exists_l1_of_mem {w : H6}
    (hw : w ∈ ({zH 0, (zH 0)⁻¹, zH 1, (zH 1)⁻¹, zH 2, (zH 2)⁻¹} : Set H6)) :
    ∃ k < 6, mat6 w = dec6 (l1C.getD k []) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, mat6_zH 0⟩
  · exact ⟨1, by norm_num, mat6_zH_inv 0⟩
  · exact ⟨2, by norm_num, mat6_zH 1⟩
  · exact ⟨3, by norm_num, mat6_zH_inv 1⟩
  · exact ⟨4, by norm_num, mat6_zH 2⟩
  · exact ⟨5, by norm_num, mat6_zH_inv 2⟩

theorem exists_nSub_l1 {a b c : ℕ} (ha : a < 6) (hb : b < 6) (hc : c < 6)
    (hnd : [a / 2, b / 2, c / 2].Nodup) : ∃ n ∈ nSub,
      mat6 (n * zH 0 * n⁻¹) = dec6 (l1C.getD a []) ∧
        mat6 (n * zH 1 * n⁻¹) = dec6 (l1C.getD b []) ∧
          mat6 (n * zH 2 * n⁻¹) = dec6 (l1C.getD c []) :=
  facts107.1 a ha b hb c hc hnd

noncomputable abbrev c7Sub : Subgroup H6 :=
  Subgroup.closure (genSet c7P pairs107.2)

private theorem w3_eq : vecElt zH ![1, 1, 1] = zH 0 * zH 1 * zH 2 := by
  simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one, pow_one, pow_one]

private theorem c7Sub_closure : c7Sub = Subgroup.closure {c0E, c1E} := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨cc, hm, rfl⟩
    simp only [c7P, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ofCode_mem_closure pairs107.2 (List.mem_cons_self ..)
    · exact ofCode_mem_closure pairs107.2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem c7Sub_eq : c7Sub = Subgroup.centralizer {vecElt zH ![1, 1, 1]} := by
  rw [c7Sub_closure, facts107.2.1, w3_eq]

noncomputable def sH (k : Fin 5) : H6 :=
  repSE fl2E sw01E k

noncomputable def aH (k : Fin 5) : H6 :=
  repLE zH k

theorem card_Op_rep (k : Fin 5) :
    Nat.card (Op 2 (Cen (sH k) ⊓ Cen (aH k))) = ![8, 2, 8, 2, 8] k :=
  facts107.2.2.1 k

theorem Op_rep_wt1 {k : Fin 5} (hk : k = 0 ∨ k = 2) :
    (∀ u ∈ Op 2 (Cen (sH k) ⊓ Cen (aH k)), ∀ v ∈ Op 2 (Cen (sH k) ⊓ Cen (aH k)), u * v = v * u) ∧
      ∀ u ∈ Op 2 (Cen (sH k) ⊓ Cen (aH k)), u * u = 1 :=
  facts107.2.2.2.1 k hk

theorem Op_rep_wt3 :
    ∃ u ∈ Op 2 (Cen (sH 4) ⊓ Cen (aH 4)), ∃ v ∈ Op 2 (Cen (sH 4) ⊓ Cen (aH 4)), u * v ≠ v * u :=
  facts107.2.2.2.2.1

theorem exists_conj_rep {s : H6} (hs : s ∈ nSub) (hs2 : orderOf s = 2) {x y : Fin 3 → ZMod 3}
    (hx : x ≠ 0) (hy : ∀ c : ZMod 3, y ≠ c • x) (hsx : s * vecElt zH x = vecElt zH x * s)
    (hsy : s * vecElt zH y = vecElt zH y * s) :
    ∃ n : H6, ∃ k : Fin 5, n * sH k * n⁻¹ = s ∧ n * aH k * n⁻¹ = vecElt zH x ∧
      ![1, 2, 1, 2, 3] k = torWt x :=
  facts107.2.2.2.2.2.1 s hs hs2 x y hx hy hsx hsy

private theorem l1_lines : ∀ a < 6, ∀ b < 6, a / 2 = b / 2 →
    l1C.getD b [] = l1C.getD a [] ∨ l1C.getD b [] = mul6 (l1C.getD a []) (l1C.getD a []) := by
  decide +kernel

private theorem zCode_ne : ∀ i j : Fin 3, i ≠ j →
    zCode j ≠ zCode i ∧ zCode j ≠ mul6 (zCode i) (zCode i) := by
  decide +kernel

private theorem conj_planes_ne {s : H6} {i j : Fin 3} (hij : i ≠ j) {a b : ℕ} (ha : a < 6)
    (hb : b < 6) (ea : mat6 (s * zH i * s⁻¹) = dec6 (l1C.getD a []))
    (eb : mat6 (s * zH j * s⁻¹) = dec6 (l1C.getD b [])) : a / 2 ≠ b / 2 := by
  intro e
  have hz := zCode_ne i j hij
  rcases l1_lines a ha b hb e with h | h
  · rw [← h, ← eb] at ea
    have := mat6_injective ea
    have hzz : zH i = zH j := by simpa using this
    exact hz.1 (dec6_injective (canon6_zCode_tCode.1 j) (canon6_zCode_tCode.1 i)
      (by rw [← mat6_zH, ← mat6_zH, hzz]))
  · rw [h, dec6_mul6, ← ea] at eb
    have e2 : s * zH i * s⁻¹ * (s * zH i * s⁻¹) = s * (zH i * zH i) * s⁻¹ := by group
    rw [← map_mul, e2] at eb
    have hzz : zH j = zH i * zH i := by simpa using mat6_injective eb
    exact hz.2 (dec6_injective (canon6_zCode_tCode.1 j) (canon6_mul6 _ _)
      (by rw [← mat6_zH, hzz, map_mul, mat6_zH, dec6_mul6]))

theorem mem_nSub {s : H6}
    (hmono : ∀ i, s * zH i * s⁻¹ ∈ ({zH 0, (zH 0)⁻¹, zH 1, (zH 1)⁻¹, zH 2, (zH 2)⁻¹} : Set H6))
    (hcen : Subgroup.centralizer ({zH 0, zH 1, zH 2} : Set H6) ≤
      Subgroup.closure ({zH 0, zH 1, zH 2} : Set H6)) : s ∈ nSub := by
  have hl : ∀ i : Fin 3, ∃ a < 6, mat6 (s * zH i * s⁻¹) = dec6 (l1C.getD a []) := fun i =>
    exists_l1_of_mem (hmono i)
  choose a ha ea using hl
  have hnd : [a 0 / 2, a 1 / 2, a 2 / 2].Nodup := by
    have d := fun i j (hij : i ≠ j) => conj_planes_ne hij (ha i) (ha j) (ea i) (ea j)
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨d 0 1 (by decide), d 0 2 (by decide)⟩, d 1 2 (by decide)⟩
  obtain ⟨n, hn, h0, h1, h2⟩ := exists_nSub_l1 (ha 0) (ha 1) (ha 2) hnd
  have hc : ∀ i : Fin 3, n * zH i * n⁻¹ = s * zH i * s⁻¹ := by
    intro i
    fin_cases i
    · exact mat6_injective (h0.trans (ea 0).symm)
    · exact mat6_injective (h1.trans (ea 1).symm)
    · exact mat6_injective (h2.trans (ea 2).symm)
  have hcomm : n⁻¹ * s ∈ Subgroup.centralizer ({zH 0, zH 1, zH 2} : Set H6) := by
    have key : ∀ i : Fin 3, zH i * (n⁻¹ * s) = n⁻¹ * s * zH i := fun i => by
      calc zH i * (n⁻¹ * s) = n⁻¹ * (n * zH i * n⁻¹) * s := by group
        _ = n⁻¹ * (s * zH i * s⁻¹) * s := by rw [hc i]
        _ = n⁻¹ * s * zH i := by group
    rw [Subgroup.mem_centralizer_iff]
    rintro _ (rfl | rfl | rfl)
    · exact key 0
    · exact key 1
    · exact key 2
  have hm := nSub.mul_mem hn (closure_zH_le_nSub (hcen hcomm))
  rwa [mul_inv_cancel_left] at hm

theorem exists_hom_std {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 3 2 1) {b₁ b₂ b₃ : X}
    (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L) (hB : IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) :
    ∃ f : H6 →* X, Function.Injective f ∧ (⊤ : Subgroup H6).map f = L ∧
      f (zH 0) = b₁ ∧ f (zH 1) = b₂ ∧ f (zH 2) = b₃ := by
  obtain ⟨f, hf, hfL, p₁, p₂, p₃, a₁, a₂, a₃, h12, h13, h23, ha₁, ha₂, ha₃, e₁, e₂, e₃⟩ :=
    exists_hom_zH_pow hL hb₁ hb₂ hb₃ hB hmono
  obtain ⟨k₁, hk₁, hp₁, m₁⟩ := mat6_l1 p₁ a₁ ha₁
  obtain ⟨k₂, hk₂, hp₂, m₂⟩ := mat6_l1 p₂ a₂ ha₂
  obtain ⟨k₃, hk₃, hp₃, m₃⟩ := mat6_l1 p₃ a₃ ha₃
  have hnd : [k₁ / 2, k₂ / 2, k₃ / 2].Nodup := by
    rw [hp₁, hp₂, hp₃]
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨Fin.val_injective.ne h12, Fin.val_injective.ne h13⟩, Fin.val_injective.ne h23⟩
  obtain ⟨n, -, h0, h1, h2⟩ := exists_nSub_l1 hk₁ hk₂ hk₃ hnd
  have hconj : ∀ c : H6, (f.comp (MulAut.conj n).toMonoidHom) c = f (n * c * n⁻¹) := fun c => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨f.comp (MulAut.conj n).toMonoidHom, hf.comp (MulAut.conj n).injective, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj n).surjective, hfL]
  · rw [hconj, mat6_injective (h0.trans m₁.symm), e₁]
  · rw [hconj, mat6_injective (h1.trans m₂.symm), e₂]
  · rw [hconj, mat6_injective (h2.trans m₃.symm), e₃]

private noncomputable def leviGL : GL (Fin 3) (ZMod 2) →* H6 where
  toFun A := CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal.leviSp
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3)
      (ZMod 2)) A.mul_inv A.inv_mul
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change Matrix.fromBlocks ((1 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
      (((1 : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose = 1
    simp [Matrix.fromBlocks_one]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    change Matrix.fromBlocks ((A * B : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
        (((A * B)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose =
      Matrix.fromBlocks (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
          ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose *
        Matrix.fromBlocks (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
          ((B⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose
    rw [Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul,
      Matrix.transpose_mul]
    simp

private theorem leviGL_injective : Function.Injective leviGL := by
  intro A B h
  have h' := congrArg (fun g : H6 => ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) h
  change Matrix.fromBlocks _ _ _ _ = Matrix.fromBlocks _ _ _ _ at h'
  exact Units.ext (Matrix.fromBlocks_inj.mp h').1

private def tP : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

private theorem leviGL_tP : leviGL tP = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := by
  refine mat6_injective ?_
  rw [mat6_tH, mat6_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem exists_conj_t : ∃ g : H6, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH = g * (zH 0 * zH 1) * g⁻¹ :=
  facts107.2.2.2.2.2.2

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79 Sp6RefS
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)


theorem kf_sp6RefS : KF_Sp6RefS := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB hC hmono s hsL hs2 hsN x y hx hy hsx hsy
  obtain ⟨f, hf, hfL, e₁, e₂, e₃⟩ := exists_hom_std hL hb₁ hb₂ hb₃ hB hmono
  have hfL' : ∀ c, f c ∈ L := fun c => hfL ▸ Subgroup.mem_map_of_mem f (Subgroup.mem_top c)
  obtain ⟨s', rfl⟩ : ∃ s', f s' = s := by
    rw [← hfL] at hsL
    obtain ⟨s', -, e⟩ := hsL
    exact ⟨s', e⟩
  have htor : ∀ v, torElt b₁ b₂ b₃ v = f (vecElt zH v) := fun v => by
    rw [torElt, vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, e₁, e₂, e₃]
  have hs2' : orderOf s' = 2 := by rwa [orderOf_injective f hf] at hs2
  have hsx' : s' * vecElt zH x = vecElt zH x * s' :=
    hf (by rw [map_mul, map_mul, ← htor]; exact hsx)
  have hsy' : s' * vecElt zH y = vecElt zH y * s' :=
    hf (by rw [map_mul, map_mul, ← htor]; exact hsy)
  have hmono' : ∀ i, s' * zH i * s'⁻¹ ∈
      ({zH 0, (zH 0)⁻¹, zH 1, (zH 1)⁻¹, zH 2, (zH 2)⁻¹} : Set H6) := by
    intro i
    have hi : f (zH i) ∈ ({b₁, b₂, b₃} : Set X) := by
      fin_cases i
      · exact Or.inl e₁
      · exact Or.inr (Or.inl e₂)
      · exact Or.inr (Or.inr e₃)
    have h := hmono (f s') hsL hsN (f (zH i)) hi
    rw [← map_inv, ← map_mul, ← map_mul, ← e₁, ← e₂, ← e₃, ← map_inv f (zH 0),
      ← map_inv f (zH 1), ← map_inv f (zH 2)] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h | h | h
    · exact Or.inl (hf h)
    · exact Or.inr (Or.inl (hf h))
    · exact Or.inr (Or.inr (Or.inl (hf h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hf h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hf h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hf h)))))
  have hcen : Subgroup.centralizer ({zH 0, zH 1, zH 2} : Set H6) ≤
      Subgroup.closure ({zH 0, zH 1, zH 2} : Set H6) := by
    intro c hc
    have hcl : (Subgroup.closure ({zH 0, zH 1, zH 2} : Set H6)).map f =
        Subgroup.closure ({b₁, b₂, b₃} : Set X) := by
      rw [MonoidHom.map_closure]
      congr 1
      simp only [Set.image_insert_eq, Set.image_singleton, e₁, e₂, e₃]
    have hfc : f c ∈ L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set X)) := by
      refine Subgroup.mem_inf.mpr ⟨hfL' c, ?_⟩
      rw [CenS, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rw [Subgroup.mem_centralizer_iff] at hc
      rintro _ (rfl | rfl | rfl)
      · rw [← e₁, ← map_mul, ← map_mul, hc (zH 0) (Or.inl rfl)]
      · rw [← e₂, ← map_mul, ← map_mul, hc (zH 1) (Or.inr (Or.inl rfl))]
      · rw [← e₃, ← map_mul, ← map_mul, hc (zH 2) (Or.inr (Or.inr rfl))]
    rw [hC, ← hcl] at hfc
    exact (Subgroup.mem_map_iff_mem hf).mp hfc
  obtain ⟨n, k, hns, hna, hw⟩ :=
    exists_conj_rep (mem_nSub hmono' hcen) hs2' hx hy hsx' hsy'
  set F : H6 →* X := f.comp (MulAut.conj n).toMonoidHom with hF
  have hFi : Function.Injective F := hf.comp (MulAut.conj n).injective
  have hFL : (⊤ : Subgroup H6).map F = L := by
    rw [hF, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj n).surjective, hfL]
  have hFs : F (sH k) = f s' := by
    rw [hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hns]
  have hFa : F (aH k) = torElt b₁ b₂ b₃ x := by
    rw [hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hna, htor]
  have hOp : Op 2 (L ⊓ Cen (f s') ⊓ Cen (torElt b₁ b₂ b₃ x)) =
      (Op 2 (Cen (sH k) ⊓ Cen (aH k))).map F := by
    rw [← hFs, ← hFa, ← map_cen_inf_cen hFi hFL, Op_map_of_injective hFi]
  rw [hOp]
  have hcard : Nat.card ↥((Op 2 (Cen (sH k) ⊓ Cen (aH k))).map F) =
      Nat.card ↥(Op 2 (Cen (sH k) ⊓ Cen (aH k))) :=
    Subgroup.card_map_of_injective hFi
  refine ⟨fun hw2 => ?_, fun hw1 => ?_, fun hw3 => ?_⟩
  · have hk : k = 1 ∨ k = 3 := by
      have h := hw.trans hw2
      fin_cases k <;> first | decide | exact absurd h (by decide)
    rw [hcard, card_Op_rep]
    rcases hk with rfl | rfl <;> decide
  · have hk : k = 0 ∨ k = 2 := by
      have h := hw.trans hw1
      fin_cases k <;> first | decide | exact absurd h (by decide)
    obtain ⟨hab, hsq⟩ := Op_rep_wt1 hk
    refine ⟨hcard.trans ((card_Op_rep k).trans (by rcases hk with rfl | rfl <;> rfl)), ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, hab u hu v hv]
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, hsq u hu, map_one]
  · have hk : k = 4 := by
      have h := hw.trans hw3
      fin_cases k <;> first | decide | exact absurd h (by decide)
    subst hk
    obtain ⟨u, hu, v, hv, huv⟩ := Op_rep_wt3
    refine ⟨hcard.trans (card_Op_rep 4), F u, ⟨u, hu, rfl⟩, F v, ⟨v, hv, rfl⟩, fun e => huv (hFi ?_)⟩
    rw [map_mul, map_mul, e]

theorem kf_sp6SL3 : KF_Sp6SL3 := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB _ hmono
  obtain ⟨f, hf, hfL, e₁, e₂, -⟩ := exists_hom_std hL hb₁ hb₂ hb₃ hB hmono
  obtain ⟨g, hg⟩ := exists_conj_t
  set F : GL (Fin 3) (ZMod 2) →* X := f.comp ((MulAut.conj g⁻¹).toMonoidHom.comp leviGL) with hF
  have hFi : Function.Injective F :=
    hf.comp ((MulAut.conj g⁻¹).injective.comp leviGL_injective)
  refine ⟨F.range, ?_, ⟨(MonoidHom.ofInjective hFi).symm⟩, tP, ?_⟩
  · rintro _ ⟨A, rfl⟩
    rw [← hfL]
    exact ⟨_, Subgroup.mem_top _, rfl⟩
  · rw [hF, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, leviGL_tP, hg,
      show g⁻¹ * (g * (zH 0 * zH 1) * g⁻¹) * g = zH 0 * zH 1 by group, map_mul, e₁, e₂]

end CFSG.RankThree.PartTwo.Sec21.FF81
