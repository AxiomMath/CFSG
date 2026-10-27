module

public import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelY
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelTr

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Tau

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem exists_mulEquiv_of_tree {G H : Type*} [Group G] [Group H] {A : Subgroup G}
    {B : Subgroup H} {m N : ℕ} {e₁ : ℕ → G} {e₂ : ℕ → H} {g : ℕ → G} {g' : ℕ → H}
    {par lab : ℕ → ℕ} (hm : 0 < m) (h₁ : e₁ 0 = 1) (h₂ : e₂ 0 = 1)
    (hpar : ∀ k, 0 < k → k < m → par k < k ∧ lab k < N)
    (hstep₁ : ∀ k, 0 < k → k < m → e₁ k = e₁ (par k) * g (lab k))
    (hstep₂ : ∀ k, 0 < k → k < m → e₂ k = e₂ (par k) * g' (lab k))
    (hsucc : ∀ k < m, ∀ l < N, ∃ k' < m, e₁ k' = e₁ k * g l ∧ e₂ k' = e₂ k * g' l)
    (hinj₁ : ∀ i < m, ∀ j < m, e₁ i = e₁ j → i = j)
    (hinj₂ : ∀ i < m, ∀ j < m, e₂ i = e₂ j → i = j)
    (hmem₂ : ∀ k < m, e₂ k ∈ B)
    (hcov₁ : ∀ x ∈ A, ∃ k < m, e₁ k = x) (hg₁ : ∀ l < N, g l ∈ A)
    (hB : B ≤ Subgroup.closure (g' '' {l | l < N})) :
    ∃ ι : ↥A ≃* ↥B, ∀ (l : ℕ) (hl : l < N), ((ι ⟨g l, hg₁ l hl⟩ : ↥B) : H) = g' l := by
  classical
  have hmul : ∀ k' < m, ∀ k < m, ∃ k'' < m, e₁ k'' = e₁ k * e₁ k' ∧ e₂ k'' = e₂ k * e₂ k' := by
    intro k'
    induction k' using Nat.strong_induction_on with
    | _ k' ih =>
      intro hk' k hk
      rcases Nat.eq_zero_or_pos k' with rfl | hpos
      · exact ⟨k, hk, by rw [h₁, mul_one], by rw [h₂, mul_one]⟩
      · obtain ⟨hp, hl⟩ := hpar k' hpos hk'
        obtain ⟨k₁, hk₁, e₁eq, e₂eq⟩ := ih _ hp (hp.trans hk') k hk
        obtain ⟨k'', hk'', e₁eq', e₂eq'⟩ := hsucc k₁ hk₁ _ hl
        exact ⟨k'', hk'', by rw [e₁eq', e₁eq, hstep₁ k' hpos hk', mul_assoc],
          by rw [e₂eq', e₂eq, hstep₂ k' hpos hk', mul_assoc]⟩
  choose kf hkf hkf' using fun x : ↥A => hcov₁ x x.2
  let φ : ↥A →* H := MonoidHom.mk' (fun x => e₂ (kf x)) (by
    intro x y
    obtain ⟨k'', hk'', e₁eq, e₂eq⟩ := hmul (kf y) (hkf y) (kf x) (hkf x)
    have hk : kf (x * y) = k'' :=
      hinj₁ _ (hkf _) _ hk'' (by rw [hkf', Subgroup.coe_mul, e₁eq, hkf', hkf'])
    show e₂ (kf (x * y)) = e₂ (kf x) * e₂ (kf y)
    rw [hk, e₂eq])
  have hgenk : ∀ (l : ℕ) (hl : l < N), φ ⟨g l, hg₁ l hl⟩ = g' l := by
    intro l hl
    obtain ⟨k', hk', e₁eq, e₂eq⟩ := hsucc 0 hm l hl
    rw [h₁, one_mul] at e₁eq
    rw [h₂, one_mul] at e₂eq
    have hk : kf ⟨g l, hg₁ l hl⟩ = k' := hinj₁ _ (hkf _) _ hk' (by rw [hkf', e₁eq])
    show e₂ (kf ⟨g l, hg₁ l hl⟩) = g' l
    rw [hk, e₂eq]
  let f : ↥A →* ↥B := φ.codRestrict B fun x => hmem₂ _ (hkf x)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxy' : e₂ (kf x) = e₂ (kf y) := congrArg Subtype.val hxy
    apply Subtype.ext
    rw [← hkf' x, ← hkf' y, hinj₂ _ (hkf x) _ (hkf y) hxy']
  have hsurj : Function.Surjective f := by
    have hBle : B ≤ φ.range := hB.trans ((Subgroup.closure_le _).2 (by
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨⟨g l, hg₁ l hl⟩, hgenk l hl⟩))
    intro b
    obtain ⟨x, hx⟩ := hBle b.2
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun l hl => hgenk l hl⟩

theorem mulTree_facts {n : ℕ} (hn : n < 2 ^ 32) {gens elts : Array Table} {par lab : Array ℕ}
    {gg : ℕ → Perm (Fin n)} (hg : ∀ l < gens.size, Rep n gens[l]! (gg l))
    (h : CFSG.Sporadic.SmallOddCore.Native.mulTreeOK n gens elts par lab = true) :
    0 < elts.size ∧ tablePerm n elts[0]! = 1 ∧
      ∀ k, 0 < k → k < elts.size → par[k]! < k ∧ lab[k]! < gens.size ∧
        tablePerm n elts[k]! = tablePerm n elts[par[k]!]! * gg lab[k]! := by
  have hrep : ∀ k < elts.size, Rep n elts[k]! (tablePerm n elts[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := mulTreeOK_spec hn ⊤ (fun l hl => ⟨hg l hl, Subgroup.mem_top _⟩) h k hk
    rw [tablePerm_eq hc]
    exact hc
  simp only [CFSG.Sporadic.SmallOddCore.Native.mulTreeOK, Bool.and_eq_true, decide_eq_true_eq,
    allIn_eq_true] at h
  obtain ⟨⟨hpos, h0⟩, hk⟩ := h
  refine ⟨hpos, (tblEq_iff_eq (hrep 0 hpos) (Rep.idT hn)).1 h0, fun k hk0 hksz => ?_⟩
  obtain ⟨⟨hpar, hlab⟩, heq⟩ := hk k hk0 hksz
  exact ⟨hpar, hlab, (tblEq_iff_eq (hrep k hksz)
    (Rep.compT (hrep _ (hpar.trans hksz)) (hg _ hlab))).1 heq⟩

theorem inj_of_nodup {n : ℕ} {E : Array Table} (h : (E.toList.map (tablePerm n)).Nodup)
    {i j : ℕ} (hi : i < E.size) (hj : j < E.size)
    (e : tablePerm n E[i]! = tablePerm n E[j]!) : i = j := by
  have hi' : i < (E.toList.map (tablePerm n)).length := by simpa using hi
  have hj' : j < (E.toList.map (tablePerm n)).length := by simpa using hj
  refine (List.Nodup.getElem_inj_iff h (hi := hi') (hj := hj')).1 ?_
  simpa [getElem!_pos E i hi, getElem!_pos E j hj] using e

theorem tau_exists (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (h : tauOK = true) :
    ∃ ι : ↥Ly1080.Txy0 ≃* ↥Ly243.Txy0, ∀ (j : ℕ) (hj : j < 5),
      (ι ⟨Ly1080.txyG j, Ly1080.txyG_mem_Txy0 hY hj⟩ : Perm (Fin 243)) = Ly243.txyG j := by
  simp only [tauOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ht₂, hd₂⟩, hsz₂⟩, hsz₃⟩, hsucc⟩ := h
  have hsz₁ : Ly1080.txyTabs.size = 5 := (Ly1080.tablesOK_sizes (Ly1080.yCheck_tables hY)).2
  have hsz₄ : Ly243.txyTabs.size = 5 := (Ly243.tablesOK_parts hT).2.2.1
  have hg₁ : ∀ l < Ly1080.txyTabs.size, Rep 1080 Ly1080.txyTabs[l]! (Ly1080.txyG l) :=
    fun l hl => Ly1080.rep_txyTab hY (by omega)
  have hg₂ : ∀ l < Ly243.txyTabs.size, Rep 243 Ly243.txyTabs[l]! (Ly243.txyG l) :=
    fun l hl => Ly243.rep_txyTab hT (by omega)
  have hE₁ : ExactEnum 1080 Ly1080.Txy0 yEnum.1 := Ly1080.exactEnum_txy hY
  have htree₁ : CFSG.Sporadic.SmallOddCore.Native.mulTreeOK 1080 Ly1080.txyTabs yEnum.1
      yEnum.2.1 yEnum.2.2 = true := by
    have htxy := (Ly1080.yCheck_parts hY).2.2.2.1
    simp only [Ly1080.txyEnumOK, CFSG.Sporadic.SmallOddCore.enumOK, Bool.and_eq_true,
      beq_iff_eq, List.all_eq_true] at htxy
    exact htxy.1.1.1.2
  obtain ⟨hpos₁, h0₁, hstep₁⟩ := mulTree_facts (by norm_num) hg₁ htree₁
  obtain ⟨hpos₂, h0₂, hstep₂⟩ := mulTree_facts (by norm_num) hg₂ ht₂
  have hspec₂ := mulTreeOK_spec (by norm_num) Ly243.Txy0
    (fun l hl => ⟨hg₂ l hl, Ly243.txyG_mem_Txy0 hT (by omega)⟩) ht₂
  have hrep₂ : ∀ k < tEnum.size, Rep 243 tEnum[k]! (tablePerm 243 tEnum[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := hspec₂ k hk
    rw [tablePerm_eq hc]
    exact hc
  have hmem₂ : ∀ k < tEnum.size, tablePerm 243 tEnum[k]! ∈ Ly243.Txy0 := by
    intro k hk
    obtain ⟨c, hc, hcrep⟩ := hspec₂ k hk
    rw [tablePerm_eq hcrep]
    exact hc
  have hnodup₂ := nodup_of_hkeysDistinct (forall₂_tablePerm hrep₂) hd₂
  have hB : Ly243.Txy0 ≤ Subgroup.closure (Ly243.txyG '' {l | l < 5}) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨T, hT', rfl⟩
    have hT'' : T ∈ Ly243.txyTabs := by simpa using hT'
    obtain ⟨j, hj, e⟩ := Ly243.Txy0_gens hT hT''
    rw [e]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  exact exists_mulEquiv_of_tree (m := yEnum.1.size) (N := 5)
    (e₁ := fun k => tablePerm 1080 yEnum.1[k]!) (e₂ := fun k => tablePerm 243 tEnum[k]!)
    (g := Ly1080.txyG) (g' := Ly243.txyG) (par := fun k => yEnum.2.1[k]!)
    (lab := fun k => yEnum.2.2[k]!) hpos₁ h0₁ h0₂
    (fun k hk0 hk => ⟨(hstep₁ k hk0 hk).1, by have := (hstep₁ k hk0 hk).2.1; omega⟩)
    (fun k hk0 hk => (hstep₁ k hk0 hk).2.2)
    (fun k hk0 hk => (hstep₂ k hk0 (by omega)).2.2)
    (fun k hk l hl => by
      obtain ⟨⟨hk', e1⟩, e2⟩ := hsucc k hk l hl
      refine ⟨(succTab[k]!)[l]!, hk', ?_, ?_⟩
      · exact (tblEq_iff_eq (hE₁.rep _ hk') (Rep.compT (hE₁.rep k hk) (hg₁ l (by omega)))).1 e1
      · exact (tblEq_iff_eq (hrep₂ _ (by omega))
          (Rep.compT (hrep₂ k (by omega)) (hg₂ l (by omega)))).1 e2)
    (fun i hi j hj e => inj_of_nodup hE₁.nodup hi hj e)
    (fun i hi j hj e => inj_of_nodup hnodup₂ (by omega) (by omega) e)
    (fun k hk => hmem₂ k (by omega))
    (fun x hx => by
      obtain ⟨k, hk, hrep⟩ := hE₁.cover x hx
      exact ⟨k, hk, tablePerm_eq hrep⟩)
    (fun l hl => Ly1080.txyG_mem_Txy0 hY hl) hB

end CFSG.Sporadic.Recognition.LyonsSims.Tau
