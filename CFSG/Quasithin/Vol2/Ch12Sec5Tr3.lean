module

public import CFSG.Quasithin.Vol2.Ch12Sec5Tr2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125Tr S125Tr2 S125W Matrix
open CFSG.LieType.SteinbergBR.BlockPar CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Tr3

theorem pr5_injective : Function.Injective JonesParshall.pr5 := by decide

theorem pr5_lt (k : Fin 10) : (JonesParshall.pr5 k).1 < (JonesParshall.pr5 k).2 := by
  revert k
  decide

theorem wedgeMat_of_fix {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} {d : ℕ}
    (hM : ∀ i c : Fin 5, c.val < d → M i c = if i = c then 1 else 0) {l : Fin 10}
    (hl : (JonesParshall.pr5 l).2.val < d) (k : Fin 10) :
    JonesParshall.wedgeMat M k l = if k = l then 1 else 0 := by
  have hl1 : (JonesParshall.pr5 l).1.val < d :=
    lt_trans (show (JonesParshall.pr5 l).1.val < (JonesParshall.pr5 l).2.val from pr5_lt l) hl
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, hM _ _ hl1, hM _ _ hl]
  have hk := pr5_lt k
  have hlt := pr5_lt l
  have hkl : k = l ↔ (JonesParshall.pr5 k).1 = (JonesParshall.pr5 l).1 ∧
      (JonesParshall.pr5 k).2 = (JonesParshall.pr5 l).2 :=
    ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => pr5_injective (Prod.ext h1 h2)⟩
  generalize (JonesParshall.pr5 k).1 = a at hk hkl ⊢
  generalize (JonesParshall.pr5 k).2 = b at hk hkl ⊢
  generalize (JonesParshall.pr5 l).1 = c at hlt hkl ⊢
  generalize (JonesParshall.pr5 l).2 = c' at hlt hkl ⊢
  rw [show (if k = l then (1 : ZMod 2) else 0) = if a = c ∧ b = c' then 1 else 0 from
    if_congr hkl rfl rfl]
  have hcc : c ≠ c' := ne_of_lt hlt
  have hab : a ≠ b := ne_of_lt hk
  by_cases hac : a = c
  · subst hac
    have hac' : a ≠ c' := hcc
    by_cases hbc' : b = c'
    · subst hbc'
      simp [hac', hab.symm]
    · simp [hbc', hac']
  · by_cases hac' : a = c'
    · subst hac'
      have hbc : b ≠ c := fun h => by
        subst h
        exact absurd (lt_trans hk hlt) (lt_irrefl _)
      simp [hac, hbc]
    · simp [hac, hac']

theorem wedgeMat_mulVec_of_fix {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} {d : ℕ}
    (hM : ∀ i c : Fin 5, c.val < d → M i c = if i = c then 1 else 0) {x : Fin 10 → ZMod 2}
    (hx : ∀ k, d ≤ (JonesParshall.pr5 k).2.val → x k = 0) :
    JonesParshall.wedgeMat M *ᵥ x = x := by
  funext k
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single k]
  · by_cases hk : (JonesParshall.pr5 k).2.val < d
    · rw [wedgeMat_of_fix hM hk k]
      simp
    · rw [hx k (not_lt.1 hk), mul_zero]
  · intro l _ hlk
    by_cases hl : (JonesParshall.pr5 l).2.val < d
    · rw [wedgeMat_of_fix hM hl k]
      simp [Ne.symm hlk]
    · rw [hx l (not_lt.1 hl), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem wedgeMat_of_fixV4 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (h0 : ∀ i : Fin 5, M i 0 = if i = 0 then 1 else 0)
    (h1 : ∀ i j : Fin 5, 1 ≤ i.val → 1 ≤ j.val → M i j = if i = j then 1 else 0) {l : Fin 10}
    (hl : (JonesParshall.pr5 l).1 = 0) (k : Fin 10) :
    JonesParshall.wedgeMat M k l = if k = l then 1 else 0 := by
  have hk := pr5_lt k
  have hlt := pr5_lt l
  have hkl : k = l ↔ (JonesParshall.pr5 k).1 = (JonesParshall.pr5 l).1 ∧
      (JonesParshall.pr5 k).2 = (JonesParshall.pr5 l).2 :=
    ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => pr5_injective (Prod.ext h1 h2)⟩
  simp only [JonesParshall.wedgeMat, Matrix.of_apply, hl, h0]
  rw [hl] at hlt hkl
  have hb : 1 ≤ (JonesParshall.pr5 k).2.val := by
    have : (JonesParshall.pr5 k).1.val < (JonesParshall.pr5 k).2.val := hk
    omega
  have hj : 1 ≤ (JonesParshall.pr5 l).2.val := by
    have : (0 : Fin 5).val < (JonesParshall.pr5 l).2.val := hlt
    have h0 : (0 : Fin 5).val = 0 := rfl
    omega
  rw [h1 _ _ hb hj]
  have hb0 : (JonesParshall.pr5 k).2 ≠ 0 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  rw [if_congr hkl rfl rfl]
  generalize (JonesParshall.pr5 k).1 = a at hkl ⊢
  generalize (JonesParshall.pr5 k).2 = b at hb0 hkl ⊢
  generalize (JonesParshall.pr5 l).2 = c' at hkl ⊢
  by_cases ha : a = 0
  · subst ha
    by_cases hbc : b = c'
    · subst hbc
      simp [hb0]
    · simp [hbc, hb0]
  · simp [ha, hb0]

theorem wedgeMat_mulVec_V4 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)}
    (h0 : ∀ i : Fin 5, M i 0 = if i = 0 then 1 else 0)
    (h1 : ∀ i j : Fin 5, 1 ≤ i.val → 1 ≤ j.val → M i j = if i = j then 1 else 0)
    {x : Fin 10 → ZMod 2} (hx : ∀ k, (JonesParshall.pr5 k).1 ≠ 0 → x k = 0) :
    JonesParshall.wedgeMat M *ᵥ x = x := by
  funext k
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single k]
  · by_cases hk : (JonesParshall.pr5 k).1 = 0
    · rw [wedgeMat_of_fixV4 h0 h1 hk k]
      simp
    · rw [hx k hk, mul_zero]
  · intro l _ hlk
    by_cases hl : (JonesParshall.pr5 l).1 = 0
    · rw [wedgeMat_of_fixV4 h0 h1 hl k]
      simp [Ne.symm hlk]
    · rw [hx l hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem sumEquiv_symm_of_lt {d e : ℕ} (hde : d + e = 5) {c : Fin 5} (hc : c.val < d) :
    (sumEquiv hde).symm c = Sum.inl ⟨c.val, hc⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [sumEquiv_inl]

theorem sumEquiv_symm_of_le {d e : ℕ} (hde : d + e = 5) {c : Fin 5} (hc : d ≤ c.val) :
    (sumEquiv hde).symm c = Sum.inr ⟨c.val - d, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [sumEquiv_inr]
  simp
  omega

theorem reindex_fix_of_blocks₁₁ {d e : ℕ} (hde : d + e = 5)
    {g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)}
    (hg : g ∈ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (h11 : g.val.toBlocks₁₁ = 1) (i c : Fin 5) (hc : c.val < d) :
    (reindexSL (ZMod 2) hde g).val i c = if i = c then 1 else 0 := by
  rw [reindexSL_val, Matrix.reindex_apply, Matrix.submatrix_apply, sumEquiv_symm_of_lt hde hc]
  by_cases hi : i.val < d
  · rw [sumEquiv_symm_of_lt hde hi]
    have := congrFun₂ h11 ⟨i.val, hi⟩ ⟨c.val, hc⟩
    change g.val.toBlocks₁₁ ⟨i.val, hi⟩ ⟨c.val, hc⟩ = _
    rw [this, Matrix.one_apply]
    by_cases hic : i = c
    · subst hic
      simp
    · have : (⟨i.val, hi⟩ : Fin d) ≠ ⟨c.val, hc⟩ := fun h => hic (Fin.ext (by
        have := congrArg Fin.val h
        simpa using this))
      simp [this, hic]
  · rw [sumEquiv_symm_of_le hde (not_lt.1 hi)]
    have h21 : g.val.toBlocks₂₁ = 0 := hg
    have := congrFun₂ h21 ⟨i.val - d, by omega⟩ ⟨c.val, hc⟩
    change g.val.toBlocks₂₁ ⟨i.val - d, by omega⟩ ⟨c.val, hc⟩ = _
    rw [this]
    have hic : i ≠ c := fun h => by rw [h] at hi; exact hi hc
    simp [hic]

theorem reindex_fixV4 {g : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 4) (ZMod 2)}
    (hg : g ∈ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 4) (ZMod 2))))
    (h22 : g.val.toBlocks₂₂ = 1) :
    (∀ i : Fin 5, (reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5) g).val i 0 =
      if i = 0 then 1 else 0) ∧
    ∀ i j : Fin 5, 1 ≤ i.val → 1 ≤ j.val →
      (reindexSL (ZMod 2) (by norm_num : 1 + 4 = 5) g).val i j = if i = j then 1 else 0 := by
  have h11 : g.val.toBlocks₁₁ = 1 := by
    have hdet := det_eq_of_mem_parQ hg
    rw [h22, Matrix.det_one, mul_one, Matrix.det_unique] at hdet
    ext i j
    fin_cases i
    fin_cases j
    simpa using hdet
  refine ⟨fun i => reindex_fix_of_blocks₁₁ _ hg h11 i 0 (by decide), fun i j hi hj => ?_⟩
  rw [reindexSL_val, Matrix.reindex_apply, Matrix.submatrix_apply,
    sumEquiv_symm_of_le _ (by simpa using hi), sumEquiv_symm_of_le _ (by simpa using hj)]
  have := congrFun₂ h22 ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
  change g.val.toBlocks₂₂ ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ = _
  rw [this, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have : (⟨i.val - 1, by omega⟩ : Fin 4) ≠ ⟨j.val - 1, by omega⟩ := fun h => hij (Fin.ext (by
      have := congrArg Fin.val h
      simp at this
      omega))
    simp [this, hij]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem rbar_le_kerChiL (F : Frame125 T L V) (hf : S125Ex.Facts125 G T L V)
    {S : Finset (Fin 10)} {d e : ℕ} (hde : d + e = 5)
    (hstab : F.IsStab (mi T L (F.sub S)) d)
    (hTW : T ≤ Subgroup.normalizer ((F.sub S : Subgroup G) : Set G))
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hJQ : J ≤ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (hres : (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J)
    (hJ : ∀ A : GL (Fin d) (ZMod 2), ∃ (g : _) (hg : g ∈ J),
      chiL (ZMod 2) (Fin d) (Fin e) ⟨g, hJQ hg⟩ = A)
    (hO : S125Pb.NoO2 (GL (Fin d) (ZMod 2))) {x : MulAut ↥V}
    (hx : x ∈ autOn (ri T L (F.sub S)) V) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) (_ : g ∈ parQ),
      g.val.toBlocks₁₁ = 1 ∧ theta F hde g = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := F.sub S with hW
  set Q := (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))) with hQ
  have hliL : li L W ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXV : li L W ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hliL.trans hf.normalizes) hf.T_le
  obtain ⟨hRX, hRn, hR2⟩ := autOn_pCoreOf_props hXV
  have hLb := lbar_eq F hf.normalizes hf.T_le hde hstab hres
  have hLX : autOn (li L W) V ≤ autOn (li L W ⊔ T) V := A4.autOn_mono le_sup_left
  have hXM : autOn (li L W ⊔ T) V ≤ Q.map (theta F hde) := by
    rw [← autOn_mi_eq_theta F hde hstab]
    exact A4.autOn_mono (sup_le_mi hTW)
  let N' : Subgroup ↥Q := (autOn (ri T L W) V).comap ((theta F hde).comp Q.subtype)
  let K : Subgroup (GL (Fin d) (ZMod 2)) := N'.map (chiL (ZMod 2) (Fin d) (Fin e))
  have hKn : K.Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ A
    obtain ⟨g, hg, rfl⟩ := hJ A
    refine ⟨⟨g, hJQ hg⟩ * n * ⟨g, hJQ hg⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change (theta F hde) (g * (n : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) * g⁻¹) ∈
      autOn (ri T L W) V
    rw [map_mul, map_mul, map_inv]
    have hgX : theta F hde g ∈ autOn (li L W ⊔ T) V := hLX (hLb ▸ ⟨g, hg, rfl⟩)
    exact hRn _ hgX _ hn
  have hK2 : IsPGroup 2 K := by
    have hN2 : IsPGroup 2 N' := by
      let φ : ↥N' →* ↥(autOn (ri T L W) V) :=
        { toFun := fun n => ⟨theta F hde (n : ↥Q), n.2⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      refine hR2.of_injective φ (fun a b h => Subtype.ext (Subtype.ext (theta_injective F hde ?_)))
      have := congrArg (fun x : ↥(autOn (ri T L W) V) => (x : MulAut ↥V)) h
      exact this
    exact hN2.map _
  have hKb := hO K hKn hK2
  obtain ⟨g, hg, rfl⟩ := hXM (hRX hx)
  refine ⟨g, hg, ?_, rfl⟩
  have hgK : chiL (ZMod 2) (Fin d) (Fin e) ⟨g, hg⟩ ∈ K := ⟨⟨g, hg⟩, hx, rfl⟩
  rw [hKb, Subgroup.mem_bot] at hgK
  exact congrArg (fun A : GL (Fin d) (ZMod 2) => (A : Matrix (Fin d) (Fin d) (ZMod 2))) hgK

theorem rbar_le_kerChiR (F : Frame125 T L V) (hf : S125Ex.Facts125 G T L V)
    {S : Finset (Fin 10)} {d e : ℕ} (hde : d + e = 5)
    (hstab : F.IsStab (mi T L (F.sub S)) d)
    (hTW : T ≤ Subgroup.normalizer ((F.sub S : Subgroup G) : Set G))
    {J : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))}
    (hJQ : J ≤ (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))))
    (hres : (CFSG.perfectResidual ↥(parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e)
      (ZMod 2)))).map parQ.subtype = J)
    (hJ : ∀ A : GL (Fin e) (ZMod 2), ∃ (g : _) (hg : g ∈ J),
      chiR (ZMod 2) (Fin d) (Fin e) ⟨g, hJQ hg⟩ = A)
    (hO : S125Pb.NoO2 (GL (Fin e) (ZMod 2))) {x : MulAut ↥V}
    (hx : x ∈ autOn (ri T L (F.sub S)) V) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) (_ : g ∈ parQ),
      g.val.toBlocks₂₂ = 1 ∧ theta F hde g = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := F.sub S with hW
  set Q := (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2))) with hQ
  have hliL : li L W ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXV : li L W ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hliL.trans hf.normalizes) hf.T_le
  obtain ⟨hRX, hRn, hR2⟩ := autOn_pCoreOf_props hXV
  have hLb := lbar_eq F hf.normalizes hf.T_le hde hstab hres
  have hLX : autOn (li L W) V ≤ autOn (li L W ⊔ T) V := A4.autOn_mono le_sup_left
  have hXM : autOn (li L W ⊔ T) V ≤ Q.map (theta F hde) := by
    rw [← autOn_mi_eq_theta F hde hstab]
    exact A4.autOn_mono (sup_le_mi hTW)
  let N' : Subgroup ↥Q := (autOn (ri T L W) V).comap ((theta F hde).comp Q.subtype)
  let K : Subgroup (GL (Fin e) (ZMod 2)) := N'.map (chiR (ZMod 2) (Fin d) (Fin e))
  have hKn : K.Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ A
    obtain ⟨g, hg, rfl⟩ := hJ A
    refine ⟨⟨g, hJQ hg⟩ * n * ⟨g, hJQ hg⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change (theta F hde) (g * (n : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) * g⁻¹) ∈
      autOn (ri T L W) V
    rw [map_mul, map_mul, map_inv]
    have hgX : theta F hde g ∈ autOn (li L W ⊔ T) V := hLX (hLb ▸ ⟨g, hg, rfl⟩)
    exact hRn _ hgX _ hn
  have hK2 : IsPGroup 2 K := by
    have hN2 : IsPGroup 2 N' := by
      let φ : ↥N' →* ↥(autOn (ri T L W) V) :=
        { toFun := fun n => ⟨theta F hde (n : ↥Q), n.2⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      refine hR2.of_injective φ (fun a b h => Subtype.ext (Subtype.ext (theta_injective F hde ?_)))
      have := congrArg (fun x : ↥(autOn (ri T L W) V) => (x : MulAut ↥V)) h
      exact this
    exact hN2.map _
  have hKb := hO K hKn hK2
  obtain ⟨g, hg, rfl⟩ := hXM (hRX hx)
  refine ⟨g, hg, ?_, rfl⟩
  have hgK : chiR (ZMod 2) (Fin d) (Fin e) ⟨g, hg⟩ ∈ K := ⟨⟨g, hg⟩, hx, rfl⟩
  rw [hKb, Subgroup.mem_bot] at hgK
  exact congrArg (fun A : GL (Fin e) (ZMod 2) => (A : Matrix (Fin e) (Fin e) (ZMod 2))) hgK

omit [Finite G] in
theorem ri_le_centralizer {W : Subgroup G} (hWV : W ≤ V)
    (hRV : ri T L W ≤ Subgroup.normalizer (V : Set G))
    (hfix : ∀ x ∈ autOn (ri T L W) V, ∀ v : ↥V, (v : G) ∈ W → x v = v) :
    ri T L W ≤ Subgroup.centralizer (W : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := hfix _ (mem_autOn_iff_exists.mpr ⟨r, hRV hr, hr, rfl⟩) ⟨w, hWV hw⟩ hw
  have h2 : r * w * r⁻¹ = w := congrArg Subtype.val h
  calc w * r = r * w * r⁻¹ * r := by rw [h2]
    _ = r * w := by group

omit [Finite G] in
theorem e_theta_apply (F : Frame125 T L V) {d e : ℕ} (hde : d + e = 5)
    (g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) (v : ↥V) :
    F.e (theta F hde g v) = Multiplicative.ofAdd (JonesParshall.wedgeMat
      ((reindexSL (ZMod 2) hde g : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (F.e v)) := by
  change F.e (((F.γ.symm (reindexSL (ZMod 2) hde g) : ↥(autOn L V)) : MulAut ↥V) v) = _
  rw [F.wedge, MulEquiv.apply_symm_apply, S125ZV.wedgeRep_apply]

end S125Tr3

end CFSG.Quasithin.H13
