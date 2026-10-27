module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDichot
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigWCard
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigIrr
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBKernel
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRestrict
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08tbt_isRefl_linRefl {n : ℕ} {g : Vn n ≃ₗ[ZMod 3] Vn n}
    (hg : IsRefl g) : GGLinRefl g := by
  obtain ⟨c, a, hac, hgv⟩ := hg
  let f : Module.Dual (ZMod 3) (Vn n) :=
    { toFun := fun v => a ⬝ᵥ v
      map_add' := fun v w => dotProduct_add a v w
      map_smul' := fun s v => by
        rw [dotProduct_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul] }
  refine (ggDepA_linRefl_iff (p := 3) (by norm_num) g).mpr ⟨c, f, ?_, ?_⟩
  · change a ⬝ᵥ c = 2
    exact hac
  · intro v
    change g v = v - (a ⬝ᵥ v) • c
    exact hgv v

private theorem ggQ2s08tbt_linRefl_conj {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (κ : V ≃ₗ[ZMod 3] V')
    {T : V ≃ₗ[ZMod 3] V} (h : GGLinRefl T) : GGLinRefl (ggLinConj κ T) := by
  rw [ggDepA_linRefl_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)] at h ⊢
  obtain ⟨c, f, hcf, hT⟩ := h
  refine ⟨κ c, f.comp κ.symm.toLinearMap, ?_, fun v => ?_⟩
  · change f (κ.symm (κ c)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hcf
  · rw [ggLinConj_apply, hT (κ.symm v)]
    change κ (κ.symm v - f (κ.symm v) • c) = v - f (κ.symm v) • κ c
    simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem ggQ2s08tbt_simple_refl [Finite G] (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) (i : M.Λ) :
    GGLinRefl (ggQ2CellLin M κ (M.simple i)) :=
  ggQ2s08tbt_linRefl_conj κ (ggQ2s08d_simple_refl M i).2.1

theorem ggQ2s08_bigB_test (hKG : GGReflClassLargeThree) [Finite G] (M : GGQ2LDatum 3 Bs L x)
    (hB : M.ShapeB) {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1) (κ : M.V ≃ₗ[ZMod 3] Vn lab.rank)
    {A Mg : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank)}
    (hT : TestHyp ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) (κ M.xV) A Mg)
    (hb : ∀ R : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank), R ≤ A →
      8 * Nat.card R < 3 ^ ((lab.rank - 1) * (lab.rank - 2) / 2))
    {r t : Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank} (hr : r ∈ Mg) (hrr : IsRefl r)
    (hrx : ¬ FixesLine (κ M.xV) r) (ht : t ∈ A) (htr : IsRefl t) (htx : ¬ FixesLine (κ M.xV) t) :
    False := by
  classical
  let W : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank) :=
    (ggAutomizer L Bs).map (ggQ2CellLin M κ)
  let R : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank) :=
    Subgroup.closure ((W : Set (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank)) ∪ {r, t})
  let H : Submodule (ZMod 3) (Vn lab.rank) := M.coSpan.map κ.toLinearMap
  have hWR : W ≤ R := fun w hw => Subgroup.subset_closure (Or.inl hw)
  have hrR : r ∈ R := Subgroup.subset_closure (Or.inr (by simp))
  have htR : t ∈ R := Subgroup.subset_closure (Or.inr (by simp))
  have hRA : R ≤ A := by
    refine (Subgroup.closure_le (K := A)).mpr ?_
    rintro a (haW | ha)
    · exact hT.le (hT.W_le haW)
    · rcases ha with rfl | rfl
      · exact hT.le hr
      · exact ht
  have hcardW : Nat.card W = (lab.rank + 1).factorial := by
    have h0 := ggQ2s08_big_W_card M hMW htag (by omega)
    have hmap : Nat.card W = Nat.card ↥(ggAutomizer L Bs) := by
      change Nat.card ((ggAutomizer L Bs).map (ggQ2CellLin M κ)) =
        Nat.card ↥(ggAutomizer L Bs)
      exact Subgroup.card_map_of_injective (ggQ2CellLin_injective M κ)
    rw [hmap, h0]
  have hWgen : W = Subgroup.closure (Set.range (fun i => ggQ2CellLin M κ (M.simple i))) := by
    change (ggAutomizer L Bs).map (ggQ2CellLin M κ) =
      Subgroup.closure (Set.range (fun i => ggQ2CellLin M κ (M.simple i)))
    rw [M.automizer_L, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨φ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
  have hW_le : W ≤ Subgroup.closure
      {a : Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank | a ∈ R ∧ GGLinRefl a} := by
    rw [hWgen]
    refine (Subgroup.closure_le (K := Subgroup.closure
      {a : Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank | a ∈ R ∧ GGLinRefl a})).mpr ?_
    rintro a ⟨i, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ggQ2s08tbt_simple_refl M κ i⟩
    exact hWR (Subgroup.mem_map_of_mem (ggQ2CellLin M κ)
      (by rw [M.automizer_L]; exact Subgroup.subset_closure (Set.mem_range_self i)))
  have hgen : R = Subgroup.closure
      {a : Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank | a ∈ R ∧ GGLinRefl a} := by
    apply le_antisymm
    · refine (Subgroup.closure_le (K := Subgroup.closure
        {a : Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank | a ∈ R ∧ GGLinRefl a})).mpr ?_
      rintro a (haW | ha)
      · exact hW_le haW
      · rcases ha with rfl | rfl
        · exact Subgroup.subset_closure ⟨hrR, ggQ2s08tbt_isRefl_linRefl hrr⟩
        · exact Subgroup.subset_closure ⟨htR, ggQ2s08tbt_isRefl_linRefl htr⟩
    · refine (Subgroup.closure_le (K := R)).mpr ?_
      intro a ha
      exact ha.1
  have hbR : 8 * Nat.card R < 3 ^ ((lab.rank - 1) * (lab.rank - 2) / 2) := hb R hRA
  have hb' : 8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2) := by
    refine lt_of_lt_of_le hbR (Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 3) ?_)
    apply Nat.div_le_div_right
    calc (lab.rank - 1) * (lab.rank - 2) ≤ (lab.rank - 1) * lab.rank :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = lab.rank * (lab.rank - 1) := Nat.mul_comm _ _
  have hWxV : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model φ M.xV = M.xV := by
    intro φ hφ
    have hmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.mem_span_singleton_self M.xV
    exact (mem_ggFixedSubmodule_iff.mp hmem) φ hφ
  have hWx : ∀ w ∈ W, w (κ M.xV) = κ M.xV := by
    intro w hw
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
    have h1 : κ (ggLin (p := 3) M.model φ (κ.symm (κ M.xV))) = κ M.xV := by
      rw [LinearEquiv.symm_apply_apply, hWxV φ hφ]
    exact (ggQ2CellLin_apply M κ φ (κ M.xV)).trans h1
  have hWfix : ∀ v : Vn lab.rank, (∀ w ∈ W, w v = v) →
      v ∈ Submodule.span (ZMod 3) {κ M.xV} := by
    intro v hv
    have h1 : κ.symm v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      have h2 : ggQ2CellLin M κ φ v = v := hv _ (Subgroup.mem_map_of_mem _ hφ)
      have h3 : κ (ggLin (p := 3) M.model φ (κ.symm v)) = v :=
        (ggQ2CellLin_apply M κ φ v).trans h2
      have h4 := congrArg κ.symm h3
      simpa [LinearEquiv.symm_apply_apply] using h4
    rw [M.fixed_x] at h1
    have h2 : v ∈ (Submodule.span (ZMod 3) {M.xV}).map κ.toLinearMap := by
      simpa [GGQ2LDatum.xV] using Submodule.mem_map_of_mem (f := κ.toLinearMap) h1
    simpa [Submodule.map_span, GGQ2LDatum.xV] using h2
  have hdisj0 : Disjoint M.coSpan (Submodule.span (ZMod 3) {M.xV}) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvco, hvspan⟩ := Submodule.mem_inf.mp hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvspan
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · exfalso
      apply hB.2.2.1
      have hx : M.xV = c⁻¹ • v := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hx]
      exact M.coSpan.smul_mem _ hvco
  have hcompl0 : IsCompl M.coSpan (Submodule.span (ZMod 3) {M.xV}) :=
    ⟨hdisj0, codisjoint_iff.mpr hB.2.2.2⟩
  have hH : IsCompl H (Submodule.span (ZMod 3) {κ M.xV}) := by
    have hmap := Submodule.isCompl_map κ hcompl0
    simpa [H, Submodule.map_span] using hmap
  have hdichGen : ∀ (P : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank)), W ≤ P →
      ∀ S : Submodule (ZMod 3) (Vn lab.rank),
      (∀ a ∈ P, ∀ u ∈ S, a u ∈ S) →
      S ≤ Submodule.span (ZMod 3) {κ M.xV} ∨ H ≤ S := by
    intro P hWP S hSP
    have hUinv : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model),
        ∀ u ∈ S.comap κ.toLinearMap, w u ∈ S.comap κ.toLinearMap := by
      intro w hw u hu
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
      rw [Submodule.mem_comap] at hu ⊢
      have hmem : ggQ2CellLin M κ φ ∈ P := hWP (Subgroup.mem_map_of_mem _ hφ)
      have h := hSP (ggQ2CellLin M κ φ) hmem (κ u) hu
      rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply] at h
      exact h
    rcases ggQ2s08_big_dichotomy M hlab hMW (S.comap κ.toLinearMap) hUinv with hle | hge
    · left
      intro s hs
      have hs' : κ.symm s ∈ S.comap κ.toLinearMap := by
        rw [Submodule.mem_comap]
        simpa using hs
      have h1 : κ.symm s ∈ Submodule.span (ZMod 3) {M.xV} := hle hs'
      have h2 : κ (κ.symm s) ∈ (Submodule.span (ZMod 3) {M.xV}).map κ.toLinearMap :=
        Submodule.mem_map_of_mem (f := κ.toLinearMap) h1
      simpa [Submodule.map_span] using h2
    · right
      have hmap : (S.comap κ.toLinearMap).map κ.toLinearMap = S :=
        (Submodule.map_comap_eq κ.toLinearMap S).trans
          (inf_eq_right.mpr (by
            rw [LinearMap.range_eq_top.mpr κ.surjective]
            exact le_top))
      calc H = M.coSpan.map κ.toLinearMap := rfl
        _ ≤ (S.comap κ.toLinearMap).map κ.toLinearMap := Submodule.map_mono hge
        _ = S := hmap
  have hWirr : ∀ S' : Submodule (ZMod 3) (Vn lab.rank), S' ≤ H →
      (∀ w ∈ W, ∀ u ∈ S', w u ∈ S') → S' = ⊥ ∨ S' = H := by
    intro S' hS'H hS'inv
    rcases hdichGen W le_rfl S' hS'inv with hle | hge
    · left
      apply le_antisymm _ bot_le
      intro s hs
      have hspan : s ∈ Submodule.span (ZMod 3) {κ M.xV} := hle hs
      have hthis : s ∈ H ⊓ Submodule.span (ZMod 3) {κ M.xV} :=
        Submodule.mem_inf.mpr ⟨hS'H hs, hspan⟩
      have hbot : H ⊓ Submodule.span (ZMod 3) {κ M.xV} = ⊥ :=
        disjoint_iff.mp hH.disjoint
      rw [hbot] at hthis
      simpa using hthis
    · right
      exact le_antisymm hS'H hge
  have hWfaith : ∀ w ∈ W, (∀ u ∈ H, w u = u) → w = 1 := by
    intro w hw hwfix
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ H ⊔ Submodule.span (ZMod 3) {κ M.xV} := by
      rw [codisjoint_iff.mp hH.codisjoint]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hv
    obtain ⟨h, hh, z, hz, hsum⟩ := hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    calc ggQ2CellLin M κ φ v
        = ggQ2CellLin M κ φ (h + z) := by rw [← hsum]
      _ = ggQ2CellLin M κ φ h + ggQ2CellLin M κ φ z := by rw [map_add]
      _ = ggQ2CellLin M κ φ h + ggQ2CellLin M κ φ (c • κ M.xV) := by rw [← hc]
      _ = ggQ2CellLin M κ φ h + c • ggQ2CellLin M κ φ (κ M.xV) := by rw [map_smul]
      _ = h + c • κ M.xV := by
            rw [hwfix h hh, hWx (ggQ2CellLin M κ φ) (Subgroup.mem_map_of_mem _ hφ)]
      _ = h + z := by rw [hc]
      _ = v := by rw [← hsum]
  have hcardΛ : Fintype.card M.Λ = lab.rank := by
    obtain ⟨e, -⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, htag] using hMW
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hfinH : Module.finrank (ZMod 3) H = lab.rank - 1 := by
    have hfr0 : Module.finrank (ZMod 3) M.coSpan = lab.rank - 1 := by
      have := hB.2.1
      omega
    change Module.finrank (ZMod 3) (M.coSpan.map κ.toLinearMap) = lab.rank - 1
    rw [LinearEquiv.finrank_map_eq, hfr0]
  have hWcard' : Nat.card W = ((lab.rank - 1) + 2).factorial := by
    rw [hcardW]
    congr 1
    omega
  have h3' : 3 ∣ (lab.rank - 1) + 2 := by
    rwa [show (lab.rank - 1) + 2 = lab.rank + 1 by omega]
  have h10 : 10 ≤ lab.rank - 1 := by omega
  have hb'' : 8 * Nat.card R < 3 ^ ((lab.rank - 1) * ((lab.rank - 1) - 1) / 2) := by
    rw [show (lab.rank - 1) - 1 = lab.rank - 2 by omega]
    exact hbR
  by_cases hirr : ∀ S : Submodule (ZMod 3) (Vn lab.rank),
      (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤
  · exact ggQ2s08_big_irr hKG (V := Vn lab.rank) (n := lab.rank)
      (Module.finrank_fin_fun (ZMod 3)) h3 (by omega) hcardW hWR hgen hb' hirr
  · rw [not_forall] at hirr
    obtain ⟨S, hS⟩ := hirr
    rw [not_imp] at hS
    obtain ⟨hSR, hSnot⟩ := hS
    rw [not_or] at hSnot
    obtain ⟨hSbot, hStop⟩ := hSnot
    have hSH : S = H := by
      rcases hdichGen R hWR S hSR with hle | hge
      · exfalso
        have hx0 : κ M.xV ≠ 0 := by
          intro h0
          apply hB.2.2.1
          have hzero : M.xV = 0 := by
            rw [← LinearEquiv.symm_apply_apply κ M.xV, h0, map_zero]
          rw [hzero]
          exact M.coSpan.zero_mem
        obtain ⟨u, huS, hu0⟩ := (Submodule.ne_bot_iff S).mp hSbot
        have huSpan : u ∈ Submodule.span (ZMod 3) {κ M.xV} := hle huS
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp huSpan
        have hc0 : c ≠ 0 := by
          intro hc0
          rw [hc0, zero_smul] at hc
          exact hu0 hc.symm
        have hspan_le : Submodule.span (ZMod 3) {κ M.xV} ≤ S := by
          rw [Submodule.span_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          have hx : κ M.xV = c⁻¹ • u := by
            rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [hx]
          exact S.smul_mem _ huS
        have hmem : r (κ M.xV) ∈ Submodule.span (ZMod 3) {κ M.xV} :=
          hle (hSR r hrR _ (hspan_le (Submodule.mem_span_singleton_self _)))
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmem
        have hd0 : d ≠ 0 := by
          intro hd0
          apply hx0
          have hr0 : r (κ M.xV) = 0 := by
            rw [hd0, zero_smul] at hd
            exact hd.symm
          exact r.injective (by rw [hr0, map_zero])
        have hdl : d = 1 ∨ d = -1 := by
          have hkey : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1 := by decide
          exact hkey d hd0
        rcases hdl with h1 | h1
        · exact hrx (Or.inl (by rw [← hd, h1, one_smul]))
        · exact hrx (Or.inr (by rw [← hd, h1]; exact neg_one_smul (ZMod 3) (κ M.xV)))
      · have hSleH : S ≤ H := by
          intro s hs
          have hv : s ∈ H ⊔ Submodule.span (ZMod 3) {κ M.xV} := by
            rw [codisjoint_iff.mp hH.codisjoint]
            exact Submodule.mem_top
          rw [Submodule.mem_sup] at hv
          obtain ⟨h, hh, z, hz, hsum⟩ := hv
          have hzS : z ∈ S := by
            have : z = s - h := by rw [← hsum]; abel
            rw [this]
            exact S.sub_mem hs (hge hh)
          have hz0 : z = 0 := by
            by_contra hz0
            apply hStop
            have hzSpan : z ∈ Submodule.span (ZMod 3) {κ M.xV} := hz
            obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hzSpan
            have hd0 : d ≠ 0 := by
              intro hd0
              rw [hd0, zero_smul] at hd
              exact hz0 hd.symm
            have hx0mem : κ M.xV ∈ S := by
              have hx : κ M.xV = d⁻¹ • z := by
                rw [← hd, smul_smul, inv_mul_cancel₀ hd0, one_smul]
              rw [hx]
              exact S.smul_mem _ hzS
            have hspanle : Submodule.span (ZMod 3) {κ M.xV} ≤ S := by
              rw [Submodule.span_le]
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              rw [hy]
              exact hx0mem
            have htop : (⊤ : Submodule (ZMod 3) (Vn lab.rank)) ≤ S := by
              rw [← codisjoint_iff.mp hH.codisjoint]
              exact sup_le hge hspanle
            exact top_le_iff.mp htop
          rw [← hsum, hz0, add_zero]
          exact hh
        exact le_antisymm hSleH hge
    have hpres : ∀ g ∈ R, ∀ u ∈ H, g u ∈ H := by
      intro g hg u hu
      have huS : u ∈ S := hSH.symm ▸ hu
      have hguS : g u ∈ S := hSR g hg u huS
      exact hSH ▸ hguS
    have hres : ∀ g ∈ R, ∃ w ∈ W, ∀ u ∈ H, g u = w u :=
      ggQ2s08_big_restrict hKG (V := Vn lab.rank) (d := lab.rank - 1)
        h3' h10 (H := H) hfinH hWcard' hWR hgen hpres hWirr hWfaith hb''
    have hfixAll : ∀ g ∈ R, FixesLine (κ M.xV) g :=
      ggQ2s08_bigB_kernel hH hWx hWfix hWR hRA hT.noTransv hpres hres
    exact htx (hfixAll t htR)

end CFSG.StandardType

end
