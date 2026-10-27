module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFixLine_finite {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Type} [Finite ι] (s : ι → (V ≃ₗ[ZMod p] V)) (hs : ∀ i, GGLinRefl (s i)) {x : V}
    (hfix : ggLinFix (Set.range s) = Submodule.span (ZMod p) {x}) : Module.Finite (ZMod p) V := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let φ : V →ₗ[ZMod p] (ι → V) :=
    { toFun := fun v i => s i v - v
      map_add' := fun u v => by
        funext i
        simp only [Pi.add_apply, map_add]
        abel
      map_smul' := fun c v => by
        funext i
        simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }
  have hker : LinearMap.ker φ = ggLinFix (Set.range s) := by
    ext v
    change φ v = 0 ↔ ∀ a ∈ Set.range s, a v = v
    rw [Set.forall_mem_range]
    constructor
    · intro hv i
      have := congr_fun hv i
      change s i v - v = 0 at this
      exact sub_eq_zero.mp this
    · intro hv
      funext i
      change s i v - v = 0
      exact sub_eq_zero.mpr (hv i)
  have hfin_move : ∀ i, Module.Finite (ZMod p) ↥(ggLinMove (s i)) := by
    intro i
    apply FiniteDimensional.of_finrank_pos
    rw [(hs i).2]
    norm_num
  have hy : ∀ i, ∃ y : V, y ∈ ggLinMove (s i) ∧ y ≠ 0 := by
    intro i
    have hne : ggLinMove (s i) ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank (ZMod p) ↥(ggLinMove (s i)) = 0 := by
        rw [hbot]; simp
      rw [(hs i).2] at h0
      exact one_ne_zero h0
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  choose y hy_mem hy_ne using hy
  have hspan : ∀ i, ggLinMove (s i) = Submodule.span (ZMod p) {y i} := by
    intro i
    haveI : FiniteDimensional (ZMod p) ↥(ggLinMove (s i)) := hfin_move i
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hy_mem i
    · rw [finrank_span_singleton (hy_ne i), (hs i).2]
  let W : Submodule (ZMod p) (ι → V) :=
    Submodule.span (ZMod p) (Set.range (fun i => Pi.single i (y i)))
  have hWfin : Module.Finite (ZMod p) ↥W := by
    have hrf : (Set.range (fun i => Pi.single i (y i))).Finite := by
      rw [← Set.image_univ]
      exact Set.finite_univ.image _
    exact FiniteDimensional.span_of_finite (ZMod p) hrf
  have hrange_le : LinearMap.range φ ≤ W := by
    rintro _ ⟨v, rfl⟩
    change (fun i => s i v - v) ∈ W
    have hdecomp : ∀ i, ∃ a : ZMod p, a • y i = s i v - v := by
      intro i
      have hmem : s i v - v ∈ ggLinMove (s i) := ⟨v, by simp [ggLinMove]⟩
      rw [hspan i] at hmem
      exact Submodule.mem_span_singleton.mp hmem
    choose a ha using hdecomp
    have hsum : (fun i => s i v - v) = ∑ i, a i • Pi.single i (y i) := by
      funext j
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same]
        exact (ha j).symm
      · intro b _ hbj
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hbj), smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange_fin : Module.Finite (ZMod p) ↥(LinearMap.range φ) := by
    haveI : FiniteDimensional (ZMod p) ↥W := hWfin
    exact Submodule.finiteDimensional_of_le hrange_le
  have htop : (⊤ : Submodule (ZMod p) V).FG := by
    haveI : Module.Finite (ZMod p) ↥(LinearMap.range φ) := hrange_fin
    refine Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_
    · rw [Submodule.map_top]
      exact Submodule.FG.of_finite
    · rw [top_inf_eq, hker, hfix]
      exact Submodule.fg_span (Set.finite_singleton x)
  haveI : Module.Finite (ZMod p) ↥(⊤ : Submodule (ZMod p) V) :=
    Module.Finite.iff_fg.mpr htop
  exact Module.Finite.equiv (Submodule.topEquiv)

private theorem l6f1_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private lemma l6f1_exists_neighbor (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    ∃ j : Fin m, j ≠ i ∧ CartanMatrix.A m j i = -1 := by
  by_cases h : (i : ℕ) + 1 < m
  · refine ⟨⟨(i : ℕ) + 1, h⟩, ?_, ?_⟩
    · intro hji
      have := congrArg Fin.val hji
      simp only [Fin.val_mk] at this
      omega
    · rw [l6f1_cartanA_entry]
      rw [if_neg (by intro hji; have := congrArg Fin.val hji; simp only [Fin.val_mk] at this; omega),
          if_pos (Or.inr rfl)]
  · have hi : (i : ℕ) + 1 = m := by omega
    have hpos : 1 ≤ (i : ℕ) := by omega
    refine ⟨⟨(i : ℕ) - 1, by omega⟩, ?_, ?_⟩
    · intro hji
      have := congrArg Fin.val hji
      simp only [Fin.val_mk] at this
      omega
    · rw [l6f1_cartanA_entry]
      rw [if_neg (by intro hji; have := congrArg Fin.val hji; simp only [Fin.val_mk] at this; omega),
          if_pos (Or.inl (by simp only [Fin.val_mk]; omega))]

private lemma l6f1_z_ne_zero {p N : ℕ} [Fact p.Prime] (hN : 2 ≤ N)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    (hind : LinearIndependent (ZMod p) h) :
    (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) ≠ 0 := by
  intro h0
  have h2 := (Fintype.linearIndependent_iff.mp hind)
    (fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)) h0 ⟨0, by omega⟩
  simp at h2

private lemma l6f1_inf_eq_span {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    (hind : LinearIndependent (ZMod p) h)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hr : ∀ i v, r i v = v - α i v • h i) :
    Submodule.span (ZMod p) (Set.range h) ⊓ ggLinFix (Set.range r) =
      Submodule.span (ZMod p)
        {∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k} := by
  let z : V := ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k
  change Submodule.span (ZMod p) (Set.range h) ⊓ ggLinFix (Set.range r) =
    Submodule.span (ZMod p) {z}
  apply le_antisymm
  · intro u hu
    obtain ⟨huR, huF⟩ := Submodule.mem_inf.mp hu
    have huF' : ∀ j, r j u = u := fun j => huF (r j) ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp huR
    have hh_ne : ∀ i, h i ≠ 0 := fun i => hind.ne_zero i
    have hker_c : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
      intro j
      have hαu : α j u = 0 := by
        have h' : u - α j u • h j = u := by rw [← hr j u]; exact huF' j
        have h2 : α j u • h j = 0 := by
          have h'' : u = u + α j u • h j := sub_eq_iff_eq_add.mp h'
          exact (add_left_cancel (by rw [add_zero]; exact h'')).symm
        rcases smul_eq_zero.mp h2 with hh | hh
        · exact hh
        · exact absurd hh (hh_ne j)
      have hsum : α j u = ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) := by
        rw [← hc, map_sum]
        simp only [map_smul, smul_eq_mul, hpair]
      have h1 : ∑ k, c k * (CartanMatrix.A (N - 1) j k : ZMod p) = 0 := by
        rw [← hsum]; exact hαu
      rw [← h1]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
    have hd_ne : d ≠ 0 := by
      intro hd
      have := congr_fun hd ⟨0, by omega⟩
      simp [d] at this
    have hd_ker : ∀ j, ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0 := by
      intro j
      simpa [d] using l6aF_A_mul_d (p := p) (N := N) hpN j
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one (p := p) (N := N - 1) d c hd_ker hker_c hd_ne
    have hcd : ∀ k, c k = l * d k := by
      intro k
      have hk := congr_fun hl k
      rwa [Pi.smul_apply, smul_eq_mul] at hk
    rw [Submodule.mem_span_singleton]
    refine ⟨l, ?_⟩
    rw [← hc]
    change l • (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) = ∑ k, c k • h k
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, hcd k]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · change ∀ a ∈ Set.range r, a z = z
      rintro a ⟨i, rfl⟩
      have hzi : α i z = 0 := by
        have h1 := l6aF_A_mul_d (p := p) (N := N) hpN i
        change α i (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) = 0
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, hpair]
        rw [← h1]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hr i z, hzi, zero_smul, sub_zero]

theorem ggFixLine_fix_bounds {p N : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hN : 5 ≤ N) (hpN : p ∣ N)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hV : Module.finrank (ZMod p) V ≤ N) {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    (hind : LinearIndependent (ZMod p) h)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hr : ∀ i v, r i v = v - α i v • h i) :
    1 ≤ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ∧
      Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 2 := by
  let R : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let F : Submodule (ZMod p) V := ggLinFix (Set.range r)
  let z : V := ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k
  change 1 ≤ Module.finrank (ZMod p) ↥F ∧ Module.finrank (ZMod p) ↥F ≤ 2
  have hRinf : R ⊓ F = Submodule.span (ZMod p) {z} := by
    change Submodule.span (ZMod p) (Set.range h) ⊓ ggLinFix (Set.range r) =
      Submodule.span (ZMod p) {z}
    exact l6f1_inf_eq_span (p := p) (N := N) hpN (by omega) hind hpair hr
  have hz_ne : z ≠ 0 := by
    change (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) ≠ 0
    exact l6f1_z_ne_zero (p := p) (N := N) (by omega) hind
  have hRdim : Module.finrank (ZMod p) ↥R = N - 1 := by
    change Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) = N - 1
    rw [finrank_span_eq_card (R := ZMod p) (b := h) hind, Fintype.card_fin]
  have hinfdim : Module.finrank (ZMod p) ↥(R ⊓ F) = 1 := by
    rw [hRinf]
    exact finrank_span_singleton hz_ne
  have hz_inf : z ∈ R ⊓ F := by
    rw [hRinf]
    exact Submodule.subset_span (Set.mem_singleton z)
  have hzF : z ∈ F := (Submodule.mem_inf.mp hz_inf).2
  have hFpos : 0 < Module.finrank (ZMod p) ↥F := by
    haveI : Nontrivial ↥F := by
      refine ⟨⟨⟨z, hzF⟩, 0, ?_⟩⟩
      intro h
      exact hz_ne (congrArg Subtype.val h)
    haveI : Module.Finite (ZMod p) ↥F := by
      haveI : Module.Finite (ZMod p) ↥(⊤ : Submodule (ZMod p) V) :=
        Module.Finite.equiv (Submodule.topEquiv.symm)
      exact Submodule.finiteDimensional_of_le (le_top : F ≤ ⊤)
    exact Module.finrank_pos
  have hsup_le : Module.finrank (ZMod p) ↥(R ⊔ F) ≤ N := by
    calc Module.finrank (ZMod p) ↥(R ⊔ F) ≤ Module.finrank (ZMod p) V :=
          Submodule.finrank_le (R ⊔ F)
      _ ≤ N := hV
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq R F
  have hFeq : Module.finrank (ZMod p) ↥(R ⊔ F) + 1 =
      (N - 1) + Module.finrank (ZMod p) ↥F := by
    have := hrank
    rw [hinfdim, hRdim] at this
    omega
  have hFle : Module.finrank (ZMod p) ↥F ≤ 2 := by omega
  exact ⟨hFpos, hFle⟩

theorem ggFixLine_split {p N : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hN : 5 ≤ N) (hpN : p ∣ N)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (hV : Module.finrank (ZMod p) V ≤ N) {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    (hind : LinearIndependent (ZMod p) h)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hr : ∀ i v, r i v = v - α i v • h i)
    (hF : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2) :
    Module.finrank (ZMod p) V = N ∧
      ∃ e : V, e ∈ ggLinFix (Set.range r) ∧
        IsCompl (Submodule.span (ZMod p) (Set.range h)) (Submodule.span (ZMod p) {e}) := by
  let R : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let F : Submodule (ZMod p) V := ggLinFix (Set.range r)
  let z : V := ∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k
  change Module.finrank (ZMod p) V = N ∧ ∃ e : V, e ∈ F ∧
      IsCompl R (Submodule.span (ZMod p) {e})
  have hF2 : Module.finrank (ZMod p) ↥F = 2 := hF
  have hRinf : R ⊓ F = Submodule.span (ZMod p) {z} := by
    change Submodule.span (ZMod p) (Set.range h) ⊓ ggLinFix (Set.range r) =
      Submodule.span (ZMod p) {z}
    exact l6f1_inf_eq_span (p := p) (N := N) hpN (by omega) hind hpair hr
  have hz_ne : z ≠ 0 := by
    change (∑ k : Fin (N - 1), (((k : ℕ) + 1 : ℕ) : ZMod p) • h k) ≠ 0
    exact l6f1_z_ne_zero (p := p) (N := N) (by omega) hind
  have hRdim : Module.finrank (ZMod p) ↥R = N - 1 := by
    change Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) = N - 1
    rw [finrank_span_eq_card (R := ZMod p) (b := h) hind, Fintype.card_fin]
  have hinfdim : Module.finrank (ZMod p) ↥(R ⊓ F) = 1 := by
    rw [hRinf]
    exact finrank_span_singleton hz_ne
  have hsupdim : Module.finrank (ZMod p) ↥(R ⊔ F) = N := by
    have hrank := Submodule.finrank_sup_add_finrank_inf_eq R F
    rw [hinfdim, hRdim, hF2] at hrank
    omega
  have hVdim : Module.finrank (ZMod p) V = N := by
    have hle : Module.finrank (ZMod p) ↥(R ⊔ F) ≤ Module.finrank (ZMod p) V :=
      Submodule.finrank_le (R ⊔ F)
    omega
  have hsup_top : R ⊔ F = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hsupdim, hVdim])
  have hex : ∃ e, e ∈ F ∧ e ∉ R := by
    by_contra h
    push Not at h
    have hFR : F ≤ R := fun x hx => h x hx
    have hinf_eq : R ⊓ F = F := inf_eq_right.mpr hFR
    have h1 : Module.finrank (ZMod p) ↥F = 1 := by
      rw [← hinf_eq]; exact hinfdim
    omega
  obtain ⟨e, heF, heR⟩ := hex
  refine ⟨hVdim, e, heF, ?_⟩
  have he_ne : e ≠ 0 := by
    intro h0
    exact heR (h0 ▸ R.zero_mem)
  rw [isCompl_iff]
  constructor
  · exact Submodule.disjoint_span_singleton.mpr (fun hR => absurd hR heR)
  · rw [codisjoint_iff_le_sup]
    have hd : Disjoint R (Submodule.span (ZMod p) {e}) :=
      Submodule.disjoint_span_singleton.mpr (fun hR => absurd hR heR)
    have hdisj : R ⊓ Submodule.span (ZMod p) {e} = ⊥ := disjoint_iff.mp hd
    have hfinf : Module.finrank (ZMod p) ↥(R ⊓ Submodule.span (ZMod p) {e}) = 0 := by
      rw [hdisj]
      simp
    have hrank := Submodule.finrank_sup_add_finrank_inf_eq R (Submodule.span (ZMod p) {e})
    rw [hfinf, hRdim, finrank_span_singleton he_ne, add_zero] at hrank
    have htop : R ⊔ Submodule.span (ZMod p) {e} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      omega
    rw [htop]

theorem ggFixLine_invariant_line {p N : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hN : 5 ≤ N)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    (hind : LinearIndependent (ZMod p) h)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p))
    (hr : ∀ i v, r i v = v - α i v • h i) {w : V} (hw : ∀ i, ∃ c : ZMod p, r i w = c • w) :
    ∀ i, r i w = w := by
  intro i
  by_contra hne
  have hαi : α i w ≠ 0 := by
    intro h0
    apply hne
    rw [hr i w, h0, zero_smul, sub_zero]
  obtain ⟨c, hc⟩ := hw i
  have hrel : α i w • h i = (1 - c) • w := by
    have hh := hr i w
    rw [hc] at hh
    have h2 : α i w • h i = w - c • w := by rw [hh]; abel
    rw [h2, sub_smul, one_smul]
  have h1c : (1 - c) ≠ 0 := by
    intro h0
    have hzero : α i w • h i = 0 := by rw [hrel, h0, zero_smul]
    have hhi : h i = 0 := by
      rcases smul_eq_zero.mp hzero with hh | hh
      · exact absurd hh hαi
      · exact hh
    exact hind.ne_zero i hhi
  let a : ZMod p := (1 - c)⁻¹ * α i w
  have ha_ne : a ≠ 0 := mul_ne_zero (inv_ne_zero h1c) hαi
  have hw_eq : w = a • h i := by
    have h2 := congrArg (fun x => (1 - c)⁻¹ • x) hrel
    simp only [smul_smul] at h2
    rw [inv_mul_cancel₀ h1c, one_smul] at h2
    exact h2.symm
  obtain ⟨j, hji, hAji⟩ := l6f1_exists_neighbor (N - 1) (by omega) i
  have hαjhi : α j (h i) = -1 := by rw [hpair j i, hAji]; norm_num
  have hαjw : α j w = -a := by
    rw [hw_eq, map_smul, hαjhi, smul_eq_mul]; ring
  obtain ⟨c', hc'⟩ := hw j
  have hrelj : α j w • h j = (1 - c') • w := by
    have hh := hr j w
    rw [hc'] at hh
    have h2 : α j w • h j = w - c' • w := by rw [hh]; abel
    rw [h2, sub_smul, one_smul]
  have hαjw_ne : α j w ≠ 0 := by
    rw [hαjw, neg_ne_zero]
    exact ha_ne
  have hj_span : h j ∈ Submodule.span (ZMod p) {h i} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨(α j w)⁻¹ * (1 - c') * a, ?_⟩
    have h2 : h j = ((α j w)⁻¹ * (1 - c')) • w := by
      have h3 := congrArg (fun x => (α j w)⁻¹ • x) hrelj
      simp only [smul_smul] at h3
      rw [inv_mul_cancel₀ hαjw_ne, one_smul] at h3
      exact h3
    rw [h2, hαjw, hw_eq]
    module
  have hpair_li : LinearIndependent (ZMod p) ![h i, h j] := by
    have hcomp : LinearIndependent (ZMod p) (h ∘ ![i, j]) :=
      hind.comp ![i, j] (by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [hji])
    convert hcomp using 1
    ext t
    fin_cases t <;> rfl
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hj_span
  have hcontra := (LinearIndependent.pair_iff.mp hpair_li) lam (-1) (by
    rw [hlam, neg_smul, one_smul]; abel)
  exact one_ne_zero (neg_eq_zero.mp hcontra.2)

theorem ggFixLine_noncomm_pairs {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    {s t : V ≃ₗ[ZMod p] V} (hs : s ∈ A) (ht : t ∈ A) {h k : V} {α β : Module.Dual (ZMod p) V}
    (hs' : ∀ v, s v = v - α v • h) (ht' : ∀ v, t v = v - β v • k) (hαh : α h = 2) (hβk : β k = 2)
    (hne : s * t ≠ t * s) : α k ≠ 0 ∧ β h ≠ 0 := by
  have hzero_forward : α k = 0 → β h = 0 := by
    intro h0
    exact ggDepA_pair_zero_symm (p := p) hp2 A hnt hs ht hs' ht' hαh hβk h0
  have hzero_backward : β h = 0 → α k = 0 := by
    intro h0
    exact ggDepA_pair_zero_symm (p := p) hp2 A hnt ht hs ht' hs' hβk hαh h0
  have hcomm : α k = 0 → β h = 0 → s * t = t * s := by
    intro h0 h1
    ext v
    show s (t v) = t (s v)
    have e1 : α (t v) = α v := by simp [ht' v, map_sub, map_smul, h0]
    have e2 : β (s v) = β v := by simp [hs' v, map_sub, map_smul, h1]
    calc s (t v) = t v - α (t v) • h := hs' (t v)
      _ = (v - β v • k) - α v • h := by rw [e1, ht' v]
      _ = (v - α v • h) - β v • k := by abel
      _ = s v - β (s v) • k := by rw [e2, hs' v]
      _ = t (s v) := (ht' (s v)).symm
  constructor
  · intro h0
    exact absurd (hcomm h0 (hzero_forward h0)) hne
  · intro h0
    exact absurd (hcomm (hzero_backward h0) h0) hne

end CFSG.StandardType

end
