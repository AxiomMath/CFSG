module

public import CFSG.LocalAnalysis.StandardType.GGResICellLine
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section WStar

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {R : Type} [CommRing R] {φ : R →+* ZMod p} {N : ℕ}
  {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {α : Fin N → Module.Dual (ZMod p) V}
  {g : Fin N → (V ≃ₗ[ZMod p] V)}

theorem ggResI_wstar_of (hp2 : p ≠ 2) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (hT : GGFTable φ T h 0 α) (hind : LinearIndependent (ZMod p) h)
    {typ : GGWTypeI} (hok : ggWTypeOk typ N = true) (t : Fin N → Fin N × List (Fin N))
    (hgen : ∀ k, g k ∈ Subgroup.closure (Set.range fun i =>
      ((t i).2.map g).prod * g (t i).1 * (((t i).2.map g).prod)⁻¹))
    (d : Fin N → ZMod p) (hd : ∀ i, d i ≠ 0)
    (hpair : ∀ i j, d i * φ (ggFRootAt T (ggFC T (t j)) (ggFH T (t i))) =
      d j * (ggWCartanI typ N i j : ZMod p))
    (ll : Fin N → Fin N → ZMod p) (dz : ZMod p) (hdz : dz ≠ 0)
    (hlam : ∀ i o, ∑ l : Fin N, φ ((ggFH T (t i)).get l.castSucc) * ll l o =
      if i = o then dz else 0) :
    ZS.LinWeyl p (Subgroup.closure (Set.range g)) := by
  set w : Fin N → (V ≃ₗ[ZMod p] V) := fun i => ((t i).2.map g).prod
  set t' : Fin N → (V ≃ₗ[ZMod p] V) := fun i => w i * g (t i).1 * (w i)⁻¹
  set H : Fin N → V := fun i => ggFPi φ h 0 (ggFH T (t i))
  set A : Fin N → Module.Dual (ZMod p) V := fun i => ggFFun φ α (ggFC T (t i))
  have ht' : ∀ i x, t' i x = x - A i x • H i := fun i x => ggF_conj' hT hg h2 (t i) x
  set H' : Fin N → V := fun i => d i • H i
  set A' : Fin N → Module.Dual (ZMod p) V := fun i => (d i)⁻¹ • A i
  have ht'' : ∀ i x, t' i x = x - A' i x • H' i := by
    intro i x
    rw [ht' i x]
    simp only [A', H', LinearMap.smul_apply, smul_eq_mul, smul_smul]
    rw [show (d i)⁻¹ * (A i) x * d i = (A i) x by
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (hd i), one_mul]]
  obtain ⟨Mx, hW, hC⟩ := ggWCartanI_spec typ N hok
  have hP : ∀ i j, A' j (H' i) = (ggWCartanI typ N i j : ZMod p) := by
    intro i j
    have hAH : A j (H i) = φ (ggFRootAt T (ggFC T (t j)) (ggFH T (t i))) :=
      ggFFun_pi hT (ggFC T (t j)) (ggFH T (t i))
    simp only [A', H', LinearMap.smul_apply, map_smul, smul_eq_mul, hAH]
    have hdj := hd j
    field_simp
    linear_combination hpair i j
  have hindH : LinearIndependent (ZMod p) H' := by
    rw [Fintype.linearIndependent_iff]
    intro c hc o
    have hcoord : ∀ l : Fin N, ∑ i, c i * d i * φ ((ggFH T (t i)).get l.castSucc) = 0 := by
      have hsum : ∑ i, c i • H' i =
          ∑ l : Fin N, (∑ i, c i * d i * φ ((ggFH T (t i)).get l.castSucc)) • h l := by
        simp only [H', H, ggFPi_zero, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
      rw [hsum] at hc
      exact fun l => (Fintype.linearIndependent_iff.mp hind) _ hc l
    have hco : c o * d o * dz = 0 := by
      calc c o * d o * dz = ∑ i, c i * d i * (if i = o then dz else 0) := by simp
        _ = ∑ i, c i * d i * ∑ l : Fin N, φ ((ggFH T (t i)).get l.castSucc) * ll l o := by
          simp only [hlam]
        _ = ∑ l : Fin N, (∑ i, c i * d i * φ ((ggFH T (t i)).get l.castSucc)) * ll l o := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
          ring
        _ = 0 := by simp [hcoord]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hco).resolve_right hdz)).resolve_right (hd o)
  have hW' := ggResI_linWeyl_T hp2 hW hC t' H' A' ht'' hP hindH
  have hle : Subgroup.closure (Set.range t') ≤ Subgroup.closure (Set.range g) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ggF_conj_mem (t i).1 (t i).2
  have hge : Subgroup.closure (Set.range g) ≤ Subgroup.closure (Set.range t') := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact hgen k
  rwa [le_antisymm hle hge] at hW'

end WStar

theorem ggTriLiftB_of_lift {p : ℕ} {a : Fin 3 → Fin 3 → ZMod p} (h : GGTriLift p a) :
    ggTriLiftB a = true := by
  obtain ⟨P01, P02, P12, τ, h01, h01', h02, h02', h12, h12', e01, e02, e12, eτ, eτ', hττ, hnn,
    hz⟩ := h
  have h64 : τ * τ ≤ 64 := by
    rw [hττ]
    have h1 : P01 * P02 ≤ 16 := by nlinarith
    nlinarith
  have hτ1 : -8 ≤ τ := by nlinarith
  have hτ2 : τ ≤ 8 := by nlinarith
  have c01 : ((P01.toNat : ℕ) : ℤ) = P01 := Int.toNat_of_nonneg h01
  have c02 : ((P02.toNat : ℕ) : ℤ) = P02 := Int.toNat_of_nonneg h02
  have c12 : ((P12.toNat : ℕ) : ℤ) = P12 := Int.toNat_of_nonneg h12
  have cτ : (((τ + 8).toNat : ℕ) : ℤ) - 8 = τ := by rw [Int.toNat_of_nonneg (by omega)]; ring
  simp only [ggTriLiftB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, List.any_eq_true, List.mem_range]
  refine ⟨hz, P01.toNat, by omega, P02.toNat, by omega, P12.toNat, by omega, (τ + 8).toNat,
    by omega, ?_⟩
  rw [cτ, ← Int.cast_natCast (R := ZMod p), ← Int.cast_natCast (R := ZMod p) P02.toNat,
    ← Int.cast_natCast (R := ZMod p) P12.toNat, c01, c02, c12]
  exact ⟨⟨⟨⟨⟨⟨e01, e02⟩, e12⟩, eτ⟩, eτ'⟩, hττ⟩, hnn⟩

section Cells

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}

theorem ggResI_false_of_nospan {T : Fin (n + 1) → Vector (ZMod p) (n + 2)}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V}
    (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α) (hind : LinearIndependent (ZMod p) h)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x})
    {z₁ z₂ : Vector (ZMod p) (n + 2)} (hz₁ : ∀ i : Fin n, ggFDot (T i.castSucc) z₁ = 0)
    (hz₂ : ∀ i : Fin n, ggFDot (T i.castSucc) z₂ = 0) {l₁ l₂ : Fin (n + 1)}
    (hmin : z₁.get l₁.castSucc * z₂.get l₂.castSucc - z₁.get l₂.castSucc * z₂.get l₁.castSucc ≠
      0) : False := by
  have hπ : ∀ z : Vector (ZMod p) (n + 2), (∀ i : Fin n, ggFDot (T i.castSucc) z = 0) →
      ∃ c : ZMod p, ggFPi (RingHom.id (ZMod p)) h 0 z = c • x := by
    intro z hz
    have hm := hfix _ fun i => by rw [ggFPi_root hT]; exact hz i
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, hc.symm⟩
  obtain ⟨c₁, hc₁⟩ := hπ z₁ hz₁
  obtain ⟨c₂, hc₂⟩ := hπ z₂ hz₂
  have hcomb : ∀ l : Fin (n + 1), c₂ * z₁.get l.castSucc - c₁ * z₂.get l.castSucc = 0 := by
    have h0 : c₂ • ggFPi (RingHom.id (ZMod p)) h 0 z₁ - c₁ • ggFPi (RingHom.id (ZMod p)) h 0 z₂ =
        0 := by
      rw [hc₁, hc₂, smul_smul, smul_smul, mul_comm, sub_self]
    rw [ggFPi_zero_comb] at h0
    exact fun l => (Fintype.linearIndependent_iff.mp hind) _ h0 l
  have e₁ : c₁ * (z₁.get l₁.castSucc * z₂.get l₂.castSucc -
      z₁.get l₂.castSucc * z₂.get l₁.castSucc) = 0 := by
    linear_combination z₁.get l₂.castSucc * hcomb l₁ - z₁.get l₁.castSucc * hcomb l₂
  have hc₁0 : c₁ = 0 := (mul_eq_zero.mp e₁).resolve_right hmin
  have hπ0 : ggFPi (RingHom.id (ZMod p)) h 0 z₁ = 0 := by rw [hc₁, hc₁0, zero_smul]
  have hz0 : ∀ l : Fin (n + 1), z₁.get l.castSucc = 0 := by
    intro l
    by_contra hl
    exact ggFPi_ne_zero (φ := RingHom.id (ZMod p)) hind (l := l) hl hπ0
  apply hmin
  rw [hz0 l₁, hz0 l₂]
  ring

theorem ggFNotProp_spec {N : ℕ} {h : Fin N → V} (hind : LinearIndependent (ZMod p) h)
    {H z : Vector (ZMod p) (N + 1)} (hnp : ggFNotProp H z = true) (c : ZMod p) :
    ggFPi (RingHom.id (ZMod p)) h 0 H ≠ c • ggFPi (RingHom.id (ZMod p)) h 0 z := by
  intro he
  have h0 : (1 : ZMod p) • ggFPi (RingHom.id (ZMod p)) h 0 H -
      c • ggFPi (RingHom.id (ZMod p)) h 0 z = 0 := by
    rw [one_smul, he, sub_self]
  rw [ggFPi_zero_comb] at h0
  have hl := fun l => (Fintype.linearIndependent_iff.mp hind) _ h0 l
  simp only [ggFNotProp, List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at hnp
  obtain ⟨l, m, hlm⟩ := hnp
  apply hlm
  have e1 := hl l
  have e2 := hl m
  simp only [RingHom.id_apply, one_mul, sub_eq_zero] at e1 e2
  rw [e1, e2]
  ring

theorem ggFPi_smul_of {N : ℕ} {h : Fin N → V} {x : V} {z z' : Vector (ZMod p) (N + 1)}
    (s : ZMod p) (hz : ∀ l, z'.get l = s * z.get l) :
    ggFPi (RingHom.id (ZMod p)) h x z' = s • ggFPi (RingHom.id (ZMod p)) h x z := by
  simp only [ggFPi, hz, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]

theorem ggResI_concl_of_q8 [Finite V] {T : Fin (n + 1) → Vector (ZMod p) (n + 2)} {ib : Fin n}
    {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V}
    (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (hind : LinearIndependent (ZMod p) h)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hp3 : p = 3) {O : List (List ℕ)} {ci : List (List (ℕ × ℕ))}
    {t : Fin (n + 1) × List (Fin (n + 1))} {x₀ : List ℕ}
    (hchk : ggQ8Check T O ci t x₀ = true) : GGResIConcl g h α ib x := by
  simp only [ggQ8Check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    true_implies, true_and, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hx₀, hnz⟩, hlen⟩, hOg⟩, hOc⟩, ht⟩, hroot⟩, hnot⟩ := hchk
  set P : ℕ → V := fun j =>
    ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec (O.getD j []) : Vector (ZMod p) (n + 2)) with hP
  set S : Set (V ≃ₗ[ZMod p] V) :=
    {r | ∃ j < O.length, ∀ v, r v - v ∈ Submodule.span (ZMod p) {P j}} with hS
  have : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun a b hab => LinearEquiv.ext (congrFun hab))
  have hSf : S.Finite := Set.toFinite S
  have hmem : ∀ r, r ∈ hSf.toFinset.toList ↔ r ∈ S := fun r => by
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
  have hti : (⟨t.1.val, ht⟩ : Fin n).castSucc = t.1 := Fin.ext rfl
  set x₀' : V := ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec x₀ : Vector (ZMod p) (n + 2))
  have hm := hfix x₀' fun i => by rw [ggFPi_root hT]; exact hx₀ i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨l, hl⟩ := hnz
    exact ggFPi_ne_zero (φ := RingHom.id (ZMod p)) hind (l := l) hl (hc.symm.trans (zero_smul _ _))
  have hx : x = c⁻¹ • x₀' := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  right; right; left
  refine ⟨hp3, hSf.toFinset.toList, fun k => ?_, fun k r hr => ?_, (t.2.map g).prod,
    ggResI_word_mem t.2, ⟨t.1.val, ht⟩, ?_, ?_⟩
  ·
    rw [hmem]
    refine ⟨k.val, by omega, fun v => ?_⟩
    have hPk : P k.val = h k.castSucc := by
      simp only [hP]
      rw [hOg k, ggFPi_unit]
    rw [hPk, hg, sub_sub_cancel_left, ← neg_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  ·
    rw [hmem] at hr ⊢
    obtain ⟨j, hj, hrj⟩ := hr
    obtain ⟨hj', hjs⟩ := hOc k ⟨j, hj⟩
    refine ⟨((ci.getD k.val []).getD j (0, 0)).1, hj', fun v => ?_⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hrj ((g k.castSucc)⁻¹ v))
    have hv : (g k.castSucc * r * (g k.castSucc)⁻¹) v - v =
        g k.castSucc (r ((g k.castSucc)⁻¹ v) - (g k.castSucc)⁻¹ v) := by
      rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]
    rw [hv, ← ha, map_smul]
    have hgP : g k.castSucc (P j) = (((ci.getD k.val []).getD j (0, 0)).2 : ZMod p) •
        P ((ci.getD k.val []).getD j (0, 0)).1 := by
      simp only [hP]
      rw [ggFPi_refl hT hg]
      exact ggFPi_smul_of _ hjs
    rw [hgP, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [hti, hx, map_smul, map_smul, ggF_root_conj hT hg h2 t, ggFFun_pi hT, smul_eq_mul]
    simp only [RingHom.id_apply, hroot, mul_zero]
  ·
    rw [hti]
    intro hmem'
    rw [hmem] at hmem'
    obtain ⟨j, hj, hrj⟩ := hmem'
    set HV : V := ggFPi (RingHom.id (ZMod p)) h 0 (ggFH T t) with hHV
    have hmove : ((t.2.map g).prod * g t.1 * ((t.2.map g).prod)⁻¹) HV - HV = (-2 : ZMod p) • HV := by
      rw [ggF_conj hT hg h2 t.1 t.2 HV]
      have h2' : ggFFun (RingHom.id (ZMod p)) α (ggFDWord T t.2.reverse (ggFDUnit t.1)) HV = 2 :=
        ggF_root_coroot hT hg h2 t
      rw [h2', neg_smul, sub_sub_cancel_left]
      rfl
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hrj HV)
    rw [hmove] at ha
    have h20 : (-2 : ZMod p) ≠ 0 := by
      rw [neg_ne_zero]
      intro h0
      have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      have h3 := (ZMod.natCast_eq_zero_iff 2 p).mp h1
      rw [hp3] at h3
      omega
    apply ggFNotProp_spec hind (hnot ⟨j, hj⟩) ((-2 : ZMod p)⁻¹ * a)
    rw [← smul_smul, ha, smul_smul, inv_mul_cancel₀ h20, one_smul]

theorem ggResI_stdShape_of {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {typ : GGWTypeI} {σ : List (Fin (n + 1))} (hok : ggWTypeOk typ (n + 1) = true)
    (hlen : σ.length = n + 1) (hnd : σ.Nodup)
    (hgl : ∀ k l, ggGlueI C ib ic e₁ e₂ k l =
      ggWCartanI typ (n + 1) (σ.getD k.val 0) (σ.getD l.val 0)) :
    GGResIStdShapeI C ib ic e₁ e₂ := by
  obtain ⟨Mx, hW, hC⟩ := ggWCartanI_spec typ (n + 1) hok
  let f : Fin (n + 1) → Fin (n + 1) := fun k => σ.getD k.val 0
  have hinj : Function.Injective f := by
    intro k k' hkk
    simp only [f] at hkk
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hkk
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp hkk)
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨Mx.reindex e.symm, l05nDP4_weyl_reindex hW e.symm, ?_⟩
  have hre : ggGlueI C ib ic e₁ e₂ = Matrix.reindex e.symm e.symm (ggWCartanI typ (n + 1)) := by
    ext k l
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    rw [hgl]
    rfl
  rw [hre]
  exact hC.reindex e.symm

omit [Fact p.Prime] in
theorem ggResIO2aI_of {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ} {u v : ZMod p}
    (h : ggO2aB p C ib ic e₁ e₂ u v = true) : GGResIO2aI p C ib ic e₁ e₂ u v := by
  simp only [ggO2aB, ggO2Bond, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.all_eq_true, List.mem_finRange, true_and, true_implies, decide_eq_true_eq,
    and_assoc] at h
  exact h

omit [Fact p.Prime] in
theorem ggResIO2bI_of {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ} {u v : ZMod p}
    (h : ggO2bB p C ib ic e₁ e₂ u v = true) : GGResIO2bI p C ib ic e₁ e₂ u v := by
  simp only [ggO2bB, ggO2Bond, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.all_eq_true, List.mem_finRange, true_and, true_implies, decide_eq_true_eq,
    and_assoc] at h
  exact h

theorem ggResI_concl_of_triMat {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    (hp5 : 5 ≤ p) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    {j j₂ : Fin n} (hj : j ≠ ib) (hj₂ : j₂ ≠ ib) (tws : List (Fin (n + 1)))
    (hbad : GGTriBad p (ggFTriMat (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)
      j₂.castSucc)) :
    GGResIConcl g h α ib x :=
  ggResI_concl_of_triple hp5 hg h2 hT hj hj₂ tws hbad

theorem ggResI_cellWit_sound [Finite V] {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    (hp2 : p ≠ 2) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod p) h)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (w : GGCellWitI n) (hchk : ggCellWitCheckI p C ib ic e₁ e₂ u v w = true) :
    GGResIConclX C ib ic e₁ e₂ u v g h α x := by
  cases w with
  | tv t₁ t₂ l₀ z =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnY⟩ := hchk
    exact Or.inl (Or.inl (ggF_tvH (φ := RingHom.id (ZMod p)) hp2 hT hg h2 t₁ t₂ l₀ (ggFUnit z)
      hmin hn₁ hn₂ hnY))
  | tvk t₁ t₂ o₀ l =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnC⟩ := hchk
    exact Or.inl (Or.inl (ggF_tvkV (φ := RingHom.id (ZMod p)) hp2 hT hg h2 hspan hind t₁ t₂ o₀ l
      hmin hn₁ hn₂ hnC))
  | tri t j' =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨ht, hj'⟩, ⟨⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩, h4⟩⟩ := hchk
    obtain ⟨tk, tws⟩ := t
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    have hP : ggFA (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws) j₂.castSucc *
        ggFDualAt (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)
          (ggFC (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) (j.castSucc, tws)) j₂.castSucc ∉
        ({0, 1, 2, 3, 4} : Set (ZMod p)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h0, h1, h2', h3, h4⟩
    exact Or.inl (ggResI_concl_of_triMat (ggResII_five_le_of_not_mem hP) hg h2 hT hj hj₂ tws
      (ggTriBad_of_pair hP))
  | triple t j' =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ht, hj'⟩, hp5⟩, hτ⟩ := hchk
    obtain ⟨tk, tws⟩ := t
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    exact Or.inl (ggResI_concl_of_triMat hp5 hg h2 hT hj hj₂ tws (ggTriBad_of_tau hτ))
  | gram t j' =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hchk
    obtain ⟨⟨⟨ht, hj'⟩, hp5⟩, hcl, hlift⟩ := hchk
    obtain ⟨tk, tws⟩ := t
    obtain ⟨j, rfl, hj⟩ := inJ_spec ht
    obtain ⟨j₂, rfl, hj₂⟩ := inJ_spec hj'
    refine Or.inl (ggResI_concl_of_triMat hp5 hg h2 hT hj hj₂ tws ⟨?_, fun hL => ?_⟩)
    · rcases hcl with ((hc | hc) | hc) | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))
    · rw [ggTriLiftB_of_lift hL] at hlift
      exact Bool.noConfusion hlift
  | wstar typ ts d lam gw =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hok, hgen⟩, hd⟩, hpair⟩, hlam⟩ := hchk
    refine Or.inl (Or.inr (Or.inr (Or.inr ?_)))
    refine ggResI_wstar_of (φ := RingHom.id (ZMod p)) hp2 hg h2 hT hind hok
      (fun i => ts.getD i.val (0, [])) ?_ (fun i => (d.getD i.val 0 : ZMod p)) hd hpair
      (fun o i => ((lam.getD o.val []).getD i.val 0 : ZMod p)) 1 one_ne_zero hlam
    intro k
    obtain ⟨hm, hk⟩ := hgen k
    have hk' := ggFMat_eq hT hg hspan hk
    rw [List.map_singleton, List.prod_singleton] at hk'
    rw [hk']
    have key : ∀ L : List ℕ, (∀ m ∈ L, m < n + 1) →
        ((L.flatMap fun m => ggConjWord (ts.getD m (0, []))).map g).prod ∈
          Subgroup.closure (Set.range fun i : Fin (n + 1) =>
            ((ts.getD i.val (0, [])).2.map g).prod * g (ts.getD i.val (0, [])).1 *
              (((ts.getD i.val (0, [])).2.map g).prod)⁻¹) := by
      intro L hL
      induction L with
      | nil => exact Subgroup.one_mem _
      | cons m L ih =>
        rw [List.flatMap_cons, List.map_append, List.prod_append]
        refine Subgroup.mul_mem _ ?_ (ih fun m' hm' => hL m' (List.mem_cons_of_mem _ hm'))
        rw [ggF_conjWord_prod hg h2]
        exact Subgroup.subset_closure ⟨⟨m, hL m List.mem_cons_self⟩, rfl⟩
    exact key _ hm
  | std typ σ =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hu, hok⟩, hlen⟩, hnd⟩, hgl⟩ := hchk
    exact Or.inr (Or.inl ⟨hu, ggResI_stdShape_of hok hlen hnd hgl⟩)
  | nospan z₁ z₂ l₁ l₂ =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at hchk
    obtain ⟨hz, hmin⟩ := hchk
    exact (ggResI_false_of_nospan hT hind hfix (fun i => (hz i).1) (fun i => (hz i).2) hmin).elim
  | q8 O ci t x₀ =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, decide_eq_true_eq] at hchk
    exact Or.inl (ggResI_concl_of_q8 hT hg h2 hind hfix hchk.1 hchk.2)
  | line TT jl K z w F gens elts =>
    simp only [ggCellWitCheckI, Bool.and_eq_true, decide_eq_true_eq] at hchk
    exact Or.inr (Or.inr (Or.inl ⟨hchk.1, ggResI_lineCheck_sound hT hg h2 hspan hind
      (P := False) (fun h => Bool.noConfusion h) hchk.2⟩))
  | o2a TT jl K z w F gens elts =>
    simp only [ggCellWitCheckI, Bool.and_eq_true] at hchk
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ggResIO2aI_of hchk.1, ggResI_lineCheck_sound hT hg h2
      hspan hind (P := True) (fun _ => trivial) hchk.2⟩)))
  | o2b =>
    simp only [ggCellWitCheckI] at hchk
    exact Or.inr (Or.inr (Or.inr (Or.inr (ggResIO2bI_of hchk))))

theorem ggResI_cell_sound [Finite V] {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {wits : List (ℕ × ℕ × GGCellWitI n)} (hcell : GGCellCheckI p C ib ic e₁ e₂ wits)
    (hp2 : p ≠ 2) {g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V} {u v : ZMod p}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod p) h)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x}) :
    GGResIConclX C ib ic e₁ e₂ u v g h α x := by
  have hat := hcell u v
  unfold ggCellAtI at hat
  split at hat
  · exact ggResI_cellWit_sound hp2 hg h2 hT hspan hind hfix _ hat
  · exact absurd hat (by simp)

end Cells

end CFSG.StandardType
