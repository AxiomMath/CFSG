module

public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice

public section

namespace CFSG.HardMathSupport.C14PSat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
open scoped Pointwise

abbrev PSat {M : Type*} [AddCommGroup M] (p : ℕ) (Λ : AddSubgroup M) : Prop :=
  ∀ v, p • v ∈ Λ → v ∈ Λ

theorem mem_of_nsmul_mem {M : Type*} [AddCommGroup M] {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n)
    {Λ : AddSubgroup M} {v : M} (hpv : p • v ∈ Λ) (hnv : n • v ∈ Λ) : v ∈ Λ := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  have e : v = x • ((p : ℤ) • v) + y • ((n : ℤ) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, hxy, one_smul]
  rw [e]
  refine add_mem (zsmul_mem ?_ _) (zsmul_mem ?_ _) <;> simpa [natCast_zsmul]

theorem mem_of_zsmul_mem {M : Type*} [AddCommGroup M] {p : ℕ} {D : ℤ} (hp : p.Prime)
    (hD : ¬ (p : ℤ) ∣ D) {Λ : AddSubgroup M} {v : M} (hpv : p • v ∈ Λ) (hDv : D • v ∈ Λ) :
    v ∈ Λ := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (p : ℤ) D :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp)).2 hD
  have e : v = x • ((p : ℤ) • v) + y • (D • v) := by
    rw [smul_smul, smul_smul, ← add_smul, hxy, one_smul]
  rw [e]
  exact add_mem (zsmul_mem (by simpa [natCast_zsmul] using hpv) _) (zsmul_mem hDv _)

@[expose] def reflGroup {τ : Tag} (Y : Set (Fin τ.rank → ℤ)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {r | ∃ (w : WeylGroup τ) (i : Fin τ.rank),
    w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ Y ∧ r = w * simple τ i * w⁻¹}

theorem sub_smul_mem {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} {h : WeylGroup τ} (hh : h ∈ reflGroup Y)
    (v : Fin τ.rank → ℤ) : v - h • v ∈ AddSubgroup.closure Y := by
  induction hh using Subgroup.closure_induction generalizing v with
  | mem x hx =>
    obtain ⟨w, i, hwi, rfl⟩ := hx
    have e : v - (w * simple τ i * w⁻¹) • v =
        (∑ j, τ.cartan i j * (w⁻¹ • v) j) • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
      rw [mul_smul, mul_smul, simple_smul, reflect, smul_sub, smul_inv_smul,
        smul_comm w _ (Pi.single i 1 : Fin τ.rank → ℤ), sub_sub_cancel]
    rw [e]
    exact zsmul_mem (AddSubgroup.subset_closure hwi) _
  | one => simp
  | mul x y _ _ hx hy =>
    have e : v - (x * y) • v = (v - y • v) + (y • v - x • (y • v)) := by
      rw [mul_smul]; abel
    rw [e]
    exact add_mem (hy v) (hx (y • v))
  | inv x _ hx =>
    have e : v - x⁻¹ • v = -(x⁻¹ • v - x • (x⁻¹ • v)) := by
      rw [smul_inv_smul]; abel
    rw [e]
    exact neg_mem (hx _)

noncomputable abbrev iform (τ : Tag) (u v : Fin τ.rank → ℤ) : ℚ :=
  form (isFiniteType_cartan τ) (toRat u) (toRat v)

theorem iform_smul {τ : Tag} (w : WeylGroup τ) (u v : Fin τ.rank → ℤ) :
    iform τ (w • u) (w • v) = iform τ u v := by
  simp only [iform, smul_def]
  exact form_weylAction _ w u v

theorem iform_add_left {τ : Tag} (u u' v : Fin τ.rank → ℤ) :
    iform τ (u + u') v = iform τ u v + iform τ u' v := by
  simp [iform, map_add]

theorem iform_neg_left {τ : Tag} (u v : Fin τ.rank → ℤ) : iform τ (-u) v = - iform τ u v := by
  simp [iform, map_neg]

theorem eq_zero_of_iform_self {τ : Tag} {u : Fin τ.rank → ℤ} (h : iform τ u u = 0) : u = 0 := by
  by_contra hu
  have hu' : toRat u ≠ 0 := fun h0 => hu (toRat_injective (by rw [h0, map_zero]))
  exact (form_pos (isFiniteType_cartan τ) hu').ne' h

theorem card_smul_mem {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} (hY : ∀ y ∈ Y, IsRoot τ y) {p : ℕ}
    (hp : p ≠ 0) {v : Fin τ.rank → ℤ} (hv : p • v ∈ AddSubgroup.closure Y) :
    Nat.card (reflGroup Y) • v ∈ AddSubgroup.closure Y := by
  classical
  set H := reflGroup Y
  haveI : Fintype H := Fintype.ofFinite H
  set S : Fin τ.rank → ℤ := ∑ h : H, (h : WeylGroup τ) • v with hS
  have h1 : Nat.card H • v - S ∈ AddSubgroup.closure Y := by
    have e : Nat.card H • v - S = ∑ h : H, (v - (h : WeylGroup τ) • v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    rw [e]
    exact AddSubgroup.sum_mem _ fun h _ => sub_smul_mem h.2 v
  have h2 : p • S ∈ AddSubgroup.closure Y := by
    have e : p • S = Nat.card H • (p • v) - ∑ h : H, (p • v - (h : WeylGroup τ) • (p • v)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        sub_sub_cancel, hS, Finset.smul_sum]
      exact Finset.sum_congr rfl fun h _ => (smul_comm _ _ _).symm
    rw [e]
    refine sub_mem (nsmul_mem hv _) (AddSubgroup.sum_mem _ fun h _ => sub_smul_mem h.2 _)
  have h3 : ∀ g ∈ H, g • S = S := by
    intro g hg
    rw [hS, Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : H)) _ _ fun h => rfl
  have h4 : ∀ β ∈ Y, iform τ β S = 0 := by
    intro β hβ
    obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 (hY β hβ)
    set r := w * simple τ i * w⁻¹
    have hr : r ∈ H := Subgroup.subset_closure ⟨w, i, hβ, rfl⟩
    have hrβ : r • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) =
        -(w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
      rw [show r = w * simple τ i * w⁻¹ from rfl, mul_smul, mul_smul, inv_smul_smul,
        simple_smul, reflect_single_self, smul_neg]
    have := iform_smul r (w • (Pi.single i 1 : Fin τ.rank → ℤ)) S
    rw [hrβ, h3 r hr, iform_neg_left] at this
    linarith
  have h5 : ∀ x ∈ AddSubgroup.closure Y, iform τ x S = 0 := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact h4 x hx
    | zero => simp [iform]
    | add x y _ _ hx hy => rw [iform_add_left, hx, hy, add_zero]
    | neg x _ hx => rw [iform_neg_left, hx, neg_zero]
  have h6 : S = 0 := by
    have hpS := h5 _ h2
    have e : iform τ (p • S) (p • S) = p * iform τ (p • S) S := by
      simp only [iform]
      rw [map_nsmul toRat p S, map_nsmul, nsmul_eq_mul]
    rw [hpS, mul_zero] at e
    have := eq_zero_of_iform_self e
    funext j
    have hj := congrFun this j
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hj
    exact hj.resolve_left hp
  have := h1
  rwa [h6, sub_zero] at this

theorem pSat_of_not_dvd {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} (hY : ∀ y ∈ Y, IsRoot τ y) {p : ℕ}
    (hp : p.Prime) (hW : ¬ p ∣ Nat.card (reflGroup Y)) :
    PSat p (AddSubgroup.closure Y) := fun _ hv =>
  mem_of_nsmul_mem hp hW hv (card_smul_mem hY hp.ne_zero hv)

theorem smul_mem_closure_smul {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} (g : WeylGroup τ)
    {x : Fin τ.rank → ℤ} (hx : x ∈ AddSubgroup.closure Y) :
    g • x ∈ AddSubgroup.closure (g • Y) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure (Set.smul_mem_smul_set hx)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem pSat_of_smul {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} {p : ℕ} (g : WeylGroup τ)
    (h : PSat p (AddSubgroup.closure (g • Y))) : PSat p (AddSubgroup.closure Y) := by
  intro v hv
  have h1 : p • (g • v) ∈ AddSubgroup.closure (g • Y) := by
    rw [smul_comm]; exact smul_mem_closure_smul g hv
  have h2 := smul_mem_closure_smul g⁻¹ (h _ h1)
  rwa [inv_smul_smul, inv_smul_smul] at h2

theorem conj_mem_reflGroup {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} (g : WeylGroup τ) {x : WeylGroup τ}
    (hx : x ∈ reflGroup Y) : g * x * g⁻¹ ∈ reflGroup (g • Y) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨u, i, hu, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨g * u, i, ?_, by group⟩
    rw [mul_smul]; exact Set.smul_mem_smul_set hu
  | one => simpa using one_mem _
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]; exact mul_mem hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hy

theorem isRoot_of_mem_smul {τ : Tag} {Y : Set (Fin τ.rank → ℤ)} (hY : ∀ y ∈ Y, IsRoot τ y)
    (g : WeylGroup τ) : ∀ y ∈ g • Y, IsRoot τ y := by
  rintro _ ⟨y, hy, rfl⟩
  exact IsRoot.smul (hY y hy) g

theorem pSat_of_sylow {τ : Tag} {p : ℕ} (hp : p.Prime) (hW2 : ¬ p ^ 2 ∣ Nat.card (WeylGroup τ))
    {w₀ : WeylGroup τ} (hw₀ : orderOf w₀ = p)
    (hcase : ∀ Y : Set (Fin τ.rank → ℤ), (∀ y ∈ Y, IsRoot τ y) → w₀ ∈ reflGroup Y →
      PSat p (AddSubgroup.closure Y))
    {Y : Set (Fin τ.rank → ℤ)} (hY : ∀ y ∈ Y, IsRoot τ y) :
    PSat p (AddSubgroup.closure Y) := by
  haveI := Fact.mk hp
  by_cases hH : p ∣ Nat.card (reflGroup Y)
  swap
  · exact pSat_of_not_dvd hY hp hH
  obtain ⟨⟨z, hzH⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := reflGroup Y) p hH
  have hzp : orderOf z = p := by rw [← hz, Subgroup.orderOf_mk]
  have hidx : ∀ t : WeylGroup τ, orderOf t = p → ¬ p ∣ (Subgroup.zpowers t).index := by
    intro t ht hdiv
    have hc := Subgroup.card_mul_index (Subgroup.zpowers t)
    rw [Nat.card_zpowers, ht] at hc
    exact hW2 (by rw [← hc, pow_two]; exact Nat.mul_dvd_mul_left p hdiv)
  have hPz : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
  have hP0 : IsPGroup p (Subgroup.zpowers w₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw₀, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup τ) (hP0.toSylow (hidx w₀ hw₀))
    (hPz.toSylow (hidx z hzp))
  have hzmem : z ∈ (g • hP0.toSylow (hidx w₀ hw₀) : Sylow p (WeylGroup τ)) := by
    rw [hg]; exact (IsPGroup.mem_toSylow _ _).2 (Subgroup.mem_zpowers z)
  have hzmem2 : z ∈ (MulAut.conj g • ((hP0.toSylow (hidx w₀ hw₀) : Sylow p (WeylGroup τ)) :
      Subgroup (WeylGroup τ))) := by
    rw [← Sylow.coe_subgroup_smul]; exact hzmem
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzmem2
  have hz' : g⁻¹ * z * g ∈ Subgroup.zpowers w₀ := by
    have := (IsPGroup.mem_toSylow _ _).1 hzmem2
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
  have hw₀z : w₀ ∈ Subgroup.zpowers (g⁻¹ * z * g) := by
    have hle : Subgroup.zpowers (g⁻¹ * z * g) ≤ Subgroup.zpowers w₀ :=
      (Subgroup.zpowers_le).2 hz'
    have hcard : Nat.card (Subgroup.zpowers (g⁻¹ * z * g)) =
        Nat.card (Subgroup.zpowers w₀) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hw₀, ← hzp]
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    have := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    rw [this]; exact Subgroup.mem_zpowers w₀
  have hmem : g⁻¹ * z * g ∈ reflGroup (g⁻¹ • Y) := by
    simpa using conj_mem_reflGroup g⁻¹ hzH
  have hw₀mem : w₀ ∈ reflGroup (g⁻¹ • Y) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hw₀z
    rw [← hn]; exact zpow_mem hmem n
  exact pSat_of_smul g⁻¹ (hcase _ (isRoot_of_mem_smul hY g⁻¹) hw₀mem)

theorem pSat_of_proj {n d : ℕ} {Y : Set (Fin n → ℤ)} {p : ℕ} (σ : Fin d → Fin n)
    (he : ∀ j, (∀ k, σ k ≠ j) → (Pi.single j 1 : Fin n → ℤ) ∈ AddSubgroup.closure Y)
    (hsat : PSat p (AddSubgroup.closure ((fun v : Fin n → ℤ => v ∘ σ) '' Y))) :
    PSat p (AddSubgroup.closure Y) := by
  classical
  let π : (Fin n → ℤ) →+ (Fin d → ℤ) :=
    { toFun := fun v => v ∘ σ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hmap : (AddSubgroup.closure Y).map π =
      AddSubgroup.closure ((fun v : Fin n → ℤ => v ∘ σ) '' Y) :=
    AddMonoidHom.map_closure π Y
  intro v hv
  have h1 : p • π v ∈ (AddSubgroup.closure Y).map π := by
    rw [← map_nsmul]; exact AddSubgroup.mem_map_of_mem _ hv
  rw [hmap] at h1
  have h2 := hsat _ h1
  rw [← hmap] at h2
  obtain ⟨l, hl, hlv⟩ := AddSubgroup.mem_map.1 h2
  have hker : ∀ k, (v - l) (σ k) = 0 := fun k => by
    have := congrFun hlv k
    simp only [π, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at this
    simp [this]
  have h3 : v - l ∈ AddSubgroup.closure Y := by
    rw [← Finset.univ_sum_single (v - l)]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    by_cases hj : ∃ k, σ k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [hker k, Pi.single_zero]; exact zero_mem _
    · push Not at hj
      rw [show Pi.single j ((v - l) j) = ((v - l) j) • (Pi.single j 1 : Fin n → ℤ) by
        ext k; by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_apply, hk]]
      exact zsmul_mem (he j hj) _
  simpa using add_mem h3 hl

@[expose] def phiL {d : ℕ} (B A : List (Fin d → ℤ)) (x : Fin d → ℤ) : Fin d → ℤ :=
  ((B.zip A).map fun ba => (∑ i, ba.2 i * x i) • ba.1).sum

theorem phiL_add {d : ℕ} (B A : List (Fin d → ℤ)) (x y : Fin d → ℤ) :
    phiL B A (x + y) = phiL B A x + phiL B A y := by
  unfold phiL
  induction B.zip A with
  | nil => simp
  | cons ba l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      add_smul, List.sum_map_add]
    abel

theorem phiL_neg {d : ℕ} (B A : List (Fin d → ℤ)) (x : Fin d → ℤ) :
    phiL B A (-x) = -phiL B A x := by
  have h := phiL_add B A x (-x)
  rw [add_neg_cancel] at h
  have h0 : phiL B A 0 = 0 := by
    unfold phiL; induction B.zip A with
    | nil => simp
    | cons ba l ih => simp [ih]
  rw [h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem phiL_nsmul {d : ℕ} (B A : List (Fin d → ℤ)) (n : ℕ) (x : Fin d → ℤ) :
    phiL B A (n • x) = n • phiL B A x := by
  induction n with
  | zero =>
    simp only [zero_smul]
    unfold phiL; induction B.zip A with
    | nil => simp
    | cons ba l ih => simp [ih]
  | succ n ih => rw [succ_nsmul, phiL_add, ih, succ_nsmul]

theorem phiL_mem {d : ℕ} {T : Set (Fin d → ℤ)} (B A : List (Fin d → ℤ)) (hB : ∀ b ∈ B, b ∈ T)
    (x : Fin d → ℤ) : phiL B A x ∈ AddSubgroup.closure T := by
  unfold phiL
  refine (AddSubgroup.closure T).list_sum_mem fun y hy => ?_
  obtain ⟨ba, hba, rfl⟩ := List.mem_map.1 hy
  exact zsmul_mem (AddSubgroup.subset_closure (hB _ (List.of_mem_zip hba).1)) _

theorem pSat_of_phiL {d p : ℕ} (hp : p.Prime) {T : Set (Fin d → ℤ)} (B A : List (Fin d → ℤ))
    (D : ℤ) (hB : ∀ b ∈ B, b ∈ T) (hD : ¬ (p : ℤ) ∣ D) (hT : ∀ t ∈ T, phiL B A t = D • t) :
    PSat p (AddSubgroup.closure T) := by
  have hcl : ∀ x ∈ AddSubgroup.closure T, phiL B A x = D • x := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact hT x hx
    | zero =>
      simp only [smul_zero]
      unfold phiL; induction B.zip A with
      | nil => simp
      | cons ba l ih => simp [ih]
    | add x y _ _ hx hy => rw [phiL_add, hx, hy, smul_add]
    | neg x _ hx => rw [phiL_neg, hx, smul_neg]
  intro v hv
  have h1 := hcl _ hv
  rw [phiL_nsmul, smul_comm] at h1
  have h2 : phiL B A v = D • v := by
    funext j
    have := congrFun h1 j
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul] at this
    exact mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
  have hDv : D • v ∈ AddSubgroup.closure T := h2 ▸ phiL_mem B A hB v
  exact mem_of_zsmul_mem hp hD hv hDv

@[expose] def certOK {d : ℕ} (p : ℕ) (T : List (Fin d → ℤ))
    (c : List (Fin d → ℤ) × List (Fin d → ℤ) × ℤ) : Bool :=
  c.1.all (fun b => decide (b ∈ T)) && decide (c.2.2 % (p : ℤ) ≠ 0) &&
    T.all (fun t => decide (phiL c.1 c.2.1 t = c.2.2 • t))

theorem pSat_of_certOK {d p : ℕ} (hp : p.Prime) {T : List (Fin d → ℤ)}
    {c : List (Fin d → ℤ) × List (Fin d → ℤ) × ℤ} (h : certOK p T c = true) :
    PSat p (AddSubgroup.closure {t | t ∈ T}) := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hB, hD⟩, hT⟩ := h
  exact pSat_of_phiL hp c.1 c.2.1 c.2.2 hB
    (fun h' => hD (Int.emod_eq_zero_of_dvd h')) hT

@[expose] def allOK {d : ℕ} (p : ℕ) (S : List (Fin d → ℤ))
    (certs : List (List (Fin d → ℤ) × List (Fin d → ℤ) × ℤ)) (idx : List ℕ) : Bool :=
  decide (idx.length = S.sublists.length) &&
    (S.sublists.zip idx).all fun Ti => certOK p Ti.1 (certs.getD Ti.2 ([], [], 1))

theorem pSat_sublists {d p : ℕ} (hp : p.Prime) {S : List (Fin d → ℤ)}
    {certs : List (List (Fin d → ℤ) × List (Fin d → ℤ) × ℤ)} {idx : List ℕ}
    (h : allOK p S certs idx = true) :
    ∀ T ∈ S.sublists, PSat p (AddSubgroup.closure {t | t ∈ T}) := by
  simp only [allOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro T hT
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hT
  have hz : (S.sublists[n], idx[n]'(hlen ▸ hn)) ∈ S.sublists.zip idx := by
    rw [List.mem_iff_getElem]
    exact ⟨n, by rw [List.length_zip, hlen, Nat.min_self]; exact hn, by simp⟩
  exact pSat_of_certOK hp (hall _ hz)

theorem pSat_of_subset_pm {d p : ℕ} {S : List (Fin d → ℤ)}
    (hS : ∀ T ∈ S.sublists, PSat p (AddSubgroup.closure {t | t ∈ T}))
    {T : Set (Fin d → ℤ)} (hT : ∀ t ∈ T, t = 0 ∨ t ∈ S ∨ -t ∈ S) :
    PSat p (AddSubgroup.closure T) := by
  classical
  set T' := S.filter fun s => decide (s ∈ T ∨ -s ∈ T)
  have hT' : T' ∈ S.sublists := List.mem_sublists.2 List.filter_sublist
  have heq : AddSubgroup.closure T = AddSubgroup.closure {t | t ∈ T'} := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      intro t ht
      rcases hT t ht with rfl | h | h
      · exact zero_mem _
      · exact AddSubgroup.subset_closure (List.mem_filter.2 ⟨h, by simp [ht]⟩)
      · have : -t ∈ AddSubgroup.closure {t | t ∈ T'} :=
          AddSubgroup.subset_closure (List.mem_filter.2 ⟨h, by simp [ht]⟩)
        simpa using neg_mem this
    · rw [AddSubgroup.closure_le]
      intro s hs
      have := (List.mem_filter.1 hs).2
      simp only [decide_eq_true_eq] at this
      rcases this with h | h
      · exact AddSubgroup.subset_closure h
      · simpa using neg_mem (AddSubgroup.subset_closure h)
  rw [heq]
  exact hS T' hT'

theorem pSat_case {τ : Tag} {d p : ℕ} (hp : p.Prime) (l : List (Fin τ.rank)) (σ : Fin d → Fin τ.rank)
    (U : Fin τ.rank → Fin τ.rank → ℤ)
    (hU : ∀ j, (∃ k, σ k = j) ∨ U j - l.foldr (reflect τ) (U j) = Pi.single j 1)
    (S : List (Fin d → ℤ)) (hroots : ∀ v, IsRoot τ v → v ∘ σ = 0 ∨ v ∘ σ ∈ S ∨ -(v ∘ σ) ∈ S)
    (hS : ∀ T ∈ S.sublists, PSat p (AddSubgroup.closure {t | t ∈ T}))
    (Y : Set (Fin τ.rank → ℤ)) (hY : ∀ y ∈ Y, IsRoot τ y)
    (hw : (l.map (simple τ)).prod ∈ reflGroup Y) : PSat p (AddSubgroup.closure Y) := by
  refine pSat_of_proj σ (fun j hj => ?_) (pSat_of_subset_pm hS ?_)
  · rcases hU j with ⟨k, hk⟩ | h
    · exact absurd hk (hj k)
    · rw [← h, ← CFSG.HardMathSupport.C14Lattice.lattice_list_prod_simple_smul]
      exact sub_smul_mem hw _
  · rintro _ ⟨y, hy, rfl⟩
    exact hroots y (hY y hy)

end CFSG.HardMathSupport.C14PSat
