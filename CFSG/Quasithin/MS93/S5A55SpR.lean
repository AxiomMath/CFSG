module

public import CFSG.Quasithin.MS93.S5A55SpC
public import CFSG.Quasithin.MS93.MSPQuad
public import CFSG.Quasithin.MS93.S5A54Sp
public import CFSG.Quasithin.MS93.S5A55SpE

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F]

theorem mulVec_e₂_of_mem_stab {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) :
    mat r *ᵥ e₂ F = mat r (.inl 0) (.inl 1) • e₁ F + mat r (.inl 1) (.inl 1) • e₂ F := by
  have hm := mem_ln₀.1 (mulVec_mem_of_mem_stab hr (mem_ln₀.2 ⟨by simp, by simp⟩ :
    e₂ F ∈ ln₀ F))
  have h : ∀ i, (mat r *ᵥ e₂ F) i = mat r i (.inl 1) := fun i => (mat_apply_eq r i _).symm
  refine ext4 ?_ ?_ ?_ ?_
  · rw [h]; simp
  · rw [h]; simp
  · rw [hm.1]; simp
  · rw [hm.2]; simp

variable [CharP F 2]

theorem entry_e₂_eq_one {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F) {n : ℕ}
    (hn : r ^ 2 ^ n = 1) : mat r (.inl 1) (.inl 1) = 1 := by
  set t := mat r (.inl 1) (.inl 1) with ht
  have hr2 := mulVec_e₂_of_mem_stab hr
  have key : ∀ m : ℕ, ∃ x : F, mat (r ^ m) *ᵥ e₂ F = x • e₁ F + t ^ m • e₂ F := by
    intro m
    induction m with
    | zero => exact ⟨0, by rw [pow_zero, mat_one, one_mulVec, zero_smul, zero_add, pow_zero,
        one_smul]⟩
    | succ m ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨x + t ^ m * mat r (.inl 0) (.inl 1), ?_⟩
      rw [pow_succ', mat_mul_mulVec, hx, mulVec_add, mulVec_smul, mulVec_smul, he, hr2]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [← ht]
      ring
  obtain ⟨x, hx⟩ := key (2 ^ n)
  rw [hn, mat_one, one_mulVec] at hx
  have := congrFun hx (.inl 1)
  simp at this
  exact eq_one_of_pow_two_pow this.symm

omit [CharP F 2] in
theorem mulVec_e₂_of_stab {r : Sp4 F} (hr : r ∈ stab (ln₀ F))
    (ht : mat r (.inl 1) (.inl 1) = 1) :
    mat r *ᵥ e₂ F = mat r (.inl 0) (.inl 1) • e₁ F + e₂ F := by
  rw [mulVec_e₂_of_mem_stab hr, ht, one_smul]

theorem nuE_mul_mem_Q₁ {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F)
    (ht : mat r (.inl 1) (.inl 1) = 1) : nuE (mat r (.inl 0) (.inl 1)) * r ∈ Q₁ F := by
  set a := mat r (.inl 0) (.inl 1)
  have h1 : mat (nuE a * r) *ᵥ e₁ F = e₁ F := by rw [mat_mul_mulVec, he, nuE_mulVec_e₁]
  have h2e : mat (nuE a * r) *ᵥ e₂ F = e₂ F := by
    rw [mat_mul_mulVec, mulVec_e₂_of_stab hr ht, mulVec_add, mulVec_smul, nuE_mulVec_e₁,
      nuE_mulVec_e₂, ← add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, zero_add]
  intro v hv
  obtain ⟨h2', h3⟩ := mem_ln₀.1 hv
  have hv' : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F :=
    ext4 (by simp) (by simp) (by simp [h2']) (by simp [h3])
  calc mat (nuE a * r) *ᵥ v = mat (nuE a * r) *ᵥ (v (.inl 0) • e₁ F + v (.inl 1) • e₂ F) := by
        rw [← hv']
    _ = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F := by
        rw [mulVec_add, mulVec_smul, mulVec_smul, h1, h2e]
    _ = v := hv'.symm

theorem q1c_conj_of_stab {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F)
    (ht : mat r (.inl 1) (.inl 1) = 1) {m : Sp4 F} (hm : m ∈ Q₁ F) :
    q1c (r * m * r⁻¹) = ((q1c m).1 + mat r (.inl 0) (.inl 1) ^ 2 * (q1c m).2.2,
      (q1c m).2.1 + mat r (.inl 0) (.inl 1) * (q1c m).2.2, (q1c m).2.2) := by
  set a := mat r (.inl 0) (.inl 1)
  have hk := nuE_mul_mem_Q₁ hr he ht
  have hr' : r = nuE a * (nuE a * r) := by rw [← mul_assoc, nuE_mul_self, one_mul]
  have hkm : (nuE a * r) * m * (nuE a * r)⁻¹ = m := by
    rw [Q₁_comm hk hm, mul_assoc, mul_inv_cancel, mul_one]
  have e : r * m * r⁻¹ = nuE a * m * (nuE a)⁻¹ := by
    calc r * m * r⁻¹ = (nuE a * (nuE a * r)) * m * (nuE a * (nuE a * r))⁻¹ := by rw [← hr']
      _ = nuE a * ((nuE a * r) * m * (nuE a * r)⁻¹) * (nuE a)⁻¹ := by group
      _ = nuE a * m * (nuE a)⁻¹ := by rw [hkm]
  rw [e, q1c_nuE_conj hm]

theorem entry_nuE_mul (a : F) (r : Sp4 F) :
    mat (nuE a * r) (.inl 1) (.inr 1) = mat r (.inl 1) (.inr 1) := by
  rw [mat_apply_eq, mat_mul_mulVec, nuE_mulVec, mat_apply_eq]
  simp

theorem q1c_sq_of_stab {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F)
    (ht : mat r (.inl 1) (.inl 1) = 1) : r * r ∈ Q₁ F ∧
      q1c (r * r) = (mat r (.inl 0) (.inl 1) ^ 2 * mat r (.inl 1) (.inr 1),
        mat r (.inl 0) (.inl 1) * mat r (.inl 1) (.inr 1), 0) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set a := mat r (.inl 0) (.inl 1)
  have hk := nuE_mul_mem_Q₁ hr he ht
  have e : r * r = (nuE a * (nuE a * r) * (nuE a)⁻¹) * (nuE a * r) := by
    rw [nuE_inv]
    calc r * r = (nuE a * nuE a) * r * ((nuE a * nuE a) * r) := by rw [nuE_mul_self, one_mul]
      _ = nuE a * (nuE a * r) * nuE a * (nuE a * r) := by group
  have hc := conj_mem_Q₁ (nuE_mem_stab a) hk
  refine ⟨by rw [e]; exact mul_mem hc hk, ?_⟩
  rw [e, q1c_mul hc hk, q1c_nuE_conj hk]
  have hδ := entry_nuE_mul a r
  simp only [q1c, Prod.mk_add_mk, Prod.mk.injEq]
  rw [hδ]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination mat (nuE a * r) (.inl 0) (.inr 0) * h2
  · linear_combination mat (nuE a * r) (.inl 0) (.inr 1) * h2
  · linear_combination mat r (.inl 1) (.inr 1) * h2

theorem nuE_mem_Q₂ (a : F) : nuE a ∈ Q₂ F := by
  refine mem_qPoint.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [pt₀_eq_span] at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [mulVec_smul, nuE_mulVec_e₁]
  · rw [mem_perp_pt₀] at hv
    rw [nuE_mulVec, hv, mul_zero, zero_smul, add_zero, add_sub_cancel_left, pt₀_eq_span]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_Q₂_iff_of_stab {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F)
    (ht : mat r (.inl 1) (.inl 1) = 1) : r ∈ Q₂ F ↔ mat r (.inl 1) (.inr 1) = 0 := by
  set a := mat r (.inl 0) (.inl 1)
  have hk := nuE_mul_mem_Q₁ hr he ht
  have hδ := entry_nuE_mul a r
  constructor
  · intro h
    rw [← hδ]
    exact (mem_Q₂_iff.1 (mul_mem (nuE_mem_Q₂ a) h)).2
  · intro h
    have hr' : r = nuE a * (nuE a * r) := by rw [← mul_assoc, nuE_mul_self, one_mul]
    rw [hr']
    exact mul_mem (nuE_mem_Q₂ a) (mem_Q₂_of_mem_Q₁ hk (hδ ▸ h))

omit [CharP F 2] in
theorem mem_Q₁_iff_of_stab {r : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F)
    (ht : mat r (.inl 1) (.inl 1) = 1) : r ∈ Q₁ F ↔ mat r (.inl 0) (.inl 1) = 0 := by
  constructor
  · intro h
    have := congrFun (h (e₂ F) (mem_ln₀.2 ⟨by simp, by simp⟩)) (.inl 0)
    rw [← mat_apply_eq] at this
    simpa using this
  · intro h v hv
    obtain ⟨h2, h3⟩ := mem_ln₀.1 hv
    have hv' : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F :=
      ext4 (by simp) (by simp) (by simp [h2]) (by simp [h3])
    rw [hv', mulVec_add, mulVec_smul, mulVec_smul, he, mulVec_e₂_of_stab hr ht, h, zero_smul,
      zero_add]

omit [CharP F 2] in
theorem entry_e₂_mul {r s : Sp4 F} (hr : r ∈ stab (ln₀ F)) (he : mat r *ᵥ e₁ F = e₁ F)
    (hs : s ∈ stab (ln₀ F)) (hst : mat s (.inl 1) (.inl 1) = 1)
    (hrt : mat r (.inl 1) (.inl 1) = 1) :
    mat (r * s) (.inl 0) (.inl 1) = mat r (.inl 0) (.inl 1) + mat s (.inl 0) (.inl 1) := by
  rw [mat_apply_eq, mat_mul_mulVec, mulVec_e₂_of_stab hs hst, mulVec_add,
    mulVec_smul, he, mulVec_e₂_of_stab hr hrt]
  simp
  ring

omit [CharP F 2] in
theorem card_le_card_inf_Q₁_mul [Finite F] {E : Subgroup (Sp4 F)}
    (hE : ∀ r ∈ E, r ∈ stab (ln₀ F) ∧ mat r *ᵥ e₁ F = e₁ F ∧ mat r (.inl 1) (.inl 1) = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ Q₁ F) * Nat.card F := by
  let f : E →* Multiplicative F :=
    { toFun := fun r => Multiplicative.ofAdd (mat (r : Sp4 F) (.inl 0) (.inl 1))
      map_one' := by simp [mat_one]
      map_mul' := fun r s => by
        obtain ⟨hr, he, hrt⟩ := hE r r.2
        obtain ⟨hs, -, hst⟩ := hE s s.2
        simp only [Subgroup.coe_mul]
        rw [entry_e₂_mul hr he hs hst hrt, ofAdd_add] }
  have hker : f.ker = (Q₁ F).subgroupOf E := by
    ext r
    obtain ⟨hr, he, hrt⟩ := hE r r.2
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Q₁_iff_of_stab hr he hrt]
    simp [f]
  have h1 := Subgroup.card_ker_mul_card_range f
  have hcs : Nat.card ↥((Q₁ F).subgroupOf E) = Nat.card ↥(E ⊓ Q₁ F) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective E.subtype_injective]
  rw [hker, hcs] at h1
  rw [← h1]
  refine Nat.mul_le_mul_left _ ?_
  calc Nat.card f.range ≤ Nat.card (Multiplicative F) := Subgroup.card_le_card_group _
    _ = Nat.card F := rfl

omit [CharP F 2] in
theorem card_sup_mul_card_inf {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (A : Set Γ)) :
    Nat.card (A ⊔ B : Subgroup Γ) * Nat.card (A ⊓ B : Subgroup Γ) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set Γ)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ X : Subgroup Γ, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

omit [CharP F 2] in
theorem ln₀_inf_mu₀ : ln₀ F ⊓ mu₀ F = pt₀ F := by
  refine le_antisymm (fun v hv => ?_) (le_inf pt₀_le_ln₀ pt₀_le_mu₀)
  obtain ⟨h2, h3⟩ := mem_ln₀.1 hv.1
  have h1 := (mem_mu₀.1 hv.2).1
  exact mem_pt₀.2 ⟨h1, h2, h3⟩

theorem not_inf_le_qPoint_gv [Finite F] {R A₀ D : Subgroup (Sp4 F)} (hR : IsPGroup 2 R)
    (hA : candMax R = {A₀}) (hRl : R ≤ stab (ln₀ F)) (hRe : ∀ r ∈ R, mat r *ᵥ e₁ F = e₁ F)
    (hA₀ : A₀ = Q₁ F ⊓ R) (hA₀c : Nat.card F ^ 2 ≤ Nat.card A₀) (hDR : D ≤ R)
    (hDn : R ≤ Subgroup.normalizer (D : Set (Sp4 F))) (hAD : Nat.card A₀ ≤ Nat.card D)
    (hDQ : ¬ D ≤ Q₁ F) (ν : F) : ¬ D ⊓ Q₁ F ≤ qPoint (F ∙ gv ν) := by
  intro hN
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hRt : ∀ r ∈ R, mat r (.inl 1) (.inl 1) = 1 := fun r hr => by
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    exact entry_e₂_eq_one (hRl hr) (hRe r hr) (by simpa using congrArg Subtype.val hn)
  have hdat : ∀ r ∈ R, r ∈ stab (ln₀ F) ∧ mat r *ᵥ e₁ F = e₁ F ∧ mat r (.inl 1) (.inl 1) = 1 :=
    fun r hr => ⟨hRl hr, hRe r hr, hRt r hr⟩
  obtain ⟨u₀, hu₀D, hu₀Q⟩ := Set.not_subset.1 hDQ
  obtain ⟨hu₀s, hu₀e, hu₀t⟩ := hdat u₀ (hDR hu₀D)
  have ha₀ : mat u₀ (.inl 0) (.inl 1) ≠ 0 := fun h =>
    hu₀Q ((mem_Q₁_iff_of_stab hu₀s hu₀e hu₀t).2 h)
  have hNbd : ∀ n ∈ D ⊓ Q₁ F, mat n (.inl 0) (.inr 0) = 0 ∧ mat n (.inl 1) (.inr 1) = 0 := by
    intro n hn
    have hc := q1c_conj_of_stab hu₀s hu₀e hu₀t hn.2
    have hn' : u₀ * n * u₀⁻¹ ∈ D ⊓ Q₁ F :=
      ⟨D.mul_mem (D.mul_mem hu₀D hn.1) (D.inv_mem hu₀D), conj_mem_Q₁ hu₀s hn.2⟩
    have e1 := (mem_qPoint_gv_iff hn.2 ν).1 (hN hn)
    have e2 := (mem_qPoint_gv_iff hn'.2 ν).1 (hN hn')
    have hc1 : mat (u₀ * n * u₀⁻¹) (.inl 0) (.inr 0) =
        mat n (.inl 0) (.inr 0) + mat u₀ (.inl 0) (.inl 1) ^ 2 * mat n (.inl 1) (.inr 1) :=
      congrArg Prod.fst hc
    have hc3 : mat (u₀ * n * u₀⁻¹) (.inl 1) (.inr 1) = mat n (.inl 1) (.inr 1) :=
      congrArg (fun x => x.2.2) hc
    rw [hc1, hc3] at e2
    have hd : mat n (.inl 1) (.inr 1) = 0 := by
      have : mat u₀ (.inl 0) (.inl 1) ^ 2 * mat n (.inl 1) (.inr 1) = 0 := by
        linear_combination e2 - e1
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 ha₀)
    exact ⟨by rw [e1, hd, mul_zero], hd⟩
  have hNq : Nat.card ↥(D ⊓ Q₁ F) ≤ Nat.card F := by
    have hinj : Function.Injective fun n : ↥(D ⊓ Q₁ F) => mat (n : Sp4 F) (.inl 0) (.inr 1) := by
      intro x y hxy
      simp only at hxy
      obtain ⟨hxb, hxd⟩ := hNbd x x.2
      obtain ⟨hyb, hyd⟩ := hNbd y y.2
      exact Subtype.ext (eq_of_mem_Q₁ x.2.2 y.2.2 (by rw [hxb, hyb]) hxy (by rw [hxd, hyd]))
    exact Nat.card_le_card_of_injective _ hinj
  have hDle := card_le_card_inf_Q₁_mul fun r hr => hdat r (hDR hr)
  have hD2 : Nat.card D = Nat.card F ^ 2 := le_antisymm (by
    calc Nat.card D ≤ Nat.card ↥(D ⊓ Q₁ F) * Nat.card F := hDle
      _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul_right _ hNq
      _ = Nat.card F ^ 2 := (sq _).symm) (hA₀c.trans hAD)
  have hA2 : Nat.card A₀ = Nat.card F ^ 2 := le_antisymm (hAD.trans hD2.le) hA₀c
  have hNq' : Nat.card ↥(D ⊓ Q₁ F) = Nat.card F := by
    refine le_antisymm hNq ?_
    have h := hDle
    rw [hD2, sq] at h
    exact Nat.le_of_mul_le_mul_right h (by omega)
  have hA₀Q₂ : A₀ ≤ Q₂ F := by
    intro m hm
    rw [hA₀] at hm
    obtain ⟨hmQ, hmR⟩ := Subgroup.mem_inf.1 hm
    have hcomm : u₀ * m * u₀⁻¹ * m⁻¹ ∈ D ⊓ Q₁ F := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (conj_mem_Q₁ hu₀s hmQ) (inv_mem hmQ)⟩
      have h1 : m * u₀⁻¹ * m⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.1 (hDn hmR) u₀⁻¹).1 (D.inv_mem hu₀D)
      have e : u₀ * m * u₀⁻¹ * m⁻¹ = u₀ * (m * u₀⁻¹ * m⁻¹) := by group
      rw [e]
      exact D.mul_mem hu₀D h1
    have hb := (hNbd _ hcomm).1
    have hcq := q1c_conj_of_stab hu₀s hu₀e hu₀t hmQ
    have hm' := conj_mem_Q₁ hu₀s hmQ
    rw [entry_mul_inv_of_mem_Q₁ hm' hmQ] at hb
    have hc1 : mat (u₀ * m * u₀⁻¹) (.inl 0) (.inr 0) =
        mat m (.inl 0) (.inr 0) + mat u₀ (.inl 0) (.inl 1) ^ 2 * mat m (.inl 1) (.inr 1) :=
      congrArg Prod.fst hcq
    rw [hc1] at hb
    have : mat u₀ (.inl 0) (.inl 1) ^ 2 * mat m (.inl 1) (.inr 1) = 0 := by linear_combination hb
    exact mem_Q₂_of_mem_Q₁ hmQ ((mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 ha₀))
  have hA₀R : A₀ ≤ R := hA₀ ▸ inf_le_right
  have hA₀Q₁ : A₀ ≤ Q₁ F := hA₀ ▸ inf_le_left
  by_cases hDQ₂ : D ≤ Q₂ F
  ·
    have hnorm : D ≤ Subgroup.normalizer (A₀ : Set (Sp4 F)) := by
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro m
      rw [hA₀]
      constructor
      · intro hm
        obtain ⟨hmQ, hmR⟩ := Subgroup.mem_inf.1 hm
        exact Subgroup.mem_inf.2 ⟨conj_mem_Q₁ (hRl (hDR hd)) hmQ,
          R.mul_mem (R.mul_mem (hDR hd) hmR) (R.inv_mem (hDR hd))⟩
      · intro hm
        obtain ⟨hmQ, hmR⟩ := Subgroup.mem_inf.1 hm
        have e : m = d⁻¹ * (d * m * d⁻¹) * d⁻¹⁻¹ := by group
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [e]
          exact conj_mem_Q₁ (inv_mem (hRl (hDR hd))) hmQ
        · rw [e]
          exact R.mul_mem (R.mul_mem (R.inv_mem (hDR hd)) hmR) (R.inv_mem (R.inv_mem (hDR hd)))
    have hinf : A₀ ⊓ D = D ⊓ Q₁ F := by
      rw [hA₀]
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, hDR h.1⟩, h.1⟩⟩
    have hcs := card_sup_mul_card_inf hnorm
    rw [hinf, hNq', hA2, hD2] at hcs
    have hcard : Nat.card ↥(A₀ ⊔ D) = Nat.card F ^ 3 := by
      have hq0 : 0 < Nat.card F := by omega
      have : Nat.card ↥(A₀ ⊔ D) * Nat.card F = Nat.card F ^ 3 * Nat.card F := by
        rw [hcs]; ring
      exact Nat.eq_of_mul_eq_mul_right hq0 this
    have hQ₂R : Q₂ F ≤ R := by
      have hle : A₀ ⊔ D ≤ Q₂ F := sup_le hA₀Q₂ hDQ₂
      have heq : A₀ ⊔ D = Q₂ F := Subgroup.eq_of_le_of_card_ge hle (by rw [card_Q₂, hcard])
      exact heq ▸ sup_le hA₀R hDR
    have hμ : Nat.card F ^ 2 ≤ Nat.card ↥(qLine (mu₀ F) ⊓ R) := by
      rw [← card_qLine_inf_qPoint isPoint_pt₀ isLine_mu₀ pt₀_le_mu₀]
      exact Subgroup.card_le_of_le (inf_le_inf_left _ hQ₂R)
    have hcand := isCandSp_qLine_inf isLine_mu₀ hμ
    have hA₀m : A₀ ∈ candMax R := hA ▸ Set.mem_singleton A₀
    have hle := hA₀m.2 _ hcand
    have hmem : qLine (mu₀ F) ⊓ R ∈ candMax R :=
      ⟨hcand, fun B hB => (hA₀m.2 B hB).trans (by rw [hA2]; exact hμ)⟩
    rw [hA] at hmem
    have hA₀μ : A₀ ≤ qLine (mu₀ F) := (Set.mem_singleton_iff.1 hmem) ▸ inf_le_left
    have hX : A₀ ≤ X₂ F := by
      rw [X₂, ← qLine_inf_qLine isLine_ln₀ isLine_mu₀ isPoint_pt₀ ln₀_inf_mu₀]
      exact le_inf hA₀Q₁ hA₀μ
    have := Subgroup.card_le_of_le hX
    rw [card_X₂, hA2] at this
    have : Nat.card F < Nat.card F ^ 2 := by
      calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
        _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq1 (by norm_num)
    omega
  ·
    obtain ⟨u, huD, huQ₂⟩ := Set.not_subset.1 hDQ₂
    obtain ⟨hus, hue, hut⟩ := hdat u (hDR huD)
    have hδ : mat u (.inl 1) (.inr 1) ≠ 0 := fun h => huQ₂ ((mem_Q₂_iff_of_stab hus hue hut).2 h)
    have ha : mat u (.inl 0) (.inl 1) ≠ 0 := by
      intro h
      have huQ := (mem_Q₁_iff_of_stab hus hue hut).2 h
      exact hδ (hNbd u ⟨huD, huQ⟩).2
    obtain ⟨hsqQ, hsq⟩ := q1c_sq_of_stab hus hue hut
    have hb := (hNbd (u * u) ⟨D.mul_mem huD huD, hsqQ⟩).1
    have : mat (u * u) (.inl 0) (.inr 0) =
        mat u (.inl 0) (.inl 1) ^ 2 * mat u (.inl 1) (.inr 1) := congrArg Prod.fst hsq
    rw [this] at hb
    exact mul_ne_zero (pow_ne_zero 2 ha) hδ hb

end CFSG.Quasithin.MS93.S5
