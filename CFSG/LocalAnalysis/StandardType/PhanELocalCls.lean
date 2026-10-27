module

public import CFSG.ClassicalInvolution.Phan.Geometry.Points
public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

@[expose] def rho : (Fin 4 → K) →ₗ[K] (Fin 2 → K) where
  toFun v i := v ⟨i.val + 2, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rho_apply (v : Fin 4 → K) (i : Fin 2) : rho v i = v ⟨i.val + 2, by omega⟩ := rfl

theorem ker_rho : LinearMap.ker (rho (K := K)) = Vsub 4 2 := by
  ext v
  rw [LinearMap.mem_ker]
  constructor
  · intro hv j hj
    have h := congrFun hv ⟨j.val - 2, by omega⟩
    rw [rho_apply] at h
    have hidx : (⟨j.val - 2 + 2, by omega⟩ : Fin 4) = j :=
      Fin.ext (by rw [Fin.val_mk]; omega)
    rwa [hidx] at h
  · intro hv
    funext i
    rw [rho_apply]
    exact hv ⟨i.val + 2, by omega⟩ (by rw [Fin.val_mk]; omega)

theorem rho_surjective : Function.Surjective (rho (K := K)) := by
  intro u
  refine ⟨fun j : Fin 4 => if h : 2 ≤ j.val then u ⟨j.val - 2, by omega⟩ else 0, ?_⟩
  funext i
  rw [rho_apply]
  rw [dif_pos (show 2 ≤ (⟨i.val + 2, by omega⟩ : Fin 4).val by rw [Fin.val_mk]; omega)]
  exact congrArg u (Fin.ext (by simp))

structure ClsData (K : Type) [Field K] where
  ok : Submodule K (Fin 2 → K) → Prop
  good : Submodule K (Fin 2 → K) → Submodule K (Fin 4 → K) → Prop

@[expose] def AdmS (D : ClsData K) (p L H : Submodule K (Fin 4 → K)) : Prop :=
  L ⊓ Vsub 4 2 = ⊥ ∧ D.ok (p.map rho) ∧ D.good (p.map rho) (H ⊓ Vsub 4 2)

structure ClsHyp (D : ClsData K) (β : ℕ) : Prop where
  col : ∀ S : Finset (Submodule K (Fin 2 → K)), S.card ≤ 4 →
    ∃ c, D.ok c ∧ finrank K c = 1 ∧ c ∉ S
  two : ∀ c, D.ok c → finrank K c = 1 → ∃ M₁ M₂ : Submodule K (Fin 4 → K), M₁ ≠ M₂ ∧
    M₁ ≤ Vsub 4 2 ∧ M₂ ≤ Vsub 4 2 ∧ finrank K M₁ = 1 ∧ finrank K M₂ = 1 ∧
    D.good c M₁ ∧ D.good c M₂
  pair : ∀ c c', D.ok c → D.ok c' → finrank K c = 1 → finrank K c' = 1 → c ≠ c' →
    ∃ M : Submodule K (Fin 4 → K), M ≤ Vsub 4 2 ∧ finrank K M = 1 ∧ D.good c M ∧ D.good c' M
  bad : ∀ a b d, D.ok a → D.ok b → D.ok d → finrank K a = 1 → finrank K b = 1 →
    finrank K d = 1 → a ≠ b → b ≠ d → d ≠ a →
    ∃ B : Finset (Submodule K (Fin 4 → K)), B.Nonempty ∧ B.card ≤ β ∧
      (∀ m ∈ B, m ≤ Vsub 4 2 ∧ finrank K m = 1) ∧
      ∀ w ∈ Vsub 4 2, (∀ m ∈ B, w ∉ m) →
        w ≠ 0 ∧ D.good a (K ∙ w) ∧ D.good b (K ∙ w) ∧ D.good d (K ∙ w)
  small : 3 * β < Nat.card K

theorem finrank_map_rho {p : Submodule K (Fin 4 → K)} (hp : finrank K p = 1)
    (h : p ⊓ Vsub 4 2 = ⊥) : finrank K (p.map rho) = 1 := by
  have hdisj : Disjoint p (LinearMap.ker (rho (K := K))) := by
    rw [ker_rho]
    exact disjoint_iff.mpr h
  have hinj : Function.Injective (LinearMap.domRestrict rho p) := by
    rw [LinearMap.injective_domRestrict_iff]
    exact hdisj
  rw [← LinearMap.range_domRestrict p rho, LinearMap.finrank_range_of_inj hinj]
  exact hp

theorem map_rho_ne_iff {x y : Submodule K (Fin 4 → K)} (hx : finrank K x = 1)
    (hy : finrank K y = 1) (hxy : x ≠ y) (hx2 : x ⊓ Vsub 4 2 = ⊥) (hy2 : y ⊓ Vsub 4 2 = ⊥) :
    (x ⊔ y) ⊓ Vsub 4 2 = ⊥ ↔ x.map rho ≠ y.map rho := by
  obtain ⟨u, hu0, rfl⟩ := exists_eq_span_of_finrank_eq_one hx
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span_of_finrank_eq_one hy
  have huV : u ∉ Vsub 4 2 := by
    intro hu
    have hmem : u ∈ K ∙ u ⊓ Vsub 4 2 := ⟨Submodule.mem_span_singleton_self u, hu⟩
    rw [hx2] at hmem
    exact hu0 (by simpa using hmem)
  have hvV : v ∉ Vsub 4 2 := by
    intro hv
    have hmem : v ∈ K ∙ v ⊓ Vsub 4 2 := ⟨Submodule.mem_span_singleton_self v, hv⟩
    rw [hy2] at hmem
    exact hv0 (by simpa using hmem)
  have hru0 : rho u ≠ 0 := fun h => huV (by rw [← ker_rho]; exact LinearMap.mem_ker.mpr h)
  have hrv0 : rho v ≠ 0 := fun h => hvV (by rw [← ker_rho]; exact LinearMap.mem_ker.mpr h)
  have hmapu : (K ∙ u).map rho = K ∙ rho u := by
    rw [Submodule.map_span, Set.image_singleton]
  have hmapv : (K ∙ v).map rho = K ∙ rho v := by
    rw [Submodule.map_span, Set.image_singleton]
  have hiff : (K ∙ u).map rho = (K ∙ v).map rho ↔ ∃ c : K, u - c • v ∈ Vsub 4 2 := by
    rw [hmapu, hmapv]
    constructor
    · intro heq
      have hmem : rho u ∈ K ∙ rho v := by
        rw [← heq]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      refine ⟨c, ?_⟩
      rw [← ker_rho, LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
    · rintro ⟨c, hc⟩
      have hcu : rho u = c • rho v := by
        have h' := hc
        rw [← ker_rho, LinearMap.mem_ker, map_sub, map_smul] at h'
        exact sub_eq_zero.mp h'
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem, hcu]
        exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
      · rw [finrank_span_singleton hru0, finrank_span_singleton hrv0]
  constructor
  · intro hbot heq
    obtain ⟨c, hc⟩ := hiff.mp heq
    have hmem : u - c • v ∈ (K ∙ u ⊔ K ∙ v) ⊓ Vsub 4 2 :=
      ⟨Submodule.sub_mem _
          (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))),
        hc⟩
    rw [hbot] at hmem
    have hz : u - c • v = 0 := by simpa using hmem
    have huv : u ∈ K ∙ v := by
      have : u = c • v := sub_eq_zero.mp hz
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    exact hxy (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr huv)
      (by rw [finrank_span_singleton hu0, finrank_span_singleton hv0]))
  · intro hne
    have hex : ¬ ∃ c : K, u - c • v ∈ Vsub 4 2 := hiff.not.mp hne
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hw, hwV⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have ha : a = 0 := by
      by_contra ha0
      apply hex
      refine ⟨-(a⁻¹ * b), ?_⟩
      have hmem : a⁻¹ • w ∈ Vsub 4 2 := Submodule.smul_mem _ (a⁻¹) hwV
      have heq : u - (-(a⁻¹ * b)) • v = a⁻¹ • w := by
        rw [← hpq, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        rw [neg_smul, sub_neg_eq_add]
      rw [heq]
      exact hmem
    have hb : b = 0 := by
      by_contra hb0
      apply hvV
      have hmem : b⁻¹ • w ∈ Vsub 4 2 := Submodule.smul_mem _ (b⁻¹) hwV
      have heq : b⁻¹ • w = v := by
        rw [← hpq, ha, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hb0, one_smul]
      rwa [heq] at hmem
    rw [ha, hb, zero_smul, zero_smul, add_zero] at hpq
    exact hpq.symm

private theorem plh_sup_Vsub_eq_top {L : Submodule K (Fin 4 → K)} (hL : finrank K L = 2)
    (hL2 : L ⊓ Vsub 4 2 = ⊥) : L ⊔ Vsub 4 2 = ⊤ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq L (Vsub (K := K) 4 2)
  rw [hL2, finrank_bot, hL, finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)] at h
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [Module.finrank_fin_fun]
  omega

theorem exists_decomp {L : Submodule K (Fin 4 → K)} (hL : finrank K L = 2)
    (hL2 : L ⊓ Vsub 4 2 = ⊥) (v : Fin 4 → K) : ∃ l ∈ L, ∃ w ∈ Vsub 4 2, v = l + w := by
  have hv' : v ∈ L ⊔ Vsub 4 2 := by
    rw [plh_sup_Vsub_eq_top hL hL2]
    exact Submodule.mem_top
  obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.mp hv'
  exact ⟨l, hl, w, hw, hlw.symm⟩

theorem finrank_sup_trace {L M : Submodule K (Fin 4 → K)} (hL : finrank K L = 2)
    (hL2 : L ⊓ Vsub 4 2 = ⊥) (hM : M ≤ Vsub 4 2) (hM1 : finrank K M = 1) :
    finrank K (L ⊔ M : Submodule K (Fin 4 → K)) = 3 := by
  have hLM : L ⊓ M = ⊥ := by
    have hle : L ⊓ M ≤ L ⊓ Vsub 4 2 := inf_le_inf_left L hM
    rw [hL2] at hle
    exact le_bot_iff.mp hle
  have h := finrank_sup_of_disjoint (S := L) (T := M) (disjoint_iff.mpr hLM)
  rw [hL, hM1] at h
  exact h

theorem sup_trace_inf {L M : Submodule K (Fin 4 → K)} (hL : finrank K L = 2)
    (hL2 : L ⊓ Vsub 4 2 = ⊥) (hM : M ≤ Vsub 4 2) (hM1 : finrank K M = 1) :
    (L ⊔ M) ⊓ Vsub 4 2 = M := by
  have hMle : M ≤ (L ⊔ M) ⊓ Vsub 4 2 := le_inf le_sup_right hM
  have hsup : (L ⊔ M) ⊔ Vsub 4 2 = ⊤ := by
    rw [sup_assoc, sup_eq_right.mpr hM]
    exact plh_sup_Vsub_eq_top hL hL2
  have h := Submodule.finrank_sup_add_finrank_inf_eq (L ⊔ M) (Vsub (K := K) 4 2)
  have h1 : finrank K ↥((L ⊔ M) ⊔ Vsub 4 2) = 4 := by
    rw [hsup, finrank_top K (Fin 4 → K), Module.finrank_fin_fun K]
  have h2 : finrank K ↥(L ⊔ M) = 3 := by
    have hLM : L ⊓ M = ⊥ := by
      have hle : L ⊓ M ≤ L ⊓ Vsub 4 2 := inf_le_inf_left L hM
      rw [hL2] at hle
      exact le_bot_iff.mp hle
    have h' := finrank_sup_of_disjoint (S := L) (T := M) (disjoint_iff.mpr hLM)
    rw [hL, hM1] at h'
    exact h'
  have h3 : finrank K (Vsub (K := K) 4 2) = 2 :=
    finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)
  have hfin : finrank K ↥((L ⊔ M) ⊓ Vsub 4 2) = 1 := by
    rw [h1, h2, h3] at h
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hMle (by rw [hM1, hfin])).symm

end CFSG.ClassicalInvolution.Phan.PhanE

end
