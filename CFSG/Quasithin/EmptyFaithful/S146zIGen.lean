module

public import CFSG.Quasithin.EmptyFaithful.S146zHRank
public import CFSG.Quasithin.EmptyFaithful.S146zHFix
public import CFSG.Quasithin.EmptyFaithful.S146zHNon

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Setup

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.setup_g_not (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hs : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) : (g : G) ∉ mcOf T := by
  intro hg
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  apply S.conj_not_mem_Z hH hs hz hz1
  have hgN : (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    rw [S.normalizer_Z]
    exact hg
  exact (Subgroup.mem_normalizer_iff.mp hgN z).mp hz

theorem Setting146.setup_le (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hs : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) :
    F8.Uγ (VZ T M) H (g : G) ≤ H ∧ conjClosure (VZ T M) H ≤ conjSub (g : G) H := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  refine ⟨h98.Uγ_le_H hs, ?_⟩
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← hs.edge₁, stab_smul, stab_γ₁ h98.amalgamHypV.le₂]
  have h1 := (h98.F913_2 hs).1
  rw [← hstab]
  exact h1.trans ((pCoreOf_le 2 _).trans inf_le_right)

end Setup

section Gen

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_nontrivial_of_not_mem (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G} (hxH : x ∈ H)
    (hxQ : x ∉ pCoreOf 2 H) :
    (∃ u ∈ uHi T M H H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T) ∨
      (∃ u ∈ uHi T M H H₂, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T) := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  rw [← S.centralizerMod_uK_eq hH] at hxQ
  obtain ⟨k, hk, hkZ⟩ : ∃ k ∈ uK T M H, x * k * x⁻¹ * k⁻¹ ∉ quasithinOmegaOneCenter T := by
    by_contra hall
    push Not at hall
    exact hxQ ⟨hxH, hHN hxH, hall⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_decomp S hred hk
  have haN := hUZ (hi₁ ha)
  by_cases hxa : x * a * x⁻¹ * a⁻¹ ∈ quasithinOmegaOneCenter T
  · right
    refine ⟨b, hb, fun hxb => hkZ ?_⟩
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    refine (quasithinOmegaOneCenter T).mul_mem hxa ?_
    have := (Subgroup.mem_normalizer_iff.mp haN (x * b * x⁻¹ * b⁻¹)).mp hxb
    simpa using this
  · left
    exact ⟨a, ha, hxa⟩

theorem IsDecP.relIndex_uHi_mul (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) =
      (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
        (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) := by
  have hH : IsHTM T M H := hred.isHTM
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hU₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hc : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hU₁ hx) (hU₂ hy)
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁)
    (uHi T M H H₂) hc
  rw [h.dir_inf] at hprod
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := by rw [S.card_Z]; norm_num
  have eS := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁ ⊔ uHi T M H H₂)
  rw [inf_eq_left.mpr (le_sup_right.trans le_sup_left)] at eS
  have e1 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₁)] at e1
  have e2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₂)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₂)] at e2
  have hZ2 : 0 < Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T) :=
    Nat.mul_pos hZpos hZpos
  refine Nat.eq_of_mul_eq_mul_right hZ2 ?_
  rw [← eS, ← e1, ← e2] at hprod
  calc (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) *
        (Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T))
      = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) *
          Nat.card (quasithinOmegaOneCenter T)) * Nat.card (quasithinOmegaOneCenter T) := by ring
    _ = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
          Nat.card (quasithinOmegaOneCenter T)) *
        ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) *
          Nat.card (quasithinOmegaOneCenter T)) := hprod
    _ = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
          (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂)) *
        (Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T)) := by ring

theorem IsDecP.relIndex_uHi_eq (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) =
      (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) := by
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := by rw [S.card_Z]; norm_num
  have hcard : Nat.card (uHi T M H H₁) = Nat.card (uHi T M H H₂) := by
    rw [← h.conjSub_uHi hred]
    exact (CosetGeom.card_conjSub t _).symm
  have e1 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₁)] at e1
  have e2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₂)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₂)] at e2
  refine Nat.eq_of_mul_eq_mul_right hZpos ?_
  rw [e1, e2, hcard]

theorem IsDecP.mIdx_uK_sup_eq (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) =
      2 * mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) := by
  have hne : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hmul := h.relIndex_uHi_mul S hred
  rw [← h.relIndex_uHi_eq S hred] at hmul
  unfold mIdx
  rw [← h.dir_sup, hmul, padicValNat.mul hne hne]
  omega

theorem IsDecP.prime_lt_card_Wsub (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hne : ∃ w ∈ Wsub h91 (uHi T M H H₁), w ≠ 1) :
    p < Nat.card (Wsub h91 (uHi T M H H₁)) := by
  have hp : p.Prime := hred.prime
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨a, ha⟩ := hφs (DihedralGroup.r 1)
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  have hapQ : (a : G) ^ p ∈ pCoreOf 2 H := by
    have h1 : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
    simpa using (hker _).mp h1
  have hαinv : conjSub (a : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ a.2))
  have hαW : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
    fun w hw => rhoH_mem_Wsub h91 ⟨(a : G), haH⟩ hi₁ hαinv hw
  have hfixα : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(a : G), haH⟩ w = w → w = 1 :=
    fun w hw hwf => h.eq_one_of_fix S hred h91 φ hker ha hw hwf
  have hpow : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      (⇑(rhoH h91 ⟨(a : G), haH⟩))^[p] w = w := by
    intro w _
    rw [iterate_eq_pow_mulAut, ← map_pow]
    have h1 : rhoH h91 ((⟨(a : G), haH⟩ : ↥H) ^ p) = 1 :=
      (rhoH_eq_one_iff h91 _).mpr (by simpa using hapQ)
    rw [h1]
    rfl
  exact prime_lt_card_of_free (rhoH h91 ⟨(a : G), haH⟩) _ hp hαW hfixα hpow hne

end Gen

end CFSG.Quasithin
