module

public import CFSG.Quasithin.EmptyFaithful.S146R4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section Aux

theorem mul_commutator_mem {Z : Subgroup G} {x a b : G} (ha : a ∈ Subgroup.normalizer (Z : Set G))
    (hxa : x * a * x⁻¹ * a⁻¹ ∈ Z) (hxb : x * b * x⁻¹ * b⁻¹ ∈ Z) :
    x * (a * b) * x⁻¹ * (a * b)⁻¹ ∈ Z := by
  have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
      (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
  rw [e]
  exact Z.mul_mem hxa ((Subgroup.mem_normalizer_iff.mp ha _).mp hxb)

theorem conj_mem_centralizer {Q : Subgroup G} {g c : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hc : c ∈ Subgroup.centralizer (Q : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro q hq
  have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
  have h1 := hc _ hq'
  have e : q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g⁻¹⁻¹) * c) * g⁻¹ := by group
  have e' : g * c * g⁻¹ * q = g * (c * (g⁻¹ * q * g⁻¹⁻¹)) * g⁻¹ := by group
  rw [e, e', h1]

end Aux

variable [Finite G] {T M : Subgroup G}

section Dec

omit [Finite G] in
theorem IsDec12.conjSub_uHi {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    conjSub t (uHi T M H H₁) = uHi T M H H₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hsZ : t ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hdec.t_mem)
  unfold uHi
  have e1 : conjSub t ⁅conjClosure (VZ T M) H, H₁⁆ =
      ⁅conjSub t (conjClosure (VZ T M) H), conjSub t H₁⁆ := (conjSub_commutator t _ _).symm
  have e2 : conjSub t (conjClosure (VZ T M) H) = conjClosure (VZ T M) H :=
    conjSub_eq_of_mem_normalizer (hHU (hTH hdec.t_mem))
  have e3 : conjSub t (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
    conjSub_eq_of_mem_normalizer hsZ
  rw [show conjSub t (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ quasithinOmegaOneCenter T) =
      conjSub t ⁅conjClosure (VZ T M) H, H₁⁆ ⊔ conjSub t (quasithinOmegaOneCenter T) from
      Subgroup.map_sup _ _ _, e1, e2, e3, ← hdec.conj]

theorem IsDec12.exists_nc (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hOF : IsOFourPlusOn T M H) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDec12 T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H₁) (hxQ : x ∉ pCoreOf 2 H) :
    ∃ y ∈ uHi T M H H₁, x * y * x⁻¹ * y⁻¹ ∉ quasithinOmegaOneCenter T := by
  by_contra hall
  push Not at hall
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hU₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hUN := S.conjClosure_le_normalizer_Z hH
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hc : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hU₁ hx) (hU₂ hy)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁)
    (uHi T M H H₂) hc
  apply hxQ
  rw [← hOF.2]
  refine ⟨hH₁H hx, S.normalizer_Z.ge (S.le_mcOf hH (hH₁H hx)), fun u hu => ?_⟩
  have hKU : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have hu' : u ∈ uHi T M H H₁ ⊔ uHi T M H H₂ := by
    rw [hdec.dir_sup]
    exact Subgroup.mem_sup_left hu
  have hu'' : u ∈ (uHi T M H H₁ : Set G) * (uHi T M H H₂ : Set G) := by
    rw [← hset]
    exact hu'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hu''
  have haN : a ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hUN (hU₁ ha)
  have hxb : x * b * x⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T := by
    have h2 := (quasithinOmegaOneCenter T).inv_mem
      (hdec.cent₂ (Subgroup.commutator_mem_commutator hb hx))
    rw [commutatorElement_inv] at h2
    simpa [commutatorElement_def] using h2
  exact mul_commutator_mem haN (hall a ha) hxb

theorem IsDec12.le_normalizer_uHi (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    H₁ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hNZ : H₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    S.normalizer_Z.ge (S.le_mcOf hH (hH₁H hx))
  exact (le_inf (S145.le_normalizer_commutator (hH₁H.trans hHU) Subgroup.le_normalizer) hNZ).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem IsDec12.sec4 (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H) {H₀ H₁ H₂ : Subgroup G}
    {t : G} (hdec : IsDec12 T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H₁) (hxQ : x ∉ pCoreOf 2 H)
    (hx3 : x ^ 3 = 1) : Sec4 (quasithinOmegaOneCenter T) (uHi T M H H₁) x := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  exact
    { le := Z_le_uHi T M H H₁
      norm := hU₁.trans (S.conjClosure_le_normalizer_Z hH)
      sq := fun a ha => by
        rw [isElemAbelian_pow_eq_one hUab (hU₁ ha)]
        exact Subgroup.one_mem _
      card := (hdec.relIndex_uHi_eq_four S hred hp3 hOF).1
      xU := hdec.le_normalizer_uHi S hred hx
      xZ := S.normalizer_Z.ge (S.le_mcOf hH (hH₁H hx))
      x3 := by rw [hx3]; exact Subgroup.one_mem _
      nc := hdec.exists_nc S hred hOF hx hxQ }

theorem IsDec12.inf_centralizer_le (S : Setting146 G T M) (h5 : Stage1461Five)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) (hp3 : p = 3)
    (hOF : IsOFourPlusOn T M H) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    (uHi T M H H₁ ⊔ uHi T M H H₂) ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      quasithinOmegaOneCenter T := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hdec3 : IsDec12 T M H 3 H₀ H₁ H₂ t := hp3 ▸ hdec
  obtain ⟨z, hz1, hzQ, -, hz3⟩ := hdec3.exists_odd_three
  have hSec := hdec.sec4 S hred hp3 hOF hz1 hzQ hz3
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hH
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hU₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hUN := S.conjClosure_le_normalizer_Z hH
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hc : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hU₁ hx) (hU₂ hy)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁)
    (uHi T M H H₂) hc
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp
      (le_centralizer_quasithinOmegaOneCenter T (hQT hq)) w hw).symm
  have hzN : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H (hH₁H hz1)
  have htN : t ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    le_normalizer_pCoreOf 2 H (hTH hdec.t_mem)
  have htZ : t ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hdec.t_mem)
  have hE₁ : uHi T M H H₁ ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      quasithinOmegaOneCenter T := by
    by_contra hnot
    have heq := hSec.eq_of_invariant
      (E := uHi T M H H₁ ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))
      (le_inf (Z_le_uHi T M H H₁) hZC) inf_le_left
      (fun a ha => ⟨(Subgroup.mem_normalizer_iff.mp hSec.xU a).mp ha.1,
        conj_mem_centralizer hzN ha.2⟩) hnot
    apply S.not_le_centralizer_uHi h5 hred hp3 hdec
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ uHi T M H H₁ ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      rw [heq]; exact hu
    exact (Subgroup.mem_centralizer_iff.mp hu'.2 q hq).symm
  rintro s ⟨hsS, hsC⟩
  have hs' : s ∈ (uHi T M H H₁ : Set G) * (uHi T M H H₂ : Set G) := by
    rw [← hset]
    exact hsS
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hs'
  have haN : a ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hUN (hU₁ ha)
  have hxb : z * b * z⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T := by
    have h2 := (quasithinOmegaOneCenter T).inv_mem
      (hdec.cent₂ (Subgroup.commutator_mem_commutator hb hz1))
    rw [commutatorElement_inv] at h2
    simpa [commutatorElement_def] using h2
  have hca : z * a * z⁻¹ * a⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    have e : z * a * z⁻¹ * a⁻¹ = (z * (a * b) * z⁻¹ * (a * b)⁻¹) *
        (a * (z * b * z⁻¹ * b⁻¹) * a⁻¹)⁻¹ := by group
    rw [e]
    have hw : a * (z * b * z⁻¹ * b⁻¹) * a⁻¹ ∈ quasithinOmegaOneCenter T :=
      (Subgroup.mem_normalizer_iff.mp haN _).mp hxb
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (conj_mem_centralizer hzN hsC)
      (Subgroup.inv_mem _ hsC)) (Subgroup.inv_mem _ (hZC hw))
  have hca1 : z * a * z⁻¹ * a⁻¹ ∈ uHi T M H H₁ :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hSec.xU a).mp ha) (Subgroup.inv_mem _ ha)
  have haZ : a ∈ quasithinOmegaOneCenter T := hSec.fixed_mem ha (hE₁ ⟨hca1, hca⟩)
  have hbC : b ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hZC haZ)) hsC
  have hbU : t⁻¹ * b * t ∈ uHi T M H H₁ := by
    have : b ∈ conjSub t (uHi T M H H₁) := by
      rw [hdec.conjSub_uHi hred]
      exact hb
    exact mem_conjSub.mp this
  have hbC' : t⁻¹ * b * t ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    have := conj_mem_centralizer (Subgroup.inv_mem _ htN) hbC
    simpa using this
  have hbZ' : t⁻¹ * b * t ∈ quasithinOmegaOneCenter T := hE₁ ⟨hbU, hbC'⟩
  have hbZ : b ∈ quasithinOmegaOneCenter T := by
    have h1 := (Subgroup.mem_normalizer_iff.mp htZ _).mp hbZ'
    have e : t * (t⁻¹ * b * t) * t⁻¹ = b := by group
    rwa [e] at h1
  exact Subgroup.mul_mem _ haZ hbZ

omit [Finite G] in
theorem relIndex_ne_zero_fin [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem Setting146.four_le_mIdx_of_isOFourPlusOn (S : Setting146 G T M) (h5 : Stage1461Five)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) (hp3 : p = 3)
    (hOF : IsOFourPlusOn T M H) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hSU : uHi T M H H₁ ⊔ uHi T M H H₂ ≤ conjClosure (VZ T M) H :=
    sup_le (uHi_le_conjClosure hH₁H) (uHi_le_conjClosure hH₂H)
  have hZS : quasithinOmegaOneCenter T ≤ uHi T M H H₁ ⊔ uHi T M H H₂ :=
    (Z_le_uHi T M H H₁).trans le_sup_left
  have hK1 := hdec.inf_centralizer_le S h5 hred hp3 hOF
  have hrS := hdec.relIndex_uHi_sup S hred hOF
  have h1 : (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) ≤
      (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) :=
    Subgroup.relIndex_le_of_le_right hSU (relIndex_ne_zero_fin _ _)
  have h2 : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) ≤
      (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (pCoreOf 2 H : Set G))
      (uHi T M H H₁ ⊔ uHi T M H H₂)]
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)) ?_
    exact Subgroup.relIndex_dvd_of_le_left _ (by rw [inf_comm]; exact hK1)
  have h16 : 16 ≤ (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) := by
    rw [hrS] at h2
    exact h2.trans h1
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    (pCoreOf_isPGroup 2 H).to_le (S.conjClosure_le_pCoreOf hH)
  rw [HypF98.relIndex_eq_two_pow_mIdx hUp] at h16
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h16)

end Dec

end CFSG.Quasithin
