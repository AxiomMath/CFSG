module

public import CFSG.Quasithin.EmptyFaithful.S146zQCent
public import CFSG.Quasithin.EmptyFaithful.S146zHOfour
public import CFSG.Quasithin.EmptyFaithful.S146zISw

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section QRefl

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem q_exists_two_ne {A : Type} [Group A] [Finite A] (hcard : Nat.card A = 4) (ζ : A) :
    ∃ w : A, w ≠ 1 ∧ w ≠ ζ := by
  classical
  by_contra hno
  push Not at hno
  have hinj : Function.Injective (fun w : A => decide (w = 1)) := by
    intro w₁ w₂ hww
    have h' : decide (w₁ = 1) = decide (w₂ = 1) := hww
    by_cases h1 : w₁ = 1
    · have h2 : w₂ = 1 := by
        by_contra h2
        simp [h1, h2] at h'
      exact h1.trans h2.symm
    · have h2 : ¬ w₂ = 1 := by
        intro h2
        simp [h1, h2] at h'
      exact (hno _ h1).trans (hno _ h2).symm
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

omit [Finite G] in
theorem q_H_cent_Z (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    ∀ x ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, x * z * x⁻¹ = z := by
  intro x hx z hz
  have h1 := (Subgroup.mem_centralizer_iff.mp (h91.H_le_centralizer hx)) z hz
  rw [← h1]
  group

omit [Finite G] in
theorem IsDecP.pCore_cent_uHi₁ {p : ℕ}
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hQC : pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G)) :
    ∀ q ∈ pCoreOf 2 H, ∀ x ∈ uHi T M H H₁, q * x * q⁻¹ = x := by
  intro q hq x hx
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  have hle : uK T M H ⊔ quasithinOmegaOneCenter T ≤ Subgroup.centralizer ({q} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun z hz => ?_)
    · have := Subgroup.mem_centralizer_iff.mp (hQC hq) u hu
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact this.symm
    · refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have := q_H_cent_Z h91 q hqH z hz
      calc q * z = (q * z * q⁻¹) * q := by group
        _ = z * q := by rw [this]
  have hx' : x ∈ uK T M H ⊔ quasithinOmegaOneCenter T := by
    rw [← h.dir_sup]
    exact Subgroup.mem_sup_left hx
  have := Subgroup.mem_centralizer_iff.mp (hle hx') q rfl
  calc q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [this]
    _ = x := by group

theorem IsDecP.htrans₁ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) {u u' : G}
    (hu : u ∈ uHi T M H H₁) (hu' : u' ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) (hu'Z : u' ∉ quasithinOmegaOneCenter T) :
    ∃ c ∈ H₁, ∃ z ∈ quasithinOmegaOneCenter T, c * u * c⁻¹ = u' * z := by
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have huU := hi₁ hu
  have hu'U := hi₁ hu'
  obtain ⟨c, hcH₁, hc⟩ := h.exists_rot_of_card_four S hred h91 hcard
    (clsU_mem_Wsub h91 huU hu) (fun e => huZ ((clsU_eq_one_iff h91 huU).mp e))
    (clsU_mem_Wsub h91 hu'U hu') (fun e => hu'Z ((clsU_eq_one_iff h91 hu'U).mp e))
  rw [rhoH_clsU] at hc
  have h1 := (clsU_eq_iff h91 (conj_mem_UH c.2 huU) hu'U).mp hc
  refine ⟨(c : G), hcH₁, (((c : G) * u * (c : G)⁻¹)⁻¹ * u')⁻¹, ?_, ?_⟩
  · exact (quasithinOmegaOneCenter T).inv_mem h1
  · group

theorem IsDecP.hrich₁ (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) :
    ∃ a ∈ uHi T M H H₁, ∃ a' ∈ uHi T M H H₁, a ∉ quasithinOmegaOneCenter T ∧
      a' ∉ quasithinOmegaOneCenter T ∧ a * a' ∉ quasithinOmegaOneCenter T := by
  classical
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hinv : ∀ v : UMod h91, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using IntMod.sq_eq_one v)
  obtain ⟨ζ, hζ1⟩ : ∃ ζ : ↥(Wsub h91 (uHi T M H H₁)), ζ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hs : Subsingleton ↥(Wsub h91 (uHi T M H H₁)) := ⟨fun a b => (hno a).trans (hno b).symm⟩
    have : Nat.card ↥(Wsub h91 (uHi T M H H₁)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩
    omega
  obtain ⟨w', hw'1, hw'ζ⟩ := q_exists_two_ne hcard ζ
  obtain ⟨a, haU, haX, hcl⟩ := exists_clsU_of_mem_Wsub h91 hi₁ ζ.2
  obtain ⟨a', ha'U, ha'X, hcl'⟩ := exists_clsU_of_mem_Wsub h91 hi₁ w'.2
  refine ⟨a, haX, a', ha'X, fun hZ => hζ1 ?_, fun hZ => hw'1 ?_, fun hZ => hw'ζ ?_⟩
  · exact Subtype.ext (hcl.symm.trans ((clsU_eq_one_iff h91 haU).mpr hZ))
  · exact Subtype.ext (hcl'.symm.trans ((clsU_eq_one_iff h91 ha'U).mpr hZ))
  · have h1 := (clsU_eq_one_iff h91 ((conjClosure (VZ T M) H).mul_mem haU ha'U)).mpr hZ
    rw [← clsU_mul h91 haU ha'U, hcl, hcl'] at h1
    apply Subtype.ext
    have h2 : (w' : UMod h91) = (ζ : UMod h91)⁻¹ := (eq_inv_of_mul_eq_one_right h1)
    rw [h2, hinv]

theorem IsDecP.card_Wsub₂ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) :
    Nat.card (Wsub h91 (uHi T M H H₂)) = 4 := by
  have hH : IsHTM T M H := hred.isHTM
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  rw [card_Wsub h91 hi₁, card_tildeOf_eq_relIndex (Z_le_uHi T M H H₁) (hi₁.trans hUZ)] at hcard
  rw [card_Wsub h91 hi₂, card_tildeOf_eq_relIndex (Z_le_uHi T M H H₂) (hi₂.trans hUZ),
    ← h.relIndex_uHi_eq S hred]
  exact hcard

theorem IsDecP.cent_H₂_U₁ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4)
    (hQC : pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G)) :
    ∀ x ∈ H₂, ∀ a ∈ uHi T M H H₁, x * a * x⁻¹ = a := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hHZ := q_H_cent_Z h91
  refine qcent_of_trans (P := H₂) (R := H₁) (N := uHi T M H H₁)
    (Zs := quasithinOmegaOneCenter T) (Qs := pCoreOf 2 H)
    (fun a ha a' ha' => isElemAbelian_comm hUab (hi₁ ha) (hi₁ ha'))
    (Z_le_uHi T M H H₁)
    (fun x hx z hz => hHZ x (h.le (h.le₂ hx)) z hz)
    (fun x hx z hz => hHZ x (h.le (h.le₁ hx)) z hz)
    (fun x hx a ha => ?_)
    (fun x hx a ha => ?_)
    (fun x hx y hy => ?_)
    (h.pCore_cent_uHi₁ h91 hQC)
    (fun u hu huZ u' hu' hu'Z => h.htrans₁ S hred h91 hcard hu hu' huZ hu'Z)
    (h.hrich₁ h91 hcard)
  · have h1 : ⁅a, x⁆ ∈ quasithinOmegaOneCenter T :=
      h.cent₁ (Subgroup.commutator_mem_commutator ha hx)
    have e : x * a * x⁻¹ * a⁻¹ = (⁅a, x⁆)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1
  · have hn := h.le_normalizer_uHi₁ S hred (h.le₁ hx)
    exact (Subgroup.mem_normalizer_iff.mp hn a).mp ha
  · have := h.comm (Subgroup.commutator_mem_commutator hx hy)
    rwa [commutatorElement_def] at this

theorem IsDecP.cent_H₁_U₂ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4)
    (hQC : pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G)) :
    ∀ x ∈ H₁, ∀ b ∈ uHi T M H H₂, x * b * x⁻¹ = b :=
  h.swap.cent_H₂_U₁ S hred h91 (h.card_Wsub₂ S hred h91 hcard) hQC

theorem IsDecP.exists_refl_fixing_sq (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) {ζ₁ : UMod h91}
    (hζ : ζ₁ ∈ Wsub h91 (uHi T M H H₁)) (hζ1 : ζ₁ ≠ 1) :
    ∃ a₁ : ↥H, (a₁ : G) ∈ H₁ ∧ (a₁ : G) * (a₁ : G) ∈ pCoreOf 2 H ∧ rhoH h91 a₁ ζ₁ = ζ₁ ∧
      ∃ u ∈ Wsub h91 (uHi T M H H₁), rhoH h91 a₁ u ≠ u := by
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have : Fact (1 < 3) := ⟨by norm_num⟩
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨b, hb⟩ := hφs (DihedralGroup.sr 0)
  have hbH : (b : G) ∈ H := h.le (h.le₁ b.2)
  have hbQ : (b : G) ∉ pCoreOf 2 H := by
    intro hQ
    have h1 := (hker b).mpr hQ
    rw [hb] at h1
    have h3 : DihedralGroup.sr (0 : ZMod 3) = DihedralGroup.r 0 := h1.trans DihedralGroup.one_def
    cases h3
  have hbb : (b : G) * (b : G) ∈ pCoreOf 2 H := by
    have h1 : φ (b * b) = 1 := by rw [map_mul, hb]; exact DihedralGroup.sr_mul_self 0
    simpa using (hker _).mp h1
  have hρbb : rhoH h91 ⟨(b : G), hbH⟩ * rhoH h91 ⟨(b : G), hbH⟩ = 1 := by
    rw [← map_mul]
    exact (rhoH_eq_one_iff h91 _).mpr hbb
  have hββ : ∀ v : UMod h91, rhoH h91 ⟨(b : G), hbH⟩ (rhoH h91 ⟨(b : G), hbH⟩ v) = v := by
    intro v
    have := congrArg (fun f : MulAut (UMod h91) => f v) hρbb
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hinvb : conjSub (b : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ b.2))
  have hexb : ∀ v ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(b : G), hbH⟩ v ∈ Wsub h91 (uHi T M H H₁) :=
    fun v hv => rhoH_mem_Wsub h91 ⟨(b : G), hbH⟩ hi₁ hinvb hv
  have hmv : ∃ u ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(b : G), hbH⟩ u ≠ u := by
    rcases h.exists_nontrivial_of_not_mem S hred hbH hbQ with ⟨u, hu, hn⟩ | ⟨u, hu, hn⟩
    · refine ⟨clsU h91 (hi₁ hu), clsU_mem_Wsub h91 (hi₁ hu) hu, fun e => hn ?_⟩
      exact (rhoH_clsU_eq_iff h91 ⟨(b : G), hbH⟩ (hi₁ hu)).mp e
    · exfalso
      apply hn
      have h1 : ⁅u, (b : G)⁆ ∈ quasithinOmegaOneCenter T :=
        h.cent₂ (Subgroup.commutator_mem_commutator hu b.2)
      have e : (b : G) * u * (b : G)⁻¹ * u⁻¹ = (⁅u, (b : G)⁆)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (quasithinOmegaOneCenter T).inv_mem h1
  obtain ⟨w₀, hw₀, hw₀1, hbw₀⟩ := exists_fixed_of_involution (rhoH h91 ⟨(b : G), hbH⟩) _ hββ hexb
    (fun v => by simpa [pow_two] using IntMod.sq_eq_one v) hmv
  obtain ⟨c, hcH₁, hcw⟩ := h.exists_rot_of_card_four S hred h91 hcard hw₀ hw₀1 hζ hζ1
  have hcH : (c : G) ∈ H := c.2
  have hcinv : conjSub (c : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ hcH₁))
  have hexc : ∀ v ∈ Wsub h91 (uHi T M H H₁), rhoH h91 c v ∈ Wsub h91 (uHi T M H H₁) :=
    fun v hv => rhoH_mem_Wsub h91 c hi₁ hcinv hv
  refine ⟨c * ⟨(b : G), hbH⟩ * c⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (c : G) * (b : G) * (c : G)⁻¹ ∈ H₁ :=
      H₁.mul_mem (H₁.mul_mem hcH₁ b.2) (H₁.inv_mem hcH₁)
    simpa using h1
  · have e : (((c * ⟨(b : G), hbH⟩ * c⁻¹ : ↥H) : G)) * (((c * ⟨(b : G), hbH⟩ * c⁻¹ : ↥H) : G)) =
        (c : G) * ((b : G) * (b : G)) * (c : G)⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H c.2) _).mp hbb
  · rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, ← hcw]
    have : ((rhoH h91 c)⁻¹) (rhoH h91 c w₀) = w₀ := by simp
    rw [this, hbw₀]
  · obtain ⟨u, hu, hnu⟩ := hmv
    refine ⟨rhoH h91 c u, hexc u hu, fun e => hnu ?_⟩
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply] at e
    have e' : ((rhoH h91 c)⁻¹) (rhoH h91 c u) = u := by simp
    rw [e'] at e
    have := (rhoH h91 c).injective e
    exact this

theorem IsDecP.refl_lift_fixed (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4)
    (hQC : pCoreOf 2 H ≤ Subgroup.centralizer (uK T M H : Set G))
    {a₁ : ↥H} (ha₁ : (a₁ : G) ∈ H₁) (hsq : (a₁ : G) * (a₁ : G) ∈ pCoreOf 2 H)
    {ζ : UMod h91} (hζ1 : ζ ≠ 1) (hζW : ζ ∈ Wsub h91 (uHi T M H H₁))
    (hfix : rhoH h91 a₁ ζ = ζ)
    {u₀ : UMod h91} (hu₀ : u₀ ∈ Wsub h91 (uHi T M H H₁)) (hmv : rhoH h91 a₁ u₀ ≠ u₀)
    {a : G} (haU : a ∈ conjClosure (VZ T M) H) (hcls : clsU h91 haU = ζ) :
    (a₁ : G) * a * (a₁ : G)⁻¹ = a := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hinv : ∀ v : UMod h91, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using IntMod.sq_eq_one v)
  have hHZ := q_H_cent_Z h91
  have hn := h.le_normalizer_uHi₁ S hred (h.le₁ ha₁)
  have hρρ : ∀ v : UMod h91, rhoH h91 a₁ (rhoH h91 a₁ v) = v := by
    intro v
    have h1 : rhoH h91 a₁ * rhoH h91 a₁ = 1 := by
      rw [← map_mul]
      exact (rhoH_eq_one_iff h91 _).mpr hsq
    have := congrArg (fun f : MulAut (UMod h91) => f v) h1
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  obtain ⟨u, huU, huX, hu₀cls⟩ := exists_clsU_of_mem_Wsub h91 hi₁ hu₀
  have hau : (a₁ : G) * u * (a₁ : G)⁻¹ ∈ uHi T M H H₁ :=
    (Subgroup.mem_normalizer_iff.mp hn u).mp huX
  have hauU : (a₁ : G) * u * (a₁ : G)⁻¹ ∈ conjClosure (VZ T M) H := conj_mem_UH a₁.2 huU
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = (a₁ : G) * u * (a₁ : G)⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hcX : c ∈ uHi T M H H₁ := by
    rw [hcdef]
    exact (uHi T M H H₁).mul_mem hau ((uHi T M H H₁).inv_mem huX)
  have hcU : c ∈ conjClosure (VZ T M) H := hi₁ hcX
  have hclsc : clsU h91 hcU = rhoH h91 a₁ u₀ * u₀⁻¹ := by
    have e1 := clsU_mul h91 hauU ((conjClosure (VZ T M) H).inv_mem huU)
    rw [← rhoH_clsU h91 a₁ huU, ← clsU_inv h91 huU, hu₀cls] at e1
    exact (clsU_congr h91 hcU _ hcdef).trans e1.symm
  have hρc : rhoH h91 a₁ (clsU h91 hcU) = clsU h91 hcU := by
    rw [hclsc, map_mul, map_inv, hρρ, hinv u₀, hinv (rhoH h91 a₁ u₀)]
    exact mul_comm _ _
  have hc1 : clsU h91 hcU ≠ 1 := by
    rw [hclsc, hinv u₀]
    intro e
    have h1 := eq_inv_of_mul_eq_one_left e
    rw [hinv] at h1
    exact hmv h1
  let F : Subgroup (UMod h91) :=
    { carrier := {x | x ∈ Wsub h91 (uHi T M H H₁) ∧ rhoH h91 a₁ x = x}
      mul_mem' := fun {x y} hx hy =>
        ⟨(Wsub h91 (uHi T M H H₁)).mul_mem hx.1 hy.1, by rw [map_mul, hx.2, hy.2]⟩
      one_mem' := ⟨(Wsub h91 (uHi T M H H₁)).one_mem, map_one _⟩
      inv_mem' := fun {x} hx =>
        ⟨(Wsub h91 (uHi T M H H₁)).inv_mem hx.1, by rw [map_inv, hx.2]⟩ }
  have hFW : F ≤ Wsub h91 (uHi T M H H₁) := fun x hx => hx.1
  have hF2 : Nat.card F = 2 := by
    have hdvd : Nat.card F ∣ Nat.card (Wsub h91 (uHi T M H H₁)) := Subgroup.card_dvd_of_le hFW
    rw [hcard] at hdvd
    have hne4 : Nat.card F ≠ 4 := by
      intro e
      have := Subgroup.eq_of_le_of_card_ge hFW (by rw [hcard, e])
      have hu₀F : u₀ ∈ F := by rw [this]; exact hu₀
      exact hmv hu₀F.2
    have hne1 : Nat.card F ≠ 1 := by
      intro e
      have hb := Subgroup.card_eq_one.mp e
      have hζF : ζ ∈ F := ⟨hζW, hfix⟩
      rw [hb] at hζF
      exact hζ1 (Subgroup.mem_bot.mp hζF)
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card F := Nat.card_pos
    generalize Nat.card F = n at hdvd hne4 hne1 hle4 hpos ⊢
    interval_cases n <;> omega
  have hζF : ζ ∈ F := ⟨hζW, hfix⟩
  have hcF : clsU h91 hcU ∈ F := ⟨clsU_mem_Wsub h91 hcU hcX, hρc⟩
  have hce : clsU h91 hcU = ζ := by
    rcases eq_one_or_eq_of_card_subgroup_two F hF2 hζF hζ1 hcF with e | e
    · exact absurd e hc1
    · exact e
  have hcz : c⁻¹ * a ∈ quasithinOmegaOneCenter T :=
    (clsU_eq_iff h91 hcU haU).mp (hce.trans hcls.symm)
  have hq2 : ((a₁ : G) * (a₁ : G)) * u * ((a₁ : G) * (a₁ : G))⁻¹ = u :=
    h.pCore_cent_uHi₁ h91 hQC _ hsq u huX
  have hc2 : c ^ 2 = 1 := hUab.2 c hcU
  have hcc : c⁻¹ = c := by
    have : c * c = 1 := by rw [← sq]; exact hc2
    exact inv_eq_of_mul_eq_one_right this
  have hfixc : (a₁ : G) * c * (a₁ : G)⁻¹ = c := by
    have e1 : (a₁ : G) * c * (a₁ : G)⁻¹ =
        (((a₁ : G) * (a₁ : G)) * u * ((a₁ : G) * (a₁ : G))⁻¹) * ((a₁ : G) * u⁻¹ * (a₁ : G)⁻¹) := by
      rw [hcdef]; group
    have e2 : c⁻¹ = u * ((a₁ : G) * u⁻¹ * (a₁ : G)⁻¹) := by
      rw [hcdef]; group
    rw [e1, hq2, ← e2, hcc]
  have hza : (a₁ : G) * (c⁻¹ * a) * (a₁ : G)⁻¹ = c⁻¹ * a := hHZ _ a₁.2 _ hcz
  calc (a₁ : G) * a * (a₁ : G)⁻¹
      = ((a₁ : G) * c * (a₁ : G)⁻¹) * ((a₁ : G) * (c⁻¹ * a) * (a₁ : G)⁻¹) := by group
    _ = c * (c⁻¹ * a) := by rw [hfixc, hza]
    _ = a := by group

end QRefl

end CFSG.Quasithin
