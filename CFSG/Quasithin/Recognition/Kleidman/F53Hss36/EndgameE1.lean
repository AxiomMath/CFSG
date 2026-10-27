module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim3
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.S5Facts
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenB

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Claim5Spec (H M S : Subgroup G) : Prop :=
  ∀ {α β α' : Geo H M}, Ctx H M S α β α' →
    ¬ Zv α' ≤ Vn β ∧ (Qv α').relIndex (Vn β) = 4 ∧ ¬ Zv β ≤ Vn α'

omit [Finite G] in
theorem exists_klein_gens {Γ : Type*} [Group Γ] [Finite Γ] {T : Subgroup Γ}
    (hT : Nat.card T = 4) (hsq : ∀ t ∈ T, t * t = 1) :
    ∃ a ∈ T, ∃ b ∈ T, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
      ∀ x ∈ T, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ T, a ≠ 1 := by
    by_contra h
    push Not at h
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr h
    rw [this, Subgroup.card_bot] at hT
    omega
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ T, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hle : ∀ x ∈ T, x = 1 ∨ x = a := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have hinj : Function.Injective (fun x : ↥T => if (x : Γ) = 1 then (0 : Fin 2) else 1) := by
      intro x y hxy
      apply Subtype.ext
      rcases hle x x.2 with hx | hx <;> rcases hle y y.2 with hy | hy
      · rw [hx, hy]
      · simp [hx, hy, ha1] at hxy
      · simp [hx, hy, ha1] at hxy
      · rw [hx, hy]
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at this
    omega
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq _ (T.mul_mem ha hb))
  have hab : a * b = b * a := by rw [← hab', mul_inv_rev, ha', hb']
  have hab1 : a * b ≠ 1 := fun h => hba (by
    have := eq_inv_of_mul_eq_one_right h; rw [this, ha'])
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  refine ⟨a, ha, b, hb, ha1, hb1, hba.symm, hab, fun x hx => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hx1, hxa, hxb, hxab⟩ := hne
  let f : Fin 5 → ↥T := ![1, ⟨a, ha⟩, ⟨b, hb⟩, ⟨a * b, T.mul_mem ha hb⟩, ⟨x, hx⟩]
  have d01 : (1 : Γ) ≠ a := ha1.symm
  have d10 : (a : Γ) ≠ 1 := d01.symm
  have d02 : (1 : Γ) ≠ b := hb1.symm
  have d20 : (b : Γ) ≠ 1 := d02.symm
  have d03 : (1 : Γ) ≠ a * b := hab1.symm
  have d30 : (a * b : Γ) ≠ 1 := d03.symm
  have d04 : (1 : Γ) ≠ x := hx1.symm
  have d40 : (x : Γ) ≠ 1 := d04.symm
  have d12 : (a : Γ) ≠ b := hba.symm
  have d21 : (b : Γ) ≠ a := d12.symm
  have d13 : (a : Γ) ≠ a * b := haba.symm
  have d31 : (a * b : Γ) ≠ a := d13.symm
  have d14 : (a : Γ) ≠ x := hxa.symm
  have d41 : (x : Γ) ≠ a := d14.symm
  have d23 : (b : Γ) ≠ a * b := habb.symm
  have d32 : (a * b : Γ) ≠ b := d23.symm
  have d24 : (b : Γ) ≠ x := hxb.symm
  have d42 : (x : Γ) ≠ b := d24.symm
  have d34 : (a * b : Γ) ≠ x := hxab.symm
  have d43 : (x : Γ) ≠ a * b := d34.symm
  have hinj : Function.Injective f := by
    intro i j hij
    have h' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact (d01 h').elim | exact (d02 h').elim | exact (d03 h').elim | exact (d04 h').elim | exact (d10 h').elim | exact (d12 h').elim | exact (d13 h').elim | exact (d14 h').elim | exact (d20 h').elim | exact (d21 h').elim | exact (d23 h').elim | exact (d24 h').elim | exact (d30 h').elim | exact (d31 h').elim | exact (d32 h').elim | exact (d34 h').elim | exact (d40 h').elim | exact (d41 h').elim | exact (d42 h').elim | exact (d43 h').elim
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at this
  omega

theorem mem_of_comm_klein {T : Subgroup (Perm (Fin 5))} (hT : Nat.card T = 4)
    (hTA : T ≤ alternatingGroup (Fin 5)) {x : Perm (Fin 5)} (hx : ∀ t ∈ T, x * t = t * x) :
    x ∈ T := by
  have hsq : ∀ t ∈ T, t * t = 1 := by
    intro t ht
    have h : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ^ 4 = 1 → y * y = 1 := by decide +kernel
    refine h t (Perm.mem_alternatingGroup.mp (hTA ht)) ?_
    have := pow_card_eq_one' (G := ↥T) (x := ⟨t, ht⟩)
    rw [hT] at this
    exact congrArg Subtype.val this
  obtain ⟨a, ha, b, hb, ha1, hb1, hab, hc, hall⟩ := exists_klein_gens hT hsq
  rcases centralizer_T_type (hsq a ha) (hsq b hb) ha1 hb1 hab hc
      (Perm.mem_alternatingGroup.mp (hTA ha)) (Perm.mem_alternatingGroup.mp (hTA hb))
      (hx a ha) (hx b hb) with h | h | h | h
  · rw [h]; exact T.one_mem
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact T.mul_mem ha hb

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem mem_sup_of_map_mem {F Q X : Subgroup G} {θ : ↥F →* Perm (Fin 5)}
    (hθk : θ.ker = Q.subgroupOf F) {g : G} (hg : g ∈ F)
    (hmem : θ ⟨g, hg⟩ ∈ (X.subgroupOf F).map θ) : g ∈ X ⊔ Q := by
  obtain ⟨k, hk, hkg⟩ := hmem
  have hq : (k⁻¹ * ⟨g, hg⟩ : ↥F) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  rw [hθk, Subgroup.mem_subgroupOf] at hq
  have e : g = (k : G) * ((k⁻¹ * ⟨g, hg⟩ : ↥F) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk))
    (Subgroup.mem_sup_right hq)

theorem mem_sup_of_centralizes (h4 : Claim4Spec H M S) (h5 : Claim5Spec H M S) {w : G}
    (hw : w ∈ stab α') (hwc : w ∈ Subgroup.centralizer (Vn β : Set G)) : w ∈ Vn β ⊔ Qv α' := by
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := C.exists_secData C.vtype_alpha'
  have hVs : Vn β ≤ stab α' := C.Vn_beta_le_stab
  set T := ((Vn β).subgroupOf (stab α')).map θ with hT
  have hT4 : Nat.card T = 4 := by
    rw [hT, ← relIndex_inf_eq_card_map hθk hVs, Subgroup.inf_relIndex_left]
    exact (h5 C).2.1
  have hTA : T ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨v, hv, rfl⟩
    exact (S34.mem_sup_iff_alt hθs hθk v.2).mp (h4 C (Subgroup.mem_subgroupOf.mp hv))
  refine C.mem_sup_of_map_mem hθk hw (mem_of_comm_klein hT4 hTA ?_)
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp hwc v (Subgroup.mem_subgroupOf.mp hv)).symm

theorem e1 (h4 : Claim4Spec H M S) (h5 : Claim5Spec H M S) (P : CritPath α β α')
    (h7 : Wnn β ≤ stab P.γ) :
    ¬ Wnn β ≤ stab α' ∧ Zv α' ≤ Wnn β ∧ ¬ Wnn β ≤ Subgroup.centralizer (Zv α' : Set G) := by
  have hb := C.hb5
  have hvγ := C.vtype_P_γ P
  have hvδ := C.vtype_P_δ P
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hδγ : P.δ ∈ nbrs P.γ := mem_nbrs_comm hγ
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  have hWδ : Wnn β ≤ stab P.δ := C.Wnn_le_stab_of_dist C.vtype_beta (C.dist_beta_P_δ P).le
  have hQγα : Qv P.γ ≤ stab α' := Qv_le_stab_of_mem_nbrs C.hA hα'
  have hi : ¬ Wnn β ≤ stab α' := by
    intro hWα
    apply C.claim3
    intro w hw
    exact C.mem_sup_of_centralizes h4 h5 (hWα hw) (C.Wnn_le_centralizer_Vn C.vtype_beta hw)
  refine ⟨hi, ?_, ?_⟩
  ·
    set U := Wnn β ⊓ Qv P.γ with hU
    have hUs : U ≤ stab α' := inf_le_right.trans hQγα
    have hUV : U ≤ Vn β ⊔ Qv α' := fun u hu =>
      C.mem_sup_of_centralizes h4 h5 (hUs hu) (C.Wnn_le_centralizer_Vn C.vtype_beta hu.1)
    have hidx : (Qv P.γ).relIndex (Wnn β) ≤ 2 := by
      have h1 := Subgroup.relIndex_le_of_le_right (H := Qv P.γ) (le_inf h7 hWδ)
        (relIndex_ne_zero_of_finite (Qv P.γ) (stab P.γ ⊓ stab P.δ))
      rwa [relIndex_Qv_inf_true C.hA hδγ hvγ] at h1
    by_contra hZ
    have hcomm : ∀ q ∈ Wnn β ⊓ Qv α', ∀ y ∈ Vn α', q * y = y * q := by
      intro q hq y hy
      by_contra hne
      apply hZ
      have hc : q * y * q⁻¹ * y⁻¹ ∈ Zv α' := by
        rw [← C.comm_Vn_Qv_eq C.vtype_alpha', Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hq.2 hy
      have hc1 : q * y * q⁻¹ * y⁻¹ ≠ 1 := by
        intro h
        apply hne
        have := congrArg (· * y * q) h
        simpa [mul_assoc] using this
      have hcW : q * y * q⁻¹ * y⁻¹ ∈ Wnn β := by
        have hys : y ∈ stab β := C.Vn_alpha'_le_stab hy
        have h1 : y * q⁻¹ * y⁻¹ ∈ Wnn β :=
          (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wnn β hys) _).mp
            (inv_mem hq.1)
        have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
        rw [e]; exact mul_mem hq.1 h1
      intro z hz
      obtain ⟨hzmem, hz1, hzonly⟩ := C.zgen_spec' C.vtype_alpha'
      rcases hzonly z hz with rfl | rfl
      · exact one_mem _
      · rcases hzonly _ hc with h | h
        · exact absurd h hc1
        · rw [← h]; exact hcW
    obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le
    have hys : y ∈ stab β := C.Vn_alpha'_le_stab hyV
    obtain ⟨μ, C'⟩ := C.exists_mirror
    have hyL : y ∈ oTwoRes (stab β) ⊔ Qv β := h4 C' hyV
    have hVQ : Vn β ≤ Subgroup.normalizer (Qv α' : Set G) :=
      C.Vn_beta_le_stab.trans (le_normalizer_pCoreOf 2 _)
    refine C.false_of_small_action C.vtype_beta hys hyQ hyL (U := U) (D := Vn β) inf_le_left
      le_rfl (Vn_le_Wnn_self β) ?_ ?_
    · rw [Subgroup.relIndex_self, mul_one]
      refine (Subgroup.relIndex_le_of_le_left le_sup_left
        (relIndex_ne_zero_of_finite _ _)).trans ?_
      rw [hU, Subgroup.inf_relIndex_left]
      exact hidx
    · intro u hu
      have hu' : u ∈ ((Vn β ⊔ Qv α' : Subgroup G) : Set G) := hUV hu
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (Vn β) (Qv α') hVQ] at hu'
      obtain ⟨v, hv, q, hq, rfl⟩ := hu'
      have hqW : q ∈ Wnn β := by
        have e : q = v⁻¹ * (v * q) := by group
        rw [e]
        exact mul_mem (inv_mem (Vn_le_Wnn_self β hv)) hu.1
      have hqy := hcomm q ⟨hqW, hq⟩ y hyV
      have e : v * q * y * (v * q)⁻¹ * y⁻¹ = v * y * v⁻¹ * y⁻¹ := by
        calc v * q * y * (v * q)⁻¹ * y⁻¹ = v * (q * y) * q⁻¹ * v⁻¹ * y⁻¹ := by group
          _ = v * (y * q) * q⁻¹ * v⁻¹ * y⁻¹ := by rw [hqy]
          _ = v * y * v⁻¹ * y⁻¹ := by group
      rw [e]
      have : v * y * v⁻¹ * y⁻¹ ∈ ⁅Vn β, Vn α'⁆ := Subgroup.commutator_mem_commutator hv hyV
      exact C.R_le_Vn_beta this
  ·
    intro hcen
    apply hi
    have hZγ := (C.Zv_sup_eq_and_inf_eq_bot hvγ hδγ hα' (by
      intro h
      have := P.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
      rw [P.p_b] at this
      have h' : dist P.δ α' = 0 := by rw [h, CosetGeom.dist_self]
      have : dist (P.p (bMin H M - 2)) α' = 2 := by omega
      exact absurd (h'.symm.trans this) (by decide))).1
    have hcZ : Wnn β ≤ Subgroup.centralizer (Zv P.γ : Set G) := by
      rw [← hZγ, Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [← Subgroup.le_centralizer_iff]
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact ((Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hvδ hz).2) w (hWδ hw)).symm
      · rw [← Subgroup.le_centralizer_iff]
        exact hcen
    have hQ : Wnn β ≤ Qv P.γ := by
      rw [← centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hvγ)]
      exact le_inf h7 hcZ
    exact hQ.trans hQγα

theorem Wnn_le_centralizer_self (hb7 : 7 ≤ bMin H M) :
    Wnn β ≤ Subgroup.centralizer (Wnn β : Set G) := by
  have hbeta := C.vtype_beta
  have key : ∀ ν ∈ nbrs β, ∀ ρ ∈ nbrs ν, ∀ ν' ∈ nbrs β, ∀ ρ' ∈ nbrs ν',
      Vn ρ ≤ Subgroup.centralizer (Vn ρ' : Set G) := by
    intro ν hν ρ hρ ν' hν' ρ' hρ'
    have hvν' := vtype_true_of_mem_nbrs_false hν' hbeta
    have hvρ' := vtype_false_of_mem_nbrs_true hρ' hvν'
    refine C.Vn_le_centralizer_Vn hvρ' ?_
    have h1 := dist_le_dist_nbr hρ β
    have h2 := dist_le_dist_nbr hρ' β
    rw [dist_eq_one_iff_adj.mpr hν] at h1
    rw [dist_eq_one_iff_adj.mpr hν'] at h2
    have h3 := dist_triangle C.hA.amalgam.gen ρ β ρ'
    rw [CosetGeom.dist_comm ρ β] at h3
    omega
  refine iSup₂_le fun ν hν => iSup₂_le fun ρ hρ => ?_
  rw [Subgroup.le_centralizer_iff]
  exact iSup₂_le fun ν' hν' => iSup₂_le fun ρ' hρ' => key ν' hν' ρ' hρ' ν hν ρ hρ

theorem bMin_eq_five (h4 : Claim4Spec H M S) (h5 : Claim5Spec H M S) (P : CritPath α β α')
    (h7 : Wnn β ≤ stab P.γ) : bMin H M = 5 := by
  obtain ⟨-, hZW, hnc⟩ := C.e1 h4 h5 P h7
  by_contra hne
  have hb7 : 7 ≤ bMin H M := by
    obtain ⟨k, hk⟩ := C.hodd
    have := C.hb5
    omega
  apply hnc
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_self hb7 hw) z (hZW hz))

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
