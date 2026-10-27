module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenC

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def FactH6 (G : Type) [Group G] : Prop :=
  ∀ {X Q : Subgroup G}, IsPGroup 2 Q → Q ≤ X → X ≤ Subgroup.normalizer (Q : Set G) →
    ⁅⁅Q, oTwoRes X⁆, oTwoRes X⁆ = ⁅Q, oTwoRes X⁆

@[expose] def StarSpec (H M S : Subgroup G) : Prop :=
  ∀ {α β α' : Geo H M}, Ctx H M S α β α' → ∀ {δ μ : Geo H M}, vtype δ = false → μ ∈ nbrs δ →
    ¬ ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv μ

omit [Finite G] in
theorem conj_mem_of_sup {A B X : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ X)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ X) : ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ X := by
  intro x hx
  have hle : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩; exact hA a ha
    · rintro _ ⟨b, hb, rfl⟩; exact hB b hb
  exact hle ⟨x, hx, rfl⟩

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem comm_Qstar_R_mem_Zv (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (hH7 : FactH7) (hH6 : FactH6 G) (P : CritPath α β α')
    (hW : ¬ Wnn β ≤ stab P.γ) :
    ∀ q ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆, ∀ r ∈ ⁅Vn β, Vn α'⁆,
      q * r * q⁻¹ * r⁻¹ ∈ Zv P.δ := by
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hCv := C.comm_Qstar_R_mem_Cv h4 hH8 h6 hI8 hH7 P hW
  have hcommL := C.comm_oTwoRes_R h4 hH8 h6 P hW
  have hQsle := C.Qstar_le P.δ
  have hUab := C.isElemAbelian_RV P
  have hUn := C.stab_le_normalizer_RV h4 hH8 h6 P hW
  have hZn : stab P.δ ≤ Subgroup.normalizer (Zv P.δ : Set G) := stab_le_normalizer_Zv C.hA _
  have hQs_s : ∀ q ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆, q ∈ stab P.δ := fun q hq =>
    pCoreOf_le 2 _ (hQsle hq).1
  have hQsn := C.stab_le_normalizer_Qstar P.δ
  intro q₀ hq₀ r hr
  let K : Subgroup G :=
    { carrier := {q | q ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ ∧ q * r * q⁻¹ * r⁻¹ ∈ Zv P.δ}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : a * b * r * (a * b)⁻¹ * r⁻¹ =
            (a * (b * r * b⁻¹ * r⁻¹) * a⁻¹) * (a * r * a⁻¹ * r⁻¹) := by group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hZn (hQs_s a ha)) _).mp hb') ha'
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ = a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hZn (hQs_s _ (inv_mem ha))) _).mp (inv_mem ha') }
  have hKmem : ∀ q, q ∈ K ↔ q ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ ∧ q * r * q⁻¹ * r⁻¹ ∈ Zv P.δ :=
    fun _ => Iff.rfl
  have hle : ⁅⁅Qv P.δ, oTwoRes (stab P.δ)⁆, oTwoRes (stab P.δ)⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    have hls : l ∈ stab P.δ := oTwoRes_le _ hl
    have hm : l * q⁻¹ * l⁻¹ ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hQsn hls) _).mp (inv_mem hq)
    refine (hKmem _).mpr ⟨?_, ?_⟩
    · have e : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]; exact mul_mem hq hm
    set v := l⁻¹ * r * l⁻¹⁻¹ * r⁻¹ with hv
    have hvV : v ∈ Vn P.δ := hcommL l⁻¹ (inv_mem hl) r hr
    have hvr : v * r = l⁻¹ * r * l := by rw [hv]; group
    have hqi : q⁻¹ ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ := inv_mem hq
    have hUc : ∀ x ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ, ∀ y ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ, x * y = y * x :=
      fun x hx y hy => isElemAbelian_comm hUab hx hy
    have hqr : q⁻¹ * r * q⁻¹⁻¹ ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ :=
      (Subgroup.mem_normalizer_iff.mp (hUn (hQs_s _ hqi)) r).mp (Subgroup.mem_sup_left hr)
    have hkey := conj_comm_mul hUc (Subgroup.mem_sup_right hvV) (Subgroup.mem_sup_left hr) hqr
    set a := q⁻¹ * v * q⁻¹⁻¹ * v⁻¹ with ha
    set c := q⁻¹ * r * q⁻¹⁻¹ * r⁻¹ with hc
    have haZ : a ∈ Zv P.δ := by
      rw [← C.comm_Vn_Qv_eq hvδ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (hQsle hqi).1 hvV
    have hcC : c ∈ F53B3.Cv P.δ := hCv _ hqi r hr
    have hacC : a * c ∈ F53B3.Cv P.δ := mul_mem (C.Zv_le_Cv hvδ haZ) hcC
    have hlac : l * (a * c) * l⁻¹ = a * c := by
      have := (Subgroup.mem_centralizer_iff.mp hacC.2) l hl
      rw [this]; group
    have hacen : a ∈ Subgroup.centralizer (stab P.δ : Set G) := (C.Zv_le_center hvδ haZ).2
    have haq : q * a = a * q := Subgroup.mem_centralizer_iff.mp hacen q (hQs_s q hq)
    have e1 : ⁅q, l⁆ * r * ⁅q, l⁆⁻¹ * r⁻¹ =
        q * (l * (q⁻¹ * (l⁻¹ * r * l) * q⁻¹⁻¹ * (l⁻¹ * r * l)⁻¹) * l⁻¹) * q⁻¹ *
          (q * r * q⁻¹ * r⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1, ← hvr, hkey, hlac]
    have e2 : q * (a * c) * q⁻¹ * (q * r * q⁻¹ * r⁻¹) = (q * a * q⁻¹) *
        (q * c * q⁻¹ * (q * r * q⁻¹ * r⁻¹)) := by group
    have e3 : q * c * q⁻¹ * (q * r * q⁻¹ * r⁻¹) = 1 := by rw [hc]; group
    rw [e2, e3, mul_one, haq, mul_inv_cancel_right]
    exact haZ
  have hQsK : ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ ≤ K := by
    have h := hH6 (X := stab P.δ) (Q := Qv P.δ) (pCoreOf_isPGroup 2 (stab P.δ)) (pCoreOf_le 2 _)
      (le_normalizer_pCoreOf 2 _)
    rw [← h]
    exact hle
  exact ((hKmem q₀).mp (hQsK hq₀)).2

theorem relIndex_edge_three {ν μ : Geo H M} (hν : vtype ν = true) (hμ : μ ∈ nbrs ν) :
    (stab ν ⊓ stab μ).relIndex (stab ν) = 3 := by
  have h1 := relIndex_Qv_inf_mul C.hA hμ
  rw [relIndex_Qv_inf_true C.hA hμ hν] at h1
  obtain ⟨φ⟩ := quot_stab_three C.hA hν
  have h6 : Nat.card (OTwoQuot (stab ν)) = 6 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  omega

theorem R_le_Vn_of_not_le (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (hH7 : FactH7) (hH6 : FactH6 G) (hstar : StarSpec H M S)
    (P : CritPath α β α') (hW : ¬ Wnn β ≤ stab P.γ) : ⁅Vn β, Vn α'⁆ ≤ Vn P.δ := by
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hvγ := C.vtype_P_γ P
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hδγ : P.δ ∈ nbrs P.γ := mem_nbrs_comm hγ
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  have hZD := C.comm_Qstar_R_mem_Zv h4 hH8 h6 hI8 hH7 hH6 P hW
  have hQsle := C.Qstar_le P.δ
  set T := ⁅Vn β, Vn α'⁆ ⊔ Zv P.γ with hT
  have hZδγ : Zv P.δ ≤ Zv P.γ := C.Zv_le_Zv_of_mem_nbrs hvγ hδγ
  have hZα'γ : Zv α' ≤ Zv P.γ := C.Zv_le_Zv_of_mem_nbrs hvγ hα'
  have hQsT : ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ ≤ Subgroup.normalizer (T : Set G) := by
    refine X1512.le_normalizer_of_forall fun q hq x hx => ?_
    have hqδ : q ∈ Qv P.δ := (hQsle hq).1
    have hqγ : q ∈ stab P.γ := Qv_le_stab_of_mem_nbrs C.hA hγ hqδ
    refine conj_mem_of_sup (fun r hr => ?_) (fun z hz => ?_) x hx
    · have e : q * r * q⁻¹ = (q * r * q⁻¹ * r⁻¹) * r := by group
      rw [e]
      exact T.mul_mem (Subgroup.mem_sup_right (hZδγ (hZD q hq r hr))) (Subgroup.mem_sup_left hr)
    · exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA _ hqγ) z).mp hz)
  have hET : stab α' ⊓ stab P.γ ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    have h1 := h6 C (mem_nbrs_comm hα') (C.Vn_beta_le_Qv_P_γ P) hg
    have h2 := stab_le_normalizer_Zv C.hA P.γ hg.2
    have h3 := mem_normalizer_sup' h1 h2
    have e : ⁅Vn β, Vn α'⁆ ⊔ Zv α' ⊔ Zv P.γ = T := by
      rw [hT, sup_assoc, sup_eq_right.mpr hZα'γ]
    rwa [e] at h3
  have hQδT : Qv P.δ ≤ Subgroup.normalizer (T : Set G) := by
    have h2 : (Qv P.γ ⊓ Qv P.δ).relIndex (Qv P.δ) = 2 := by
      rw [Subgroup.inf_relIndex_right]; exact C.relIndex_Qv_Qv_eq_two hvδ hγ
    set J := ⁅Qv P.δ, oTwoRes (stab P.δ)⁆ ⊔ (Qv P.γ ⊓ Qv P.δ) with hJ
    have hNJ : Qv P.γ ⊓ Qv P.δ ≤ J := le_sup_right
    have hJQ : J ≤ Qv P.δ := sup_le (fun q hq => (hQsle hq).1) inf_le_right
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hNJ hJQ
    rw [h2] at hmul
    have hQJ : Qv P.δ ≤ J := by
      by_contra hne
      have h1 : J.relIndex (Qv P.δ) ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
      have h0 : (Qv P.γ ⊓ Qv P.δ).relIndex J = 1 := by
        rcases Nat.lt_or_ge ((Qv P.γ ⊓ Qv P.δ).relIndex J) 2 with h | h
        · have := relIndex_ne_zero_of_finite (Qv P.γ ⊓ Qv P.δ) J; omega
        · have h3 : 2 ≤ J.relIndex (Qv P.δ) := by
            have := relIndex_ne_zero_of_finite J (Qv P.δ); omega
          nlinarith
      have hJN := Subgroup.relIndex_eq_one.mp h0
      exact hstar C hvδ hγ ((le_sup_left.trans hJN).trans inf_le_left)
    refine hQJ.trans (sup_le hQsT ?_)
    intro q hq
    exact hET ⟨Qv_le_stab_of_mem_nbrs C.hA hα' hq.1, pCoreOf_le 2 _ hq.1⟩
  have hGT : stab P.γ ≤ Subgroup.normalizer (T : Set G) := by
    set E := stab P.γ ⊓ stab α' with hE
    have h3 := C.relIndex_edge_three hvγ hα'
    set J := Qv P.δ ⊔ E with hJ
    have hEJ : E ≤ J := le_sup_right
    have hJs : J ≤ stab P.γ := sup_le (Qv_le_stab_of_mem_nbrs C.hA hγ) inf_le_left
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hEJ hJs
    rw [h3] at hmul
    have hsJ : stab P.γ ≤ J := by
      by_contra hne
      have h1 : J.relIndex (stab P.γ) ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
      have h0 : E.relIndex J = 1 := by
        have hdvd : E.relIndex J ∣ 3 := ⟨_, hmul.symm⟩
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact h
        · exfalso; rw [h] at hmul; omega
      have hJE := Subgroup.relIndex_eq_one.mp h0
      apply C.not_Qv_le_Qv hvγ hδγ
      intro q hq
      have hqE : q ∈ E := hJE (Subgroup.mem_sup_left hq)
      have hne' : P.δ ≠ α' := by
        intro h
        have := P.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
        rw [P.p_b] at this
        have h' : dist P.δ α' = 0 := by rw [h, CosetGeom.dist_self]
        have : dist (P.p (bMin H M - 2)) α' = 2 := by omega
        exact absurd (h'.symm.trans this) (by decide)
      exact mem_Qv_of_fixes_two_nbrs C.hA hvγ hδγ hα' hne' hqE.1
        (pCoreOf_le 2 _ hq) hqE.2
    refine hsJ.trans (sup_le hQδT ?_)
    intro g hg
    exact hET ⟨hg.2, hg.1⟩
  obtain ⟨g, hgs, hgα⟩ := stab_transitive_on_nbrs hα' hδγ
  have hTV : T ≤ Vn α' := sup_le C.R_le_Vn_alpha' (Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hα'))
  intro r hr
  have hrT : r ∈ T := Subgroup.mem_sup_left hr
  have h1 : (g : G)⁻¹ * r * (g : G) ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (hGT (Subgroup.inv_mem _ hgs)) r).mp hrT
    simpa using this
  have h2 : (g : G) * ((g : G)⁻¹ * r * (g : G)) * (g : G)⁻¹ ∈ conjSub (g : G) (Vn α') :=
    mul_mem_conjSub (hTV h1)
  rw [← Vn_smul, hgα] at h2
  simpa [mul_assoc] using h2

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
