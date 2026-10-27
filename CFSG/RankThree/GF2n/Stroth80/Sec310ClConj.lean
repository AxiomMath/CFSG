module

public import CFSG.CGT.Timmesfeld75.WCBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem iSup_conj_reindex (M L X : Subgroup G) (t m₀ : G) (hm₀ : m₀ ∈ M) :
    (⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (conjSubgroup m₀ L)),
        conjSubgroup m (conjSubgroup m₀ X)) =
      ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m L), conjSubgroup m X := by
  apply le_antisymm
  · refine iSup_le fun m => iSup_le fun hm => iSup_le fun ht => ?_
    rw [conjSubgroup_conjSubgroup] at ht ⊢
    exact le_iSup_of_le (m * m₀) (le_iSup_of_le (M.mul_mem hm hm₀) (le_iSup_of_le ht le_rfl))
  · refine iSup_le fun m => iSup_le fun hm => iSup_le fun ht => ?_
    have hmm : m * m₀⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hm₀)
    have key : ∀ T : Subgroup G,
        conjSubgroup (m * m₀⁻¹) (conjSubgroup m₀ T) = conjSubgroup m T := by
      intro T
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    refine le_iSup_of_le (m * m₀⁻¹) (le_iSup_of_le hmm (le_iSup_of_le ?_ (key X).ge))
    rw [key L]
    exact ht

theorem rt_vt_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) :
    Rt M (LB M Q (conjSubgroup m B)) t = Rt M (LB M Q B) t ∧
      Vt M (LB M Q (conjSubgroup m B)) (conjSubgroup m B) Z t = Vt M (LB M Q B) B Z t := by
  rw [hc.LB_conj hm]
  exact ⟨iSup_conj_reindex M _ _ t m hm, by
    unfold Vt
    rw [iSup_conj_reindex M _ _ t m hm]⟩

theorem sec5Hyp_conj (hc : Ctx M Q Z B) {n : ℕ} {t m : G} (hm : m ∈ M) (hs : Sec5Hyp hc n t)
    (ht : t ∈ conjSubgroup m (LB M Q B)) : Sec5Hyp (hc.conj_of_mem hm) n t where
  width := hs.width
  n_gt := hs.n_gt
  noA2 := hc.noA2_conj hs.noA2 hm
  gen := hs.gen.conj_of_mem hm
  mem := by
    rw [hc.LB_conj hm]
    exact ht
  notQ := hs.notQ

section ImgJoin

variable {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem quadModel_img_iSup (M₀ : Tim79.QuadModel QF V K γ) {ι : Sort*} (S : ι → Subgroup G)
    (hS : ∀ i, S i ≤ QF) : M₀.img (⨆ i, S i) = ⨆ i, M₀.img (S i) := by
  apply le_antisymm
  · have hle : (⨆ i, S i) ≤ M₀.lift (⨆ i, M₀.img (S i)) := iSup_le fun i x hx =>
      (M₀.mem_lift).mpr ⟨hS i hx, le_iSup (fun i => M₀.img (S i)) i (M₀.pi_mem_img hx (hS i hx))⟩
    rintro _ ⟨x, hx, -, rfl⟩
    exact ((M₀.mem_lift).mp (hle hx)).2
  · exact iSup_le fun i => M₀.img_mono (le_iSup S i)

theorem quadModel_img_sup (M₀ : Tim79.QuadModel QF V K γ) {S T : Subgroup G} (hS : S ≤ QF)
    (hT : T ≤ QF) :
    M₀.img (S ⊔ T) = M₀.img S ⊔ M₀.img T := by
  rw [sup_eq_iSup, sup_eq_iSup, quadModel_img_iSup M₀ _ (Bool.forall_bool.mpr ⟨hT, hS⟩)]
  exact le_antisymm (iSup_le (Bool.forall_bool.mpr ⟨le_iSup_of_le false le_rfl,
    le_iSup_of_le true le_rfl⟩)) (iSup_le (Bool.forall_bool.mpr ⟨le_iSup_of_le false le_rfl,
    le_iSup_of_le true le_rfl⟩))

theorem quadModel_img_center_eq_bot (M₀ : Tim79.QuadModel QF V K γ) (hV : V ≤ QF) :
    M₀.img V = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨x, hx, hxQ, rfl⟩
  exact (AddSubgroup.mem_bot).mpr ((M₀.π_ker x hxQ).mpr hx)

end ImgJoin

theorem Ctx.img_Vt_eq (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) :
    M₀.img (Vt M (LB M Q B) B Z t) =
      ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)), M₀.img (conjSubgroup m B) := by
  unfold Vt
  have h1 : ∀ m : G, (⨆ (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)), conjSubgroup m B) ≤ Q :=
    fun m => iSup_le fun hm => iSup_le fun _ => (hc.conj_of_mem hm).le
  have h2 : ∀ (m : G) (_ : m ∈ M), (⨆ (_ : t ∈ conjSubgroup m (LB M Q B)),
      conjSubgroup m B) ≤ Q := fun m hm => iSup_le fun _ => (hc.conj_of_mem hm).le
  have hQ : (⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)), conjSubgroup m B) ≤ Q :=
    iSup_le h1
  rw [quadModel_img_sup M₀ hc.Z_le_Q hQ, quadModel_img_center_eq_bot M₀ hc.Z_le_Q, bot_sup_eq,
    quadModel_img_iSup M₀ _ h1]
  congr 1
  funext m
  rw [quadModel_img_iSup M₀ _ (fun hm => h2 m hm)]
  congr 1
  funext hm
  rw [quadModel_img_iSup M₀ _ (fun ht => (hc.conj_of_mem hm).le)]

end CFSG.RankThree.GF2n.Stroth80
