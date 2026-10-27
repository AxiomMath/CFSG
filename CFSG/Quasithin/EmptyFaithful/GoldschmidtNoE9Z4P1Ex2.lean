module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Ex1
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Ex2

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem exists_mem_uHi_of_mem_commV
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQ : Q ≤ (resBeta (rhoH h)).range)
    {k : ↥(kOf (rhoH h))} (hk : k ∈ commV Q) :
    ∃ u : G, ∃ hu : u ∈ conjClosure (VZ T M) H,
      u ∈ uHi T M H (HLb (resBeta (rhoH h)) Q) ∧ clsU h hu = (k : UMod h) := by
  have hw : (k : UMod h) ∈ Wsub h (uHi T M H (HLb (resBeta (rhoH h)) Q)) := by
    rw [Wsub_uHi_HLb h hsplit hQ]
    exact ⟨k, hk, rfl⟩
  exact exists_clsU_of_mem_Wsub h (uHi_le_conjClosure (HLb_le Q)) hw

theorem exists_mem_commV_of_mem_uHi
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQ : Q ≤ (resBeta (rhoH h)).range) {u : G}
    (hu : u ∈ conjClosure (VZ T M) H) (huQ : u ∈ uHi T M H (HLb (resBeta (rhoH h)) Q)) :
    ∃ k ∈ commV Q, (k : UMod h) = clsU h hu := by
  have hw := clsU_mem_Wsub h hu huQ
  rw [Wsub_uHi_HLb h hsplit hQ] at hw
  obtain ⟨k, hk, hkw⟩ := hw
  exact ⟨k, hk, hkw⟩

theorem uHi_inf_uHi
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {P₁ P₂ : Subgroup (MulAut ↥(kOf (rhoH h)))} (hP₁ : P₁ ≤ (resBeta (rhoH h)).range)
    (hP₂ : P₂ ≤ (resBeta (rhoH h)).range) (hdisj : Disjoint (commV P₁) (commV P₂)) :
    uHi T M H (HLb (resBeta (rhoH h)) P₁) ⊓ uHi T M H (HLb (resBeta (rhoH h)) P₂) =
      quasithinOmegaOneCenter T := by
  refine le_antisymm (fun u ⟨hu1, hu2⟩ => ?_) (le_inf (Z_le_uHi _ _ _ _) (Z_le_uHi _ _ _ _))
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu1
  obtain ⟨k₁, hk₁, hkw₁⟩ := exists_mem_commV_of_mem_uHi h hsplit hP₁ hUu hu1
  obtain ⟨k₂, hk₂, hkw₂⟩ := exists_mem_commV_of_mem_uHi h hsplit hP₂ hUu hu2
  have hkk : k₁ = k₂ := Subtype.ext (hkw₁.trans hkw₂.symm)
  have hk1 : k₁ = 1 := by
    have : k₁ ∈ commV P₁ ⊓ commV P₂ := ⟨hk₁, hkk ▸ hk₂⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at this
    exact this
  exact (clsU_eq_one_iff h hUu).mp (by rw [← hkw₁, hk1]; rfl)

theorem comm_uHi_le
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Q Q' : Subgroup (MulAut ↥(kOf (rhoH h)))} (hQ : Q ≤ (resBeta (rhoH h)).range)
    (hfix : commV Q ≤ fixV Q') :
    ⁅uHi T M H (HLb (resBeta (rhoH h)) Q), HLb (resBeta (rhoH h)) Q'⁆ ≤
      quasithinOmegaOneCenter T := by
  rw [Subgroup.commutator_le]
  intro u hu r hr
  have hUu : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure (HLb_le _) hu
  have hrH : r ∈ H := HLb_le _ hr
  obtain ⟨k, hk, hkw⟩ := exists_mem_commV_of_mem_uHi h hsplit hQ hUu hu
  have hβr : resBeta (rhoH h) ⟨r, hrH⟩ ∈ Q' := (mem_HLb_iff hrH).mp hr
  have hfk : resBeta (rhoH h) ⟨r, hrH⟩ k = k := hfix hk _ hβr
  have hρ : rhoH h ⟨r, hrH⟩ (clsU h hUu) = clsU h hUu := by
    rw [← hkw]
    exact (resBeta_apply _ _ _).symm.trans (congrArg Subtype.val hfk)
  have h1 := (rhoH_clsU_eq_iff h ⟨r, hrH⟩ hUu).mp hρ
  have e : ⁅u, r⁆ = (r * u * r⁻¹ * u⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (quasithinOmegaOneCenter T).inv_mem h1

theorem uHi_sup_uHi
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {P₁ P₂ : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hP₁ : P₁ ≤ (resBeta (rhoH h)).range) (hP₂ : P₂ ≤ (resBeta (rhoH h)).range)
    (hcsup : commV P₁ ⊔ commV P₂ = ⊤) :
    uHi T M H (HLb (resBeta (rhoH h)) P₁) ⊔ uHi T M H (HLb (resBeta (rhoH h)) P₂) =
      uK T M H ⊔ quasithinOmegaOneCenter T := by
  refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ (le_sup_of_le_left (Z_le_uHi _ _ _ _)))
  · exact sup_le_sup_right (Subgroup.commutator_mono le_rfl (HLb_le _)) _
  · exact sup_le_sup_right (Subgroup.commutator_mono le_rfl (HLb_le _)) _
  · rw [uK, Subgroup.commutator_le]
    intro u hu h' hh'
    have key : h' * u * h'⁻¹ * u⁻¹ ∈ uHi T M H (HLb (resBeta (rhoH h)) P₁) ⊔
        uHi T M H (HLb (resBeta (rhoH h)) P₂) := by
      obtain ⟨a, ha⟩ := rho_mul_inv_eq h hsplit ⟨h', hh'⟩ (clsU h hu)
      have hb : (resBeta (rhoH h) ⟨h', hh'⟩ a * a⁻¹ : ↥(kOf (rhoH h))) ∈
          commV P₁ ⊔ commV P₂ := by
        rw [hcsup]
        exact Subgroup.mem_top _
      obtain ⟨b₁, hb₁, b₂, hb₂, hbb⟩ := Subgroup.mem_sup.mp hb
      obtain ⟨u₁, hu₁U, hu₁, hc₁⟩ := exists_mem_uHi_of_mem_commV h hsplit hP₁ hb₁
      obtain ⟨u₂, hu₂U, hu₂, hc₂⟩ := exists_mem_uHi_of_mem_commV h hsplit hP₂ hb₂
      have hcU : h' * u * h'⁻¹ * u⁻¹ ∈ conjClosure (VZ T M) H :=
        (conjClosure (VZ T M) H).mul_mem (conj_mem_UH hh' hu)
          ((conjClosure (VZ T M) H).inv_mem hu)
      have hprod : u₁ * u₂ ∈ conjClosure (VZ T M) H := (conjClosure (VZ T M) H).mul_mem hu₁U hu₂U
      have heq : clsU h hcU = clsU h hprod := by
        rw [← clsU_mul h hu₁U hu₂U, hc₁, hc₂, ← Subgroup.coe_mul, hbb, ← ha, rhoH_clsU, clsU_inv,
          clsU_mul h (conj_mem_UH hh' hu) ((conjClosure (VZ T M) H).inv_mem hu)]
      have hz := (clsU_eq_iff h hcU hprod).mp heq
      have e : h' * u * h'⁻¹ * u⁻¹ =
          (u₁ * u₂) * ((h' * u * h'⁻¹ * u⁻¹)⁻¹ * (u₁ * u₂))⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem_sup hu₁ hu₂)
        (Subgroup.mem_sup_left ((Z_le_uHi T M H _) ((quasithinOmegaOneCenter T).inv_mem hz)))
    have e : ⁅u, h'⁆ = (h' * u * h'⁻¹ * u⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ key

theorem exists_isE9Dat (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    ∃ (R₁ R₂ : Subgroup G) (s : G), IsE9Dat T M H PQ R₁ R₂ s := by
  classical
  have hcls : ClassAutShapeStmt := classAutShapeStmt
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  obtain ⟨hsplit, -, -⟩ := shape_splitting h35 S hred h98
  have hstr := e9z4Str_of_shape hcls h35 S hred hshape h98
  obtain ⟨P₁, P₂, hp⟩ := hstr.exists_planePair
  have hrk := hstr.rk_commV_plane hp
  have hinfP := hstr.plane_inf_eq_bot hp
  obtain ⟨hP₁, hP₂, hc₁, hc₂, hsupP, hdisj, hcsup, hf₁, hf₂, σ, hσ, hσP⟩ := hp
  have hp' : PlanePair ((T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)))
      ((PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) P₁ P₂ :=
    ⟨hP₁, hP₂, hc₁, hc₂, hsupP, hdisj, hcsup, hf₁, hf₂, σ, hσ, hσP⟩
  have hr₁ : P₁ ≤ (resBeta (rhoH h98.toHypF91)).range := hP₁.trans (Subgroup.map_le_range _ _)
  have hr₂ : P₂ ≤ (resBeta (rhoH h98.toHypF91)).range := hP₂.trans (Subgroup.map_le_range _ _)
  obtain ⟨s', hs'T, hs'σ⟩ := Subgroup.mem_map.mp hσ
  refine ⟨HLb (resBeta (rhoH h98.toHypF91)) P₁, HLb (resBeta (rhoH h98.toHypF91)) P₂, (s' : G),
    isPlaneSub_HLb S hred h98 hsplit hP₁ hc₁ hrk.1, isPlaneSub_HLb S hred h98 hsplit hP₂ hc₂ hrk.2,
    ?_, ?_, Subgroup.mem_subgroupOf.mp hs'T, ?_, indexT_HLb hred h98 rfl hp' hr₁ hstr,
    uHi_inf_uHi h98.toHypF91 hsplit hr₁ hr₂ hdisj,
    uHi_sup_uHi h98.toHypF91 hsplit hr₁ hr₂ hcsup,
    comm_uHi_le h98.toHypF91 hsplit hr₁ hf₁, comm_uHi_le h98.toHypF91 hsplit hr₂ hf₂⟩
  · rw [← HLb_sup hr₁ hr₂, hsupP]
    exact HLb_map_eq h98.toHypF91 hsplit hred.lt.le hred.le
  · rw [← HLb_inf, hinfP, HLb_bot, ker_resBeta_eq h98.toHypF91 hsplit,
      Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (pCoreOf_le 2 H)
  · refine conjSub_HLb s'.2 (fun x => ?_)
    rw [← hσP, mem_conjBy_iff]
    have e : resBeta (rhoH h98.toHypF91) ⟨(s' : G), s'.2⟩ = σ := hs'σ
    rw [e]

end Ex2

end CFSG.Quasithin
