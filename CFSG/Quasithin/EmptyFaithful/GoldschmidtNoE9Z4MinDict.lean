module

public import CFSG.Quasithin.EmptyFaithful.S14612GB0
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits
  CFSG.Quasithin.C1Pack CFSG.Quasithin.S1417
open scoped commutatorElement

section Dict

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem exists_valK_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hU : conjClosure (VZ T M) H = uK T M H ⊔ quasithinOmegaOneCenter T)
    (hK : commV (resBeta (rhoH h)).range = ⊤) {u : G} (hu : u ∈ conjClosure (VZ T M) H) :
    ∃ k : ↥(kOf (rhoH h)), valK h k =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, U_le_normalizer h hu⟩ := by
  have h1 := secMk_mem_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (X := conjClosure (VZ T M) H)
    (x := ⟨u, U_le_normalizer h hu⟩) hu
  have h2 := tildeOf_uK_sup_Z_eq h hsplit
  have h3 : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) ⟨u, U_le_normalizer h hu⟩ ∈
        (commV (resBeta (rhoH h)).range).map (valK h) := by
    rw [← h2, ← hU]
    exact h1
  rw [hK] at h3
  obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp h3
  exact ⟨k, hk⟩

theorem exists_cls
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hU : conjClosure (VZ T M) H = uK T M H ⊔ quasithinOmegaOneCenter T)
    (hK : commV (resBeta (rhoH h)).range = ⊤) :
    ∃ cls : G → ↥(kOf (rhoH h)), ∀ (u : G) (hu : u ∈ conjClosure (VZ T M) H),
      valK h (cls u) = secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, U_le_normalizer h hu⟩ := by
  classical
  refine ⟨fun u => if hu : u ∈ conjClosure (VZ T M) H then
    Classical.choose (exists_valK_eq h hsplit hU hK hu) else 1, fun u hu => ?_⟩
  simp only [hu, ↓reduceDIte]
  exact Classical.choose_spec (exists_valK_eq h hsplit hU hK hu)

theorem clsData_of
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hU : conjClosure (VZ T M) H = uK T M H ⊔ quasithinOmegaOneCenter T)
    (hK : commV (resBeta (rhoH h)).range = ⊤) {z : G}
    (P : NoE9Z4MinGrp.PairCtx (pCoreOf 2 H) (conjClosure (VZ T M) H)
      (quasithinOmegaOneCenter T) H z)
    {cls : G → ↥(kOf (rhoH h))}
    (hcls : ∀ (u : G) (hu : u ∈ conjClosure (VZ T M) H),
      valK h (cls u) = secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, U_le_normalizer h hu⟩) :
    NoE9Z4MinGrp.ClsData P (resBeta (rhoH h)) cls where
  mul u hu u' hu' := by
    apply valK_injective h
    rw [map_mul, hcls u hu, hcls u' hu', hcls (u * u') ((conjClosure (VZ T M) H).mul_mem hu hu'),
      ← map_mul]
    rfl
  eq_one u hu := by
    constructor
    · intro h1
      have h2 : valK h (cls u) = 1 := by rw [h1, map_one]
      rw [hcls u hu] at h2
      exact secMk_eq_one_iff.mp h2
    · intro h1
      apply valK_injective h
      rw [hcls u hu, map_one]
      exact secMk_eq_one_iff.mpr h1
  conj x u hu := by
    have hxu : (x : G) * u * (x : G)⁻¹ ∈ conjClosure (VZ T M) H :=
      P.normU (x : G) x.2 u hu
    apply valK_injective h
    rw [hcls _ hxu, valK_resBeta_apply, hcls u hu, ← map_inv, ← map_mul, ← map_mul]
    rfl
  surj k := by
    have h1 : valK h k ∈ tildeOf (quasithinOmegaOneCenter T)
        (uK T M H ⊔ quasithinOmegaOneCenter T) := by
      rw [tildeOf_uK_sup_Z_eq h hsplit, hK, Subgroup.map_top]
      exact ⟨k, rfl⟩
    obtain ⟨x, hx, hxk⟩ := mem_secImg.mp h1
    have hxU : (x : G) ∈ conjClosure (VZ T M) H := by rw [hU]; exact hx
    refine ⟨x, hxU, valK_injective h ?_⟩
    rw [hcls (x : G) hxU, hxk]

end Dict

end CFSG.Quasithin
