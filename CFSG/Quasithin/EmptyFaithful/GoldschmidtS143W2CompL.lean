module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompAbs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section E0

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem E0_le_Tw (h : Ctx T M g A t d x) :
    rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G) ≤ Tw T d x :=
  inf_le_inf_right _ (rOf_le_T_of_hyp h.c.h1281) |>.trans le_rfl

theorem Ctx.x_mem_iTwo (h : Ctx T M g A t d x) : x ∈ iTwo T M := by
  rw [iTwo_eq h.c.h1281 h.c.nonab]; exact Subgroup.mem_sup_left h.hx

theorem Ctx.x_mem_normalizer_R (h : Ctx T M g A t d x) :
    x ∈ Subgroup.normalizer (rOf T M : Set G) :=
  le_normalizer_pCoreOf 2 (iTwo T M) h.x_mem_iTwo

theorem x_mem_normalizer_E0 (h : Ctx T M g A t d x) :
    x ∈ Subgroup.normalizer ((rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G) :
      Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  have h1 := (Subgroup.mem_normalizer_iff.mp h.x_mem_normalizer_R) e
  have h2 : e ∈ Gw d x ↔ x * e * x⁻¹ ∈ Gw d x := by
    constructor
    · intro he
      exact (Gw d x).mul_mem ((Gw d x).mul_mem h.x_mem_Gw he) ((Gw d x).inv_mem h.x_mem_Gw)
    · intro he
      have := (Gw d x).mul_mem ((Gw d x).mul_mem ((Gw d x).inv_mem h.x_mem_Gw) he) h.x_mem_Gw
      simpa [mul_assoc] using this
  exact ⟨fun he => ⟨h1.mp he.1, h2.mp he.2⟩, fun he => ⟨h1.mpr he.1, h2.mpr he.2⟩⟩

theorem E0_fpf (h : Ctx T M g A t d x) {e : G}
    (he : e ∈ rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) (hfix : x * e * x⁻¹ = e) :
    e = 1 :=
  h.c18.a.r_fpf x h.x_mem_iTwo h.hx3 e he.1 hfix

theorem x_fixes_P (h : Ctx T M g A t d x) (hf : Wp1 T d x) :
    ∀ p ∈ pCoreOf 2 (Gw d x), x * p * x⁻¹ = p := by
  have hP : Nat.card ↥(pCoreOf 2 (Gw d x)) ≤ 4 := hf.card_P
  refine fix_of_odd_of_small hP (hf.w_mem_P (Subgroup.mem_zpowers _)) h.w_ne ?_ ?_ h.x_comm_w
  · rw [h.hx3]; decide
  · intro p hp
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (Gw d x) h.x_mem_Gw) p).mp hp
    exact this

theorem E0_inf_P (h : Ctx T M g A t d x) (hf : Wp1 T d x) :
    (rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) ⊓ pCoreOf 2 (Gw d x) = ⊥ := by
  rw [eq_bot_iff]
  rintro e ⟨he, heP⟩
  exact E0_fpf h he (x_fixes_P h hf e heP)

end E0

end InspW2

end S143

end CFSG.Quasithin
