module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2PcB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem K0_conj_mem (hf0 : Wp0 T d x) {p : G} (hp : p ∈ Cw T d x) {k : G} (hk : k ∈ K0 T d x) :
    p * k * p⁻¹ ∈ K0 T d x := by
  have hkC : k ∈ Cw T d x := ⟨oTwoUpper_le _ hk.1, hk.2⟩
  have := hf0.K0_normal.conj_mem ⟨k, hkC⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨p, hp⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem pCore_inf_K0 (h : Ctx T M g A t d x) (hf0 : Wp0 T d x) :
    pCoreOf 2 (Gw d x) ⊓ K0 T d x = ⊥ := by
  by_contra hne
  have hnorm := le_normalizer_pCoreOf 2 (Gw d x)
  refine z_not_mem_pCore_Gw h (hf0.K0_contains_z _ inf_le_right ⟨fun n hn k => ?_⟩ hne).1
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp (hnorm k.2.2) _).mp hn.1,
    (K0 T d x).mul_mem ((K0 T d x).mul_mem k.2 n.2) ((K0 T d x).inv_mem k.2)⟩

theorem pCore_le_Bw (h : Ctx T M g A t d x) (hf0 : Wp0 T d x) :
    pCoreOf 2 (Gw d x) ≤ Bw T d x := by
  intro p hp
  have hnorm := le_normalizer_pCoreOf 2 (Gw d x)
  have hpC : p ∈ Cw T d x := ⟨le_mcOf_self T (pCore_Gw_le_T h hp), pCoreOf_le 2 _ hp⟩
  refine ⟨hpC, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hcP : p * (k * p⁻¹ * k⁻¹) ∈ pCoreOf 2 (Gw d x) :=
    (pCoreOf 2 (Gw d x)).mul_mem hp
      ((Subgroup.mem_normalizer_iff.mp (hnorm hk.2) _).mp ((pCoreOf 2 (Gw d x)).inv_mem hp))
  have hcK : p * (k * p⁻¹ * k⁻¹) ∈ K0 T d x := by
    have := (K0 T d x).mul_mem (K0_conj_mem hf0 hpC hk) ((K0 T d x).inv_mem hk)
    rwa [show p * k * p⁻¹ * k⁻¹ = p * (k * p⁻¹ * k⁻¹) by group] at this
  have h1 : p * (k * p⁻¹ * k⁻¹) ∈ pCoreOf 2 (Gw d x) ⊓ K0 T d x := ⟨hcP, hcK⟩
  rw [pCore_inf_K0 h hf0, Subgroup.mem_bot] at h1
  have h2 : p * k * p⁻¹ * k⁻¹ = 1 := by
    calc p * k * p⁻¹ * k⁻¹ = p * (k * p⁻¹ * k⁻¹) := by group
      _ = 1 := h1
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm

end InspW2

end S143

end CFSG.Quasithin
