module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Prelim

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subsingleton_mulAut_bot : Subsingleton (MulAut (↥(⊥ : Subgroup G))) :=
  ⟨fun _ _ => MulEquiv.ext fun _ => Subsingleton.elim _ _⟩

theorem qInt_eq_top_of_eq_bot (X : Subgroup G) (hV : IsElemAbelian 2 (⊥ : Subgroup G)) :
    qInt X ⊥ hV = ⊤ := by
  let _ : CommGroup ↥(⊥ : Subgroup G) := commGroupOfElemAbelian hV
  have : Subsingleton (MulAut (↥(⊥ : Subgroup G))) := subsingleton_mulAut_bot
  show kq (autOn X ⊥) 2 = ⊤
  rw [kq_eq_top_iff]
  rintro ⟨A, hA, -⟩
  exact hA.ne_bot (Subsingleton.elim _ _)

end Prelim

section Core

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem not_exists_normal_of_isUniqueM_of_not_le {M₀ H M : Subgroup G} (hMu : IsUniqueM M₀ M)
    (hH : ¬ H ≤ M) :
    ¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  rintro ⟨R₀, hR₀, hle, hnorm⟩
  have hR₀sup : R₀ ≤ M₀ ⊔ H := (hle.trans (pCoreOf_le 2 _)).trans le_sup_left
  have h1 : R₀ ≤ pCoreOf 2 (M₀ ⊔ H) :=
    le_pCoreOf_of_le_normalizer 2 hR₀sup hnorm ((pCoreOf_isPGroup 2 _).to_le hle)
  rw [pCoreOf_sup_eq_bot_of_isUniqueM hMu hH, le_bot_iff] at h1
  exact hR₀ h1

theorem Hyp319.V_ne_bot (h : Hyp319 T M M₀ H V) : V ≠ ⊥ := by
  intro hV0
  have h2 := h.q_eq
  subst hV0
  rw [qInt_eq_top_of_eq_bot] at h2
  exact absurd h2 (by simp)

theorem Hyp319.not_qInt_le_one (h : Hyp319 T M M₀ H V) : ¬ qInt M₀ V h.reduced.2.2.1 ≤ 1 := by
  rw [h.q_eq]
  norm_num

theorem Hyp319.not_exists_normal (h : Hyp319 T M M₀ H V) :
    ¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) :=
  not_exists_normal_of_isUniqueM_of_not_le h.unique h.hStar.2.1

theorem Hyp319.d11Hyp (hT : quasithinIsSylowTwo T) (h : Hyp319 T M M₀ H V) :
    D11Hyp M₀ H T V (H ⊓ M) :=
  h.toHyp315Base.d11Hyp hT h.V_ne_bot (noNormal_of_not_exists h.not_exists_normal)

end Core

section Parts

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

omit [Finite G] in
theorem secRank_self (N : Subgroup G) : secRank N N = 0 := by
  unfold secRank rkIdx
  rw [Subgroup.subgroupOf_self, Subgroup.index_top]
  simp

theorem secRank_anti {N L₁ L₂ : Subgroup G} (h : L₁ ≤ L₂) : secRank N L₂ ≤ secRank N L₁ :=
  padicValNat_two_le_of_dvd (Subgroup.index_ne_zero_of_finite (H := L₁.subgroupOf N))
    (Subgroup.relIndex_dvd_of_le_left N h)

theorem one_le_secRank_of_not_le {A B : Subgroup G} (hA : IsPGroup 2 A) (hAB : ¬ A ≤ B) :
    1 ≤ secRank A B := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  have h1 : B.relIndex A ∣ 2 ^ n := by
    rw [← hn, ← Subgroup.relIndex_mul_card B A]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hAB (Subgroup.relIndex_eq_one.mp (by simpa using hj))
  unfold secRank rkIdx
  show 1 ≤ padicValNat 2 (B.relIndex A)
  rw [hj, padicValNat.prime_pow]
  omega

omit [Finite G] in
theorem conjSubgroup_le_conjClosure {g : G} (hg : g ∈ H) : conjSubgroup V g ≤ conjClosure V H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := mem_conjClosure (Z := V) (H := H) (H.inv_mem hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h1

omit [Finite G] in
theorem exists_conj_not_comm {B : Subgroup G} (hB : ¬ B ≤ Subgroup.centralizer (conjClosure V H : Set G)) :
    ∃ g ∈ H, ⁅conjSubgroup V g, B⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply hB
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine conjClosure_le fun g hg z hz => ?_
  have h1 : ⁅conjSubgroup V g⁻¹, B⁆ = ⊥ := hall g⁻¹ (H.inv_mem hg)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  apply h1
  rw [mem_conjSubgroup_iff]
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rw [e]
  exact hz

end Parts

end CFSG.Quasithin
