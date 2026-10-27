module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFrag

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_conjClosure_of_mem_normalizer {V K : Subgroup G} {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer (conjClosure V K : Set G) := by
  have hS : t ∈ Subgroup.normalizer {x : G | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x} := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨h, hh, z, hz, rfl⟩ := hn
    exact ⟨t * h * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK h).1 hh,
      t * z * t⁻¹, (Subgroup.mem_normalizer_iff.mp htV z).1 hz, by group⟩
  exact Subgroup.normalizer_le_normalizer_closure _ hS

theorem Sit813.faithful {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    A ⊓ centralizer (uGrp V K : Set G) = ⊥ ∧
      ∀ a ∈ A, a ≠ 1 →
        uGrp V K ⊓ centralizer (A : Set G) = uGrp V K ⊓ centralizer ({a} : Set G) := by
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hTI := hyp.hyp7.2.2
  have hH0 : IsCalH0 V H := h.calH0
  have hH : IsCalH V H := hH0.1
  have hT := hyp.sylow
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := hyp.hyp7.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  obtain ⟨hAT, g, hAg, -⟩ := h.mem
  have hAH : A ≤ H := hAT.trans hTH.le
  have hc := h.concl813
  have hLH : L ≤ H := hc.comp.2.2.1
  have hKH : K ≤ H := hc.sub_L.trans hLH
  have hVO : V ≤ pCoreOf 2 H := hH0.2
  have hUO : uGrp V K ≤ pCoreOf 2 H := by
    unfold uGrp
    refine conjClosure_le fun k hk v hv => ?_
    have hnorm := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H) (hKH hk)
    exact (Subgroup.mem_normalizer_iff.mp hnorm v).1 (hVO hv)
  rcases eight_four_one hV hTI hVne hH0 hT g with ⟨-, hn⟩ | ⟨hb, -⟩
  · exfalso
    obtain ⟨x, hx, hxM⟩ := h.notLe
    have hAU : A ≤ conjSubgroup V g ⊓ H := le_inf hAg hAH
    exact hxM ((E3.conjSubgroup_mono_left x hAU).trans (hn x hx))
  · have hUt : conjSubgroup V g ⊓ pCoreOf 2 H = ⊥ := by
      refine eq_bot_iff.mpr fun u hu => ?_
      obtain ⟨huVg, huO⟩ := Subgroup.mem_inf.mp hu
      have hEO := eSub_le_omegaOneCenter hV hH hT
      have huC : u ∈ centralizer (eSub V H T : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (mem_centralizer_of_mem_omegaOneCenterOf (hEO hy) huO).symm
      have hmem : u ∈ (conjSubgroup V g ⊓ H) ⊓ centralizer (eSub V H T : Set G) :=
        Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_inf.mpr ⟨huVg, (CFSG.openPCoreOf_le 2 H) huO⟩, huC⟩
      rw [hb] at hmem
      exact hmem
    have hUV : uGrp V K ⊓ conjSubgroup V g = ⊥ := by
      refine eq_bot_iff.mpr fun u hu => ?_
      obtain ⟨huU, huVg⟩ := Subgroup.mem_inf.mp hu
      have hmem : u ∈ conjSubgroup V g ⊓ pCoreOf 2 H :=
        Subgroup.mem_inf.mpr ⟨huVg, hUO huU⟩
      rw [hUt] at hmem
      exact hmem
    have hAN : A ≤ normalizer (uGrp V K : Set G) := by
      intro y hy
      obtain ⟨k, hk, t, ht, hct⟩ := hc.a_le y hy
      have htV : t ∈ normalizer (V : Set G) := (hT.le ht.1).2
      have htK : t ∈ normalizer (K : Set G) := by
        refine Subgroup.mem_normalizer_fintype fun n hn => ?_
        have h1 : t * n * t⁻¹ * n⁻¹ ∈ cGrp H T := ht.2 n (hc.sub_L hn)
        have h2 : (t * n * t⁻¹ * n⁻¹) * n ∈ K := K.mul_mem (hc.ge_C h1) hn
        have h3 : t * n * t⁻¹ = (t * n * t⁻¹ * n⁻¹) * n := by group
        rw [h3]
        exact h2
      have htU : t ∈ normalizer (uGrp V K : Set G) :=
        mem_normalizer_conjClosure_of_mem_normalizer htV htK
      have hkU : k ∈ normalizer (uGrp V K : Set G) :=
        le_normalizer_conjClosure V K hk
      have hktU : k * t ∈ normalizer (uGrp V K : Set G) :=
        (Subgroup.normalizer (uGrp V K : Set G)).mul_mem hkU htU
      have hyU : (k * t)⁻¹ * y ∈ normalizer (uGrp V K : Set G) :=
        le_normalizer_conjClosure V K (hc.ge_C hct)
      have hy_eq : y = (k * t) * ((k * t)⁻¹ * y) := by group
      rw [hy_eq]
      exact (Subgroup.normalizer (uGrp V K : Set G)).mul_mem hktU hyU
    exact ⟨h.inf_centralizer_uGrp, fun a ha ha1 => eight_one (isTI_conj hTI g) hAg hAN hUV ha ha1⟩

end CFSG.LocalAnalysis.WeakClosure81

end
