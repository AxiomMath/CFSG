module

public import CFSG.Quasithin.H13.GoldschmidtCTKAbs
public import CFSG.Quasithin.H13.GoldschmidtCTKFam

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique

theorem IsDelta5Ext.of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    {V : Subgroup K} {W : Subgroup L} (hVW : ∀ x : K, x ∈ V ↔ e x ∈ W)
    (h : IsDelta5Ext K V) : IsDelta5Ext L W := by
  obtain ⟨α, hα, hαk, β, hβ, hβe⟩ := h
  have hW : V.map e.toMonoidHom = W := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hVW x).1 hx
    · intro hy
      exact ⟨e.symm y, (hVW _).2 (by simpa using hy), by simp⟩
  let ε : ↥V ≃* ↥W := (e.subgroupMap V).trans (MulEquiv.subgroupCongr hW)
  have hε : ∀ v : ↥V, ((ε v : ↥W) : L) = e v := fun v => rfl
  refine ⟨α.comp e.symm.toMonoidHom, hα.comp e.symm.surjective, ?_,
    β.comp ε.symm.toMonoidHom, ?_, ?_⟩
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk]
    exact (hVW _).trans (by simp)
  · exact hβ.comp ε.symm.bijective
  · intro ℓ u v huv i
    have hεu : ((ε.symm u : ↥V) : K) = e.symm (u : L) := by
      apply e.injective
      rw [← hε, MulEquiv.apply_symm_apply]
      simp
    have hεv : ((ε.symm v : ↥V) : K) = e.symm (v : L) := by
      apply e.injective
      rw [← hε, MulEquiv.apply_symm_apply]
      simp
    refine hβe (e.symm ℓ) (ε.symm u) (ε.symm v) ?_ i
    rw [hεu, hεv, huv]
    simp

theorem isDelta5Ext_of_alt5 {G : Type} [Group G] [Finite G] {K V : Subgroup G}
    (hKs : IsShort2 K) (hKa : IsAltType K 5) (hKV : pCoreOf 2 K = V) (hV16 : Nat.card ↥V = 16) :
    IsDelta5Ext ↥K (V.subgroupOf K) := by
  have hU : blockU K = V := blockU_eq_of_alt5 hKs hKa hKV hV16
  have hZ : blockZ K = ⊥ := AppC.blockZ_eq_bot_of_alt5 hKs hKa
  have hVK : V ≤ K := hKV ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 K
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := hKa
  have hVsub : V.subgroupOf K = CFSG.pCore 2 K := by
    have h : pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := by
      unfold pCoreOf
      try with_reducible rfl
    rw [← hKV, h]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  let ε : ↥(V.subgroupOf K) ≃* ↥(blockU K) :=
    (Subgroup.subgroupOfEquivOfLe hVK).trans (MulEquiv.subgroupCongr hU.symm)
  have hε : ∀ u : ↥(V.subgroupOf K), (((ε u : ↥(blockU K)) : G)) = ((u : ↥K) : G) :=
    fun u => rfl
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ]
    exact Subgroup.bot_subgroupOf _
  refine ⟨α, hα, hαk.trans hVsub.symm, β.comp ε.toMonoidHom, ?_, ?_⟩
  · exact ⟨hβinj.comp ε.injective, hβ.comp ε.surjective⟩
  · intro ℓ u v huv i
    exact hβe ℓ (ε u) (ε v) (by rw [hε, hε]; exact congrArg Subtype.val huv) i

end CFSG.Quasithin.H13.CTK
