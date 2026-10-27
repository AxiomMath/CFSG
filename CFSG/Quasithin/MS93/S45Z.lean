module

public import CFSG.Quasithin.MS93.S46Fin
public import CFSG.Quasithin.MS93.S45M0

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Smul

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem IsGoodPath.smul {p : ℕ → Vtx X} {N : ℕ} (hp : IsGoodPath X p N) (g : X.Universal) :
    IsGoodPath X (fun i => g • p i) N := by
  refine ⟨⟨fun i hi => (adj_smul X g _ _).mpr (hp.adj i hi),
    fun i hi heq => hp.nb i hi (smul_left_cancel g heq)⟩,
    (isMVtx_smul X g _).mpr hp.mvtx, fun i hi hi8 => (isCritical_smul X g _ _).mpr
      (hp.crit i hi hi8), fun i hi h2 hi2 => ?_, fun i hi h8 hiN => ?_⟩
  · obtain ⟨g', hg', hgx⟩ := hp.straight i hi h2 hi2
    refine ⟨g * g' * g⁻¹, ?_, ?_⟩
    · rw [stab_smul]
      exact ⟨g', hg', rfl⟩
    · show (g * g' * g⁻¹) • g • p (i + 2) = g • p (i - 2)
      rw [mul_smul, mul_smul, inv_smul_smul, hgx]
  · intro hle
    apply hp.pe i hi h8 hiN
    have hle' : ZM X (g • p (i - 8)) ≤
        Subgroup.normalizer (Usup X (g • p i) (g • p (i + 1)) : Set X.Universal) := hle
    rw [zm_smul, usup_smul, ← Subgroup.map_equiv_normalizer_eq] at hle'
    exact (map_conj_le_map_conj_iff g).mp hle'

end Smul

section ImM

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem frattini_map_equiv {V W : Type*} [Group V] [Group W] (f : V ≃* W) :
    (frattini V).map f.toMonoidHom = frattini W := by
  have h1 : (frattini W).comap f.toMonoidHom = frattini V := f.comapSubgroup.map_radical
  rw [← h1, Subgroup.map_comap_eq_self_of_surjective f.surjective]

theorem imM_frattiniIn {V : Subgroup G} (hV : V ≤ M) :
    imM hTM (frattiniIn V) = frattiniIn (imM hTM V) := by
  set e := S46.imMEquiv hTM hV with he
  have h1 : (frattini ↥V).map e.toMonoidHom = frattini ↥(imM hTM V) := frattini_map_equiv e
  rw [frattiniIn, frattiniIn, ← h1, Subgroup.map_map]
  apply le_antisymm
  · rintro _ ⟨⟨m, hm⟩, hmF, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hmF
    obtain ⟨x, hx, hxm⟩ := hmF
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    rw [S46.coe_imMEquiv]
    congr 1
    exact Subtype.ext hxm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, hV x.2⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact ⟨x, hx, rfl⟩
    · simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom]
      rw [S46.coe_imMEquiv]

theorem imM_sup {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM (K ⊔ K') = imM hTM K ⊔ imM hTM K' := by
  simp only [imM]
  rw [Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

theorem card_imM {K : Subgroup G} (hK : K ≤ M) : Nat.card ↥(imM hTM K) = Nat.card ↥K :=
  (Nat.card_congr (S46.imMEquiv hTM hK).toEquiv).symm

end ImM

section Qj

variable {G : Type} [Group G]

theorem qjInfo_sup_of_le_centralizer {M T L U H : Subgroup G} {q : ℕ} (hQ : QjInfo T L U q)
    (hTM : T ≤ M) (hUM : U ≤ M) (hHM : H ≤ Subgroup.centralizer (M : Set G))
    (hUH : U ⊓ H = ⊥) (hU : U ≤ Subgroup.centralizer (U : Set G)) : QjInfo T L (U ⊔ H) q := by
  intro SL hSL hTSL
  obtain ⟨X, hX, hXq, hXT⟩ := hQ SL hSL hTSL
  refine ⟨X, hX, ?_, hXT⟩
  have hHX : H ≤ Subgroup.centralizer (X : Set G) :=
    hHM.trans (Subgroup.centralizer_le (hXT.trans hTM))
  have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.le_centralizer_iff.mp hHM).trans (Subgroup.centralizer_le_normalizer _)
  have hHU : H ≤ Subgroup.normalizer (U : Set G) :=
    (hHM.trans (Subgroup.centralizer_le hUM)).trans (Subgroup.centralizer_le_normalizer _)
  set C := U ⊓ Subgroup.centralizer (X : Set G) with hC
  have hinf : (U ⊔ H) ⊓ Subgroup.centralizer (X : Set G) = C ⊔ H := by
    rw [sup_comm U H, sup_comm C H, sup_inf_eq_of_le hHX hHU]
  rw [hinf]
  have hCU : C ≤ U := inf_le_left
  have hUC : U ≤ Subgroup.normalizer (C : Set G) :=
    (hU.trans (Subgroup.centralizer_le hCU)).trans (Subgroup.centralizer_le_normalizer _)
  have hUn : U ≤ Subgroup.normalizer ((C ⊔ H : Subgroup G) : Set G) :=
    le_normalizer_sup hUC (hUM.trans hMH)
  have hsup : U ⊔ (C ⊔ H) = U ⊔ H := by
    rw [← sup_assoc, sup_eq_left.mpr hCU]
  have hCHU : (C ⊔ H) ⊓ U = C := by
    rw [sup_inf_eq_of_le hCU ((hCU.trans hUM).trans hMH), inf_comm H U, hUH, sup_bot_eq]
  rw [← hsup, relIndex_sup_eq hUn, ← Subgroup.inf_relIndex_right, hCHU]
  exact hXq

end Qj

end CFSG.Quasithin.MS93.S45
