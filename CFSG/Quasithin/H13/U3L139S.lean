module

public import CFSG.Quasithin.H13.U3L139
public import CFSG.Quasithin.H13.A6HatPlusB
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem pres45_of_act4f : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 → Pres45 σ := by
  decide +kernel

theorem pres45_of_inW1 : ∀ σ : Perm (Fin 6), InW1 (G6.permAct 6 σ e45) → Pres45 σ := by
  decide +kernel

theorem fix_W1_of_pres45 : ∀ σ : Perm (Fin 6), Pres45 σ → ∀ x : P6, InW1 x →
    G6.permAct 6 σ x = x := by
  decide +kernel

theorem pres45_of_fix : ∀ σ : Perm (Fin 6),
    (G6.permAct 6 σ e0123 = e0123 ∨ G6.permAct 6 σ e45 = e45) → Pres45 σ := by
  decide +kernel

variable {G : Type} [Group G]

noncomputable def frame139OfSetting4 [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V) :
    Frame139 T L V where
  ρ := S.frame.ρ
  L_le := S.frame.L_le
  T_le := S.frame.T_le
  ker := S.rho_eq_one_iff
  image_L := S.frame.image_L
  T_D := S.frame.T_D
  N1 := fun g hg => pres45_of_act4f _ (S.fix_e0123 g (S.conj_z_of_normalizes hg))

theorem s134_rho_eq_one_iff [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
    (g : ↥(normalizer (V : Set G))) :
    S.frame.ρ g = 1 ↔ (g : G) ∈ centralizer (V : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro v hv
    have := (S.conj_eq_iff g ⟨v, hv⟩).2 (by rw [h, map_one, MulAut.one_apply])
    calc v * g = g * v * (g : G)⁻¹ * g := by rw [this]
      _ = g * v := by group
  · intro h
    apply coreAct_injective
    refine MulEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    have := (S.conj_eq_iff g v).1 (by
      have := mem_centralizer_iff.mp h v v.2
      calc (g : G) * v * (g : G)⁻¹ = v * g * (g : G)⁻¹ := by rw [this]
        _ = v := by group)
    rw [map_one, MulAut.one_apply]
    exact this

theorem s134_e45_mem_V1 [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V) :
    ((S.frame.ψ.symm ⟨e45, e45_mem⟩ : ↥V) : G) ∈ fsuV1 T V := by
  rw [S.mem_V1_iff]
  refine ⟨(S.frame.ψ.symm ⟨e45, e45_mem⟩).2, ?_⟩
  rw [show (⟨((S.frame.ψ.symm ⟨e45, e45_mem⟩ : ↥V) : G),
      (S.frame.ψ.symm ⟨e45, e45_mem⟩).2⟩ : ↥V) = S.frame.ψ.symm ⟨e45, e45_mem⟩ from rfl,
    MulEquiv.apply_symm_apply]
  decide

theorem s134_pres45 [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
    (g : ↥(normalizer (V : Set G))) (hg : (g : G) ∈ normalizer (fsuV1 T V : Set G)) :
    Pres45 (S.frame.ρ g) := by
  set z₂ := S.frame.ψ.symm ⟨e45, e45_mem⟩ with hz₂
  have h1 := (mem_normalizer_iff.1 hg (z₂ : G)).1 (s134_e45_mem_V1 S)
  obtain ⟨hV', hW⟩ := S.mem_V1_iff.1 h1
  have h2 := S.psi_conj g z₂
  rw [hz₂, MulEquiv.apply_symm_apply] at h2
  rw [show (⟨(g : G) * (z₂ : G) * (g : G)⁻¹, hV'⟩ : ↥V) =
      ⟨(g : G) * (z₂ : G) * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 z₂).mp z₂.2⟩ from rfl,
    h2] at hW
  exact pres45_of_inW1 _ (by rwa [G6.coreAct_coe] at hW)

noncomputable def frame139OfSetting134 [Finite G] {T L V : Subgroup G}
    (S : Setting134 G T L V) : Frame139 T L V where
  ρ := S.frame.ρ
  L_le := S.frame.L_le
  T_le := S.frame.T_le
  ker := s134_rho_eq_one_iff S
  image_L := S.frame.image_L
  T_D := S.frame.T_D
  N1 := s134_pres45 S

theorem s134_mem_normalizer_V1 [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
    {v : G} (hv : v ∈ fsuV1 T V) (hvL : v ∉ centralizer (L : Set G)) {y : G}
    (hyN : y ∈ normalizer (V : Set G)) (hyv : y ∈ centralizer ({v} : Set G)) :
    y ∈ normalizer (fsuV1 T V : Set G) := by
  obtain ⟨hvV, hvW⟩ := S.mem_V1_iff.1 hv
  have hψv : (S.frame.ψ ⟨v, hvV⟩ : P6) = e0123 ∨ (S.frame.ψ ⟨v, hvV⟩ : P6) = e45 := by
    rcases W1_cases _ (S.frame.ψ ⟨v, hvV⟩).2 hvW with h | h | h | h
    · exfalso
      apply hvL
      have : (⟨v, hvV⟩ : ↥V) = 1 := S.frame.ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
      rw [show v = 1 from congrArg Subtype.val this]
      exact one_mem _
    · exfalso
      apply hvL
      have : (⟨v, hvV⟩ : ↥V) = ⟨S.zV, S.zV_mem_V⟩ :=
        S.frame.ψ.injective (Subtype.ext (by rw [h, S.psi_zV]))
      exact (S.mem_centralizer_L_iff ⟨v, hvV⟩).2 (Or.inr this)
    · exact Or.inl h
    · exact Or.inr h
  have hfix := (S.conj_eq_iff ⟨y, hyN⟩ ⟨v, hvV⟩).1 (by
    rw [mem_centralizer_singleton_iff.1 hyv, mul_inv_cancel_right])
  have hfix' := congrArg Subtype.val hfix
  rw [G6.coreAct_coe] at hfix'
  have hp : Pres45 (S.frame.ρ ⟨y, hyN⟩) := pres45_of_fix _ (by
    rcases hψv with h | h
    · left; rw [← h]; exact hfix'
    · right; rw [← h]; exact hfix')
  have hc : ∀ w ∈ fsuV1 T V, y * w * y⁻¹ = w := by
    intro w hw
    obtain ⟨hwV, hwW⟩ := S.mem_V1_iff.1 hw
    refine (S.conj_eq_iff ⟨y, hyN⟩ ⟨w, hwV⟩).2 (Subtype.ext ?_)
    rw [G6.coreAct_coe]
    exact fix_W1_of_pres45 _ hp _ hwW
  refine centralizer_le_normalizer (fsuV1 T V) (mem_centralizer_iff.2 fun w hw => ?_)
  calc w * y = y * w * y⁻¹ * y := by rw [hc w hw]
    _ = y * w := by group

theorem stmt13_3_9_of (h1332 : Stmt13_3_2) (h1226 : Stmt12_2_6) (h1228 : Stmt12_2_8)
    (h1338 : A6.Stmt13_3_8) (hL1 : Stmt13_2_2_9L1) : A6.Stmt13_3_9 := by
  intro G _ _ T L V H Y v hH hV hA6 hHin hHM hY2 hYH hHY hv hvL hYv
  by_cases hZV : V ⊓ centralizer (L : Set G) = ⊥
  ·
    obtain ⟨h5, ⟨hTL, -, -, -⟩, -, -⟩ := h1332 G T L hH L hH.faithful
    have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
    have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
      refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
      intro k hk
      exact mem_centralizer_iff.2 fun w hw =>
        ((mem_reducedAggregate' (hV.1 hw)).2.1 k hk).symm
    obtain ⟨S⟩ := exists_setting4_of_1332 h1332 hH (a6CentralQuotient_of_isA6On hLV hO h5 hA6)
      hV hZV
    have hv1 : v ≠ 1 := fun h => hvL (h ▸ one_mem _)
    have hvz : v = S.z := (S.mem_V1_iff.1 hv).resolve_left hv1
    refine (stmt13_3_9_core h1332 h1226 h1228 h1338 hL1 hH hV hA6 hHin hHM hY2 hYH hHY hv hvL
      hYv (frame139OfSetting4 S) fun y hy _ => ?_).imp_right fun h => ⟨h.1, h.2.1, h.2.2.1⟩
    rw [S.normalizer_V1, ← hvz]
    exact (hYv hy).2
  ·
    obtain ⟨S⟩ := exists_setting134 h1332 hH hV hZV
    exact (stmt13_3_9_core h1332 h1226 h1228 h1338 hL1 hH hV hA6 hHin hHM hY2 hYH hHY hv hvL
      hYv (frame139OfSetting134 S) fun y hy hyN =>
        s134_mem_normalizer_V1 S hv hvL hyN (hYv hy).2).imp_right fun h => ⟨h.1, h.2.1, h.2.2.1⟩

end CFSG.Quasithin.H13.U3
