module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Conj
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.Open
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.StandardType.LieKnownR2.Short

private theorem rckSTwE6_map_centralizer_mulEquiv {H : Type*} [Group H] (e : H ≃* H)
    (S : Set H) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e.toMonoidHom '' S) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image S e.toMonoidHom
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro s hs
    have h := hy (e.toMonoidHom s) (Set.mem_image_of_mem e.toMonoidHom hs)
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h

theorem rckSTwE6_core_map_mulEquiv {M : LieUniversal} {α β : Fin M.D.rank → ℤ}
    (e : M.K ≃* M.K) (h : RCKLemmaHCore M α)
    (hmap : (M.D.rootGroup α).map e.toMonoidHom = M.D.rootGroup β) :
    RCKLemmaHCore M β := by
  intro x hx hx1
  obtain ⟨x₀, hx₀, hx₀eq⟩ := Subgroup.mem_map.mp (hmap ▸ hx)
  have hx₀1 : x₀ ≠ 1 := by
    rintro rfl
    exact hx1 (by rw [← hx₀eq]; simp)
  have hx0 := h x₀ hx₀ hx₀1
  have hcen : (Subgroup.centralizer ({x₀} : Set M.K)).map e.toMonoidHom =
      Subgroup.centralizer ({x} : Set M.K) := by
    rw [rckSTwE6_map_centralizer_mulEquiv e {x₀}, Set.image_singleton, hx₀eq]
  have hmapcen : (Subgroup.centralizer ((M.D.rootGroup α : Subgroup M.K) : Set M.K)).map
        e.toMonoidHom = Subgroup.centralizer ((M.D.rootGroup β : Subgroup M.K) : Set M.K) := by
    rw [rckSTwE6_map_centralizer_mulEquiv e ((M.D.rootGroup α : Subgroup M.K) : Set M.K),
      ← Subgroup.coe_map, hmap]
  have hpc : pCoreOf 2 (Subgroup.centralizer ({x} : Set M.K)) =
      (pCoreOf 2 (Subgroup.centralizer ({x₀} : Set M.K))).map e.toMonoidHom := by
    rw [← hcen]
    exact GGRootNorm.pCoreOf_map_mulEquiv e _
  rw [hpc, ← hmapcen]
  exact Subgroup.map_mono hx0

theorem rckSTwE6_core_of_alpha
    {m g : ℕ} (hg : 1 ≤ g)
    (hα : RCKLemmaHCore (ggU .twistedE6 m g) twE6Alpha)
    {β : Fin (ggU .twistedE6 m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .twistedE6 m g).D.roots)
    (hL : ¬ GGLongRoot (ggU .twistedE6 m g).D β) :
    RCKLemmaHCore (ggU .twistedE6 m g) β := by
  have hθ : ∀ c : GaloisField 2 (2 * g), frobQ 2 g (frobQ 2 g c) = c :=
    fun c => frobQ_frobQ 2 g (by omega) c
  have hct := twistedDatum_isCTGroupDatum (frobQ 2 g) hθ
    (iSup_twistedDatum_rootGroup (frobQ 2 g) hθ)
  obtain ⟨w, hw⟩ := twE6_exists_weyl_of_not_long (frobQ 2 g) hβ hL
  obtain ⟨g₀, hg₀, -⟩ := exists_conj_ggRootSub_of_weylAction
    (D := twistedDatum (GaloisField 2 (2 * g)) (frobQ 2 g))
    hct (twE6_alpha_mem_roots (frobQ 2 g)) w hw
    (1 : fixedGroup (GaloisField 2 (2 * g)) (frobQ 2 g))
  have hg₀' : (twistedDatum (GaloisField 2 (2 * g)) (frobQ 2 g)).rootGroup β =
      ((twistedDatum (GaloisField 2 (2 * g)) (frobQ 2 g)).rootGroup twE6Alpha).map
        (MulAut.conj g₀).toMonoidHom := by
    have hL : ggRootSub (twistedDatum (GaloisField 2 (2 * g)) (frobQ 2 g))
        (MonoidHom.id (fixedGroup (GaloisField 2 (2 * g)) (frobQ 2 g))) β
        (1 : fixedGroup (GaloisField 2 (2 * g)) (frobQ 2 g)) =
        (twistedDatum (GaloisField 2 (2 * g)) (frobQ 2 g)).rootGroup β := by
      simp only [ggRootSub, Subgroup.map_id]
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        simpa [MulAut.conj_apply] using hy
      · intro x hx
        exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rw [hL] at hg₀
    exact hg₀
  exact rckSTwE6_core_map_mulEquiv (M := ggU .twistedE6 m g) (MulAut.conj g₀) hα hg₀'.symm

end CFSG.StandardType.RCKC1
