module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVLemmaQ
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerRest
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggItem2_main (hS1 : GGStructSOne) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ Bs D K : Subgroup G} {b m : G} (hsimple : IsSimpleGroup ↥G₀)
    (hBsEl : IsElemAbelian p Bs) (hDel : IsElemAbelian p D) (hDBs : D ≤ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hmark : ∀ {n : G}, n ∈ Subgroup.normalizer (G₀ : Set G) → ∀ {b d : G}, b ∈ Bs → d ∈ Bs →
      LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ a ∈ Subgroup.closure ({b, n * d * n⁻¹} : Set G),
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ)
    (hperf : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (G₀ : Set G) → ⁅P, P⁆ = P → P ≤ G₀)
    (hfus : GGControlsStrongFusion (Subgroup.normalizer (G₀ : Set G))
      (D.map (MulAut.conj m⁻¹).toMonoidHom))
    (hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Bs) (hK : IsSubnormal K (Subgroup.centralizer {b})) (hm : m ∈ Subgroup.normalizer
      (G₀ : Set G)) (hEC : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b})
    [((ggAutKV D K (Subgroup.normalizer (G₀ : Set G)) m).subgroupOf (ggAutKW D K m)).Normal] :
    GGHypRestIVComponentwise p
      (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
        (ggAutKPi D K (Subgroup.normalizer (G₀ : Set G)) m)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hx hx1 C hC
  set E₀ : Subgroup G := D.map (MulAut.conj m⁻¹).toMonoidHom with hE₀
  have hE0el : IsElemAbelian p E₀ := CFSG.Open.IsElemAbelian.map hDel _
  have hKW : K ≤ ggAutKW D K m := le_sup_right
  have hπsurj : Function.Surjective (ggAutKPi D K (Subgroup.normalizer (G₀ : Set G)) m) :=
    QuotientGroup.mk'_surjective _
  have hKn : (K.subgroupOf (ggAutKW D K m)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKW]
    exact sup_le hnorm Subgroup.le_normalizer
  have hkerV : ∀ w : ↥(ggAutKW D K m),
      ggAutKPi D K (Subgroup.normalizer (G₀ : Set G)) m w = 1 →
        (w : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro w hw
    have hw' : w ∈ (ggAutKV D K (Subgroup.normalizer (G₀ : Set G)) m).subgroupOf
        (ggAutKW D K m) := (QuotientGroup.eq_one_iff w).mp hw
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw')).2
  obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hx
  have heE : (e' : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp he'
  have he1 : (e' : G) ≠ 1 := by
    intro h
    apply hx1
    rw [show e' = 1 from Subtype.ext h, map_one]
  obtain ⟨hCle, hCp⟩ := (ggLargeEvenPComponent_iff p _ C).1 hC
  obtain ⟨C₀, hC₀le, hC₀p, hC₀map⟩ := ggLemmaQ_ambient p
    (ggAutKPi D K (Subgroup.normalizer (G₀ : Set G)) m) hπsurj (E := E₀) rfl hKn hE0el.1
    (fun w hw _ => hkerV w hw) e' hCle hCp
  obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.mp heE
  have hed : (e' : G) = m⁻¹ * d * (m⁻¹)⁻¹ := by
    rw [← hde]
    simp [MulAut.conj_apply]
  have hdBs : d ∈ Bs := hDBs hd
  have hmk := hmark (inv_mem hm) hb hdBs
  rw [← hed] at hmk
  have hbp : b ^ p = 1 := hBsEl.2 b hb
  have hep : (e' : G) ^ p = 1 := hE0el.2 _ heE
  have hbe : Commute b (e' : G) := (Subgroup.mem_centralizer_singleton_iff.mp (hEC heE)).symm
  have hA := ggIsElemAbelian_closure_pair hbp hep hbe
  have heN : (e' : G) ∈ Subgroup.normalizer (G₀ : Set G) := by
    rw [hed]
    exact mul_mem (mul_mem (inv_mem hm) (hBsN hdBs)) (inv_mem (inv_mem hm))
  have hAN : Subgroup.closure ({b, (e' : G)} : Set G) ≤ Subgroup.normalizer (G₀ : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hBsN hb
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact heN
  have hperf' : ∀ P : Subgroup G, P ≤ Subgroup.centralizer {(e' : G)} → ⁅P, P⁆ = P → P ≤ G₀ :=
    fun P hP hPP => hperf P (hP.trans (hfus.centralizer_le heE he1)) hPP
  obtain ⟨hqs, hmk0⟩ := ggItem2_core hS1 hp hp2 hsimple hA hAN hmk hperf' hK hC₀le hC₀p
  have hC₀K : C₀ ≤ K := hC₀le.trans inf_le_left
  obtain ⟨Φ, hΦ, hΦc⟩ := ggExists_central_surj
    (ggAutKPi D K (Subgroup.normalizer (G₀ : Set G)) m) (hC₀K.trans hKW) hC₀map
    (fun w hw => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hC₀K) (hkerV w hw))
  exact ggQuasisimple_marking_of_central_surjective Φ hΦ hΦc hqs hmk0

end Main

end CFSG.StandardType
