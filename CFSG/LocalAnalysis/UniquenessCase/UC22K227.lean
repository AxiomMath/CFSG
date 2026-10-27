module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KBar
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21n
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22K339Zc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sd
import CFSG.LocalAnalysis.UniquenessCase.UC22CmpMain
public import CFSG.LocalAnalysis.UniquenessCase.UC22K339Z

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn
  IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Quasithin (thompsonJ)
open P22x P22s

variable {G : Type} [Group G] [Finite G]

theorem uc22k_le_centralizer_conj (D : Data G) (hK : K339Z)
    {Y : Subgroup (MBar D.M D.U)} {H : Subgroup G} (hpkg : HiPkgK D Y H) {g : G}
    (hgS : g ∈ normalizer (proofS D : Set G)) (hgE : g ∉ normalizer (proofEiHat D (preN D Y) : Set G)) :
    H ≤ centralizer ((proofEiHat D (preN D Y)).map (MulAut.conj g).toMonoidHom : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpkg' := hpkg
  obtain ⟨hSH, hG, hZ, hX, hb, hEle, -, -, -, -⟩ := hpkg
  set S : Subgroup G := proofS D with hSdef
  set F : Subgroup G := omegaZJ22 (pCoreOf 2 H) with hFdef
  set Ehat : Subgroup G := proofEiHat D (preN D Y) with hEhat
  set ι : ↥S →* ↥H := Subgroup.inclusion hSH with hι
  set cg : MulAut ↥S := S.normalizerMonoidHom ⟨g⁻¹, inv_mem hgS⟩ with hcg
  have hcg_apply : ∀ s : ↥S, ((cg s : ↥S) : G) = g⁻¹ * s * g := by
    intro s
    change g⁻¹ * (s : G) * g⁻¹⁻¹ = g⁻¹ * s * g
    rw [inv_inv]
  set ι₁ : ↥S →* ↥H := ι.comp cg.toMonoidHom with hι₁
  have hS2 : IsPGroup 2 ↥S := D.sylowM.isPGroup.to_le inf_le_left
  have hG₁ : InClassG ↥S ↥H ι₁ := inClassG_comp hG cg
  have hSJ := centralizer_elemThompsonCenterTorsion_proofS D
  have hZ₂ : ⁅(⊤ : Subgroup ↥H), (omegaOne 2 (Subgroup.center ↥S)).map ι⁆ ≠ ⊥ :=
    commutator_omegaOne_ne_bot hSH hZ
  have hZ₁ : ⁅(⊤ : Subgroup ↥H), (omegaOne 2 (Subgroup.center ↥S)).map ι₁⁆ ≠ ⊥ := by
    rw [hι₁, ← Subgroup.map_map, map_omegaOne_center_mulEquiv cg]
    exact hZ₂
  have hconjS : ∀ s ∈ S, g * s * g⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.1 hgS s).1 hs
  have hVS : ⁅H, F⁆ ≤ S := by
    rw [hFdef, ← map_tripleV H]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs⟩ := tripleV_le_range hG hy
    rw [← hs]
    exact s.2
  have hVF : ∀ y : ↥H, y ∈ tripleV ↥H → (y : G) ∈ F := by
    intro y hy
    rw [hFdef, ← map_tripleE H]
    exact ⟨y, tripleV_le_tripleE hy, rfl⟩
  rcases hK ↥S hS2 hSJ ↥H ι₁ hG₁ ↥H ι hG hZ₁ hZ₂ with h1 | h2' | h3'
  ·
    exfalso
    apply hgE
    have hEtS : tripleE ↥H ≤ ι.range := tripleE_le_range hG
    have hFS : F ≤ S := by
      rw [hFdef, ← map_tripleE H]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨s, hs⟩ := hEtS hy
      rw [← hs]
      exact s.2
    have hmemF : ∀ s : ↥S, ι s ∈ tripleE ↥H ↔ (s : G) ∈ F := by
      intro s
      rw [hFdef, ← map_tripleE H]
      constructor
      · intro h
        exact ⟨ι s, h, rfl⟩
      · rintro ⟨y, hy, hys⟩
        have : y = ι s := Subtype.ext hys
        rwa [← this]
    have hFg : F.map (MulAut.conj g).toMonoidHom = F := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        have hyS : y ∈ S := hFS hy
        have hmem : (⟨g * y * g⁻¹, hconjS y hyS⟩ : ↥S) ∈ (tripleE ↥H).comap ι₁ := by
          change ι (cg ⟨g * y * g⁻¹, hconjS y hyS⟩) ∈ tripleE ↥H
          rw [hmemF, hcg_apply]
          have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
          rw [e]
          exact hy
        rw [h1] at hmem
        exact (hmemF _).1 hmem
      · intro y hy
        have hyS : y ∈ S := hFS hy
        have hmem : (⟨y, hyS⟩ : ↥S) ∈ (tripleE ↥H).comap ι := (hmemF _).2 hy
        rw [← h1] at hmem
        change ι (cg ⟨y, hyS⟩) ∈ tripleE ↥H at hmem
        rw [hmemF, hcg_apply] at hmem
        exact ⟨g⁻¹ * y * g, hmem, by simp [MulAut.conj_apply]; group⟩
    have hJg : (jOf D.T).map (MulAut.conj g).toMonoidHom = jOf D.T :=
      map_conj_eq_of_mem_normalizer (mem_normalizer_jOf D hgS)
    refine mem_normalizer_of_map_conj ?_
    rw [← hb, Subgroup.map_commutator, hJg, hFg]
  ·
    exfalso
    apply h2'
    rcases P22k.campbell_seed D hSH hSH hG hG hZ hZ with hc1 | hc3
    · have hc1' : ∀ e ∈ F, g⁻¹ * e * g ∈ pCoreOf 2 H := fun e he => by
        simpa using hc1 g⁻¹ (inv_mem hgS) e he
      have hcomm := P22k.commute_conj_of_pkg D hpkg' hgS hc1'
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb'
      apply Subtype.ext
      have haF : g⁻¹ * (a : G) * g ∈ F := by
        have := hVF (ι₁ a) ha
        rwa [show ((ι₁ a : ↥H) : G) = ((cg a : ↥S) : G) from rfl, hcg_apply] at this
      have hbF : (b : G) ∈ F := hVF (ι b) hb'
      have h := hcomm (b : G) hbF (g⁻¹ * (a : G) * g) haF
      have e : g * (g⁻¹ * (a : G) * g) * g⁻¹ = (a : G) := by group
      rw [e] at h
      exact h
    · exact absurd hc3 hX
  ·
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨heV, -⟩ := hEle he
    have heS : e ∈ S := hVS heV
    set s₀ : ↥S := ⟨g * e * g⁻¹, hconjS e heS⟩ with hs₀
    have hcs₀ : cg s₀ = ⟨e, heS⟩ := by
      apply Subtype.ext
      rw [hcg_apply]
      simp [hs₀]
      group
    have hrange : ι₁.range = ι.range := by
      rw [hι₁, MonoidHom.range_comp]
      have htop : (cg.toMonoidHom).range = ⊤ := MonoidHom.range_eq_top.2 cg.surjective
      rw [htop, ← MonoidHom.range_eq_map]
    have hs₀mem : s₀ ∈ (⁅thompsonJ ι₁.range, tripleE ↥H⁆).comap ι₁ := by
      change ι (cg s₀) ∈ ⁅thompsonJ ι₁.range, tripleE ↥H⁆
      rw [hcs₀, hrange]
      exact K339.mem_commutator_thompsonJ_tripleE hSH (hSH heS) (K339.proofEiHat_le_commutator_jOf D hpkg' he)
    have hcen := h3' ⟨s₀, hs₀mem, rfl⟩
    rw [Subgroup.mem_center_iff] at hcen
    have := congrArg Subtype.val (hcen ⟨x, hx⟩)
    simp only [Subgroup.coe_mul] at this
    change (MulAut.conj g).toMonoidHom e * x = x * (MulAut.conj g).toMonoidHom e
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact this.symm

theorem uc22k_s22_7 (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D)
    (h32 : S22_3_2 D Ch) (h4 : S22_4 D Ch) (h52 : S22_5_2Bar D Ch) (h6 : S22_6Hat D Ch)
    (hHi : H1930 D → ∀ c : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)), NbarSplit D Nb →
      ∀ i, ∃ H : Subgroup G, HiPkgK D (Nb i) H)
    (hK : K339Z) : S22_7 D Ch := by
  intro hH c g hg
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨m, Nb, hNb⟩ := h32 hH c
  obtain ⟨i, hi⟩ := uc22k_exists_index_bar D hNb hpP (h52 hH c p hp)
  obtain ⟨H, hpkg⟩ := hHi hH c m Nb hNb i
  by_cases hgE : g ∈ normalizer (proofEiHat D (preN D (Nb i)) : Set G)
  · exact h6 hH c m Nb hNb i hgE
  · by_contra hgM
    have hcen := uc22k_le_centralizer_conj D hK hpkg hg hgE
    obtain ⟨-, -, -, -, -, -, hHM, hpH, -⟩ := hpkg
    have hsp : IsStronglyPEmbedded p D.M := hSg.sig1_sp p (h4 hH c ▸ hp)
    refine hsp.2.2 g hgM ((hpH p hpP hp2 hi).trans (Subgroup.card_dvd_of_le ?_))
    intro x hx
    refine ⟨hHM hx, ?_⟩
    have hxc := Subgroup.mem_centralizer_iff.1 (hcen hx)
    have hcomm : g⁻¹ * x * g ∈ centralizer (proofEiHat D (preN D (Nb i)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h1 := hxc (g * e * g⁻¹) ⟨e, he, by simp [MulAut.conj_apply]⟩
      calc e * (g⁻¹ * x * g) = g⁻¹ * ((g * e * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * e * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * x * g * e := by group
    have hM := h6 hH c m Nb hNb i (Subgroup.centralizer_le_normalizer _ hcomm)
    exact ⟨g⁻¹ * x * g, hM, by simp [MulAut.conj_apply]; group⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
