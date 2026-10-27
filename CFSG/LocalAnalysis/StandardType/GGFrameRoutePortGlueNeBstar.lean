module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRoot
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueStar
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueTwo
import CFSG.GroupTheory.CoprimeHyperplaneCentralizer

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem twoGroup_le_centralizer_of_D6
    {B Bs K : Subgroup G} {z : G}
    (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 7) (hz : z ∈ B) (hz1 : z ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) 3 Bs K)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hBsT : Bs ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨hZ, hEcard, hsup, -, hKn, hm⟩ :=
    sStar_normal_D6 hB hBBs hBs hcard hz hz1 hcomp hN hker hBstar hK
  refine le_centralizer_bstar_of_normal hcomp.1 hKn hsup ?_ hT hTz hBsT
  intro S hS hSN hES
  exact le_centralizer_of_omegaPlusSix_marking hm hZ inf_le_right
    (IsElemAbelian.mono hBs inf_le_left) (by rw [hEcard]) hS hSN hES

theorem twoGroup_le_centralizer_of_E7
    {B Bs K : Subgroup G} {z : G} {n : ℕ}
    (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ B) (hz1 : z ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs K)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hBsT : Bs ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨-, hZ, ⟨F, fieldF, finiteF, hcharF, hF2, ⟨eK⟩⟩, hEcard, hsup, -, hKn, hm⟩ :=
    sStar_normal_E7 hB hBBs hBs hcard hn hz hz1 hcomp hN hker hBstar hK
  refine le_centralizer_bstar_of_normal hcomp.1 hKn hsup ?_ hT hTz hBsT
  intro S hS hSN hES
  exact le_centralizer_of_E7Two_torus hF2 eK inf_le_right
    (IsElemAbelian.mono hBs inf_le_left) (by rw [hEcard]) hS hSN hES

theorem ne_bstar_of_isRoot_twoGroup {B Bs : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ}
    (hI : GGThmIHyp 3 B x L) (M : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hBs : IsElemAbelian 3 Bs) {z₀ : G} (hz₀ : M.IsRoot z₀)
    (hT₀ : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.centralizer ({z₀} : Set G) →
      Bs ≤ Subgroup.normalizer (T : Set G) → T ≤ Subgroup.centralizer (Bs : Set G)) :
    B ≠ Bs := by
  intro hB
  have hI' : GGThmIHyp 3 Bs x L := hB ▸ hI
  have hstd : LargeEvenStandardType 3 Bs x L := hI'.2.2.2.2.2.2.2
  obtain ⟨T, -, hT2, hBsT, hTB⟩ := hstd.2.1
  have hfaith : ¬ Bs ≤ Subgroup.centralizer (T : Set G) := by
    intro h
    exact hTB (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp h))
  have hcardBs : Nat.card Bs = 3 ^ n := by
    calc Nat.card Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card (FEVec n) := Nat.card_congr M.ψ.toEquiv
      _ = 3 ^ n := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hEcard : 3 ^ 2 ≤ Nat.card Bs := by
    rw [hcardBs]
    rcases hn with rfl | rfl <;> norm_num
  have h3T : ¬ 3 ∣ Nat.card T := by
    obtain ⟨m, hm⟩ := hT2.exists_card_eq (p := 2)
    rw [hm]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow (p := 3) (m := 2) (by norm_num) h)
      (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Y, hYBs, hYcard, hYnot⟩ :=
    CFSG.GroupTheory.exists_hyperplane_not_le_centralizer_inf_centralizer
      (r := 3) hBs hEcard hBsT h3T hfaith
  have hYcard' : Nat.card Bs = 3 * Nat.card Y := by
    rw [← hYcard, Nat.mul_comm]
  obtain ⟨z, hzY, hzroot⟩ := M.exists_isRoot_mem_of_index_three hn hBs hYBs hYcard'
  obtain ⟨g, hgN, hgzor⟩ := M.exists_conj_of_isRoot hn hBs hz₀ hzroot
  set S : Subgroup G := T ⊓ Subgroup.centralizer (Y : Set G) with hSdef
  set T' : Subgroup G := S.map (MulAut.conj g⁻¹).toMonoidHom with hT'def
  have hT'2 : IsPGroup 2 T' := by
    rw [hT'def, hSdef]
    exact (IsPGroup.to_inf_left hT2).map (MulAut.conj g⁻¹).toMonoidHom
  have hT'z : T' ≤ Subgroup.centralizer ({z₀} : Set G) := by
    intro t ht
    rw [hT'def, hSdef] at ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsz : Commute s z := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_centralizer_iff.mp hs.2 z hzY).symm
    rcases hgzor with hgz | hgz
    · rw [← hgz] at hsz
      have hconj : Commute (g⁻¹ * s * g) z₀ := by
        have h := (Commute.conj_iff (h := g⁻¹)).mpr hsz
        simpa [mul_assoc] using h
      simpa [MulAut.conj_apply] using hconj.eq
    · have hz₀eq : z₀ = (g⁻¹ * z * g)⁻¹ := by
        have hz : z = (g * z₀ * g⁻¹)⁻¹ := by
          have h := congrArg (fun t : G => t⁻¹) hgz
          simpa using h.symm
        rw [hz]
        group
      rw [hz₀eq]
      have hconj : Commute (g⁻¹ * s * g) (g⁻¹ * z * g) := by
        simpa using (Commute.conj_iff (h := g⁻¹)).mpr hsz
      simpa [MulAut.conj_apply] using hconj.inv_right.eq
  have hT'Bs : Bs ≤ Subgroup.normalizer (T' : Set G) := by
    have hBsCY : Bs ≤ Subgroup.centralizer (Y : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (congrArg Subtype.val
        (isMulCommutative_iff.mp hBs.1 ⟨b, hb⟩ ⟨y, hYBs hy⟩)).symm
    have hBsNS : Bs ≤ Subgroup.normalizer (S : Set G) := by
      rw [hSdef]
      exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hBsT hb, (hBsCY.trans (Subgroup.le_normalizer
          (H := Subgroup.centralizer (Y : Set G)))) hb⟩
    have hmapN : Bs.map (MulAut.conj g⁻¹).toMonoidHom ≤
        (Subgroup.normalizer (S : Set G)).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono hBsNS
    rw [Subgroup.map_equiv_normalizer_eq] at hmapN
    have hBsmap : Bs.map (MulAut.conj g⁻¹).toMonoidHom = Bs :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := Bs) (g := g⁻¹)).mp
        (Subgroup.inv_mem _ hgN)
    rw [hBsmap] at hmapN
    rwa [hT'def]
  have hT'C : T' ≤ Subgroup.centralizer (Bs : Set G) := hT₀ T' hT'2 hT'z hT'Bs
  have hSC : S ≤ Subgroup.centralizer (Bs : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have ht : g⁻¹ * s * g ∈ T' := by
      rw [hT'def, hSdef]
      exact Subgroup.mem_map.mpr ⟨s, hs, by simp⟩
    have hb' : g⁻¹ * b * g ∈ Bs := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) b).mp hb
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hT'C ht)) (g⁻¹ * b * g) hb'
    calc b * s = g * (g⁻¹ * b * g) * g⁻¹ * (g * (g⁻¹ * s * g) * g⁻¹) := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * (g⁻¹ * b * g)) * g⁻¹ := by rw [hcomm]
      _ = s * b := by group
  have hnot : ¬ Bs ≤ Subgroup.centralizer (S : Set G) := by
    simpa [hSdef] using hYnot
  exact hnot (Subgroup.le_centralizer_iff.mpr hSC)

end CFSG.StandardType.FrameRoute

end
