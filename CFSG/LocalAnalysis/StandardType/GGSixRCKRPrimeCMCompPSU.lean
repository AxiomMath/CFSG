module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMLiftPSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes

theorem rckIsComponentOf_top_of_commutator_map {U V : Type} [Group U] [Group V] {ι : U →* V}
    (hι : Function.Injective ι) {H : Subgroup U} {G : Subgroup V} (hHG : H.map ι ≤ G)
    (hnorm : ((H.map ι).subgroupOf G).Normal) {J' : Subgroup U}
    (hJ' : IsComponentOf J' ⁅H, H⁆) :
    CFSG.Open.IsComponentOf ((J'.map ι).subgroupOf G) ⊤ := by
  obtain ⟨hle, hsub, hq⟩ := hJ'
  have hcommH : ⁅H, H⁆ ≤ H :=
    Subgroup.commutator_le.2 fun a ha b hb =>
      H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hHN : H ≤ Subgroup.normalizer ((⁅H, H⁆ : Subgroup U) : Set U) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_commutator (H₁ := H) (H₂ := H) (f := (↑(MulAut.conj k) : U →* U))]
    have hHmap : H.map (↑(MulAut.conj k) : U →* U) = H := by
      refine le_antisymm ?_ ?_
      · rintro x ⟨a, ha, rfl⟩
        exact H.mul_mem (H.mul_mem hk ha) (H.inv_mem hk)
      · intro a ha
        exact ⟨k⁻¹ * a * k, H.mul_mem (H.mul_mem (H.inv_mem hk) ha) hk, by
          show (MulAut.conj k) (k⁻¹ * a * k) = a
          rw [MulAut.conj_apply]
          group⟩
    rw [hHmap]
  have hcommNormal : (⁅H, H⁆.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcommH).2 hHN
  have hA2 : CFSG.Assembly.IsSubnormal ⁅H, H⁆ H :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hcommH).mpr hcommNormal.isSubnormal
  have hJH : J' ≤ H := hle.trans hcommH
  have hsubH : CFSG.Assembly.IsSubnormal J' H := hsub.trans hA2
  have hsubMap : CFSG.Assembly.IsSubnormal (J'.map ι) (H.map ι) := hsubH.map ι
  have hJHmap : J'.map ι ≤ G := (Subgroup.map_mono hJH).trans hHG
  have hA3 : CFSG.Assembly.IsSubnormal (H.map ι) G :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hHG).mpr hnorm.isSubnormal
  have hsubG : CFSG.Assembly.IsSubnormal (J'.map ι) G := hsubMap.trans hA3
  refine (CFSG.Assembly.isComponentOf_iff_open).mp ⟨le_top, ?_, ?_⟩
  · exact CFSG.Assembly.IsSubnormal.of_mathlib
      (CFSG.Assembly.IsSubnormal.subgroupOf hsubG)
  ·
    have e₁ : ↥J' ≃* ↥(J'.map ι) := Subgroup.equivMapOfInjective J' ι hι
    have e₂ : ↥((J'.map ι).subgroupOf G) ≃* ↥(J'.map ι) :=
      Subgroup.subgroupOfEquivOfLe hJHmap
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv e₂
      (CFSG.Assembly.IsQuasisimple.of_mulEquiv e₁.symm hq)

theorem rckPSU_blockGroup_map_normal {n g : ℕ} (s : GL (Fin n) (PSUF g))
    (ε : Matrix (Fin n) (Fin n) (PSUF g)) :
    (glBlockCentralizer (PSUj n g) {s} ε).map (PSUj n g) ≤
        Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
          GUsub (PSUσ g) n ∧
      (((glBlockCentralizer (PSUj n g) {s} ε).map (PSUj n g)).subgroupOf
        (Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
          GUsub (PSUσ g) n)).Normal := by
  let Hsub : Subgroup ↥(Unitary.SU (PSUσ g) n) := glBlockCentralizer (PSUj n g) {s} ε
  let Y : Subgroup (GL (Fin n) (PSUF g)) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
      GUsub (PSUσ g) n
  have hmem : ∀ u ∈ Hsub, (PSUj n g u : GL (Fin n) (PSUF g)) ∈ Y := by
    intro u hu
    have hu' : (PSUj n g u : GL (Fin n) (PSUF g)) ∈
        Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hu
    have huGU : (PSUj n g u : GL (Fin n) (PSUF g)) ∈ GUsub (PSUσ g) n := by
      rw [mem_GUsub_iff]
      simpa [Unitary.conjTr] using (Unitary.mem_SU.mp u.2).2
    exact Subgroup.mem_inf.mpr ⟨hu', huGU⟩
  have hle : Hsub.map (PSUj n g) ≤ Y := by
    rintro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact hmem u hu
  refine ⟨hle, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h x hh hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
  have hxGU : x ∈ GUsub (PSUσ g) n := (Subgroup.mem_inf.mp hx).2
  have hxZ : x ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓
      glFixing (1 - ε) := (Subgroup.mem_inf.mp hx).1
  have huZ : (PSUj n g u : GL (Fin n) (PSUF g)) ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) :=
    (Subgroup.mem_inf.mp (hmem u hu)).1
  have hconjmem : x * (PSUj n g u) * x⁻¹ ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) := by
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxZ huZ) (Subgroup.inv_mem _ hxZ)
  exact Subgroup.mem_map.mpr
    ⟨⟨x * (PSUj n g u) * x⁻¹, rckPSU_conj_mem_SU hxGU u.2⟩,
      Subgroup.mem_comap.mpr hconjmem, rfl⟩

end CFSG.StandardType.RCKRP
