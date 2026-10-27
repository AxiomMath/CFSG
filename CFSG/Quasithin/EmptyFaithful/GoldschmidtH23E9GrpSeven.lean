module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9GrpOne

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem index_dvd_three_of_odd {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (hE : E9Pre T Mc M Z₁ Z₂ V₁ V₂)
    (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M) (h14 : Lemma15114Concl T Mc M)
    (h113 : Lemma15113Four T Mc M)
    {H : Subgroup G} (hH : H ≤ M ⊓ mZ1516 Mc Z₁) (hodd : Odd (Nat.card H)) :
    (H ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex H ∣ 3 := by
  obtain ⟨hVe, d, hV₁, hV₂⟩ := hE.data
  have h5 := hE.h5
  obtain ⟨x₁, x₂, r⟩ := exists_reflData d h5 h113
  obtain ⟨-, ε₂, -, ⟨hε₂M, hε₂3, hε₂₁, hε₂a, hε₂f, -, -⟩⟩ := exists_torus r hE.e9
  have hC1 := vZ_mc_eq_vE hq hM hCE h5 hE.e9 h15 h19 h14 h113
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hHM : H ≤ M := fun h hh => (hH hh).1
  have hHN : H ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hHM.trans d.hMN
  have hZ₁ := r.z₁_eq hE.z₁ hV₁
  rw [← card_autI_eq hVe hHN]
  have hle : autI hVe H ≤ Subgroup.zpowers ε₂ := by
    intro φ hφ
    obtain ⟨⟨h, hN⟩, hhH, rfl⟩ := (mem_autI hVe).1 hφ
    have hMb : convI hVe ⟨h, hN⟩ ∈ autI hVe M := autI_mono hVe hHM hφ
    have hcenter : h ∈ Subgroup.centralizer ((d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)).map
        (valHomI hVe) : Set G) := by
      rw [← hZ₁]
      exact (hH hhH).2.1
    have hnorm : h ∈ Subgroup.normalizer ((d.S.vEMod x₁ x₂).map (valHomI hVe) : Set G) := by
      rw [← r.vE, ← hC1.2]
      exact (hH hhH).2.2
    have hstab := stab_of_mem_normalizer_map hN hnorm
    have hodd' : Odd (orderOf (convI hVe ⟨h, hN⟩)) := by
      have h1 : orderOf (convI hVe ⟨h, hN⟩) ∣ orderOf (⟨h, hN⟩ :
          Subgroup.normalizer (V154 T Mc M : Set G)) := orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      have h2 : orderOf (⟨h, hhH⟩ : ↥H) ∣ Nat.card H := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h2
      exact Odd.of_dvd_nat (Odd.of_dvd_nat hodd h2) h1
    exact d.S.odd_mem_zpowers_eps hW d.hcard d.hnorm r.x₁_mem.1 r.x₂_mem.1 r.x₁_two r.x₂_two
      hε₂M.1 hε₂3 hε₂₁ hε₂f hε₂a
      ⟨⟨hMb, hstab⟩, (mem_centralizer_map_iff hN).1 hcenter⟩ hodd'
  have := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, hε₂3] at this

end CFSG.Quasithin.E9
