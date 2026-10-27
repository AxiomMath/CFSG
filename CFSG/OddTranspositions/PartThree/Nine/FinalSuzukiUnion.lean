module

public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzukiInvolutions

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem mem_sup_or_mem_sup_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {h : G} (hhz : Commute (h * z * h⁻¹) z)
    (hhEU : ∀ a ∈ U, ∀ w ∈ U, h * z * h⁻¹ ≠ g * a * g⁻¹ * w) {v : G}
    (hvV : v ∈ U.map (MulAut.conj g).toMonoidHom ⊔
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)))
    (hv2 : v * v = 1) :
    v ∈ U.map (MulAut.conj g).toMonoidHom ⊔ U ∨ v ∈ U.map (MulAut.conj h).toMonoidHom ⊔ U := by
  obtain ⟨a, haU, r, hr, rfl⟩ :=
    (hU.mem_sup_iff_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he).mp hvV
  by_cases hrU : r ∈ U
  ·
    left
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ haU) hrU
  ·
    right
    obtain ⟨b, hbU, -, w, hwU, a', ha'U, heq⟩ :=
      hU.exists_conj_mul_eq_of_sz hH h3 h4 h5 hQ h7 hm eH hUn hzU hz1 hgz he hhz hhEU hr hrU
    have hsq : g * a' * g⁻¹ * r * (g * a' * g⁻¹ * r) = 1 := by
      rw [← heq]
      exact hU.conj_mul_mul_self_eq_one hH h3 h5 hQ h7 hzU hz1 hhz hbU hwU
    have haa := hU.eq_of_mul_self_eq_one_of_sz hH h3 h5 hQ h7 hm eH hUn hzU hz1 hgz he
      haU ha'U hr hrU hv2 hsq
    have hbF : h * b * h⁻¹ ∈ U.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hbU
    rw [haa, ← heq]
    exact Subgroup.mul_mem_sup hbF hwU

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
