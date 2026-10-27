module

public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtCore
public import CFSG.RankThree.GF2n.Stroth80.Sec78CommW
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_not_B_le_Z (hc : Ctx M Q Z B) : ¬ B ≤ Z := by
  intro h
  obtain ⟨g, hg⟩ := hc.conj
  exact hc.ne (Subgroup.eq_of_le_of_card_ge h (by rw [hg, card_conjSubgroup]))

theorem sec7ctr_Vgen_of_irred (hirr : Sec7VtIrredStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) :
    Vt M (LB M Q B) B Z t ≤ Z ⊔ ⨆ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ B := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  set U : Subgroup G := Z ⊔ ⨆ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ B with hU
  have hZU : Z ≤ U := le_sup_left
  have hBU : B ≤ U := by
    refine le_sup_of_le_right (le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_)
    rw [conjSubgroup_one]
  have hUV : U ≤ Vt M (LB M Q B) B Z t :=
    sup_le sec39_Z_le_Vt (iSup₂_le fun ρ hρ => le_sup_left.trans (hc.conj_Rt_le_Vt ht hρ))
  have hinv : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ U, r * u * r⁻¹ ∈ U := by
    intro r hr
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have hle : U ≤ Subgroup.comap (MulAut.conj r).toMonoidHom U := by
      refine sup_le (fun z hz => ?_) (iSup₂_le fun ρ hρ x hx => ?_)
      · show r * z * r⁻¹ ∈ U
        exact hZU ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrM) z).mp hz)
      · show r * x * r⁻¹ ∈ U
        rw [mem_conjSubgroup] at hx
        have hrρ : r * ρ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).mul_mem hr hρ
        have hmem : r * x * r⁻¹ ∈ conjSubgroup (r * ρ) B := by
          rw [mem_conjSubgroup]
          have e : (r * ρ)⁻¹ * (r * x * r⁻¹) * (r * ρ) = ρ⁻¹ * x * ρ := by group
          rw [e]
          exact hx
        have hle2 : conjSubgroup (r * ρ) B ≤ U :=
          le_sup_of_le_right (le_iSup₂_of_le (r * ρ) hrρ le_rfl)
        exact hle2 hmem
    exact fun u hu => hle hu
  rcases hirr G M Q Z B hc n t hs U hZU hUV hinv with h | h
  · exact absurd (h ▸ hBU) (sec7ctr_not_B_le_Z hc)
  · exact h ▸ le_rfl

theorem sec7ctr_zt_omega (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) (hirr : Sec7VtIrredStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ s ∈ Z0, s ∉ Q → Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s ∧
        Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hs5 := hs.toSec5
  have hnat : SpNat hc t ∨ OmegaNat hc t := Or.inr hs.omegaNat
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hZL := sec7ctr_Z0_le_LB h51 hc hs5 hnat hr hZ0 hZN
  have hZC := sec7ctr_Z0_le_LC h51 hc hs5 hnat hr hZ0 hZN
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hnotQB := stroth310NotQB_of_34 h34 G M Q Z B hc n t hs5 hnat
  have hchi := stroth_5_2c h34 (stroth310NotQB_of_34 h34) G M Q Z B hc n t hs5 hs.omegaNat _ _ _
    rfl rfl rfl
  exact sec7ctr_zt_core hc hs5 hr hZ0 hZL h35 hnotQB hchi (sec7ctr_Vgen_of_irred hirr hc hs)
    (fun s' hs' w hw => sec7ctr_comm_W_le_Z h52a hirr hc hs hr hZ0 hZN hZL hZC hs' w hw) hsZ hsQ

theorem sec8Zt_of_inputs (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hcomm : Sec8CommWtStatement) (h56 : Stroth56SpStatement) :
    Sec8ZtStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hs5 := hs.toSec5
  have hnat : SpNat hc t ∨ OmegaNat hc t := Or.inl hs.spNat
  have hZN : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  have hZL := sec7ctr_Z0_le_LB h51 hc hs5 hnat hr hZ0 hZN
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hnotQB := stroth310NotQB_of_34 h34 G M Q Z B hc n t hs5 hnat
  have hchi := stroth_5_3e h34 (stroth310NotQB_of_34 h34) G M Q Z B hc n t hs5 hs.spNat _ _ _
    rfl rfl rfl
  have h56' : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z :=
    fun m hm hsub => h56 G M Q Z B hc n t hs m hm hsub
  obtain ⟨hRle, hV⟩ := sec7ctr_zt_core hc hs5 hr hZ0 hZL h35 hnotQB hchi
    (sec7ctr_Vgen_of_56 h56')
    (fun s' hs' w hw => hcomm G M Q Z B hc n t hs Z0 hZ0 s' hs' w hw) hsZ hsQ
  exact ⟨le_antisymm (sec7ctr_Rt_le_of_56 hc h56' hs5.mem hV) hRle, hV⟩

end CFSG.RankThree.GF2n.Stroth80
