module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.StandardType.OrthTorus

open CFSG CFSG.Assembly CFSG.RankThree.Classical2 NbrOrth

theorem OrthFrameCore.pow_rank_succ_le_card_bstar
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (Φ : OrthFrameCore p Bs L) (hZ : Subgroup.center L = ⊥) :
    p ^ (Φ.r + 1) ≤ Nat.card Bs := by
  classical
  obtain ⟨hp, hBs, hxBs, hxL, -⟩ := hcfg.tableB_facts
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let τ := Φ.Δ.τΩ Φ.hA
  let ξ := Φ.ψ.comp τ
  let E : Subgroup G := ξ.range
  have hξinj : Function.Injective ξ :=
    Φ.hinj.comp (tbjA_tauOmega_injective Φ.Δ Φ.hA)
  have hEc : Nat.card E = p ^ Φ.r := by
    have h := Nat.card_congr (Equiv.ofInjective ξ hξinj).symm
    change Nat.card E = Nat.card (Fin Φ.r → Multiplicative (ZMod p)) at h
    rw [h]
    simp [Nat.card_eq_fintype_card]
  have hEL : E ≤ L := by
    rintro _ ⟨f, rfl⟩
    exact (le_of_eq Φ.hrange) (MonoidHom.mem_range.mpr ⟨τ f, rfl⟩)
  have hEB : E ≤ Bs := by
    rintro _ ⟨f, rfl⟩
    apply hcfg.2.1.2.2.2
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp
        ((le_of_eq Φ.Δ.τ_range.symm) (Φ.hβA ⟨b, hb⟩))
      have hβg : Φ.β ⟨b, hb⟩ = τ g := Subtype.ext hg.symm
      have hcomm : Φ.β ⟨b, hb⟩ * τ f * (Φ.β ⟨b, hb⟩)⁻¹ = τ f := by
        rw [hβg]
        calc
          τ g * τ f * (τ g)⁻¹ = τ (g * f * g⁻¹) := by simp only [map_mul, map_inv]
          _ = τ f := by rw [mul_right_comm, mul_inv_cancel, one_mul]
      have hc := Φ.hcompat ⟨b, hb⟩ (τ f)
      rw [hcomm] at hc
      change ξ f = b * ξ f * b⁻¹ at hc
      simpa [mul_assoc] using congrArg (fun a : G => a * b) hc.symm
    · have hfp : f ^ p = 1 := by
        ext i
        change p • Multiplicative.toAdd (f i) = 0
        simp [nsmul_eq_mul]
      change ξ f ^ p = 1
      rw [← map_pow, hfp, map_one]
  have hZpL : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hcfg.data_L.1
  have hLcen : L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    let aL : L := ⟨a, ha.1⟩
    have haZ : aL ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr
      fun u => Subtype.ext (Subgroup.mem_centralizer_iff.mp ha.2 u u.2)
    rw [hZ, Subgroup.mem_bot] at haZ
    exact congrArg Subtype.val haZ
  have hdisj : Subgroup.zpowers x ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hm : a ∈ L ⊓ Subgroup.centralizer (L : Set G) := ⟨hEL ha.2, hZpL ha.1⟩
    rwa [hLcen] at hm
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ e ∈ E, Commute a e :=
    fun a ha e he => (show Commute e a from
      Subgroup.mem_centralizer_iff.mp (hZpL ha) e (hEL he)).symm
  have hc := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers x) E hcomm hdisj
  have hxcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hcfg.data_L.2.1]
  calc
    p ^ (Φ.r + 1) = p * p ^ Φ.r := by rw [pow_succ, Nat.mul_comm]
    _ = Nat.card (Subgroup.zpowers x ⊔ E : Subgroup G) := by rw [hc, hxcard, hEc]
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le (sup_le (Subgroup.zpowers_le.mpr hxBs) hEB)

end CFSG.StandardType.OrthTorus

end
