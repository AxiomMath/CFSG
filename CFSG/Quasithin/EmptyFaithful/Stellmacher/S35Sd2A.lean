module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10A
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Sd2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem pdCrit (hS : Sit H M S) : S35.II.PDCrit H M := by
  intro β α' hp
  have hvβ := hp.vδ
  have hex : ∃ μ ∈ nbrs β, ¬ Zv μ ≤ Qv α' := by
    by_contra h
    push Not at h
    exact hp.not_le (iSup₂_le fun μ hμ => h μ hμ)
  obtain ⟨μ, hμ, hn⟩ := hex
  have hvμ : vtype μ = true := Std.vtype_nbr_S5 hvβ hμ
  have h1 : dist α' μ ≤ dist α' β + 1 := dist_le_dist_nbr hμ α'
  have h2 : dist α' β = dist β α' := CosetGeom.dist_comm _ _
  have h3 : dist α' μ = dist μ α' := CosetGeom.dist_comm _ _
  have hb := hp.dist_eq
  have hge : bMin H M ≤ dist μ α' := by
    by_contra hlt
    push Not at hlt
    exact hn (Std.Zv_le_Qv_dist hlt)
  exact ⟨μ, hvμ, ⟨hμ.symm, hS.glob.crit μ hvμ, by omega, by omega, hn⟩⟩

theorem noTrivialAct (hS : Sit H M S) : S35.II.NoTrivialAct H M := by
  intro β hβ x hx hc
  by_contra hxQ
  exact S35.E10.not_centralizes_Wb hS hβ hx hxQ fun w hw => hc w hw

theorem Wb_sq_eq_one (hS : Sit H M S) (h7 : 7 ≤ bMin H M) (β : Geo H M) :
    ∀ x ∈ Wb β, x ^ 2 = 1 := by
  have hcomm := Std.Wb_comm_of_b7 hS h7 β
  let K : Subgroup G :=
    { carrier := {x | x ∈ Wb β ∧ x ^ 2 = 1}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hcomm a ha b hb).mul_pow, ha2, hb2, mul_one]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [inv_pow, ha2, inv_one] }
  have hK : Wb β ≤ K := Std.Wb_le fun ρ hρ a ha =>
    ⟨Std.Vn_le_Wb hρ ha, (Std.Vn_isElemAbelian hS ρ).2 a ha⟩
  exact fun x hx => (hK hx).2

theorem wbSec7 (hS : Sit H M S) : S35.II.WbSec7 H M := by
  intro h7 β hβ
  refine ⟨Std.Vn_le_Wb_self hS hβ, Std.Wb_normal β, Std.Vn_normal β, ?_, ?_⟩
  · intro x hx y hy
    have : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [Std.Wb_comm_of_b7 hS h7 β x hx y hy]
      group
    rw [this]
    exact one_mem _
  · intro x hx
    rw [Wb_sq_eq_one hS h7 β x hx]
    exact one_mem _

end S35.Sd2

end F53.Stellmacher

end CFSG.Quasithin
