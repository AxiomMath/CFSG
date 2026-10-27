module

public import CFSG.Quasithin.Vol2.Ch10SecC9S49b
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecC9S4b
public import CFSG.Quasithin.Vol2.Ch10SecC9S4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

namespace Conf

variable (c : Conf T L I t w J)
include c

theorem inf_pCoreOf_le_centralizer
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))) :
    pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ⊓ (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))
      ≤ Subgroup.centralizer (VI T L I J w : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({w} : Set G)
  set X := J ⊔ (T ⊓ H)
  have hXH : X ≤ H := sup_le c.J_le inf_le_right
  have hle : pCoreOf 2 H ⊓ X ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => mem_normalizer_inf' (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hx))
        (Subgroup.le_normalizer hx))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have hV := (VI_props c.hyp c.w_mem_V c.isSylowTwoOf_sup hF).1
  exact hle.trans (Subgroup.le_centralizer_iff.mp (hV.trans inf_le_right))

theorem not_three_dvd_autI_solvRad (h36 : Vol2Native.A36CoreForSQTKCat)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w))
    (hcen : ¬ autI hVe (solvRad J) ≤
      Subgroup.centralizer (autI hVe J : Set (MulAut (IntMod (VI T L I J w) hVe)))) :
    ¬ 3 ∣ Nat.card ↥(autI hVe (solvRad J)) := by
  have hK0 := c.inf_pCoreOf_le_centralizer hF
  have hJX : ∀ x ∈ J, x ∈ J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) :=
    fun x hx => Subgroup.mem_sup_left hx
  rcases c.solvRad_dichotomy h36 with hcent | h3
  · exfalso
    apply hcen
    intro ρ hρ
    rw [Subgroup.mem_centralizer_iff]
    intro σ hσ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hVe).1 hρ
    obtain ⟨h, hh, rfl⟩ := (mem_autI hVe).1 hσ
    have hc := hcent g hg h hh
    have hcJ : (g : G) * h * (g : G)⁻¹ * (h : G)⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem (solvRad_le J hg) hh) (J.inv_mem (solvRad_le J hg)))
        (J.inv_mem hh)
    have hcC := hK0 ⟨hc, hJX _ hcJ⟩
    have e : convI hVe (g * h * g⁻¹ * h⁻¹) = 1 := (convI_eq_one_iff hVe _).2 (by simpa using hcC)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
      commutatorElement_eq_one_iff_mul_comm] at e
    exact e.symm
  · intro h3R
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ρ, hρ⟩ := exists_prime_orderOf_dvd_card' 3 h3R
    obtain ⟨g, hg, hgρ⟩ := (mem_autI hVe).1 ρ.2
    set x : ↥J := ⟨g, solvRad_le J hg⟩
    have hxNb : toModO2 c.J_le x ∈ ((solvRad J).subgroupOf J).map (toModO2 c.J_le) :=
      ⟨x, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hk : orderOf (⟨_, hxNb⟩ : ↥(((solvRad J).subgroupOf J).map (toModO2 c.J_le))) ∣
        Nat.card ↥(((solvRad J).subgroupOf J).map (toModO2 c.J_le)) := orderOf_dvd_natCard _
    set k := orderOf (⟨_, hxNb⟩ : ↥(((solvRad J).subgroupOf J).map (toModO2 c.J_le)))
    have h3k : ¬ 3 ∣ k := fun h => h3 (h.trans hk)
    have hxk : toModO2 c.J_le (x ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val (pow_orderOf_eq_one
        (⟨_, hxNb⟩ : ↥(((solvRad J).subgroupOf J).map (toModO2 c.J_le))))
    have hmem := mem_pCoreOf_of_toModO2_eq_one c.J_le hxk
    have hxkJ : ((x ^ k : ↥J) : G) ∈ J := (x ^ k).2
    have hC := hK0 ⟨hmem, hJX _ hxkJ⟩
    have hρk : ρ ^ k = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hgρ, ← map_pow]
      refine (convI_eq_one_iff hVe (g ^ k)).2 ?_
      simpa [x] using hC
    have := orderOf_dvd_of_pow_eq_one hρk
    rw [hρ] at this
    exact h3k this

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
