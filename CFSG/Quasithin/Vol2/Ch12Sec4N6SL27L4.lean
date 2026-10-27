module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27Tr
public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27Coset

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (one_mul 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = a⁻¹ * b⁻¹ := (hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  have hx' : x ∈ S := sup_le hAS hBS hx
  exact hx'

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem mem_E_of_comm_a {a : G} (haL1 : a ∈ c.L1) (ha3 : a * a * a = 1)
    (haV : a ∉ Subgroup.centralizer (V : Set G)) {w : G} (hw : w ∈ V) (hwa : a * w = w * a) :
    w ∈ E := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  have haCLE := c.L1_le haL1
  have haN := c.f.normalizes haCLE.1
  obtain ⟨γa, hγa, hγac, -⟩ := c.image_CLE D haCLE
  have hγa3 : γa * γa * γa = 1 := by
    apply D.rho_injective
    rw [map_mul, map_mul, hγa, ← map_mul, ← map_mul, map_one]
    exact A4.conjAct_eq_one_iff.2 (by
      show a * a * a ∈ Subgroup.centralizer (V : Set G)
      rw [ha3]; exact Subgroup.one_mem _)
  have hγa1 : γa ≠ 1 := fun h => haV (A4.conjAct_eq_one_iff.1 (by rw [← hγa, h, map_one]))
  have hmem := (c.mem_E_iff D ⟨w, hw⟩).2
  apply hmem
  apply three_fix _ (c.cv_ne D) γa hγac hγa3 hγa1
  rw [← bv_rho]
  congr 1
  apply Subtype.ext
  rw [hγa, conjAct_coe]
  simp only
  rw [hwa, mul_inv_cancel_right]

theorem exists_E_mul_D (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    {k : G} (hk : k ∈ c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G)) :
    ∃ e ∈ E, ∃ d ∈ T ⊓ Subgroup.centralizer (L : Set G), k = e * d := by
  obtain ⟨a, haL1, ha3, haV⟩ := c.exists_a
  have hkQ : k ∈ pCoreOf 2 (L ⊔ T) := c.inf_centralizer_L1_le_Q hk
  have hkC : k ∈ Subgroup.centralizer (c.L1 : Set G) := hk.2
  have hkV : k ∈ Subgroup.centralizer (V : Set G) := by
    have h := hkQ
    rw [c.Q] at h
    exact h.2
  have hPab := c.pCore_comm hcomm
  have hVD : ∀ a ∈ V, ∀ b ∈ T ⊓ Subgroup.centralizer (L : Set G), a * b = b * a := by
    intro a ha b hb
    have hbQ : b ∈ pCoreOf 2 (L ⊔ T) := c.CTL_le_Q hb
    rw [c.Q] at hbQ
    exact (Subgroup.mem_centralizer_iff.1 hbQ.2) a ha
  have hsub : c.L1 ⊔ V ≤ Subgroup.centralizer ({k} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun w hw => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.1 hkC) l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.1 hkV) w hw).symm
  have hpk : ∀ p ∈ pCoreOf 2 L, p * k = k * p := by
    intro p hp
    have hpQ : p ∈ pCoreOf 2 (L ⊔ T) := c.pCore_le_Q hp
    have hsup := c.mem_sup_of_commute_pCore hcomm hpQ (fun q hq => hPab q hq p hp)
    obtain ⟨w, hw, d, hd, hpwd⟩ := mem_sup_of_commute hVD hsup
    have hdP : d ∈ pCoreOf 2 L := by
      have e : d = w⁻¹ * p := by rw [hpwd]; group
      rw [e]
      exact (pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem (c.V_le_pCore hw)) hp
    have hdL1 : d ∈ c.L1 ⊔ V := c.mem_L1_sup_of_central hcomm hdP (Subgroup.mem_inf.1 hd).2
    have hkd : k * d = d * k := Subgroup.mem_centralizer_iff.1 (hsub hdL1) k (Set.mem_singleton k)
    have hwk : w * k = k * w := (Subgroup.mem_centralizer_iff.1 hkV) w hw
    rw [hpwd]
    calc (w * d) * k = w * (d * k) := by group
      _ = w * (k * d) := by rw [← hkd]
      _ = (w * k) * d := by group
      _ = (k * w) * d := by rw [hwk]
      _ = k * (w * d) := by group
  have hk_sup := c.mem_sup_of_commute_pCore hcomm hkQ hpk
  obtain ⟨w, hw, d, hd, hkwd⟩ := mem_sup_of_commute hVD hk_sup
  have hdC : d ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.1 hd).2
  have hak : Commute a k := (Subgroup.mem_centralizer_iff.1 hkC) a haL1
  have had : Commute a d := (Subgroup.mem_centralizer_iff.1 hdC) a (c.L1_le haL1).1
  have hw_eq : w = k * d⁻¹ := by rw [hkwd]; group
  have haw : Commute a w := by
    rw [hw_eq]
    exact hak.mul_right had.inv_right
  have hwE : w ∈ E := c.mem_E_of_comm_a haL1 ha3 haV hw haw
  exact ⟨w, hwE, d, hd, hkwd⟩

end Ctx

end N1246

end CFSG.Quasithin.H13
