module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TBorelBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3t_eq_one_of_alt9 {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 9))
    {r : ℕ} (hr : r.Prime) (hr7 : 7 < r) {k : ℕ} {w : X} (hw : w ^ (r ^ k) = 1) :
    w = 1 := by
  have h9 : 9 < r := by
    by_contra h
    have h8 : r = 8 ∨ r = 9 := by omega
    rcases h8 with rfl | rfl <;> norm_num at hr
  have hcop : Nat.Coprime (r ^ k) (Nat.factorial 9) :=
    (hr.coprime_factorial_of_lt h9).pow_left k
  have h1 : orderOf (e w) ∣ r ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hw, map_one])
  have h2 : orderOf (e w) ∣ Nat.factorial 9 := by
    have h := orderOf_dvd_natCard (e w)
    rw [nat_card_alternatingGroup, Nat.card_fin] at h
    exact h.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by norm_num)))
  exact (e.map_eq_one_iff).1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

theorem uc22r3t_mem_center_of_layer_alt9 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.layer Y = ⊤)
    (hC : ∀ C : CFSG.LocalCores.ComponentIndex Y,
      Nonempty ((↥C.1 ⧸ Subgroup.center ↥C.1) ≃* alternatingGroup (Fin 9)))
    {r : ℕ} (hr : r.Prime) (hr7 : 7 < r) {k : ℕ} {u : Y} (hu : u ^ (r ^ k) = 1) :
    u ∈ Subgroup.center Y := by
  have huE : u ∈ CFSG.layer Y := by
    rw [hY]
    exact mem_top u
  set ū : ↥(CFSG.layer Y) ⧸ Subgroup.center ↥(CFSG.layer Y) :=
    ((⟨u, huE⟩ : ↥(CFSG.layer Y)) : ↥(CFSG.layer Y) ⧸ Subgroup.center ↥(CFSG.layer Y))
    with hū
  have hsub : (⟨u, huE⟩ : ↥(CFSG.layer Y)) ^ (r ^ k) = 1 := Subtype.ext (by simpa using hu)
  have hūp : ū ^ (r ^ k) = 1 := by
    rw [hū, ← QuotientGroup.mk_pow, hsub, QuotientGroup.mk_one]
  have h1 : (CFSG.LocalCores.layerCentralQuotientEquiv Y).symm ū ^ (r ^ k) = 1 := by
    rw [← map_pow, hūp, map_one]
  have h2 : (CFSG.LocalCores.layerCentralQuotientEquiv Y).symm ū = 1 := by
    funext C
    obtain ⟨eA⟩ := hC C
    exact uc22r3t_eq_one_of_alt9 eA hr hr7 (by simpa [Pi.pow_apply] using congrFun h1 C)
  have h3 : ū = 1 := by
    have h := congrArg (CFSG.LocalCores.layerCentralQuotientEquiv Y) h2
    simpa using h
  have h4 : (⟨u, huE⟩ : ↥(CFSG.layer Y)) ∈ Subgroup.center ↥(CFSG.layer Y) := by
    refine (QuotientGroup.eq_one_iff (⟨u, huE⟩ : ↥(CFSG.layer Y))).1 ?_
    rwa [← hū]
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ CFSG.layer Y := by
    rw [hY]
    exact mem_top g
  have h := Subgroup.mem_center_iff.1 h4 ⟨g, hg⟩
  simpa using congrArg Subtype.val h

theorem uc22r3t_mk_mem_center_of_alt9 (D : Data G) {K₁ K : Subgroup G}
    (hK₁ : K₁ ∈ calL D.T D.M) (hK : K ∈ calC K₁) (hLK : K₁ = uc22p20bOrb D.T K)
    (hA : Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* alternatingGroup (Fin 9)))
    {y : G} (hy : y ∈ K₁) {r : ℕ} (hr : r.Prime) (hr7 : 7 < r) {k : ℕ}
    (hyo : orderOf y = r ^ k) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⟨y, hy⟩ ∈ Subgroup.center (Bar2 K₁) := by
  obtain ⟨eA⟩ := hA
  have hy1 : (⟨y, hy⟩ : ↥K₁) ^ (r ^ k) = 1 := by
    refine Subtype.ext ?_
    simpa [hyo] using pow_orderOf_eq_one y
  refine uc22r3t_mem_center_of_layer_alt9 (Y := Bar2 K₁) (k := k)
    (uc22r3t_layer_bar2_eq_top D hK₁) (fun C => ?_) hr hr7 ?_
  · obtain ⟨e⟩ := uc22r3t_component_equiv D hK₁ hK hLK C
    obtain ⟨f⟩ := uc22p20p_quotCenter_equiv e
    exact ⟨f.symm.trans eA⟩
  · rw [← map_pow, hy1, map_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22
