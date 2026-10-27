module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4EA5
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H] [Finite H]

theorem e34_eq_one_of_two_three {v : H} (h2 : ∃ j : ℕ, v ^ (2 ^ j) = 1)
    (h3 : ∃ k : ℕ, v ^ (3 ^ k) = 1) : v = 1 := by
  obtain ⟨j, hj⟩ := h2
  obtain ⟨k, hk⟩ := h3
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) :=
    Nat.Coprime.pow _ _ (by decide)
  have := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj)
    (orderOf_dvd_of_pow_eq_one hk)
  exact orderOf_eq_one_iff.mp this

theorem e34_layer_normal : (layer H).Normal := by
  haveI := LocalCores.layer_characteristic (G := H)
  infer_instance

theorem e34_layer_inv (β : MulAut H) {x : H} (hx : x ∈ layer H) : β x ∈ layer H := by
  have h := WholeGroup.layer_map_mulEquiv β
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem e34_comp_ne_bot {C : Subgroup H} (hC : IsComponent C) : C ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := hC.1.2.2
  apply hab
  subst h
  exact Subsingleton.elim _ _

theorem e34_center_layer_trivial (hO : pPrimeCore 3 H = ⊥)
    (hS : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S) {z : H} (hz : z ∈ layer H)
    (hc : ∀ w ∈ layer H, w * z = z * w) : z = 1 := by
  have hzm : z ∈ (Subgroup.center (layer H)).map (layer H).subtype :=
    (LocalCores.mem_map_center_iff _).mpr ⟨hz, Subgroup.mem_centralizer_iff.mpr hc⟩
  rw [(LocalCores.layer_center (G := H)).1] at hzm
  have hbot : (⨆ K : LocalCores.ComponentIndex H, (Subgroup.center K.1).map K.1.subtype) = ⊥ := by
    refine iSup_eq_bot.mpr fun K => ?_
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    exact e34_comp_center_trivial hO hS K.2 w.2 fun u hu =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hw) ⟨u, hu⟩)
  rw [hbot] at hzm
  exact hzm

variable {β : MulAut H} {Z K : Subgroup H} {z₀ : H}

theorem e34_layer_ne_bot (hd : FF79APData β Z K z₀) : layer H ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hE
  obtain ⟨e⟩ := hd.K_a5
  obtain ⟨x, hxK, hx3, V, hVK, hV2, hV1, -⟩ := e34_a5_data e
  have hgf : generalizedFitting H = pCore 3 H := by
    rw [generalizedFitting, hE, sup_bot_eq, Fitting_eq_pcore H 3 hd.core]
  have hKR : K ≤ pCore 3 H := by
    intro k hk
    rw [← hgf]
    apply centralizer_generalizedFitting_le H
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hgf] at hg
    exact hd.K_cen_R g hg k hk
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hV1)
  apply hv1
  refine Subtype.ext (e34_eq_one_of_two_three ?_ ?_)
  · obtain ⟨j, hj⟩ := hV2 v
    exact ⟨j, congrArg Subtype.val hj⟩
  · obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 3) (G := H)) ⟨v, hKR (hVK v.2)⟩
    exact ⟨k, congrArg Subtype.val hk⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
