module

public import CFSG.Quasithin.Vol2.KGFactJ4M4GenSpec
public import CFSG.Quasithin.Vol2.KGFactJ4GenL52
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GB

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L52

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4
  CFSG.Quasithin.KGC31.J4M4.Gen

theorem mem_of_pow_odd_of_card_eq_two_mul {X : Type*} [Group X] [Finite X] {C N : Subgroup X}
    (hNC : N ≤ C) (hcard : Nat.card ↥C = 2 * Nat.card ↥N) {x : X} (hx : x ∈ C) {n : ℕ}
    (hn : x ^ (2 * n + 1) = 1) : x ∈ N := by
  have hidx : (N.subgroupOf C).index = 2 := by
    have h1 := (N.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  haveI : (N.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
  have h2 : (⟨x, hx⟩ : ↥C) ^ 2 ∈ N.subgroupOf C := by
    have := Subgroup.pow_index_mem (N.subgroupOf C) (⟨x, hx⟩ : ↥C)
    rwa [hidx] at this
  have hxe : (⟨x, hx⟩ : ↥C) = ((⟨x, hx⟩ : ↥C) ^ 2) ^ (n + 1) := by
    apply Subtype.ext
    have : x = x ^ (2 * (n + 1)) := by
      calc x = x ^ (2 * n + 1) * x := by rw [hn, one_mul]
        _ = x ^ (2 * n + 1 + 1) := (pow_succ x (2 * n + 1)).symm
        _ = x ^ (2 * (n + 1)) := by rw [mul_add, mul_one]
    simpa [pow_mul] using this
  have h3 : (⟨x, hx⟩ : ↥C) ∈ N.subgroupOf C := by
    rw [hxe]
    exact pow_mem h2 _
  exact h3

theorem card_centralizer_eq_two_mul_perfectCore
    {z : J}
    (hz : ∃ g : J, z = g * CFSG.Quasithin.J4Loc.z0 * g⁻¹) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set J)) =
      2 * Nat.card ↥(perfectCore (Subgroup.centralizer ({z} : Set J))) := by
  obtain ⟨g, hg⟩ := hz
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  set φ := (MulAut.conj g).toMonoidHom with hφ
  have h1 : Subgroup.centralizer ({z} : Set J) =
      (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map φ := by
    rw [hφ, CFSG.Quasithin.H13.J4.map_centralizer_singleton, MulAut.conj_apply, hg]
  have hB : perfectCore (Subgroup.centralizer ({z} : Set J)) = J4M2.B0grp.map φ := by
    rw [h1, ← map_perfectCore, show Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J) =
      J4M2.M2 from rfl, JM.perfectCore_M2 hF]
  have hcz : Nat.card ↥(Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)) =
      21799895040 := CFSG.Sporadic.J4.QT2.card_centralizer_z0 hF
  rw [hB, h1, hφ, card_map_conj, card_map_conj, JM.card_B0grp hF, hcz]

theorem c_mem_perfectCore
    (hz : ∃ g : J, z1Elt = g * CFSG.Quasithin.J4Loc.z0 * g⁻¹) :
    cElt ∈ perfectCore (Subgroup.centralizer ({z1Elt} : Set J)) := by
  obtain ⟨-, hc11, hcz, -, -⟩ := chkGen_facts
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hn : cElt ^ (2 * 5 + 1) = 1 := by
    rw [show 2 * 5 + 1 = 11 from rfl]
    exact hc11
  refine mem_of_pow_odd_of_card_eq_two_mul (perfectCore_le _)
    (card_centralizer_eq_two_mul_perfectCore hz) ?_ hn
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcz

end L52

end CFSG.Quasithin.H13.Ch4.G443J4

end
