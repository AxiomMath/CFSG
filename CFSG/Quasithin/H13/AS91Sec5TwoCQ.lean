module

public import CFSG.Quasithin.H13.AS91Sec5TwoCRed
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Involutions

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem E_sq {e : G} (he : e ∈ c.E) : e * e = 1 := by
  have := c.E_elem.2 e he
  simpa [pow_two] using this

theorem pow_three_mem_Q_of_mem_sup_X {u : G} (hu : u ∈ Q z ⊔ c.X) : u ^ 3 ∈ Q z := by
  have huH : u ∈ H z :=
    (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 (H z)) c.X_le) hu
  have hQnorm : ∀ h ∈ H z, ∀ q ∈ Q z, h * q * h⁻¹ ∈ Q z := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H z) hh) q).mp hq
  have hQn : ((Q z).subgroupOf (H z)).Normal := by
    have hN : (Q z).subgroupOf (H z) = CFSG.Open.pCore 2 (H z) :=
      Subgroup.comap_map_eq_self_of_injective (H z).subtype_injective _
    rw [hN]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have huH' : (⟨u, huH⟩ : ↥(H z)) ∈
      (Q z).subgroupOf (H z) ⊔ (c.X).subgroupOf (H z) := by
    rw [← Subgroup.subgroupOf_sup (A := Q z) (A' := c.X) (B := H z)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (H z)) c.X_le]
    exact Subgroup.mem_subgroupOf.mpr hu
  letI : ((Q z).subgroupOf (H z)).Normal := hQn
  obtain ⟨q, hq, x, hx, hqx⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (Q z).subgroupOf (H z))
      (t := (c.X).subgroupOf (H z))).mp huH'
  have hqG : (q : G) ∈ Q z := Subgroup.mem_subgroupOf.mp hq
  have hxG : (x : G) ∈ c.X := Subgroup.mem_subgroupOf.mp hx
  have hqxG : (q : G) * (x : G) = u := by
    have := congrArg Subtype.val hqx
    simpa using this
  have hx3 : (x : G) ^ 3 = 1 := by
    have hx' : (⟨(x : G), hxG⟩ : ↥c.X) ^ 3 = 1 := by
      rw [← c.card_X]
      exact pow_card_eq_one'
    have := congrArg Subtype.val hx'
    simpa using this
  have hmem1 : (x : G) * (q : G) * (x : G)⁻¹ ∈ Q z :=
    hQnorm x (c.X_le hxG) q hqG
  have hmem2 : (x : G) ^ 2 * (q : G) * ((x : G) ^ 2)⁻¹ ∈ Q z :=
    hQnorm ((x : G) ^ 2) (c.X_le (pow_mem hxG 2)) q hqG
  have hmem : ((q : G) * (x : G)) ^ 3 ∈ Q z := by
    have e : ((q : G) * (x : G)) ^ 3 =
        (q : G) * ((x : G) * (q : G) * (x : G)⁻¹) *
          ((x : G) ^ 2 * (q : G) * ((x : G) ^ 2)⁻¹) * (x : G) ^ 3 := by
      rw [pow_succ, pow_succ, pow_one]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hqG hmem1) hmem2) (by rw [hx3]; exact one_mem _)
  rwa [← hqxG]

theorem mem_Q_of_mem_sup_X_of_sq_eq_one {u : G} (hu : u ∈ Q z ⊔ c.X) (hu2 : u * u = 1) :
    u ∈ Q z := by
  have h3 := pow_three_mem_Q_of_mem_sup_X c hu
  have hu3 : u ^ 3 = u := by
    calc u ^ 3 = u ^ 2 * u := by rw [pow_succ]
      _ = u := by rw [pow_two, hu2, one_mul]
  rwa [hu3] at h3

theorem mem_Q_of_mem_sup_X_of_orderOf_eq_five {u : G} (hu : u ∈ Q z ⊔ c.X)
    (h5 : orderOf u = 5) : u ∈ Q z := by
  have h3 := pow_three_mem_Q_of_mem_sup_X c hu
  have hu5 : u ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one u
  have hu6 : u ^ 6 = u := by
    rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, hu5, one_mul]
  have hueq : u = (u ^ 3) ^ 2 := by
    calc u = u ^ 6 := hu6.symm
      _ = (u ^ 3) ^ 2 := by rw [← pow_mul]
  rw [hueq]
  exact pow_mem h3 2

theorem not_mem_Q_of_orderOf_eq_five {u : G} (h5 : orderOf u = 5) : u ∉ Q z := by
  intro hu
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H z)))
      (⟨u, hu⟩ : ↥(Q z))
  have hord : orderOf u = 2 ^ n := (Subgroup.orderOf_coe ⟨u, hu⟩).trans hn
  rw [h5] at hord
  have hn : n ≠ 0 := by
    intro h0
    rw [h0] at hord
    norm_num at hord
  have h2dvd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have h25 : 2 ∣ 5 := hord.symm ▸ h2dvd
  omega

theorem not_commute_of_orderOf_eq_five
    (N : Subgroup G) (π : ↥N →* J4.M22)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X)
    (hcomm : ∀ h ∈ H z, (∀ x ∈ c.X, h * x * h⁻¹ * x⁻¹ ∈ Q z) → h ∈ N)
    (hodd : ∀ h ∈ H z, Odd (orderOf h) → h ∈ N)
    {w : G} (hw : w ∈ c.E) (hwQ : w ∉ Q z) {a : G} (ha : a ∈ H z) (ha5 : orderOf a = 5) :
    ¬ Commute a w := by
  intro hcommute
  have hwH : w ∈ H z := c.E_le_G3 hw
  have hwG13 : w ∈ c.G13 := c.E_le hw
  have hw2 : w * w = 1 := E_sq c hw
  have hwN : w ∈ N := by
    refine hcomm w hwH ?_
    intro x hx
    have hxG13 : x ∈ c.G13 := c.QX_le (Subgroup.mem_sup_right hx)
    have hxw : x * w * x⁻¹ ∈ c.E := c.E_normal x hxG13 w hw
    have hE : w * x * w⁻¹ * x⁻¹ ∈ c.E := by
      have := mul_mem hw (inv_mem hxw)
      simpa [mul_assoc] using this
    have hQX : w * x * w⁻¹ * x⁻¹ ∈ Q z ⊔ c.X :=
      mul_mem (c.QX_normal w hwH x (Subgroup.mem_sup_right hx))
        (inv_mem (Subgroup.mem_sup_right hx))
    exact mem_Q_of_mem_sup_X_of_sq_eq_one c hQX (by
      have := c.E_elem.2 _ hE
      simpa [pow_two] using this)
  have haN : a ∈ N := hodd a ha (by rw [ha5]; norm_num)
  have hπa_ne : π ⟨a, haN⟩ ≠ 1 := by
    intro h1
    have haQX : a ∈ Q z ⊔ c.X := (hker ⟨a, haN⟩).mp h1
    exact not_mem_Q_of_orderOf_eq_five ha5
      (mem_Q_of_mem_sup_X_of_orderOf_eq_five c haQX ha5)
  have hπw_ne : π ⟨w, hwN⟩ ≠ 1 := by
    intro h1
    have hwQX : w ∈ Q z ⊔ c.X := (hker ⟨w, hwN⟩).mp h1
    exact hwQ (mem_Q_of_mem_sup_X_of_sq_eq_one c hwQX hw2)
  have hπa5 : orderOf (π ⟨a, haN⟩) = 5 := by
    have h := orderOf_map_dvd π (⟨a, haN⟩ : ↥N)
    have hN : orderOf (⟨a, haN⟩ : ↥N) = 5 := by
      rw [Subgroup.orderOf_mk a haN, ha5]
    rw [hN] at h
    rcases (Nat.dvd_prime Nat.prime_five).mp h with h1 | h5
    · exact absurd h1 (fun h => hπa_ne (orderOf_eq_one_iff.mp h))
    · exact h5
  have hπw2 : orderOf (π ⟨w, hwN⟩) = 2 := by
    have h := orderOf_map_dvd π (⟨w, hwN⟩ : ↥N)
    have hN : orderOf (⟨w, hwN⟩ : ↥N) = 2 := by
      rw [Subgroup.orderOf_mk w hwN]
      have hd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hw2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd h1 (fun h => hwQ (by rw [orderOf_eq_one_iff.mp h]; exact one_mem _))
      · exact h2
    rw [hN] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact absurd h1 (fun h => hπw_ne (orderOf_eq_one_iff.mp h))
    · exact h2
  have hπcomm : Commute (π ⟨a, haN⟩) (π ⟨w, hwN⟩) := by
    have hsub : (⟨a, haN⟩ : ↥N) * ⟨w, hwN⟩ = ⟨w, hwN⟩ * ⟨a, haN⟩ :=
      Subtype.ext hcommute
    calc π ⟨a, haN⟩ * π ⟨w, hwN⟩ = π ((⟨a, haN⟩ : ↥N) * ⟨w, hwN⟩) :=
          (map_mul π _ _).symm
      _ = π (⟨w, hwN⟩ * ⟨a, haN⟩) := by rw [hsub]
      _ = π ⟨w, hwN⟩ * π ⟨a, haN⟩ := map_mul π _ _
  have hmem : π ⟨a, haN⟩ ∈ Subgroup.centralizer ({π ⟨w, hwN⟩} : Set J4.M22) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hπcomm.symm
  have hzle : Subgroup.zpowers (π ⟨a, haN⟩) ≤
      Subgroup.centralizer ({π ⟨w, hwN⟩} : Set J4.M22) :=
    Subgroup.zpowers_le.mpr hmem
  have hcard : Nat.card (Subgroup.zpowers (π ⟨a, haN⟩)) = 5 := by
    rw [Nat.card_zpowers, hπa5]
  have hdvd5 : 5 ∣ Nat.card (Subgroup.centralizer ({π ⟨w, hwN⟩} : Set J4.M22)) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hzle
  have h384 : Nat.card (Subgroup.centralizer ({π ⟨w, hwN⟩} : Set J4.M22)) = 384 :=
    CFSG.ComponentClassification.WittDesign.card_centralizer_involution hπw2
  rw [h384] at hdvd5
  norm_num at hdvd5

theorem exists_orderOf_eq_five_commute {g : G} (hg : g ∈ c.G2)
    (hgx : g • c.x0 ≠ c.x0) :
    ∃ a ∈ H z, orderOf a = 5 ∧
      ∀ w ∈ c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E, Commute a w := by
  classical
  let A : Subgroup G := c.E ⊔ c.E.map (MulAut.conj g).toMonoidHom
  have hEg_le_G2 : c.E.map (MulAut.conj g).toMonoidHom ≤ c.G2 := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    exact mul_mem (mul_mem hg (c.E_le_G2 he)) (inv_mem hg)
  have hA_G2 : A ≤ c.G2 := sup_le c.E_le_G2 hEg_le_G2
  have hEg_le_H : c.E.map (MulAut.conj g).toMonoidHom ≤ H z := by
    intro y hy
    obtain ⟨e, he, hye⟩ := Subgroup.mem_map.mp hy
    rw [← hye]
    change (MulAut.conj g).toMonoidHom e ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    change z * (g * e * g⁻¹) = (g * e * g⁻¹) * z
    have hzg : g⁻¹ * z * g ∈ c.Z := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) z).mp c.z_mem_Z
      simpa using this
    have hzgE : g⁻¹ * z * g ∈ c.E := c.Z_le_E hzg
    have hec : e * (g⁻¹ * z * g) = (g⁻¹ * z * g) * e := c.E_comm he hzgE
    calc z * (g * e * g⁻¹) = g * ((g⁻¹ * z * g) * e) * g⁻¹ := by group
      _ = g * (e * (g⁻¹ * z * g)) * g⁻¹ := by rw [hec]
      _ = (g * e * g⁻¹) * z := by group
  have hA_H : A ≤ H z := sup_le c.E_le_G3 hEg_le_H
  have hcentral : ∀ a ∈ A, ∀ w ∈ c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E, Commute a w := by
    intro a ha w hw
    have hwE : w ∈ c.E := hw.2
    have hwEg : w ∈ c.E.map (MulAut.conj g).toMonoidHom := hw.1
    have hcent : A ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sup_le ?_ ?_
      · intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        rw [Set.mem_singleton_iff] at hv
        rw [hv]
        exact (c.E_comm he hwE).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        rw [Set.mem_singleton_iff] at hv
        rw [hv]
        obtain ⟨e, he, hye⟩ := Subgroup.mem_map.mp hy
        obtain ⟨e', he', hwe⟩ := Subgroup.mem_map.mp hwEg
        rw [← hye, ← hwe]
        change (g * e' * g⁻¹) * (g * e * g⁻¹) = (g * e * g⁻¹) * (g * e' * g⁻¹)
        have hcomm' : e * e' = e' * e := c.E_comm he he'
        calc (g * e' * g⁻¹) * (g * e * g⁻¹) = g * (e' * e) * g⁻¹ := by group
          _ = g * (e * e') * g⁻¹ := by rw [hcomm']
          _ = (g * e * g⁻¹) * (g * e' * g⁻¹) := by group
    exact ((Subgroup.mem_centralizer_iff.mp (hcent ha) w (Set.mem_singleton w))).symm
  have horbit_sub : MulAction.orbit ↥A c.x0 ⊆ c.ptsL := by
    rintro p ⟨a, rfl⟩
    exact smul_mem_objOf_base (A := c.G1) (B := c.G2) (hA_G2 a.2) c.x0_mem_ptsL
  have hptsL_sub : c.ptsL ⊆ MulAction.orbit ↥A c.x0 := by
    intro p hp
    by_cases hpx : p = c.x0
    · rw [hpx]
      exact MulAction.mem_orbit_iff.mpr ⟨1, one_smul _ _⟩
    by_cases hpy : p = g • c.x0
    · rw [hpy]
      have hy : g • c.x0 ∈ c.ptsL :=
        smul_mem_objOf_base (A := c.G1) (B := c.G2) hg c.x0_mem_ptsL
      have hfin : ({c.x0, g • c.x0} : Set (G ⧸ c.G1)).Finite := Set.toFinite _
      have hlt : ({c.x0, g • c.x0} : Set (G ⧸ c.G1)).ncard < c.ptsL.ncard := by
        rw [Set.ncard_pair hgx.symm, ← Nat.card_coe_set_eq, c.card_ptsL]
        norm_num
      obtain ⟨q, hq, hq'⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt hfin
      have hqx : q ≠ c.x0 := fun h => hq' (Or.inl h)
      have hqy : q ≠ g • c.x0 := fun h => hq' (Or.inr h)
      obtain ⟨e', he', he'q⟩ := c.conj_E_transitive hg c.x0_mem_ptsL hq hgx.symm hqy
      obtain ⟨e, he, heq⟩ := c.E_transitive hq hy hqx hgx
      refine MulAction.mem_orbit_iff.mpr
        ⟨⟨e * e', mul_mem (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right he')⟩, ?_⟩
      show (e * e') • c.x0 = g • c.x0
      rw [mul_smul, he'q, heq]
    · obtain ⟨e', he', he'p⟩ := c.conj_E_transitive hg c.x0_mem_ptsL hp hgx.symm hpy
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨e', Subgroup.mem_sup_right he'⟩, he'p⟩
  have horbit : MulAction.orbit ↥A c.x0 = c.ptsL := le_antisymm horbit_sub hptsL_sub
  have horbit_card : Nat.card (MulAction.orbit ↥A c.x0) = 5 := by
    rw [horbit]
    exact c.card_ptsL
  have h5dvd : 5 ∣ Nat.card ↥A := by
    letI : Fintype ↥A := Fintype.ofFinite _
    letI : Fintype ↥(MulAction.orbit ↥A c.x0) := Fintype.ofFinite _
    letI : Fintype ↥(MulAction.stabilizer ↥A c.x0) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A) c.x0
    rw [show Fintype.card ↥(MulAction.orbit ↥A c.x0) = 5 by
      rw [← Nat.card_eq_fintype_card, horbit_card]] at h
    refine ⟨Fintype.card ↥(MulAction.stabilizer ↥A c.x0), ?_⟩
    rw [Nat.card_eq_fintype_card]
    exact h.symm
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha5⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 5 h5dvd
  have ha5G : orderOf (a : G) = 5 := (Subgroup.orderOf_coe a).trans ha5
  exact ⟨(a : G), hA_H a.2, ha5G, fun w hw => hcentral (a : G) a.2 w hw⟩

theorem conj_inf_E_le_Q
    (N : Subgroup G) (π : ↥N →* J4.M22)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X)
    (hcomm : ∀ h ∈ H z, (∀ x ∈ c.X, h * x * h⁻¹ * x⁻¹ ∈ Q z) → h ∈ N)
    (hodd : ∀ h ∈ H z, Odd (orderOf h) → h ∈ N)
    {g : G} (hg : g ∈ c.G2) (hgx : g • c.x0 ≠ c.x0) :
    c.E.map (MulAut.conj g).toMonoidHom ⊓ c.E ≤ Q z := by
  intro w hw
  by_contra hwQ
  obtain ⟨a, ha, ha5, hcent⟩ := c.exists_orderOf_eq_five_commute hg hgx
  exact c.not_commute_of_orderOf_eq_five N π hker hcomm hodd hw.2 hwQ ha ha5
    (hcent w hw)

end Loc49

end CFSG.Quasithin.H13.AS91

