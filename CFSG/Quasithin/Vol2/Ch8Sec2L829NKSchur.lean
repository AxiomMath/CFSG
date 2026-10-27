module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.L829NK

theorem nk_not_sq_dvd_168 {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) : ¬ p ^ 2 ∣ 168 := by
  intro h
  have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have hp12 : p ≤ 12 := by nlinarith
  interval_cases p
  all_goals first
    | omega
    | exact absurd hp (by norm_num)
    | exact absurd h (by norm_num)

theorem nk_hom_comm_trivial {G A : Type} [Group G] [CommGroup A]
    (hperf : _root_.commutator G = ⊤) (f : G →* A) (g : G) : f g = 1 := by
  have hle : _root_.commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf] at hle
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

theorem nk_pow_index_eq_one {G : Type} [Group G] [Finite G] (hperf : _root_.commutator G = ⊤)
    (H : Subgroup G) (hH : ∀ a b : H, a * b = b * a) {z : G} (hz : z ∈ H)
    (hcen : ∀ g : G, g * z = z * g) : z ^ H.index = 1 := by
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hH }
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc0 : Commute z g₀ := (hcen g₀).symm
    have hc : Commute (z ^ k) g₀ := Commute.pow_left hc0 k
    rw [mul_assoc, hc.eq, inv_mul_cancel_left]
  have h1 := nk_hom_comm_trivial hperf (MonoidHom.transfer (MonoidHom.id H : H →* H)) z
  rw [MonoidHom.transfer_eq_pow (MonoidHom.id H : H →* H) z key] at h1
  exact congrArg Subtype.val h1

theorem nk_range_cyclic {H L : Type} [Group H] [Finite H] [Group L] [Finite L]
    (hL : Nat.card L = 168) {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    (hH : IsPGroup p H) (f : H →* L) : IsCyclic f.range := by
  have hfr : IsPGroup p f.range := hH.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hfr
  have hdvd : p ^ n ∣ 168 := by
    have h := Subgroup.card_subgroup_dvd_card f.range
    rw [hn, hL] at h
    exact h
  rcases n with _ | _ | n
  · have h1 : Nat.card f.range = 1 := by simpa using hn
    haveI : Subsingleton f.range := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have h1 : Nat.card f.range = p := by simpa using hn
    exact isCyclic_of_prime_card h1
  · exfalso
    have h2 : p ^ 2 ∣ 168 := (pow_dvd_pow p (by omega)).trans hdvd
    exact nk_not_sq_dvd_168 (Fact.out : p.Prime) hodd h2

theorem nk_sylow_abelian {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    (hL : Nat.card L = 168) (π : G →* L) (hcent : ∀ z ∈ π.ker, ∀ g : G, g * z = z * g)
    {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1) (P : Sylow p G) :
    ∀ a b : P.toSubgroup, a * b = b * a := by
  have hker : (π.comp P.toSubgroup.subtype).ker ≤ Subgroup.center P.toSubgroup := by
    intro x hx
    have hx' : π (x : G) = 1 := MonoidHom.mem_ker.mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hcent (x : G) (MonoidHom.mem_ker.mpr hx') (g : G)
  have hcyc : IsCyclic (π.comp P.toSubgroup.subtype).range :=
    nk_range_cyclic hL hodd P.isPGroup' (π.comp P.toSubgroup.subtype)
  haveI := hcyc
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (π.comp P.toSubgroup.subtype).rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
  exact fun a b => hcomm.is_comm.comm a b

theorem nk_no_prime_order_ker {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    (hL : Nat.card L = 168) (hperf : _root_.commutator G = ⊤) (π : G →* L)
    (hcent : ∀ z ∈ π.ker, ∀ g : G, g * z = z * g) {p : ℕ} [Fact p.Prime] (hodd : p % 2 = 1)
    {w : G} (hw : orderOf w = p) (hwker : w ∈ π.ker) : False := by
  have hQ : IsPGroup p (Subgroup.zpowers w) :=
    IsPGroup.of_card
      (show Nat.card (Subgroup.zpowers w) = p ^ 1 by rw [Nat.card_zpowers, hw, pow_one])
  obtain ⟨P, hPQ⟩ := IsPGroup.exists_le_sylow hQ
  have hwP : w ∈ P.toSubgroup := hPQ (Subgroup.mem_zpowers w)
  have hab := nk_sylow_abelian hL π hcent hodd P
  have hidx := nk_pow_index_eq_one hperf P.toSubgroup hab hwP (hcent w hwker)
  have hdvd : orderOf w ∣ P.toSubgroup.index := orderOf_dvd_of_pow_eq_one hidx
  rw [hw] at hdvd
  exact Sylow.not_dvd_index P hdvd

theorem nk_leafSchurL32 : NKLeafSchurL32 := by
  intro G L _ _ _ hperf hL π hsurj hcent hodd
  have hLcard : Nat.card L = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hL
  haveI : Finite L := Finite.of_surjective π hsurj
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  have ha' : a ∈ π.ker := MonoidHom.mem_ker.mpr ha
  have hn1 : orderOf a ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpp, hpd⟩ : ∃ p, p.Prime ∧ p ∣ orderOf a :=
    ⟨_, Nat.minFac_prime hn1, Nat.minFac_dvd _⟩
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Odd.of_dvd_nat (hodd a ha') hpd)
  have hw : orderOf (a ^ (orderOf a / p)) = p :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' hpd
  exact nk_no_prime_order_ker hLcard hperf π hcent hpodd hw (Subgroup.pow_mem _ ha' _)

end CFSG.Quasithin.H13.L829NK
