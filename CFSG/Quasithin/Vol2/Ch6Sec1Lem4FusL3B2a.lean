module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

private theorem card_mulAut_zpowers5_L3B2a {G : Type*} [Group G] [Finite G] {y : G}
    (hy5 : orderOf y = 5) : Nat.card (MulAut (Subgroup.zpowers y)) = 4 := by
  rw [IsCyclic.card_mulAut, Nat.card_zpowers, hy5, Nat.totient_prime (by norm_num : Nat.Prime 5)]

private theorem leviOfL3_le_L3B2a {G : Type*} [Group G] (N : Subgroup G) (u : G) :
    leviOfL3 N u ≤ N := by
  unfold leviOfL3
  refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
  have ha' : a ∈ N := (inf_le_left : N ⊓ Subgroup.centralizer ({u} : Set G) ≤ N) ha
  have hb' : b ∈ N := (inf_le_left : N ⊓ Subgroup.centralizer ({u} : Set G) ≤ N) hb
  rw [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem ha' hb') (N.inv_mem ha')) (N.inv_mem hb')

private theorem eight_dvd_sq_sub_one_L3B2a {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    8 ∣ p ^ 2 - 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have h8 : p ^ 2 % 8 = 1 := by
    have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases hr with hr | hr | hr | hr <;> rw [Nat.pow_mod, hr] <;> norm_num
  have hpos : 0 < p ^ 2 := by positivity
  generalize p ^ 2 = q at h8 hpos ⊢
  omega

private theorem card_of_isL3Levi_L3B2a {G : Type*} [Group G] {K : Subgroup G} {u : G} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : IsL3Levi K u p) :
    Nat.card K = p * (p ^ 2 - 1) := by
  obtain ⟨hu2, huK, hcen, -, F, hFld, hFfin, hFcard, ⟨e⟩⟩ := hK
  have hset : ((Subgroup.center ↥K : Subgroup ↥K) : Set ↥K) = {1, ⟨u, huK⟩} := by
    ext x
    rw [SetLike.mem_coe, hcen x, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have hne : (1 : ↥K) ≠ ⟨u, huK⟩ := by
    intro h
    have h' : u = 1 := (congrArg Subtype.val h).symm
    rw [h', orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hZ : Nat.card (Subgroup.center ↥K) = 2 := by
    rw [← Set.ncard_pair hne, ← hset]
    exact Nat.card_coe_set_eq _
  have hodd : IsOddPrimePower (Nat.card F) := by
    rw [hFcard]
    unfold IsOddPrimePower
    exact ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_refl 1, (pow_one p).symm⟩
  have hQ : Nat.card (↥K ⧸ Subgroup.center ↥K) = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, psl2_card_formula F hodd, hFcard]
  have h8 := eight_dvd_sq_sub_one_L3B2a hp hp5
  have hdiv : 2 ∣ p * (p ^ 2 - 1) := Dvd.dvd.mul_left (dvd_trans (by norm_num) h8) p
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K), hQ, hZ,
    Nat.div_mul_cancel hdiv]

private theorem zpowers_eq_of_mem_L3B2a {G : Type*} [Group G] [Finite G] {y c : G}
    (hy5 : orderOf y = 5) (hcY : c ∈ Subgroup.zpowers y) (hc1 : c ≠ 1) :
    Subgroup.zpowers c = Subgroup.zpowers y := by
  have hd := orderOf_dvd_of_mem_zpowers hcY
  rw [hy5] at hd
  have hc5 : orderOf c = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hc1
    · exact h1
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcY) ?_
  simp [Nat.card_zpowers, hc5, hy5]

private theorem mem_leviOfL3_of_commutator_L3B2a {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} {y z s : G} (hy5 : orderOf y = 5) (hyN : y ∈ N) (hsN : s ∈ N)
    (hyz : Commute y z) (hsz : Commute s z) (hcY : s * y * s⁻¹ * y⁻¹ ∈ Subgroup.zpowers y)
    (hc1 : s * y * s⁻¹ * y⁻¹ ≠ 1) : y ∈ leviOfL3 N z := by
  have hyC : y ∈ N ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hyN, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩
  have hsC : s ∈ N ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hsN, Subgroup.mem_centralizer_singleton_iff.mpr hsz⟩
  have hcC : s * y * s⁻¹ * y⁻¹ ∈
      ⁅N ⊓ Subgroup.centralizer ({z} : Set G), N ⊓ Subgroup.centralizer ({z} : Set G)⁆ := by
    have h := Subgroup.commutator_mem_commutator hsC hyC
    rwa [commutatorElement_def] at h
  have hyc : y ∈ Subgroup.zpowers (s * y * s⁻¹ * y⁻¹) := by
    rw [zpowers_eq_of_mem_L3B2a hy5 hcY hc1]
    exact Subgroup.mem_zpowers y
  unfold leviOfL3
  exact Subgroup.zpowers_le.mpr hcC hyc

theorem exists_involution_of_sylow_normalizes {G : Type} [Group G] [Finite G] {N : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : L3FusFacts N p) {y : G} {S : Subgroup G}
    (hyN : y ∈ N) (hy5 : orderOf y = 5) (hS : IsSylowTwoOf S N)
    (hSy : S ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hSc : ¬ S ≤ Subgroup.centralizer ({y} : Set G)) :
    ∃ z ∈ S, orderOf z = 2 ∧ Commute z y ∧ (∀ s ∈ S, Commute s z) ∧ y ∈ leviOfL3 N z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  haveI : Group.IsNilpotent ↥S := IsPGroup.isNilpotent hS2
  let φ : ↥S →* MulAut (Subgroup.zpowers y) :=
    (Subgroup.normalizerMonoidHom (Subgroup.zpowers y)).comp (Subgroup.inclusion hSy)
  have hidx : φ.ker.index ≤ 4 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (MulAut (Subgroup.zpowers y)) :=
          Subgroup.card_le_card_group _
      _ = 4 := card_mulAut_zpowers5_L3B2a hy5
  have hSne : S ≠ ⊥ := fun h0 => hSc (by rw [h0]; exact bot_le)
  have hnt : Nat.card ↥S ≠ 1 := fun h1 => hSne ((Subgroup.eq_bot_iff_card _).mpr h1)
  obtain ⟨u0, hu0⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2
    (hS2.card_eq_or_dvd.resolve_left hnt)
  have huN : (u0 : G) ∈ N := hS.1 u0.2
  have hu : orderOf (u0 : G) = 2 := by rw [Subgroup.orderOf_coe, hu0]
  have hK8 : 8 ∣ Nat.card (leviOfL3 N (u0 : G)) := by
    rw [card_of_isL3Levi_L3B2a hp hp5 (h.levi (u0 : G) huN hu).1]
    exact Dvd.dvd.mul_left (eight_dvd_sq_sub_one_L3B2a hp hp5) p
  have hN8 : 8 ∣ Nat.card N :=
    hK8.trans (Subgroup.card_dvd_of_le (leviOfL3_le_L3B2a N (u0 : G)))
  have hS8 : 8 ∣ Nat.card ↥S := by
    have hcardN : Nat.card N = Nat.card ↥S * (S.subgroupOf N).index := by
      have h1 := (S.subgroupOf N).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv] at h1
      exact h1.symm
    have hcop : Nat.Coprime 8 (S.subgroupOf N).index := by
      have h2 : Nat.Coprime 2 (S.subgroupOf N).index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS.2.2
      have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8]
      exact Nat.Coprime.pow_left 3 h2
    rw [hcardN] at hN8
    exact hcop.dvd_of_dvd_mul_right hN8
  have hcardS : Nat.card ↥S = Nat.card φ.ker * φ.ker.index :=
    (Subgroup.card_mul_index φ.ker).symm
  have hK2 : 2 ≤ Nat.card φ.ker := by
    have h8le : 8 ≤ Nat.card ↥S := Nat.le_of_dvd Nat.card_pos hS8
    rw [hcardS] at h8le
    by_contra hlt
    have h1 : Nat.card φ.ker * φ.ker.index ≤ 1 * 4 := Nat.mul_le_mul (by omega) hidx
    omega
  have hK0 : φ.ker ≠ ⊥ := fun h0 => by
    rw [Subgroup.eq_bot_iff_card] at h0
    omega
  have hFne : φ.ker ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hK0
  have hF2 : 2 ∣ Nat.card ↥(φ.ker ⊓ Subgroup.center ↥S) :=
    (hS2.to_subgroup (φ.ker ⊓ Subgroup.center ↥S)).card_eq_or_dvd.resolve_left
      (fun h1 => hFne ((Subgroup.eq_bot_iff_card _).mpr h1))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(φ.ker ⊓ Subgroup.center ↥S)) 2 hF2
  have hwK : (w : ↥S) ∈ φ.ker := (Subgroup.mem_inf.mp w.2).1
  have hwc : (w : ↥S) ∈ Subgroup.center ↥S := (Subgroup.mem_inf.mp w.2).2
  have hzS : ((w : ↥S) : G) ∈ S := (w : ↥S).2
  have hzord : orderOf ((w : ↥S) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hzy : Commute ((w : ↥S) : G) y := by
    have h1 : Subgroup.inclusion hSy (w : ↥S) ∈
        (Subgroup.normalizerMonoidHom (Subgroup.zpowers y)).ker :=
      MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hwK)
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 y (Subgroup.mem_zpowers y)).symm
  have hzc : ∀ s ∈ S, Commute s ((w : ↥S) : G) := by
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨s, hs⟩)
  obtain ⟨s, hsS, hsnc⟩ := SetLike.not_le_iff_exists.mp hSc
  have hsY : s * y * s⁻¹ ∈ Subgroup.zpowers y :=
    (Subgroup.mem_normalizer_iff.mp (hSy hsS) y).mp (Subgroup.mem_zpowers y)
  have hcY : s * y * s⁻¹ * y⁻¹ ∈ Subgroup.zpowers y :=
    Subgroup.mul_mem _ hsY (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  have hc1 : s * y * s⁻¹ * y⁻¹ ≠ 1 := by
    intro h1
    apply hsnc
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_one] at h1
    calc s * y = s * y * s⁻¹ * s := by group
      _ = y * s := by rw [h1]
  exact ⟨((w : ↥S) : G), hzS, hzord, hzy, hzc,
    mem_leviOfL3_of_commutator_L3B2a hy5 hyN (hS.1 hsS) hzy.symm (hzc s hsS) hcY hc1⟩

end CFSG.Quasithin.H13
