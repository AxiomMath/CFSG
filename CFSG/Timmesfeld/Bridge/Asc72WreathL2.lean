module

public import CFSG.Timmesfeld.Bridge.Asc72WreathDefs
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Bridge.Asc72NoPolar

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Open

namespace WreathL2

variable {K : Type*} [Group K]

theorem mul_comm_of_forall_mul_self {P : Subgroup K} (hexp : ∀ a ∈ P, a * a = 1) {a b : K}
    (ha : a ∈ P) (hb : b ∈ P) : a * b = b * a := by
  have h := inv_eq_of_mul_eq_one_right (hexp _ (P.mul_mem ha hb))
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hexp b hb),
    inv_eq_of_mul_eq_one_right (hexp a ha)] at h
  exact h.symm

theorem not_quaternion_of_mul_self {P : Subgroup K} (hexp : ∀ a ∈ P, a * a = 1) {n : ℕ}
    [NeZero n] (e : P ≃* QuaternionGroup n) : False := by
  have h4 := QuaternionGroup.orderOf_xa (n := n) 0
  rw [← e.symm.orderOf_eq] at h4
  have h2 : orderOf (e.symm (QuaternionGroup.xa 0)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simpa [pow_two] using hexp _ (e.symm (QuaternionGroup.xa 0)).2))
  rw [h4] at h2
  norm_num at h2

theorem isPGroup_of_mul_self {P : Subgroup K} (hexp : ∀ a ∈ P, a * a = 1) : IsPGroup 2 P :=
  fun a => ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using hexp a a.2)⟩

theorem mem_sylow_of_mem_normalizer (P : Sylow 2 K) {x : K}
    (hx : x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) (hx2 : x * x = 1) :
    x ∈ (P : Subgroup K) := by
  have hdvd : orderOf x ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two, hx2])
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hmax := P.is_maximal' (IsPGroup.to_sup_of_normal_right' hp P.isPGroup'
    (Subgroup.zpowers_le.2 hx)) le_sup_right
  have hmem : x ∈ Subgroup.zpowers x ⊔ (P : Subgroup K) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  rwa [hmax] at hmem

variable [Finite K]

theorem fusionStronglyEmbedded_normalizer_of_isTI (P : Sylow 2 K)
    (hTI : fusionIsTI (P : Subgroup K))
    (hne : Subgroup.normalizer ((P : Subgroup K) : Set K) ≠ ⊤)
    (heven : Even (Nat.card (P : Subgroup K))) :
    fusionStronglyEmbedded (Subgroup.normalizer ((P : Subgroup K) : Set K)) := by
  refine ⟨hne, even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans
    (Subgroup.card_dvd_of_le Subgroup.le_normalizer)), fun g hg => ?_⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have hxo : orderOf (x : K) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hx2 : (x : K) * x = 1 := by
    have h := pow_orderOf_eq_one (x : K)
    rwa [hxo, pow_two] at h
  have hx1 : (x : K) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hxP : (x : K) ∈ (P : Subgroup K) := mem_sylow_of_mem_normalizer P x.2.1 hx2
  have hgx := CFSG.Timmesfeld.Bridge.mem_map_conj_inv_iff.1 x.2.2
  have hgx2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx2, mul_one,
      mul_inv_cancel]
  have hxP' : (x : K) ∈ (P : Subgroup K).map (MulAut.conj g⁻¹).toMonoidHom :=
    CFSG.Timmesfeld.Bridge.mem_map_conj_inv_iff.2 (mem_sylow_of_mem_normalizer P hgx hgx2)
  have hfix : (P : Subgroup K).map (MulAut.conj g⁻¹).toMonoidHom = P := by
    by_contra hne'
    have hmem : (x : K) ∈
        (P : Subgroup K) ⊓ (P : Subgroup K).map (MulAut.conj g⁻¹).toMonoidHom := ⟨hxP, hxP'⟩
    rw [hTI g⁻¹ hne', Subgroup.mem_bot] at hmem
    exact hx1 hmem
  exact hg (by
    simpa using Subgroup.inv_mem _ (CFSG.Timmesfeld.RankOne.map_conj_eq_self_iff.1 hfix))

theorem exists_psl2_of_forall_commute [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
    (hA : ∀ a b : K, a ≠ 1 → a * a = 1 → Commute a b → b * b = 1) :
    ∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  have heven : Even (Nat.card K) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) a b)
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hPne : (P : Subgroup K) ≠ ⊥ := P.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  have hZ := P.isPGroup'.center_nontrivial
  obtain ⟨k, hk, hkcard⟩ :=
    ((P.isPGroup'.to_subgroup (Subgroup.center P)).nontrivial_iff_card).mp hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2
    (hkcard ▸ dvd_pow_self 2 hk.ne')
  set t : K := ((z : P) : K)
  have htord : orderOf t = 2 := by
    have h1 : orderOf (z : P) = 2 :=
      (orderOf_injective (Subgroup.center P).subtype Subtype.val_injective z).trans hz
    exact (orderOf_injective (P : Subgroup K).subtype Subtype.val_injective (z : P)).trans h1
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    omega
  have ht2 : t * t = 1 := by
    rw [← sq, ← htord, pow_orderOf_eq_one]
  have htc : ∀ y ∈ (P : Subgroup K), Commute t y := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)).symm
  have hexp : ∀ x ∈ (P : Subgroup K), x * x = 1 := fun x hx => hA t x ht1 ht2 (htc x hx)
  have hcomm : ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K), x * y = y * x :=
    fun x hx y hy => mul_comm_of_forall_mul_self hexp hx hy
  have hcent : ∀ x ∈ (P : Subgroup K), x ≠ 1 → Subgroup.centralizer {x} = P := by
    intro x hx hx1
    refine P.is_maximal' (isPGroup_of_mul_self fun y hy => hA x y hx1 (hexp x hx) ?_) ?_
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
    · intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy x hx)
  have hTI : fusionIsTI (P : Subgroup K) := by
    intro g hne
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxg⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    apply hne
    have hle : (P : Subgroup K).map (MulAut.conj g).toMonoidHom ≤ P := by
      refine le_trans ?_ (hcent x hxP hx1).le
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x', hx', rfl⟩ := hxg
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm y hy x' hx']
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hN : Subgroup.normalizer ((P : Subgroup K) : Set K) ≠ ⊤ := by
    intro htop
    have := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup K) with h | h
    · exact hPne h
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (hcomm a (h ▸ Subgroup.mem_top a) b (h ▸ Subgroup.mem_top b))
  have hPeven : Even (Nat.card (P : Subgroup K)) := by
    rcases P.isPGroup'.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hPne
    · exact even_iff_two_dvd.mpr h
  have hSE := fusionStronglyEmbedded_normalizer_of_isTI P hTI hN hPeven
  rcases bender_strongly_embedded_normal_series K _ hSE with hcq |
    ⟨M₀, N, hM₀, hNn, hMN, -, hModd, hNodd, hB⟩
  · exfalso
    rcases hcq P with hcyc | ⟨r, -, ⟨e⟩⟩
    · exact CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_nonabelian_simple K hnab
        heven P hcyc
    · have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      exact not_quaternion_of_mul_self hexp e
  have hM1 : M₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M₀ with h | h
    · exact h
    · rw [h, Subgroup.card_top] at hModd
      exact absurd heven (Nat.not_even_iff_odd.mpr hModd)
  have hNtop : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h, Subgroup.index_bot] at hNodd
      exact absurd heven (Nat.not_even_iff_odd.mpr hNodd)
    · exact h
  have hsub : M₀.subgroupOf N = ⊥ := by
    rw [hM1, Subgroup.bot_subgroupOf]
  let e₁ : K ≃* N := (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr hNtop.symm)
  let e₂ : N ≃* N ⧸ M₀.subgroupOf N :=
    (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hsub.symm)
  have hK : CFSG.BenderSuzuki.IsBenderGroup K := isBenderGroup_of_mulEquiv (e₁.trans e₂)
    (CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup hB)
  exact IsBenderGroup.exists_psl2_of_commute hK P fun x hx y hy => hcomm x hx y hy

end WreathL2

namespace WreathData

variable {G : Type} [Group G] {D : Set G} {M : Subgroup G} (W : WreathData G D M)

theorem e_mulSingle (i : Fin W.r) (x : W.S i) : (W.e (Pi.mulSingle i x) : G) = x := by
  have h := W.e_single i (Pi.mulSingle i x) fun k hk =>
    Pi.mulSingle_eq_of_ne (M := fun j => W.S j) hk x
  rw [h, Pi.mulSingle_eq_same]

theorem commute_of_ne {i j : Fin W.r} (hij : i ≠ j) {x y : G} (hx : x ∈ W.S i)
    (hy : y ∈ W.S j) : Commute x y := by
  have h := ((Pi.mulSingle_commute hij (⟨x, hx⟩ : W.S i) (⟨y, hy⟩ : W.S j)).map W.e).map
    M.subtype
  simpa only [Subgroup.coe_subtype, e_mulSingle] using h

theorem inf_eq_bot {i j : Fin W.r} (hij : i ≠ j) : W.S i ⊓ W.S j = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxi, hxj⟩
  have h : Pi.mulSingle i (⟨x, hxi⟩ : W.S i) = Pi.mulSingle j (⟨x, hxj⟩ : W.S j) :=
    W.e.injective (Subtype.ext ((W.e_mulSingle i _).trans (W.e_mulSingle j ⟨x, hxj⟩).symm))
  have hi := congrFun h i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at hi
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hi)

theorem conj_mem (g : G) {i : Fin W.r} {x : G} (hx : x ∈ W.S i) :
    g * x * g⁻¹ ∈ W.S (W.π g i) := by
  rw [← W.conj g i]
  exact ⟨x, hx, rfl⟩

theorem exists_mem_ne (hS : Setup G D) (i : Fin W.r) : ∃ u ∈ D, W.π u i ≠ i := by
  by_contra h
  push Not at h
  have : Nontrivial (Fin W.r) := Fin.nontrivial_iff_two_le.mpr W.two_le
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨g, hg⟩ := W.transitive i j
  have hle : Subgroup.closure D ≤
      (MulAction.stabilizer (Equiv.Perm (Fin W.r)) i).comap W.π := by
    rw [Subgroup.closure_le]
    exact fun u hu => h u hu
  rw [hS.gen] at hle
  have hgi : W.π g i = i := hle (Subgroup.mem_top g)
  exact hj (hg.symm.trans hgi)

theorem mul_self_eq_one_of_commute (hS : Setup G D) {i : Fin W.r} {a b : G} (ha : a ∈ W.S i)
    (hb : b ∈ W.S i) (ha1 : a ≠ 1) (ha2 : a * a = 1) (hab : Commute a b) : b * b = 1 := by
  obtain ⟨u, hu, hui⟩ := W.exists_mem_ne hS i
  have hij : i ≠ W.π u i := fun h => hui h.symm
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have huinv : u⁻¹ = u := hS.oddT.inv_eq hu
  have hconj : ∀ x ∈ W.S i, u * x * u ∈ W.S (W.π u i) := fun x hx => by
    simpa only [huinv] using W.conj_mem u hx
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hc : u * a * u ∈ W.S (W.π u i) := hconj a ha
  have hac : Commute a (u * a * u) := W.commute_of_ne hij ha hc
  have hu' : a * u * a ∈ D := by simpa only [hainv] using hS.conj_mem a hu
  have h1 : u * (a * u * a) = u * a * u * a := by group
  have huu' : Commute u (a * u * a) := by
    show u * (a * u * a) = a * u * a * u
    calc u * (a * u * a) = (u * a * u) * a := by group
      _ = a * (u * a * u) := hac.eq.symm
      _ = a * u * a * u := by group
  have hne : u ≠ a * u * a := by
    intro h
    have hca : u * a * u = a := by
      calc u * a * u = a * u * a * a * u := by rw [← h]
        _ = a * u * (a * a) * u := by group
        _ = a := by rw [ha2, mul_one, mul_assoc, hu2, mul_one]
    have hmem : a ∈ W.S i ⊓ W.S (W.π u i) := ⟨ha, hca ▸ hc⟩
    rw [W.inf_eq_bot hij, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hbc : Commute b (u * a * u) := W.commute_of_ne hij hb hc
  have hbuu' : Commute b (u * (a * u * a)) := by
    rw [h1]
    exact hbc.mul_right hab.symm
  have hw : b * u * b⁻¹ ∈ D := hS.conj_mem b hu
  have hwuu' : Commute (b * u * b⁻¹) (u * (a * u * a)) := by
    have h2 := (Commute.conj_iff b).mpr ((Commute.refl u).mul_right huu')
    rwa [hbuu'.eq, mul_inv_cancel_right] at h2
  have hwu : Commute (b * u * b⁻¹) u :=
    ((hS.oddT.commute_mul_iff hu hu' hw hne huu').mp hwuu').1
  have he : u * b * u ∈ W.S (W.π u i) := hconj b hb
  have hbe : Commute b (u * b * u) := W.commute_of_ne hij hb he
  have hke : b * (u * b * u)⁻¹ = u * b * u * b⁻¹ := by
    calc b * (u * b * u)⁻¹ = b * u⁻¹ * b⁻¹ * u⁻¹ := by group
      _ = b * u * b⁻¹ * u := by rw [huinv]
      _ = u * b * u * b⁻¹ := hwu.eq.trans (by group)
  have hbb : b * b = u * (b * b) * u := by
    calc b * b = b * (u * b * u)⁻¹ * (u * b * u) * b := by group
      _ = u * b * u * b⁻¹ * ((u * b * u) * b) := by rw [hke]; group
      _ = u * b * u * b⁻¹ * (b * (u * b * u)) := by rw [← hbe.eq]
      _ = u * b * (u * u) * b * u := by group
      _ = u * (b * b) * u := by rw [hu2]; group
  have hmem : b * b ∈ W.S i ⊓ W.S (W.π u i) :=
    ⟨(W.S i).mul_mem hb hb, hbb ▸ hconj _ ((W.S i).mul_mem hb hb)⟩
  rw [W.inf_eq_bot hij, Subgroup.mem_bot] at hmem
  exact hmem

end WreathData

theorem wreathData_factor_psl2 {G : Type} [Group G] [Finite G] {D : Set G} {M : Subgroup G}
    (hS : Setup G D) (W : WreathData G D M) (i : Fin W.r) :
    ∃ f : ℕ, 2 ≤ f ∧ Nonempty (W.S i ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  have := W.simple i
  refine WreathL2.exists_psl2_of_forall_commute (W.not_comm i) fun x y hx1 hx2 hxy => ?_
  exact Subtype.ext (W.mul_self_eq_one_of_commute hS x.2 y.2 (fun h => hx1 (Subtype.ext h))
    (congrArg Subtype.val hx2) (hxy.map (W.S i).subtype))

end CFSG.Timmesfeld.Bridge.Asc72
