module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open scoped commutatorElement

section B
variable {G : Type} [Group G] [Finite G]

theorem B_stability (p : ℕ) [Fact p.Prime] (T N : Subgroup G) (a : G) (hT : IsPGroup p T)
    (hN : N ≤ T) (hNn : (N.subgroupOf T).Normal) (haT : a ∈ Nor T) (ha : ¬ p ∣ orderOf a)
    (h1 : ∀ u ∈ T, ∃ n ∈ N, a * u * a⁻¹ = u * n) (h2 : ∀ n ∈ N, a * n * a⁻¹ = n) :
    a ∈ CenS T := by
  have hcon : ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 haT t).1 ht
  have hcon' : ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun t ht => by
    have h := (Subgroup.mem_normalizer_iff.1 ((Nor T).inv_mem haT) t).1 ht
    simpa using h
  let φ : MulAut T :=
    { toFun := fun t => ⟨a * t * a⁻¹, hcon t.1 t.2⟩
      invFun := fun t => ⟨a⁻¹ * t * a, hcon' t.1 t.2⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun t => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
  have hpow : ∀ n : ℕ, ∀ t : T, ((φ ^ n) t : G) = a ^ n * t * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have h := ih (φ t)
      have hφt : ((φ t : T) : G) = a * t * a⁻¹ := rfl
      calc ((φ ^ (k + 1)) t : G) = ((φ ^ k) (φ t) : G) := by rw [pow_succ, MulAut.mul_apply]
        _ = a ^ k * (a * t * a⁻¹) * (a ^ k)⁻¹ := by rw [h, hφt]
        _ = a ^ (k + 1) * t * (a ^ (k + 1))⁻¹ := by rw [pow_succ]; group
  have hpowφ : φ ^ (orderOf a) = 1 := by
    apply MulEquiv.ext
    intro t
    have h := hpow (orderOf a) t
    rw [pow_orderOf_eq_one a, inv_one, mul_one, one_mul] at h
    apply Subtype.ext
    simpa using h
  have hNp : IsPGroup p (N.subgroupOf T) := hT.to_subgroup _
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hcop : (orderOf a).Coprime (Nat.card (N.subgroupOf T)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ha).symm
  have hφ1 : φ = 1 := by
    apply CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement (N.subgroupOf T) φ (orderOf a) hpowφ hcop
    · intro e he
      have he' : (e : G) ∈ N := he
      apply Subtype.ext
      exact h2 _ he'
    · intro e
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨n, hn, hnE⟩ := h1 e e.2
      have hval : ((e⁻¹ * φ e : T) : G) = n := by
        show (e : G)⁻¹ * (a * e * a⁻¹) = n
        rw [hnE]
        group
      rw [hval]
      exact hn
  refine Subgroup.mem_centralizer_iff.2 (fun t ht => ?_)
  have hfix : φ ⟨t, ht⟩ = ⟨t, ht⟩ := by rw [hφ1]; rfl
  have h' : a * t * a⁻¹ = t := congrArg Subtype.val hfix
  exact (mul_inv_eq_iff_eq_mul.1 h').symm

private theorem comm_aux {a b c d : G} (hca : Commute c a) (hcb : Commute c b)
    (hda : Commute d a) (hdb : Commute d b) (hcd : Commute c d) :
    ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hK : Commute (c * d) ⁅a, b⁆ := by
    have hza : Commute (c * d) a := hca.mul_left hda
    have hzb : Commute (c * d) b := hcb.mul_left hdb
    rw [commutatorElement_def]
    exact ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have hc' : Commute c⁻¹ (b⁻¹ * d⁻¹) := hcb.inv_inv.mul_right hcd.inv_inv
  have key : ⁅c * a, d * b⁆ = (c * d) * ⁅a, b⁆ * (c * d)⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc c * a * (d * b) * (c * a)⁻¹ * (d * b)⁻¹
        = c * (a * d) * b * (a⁻¹ * (c⁻¹ * (b⁻¹ * d⁻¹))) := by group
      _ = c * (d * a) * b * (a⁻¹ * (c⁻¹ * (b⁻¹ * d⁻¹))) := by rw [← hda.eq]
      _ = c * (d * a) * b * (a⁻¹ * ((b⁻¹ * d⁻¹) * c⁻¹)) := by rw [hc'.eq]
      _ = (c * d) * (a * b * a⁻¹ * b⁻¹) * (c * d)⁻¹ := by group
  rw [key, hK.eq, mul_inv_cancel_right]

theorem perfect_centralizes_of_comm_central (L : Subgroup G) (hL : ⁅L, L⁆ = L) (x : G)
    (hxL : ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hz : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CenS L) :
    ∀ l ∈ L, x * l = l * x := by
  have hcomm : ⁅L, L⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    set ca : G := x * a * x⁻¹ * a⁻¹ with hca_def
    set cb : G := x * b * x⁻¹ * b⁻¹ with hcb_def
    have hca_L : ca ∈ L := L.mul_mem (hxL a ha) (L.inv_mem ha)
    have hcb_L : cb ∈ L := L.mul_mem (hxL b hb) (L.inv_mem hb)
    have hca_c : ∀ m ∈ L, m * ca = ca * m := fun m hm =>
      (Subgroup.mem_centralizer_iff.1 (hz a ha) m hm)
    have hcb_c : ∀ m ∈ L, m * cb = cb * m := fun m hm =>
      (Subgroup.mem_centralizer_iff.1 (hz b hb) m hm)
    have hca_a : Commute ca a := (hca_c a ha).symm
    have hcb_b : Commute cb b := (hcb_c b hb).symm
    have hca_b : Commute ca b := (hca_c b hb).symm
    have hcb_a : Commute cb a := (hcb_c a ha).symm
    have hca_cb : Commute ca cb := (hca_c cb hcb_L).symm
    have ea : x * a * x⁻¹ = ca * a := by rw [hca_def]; group
    have eb : x * b * x⁻¹ = cb * b := by rw [hcb_def]; group
    have hconj : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    have hfix : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      rw [hconj, ea, eb]
      exact comm_aux hca_a hca_b hcb_a hcb_b hca_cb
    refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
    rw [Set.mem_singleton_iff.1 hh]
    exact mul_inv_eq_iff_eq_mul.1 hfix
  intro l hl
  have hlC : l ∈ Subgroup.centralizer ({x} : Set G) := by
    apply hcomm
    rw [hL]
    exact hl
  exact Subgroup.mem_centralizer_iff.1 hlC x (Set.mem_singleton x)

theorem B_perfect_comm (L X : Subgroup G) (hL : ⁅L, L⁆ = L) (hLX : L ≤ Nor X) (hXL : X ≤ Nor L)
    (h : ∀ x ∈ X ⊓ L, ∀ l ∈ L, x * l = l * x) : X ≤ CenS L := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 (fun l hl => ?_)
  have hxl : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.1 (hXL hx) l).1 hl
  have hz : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CenS L := by
    intro l hl
    have hmemX : x * l * x⁻¹ * l⁻¹ ∈ X := by
      have h1 : l * x⁻¹ * l⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (hLX hl) x⁻¹).1 (X.inv_mem hx)
      have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
      rw [e]
      exact X.mul_mem hx h1
    have hmemL : x * l * x⁻¹ * l⁻¹ ∈ L := L.mul_mem (hxl l hl) (L.inv_mem hl)
    have hY : x * l * x⁻¹ * l⁻¹ ∈ X ⊓ L := Subgroup.mem_inf.2 ⟨hmemX, hmemL⟩
    exact Subgroup.mem_centralizer_iff.2 (fun m hm => (h _ hY m hm).symm)
  exact (perfect_centralizes_of_comm_central L hL x hxl hz l hl).symm

private theorem Opp_conj_mem (p : ℕ) [Fact p.Prime] (K : Subgroup G) {h : G} (hh : h ∈ Nor K) :
    ∀ m ∈ Opp p K, h * m * h⁻¹ ∈ Opp p K := by
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hm
  let α : MulAut K := K.normalizerMonoidHom ⟨h, hh⟩
  have hmap := pPrimeCore_map_iso p α
  have hmem : α y ∈ pPrimeCore p K := by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  refine Subgroup.mem_map.2 ⟨α y, hmem, ?_⟩
  have h5 : ((α y : K) : G) = h * (y : G) * h⁻¹ := by
    show ((K.normalizerMonoidHom ⟨h, hh⟩ y : K) : G) = h * (y : G) * h⁻¹
    simp
  exact h5

private theorem le_Opp_of_normal_coprime (p : ℕ) [Fact p.Prime] (H M : Subgroup G)
    (hMH : M ≤ H) (hMn : (M.subgroupOf H).Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    M ≤ Opp p H := by
  have hcard : Nat.Coprime p (Nat.card (M.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv]
    exact hcop
  have hle : M.subgroupOf H ≤ pPrimeCore p H := by
    unfold pPrimeCore
    exact le_sSup ⟨hMn, hcard⟩
  intro m hm
  have hmem : (⟨m, hMH hm⟩ : H) ∈ M.subgroupOf H := hm
  exact Subgroup.mem_map.2 ⟨⟨m, hMH hm⟩, hle hmem, rfl⟩

private theorem card_Opp_coprime (p : ℕ) [Fact p.Prime] [Finite G] (H : Subgroup G) :
    Nat.Coprime p (Nat.card (Opp p H)) := by
  have e := (pPrimeCore p H).equivMapOfInjective H.subtype H.subtype_injective
  have h : Nat.card (Opp p H) = Nat.card (pPrimeCore p H) :=
    (Nat.card_congr e.toEquiv.symm)
  rw [h]
  exact pPrimeCore_coprime_card

private theorem oddClosure_normalized (H : Subgroup G) {h : G} (hh : h ∈ H) (g : G)
    (hg : g ∈ Subgroup.closure {x : G | x ∈ H ∧ ¬ 3 ∣ orderOf x}) :
    h * g * h⁻¹ ∈ Subgroup.closure {x : G | x ∈ H ∧ ¬ 3 ∣ orderOf x} := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have hord : orderOf (h * x * h⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
    exact ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), by rw [hord]; exact hx.2⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem B_Opp_O3 (H : Subgroup G) :
    Opp 3 H = Opp 3 (Subgroup.closure {x : G | x ∈ H ∧ ¬ 3 ∣ orderOf x}) := by
  set K := Subgroup.closure {x : G | x ∈ H ∧ ¬ 3 ∣ orderOf x} with hK
  have hKH : K ≤ H := (Subgroup.closure_le H).2 (fun x hx => hx.1)
  have hNor : ∀ h ∈ H, h ∈ Nor K := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact oddClosure_normalized H hh g
    · intro hg
      have := oddClosure_normalized H (H.inv_mem hh) (h * g * h⁻¹) hg
      simpa [mul_assoc] using this
  apply le_antisymm
  · have hMK : Opp 3 H ≤ K := by
      intro m hm
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hm
      apply Subgroup.subset_closure
      refine ⟨y.2, ?_⟩
      show ¬ 3 ∣ orderOf (y : G)
      have hdvd : orderOf (y : G) ∣ Nat.card (pPrimeCore 3 H) := by
        rw [Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard _ hy
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
        (Nat.Coprime.coprime_dvd_right hdvd (pPrimeCore_coprime_card (p := 3)))
    have hMn : ((Opp 3 H).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact Opp_conj_mem 3 H (Subgroup.le_normalizer (hKH g.2)) n hn
    exact le_Opp_of_normal_coprime 3 K (Opp 3 H) hMK hMn (card_Opp_coprime 3 H)
  · have hMH : Opp 3 K ≤ H := by
      intro m hm
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hm
      exact hKH y.2
    have hMn : ((Opp 3 K).subgroupOf H).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact Opp_conj_mem 3 K (hNor g g.2) n hn
    exact le_Opp_of_normal_coprime 3 H (Opp 3 K) hMH hMn (card_Opp_coprime 3 K)

theorem B_central_notin_Oup (p : ℕ) [Fact p.Prime] (H P : Subgroup G) (hP : IsSylowOf p P H)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {z : G} (hzP : z ∈ P) (hz : ∀ h ∈ H, h * z = z * h)
    (hz1 : z ≠ 1) :
    z ∉ Subgroup.closure {x : G | x ∈ H ∧ ¬ p ∣ orderOf x} := by
  obtain ⟨hPH, hPp, hcop⟩ := hP
  letI : CommGroup ↥P :=
    { (inferInstance : Group ↥P) with mul_comm := fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2) }
  let ϕ : ↥(P.subgroupOf H) →* ↥P := (Subgroup.subgroupOfEquivOfLe hPH).toMonoidHom
  let V : ↥H →* ↥P := MonoidHom.transfer ϕ
  have hkill : ∀ x : ↥H, ¬ p ∣ orderOf x → V x = 1 := by
    intro x hx
    obtain ⟨j, hj⟩ := hPp (V x)
    have h1 : orderOf (V x) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf (V x) ∣ orderOf x := orderOf_map_dvd V x
    have hpx : Nat.Coprime p (orderOf x) := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hx
    have h3 : Nat.Coprime (orderOf (V x)) (orderOf x) :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left j hpx)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)
  let z' : ↥H := ⟨z, hPH hzP⟩
  have hzc : ∀ g : ↥H, Commute z' g := fun g => Subtype.ext (hz g g.2).symm
  have key : ∀ (k : ℕ) (g₀ : ↥H), g₀⁻¹ * z' ^ k * g₀ ∈ P.subgroupOf H →
      g₀⁻¹ * z' ^ k * g₀ = z' ^ k := by
    intro k g₀ _
    have hc : Commute (z' ^ k) g₀ := (hzc g₀).pow_left k
    calc g₀⁻¹ * z' ^ k * g₀ = g₀⁻¹ * (z' ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z' ^ k) := by rw [hc.eq]
      _ = z' ^ k := by group
  have hVz : V z' = ϕ ⟨z' ^ (P.subgroupOf H).index, MonoidHom.transfer_eq_pow_aux z' key⟩ :=
    MonoidHom.transfer_eq_pow ϕ z' key
  have hzpow : z ^ (P.subgroupOf H).index ≠ 1 := by
    intro h1
    obtain ⟨j, hj⟩ := hPp ⟨z, hzP⟩
    have hzj : z ^ p ^ j = 1 := congrArg Subtype.val hj
    have hidx : Nat.Coprime p (P.subgroupOf H).index := hcop
    have h2 : orderOf z ∣ p ^ j := orderOf_dvd_of_pow_eq_one hzj
    have h3 : orderOf z ∣ (P.subgroupOf H).index := orderOf_dvd_of_pow_eq_one h1
    have h4 : Nat.Coprime (orderOf z) (P.subgroupOf H).index :=
      Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left j hidx)
    exact hz1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h3))
  have hVz1 : V z' ≠ 1 := by
    rw [hVz]
    intro h1
    apply hzpow
    have := congrArg Subtype.val h1
    simpa [ϕ] using this
  intro hmem
  have hsub : Subgroup.closure {x : G | x ∈ H ∧ ¬ p ∣ orderOf x} ≤ (V.ker).map H.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxH, hx⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply hkill
    rw [← Subgroup.orderOf_coe]
    exact hx
  obtain ⟨w, hwV, hwx⟩ := Subgroup.mem_map.1 (hsub hmem)
  have hw : w = z' := Subtype.ext hwx
  rw [MonoidHom.mem_ker, hw] at hwV
  exact hVz1 hwV

theorem B_charTwo (hchar : CFSG.Assembly.IsCharTwoType G) (Q : Subgroup G) (hQ : Q ≠ ⊥)
    (h2 : IsPGroup 2 Q) :
    Nor Q ⊓ CenS (Op 2 (Nor Q)) ≤ Op 2 (Nor Q) :=
  fun _ hg => hchar (Nor Q) ⟨Q, hQ, h2, rfl⟩ hg

theorem B_kgroup (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (H : Subgroup G)
    (hH : H ≠ ⊤) :
    CFSG.KCore.KGroupNonab CFSG.Assembly.InCatalog ↥H :=
  CFSG.KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hK H hH

end B

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
