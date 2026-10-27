module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneA
public import CFSG.Quasithin.Background.Asc81cPfBasic
public import CFSG.Quasithin.EmptyFaithful.S145Cop
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

theorem w16h_ext_center (h : Cfg132 t P) (hext : IsPOnePlusTwo 3 ↥P) :
    ∃ z : MulAut W, z ∈ P ∧ orderOf z = 3 ∧ (∀ y ∈ P, y * z = z * y) ∧ t * z * t⁻¹ = z ∧
      (∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) := by
  haveI : CFSG.IsExtraspecial 3 ↥P := hext.1
  have hcardP : Nat.card ↥P = 27 := by rw [hext.2.1]; norm_num
  have hZcard : Nat.card (Subgroup.center ↥P) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥P
  have hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro hab
    have hcentop : Subgroup.center ↥P = ⊤ := by
      apply le_antisymm le_top
      intro y _
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (hab y y.2 x x.2).symm
    have h3 := CFSG.IsExtraspecial.center_order_p 3 ↥P
    rw [hcentop, Subgroup.card_top, hcardP] at h3
    norm_num at h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcyc : IsCyclic (Subgroup.center ↥P) := isCyclic_of_prime_card hZcard
  obtain ⟨z0, hz0gen⟩ := IsCyclic.exists_generator (α := Subgroup.center ↥P)
  have hz0top : Subgroup.zpowers z0 = ⊤ :=
    le_antisymm le_top fun x _ => hz0gen x
  have hz0ord : orderOf z0 = 3 := by
    rw [← Nat.card_zpowers z0, hz0top, Subgroup.card_top, hZcard]
  have hzord : orderOf (((z0 : ↥P)) : MulAut W) = 3 := by
    calc orderOf (((z0 : ↥P)) : MulAut W) = orderOf (z0 : ↥P) := Subgroup.orderOf_coe _
      _ = orderOf z0 := Subgroup.orderOf_coe _
      _ = 3 := hz0ord
  have hzcent : ∀ y ∈ P, y * ((z0 : ↥P) : MulAut W) = ((z0 : ↥P) : MulAut W) * y := by
    intro y hy
    exact congrArg (fun w : ↥P => (w : MulAut W))
      (Subgroup.mem_center_iff.mp z0.2 (⟨y, hy⟩ : ↥P))
  refine ⟨((z0 : ↥P) : MulAut W), (z0 : ↥P).2, hzord, hzcent, ?_, ?_⟩
  · have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [h.ht, pow_two] at this
      exact this
    exact w16h_central_of_order_27 htt h.hn h.hc hcardP hnab _ (z0 : ↥P).2 hzcent
  · have hzpowers_eq : Subgroup.zpowers (z0 : ↥P) = Subgroup.center ↥P := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z0.2) ?_
      rw [hZcard, Nat.card_zpowers, Subgroup.orderOf_coe, hz0ord]
    intro x hx hxc
    have hxcent : (⟨x, hx⟩ : ↥P) ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hxc y y.2)
    have hxzp : (⟨x, hx⟩ : ↥P) ∈ Subgroup.zpowers (z0 : ↥P) := by
      rw [hzpowers_eq]
      exact hxcent
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxzp
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have hval : ((z0 : ↥P) : MulAut W) ^ n = x := by
      rw [← Subgroup.coe_zpow, hn]
    exact hval

private theorem w16g_commSub_stable_of_commute {M : Subgroup W} {X : Subgroup (MulAut W)}
    {c : MulAut W} (hc : ∀ x ∈ X, c * x = x * c) (hM : ∀ u ∈ M, c u ∈ M) :
    ∀ u ∈ commSub M X, c u ∈ commSub M X := by
  have hmapM : M.map c.toMonoidHom = M := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      exact hM v hv
    · rw [Subgroup.card_map_of_injective c.injective]
  have hmapX : X.map (MulAut.conj c).toMonoidHom = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : c * x * c⁻¹ = x := by rw [hc x hx, mul_inv_cancel_right]
      show c * x * c⁻¹ ∈ X
      rw [h1]; exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      show c * y * c⁻¹ = y
      rw [hc y hy, mul_inv_cancel_right]
  have h := CFSG.Quasithin.Z391.commSub_map_conj c M X
  rw [hmapM, hmapX] at h
  intro u hu
  rw [h]
  exact ⟨u, hu, rfl⟩

private theorem w16g_commSub_sup_left (D M : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (D ⊔ M) X = commSub D X ⊔ commSub M X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨d, hd, m, hm, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (d * m) * (d * m)⁻¹ = (x d * d⁻¹) * (x m * m⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [h1]
    have hd1 : x d * d⁻¹ ∈ commSub D X := Subgroup.subset_closure ⟨x, hx, d, hd, rfl⟩
    have hm1 : x m * m⁻¹ ∈ commSub M X := Subgroup.subset_closure ⟨x, hx, m, hm, rfl⟩
    exact (commSub D X ⊔ commSub M X).mul_mem (Subgroup.mem_sup_left hd1)
      (Subgroup.mem_sup_right hm1)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w16g_fixV_stable_of_commute {X : Subgroup (MulAut W)} {c : MulAut W}
    (hc : ∀ x ∈ X, c * x = x * c) : ∀ u ∈ fixV X, c u ∈ fixV X := by
  intro u hu
  rw [mem_fixV] at hu ⊢
  intro x hx
  calc x (c u) = (x * c) u := by rw [MulAut.mul_apply]
    _ = (c * x) u := by rw [(hc x hx).symm]
    _ = c (x u) := by rw [MulAut.mul_apply]
    _ = c u := by rw [hu x hx]

private def w16g_Faith (G : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  ∀ y ∈ G, (∀ u ∈ U, y u = u) → y = 1

private theorem w16g_mem_map_subtype {V₀ : Subgroup W} {U : Subgroup ↥V₀} {u : ↥V₀} :
    (u : W) ∈ U.map V₀.subtype ↔ u ∈ U :=
  Subgroup.mem_map_iff_mem V₀.subtype_injective

private theorem w16g_stableUnder_range {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (U : Subgroup ↥V₀) :
    StableUnder σ.range U ↔ StableUnder G (U.map V₀.subtype) := by
  constructor
  · intro hstable x hx w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    have hmem : σ ⟨x, hx⟩ u ∈ U :=
      hstable _ (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩) u hu
    exact Subgroup.mem_map.mpr ⟨_, hmem, hσ ⟨x, hx⟩ u⟩
  · intro hstable y hy u hu
    obtain ⟨xg, rfl⟩ := MonoidHom.mem_range.mp hy
    have hmem : (xg : MulAut W) (u : W) ∈ U.map V₀.subtype :=
      hstable xg xg.2 (u : W) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    rw [← hσ xg u] at hmem
    exact w16g_mem_map_subtype.mp hmem

private theorem w16g_faith_range {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (hσinj : Function.Injective σ)
    (U : Subgroup ↥V₀) :
    w16g_Faith σ.range U ↔ w16g_Faith G (U.map V₀.subtype) := by
  constructor
  · intro h x hx hfix
    have hσ1 : σ ⟨x, hx⟩ = 1 := by
      refine h _ (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩) ?_
      intro u hu
      apply Subtype.ext
      rw [hσ]
      simpa using hfix (u : W) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    have hG : (⟨x, hx⟩ : G) = 1 := hσinj (by rw [hσ1, map_one])
    exact congrArg Subtype.val hG
  · intro h y hy hfix
    obtain ⟨xg, rfl⟩ := MonoidHom.mem_range.mp hy
    have hxg1 : (xg : MulAut W) = 1 := by
      refine h xg xg.2 ?_
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      have := congrArg Subtype.val (hfix u hu)
      rw [hσ] at this
      exact this
    rw [show xg = 1 from Subtype.ext hxg1, map_one]

private theorem w16g_map_commSub_le {G : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (σ : G →* MulAut ↥V₀)
    (hσ : ∀ (x : G) (u : ↥V₀), ((σ x) u : W) = (x : MulAut W) (u : W))
    (x : G) :
    (commSub ⊤ (Subgroup.zpowers (σ x))).map V₀.subtype ≤
      commSub V₀ (Subgroup.zpowers (x : MulAut W)) := by
  rw [commSub, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro c ⟨d, hd, rfl⟩
  obtain ⟨y, hy, v, _, hdxy⟩ := hd
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  change (d : W) ∈ {c | ∃ z ∈ Subgroup.zpowers (x : MulAut W), ∃ w ∈ V₀, z w * w⁻¹ = c}
  refine ⟨(x : MulAut W) ^ n, Subgroup.zpow_mem_zpowers _ _, (v : W), v.2, ?_⟩
  have hleft : ((x : MulAut W) ^ n) (v : W) = (((σ x) ^ n) v : W) := by
    rw [← map_zpow, hσ, Subgroup.coe_zpow]
  rw [← hdxy, ← hn, Subgroup.coe_mul, Subgroup.coe_inv, hleft]

private theorem w16g_center_le_of_normal {P : Subgroup (MulAut W)}
    (hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h27 : Nat.card ↥P = 27)
    {N : Subgroup ↥P} (hN : N.Normal) (hNne : N ≠ ⊥) :
    Subgroup.center ↥P ≤ N := by
  have hnc : ∃ u v : ↥P, u * v ≠ v * u := by
    push Not at hnab
    obtain ⟨u, hu, v, hv, huv⟩ := hnab
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv (congrArg Subtype.val h)⟩
  have hcc := CFSG.Quasithin.SzN31.SmD6Grp.commutator_mem_center h27 hnc
  have hZ3 := CFSG.Quasithin.SzN31.SmD6Grp.card_center_eq_three h27 hnc
  have hcommle : commutator ↥P ≤ Subgroup.center ↥P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    simpa [commutatorElement_def] using hcc a b
  have hNcenter : N ⊓ Subgroup.center ↥P ≠ ⊥ := by
    intro hbot
    apply hNne
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hcent : n ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : ⁅n, g⁆ ∈ N := by
        rw [commutatorElement_def]
        have hb : g * n⁻¹ * g⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) g
        have hcalc : n * g * n⁻¹ * g⁻¹ = n * (g * n⁻¹ * g⁻¹) := by group
        rw [hcalc]
        exact N.mul_mem hn hb
      have h2 : ⁅n, g⁆ ∈ Subgroup.center ↥P :=
        hcommle (Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top g))
      have h3 : ⁅n, g⁆ ∈ N ⊓ Subgroup.center ↥P := ⟨h1, h2⟩
      rw [hbot] at h3
      exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := n) (g₂ := g)).mp
        (Subgroup.mem_bot.mp h3)).symm
    have : n ∈ N ⊓ Subgroup.center ↥P := ⟨hn, hcent⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  obtain ⟨z₀, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNcenter
  let z : ↥P := (z₀ : ↥P)
  have hzN : z ∈ N := z₀.2.1
  have hzC : z ∈ Subgroup.center ↥P := z₀.2.2
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3ord : orderOf z = 3 := by
    have hz3ord' : orderOf (z₀ : ↥P) = 3 := by
      have hdvd : orderOf (z₀ : ↥P) ∣ 3 := by
        have h1 : orderOf (z₀ : ↥P) ∣ Nat.card ↥(N ⊓ Subgroup.center ↥P) :=
          Subgroup.orderOf_dvd_natCard (N ⊓ Subgroup.center ↥P) z₀.2
        have h2 : Nat.card ↥(N ⊓ Subgroup.center ↥P) ∣ Nat.card (Subgroup.center ↥P) :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [hZ3] at h2
        exact h1.trans h2
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1'
      · exact h
    rwa [show z = (z₀ : ↥P) from rfl]
  have htop : Subgroup.zpowers z = Subgroup.center ↥P := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzC) ?_
    rw [hZ3, Nat.card_zpowers, hz3ord]
  rw [← htop]
  exact Subgroup.zpowers_le.mpr hzN

private theorem w16g_zpow_eq_one_or_self {A : Type*} [Group A] {t : A} (htt : t * t = 1)
    {b : A} (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact htt
  have hmod := zpow_eq_zpow_emod k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hmod, h, zpow_zero]
  · right; rw [hmod, h, zpow_one]

private theorem w16g_int_emod_three (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  have hge := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
  omega

private theorem w16g_not_comm_of_isExtraspecial {p : ℕ} {X : Type*} [Group X]
    [CFSG.IsExtraspecial p X] : ¬ IsMulCommutative X := by
  intro hcomm
  have hcenter : Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hcomm.is_comm.comm x y).symm
  haveI : Subsingleton (X ⧸ Subgroup.center X) :=
    (QuotientGroup.subsingleton_iff (N := Subgroup.center X)).2 hcenter
  haveI := CFSG.IsExtraspecial.quotient_nontrivial p X
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
  exact hxy (Subsingleton.elim x y)

private theorem w16g_card_isZ3Times {X : Type} [Group X] (h : IsZ3TimesPOnePlusTwo X) :
    Nat.card X = 81 := by
  obtain ⟨H, instH, hP1, ⟨e⟩⟩ := h
  letI := instH
  have hcardH : Nat.card H = 27 := by rw [hP1.2.1]; norm_num
  have hcardZ : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  calc Nat.card X = Nat.card (Multiplicative (ZMod 3) × H) := Nat.card_congr e.toEquiv
    _ = Nat.card (Multiplicative (ZMod 3)) * Nat.card H := Nat.card_prod _ _
    _ = 3 * 27 := by rw [hcardZ, hcardH]
    _ = 81 := by norm_num

private theorem w16g_card_isZ3WrZ3 {X : Type} [Group X] (h : IsZ3WrZ3 X) :
    Nat.card X = 81 := h.1

private theorem w16g_map_inclusion_subgroupOf {G K : Subgroup (MulAut W)}
    (hGK : G ≤ K) {P : Subgroup (MulAut W)} (hPG : P ≤ G) :
    (P.subgroupOf G).map (Subgroup.inclusion hGK) = P.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    exact ⟨⟨(x : MulAut W), hPG (Subgroup.mem_subgroupOf.mp hx)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩

private theorem w16g_subgroupOf_commutator {M : Type} [Group M] {H₁ H₂ K : Subgroup M}
    (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ = (⁅H₁, H₂⁆).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le h₁ h₂)]

private theorem w16g_map_commSub_subgroup {G : Subgroup (MulAut W)} {U : Subgroup W}
    {P : Subgroup (MulAut W)} (σ : G →* MulAut ↥U)
    (hσ : ∀ (x : G) (u : ↥U), ((σ x) u : W) = (x : MulAut W) (u : W))
    (hPG : P ≤ G) :
    (commSub ⊤ ((P.subgroupOf G).map σ)).map U.subtype = commSub U P := by
  apply le_antisymm
  · rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨x, hx, v, -, rfl⟩ := hc
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    have hgP : (g : MulAut W) ∈ P := Subgroup.mem_subgroupOf.mp hg
    have hcoe : U.subtype ((σ g) v * v⁻¹) = (g : MulAut W) (v : W) * (v : W)⁻¹ := by
      show (((σ g) v * v⁻¹ : ↥U) : W) = (g : MulAut W) (v : W) * (v : W)⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ g v]
    rw [hcoe]
    exact Subgroup.subset_closure ⟨(g : MulAut W), hgP, (v : W), v.2, rfl⟩
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨p, hp, w, hw, rfl⟩
    let g : P.subgroupOf G := ⟨⟨p, hPG hp⟩, Subgroup.mem_subgroupOf.mpr hp⟩
    refine Subgroup.mem_map.mpr ⟨σ g ⟨w, hw⟩ * ⟨w, hw⟩⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure
        ⟨σ g, Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩, ⟨w, hw⟩, Subgroup.mem_top _, rfl⟩
    · show (((σ g) ⟨w, hw⟩ * ⟨w, hw⟩⁻¹ : ↥U) : W) = p w * w⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ]

private theorem w16g_stableUnder_sup {A : Subgroup (MulAut W)} {X Y : Subgroup W}
    (hX : StableUnder A X) (hY : StableUnder A Y) : StableUnder A (X ⊔ Y) := by
  intro φ hφ u hu
  rw [Subgroup.sup_eq_closure] at hu ⊢
  refine Subgroup.closure_induction
    (p := fun z _ => φ z ∈ Subgroup.closure ((X : Set W) ∪ (Y : Set W))) ?_ ?_ ?_ ?_ hu
  · rintro z (hz | hz)
    · exact Subgroup.subset_closure (Or.inl (hX φ hφ z hz))
    · exact Subgroup.subset_closure (Or.inr (hY φ hφ z hz))
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact inv_mem hx

private theorem w16g_le_stabSub_of_stableUnder {A : Subgroup (MulAut W)} {M : Subgroup W}
    (hA : StableUnder A M) : A ≤ stabSub M := by
  intro x hx
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have hinj : Function.Injective (fun m : M => (⟨x m, hA x hx m m.2⟩ : M)) := by
      intro a b hab
      apply Subtype.ext
      exact x.injective (congrArg Subtype.val hab)
    obtain ⟨m, hm⟩ := Finite.surjective_of_injective hinj ⟨x u, hu⟩
    have h2 : x (m : W) = x u := congrArg Subtype.val hm
    have h3 : (m : W) = u := x.injective h2
    exact h3 ▸ m.2
  · exact hA x hx u

private theorem w16g_stableUnder_sup_group {A B : Subgroup (MulAut W)} {M : Subgroup W}
    (hA : StableUnder A M) (hB : StableUnder B M) : StableUnder (A ⊔ B) M := by
  intro x hx u hu
  have hle : A ⊔ B ≤ stabSub M :=
    sup_le (w16g_le_stabSub_of_stableUnder hA) (w16g_le_stabSub_of_stableUnder hB)
  exact (mem_stabSub.mp (hle hx) u).2 hu

private theorem w16g_rank_six_of_min_faithful (hMin : W4Lem13_2MinLe 27) {W : Type}
    [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {t : MulAut W} (ht : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {P : Subgroup (MulAut W)}
    (hPgrp : IsPGroup 3 ↥P) (hPne : P ≠ ⊥) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) (hext : IsPOnePlusTwo 3 ↥P) {U : Subgroup W}
    (hUstab : StableUnder (P ⊔ Subgroup.zpowers t) U)
    (hUfaith : ∀ y ∈ P, (∀ u ∈ U, y u = u) → y = 1)
    (hUmin : ∀ U₁ : Subgroup W, U₁ ≤ U → StableUnder (P ⊔ Subgroup.zpowers t) U₁ →
      (∀ y ∈ P, (∀ u ∈ U₁, y u = u) → y = 1) → U₁ = U) :
    rk ↥(commSub U P) = 6 ∧ commSub U (Subgroup.zpowers t) ≠ ⊥ := by
  classical
  haveI : CFSG.IsExtraspecial 3 ↥P := hext.1
  have hcardP : Nat.card ↥P = 27 := by rw [hext.2.1]; norm_num
  let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hPG : P ≤ G := le_sup_left
  have ht2sq : (t : MulAut W) ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hW'2 : ∀ w : ↥U, w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using hW2 (w : W)
  have hGU : G ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro v
    exact ⟨fun hv => by simpa using hUstab x⁻¹ (G.inv_mem hx) (x v) hv,
      fun hv => hUstab x hx v hv⟩
  let σ : G →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hGU)
  have hσ : ∀ (x : G) (u : ↥U), ((σ x) u : W) = (x : MulAut W) (u : W) := by
    intro x u
    change (((resHom U) (Subgroup.inclusion hGU x)) u : W) = (x : MulAut W) (u : W)
    rw [resHom_apply]
    rfl
  let t' : MulAut ↥U := σ ⟨t, htG⟩
  have ht'sq : t' ^ 2 = 1 := by
    change σ ⟨t, htG⟩ ^ 2 = 1
    rw [← map_pow]
    have h2 : (⟨t, htG⟩ : G) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one] using ht2sq
    rw [h2, map_one]
  have hmapσ : (P.subgroupOf G).map σ = autSub P U := by
    rw [show σ = (resHom U).comp (Subgroup.inclusion hGU) from rfl]
    rw [← Subgroup.map_map (K := P.subgroupOf G) (g := resHom U)
      (f := Subgroup.inclusion hGU)]
    rw [w16g_map_inclusion_subgroupOf hGU hPG]
    rfl
  have hzp : ((Subgroup.zpowers t).subgroupOf G).map σ = Subgroup.zpowers t' := by
    have h1 : (Subgroup.zpowers t).subgroupOf G = Subgroup.zpowers (⟨t, htG⟩ : G) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rw [h1, MonoidHom.map_zpowers]
  have hG'eq : autSub P U ⊔ Subgroup.zpowers t' = σ.range := by
    have hsub : (P.subgroupOf G) ⊔ ((Subgroup.zpowers t).subgroupOf G) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPG (Subgroup.zpowers_le.mpr htG),
        show P ⊔ Subgroup.zpowers t = G from rfl, Subgroup.subgroupOf_self]
    calc autSub P U ⊔ Subgroup.zpowers t'
        = (P.subgroupOf G).map σ ⊔ ((Subgroup.zpowers t).subgroupOf G).map σ := by
            rw [hmapσ, hzp]
      _ = ((P.subgroupOf G) ⊔ ((Subgroup.zpowers t).subgroupOf G)).map σ := by
            rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup G).map σ := by rw [hsub]
      _ = σ.range := (MonoidHom.range_eq_map σ).symm
  let ρ : P →* MulAut ↥U := σ.comp (Subgroup.inclusion hPG)
  have hρrange : ρ.range = autSub P U := by
    rw [show ρ = σ.comp (Subgroup.inclusion hPG) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range hPG, hmapσ]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      apply Subtype.ext
      apply hUfaith x x.2
      intro u hu
      have h1 := congrArg (fun φ : MulAut ↥U => (φ ⟨u, hu⟩ : W)) hx
      have h2 : ((ρ x) ⟨u, hu⟩ : W) = (x : MulAut W) (u : W) := by
        change ((σ (Subgroup.inclusion hPG x)) ⟨u, hu⟩ : W) = (x : MulAut W) (u : W)
        rw [hσ]
        rfl
      rw [h2] at h1
      simpa using h1
    · intro hx; rw [hx, map_one]
  let ePP' : ↥P ≃* ↥(autSub P U) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hcardP' : Nat.card ↥(autSub P U) = 27 := by
    rw [← Nat.card_congr ePP'.toEquiv]; exact hcardP
  have hP'grp : IsPGroup 3 ↥(autSub P U) := by
    intro y
    obtain ⟨x, rfl⟩ := ePP'.surjective y
    obtain ⟨n, hn⟩ := hPgrp x
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hP'ne : autSub P U ≠ ⊥ := by
    intro hbot
    apply hPne
    have hcard : Nat.card ↥P = 1 := by
      rw [Nat.card_congr ePP'.toEquiv, hbot]
      simp
    exact (Subgroup.card_eq_one).mp hcard
  have ht'norm : ∀ x ∈ autSub P U, t' * x * t'⁻¹ ∈ autSub P U := by
    intro x hx
    rw [← hmapσ] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨t, htG⟩ * q * ⟨t, htG⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change t * (q : MulAut W) * t⁻¹ ∈ P
      exact hn _ (Subgroup.mem_subgroupOf.mp hq)
    · rw [map_mul, map_mul, map_inv]
  have hcomm' : ⁅autSub P U, Subgroup.zpowers t'⁆ = autSub P U := by
    have hcommG : ⁅P.subgroupOf G, (Subgroup.zpowers t).subgroupOf G⁆ = P.subgroupOf G := by
      rw [w16g_subgroupOf_commutator hPG (Subgroup.zpowers_le.mpr htG), hc]
    have hmap := Subgroup.map_commutator (P.subgroupOf G) ((Subgroup.zpowers t).subgroupOf G) σ
    rw [hcommG, hmapσ, hzp] at hmap
    exact hmap.symm
  have ht'ne : t' ≠ 1 := by
    intro h1
    have hbot : ⁅autSub P U, Subgroup.zpowers t'⁆ = ⊥ := by
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    rw [hcomm'] at hbot
    exact hP'ne hbot
  have ht'2 : orderOf t' = 2 := orderOf_eq_prime ht'sq ht'ne
  have hmaple := w16g_map_commSub_le σ hσ ⟨t, htG⟩
  have hle : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    calc rk ↥(commSub ⊤ (Subgroup.zpowers t'))
        = rk ↥((commSub ⊤ (Subgroup.zpowers t')).map U.subtype) := by
            unfold rk
            rw [Subgroup.card_map_of_injective (K := commSub ⊤ (Subgroup.zpowers t'))
              (f := U.subtype) U.subtype_injective]
      _ ≤ rk ↥(commSub U (Subgroup.zpowers t)) := rk_mono hmaple
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono (commSub_mono le_top le_rfl)
  have htrk' : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 3 := hle.trans hrk
  have hmin' : MinFaith132 t' (autSub P U) := by
    intro U₁ hU₁ hU₁f
    have hU₀stab : StableUnder G (U₁.map U.subtype) := by
      rw [← w16g_stableUnder_range σ hσ U₁, ← hG'eq]
      exact hU₁
    have hU₀Pfaith : ∀ y ∈ P, (∀ u ∈ U₁.map U.subtype, y u = u) → y = 1 := by
      intro y hy hyfix
      have hσy : σ ⟨y, hPG hy⟩ = 1 := by
        refine hU₁f _ ?_ ?_
        · rw [hG'eq]
          exact MonoidHom.mem_range.mpr ⟨⟨y, hPG hy⟩, rfl⟩
        · intro u hu
          apply Subtype.ext
          rw [hσ]
          exact hyfix (u : W) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
      have h1 : ρ ⟨y, hy⟩ = 1 := by
        rw [show ρ ⟨y, hy⟩ = σ ⟨y, hPG hy⟩ from rfl, hσy]
      have h2 := hρinj (show ρ ⟨y, hy⟩ = ρ 1 by rw [h1, map_one])
      exact congrArg Subtype.val h2
    have heq : U₁.map U.subtype = U :=
      hUmin _ (Subgroup.map_subtype_le _) hU₀stab hU₀Pfaith
    have htop : (⊤ : Subgroup ↥U).map U.subtype = U := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective U.subtype_injective (heq.trans htop.symm)
  have hcardle : Nat.card ↥(autSub P U) ≤ 27 := hcardP'.le
  have hconc := hMin (↥U) hW'2 t' ht'2 htrk' 3 (autSub P U) Nat.prime_three hP'grp hP'ne
    ht'norm hcomm' hcardle hmin'
  have hUtne : commSub U (Subgroup.zpowers t) ≠ ⊥ := by
    intro hbot
    have htfix : ∀ u ∈ U, t u = u := by
      intro u hu
      exact mem_fixV_zpowers_iff_apply.mp (commSub_eq_bot_iff.mp hbot hu)
    have ht'one : t' = 1 := by
      ext u
      have h1 : ((t' u : ↥U) : W) = t (u : W) := by
        change ((σ ⟨t, htG⟩ u : ↥U) : W) = t (u : W)
        rw [hσ]
      rw [h1]
      simp only [MulAut.one_apply]
      exact htfix (u : W) u.2
    have hbot2 : ⁅autSub P U, Subgroup.zpowers t'⁆ = ⊥ := by
      rw [ht'one, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    rw [hcomm'] at hbot2
    exact hP'ne hbot2
  have hrkeq : rk ↥(commSub U P) = rk ↥(commSub ⊤ (autSub P U)) := by
    have hmapcomm := w16g_map_commSub_subgroup (P := P) σ hσ hPG
    rw [hmapσ] at hmapcomm
    rw [← hmapcomm]
    unfold rk
    rw [Subgroup.card_map_of_injective U.subtype_injective]
  rcases hconc with ⟨hcyc, hcard9⟩ | ⟨k, hk, hE⟩ | ⟨hP1, hrk6⟩ | ⟨hZ, hrk3, huniq⟩
  · exfalso
    omega
  · exfalso
    have hEcomm : IsMulCommutative ↥(autSub P U) := by
      obtain ⟨e⟩ := hE
      exact IsMulCommutative.of_comm fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])
    have hPcomm : IsMulCommutative ↥P :=
      IsMulCommutative.of_comm fun a b =>
        ePP'.injective (by rw [map_mul, map_mul]; exact hEcomm.is_comm.comm _ _)
    exact w16g_not_comm_of_isExtraspecial (p := 3) (X := ↥P) hPcomm
  · exact ⟨hrkeq.trans hrk6, hUtne⟩
  · exfalso
    have hcard81 : Nat.card ↥(autSub P U) = 81 := by
      rcases hZ with hZ | hZ
      · exact w16g_card_isZ3Times hZ
      · exact w16g_card_isZ3WrZ3 hZ
    omega

theorem w16h_ext_faithful_part (hMin : W4Lem13_2MinLe 27) (h : Cfg132 t P)
    (hext : IsPOnePlusTwo 3 ↥P) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y) (hzt : t * z * t⁻¹ = z)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) :
    rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) = 2 ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers z)) = 6 := by
  let zs : Subgroup (MulAut W) := Subgroup.zpowers z
  let M : Subgroup W := commSub ⊤ zs
  let D : Subgroup W := fixV zs
  change rk ↥(commSub M (Subgroup.zpowers t)) = 2 ∧ rk ↥M = 6
  have hz3pow : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz3] at this
    exact this
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at this
    exact this
  have htz : t * z = z * t := by
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hzt]
  have hodd : Odd (Nat.card zs) := by
    change Odd (Nat.card (Subgroup.zpowers z))
    rw [Nat.card_zpowers, hz3]
    decide
  have hcompl : IsCompl D M := by
    have hc := isCompl_fixV_commV_of_odd zs hodd h.hW
    rw [commV_eq_commSub] at hc
    exact hc
  have hsup : D ⊔ M = ⊤ := hcompl.sup_eq_top
  have hinf : D ⊓ M = ⊥ := hcompl.inf_eq_bot
  have hMz : ∀ u ∈ M, z u ∈ M := by
    intro u hu
    change u ∈ commSub ⊤ zs at hu
    change z u ∈ commSub ⊤ zs
    refine CFSG.Quasithin.Asc81c.Pf.commSub_stable_of_commute (X := zs) (fun x hx => ?_) hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.refl z).zpow_right n).eq
  have hMt : ∀ u ∈ M, t u ∈ M := by
    intro u hu
    change u ∈ commSub ⊤ zs at hu
    change t u ∈ commSub ⊤ zs
    refine CFSG.Quasithin.Asc81c.Pf.commSub_stable_of_commute (X := zs) (fun x hx => ?_) hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute t z from htz).zpow_right n).eq
  have hMne : M ≠ ⊥ := by
    intro hbot
    have hzfix : ∀ w : W, z w = w := by
      intro w
      have htop : (⊤ : Subgroup W) ≤ fixV zs := commSub_eq_bot_iff.mp hbot
      exact mem_fixV_zpowers_iff_apply.mp (htop (Subgroup.mem_top w))
    have hz1 : z = 1 := by ext w; exact hzfix w
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3
  have htD : ∀ u ∈ D, t u ∈ D := by
    intro u hu
    change u ∈ fixV zs at hu
    change t u ∈ fixV zs
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    calc z (t u) = t (z u) := by rw [← MulAut.mul_apply, htz.symm, MulAut.mul_apply]
      _ = t u := by rw [hu]
  have hPD : ∀ x ∈ P, ∀ u ∈ D, x u ∈ D := by
    intro x hx u hu
    change u ∈ fixV zs at hu
    change x u ∈ fixV zs
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    calc z (x u) = x (z u) := by rw [← MulAut.mul_apply, (hzc x hx).symm, MulAut.mul_apply]
      _ = x u := by rw [hu]
  have hMt' : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ M, x u ∈ M := by
    have htstabM : t ∈ stabSub M := by
      rw [mem_stabSub]
      intro u
      refine ⟨fun htu => ?_, hMt u⟩
      have h := hMt (t u) htu
      rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h
    intro x hx u hu
    exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr htstabM hx) u).2 hu
  have hKleM : commSub M (Subgroup.zpowers t) ≤ M := commSub_le_of_invariant hMt'
  have hKstabz : ∀ u ∈ commSub M (Subgroup.zpowers t), z u ∈ commSub M (Subgroup.zpowers t) :=
    w16g_commSub_stable_of_commute (M := M) (X := Subgroup.zpowers t) (c := z)
      (fun x hx => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ((show Commute z t from htz.symm).zpow_right n).eq) hMz
  have hKfix : ∀ u ∈ commSub M (Subgroup.zpowers t), z u = u → u = 1 := by
    intro u hu hzu
    have h1 : u ∈ M := hKleM hu
    have h2 : u ∈ D := by
      change u ∈ fixV zs
      exact mem_fixV_zpowers_iff_apply.mpr hzu
    have h3 : u ∈ D ⊓ M := ⟨h2, h1⟩
    rw [hinf] at h3
    exact Subgroup.mem_bot.mp h3
  have hKle3 : rk ↥(commSub M (Subgroup.zpowers t)) ≤ 3 :=
    le_trans (rk_mono (commSub_mono le_top le_rfl)) h.hrk
  have hKne : commSub M (Subgroup.zpowers t) ≠ ⊥ := by
    intro hKbot
    have htfixM : ∀ u ∈ M, t u = u := by
      intro u hu
      exact mem_fixV_zpowers_iff_apply.mp (commSub_eq_bot_iff.mp hKbot hu)
    have htcommD : ∀ u : W, t u * u⁻¹ ∈ D := by
      intro u
      obtain ⟨d, hd, m, hm, hdm⟩ :=
        Subgroup.mem_sup.mp (by rw [hsup]; exact Subgroup.mem_top u)
      rw [← hdm, map_mul]
      have htd : t d * d⁻¹ ∈ D := D.mul_mem (htD d hd) (D.inv_mem hd)
      have htm : t m * m⁻¹ ∈ D := by
        have hmem : t m * m⁻¹ ∈ commSub M (Subgroup.zpowers t) :=
          Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, m, hm, rfl⟩
        rw [hKbot] at hmem
        rw [Subgroup.mem_bot.mp hmem]
        exact D.one_mem
      have hprod : t d * t m * (d * m)⁻¹ = (t d * d⁻¹) * (t m * m⁻¹) := by
        rw [mul_inv_rev]; ac_rfl
      rw [hprod]
      exact D.mul_mem htd htm
    have htriv := w16h_acts_trivially_of_comm_eq_self htt h.hn h.hc hPD htD htcommD
    obtain ⟨⟨u, huM⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
    have hzu : z u = u := by
      have h1 : z u * u⁻¹ ∈ D := htriv z hzP u
      have h2 : z u * u⁻¹ ∈ M := M.mul_mem (hMz u huM) (M.inv_mem huM)
      have h3 : z u * u⁻¹ ∈ D ⊓ M := ⟨h1, h2⟩
      rw [hinf] at h3
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)
    have hcon : u ∈ D ⊓ M := by
      refine ⟨?_, huM⟩
      change u ∈ fixV zs
      exact mem_fixV_zpowers_iff_apply.mpr hzu
    rw [hinf] at hcon
    exact hu1 (Subtype.ext (Subgroup.mem_bot.mp hcon))
  have hK2 : rk ↥(commSub M (Subgroup.zpowers t)) = 2 := by
    have hge1 : 1 ≤ rk ↥(commSub M (Subgroup.zpowers t)) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact hKne ((rk_eq_zero_iff h.hW).mp h0)
    have heven := w16h_even_rk_of_fixedFree h.hW hz3pow hKstabz hKfix
    obtain ⟨m, hm⟩ := heven
    omega
  refine ⟨hK2, ?_⟩
  · classical
    haveI : CFSG.IsExtraspecial 3 ↥P := hext.1
    have hPM : ∀ x ∈ P, ∀ u ∈ M, x u ∈ M := by
      intro x hx u hu
      change u ∈ commSub ⊤ zs at hu
      change x u ∈ commSub ⊤ zs
      exact w16g_commSub_stable_of_commute (M := ⊤) (X := zs) (c := x)
        (fun y hy => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact ((show Commute x z from hzc x hx).zpow_right n).eq)
        (fun w _ => Subgroup.mem_top (x w)) u hu
    let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
    have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hPG : P ≤ G := le_sup_left
    have hzG : z ∈ G := hPG hzP
    have hGM : StableUnder G M := by
      change StableUnder (P ⊔ Subgroup.zpowers t) M
      exact w16g_stableUnder_sup_group (fun x hx u hu => hPM x hx u hu)
        (fun x hx u hu => hMt' x hx u hu)
    have hPfaith : ∀ x ∈ P, (∀ u ∈ M, x u = u) → x = 1 := by
      intro x hx hxfix
      by_contra hxne
      let N : Subgroup ↥P := (centSub M).comap P.subtype
      have hxN : (⟨x, hx⟩ : ↥P) ∈ N := by
        rw [Subgroup.mem_comap, mem_centSub]
        exact hxfix
      have hxNne : (⟨x, hx⟩ : ↥P) ≠ 1 := fun h => hxne (congrArg Subtype.val h)
      have hNne : N ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.mem_bot] at hxN
        exact hxNne hxN
      have hNnormal : N.Normal := by
        refine ⟨fun a ha g => ?_⟩
        rw [Subgroup.mem_comap, mem_centSub] at ha ⊢
        intro u hu
        have hgu : (g : MulAut W)⁻¹ u ∈ M :=
          hPM (g : MulAut W)⁻¹ (P.inv_mem g.2) u hu
        have h1 : (a : MulAut W) ((g : MulAut W)⁻¹ u) = (g : MulAut W)⁻¹ u := ha _ hgu
        change (g : MulAut W) ((a : MulAut W) ((g : MulAut W)⁻¹ u)) = u
        rw [h1]
        simp
      have hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
        intro hcomm
        exact w16g_not_comm_of_isExtraspecial (p := 3) (X := ↥P)
          (IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2))
      have hcardP : Nat.card ↥P = 27 := by rw [hext.2.1]; norm_num
      have hZle := w16g_center_le_of_normal hnab hcardP hNnormal hNne
      have hzcenter : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hzc y.1 y.2)
      have hzN : (⟨z, hzP⟩ : ↥P) ∈ N := hZle hzcenter
      rw [Subgroup.mem_comap, mem_centSub] at hzN
      have hMbot : M = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro u hu
        have h1 : z u = u := hzN u hu
        have h2 : u ∈ D := by
          change u ∈ fixV zs
          exact mem_fixV_zpowers_iff_apply.mpr h1
        have h3 : u ∈ D ⊓ M := ⟨h2, hu⟩
        rw [hinf] at h3
        exact Subgroup.mem_bot.mp h3
      exact hMne hMbot
    let Good : Subgroup W → Prop := fun U =>
      U ≤ M ∧ StableUnder G U ∧ (∀ y ∈ P, (∀ u ∈ U, y u = u) → y = 1)
    have hex : ∃ n, ∃ U, Good U ∧ Nat.card U = n :=
      ⟨Nat.card M, M, ⟨le_rfl, hGM, hPfaith⟩, rfl⟩
    let U : Subgroup W := Classical.choose (Nat.find_spec hex)
    have hUspec : Good U ∧ Nat.card U = Nat.find hex :=
      Classical.choose_spec (Nat.find_spec hex)
    have hUleM : U ≤ M := hUspec.1.1
    have hUstab : StableUnder G U := hUspec.1.2.1
    have hUfaith : ∀ y ∈ P, (∀ u ∈ U, y u = u) → y = 1 := hUspec.1.2.2
    have hUmin : ∀ U₁ : Subgroup W, U₁ ≤ U → StableUnder G U₁ →
        (∀ y ∈ P, (∀ u ∈ U₁, y u = u) → y = 1) → U₁ = U := by
      intro U₁ hU₁le hU₁stab hU₁faith
      have hcard := Nat.find_min' hex
        ⟨U₁, ⟨hU₁le.trans hUleM, hU₁stab, hU₁faith⟩, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge hU₁le (by rw [hUspec.2]; exact hcard)
    obtain ⟨hU6, hUtne⟩ := w16g_rank_six_of_min_faithful hMin h.hW h.ht h.hrk h.hP h.hne
      h.hn h.hc hext hUstab hUfaith hUmin
    have hUtleM' : commSub U (Subgroup.zpowers t) ≤ commSub M (Subgroup.zpowers t) :=
      commSub_mono hUleM le_rfl
    have hUtleM : commSub U (Subgroup.zpowers t) ≤ M := hUtleM'.trans hKleM
    have hUtstabz : ∀ u ∈ commSub U (Subgroup.zpowers t),
        z u ∈ commSub U (Subgroup.zpowers t) :=
      w16g_commSub_stable_of_commute (M := U) (X := Subgroup.zpowers t) (c := z)
        (fun x hx => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          exact ((show Commute z t from htz.symm).zpow_right n).eq) (hUstab z hzG)
    have hUtfix : ∀ u ∈ commSub U (Subgroup.zpowers t), z u = u → u = 1 := by
      intro u hu hzu
      have h1 : u ∈ M := hUtleM hu
      have h2 : u ∈ D := by
        change u ∈ fixV zs
        exact mem_fixV_zpowers_iff_apply.mpr hzu
      have h3 : u ∈ D ⊓ M := ⟨h2, h1⟩
      rw [hinf] at h3
      exact Subgroup.mem_bot.mp h3
    have heven := w16h_even_rk_of_fixedFree h.hW hz3pow hUtstabz hUtfix
    obtain ⟨m, hm⟩ := heven
    have hUtge : 1 ≤ rk ↥(commSub U (Subgroup.zpowers t)) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact hUtne ((rk_eq_zero_iff h.hW).mp h0)
    have hUtrk : rk ↥(commSub U (Subgroup.zpowers t)) = 2 := by
      have hle2 : rk ↥(commSub U (Subgroup.zpowers t)) ≤ 2 := by
        have hmono := rk_mono hUtleM'
        rw [hK2] at hmono
        exact hmono
      omega
    have hUteq : commSub U (Subgroup.zpowers t) = commSub M (Subgroup.zpowers t) :=
      eq_of_le_of_rk_le h.hW hUtleM' (by rw [hUtrk, hK2])
    have hUt_le : commSub U (Subgroup.zpowers t) ≤ U :=
      commSub_le_of_invariant fun x hx w hw => hUstab x (Subgroup.zpowers_le.mpr htG hx) w hw
    have htm : ∀ m ∈ M, t m * m⁻¹ ∈ U := by
      intro m hm
      have h1 : t m * m⁻¹ ∈ commSub M (Subgroup.zpowers t) :=
        Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, m, hm, rfl⟩
      rw [← hUteq] at h1
      exact hUt_le h1
    have hSinfM : (U ⊔ D) ⊓ M = U := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxS, hxM⟩ := hx
        obtain ⟨u, hu, d, hd, rfl⟩ := Subgroup.mem_sup.mp hxS
        have hdM : d ∈ M := by
          have h : u⁻¹ * (u * d) ∈ M := M.mul_mem (M.inv_mem (hUleM hu)) hxM
          rwa [inv_mul_cancel_left] at h
        have hd1 : d = 1 := by
          have : d ∈ D ⊓ M := ⟨hd, hdM⟩
          rw [hinf] at this
          exact Subgroup.mem_bot.mp this
        rw [hd1, mul_one]
        exact hu
      · intro x hx
        exact ⟨Subgroup.mem_sup_left hx, hUleM hx⟩
    have hSP : ∀ x ∈ P, ∀ u ∈ U ⊔ D, x u ∈ U ⊔ D := by
      intro x hx u hu
      obtain ⟨u₁, hu₁, d, hd, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul]
      exact (U ⊔ D).mul_mem (Subgroup.mem_sup_left (hUstab x (hPG hx) u₁ hu₁))
        (Subgroup.mem_sup_right (hPD x hx d hd))
    have hSt : ∀ u ∈ U ⊔ D, t u ∈ U ⊔ D := by
      intro u hu
      obtain ⟨u₁, hu₁, d, hd, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul]
      exact (U ⊔ D).mul_mem (Subgroup.mem_sup_left (hUstab t htG u₁ hu₁))
        (Subgroup.mem_sup_right (htD d hd))
    have htS : ∀ u : W, t u * u⁻¹ ∈ U ⊔ D := by
      intro u
      obtain ⟨d, hd, m, hm, rfl⟩ :=
        Subgroup.mem_sup.mp (by rw [hsup]; exact Subgroup.mem_top u)
      have h1 : t (d * m) * (d * m)⁻¹ = (t d * d⁻¹) * (t m * m⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [h1]
      exact (U ⊔ D).mul_mem (Subgroup.mem_sup_right (D.mul_mem (htD d hd) (D.inv_mem hd)))
        (Subgroup.mem_sup_left (htm m hm))
    have htriv := w16h_acts_trivially_of_comm_eq_self htt h.hn h.hc hSP hSt htS
    have hzU : ∀ m ∈ M, z m * m⁻¹ ∈ U := by
      intro m hm
      have h1 : z m * m⁻¹ ∈ U ⊔ D := htriv z hzP m
      have h2 : z m * m⁻¹ ∈ M := M.mul_mem (hMz m hm) (M.inv_mem hm)
      have h3 : z m * m⁻¹ ∈ (U ⊔ D) ⊓ M := ⟨h1, h2⟩
      rwa [hSinfM] at h3
    have hMzcomm : commSub M zs = M := by
      change commSub (commSub ⊤ zs) zs = commSub ⊤ zs
      exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.commSub_commSub_eq h.hW hodd
    have hz2U : ∀ m ∈ M, (z ^ 2) m * m⁻¹ ∈ U := by
      intro m hm
      have h1 : z (z m) * (z m)⁻¹ ∈ U := hzU (z m) (hMz m hm)
      have h2 : z m * m⁻¹ ∈ U := hzU m hm
      have hkey : (z ^ 2) m * m⁻¹ = (z (z m) * (z m)⁻¹) * (z m * m⁻¹) := by
        rw [pow_two, MulAut.mul_apply]
        group
      rw [hkey]
      exact U.mul_mem h1 h2
    have hzpow : ∀ n : ℤ, ∀ m ∈ M, (z ^ n) m * m⁻¹ ∈ U := by
      intro n m hm
      have hz3zpow : z ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, hz3pow]
      have hmod := zpow_eq_zpow_emod n hz3zpow
      rcases w16g_int_emod_three n with h | h | h
      · rw [hmod, h, zpow_zero]; simp
      · rw [hmod, h, zpow_one]; exact hzU m hm
      · rw [hmod, h, zpow_ofNat]
        exact hz2U m hm
    have hMzleU : commSub M zs ≤ U := by
      rw [commSub, Subgroup.closure_le]
      rintro c ⟨x, hx, m, hm, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact hzpow n m hm
    have hMleU : M ≤ U := by
      rw [← hMzcomm]
      exact hMzleU
    have hMU : M = U := le_antisymm hMleU hUleM
    have hMP : commSub M P = M := by
      refine le_antisymm (commSub_le_of_invariant hPM) ?_
      calc M = commSub M zs := hMzcomm.symm
        _ ≤ commSub M P := commSub_mono le_rfl (Subgroup.zpowers_le.mpr hzP)
    rw [← hMP, hMU]
    exact hU6

private theorem w16g_rank_le_two_of_transvection {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) {t x : MulAut V} (ht2 : t ^ 2 = 1) (hx3 : x ^ 3 = 1)
    (htx : t * x * t⁻¹ = x⁻¹) (hCx : ∀ v : V, x v = v → v = 1)
    (hE1 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 1) : rk V ≤ 2 := by
  let E : Subgroup V := commSub ⊤ (Subgroup.zpowers t)
  have hinv : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by
    rw [← pow_two]; exact hV2 w)
  have hinj : ∀ w : V, x w * w = 1 → w = 1 := by
    intro w hw
    apply hCx
    rw [← mul_inv_eq_one, hinv w]
    exact hw
  have hrel : ∀ w : V, w * x w * (x * x) w = 1 := by
    intro w
    have hx3w : x ((x * x) w) = w := by
      have h : x * x * x = 1 := by
        rw [show x * x * x = x ^ 3 from rfl]; exact hx3
      rw [show x ((x * x) w) = (x * x * x) w from rfl, h, MulAut.one_apply]
    have hx2w : x (x w) = (x * x) w := by rw [MulAut.mul_apply]
    have h1 : x ((x * x) w * x w * w) * ((x * x) w * x w * w) = 1 := by
      simp only [map_mul]
      rw [hx3w, hx2w]
      rw [show w * (x * x) w * x w * ((x * x) w * x w * w)
          = (w * w) * ((x * x) w * (x * x) w) * (x w * x w) from by ac_rfl]
      rw [show w * w = 1 from by rw [← pow_two]; exact hV2 w,
        show (x * x) w * (x * x) w = 1 from by rw [← pow_two]; exact hV2 _,
        show x w * x w = 1 from by rw [← pow_two]; exact hV2 _]
      simp
    have h2 := hinj _ h1
    rw [← h2]
    ac_rfl
  have hle : (⊤ : Subgroup V) ≤ E ⊔ E.map (x ^ 2).toMonoidHom := by
    intro v _
    have he1 : t (x v) * (x v)⁻¹ ∈ E :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, x v, Subgroup.mem_top _, rfl⟩
    have he2 : t v * v⁻¹ ∈ E :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, Subgroup.mem_top _, rfl⟩
    have htx' : t * x = x⁻¹ * t := by rw [← htx]; group
    have hw : x⁻¹ (t v) * x (t v) = t v := by
      have h := hrel (x⁻¹ (t v))
      rw [show x (x⁻¹ (t v)) = t v from by simp,
        show (x * x) (x⁻¹ (t v)) = x (t v) from by
          rw [MulAut.mul_apply, show x (x⁻¹ (t v)) = t v from by simp]] at h
      have h' : x⁻¹ (t v) * x (t v) * t v = 1 := by
        rw [show x⁻¹ (t v) * x (t v) * t v = x⁻¹ (t v) * t v * x (t v) from by ac_rfl]
        exact h
      have h2 : x⁻¹ (t v) * x (t v) = (t v)⁻¹ := eq_inv_of_mul_eq_one_left h'
      rwa [hinv (t v)] at h2
    have hkey1 : t v = (t (x v) * (x v)⁻¹) * (x (t v * v⁻¹)) := by
      have htxv : t (x v) = x⁻¹ (t v) := by
        rw [show t (x v) = (t * x) v from rfl, htx', MulAut.mul_apply]
      have hxvv : x v * x v = 1 := by rw [← pow_two]; exact hV2 (x v)
      rw [map_mul, map_inv, htxv, hinv (x v)]
      calc t v = x⁻¹ (t v) * x (t v) := hw.symm
        _ = x⁻¹ (t v) * x v * (x (t v) * x v) := by
            rw [show x⁻¹ (t v) * x v * (x (t v) * x v)
                = (x⁻¹ (t v) * x (t v)) * (x v * x v) from by ac_rfl,
              hxvv, mul_one]
    have hkey2 : (t v * v⁻¹) * x (t v * v⁻¹) = (x * x) (t v * v⁻¹) := by
      have h := hrel (t v * v⁻¹)
      have h1 : (t v * v⁻¹) * x (t v * v⁻¹)
          = ((x * x) (t v * v⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left h
      rwa [hinv ((x * x) (t v * v⁻¹))] at h1
    have hv : v = (t (x v) * (x v)⁻¹) * (x ^ 2) (t v * v⁻¹) := by
      let e₁ : V := t (x v) * (x v)⁻¹
      let e₂ : V := t v * v⁻¹
      have hk1 : t v = e₁ * x e₂ := hkey1
      have hk2 : e₂ * x e₂ = (x ^ 2) e₂ := by
        rw [hkey2, pow_two, MulAut.mul_apply]
      have he2 : e₂ * t v = v := by
        change (t v * v⁻¹) * t v = v
        rw [show (t v * v⁻¹) * t v = (t v * t v) * v⁻¹ from by ac_rfl,
          show t v * t v = 1 from by rw [← pow_two]; exact hV2 (t v), one_mul, hinv v]
      calc v = e₂ * t v := he2.symm
        _ = e₂ * (e₁ * x e₂) := congrArg (fun w => e₂ * w) hk1
        _ = e₁ * (e₂ * x e₂) := by ac_rfl
        _ = e₁ * (x ^ 2) e₂ := congrArg (fun w => e₁ * w) hk2
    rw [hv]
    refine (E ⊔ E.map (x ^ 2).toMonoidHom).mul_mem (Subgroup.mem_sup_left he1) ?_
    exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t v * v⁻¹, he2, rfl⟩)
  have hcard : rk ↥(E.map (x ^ 2).toMonoidHom) = rk ↥E := by
    unfold rk
    rw [Subgroup.card_map_of_injective (x ^ 2).injective]
  calc rk V = rk (⊤ : Subgroup V) := rk_top.symm
    _ ≤ rk ↥(E ⊔ E.map (x ^ 2).toMonoidHom) := rk_mono hle
    _ ≤ rk ↥E + rk ↥(E.map (x ^ 2).toMonoidHom) := by
        have hh := rk_sup_add_rk_inf E (E.map (x ^ 2).toMonoidHom)
        omega
    _ = 1 + 1 := by
        rw [hcard, show rk ↥E = 1 from hE1]
    _ = 2 := by norm_num

private theorem w16g_commSub_stable_of_normalizes {D : Subgroup W} {X : Subgroup (MulAut W)}
    {c : MulAut W} (hD : ∀ u ∈ D, c u ∈ D) (hX : ∀ x ∈ X, c * x * c⁻¹ ∈ X) :
    ∀ u ∈ commSub D X, c u ∈ commSub D X := by
  have hmapD : D.map c.toMonoidHom = D := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      exact hD v hv
    · rw [Subgroup.card_map_of_injective c.injective]
  have hmapX : X.map (MulAut.conj c).toMonoidHom = X := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      show c * x * c⁻¹ ∈ X
      exact hX x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have h := CFSG.Quasithin.Z391.commSub_map_conj c D X
  rw [hmapD, hmapX] at h
  intro u hu
  rw [h]
  exact ⟨u, hu, rfl⟩

theorem w16h_ext_trivial_part (h131 : W4Lem13_1) (h : Cfg132 t P) (hext : IsPOnePlusTwo 3 ↥P)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, y * z = z * y)
    (hzt : t * z * t⁻¹ = z)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z)
    (hD : rk ↥(commSub (fixV (Subgroup.zpowers z)) (Subgroup.zpowers t)) ≤ 1) :
    (rk ↥(commSub (fixV (Subgroup.zpowers z)) P) = 0 ∨
      rk ↥(commSub (fixV (Subgroup.zpowers z)) P) = 2) ∧
    (rk ↥(commSub (fixV (Subgroup.zpowers z)) (Subgroup.zpowers t)) = 0 →
      rk ↥(commSub (fixV (Subgroup.zpowers z)) P) = 0) := by
  classical
  let zs : Subgroup (MulAut W) := Subgroup.zpowers z
  let D : Subgroup W := fixV zs
  let D' : Subgroup W := commSub D P
  change (rk ↥D' = 0 ∨ rk ↥D' = 2) ∧
    (rk ↥(commSub D (Subgroup.zpowers t)) = 0 → rk ↥D' = 0)
  have htt : t * t = 1 := by
    have hpoweq := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at hpoweq
    exact hpoweq
  have ht2sq : t ^ 2 = 1 := by rw [pow_two]; exact htt
  have htz : t * z = z * t := by
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hzt]
  have hcardP : Nat.card ↥P = 27 := by rw [hext.2.1]; norm_num
  have hPodd : Odd (Nat.card ↥P) := by rw [hcardP]; decide
  have hPD : ∀ x ∈ P, ∀ u ∈ D, x u ∈ D := by
    intro x hx u hu
    change u ∈ fixV zs at hu
    change x u ∈ fixV zs
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    calc z (x u) = x (z u) := by
          rw [← MulAut.mul_apply, (hzc x hx).symm, MulAut.mul_apply]
      _ = x u := by rw [hu]
  have hDt : ∀ u ∈ D, t u ∈ D := by
    intro u hu
    change u ∈ fixV zs at hu
    change t u ∈ fixV zs
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    calc z (t u) = t (z u) := by rw [← MulAut.mul_apply, htz.symm, MulAut.mul_apply]
      _ = t u := by rw [hu]
  have hD'le : D' ≤ D := commSub_le_of_invariant hPD
  have hD'Pinv : ∀ x ∈ P, ∀ u ∈ D', x u ∈ D' := by
    intro x hx u hu
    exact w16g_commSub_stable_of_normalizes (D := D) (X := P) (c := x)
      (fun v hv => hPD x hx v hv)
      (fun y hy => P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) u hu
  have hD't : ∀ u ∈ D', t u ∈ D' :=
    w16g_commSub_stable_of_normalizes (D := D) (X := P) (c := t) hDt h.hn
  have hD'zp : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ D', x u ∈ D' := by
    intro x hx u hu
    rcases w16g_zpow_eq_one_or_self htt hx with h1 | h1
    · rw [h1]; simpa using hu
    · rw [h1]; exact hD't u hu
  have hD'stab : StableUnder (P ⊔ Subgroup.zpowers t) D' :=
    w16g_stableUnder_sup_group hD'Pinv hD'zp
  have htopfix : commSub (⊤ : Subgroup W) P ⊓ fixV P = ⊥ := by
    have h2 := (CFSG.Quasithin.coprime_decomp hPodd h.hW (W := (⊤ : Subgroup W))
      (fun g _ w _ => Subgroup.mem_top (g w))).2
    simpa using h2
  have hD'fixP : D' ⊓ fixV P = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact Subgroup.mem_bot.mp
      (htopfix ▸ ⟨commSub_mono le_top le_rfl hu.1, hu.2⟩)
  have hD'P : commSub D' P = D' := by
    have h1 := (CFSG.Quasithin.coprime_decomp hPodd h.hW (W := D') hD'Pinv).1
    rwa [hD'fixP, sup_bot_eq] at h1
  by_cases hbot : D' = ⊥
  · refine ⟨Or.inl ?_, ?_⟩
    · rw [hbot, rk_bot]
    · intro _; rw [hbot, rk_bot]
  · let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
    have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hPG : P ≤ G := le_sup_left
    have hGD' : G ≤ stabSub D' := by
      change P ⊔ Subgroup.zpowers t ≤ stabSub D'
      exact w16g_le_stabSub_of_stableUnder hD'stab
    let σ : G →* MulAut ↥D' := (resHom D').comp (Subgroup.inclusion hGD')
    have hσ : ∀ (x : G) (u : ↥D'), ((σ x) u : W) = (x : MulAut W) (u : W) := by
      intro x u
      change (((resHom D') (Subgroup.inclusion hGD' x)) u : W) = (x : MulAut W) (u : W)
      rw [resHom_apply]
      rfl
    let t' : MulAut ↥D' := σ ⟨t, htG⟩
    have ht'2sq : t' ^ 2 = 1 := by
      change σ ⟨t, htG⟩ ^ 2 = 1
      rw [← map_pow]
      have h2 : (⟨t, htG⟩ : G) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [Subgroup.coe_pow, Subgroup.coe_one] using ht2sq
      rw [h2, map_one]
    have hmapσ : (P.subgroupOf G).map σ = autSub P D' := by
      rw [show σ = (resHom D').comp (Subgroup.inclusion hGD') from rfl]
      rw [← Subgroup.map_map (K := P.subgroupOf G) (g := resHom D')
        (f := Subgroup.inclusion hGD')]
      rw [w16g_map_inclusion_subgroupOf hGD' hPG]
      rfl
    have hzp : ((Subgroup.zpowers t).subgroupOf G).map σ = Subgroup.zpowers t' := by
      have h1 : (Subgroup.zpowers t).subgroupOf G = Subgroup.zpowers (⟨t, htG⟩ : G) := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
        constructor
        · rintro ⟨n, hn⟩
          exact ⟨n, Subtype.ext (by simpa using hn)⟩
        · rintro ⟨n, hn⟩
          exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      rw [h1, MonoidHom.map_zpowers]
    have ht'norm : ∀ x ∈ autSub P D', t' * x * t'⁻¹ ∈ autSub P D' := by
      intro x hx
      rw [← hmapσ] at hx ⊢
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨⟨t, htG⟩ * q * ⟨t, htG⟩⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        change t * (q : MulAut W) * t⁻¹ ∈ P
        exact h.hn _ (Subgroup.mem_subgroupOf.mp hq)
      · rw [map_mul, map_mul, map_inv]
    have hcomm' : ⁅autSub P D', Subgroup.zpowers t'⁆ = autSub P D' := by
      have hcommG : ⁅P.subgroupOf G, (Subgroup.zpowers t).subgroupOf G⁆ = P.subgroupOf G := by
        rw [w16g_subgroupOf_commutator hPG (Subgroup.zpowers_le.mpr htG), h.hc]
      have hmap := Subgroup.map_commutator (P.subgroupOf G)
        ((Subgroup.zpowers t).subgroupOf G) σ
      rw [hcommG, hmapσ, hzp] at hmap
      exact hmap.symm
    have hP'ne : autSub P D' ≠ ⊥ := by
      intro hbot'
      have hmapcomm : (commSub ⊤ (autSub P D')).map D'.subtype = commSub D' P := by
        have hh := w16g_map_commSub_subgroup (G := G) (U := D') (P := P) σ hσ hPG
        rwa [hmapσ] at hh
      have hzero : commSub (⊤ : Subgroup ↥D') (⊥ : Subgroup (MulAut ↥D')) = ⊥ := by
        rw [commSub_eq_bot_iff]
        intro x _
        rw [mem_fixV]
        intro g hg
        rw [Subgroup.mem_bot.mp hg]
        simp
      have hbot2 : commSub D' P = ⊥ := by
        rw [← hmapcomm, hbot', hzero, Subgroup.map_bot]
      rw [hD'P] at hbot2
      exact hbot hbot2
    have ht'ne : t' ≠ 1 := by
      intro hone
      have hb : ⁅autSub P D', Subgroup.zpowers t'⁆ = ⊥ := by
        rw [hone, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
      rw [hcomm'] at hb
      exact hP'ne hb
    have htri_map : (commSub ⊤ (Subgroup.zpowers t')).map D'.subtype
        = commSub D' (Subgroup.zpowers t) := by
      have hh := w16g_map_commSub_subgroup (G := G) (U := D')
        (P := Subgroup.zpowers t) σ hσ (Subgroup.zpowers_le.mpr htG)
      rwa [hzp] at hh
    have htri_le1 : rk ↥(commSub D' (Subgroup.zpowers t)) ≤ 1 :=
      (rk_mono (commSub_mono hD'le le_rfl)).trans hD
    have htri_ge1 : 1 ≤ rk ↥(commSub D' (Subgroup.zpowers t)) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      apply ht'ne
      have hbot2 : commSub D' (Subgroup.zpowers t) = ⊥ := (rk_eq_zero_iff h.hW).mp h0
      have hfix : D' ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp hbot2
      ext u
      have h1 : ((t' u : ↥D') : W) = t (u : W) := by
        change ((σ ⟨t, htG⟩ u : ↥D') : W) = t (u : W)
        rw [hσ]
      rw [h1]
      simp only [MulAut.one_apply]
      exact mem_fixV_zpowers_iff_apply.mp (hfix u.2)
    have htri_eq : rk ↥(commSub D' (Subgroup.zpowers t))
        = rk ↥(commSub ⊤ (Subgroup.zpowers t')) := by
      rw [← htri_map]
      unfold rk
      rw [Subgroup.card_map_of_injective (f := D'.subtype) D'.subtype_injective]
    have htri : rk ↥(commSub ⊤ (Subgroup.zpowers t')) = 1 := by
      rw [← htri_eq]
      exact le_antisymm htri_le1 htri_ge1
    have htr'3 : rk ↥(commSub ⊤ (Subgroup.zpowers t')) ≤ 3 := by omega
    have htrans : InducesTransvection t' ⊤ := by
      refine ⟨?_, htri⟩
      rw [mem_stabSub]
      intro u
      simp
    have hD'w2 : ∀ w : ↥D', w ^ 2 = 1 := by
      intro w
      apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one] using h.hW (w : W)
    have hP'grp : IsPGroup 3 ↥(autSub P D') := by
      rw [← hmapσ]
      have hPsub : IsPGroup 3 ↥(P.subgroupOf G) :=
        h.hP.comap_of_injective G.subtype G.subtype_injective
      exact IsPGroup.map hPsub σ
    have htt' : t' * t' = 1 := by rw [← pow_two]; exact ht'2sq
    have ht'2 : orderOf t' = 2 := orderOf_eq_prime ht'2sq ht'ne
    have hcardP'3 : Nat.card ↥(autSub P D') = 3 := by
      have h131' := (h131 ↥D' hD'w2 t' ht'2 htr'3 3 (autSub P D') Nat.prime_three
        hP'grp hP'ne ht'norm hcomm').2 (Or.inr htrans)
      simpa using h131'
    have hc_ne : ⁅autSub P D', Subgroup.zpowers t'⁆ ≠ ⊥ := by
      rw [hcomm']; exact hP'ne
    obtain ⟨x, hxP', hxord, hxinv⟩ :=
      exists_inverted_orderOf_eq_prime htt' Nat.prime_three hP'grp ht'norm hc_ne
    have hxgen : Subgroup.zpowers x = autSub P D' := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP') ?_
      rw [Nat.card_zpowers, hxord, hcardP'3]
    have hx3 : x ^ 3 = 1 := by
      have hx := pow_orderOf_eq_one x
      rw [hxord] at hx
      exact hx
    have hCx : ∀ v : ↥D', x v = v → v = 1 := by
      intro v hv
      have hvf : v ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff_apply.mpr hv
      have hall : ∀ y ∈ autSub P D', y v = v := by
        intro y hy
        rw [← hxgen] at hy
        exact (mem_fixV.mp hvf) y hy
      have hvfix : (v : W) ∈ fixV P := by
        rw [mem_fixV]
        intro p hp
        have hmem : σ ⟨p, hPG hp⟩ ∈ autSub P D' := by
          rw [← hmapσ]
          exact Subgroup.mem_map.mpr ⟨⟨p, hPG hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
        have h1 := hall (σ ⟨p, hPG hp⟩) hmem
        have h2 := congrArg Subtype.val h1
        rw [hσ] at h2
        exact h2
      have hvmem : (v : W) ∈ commSub (⊤ : Subgroup W) P :=
        commSub_mono le_top le_rfl v.2
      have hmem : (v : W) ∈ (⊥ : Subgroup W) := htopfix ▸ ⟨hvmem, hvfix⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    have heven : Even (rk ↥D') := by
      have hh := w16h_even_rk_of_fixedFree (W := ↥D') hD'w2 hx3 (S := ⊤)
        (fun u _ => Subgroup.mem_top (x u)) (fun u _ hu => hCx u hu)
      rwa [rk_top] at hh
    have hrkD'ne0 : rk ↥D' ≠ 0 := by
      intro h0
      exact hbot ((rk_eq_zero_iff h.hW).mp h0)
    have hge2 : 2 ≤ rk ↥D' := by
      obtain ⟨m, hm⟩ := heven
      have h1 : 1 ≤ rk ↥D' := Nat.one_le_iff_ne_zero.mpr hrkD'ne0
      omega
    have hle2 : rk ↥D' ≤ 2 :=
      w16g_rank_le_two_of_transvection (V := ↥D') hD'w2 ht'2sq hx3 hxinv hCx htri
    have hrkD' : rk ↥D' = 2 := le_antisymm hle2 hge2
    refine ⟨Or.inr hrkD', ?_⟩
    intro hE0
    exfalso
    have hEbot : commSub D (Subgroup.zpowers t) = ⊥ := (rk_eq_zero_iff h.hW).mp hE0
    have htri_ne : commSub D' (Subgroup.zpowers t) ≠ ⊥ := by
      intro hb
      rw [hb, rk_bot] at htri_ge1
      omega
    have hD'bot2 : commSub D' (Subgroup.zpowers t) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      exact Subgroup.mem_bot.mp (hEbot ▸ commSub_mono hD'le le_rfl hu)
    exact htri_ne hD'bot2
theorem w16h_rk_six_or_eight (hMin : W4Lem13_2MinLe 27) (h131 : W4Lem13_1) (h : Cfg132 t P)
    (hext : IsPOnePlusTwo 3 ↥P) :
    (rk ↥(commSub ⊤ P) = 6 ∨ rk ↥(commSub ⊤ P) = 8) ∧
      (rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 2 → rk ↥(commSub ⊤ P) = 6) := by
  obtain ⟨z, hzP, hz3, hzc, hzt, hZP⟩ := w16h_ext_center h hext
  obtain ⟨hK2, hM6⟩ := w16h_ext_faithful_part hMin h hext hzP hz3 hzc hzt hZP
  let zs : Subgroup (MulAut W) := Subgroup.zpowers z
  let D : Subgroup W := fixV zs
  let M : Subgroup W := commSub ⊤ zs
  have hK2' : rk ↥(commSub M (Subgroup.zpowers t)) = 2 := hK2
  have hM6' : rk ↥M = 6 := hM6
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at this
    exact this
  have htz : t * z = z * t := by
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hzt]
  have hodd : Odd (Nat.card zs) := by
    change Odd (Nat.card (Subgroup.zpowers z))
    rw [Nat.card_zpowers, hz3]
    decide
  have hcompl : IsCompl D M := by
    have hc := isCompl_fixV_commV_of_odd zs hodd h.hW
    rw [commV_eq_commSub] at hc
    exact hc
  have hsup : D ⊔ M = ⊤ := hcompl.sup_eq_top
  have hinf : D ⊓ M = ⊥ := hcompl.inf_eq_bot
  have hPM : ∀ x ∈ P, ∀ u ∈ M, x u ∈ M := by
    intro x hx u hu
    change u ∈ commSub ⊤ zs at hu
    change x u ∈ commSub ⊤ zs
    exact w16g_commSub_stable_of_commute (M := ⊤) (X := zs) (c := x)
      (fun y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((show Commute x z from hzc x hx).zpow_right n).eq)
      (fun w _ => Subgroup.mem_top (x w)) u hu
  have hPD : ∀ x ∈ P, ∀ u ∈ D, x u ∈ D := by
    intro x hx u hu
    change u ∈ fixV zs at hu
    change x u ∈ fixV zs
    exact w16g_fixV_stable_of_commute (X := zs) (c := x)
      (fun y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((show Commute x z from hzc x hx).zpow_right n).eq) u hu
  have hMt' : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ M, x u ∈ M := by
    have htM : ∀ u ∈ M, t u ∈ M := by
      intro u hu
      change t u ∈ commSub ⊤ zs
      exact w16g_commSub_stable_of_commute (M := ⊤) (X := zs) (c := t)
        (fun y hy => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact ((show Commute t z from htz).zpow_right n).eq)
        (fun w _ => Subgroup.mem_top (t w)) u hu
    have htstabM : t ∈ stabSub M := by
      rw [mem_stabSub]
      intro u
      exact ⟨fun htu => by
          have h1 := htM (t u) htu
          rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h1,
        htM u⟩
    intro x hx u hu
    exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr htstabM hx) u).2 hu
  have hDt' : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ D, x u ∈ D := by
    have htD : ∀ u ∈ D, t u ∈ D := by
      intro u hu
      change t u ∈ fixV zs
      exact w16g_fixV_stable_of_commute (X := zs) (c := t)
        (fun y hy => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact ((show Commute t z from htz).zpow_right n).eq) u hu
    have htstabD : t ∈ stabSub D := by
      rw [mem_stabSub]
      intro u
      exact ⟨fun htu => by
          have h1 := htD (t u) htu
          rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h1,
        htD u⟩
    intro x hx u hu
    exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr htstabD hx) u).2 hu
  have hMP : commSub M P = M := by
    refine le_antisymm (commSub_le_of_invariant hPM) ?_
    have h1 : commSub M zs = M := by
      change commSub (commSub ⊤ zs) zs = commSub ⊤ zs
      exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.commSub_commSub_eq h.hW hodd
    calc M = commSub M zs := h1.symm
      _ ≤ commSub M P := commSub_mono le_rfl (Subgroup.zpowers_le.mpr hzP)
  have hTM : commSub M (Subgroup.zpowers t) ≤ M := commSub_le_of_invariant hMt'
  have hD'P : commSub D P ≤ D := commSub_le_of_invariant hPD
  have hD'T : commSub D (Subgroup.zpowers t) ≤ D := commSub_le_of_invariant hDt'
  have hdisjP : commSub D P ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact Subgroup.mem_bot.mp (hinf ▸ ⟨hD'P hu.1, hu.2⟩)
  have hdisjT : commSub D (Subgroup.zpowers t) ⊓ commSub M (Subgroup.zpowers t) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact Subgroup.mem_bot.mp (hinf ▸ ⟨hD'T hu.1, hTM hu.2⟩)
  have hPdecomp : commSub ⊤ P = commSub D P ⊔ M := by
    rw [← hsup, w16g_commSub_sup_left, hMP]
  have hTdecomp : commSub ⊤ (Subgroup.zpowers t)
      = commSub D (Subgroup.zpowers t) ⊔ commSub M (Subgroup.zpowers t) := by
    rw [← hsup, w16g_commSub_sup_left]
  have hrankP : rk ↥(commSub ⊤ P) = rk ↥(commSub D P) + rk ↥M := by
    rw [hPdecomp]
    have hh := rk_sup_add_rk_inf (commSub D P) M
    rw [hdisjP, rk_bot, add_zero] at hh
    exact hh
  have hrankT : rk ↥(commSub ⊤ (Subgroup.zpowers t))
      = rk ↥(commSub D (Subgroup.zpowers t)) + rk ↥(commSub M (Subgroup.zpowers t)) := by
    rw [hTdecomp]
    have hh := rk_sup_add_rk_inf (commSub D (Subgroup.zpowers t))
      (commSub M (Subgroup.zpowers t))
    rw [hdisjT, rk_bot, add_zero] at hh
    exact hh
  have hDle1 : rk ↥(commSub (fixV (Subgroup.zpowers z)) (Subgroup.zpowers t)) ≤ 1 := by
    change rk ↥(commSub D (Subgroup.zpowers t)) ≤ 1
    have hh := h.hrk
    rw [hrankT, hK2'] at hh
    omega
  obtain ⟨hD'01, hD'cond⟩ := w16h_ext_trivial_part h131 h hext hzP hz3 hzc hzt hZP hDle1
  have hD'01' : rk ↥(commSub D P) = 0 ∨ rk ↥(commSub D P) = 2 := hD'01
  have hD'cond' : rk ↥(commSub D (Subgroup.zpowers t)) = 0 → rk ↥(commSub D P) = 0 :=
    hD'cond
  refine ⟨?_, ?_⟩
  · rw [hrankP, hM6']
    rcases hD'01' with h | h
    · left; omega
    · right; omega
  · intro ht2
    have hDt0 : rk ↥(commSub D (Subgroup.zpowers t)) = 0 := by
      have hh := ht2
      rw [hrankT, hK2'] at hh
      omega
    rw [hrankP, hM6', hD'cond' hDt0]

end CFSG.LocalAnalysis.WeakClosure81
