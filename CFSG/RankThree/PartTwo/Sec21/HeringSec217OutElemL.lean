module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutTrans
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutElemJ3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

theorem mem_normalizer_of_conj_mem_out {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y} {u : Y}
    (h : ∀ x ∈ K, u * x * u⁻¹ ∈ K) : u ∈ normalizer (K : Set Y) := by
  have hle : K.map (MulAut.conj u).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq := map_conj_eq_of_le hle
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact (mem_map_conj_iff_of_eq heq).symm

section ElemL

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.exists_u₀ (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    1944 ≤ Nat.card ↥(normalizer ((((A ⊓ L).subgroupOf L : Subgroup ↥L)) : Set ↥L)) ∧
      ∃ u₀ : ↥L, u₀ ∈ normalizer ((((A ⊓ L).subgroupOf L : Subgroup ↥L)) : Set ↥L) ∧
        orderOf u₀ = 8 := by
  have h72 := card_eq_72_of_isExtOf h.ext
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  set M : Subgroup G := L ⊓ Subgroup.normalizer (A : Set G) with hMdef
  have hMle : M ≤ Subgroup.normalizer (A : Set G) := inf_le_right
  set g : M →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hMle) with hg
  have hrange : g.range = starOf A L := by
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), hMle x.2⟩, Subgroup.mem_subgroupOf.2 x.2.1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), (Subgroup.mem_subgroupOf.1 hx), x.2⟩, rfl⟩
  have hAM : A ⊓ L ≤ M := fun x hx => ⟨hx.2, Subgroup.le_normalizer hx.1⟩
  have hker : (A ⊓ L).subgroupOf M ≤ g.ker := by
    intro x hx
    have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.1 hx).1
    rw [MonoidHom.mem_ker]
    ext y
    show (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
    rw [hab.1 _ hxA y y.2, mul_inv_cancel_right]
  have hmul := Subgroup.card_ker_mul_card_range g
  rw [hrange, h72] at hmul
  have h27 : 27 ≤ Nat.card g.ker := by
    calc 27 = Nat.card ↥(A ⊓ L) := (h.card_inf_eq h45).symm
      _ = Nat.card ↥((A ⊓ L).subgroupOf M) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).symm
      _ ≤ Nat.card g.ker := Subgroup.card_le_of_le hker
  have hM : 1944 ≤ Nat.card M := by nlinarith
  have hMN : M.subgroupOf L ≤ normalizer ((((A ⊓ L).subgroupOf L : Subgroup ↥L)) : Set ↥L) := by
    intro x hx
    have hxM : (x : G) ∈ M := Subgroup.mem_subgroupOf.1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 hxM.2 (y : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun hy => ⟨this.1 hy.1, (x * y * x⁻¹ : ↥L).2⟩, fun hy => ⟨this.2 hy.1, y.2⟩⟩
  have hcardM : Nat.card ↥(M.subgroupOf L) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  refine ⟨?_, ?_⟩
  · calc 1944 ≤ Nat.card M := hM
      _ = Nat.card ↥(M.subgroupOf L) := hcardM.symm
      _ ≤ _ := Subgroup.card_le_of_le hMN
  · obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h.ext
    have hz8 : orderOf (eQ.symm (Multiplicative.ofAdd (1 : ZMod 8))) = 8 := by
      have h1 := orderOf_injective eQ.symm.toMonoidHom eQ.symm.injective
        (Multiplicative.ofAdd (1 : ZMod 8))
      have h2 : orderOf (Multiplicative.ofAdd (1 : ZMod 8)) = 8 := by
        rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
      exact h1.trans h2
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (eQ.symm (Multiplicative.ofAdd (1 : ZMod 8)))
    have hx8 : 8 ∣ orderOf (x : MulAut A) := by
      have h1 : orderOf (QuotientGroup.mk x : ↥(starOf A L) ⧸ K) ∣ orderOf x :=
        orderOf_map_dvd (QuotientGroup.mk' K) x
      rw [hx, hz8] at h1
      rw [Subgroup.orderOf_coe]
      exact h1
    have hxr : (x : MulAut A) ∈ g.range := by rw [hrange]; exact x.2
    obtain ⟨m, hm⟩ := hxr
    have hm8 : 8 ∣ orderOf m := by
      have h1 : orderOf (g m) ∣ orderOf m := orderOf_map_dvd g m
      rw [hm] at h1
      exact dvd_trans hx8 h1
    have hk8 : orderOf (m ^ (orderOf m / 8)) = 8 :=
      orderOf_pow_orderOf_div (orderOf_pos m).ne' hm8
    have hu₀M : ((m ^ (orderOf m / 8) : ↥M) : G) ∈ M := (m ^ (orderOf m / 8)).2
    refine ⟨⟨((m ^ (orderOf m / 8) : ↥M) : G), hu₀M.1⟩, hMN (Subgroup.mem_subgroupOf.2 hu₀M), ?_⟩
    rw [← Subgroup.orderOf_coe]
    show orderOf (((m ^ (orderOf m / 8) : ↥M)) : G) = 8
    rw [Subgroup.orderOf_coe]
    exact hk8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.exists_u (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    ∃ u : G, u ∈ L ∧ u ∈ Subgroup.normalizer (A : Set G) ∧
      u ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) ∧
      u ∉ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) ∧
      orderOf u = 8 ∧ c * u = u * c ∧
      u ∈ Subgroup.normalizer ((iCore L a : Subgroup G) : Set G) ∧
      u ∈ Subgroup.normalizer ((A ⊓ iCore L a : Subgroup G) : Set G) ∧
      u ^ 4 ∉ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
  have hZ := h.center_eq_bot h45
  obtain ⟨l, I', hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hI'C, hI'perf, ⟨φ⟩, hI, hI'max, hD3, hDI, hDcomm,
    hCeq, hDeq, hDL⟩ := h.local_frame h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hlq3 : (l : ↥L ⧸ center ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hl3]; rfl
  have hlq1 : (l : ↥L ⧸ center ↥L) ≠ 1 := fun h1 => by
    have := (QuotientGroup.eq_one_iff l).1 h1
    rw [hZ, Subgroup.mem_bot] at this
    exact hl1 this
  have h5q := five_dvd_centralizer_of_nonCentral h.quot.some hlq3 hlq1 hlnc
  have h5 : 5 ∣ Nat.card (centralizer ({h.equivJ3 hZ l} : Set NativeSporadic.J3)) := by
    rw [h.equivJ3_apply hZ]; exact h5q
  have hFel : CFSG.IsElementaryAbelian 3 ((A ⊓ L).subgroupOf L) := by
    refine CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.2
      ⟨fun x hx y hy => Subtype.ext ?_, fun x hx => Subtype.ext ?_⟩
    · exact hab.1 _ (Subgroup.mem_subgroupOf.1 hx).1 _ (Subgroup.mem_subgroupOf.1 hy).1
    · have := hab.2 _ (Subgroup.mem_subgroupOf.1 hx).1
      simpa using this
  have hF27 : Nat.card ((A ⊓ L).subgroupOf L) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact h.card_inf_eq h45
  have hlF : l ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.2 ⟨hlA, l.2⟩
  obtain ⟨hN, u₀, hu₀N, hu₀⟩ := h.exists_u₀ h45
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ :=
    exists_u_J3Plain (h.equivJ3 hZ) hFel hF27 hlF hl1 h5 hN hu₀N hu₀
  have hulz : (u : G) * (l : G) * (u : G)⁻¹ ∈ Subgroup.zpowers (l : G) := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hu3 l).1 (Subgroup.mem_zpowers l)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have huzN : (u : G) ∈ Subgroup.normalizer ((Subgroup.zpowers (l : G) : Subgroup G) : Set G) :=
    normalizer_zpowers_of_conj_mem hulz
  have huc : ∀ k : ℤ, (u : G) * c ^ k * (u : G)⁻¹ = c ^ k := by
    intro k
    have hc : (u : G) * c ^ k = c ^ k * (u : G) :=
      ((show Commute c (u : G) from h.c_comm _ u.2).zpow_left k).eq.symm
    rw [hc]; group
  have huA : ∀ x ∈ A, (u : G) * x * (u : G)⁻¹ ∈ A := by
    intro x hx
    obtain ⟨f, hf, k, rfl⟩ := h.decomp_A h45 x hx
    have hfF : (⟨f, hf.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.2 hf
    have h1 := (Subgroup.mem_normalizer_iff.1 hu1 ⟨f, hf.2⟩).1 hfF
    have h2 : (u : G) * f * (u : G)⁻¹ ∈ A := (Subgroup.mem_subgroupOf.1 h1).1
    have : (u : G) * (f * c ^ k) * (u : G)⁻¹ = ((u : G) * f * (u : G)⁻¹) * c ^ k := by
      calc (u : G) * (f * c ^ k) * (u : G)⁻¹
          = ((u : G) * f * (u : G)⁻¹) * ((u : G) * c ^ k * (u : G)⁻¹) := by group
        _ = ((u : G) * f * (u : G)⁻¹) * c ^ k := by rw [huc k]
    rw [this]
    exact A.mul_mem h2 (Subgroup.zpow_mem _ h.c_mem_A k)
  have huN : (u : G) ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_of_conj_mem_out huA
  have hcomm' : ∀ x ∈ Subgroup.zpowers (l : G), ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute (l : G) c from hab.1 _ hlA c h.c_mem_A).zpow_zpow j k).eq
  have huD : (u : G) ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem_out
    intro x hx
    rw [hDeq] at hx ⊢
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hcomm').1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have : (u : G) * (p * c ^ k) * (u : G)⁻¹ = ((u : G) * p * (u : G)⁻¹) * c ^ k := by
      calc (u : G) * (p * c ^ k) * (u : G)⁻¹
          = ((u : G) * p * (u : G)⁻¹) * ((u : G) * c ^ k * (u : G)⁻¹) := by group
        _ = ((u : G) * p * (u : G)⁻¹) * c ^ k := by rw [huc k]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 huzN p).1 hp))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k))
  have hlD : (l : G) ∈ dGroup a c := by
    rw [hDeq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have huC : (u : G) ∉ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) := by
    intro hc
    apply hu4
    have := Subgroup.mem_centralizer_iff.1 hc (l : G) hlD
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext this.symm)
  have huI' : u ∈ normalizer (I' : Set ↥L) := by
    have hl' : u⁻¹ * l * u ∈ Subgroup.zpowers l := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hu3) l).1 (Subgroup.mem_zpowers l)
      simpa using this
    have hPC : I'.map (MulAut.conj u).toMonoidHom ≤ centralizer ({l} : Set ↥L) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxl := Subgroup.mem_centralizer_singleton_iff.1 (hI'C hx)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hl'
      have hxl' : x * (u⁻¹ * l * u) = (u⁻¹ * l * u) * x := by
        rw [← hj]
        exact ((show Commute x l from hxl).zpow_right j).eq
      show u * x * u⁻¹ * l = l * (u * x * u⁻¹)
      calc u * x * u⁻¹ * l = u * (x * (u⁻¹ * l * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * l * u) * x) * u⁻¹ := by rw [hxl']
        _ = l * (u * x * u⁻¹) := by group
    have hPperf : ⁅I'.map (MulAut.conj u).toMonoidHom, I'.map (MulAut.conj u).toMonoidHom⁆ =
        I'.map (MulAut.conj u).toMonoidHom := by
      rw [← Subgroup.map_commutator, hI'perf]
    have hle := hI'max _ hPC hPperf
    apply mem_normalizer_of_conj_mem_out
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  have huIc : (u : G) ∈ Subgroup.normalizer ((iCore L a : Subgroup G) : Set G) := by
    rw [hI]
    exact Subgroup.le_normalizer_map L.subtype ⟨u, huI', rfl⟩
  have huAI : (u : G) ∈ Subgroup.normalizer ((A ⊓ iCore L a : Subgroup G) : Set G) :=
    mem_normalizer_inf_out huN huIc
  have hu4' : (u : G) ^ 4 ∉ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
    intro hc
    have hy2 : orderOf (u ^ 4) = 2 := by
      have := orderOf_pow_of_dvd (x := u) (n := 4) (by norm_num) (by rw [hu2]; norm_num)
      rw [this, hu2]
    have hlDL : (l : G) ∈ dGroup a c ⊓ L := by rw [hDL]; exact Subgroup.mem_zpowers _
    have hyl := h.centralizes_l h45 hfr (Subgroup.le_normalizer (u ^ 4 : ↥L).2) hc (l : G) hlDL
    have hyC : (u ^ 4 : ↥L) ∈ centralizer ({l} : Set ↥L) := by
      refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
      have hyl' : ((u : G) ^ 4) * (l : G) * ((u : G) ^ 4)⁻¹ = l := hyl
      calc ((u : G) ^ 4) * (l : G) = (((u : G) ^ 4) * (l : G) * ((u : G) ^ 4)⁻¹) * (u : G) ^ 4 := by
            group
        _ = (l : G) * ((u : G) ^ 4) := by rw [hyl']
    have hy' : (u ^ 4 : ↥L) ∈ Subgroup.zpowers l ⊔ I' := by rw [hCeq]; exact hyC
    obtain ⟨d, hd, i₁, hi₁, hdi⟩ :=
      (mem_sup_of_commute (fun x hx z hz => hDcomm x hx z (hI'C hz))).1 hy'
    have hi₁cen : (⟨i₁, hi₁⟩ : ↥I') ∈ Subgroup.center ↥I' := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hwI : ((w : ↥L) : G) ∈ iCore L a := by rw [hI]; exact ⟨w, w.2, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hc _ hwI
      have h1' : (w : ↥L) * u ^ 4 = u ^ 4 * (w : ↥L) := Subtype.ext (by simpa using h1)
      have h2 : d * (w : ↥L) = (w : ↥L) * d := hDcomm d hd w (hI'C w.2)
      have h3 : i₁ = d⁻¹ * u ^ 4 := by rw [← hdi]; group
      have hdw : d⁻¹ * (w : ↥L) = (w : ↥L) * d⁻¹ :=
        (Commute.inv_left (show Commute d (w : ↥L) from h2)).eq
      have key : (w : ↥L) * i₁ = i₁ * (w : ↥L) := by
        rw [h3]
        calc (w : ↥L) * (d⁻¹ * u ^ 4) = ((w : ↥L) * d⁻¹) * u ^ 4 := by group
          _ = (d⁻¹ * (w : ↥L)) * u ^ 4 := by rw [hdw]
          _ = d⁻¹ * ((w : ↥L) * u ^ 4) := by group
          _ = d⁻¹ * (u ^ 4 * (w : ↥L)) := by rw [h1']
          _ = (d⁻¹ * u ^ 4) * (w : ↥L) := by group
      exact key
    have hi₁1 : i₁ = 1 := by
      rw [center_eq_bot_of_equiv_alt6 I' φ, Subgroup.mem_bot] at hi₁cen
      simpa using congrArg Subtype.val hi₁cen
    rw [hi₁1, mul_one] at hdi
    have hd3 : d ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (⟨d, hd⟩ : ↥(Subgroup.zpowers l)))
      rw [hD3] at this
      simpa using congrArg Subtype.val this
    have hy3 : (u ^ 4 : ↥L) ^ 3 = 1 := by rw [← hdi]; exact hd3
    have := orderOf_dvd_of_pow_eq_one hy3
    rw [hy2] at this
    omega
  exact ⟨(u : G), u.2, huN, huD, huC, (Subgroup.orderOf_coe u).trans hu2, h.c_comm _ u.2, huIc,
    huAI, hu4'⟩

end ElemL

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
