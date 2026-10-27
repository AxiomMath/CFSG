module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutSecond
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutDTrans

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Trans

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.normalizes_L (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {g : G}
    (hgI : g ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G))
    (hgc : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨⟨eI⟩, -⟩ := h.iCore_structure h45 hfr
  have hLc := h.mem_thetaComponentsAt
  have hperf : ⁅iCore L a, iCore L a⁆ = iCore L a := perfect_of_equiv_alt6 _ eI
  have hns : ¬ Group.IsSolvable ↥(iCore L a) := not_isSolvable_of_equiv_alt6 eI
  have hL' := CFSG.RankThree.PartOne.Sec12TwoAssembly.conj_mem_thetaComponentsAt Nat.prime_three
    hgc hLc
  have hgfix : ∀ i ∈ iCore L a, g * i * g⁻¹ = i := by
    intro i hi
    have := Subgroup.mem_centralizer_iff.1 hgI i hi
    calc g * i * g⁻¹ = (i * g) * g⁻¹ := by rw [← this]
      _ = i := by group
  have hIle : iCore L a ≤ L ⊓ L.map (MulAut.conj g).toMonoidHom := by
    intro i hi
    exact ⟨(iCore_le L a hi).2, ⟨i, (iCore_le L a hi).2, by simpa using hgfix i hi⟩⟩
  have heq := eq_of_perfect_le_inf_thetaComponentsAt hLc hL' hIle hperf hns
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq.symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.centralizes_l (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgI : g ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G)) :
    ∀ z ∈ dGroup a c ⊓ L, g * z * g⁻¹ = z := by
  obtain ⟨l, I', hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hI'C, hI'perf, ⟨φ⟩, hI, hI'max, hD3, hDI,
    hDcomm, hCeq, hDeq, hDL⟩ := h.local_frame h45 hfr
  have hZ := h.center_eq_bot h45
  have hl3L : l ^ 3 = 1 := hl3
  have hlq3 : (l : ↥L ⧸ center ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hl3L]; rfl
  have hlq1 : (l : ↥L ⧸ center ↥L) ≠ 1 := fun h1 => by
    have := (QuotientGroup.eq_one_iff l).1 h1
    rw [hZ, Subgroup.mem_bot] at this
    exact hl1 this
  have h5q := five_dvd_centralizer_of_nonCentral h.quot.some hlq3 hlq1 hlnc
  have h5 : 5 ∣ Nat.card (centralizer ({h.equivJ3 hZ l} : Set NativeSporadic.J3)) := by
    rw [h.equivJ3_apply hZ]; exact h5q
  have hC1080 : Nat.card (centralizer ({l} : Set ↥L)) = 1080 :=
    card_centralizer_of_equiv_J3 (h.equivJ3 hZ) hl3L hl1 h5
  have hI360 : Nat.card I' = 360 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hgL⟩ with hσ
  have hσapp : ∀ x : ↥L, ((σ x : ↥L) : G) = g * x * g⁻¹ := fun x => rfl
  have hσI : ∀ i ∈ I', σ i = i := by
    intro i hi
    apply Subtype.ext
    rw [hσapp]
    have hiG : (i : G) ∈ iCore L a := by rw [hI]; exact ⟨i, hi, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hgI (i : G) hiG
    calc g * (i : G) * g⁻¹ = ((i : G) * g) * g⁻¹ := by rw [← this]
      _ = i := by group
  obtain ⟨n, hn⟩ := aut_eq_conj_of_trivial_on_perfect (h.equivJ3 hZ) hl3L hl1 hC1080 hI'C hI'perf
    hI360 ⟨φ⟩ σ hσI
  intro z hz
  rw [hDL] at hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have h1 : (((l ^ k : ↥L)) : G) = (l : G) ^ k := by simp
  have h2 := hσapp (l ^ k)
  rw [hn, MulAut.conj_apply, h1] at h2
  have h3 : ((l ^ n * l ^ k * (l ^ n)⁻¹ : ↥L) : G) = (l : G) ^ k := by
    have : l ^ n * l ^ k * (l ^ n)⁻¹ = l ^ k := by
      rw [← zpow_neg, ← zpow_add, ← zpow_add]; simp [add_comm, add_left_comm]
    rw [this, h1]
  rw [h3] at h2
  exact h2.symm

theorem mem_centralizer_dGroup {x a c : G} (hca : c * a = a * c)
    (hxa : x ∈ Subgroup.centralizer ({a} : Set G)) (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) :
    x ∈ Subgroup.centralizer ((dGroup a c : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  have hcomm : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers c, p * q = q * p := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact ((show Commute a c from hca.symm).zpow_zpow i j).eq
  intro y hy
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hcomm).1 hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
  have h1 : a ^ i * x = x * a ^ i :=
    ((show Commute a x from (Subgroup.mem_centralizer_singleton_iff.1 hxa).symm).zpow_left i).eq
  have h2 : c ^ j * x = x * c ^ j :=
    ((show Commute c x from (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm).zpow_left j).eq
  calc a ^ i * c ^ j * x = a ^ i * (c ^ j * x) := by group
    _ = a ^ i * (x * c ^ j) := by rw [h2]
    _ = (a ^ i * x) * c ^ j := by group
    _ = (x * a ^ i) * c ^ j := by rw [h1]
    _ = x * (a ^ i * c ^ j) := by group

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.reflections (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) {u v : G}
    (huv : UV217Out A c L K a u v) :
    ∃ d : G, d ∈ dGroup a c ⊓ L ∧ d ≠ 1 ∧ u * d * u⁻¹ = d⁻¹ ∧ v * d * v⁻¹ = d⁻¹ ∧
      (u * v⁻¹) * d * (u * v⁻¹)⁻¹ = d ∧
      (∃ δ ∈ dGroup a c, (u * v⁻¹) * δ * (u * v⁻¹)⁻¹ = δ * d) ∧
      ∀ δ ∈ dGroup a c, ∃ n : ℕ, (u * v⁻¹) * δ * (u * v⁻¹)⁻¹ = δ * d ^ n := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hEA : E ≤ A := h.pair.mem_E.2
  have haA : a ∈ A := hEA hfr.mem
  have hcA : c ∈ A := h.c_mem_A
  have hca : c * a = a * c := hab.1 c hcA a haA
  have ha3 : a ^ 3 = 1 := hab.2 a haA
  have hc3 : c ^ 3 = 1 := hab.2 c hcA
  have ha1 : a ≠ 1 := fun h1 => hfr.not_mem (h1 ▸ Subgroup.one_mem _)
  have hc1 : c ≠ 1 := h.c_ne_one
  have hnot : c ∉ Subgroup.zpowers a := fun hca' => hfr.not_mem
    (mem_zpowers_of_mem_zpowers ha3 hc1 hca')
  have huL : u ∈ L := huv.mem_u.1
  have hu : c * u = u * c := h.c_comm u huL
  have hvC : v ∈ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK huv.mem_v.1
  have hv : a * v = v * a := (Subgroup.mem_centralizer_singleton_iff.1 hvC).symm
  have huC : u ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hu.symm
  have hua : u ∉ Subgroup.centralizer ({a} : Set G) := fun hmem =>
    huv.nontriv_u (mem_centralizer_dGroup hca hmem huC)
  have hvc : v ∉ Subgroup.centralizer ({c} : Set G) := fun hmem =>
    huv.nontriv_v (mem_centralizer_dGroup hca hvC hmem)
  have hu8 := huv.pow_u
  have hv8 := huv.pow_v
  have hinv : ∀ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 3) →
      ¬ ∀ δ ∈ zpowers a ⊔ zpowers c, (u * v⁻¹) ^ n * δ * ((u * v⁻¹) ^ n)⁻¹ = δ⁻¹ := by
    intro n hn hall
    have hgI : (u * v⁻¹) ^ n ∈ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) :=
      Subgroup.pow_mem _ huv.t_cent n
    have hcD : c ∈ zpowers a ⊔ zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have hgc : (u * v⁻¹) ^ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      normalizer_zpowers_of_conj_mem (by
        rw [hall c hcD]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    have hgL := h.normalizes_L h45 hfr hgI hgc
    have hlD : (l : G) ∈ dGroup a c ⊓ L := by rw [hDL]; exact Subgroup.mem_zpowers _
    have h1 := h.centralizes_l h45 hfr hgL hgI (l : G) hlD
    have h2 := hall (l : G) hlD.1
    rw [h1] at h2
    apply hl1
    apply Subtype.ext
    have h3 : (l : G) * (l : G) = 1 := by
      calc (l : G) * (l : G) = (l : G)⁻¹⁻¹ * (l : G) := by rw [inv_inv]
        _ = 1 := by rw [← h2]; group
    have h4 : (l : G) = 1 := by
      calc (l : G) = (l : G) ^ 3 * ((l : G) * (l : G))⁻¹ := by group
        _ = 1 := by rw [hl3, h3]; group
    simpa using h4
  obtain ⟨d, hdD, hd1, hud, hvd, htd, hD1, hD⟩ := transvection_on_D_out hca ha3 hc3 ha1 hc1 hnot
    (u := u) (v := v) (t := u * v⁻¹) huv.norm_u hu hua hu8 huv.norm_v hv hvc hv8 rfl hinv
  refine ⟨d, ?_, hd1, hud, hvd, htd, hD1, hD⟩
  have hdA : d ∈ A := hDA hdD
  have hd3 : d ^ 3 = 1 := hab.2 d hdA
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := h.A_le_normalizer h45 hdA
  have hdL : d ∈ L := by
    have hdd : d⁻¹ * d⁻¹ = d := by
      have h3 : d * d * d = 1 := by simpa [pow_succ] using hd3
      calc d⁻¹ * d⁻¹ = d⁻¹ * d⁻¹ * (d * d * d) := by rw [h3, mul_one]
        _ = d := by group
    have e1 : d = u * (d * u⁻¹ * d⁻¹) := by
      calc d = d⁻¹ * d⁻¹ := hdd.symm
        _ = (u * d * u⁻¹) * d⁻¹ := by rw [hud]
        _ = u * (d * u⁻¹ * d⁻¹) := by group
    rw [e1]
    have : d * u⁻¹ * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hdN u⁻¹).1 (L.inv_mem huL)
    exact L.mul_mem huL this
  exact ⟨hdD, hdL⟩

theorem CoverOut.zpowers_eq_inf (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} (hd : d ∈ dGroup a c ⊓ L) (hd1 : d ≠ 1) :
    Subgroup.zpowers d = dGroup a c ⊓ L := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hdl : d ∈ Subgroup.zpowers (l : G) := hDL ▸ hd
  rw [hDL]
  exact le_antisymm (Subgroup.zpowers_le.2 hdl)
    (Subgroup.zpowers_le.2 (mem_zpowers_of_mem_zpowers hl3 hd1 hdl))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.out_transvection (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) {u v : G}
    (huv : UV217Out A c L K a u v) :
    ∃ d : G, d ≠ 1 ∧ Subgroup.zpowers d = dGroup a c ⊓ L ∧ u * d * u⁻¹ = d⁻¹ ∧
      v * d * v⁻¹ = d⁻¹ ∧
      IsTransvectionOn (A.normalizerMonoidHom
        ⟨u * v⁻¹, mul_mem huv.mem_u.2 (inv_mem huv.mem_v.2)⟩) ∧
      (commOf (A.normalizerMonoidHom
        ⟨u * v⁻¹, mul_mem huv.mem_u.2 (inv_mem huv.mem_v.2)⟩)).map A.subtype =
          Subgroup.zpowers d ∧
      (fixedSubgroupOf (A.normalizerMonoidHom
        ⟨u * v⁻¹, mul_mem huv.mem_u.2 (inv_mem huv.mem_v.2)⟩)).map A.subtype = A ⊓ L := by
  obtain ⟨d, hdDL, hd1, hud, hvd, htd, hD1, hD⟩ := h.reflections h45 hfr hK huv
  have hzd := h.zpowers_eq_inf h45 hfr hdDL hd1
  obtain ⟨⟨eI⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hab.1 x hx y hy
  have hD9 := h.card_dGroup h45 hfr
  have hdA : d ∈ A := hDA hdDL.1
  have hd3 : d ^ 3 = 1 := hab.2 d hdA
  have hcA : c ∈ A := h.c_mem_A
  have hc3 : c ^ 3 = 1 := hab.2 c hcA
  have htA : u * v⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem huv.mem_u.2 (inv_mem huv.mem_v.2)
  set t : G := u * v⁻¹ with ht
  have htI : ∀ x ∈ iCore L a, t * x * t⁻¹ = x := by
    intro x hx
    have := Subgroup.mem_centralizer_iff.1 huv.t_cent x hx
    calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [← this]
      _ = x := by group
  have hDI : dGroup a c ≤ Subgroup.centralizer ((iCore L a : Subgroup G) : Set G) := by
    rw [← hAC]; exact inf_le_right
  have hdisj : Disjoint (dGroup a c) (A ⊓ iCore L a) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxI
    exact hIcen x hxI.2 (fun z hz => (Subgroup.mem_centralizer_iff.1 (hDI hxD) z hz).symm)
  have hN : A ⊓ iCore L a ≤ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((dGroup a c : Subgroup G) : Set G))
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcommA x (hDA hx) y hy.1
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj
  have hAcard : Nat.card A ≤ Nat.card ↥(dGroup a c ⊔ (A ⊓ iCore L a)) := by
    rw [hcard, hD9, hcardAI, h.card]; norm_num
  have hE : ∀ ε ∈ A ⊓ iCore L a, t * ε * t⁻¹ = ε := fun ε hε => htI ε hε.2
  have hTr := isTransvectionOn_of_action hDA inf_le_left hAcard hcommA htA hdDL.1 hd3 hd1 htd hD
    hD1 hE
  have hcD : c ∈ dGroup a c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hdl' : Subgroup.zpowers d = Subgroup.zpowers (l : G) := hzd.trans hDL
  have hDeq' : dGroup a c = Subgroup.zpowers d ⊔ Subgroup.zpowers c := by rw [hDeq, hdl']
  obtain ⟨m, hm⟩ := hD c hcD
  have hcd : c * d = d * c := hcommA c hcA d hdA
  have htdz : ∀ j : ℤ, t * d ^ j * t⁻¹ = d ^ j := by
    intro j
    rw [← conj_zpow, htd]
  have hmne : ¬ 3 ∣ (m : ℤ) := by
    intro hm3
    obtain ⟨δ, hδ, hδt⟩ := hD1
    rw [hDeq'] at hδ
    have hcomm' : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
      intro x hx y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute d c from hcd.symm).zpow_zpow j k).eq
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_commute hcomm').1 hδ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have htcm : t * c * t⁻¹ = c := by
      rw [hm]
      obtain ⟨q, hq⟩ := hm3
      have : d ^ m = 1 := by
        have h' : d ^ (m : ℤ) = 1 := by
          rw [hq, zpow_mul]
          have h3z : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
          rw [h3z, one_zpow]
        exact_mod_cast h'
      rw [this, mul_one]
    have htck : t * c ^ k * t⁻¹ = c ^ k := by rw [← conj_zpow, htcm]
    apply hd1
    have h1 : t * (d ^ j * c ^ k) * t⁻¹ = d ^ j * c ^ k * d := hδt
    have h2 : t * (d ^ j * c ^ k) * t⁻¹ = d ^ j * c ^ k := by
      calc t * (d ^ j * c ^ k) * t⁻¹ = (t * d ^ j * t⁻¹) * (t * c ^ k * t⁻¹) := by group
        _ = d ^ j * c ^ k := by rw [htdz, htck]
    rw [h2] at h1
    have : d ^ j * c ^ k * d = d ^ j * c ^ k * 1 := by rw [← h1, mul_one]
    exact mul_left_cancel this
  have hcm : Commute c (d ^ m) := (show Commute c d from hcd).pow_right m
  have htck : ∀ k : ℤ, t * c ^ k * t⁻¹ = c ^ k * d ^ ((m : ℤ) * k) := by
    intro k
    rw [← conj_zpow, hm, hcm.mul_zpow, ← zpow_natCast d m, ← zpow_mul]
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hfF : ∀ f ∈ A ⊓ L, t * f * t⁻¹ = f := by
    intro f hf
    obtain ⟨d₀, hd₀, y₀, hy₀, rfl⟩ := h.decomp_F h45 hfr f hf
    rw [← hzd] at hd₀
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd₀
    calc t * (d ^ j * y₀) * t⁻¹ = (t * d ^ j * t⁻¹) * (t * y₀ * t⁻¹) := by group
      _ = d ^ j * y₀ := by rw [htdz, htI y₀ hy₀]
  have hfixiff : ∀ y ∈ A, (t * y * t⁻¹ = y ↔ y ∈ A ⊓ L) := by
    intro y hy
    refine ⟨fun hty => ?_, fun hyF => hfF y hyF⟩
    obtain ⟨f, hf, k, hyk⟩ := h.decomp_A h45 y hy
    have h1 : t * c ^ k * t⁻¹ = c ^ k := by
      have h0 : t * (f * c ^ k) * t⁻¹ = f * c ^ k := by rw [← hyk]; exact hty
      calc t * c ^ k * t⁻¹ = (t * f * t⁻¹)⁻¹ * (t * (f * c ^ k) * t⁻¹) := by group
        _ = f⁻¹ * (f * c ^ k) := by rw [hfF f hf, h0]
        _ = c ^ k := by group
    rw [htck k] at h1
    have h2 : d ^ ((m : ℤ) * k) = 1 := mul_left_cancel (h1.trans (mul_one _).symm)
    have h3 : (3 : ℤ) ∣ (m : ℤ) * k := three_dvd_of_zpow_eq_one hd3 hd1 h2
    have h4 : (3 : ℤ) ∣ k := (Int.prime_three.dvd_or_dvd h3).resolve_left hmne
    obtain ⟨q, rfl⟩ := h4
    have hck : c ^ (3 * q) = 1 := by
      rw [zpow_mul]
      have h3z : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
      rw [h3z, one_zpow]
    rw [hyk, hck, mul_one]
    exact hf
  set φ := A.normalizerMonoidHom ⟨t, htA⟩ with hφ
  have hφapp : ∀ y : A, ((φ y : A) : G) = t * y * t⁻¹ := fun y => rfl
  have hcomm_mem : ∀ y : A, (y : G)⁻¹ * ((φ y : A) : G) ∈ Subgroup.zpowers d := by
    intro y
    rw [hφapp]
    obtain ⟨f, hf, k, hyk⟩ := h.decomp_A h45 y y.2
    rw [hyk]
    have : (f * c ^ k)⁻¹ * (t * (f * c ^ k) * t⁻¹) = d ^ ((m : ℤ) * k) := by
      calc (f * c ^ k)⁻¹ * (t * (f * c ^ k) * t⁻¹)
          = (f * c ^ k)⁻¹ * ((t * f * t⁻¹) * (t * c ^ k * t⁻¹)) := by group
        _ = (f * c ^ k)⁻¹ * (f * (c ^ k * d ^ ((m : ℤ) * k))) := by rw [hfF f hf, htck k]
        _ = d ^ ((m : ℤ) * k) := by group
    rw [this]
    exact Subgroup.zpow_mem_zpowers d _
  have hcommOf : (commOf φ).map A.subtype = Subgroup.zpowers d := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hle : commOf φ ≤ (Subgroup.zpowers d).comap A.subtype := by
        rw [commOf, Subgroup.closure_le]
        rintro _ ⟨y, rfl⟩
        exact hcomm_mem y
      exact hle hx
    · rw [Subgroup.zpowers_le]
      have hmm : ((m : ℤ) * m) % 3 = 1 := by
        have : (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2 := by omega
        rcases this with h' | h' <;> simp [Int.mul_emod, h']
      have hdm : d ^ ((m : ℤ) * m) = d := by
        have := zpow_mod_orderOf d ((m : ℤ) * m)
        rw [hdo] at this
        have h3 : ((m : ℤ) * m) % ((3 : ℕ) : ℤ) = 1 := by exact_mod_cast hmm
        rw [h3, zpow_one] at this
        exact this.symm
      refine ⟨(⟨c ^ (m : ℤ), A.zpow_mem hcA _⟩ : A)⁻¹ * φ ⟨c ^ (m : ℤ), A.zpow_mem hcA _⟩,
        mem_commOf φ _, ?_⟩
      show ((⟨c ^ (m : ℤ), A.zpow_mem hcA _⟩ : A) : G)⁻¹ *
        ((φ ⟨c ^ (m : ℤ), A.zpow_mem hcA _⟩ : A) : G) = d
      rw [hφapp]
      show (c ^ (m : ℤ))⁻¹ * (t * c ^ (m : ℤ) * t⁻¹) = d
      rw [htck (m : ℤ)]
      calc (c ^ (m : ℤ))⁻¹ * (c ^ (m : ℤ) * d ^ ((m : ℤ) * m)) = d ^ ((m : ℤ) * m) := by group
        _ = d := hdm
  have hfixed : (fixedSubgroupOf φ).map A.subtype = A ⊓ L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : φ x = x := hx
      have : t * (x : G) * t⁻¹ = x := by
        have := congrArg Subtype.val hx'
        rwa [hφapp] at this
      exact (hfixiff x x.2).1 this
    · intro hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      show φ ⟨y, hy.1⟩ = ⟨y, hy.1⟩
      exact Subtype.ext (by rw [hφapp]; exact hfF y hy)
  exact ⟨d, hd1, hzd, hud, hvd, hTr, hcommOf, hfixed⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217OutTransvection_of (h45 : Sec4.Item4_5) : Sec217OutTransvection := by
  intro G _ _ A E U c L a U₀ K hOS u v huv
  have h : CoverOut A E U c L := hOS.base
  have hfr := hOS.frame
  have hK : K ∈ thetaComponentsAt 3 a := hOS.mem_K.2
  obtain ⟨d, hd1, hzd, hud, hvd, hTr, hcom, hfix⟩ := h.out_transvection h45 hfr hK huv
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hdDL : d ∈ dGroup a c ⊓ L := hzd ▸ Subgroup.mem_zpowers d
  have hdA : d ∈ A := hDA hdDL.1
  have hd3 : d ^ 3 = 1 := hab.2 d hdA
  have huL : u ∈ L := huv.mem_u.1
  have huN := huv.norm_u
  have hcommle : ⁅Subgroup.zpowers u, dGroup a c⁆ ≤ dGroup a c ⊓ L := by
    rw [Subgroup.commutator_le]
    intro g hg y hy
    have hgN : g ∈ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact Subgroup.zpow_mem _ huN k
    have hgL : g ∈ L := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact L.zpow_mem huL k
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := h.A_le_normalizer h45 (hDA hy)
    refine ⟨?_, ?_⟩
    · have : g * y * g⁻¹ ∈ dGroup a c := (Subgroup.mem_normalizer_iff.1 hgN y).1 hy
      rw [commutatorElement_def]
      exact (dGroup a c).mul_mem this ((dGroup a c).inv_mem hy)
    · rw [commutatorElement_def]
      have h1 : y * g⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hyN g⁻¹).1 (L.inv_mem hgL)
      have e : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
      rw [e]
      exact L.mul_mem hgL h1
  have hdd : d⁻¹ * d⁻¹ = d := by
    have h3 : d * d * d = 1 := by simpa [pow_succ] using hd3
    calc d⁻¹ * d⁻¹ = d⁻¹ * d⁻¹ * (d * d * d) := by rw [h3, mul_one]
      _ = d := by group
  have hcomm_eq : ⁅Subgroup.zpowers u, dGroup a c⁆ = Subgroup.zpowers d := by
    apply le_antisymm
    · rw [hzd]; exact hcommle
    · rw [Subgroup.zpowers_le]
      have hud' : ⁅u, d⁆ = d := by rw [commutatorElement_def, hud]; exact hdd
      rw [← hud']
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hdDL.1
  refine ⟨d, hd1, hzd, hcomm_eq, ?_, hud, hvd, hTr, hcom, hfix⟩
  intro hca
  rw [hcomm_eq] at hca
  have hvC : v ∈ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK huv.mem_v.1
  have hv : a * v = v * a := (Subgroup.mem_centralizer_singleton_iff.1 hvC).symm
  have haA : a ∈ A := h.pair.mem_E.2 hfr.mem
  have ha3 : a ^ 3 = 1 := hab.2 a haA
  have ha1 : a ≠ 1 := fun h1 => hfr.not_mem (h1 ▸ Subgroup.one_mem _)
  have had : a ∈ Subgroup.zpowers d := hca ▸ Subgroup.mem_zpowers a
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 had
  have h1 : v * a * v⁻¹ = a⁻¹ := by
    rw [← hk, ← conj_zpow, hvd, inv_zpow]
  have h2 : v * a * v⁻¹ = a := by
    rw [← hv]; group
  have h3 : a⁻¹ = a := h1.symm.trans h2
  have h4 : a * a = 1 := mul_eq_one_iff_eq_inv.2 h3.symm
  have h5 : a * a * a = 1 := by simpa [pow_succ] using ha3
  rw [h4, one_mul] at h5
  exact ha1 h5

end Trans

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
