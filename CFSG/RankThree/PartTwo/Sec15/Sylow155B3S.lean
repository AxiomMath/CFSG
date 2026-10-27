module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155B3
import CFSG.RankThree.PartTwo.Sec15.Sylow155KA6P
import CFSG.RankThree.PartTwo.Sec15.Sylow155Gen

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

namespace Sylow155B3

open Sylow155R

theorem pow_three_eq_one_of_psl29 {Q : Type} [Group Q] (hZ : Nat.card (Subgroup.center Q) = 3)
    (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) {q r : Q} {x g : P10}
    (hq : ((ψ6 (QuotientGroup.mk q) : ↥A6Models.psl29) : P10) = x)
    (hr : ((ψ6 (QuotientGroup.mk r) : ↥A6Models.psl29) : P10) = g) (hx3 : x ^ 3 = 1)
    (hgx : g * x * g⁻¹ = x⁻¹) : q ^ 3 = 1 := by
  have hcen : ∀ y : Q, ((ψ6 (QuotientGroup.mk y) : ↥A6Models.psl29) : P10) = 1 →
      y ∈ Subgroup.center Q := by
    intro y hy
    have h1 : ψ6 (QuotientGroup.mk y) = 1 := Subtype.ext hy
    rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  refine Sylow155B3Q.pow_three_eq_one_of_conj_inv hZ (g := r) (hcen _ ?_) (hcen _ ?_)
  · rw [QuotientGroup.mk_pow, map_pow, SubgroupClass.coe_pow, hq, hx3]
  · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, hq, hr, hgx, inv_mul_cancel]

section Generic

variable {G : Type} [Group G] [Finite G] {W K : Subgroup G} [(K.subgroupOf W).Normal]
  (ψ6 : (↥W ⧸ K.subgroupOf W) ⧸ Subgroup.center (↥W ⧸ K.subgroupOf W) ≃* ↥A6Models.psl29)

theorem rho6_mem_psl29_of_pow_three (g : ↥(nWK W K)) (hg : (g : G) ^ 3 = 1) :
    rho6 ψ6 g ∈ A6Models.psl29 := by
  have h3 : rho6 ψ6 g ^ 3 = 1 := by
    rw [← map_pow, show g ^ 3 = 1 from Subtype.ext (by simpa using hg), map_one]
  by_cases h1 : rho6 ψ6 g = 1
  · rw [h1]
    exact one_mem _
  · exact (mem_psl29_of_prime_pow Nat.prime_three (by norm_num) (rho6_mem_autA6 ψ6 g) h3 h1).1

theorem rho6_conj_mem {H : Subgroup G} {g : ↥(nWK W K)}
    (hg : (g : G) ∈ Subgroup.normalizer (H : Set G)) {y : P10}
    (hy : y ∈ (H.subgroupOf (nWK W K)).map (rho6 ψ6)) :
    rho6 ψ6 g * y * (rho6 ψ6 g)⁻¹ ∈ (H.subgroupOf (nWK W K)).map (rho6 ψ6) := by
  obtain ⟨u, hu, rfl⟩ := hy
  refine ⟨g * u * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hg u).mp (Subgroup.mem_subgroupOf.mp hu)

theorem not_dvd_card_map_rho6 {H : Subgroup G} (hH : H ≤ nWK W K) (hH3 : ¬ 3 ∣ Nat.card H) :
    ¬ 3 ∣ Nat.card ↥((H.subgroupOf (nWK W K)).map (rho6 ψ6)) :=
  fun h3 => hH3 ((h3.trans (Subgroup.card_map_dvd _ _)).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv).dvd)

theorem exists_rho6_eq_of_pow_three (hWK : W ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3) {x : P10}
    (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) :
    ∃ (w : G) (hw : w ∈ W), rho6 ψ6 ⟨w, mem_nWK hWK hw⟩ = x ∧ w ^ 3 ∈ K := by
  obtain ⟨w, hw, hρw⟩ := exists_rho6_eq ψ6 hWK hx
  obtain ⟨g, hg, hgx⟩ := Sylow155KA6P.exists_conj_inv hx hx3
  obtain ⟨v, hv, hρv⟩ := exists_rho6_eq ψ6 hWK hg
  refine ⟨w, hw, hρw, ?_⟩
  have h3 := pow_three_eq_one_of_psl29 hZ ψ6 (q := QuotientGroup.mk ⟨w, hw⟩)
    (r := QuotientGroup.mk ⟨v, hv⟩) ((rho6_mem ψ6 hWK w hw).symm.trans hρw)
    ((rho6_mem ψ6 hWK v hv).symm.trans hρv) hx3 hgx
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem exists_rho6_ne_one {A : Subgroup G} (hAF : A ∈ partTwoF G) (hAn : A ≤ nWK W K)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3)
    (hperf : commutator (↥W ⧸ K.subgroupOf W) = ⊤) :
    ∃ (a : G) (ha : a ∈ A), rho6 ψ6 ⟨a, hAn ha⟩ ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ (a : G) (ha : a ∈ A), rho6 ψ6 ⟨a, hAn ha⟩ = 1 := fun a ha =>
    Classical.byContradiction fun hne => hcon ⟨a, ha, hne⟩
  obtain ⟨x, hx, y, -, hx3, -, hxy⟩ := Push153B.A6.exists_noncomm_three
  have hx1 : x ≠ 1 := fun h1 => hxy (by rw [h1, one_mul, mul_one])
  obtain ⟨w, hw, hρw, hw3⟩ := exists_rho6_eq_of_pow_three ψ6 hWK hZ hx hx3
  have hfix : ∀ a ∈ A, a * w * a⁻¹ * w⁻¹ ∈ K := by
    intro a ha
    have hq : qAct W K ⟨a, hAn ha⟩ = 1 := (rho6_eq_one_iff ψ6 hperf _).mp (hcon' a ha)
    exact (qAct_mk_eq_iff hWK ⟨a, hAn ha⟩ hw).mp (by rw [hq, MulAut.one_apply])
  obtain ⟨a₀, ha₀, ha₀K⟩ := exists_mem_inf_of_fixed hAF (fun a ha => (hAn ha).1)
    (fun a ha => (hAn ha).2) hWK hK hw hfix hw3
  have h1 : rho6 ψ6 ⟨a₀, mem_nWK hWK ha₀.2⟩ = x := by
    rw [rho6_mem ψ6 hWK a₀ ha₀.2, mk_eq_mk_of_mul_inv_mem hWK ha₀.2 hw ha₀K,
      ← rho6_mem ψ6 hWK w hw]
    exact hρw
  exact hx1 (h1.symm.trans (hcon' a₀ ha₀.1))

theorem rho6_eq_one_of_fixes (hperf : commutator (↥W ⧸ K.subgroupOf W) = ⊤)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3)
    (hcard : Nat.card (↥W ⧸ K.subgroupOf W) = 1080) {c a₁ : ↥(nWK W K)}
    (hc : ∀ z ∈ Subgroup.center (↥W ⧸ K.subgroupOf W), qAct W K c z = z)
    (ha₁ : rho6 ψ6 a₁ ∈ A6Models.psl29) (ha₁3 : rho6 ψ6 a₁ ^ 3 = 1) (ha₁1 : rho6 ψ6 a₁ ≠ 1)
    (hca : c * a₁ = a₁ * c) (hc3 : ¬ 3 ∣ orderOf c) : rho6 ψ6 c = 1 := by
  have hcomm : rho6 ψ6 c * rho6 ψ6 a₁ = rho6 ψ6 a₁ * rho6 ψ6 c := by
    rw [← map_mul, hca, map_mul]
  have hm := mem_m10_of_fixes_center hperf hZ hcard ψ6 hc (rho6_mem_autA6 ψ6 c)
    (rho6_spec ψ6 c) ha₁ ha₁3 ha₁1 hcomm
  exact Sylow155KA6P.eq_one_of_mem_m10_of_coprime ha₁ ha₁3 ha₁1 hm hcomm
    fun h3 => hc3 (h3.trans (orderOf_map_dvd _ _))

theorem rho6_mem_psl29_of_invariant (hperf : commutator (↥W ⧸ K.subgroupOf W) = ⊤)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3)
    (hcard : Nat.card (↥W ⧸ K.subgroupOf W) = 1080) {A V : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAn : A ≤ nWK W K) (hWK : W ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K)
    (hVn : V ≤ nWK W K) (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hV3 : ¬ 3 ∣ Nat.card V)
    {a₁ : G} (ha₁ : a₁ ∈ A) (ha₁1 : rho6 ψ6 ⟨a₁, hAn ha₁⟩ ≠ 1) {v : G} (hv : v ∈ V) :
    rho6 ψ6 ⟨v, hVn hv⟩ ∈ A6Models.psl29 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAF.1.2 a a.2)⟩
  have hVZ := le_fixZ hAF hAn hWK hK hZ hVn hAV hV3
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G,
      L = ((A6Models.psl29).comap (rho6 ψ6)).map (nWK W K).subtype := ⟨_, rfl⟩
  have hLmem : ∀ {g : G} (hg : g ∈ nWK W K), g ∈ L ↔ rho6 ψ6 ⟨g, hg⟩ ∈ A6Models.psl29 := by
    intro g hg
    rw [hL]
    constructor
    · rintro ⟨y, hy, hyg⟩
      have e : y = ⟨g, hg⟩ := Subtype.ext hyg
      rw [← e]
      exact hy
    · intro h1
      exact ⟨⟨g, hg⟩, h1, rfl⟩
  have hLn : L ≤ nWK W K := by
    rw [hL]
    exact Subgroup.map_subtype_le _
  have hconjL : ∀ g ∈ nWK W K, ∀ y ∈ L, g * y * g⁻¹ ∈ L := by
    intro g hg y hy
    have hyn := hLn hy
    have hgy : g * y * g⁻¹ ∈ nWK W K :=
      (nWK W K).mul_mem ((nWK W K).mul_mem hg hyn) ((nWK W K).inv_mem hg)
    refine (hLmem hgy).mpr ?_
    have e : (⟨g * y * g⁻¹, hgy⟩ : ↥(nWK W K)) = ⟨g, hg⟩ * ⟨y, hyn⟩ * (⟨g, hg⟩)⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
    exact psl29_normal _ (rho6_mem_autA6 ψ6 _) _ ((hLmem hyn).mp hy)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconjL a (hAn ha) y hy, fun hy => ?_⟩
    have h1 := hconjL a⁻¹ ((nWK W K).inv_mem (hAn ha)) _ hy
    have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
    rwa [e] at h1
  have hcop : ¬ 3 ∣ Nat.card ↥(V ⊓ L) := fun h3 =>
    hV3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hvn := hVn hv
  have hfix : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ L := by
    intro a ha
    have hmem : a * v * a⁻¹ * v⁻¹ ∈ nWK W K :=
      (nWK W K).mul_mem ((nWK W K).mul_mem ((nWK W K).mul_mem (hAn ha) hvn)
        ((nWK W K).inv_mem (hAn ha))) ((nWK W K).inv_mem hvn)
    refine (hLmem hmem).mpr ?_
    have e : (⟨a * v * a⁻¹ * v⁻¹, hmem⟩ : ↥(nWK W K)) =
        ⟨a, hAn ha⟩ * ⟨v, hvn⟩ * (⟨a, hAn ha⟩)⁻¹ * (⟨v, hvn⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact Sylow155KA6P.commutator_mem_psl29 (rho6_mem_autA6 ψ6 _) (rho6_mem_autA6 ψ6 _)
  obtain ⟨c, hcV, hcA, hcv⟩ := Sylow155G.exists_fixed_mul_inv_mem hA3 hAV hAL hcop hv hfix
  obtain ⟨hcn, hcZ⟩ := mem_fixZ_iff.mp (hVZ hcV)
  have ha₁n := hAn ha₁
  have hρa₁3 : rho6 ψ6 ⟨a₁, ha₁n⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨a₁, ha₁n⟩ : ↥(nWK W K)) ^ 3 = 1 from
      Subtype.ext (by simpa using hAF.1.2 a₁ ha₁), map_one]
  have hca : (⟨c, hcn⟩ : ↥(nWK W K)) * ⟨a₁, ha₁n⟩ = ⟨a₁, ha₁n⟩ * ⟨c, hcn⟩ := by
    refine Subtype.ext ?_
    change c * a₁ = a₁ * c
    have h1 := hcA a₁ ha₁
    calc c * a₁ = a₁ * c * a₁⁻¹ * a₁ := by rw [h1]
      _ = a₁ * c := by group
  have hc3 : ¬ 3 ∣ orderOf (⟨c, hcn⟩ : ↥(nWK W K)) := by
    rw [Subgroup.orderOf_mk]
    exact fun h3 => hV3 (h3.trans (Subgroup.orderOf_dvd_natCard V hcV))
  have hρc : rho6 ψ6 ⟨c, hcn⟩ = 1 :=
    rho6_eq_one_of_fixes ψ6 hperf hZ hcard hcZ
      (rho6_mem_psl29_of_pow_three ψ6 _ (hAF.1.2 a₁ ha₁)) hρa₁3 ha₁1 hca hc3
  have hcvn : c * v⁻¹ ∈ nWK W K := (nWK W K).mul_mem hcn ((nWK W K).inv_mem hvn)
  have hρcv := (hLmem hcvn).mp hcv
  have e : (⟨c * v⁻¹, hcvn⟩ : ↥(nWK W K)) = ⟨c, hcn⟩ * (⟨v, hvn⟩)⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_inv, hρc, one_mul] at hρcv
  have h2 := (A6Models.psl29).inv_mem hρcv
  rwa [inv_inv] at h2

theorem rho6_eq_one_of_not_mem_zpowers (hperf : commutator (↥W ⧸ K.subgroupOf W) = ⊤)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3)
    (hcard : Nat.card (↥W ⧸ K.subgroupOf W) = 1080) {A V : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAn : A ≤ nWK W K) (hWK : W ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K)
    (hVn : V ≤ nWK W K) (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hV3 : ¬ 3 ∣ Nat.card V)
    {a₁ b : G} (ha₁ : a₁ ∈ A) (ha₁1 : rho6 ψ6 ⟨a₁, hAn ha₁⟩ ≠ 1) (hb : b ∈ A)
    (hbA : rho6 ψ6 ⟨b, hAn hb⟩ ∉ Subgroup.zpowers (rho6 ψ6 ⟨a₁, hAn ha₁⟩)) {v : G}
    (hv : v ∈ V) : rho6 ψ6 ⟨v, hVn hv⟩ = 1 := by
  have hpow : ∀ {g : G} (hg : g ∈ A), rho6 ψ6 ⟨g, hAn hg⟩ ^ 3 = 1 := by
    intro g hg
    rw [← map_pow, show (⟨g, hAn hg⟩ : ↥(nWK W K)) ^ 3 = 1 from
      Subtype.ext (by simpa using hAF.1.2 g hg), map_one]
  have hab0 : a₁ * b = b * a₁ := by
    have h0 := hAF.1.1.is_comm.comm (⟨a₁, ha₁⟩ : ↥A) ⟨b, hb⟩
    exact congrArg Subtype.val h0
  have e : (⟨a₁, hAn ha₁⟩ : ↥(nWK W K)) * ⟨b, hAn hb⟩ = ⟨b, hAn hb⟩ * ⟨a₁, hAn ha₁⟩ :=
    Subtype.ext hab0
  have hab : rho6 ψ6 ⟨a₁, hAn ha₁⟩ * rho6 ψ6 ⟨b, hAn hb⟩ =
      rho6 ψ6 ⟨b, hAn hb⟩ * rho6 ψ6 ⟨a₁, hAn ha₁⟩ := by
    rw [← map_mul, ← map_mul, e]
  have hVbar : (V.subgroupOf (nWK W K)).map (rho6 ψ6) = ⊥ :=
    Sylow155KA6P.eq_bot_of_invariant_e9 (rho6_mem_psl29_of_pow_three ψ6 _ (hAF.1.2 a₁ ha₁))
      (hpow ha₁) ha₁1 (rho6_mem_psl29_of_pow_three ψ6 _ (hAF.1.2 b hb)) (hpow hb) hab hbA
      (by
        rintro _ ⟨⟨u, hun⟩, hu, rfl⟩
        exact rho6_mem_psl29_of_invariant ψ6 hperf hZ hcard hAF hAn hWK hK hVn hAV hV3 ha₁ ha₁1
          (Subgroup.mem_subgroupOf.mp hu))
      (not_dvd_card_map_rho6 ψ6 hVn hV3) (fun _ hy => rho6_conj_mem ψ6 (hAV ha₁) hy)
      (fun _ hy => rho6_conj_mem ψ6 (hAV hb) hy)
  have hmem : rho6 ψ6 ⟨v, hVn hv⟩ ∈ (V.subgroupOf (nWK W K)).map (rho6 ψ6) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  rw [hVbar, Subgroup.mem_bot] at hmem
  exact hmem

theorem exists_mem_normalizer_rho6_eq (hperf : commutator (↥W ⧸ K.subgroupOf W) = ⊤)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3) {A : Subgroup G}
    (hAF : A ∈ partTwoF G) (hAn : A ≤ nWK W K) (hWK : W ≤ Subgroup.normalizer (K : Set G))
    (hK : ¬ 3 ∣ Nat.card K) {x : P10}
    (hAx : ∀ (a : G) (ha : a ∈ A), rho6 ψ6 ⟨a, hAn ha⟩ ∈ Subgroup.zpowers x) {n : P10}
    (hn : n ∈ A6Models.psl29) (hnx : n * x = x * n) :
    ∃ (w : G) (hw : w ∈ W), w ∈ Subgroup.normalizer (A : Set G) ∧
      rho6 ψ6 ⟨w, mem_nWK hWK hw⟩ = n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAF.1.2 a a.2)⟩
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha => (hAn ha).1
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha => (hAn ha).2
  obtain ⟨z₀, hz₀, hz₀Z, hz₀1⟩ := exists_mem_inf_center hAF hAW hAK hWK hK hZ
  obtain ⟨j, hjW, hρj⟩ := exists_rho6_eq ψ6 hWK hn
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup G, J = W ⊓
      ((Subgroup.centralizer ({x} : Set P10)).comap (rho6 ψ6)).map (nWK W K).subtype :=
    ⟨_, rfl⟩
  have hJmem : ∀ {y : G} (hy : y ∈ W), rho6 ψ6 ⟨y, mem_nWK hWK hy⟩ * x =
      x * rho6 ψ6 ⟨y, mem_nWK hWK hy⟩ → y ∈ J := by
    intro y hy hρy
    rw [hJ]
    exact ⟨hy, ⟨y, mem_nWK hWK hy⟩, Subgroup.mem_centralizer_singleton_iff.mpr hρy, rfl⟩
  have hρK : ∀ (k : G) (hk : k ∈ W), k ∈ K → rho6 ψ6 ⟨k, mem_nWK hWK hk⟩ = 1 :=
    fun k hk hkK => rho6_eq_one_of_mem ψ6 hWK k hk hkK
  have hN : ¬ 3 ∣ Nat.card ↥(K ⊓ W) := fun h3 =>
    hK (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hNJ : K ⊓ W ≤ J := fun k hk => hJmem hk.2 (by rw [hρK k hk.2 hk.1, one_mul, mul_one])
  have hJW : J ≤ W := by
    rw [hJ]
    exact inf_le_left
  have hAN : A ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
    (le_inf hAK hAW).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hJN : J ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
    (hJW.trans (le_inf hWK Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hJA : ∀ j' ∈ J, ∀ a ∈ A, ∃ k ∈ K ⊓ W, ∃ a' ∈ A, j' * a * j'⁻¹ = k * a' := by
    intro j' hj' a ha
    have hj'W := hJW hj'
    have hj'n : j' ∈ nWK W K := mem_nWK hWK hj'W
    rw [hJ] at hj'
    obtain ⟨-, ⟨j'', hj''C, hj''⟩⟩ := hj'
    have hρj' : rho6 ψ6 ⟨j', hj'n⟩ * x = x * rho6 ψ6 ⟨j', hj'n⟩ := by
      have e : (⟨j', hj'n⟩ : ↥(nWK W K)) = j'' := Subtype.ext hj''.symm
      rw [e]
      exact Subgroup.mem_centralizer_singleton_iff.mp hj''C
    have hcomm : rho6 ψ6 ⟨j', hj'n⟩ * rho6 ψ6 ⟨a, hAn ha⟩ =
        rho6 ψ6 ⟨a, hAn ha⟩ * rho6 ψ6 ⟨j', hj'n⟩ := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hAx a ha)
      rw [← hi]
      exact (Commute.zpow_right (show Commute (rho6 ψ6 ⟨j', hj'n⟩) x from hρj') i).eq
    have haW : a * j'⁻¹ * a⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hAn ha).1 _).mp (W.inv_mem hj'W)
    have hxW : j' * a * j'⁻¹ * a⁻¹ ∈ W := by
      have e : j' * a * j'⁻¹ * a⁻¹ = j' * (a * j'⁻¹ * a⁻¹) := by group
      rw [e]
      exact W.mul_mem hj'W haW
    have hρx : rho6 ψ6 ⟨j' * a * j'⁻¹ * a⁻¹, mem_nWK hWK hxW⟩ = 1 := by
      have e : (⟨j' * a * j'⁻¹ * a⁻¹, mem_nWK hWK hxW⟩ : ↥(nWK W K)) =
          ⟨j', hj'n⟩ * ⟨a, hAn ha⟩ * (⟨j', hj'n⟩)⁻¹ * (⟨a, hAn ha⟩)⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_inv_cancel_right,
        mul_inv_cancel]
    obtain ⟨k, hk, m, hkm⟩ := exists_eq_mul_zpow hWK hZ hz₀.2 hz₀Z hz₀1 hxW
      ((rho6_eq_one_iff ψ6 hperf _).mp hρx)
    refine ⟨k, hk, z₀ ^ m * a, A.mul_mem (A.zpow_mem hz₀.1 m) ha, ?_⟩
    calc j' * a * j'⁻¹ = (j' * a * j'⁻¹ * a⁻¹) * a := by group
      _ = k * (z₀ ^ m * a) := by rw [hkm, mul_assoc]
  obtain ⟨k, hkN, hkj⟩ := Sylow155G.exists_mul_mem_normalizer hA3 hN hNJ hAN hJN hJA
    (hJmem hjW (by rw [hρj]; exact hnx))
  have hkjW : k * j ∈ W := W.mul_mem hkN.2 hjW
  refine ⟨k * j, hkjW, hkj, ?_⟩
  have e : (⟨k * j, mem_nWK hWK hkjW⟩ : ↥(nWK W K)) =
      ⟨k, mem_nWK hWK hkN.2⟩ * ⟨j, mem_nWK hWK hjW⟩ := Subtype.ext rfl
  rw [e, map_mul, hρK k hkN.2 hkN.1, one_mul, hρj]

end Generic

section Sec155

variable {G : Type} [Group G] [Finite G]
variable {A X K Y M T P : Subgroup G} [((pPrimeCoreOf 3 M).subgroupOf (w155 A M X)).Normal]
  (ψ6 : (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) ⧸
    Subgroup.center (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) ≃*
      ↥A6Models.psl29)

include ψ6 in
theorem exists_conj_le_normalizer6
    (hperf : commutator (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) = ⊤)
    (hZ : Nat.card (Subgroup.center
      (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X))) = 3)
    (hcard : Nat.card (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) = 1080)
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hf : Proof155Wx.Facts155W A X Y M P) (hBXW : b155 A M X ≤ X ⊔ w155 A M X)
    (hBN : b155 A M X ≤ n155 A K) {V : Subgroup G} (hV : V ∈ scriptQ A (lB A)) (hVM : V ≤ M) :
    ∃ w ∈ n155 A K, w ∈ Subgroup.normalizer (A : Set G) ∧
      V.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) : Subgroup G) : Set G) := by
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAn := Sylow155B2.a_le_nWK hC
  have hWK := Sylow155B2.w155_le_normalizer A M X
  have hK : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)
  obtain ⟨a₁, ha₁, ha₁1⟩ := exists_rho6_ne_one ψ6 hAF hAn hWK hK hZ hperf
  have hx : rho6 ψ6 ⟨a₁, hAn ha₁⟩ ∈ A6Models.psl29 :=
    rho6_mem_psl29_of_pow_three ψ6 _ (hAF.1.2 a₁ ha₁)
  have hx3 : rho6 ψ6 ⟨a₁, hAn ha₁⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨a₁, hAn ha₁⟩ : ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) ^ 3 = 1 from
      Subtype.ext (by simpa using hAF.1.2 a₁ ha₁), map_one]
  have hP𝓠 : P ∈ scriptQ A (lB A) := hE.mem_p.prop.1.1
  have hR𝓠 : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hP𝓠 hRP (Sylow155B1.le_normalizer_r hC)
  have hRM : CFSG.Open.pCoreOf 2 Y ≤ M := hRP.trans (hE.mem_p.prop.1.2.trans inf_le_left)
  have hn : ∀ {Q : Subgroup G}, Q ∈ scriptQ A (lB A) → Q ≤ M →
      Q ≤ nWK (w155 A M X) (pPrimeCoreOf 3 M) := fun hQ hQM =>
    (le_delta hQ hQM).trans (Sylow155B2.delta_le_nWK hIX)
  have h3Q : ∀ {Q : Subgroup G}, Q ∈ scriptQ A (lB A) → ¬ 3 ∣ Nat.card Q := fun hQ =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQ.1.2.1
  have hpsl : ∀ {Q : Subgroup G}, Q ∈ scriptQ A (lB A) → Q ≤ M →
      (Q.subgroupOf (nWK (w155 A M X) (pPrimeCoreOf 3 M))).map (rho6 ψ6) ≤
        A6Models.psl29 := by
    rintro Q hQ hQM _ ⟨⟨q, hqn⟩, hq, rfl⟩
    exact rho6_mem_psl29_of_invariant ψ6 hperf hZ hcard hAF hAn hWK hK (hn hQ hQM) hQ.1.2.2
      (h3Q hQ) ha₁ ha₁1 (Subgroup.mem_subgroupOf.mp hq)
  have hker : ∀ {k : G} (hk : k ∈ u155 A M X),
      rho6 ψ6 ⟨k, Sylow155B2.u155_le_nWK A M X hk⟩ = 1 →
      (∀ u ∈ u155 A M X, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X)) ∧
        ∃ m : ℕ, k ^ 3 ^ m ∈ pPrimeCoreOf 3 (u155 A M X) :=
    fun hk hρ => ker_central6 ψ6 hperf h hC hIX hZ hf hE.mem_x hBXW hk hρ
  by_cases hcyc : ∀ (a : G) (ha : a ∈ A),
      rho6 ψ6 ⟨a, hAn ha⟩ ∈ Subgroup.zpowers (rho6 ψ6 ⟨a₁, hAn ha₁⟩)
  ·
    obtain ⟨n, hn6, hnx, hnV⟩ := Sylow155KA6P.exists_swap hx hx3 ha₁1 (hpsl hR𝓠 hRM)
      (hpsl hV hVM) (not_dvd_card_map_rho6 ψ6 (hn hR𝓠 hRM) (h3Q hR𝓠))
      (not_dvd_card_map_rho6 ψ6 (hn hV hVM) (h3Q hV))
      (fun _ hr => rho6_conj_mem ψ6 (Sylow155B1.le_normalizer_r hC ha₁) hr)
      (fun _ hv => rho6_conj_mem ψ6 (hV.1.2.2 ha₁) hv)
    obtain ⟨w, hwW, hwA, hρw⟩ :=
      exists_mem_normalizer_rho6_eq ψ6 hperf hZ hAF hAn hWK hK hcyc hn6 hnx
    have hWB : w155 A M X ≤ b155 A M X := Subgroup.map_subtype_le _
    refine ⟨w, hBN (hWB hwW), hwA, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hvI : v ∈ delta A (lB A) M := le_delta hV hVM hv
    have hwI : w ∈ delta A (lB A) M := ((Proof155Wx.w155_le_u155 A M X).trans inf_le_left) hwW
    have hgI : w * v * w⁻¹ ∈ delta A (lB A) M :=
      (delta A (lB A) M).mul_mem ((delta A (lB A) M).mul_mem hwI hvI)
        ((delta A (lB A) M).inv_mem hwI)
    change w * v * w⁻¹ ∈ _
    refine mem_normalizer_sup_of_ker (rho6 ψ6) hker hE hRP hIX hgI ?_
    have hwn := Sylow155B2.delta_le_nWK hIX hwI
    have hvn := Sylow155B2.delta_le_nWK hIX hvI
    have e : (⟨w * v * w⁻¹, Sylow155B2.delta_le_nWK hIX hgI⟩ :
        ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) = ⟨w, hwn⟩ * ⟨v, hvn⟩ * (⟨w, hwn⟩)⁻¹ :=
      Subtype.ext rfl
    have hρw' : rho6 ψ6 ⟨w, hwn⟩ = n := hρw
    rw [e, map_mul, map_mul, map_inv, hρw']
    exact hnV _ ⟨⟨v, hvn⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  ·
    obtain ⟨b, hb, hbA⟩ : ∃ (b : G) (hb : b ∈ A),
        rho6 ψ6 ⟨b, hAn hb⟩ ∉ Subgroup.zpowers (rho6 ψ6 ⟨a₁, hAn ha₁⟩) := by
      by_contra hne
      exact hcyc fun a ha => Classical.byContradiction fun hna => hne ⟨a, ha, hna⟩
    refine ⟨1, one_mem _, one_mem _, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hvI : v ∈ delta A (lB A) M := le_delta hV hVM hv
    change (1 : G) * v * (1 : G)⁻¹ ∈ _
    rw [one_mul, inv_one, mul_one]
    refine mem_normalizer_sup_of_ker (rho6 ψ6) hker hE hRP hIX hvI ?_
    have hρv : rho6 ψ6 ⟨v, Sylow155B2.delta_le_nWK hIX hvI⟩ = 1 :=
      rho6_eq_one_of_not_mem_zpowers ψ6 hperf hZ hcard hAF hAn hWK hK (hn hV hVM) hV.1.2.2
        (h3Q hV) ha₁ ha₁1 hb hbA hv
    rw [hρv]
    exact one_mem _

end Sec155

end Sylow155B3

end CFSG.RankThree.PartTwo.Sec15
