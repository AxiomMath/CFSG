module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47LemmaR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47NoL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_A9 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M)
    (ctx : G47Ctx D V₀ V L hV x)
    (hX : IsSL2Prime ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) 5)
    {u : Bar2 (centralizer ({x.val} : Set G))}
    (hu : u ∈ starImg (centralizer ({x.val} : Set G)) V) (hu1 : u ≠ 1)
    (hVu : ∀ v ∈ starImg (centralizer ({x.val} : Set G)) V, v = 1 ∨ v = u) :
    ∀ c : Bar2 (centralizer ({x.val} : Set G)),
      (∀ y ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val), c * y = y * c) →
        c * u = u * c := by
  have hSt := G47Star.of_ctx hsp hL ctx hX
  have hXHL := s16c1_G47_xInf_le L x.val
  have hXH : xInf L x.val ≤ centralizer ({x.val} : Set G) := hXHL.trans inf_le_left
  have hXM : xInf L x.val ≤ D.M := (hXHL.trans inf_le_right).trans hL.1.le
  have hQM : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ D.M := s16c1_pCoreOf_le_M D ctx.sylow
  have h120 : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) = 120 :=
    (s16c1_sl2five_facts hX).1
  have h3X : 3 ∣ Nat.card ↥(xInf L x.val) := by
    have h := s16c1_G47_card_starImg_mul hXH
    rw [h120] at h
    rw [← h]
    exact Dvd.dvd.mul_right (by norm_num) _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xInf L x.val)) 3 h3X
  have hd3 : orderOf (d : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd
  intro c hc
  have hdbar : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G)))
      ⟨(d : G), hXH d.2⟩ ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val) :=
    Subgroup.mem_map.2 ⟨⟨(d : G), hXH d.2⟩, Subgroup.mem_subgroupOf.2 d.2, rfl⟩
  have hcent : c ∈ Subgroup.centralizer
      ((Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G)))
        ⟨(d : G), hXH d.2⟩) : Subgroup (Bar2 (centralizer ({x.val} : Set G)))) :
        Set (Bar2 (centralizer ({x.val} : Set G)))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((show Commute c _ from hc _ hdbar).zpow_right k).eq.symm
  have hB := s16c1_G47_star_normalizer_le hQM hsp hXH hXM d.2 hd3
    (Subgroup.centralizer_le_normalizer _ hcent)
  have hcu : c * u * c⁻¹ ∈ starImg (centralizer ({x.val} : Set G)) V := hSt.conj_B c hB u hu
  have hcu1 : c * u * c⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have : u = c⁻¹ * 1 * c := by rw [← h]; group
    simpa using this
  have heq : c * u * c⁻¹ = u := (hVu _ hcu).resolve_left hcu1
  exact mul_inv_eq_iff_eq_mul.1 heq

theorem s16c1_G47_odd_module_false {Hs : Type} [Group Hs] [Finite Hs] {Xs Ys Vs B : Subgroup Hs}
    (hO2 : CFSG.pCore 2 Hs = ⊥) (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup Hs) ≤ 1)
    (hrk : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (⊤ : Subgroup Hs) ≤ 2)
    (hY : Ys.Normal) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5) (hodd : EqTimesOdd Xs Ys)
    (hHs : ∀ h : Hs, ∃ y ∈ Ys, ∃ b ∈ B, h = y * b)
    (hVB : ∀ b ∈ B, ∀ v ∈ Vs, b * v * b⁻¹ ∈ Vs) (hV2 : IsPGroup 2 Vs)
    (hXV : ∀ y ∈ Xs, ∀ v ∈ Vs, y * v * y⁻¹ ∈ Vs) (hcard : Nat.card ↥Vs = 2)
    {u : Hs} (hu : u ∈ Vs) (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hA9 : ∀ c : Hs, (∀ y ∈ Xs, c * y = y * c) → c * u = u * c)
    {F : Type} [Group F] [Finite F] (hF : ∀ e : F, e * e = 1) (ρ : Hs →* MulAut F)
    (hD : ∃ e : F, ρ u e * e ≠ 1)
    (hTI : ∀ r : Hs, r * u * r⁻¹ ≠ u → ∀ e e' : F, ρ r (ρ u e * e) = ρ u e' * e' →
      ρ u e * e = 1)
    (hSc : ∀ c : Hs, ∀ q : ℕ, q.Prime → 5 ≤ q → orderOf c = q → c * u = u * c →
      (∀ y ∈ Xs, c * y = y * c) → ∀ e : F, ρ c (ρ u e * e) = ρ u e * e) : False := by
  classical
  obtain ⟨N, hNY, hNn, hNodd, hYeq⟩ := hodd
  obtain ⟨N₀, hN₀, hN₀odd, hNN₀, hN₀Y, hXN₀⟩ := s16c1_G47_oddNormal hY hXY hX hNY hNn hNodd
  obtain ⟨hX120, hperf, -⟩ := s16c1_sl2five_facts hX
  haveI : Group.IsPerfect ↥Xs := Group.isPerfect_def.2 (by simpa [commutator_def] using hperf)
  have h3 : ¬ 3 ∣ Nat.card ↥N₀ :=
    s16c1_G47_no_three hXY hN₀Y (Subgroup.Normal.subgroupOf hN₀ Ys) hXN₀
      (by rw [hX120]; norm_num) hr3
  have hVX := s16c1_G47_comm_of_card_le_four hX hXV (by omega)
  have hux : ∀ y ∈ Xs, u * y = y * u := fun y hy => hVX u hu y hy
  have hnN : ∃ n ∈ N₀, u * n * u⁻¹ ≠ n := by
    by_contra hcon
    push Not at hcon
    have hle : Ys ≤ centralizer ({u} : Set Hs) := by
      refine hYeq.le.trans (sup_le (fun y hy => ?_) (fun n hn => ?_))
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact hux y hy
      · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact mul_inv_eq_iff_eq_mul.1 (hcon n (hNN₀ hn))
    exact hu1 (s16c1_G47_cent_trivial hO2 hY hHs hVB hV2 u hu fun y hy =>
      Subgroup.mem_centralizer_iff.1 (hle hy) u (Set.mem_singleton u))
  exact s16c1_G47_lemmaR ‹Group.IsPerfect ↥Xs› hN₀ hN₀odd h3 hrk hu2 hux hnN hA9 hF ρ hD hTI hSc

theorem s16c1_G47_wrap {D : Data G} (hsp : IsStronglyPEmbedded 3 D.M) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : IntMod V hV} (hL : L ∈ calC D.M)
    (ctx : G47Ctx D V₀ V L hV x) (h46 : Concl1646 L x.val) (h47 : Concl1647 V x.val)
    {F : Type} [Group F] [Finite F] (hF : ∀ e : F, e * e = 1)
    (ρ : Bar2 (centralizer ({x.val} : Set G)) →* MulAut F)
    (hD : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, u ≠ 1 → ∃ e : F, ρ u e * e ≠ 1)
    (hTI : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, u ≠ 1 →
      ∀ r : Bar2 (centralizer ({x.val} : Set G)), r * u * r⁻¹ ≠ u → ∀ e e' : F,
        ρ r (ρ u e * e) = ρ u e' * e' → ρ u e * e = 1)
    (hSc : ∀ u ∈ starImg (centralizer ({x.val} : Set G)) V, u ≠ 1 →
      ∀ c : Bar2 (centralizer ({x.val} : Set G)), ∀ q : ℕ, q.Prime → 5 ≤ q → orderOf c = q →
        c * u = u * c →
        (∀ y ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val), c * y = y * c) →
          ∀ e : F, ρ c (ρ u e * e) = ρ u e * e) : False := by
  have hX := h46.2.2.1
  have hSt := G47Star.of_ctx hsp hL ctx hX
  have hodd := h46.2.2.2.resolve_left (s16c1_G47_noL3 hSt h46 h47)
  have hrk : ∀ q : ℕ, q.Prime → 3 < q →
      CFSG.Open.pRank q (⊤ : Subgroup (Bar2 (centralizer ({x.val} : Set G)))) ≤ 2 := by
    intro q hq h3
    rw [s16c1_G47_pRank_bar _ hq (by omega)]
    exact ctx.rankq q hq h3
  obtain ⟨⟨u, hu⟩, hu1, huniq⟩ := (Nat.card_eq_two_iff'
    (1 : ↥(starImg (centralizer ({x.val} : Set G)) V))).1 h47.1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hVu : ∀ v ∈ starImg (centralizer ({x.val} : Set G)) V, v = 1 ∨ v = u := by
    intro v hv
    by_cases hv1 : v = 1
    · exact Or.inl hv1
    · exact Or.inr (congrArg Subtype.val (huniq ⟨v, hv⟩ (fun h => hv1 (congrArg Subtype.val h))))
  exact s16c1_G47_odd_module_false hSt.pCore_bot hSt.pRank_le hrk hSt.normal_Y hSt.le_XY hX hodd
    hSt.split hSt.conj_B hSt.pgroup hSt.conj_X h47.1 hu hu1' (hSt.sq u hu)
    (s16c1_G47_A9 hsp hL ctx hX hu hu1' hVu) hF ρ (hD u hu hu1') (hTI u hu hu1')
    (hSc u hu hu1')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
