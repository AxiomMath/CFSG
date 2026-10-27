module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5U34M
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Rk2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5In
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem autControlAt_top_of_isPSU_cs5 {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hG : IsPSU 3 2 n G) (T : Sylow 2 G) : AutControlAt (T : Subgroup G) := by
  obtain ⟨e⟩ := exists_mulEquiv_psu3_proj_cs5 hn hG
  haveI := psuK_charP_cs5 n
  haveI := finite_psu_cs5 (binaryQuadraticHermitian n (by omega))
  have hKcard : Nat.card (PsuKCS5 n) = (2 ^ n) ^ 2 := psuK_card_cs5 n (by omega)
  have hfixed : Nat.card {x : PsuKCS5 n // (binaryQuadraticHermitian n (by omega)).conj x = x} =
      2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
  exact autControlAt_of_mulEquiv e
    (fun T' => UnitaryAut.autControlAt_projectiveSpecialUnitary
      (binaryQuadraticHermitian n (by omega)) n hn hKcard hfixed rfl T') T

theorem mem_normalizer_of_commute_centerSub_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ}
    (hR : RankOneSyl X S q) {x : Y} (hxX : x ∈ X) (hxZ : ∀ z ∈ centerSub S, z * x = x * z) :
    x ∈ Subgroup.normalizer (S : Set Y) := by
  by_contra hxN
  have hZ : centerSub S ≤ S ⊓ B6.conjSub x S := by
    refine le_inf (centerSub_le_cs5 S) (fun z hz => ?_)
    rw [B6.mem_conjSub]
    have : x⁻¹ * z * x = z := by rw [mul_assoc, hxZ z hz, inv_mul_cancel_left]
    rw [this]
    exact centerSub_le_cs5 S hz
  rw [hR.ti x hxX hxN] at hZ
  exact centerSub_ne_bot_cs5 hR (le_bot_iff.mp hZ)

theorem elemAbelian_le_of_isPSU_cs5 {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y} [X.Normal]
    {n : ℕ} (hn : 2 ≤ n) (hX : IsPSU 3 2 n ↥X)
    (hC : ∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1) (hS : IsSylowTwoOf S X)
    {E : Subgroup Y} (hE : IsElemAbelian 2 E)
    (hB : X ⊓ Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (E : Set Y))
    (hZ : centerSub S ≤ E) : E ≤ X := by
  have hR : RankOneSyl X S (2 ^ n) := rankOneSyl_of_isPSU_three_cs5 hn hX hS
  have hSX : S ≤ X := hS.1
  by_contra hEX
  obtain ⟨t, htE, htX⟩ : ∃ t ∈ E, t ∉ X := by
    by_contra h
    exact hEX fun x hx => by_contra fun hx' => h ⟨x, hx, hx'⟩
  have ht2 : t * t = 1 := by simpa [pow_two] using hE.2 t htE
  have htZ : ∀ z ∈ centerSub S, t * z = z * t := fun z hz => by
    have := congrArg Subtype.val
      (isMulCommutative_iff.mp hE.1 ⟨t, htE⟩ ⟨z, hZ hz⟩)
    exact this
  have hSt : B6.conjSub t S = S := by
    obtain ⟨g, hgX, hgeq⟩ :=
      exists_conj_eq_of_isSylowTwoOf_cs5 hS (isSylowTwoOf_conjSub_cs5 hS t)
    have hZle : centerSub S ≤ B6.conjSub t S := by
      intro z hz
      rw [B6.mem_conjSub]
      have : t⁻¹ * z * t = z := by rw [mul_assoc, ← htZ z hz, inv_mul_cancel_left]
      rw [this]
      exact centerSub_le_cs5 S hz
    by_cases hgN : g ∈ Subgroup.normalizer (S : Set Y)
    · rw [hgeq]
      exact B6.conjSub_eq_self hgN
    · exfalso
      have hZ' : centerSub S ≤ S ⊓ B6.conjSub g S :=
        le_inf (centerSub_le_cs5 S) (hgeq ▸ hZle)
      rw [hR.ti g hgX hgN] at hZ'
      exact centerSub_ne_bot_cs5 hR (le_bot_iff.mp hZ')
  have htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => by
    have : t * s * t⁻¹ ∈ B6.conjSub t S := by
      rw [B6.mem_conjSub]
      have : t⁻¹ * (t * s * t⁻¹) * t = s := by group
      rw [this]
      exact hs
    rwa [hSt] at this
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf_top_cs5 ((isSylowTwoOf_top_iff_cs5 hSX).mpr hS)
  have hAut := autControlAt_top_of_isPSU_cs5 hn hX T
  rw [hT] at hAut
  have hcs : centerSub (S.subgroupOf X) = sylowCenter (S.subgroupOf X) :=
    map_center_eq_sylowCenter _
  have hα2 : (MulAut.conjNormal t : MulAut ↥X) ^ 2 = 1 := by
    rw [← map_pow, pow_two, ht2, map_one]
  obtain ⟨-, -, s₀, hs₀, hs₀Z⟩ := hAut (MulAut.conjNormal t)
    (fun s hs => by
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      rw [MulAut.conjNormal_apply]
      exact htS _ hs)
    (fun z hz => by
      rw [← hcs] at hz
      have hz' := (mem_centerSub_subgroupOf_cs5 hSX z).mp hz
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := htZ _ hz'
      rw [this, mul_inv_cancel_right])
    ⟨1, by rw [pow_one]; exact hα2⟩
    (fun s hs heq => by
      apply htX
      have hy : (s : Y)⁻¹ * t = 1 := hC _ (fun x hx => by
        have h1 := congrArg (fun a : MulAut ↥X => ((a ⟨x, hx⟩ : ↥X) : Y)) heq
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h1
        calc (s : Y)⁻¹ * t * x = (s : Y)⁻¹ * (t * x * t⁻¹) * t := by group
          _ = (s : Y)⁻¹ * ((s : Y) * x * (s : Y)⁻¹) * t := by rw [h1]
          _ = x * ((s : Y)⁻¹ * t) := by group)
      have hts : t = s := (inv_mul_eq_one.mp hy).symm
      rw [hts]
      exact s.2)
  apply hs₀Z
  rw [← hcs]
  refine (mem_centerSub_subgroupOf_cs5 hSX _).mpr ?_
  have hs₀S : (s₀ : Y) ∈ S := Subgroup.mem_subgroupOf.mp hs₀
  have hnE : (s₀ : Y)⁻¹ ∈ Subgroup.normalizer (E : Set Y) :=
    hB ⟨X.inv_mem s₀.2, Subgroup.inv_mem _ (Subgroup.le_normalizer hs₀S)⟩
  have hv : (s₀ : Y)⁻¹ * t * (s₀ : Y) ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp hnE t).mp htE
    simpa using this
  have hu : (s₀ : Y)⁻¹ * (t * (s₀ : Y) * t⁻¹) ∈ E := by
    have e : (s₀ : Y)⁻¹ * (t * (s₀ : Y) * t⁻¹) = ((s₀ : Y)⁻¹ * t * (s₀ : Y)) * t⁻¹ := by group
    rw [e]
    exact E.mul_mem hv (E.inv_mem htE)
  have huS : (s₀ : Y)⁻¹ * (t * (s₀ : Y) * t⁻¹) ∈ S := S.mul_mem (S.inv_mem hs₀S) (htS _ hs₀S)
  have hu2 : (s₀ : Y)⁻¹ * (t * (s₀ : Y) * t⁻¹) * ((s₀ : Y)⁻¹ * (t * (s₀ : Y) * t⁻¹)) = 1 := by
    simpa [pow_two] using hE.2 _ hu
  have := hR.omega1 _ huS hu2
  simpa [MulAut.conjNormal_apply] using this

theorem five_dvd_card_centralizer_cs5 {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y}
    (hX : IsPSU 3 2 2 ↥X) (hS : IsSylowTwoOf S X) {g : Y} (hg : g ∈ X)
    (hgN : g ∉ Subgroup.normalizer (S : Set Y)) :
    5 ∣ Nat.card ↥(X ⊓ Subgroup.centralizer
      ((centerSub S ⊔ B6.conjSub g (centerSub S) : Subgroup Y) : Set Y)) := by
  have hSX : S ≤ X := hS.1
  obtain ⟨c, hc5, hcz, hcg⟩ := fiveCent_top_of_isPSU_cs5 hX (S.subgroupOf X)
    ((isSylowTwoOf_top_iff_cs5 hSX).mpr hS) ⟨g, hg⟩
    (fun hc => hgN ((mem_normalizer_subgroupOf_cs5 hSX ⟨g, hg⟩).mp hc))
  have hcomm : ∀ z ∈ centerSub S, (c : Y) * z = z * c := fun z hz => by
    have hzX : z ∈ X := hSX (centerSub_le_cs5 S hz)
    have := congrArg Subtype.val
      (hcz ⟨z, hzX⟩ ((mem_centerSub_subgroupOf_cs5 hSX ⟨z, hzX⟩).mpr hz))
    exact this
  have hcommg : ∀ z ∈ centerSub S, (c : Y) * (g * z * g⁻¹) = g * z * g⁻¹ * c := fun z hz => by
    have hzX : z ∈ X := hSX (centerSub_le_cs5 S hz)
    have := congrArg Subtype.val
      (hcg ⟨z, hzX⟩ ((mem_centerSub_subgroupOf_cs5 hSX ⟨z, hzX⟩).mpr hz))
    simpa using this
  have hmem : (c : Y) ∈ X ⊓ Subgroup.centralizer
      ((centerSub S ⊔ B6.conjSub g (centerSub S) : Subgroup Y) : Set Y) := by
    refine ⟨c.2, ?_⟩
    have hle : (centerSub S ⊔ B6.conjSub g (centerSub S) : Subgroup Y) ≤
        Subgroup.centralizer ({(c : Y)} : Set Y) := by
      refine sup_le (fun z hz => ?_) (fun z' hz' => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hcomm z hz
      · rw [B6.mem_conjSub] at hz'
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        have := hcommg _ hz'
        have e : g * (g⁻¹ * z' * g) * g⁻¹ = z' := by group
        rwa [e] at this
    refine Subgroup.mem_centralizer_iff.mpr (fun w hw => ?_)
    have := (Subgroup.mem_centralizer_iff.mp (hle hw)) (c : Y) (Set.mem_singleton _)
    exact this.symm
  have hd := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [Subgroup.orderOf_coe, hc5] at hd

theorem u34Facts_cs5 : U34Facts := by
  intro Y _ _ X S _ hX hC hS
  have hR : RankOneSyl X S (2 ^ 2) := rankOneSyl_of_isPSU_three_cs5 le_rfl hX hS
  refine ⟨fun E hE hB hZ => elemAbelian_le_of_isPSU_cs5 le_rfl hX hC hS hE hB hZ,
    fun g hg hgN => ⟨five_dvd_card_centralizer_cs5 hX hS hg hgN, fun x hx => ?_⟩⟩
  obtain ⟨hxX, hxc⟩ := Subgroup.mem_inf.mp hx
  refine mem_normalizer_of_commute_centerSub_cs5 hR hxX (fun z hz => ?_)
  exact Subgroup.mem_centralizer_iff.mp hxc z
    ((le_sup_left : centerSub S ≤ centerSub S ⊔ B6.conjSub g (centerSub S)) hz)

end CFSG.Quasithin.H13
