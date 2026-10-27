module

public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Defs
public import CFSG.Quasithin.Vol2.GoldschmidtE217E4Core
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Quot
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217Bridge
public import CFSG.Quasithin.Vol2.Ch3E213MP3E
public import CFSG.Quasithin.Vol2.GoldschmidtE217Torus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3 E217R1
open CFSG.GorensteinWalter (PSL2)

namespace E217R4

theorem r4PkgOdd4
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : R4PkgOdd4 := by
  intro G _ _ H T M V K hS _ h1 p hp hp8 hPSL _ haut
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', hDker⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  obtain ⟨-, -, -, hKn, hCK, -, ⟨hSB, -, -⟩, -, hEcard, hEO⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ :=
    exists_paired_of_case1_aux h38 hS.hyp hS.mem_cComp hS.eq_sup h1
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hD
  set π := QuotientGroup.mk' D with hπ
  set K₁ := barIn M H K with hK₁
  set S := (T' : Subgroup H).map π with hSdef
  set E := (V.subgroupOf H).map π with hEdef
  rw [hK] at hKn hCK
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  obtain ⟨-, F, _, _, hF, ⟨ψ₀⟩⟩ := hPSL
  have hF' : Nat.card F = p := by rw [hF, pow_one]
  set θ : K₁ ≃* PSL2 F := φ.trans (ψ₀.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm) with hθ
  have := P3.isSimpleGroup_of hp hp8 hF' θ
  have hS2 : IsPGroup 2 S := T'.isPGroup'.map π
  have hSsyl : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hS2, ?_⟩
    show ¬ 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := (T'.mapSurjective (QuotientGroup.mk'_surjective D)).not_dvd_index
    rwa [Sylow.coe_mapSurjective] at h
  have htS : π t₀ ∈ S := ⟨t₀, hT' ▸ ht₀T, rfl⟩
  have haut' : 8 < E2.autCard S K₁ := by
    have hST : S = barIn M H T := by rw [hSdef, hT']; rfl
    rw [← P3.autCard_map (starEquiv hMH), hST, hK₁, map_barIn_starEquiv, map_barIn_starEquiv]
    exact haut
  set K₂ := K₁.map (MulAut.conj (π t₀)).toMonoidHom with hK₂
  have hSE : S ≤ Subgroup.normalizer (E : Set (↥H ⧸ D)) :=
    (Subgroup.map_mono hTV').trans (Subgroup.le_normalizer_map π)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have h := hS.hyp.elem.1.is_comm.comm (⟨(v : G), hv⟩ : V) ⟨(w : G), hw⟩
    exact Subtype.ext (congrArg (Subtype.val : V → G) h)
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian v hv, map_one]
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ'
  have hDeq : D = (pCoreOf 2 H).subgroupOf H :=
    (kerIn_subgroupOf_top_eq hMH).trans (by rw [h1.1])
  have hker : ∀ w : ↥H, π w = 1 ↔ (w : G) ∈ pCoreOf 2 H := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hDeq, Subgroup.mem_subgroupOf]
  have hcube : E ≤ Subgroup.normalizer (K₁ : Set (↥H ⧸ D)) → ∀ x ∈ E,
      x ∉ E ⊓ Subgroup.centralizer (K₁ : Set (↥H ⧸ D)) →
      (∀ e ∈ E, e ∈ E ⊓ Subgroup.centralizer (K₁ : Set (↥H ⧸ D)) ∨
        x * e ∈ E ⊓ Subgroup.centralizer (K₁ : Set (↥H ⧸ D))) → ∀ g ∈ K₁, ∀ n : ℕ, Odd n →
      (x * (g * x * g⁻¹)) ^ n = 1 → (x * (g * x * g⁻¹)) ^ 3 = 1 := by
    intro hEN x hxE hxA hdec g hg n hn hyn
    set A₁ := E ⊓ Subgroup.centralizer (K₁ : Set (↥H ⧸ D)) with hA₁
    have hx2 : x * x = 1 := hE2 x hxE
    obtain ⟨x', hx', rfl⟩ := hxE
    obtain ⟨g', hg', rfl⟩ := hg
    have hgK : (g' : G) ∈ K := hg'
    set Ũ : Subgroup ↥H := V.subgroupOf H ⊓ A₁.comap π with hŨ
    have hcoe : ∀ k : ℕ, (((x' * (g' * x' * g'⁻¹)) ^ k : ↥H) : G) =
        ((x' : G) * ((g' : G) * (x' : G) * (g' : G)⁻¹)) ^ k := fun k => by simp
    have hyn' : ((x' : G) * ((g' : G) * (x' : G) * (g' : G)⁻¹)) ^ n ∈ kerIn M H := by
      rw [h1.1, ← hcoe n]
      apply (hker _).1
      rw [map_pow, map_mul, map_mul, map_mul, map_inv]
      exact hyn
    have key := E2.cube_mem_kerIn_of_odd (U := Ũ.map H.subtype) hS.hyp hS.charTwo hS.V16 hS.q32
      (by rintro _ ⟨u, ⟨hu, -⟩, rfl⟩; exact hu)
      (by
        rintro v ⟨hvV, hvQ⟩
        have hvH : v ∈ H := hVH hvV
        refine ⟨⟨v, hvH⟩, ⟨hvV, ?_⟩, rfl⟩
        show π ⟨v, hvH⟩ ∈ A₁
        rw [(hker ⟨v, hvH⟩).2 hvQ]
        exact one_mem A₁)
      (x := (x' : G)) hx'
      (by
        rintro ⟨u, ⟨-, hu⟩, hux⟩
        have : u = x' := Subtype.ext hux
        rw [this] at hu
        exact hxA hu)
      (by
        intro v hv
        have hvH : v ∈ H := hVH hv
        have hv' : (⟨v, hvH⟩ : ↥H) ∈ V.subgroupOf H := hv
        have hπv : π ⟨v, hvH⟩ ∈ E := ⟨_, hv', rfl⟩
        rcases hdec _ hπv with h | h
        · left
          exact ⟨⟨v, hvH⟩, ⟨hv, h⟩, rfl⟩
        · right
          have hxv : x' * ⟨v, hvH⟩ ∈ V.subgroupOf H := (V.subgroupOf H).mul_mem hx' hv'
          refine ⟨x' * ⟨v, hvH⟩, ⟨hxv, ?_⟩, rfl⟩
          show π (x' * ⟨v, hvH⟩) ∈ A₁
          rw [map_mul]
          exact h)
      (g := (g' : G)) g'.2
      (by
        intro u hu
        obtain ⟨u', ⟨-, hu'A⟩, rfl⟩ := hu
        have hg'K : π g' ∈ K₁ := ⟨g', hg', rfl⟩
        have haK : π x' * π g' * (π x')⁻¹ ∈ K₁ :=
          (Subgroup.mem_normalizer_iff.mp (hEN ⟨x', hx', rfl⟩) _).mp hg'K
        set y' : ↥H := x' * (g' * x' * g'⁻¹) with hy'
        have hπy : π y' ∈ K₁ := by
          have : π y' = (π x' * π g' * (π x')⁻¹) * (π g')⁻¹ := by
            rw [hy', map_mul, map_mul, map_mul, map_inv]
            have hai : (π x')⁻¹ = π x' := inv_eq_of_mul_eq_one_right hx2
            rw [hai]
            group
          rw [this]
          exact K₁.mul_mem haK (K₁.inv_mem hg'K)
        have hcomm := Subgroup.mem_centralizer_iff.1 hu'A.2 (π y') hπy
        have h1' : π (y' * u' * y'⁻¹ * u'⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
          group
        exact (hker _).1 h1')
      hn hyn'
    rw [h1.1] at key
    have h3 : π ((x' * (g' * x' * g'⁻¹)) ^ 3) = 1 := by
      rw [hker, hcoe]
      exact key
    rw [map_pow, map_mul, map_mul, map_mul, map_inv] at h3
    exact h3
  obtain ⟨Ā, T₀, hA9, hT₀S, hT₀N, hirr, hET, v, hvE, hvinv⟩ :=
    e4_core hp hp8 hF' θ hc hd hKn hCK hSsyl htS rfl haut' hSE hEc hE2 hE4 hcube
  obtain ⟨x₀, hx₀, rfl⟩ := hvE
  have hST : S = (T.subgroupOf H).map π := by rw [hSdef, hT']
  refine false_of_quotient hS.hyp hS.charTwo hS.q32 hS.V16 (D := D) hDeq hA9
    (hT₀S.trans hST.le) hT₀N hirr (v := (x₀ : G)) hx₀ hET fun a ha => ?_
  exact hvinv a ha

end E217R4

end CFSG.Quasithin
