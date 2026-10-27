module

public import CFSG.RankThree.PartOne.K1327.ClaimA
public import CFSG.RankThree.PartOne.K1327.Basic
import CFSG.RankThree.PartOne.HNB.Tools
public import CFSG.RankThree.PartOne.K1320.L4Core

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem moved_le_L (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (fr : Row8Frame p A L E f K) {d : MulAut E} (hd : d = fr.r₁ ∨ d = fr.r₀ * fr.r₁ * fr.r₀⁻¹) :
    autMovedInG E d ≤ L := by
  have h1 : autMovedInG E fr.r₁ ≤ L :=
    fr.kf₁.2.2.2.1.trans (kZero_le_of_reflection h hF13 fr.mem₁ fr.mem₁L)
  rcases hd with rfl | rfl
  · exact h1
  · obtain ⟨w, hwL, hwN, hw⟩ := Sec12Three.mem_torusImage_iff.1 fr.mem₀L
    have hw' : conjAut E w hwN = fr.r₀ := hw
    rw [← hw', Equivariance.autMovedInG_conj fr.r₁ hwN]
    have h2 : conjBy w (autMovedInG E fr.r₁) ≤ conjBy w L := Subgroup.map_mono h1
    rwa [conjBy_eq_self_of_mem' hwL] at h2


theorem commute_of_third (hp : p.Prime) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 3) (hEA : E = A)
    (Bd : Bridge p E) (fr : Row8Frame p A L E f K) (hZ : Subgroup.center L = ⊥)
    {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) {zs : MulAut E} (hcore : fr.Core c r zs)
    (hR0 : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : fr.lft (Rr K r) ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRE : ∀ x ∈ fr.lft (Rr K r), ∀ e ∈ E, x * e = e * x)
    {d'' : MulAut E} (hd'' : d'' = fr.r₁ ∨ d'' = fr.r₀ * fr.r₁ * fr.r₀⁻¹)
    {b : G} (hb : b ∈ autMovedInG E d'') (hb1 : b ≠ 1) {u : G}
    (huV : u ∈ Vof p (Jof p (fr.lft (Rr K r)))) (hub : u * b = b * u) : Commute u c := by
  set R := fr.lft (Rr K r) with hRdef
  set J := Jof p R with hJdef
  set V := Vof p J with hVdef
  have hp5 := Sec12Three.five_le h
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEM : ∀ e ∈ E, e ∈ Subgroup.centralizer (R : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hRE x hx e he
  have hEJ : ∀ e ∈ E, e ∈ J := fun e he =>
    mem_Jof_of_pow hp (hEM e he) (Sec12Three.pow_eq_one_of_mem_E h he)
  have hJM : J ≤ Subgroup.centralizer (R : Set G) := by
    rw [hJdef, Jof_def]
    unfold pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have huM : ∀ x ∈ R, u * x = x * u := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (hJM (Vof_le p J huV)) x hx).symm
  obtain ⟨g₀, hg₀X, hg₀⟩ := hcore.conj
  have hr₀X : fr.r₀ ∈ reflectionGroup p E := Subgroup.subset_closure fr.mem₀
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  have hzsr₀ : zs ≠ fr.r₀ := fun h1 => hcore.notL (h1 ▸ hL₀)
  have hzsr₁ : zs ≠ fr.r₁ := fun h1 => hcore.notL (h1 ▸ hL₁)
  have hzs1 : zs ≠ fr.r₀ * fr.r₁ * fr.r₀⁻¹ := fun h1 =>
    hcore.notL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
      ((torusImage E L).inv_mem hL₀))
  have hzs2 : zs ≠ fr.r₁ * fr.r₀ * fr.r₁⁻¹ := fun h1 =>
    hcore.notL (h1 ▸ (torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
      ((torusImage E L).inv_mem hL₁))
  have hd''ne : d'' ≠ zs := by
    rcases hd'' with rfl | rfl
    · exact fun e => hzsr₁ e.symm
    · exact fun e => hzs1 e.symm
  obtain ⟨x, hxX, hx⟩ : ∃ x ∈ reflectionGroup p E, x * zs * x⁻¹ = d'' := by
    rcases hd'' with rfl | rfl
    · refine ⟨g₀⁻¹, inv_mem hg₀X, ?_⟩
      rw [← hg₀]
      group
    · refine ⟨fr.r₀ * g₀⁻¹, mul_mem hr₀X (inv_mem hg₀X), ?_⟩
      rw [← hg₀]
      group
  obtain ⟨y, hy, hyx⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hxX)
  have hxy : conjAut E y hy * zs * (conjAut E y hy)⁻¹ = d'' := by
    rw [hyx]
    exact hx
  have hRy : conjBy y R = R := hcore.R_norm y hy (by rw [hyx]; exact hxX)
  have hJy : conjBy y J = J := conjBy_Jof hRy
  have hVy : conjBy y V = V := conjBy_Vof hp hJy
  have hu'V : y⁻¹ * u * y ∈ V := by
    have : u ∈ conjBy y V := by
      rw [hVy]
      exact huV
    exact Equivariance.mem_conjBy.1 this
  have hu'R : ∀ x ∈ R, (y⁻¹ * u * y) * x = x * (y⁻¹ * u * y) := by
    intro x hx
    have hx' : y * x * y⁻¹ ∈ R := by
      have : y * x * y⁻¹ ∈ conjBy y R := by
        rw [Equivariance.mem_conjBy]
        have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
        rw [e]
        exact hx
      rwa [hRy] at this
    have h1 := huM _ hx'
    calc y⁻¹ * u * y * x = y⁻¹ * (u * (y * x * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * x * y⁻¹) * u) * y := by rw [h1]
      _ = x * (y⁻¹ * u * y) := by group
  have hmovd : autMovedInG E d'' = conjBy y (Subgroup.zpowers c) := by
    rw [← hxy, Equivariance.autMovedInG_conj zs hy, hcore.mov]
  have hb' : y⁻¹ * b * y ∈ Subgroup.zpowers c := by
    have : b ∈ conjBy y (Subgroup.zpowers c) := hmovd ▸ hb
    exact Equivariance.mem_conjBy.1 this
  have hb'1 : y⁻¹ * b * y ≠ 1 := by
    intro e
    apply hb1
    have := congrArg (fun z => y * z * y⁻¹) e
    simpa [mul_assoc] using this
  have hu'b : (y⁻¹ * u * y) * (y⁻¹ * b * y) = (y⁻¹ * b * y) * (y⁻¹ * u * y) := by
    calc (y⁻¹ * u * y) * (y⁻¹ * b * y) = y⁻¹ * (u * b) * y := by group
      _ = y⁻¹ * (b * u) * y := by rw [hub]
      _ = (y⁻¹ * b * y) * (y⁻¹ * u * y) := by group
  have : Fact p.Prime := ⟨hp⟩
  have hcb' : c ∈ Subgroup.zpowers (y⁻¹ * b * y) :=
    HNB.mem_zpowers_of_mem_zpowers_prime (Sec12Three.orderOf_c h) hb' hb'1
  have hu'c : (y⁻¹ * u * y) * c = c * (y⁻¹ * u * y) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcb'
    rw [← hm]
    exact (Commute.zpow_right (show Commute (y⁻¹ * u * y) (y⁻¹ * b * y) from hu'b) m).eq
  have hvcl := Bd.vclass h hcard fr.mem₀ fr.mem₁ hcore.mem fr.ord₀₁ (hcore.comm _ hL₀)
    (hcore.comm _ hL₁) hzsr₀ hzsr₁ hzs1 hzs2 ⟨g₀, hg₀X, hg₀⟩ (x⁻¹ * g₀)
    ((reflectionGroup p E).mul_mem ((reflectionGroup p E).inv_mem hxX) hg₀X)
  have hz3 : x⁻¹ * zs * x = fr.r₁ ∨ x⁻¹ * zs * x = fr.r₀ * fr.r₁ * fr.r₀⁻¹ := by
    have e : x⁻¹ * g₀ * fr.r₁ * (x⁻¹ * g₀)⁻¹ = x⁻¹ * zs * x := by
      calc x⁻¹ * g₀ * fr.r₁ * (x⁻¹ * g₀)⁻¹ = x⁻¹ * (g₀ * fr.r₁ * g₀⁻¹) * x := by group
        _ = x⁻¹ * zs * x := by rw [hg₀]
    rw [e] at hvcl
    rcases hvcl with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      apply hd''ne
      rw [← hx]
      calc x * zs * x⁻¹ = x * (x⁻¹ * zs * x) * x⁻¹ := by rw [h1]
        _ = zs := by group
  have hmov3 : autMovedInG E (x⁻¹ * zs * x) = conjBy y⁻¹ (Subgroup.zpowers c) := by
    have h1 := Equivariance.autMovedInG_conj zs ((Subgroup.normalizer (E : Set G)).inv_mem hy)
    rw [Equivariance.conjAut_inv hy, hyx] at h1
    simp only [inv_inv] at h1
    rw [h1, hcore.mov]
  have he_mem : y⁻¹ * c * y ∈ autMovedInG E (x⁻¹ * zs * x) := by
    rw [hmov3, Equivariance.mem_conjBy]
    have e : y⁻¹⁻¹ * (y⁻¹ * c * y) * y⁻¹ = c := by group
    rw [e]
    exact Subgroup.mem_zpowers c
  have heL : y⁻¹ * c * y ∈ L := (moved_le_L h hF13 fr hz3) he_mem
  have heE : y⁻¹ * c * y ∈ E := Subgroup.map_subtype_le _ he_mem
  have hK₀J : kZero p E fr.r₀ ≤ J := kZero_le_pElementSubgroup fr.r₀ (le_centralizer_symm hR0)
  have hK₀'J : kZero p E fr.r₀' ≤ J := kZero_le_pElementSubgroup fr.r₀' (le_centralizer_symm hR0')
  have hVsc := Vof_solvable_coprime hp J
  have hcomm_e := claimA_frame hp fr h hF hZ hr hrq (Vof_conj p J) hVsc.1 hVsc.2 hK₀J hK₀'J
    (fr.kz₀ h hF13 hZ) (fr.kz₀' h hF13 hZ) (hEJ _ heE) (hEA ▸ heE) heL
    (Sec12Three.pow_eq_one_of_mem_E h heE) (fun x hx => (hRE x hx _ heE).symm) hu'V hu'c hu'R
  have h3 : (y⁻¹ * u * y) * (y⁻¹ * c * y) = (y⁻¹ * c * y) * (y⁻¹ * u * y) := hcomm_e.eq
  have h4 : u * c = c * u := by
    calc u * c = y * ((y⁻¹ * u * y) * (y⁻¹ * c * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * c * y) * (y⁻¹ * u * y)) * y⁻¹ := by rw [h3]
      _ = c * u := by group
  exact h4

end CFSG.RankThree.PartOne.K1327
