module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Std
public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Dec
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42S6
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81S0

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

namespace Am4

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}

structure StdData (b : G) (L : Subgroup G) (b₁ b₂ b₃ : G) (fL : K3 →* G) (g₀ : G) : Prop where
  inj : Function.Injective fL
  range : fL.range = L
  e0 : fL (nsElt 0) = b₃
  e1 : fL (nsElt 1) = b₂
  e2 : fL (nsElt 2) = b₁
  c1 : g₀ * b₁ * g₀⁻¹ = b
  c2 : g₀ * b₂ * g₀⁻¹ = b₁
  c3 : g₀ * b₃ * g₀⁻¹ = b₂
  c0 : g₀ * b * g₀⁻¹ = b₃

variable {fL : K3 →* G} {g₀ : G}

theorem StdData.conj_embS_mem_range (hD : Data b L B b₁ b₂ b₃ t₀)
    (hS : StdData b L b₁ b₂ b₃ fL g₀) (w : StatedSp 2 (ZMod 2)) (hw : w * w = 1) :
    ∃ z : StatedSp 2 (ZMod 2), g₀ * fL (embS w) * g₀⁻¹ = fL (embS' z) := by
  have hB := hD.h4.basis
  set y := fL (embS w) with hy
  have hyL : y ∈ L := hS.range ▸ ⟨embS w, rfl⟩
  have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hyL)
  have hyy : y * y = 1 := by rw [hy, ← map_mul, ← map_mul, hw, map_one, map_one]
  have hx2 : (g₀ * y * g₀⁻¹) * (g₀ * y * g₀⁻¹) = 1 := by
    calc (g₀ * y * g₀⁻¹) * (g₀ * y * g₀⁻¹) = g₀ * (y * y) * g₀⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  have hxb : g₀ * y * g₀⁻¹ ∈ Cen b := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hmem : embS w ∈ complSp (ZMod 2) (2 : Fin 3) := by
      rw [← range_embS]; exact ⟨w, rfl⟩
    have hc : embS w * nsElt 2 = nsElt 2 * embS w :=
      (commute_of_mem_longRootSp2_of_mem_complSp (k := 2) (x := nsElt 2)
        ⟨zThreeSL, rfl⟩ hmem).eq.symm
    have hc' : y * b₁ = b₁ * y := by rw [hy, ← hS.e2, ← map_mul, ← map_mul, hc]
    rw [← hS.c1]
    calc g₀ * y * g₀⁻¹ * (g₀ * b₁ * g₀⁻¹) = g₀ * (y * b₁) * g₀⁻¹ := by group
      _ = g₀ * (b₁ * y) * g₀⁻¹ := by rw [hc']
      _ = g₀ * b₁ * g₀⁻¹ * (g₀ * y * g₀⁻¹) := by group
  have hxL : g₀ * y * g₀⁻¹ ∈ L := hB.mem_of_pow_two hxb (k := 1) (by rw [pow_one, sq]; exact hx2)
  obtain ⟨x', hx'⟩ : ∃ x', fL x' = g₀ * y * g₀⁻¹ := by
    have := hxL; rw [← hS.range] at this; exact this
  have hx'2 : x' * x' = 1 := hS.inj (by rw [map_mul, hx', hx2, map_one])
  have hx3 : g₀ * y * g₀⁻¹ * b₃ = b₃ * (g₀ * y * g₀⁻¹) := by
    rw [← hS.c0]
    calc g₀ * y * g₀⁻¹ * (g₀ * b * g₀⁻¹) = g₀ * (y * b) * g₀⁻¹ := by group
      _ = g₀ * (b * y) * g₀⁻¹ := by rw [hyb]
      _ = g₀ * b * g₀⁻¹ * (g₀ * y * g₀⁻¹) := by group
  have hx'c : x' * nsElt 0 = nsElt 0 * x' :=
    hS.inj (by rw [map_mul, map_mul, hx', hS.e0]; exact hx3)
  have hcomp : x' ∈ complSp (ZMod 2) (0 : Fin 3) :=
    mem_complSp_of_two_pow (0 : Fin 3) hx'c (m := 1) (by rw [pow_one, sq]; exact hx'2)
  rw [← range_embS'] at hcomp
  obtain ⟨z, hz⟩ := hcomp
  exact ⟨z, by rw [hz, hx']⟩

theorem StdData.exists_embS' (hD : Data b L B b₁ b₂ b₃ t₀)
    (hS : StdData b L b₁ b₂ b₃ fL g₀) (z : StatedSp 2 (ZMod 2)) :
    ∃ z' : StatedSp 2 (ZMod 2), g₀ * fL (embS z) * g₀⁻¹ = fL (embS' z') := by
  let F₁ : StatedSp 2 (ZMod 2) →* G := (MulAut.conj g₀).toMonoidHom.comp (fL.comp embS)
  let F₂ : StatedSp 2 (ZMod 2) →* G := fL.comp embS'
  have key : Subgroup.closure {w : StatedSp 2 (ZMod 2) | w * w = 1} ≤ F₂.range.comap F₁ := by
    rw [Subgroup.closure_le]
    intro w hw
    obtain ⟨z', hz'⟩ := hS.conj_embS_mem_range hD w hw
    exact ⟨z', hz'.symm⟩
  have hz : z ∈ Subgroup.closure {w : StatedSp 2 (ZMod 2) | w * w = 1} := by
    rw [closure_sq_eq_top_Sp4]; exact Subgroup.mem_top z
  obtain ⟨z', hz'⟩ := key hz
  exact ⟨z', hz'.symm⟩

theorem StdData.exists_inner (hD : Data b L B b₁ b₂ b₃ t₀)
    (hS : StdData b L b₁ b₂ b₃ fL g₀) :
    ∃ j : StatedSp 2 (ZMod 2),
      (∀ z, g₀ * fL (embS z) * g₀⁻¹ = fL (embS' (j * z * j⁻¹))) ∧
      j * nsElt 0 * j⁻¹ = nsElt 0 ∧ j * nsElt 1 * j⁻¹ = nsElt 1 := by
  let F₁ : StatedSp 2 (ZMod 2) →* G := (MulAut.conj g₀).toMonoidHom.comp (fL.comp embS)
  let F₂ : StatedSp 2 (ZMod 2) →* G := fL.comp embS'
  have hF₁inj : Function.Injective F₁ :=
    (MulAut.conj g₀).injective.comp (hS.inj.comp embS_injective)
  have hF₂inj : Function.Injective F₂ := hS.inj.comp embS'_injective
  have hF₁ : ∀ z, F₁ z = g₀ * fL (embS z) * g₀⁻¹ := fun z => rfl
  have hle : F₁.range ≤ F₂.range := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ := hS.exists_embS' hD z
    show ∃ y, fL (embS' y) = g₀ * fL (embS z) * g₀⁻¹
    exact ⟨z', hz'.symm⟩
  have hcard : Nat.card ↥F₂.range ≤ Nat.card ↥F₁.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hF₁inj).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hF₂inj).toEquiv]
  have hrange : F₁.range = F₂.range := Subgroup.eq_of_le_of_card_ge hle hcard
  let α : StatedSp 2 (ZMod 2) ≃* StatedSp 2 (ZMod 2) :=
    ((MonoidHom.ofInjective hF₁inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hF₂inj).symm
  have hα : ∀ z, F₂ (α z) = F₁ z := by
    intro z
    have := (MonoidHom.ofInjective hF₂inj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hF₁inj z))
    exact congrArg Subtype.val this
  have hn0 : α (nsElt 0) = nsElt 0 := by
    apply hF₂inj
    rw [hα, hF₁]
    have h1 : embS (nsElt (K := ZMod 2) (n := 2) 0) = nsElt (K := ZMod 2) (n := 3) 0 :=
      embS_nsElt 0
    have h2 : embS' (nsElt (K := ZMod 2) (n := 2) 0) = nsElt (K := ZMod 2) (n := 3) 1 :=
      embS'_nsElt 0
    show g₀ * fL (embS (nsElt 0)) * g₀⁻¹ = fL (embS' (nsElt 0))
    rw [h1, h2, hS.e0, hS.e1, hS.c3]
  have hn1 : α (nsElt 1) = nsElt 1 := by
    apply hF₂inj
    rw [hα, hF₁]
    have h1 : embS (nsElt (K := ZMod 2) (n := 2) 1) = nsElt (K := ZMod 2) (n := 3) 1 :=
      embS_nsElt 1
    have h2 : embS' (nsElt (K := ZMod 2) (n := 2) 1) = nsElt (K := ZMod 2) (n := 3) 2 :=
      embS'_nsElt 1
    show g₀ * fL (embS (nsElt 1)) * g₀⁻¹ = fL (embS' (nsElt 1))
    rw [h1, h2, hS.e1, hS.e2, hS.c2]
  have hfix : ∀ e ∈ nsTorusSp (ZMod 2) (0 : Fin 2) ⊔ nsTorusSp (ZMod 2) (1 : Fin 2),
      α e = e := by
    have hle' : nsTorusSp (ZMod 2) (0 : Fin 2) ⊔ nsTorusSp (ZMod 2) (1 : Fin 2) ≤
        MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) := by
      refine sup_le ?_ ?_
      · rw [nsTorusSp, Subgroup.zpowers_le]; exact hn0
      · rw [nsTorusSp, Subgroup.zpowers_le]; exact hn1
    intro e he
    exact hle' he
  obtain ⟨φ⟩ := nonempty_sp4_mulEquiv_perm
  obtain ⟨j, hj⟩ := mulAut_inner_of_fix_card_nine φ _ card_nsTorus_pair α hfix
  refine ⟨j, fun z => ?_, ?_, ?_⟩
  · calc g₀ * fL (embS z) * g₀⁻¹ = F₁ z := rfl
      _ = F₂ (α z) := (hα z).symm
      _ = F₂ (j * z * j⁻¹) := by rw [hj z]
      _ = fL (embS' (j * z * j⁻¹)) := rfl
  · rw [← hj, hn0]
  · rw [← hj, hn1]

theorem StdData.exists_g_S (hD : Data b L B b₁ b₂ b₃ t₀)
    (hS : StdData b L b₁ b₂ b₃ fL g₀) :
    ∃ g : G, g * b₁ * g⁻¹ = b ∧ g * b₂ * g⁻¹ = b₁ ∧ g * b₃ * g⁻¹ = b₂ ∧ g * b * g⁻¹ = b₃ ∧
      ∀ z, g * fL (embS z) * g⁻¹ = fL (embS' z) := by
  have hB := hD.h4.basis
  obtain ⟨j, hj, hj0, hj1⟩ := hS.exists_inner hD
  set c := fL (embS j⁻¹) with hc
  have hcL : c ∈ L := hS.range ▸ ⟨embS j⁻¹, rfl⟩
  have hconj : ∀ x : G, c * x = x * c → (g₀ * c) * x * (g₀ * c)⁻¹ = g₀ * x * g₀⁻¹ := by
    intro x hx
    calc (g₀ * c) * x * (g₀ * c)⁻¹ = g₀ * (c * x) * c⁻¹ * g₀⁻¹ := by group
      _ = g₀ * (x * c) * c⁻¹ * g₀⁻¹ := by rw [hx]
      _ = g₀ * x * g₀⁻¹ := by group
  have hcomm : ∀ n : StatedSp 2 (ZMod 2), j * n * j⁻¹ = n → j⁻¹ * n = n * j⁻¹ := by
    intro n hn
    have h1 : j * n = n * j := by
      calc j * n = (j * n * j⁻¹) * j := by group
        _ = n * j := by rw [hn]
    calc j⁻¹ * n = j⁻¹ * (n * j) * j⁻¹ := by group
      _ = j⁻¹ * (j * n) * j⁻¹ := by rw [h1]
      _ = n * j⁻¹ := by group
  have h0 : embS (nsElt (K := ZMod 2) (n := 2) 0) = nsElt (K := ZMod 2) (n := 3) 0 :=
    embS_nsElt 0
  have h1 : embS (nsElt (K := ZMod 2) (n := 2) 1) = nsElt (K := ZMod 2) (n := 3) 1 :=
    embS_nsElt 1
  have hmem : embS j⁻¹ ∈ complSp (ZMod 2) (2 : Fin 3) := by
    rw [← range_embS]; exact ⟨j⁻¹, rfl⟩
  have hc2 : c * b₁ = b₁ * c := by
    have : embS j⁻¹ * nsElt 2 = nsElt 2 * embS j⁻¹ :=
      (commute_of_mem_longRootSp2_of_mem_complSp (k := 2) (x := nsElt 2) ⟨zThreeSL, rfl⟩
        hmem).eq.symm
    rw [hc, ← hS.e2, ← map_mul, ← map_mul, this]
  have hc1 : c * b₂ = b₂ * c := by
    have := hcomm _ hj1
    rw [hc, ← hS.e1, ← h1, ← map_mul, ← map_mul, ← map_mul, ← map_mul, this]
  have hc0 : c * b₃ = b₃ * c := by
    have := hcomm _ hj0
    rw [hc, ← hS.e0, ← h0, ← map_mul, ← map_mul, ← map_mul, ← map_mul, this]
  have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hcL)
  refine ⟨g₀ * c, ?_, ?_, ?_, ?_, fun z => ?_⟩
  · rw [hconj _ hc2, hS.c1]
  · rw [hconj _ hc1, hS.c2]
  · rw [hconj _ hc0, hS.c3]
  · rw [hconj _ hcb, hS.c0]
  · have e : c * fL (embS z) * c⁻¹ = fL (embS (j⁻¹ * z * j)) := by
      calc c * fL (embS z) * c⁻¹ = fL (embS j⁻¹ * embS z * (embS j⁻¹)⁻¹) := by
            rw [map_mul fL, map_mul fL, map_inv fL]
        _ = fL (embS (j⁻¹ * z * j)) := by
            rw [← map_inv embS, ← map_mul embS, ← map_mul embS, inv_inv]
    calc g₀ * c * fL (embS z) * (g₀ * c)⁻¹ = g₀ * (c * fL (embS z) * c⁻¹) * g₀⁻¹ := by group
      _ = g₀ * fL (embS (j⁻¹ * z * j)) * g₀⁻¹ := by rw [e]
      _ = fL (embS' (j * (j⁻¹ * z * j) * j⁻¹)) := hj _
      _ = fL (embS' z) := by rw [show j * (j⁻¹ * z * j) * j⁻¹ = z by group]

theorem exists_pow_mul_of_mem (hB : FF81Basis b L B b₁ b₂ b₃) {u : G} (hu : u ∈ B) :
    ∃ i : ℕ, ∃ v ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), u = b ^ i * v := by
  have hBc := hB.mono.2.1
  have hcomm := comm_of_isElemAb hB.mono.1
  obtain ⟨hb, hb1, hb2, hb3⟩ := hB.mem
  have hB1 : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (rfl | rfl | rfl)
    exacts [hb1, hb2, hb3]
  have hb3pow : b ^ 3 = 1 := pow_three_eq_one_of_isElemAb hB.mono.1 hb
  rw [hBc] at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨0, x, Subgroup.subset_closure (by simp), by simp⟩
    · exact ⟨0, x, Subgroup.subset_closure (by simp), by simp⟩
    · exact ⟨0, x, Subgroup.subset_closure (by simp), by simp⟩
  | one => exact ⟨0, 1, Subgroup.one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, v, hv, rfl⟩ := hx
    obtain ⟨j, w, hw, rfl⟩ := hy
    refine ⟨i + j, v * w, Subgroup.mul_mem _ hv hw, ?_⟩
    have hvb : v * b ^ j = b ^ j * v :=
      (Commute.pow_right (hcomm v (hB1 hv) b hb) j).eq
    calc b ^ i * v * (b ^ j * w) = b ^ i * (v * b ^ j) * w := by group
      _ = b ^ i * (b ^ j * v) * w := by rw [hvb]
      _ = b ^ (i + j) * (v * w) := by rw [pow_add]; group
  | inv x _ hx =>
    obtain ⟨i, v, hv, rfl⟩ := hx
    refine ⟨2 * i, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
    have hvb : v⁻¹ * b ^ (2 * i) = b ^ (2 * i) * v⁻¹ :=
      (Commute.pow_right (hcomm v⁻¹ (hB1 (Subgroup.inv_mem _ hv)) b hb) (2 * i)).eq
    have hbi : (b ^ i)⁻¹ = b ^ (2 * i) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hb3pow, one_pow]
    rw [mul_inv_rev, hbi, hvb]

theorem mem_zpowers_of_inverted (hB : FF81Basis b L B b₁ b₂ b₃) {t₀ : G} (ht₀L : t₀ ∈ CenS L)
    (htb : t₀ * b * t₀⁻¹ = b⁻¹) {u : G} (huB : u ∈ B) (hu : t₀ * u * t₀⁻¹ = u⁻¹) :
    u ∈ Subgroup.zpowers b := by
  obtain ⟨i, v, hv, rfl⟩ := exists_pow_mul_of_mem hB huB
  have hcomm := comm_of_isElemAb hB.mono.1
  obtain ⟨hb, hb1, hb2, hb3⟩ := hB.mem
  have hvB : v ∈ B := by
    refine ((Subgroup.closure_le B).mpr ?_) hv
    rintro y (rfl | rfl | rfl)
    exacts [hb1, hb2, hb3]
  have hvL : v ∈ L := by
    refine ((Subgroup.closure_le L).mpr ?_) hv
    rintro y (rfl | rfl | rfl)
    exacts [hB.hb₁, hB.hb₂, hB.hb₃]
  have htv : t₀ * v * t₀⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp ht₀L v hvL
    rw [← this]; group
  have hcp : t₀ * b ^ i * t₀⁻¹ = (b⁻¹) ^ i := by
    have := map_pow (MulAut.conj t₀) b i
    simpa [MulAut.conj_apply, htb] using this
  have h1 : t₀ * (b ^ i * v) * t₀⁻¹ = (b⁻¹) ^ i * v := by
    calc t₀ * (b ^ i * v) * t₀⁻¹ = (t₀ * b ^ i * t₀⁻¹) * (t₀ * v * t₀⁻¹) := by group
      _ = (b⁻¹) ^ i * v := by rw [hcp, htv]
  have h2 : (b⁻¹) ^ i * v = v⁻¹ * (b⁻¹) ^ i := by
    rw [← h1, hu, mul_inv_rev, inv_pow]
  have hvb : v⁻¹ * (b⁻¹) ^ i = (b⁻¹) ^ i * v⁻¹ :=
    (Commute.pow_right (hcomm v⁻¹ (B.inv_mem hvB) b⁻¹ (B.inv_mem hb)) i).eq
  have h2' : (b⁻¹) ^ i * v = (b⁻¹) ^ i * v⁻¹ := by rw [h2, hvb]
  have hvv : v = v⁻¹ := mul_left_cancel h2'
  have h3 : v * v = 1 := by
    calc v * v = v * v⁻¹ := by rw [← hvv]
      _ = 1 := mul_inv_cancel v
  have h4 : v = 1 := by
    calc v = v * (v * v) := by rw [h3, mul_one]
      _ = v ^ 3 := (pow_three v).symm
      _ = 1 := pow_three_eq_one_of_isElemAb hB.mono.1 hvB
  rw [h4, mul_one]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) i

structure GData (b : G) (b₁ b₂ b₃ t₀ : G) (fL : K3 →* G) (g : G) : Prop where
  c1 : g * b₁ * g⁻¹ = b
  c2 : g * b₂ * g⁻¹ = b₁
  c3 : g * b₃ * g⁻¹ = b₂
  c0 : g * b * g⁻¹ = b₃
  S : ∀ z, g * fL (embS z) * g⁻¹ = fL (embS' z)
  tM : g * fL tM * g⁻¹ = t₀

theorem StdData.exists_g (hD : Data b L B b₁ b₂ b₃ t₀) (hS : StdData b L b₁ b₂ b₃ fL g₀) :
    ∃ g : G, GData b b₁ b₂ b₃ t₀ fL g := by
  have hB := hD.h4.basis
  obtain ⟨g, c1, c2, c3, c0, hSg⟩ := hS.exists_g_S hD
  obtain ⟨hb, hb1, hb2, hb3⟩ := hB.mem
  have ht2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [hD.h4.ht₀, sq] at this
  have ht0inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht2
  have htb : t₀ * b * t₀⁻¹ = b⁻¹ := hD.h4.ht₀b
  have htL : ∀ l ∈ L, l * t₀ = t₀ * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hD.h4.ht₀L l hl
  have hLb : ∀ l ∈ L, l * b = b * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hl)
  have hftM : fL tM ∈ L := hS.range ▸ ⟨tM, rfl⟩
  set s := g * fL tM * g⁻¹ with hs
  have hs2 : s * s = 1 := by
    have : fL tM * fL tM = 1 := by rw [← map_mul, tM_mul_self, map_one]
    calc s * s = g * (fL tM * fL tM) * g⁻¹ := by rw [hs]; group
      _ = 1 := by rw [this]; group
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have g1 : g⁻¹ * b * g = b₁ := by rw [← c1]; group
  have g2 : g⁻¹ * b₁ * g = b₂ := by rw [← c2]; group
  have g3 : g⁻¹ * b₂ * g = b₃ := by rw [← c3]; group
  have g0 : g⁻¹ * b₃ * g = b := by rw [← c0]; group
  have hcomm_nsElt : ∀ k : Fin 3, k ≠ 2 → tM * nsElt (K := ZMod 2) (n := 3) k =
      nsElt k * tM := fun k hk =>
    (commute_longBlock (j := (2 : Fin 3)) (k := k) (Ne.symm hk) (sl2Upper 1) zThreeSL).eq
  have hcomm_b₂ : fL tM * b₂ = b₂ * fL tM := by
    rw [← hS.e1, ← map_mul, ← map_mul, hcomm_nsElt 1 (by decide)]
  have hcomm_b₃ : fL tM * b₃ = b₃ * fL tM := by
    rw [← hS.e0, ← map_mul, ← map_mul, hcomm_nsElt 0 (by decide)]
  have hcomm_b : fL tM * b = b * fL tM := hLb _ hftM
  have hinv_b₁ : fL tM * b₁ * (fL tM)⁻¹ = b₁⁻¹ := by
    rw [← hS.e2, ← map_mul fL, ← map_inv fL, ← map_mul fL, tM_conj_nsElt, map_inv fL]
  have hsb : s * b * s⁻¹ = b⁻¹ := by
    calc s * b * s⁻¹ = g * (fL tM * (g⁻¹ * b * g) * (fL tM)⁻¹) * g⁻¹ := by rw [hs]; group
      _ = g * b₁⁻¹ * g⁻¹ := by rw [g1, hinv_b₁]
      _ = b⁻¹ := by rw [show g * b₁⁻¹ * g⁻¹ = (g * b₁ * g⁻¹)⁻¹ by group, c1]
  have hsb₁ : s * b₁ * s⁻¹ = b₁ := by
    calc s * b₁ * s⁻¹ = g * (fL tM * (g⁻¹ * b₁ * g) * (fL tM)⁻¹) * g⁻¹ := by rw [hs]; group
      _ = g * b₂ * g⁻¹ := by rw [g2, hcomm_b₂]; group
      _ = b₁ := c2
  have hsb₂ : s * b₂ * s⁻¹ = b₂ := by
    calc s * b₂ * s⁻¹ = g * (fL tM * (g⁻¹ * b₂ * g) * (fL tM)⁻¹) * g⁻¹ := by rw [hs]; group
      _ = g * b₃ * g⁻¹ := by rw [g3, hcomm_b₃]; group
      _ = b₂ := c3
  have hsb₃ : s * b₃ * s⁻¹ = b₃ := by
    calc s * b₃ * s⁻¹ = g * (fL tM * (g⁻¹ * b₃ * g) * (fL tM)⁻¹) * g⁻¹ := by rw [hs]; group
      _ = g * b * g⁻¹ := by rw [g0, hcomm_b]; group
      _ = b₃ := c0
  set u := t₀ * s with hu
  have hu0 : u * b * u⁻¹ = b := by
    calc u * b * u⁻¹ = t₀ * (s * b * s⁻¹) * t₀⁻¹ := by rw [hu]; group
      _ = (t₀ * b * t₀⁻¹)⁻¹ := by rw [hsb]; group
      _ = b := by rw [htb, inv_inv]
  have hui : ∀ x ∈ L, s * x * s⁻¹ = x → u * x * u⁻¹ = x := fun x hx hsx =>
    calc u * x * u⁻¹ = t₀ * (s * x * s⁻¹) * t₀⁻¹ := by rw [hu]; group
      _ = t₀ * x * t₀⁻¹ := by rw [hsx]
      _ = x := by rw [← htL x hx]; group
  have huB : u ∈ B := by
    rw [← hB.cenS_eq hD.hO3]
    exact hB.mem_cenS hu0 (hui b₁ hB.hb₁ hsb₁) (hui b₂ hB.hb₂ hsb₂) (hui b₃ hB.hb₃ hsb₃)
  have hu_inv : t₀ * u * t₀⁻¹ = u⁻¹ := by
    have e1 : t₀ * u * t₀⁻¹ = s * t₀ := by
      rw [hu, ht0inv]
      calc t₀ * (t₀ * s) * t₀ = (t₀ * t₀) * s * t₀ := by group
        _ = s * t₀ := by rw [ht2, one_mul]
    have e2 : u⁻¹ = s * t₀ := by rw [hu, mul_inv_rev, hsinv, ht0inv]
    rw [e1, e2]
  have hu_mem : u ∈ Subgroup.zpowers b :=
    mem_zpowers_of_inverted hB hD.h4.ht₀L htb huB hu_inv
  have hucomm : ∀ l ∈ L, l * u = u * l := by
    intro l hl
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
    rw [← hk]
    exact (Commute.zpow_right (hLb l hl : Commute l b) k).eq
  have hcommB := comm_of_isElemAb hB.mono.1
  have hu3 : u ^ 3 = 1 := pow_three_eq_one_of_isElemAb hB.mono.1 huB
  have hconjB : ∀ x ∈ B, u * u * x * (u * u)⁻¹ = x := by
    intro x hx
    have h : u * u * x = x * (u * u) := by
      rw [mul_assoc, hcommB u huB x hx, ← mul_assoc, hcommB u huB x hx, mul_assoc]
    rw [h]; group
  have hconjL : ∀ x ∈ L, u * u * x * (u * u)⁻¹ = x := by
    intro x hx
    have h : u * u * x = x * (u * u) := by
      rw [mul_assoc, (hucomm x hx).symm, ← mul_assoc, (hucomm x hx).symm, mul_assoc]
    rw [h]; group
  have hut : u * t₀ = t₀ * u⁻¹ := by
    have h : t₀ * u⁻¹ * t₀⁻¹ = u := by
      calc t₀ * u⁻¹ * t₀⁻¹ = (t₀ * u * t₀⁻¹)⁻¹ := by group
        _ = u := by rw [hu_inv, inv_inv]
    calc u * t₀ = (t₀ * u⁻¹ * t₀⁻¹) * t₀ := by rw [h]
      _ = t₀ * u⁻¹ := by group
  have hsu : s = t₀ * u := by rw [hu, ← mul_assoc, ht2, one_mul]
  refine ⟨(u * u) * g, ?_, ?_, ?_, ?_, fun z => ?_, ?_⟩
  · calc (u * u * g) * b₁ * (u * u * g)⁻¹ = (u * u) * (g * b₁ * g⁻¹) * (u * u)⁻¹ := by group
      _ = b := by rw [c1]; exact hconjB b hb
  · calc (u * u * g) * b₂ * (u * u * g)⁻¹ = (u * u) * (g * b₂ * g⁻¹) * (u * u)⁻¹ := by group
      _ = b₁ := by rw [c2]; exact hconjB b₁ hb1
  · calc (u * u * g) * b₃ * (u * u * g)⁻¹ = (u * u) * (g * b₃ * g⁻¹) * (u * u)⁻¹ := by group
      _ = b₂ := by rw [c3]; exact hconjB b₂ hb2
  · calc (u * u * g) * b * (u * u * g)⁻¹ = (u * u) * (g * b * g⁻¹) * (u * u)⁻¹ := by group
      _ = b₃ := by rw [c0]; exact hconjB b₃ hb3
  · have hmem : fL (embS' z) ∈ L := hS.range ▸ ⟨embS' z, rfl⟩
    calc (u * u * g) * fL (embS z) * (u * u * g)⁻¹ =
        (u * u) * (g * fL (embS z) * g⁻¹) * (u * u)⁻¹ := by group
      _ = fL (embS' z) := by rw [hSg z]; exact hconjL _ hmem
  · calc (u * u * g) * fL tM * (u * u * g)⁻¹ = (u * u) * s * (u * u)⁻¹ := by rw [hs]; group
      _ = t₀ := by
        rw [hsu]
        have h1 : u * u * t₀ = t₀ * u⁻¹ * u⁻¹ := by
          calc u * u * t₀ = u * (u * t₀) := by group
            _ = u * (t₀ * u⁻¹) := by rw [hut]
            _ = (u * t₀) * u⁻¹ := by group
            _ = t₀ * u⁻¹ * u⁻¹ := by rw [hut]
        calc u * u * (t₀ * u) * (u * u)⁻¹ = (u * u * t₀) * u * (u * u)⁻¹ := by group
          _ = t₀ * u⁻¹ * u⁻¹ * u * (u * u)⁻¹ := by rw [h1]
          _ = t₀ * (u ^ 3)⁻¹ := by group
          _ = t₀ := by rw [hu3, inv_one, mul_one]

end Am4

end CFSG.RankThree.PartTwo.Sec21.FF81
