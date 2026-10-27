module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Nodes
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGForkF1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggAutomizer_fix_of_range_fix {G : Type} [Group G] {Bs : Subgroup G}
    {Λ : Type} {φ : Λ → MulAut ↥Bs} {Y : Subgroup G}
    (hclos : ggAutomizer Y Bs = Subgroup.closure (Set.range φ))
    {b : ↥Bs} (hb : ∀ i, φ i b = b) :
    ∀ ψ ∈ ggAutomizer Y Bs, ψ b = b := by
  intro ψ hψ
  have hψ' : ψ ∈ Subgroup.closure (Set.range φ) := by rwa [hclos] at hψ
  have hle : Subgroup.closure (Set.range φ) ≤ MulAction.stabilizer (MulAut ↥Bs) b := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (by simpa using hb i)
  simpa using hle hψ'

private theorem ggLE3_z_ne_zero {G : Type} [Group G] {V : Type} [AddCommGroup V]
    {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V) {w : G} (hwB : w ∈ Bs) (hw1 : w ≠ 1) :
    ι (Additive.ofMul ⟨w, hwB⟩) ≠ 0 := by
  intro hz0
  have h : (⟨w, hwB⟩ : ↥Bs) = 1 :=
    Additive.ofMul.injective (ι.injective (by simpa using hz0))
  exact hw1 (by simpa using Subtype.ext_iff.mp h)

private theorem ggLE3_kill {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs Y : Subgroup G} {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hC : GGIntCartan M C) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hclos : ggAutomizer Y Bs = Subgroup.closure (Set.range φ))
    {w : G} (hwB : w ∈ Bs) (hwfix : ∀ ψ ∈ ggAutomizer Y Bs, ψ ⟨w, hwB⟩ = ⟨w, hwB⟩) :
    ∀ i, α i (ι (Additive.ofMul ⟨w, hwB⟩)) = 0 := by
  intro i
  have hmem : φ i ∈ ggAutomizer Y Bs := by
    rw [hclos]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hfixi : φ i (⟨w, hwB⟩ : ↥Bs) = ⟨w, hwB⟩ := hwfix (φ i) hmem
  have hlinz : ggLin (p := p) ι (φ i) (ι (Additive.ofMul ⟨w, hwB⟩)) =
      ι (Additive.ofMul ⟨w, hwB⟩) := (ggLin_fix_iff ι (φ i) ⟨w, hwB⟩).mp hfixi
  have h1 : ι (Additive.ofMul ⟨w, hwB⟩) - α i (ι (Additive.ofMul ⟨w, hwB⟩)) • h i =
      ι (Additive.ofMul ⟨w, hwB⟩) := by
    rw [← hlin i (ι (Additive.ofMul ⟨w, hwB⟩)), hlinz]
  have h2 : α i (ι (Additive.ofMul ⟨w, hwB⟩)) • h i = 0 := sub_eq_self.mp h1
  have h3 : α i (ι (Additive.ofMul ⟨w, hwB⟩)) • α i (h i) = 0 := by
    have := congrArg (α i) h2
    simpa using this
  rw [hpair i i, hC.1 i] at h3
  have h4 : α i (ι (Additive.ofMul ⟨w, hwB⟩)) * (2 : ZMod p) = 0 := by
    simpa [smul_eq_mul] using h3
  rcases mul_eq_zero.mp h4 with hzero | htwo
  · exact hzero
  · exact absurd htwo (zmod_two_ne_zero hp2)

private theorem ggNatCard_eq_pow_finrank {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) :
    Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  calc
    Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
    _ = Nat.card V := Nat.card_congr ι.toEquiv
    _ = p ^ Module.finrank (ZMod p) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

private theorem ggLE3_card_le_aux {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs Y : Subgroup G} {N : ℕ}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hcard : Fintype.card Λ = N) (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hclos : ggAutomizer Y Bs = Subgroup.closure (Set.range φ))
    {w : G} (hwB : w ∈ Bs) (hw1 : w ≠ 1)
    (hwfix : ∀ ψ ∈ ggAutomizer Y Bs, ψ ⟨w, hwB⟩ = ⟨w, hwB⟩) :
    N ≤ Module.finrank (ZMod p) V := by
  have hz : ι (Additive.ofMul ⟨w, hwB⟩) ≠ 0 := ggLE3_z_ne_zero ι hwB hw1
  have hzα : ∀ i, α i (ι (Additive.ofMul ⟨w, hwB⟩)) = 0 :=
    ggLE3_kill (p := p) hp2 ι φ h α hC hlin hpair hclos hwB hwfix
  have h := ggPZ_card_le_finrank hp2 hW hC h α hpair hz hzα
  rwa [hcard] at h

theorem ggLE3_count {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hαh : ∀ i j, α i (h j) = (C i j : ZMod p))
    {z : V} (hz : z ≠ 0) (hzα : ∀ i, α i z = 0) {N : ℕ} (hcard : Fintype.card Λ = N)
    (hpN : p ∣ N) (hdim : Module.finrank (ZMod p) V ≤ N) :
    p = 3 ∧ N = 6 ∧ Module.finrank (ZMod p) V = 6 := by
  classical
  have hp : p.Prime := Fact.out
  have hdimΛ : Module.finrank (ZMod p) V ≤ Fintype.card Λ := by rwa [hcard]
  rcases ggIntCartan_A_or_E6_of_finrank_le hM hC hp2 h α hαh hz hzα hdimΛ with
    ⟨n, e, _, hpdvd, _⟩ | ⟨hp3, e, _⟩
  · exfalso
    have hcardn : Fintype.card Λ = n := by
      rw [← Fintype.card_fin n, Fintype.card_congr e]
    have hnN : n = N := by omega
    have hpdvdN1 : p ∣ N + 1 := by simpa [hnN] using hpdvd
    have hpdvd1 : p ∣ 1 := (Nat.dvd_add_iff_right hpN).2 hpdvdN1
    exact absurd hpdvd1 hp.not_dvd_one
  · have hcard6 : Fintype.card Λ = 6 := by
      rw [← Fintype.card_fin 6, Fintype.card_congr e]
    have hN6 : N = 6 := by omega
    have hdim6 : Module.finrank (ZMod p) V = 6 := by
      have hle := ggPZ_card_le_finrank hp2 hM hC h α hαh hz hzα
      rw [hcard6] at hle
      omega
    exact ⟨hp3, hN6, hdim6⟩

theorem ggLE3_card_le_of_fix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {N : ℕ} (hN : 1 ≤ N) (hXd : GGResXDatumA p Bs X (N - 1)) {w : G}
    (hw : w ^ p = 1)
    (hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer X Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers w) :
    Nat.card ↥Bs ≤ p ^ N := by
  classical
  obtain ⟨Λ, hΛfin, hΛdec, M, C, V, hVadd, hVmod, ι, φ, h, α, e, _, hW, hC,
    hlin, _, hpair, _, hclos⟩ := hXd
  letI : Fintype Λ := hΛfin
  letI : DecidableEq Λ := hΛdec
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  have hfix' : ∀ b : ↥Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers w := by
    intro b hb
    exact hfix b (ggAutomizer_fix_of_range_fix hclos hb)
  have hdim : Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 :=
    ggFinrank_le_of_fix_le (x := w) hw ι φ h α hlin hfix'
  have hcardΛ : Fintype.card Λ = N - 1 := by
    rw [← Fintype.card_fin (N - 1), Fintype.card_congr e]
  have hdimN : Module.finrank (ZMod p) V ≤ N := by
    rw [hcardΛ] at hdim
    omega
  rw [ggNatCard_eq_pow_finrank (p := p) ι]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdimN

theorem ggLE3_three_card {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X J Y : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N) (hpN : p ∣ N)
    (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hY : GGResLeviSideDatumLE3 p Bs Y J) (hY2 : ¬ GGResTwoNodeSideDatum p Bs Y J)
    {w : G} (hwB : w ∈ Bs) (hw1 : w ≠ 1)
    (hwfix : ∀ ψ ∈ ggAutomizer Y Bs, ψ ⟨w, hwB⟩ = ⟨w, hwB⟩) :
    (p = 3 ∧ N = 6 ∧ Nat.card ↥Bs = 3 ^ 6) ∨ p ^ (N + 1) ≤ Nat.card ↥Bs := by
  classical
  obtain ⟨Λ, hΛfin, hΛdec, M, C, V, hVadd, hVmod, ι, φ, h, α, hcard, hW, hC,
    hlin, hpair, hclos⟩ := ggLE3_three_nodes hp2 hBs hN5 hXd hXs hY hY2
  letI : Fintype Λ := hΛfin
  letI : DecidableEq Λ := hΛdec
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hNle : N ≤ Module.finrank (ZMod p) V :=
    ggLE3_card_le_aux (p := p) hp2 ι φ h α hcard hW hC hlin hpair hclos hwB hw1 hwfix
  by_cases hdim : Module.finrank (ZMod p) V ≤ N
  · left
    have hz : ι (Additive.ofMul ⟨w, hwB⟩) ≠ 0 := ggLE3_z_ne_zero ι hwB hw1
    have hzα : ∀ i, α i (ι (Additive.ofMul ⟨w, hwB⟩)) = 0 :=
      ggLE3_kill (p := p) hp2 ι φ h α hC hlin hpair hclos hwB hwfix
    obtain ⟨hp3, hN6, hdim6⟩ := ggLE3_count (p := p) hp2 hW hC h α hpair hz hzα hcard hpN hdim
    exact ⟨hp3, hN6, by rw [ggNatCard_eq_pow_finrank (p := p) ι, hdim6, hp3]⟩
  · right
    have hge : N + 1 ≤ Module.finrank (ZMod p) V := by omega
    rw [ggNatCard_eq_pow_finrank (p := p) ι]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hge

theorem ggLE3_three_card_fixY {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs X J Y : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hpN : p ∣ N) (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hY : GGResLeviSideDatumLE3 p Bs Y J) (hY2 : ¬ GGResTwoNodeSideDatum p Bs Y J)
    {w : G} (hwB : w ∈ Bs) (hw1 : w ≠ 1) (hwp : w ^ p = 1)
    (hwfix : ∀ ψ ∈ ggAutomizer Y Bs, ψ ⟨w, hwB⟩ = ⟨w, hwB⟩)
    (hfixY : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer Y Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers w) :
    (p = 3 ∧ N = 6 ∧ Nat.card ↥Bs = 3 ^ 6) ∨ Nat.card ↥Bs = p ^ (N + 1) := by
  classical
  obtain ⟨Λ, hΛfin, hΛdec, M, C, V, hVadd, hVmod, ι, φ, h, α, hcard, hW, hC,
    hlin, hpair, hclos⟩ := ggLE3_three_nodes hp2 hBs hN5 hXd hXs hY hY2
  letI : Fintype Λ := hΛfin
  letI : DecidableEq Λ := hΛdec
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hNle : N ≤ Module.finrank (ZMod p) V :=
    ggLE3_card_le_aux (p := p) hp2 ι φ h α hcard hW hC hlin hpair hclos hwB hw1 hwfix
  have hfix' : ∀ b : ↥Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers w := by
    intro b hb
    exact hfixY b (ggAutomizer_fix_of_range_fix hclos hb)
  have hdimN1 : Module.finrank (ZMod p) V ≤ N + 1 := by
    have h := ggFinrank_le_of_fix_le (x := w) hwp ι φ h α hlin hfix'
    rwa [hcard] at h
  have hcases : Module.finrank (ZMod p) V = N ∨ Module.finrank (ZMod p) V = N + 1 := by
    omega
  rcases hcases with hdim | hdim
  · left
    have hz : ι (Additive.ofMul ⟨w, hwB⟩) ≠ 0 := ggLE3_z_ne_zero ι hwB hw1
    have hzα : ∀ i, α i (ι (Additive.ofMul ⟨w, hwB⟩)) = 0 :=
      ggLE3_kill (p := p) hp2 ι φ h α hC hlin hpair hclos hwB hwfix
    obtain ⟨hp3, hN6, hdim6⟩ := ggLE3_count (p := p) hp2 hW hC h α hpair hz hzα hcard hpN (by omega)
    exact ⟨hp3, hN6, by rw [ggNatCard_eq_pow_finrank (p := p) ι, hdim6, hp3]⟩
  · right
    rw [ggNatCard_eq_pow_finrank (p := p) ι, hdim]

end CFSG.StandardType

end
