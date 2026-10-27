module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepA_y_fixed_data {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {b : Λ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hα : ∀ c : Λ, α (some c) (h (some c)) = 2)
    (hAJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ (some j))) :
    ∃ hy : y ∈ Bs, ι (Additive.ofMul (⟨y, hy⟩ : Bs)) ∉
      Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)} ∧
      ∀ c : Λ, c ≠ b → α (some c) (ι (Additive.ofMul (⟨y, hy⟩ : Bs))) = 0 := by
  have hStd : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hBstar : GGBstar p B Bs := hH.1.2.1
  have hNbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hBspow : ∀ z ∈ Bs, z ^ p = 1 := hBstar.2.1.2
  have hDB : D ≤ B := hStd.1.1
  have hDcard : Nat.card D = p ^ 2 := hStd.1.2.2.1
  have hDcent : D = B ⊓ Subgroup.centralizer (J : Set G) := hStd.1.2.2.2.2.2.2
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hNbr.2.1
  have hyD : y ∈ D := by
    rw [hDgen]
    exact Subgroup.subset_closure (by simp)
  have hyBs : y ∈ Bs := hBBs (hDB hyD)
  have hyCent : y ∈ Subgroup.centralizer (J : Set G) := by
    have h := hyD
    rw [hDcent] at h
    exact h.2
  have hnotspan : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ∉
      Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} := by
    intro hy'mem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy'mem
    set k : ℕ := c.val with hk
    have hck : ((k : ℕ) : ZMod p) = c := by rw [hk]; exact ZMod.natCast_zmod_val c
    have hc_nsmul : k • ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) =
        ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) := by
      have h := hc
      rw [← hck] at h
      rwa [Nat.cast_smul_eq_nsmul] at h
    have hsymm : k • Additive.ofMul (⟨x, hx⟩ : ↥Bs) =
        Additive.ofMul (⟨y, hyBs⟩ : ↥Bs) := by
      have h := congrArg ι.symm hc_nsmul
      simpa using h
    have hpow : Additive.ofMul ((⟨x, hx⟩ : ↥Bs) ^ k) =
        Additive.ofMul (⟨y, hyBs⟩ : ↥Bs) := by
      rw [ofMul_pow]
      exact hsymm
    have hba : (⟨x, hx⟩ : ↥Bs) ^ k = ⟨y, hyBs⟩ := Additive.ofMul.injective hpow
    have hy_eq : y = x ^ k := by
      have h := congrArg (fun t : ↥Bs => (t : G)) hba
      simpa using h.symm
    have hy_zp : y ∈ Subgroup.zpowers x := by
      rw [hy_eq]
      exact Subgroup.npow_mem_zpowers x k
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hDgen]
      refine (Subgroup.closure_le (Subgroup.zpowers x)).mpr ?_
      intro a ha
      have ha' : a = x ∨ a = y := by simpa using ha
      rcases ha' with h | h
      · rw [h]; exact Subgroup.mem_zpowers x
      · rw [h]; exact hy_zp
    have hx_pow : x ^ p = 1 := hBspow x hx
    have hxord : orderOf x ≤ p :=
      Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one hx_pow)
    have hcardle : p ^ 2 ≤ p := by
      calc p ^ 2 = Nat.card D := hDcard.symm
        _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
        _ ≤ p := by rw [Nat.card_zpowers]; exact hxord
    nlinarith [hcardle, (Fact.out : p.Prime).two_le]
  have hfixall : ∀ c : Λ, c ≠ b →
      α (some c) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = 0 := by
    intro c hc
    have hstab : ggInduced J Bs ⊆
        MulAction.stabilizer (MulAut ↥Bs) (⟨y, hyBs⟩ : ↥Bs) := by
      rintro ψ ⟨g, hgJ, -, hgψ⟩
      change ψ ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hyBs⟩ : ↥Bs)
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      change ((ψ ⟨y, hyBs⟩ : ↥Bs) : G) = y
      have hgψy : ((ψ ⟨y, hyBs⟩ : ↥Bs) : G) = g * y * g⁻¹ := by
        simpa using hgψ ⟨y, hyBs⟩
      rw [hgψy]
      have hcomm : g * y = y * g := (Subgroup.mem_centralizer_iff.mp hyCent) g hgJ
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hfix : φ (some c) ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
      have hmem : φ (some c) ∈ ggAutomizer J Bs := by
        rw [hAJ]
        exact Subgroup.subset_closure
          (Set.mem_range_self (f := fun j : {j : Λ // j ≠ b} => φ (some j)) ⟨c, hc⟩)
      have hle : Subgroup.closure (ggInduced J Bs) ≤
          MulAction.stabilizer (MulAut ↥Bs) (⟨y, hyBs⟩ : ↥Bs) :=
        (Subgroup.closure_le (MulAction.stabilizer (MulAut ↥Bs) (⟨y, hyBs⟩ : ↥Bs))).mpr hstab
      have h := MulAction.mem_stabilizer_iff.mp (hle hmem)
      simpa using h
    have hvec : ggLin (p := p) ι (φ (some c)) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) =
        ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) :=
      (ggLin_fix_iff (p := p) ι (φ (some c)) (⟨y, hyBs⟩ : ↥Bs)).mp hfix
    have hsub : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) =
        ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) -
          α (some c) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) • h (some c) := by
      have h := hφ (some c) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)))
      rw [hvec] at h
      exact h
    have hcongr := congrArg (α (some c)) hsub
    rw [map_sub, map_smul, hα c, smul_eq_mul] at hcongr
    have hmul : α (some c) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) * 2 = 0 :=
      sub_eq_self.mp hcongr.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h (zmod_two_ne_zero hp2)
  exact ⟨hyBs, hnotspan, hfixall⟩

theorem ggDepA_y_fixed {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {b : Λ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hα : ∀ c : Λ, α (some c) (h (some c)) = 2)
    (hAJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ (some j))) :
    ∃ y' : V, y' ∉ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)} ∧
      ∀ c : Λ, c ≠ b → α (some c) y' = 0 := by
  obtain ⟨hy, hnot, hfix⟩ := ggDepA_y_fixed_data hp2 hH hx hφ hα hAJ
  exact ⟨ι (Additive.ofMul (⟨y, hy⟩ : Bs)), hnot, hfix⟩

end CFSG.StandardType
