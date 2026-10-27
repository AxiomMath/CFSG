module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem relIndex_U_eq_relIndex_B (h : Hyp65 n M V₀ V g) (hswap : SwapHyp V g) :
    (NOf M V g).relIndex (UOf M V g) = (NOf M V g).relIndex (BOf M V g) := by
  obtain ⟨l, hlL, h1, h2⟩ := hswap
  have hU : conjSubgroup (UOf M V g) l = BOf M V g :=
    conjSubgroup_U_eq_B_of_swap h h1 h2
  have hN : conjSubgroup (NOf M V g) l = NOf M V g := conjSubgroup_N_eq h hlL
  have hNmap : (NOf M V g).map (MulAut.conj l⁻¹).toMonoidHom = NOf M V g := hN
  have hUmap : (UOf M V g).map (MulAut.conj l⁻¹).toMonoidHom = BOf M V g := hU
  have key := Subgroup.relIndex_map_map_of_injective (NOf M V g) (UOf M V g)
    (f := (MulAut.conj l⁻¹).toMonoidHom) (MulAut.conj l⁻¹).injective
  rw [hNmap, hUmap] at key
  exact key.symm

private theorem s65_SixFiveJ_commutator_mul_modN (h : Hyp65 n M V₀ V g) {b₁ b₂ v : G}
    (hb₁ : b₁ ∈ BOf M V g) (hb₂ : b₂ ∈ BOf M V g) (hv : v ∈ V) :
    ⁅b₁ * b₂, v⁆ * (⁅b₁, v⁆ * ⁅b₂, v⁆)⁻¹ ∈ NOf M V g := by
  have hBU : ⁅BOf M V g, UOf M V g⁆ ≤ NOf M V g := by
    rw [Subgroup.commutator_comm]
    exact commutator_U_B_le_N h
  have hb₂v : ⁅b₂, v⁆ ∈ UOf M V g :=
    commutator_B_V_le_U h (Subgroup.commutator_mem_commutator hb₂ hv)
  have hb₁v : ⁅b₁, v⁆ ∈ UOf M V g :=
    commutator_B_V_le_U h (Subgroup.commutator_mem_commutator hb₁ hv)
  have hN : b₁ * ⁅b₂, v⁆ * b₁⁻¹ * ⁅b₂, v⁆⁻¹ ∈ NOf M V g :=
    hBU (Subgroup.commutator_mem_commutator hb₁ hb₂v)
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hsplit : (b₁ * ⁅b₂, v⁆ * b₁⁻¹ * ⁅b₁, v⁆) * (⁅b₁, v⁆ * ⁅b₂, v⁆)⁻¹
      = (b₁ * ⁅b₂, v⁆ * b₁⁻¹ * ⁅b₂, v⁆⁻¹)
        * (⁅b₂, v⁆ * ⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹ * ⁅b₁, v⁆⁻¹) := by group
  rw [hsplit]
  refine (NOf M V g).mul_mem hN ?_
  have hcomm : ⁅b₂, v⁆ * ⁅b₁, v⁆ = ⁅b₁, v⁆ * ⁅b₂, v⁆ :=
    IsElemAbelian.comm h.elemAbelian hb₂v.1 hb₁v.1
  rw [show ⁅b₂, v⁆ * ⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹ * ⁅b₁, v⁆⁻¹ = 1 by rw [hcomm]; group]
  exact (NOf M V g).one_mem

theorem exists_commutator_mul_N (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) (hswap : SwapHyp V g) {v : G}
    (hvV : v ∈ V) (hvU : v ∉ UOf M V g) :
    ∀ u ∈ UOf M V g, ∃ b ∈ BOf M V g, ∃ m ∈ NOf M V g, u = ⁅b, v⁆ * m := by
  haveI : IsMulCommutative ↥(UOf M V g) :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (h.elemAbelian.comm (Subgroup.mem_inf.1 a.2).1 (Subgroup.mem_inf.1 b.2).1)
  have hmem : ∀ b ∈ BOf M V g, ⁅(b : G), v⁆ ∈ UOf M V g := fun b hb =>
    commutator_B_V_le_U h (Subgroup.commutator_mem_commutator hb hvV)
  let U' : Subgroup ↥(UOf M V g) := (NOf M V g).subgroupOf (UOf M V g)
  let φ : ↥(BOf M V g) →* (↥(UOf M V g) ⧸ U') :=
    MonoidHom.mk' (fun b => QuotientGroup.mk (⟨⁅(b : G), v⁆, hmem b b.2⟩ : ↥(UOf M V g)))
      (by
        intro b₁ b₂
        have hb₁ : (b₁ : G) ∈ BOf M V g := b₁.2
        have hb₂ : (b₂ : G) ∈ BOf M V g := b₂.2
        have hN := s65_SixFiveJ_commutator_mul_modN h hb₁ hb₂ hvV
        rw [← QuotientGroup.mk_mul]
        apply QuotientGroup.eq.2
        rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hcU : ⁅(b₁ : G) * (b₂ : G), v⁆ ∈ UOf M V g :=
          hmem ((b₁ : G) * (b₂ : G)) ((BOf M V g).mul_mem hb₁ hb₂)
        have habU : ⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆ ∈ UOf M V g :=
          (UOf M V g).mul_mem (hmem _ hb₁) (hmem _ hb₂)
        have hcomm : ⁅(b₁ : G) * (b₂ : G), v⁆ * (⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆)
            = (⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆) * ⁅(b₁ : G) * (b₂ : G), v⁆ :=
          h.elemAbelian.comm (Subgroup.mem_inf.1 hcU).1 (Subgroup.mem_inf.1 habU).1
        have hNinv : (⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆) * (⁅(b₁ : G) * (b₂ : G), v⁆)⁻¹
            ∈ NOf M V g := by
          simpa using (NOf M V g).inv_mem hN
        have heq : (⁅(b₁ : G) * (b₂ : G), v⁆)⁻¹ * (⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆)
            = (⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆) * (⁅(b₁ : G) * (b₂ : G), v⁆)⁻¹ :=
          (Commute.inv_left (show Commute ⁅(b₁ : G) * (b₂ : G), v⁆
            (⁅(b₁ : G), v⁆ * ⁅(b₂ : G), v⁆) from hcomm)).eq
        rw [heq]
        exact hNinv)
  have hker : φ.ker = (NOf M V g).subgroupOf (BOf M V g) := by
    ext b
    rw [MonoidHom.mem_ker]
    have hφb : φ b = QuotientGroup.mk (⟨⁅(b : G), v⁆, hmem b b.2⟩ : ↥(UOf M V g)) := rfl
    rw [hφb, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hbN
      have hbK : (b : G) ∈ KOf M V g := Subgroup.mem_sup_right b.2
      have hbU : (b : G) ∈ UOf M V g :=
        stepB h hgen hlK hvV hvU (b : G) hbK hbN
      exact Subgroup.mem_inf.2 ⟨hbU, b.2⟩
    · intro hbN
      have hbV : (b : G) ∈ V :=
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hbN).1).1
      have hcomm : (b : G) * v = v * (b : G) := h.elemAbelian.comm hbV hvV
      have h1 : ⁅(b : G), v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm
      have h2 : (⟨⁅(b : G), v⁆, hmem b b.2⟩ : ↥(UOf M V g)) = 1 := Subtype.ext h1
      rw [h2]
      exact (NOf M V g).one_mem
  have hcardRange : Nat.card φ.range = (NOf M V g).relIndex (BOf M V g) := by
    rw [← Subgroup.index_ker φ, hker]
    rfl
  have hcardQ : Nat.card (↥(UOf M V g) ⧸ U') = (NOf M V g).relIndex (UOf M V g) := rfl
  have htop : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcardRange, ← relIndex_U_eq_relIndex_B h hswap]
    exact hcardQ.symm
  intro u hu
  have hq : (QuotientGroup.mk (⟨u, hu⟩ : ↥(UOf M V g)) : ↥(UOf M V g) ⧸ U') ∈ φ.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hq
  have hmemQ : (⟨⁅(b : G), v⁆, hmem b b.2⟩ : ↥(UOf M V g))⁻¹ * ⟨u, hu⟩ ∈ U' :=
    QuotientGroup.eq.1 hb
  rw [Subgroup.mem_subgroupOf] at hmemQ
  refine ⟨b, b.2, ⁅(b : G), v⁆⁻¹ * u, ?_, ?_⟩
  · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmemQ
  · group

theorem U_le_Z0_sup_N (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) (hswap : SwapHyp V g)
    (hVV : V ≤ V₀ ⊔ UOf M V g) : UOf M V g ≤ Z0Of M V₀ g ⊔ NOf M V g := by
  obtain ⟨v, hvV, hvMg⟩ := Set.not_subset.1 h.not_V_le_conjM
  have hvU : v ∉ UOf M V g := fun hv => hvMg (Subgroup.mem_inf.1 hv).2
  have hV0centU : V₀ ≤ Subgroup.centralizer (UOf M V g : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h.elemAbelian.comm (h.le hz) (Subgroup.mem_inf.1 hx).1).symm
  have hV0normU : V₀ ≤ Subgroup.normalizer (UOf M V g : Set G) :=
    hV0centU.trans (Subgroup.centralizer_le_normalizer _)
  have hVprod : (↑(V₀ ⊔ UOf M V g) : Set G) = (V₀ : Set G) * (UOf M V g : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hV0normU
  intro u hu
  obtain ⟨b, hbB, m, hmN, hu_eq⟩ :=
    exists_commutator_mul_N h hgen hlK hswap hvV hvU u hu
  have hv_prod : v ∈ (V₀ : Set G) * (UOf M V g : Set G) := by
    rw [← hVprod]
    exact hVV hvV
  obtain ⟨v₀, hv₀, u₁, hu₁, hv_eq⟩ := Set.mem_mul.1 hv_prod
  have hzV0 : ⁅b, v₀⁆ ∈ V₀ := by
    have hbNorm : b ∈ Subgroup.normalizer (V₀ : Set G) := by
      rw [h.normalizer₀]
      exact hbB.2
    have hbconj : b * v₀ * b⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 hbNorm v₀).1 hv₀
    rw [commutatorElement_def]
    exact V₀.mul_mem hbconj (V₀.inv_mem hv₀)
  have hzU : ⁅b, v₀⁆ ∈ UOf M V g :=
    commutator_B_V_le_U h (Subgroup.commutator_mem_commutator hbB (h.le hv₀))
  have hzZ0 : ⁅b, v₀⁆ ∈ Z0Of M V₀ g := by
    rw [Z0Of, Subgroup.mem_inf]
    exact ⟨hzV0, (Subgroup.mem_inf.1 hzU).2⟩
  have hnN : ⁅b, u₁⁆ ∈ NOf M V g := by
    have h1 : ⁅u₁, b⁆ ∈ NOf M V g :=
      commutator_U_B_le_N h (Subgroup.commutator_mem_commutator hu₁ hbB)
    simpa using (NOf M V g).inv_mem h1
  have hv₀L : v₀ ∈ LOf V g := by
    rw [LOf]
    exact Subgroup.mem_sup_left (h.le hv₀)
  have hcommn : v₀ * ⁅b, u₁⁆ * v₀⁻¹ = ⁅b, u₁⁆ := by
    have hc : v₀ * ⁅b, u₁⁆ = ⁅b, u₁⁆ * v₀ :=
      Subgroup.mem_centralizer_iff.1 (N_le_centralizer_L h hnN) v₀ hv₀L
    rw [hc]
    group
  have hzN : ⁅b, v₀ * u₁⁆ = ⁅b, v₀⁆ * ⁅b, u₁⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅b, v₀⁆ * v₀ * ⁅b, u₁⁆ * v₀⁻¹
      = ⁅b, v₀⁆ * (v₀ * ⁅b, u₁⁆ * v₀⁻¹) by group]
    rw [hcommn]
  rw [hu_eq, ← hv_eq, hzN, mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hzZ0)
    (Subgroup.mem_sup_right ((NOf M V g).mul_mem hnN hmN))

theorem exists_commutator_eq_of_V₀_le_K (h : Hyp65 n M V₀ V g) (hgen : GenHyp M V g)
    (hlK : ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) (hV₀K : V₀ ≤ KOf M V g) {x : G}
    (hxVg : x ∈ conjSubgroup V g) (hxB : x ∉ BOf M V g) :
    ∀ y ∈ conjSubgroup V₀ g, ∃ z ∈ V₀, ⁅z, x⁆ = y := by
  have hV0U : V₀ ≤ UOf M V g := by
    rw [← V_inf_K h]
    exact le_inf h.le hV₀K
  have hV0Z0 : V₀ ≤ Z0Of M V₀ g := by
    rw [Z0Of]
    exact le_inf le_rfl (hV0U.trans inf_le_right)
  have hmemY : ∀ z ∈ V₀, ⁅z, x⁆ ∈ YOf M V₀ g := fun z hz =>
    commutator_Z0_conjV_le_Y h (Subgroup.commutator_mem_commutator (hV0Z0 hz) hxVg)
  have hYT : YOf M V₀ g ≤ conjSubgroup V₀ g := by
    rw [YOf]
    exact inf_le_left
  let f : ↥V₀ →* ↥(conjSubgroup V₀ g) :=
    MonoidHom.mk' (fun z => ⟨⁅(z : G), x⁆, hYT (hmemY z z.2)⟩) (by
      intro z z'
      apply Subtype.ext
      change ⁅(z : G) * (z' : G), x⁆ = ⁅(z : G), x⁆ * ⁅(z' : G), x⁆
      have hzZ0 : (z : G) ∈ Z0Of M V₀ g := hV0Z0 z.2
      have hyY : ⁅(z' : G), x⁆ ∈ YOf M V₀ g := hmemY z' z'.2
      have hcomm : (z : G) * ⁅(z' : G), x⁆ = ⁅(z' : G), x⁆ * (z : G) :=
        Z0_Y_comm h hzZ0 hyY
      have hYab : IsElemAbelian 2 (conjSubgroup V₀ g) :=
        h.swap.elemAbelian.mono (conjSubgroup_mono h.le g)
      have hcomm2 : ⁅(z : G), x⁆ * ⁅(z' : G), x⁆ = ⁅(z' : G), x⁆ * ⁅(z : G), x⁆ :=
        IsElemAbelian.comm hYab (hYT (hmemY z z.2)) (hYT (hmemY z' z'.2))
      rw [commutatorElement_mul_left_eq_conj_mul]
      calc (z : G) * ⁅(z' : G), x⁆ * (z : G)⁻¹ * ⁅(z : G), x⁆
          = ⁅(z' : G), x⁆ * ⁅(z : G), x⁆ := by
            rw [show (z : G) * ⁅(z' : G), x⁆ * (z : G)⁻¹ = ⁅(z' : G), x⁆ by
              rw [hcomm]; group]
        _ = ⁅(z : G), x⁆ * ⁅(z' : G), x⁆ := hcomm2.symm)
  have hfinj : Function.Injective f := by
    intro z z' heq
    have hf : f (z * z'⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have hcomm1 : ((z * z'⁻¹ : ↥V₀) : G) ∈ V₀ ∧ ⁅((z * z'⁻¹ : ↥V₀) : G), x⁆ = 1 :=
      ⟨(z * z'⁻¹).2, by
        have h := congrArg (fun w : ↥(conjSubgroup V₀ g) => (w : G)) hf
        simpa [f] using h⟩
    have hkB : ((z * z'⁻¹ : ↥V₀) : G) ∈ BOf M V g :=
      stepA h hgen hlK hxVg hxB _ (hV₀K hcomm1.1)
        (by rw [hcomm1.2]; exact (NOf M V g).one_mem)
    have hkbot : ((z * z'⁻¹ : ↥V₀) : G) ∈ (⊥ : Subgroup G) := by
      have hmem : ((z * z'⁻¹ : ↥V₀) : G) ∈ V₀ ⊓ conjSubgroup V g :=
        ⟨hcomm1.1, hkB.1⟩
      rwa [V₀_inf_conjV h] at hmem
    have hk1 : ((z * z'⁻¹ : ↥V₀) : G) = 1 := Subgroup.mem_bot.1 hkbot
    exact mul_inv_eq_one.1 (Subtype.ext hk1)
  have hfsurj : Function.Surjective f :=
    (Finite.injective_iff_surjective_of_equiv
      (Subgroup.equivMapOfInjective V₀ (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).toEquiv).1 hfinj
  intro y hy
  obtain ⟨z, hz⟩ := hfsurj ⟨y, hy⟩
  exact ⟨(z : G), z.2, congrArg (fun w : ↥(conjSubgroup V₀ g) => (w : G)) hz⟩

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
