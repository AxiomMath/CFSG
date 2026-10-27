module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E7Le
public import CFSG.Quasithin.Vol2.Ch4Sec4W4414Z

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise

variable {G : Type} [Group G]

theorem conjAct_coe (V : Subgroup G) (n : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAct V n v : ↥V) : G) = (n : G) * (v : G) * (n : G)⁻¹ := by
  unfold conjAct
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem mem_autOn_iff' {X V : Subgroup G} {φ : MulAut ↥V} :
    φ ∈ autOn X V ↔ ∃ n : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ X ∧ conjAct V n = φ := by
  unfold autOn
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem autOn_mono' {X Y V : Subgroup G} (h : X ≤ Y) : autOn X V ≤ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_mono h

theorem exists_conj_eq {X C V : Subgroup G} (hXC : X ≤ Subgroup.normalizer (C : Set G))
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) {y : G} (hy : y ∈ X ⊔ C) :
    ∃ a ∈ X, ∀ v ∈ V, y * v * y⁻¹ = a * v * a⁻¹ := by
  have hy' : y ∈ (X : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X C hXC]
    exact hy
  obtain ⟨a, ha, c, hc, rfl⟩ := hy'
  refine ⟨a, ha, fun v hv => ?_⟩
  have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.mp (hCV hc) v hv).symm
  calc a * c * v * (a * c)⁻¹ = a * (c * v) * c⁻¹ * a⁻¹ := by group
    _ = a * (v * c) * c⁻¹ * a⁻¹ := by rw [hcv]
    _ = a * v * a⁻¹ := by group

theorem autOn_sup_eq {X C V : Subgroup G} (hXC : X ≤ Subgroup.normalizer (C : Set G))
    (hCV : C ≤ Subgroup.centralizer (V : Set G)) (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (X ⊔ C) V = autOn X V := by
  refine le_antisymm (fun φ hφ => ?_) (autOn_mono' le_sup_left)
  obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.mp hφ
  obtain ⟨a, ha, hav⟩ := exists_conj_eq hXC hCV hn
  refine mem_autOn_iff'.mpr ⟨⟨a, hXV ha⟩, ha, MulEquiv.ext fun v => Subtype.ext ?_⟩
  rw [conjAct_coe, conjAct_coe]
  exact (hav v v.2).symm

theorem isNaturalSumUnder_sup {n : ℕ} {X C V : Subgroup G}
    (hXC : X ≤ Subgroup.normalizer (C : Set G)) (hCV : C ≤ Subgroup.centralizer (V : Set G))
    (h : IsNaturalSumUnder n X V) : IsNaturalSumUnder n (X ⊔ C) V := by
  obtain ⟨k, W, hk, hW, hiso, hind, hsup⟩ := h
  refine ⟨k, W, hk, fun i => ?_, fun i j => ?_, hind, hsup⟩
  · obtain ⟨hWV, hXW, hc, hnat⟩ := hW i
    have hCW : C ≤ Subgroup.centralizer (W i : Set G) := hCV.trans (Subgroup.centralizer_le hWV)
    refine ⟨hWV, sup_le hXW (hCW.trans (Subgroup.centralizer_le_normalizer _)), hc, ?_⟩
    rw [autOn_sup_eq hXC hCW hXW]
    exact hnat
  · obtain ⟨h1, h2, e, he⟩ := hiso i j
    refine ⟨h1, h2, e, fun x hx a b ha hb hab => ?_⟩
    obtain ⟨y, hy, hyv⟩ := exists_conj_eq hXC hCV hx
    have ea := hyv _ ((hW i).1 a.2)
    have eb := hyv _ ((hW j).1 b.2)
    have ha' : y * (a : G) * y⁻¹ ∈ W i := ea ▸ ha
    have hb' : y * (b : G) * y⁻¹ ∈ W j := eb ▸ hb
    have e1 : (⟨x * (a : G) * x⁻¹, ha⟩ : ↥(W i)) = ⟨y * (a : G) * y⁻¹, ha'⟩ := Subtype.ext ea
    have e2 : (⟨x * (b : G) * x⁻¹, hb⟩ : ↥(W j)) = ⟨y * (b : G) * y⁻¹, hb'⟩ := Subtype.ext eb
    rw [e1, e2]
    exact he y hy a b ha' hb' hab

variable [Finite G]

theorem nonempty_quotEquiv {X Y : Subgroup G} (hXY : X ≤ Y) (hY : Y = X ⊔ pCoreOf 2 Y)
    (hO : pCoreOf 2 X ≤ pCoreOf 2 Y) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥X →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hXY) with hφ
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hXY.trans (le_normalizer_pCoreOf 2 Y)
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ (X : Set G) * (pCoreOf 2 Y : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right X _ hXN, ← hY]
      exact y.2
    obtain ⟨a, ha, c, hc, hac⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine (coe_mem_pCoreOf_two_iff _).mp ?_
    have e : ((Subgroup.inclusion hXY ⟨a, ha⟩)⁻¹ * y : ↥Y) = (c : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hac]
      group
    rw [e]
    exact hc
  have hker : φ.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← coe_mem_pCoreOf_two_iff, ← coe_mem_pCoreOf_two_iff,
      Subgroup.coe_inclusion]
    refine ⟨fun hx => ?_, fun hx => hO hx⟩
    have h1 : X ⊓ pCoreOf 2 Y ≤ pCoreOf 2 X :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => (mem_normalizer_inf_sup (Subgroup.le_normalizer hg) (hXN hg)).1)
        ((pCoreOf_isPGroup 2 Y).to_le inf_le_right)
    exact h1 ⟨x.2, hx⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

end CFSG.Quasithin.H13.Ch4.E443
