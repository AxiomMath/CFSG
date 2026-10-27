module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIGrp
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def ccF (a k : G) : G := k * a * k⁻¹ * a⁻¹

theorem ccF_one (a : G) : ccF a 1 = 1 := by simp [ccF]

theorem ccF_mul (a k l : G) : ccF a (k * l) = (k * ccF a l * k⁻¹) * ccF a k := by
  unfold ccF; group

theorem hom_odd_trivial {N Q : Type} [Group N] [Group Q] (φ : N →* Q)
    (h2 : ∀ x : N, φ x ^ 2 = 1) (x : N) (hx : Odd (orderOf x)) : φ x = 1 := by
  obtain ⟨j, hj⟩ := hx
  have hm : φ x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have e : φ x = φ x ^ (orderOf x + 1) := by
    rw [pow_succ, hm, one_mul]
  rw [e, hj, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, h2, one_pow]

theorem subgroupOf_normal_of_comm {Zs J : Subgroup G}
    (hZc : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x) : (J.subgroupOf Zs).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : ((g * n * g⁻¹ : ↥Zs) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hZc (g : G) g.2 (n : G) n.2]
      group
    rw [e]
    exact hn⟩

theorem hom_quot {K0 Zs J : Subgroup G} [hJn : (J.subgroupOf Zs).Normal]
    (hZc : ∀ x ∈ Zs, ∀ y ∈ Zs, x * y = y * x)
    (hKZ : ∀ k ∈ K0, ∀ z ∈ Zs, k * z * k⁻¹ ∈ Zs)
    (c : G → G) (hc1 : c 1 = 1) (hcZ : ∀ k ∈ K0, c k ∈ Zs)
    (hmul : ∀ k ∈ K0, ∀ l ∈ K0, c (k * l) = (k * c l * k⁻¹) * c k)
    (htriv : ∀ k ∈ K0, ∀ z ∈ Zs, k * z * k⁻¹ * z⁻¹ ∈ J) :
    ∃ φ : K0 →* (Zs ⧸ J.subgroupOf Zs), ∀ k (hk : k ∈ K0),
      φ ⟨k, hk⟩ = QuotientGroup.mk ⟨c k, hcZ k hk⟩ := by
  have hcongr : ∀ (k l : G) (hk : k ∈ K0) (hl : l ∈ K0),
      (QuotientGroup.mk ⟨k * c l * k⁻¹, hKZ k hk _ (hcZ l hl)⟩ : Zs ⧸ J.subgroupOf Zs) =
        QuotientGroup.mk ⟨c l, hcZ l hl⟩ := by
    intro k l hk hl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := htriv k hk (c l)⁻¹ (Zs.inv_mem (hcZ l hl))
    rw [inv_inv] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    convert h using 1
    group
  let f : K0 → (Zs ⧸ J.subgroupOf Zs) := fun k => QuotientGroup.mk ⟨c k.1, hcZ k.1 k.2⟩
  have hf_mul : ∀ x y : K0, f (x * y) = f x * f y := by
    intro x y
    have e : (⟨c ((x * y : K0) : G), hcZ _ (x * y).2⟩ : Zs) =
        ⟨(x : G) * c y * (x : G)⁻¹, hKZ x x.2 _ (hcZ y y.2)⟩ * ⟨c x, hcZ x x.2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hmul x x.2 y y.2
    show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [e, QuotientGroup.mk_mul, hcongr x y x.2 y.2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hZc _ (hcZ y y.2) _ (hcZ x x.2)
  exact ⟨MonoidHom.mk' f hf_mul, fun k hk => rfl⟩

end CFSG.Quasithin.H13.C1294
