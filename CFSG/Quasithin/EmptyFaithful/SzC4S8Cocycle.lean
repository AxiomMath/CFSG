module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.SzC4S8

open scoped commutatorElement

variable {G : Type} [Group G]

theorem cocycle_mem_of_perfect {L K N : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (hNK : N ≤ K) (hKL : ⁅K, L⁆ ≤ N) (hKK : ⁅K, K⁆ ≤ N)
    (ε : G → G) (hεK : ∀ l ∈ L, ε l ∈ K)
    (hcoc : ∀ a ∈ L, ∀ b ∈ L, ε (a * b) = ε a * (a * ε b * a⁻¹)) :
    ∀ l ∈ L, ε l ∈ N := by
  have hN : (N.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNK]
    intro n k hn hk
    have h : k * n * k⁻¹ = ⁅k, n⁆ * n := by simp [commutatorElement_def, mul_assoc]
    rw [h]
    exact N.mul_mem (hKK (Subgroup.commutator_mem_commutator hk (hNK hn))) hn
  let F : L →* K ⧸ N.subgroupOf K :=
    MonoidHom.mk' (fun l => QuotientGroup.mk ⟨ε l, hεK l l.2⟩) (fun a b => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h : (ε (a * b))⁻¹ * (ε a * ε b) = ⁅(ε b)⁻¹, (a : G)⁆⁻¹ := by
        simp [hcoc _ a.2 _ b.2, commutatorElement_def, mul_assoc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      show (ε (a * b))⁻¹ * (ε a * ε b) ∈ N
      rw [h]
      exact N.inv_mem (hKL (Subgroup.commutator_mem_commutator (K.inv_mem (hεK b b.2)) a.2)))
  have hab : ∀ x y : K ⧸ N.subgroupOf K, ⁅x, y⁆ = 1 := by
    intro x y
    induction x using QuotientGroup.induction_on with | H x =>
    induction y using QuotientGroup.induction_on with | H y =>
    have h : (⁅(x : K ⧸ N.subgroupOf K), (y : K ⧸ N.subgroupOf K)⁆ : K ⧸ N.subgroupOf K) =
        ((⁅x, y⁆ : K) : K ⧸ N.subgroupOf K) := rfl
    rw [h, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hKK (Subgroup.commutator_mem_commutator x.2 y.2)
  have hcomm : ⁅L, L⁆ ≤ F.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⁅(⟨g₁, hg₁⟩ : L), ⟨g₂, hg₂⟩⁆, ?_, rfl⟩
    exact (map_commutatorElement F _ _).trans (hab _ _)
  intro l hl
  obtain ⟨x, hx, rfl⟩ := hcomm (hperf.ge hl)
  have hx' : F x = 1 := hx
  exact (QuotientGroup.eq_one_iff (⟨ε x, hεK x x.2⟩ : K)).1 hx'

private theorem eq_prod_mul_inv_prod {A Q : Type} [CommGroup A] [Fintype Q]
    (hA2 : ∀ a : A, a * a = 1) (hodd : ¬ 2 ∣ Fintype.card Q) (e : Equiv.Perm Q) (f : Q → A)
    (φ : A →* A) (c : A) (hf : ∀ q, f (e q) = c * φ (f q)) :
    c = (∏ q, f q) * (φ (∏ q, f q))⁻¹ := by
  have h1 : ∏ q, f q = c ^ Fintype.card Q * φ (∏ q, f q) := by
    calc ∏ q, f q = ∏ q, f (e q) := (Equiv.prod_comp e f).symm
      _ = ∏ q, (c * φ (f q)) := Finset.prod_congr rfl fun q _ => hf q
      _ = c ^ Fintype.card Q * φ (∏ q, f q) := by
        rw [Finset.prod_mul_distrib, map_prod, Finset.prod_const, Finset.card_univ]
  have hc : c ^ Fintype.card Q = c := by
    obtain ⟨j, hj⟩ : Odd (Fintype.card Q) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    rw [hj, pow_succ, pow_mul, sq, hA2, one_pow, one_mul]
  rw [hc] at h1
  exact eq_mul_inv_iff_mul_eq.2 h1.symm

theorem cocycle_eq_one_of_odd_index {L U M₀ : Subgroup G}
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a * a = 1)
    (hM₀L : M₀ ≤ L) (hodd : ¬ 2 ∣ (M₀.subgroupOf L).index)
    (hfix : ∀ u ∈ U, (∀ m ∈ M₀, m * u * m⁻¹ = u) → u = 1)
    (d : G → G) (hdU : ∀ x ∈ L, d x ∈ U)
    (hcoc : ∀ x ∈ L, ∀ y ∈ L, d (x * y) = d x * (x * d y * x⁻¹))
    (hM : ∀ m ∈ M₀, d m = 1) : ∀ x ∈ L, d x = 1 := by
  have hconj : ∀ y ∈ L, ∀ u ∈ U, y * u * y⁻¹ ∈ U := fun y hy u hu =>
    (Subgroup.mem_set_normalizer_iff.1 (hLU hy) u).1 hu
  let _ : CommGroup U :=
    { (inferInstance : Group U) with
      mul_comm := fun a b => Subtype.ext (hUab a a.2 b b.2) }
  have hfin : Finite (L ⧸ M₀.subgroupOf L) :=
    Subgroup.index_ne_zero_iff_finite.1 fun h => hodd (h ▸ dvd_zero 2)
  let _ : Fintype (L ⧸ M₀.subgroupOf L) := Fintype.ofFinite _
  have hcard : Fintype.card (L ⧸ M₀.subgroupOf L) = (M₀.subgroupOf L).index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  let dbar : L ⧸ M₀.subgroupOf L → U := fun c => ⟨d c.out, hdU _ c.out.2⟩
  have hdbar : ∀ x : L, dbar (x : L ⧸ M₀.subgroupOf L) = ⟨d x, hdU _ x.2⟩ := by
    intro x
    apply Subtype.ext
    show d (((x : L ⧸ M₀.subgroupOf L).out : L) : G) = d x
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M₀.subgroupOf L) x
    have hm' : ((m : L) : G) ∈ M₀ := m.2
    rw [hm]
    simp [hcoc _ x.2 _ (hM₀L hm'), hM _ hm']
  let φ : L → U →* U := fun y => MonoidHom.mk' (fun u => ⟨y * u * y⁻¹, hconj y y.2 u u.2⟩)
    (fun a b => Subtype.ext (by simp [mul_assoc]))
  have key : ∀ y : L, (⟨d y, hdU _ y.2⟩ : U) = (∏ q, dbar q) * (φ y (∏ q, dbar q))⁻¹ := by
    intro y
    refine eq_prod_mul_inv_prod (fun a => Subtype.ext (hU2 a a.2)) (by rw [hcard]; exact hodd)
      (MulAction.toPerm y) dbar (φ y) _ ?_
    intro q
    induction q using QuotientGroup.induction_on with | H x =>
    have h1 : (MulAction.toPerm y) (x : L ⧸ M₀.subgroupOf L) =
        ((y * x : L) : L ⧸ M₀.subgroupOf L) := rfl
    rw [h1, hdbar, hdbar]
    exact Subtype.ext (hcoc _ y.2 _ x.2)
  set σ : U := ∏ q, dbar q
  have hσ1 : σ = 1 := by
    refine Subtype.ext (hfix σ σ.2 fun m hm => ?_)
    have h1 := key ⟨m, hM₀L hm⟩
    have h2 : (⟨d m, hdU _ (hM₀L hm)⟩ : U) = 1 := Subtype.ext (hM m hm)
    have h3 : σ = φ ⟨m, hM₀L hm⟩ σ := mul_inv_eq_one.1 (h1.symm.trans h2)
    exact (congrArg Subtype.val h3).symm
  intro x hx
  have h := key ⟨x, hx⟩
  rw [hσ1, map_one, inv_one, mul_one] at h
  exact congrArg Subtype.val h

end CFSG.Quasithin.SzC4S8
