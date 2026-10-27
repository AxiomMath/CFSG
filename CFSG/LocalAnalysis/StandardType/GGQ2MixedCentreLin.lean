module

public import Mathlib.LinearAlgebra.Dual.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

open CFSG Module

section Linear

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ggQ2Mix_stable_dichotomy (c : ι → V) (α : ι → Dual K V) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span K {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (U : Submodule K V) (hU : ∀ i, ∀ u ∈ U, α i u • c i ∈ U) :
    Submodule.span K (Set.range c) ≤ U ∨ U ≤ Submodule.span K {x} := by
  classical
  by_cases hex : ∃ i, c i ∈ U
  · left
    obtain ⟨i, hi⟩ := hex
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hmem : ∀ k, c k ∈ U := by
      intro k
      have hpath := hconn i k
      induction hpath with
      | refl => exact hi
      | tail hab hbc ih =>
          rename_i b d
          have h := hU d (c b) ih
          have h' : c d = (α d (c b))⁻¹ • (α d (c b) • c d) := by
            rw [smul_smul, inv_mul_cancel₀ hbc.2, one_smul]
          rw [h']
          exact Submodule.smul_mem _ _ h
    exact hmem j
  · right
    intro u hu
    apply hfix u
    intro i
    by_contra hne
    apply hex
    exact ⟨i, by
      have h := hU i u hu
      have h' : c i = (α i u)⁻¹ • (α i u • c i) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [h']
      exact Submodule.smul_mem _ _ h⟩

theorem ggQ2Mix_stable_eq_bot_or_top (c : ι → V) (α : ι → Dual K V) (x : V)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span K {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hsplit : Submodule.span K (Set.range c) ⊔ Submodule.span K {x} = ⊤)
    (f : Dual K V) (c₀ : V) (hc₀H : c₀ ∉ Submodule.span K (Set.range c))
    (hc₀x : c₀ ∉ Submodule.span K {x}) (hfx : f x ≠ 0)
    (hfH : ∃ h ∈ Submodule.span K (Set.range c), f h ≠ 0)
    (U : Submodule K V) (hU : ∀ i, ∀ u ∈ U, α i u • c i ∈ U) (hUt : ∀ u ∈ U, f u • c₀ ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  rcases ggQ2Mix_stable_dichotomy c α x hfix hconn U hU with hH | hx
  · right
    obtain ⟨h, hhH, hfh⟩ := hfH
    have hhU : h ∈ U := hH hhH
    have hc0U : c₀ ∈ U := by
      have hmem := hUt h hhU
      have h' : c₀ = (f h)⁻¹ • (f h • c₀) := by
        rw [smul_smul, inv_mul_cancel₀ hfh, one_smul]
      rw [h']
      exact Submodule.smul_mem _ _ hmem
    have hc0 : c₀ ∈ Submodule.span K (Set.range c) ⊔ Submodule.span K {x} := by
      rw [hsplit]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hc0
    obtain ⟨h', hh', z, hz, hc0_eq⟩ := hc0
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨a, ha_eq⟩ := hz
    have hc0_eq' : h' + a • x = c₀ := by
      rw [ha_eq]
      exact hc0_eq
    have ha_ne : a ≠ 0 := by
      intro ha0
      apply hc₀H
      rw [← hc0_eq', ha0, zero_smul, add_zero]
      exact hh'
    have hxU : x ∈ U := by
      have h1 : a • x ∈ U := by
        have h2 : a • x = c₀ - h' := by
          rw [← hc0_eq']
          abel
        rw [h2]
        exact Submodule.sub_mem _ hc0U (hH hh')
      have h3 : x = a⁻¹ • (a • x) := by
        rw [smul_smul, inv_mul_cancel₀ ha_ne, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _ h1
    rw [eq_top_iff]
    intro v hv
    have hv' : v ∈ Submodule.span K (Set.range c) ⊔ Submodule.span K {x} := by
      rw [hsplit]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hv'
    obtain ⟨h'', hh'', z, hz, hv_eq⟩ := hv'
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨b, hb⟩ := hz
    rw [← hv_eq, ← hb]
    exact Submodule.add_mem _ (hH hh'') (Submodule.smul_mem _ _ hxU)
  · left
    by_contra hbot
    have hne : U ≠ ⊥ := hbot
    obtain ⟨u, huU, hu0⟩ := U.ne_bot_iff.mp hne
    have hu : u ∈ Submodule.span K {x} := hx huU
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨b, hb⟩ := hu
    have hbne : b ≠ 0 := by
      intro hb0
      apply hu0
      rw [← hb, hb0, zero_smul]
    have hxU : x ∈ U := by
      have h := Submodule.smul_mem _ b⁻¹ huU
      have h' : x = b⁻¹ • u := by
        rw [← hb, smul_smul, inv_mul_cancel₀ hbne, one_smul]
      rw [h']
      exact h
    have hc0U : c₀ ∈ U := by
      have h := hUt x hxU
      have h' : c₀ = (f x)⁻¹ • (f x • c₀) := by
        rw [smul_smul, inv_mul_cancel₀ hfx, one_smul]
      rw [h']
      exact Submodule.smul_mem _ _ h
    exact hc₀x (hx hc0U)

theorem ggQ2Mix_commute_eq_smul (two_ne : (2 : K) ≠ 0) (c : ι → V) (α : ι → Dual K V)
    (hαc : ∀ i, α i (c i) = 2) (x : V) (hαx : ∀ i, α i x = 0)
    (hxH : x ∉ Submodule.span K (Set.range c))
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span K {x})
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hsplit : Submodule.span K (Set.range c) ⊔ Submodule.span K {x} = ⊤)
    (f : Dual K V) (c₀ : V) (hfc₀ : f c₀ = 2) (hc₀H : c₀ ∉ Submodule.span K (Set.range c))
    (hc₀x : c₀ ∉ Submodule.span K {x}) (T : V →ₗ[K] V)
    (hTs : ∀ i v, T (v - α i v • c i) = T v - α i (T v) • c i)
    (hTt : ∀ v, T (v - f v • c₀) = T v - f (T v) • c₀) :
    ∃ μ : K, T = μ • LinearMap.id := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    have hc_ne : ∀ i, c i ≠ 0 := by
      intro i hci0
      have h := hαc i
      rw [hci0, map_zero] at h
      exact two_ne h.symm
    have hμ_exists : ∀ i, ∃ μ_i : K, T (c i) = μ_i • c i := by
      intro i
      have hsi : c i - α i (c i) • c i = - c i := by
        rw [hαc i]
        module
      have h := hTs i (c i)
      rw [hsi, map_neg] at h
      have h2 : (2 : K) • T (c i) = α i (T (c i)) • c i := by
        calc
          (2 : K) • T (c i) = T (c i) + T (c i) := by rw [two_smul]
          _ = (T (c i) - α i (T (c i)) • c i) + α i (T (c i)) • c i + T (c i) := by
            abel
          _ = -T (c i) + α i (T (c i)) • c i + T (c i) := by rw [← h]
          _ = α i (T (c i)) • c i := by abel
      refine ⟨(2 : K)⁻¹ * α i (T (c i)), ?_⟩
      calc
        T (c i) = (2 : K)⁻¹ • ((2 : K) • T (c i)) := by
          rw [smul_smul, inv_mul_cancel₀ two_ne, one_smul]
        _ = (2 : K)⁻¹ • (α i (T (c i)) • c i) := by rw [h2]
        _ = ((2 : K)⁻¹ * α i (T (c i))) • c i := by rw [smul_smul]
    choose μ hμ using hμ_exists
    have hμ_edge : ∀ a b, α a (c b) ≠ 0 → α b (c a) ≠ 0 → μ a = μ b := by
      intro a b hab hba
      have h := hTs b (c a)
      rw [map_sub, map_smul] at h
      have h1 : α b (c a) • T (c b) = α b (T (c a)) • c b := by
        have h2 : -(α b (c a) • T (c b)) = -(α b (T (c a)) • c b) := by
          calc
            -(α b (c a) • T (c b)) = T (c a) - α b (c a) • T (c b) - T (c a) := by
              abel
            _ = T (c a) - α b (T (c a)) • c b - T (c a) := by rw [h]
            _ = -(α b (T (c a)) • c b) := by abel
        exact neg_inj.mp h2
      rw [hμ b, hμ a] at h1
      simp only [smul_smul, map_smul, smul_eq_mul] at h1
      have hzero : (α b (c a) * μ b - μ a * α b (c a)) • c b = 0 := by
        rw [sub_smul, h1, sub_self]
      have hscalar : α b (c a) * μ b - μ a * α b (c a) = 0 := by
        by_contra hne
        have hne' : (α b (c a) * μ b - μ a * α b (c a)) • c b ≠ 0 := by
          intro hz
          rw [smul_eq_zero] at hz
          rcases hz with h | h
          · exact hne h
          · exact hc_ne b h
        exact hne' hzero
      have hcomm : α b (c a) * μ b = α b (c a) * μ a := by
        rw [mul_comm (μ a) (α b (c a))] at hscalar
        exact sub_eq_zero.mp hscalar
      exact (mul_left_cancel₀ hba hcomm).symm
    have hμ_const : ∀ i, μ i = μ i₀ := by
      intro i
      have hpath := hconn i₀ i
      induction hpath with
      | refl => rfl
      | tail hab hbc ih =>
          rename_i b d
          exact (hμ_edge b d hbc.1 hbc.2).symm.trans ih
    let μ₀ : K := μ i₀
    have hH : ∀ h ∈ Submodule.span K (Set.range c), T h = μ₀ • h := by
      intro h hh
      apply Submodule.span_induction (p := fun x _ => T x = μ₀ • x) _ _ _ _ hh
      · rintro x ⟨i, rfl⟩
        rw [hμ i, hμ_const i]
      · simp
      · intro x y hx hy ihx ihy
        rw [map_add, ihx, ihy, smul_add]
      · intro a x hx ihx
        rw [map_smul, ihx, smul_smul, smul_smul, mul_comm a μ₀]
    have hxT : ∃ lam : K, T x = lam • x := by
      have hαTx : ∀ i, α i (T x) = 0 := by
        intro i
        have h := hTs i x
        rw [hαx i, zero_smul, sub_zero] at h
        have hzero : α i (T x) • c i = 0 := by
          calc
            α i (T x) • c i = T x - (T x - α i (T x) • c i) := by abel
            _ = T x - T x := by rw [← h]
            _ = 0 := by abel
        by_contra hne
        have hci0 : c i = 0 := by
          rw [smul_eq_zero] at hzero
          rcases hzero with h | h
          · exact absurd h hne
          · exact h
        exact hc_ne i hci0
      obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (hfix (T x) hαTx)
      exact ⟨lam, hlam.symm⟩
    obtain ⟨lam, hlam⟩ := hxT
    have hlam' : T x = lam • x := hlam
    have hc0T : ∃ κ : K, T c₀ = κ • c₀ := by
      have h := hTt c₀
      rw [hfc₀] at h
      have ht : c₀ - (2 : K) • c₀ = - c₀ := by
        rw [two_smul]
        abel
      rw [ht, map_neg] at h
      have h2 : (2 : K) • T c₀ = f (T c₀) • c₀ := by
        calc
          (2 : K) • T c₀ = T c₀ + T c₀ := by rw [two_smul]
          _ = (T c₀ - f (T c₀) • c₀) + f (T c₀) • c₀ + T c₀ := by
            abel
          _ = -T c₀ + f (T c₀) • c₀ + T c₀ := by rw [← h]
          _ = f (T c₀) • c₀ := by abel
      refine ⟨(2 : K)⁻¹ * f (T c₀), ?_⟩
      calc
        T c₀ = (2 : K)⁻¹ • ((2 : K) • T c₀) := by
          rw [smul_smul, inv_mul_cancel₀ two_ne, one_smul]
        _ = (2 : K)⁻¹ • (f (T c₀) • c₀) := by rw [h2]
        _ = ((2 : K)⁻¹ * f (T c₀)) • c₀ := by rw [smul_smul]
    obtain ⟨κ, hκ⟩ := hc0T
    have hc0_mem : c₀ ∈ Submodule.span K (Set.range c) ⊔ Submodule.span K {x} := by
      rw [hsplit]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hc0_mem
    obtain ⟨h, hhH, z, hz, hc0_eq⟩ := hc0_mem
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨a, ha_eq⟩ := hz
    have hc0_eq' : h + a • x = c₀ := by
      rw [ha_eq]
      exact hc0_eq
    have ha_ne : a ≠ 0 := by
      intro ha0
      apply hc₀H
      rw [← hc0_eq', ha0, zero_smul, add_zero]
      exact hhH
    have hh_ne : h ≠ 0 := by
      intro hh0
      apply hc₀x
      rw [← hc0_eq', hh0, zero_add]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
    have hdisj : Submodule.span K (Set.range c) ⊓ Submodule.span K {x} = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvH, hvx⟩ := hv
      rw [Submodule.mem_span_singleton] at hvx
      obtain ⟨b, hb⟩ := hvx
      by_contra hbne
      apply hxH
      have hb0 : b ≠ 0 := by
        intro hb0
        apply hbne
        rw [← hb, hb0, zero_smul]
        exact Submodule.zero_mem _
      have hx_eq : x = b⁻¹ • (b • x) := by
        rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
      rw [hx_eq]
      exact Submodule.smul_mem _ _ (by rw [hb]; exact hvH)
    have hT_c0_1 : T c₀ = μ₀ • h + a • (lam • x) := by
      rw [← hc0_eq', map_add, map_smul, hH h hhH, hlam']
    have hT_c0_2 : T c₀ = κ • h + κ • (a • x) := by
      rw [hκ, ← hc0_eq', smul_add]
    have heq : μ₀ • h + a • (lam • x) = κ • h + κ • (a • x) := by
      rw [← hT_c0_1, ← hT_c0_2]
    have hdiff : (μ₀ - κ) • h = (a * (κ - lam)) • x := by
      have hheq := heq
      rw [smul_smul, smul_smul, mul_comm κ a] at hheq
      have h' : μ₀ • h - κ • h = (a * κ) • x - (a * lam) • x := by
        calc
          μ₀ • h - κ • h = (μ₀ • h + (a * lam) • x) - (κ • h + (a * lam) • x) := by
            abel
          _ = (κ • h + (a * κ) • x) - (κ • h + (a * lam) • x) := by rw [hheq]
          _ = (a * κ) • x - (a * lam) • x := by abel
      rw [← sub_smul] at h'
      rw [← sub_smul] at h'
      rw [← mul_sub] at h'
      exact h'
    have hμκ : μ₀ = κ := by
      have hH_left : (μ₀ - κ) • h ∈ Submodule.span K (Set.range c) :=
        Submodule.smul_mem _ _ hhH
      have hx_right : (a * (κ - lam)) • x ∈ Submodule.span K {x} :=
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
      have hzero : (μ₀ - κ) • h = 0 := by
        have hmem : (μ₀ - κ) • h ∈
            Submodule.span K (Set.range c) ⊓ Submodule.span K {x} := by
          rw [Submodule.mem_inf]
          exact ⟨hH_left, by rw [hdiff]; exact hx_right⟩
        rw [hdisj] at hmem
        exact hmem
      have hsub : μ₀ - κ = 0 := by
        rcases smul_eq_zero.mp hzero with h | h
        · exact h
        · exact absurd h hh_ne
      exact sub_eq_zero.mp hsub
    have hlamκ : lam = κ := by
      have hzero : (a * (κ - lam)) • x = 0 := by
        rw [← hdiff, hμκ, sub_self, zero_smul]
      have hx_ne : x ≠ 0 := by
        intro hx0
        apply hc₀H
        rw [← hc0_eq', hx0, smul_zero, add_zero]
        exact hhH
      have hscalar : a * (κ - lam) = 0 := by
        by_contra hne
        have hne' : (a * (κ - lam)) • x ≠ 0 := by
          intro hz
          rw [smul_eq_zero] at hz
          rcases hz with h | h
          · exact hne h
          · exact hx_ne h
        exact hne' hzero
      have hsub : κ - lam = 0 := by
        rcases mul_eq_zero.mp hscalar with h | h
        · exact absurd h ha_ne
        · exact h
      exact (sub_eq_zero.mp hsub).symm
    refine ⟨μ₀, ?_⟩
    apply LinearMap.ext
    intro v
    have hv : v ∈ Submodule.span K (Set.range c) ⊔ Submodule.span K {x} := by
      rw [hsplit]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hv
    obtain ⟨h', hh', z, hz, hv_eq⟩ := hv
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨b, hb⟩ := hz
    rw [← hv_eq, ← hb]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [map_add, map_smul, hH h' hh', hlam', smul_add, smul_smul, smul_smul, hlamκ, hμκ,
      mul_comm b κ]
  · have hH_bot : Submodule.span K (Set.range c) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, _⟩
      exact (hι ⟨i⟩).elim
    have hx_top : Submodule.span K {x} = ⊤ := by
      simpa [hH_bot] using hsplit
    have hc0_span : c₀ ∈ Submodule.span K {x} := by
      rw [hx_top]
      exact Submodule.mem_top
    exact absurd hc0_span hc₀x

end Linear

theorem ggQ2Mix_isAbsolutelyIrreducible {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V)
    (hinv : ∀ U : Submodule K V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcomm : ∀ T : V →ₗ[K] V, (∀ g, T ∘ₗ ρ g = ρ g ∘ₗ T) → ∃ μ : K, T = μ • LinearMap.id) :
    Theory.Representation.IsAbsolutelyIrreducible ρ := by
  let : _root_.Representation.IsIrreducible ρ :=
    { exists_pair_ne := by
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine ⟨⊤, ⊥, ?_⟩
        intro h
        have hsub : (⊤ : Submodule K V) = ⊥ := by
          have h' := congrArg Subrepresentation.toSubmodule h
          exact h'
        have hmem : v ∈ (⊥ : Submodule K V) := by
          have htop : v ∈ (⊤ : Submodule K V) := Submodule.mem_top
          rwa [hsub] at htop
        exact hv (by simpa using hmem)
      eq_bot_or_eq_top := fun S => by
        have h := hinv S.toSubmodule S.apply_mem_toSubmodule
        rcases h with hbot | htop
        · left
          apply Subrepresentation.toSubmodule_injective
          change S.toSubmodule = (⊥ : Submodule K V)
          exact hbot
        · right
          apply Subrepresentation.toSubmodule_injective
          change S.toSubmodule = (⊤ : Submodule K V)
          exact htop }
  rw [Theory.Representation.isAbsolutelyIrreducible_iff_surjective]
  intro e
  have hcomm_e : ∀ g, e.toLinearMap ∘ₗ ρ g = ρ g ∘ₗ e.toLinearMap := e.isIntertwining'
  obtain ⟨μ, hμ⟩ := hcomm e.toLinearMap hcomm_e
  refine ⟨μ, ?_⟩
  rw [Theory.Representation.End.algebraMap_apply]
  apply _root_.Representation.IntertwiningMap.ext
  rw [_root_.Representation.IntertwiningMap.toLinearMap_smul]
  change μ • LinearMap.id = e.toLinearMap
  rw [hμ]

end CFSG.StandardType

end
