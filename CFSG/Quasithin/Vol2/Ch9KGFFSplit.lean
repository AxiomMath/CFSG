module

public import CFSG.Quasithin.Background.Module
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

@[expose] def modCommOf (K : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup V :=
  Subgroup.closure {w | ∃ k ∈ K, ∃ u ∈ U, k u * u⁻¹ = w}

theorem inf_fixV_eq_bot_of_split (hV : ∀ v : V, v ^ 2 = 1) {L K Q : Subgroup (MulAut V)}
    {h : MulAut V} (hKL : K ≤ L) (hhL : h ∈ L) (h3 : h ^ 3 = 1)
    (hhQ : h ∈ Subgroup.normalizer (Q : Set (MulAut V)))
    (hKQ : K ≤ Subgroup.normalizer (Q : Set (MulAut V)))
    (hhK : ∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ Q)
    (hKP : ∀ x ∈ commV L, (∀ q ∈ Q, q x = x) → h x = x → ∀ k ∈ K, k x * x⁻¹ ∈ fixV L)
    {U₀ : Subgroup V} (hU₀K : U₀ ≤ modCommOf K U₀) (hU₀Q : ∀ q ∈ Q, ∀ u ∈ U₀, q u = u) :
    U₀ ⊓ fixV L = ⊥ := by
  have hfixQ : ∀ g : MulAut V, g ∈ Subgroup.normalizer (Q : Set (MulAut V)) →
      ∀ x : V, (∀ q ∈ Q, q x = x) → ∀ q ∈ Q, q (g x) = g x := by
    intro g hg x hx q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) q).mp hq
      simpa [mul_assoc] using this
    have h1 := hx _ hq'
    have h2 : (g⁻¹ * q * g) x = g⁻¹ (q (g x)) := rfl
    rw [h2] at h1
    calc q (g x) = g (g⁻¹ (q (g x))) := by simp
      _ = g x := by rw [h1]
  have hcomm : ∀ k ∈ K, ∀ x : V, (∀ q ∈ Q, q x = x) → h (k x) = k (h x) := by
    intro k hk x hx
    have hc := hhK k hk
    have hhx : ∀ q ∈ Q, q (h x) = h x := hfixQ h hhQ x hx
    have hkhx : ∀ q ∈ Q, q (k (h x)) = k (h x) := hfixQ k (hKQ hk) (h x) hhx
    have e : h * k = (h * k * h⁻¹ * k⁻¹) * (k * h) := by group
    calc h (k x) = (h * k) x := rfl
      _ = ((h * k * h⁻¹ * k⁻¹) * (k * h)) x := by rw [← e]
      _ = (h * k * h⁻¹ * k⁻¹) (k (h x)) := rfl
      _ = k (h x) := hkhx _ hc
  set ε : V →* V :=
    { toFun := fun x => x * h x * h (h x)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul]
        ac_rfl } with hε
  have hεv : ∀ x : V, ε x = x * h x * h (h x) := fun x => rfl
  have hεfix : ∀ x : V, h x = x → ε x = x := by
    intro x hx
    rw [hεv, hx, hx, mul_assoc, ← sq, hV, mul_one]
  have hh3 : ∀ x : V, h (h (h x)) = x := by
    intro x
    have := congrArg (fun g : MulAut V => g x) h3
    simpa [pow_succ, pow_zero] using this
  have hεh : ∀ x : V, h (ε x) = ε x := by
    intro x
    rw [hεv, map_mul, map_mul, hh3]
    rw [mul_comm (h x * h (h x)) x, mul_assoc]
  have hεk : ∀ k ∈ K, ∀ x : V, (∀ q ∈ Q, q x = x) → ε (k x) = k (ε x) := by
    intro k hk x hx
    have hhx : ∀ q ∈ Q, q (h x) = h x := hfixQ h hhQ x hx
    rw [hεv, hεv, map_mul, map_mul, hcomm k hk x hx, hcomm k hk (h x) hhx]
  set E₀ := U₀.map ε with hE₀
  have hE₀Q : ∀ y ∈ E₀, ∀ q ∈ Q, q y = y := by
    rintro _ ⟨u, hu, rfl⟩ q hq
    have hu' := fun q hq => hU₀Q q hq u hu
    rw [hεv, map_mul, map_mul, hU₀Q q hq u hu, hfixQ h hhQ u hu' q hq,
      hfixQ h hhQ (h u) (hfixQ h hhQ u hu') q hq]
  have hU₀V : U₀ ≤ commV L := by
    refine hU₀K.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨k, hk, u, -, rfl⟩
    exact Subgroup.subset_closure ⟨k, hKL hk, u, rfl⟩
  have hLV : ∀ g ∈ L, ∀ x ∈ commV L, g x ∈ commV L := by
    intro g hg x hx
    refine Subgroup.closure_induction (p := fun x _ => g x ∈ commV L) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨l, hl, w, rfl⟩
      rw [map_mul, map_inv]
      have e : g (l w) * (g w)⁻¹ = ((g * l * g⁻¹) (g w)) * (g w)⁻¹ := by simp
      rw [e]
      exact Subgroup.subset_closure ⟨g * l * g⁻¹, L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg),
        g w, rfl⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact (commV L).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact (commV L).inv_mem ha
  have hE₀W : ∀ y ∈ E₀, y ∈ commV L := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hU₀V hu
    rw [hεv]
    exact (commV L).mul_mem ((commV L).mul_mem h1 (hLV h hhL u h1))
      (hLV h hhL _ (hLV h hhL u h1))
  have hE₀K : E₀ ≤ modCommOf K E₀ := by
    have hmap : U₀.map ε ≤ (modCommOf K U₀).map ε := Subgroup.map_mono hU₀K
    refine hmap.trans ?_
    rw [modCommOf, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨_, ⟨k, hk, u, hu, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨k, hk, ε u, ⟨u, hu, rfl⟩, ?_⟩
    rw [map_mul, map_inv, hεk k hk u (fun q hq => hU₀Q q hq u hu)]
  have hE₀Z : modCommOf K E₀ ≤ fixV L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, y, hy, rfl⟩
    exact hKP y (hE₀W y hy) (hE₀Q y hy) (by
      obtain ⟨u, -, rfl⟩ := hy
      exact hεh u) k hk
  have hE₀bot : E₀ = ⊥ := by
    refine eq_bot_iff.mpr (hE₀K.trans ?_)
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, y, hy, rfl⟩
    have hyZ : y ∈ fixV L := hE₀Z (hE₀K hy)
    rw [mem_fixV.mp hyZ k (hKL hk), mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [eq_bot_iff]
  rintro v ⟨hvU, hvZ⟩
  have h1 : ε v ∈ E₀ := ⟨v, hvU, rfl⟩
  rw [hE₀bot, Subgroup.mem_bot, hεfix v (mem_fixV.mp hvZ h hhL)] at h1
  exact h1

end CFSG.Quasithin.H13.Ch9.KGFF
