module

public import CFSG.Quasithin.Background.FLcP0Base
public import CFSG.Quasithin.Background.FLcLn

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

theorem isPGroup_two_of_forall {H : Subgroup G} (h : ∀ x ∈ H, ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    IsPGroup 2 ↥H := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := h x hx
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem exists_pow_mem_of_normalizes {L S : Subgroup G}
    (hn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) {l s : G} (hl : l ∈ L) (hs : s ∈ S) (m : ℕ) :
    ∃ l' ∈ L, (l * s) ^ m = l' * s ^ m := by
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', hm⟩ := ih
    have hsm : s ^ m ∈ S := S.pow_mem hs m
    refine ⟨l' * (s ^ m * l * (s ^ m)⁻¹), L.mul_mem hl' (hn _ hsm l hl), ?_⟩
    have key : ∀ t : G, l' * t * (l * s) = (l' * (t * l * t⁻¹)) * (t * s) := fun t => by group
    rw [pow_succ, hm, pow_succ, key]

theorem exists_pow_mul_of_normal {H N : Subgroup G} (hN : ∀ x ∈ H, ∀ k ∈ N, x * k * x⁻¹ ∈ N)
    {l c : G} (hl : l ∈ H) (hc : c ∈ N) (m : ℕ) : ∃ c' ∈ N, (l * c) ^ m = l ^ m * c' := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨c', hc', hm⟩ := ih
    refine ⟨(l⁻¹ * c' * l) * c, N.mul_mem ?_ hc, ?_⟩
    · have := hN l⁻¹ (H.inv_mem hl) c' hc'
      simpa using this
    · rw [pow_succ, hm, pow_succ]
      group

theorem kc_facts [Finite G] {L S UL : Subgroup G} (hSLn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (hS2 : IsPGroup 2 S) (hLU : L ≤ Subgroup.normalizer (UL : Set G))
    (hSU : S ≤ Subgroup.normalizer (UL : Set G))
    (hK : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (UL : Set G))) :
    IsPGroup 2 ↥(Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S)) ∧
      ∀ x ∈ L ⊔ S, ∀ k ∈ Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S),
        x * k * x⁻¹ ∈ Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S) := by
  constructor
  · refine isPGroup_two_of_forall fun k hk => ?_
    obtain ⟨l, hl, s, hs, rfl⟩ := mem_sup_prod_of_conj hSLn k hk.2
    obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
    have hsa : s ^ (2 ^ a) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    obtain ⟨l', hl', hm⟩ := exists_pow_mem_of_normalizes hSLn hl hs (2 ^ a)
    rw [hsa, mul_one] at hm
    have hzC : (l * s) ^ (2 ^ a) ∈ Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S) :=
      Subgroup.pow_mem _ hk _
    rw [hm] at hzC
    obtain ⟨b, hb⟩ := hK ⟨l', hl', hzC.1⟩
    have hb' : l' ^ (2 ^ b) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    refine ⟨a + b, ?_⟩
    rw [pow_add, pow_mul, hm, hb']
  · intro x hx k hk
    refine Subgroup.mem_inf.2 ⟨?_, (L ⊔ S).mul_mem ((L ⊔ S).mul_mem hx hk.2) ((L ⊔ S).inv_mem hx)⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hxU : x⁻¹ * u * x ∈ UL := by
      have := (Subgroup.mem_normalizer_iff.1 ((sup_le hLU hSU : L ⊔ S ≤ _) ((L ⊔ S).inv_mem hx)) u).1 hu
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hk.1 _ hxU
    calc u * (x * k * x⁻¹) = x * ((x⁻¹ * u * x) * k) * x⁻¹ := by group
      _ = x * (k * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
      _ = x * k * x⁻¹ * u := by group

theorem exists_dec {L S UL : Subgroup G} {n : ℕ} (α : ↥L →* SLt n)
    (β : ↥UL ≃* Multiplicative (Vt n)) (hαs : Function.Surjective α)
    (hLU : L ≤ Subgroup.normalizer (UL : Set G)) (hSU : S ≤ Subgroup.normalizer (UL : Set G))
    (hSLn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (hrel : ∀ (a : ↥L) (u v : ↥UL), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = mat (α a) *ᵥ Multiplicative.toAdd (β u))
    {x : G} (hx : x ∈ L ⊔ S) :
    ∃ (l : ↥L) (c : G), c ∈ Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S) ∧ x = (l : G) * c := by
  obtain ⟨l', hl', s, hs, rfl⟩ := mem_sup_prod_of_conj hSLn x hx
  obtain ⟨ls, hls⟩ := exists_inner_of_normalizes α β hαs hLU hrel (hSU hs)
  refine ⟨⟨l' * (ls : G), L.mul_mem hl' ls.2⟩, (ls : G)⁻¹ * s, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hls ⟨u, hu⟩
    have h2 : s * u * s⁻¹ = (ls : G) * u * (ls : G)⁻¹ := h1
    calc u * ((ls : G)⁻¹ * s) = (ls : G)⁻¹ * ((ls : G) * u * (ls : G)⁻¹) * s := by group
      _ = (ls : G)⁻¹ * (s * u * s⁻¹) * s := by rw [h2]
      _ = (ls : G)⁻¹ * s * u := by group
  · exact (L ⊔ S).mul_mem ((L ⊔ S).inv_mem ((le_sup_left : L ≤ L ⊔ S) ls.2))
      ((le_sup_right : S ≤ L ⊔ S) hs)
  · show l' * s = l' * (ls : G) * ((ls : G)⁻¹ * s)
    group

end CFSG.Quasithin.FLc
