module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDict
public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {G : Type} [Group G]

theorem mk_eq_iff_mem {L X : Subgroup G} [(L.subgroupOf X).Normal] {y z : ↥X} :
    (QuotientGroup.mk y : ↥X ⧸ L.subgroupOf X) = QuotientGroup.mk z ↔
      (z : G) * (y : G)⁻¹ ∈ L := by
  rw [QuotientGroup.eq]
  have hn : (L.subgroupOf X).Normal := inferInstance
  constructor
  · intro h
    have := hn.mem_comm h
    simpa [Subgroup.mem_subgroupOf] using this
  · intro h
    have h' : z * y⁻¹ ∈ L.subgroupOf X := by
      simpa [Subgroup.mem_subgroupOf] using h
    exact hn.mem_comm h'

theorem IsModelSec.relIndex_eq {n : ℕ} {M : Model n} {F L X : Subgroup G}
    (h : IsModelSec M F L X) : L.relIndex X = Nat.card M.W := by
  obtain ⟨hn, θ, β, -, -, hsd⟩ := h
  exact hsd.relIndex_eq

theorem IsOrthSec.relIndex_eq {F L X : Subgroup G} (h : IsOrthSec F L X) : L.relIndex X = 16 := by
  rw [IsModelSec.relIndex_eq h, card_orth]

theorem IsNatSec.relIndex_eq {F L X : Subgroup G} (h : IsNatSec F L X) : L.relIndex X = 16 := by
  rw [IsModelSec.relIndex_eq h, card_nat]

theorem IsNat3Sec.relIndex_eq {F L X : Subgroup G} (h : IsNat3Sec F L X) : L.relIndex X = 4 := by
  rw [IsModelSec.relIndex_eq h, card_nat3]

theorem IsModelSec.irred_of {n : ℕ} {M : Model n} {F L X : Subgroup G} (h : IsModelSec M F L X)
    (hirr : ∀ Y : Subgroup M.W, (∀ σ : Perm (Fin n), ∀ y ∈ Y, M.act σ y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    {N : Subgroup G} (hLN : L ≤ N) (hNX : N ≤ X) (hF : F ≤ Subgroup.normalizer (N : Set G)) :
    N = L ∨ N = X := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  have hinv : ∀ k ∈ F, ∀ u ∈ N, k * u * k⁻¹ ∈ N := fun k hk u hu =>
    ((Subgroup.mem_normalizer_iff.mp (hF hk)) u).mp hu
  obtain ⟨Y, hY, hYm⟩ := (hsd.invariant_iff hθs hLN hNX).mp hinv
  have hLX : L ≤ X := hLN.trans hNX
  rcases hirr Y hY with rfl | rfl
  · left
    refine le_antisymm (fun u hu => ?_) hLN
    have hu' : (QuotientGroup.mk' (L.subgroupOf X)) ⟨u, hNX hu⟩ ∈
        (N.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) :=
      ⟨⟨u, hNX hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [← hYm, Subgroup.map_bot, Subgroup.mem_bot] at hu'
    have := (QuotientGroup.eq_one_iff _).mp hu'
    exact Subgroup.mem_subgroupOf.mp this
  · right
    refine le_antisymm hNX (fun x hx => ?_)
    have hx' : (QuotientGroup.mk (⟨x, hx⟩ : ↥X) : ↥X ⧸ L.subgroupOf X) ∈
        (N.subgroupOf X).map (QuotientGroup.mk' (L.subgroupOf X)) := by
      rw [← hYm, Subgroup.map_top_of_surjective _ hsd.surj]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hx'
    have h1 : (x : G) * (c : G)⁻¹ ∈ L := mk_eq_iff_mem.mp hcx
    have h2 : x = (x * (c : G)⁻¹) * (c : G) := by group
    rw [h2]
    exact N.mul_mem (hLN h1) (Subgroup.mem_subgroupOf.mp hc)

theorem IsNatSec.irred {F L X : Subgroup G} (h : IsNatSec F L X) :
    ∀ N : Subgroup G, L ≤ N → N ≤ X → F ≤ Subgroup.normalizer (N : Set G) → N = L ∨ N = X :=
  fun _ hLN hNX hF => IsModelSec.irred_of h irreducible_nat hLN hNX hF

theorem IsOrthSec.irred {F L X : Subgroup G} (h : IsOrthSec F L X) :
    ∀ N : Subgroup G, L ≤ N → N ≤ X → F ≤ Subgroup.normalizer (N : Set G) → N = L ∨ N = X :=
  fun _ hLN hNX hF => IsModelSec.irred_of h irreducible_orth hLN hNX hF

private theorem nat_fix_three : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 3 = 1 →
    ∀ w : nat.W, nat.act σ w = w → w = 1 := by decide +kernel

private theorem orth_fix_three : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 3 = 1 →
    ∃ w : orth.W, w ≠ 1 ∧ orth.act σ w = w := by decide +kernel

private theorem image_order_three {n : ℕ} {F L X : Subgroup G} {θ : ↥F →* Perm (Fin n)}
    (hk : θ.ker = (cSecIn F L X).subgroupOf F) {d : G} (hd : d ∈ F) (hd1 : d ∉ cSecIn F L X)
    (hd3 : d ^ 3 ∈ cSecIn F L X) : θ ⟨d, hd⟩ ≠ 1 ∧ θ ⟨d, hd⟩ ^ 3 = 1 := by
  refine ⟨fun h => hd1 ((mem_cSecIn_iff_of_ker hk hd).mp h), ?_⟩
  have h3 : θ ⟨d ^ 3, F.pow_mem hd 3⟩ = 1 := (mem_cSecIn_iff_of_ker hk (F.pow_mem hd 3)).mpr hd3
  rw [← map_pow]
  exact h3

theorem IsNatSec.no_fixed_of_three {F L X : Subgroup G} (h : IsNatSec F L X) {d : G} (hd : d ∈ F)
    (hd1 : d ∉ cSecIn F L X) (hd3 : d ^ 3 ∈ cSecIn F L X) :
    ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ L → x ∈ L := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨hσ1, hσ3⟩ := image_order_three hθk hd hd1 hd3
  intro x hx hcomm
  obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
  obtain ⟨hdx, h1⟩ := hsd.equiv ⟨d, hd⟩ u ⟨x, hx⟩ hu
  have h2 : β (nat.act (θ ⟨d, hd⟩) u) = β u := by
    rw [h1, hu]
    refine mk_eq_iff_mem.mpr ?_
    have e : (x : G) * (d * x * d⁻¹)⁻¹ = (d * x * d⁻¹ * x⁻¹)⁻¹ := by group
    show x * (d * x * d⁻¹)⁻¹ ∈ L
    rw [e]
    exact L.inv_mem hcomm
  have h3 := hsd.inj h2
  have h4 : u = 1 := nat_fix_three _ hσ1 hσ3 u h3
  rw [h4, map_one] at hu
  have := (QuotientGroup.eq_one_iff _).mp hu.symm
  exact Subgroup.mem_subgroupOf.mp this

theorem IsOrthSec.exists_fixed_of_three {F L X : Subgroup G} (h : IsOrthSec F L X) {d : G}
    (hd : d ∈ F) (hd1 : d ∉ cSecIn F L X) (hd3 : d ^ 3 ∈ cSecIn F L X) :
    ∃ x ∈ X, x ∉ L ∧ d * x * d⁻¹ * x⁻¹ ∈ L := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  obtain ⟨hσ1, hσ3⟩ := image_order_three hθk hd hd1 hd3
  obtain ⟨w, hw1, hw⟩ := orth_fix_three _ hσ1 hσ3
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β w)
  refine ⟨(x : G), x.2, fun hxL => hw1 ?_, ?_⟩
  · apply hsd.inj
    rw [map_one, ← hx]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxL)
  · obtain ⟨hdx, h1⟩ := hsd.equiv ⟨d, hd⟩ w x hx.symm
    rw [hw, ← hx] at h1
    have := mk_eq_iff_mem.mp h1
    simpa using this

theorem not_isOrthSec_and_isNatSec {F L X : Subgroup G} (ho : IsOrthSec F L X)
    (hn : IsNatSec F L X) : False := by
  obtain ⟨θ, hθs, hθk⟩ : ∃ θ : ↥F →* Perm (Fin 5), Function.Surjective θ ∧
      θ.ker = (cSecIn F L X).subgroupOf F := by
    obtain ⟨-, θ, -, hθs, hθk, -⟩ := ho
    exact ⟨θ, hθs, hθk⟩
  obtain ⟨d, hd⟩ := hθs (Equiv.swap 0 1 * Equiv.swap 1 2)
  have hd1 : d.1 ∉ cSecIn F L X := fun hmem => by
    have := (mem_cSecIn_iff_of_ker hθk d.2).mpr hmem
    rw [show (⟨d.1, d.2⟩ : ↥F) = d from rfl, hd] at this
    exact absurd this (by decide +kernel)
  have hd3 : d.1 ^ 3 ∈ cSecIn F L X := by
    have h3 : θ (d ^ 3) = 1 := by rw [map_pow, hd]; decide +kernel
    exact (mem_cSecIn_iff_of_ker hθk (F.pow_mem d.2 3)).mp h3
  obtain ⟨x, hx, hxL, hcomm⟩ := ho.exists_fixed_of_three d.2 hd1 hd3
  exact hxL (hn.no_fixed_of_three d.2 hd1 hd3 x hx hcomm)

def commHom {n : ℕ} (M : Model n) (σ : Perm (Fin n)) : M.W →* M.W where
  toFun w := M.act σ w * w⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm v⁻¹ u⁻¹, mul_mul_mul_comm]

theorem ker_commHom {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    (commHom M σ).ker = fixW M (Subgroup.zpowers σ) := by
  ext w
  rw [MonoidHom.mem_ker, mem_fixW_zpowers]
  show M.act σ w * w⁻¹ = 1 ↔ _
  exact mul_inv_eq_one

theorem range_commHom {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    (commHom M σ).range = commW M (Subgroup.zpowers σ) ⊤ := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact Subgroup.subset_closure ⟨σ, Subgroup.mem_zpowers σ, w, Subgroup.mem_top _, rfl⟩
  · unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, u, -, rfl⟩
    have key : ∀ b ∈ Subgroup.zpowers σ, ∀ u : M.W, M.act b u * u⁻¹ ∈ (commHom M σ).range := by
      intro b hb
      rw [Subgroup.zpowers_eq_closure] at hb
      induction hb using Subgroup.closure_induction with
      | mem x hx =>
        intro u
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨u, rfl⟩
      | one => intro u; simp
      | mul x y _ _ hx hy =>
        intro u
        have e : M.act (x * y) u * u⁻¹ =
            (M.act x (M.act y u) * (M.act y u)⁻¹) * (M.act y u * u⁻¹) := by
          rw [act_mul_apply]; group
        rw [e]
        exact Subgroup.mul_mem _ (hx _) (hy u)
      | inv x _ hx =>
        intro u
        have e : M.act x⁻¹ u * u⁻¹ = (M.act x (M.act x⁻¹ u) * (M.act x⁻¹ u)⁻¹)⁻¹ := by
          rw [act_act_inv]; group
        rw [e]
        exact Subgroup.inv_mem _ (hx _)
    exact key b hb u

theorem card_commW_zpowers_mul {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    Nat.card (commW M (Subgroup.zpowers σ) ⊤) * Nat.card (fixW M (Subgroup.zpowers σ)) =
      Nat.card M.W := by
  rw [← range_commHom, ← ker_commHom, ← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index]

theorem map_zpowers_subgroupOf {K : Subgroup G} {H : Type*} [Group H] (Ψ : ↥K →* H) {a : G}
    (ha : a ∈ K) : ((Subgroup.zpowers a).subgroupOf K).map Ψ = Subgroup.zpowers (Ψ ⟨a, ha⟩) := by
  have : (Subgroup.zpowers a).subgroupOf K = Subgroup.zpowers (⟨a, ha⟩ : ↥K) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp⟩
  rw [this, MonoidHom.map_zpowers]

theorem IsNatSec.involution {F L X : Subgroup G} (h : IsNatSec F L X) (hLX : L ≤ X) {a : G}
    (ha : a ∈ F) (ha1 : a ∉ cSecIn F L X) (ha2 : a ^ 2 ∈ cSecIn F L X) :
    secIdx (Subgroup.zpowers a) L X = 4 ∧ L.relIndex (commSec (Subgroup.zpowers a) L X) = 4 := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  have hσ1 : θ ⟨a, ha⟩ ≠ 1 := fun h1 => ha1 ((mem_cSecIn_iff_of_ker hθk ha).mp h1)
  have hσ2 : θ ⟨a, ha⟩ ^ 2 = 1 := by
    rw [← map_pow]
    exact (mem_cSecIn_iff_of_ker hθk (F.pow_mem ha 2)).mpr ha2
  have hidx : idx nat (θ ⟨a, ha⟩) = 4 := by
    rw [idx_nat]; simp [hσ1, hσ2]
  have hle : Subgroup.zpowers a ≤ F := (Subgroup.zpowers_le).mpr ha
  refine ⟨?_, ?_⟩
  · rw [hsd.secIdx_eq_idx hLX ha, hidx]
  · rw [hsd.card_commSec hLX hle, map_zpowers_subgroupOf θ ha]
    have h1 := card_commW_zpowers_mul nat (θ ⟨a, ha⟩)
    have h2 := idx_mul_card nat (θ ⟨a, ha⟩)
    rw [← card_fixW_zpowers, hidx] at h2
    rw [card_nat] at h1 h2
    have hf : Nat.card (fixW nat (Subgroup.zpowers (θ ⟨a, ha⟩))) = 4 := by omega
    rw [hf] at h1
    omega

end CFSG.Quasithin.F53Mod
