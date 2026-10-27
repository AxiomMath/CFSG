module

public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.OuterAutomorphisms

section NoOddNormal

variable {Y : Type*} [Group Y]

@[expose] def NoOddNormal (K : Subgroup Y) : Prop :=
  ∀ N : Subgroup Y, N ≤ K → (∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N) → Odd (Nat.card N) → N = ⊥

theorem noOddNormal_of_oddCore {K : Subgroup Y} (h : CFSG.oddCore K = ⊥) : NoOddNormal K := by
  intro N hNK hnorm hodd
  have hN'n : (N.subgroupOf K).Normal := ⟨fun x hx k => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hnorm k k.2 x hx⟩
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ CFSG.oddCore K := le_sSup ⟨hN'n, hcard ▸ hodd⟩
  rw [h, le_bot_iff] at hle
  have hmap := Subgroup.subgroupOf_map_subtype N K
  rw [hle, Subgroup.map_bot, inf_eq_left.2 hNK] at hmap
  exact hmap.symm

theorem oddCore_eq_bot_of_noOddNormal {K : Subgroup Y} (h : NoOddNormal K) :
    CFSG.oddCore K = ⊥ :=
  sSup_eq_bot.2 fun N' hN' => by
    have := hN'.1
    have hmap := h (N'.map K.subtype) (Subgroup.map_subtype_le N') (fun k hk x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y hy _, rfl⟩)
      (by rw [Subgroup.card_map_of_injective K.subtype_injective]; exact hN'.2)
    exact (Subgroup.map_eq_bot_iff_of_injective N' K.subtype_injective).1 hmap

theorem NoOddNormal.map {Y' : Type*} [Group Y'] {f : Y →* Y'} (hf : Function.Injective f)
    {K : Subgroup Y} (h : NoOddNormal K) : NoOddNormal (K.map f) := by
  intro N hN hnorm hodd
  have hNrange : N ≤ f.range := hN.trans (Subgroup.map_le_range f K)
  have hmapcomap : (N.comap f).map f = N := Subgroup.map_comap_eq_self hNrange
  have hc := h (N.comap f) (fun x hx => by
      obtain ⟨k, hk, hkx⟩ := hN hx
      rwa [← hf hkx])
    (fun k hk x hx => by
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv]
      exact hnorm (f k) ⟨k, hk, rfl⟩ (f x) hx)
    (by rw [← Subgroup.card_map_of_injective hf, hmapcomap]; exact hodd)
  rw [← hmapcomap, hc, Subgroup.map_bot]

end NoOddNormal

section Maps

variable {X : Type*} [Group X] {G : Type*} [Group G]

theorem map_centralizer_eq (S : Subgroup X) (ψ : S ≃* G) (t : X) (ht : t ∈ S) :
    (Subgroup.centralizer ({ψ ⟨t, ht⟩} : Set G)).map (S.subtype.comp ψ.symm.toMonoidHom) =
      S ⊓ Subgroup.centralizer ({t} : Set X) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MonoidHom.coe_comp,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, Function.comp_apply, Subgroup.mem_inf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(ψ.symm g).2, ?_⟩
    have h := congrArg ψ.symm hg
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val h
  · rintro ⟨hx, hxt⟩
    refine ⟨ψ ⟨x, hx⟩, ?_, by simp⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hxt)

theorem map_fixSub_eq (S : Subgroup X) [S.Normal] (ψ : S ≃* G) (t : X) :
    (fixSub (MulAut.congr ψ (MulAut.conjNormal t))).map (S.subtype.comp ψ.symm.toMonoidHom) =
      S ⊓ Subgroup.centralizer ({t} : Set X) := by
  have happ : ∀ g : G, (MulAut.congr ψ (MulAut.conjNormal t)) g =
      ψ (MulAut.conjNormal t (ψ.symm g)) := fun _ => rfl
  ext x
  simp only [Subgroup.mem_map, mem_fixSub, MonoidHom.coe_comp, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, happ]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(ψ.symm g).2, ?_⟩
    have h := congrArg (fun z => ((ψ.symm z : S) : X)) hg
    simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h
    calc ((ψ.symm g : S) : X) * t = t * ((ψ.symm g : S) : X) * t⁻¹ * t := by rw [h]
      _ = t * ((ψ.symm g : S) : X) := by group
  · rintro ⟨hx, hxt⟩
    refine ⟨ψ ⟨x, hx⟩, ?_, by simp⟩
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hxt]
      _ = x := by group

end Maps

section Normal

variable {X : Type*} [Group X] [Finite X]

theorem mem_of_odd_orderOf (S : Subgroup X) [S.Normal] (hX : Nat.card X ≤ 2 * Nat.card S)
    {x : X} (hx : Odd (orderOf x)) : x ∈ S := by
  have hq : Nat.card (X ⧸ S) ≤ 2 := by
    have h := S.card_eq_card_quotient_mul_card_subgroup
    have hS : 0 < Nat.card S := Nat.card_pos
    by_contra hlt
    rw [not_le] at hlt
    have : 3 * Nat.card S ≤ Nat.card (X ⧸ S) * Nat.card S := Nat.mul_le_mul_right _ hlt
    omega
  have hdvd : orderOf (QuotientGroup.mk' S x) ∣ orderOf x := orderOf_map_dvd _ x
  have hodd : Odd (orderOf (QuotientGroup.mk' S x)) := Odd.of_dvd_nat hx hdvd
  have hle : orderOf (QuotientGroup.mk' S x) ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)).trans hq
  have h1 : orderOf (QuotientGroup.mk' S x) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem le_of_odd_card (S : Subgroup X) [S.Normal] (hX : Nat.card X ≤ 2 * Nat.card S)
    (N : Subgroup X) (hodd : Odd (Nat.card N)) : N ≤ S := fun x hx => by
  refine mem_of_odd_orderOf S hX (Odd.of_dvd_nat hodd ?_)
  have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
  rwa [Subgroup.orderOf_mk] at this

variable {G : Type*} [Group G]

theorem oddCore_centralizer_eq_bot_of_normal [Finite G]
    (hF1 : ∀ t : G, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (hF2 : Nat.card (MulAut G) ≤ 2 * Nat.card G)
    (hF3 : ∀ α : MulAut G, α * α = 1 → α ∉ inner G → CFSG.oddCore (fixSub α) = ⊥)
    (S : Subgroup X) [S.Normal] (ψ : S ≃* G)
    (hC : Subgroup.centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  set φ : X →* MulAut S := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro s hs
    have h := congrArg (fun β : MulAut S => ((β ⟨s, hs⟩ : S) : X)) (MonoidHom.mem_ker.1 hx)
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc s * x = x * s * x⁻¹ * x := by rw [h]
      _ = x * s := by group
  have hX : Nat.card X ≤ 2 * Nat.card S := by
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv] at h1
    rw [Nat.card_congr ψ.toEquiv]
    exact h1.trans hF2
  set f : G →* X := S.subtype.comp ψ.symm.toMonoidHom
  have hf : Function.Injective f := S.subtype_injective.comp ψ.symm.injective
  apply oddCore_eq_bot_of_noOddNormal
  intro N hNC hnorm hodd
  have hNS : N ≤ S := le_of_odd_card S hX N hodd
  have key : NoOddNormal (S ⊓ Subgroup.centralizer ({t} : Set X)) := by
    by_cases htS : t ∈ S
    · have h := hF1 (ψ ⟨t, htS⟩) (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ht)
      rw [← map_centralizer_eq S ψ t htS]
      exact (noOddNormal_of_oddCore h).map hf
    · have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
      have hα2 : MulAut.congr ψ (φ t) * MulAut.congr ψ (φ t) = 1 := by
        rw [← map_mul, ← map_mul, ht2, map_one, map_one]
      have hα : MulAut.congr ψ (φ t) ∉ inner G := by
        rintro ⟨g, hg⟩
        apply htS
        have h1 : φ t = MulAut.conj (ψ.symm g) := by
          apply (MulAut.congr ψ).injective
          rw [congr_conj, MulEquiv.apply_symm_apply]
          exact hg.symm
        have h2 : φ ((ψ.symm g : S) : X) = MulAut.conj (ψ.symm g) := by
          ext h
          simp [φ, MulAut.conjNormal_apply]
        rw [hφ (h1.trans h2.symm)]
        exact (ψ.symm g).2
      have h := hF3 _ hα2 hα
      rw [← map_fixSub_eq S ψ t]
      exact (noOddNormal_of_oddCore h).map hf
  exact key N (le_inf hNS hNC) (fun k hk x hx => hnorm k (Subgroup.mem_inf.1 hk).2 x hx)
    hodd

end Normal

theorem inner_eq_top_of_card_le {G : Type*} [Group G] [Finite G]
    (hc : Subgroup.center G = ⊥) (h : Nat.card (MulAut G) ≤ Nat.card G) : inner G = ⊤ := by
  have hfin : Finite (MulAut G) :=
    Finite.of_injective (fun α : MulAut G => (α : G → G)) DFunLike.coe_injective
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm (Subgroup.card_le_card_group _)
  rw [card_inner_of_center_eq_bot hc]
  exact h

theorem outer_vacuous_of_card_le {G : Type*} [Group G] [Finite G]
    (hc : Subgroup.center G = ⊥) (h : Nat.card (MulAut G) ≤ Nat.card G) (α : MulAut G)
    (hα : α ∉ inner G) : False :=
  hα (by rw [inner_eq_top_of_card_le hc h]; trivial)

theorem evalW_commutator {M : Type*} [Group M] (x y : M) :
    evalW x y [0, 1, 2, 3] = x * y * x⁻¹ * y⁻¹ := by
  simp [evalW, letterW, mul_assoc]

end CFSG.Sporadic.Schreier
