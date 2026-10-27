module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCNeg

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {m : ℕ}
  {V VT : Type} [Group V] [Group VT]

theorem qTwoLMFrameC_direct_pos (F : QTwoFrame m V VT Bs L x)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L, ∃ k : ℕ, b = t * x ^ k)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    {r : MulAut ↥Bs} (hrx : r ⟨x, F.hx⟩ = ⟨x, F.hx⟩) (π : Equiv.Perm (Fin m))
    (hr : ∀ v : VT, ((r ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
      ((F.thetaT (F.permVT π v) : ↥(Bs ⊓ L)) : G)) :
    r ∈ ggAutomizer L Bs := by
  obtain ⟨n, hnBs, hn⟩ := F.indT π
  rw [mem_ggAutomizer_iff]
  refine ⟨(n : G), n.2, hnBs, fun b => ?_⟩
  obtain ⟨t, ht, k, hb⟩ := hsplit (b : G) b.2
  set v : VT := F.thetaT.symm ⟨t, ht⟩ with hv
  have hθ : F.thetaT v = ⟨t, ht⟩ := by
    rw [hv]
    exact F.thetaT.apply_symm_apply ⟨t, ht⟩
  have htcoe : ((F.thetaT v : ↥(Bs ⊓ L)) : G) = t := by rw [hθ]
  have hcx : (n : G) * x ^ k * (n : G)⁻¹ = x ^ k := by
    have hxcomm : x * (n : G) = (n : G) * x :=
      Subgroup.mem_centralizer_iff.mp (hLx n.2) x (Set.mem_singleton x)
    have hc : Commute (n : G) x := hxcomm.symm
    rw [show (n : G) * x ^ k = x ^ k * (n : G) from hc.pow_right k]
    group
  have hb_eq : b = (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) *
      ⟨x, F.hx⟩ ^ k := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hb, htcoe]
  have hleft : ((r b : ↥Bs) : G) =
      ((F.thetaT (F.permVT π v) : ↥(Bs ⊓ L)) : G) * x ^ k := by
    rw [hb_eq, map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, hrx, hr v]
  have hright : (n : G) * (b : G) * (n : G)⁻¹ =
      ((F.thetaT (F.permVT π v) : ↥(Bs ⊓ L)) : G) * x ^ k := by
    rw [hb, ← htcoe]
    rw [show (n : G) * (((F.thetaT v : ↥(Bs ⊓ L)) : G) * x ^ k) * (n : G)⁻¹
        = ((n : G) * ((F.thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹) *
          ((n : G) * x ^ k * (n : G)⁻¹) by group]
    rw [hn v, hcx]
  exact hleft.trans hright.symm

theorem qTwoLMFrameC_fix_card_le (F : QTwoFrame m V VT Bs L x)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L, ∃ k : ℕ, b = t * x ^ k) (hord : orderOf x = 3)
    {r : MulAut ↥Bs} (hrx : r ⟨x, F.hx⟩ = ⟨x, F.hx⟩) (ψ : VT → VT)
    (hr : ∀ v : VT, ((r ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
      ((F.thetaT (ψ v) : ↥(Bs ⊓ L)) : G)) :
    Nat.card {b : ↥Bs // r b = b} ≤ 3 * Nat.card {v : VT // ψ v = v} := by
  haveI : Finite ↥(Bs ⊓ L) := Subtype.finite
  haveI : Finite VT :=
    Finite.of_injective (F.thetaT : VT → ↥(Bs ⊓ L)) F.thetaT.injective
  let f : {v : VT // ψ v = v} × Fin 3 → ↥Bs := fun p =>
    ⟨((F.thetaT p.1.1 : ↥(Bs ⊓ L)) : G) * x ^ (p.2 : ℕ),
      Bs.mul_mem (F.thetaT p.1.1).2.1 (Bs.pow_mem F.hx (p.2 : ℕ))⟩
  have hf_mem : ∀ p, r (f p) = f p := by
    rintro ⟨⟨v, hv⟩, k⟩
    have hfa : f (⟨⟨v, hv⟩, k⟩) =
        (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) *
          ⟨x, F.hx⟩ ^ (k : ℕ) := by
      apply Subtype.ext
      show ((F.thetaT v : ↥(Bs ⊓ L)) : G) * x ^ (k : ℕ)
        = (((⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs)
            * ⟨x, F.hx⟩ ^ (k : ℕ) : ↥Bs) : G)
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
    rw [hfa, map_mul, map_pow, hrx]
    rw [show r (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) =
        ⟨((F.thetaT (ψ v) : ↥(Bs ⊓ L)) : G), (F.thetaT (ψ v)).2.1⟩ from
      Subtype.ext (hr v)]
    rw [hv]
  let Φ : {v : VT // ψ v = v} × Fin 3 → {b : ↥Bs // r b = b} := fun p => ⟨f p, hf_mem p⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨b, hb⟩
    obtain ⟨t, ht, k, hbt⟩ := hsplit (b : G) b.2
    set v : VT := F.thetaT.symm ⟨t, ht⟩ with hv
    have hθ : F.thetaT v = ⟨t, ht⟩ := by
      rw [hv]
      exact F.thetaT.apply_symm_apply ⟨t, ht⟩
    have htcoe : ((F.thetaT v : ↥(Bs ⊓ L)) : G) = t := by rw [hθ]
    have hb_eq : b = (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) *
        ⟨x, F.hx⟩ ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, hbt, htcoe]
    have hra : r (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) =
        (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) := by
      have hcoeeq : ((r (⟨((F.thetaT v : ↥(Bs ⊓ L)) : G),
              (F.thetaT v).2.1⟩ : ↥Bs) : ↥Bs) : G) * x ^ k
          = ((⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) * x ^ k := by
        have hcong := congrArg (fun z : ↥Bs => (z : G)) hb
        rw [hb_eq] at hcong
        rw [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, hrx] at hcong
        exact hcong
      exact Subtype.ext (mul_right_cancel hcoeeq)
    have hψv : ψ v = v := by
      apply F.thetaT.injective
      apply Subtype.ext
      rw [← hr v]
      exact congrArg (fun z : ↥Bs => (z : G)) hra
    have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
    have hfb : f (⟨⟨v, hψv⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩⟩) = b := by
      apply Subtype.ext
      change ((F.thetaT v : ↥(Bs ⊓ L)) : G) * x ^ (k % 3) = (b : G)
      rw [hb_eq, Subgroup.coe_mul, Subgroup.coe_pow]
      rw [pow_eq_pow_mod k hx3]
    exact ⟨(⟨v, hψv⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext hfb⟩
  have hcard : Nat.card ({v : VT // ψ v = v} × Fin 3)
      = Nat.card {v : VT // ψ v = v} * 3 := by
    rw [Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  calc Nat.card {b : ↥Bs // r b = b}
      ≤ Nat.card ({v : VT // ψ v = v} × Fin 3) := Nat.card_le_card_of_surjective Φ hsurj
    _ = Nat.card {v : VT // ψ v = v} * 3 := hcard
    _ = 3 * Nat.card {v : VT // ψ v = v} := Nat.mul_comm _ 3

theorem qTwoLMFrameC_direct_neg (F : QTwoFrame m V VT Bs L x) (hm5 : 5 ≤ m)
    (hVT : IsAugModel m VT F.permVT) (hcard : Nat.card ↥Bs = 3 ^ m)
    (hsplit : ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L, ∃ k : ℕ, b = t * x ^ k)
    {r : MulAut ↥Bs} (hr : GGIsReflection 3 r) (hrx : r ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    (π : Equiv.Perm (Fin m))
    (hneg : ∀ v : VT, ((r ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
      ((F.thetaT ((F.permVT π v)⁻¹) : ↥(Bs ⊓ L)) : G)) : False := by
  unfold GGIsReflection at hr
  obtain ⟨hr2, hrfix⟩ := hr
  let b : VT → ↥Bs := fun v =>
    ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩
  have hb_eq : ∀ v : VT, r (b v) = b ((F.permVT π v)⁻¹) := fun v => Subtype.ext (hneg v)
  have hfixr : ∀ x : ↥Bs, r (r x) = x := by
    intro x
    have hx := congrArg (fun f : MulAut ↥Bs => f x) hr2
    simpa [pow_two, MulAut.mul_apply] using hx
  have hπ : π * π = 1 := by
    apply qTwoLMFrameC_perm_faithful hVT
    intro v
    have h1 : r (b v) = b ((F.permVT π v)⁻¹) := hb_eq v
    have h2 : r (b ((F.permVT π v)⁻¹)) = b v := by
      rw [← h1]
      exact hfixr (b v)
    have h3 : F.thetaT ((F.permVT π ((F.permVT π v)⁻¹))⁻¹) = F.thetaT v := by
      apply Subtype.ext
      rw [← hneg ((F.permVT π v)⁻¹)]
      exact congrArg (fun z : ↥Bs => (z : G)) h2
    have h4 : (F.permVT π ((F.permVT π v)⁻¹))⁻¹ = v := F.thetaT.injective h3
    have h5 : F.permVT (π * π) v = (F.permVT π ((F.permVT π v)⁻¹))⁻¹ := by
      rw [map_inv, inv_inv, ← MulAut.mul_apply, ← map_mul]
    exact h5.trans h4
  have hψcard : Nat.card {v : VT // (F.permVT π v)⁻¹ = v} ≤ 3 ^ (m / 2) := by
    have heq : Nat.card {v : VT // (F.permVT π v)⁻¹ = v}
        = Nat.card {v : VT // F.permVT π v = v⁻¹} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun v => inv_eq_iff_eq_inv))
    rw [heq]
    exact qTwoLMFrameC_negFix_card_le_VT hVT hπ
  have hfix := qTwoLMFrameC_fix_card_le F hsplit F.hord hrx
    (fun v => (F.permVT π v)⁻¹) hneg
  have hle : 3 ^ m ≤ 3 ^ (m / 2 + 2) := by
    calc 3 ^ m = Nat.card ↥Bs := hcard.symm
      _ = Nat.card {b : ↥Bs // r b = b} * 3 := hrfix.symm
      _ ≤ (3 * Nat.card {v : VT // (F.permVT π v)⁻¹ = v}) * 3 :=
          mul_le_mul_left hfix 3
      _ ≤ (3 * 3 ^ (m / 2)) * 3 :=
          mul_le_mul_left (mul_le_mul_right hψcard 3) 3
      _ = 3 ^ (m / 2 + 2) := by rw [pow_add]; ring
  have hle2 : m ≤ m / 2 + 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  omega

end CFSG.StandardType.QTwo

end
