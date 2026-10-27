module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem s151u_perf_map_mem {L T : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hT : ∀ l ∈ L, ∀ t ∈ T, l * t * l⁻¹ ∈ T) (ε : G → G) (hεL : ∀ l ∈ L, ε l ∈ L)
    (hmul : ∀ l ∈ L, ∀ m ∈ L, ε (l * m) * (ε l * ε m)⁻¹ ∈ T)
    (hcomm : ∀ l ∈ L, ∀ m ∈ L, ε l * ε m * (ε m * ε l)⁻¹ ∈ T) :
    ∀ l ∈ L, ε l ∈ T := by
  have hn : (T.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hT g g.2 n hn
    simpa using this
  have hT' : ∀ l ∈ L, ∀ t ∈ T, l⁻¹ * t * l ∈ T := fun l hl t ht => by
    have := hT l⁻¹ (L.inv_mem hl) t ht
    simpa using this
  have h1 : ε 1 ∈ T := by
    have h := hmul 1 L.one_mem 1 L.one_mem
    simp only [mul_one] at h
    have h' : ((ε 1) * (ε 1)⁻¹ * (ε 1)⁻¹) ∈ T := by
      simpa [mul_assoc] using h
    simpa using h'
  let ψ : ↥L →* ↥L ⧸ T.subgroupOf L :=
    { toFun := fun l => ((⟨ε l, hεL l l.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L)
      map_one' := by
        show ((⟨ε 1, hεL 1 L.one_mem⟩ : ↥L) : ↥L ⧸ T.subgroupOf L) = 1
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h1
      map_mul' := by
        intro l m
        show ((⟨ε (l * m), hεL _ (L.mul_mem l.2 m.2)⟩ : ↥L) : ↥L ⧸ T.subgroupOf L) =
          ((⟨ε l, hεL l l.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L) * ((⟨ε m, hεL m m.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L)
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h := hmul l l.2 m m.2
        have hinv : (ε l * ε m) * (ε (l * m))⁻¹ ∈ T := by
          have := T.inv_mem h
          simpa using this
        have := hT' (ε (l * m)) (hεL _ (L.mul_mem l.2 m.2)) _ hinv
        simpa [mul_assoc] using this }
  have hψc : ∀ x y : ↥L, ψ x * ψ y = ψ y * ψ x := by
    intro x y
    show ((⟨ε x, hεL x x.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L) * ((⟨ε y, hεL y y.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L) =
      ((⟨ε y, hεL y y.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L) * ((⟨ε x, hεL x x.2⟩ : ↥L) : ↥L ⧸ T.subgroupOf L)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hcomm x x.2 y y.2
    have hinv : (ε y * ε x) * (ε x * ε y)⁻¹ ∈ T := by
      have := T.inv_mem h
      simpa using this
    have := hT' (ε x * ε y) (L.mul_mem (hεL x x.2) (hεL y y.2)) _ hinv
    simpa [mul_assoc] using this
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hker : (⊤ : Subgroup ↥L) ≤ ψ.ker := by
    have h1 : commutator ↥L ≤ ψ.ker := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
      rw [MonoidHom.mem_ker, commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [hψc x y]
      group
    rwa [Group.isPerfect_def.mp hperfL] at h1
  intro l hl
  have h2 : ψ ⟨l, hl⟩ = 1 := hker (Subgroup.mem_top _)
  have h3 : (⟨ε l, hεL l hl⟩ : ↥L) ∈ T.subgroupOf L := (QuotientGroup.eq_one_iff _).mp h2
  exact h3

theorem s151u_transfer [Finite G] {L P U Z : Subgroup G} {δ : G → G}
    (hodd : ¬ 2 ∣ (P.subgroupOf L).index)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a * a = 1)
    (hLU : ∀ l ∈ L, ∀ u ∈ U, l * u * l⁻¹ ∈ U)
    (hZc : ∀ z ∈ Z, ∀ l ∈ L, l * z * l⁻¹ = z)
    (hδU : ∀ l ∈ L, δ l ∈ U)
    (hcoc : ∀ x ∈ L, ∀ y ∈ L, δ (x * y) = δ x * (x * δ y * x⁻¹))
    (hδP : ∀ p ∈ P, δ p ∈ Z) :
    ∃ u ∈ U, ∀ x ∈ L, ∃ ζ ∈ Z, δ x = u * (x * u * x⁻¹)⁻¹ * ζ := by
  classical
  let _ : CommGroup ↥U := { (inferInstance : Group ↥U) with
    mul_comm := fun a b => Subtype.ext (hUab a a.2 b b.2) }
  let _ : Fintype (↥L ⧸ P.subgroupOf L) := Fintype.ofFinite _
  set P' : Subgroup ↥L := P.subgroupOf L with hP'
  let r : ↥L ⧸ P' → ↥L := fun t => Quotient.out t
  have hr : ∀ t, ((r t : ↥L) : ↥L ⧸ P') = t := fun t => QuotientGroup.out_eq' t
  let d : ↥L → ↥U := fun l => ⟨δ l, hδU l l.2⟩
  let c : ↥L → ↥U →* ↥U := fun l =>
    { toFun := fun u => ⟨(l : G) * u * (l : G)⁻¹, hLU l l.2 u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let s : ↥U := ∏ t : ↥L ⧸ P', d (r t)
  have hm : Odd (Fintype.card (↥L ⧸ P')) := by
    have h1 : P'.index = Nat.card (↥L ⧸ P') := Subgroup.index_eq_card P'
    rw [Nat.card_eq_fintype_card] at h1
    rw [← h1]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hd2 : ∀ l : ↥L, d l * d l = 1 := fun l => Subtype.ext (hU2 _ (hδU l l.2))
  refine ⟨s, s.2, fun x hx => ?_⟩
  let x' : ↥L := ⟨x, hx⟩
  let pt : ↥L ⧸ P' → ↥L := fun t => (r (x' • t))⁻¹ * x' * r t
  have hpt : ∀ t, pt t ∈ P' := by
    intro t
    have h1 : x' • t = ((x' * r t : ↥L) : ↥L ⧸ P') := by
      have h0 : x' • t = x' • ((r t : ↥L) : ↥L ⧸ P') := by rw [hr t]
      rw [h0, MulAction.Quotient.smul_mk]
      rfl
    have h2 : ((r (x' • t) : ↥L) : ↥L ⧸ P') = ((x' * r t : ↥L) : ↥L ⧸ P') := by
      rw [hr, h1]
    have := QuotientGroup.eq.mp h2
    simpa [pt, mul_assoc] using this
  have hptz : ∀ t, δ ((pt t : ↥L) : G) ∈ Z := fun t => hδP _ (Subgroup.mem_subgroupOf.mp (hpt t))
  have key : ∀ t : ↥L ⧸ P', d x' * c x' (d (r t)) = d (r (x' • t)) * d (pt t) := by
    intro t
    apply Subtype.ext
    show δ (x' : G) * ((x' : G) * δ (r t) * (x' : G)⁻¹) = δ (r (x' • t)) * δ ((pt t : ↥L) : G)
    have e1 : δ ((x' : G) * (r t : G)) = δ x' * ((x' : G) * δ (r t) * (x' : G)⁻¹) :=
      hcoc _ x'.2 _ (r t).2
    have e2' : x' * r t = r (x' • t) * pt t := by simp only [pt]; group
    have e2 : (x' : G) * (r t : G) = (r (x' • t) : G) * ((pt t : ↥L) : G) := by
      have := congrArg (fun y : ↥L => (y : G)) e2'
      exact this
    have e3 : δ ((r (x' • t) : G) * ((pt t : ↥L) : G)) =
        δ (r (x' • t)) * ((r (x' • t) : G) * δ ((pt t : ↥L) : G) * (r (x' • t) : G)⁻¹) :=
      hcoc _ (r (x' • t)).2 _ (pt t).2
    rw [hZc _ (hptz t) _ (r (x' • t)).2] at e3
    rw [← e1, e2, e3]
  have hprod := Finset.prod_congr rfl (fun t (_ : t ∈ (Finset.univ : Finset (↥L ⧸ P'))) => key t)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod,
    Finset.card_univ] at hprod
  have hperm : ∏ t : ↥L ⧸ P', d (r (x' • t)) = s :=
    Equiv.prod_comp (MulAction.toPerm x') (fun t => d (r t))
  rw [hperm] at hprod
  have hdpow : d x' ^ Fintype.card (↥L ⧸ P') = d x' := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_succ, pow_mul, sq, hd2, one_pow, one_mul]
  rw [hdpow] at hprod
  set ζ : ↥U := ∏ t : ↥L ⧸ P', d (pt t) with hζdef
  have hζ : (ζ : G) ∈ Z := by
    have : ζ ∈ Z.subgroupOf U := Subgroup.prod_mem _ (fun t _ => Subgroup.mem_subgroupOf.mpr (hptz t))
    exact Subgroup.mem_subgroupOf.mp this
  have hfin : d x' = s * (c x' s)⁻¹ * ζ := by
    calc d x' = d x' * c x' s * (c x' s)⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = s * ζ * (c x' s)⁻¹ := by rw [hprod]
      _ = s * (c x' s)⁻¹ * ζ := mul_right_comm _ _ _
  refine ⟨(ζ : G), hζ, ?_⟩
  have := congrArg Subtype.val hfin
  exact this


end CFSG.Quasithin
