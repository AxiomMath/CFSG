module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace SBc9

section Averaging

private theorem exists_coboundary_of_odd_index {X A : Type} [Group X] [Finite X] [Group A]
    [Finite A] (hAc : ∀ a b : A, a * b = b * a) (hA2 : IsPGroup 2 A) (act : X → A →* A)
    {P : Subgroup X} (hodd : ¬ 2 ∣ P.index) (δ : X → A)
    (hδ : ∀ x y : X, δ (x * y) = act x (δ y) * δ x) (hP : ∀ p ∈ P, δ p = 1) :
    ∃ m : A, ∀ x : X, δ x = act x m * m⁻¹ := by
  classical
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
  have hcop : (Nat.card A).Coprime P.index := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).pow_left k
  let _ : CommGroup A := { ‹Group A› with mul_comm := hAc }
  have : Fintype (X ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (X ⧸ P) = P.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hcoset : ∀ x p : X, p ∈ P → δ (x * p) = δ x := fun x p hp => by
    rw [hδ, hP p hp, map_one, one_mul]
  have hperm : ∀ g : X, ∏ i : X ⧸ P, δ (g * i.out) = ∏ i : X ⧸ P, δ i.out := by
    intro g
    have h1 : ∀ i : X ⧸ P, δ (g * i.out) = δ (g • i).out := fun i => by
      have hq : (QuotientGroup.mk (g • i).out : X ⧸ P) = QuotientGroup.mk (g * i.out) := by
        rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      calc δ (g * i.out)
          = δ ((g • i).out * ((g • i).out⁻¹ * (g * i.out))) := by rw [mul_inv_cancel_left]
        _ = δ (g • i).out := hcoset _ _ (QuotientGroup.eq.mp hq)
    simp_rw [h1]
    exact Equiv.prod_comp (MulAction.toPerm g) (fun i : X ⧸ P => δ i.out)
  set m₀ : A := ∏ i : X ⧸ P, δ i.out with hm₀
  have hconj : ∀ g : X, act g m₀ * δ g ^ P.index = m₀ := by
    intro g
    have h2 : act g m₀ = ∏ i : X ⧸ P, (δ (g * i.out) * (δ g)⁻¹) := by
      rw [hm₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hδ g i.out, mul_inv_cancel_right]
    rw [h2, Finset.prod_mul_distrib, hperm g, Finset.prod_const, Finset.card_univ, hcard, inv_pow,
      inv_mul_cancel_right]
  obtain ⟨m, hm⟩ := (powCoprime hcop).surjective m₀⁻¹
  rw [powCoprime_apply] at hm
  refine ⟨m, fun x => (powCoprime hcop).injective ?_⟩
  have h3 : (act x m * m⁻¹) ^ P.index = (act x m₀)⁻¹ * m₀ := by
    rw [mul_pow, inv_pow, ← map_pow, hm, map_inv, inv_inv]
  rw [powCoprime_apply, powCoprime_apply, h3]
  exact eq_inv_mul_of_mul_eq (hconj x)

end Averaging

section Covering

private theorem normal_of_commutative {G : Type} [Group G] {W : Subgroup G}
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (N : Subgroup ↥W) : N.Normal where
  conj_mem n hn g := by
    have h : g * n = n * g := Subtype.ext (hWc g g.2 n n.2)
    rwa [h, mul_inv_cancel_right]

theorem exists_mul_mod_of_cocycle {G : Type} [Group G] [Finite G] {L P W Z : Subgroup G} {d : G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hW2 : IsPGroup 2 ↥W)
    (hZW : Z ≤ W) (hLZ : ∀ l ∈ L, ∀ z ∈ Z, l * z * l⁻¹ ∈ Z)
    (hodd : ¬ 2 ∣ P.relIndex L)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w)
    (hd : ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ W)
    (hP : ∀ p ∈ P, p * d * p⁻¹ * d⁻¹ ∈ Z) :
    ∃ m ∈ W, ∀ l ∈ L, l * (d * m⁻¹) * l⁻¹ * (d * m⁻¹)⁻¹ ∈ Z := by
  have _ := hZW
  have hconjW : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := fun l hl w hw =>
    (Subgroup.mem_set_normalizer_iff.mp (hLW hl) w).mp hw
  have : (Z.subgroupOf W).Normal := normal_of_commutative hWc _
  have hAc : ∀ a b : ↥W ⧸ Z.subgroupOf W, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a fun a => QuotientGroup.induction_on b fun b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (hWc a a.2 b b.2))
  let conj : ↥L → ↥W →* ↥W := fun l =>
    MonoidHom.mk' (fun w : ↥W => (⟨(l : G) * w * (l : G)⁻¹, hconjW l l.2 w w.2⟩ : ↥W))
      (fun a b => Subtype.ext (by simp [mul_assoc]))
  have hconjZ : ∀ l : ↥L, Z.subgroupOf W ≤ (Z.subgroupOf W).comap (conj l) := fun l n hn =>
    hLZ l l.2 n (Subgroup.mem_subgroupOf.mp hn)
  let act : ↥L → (↥W ⧸ Z.subgroupOf W) →* (↥W ⧸ Z.subgroupOf W) := fun l =>
    QuotientGroup.map (Z.subgroupOf W) (Z.subgroupOf W) (conj l) (hconjZ l)
  obtain ⟨mbar, hm⟩ := exists_coboundary_of_odd_index (X := ↥L) (A := ↥W ⧸ Z.subgroupOf W)
    (P := P.subgroupOf L) hAc (hW2.to_quotient _) act hodd
    (fun l => QuotientGroup.mk ⟨(l : G) * d * (l : G)⁻¹ * d⁻¹, hd l l.2⟩)
    (fun x y => by
      have h : (⟨((x * y : ↥L) : G) * d * ((x * y : ↥L) : G)⁻¹ * d⁻¹, hd _ (x * y).2⟩ : ↥W) =
          conj x ⟨(y : G) * d * (y : G)⁻¹ * d⁻¹, hd y y.2⟩ *
            ⟨(x : G) * d * (x : G)⁻¹ * d⁻¹, hd x x.2⟩ :=
        Subtype.ext (by simp [conj]; group)
      show QuotientGroup.mk _ = QuotientGroup.map _ _ _ _ (QuotientGroup.mk _) * QuotientGroup.mk _
      rw [QuotientGroup.map_mk, ← QuotientGroup.mk_mul, h])
    (fun p hp => (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_subgroupOf.mpr (hP p (Subgroup.mem_subgroupOf.mp hp))))
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective mbar
  refine ⟨m, m.2, fun l hl => ?_⟩
  have key : (QuotientGroup.mk (⟨l * d * l⁻¹ * d⁻¹, hd l hl⟩ : ↥W) : ↥W ⧸ Z.subgroupOf W) =
      act ⟨l, hl⟩ (QuotientGroup.mk m) * (QuotientGroup.mk m)⁻¹ := hm ⟨l, hl⟩
  have hw : l * (m : G)⁻¹ * l⁻¹ * m ∈ W :=
    W.mul_mem (hconjW l hl _ (W.inv_mem m.2)) m.2
  have hdw : d⁻¹ * (l * (m : G)⁻¹ * l⁻¹ * m) = (l * (m : G)⁻¹ * l⁻¹ * m) * d⁻¹ :=
    (Commute.inv_left (mul_inv_eq_iff_eq_mul.mp (hdW _ hw) : Commute d _)).eq
  have hid : l * (d * (m : G)⁻¹) * l⁻¹ * (d * (m : G)⁻¹)⁻¹ =
      (l * d * l⁻¹ * d⁻¹) * (l * (m : G)⁻¹ * l⁻¹ * m) :=
    calc l * (d * (m : G)⁻¹) * l⁻¹ * (d * (m : G)⁻¹)⁻¹
        = (l * d * l⁻¹) * ((l * (m : G)⁻¹ * l⁻¹ * m) * d⁻¹) := by group
      _ = (l * d * l⁻¹) * (d⁻¹ * (l * (m : G)⁻¹ * l⁻¹ * m)) := by rw [hdw]
      _ = (l * d * l⁻¹ * d⁻¹) * (l * (m : G)⁻¹ * l⁻¹ * m) := by group
  have hmem : l * (d * (m : G)⁻¹) * l⁻¹ * (d * (m : G)⁻¹)⁻¹ ∈ W := hid ▸ W.mul_mem (hd l hl) hw
  have h2 : (QuotientGroup.mk (conj ⟨l, hl⟩ m⁻¹) : ↥W ⧸ Z.subgroupOf W) =
      (act ⟨l, hl⟩ (QuotientGroup.mk m))⁻¹ := by
    rw [← map_inv, ← QuotientGroup.mk_inv]
    rfl
  have hq : (QuotientGroup.mk (⟨l * (d * (m : G)⁻¹) * l⁻¹ * (d * (m : G)⁻¹)⁻¹, hmem⟩ : ↥W) :
      ↥W ⧸ Z.subgroupOf W) = 1 := by
    have h1 : (⟨l * (d * (m : G)⁻¹) * l⁻¹ * (d * (m : G)⁻¹)⁻¹, hmem⟩ : ↥W) =
        ⟨l * d * l⁻¹ * d⁻¹, hd l hl⟩ * (conj ⟨l, hl⟩ m⁻¹ * m) := Subtype.ext hid
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, key, h2]
    let _ : CommGroup (↥W ⧸ Z.subgroupOf W) :=
      { (inferInstance : Group (↥W ⧸ Z.subgroupOf W)) with mul_comm := hAc }
    rw [mul_mul_mul_comm, mul_inv_cancel, inv_mul_cancel, mul_one]
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)

end Covering

end SBc9

end CFSG.Quasithin
