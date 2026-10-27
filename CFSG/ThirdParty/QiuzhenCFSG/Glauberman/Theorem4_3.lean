module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem4_2
public import Mathlib.GroupTheory.Nilpotent

namespace CFSG
end CFSG
open CFSG

universe u

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — §4, Theorem 4.3

Statement and proof of Theorem 4.3 of George Glauberman, *A Characteristic Subgroup of a
p-Stable Group*, Canadian Journal of Mathematics 20 (1968), 1101–1135 — reference [6] of
the dihedral-Sylow project — following the validated transcription in
`refs/glauberman-p-stable.tex` (Theorem 4.3 at L951–L971).

* Theorem 4.3 (tex L951–L971): `p` odd, `S ∈ Syl_p G`, `B ⊴ G` a normal `p`-subgroup,
  `G` `p`-stable ⟹ `Z(J(S)) ∩ B ⊴ G`.  This removes the nilpotence-class restriction of
  Theorem 4.2.

Proof (tex L953–L971): assume the theorem fails and take a counterexample `B` of least
order.  Let `Z = Z(J(S))`; `B₁ = ⟨(Z∩B)^G⟩` is the normal closure of `Z ∩ B`, so
`B₁ ⊆ B` and `Z ∩ B₁ = Z ∩ B`; by minimality `B₁ = B` (4.10), i.e. `B` is the smallest
normal subgroup of `G` containing `Z ∩ B`.  Let `B' = [B,B]`.  Then `B' < B` (`B` is a
finite `p`-group, hence nilpotent, so its lower central series reaches `⊥`), `B' ⊴ G`
(characteristic in the normal subgroup `B`), and by minimality `Z ∩ B' ⊴ G`.  Since
`Z ∩ B ⊆ Z` and `B ⊆ S` normalises `Z`, we get `[Z∩B, B] ⊆ Z ∩ B'`; writing
`K = Z ∩ B'`, the modular centralizer `C_G(B/K) = {g | [g,B] ⊆ K}` is a normal subgroup
of `G` containing `Z ∩ B`, hence (by 4.10) containing `B`, so `B' = [B,B] ⊆ K ⊆ Z`.
Now `Z` is Abelian and `B' ⊆ Z`, so `Z ∩ B` centralises `B'`; the ordinary centralizer
`C_G(B')` is normal in `G` (as `B' ⊴ G`), hence by 4.10 `B ⊆ C_G(B')`, so `[B',B] = 1`
and `B` has nilpotence class at most two with `[B,B] ⊆ Z(J(S))`; Theorem 4.2 applies and
gives `Z ∩ B ⊴ G`, contradicting the choice of `B`.

The modular centralizer is built explicitly as a subgroup of `G` (`modularCentralizer`);
the "finite `p`-group is nilpotent" fact (`isNilpotent_of_finite_pGroup`, which Mathlib
does not provide) is proved by induction on the order using the nontrivial centre of a
nontrivial `p`-group and `isNilpotent_of_ker_le_center`.

No `axiom`/`opaque`/unregistered `sorry` is used.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G] [Finite G]

/-! ## Finite `p`-groups are nilpotent -/

/-- A finite `p`-group is nilpotent (Mathlib does not provide this).  Proved by strong
induction on the order: a nontrivial finite `p`-group has a nontrivial centre
(`IsPGroup.bot_lt_center`); its quotient by the centre is a strictly smaller `p`-group,
hence nilpotent by the induction hypothesis; and nilpotency lifts back through a
homomorphism whose kernel lies in the centre (`isNilpotent_of_ker_le_center`). -/
private lemma isNilpotent_of_finite_pGroup {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hHp : IsPGroup p H) : Group.IsNilpotent H := by
  classical
  -- strong induction on the order
  have hmain : ∀ n : ℕ, ∀ (K : Type u) [Group K] [Finite K] (q : ℕ) [Fact q.Prime],
      IsPGroup q K → Nat.card K = n → Group.IsNilpotent K := by
    intro n
    exact Nat.strong_induction_on (p := fun m => ∀ (K : Type u) [Group K] [Finite K] (q : ℕ)
      [Fact q.Prime], IsPGroup q K → Nat.card K = m → Group.IsNilpotent K) n (fun m ih => by
      intro K hKgrp hKfin q hqprime hKq hcardm
      by_cases htriv : Nat.card K = 1
      · -- the trivial group: the centre is the whole group, so the upper central series
        -- reaches `⊤` at step 1
        have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp htriv).1
        refine ⟨1, ?_⟩
        rw [Subgroup.upperCentralSeries_one]
        ext x
        constructor
        · intro hx
          trivial
        · intro hx
          rw [Subgroup.mem_center_iff]
          intro y
          have hx1 : x = 1 := Subsingleton.elim x 1
          rw [hx1]
          simp
      · -- nontrivial: use the centre
        have : Nontrivial K := by
          have hpos : 0 < Nat.card K := Nat.card_pos
          have hcard2 : 1 < Nat.card K := lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (by
            intro h
            apply htriv
            exact h.symm)
          exact (Finite.one_lt_card_iff_nontrivial (α := K)).1 hcard2
        let Zc : Subgroup K := Subgroup.center K
        have hZ_ne : Zc ≠ ⊥ := ne_of_gt (IsPGroup.bot_lt_center hKq)
        have hq_quot : IsPGroup q (K ⧸ Zc) := IsPGroup.to_quotient hKq Zc
        have hcard_lt : Nat.card (K ⧸ Zc) < Nat.card K := by
          have hZ_card : 1 < Nat.card Zc := (Subgroup.one_lt_card_iff_ne_bot (H := Zc)).2 hZ_ne
          have hindex_pos : 0 < Zc.index :=
            Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (G := K) (H := Zc))
          have hindex_lt : Zc.index < Nat.card K := by
            calc
              Zc.index = 1 * Zc.index := by simp
              _ < Nat.card Zc * Zc.index := Nat.mul_lt_mul_of_pos_right hZ_card hindex_pos
              _ = Nat.card K := Subgroup.card_mul_index Zc
          rw [← Subgroup.index_eq_card]
          exact hindex_lt
        have hcard_lt' : Nat.card (K ⧸ Zc) < m := by
          rwa [← hcardm]
        have hq_nil : Group.IsNilpotent (K ⧸ Zc) :=
          ih (Nat.card (K ⧸ Zc)) hcard_lt' (K ⧸ Zc) q hq_quot rfl
        exact Subgroup.isNilpotent_of_ker_le_center (f := QuotientGroup.mk' Zc) (by
          rw [QuotientGroup.ker_mk']))
  exact hmain (Nat.card H) H p hHp rfl

/-! ## The modular centralizer `C_G(B/K)` -/

/-- The *modular centralizer* `C_G(B/K)`: the elements of `G` whose conjugation action on
`B` is trivial modulo `K`, i.e. `{g | ∀ b ∈ B, ⁅g, b⁆ ∈ K}`.  When `K ⊴ G` this is a
subgroup of `G` (closure under products and inverses uses the identities
`commutatorElement_mul_left_eq_conj_mul` and `commutatorElement_inv_left` together with
the normality of `K`). -/
public def modularCentralizer (B K : Subgroup G) [K.Normal] : Subgroup G where
  carrier := {g : G | ∀ b : B, ⁅g, (b : G)⁆ ∈ K}
  one_mem' := by
    intro b
    simp
  mul_mem' := by
    intro g h hg hh b
    have h1 : ⁅g * h, (b : G)⁆ = g * ⁅h, (b : G)⁆ * g⁻¹ * ⁅g, (b : G)⁆ :=
      commutatorElement_mul_left_eq_conj_mul g h (b : G)
    rw [h1]
    exact K.mul_mem ((inferInstance : K.Normal).conj_mem (⁅h, (b : G)⁆) (hh b) g) (hg b)
  inv_mem' := by
    intro g hg b
    have h1 : ⁅g⁻¹, (b : G)⁆ = g⁻¹ * ⁅(b : G), g⁆ * g :=
      commutatorElement_inv_left g (b : G)
    rw [h1]
    have hbg : ⁅(b : G), g⁆ ∈ K := by
      simpa [commutatorElement_inv] using (K.inv_mem (hg b))
    exact by simpa using ((inferInstance : K.Normal).conj_mem (⁅(b : G), g⁆) hbg g⁻¹)

omit [Finite G] in
/-- The modular centralizer is normal in `G` when both `B` and `K` are normal in `G`:
conjugation by `g` transports the defining condition through the identity
`⁅g*x*g⁻¹, b⁆ = g * ⁅x, g⁻¹*b*g⁆ * g⁻¹`. -/
public lemma modularCentralizer_normal (B K : Subgroup G) [B.Normal] [K.Normal] :
    (modularCentralizer B K).Normal := by
  -- conjugation by `g` preserves membership: `x ∈ M ⟹ g*x*g⁻¹ ∈ M`
  have hfwd : ∀ (g x : G), x ∈ modularCentralizer B K → g * x * g⁻¹ ∈ modularCentralizer B K := by
    intro g x hx b
    have hmem : g⁻¹ * (b : G) * g ∈ B := by
      simpa using ((inferInstance : B.Normal).conj_mem (b : G) b.2 g⁻¹)
    have hx' : ⁅x, g⁻¹ * (b : G) * g⁆ ∈ K := hx ⟨g⁻¹ * (b : G) * g, hmem⟩
    have hconj : ⁅g * x * g⁻¹, (b : G)⁆ = g * ⁅x, g⁻¹ * (b : G) * g⁆ * g⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hconj]
    exact (inferInstance : K.Normal).conj_mem (⁅x, g⁻¹ * (b : G) * g⁆) hx' g
  rw [← Subgroup.normalizer_eq_top_iff]
  refine le_antisymm le_top ?_
  intro g _hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hfwd g x
  · intro hgxg
    have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxeq]
    simpa using (hfwd g⁻¹ (g * x * g⁻¹) hgxg)

/-! ## Theorem 4.3 (tex L951–L971) -/

/-- Theorem 4.3 ([6], §4, Theorem 4.3, p. 1111; `refs/glauberman-p-stable.tex` L951–L971):
let `p` be an odd prime and `S` a Sylow `p`-subgroup of a finite group `G`.  Suppose that
`B` is a normal `p`-subgroup of `G`.  If `G` is `p`-stable, then `Z(J(S)) ∩ B` is a
normal subgroup of `G`.

Proof (tex L953–L971; minimal-counterexample reduction to Theorem 4.2): see the module
docstring.  The "least order" choice of the counterexample is implemented as a minimal
`B₀` among the normal `p`-subgroups `X` of `G` with `Z ∩ X` not normal, so the
minimality hypothesis `hmin` (any normal `p`-subgroup of smaller order has normal
`Z ∩ X`) is available for `B₁ = ⟨(Z∩B₀)^G⟩` and for `B' = [B₀,B₀]`. -/
public theorem theorem4_3 {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) {B : Subgroup G} (hB_norm : B.Normal)
    (hB_p : IsPGroup p B) (hstab : pStable p G) :
    ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G).Normal) := by
  classical
  let Z : Subgroup G := ZJ (G := G) (S : Subgroup G)
  by_cases hB_bot : B = ⊥
  · have hZ_inf_bot : Z ⊓ B = ⊥ := by
      simp [hB_bot]
    rw [hZ_inf_bot]
    infer_instance
  -- assume the theorem fails for `B`; then `B` is a counterexample
  by_contra hnot
  -- take a counterexample `B₀` of least order (minimal `Nat.card`)
  let t : Set (Subgroup G) := {X : Subgroup G | X.Normal ∧ IsPGroup p X ∧ ¬ (Z ⊓ X : Subgroup G).Normal}
  have ht_fin : t.Finite := Set.toFinite t
  have ht_ne : t.Nonempty := ⟨B, hB_norm, hB_p, hnot⟩
  obtain ⟨B0, hB0_t, hB0_min⟩ :=
    Set.exists_min_image t (fun X : Subgroup G => Nat.card X) ht_fin ht_ne
  have hB0_norm : B0.Normal := hB0_t.1
  have : B0.Normal := hB0_norm
  have hB0_p : IsPGroup p B0 := hB0_t.2.1
  have hB0_not : ¬ (Z ⊓ B0 : Subgroup G).Normal := hB0_t.2.2
  -- minimality: any normal `p`-subgroup of smaller order has normal `Z ∩ X`
  have hmin : ∀ X : Subgroup G, X.Normal → IsPGroup p X → Nat.card X < Nat.card B0 →
      (Z ⊓ X : Subgroup G).Normal := by
    intro X hXn hXp hXcard
    by_contra hXnot
    exact (not_lt_of_ge (hB0_min X ⟨hXn, hXp, hXnot⟩)) hXcard
  have hB0_ne_bot : B0 ≠ ⊥ := by
    intro hB0bot
    apply hB0_not
    rw [hB0bot]
    simp
  -- `B₀ ⊆ S` (a normal `p`-subgroup) and `S` normalises `Z = Z(J(S))`
  have hB0_le_S : B0 ≤ (S : Subgroup G) := IsPGroup.le_sylow_of_normal (N := B0) hB0_p S
  have hS_le_NZ : S ≤ Subgroup.normalizer ((Z : Subgroup G) : Set G) := by
    calc
      S ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := Subgroup.le_normalizer
      _ ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonSubgroup (S : Subgroup G)
      _ ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
            simpa [Z, ZJ] using (normalizer_le_normalizer_of_thompsonCenter (S : Subgroup G))
  -- `B₁ = ⟨(Z∩B₀)^G⟩`: the normal closure of `Z ∩ B₀`
  let ZB0 : Subgroup G := Z ⊓ B0
  let B1 : Subgroup G := Subgroup.normalClosure (ZB0 : Set G)
  have hB1_norm : B1.Normal := Subgroup.normalClosure_normal
  have hB1_le_B0 : B1 ≤ B0 := by
    exact Subgroup.normalClosure_le_normal (N := B0) (s := (ZB0 : Set G))
      (show ZB0 ≤ B0 from inf_le_right)
  have hZB0_le_B1 : ZB0 ≤ B1 := Subgroup.le_normalClosure
  -- `Z ∩ B₁ = Z ∩ B₀`
  have hZ_inf_B1 : Z ⊓ B1 = Z ⊓ B0 := by
    apply le_antisymm
    · exact inf_le_inf_left Z hB1_le_B0
    · exact le_inf (inf_le_left : Z ⊓ B0 ≤ Z) hZB0_le_B1
  -- by minimality, `B₁ = B₀` ("(4.10)"): `B₀` is the smallest normal subgroup
  -- containing `Z ∩ B₀`
  have hB1_eq_B0 : B1 = B0 := by
    apply le_antisymm hB1_le_B0
    by_contra hnot_le
    have hB1_ne_B0 : B1 ≠ B0 := by
      intro h
      apply hnot_le
      rw [h]
    have hB1_p : IsPGroup p B1 := IsPGroup.to_le hB0_p hB1_le_B0
    have hB1_card_lt : Nat.card B1 < Nat.card B0 := by
      have hle : Nat.card B1 ≤ Nat.card B0 := Subgroup.card_le_of_le hB1_le_B0
      refine lt_of_le_of_ne hle ?_
      intro hEq
      have hEq' : B1 = B0 := Subgroup.eq_of_le_of_card_ge hB1_le_B0 (Nat.le_of_eq hEq.symm)
      exact hB1_ne_B0 hEq'
    have hZ_inf_B1_normal : (Z ⊓ B1 : Subgroup G).Normal := hmin B1 hB1_norm hB1_p hB1_card_lt
    have hZ_inf_B0_normal : (Z ⊓ B0 : Subgroup G).Normal := by
      simpa [hZ_inf_B1] using hZ_inf_B1_normal
    exact hB0_not hZ_inf_B0_normal
  -- `B' = [B₀,B₀]`: normal in `G` (characteristic in the normal subgroup `B₀`),
  -- a `p`-subgroup, and a proper subgroup of `B₀` (`B₀` is nilpotent)
  let B' : Subgroup G := ⁅B0, B0⁆
  have hB'_le_B0 : B' ≤ B0 :=
    commutator_le_left_of_normalizer (H := B0) (K := B0) Subgroup.le_normalizer
  have hB'_normal : B'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine le_antisymm le_top ?_
    intro g _hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      B'.map (MulAut.conj g).toMonoidHom = ⁅B0.map (MulAut.conj g).toMonoidHom, B0.map (MulAut.conj g).toMonoidHom⁆ := by
        simpa [B'] using (Subgroup.map_commutator B0 B0 (MulAut.conj g).toMonoidHom)
      _ = ⁅B0, B0⁆ := by
        congr 1 <;>
          exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
            ((Subgroup.normalizer_eq_top_iff.mpr hB0_norm) ▸ (show g ∈ (⊤ : Subgroup G) from trivial)))
  have hB'_p : IsPGroup p B' := IsPGroup.to_le hB0_p hB'_le_B0
  have hB'_ne_B0 : B' ≠ B0 := by
    have hnil : Group.IsNilpotent ↥B0 := isNilpotent_of_finite_pGroup hB0_p
    intro hB'
    have hg1 : B0.lowerCentralSeries 1 = B0 := by
      simpa [B'] using hB'
    have hg_all : ∀ n, B0.lowerCentralSeries n = B0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Subgroup.lowerCentralSeries_succ, ih]
          exact hg1
    rcases (Subgroup.isNilpotent_iff_lowerCentralSeries B0).mp hnil with ⟨n, hn⟩
    have hB0_bot : B0 = ⊥ := by
      calc
        B0 = B0.lowerCentralSeries n := (hg_all n).symm
        _ = ⊥ := hn
    exact hB0_ne_bot hB0_bot
  have hB'_card_lt : Nat.card B' < Nat.card B0 := by
    have hle : Nat.card B' ≤ Nat.card B0 := Subgroup.card_le_of_le hB'_le_B0
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hEq' : B' = B0 := Subgroup.eq_of_le_of_card_ge hB'_le_B0 (Nat.le_of_eq hEq.symm)
    exact hB'_ne_B0 hEq'
  -- by minimality, `Z ∩ B' ⊴ G`
  have hZ_inf_B'_normal : (Z ⊓ B' : Subgroup G).Normal := hmin B' hB'_normal hB'_p hB'_card_lt
  -- `[Z∩B₀, B₀] ⊆ Z ∩ B'`: the commutator of `z ∈ Z` and `b ∈ B₀ ⊆ S` lies in `Z`
  -- (as `S` normalises `Z`) and in `[B₀,B₀] = B'`
  let K : Subgroup G := Z ⊓ B'
  have hK_normal : K.Normal := by
    simpa [K] using hZ_inf_B'_normal
  have : K.Normal := hK_normal
  have : (modularCentralizer B0 K).Normal := modularCentralizer_normal B0 K
  have hZBB : ⁅ZB0, B0⁆ ≤ K := by
    apply le_inf
    · -- `[ZB0, B0] ⊆ Z`
      rw [Subgroup.commutator_le]
      intro z hz b hb
      have hzZ : z ∈ Z := hz.1
      have hz2 : b * z⁻¹ * b⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hS_le_NZ (hB0_le_S hb)) z⁻¹).1 (Z.inv_mem hzZ)
      rw [commutatorElement_def]
      simpa [mul_assoc] using Z.mul_mem hzZ hz2
    · -- `[ZB0, B0] ⊆ [B₀,B₀] = B'`
      exact Subgroup.commutator_mono (inf_le_right : ZB0 ≤ B0) le_rfl
  -- `Z ∩ B₀ ⊆ C_G(B₀/K)`, and `C_G(B₀/K) ⊴ G`, so by "(4.10)" `B₀ ⊆ C_G(B₀/K)`;
  -- hence `B' = [B₀,B₀] ⊆ K ⊆ Z`
  have hZB_le_M : ZB0 ≤ modularCentralizer B0 K := by
    intro x hx b
    exact (Subgroup.commutator_le.mp hZBB) x hx (b : G) b.2
  have hB0_le_M : B0 ≤ modularCentralizer B0 K := by
    calc
      B0 = Subgroup.normalClosure (ZB0 : Set G) := hB1_eq_B0.symm
      _ ≤ modularCentralizer B0 K := by
        exact Subgroup.normalClosure_le_normal (N := modularCentralizer B0 K)
          (s := (ZB0 : Set G)) hZB_le_M
  have hB'_le_K : B' ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx b hb
    exact (hB0_le_M hx) ⟨b, hb⟩
  have hB'_le_Z : B' ≤ Z := hB'_le_K.trans (inf_le_left : K ≤ Z)
  -- `Z` is Abelian and `B' ⊆ Z`, so `Z ∩ B₀ ⊆ C_G(B')`; as `B' ⊴ G`, `C_G(B') ⊴ G`,
  -- so by "(4.10)" `B₀ ⊆ C_G(B')`
  have hZ_comm : IsMulCommutative Z := thompsonCenter_isMulCommutative (G := G) (S : Subgroup G)
  have hZ_le_CZ : Z ≤ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := Z)).2 hZ_comm
  have hZ_le_CB' : Z ≤ Subgroup.centralizer (B' : Set G) :=
    hZ_le_CZ.trans (Subgroup.centralizer_le (show (B' : Set G) ⊆ (Z : Set G) from hB'_le_Z))
  have hB0_le_CB' : B0 ≤ Subgroup.centralizer (B' : Set G) := by
    calc
      B0 = Subgroup.normalClosure (ZB0 : Set G) := hB1_eq_B0.symm
      _ ≤ Subgroup.centralizer (B' : Set G) := by
        exact Subgroup.normalClosure_le_normal (N := Subgroup.centralizer (B' : Set G))
          (s := (ZB0 : Set G)) ((inf_le_left : ZB0 ≤ Z).trans hZ_le_CB')
  -- `B₀` has nilpotence class at most two with `[B₀,B₀] ⊆ Z(J(S))`, so Theorem 4.2
  -- applies and gives `Z ∩ B₀ ⊴ G`, contradicting the choice of `B₀`
  have hBB'_bot : ⁅B0, B'⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := B0) (H₂ := B')).2 hB0_le_CB'
  have hB0_class2 : ⁅⁅B0, B0⁆, B0⁆ = ⊥ := by
    change ⁅B', B0⁆ = ⊥
    rw [Subgroup.commutator_comm B' B0]
    exact hBB'_bot
  have hB'B_le_ZJ : ⁅B0, B0⁆ ≤ Z := hB'_le_Z
  have hZ_inf_B0_normal : (Z ⊓ B0 : Subgroup G).Normal :=
    theorem4_2 (p := p) hpodd S hB0_norm hB0_p hB0_class2 hB'B_le_ZJ hstab
  exact hB0_not hZ_inf_B0_normal

end CFSG.Glauberman
