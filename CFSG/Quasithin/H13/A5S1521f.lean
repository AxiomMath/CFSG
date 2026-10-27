module

public import CFSG.Quasithin.H13.A5Facts1321c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.InternalSec
open scoped commutatorElement

section Lift

variable {M : Type} [CommGroup M] [Finite M]

theorem exists_fix_mul_of_mem (g : MulAut M) (hg : g ^ 3 = 1) {C : Subgroup M}
    (hC : ¬ 3 ∣ Nat.card C) (hgC : ∀ c ∈ C, g c ∈ C) {x : M} (hx : g x * x⁻¹ ∈ C) :
    ∃ c ∈ C, g (x * c) = x * c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype C := Fintype.ofFinite C
  let f : Function.End ↥C := fun c => ⟨x⁻¹ * g (x * c), by
    rw [map_mul, ← mul_assoc, mul_comm x⁻¹]
    exact C.mul_mem hx (hgC c c.2)⟩
  have hfn : ∀ n : ℕ, ∀ c : ↥C, (((f ^ n) c : ↥C) : M) = x⁻¹ * (g ^ n) (x * c) := by
    intro n
    induction n with
    | zero =>
      intro c
      rw [pow_zero, pow_zero, MulAut.one_apply, inv_mul_cancel_left]
      rfl
    | succ n ih =>
      intro c
      have e : (f ^ (n + 1)) c = f ((f ^ n) c) := by rw [pow_succ']; rfl
      rw [e]
      show x⁻¹ * g (x * ((f ^ n) c : M)) = _
      rw [ih, mul_inv_cancel_left, pow_succ', MulAut.mul_apply]
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext c
    apply Subtype.ext
    rw [pow_one, hfn, hg, MulAut.one_apply, inv_mul_cancel_left]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  have hne : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    apply hC
    rw [Nat.card_eq_fintype_card]
    exact Nat.modEq_zero_iff_dvd.mp hmod
  obtain ⟨⟨c, hc⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hne)
  refine ⟨c, c.2, ?_⟩
  have h := congrArg Subtype.val (show f c = c from hc)
  change x⁻¹ * g (x * c) = c at h
  calc g (x * c) = x * (x⁻¹ * g (x * c)) := by rw [mul_inv_cancel_left]
    _ = x * c := by rw [h]

theorem not_three_dvd_card (hM : ∀ m : M, m ^ 2 = 1) (C : Subgroup M) : ¬ 3 ∣ Nat.card C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥C := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hM x)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end Lift

section Polar

variable {M : Type} [CommGroup M]

@[expose] def polarQ (q : M → ZMod 2) (a w : M) : ZMod 2 := q (a * w) - q a - q w

theorem polarQ_comm (q : M → ZMod 2) (a w : M) : polarQ q a w = polarQ q w a := by
  rw [polarQ, polarQ, mul_comm]
  ring

theorem q_mul_eq (q : M → ZMod 2) (a w : M) : q (a * w) = polarQ q a w + q a + q w := by
  rw [polarQ]
  ring

variable {q : M → ZMod 2} (hβ : ∀ a b w, polarQ q (a * b) w = polarQ q a w + polarQ q b w)
include hβ

theorem polarQ_one_left (w : M) : polarQ q 1 w = 0 := by
  have h := hβ 1 1 w
  rw [one_mul] at h
  have h2 : polarQ q 1 w + polarQ q 1 w = 0 := CharTwo.add_self_eq_zero _
  rw [← h] at h2
  exact h2

theorem polarQ_inv_left (a w : M) : polarQ q a⁻¹ w = polarQ q a w := by
  have h := hβ a a⁻¹ w
  rw [mul_inv_cancel, polarQ_one_left hβ] at h
  have h2 : polarQ q a w + polarQ q a w = 0 := CharTwo.add_self_eq_zero _
  calc polarQ q a⁻¹ w = polarQ q a w + polarQ q a⁻¹ w - polarQ q a w := by ring
    _ = polarQ q a w := by rw [← h, zero_sub, ZMod.neg_eq_self_mod_two]

theorem polarQ_mul_right (a b w : M) : polarQ q a (b * w) = polarQ q a b + polarQ q a w := by
  rw [polarQ_comm, hβ, polarQ_comm q b a, polarQ_comm q w a]

@[expose] def radQ : Subgroup M where
  carrier := {a | ∀ w, polarQ q a w = 0}
  one_mem' := fun w => polarQ_one_left hβ w
  mul_mem' := fun {a b} ha hb w => by rw [Set.mem_ofPred_eq] at ha hb; rw [hβ, ha, hb, add_zero]
  inv_mem' := fun {a} ha w => by rw [Set.mem_ofPred_eq] at ha; rw [polarQ_inv_left hβ, ha]

@[expose] def perpQ (a : M) : Subgroup M where
  carrier := {w | polarQ q a w = 0}
  one_mem' := by rw [Set.mem_ofPred_eq, polarQ_comm]; exact polarQ_one_left hβ a
  mul_mem' := fun {b w} hb hw => by
    rw [Set.mem_ofPred_eq] at hb hw ⊢
    rw [polarQ_mul_right hβ, hb, hw, add_zero]
  inv_mem' := fun {w} hw => by
    rw [Set.mem_ofPred_eq] at hw ⊢
    rw [polarQ_comm, polarQ_inv_left hβ, polarQ_comm, hw]

end Polar

section Canonical

variable {Y : Type} [Group Y] [Finite Y] {W : Type} [CommGroup W] [Finite W]

namespace Hyp1321

variable (P : Hyp1321 Y W)

omit [Finite W] in
theorem normal_K (h38 : A38Part3 Y) (hZ : Subgroup.center ↥P.K = ⊥) {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) {L : Subgroup Y} (hLK : L ≤ P.K) (hL : L ≠ ⊥)
    (hTL : T ≤ Subgroup.normalizer (L : Set Y)) : P.K.Normal := by
  have hK' := isComponent_of_isComponentOf_top P.comp
  have hTK : T ≤ Subgroup.normalizer (P.K : Set Y) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    by_contra hne
    have hKt := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK'
    have hcomm := (CFSG.LocalCores.distinct_components_commute hK' hKt).resolve_left
      (Ne.symm hne)
    apply hL
    rw [eq_bot_iff]
    intro l hl
    have hlt : l ∈ P.K.map (MulAut.conj t).toMonoidHom := by
      refine ⟨t⁻¹ * l * t, hLK ?_, by simp [mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTL ht)) l).mp hl
      simpa using this
    have hcen : (⟨l, hLK hl⟩ : ↥P.K) ∈ Subgroup.center ↥P.K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have hle : P.K.map (MulAut.conj t).toMonoidHom ≤
          Subgroup.centralizer (P.K : Set Y) :=
        Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle hlt) k k.2)
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcen)
  obtain ⟨-, hT2⟩ := h38 P.K (mem_cComp_of_isComponentOf_top P.comp)
  rcases hT2 T hT with ⟨hn, -⟩ | ⟨t, ht, htN, -⟩
  · exact hn
  · exact absurd (hTK ht) htN

omit [Finite Y] [Finite W] in
theorem fixV_inv (x : Y) (hx : x ∈ Subgroup.normalizer (P.K : Set Y)) :
    ∀ w ∈ fixV (P.K.map P.ρ), P.ρ x w ∈ fixV (P.K.map P.ρ) := by
  rintro w hw _ ⟨k, hk, rfl⟩
  have hk' : x⁻¹ * k * x ∈ P.K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) k).mp hk
    simpa using this
  have h1 := hw (P.ρ (x⁻¹ * k * x)) ⟨_, hk', rfl⟩
  calc P.ρ k (P.ρ x w) = P.ρ x (P.ρ (x⁻¹ * k * x) w) := by
        simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply,
          MulEquiv.apply_symm_apply]
    _ = P.ρ x w := by rw [h1]

omit [Finite Y] [Finite W] in
theorem chief_eq_canonical (hZ : Subgroup.center ↥P.K = ⊥) {U1 U2 : Subgroup W}
    (h1 : ∀ y ∈ P.K ⊔ Subgroup.zpowers P.b, ∀ u ∈ U1, P.ρ y u ∈ U1) (hU21 : U2 < U1)
    (hfix : ∀ k ∈ P.K, ∀ u ∈ U2, P.ρ k u = u) (hcomm : commSubOf U1 (P.K.map P.ρ) = U1)
    (hirr : ∀ J : Subgroup W, (∀ k ∈ P.K, ∀ u ∈ J, P.ρ k u ∈ J) → U2 ≤ J → J ≤ U1 →
      J = U2 ∨ J = U1) (hDU1 : P.D ≤ U1) :
    U1 = commSubOf ⊤ (P.K.map P.ρ) ∧ U2 = U1 ⊓ fixV (P.K.map P.ρ) := by
  have hKstab : ∀ k ∈ P.K, P.ρ k ∈ stabSub U1 := fun k hk =>
    le_stabSub_of_maps (X := Subgroup.zpowers (P.ρ k)) (by
      intro x hx u hu
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← map_zpow]
      exact h1 _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _ hk i)) u hu) (Subgroup.mem_zpowers _)
  have hbq : P.ρ P.b ∈ centQuot U1 := fun w => hDU1 (P.hD w)
  have hnorm : ∀ g ∈ stabSub U1, ∀ x ∈ centQuot U1, g * x * g⁻¹ ∈ centQuot U1 := by
    intro g hg x hx w
    have h1' := hx (g⁻¹ w)
    have e : (g * x * g⁻¹) w * w⁻¹ = g (x (g⁻¹ w) * (g⁻¹ w)⁻¹) := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact ((hg _).mpr h1')
  set N : Subgroup ↥P.K := (centQuot U1).comap (P.ρ.comp P.K.subtype) with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    show P.ρ ((g : Y) * n * (g : Y)⁻¹) ∈ centQuot U1
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hKstab g g.2) _ hn⟩
  have hNtop : N = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups P.quasi hNn with h | h
    · exact h
    · exfalso
      rw [hZ] at h
      obtain ⟨k, hk, hkb⟩ := P.bc
      apply hkb
      have hkbK : P.b * k * P.b⁻¹ * k⁻¹ ∈ P.K :=
        P.K.mul_mem ((Subgroup.mem_normalizer_iff.mp P.bN k).mp hk) (P.K.inv_mem hk)
      have hmem : (⟨_, hkbK⟩ : ↥P.K) ∈ N := by
        show P.ρ (P.b * k * P.b⁻¹ * k⁻¹) ∈ centQuot U1
        have e : P.ρ (P.b * k * P.b⁻¹ * k⁻¹) =
            P.ρ P.b * (P.ρ k * (P.ρ P.b)⁻¹ * (P.ρ k)⁻¹) := by
          simp only [map_mul, map_inv]
          group
        rw [e]
        exact (centQuot U1).mul_mem hbq (hnorm _ (hKstab k hk) _ ((centQuot U1).inv_mem hbq))
      have h' : P.b * k * P.b⁻¹ * k⁻¹ = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp (h hmem))
      calc k * P.b = (P.b * k * P.b⁻¹ * k⁻¹)⁻¹ * (P.b * k) := by group
        _ = P.b * k := by rw [h', inv_one, one_mul]
  have hKq : ∀ k ∈ P.K, ∀ w : W, P.ρ k w * w⁻¹ ∈ U1 := fun k hk w =>
    (show (⟨k, hk⟩ : ↥P.K) ∈ N from hNtop ▸ Subgroup.mem_top _) w
  have hU1 : U1 = commSubOf ⊤ (P.K.map P.ρ) := by
    apply le_antisymm
    · conv_lhs => rw [← hcomm]
      exact Subgroup.closure_mono (by
        rintro _ ⟨k, hk, u, -, rfl⟩
        exact ⟨k, hk, u, Subgroup.mem_top u, rfl⟩)
    · rw [commSubOf, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, w, -, rfl⟩
      exact hKq k hk w
  refine ⟨hU1, ?_⟩
  have hle : U2 ≤ U1 ⊓ fixV (P.K.map P.ρ) := fun u hu =>
    ⟨hU21.le hu, by rintro _ ⟨k, hk, rfl⟩; exact hfix k hk u hu⟩
  rcases hirr (U1 ⊓ fixV (P.K.map P.ρ)) (fun k hk u hu =>
      ⟨h1 k (Subgroup.mem_sup_left hk) u hu.1,
        P.fixV_inv k (Subgroup.le_normalizer hk) u hu.2⟩) hle inf_le_left with h | h
  · exact h.symm
  · exfalso
    have hbot : U1 ≤ ⊥ := by
      conv_lhs => rw [← hcomm]
      rw [commSubOf, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, u, hu, rfl⟩
      have hu'' : u ∈ U1 ⊓ fixV (P.K.map P.ρ) := by rw [h]; exact hu
      have hu' : u ∈ fixV (P.K.map P.ρ) := hu''.2
      rw [SetLike.mem_coe, Subgroup.mem_bot, hu' (P.ρ k) ⟨k, hk, rfl⟩, mul_inv_cancel]
    have := lt_of_lt_of_le hU21 hbot
    exact absurd this (not_lt_bot)

omit [Finite Y] [Finite W] in
theorem commSubOf_eq_top (hKn : P.K.Normal)
    (hgen : (⨆ y : Y, P.D.map (P.ρ y).toMonoidHom) = ⊤)
    (hD : P.D ≤ commSubOf ⊤ (P.K.map P.ρ)) : commSubOf ⊤ (P.K.map P.ρ) = ⊤ := by
  have hxK : ∀ y : Y, ∀ k ∈ P.K.map P.ρ, P.ρ y * k * (P.ρ y)⁻¹ ∈ P.K.map P.ρ := by
    rintro y _ ⟨k, hk, rfl⟩
    refine ⟨y * k * y⁻¹, hKn.conj_mem k hk y, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hle : (⨆ y : Y, P.D.map (P.ρ y).toMonoidHom) ≤ commSubOf ⊤ (P.K.map P.ρ) := by
    refine iSup_le fun y => ?_
    rintro _ ⟨d, hd, rfl⟩
    exact maps_commSubOf (hxK y) (fun u _ => Subgroup.mem_top _) d (hD hd)
  rw [eq_top_iff]
  intro w _
  exact hle (hgen ▸ Subgroup.mem_top w)

end Hyp1321

end Canonical

section Quad

variable {Y : Type} [Group Y] [Finite Y] {W : Type} [CommGroup W] [Finite W]

namespace Hyp1321

variable (P : Hyp1321 Y W)

theorem exists_fix_quad
    (QY : HypY P) (QL : HypL1 P) (hF : Facts1321) (hR : FactRankRows1321)
    (hA7 : FactA7Grp1321) (hL3 : FactL3Grp1321) (hO : FactOutRows1321)
    (hQ : FactQuadRows1321) (h38 : A38Part3 Y) {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hTL : T ≤ Subgroup.normalizer (QL.L : Set Y))
    (hgen : (⨆ y : Y, P.D.map (P.ρ y).toMonoidHom) = ⊤) (q : W → ZMod 2)
    (hqY : ∀ y : Y, ∀ w, q (P.ρ y w) = q w)
    (hβ : ∀ a b w, polarQ q (a * b) w = polarQ q a w + polarQ q b w)
    (hβ0 : ∃ a w, polarQ q a w ≠ 0) {c : Y} (hc : c ∈ QL.L) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ w, P.ρ c w = w ∧ q w ≠ 0 := by
  classical
  obtain ⟨hZ, hLK, U1, U2, h1, h2, hU21, hfix, hcomm, hirr, hB4, hcond, hinj, hDU1, -, hrk,
    A, hA⟩ := lemma_13_5_21_main P QY QL hF hR hA7 hL3 hO
  obtain ⟨hU1, hU2⟩ := P.chief_eq_canonical hZ h1 hU21 hfix hcomm hirr hDU1
  have hLne : QL.L ≠ ⊥ := by
    obtain ⟨l, hl, d, -, hld⟩ := QL.Dnt
    intro h
    rw [h, Subgroup.mem_bot] at hl
    rw [hl, map_one, MulAut.one_apply] at hld
    exact hld rfl
  have hKn := P.normal_K h38 hZ hT hLK hLne hTL
  have htop := P.commSubOf_eq_top hKn hgen (by rw [← hU1]; exact hDU1)
  have hU1t : U1 = ⊤ := hU1.trans htop
  subst hU1t
  subst hU2
  have hcK : c ∈ P.K := hLK hc
  by_cases hqC : ∃ w ∈ fixV (P.K.map P.ρ), q w ≠ 0
  · obtain ⟨w, hw, hqw⟩ := hqC
    exact ⟨w, hw _ ⟨c, hcK, rfl⟩, hqw⟩
  push Not at hqC
  have hβK : ∀ k ∈ P.K, ∀ a w, polarQ q (P.ρ k a) (P.ρ k w) = polarQ q a w := by
    intro k _ a w
    rw [polarQ, polarQ, ← map_mul, hqY k, hqY k, hqY k]
  have hCrad : ∀ a ∈ fixV (P.K.map P.ρ), ∀ w, polarQ q a w = 0 := by
    intro a ha w
    have hle : commSubOf ⊤ (P.K.map P.ρ) ≤ perpQ hβ a := by
      rw [commSubOf, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, x, -, rfl⟩
      show polarQ q a (P.ρ k x * x⁻¹) = 0
      rw [polarQ_mul_right hβ, polarQ_comm q a x⁻¹, polarQ_inv_left hβ, polarQ_comm q x a]
      have e : polarQ q a (P.ρ k x) = polarQ q a x := by
        rw [← hβK k hk a x, ha _ ⟨k, hk, rfl⟩]
      rw [e]
      exact CharTwo.add_self_eq_zero _
    exact hle (by rw [htop]; exact Subgroup.mem_top w)
  have hradC : ∀ a, (∀ w, polarQ q a w = 0) → a ∈ fixV (P.K.map P.ρ) := by
    intro a ha
    have hRinv : ∀ k ∈ P.K, ∀ r ∈ radQ hβ, P.ρ k r ∈ radQ hβ := by
      intro k hk r hr w
      have hw : P.ρ k ((P.ρ k)⁻¹ w) = w := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rw [← hw, hβK k hk]
      exact hr _
    have hJ : ∀ k ∈ P.K, ∀ u ∈ radQ hβ ⊔ fixV (P.K.map P.ρ),
        P.ρ k u ∈ radQ hβ ⊔ fixV (P.K.map P.ρ) := by
      intro k hk u hu
      obtain ⟨r, hr, x, hx, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul]
      exact Subgroup.mul_mem_sup (hRinv k hk r hr)
        (P.fixV_inv k (Subgroup.le_normalizer hk) x hx)
    rcases hirr (radQ hβ ⊔ fixV (P.K.map P.ρ)) hJ (inf_le_right.trans le_sup_right) le_top
      with h | h
    · have hm : a ∈ radQ hβ ⊔ fixV (P.K.map P.ρ) := Subgroup.mem_sup_left ha
      rw [h] at hm
      exact hm.2
    · exfalso
      obtain ⟨a', w', hne⟩ := hβ0
      apply hne
      have hm : a' ∈ radQ hβ ⊔ fixV (P.K.map P.ρ) := by rw [h]; exact Subgroup.mem_top a'
      obtain ⟨r, hr, x, hx, rfl⟩ := Subgroup.mem_sup.mp hm
      rw [hβ, hr w', hCrad x hx w', add_zero]
  have hqCm : ∀ x, ∀ y ∈ fixV (P.K.map P.ρ), q (x * y) = q x := by
    intro x y hy
    rw [q_mul_eq q, polarQ_comm, hCrad y hy x, hqC y hy, zero_add, add_zero]
  let lift : ChiefSec (⊤ : Subgroup W) (⊤ ⊓ fixV (P.K.map P.ρ)) → ↥(⊤ : Subgroup W) :=
    Function.surjInv (chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)))
  let qh : ChiefSec (⊤ : Subgroup W) (⊤ ⊓ fixV (P.K.map P.ρ)) → ZMod 2 := fun y => q (lift y : W)
  have hqh : ∀ u : ↥(⊤ : Subgroup W), qh (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u) = q u := by
    intro u
    have hl : chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) (lift (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u)) =
        chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u := Function.surjInv_eq _ _
    have hmem : ((u⁻¹ * lift (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u) : ↥(⊤ : Subgroup W)) : W) ∈
        ⊤ ⊓ fixV (P.K.map P.ρ) := by
      rw [← chiefQ_eq_one_iff, map_mul, map_inv, hl, inv_mul_cancel]
    show q (lift (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u) : W) = q u
    have e : ((lift (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u) : ↥(⊤ : Subgroup W)) : W) =
        (u : W) * ((u⁻¹ * lift (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u) : ↥(⊤ : Subgroup W)) : W) := by
      simp
    rw [e, hqCm _ _ hmem.2]
  have hV2 := P.chiefSec_sq (⊤ : Subgroup W) (⊤ ⊓ fixV (P.K.map P.ρ))
  have hchL : secAct P.ρ _ h1 h2 ⟨c, Subgroup.mem_sup_left hcK⟩ ∈
      (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map (secAct P.ρ _ h1 h2) :=
    ⟨⟨c, Subgroup.mem_sup_left hcK⟩, hcK, rfl⟩
  have hchv : secAct P.ρ _ h1 h2 ⟨c, Subgroup.mem_sup_left hcK⟩ *
      secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ =
      secAct P.ρ _ h1 h2 ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ *
        secAct P.ρ _ h1 h2 ⟨c, Subgroup.mem_sup_left hcK⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (QL.comm c hc)
  have hch3 : secAct P.ρ _ h1 h2 ⟨c, Subgroup.mem_sup_left hcK⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, Subgroup.mem_sup_left hcK⟩ : ↥(P.K ⊔ Subgroup.zpowers P.b)) ^ 3 = 1 :=
      Subtype.ext hc3
    rw [this, map_one]
  have hch1 : secAct P.ρ _ h1 h2 ⟨c, Subgroup.mem_sup_left hcK⟩ ≠ 1 := by
    intro h
    apply hc1
    have h' := hinj (a₁ := ⟨c, hcK⟩) (a₂ := 1) (by rw [map_one]; exact h)
    exact congrArg Subtype.val h'
  have hqhL : ∀ x ∈ (secAct P.ρ _ h1 h2).range, ∀ y, qh (x y) = qh y := by
    rintro _ ⟨k, rfl⟩ y
    obtain ⟨u, rfl⟩ := chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) y
    rw [secAct_chiefQ, hqh, hqh]
    exact hqY (k : Y) (u : W)
  have hβh : ∀ a b w, qh (a * b * w) - qh (a * b) - qh w =
      (qh (a * w) - qh a - qh w) + (qh (b * w) - qh b - qh w) := by
    intro a b w
    obtain ⟨a', rfl⟩ := chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) a
    obtain ⟨b', rfl⟩ := chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) b
    obtain ⟨w', rfl⟩ := chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) w
    simp only [← map_mul, hqh, Subgroup.coe_mul]
    exact hβ a' b' w'
  have hndh : ∀ a, a ≠ 1 → ∃ w, qh (a * w) - qh a - qh w ≠ 0 := by
    intro a ha
    obtain ⟨a', rfl⟩ := chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) a
    have ha' : (a' : W) ∉ fixV (P.K.map P.ρ) := fun h =>
      ha ((chiefQ_eq_one_iff a').mpr ⟨trivial, h⟩)
    have hrad : ¬ ∀ w, polarQ q a' w = 0 := fun h => ha' (hradC _ h)
    push Not at hrad
    obtain ⟨w, hw⟩ := hrad
    refine ⟨chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) ⟨w, trivial⟩, ?_⟩
    rw [← map_mul, hqh, hqh, hqh]
    exact hw
  obtain ⟨wh, hwh, hqwh⟩ := hQ _ hV2 _ _ A hB4 hA _ hcond hrk _ hchL hchv hch3 hch1 qh hqhL hβh
    hndh
  obtain ⟨u, rfl⟩ := chiefQ_surjective ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) wh
  rw [secAct_chiefQ] at hwh
  have hx : P.ρ c u * (u : W)⁻¹ ∈ fixV (P.K.map P.ρ) := by
    have h' : chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) ⟨P.ρ c u, trivial⟩ *
        (chiefQ ⊤ (⊤ ⊓ fixV (P.K.map P.ρ)) u)⁻¹ = 1 := by
      rw [hwh, mul_inv_cancel]
    rw [← map_inv, ← map_mul, chiefQ_eq_one_iff] at h'
    exact h'.2
  have hc3' : P.ρ c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  obtain ⟨y, hy, hfixy⟩ := exists_fix_mul_of_mem (P.ρ c) hc3'
    (not_three_dvd_card P.sq (fixV (P.K.map P.ρ)))
    (fun y hy => by rw [hy _ ⟨c, hcK, rfl⟩]; exact hy) hx
  refine ⟨(u : W) * y, hfixy, ?_⟩
  rw [hqCm _ _ hy, ← hqh]
  exact hqwh

end Hyp1321

end Quad

end CFSG.Quasithin.H13.A5
