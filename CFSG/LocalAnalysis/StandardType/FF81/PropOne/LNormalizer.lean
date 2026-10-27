module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single_one)

private abbrev LN {G : Type} [Group G] {L : Subgroup G} (z : Fin 3 → ↥L) : Subgroup G :=
  L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G)

private abbrev toL {G : Type} [Group G] {L : Subgroup G} {z : Fin 3 → ↥L}
    (m : ↥(LN z)) : ↥L := ⟨m.1, m.2.1⟩

private theorem monoIndex_unique {H : Type} [Group H] {z : Fin 3 → H} (hm : GGFF.Model H z)
    {a : H} {i j j' : Fin 3}
    (h1 : a * z i * a⁻¹ = z j ∨ a * z i * a⁻¹ = (z j)⁻¹)
    (h2 : a * z i * a⁻¹ = z j' ∨ a * z i * a⁻¹ = (z j')⁻¹) : j = j' := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hm.eq_of_z_eq (Or.inl (h1.symm.trans h2))
  · exact hm.eq_of_z_eq (Or.inr (h1.symm.trans h2))
  · exact (hm.eq_of_z_eq (Or.inr (h2.symm.trans h1))).symm
  · exact hm.eq_of_z_eq (Or.inl (inv_inj.mp (h1.symm.trans h2)))

private theorem monoIndex_mul {H : Type} [Group H] {z : Fin 3 → H} {a c : H} {i j k : Fin 3}
    (ha : a * z j * a⁻¹ = z k ∨ a * z j * a⁻¹ = (z k)⁻¹)
    (hc : c * z i * c⁻¹ = z j ∨ c * z i * c⁻¹ = (z j)⁻¹) :
    (a * c) * z i * (a * c)⁻¹ = z k ∨ (a * c) * z i * (a * c)⁻¹ = (z k)⁻¹ := by
  rw [show (a * c) * z i * (a * c)⁻¹ = a * (c * z i * c⁻¹) * a⁻¹ by group]
  rcases hc with hc | hc
  · rw [hc]; exact ha
  · have e : a * (z j)⁻¹ * a⁻¹ = (a * z j * a⁻¹)⁻¹ := by group
    rw [hc, e]
    rcases ha with ha | ha
    · rw [ha]; exact Or.inr (by simp)
    · rw [ha]; exact Or.inl (by simp)

private theorem monoIndex_inv {H : Type} [Group H] {z : Fin 3 → H} {a : H} {i j : Fin 3}
    (ha : a⁻¹ * z i * a = z j ∨ a⁻¹ * z i * a = (z j)⁻¹) :
    a * z j * a⁻¹ = z i ∨ a * z j * a⁻¹ = (z i)⁻¹ := by
  rcases ha with ha | ha
  · left
    rw [← ha]; group
  · right
    have e : (a * z j * a⁻¹)⁻¹ = z i := by
      rw [show (a * z j * a⁻¹)⁻¹ = a * (z j)⁻¹ * a⁻¹ by group, ← ha]
      group
    rw [← e, inv_inv]

private theorem exists_mono {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {m : G} (hmL : m ∈ L)
    (hmN : m ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) (i : Fin 3) :
    ∃ j : Fin 3, (⟨m, hmL⟩ : ↥L) * z i * (⟨m, hmL⟩ : ↥L)⁻¹ = z j ∨
      (⟨m, hmL⟩ : ↥L) * z i * (⟨m, hmL⟩ : ↥L)⁻¹ = (z j)⁻¹ := by
  have hS := h.settingCore
  have hα : ∀ v, ∃ w, MulAut.conj (⟨m, hmL⟩ : ↥L) (vecElt z v) = vecElt z w := by
    intro v
    have hmem : m * vecElt (GGFF.zs z) v * m⁻¹ ∈ bOne z :=
      (Subgroup.mem_normalizer_iff.mp hmN _).mp (GGFF.vecElt_mem_tor _ v)
    obtain ⟨w, hw⟩ := hS.mem_torG.mp hmem
    refine ⟨w, Subtype.ext ?_⟩
    show m * vecElt (GGFF.zs z) v * m⁻¹ = vecElt (GGFF.zs z) w
    exact hw
  exact h.model.mono_of_aut _ hα i

private noncomputable def monoIndex {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (m : ↥(LN z))
    (i : Fin 3) : Fin 3 :=
  Classical.choose (exists_mono h m.2.1 m.2.2 i)

private theorem monoIndex_spec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (m : ↥(LN z)) (i : Fin 3) :
    toL m * z i * (toL m)⁻¹ = z (monoIndex h m i) ∨
      toL m * z i * (toL m)⁻¹ = (z (monoIndex h m i))⁻¹ :=
  Classical.choose_spec (exists_mono h m.2.1 m.2.2 i)

private theorem monoIndex_surj {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (m : ↥(LN z)) :
    Function.Surjective (monoIndex h m) := by
  intro i
  refine ⟨monoIndex h m⁻¹ i, ?_⟩
  refine monoIndex_unique h.model (monoIndex_spec h m (monoIndex h m⁻¹ i)) ?_
  have hcoee : toL (m⁻¹ : ↥(LN z)) = (toL m)⁻¹ := rfl
  have hspec := monoIndex_spec h m⁻¹ i
  rw [hcoee, inv_inv] at hspec
  exact monoIndex_inv hspec

private theorem monoIndex_one {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (i : Fin 3) :
    monoIndex h 1 i = i :=
  monoIndex_unique h.model (monoIndex_spec h 1 i)
    (Or.inl (by rw [show toL (1 : ↥(LN z)) = 1 from rfl]; group))

private theorem monoIndex_mul_spec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (m m' : ↥(LN z))
    (i : Fin 3) : monoIndex h (m * m') i = monoIndex h m (monoIndex h m' i) :=
  monoIndex_unique h.model (monoIndex_spec h (m * m') i)
    (monoIndex_mul (monoIndex_spec h m (monoIndex h m' i)) (monoIndex_spec h m' i))

private noncomputable def rhoHom {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ↥(LN z) →* Equiv.Perm (Fin 3) where
  toFun m := Equiv.ofBijective (monoIndex h m)
    (Finite.surjective_iff_bijective.mp (monoIndex_surj h m))
  map_one' := by
    apply Equiv.ext
    intro i
    simpa using monoIndex_one h i
  map_mul' m m' := by
    apply Equiv.ext
    intro i
    simpa using monoIndex_mul_spec h m m' i

private theorem unit_eq_one_or_neg_one (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide

private theorem unit_val_cases (u : (ZMod 3)ˣ) :
    (((u : (ZMod 3)ˣ) : ZMod 3)).val = 1 ∨ (((u : (ZMod 3)ˣ) : ZMod 3)).val = 2 := by
  revert u
  decide

private theorem pow_val_inj {H : Type} [Group H] {z : Fin 3 → H} (hm : GGFF.Model H z)
    (i : Fin 3) {e e' : ℕ} (he : e = 1 ∨ e = 2) (he' : e' = 1 ∨ e' = 2)
    (hz : z i ^ e = z i ^ e') : e = e' := by
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · rfl
  · exfalso
    rw [pow_one, pow_two] at hz
    have h' : (1 : H) * z i = z i * z i := by rw [one_mul]; exact hz
    exact hm.z_ne_one i (mul_right_cancel h').symm
  · exfalso
    rw [pow_one, pow_two] at hz
    have h' : z i * z i = z i * 1 := by rw [mul_one]; exact hz
    exact hm.z_ne_one i (mul_left_cancel h')
  · rfl

private theorem zpow_units_mul_eq {H : Type} [Group H] {z : Fin 3 → H} (hm : GGFF.Model H z)
    (i : Fin 3) (u v : (ZMod 3)ˣ) :
    z i ^ (((u : ZMod 3) * (v : ZMod 3)).val) =
      (z i ^ ((u : ZMod 3)).val) ^ ((v : ZMod 3)).val := by
  rcases unit_eq_one_or_neg_one u with rfl | rfl <;>
  rcases unit_eq_one_or_neg_one v with rfl | rfl
  · rw [show (((1 : (ZMod 3)ˣ) : ZMod 3) * ((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide,
        show (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide]
    simp
  · rw [show (((1 : (ZMod 3)ˣ) : ZMod 3) * ((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 by decide,
        show (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide,
        show (((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 by decide]
    simp
  · rw [show (((-1 : (ZMod 3)ˣ) : ZMod 3) * ((1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 by decide,
        show (((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 by decide,
        show (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide]
    simp
  · rw [show (((-1 : (ZMod 3)ˣ) : ZMod 3) * ((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide,
        show (((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 by decide]
    rw [show (z i ^ 2) ^ 2 = z i by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hm.pow_z, one_mul, pow_one]]
    simp

private noncomputable def epsFun {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (m : ↥(rhoHom h).ker) (i : Fin 3) : (ZMod 3)ˣ := by
  classical
  exact if toL (m : ↥(LN z)) * z i * (toL (m : ↥(LN z)))⁻¹ = z i then 1 else -1

private theorem epsFun_spec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (m : ↥(rhoHom h).ker) (i : Fin 3) :
    toL (m : ↥(LN z)) * z i * (toL (m : ↥(LN z)))⁻¹ =
      z i ^ (((epsFun h m i : (ZMod 3)ˣ) : ZMod 3)).val := by
  classical
  by_cases hcase : toL (m : ↥(LN z)) * z i * (toL (m : ↥(LN z)))⁻¹ = z i
  · rw [epsFun, if_pos hcase, hcase,
      show (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide, pow_one]
  · rw [epsFun, if_neg hcase]
    have hm : rhoHom h (m : ↥(LN z)) = 1 := m.2
    have hmi : monoIndex h (m : ↥(LN z)) i = i := by
      have := congrArg (fun e : Equiv.Perm (Fin 3) => e i) hm
      simpa [rhoHom, Equiv.ofBijective_apply] using this
    have hspec := monoIndex_spec h (m : ↥(LN z)) i
    rw [hmi] at hspec
    rcases hspec with hspec | hspec
    · exact absurd hspec hcase
    · rw [hspec,
        show (((-1 : (ZMod 3)ˣ) : ZMod 3)).val = 2 by decide]
      exact (eq_inv_iff_mul_eq_one.mpr (by rw [← pow_succ, h.model.pow_z])).symm

private theorem epsFun_mul {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (m m' : ↥(rhoHom h).ker) (i : Fin 3) :
    epsFun h (m * m') i = epsFun h m i * epsFun h m' i := by
  apply Units.ext
  apply ZMod.val_injective
  rw [Units.val_mul]
  have key : z i ^ (((epsFun h (m * m') i : (ZMod 3)ˣ) : ZMod 3)).val =
      z i ^ (((epsFun h m i : (ZMod 3)ˣ) : ZMod 3) *
        ((epsFun h m' i : (ZMod 3)ˣ) : ZMod 3)).val := by
    calc z i ^ (((epsFun h (m * m') i : (ZMod 3)ˣ) : ZMod 3)).val
        = toL ((m * m' : ↥(rhoHom h).ker) : ↥(LN z)) * z i *
            (toL ((m * m' : ↥(rhoHom h).ker) : ↥(LN z)))⁻¹ :=
          (epsFun_spec h (m * m') i).symm
      _ = toL (m : ↥(LN z)) *
            (toL (m' : ↥(LN z)) * z i * (toL (m' : ↥(LN z)))⁻¹) *
            (toL (m : ↥(LN z)))⁻¹ := by
          rw [show toL ((m * m' : ↥(rhoHom h).ker) : ↥(LN z)) =
            toL (m : ↥(LN z)) * toL (m' : ↥(LN z)) from rfl]
          group
      _ = toL (m : ↥(LN z)) *
            z i ^ (((epsFun h m' i : (ZMod 3)ˣ) : ZMod 3)).val *
            (toL (m : ↥(LN z)))⁻¹ := by rw [epsFun_spec h m' i]
      _ = (toL (m : ↥(LN z)) * z i * (toL (m : ↥(LN z)))⁻¹) ^
            (((epsFun h m' i : (ZMod 3)ˣ) : ZMod 3)).val := (conj_pow).symm
      _ = (z i ^ (((epsFun h m i : (ZMod 3)ˣ) : ZMod 3)).val) ^
            (((epsFun h m' i : (ZMod 3)ˣ) : ZMod 3)).val := by rw [epsFun_spec h m i]
      _ = z i ^ ((((epsFun h m i : (ZMod 3)ˣ) : ZMod 3) *
            ((epsFun h m' i : (ZMod 3)ˣ) : ZMod 3)).val) :=
          (zpow_units_mul_eq h.model i (epsFun h m i) (epsFun h m' i)).symm
  exact pow_val_inj h.model i (unit_val_cases (epsFun h (m * m') i))
    (by rw [← Units.val_mul]; exact unit_val_cases (epsFun h m i * epsFun h m' i)) key

private noncomputable def epsHom {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ↥(rhoHom h).ker →* (Fin 3 → (ZMod 3)ˣ) where
  toFun m := fun i => epsFun h m i
  map_one' := by
    classical
    funext i
    show epsFun h 1 i = 1
    rw [epsFun, if_pos (show toL (↑(1 : ↥(rhoHom h).ker) : ↥(LN z)) * z i *
      (toL (↑(1 : ↥(rhoHom h).ker) : ↥(LN z)))⁻¹ = z i from by
        show (1 : ↥L) * z i * (1 : ↥L)⁻¹ = z i
        group)]
  map_mul' m m' := by
    funext i
    exact epsFun_mul h m m' i

private theorem zs_mem_bOne {G : Type} [Group G] {L : Subgroup G} {z : Fin 3 → ↥L}
    (i : Fin 3) : GGFF.zs z i ∈ bOne z := by
  have := GGFF.vecElt_mem_tor (GGFF.zs z) (Pi.single i 1)
  rwa [vecElt_single_one] at this

private theorem epsHom_ker {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    (epsHom h).ker = ((bOne z).subgroupOf (LN z)).subgroupOf (rhoHom h).ker := by
  have hS := h.settingCore
  classical
  ext m
  constructor
  · intro hm
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hkey : ∀ i, toL (m : ↥(LN z)) * z i = z i * toL (m : ↥(LN z)) := by
      intro i
      have hspec := epsFun_spec h m i
      have h1 : epsFun h m i = 1 := by
        simpa [epsHom] using congrFun hm i
      rw [h1, show (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 by decide, pow_one] at hspec
      calc toL (m : ↥(LN z)) * z i
          = toL (m : ↥(LN z)) * z i * (toL (m : ↥(LN z)))⁻¹ * toL (m : ↥(LN z)) := by
            group
        _ = z i * toL (m : ↥(LN z)) := by rw [hspec]
    obtain ⟨v, hv⟩ :=
      CFSG.StandardType.FF81.cen_of_model h.hypA.n_cases h.hypA.model h.model
        (toL (m : ↥(LN z))) hkey
    have hmem : (toL (m : ↥(LN z)) : G) ∈ bOne z := by
      rw [hv]
      exact GGFF.vecElt_mem_tor _ v
    simpa [toL] using hmem
  · intro hm
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hm
    funext i
    have hmB : (toL (m : ↥(LN z)) : G) ∈ bOne z := by simpa [toL] using hm
    have hziB : (z i : G) ∈ bOne z := zs_mem_bOne i
    have hcommG : (toL (m : ↥(LN z)) : G) * (z i : G) =
        (z i : G) * (toL (m : ↥(LN z)) : G) := by
      simpa using congrArg Subtype.val
        ((GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).1.is_comm.comm
          (⟨(toL (m : ↥(LN z)) : G), hmB⟩ : ↥(bOne z))
          (⟨(z i : G), hziB⟩ : ↥(bOne z)))
    have hcomm : toL (m : ↥(LN z)) * z i = z i * toL (m : ↥(LN z)) := by
      apply Subtype.ext
      simpa using hcommG
    show epsFun h m i = 1
    rw [epsFun, if_pos (by rw [hcomm]; group)]

private abbrev Bsub {G : Type} [Group G] {L : Subgroup G} (z : Fin 3 → ↥L) :
    Subgroup ↥(LN z) :=
  (bOne z).subgroupOf (LN z)

private theorem bOne_comm {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    (hS : GGFF.SettingCore b L z) {x y : G} (hx : x ∈ bOne z) (hy : y ∈ bOne z) :
    x * y = y * x := by
  have h := (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val h

private theorem Bsub_comm {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {x y : ↥(LN z)}
    (hx : x ∈ Bsub z) (hy : y ∈ Bsub z) : x * y = y * x := by
  apply Subtype.ext
  exact bOne_comm h.settingCore (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)

private theorem tau_inv_bOne {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    (hS : GGFF.SettingCore b L z) {τ : G}
    (hτz : ∀ i, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹) {x : G} (hx : x ∈ bOne z) :
    τ * x * τ⁻¹ = x⁻¹ := by
  have hx' : x ∈ Subgroup.closure (Set.range (GGFF.zs z)) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hτz i
  | one => simp
  | mul a b ha hb iha ihb =>
      have hcomm : a * b = b * a := bOne_comm hS ha hb
      calc τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [iha, ihb]
        _ = (b * a)⁻¹ := (mul_inv_rev b a).symm
        _ = (a * b)⁻¹ := by rw [hcomm]
  | inv a _ iha =>
      rw [show τ * a⁻¹ * τ⁻¹ = (τ * a * τ⁻¹)⁻¹ by group, iha, inv_inv]

private theorem Bsub_le_ker {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : Bsub z ≤ (rhoHom h).ker := by
  intro m hm
  rw [Subgroup.mem_subgroupOf] at hm
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro i
  change monoIndex h m i = i
  refine monoIndex_unique h.model (monoIndex_spec h m i) (Or.inl ?_)
  have hx : (toL m : G) ∈ bOne z := by simpa [toL] using hm
  have hy : (z i : G) ∈ bOne z := zs_mem_bOne i
  have hcommG := bOne_comm h.settingCore hx hy
  have hcomm : toL m * z i = z i * toL m := Subtype.ext (by simpa using hcommG)
  rw [hcomm]; group

private theorem Bsub_le_LN {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (_h : Counterexample G n b L z) : bOne z ≤ LN z :=
  le_inf (GGFF.SettingCore.tor_le z) Subgroup.le_normalizer

private theorem card_Bsub {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : Nat.card (Bsub z) = 27 := by
  rw [← Subgroup.card_map_of_injective (LN z).subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (Bsub_le_LN h)]
  exact h.settingCore.card_torG

private theorem card_subgroup_dvd {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) (X : Subgroup ↥(LN z)) :
    Nat.card X ∣ 48 * Nat.card (X ⊓ Bsub z : Subgroup ↥(LN z)) := by
  let K := (rhoHom h).ker
  let B := Bsub z
  have hBK : B ≤ K := Bsub_le_ker h
  let XK : Subgroup ↥(LN z) := X ⊓ K
  have hXK_le_X : XK ≤ X := inf_le_left
  have hXK_le_K : XK ≤ K := inf_le_right
  have hcard_perm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  have hcard_units : Nat.card (Fin 3 → (ZMod 3)ˣ) = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    have : Fintype.card (ZMod 3)ˣ = 2 := by decide
    rw [this]; norm_num
  have h1 : Nat.card X = Nat.card (X ⧸ XK.subgroupOf X) * Nat.card (XK.subgroupOf X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (XK.subgroupOf X)
  have hkerX : ((rhoHom h).comp X.subtype).ker = XK.subgroupOf X := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, XK,
      Subgroup.mem_inf]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have h2 : Nat.card (X ⧸ XK.subgroupOf X) ∣ 6 := by
    rw [← hkerX,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ((rhoHom h).comp X.subtype)).toEquiv,
      ← hcard_perm]
    exact Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (XK.subgroupOf X) = Nat.card XK := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hXK_le_X]
  have h4 : Nat.card XK = Nat.card (XK ⧸ (B.subgroupOf XK)) * Nat.card (B.subgroupOf XK) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf XK)
  let εX : ↥XK →* (Fin 3 → (ZMod 3)ˣ) := (epsHom h).comp (Subgroup.inclusion hXK_le_K)
  have hεXker : εX.ker = B.subgroupOf XK := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (epsHom h) (Subgroup.inclusion hXK_le_K x) = 1 ↔ (x : ↥(LN z)) ∈ B
    rw [← MonoidHom.mem_ker, epsHom_ker h, Subgroup.mem_subgroupOf]
    rfl
  have h5 : Nat.card (XK ⧸ (B.subgroupOf XK)) ∣ 8 := by
    rw [← hεXker, Nat.card_congr (QuotientGroup.quotientKerEquivRange εX).toEquiv,
      ← hcard_units]
    exact Subgroup.card_subgroup_dvd_card _
  have h6 : Nat.card (B.subgroupOf XK) = Nat.card (X ⊓ B : Subgroup ↥(LN z)) := by
    have hmap : (B.subgroupOf XK).map (Subgroup.inclusion hXK_le_X) = (X ⊓ B).subgroupOf X := by
      apply le_antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact ⟨(Subgroup.mem_inf.mp x.2).1, hx⟩
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        exact ⟨⟨(y : ↥(LN z)),
          Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).1, hBK (Subgroup.mem_inf.mp hy).2⟩⟩,
          (Subgroup.mem_inf.mp hy).2, rfl⟩
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXK_le_X), hmap,
      ← Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hkey : Nat.card (X ⧸ XK.subgroupOf X) * Nat.card (XK ⧸ (B.subgroupOf XK)) ∣ 48 := by
    have h2' : Nat.card (X ⧸ XK.subgroupOf X) * Nat.card (XK ⧸ (B.subgroupOf XK)) ∣
        6 * Nat.card (XK ⧸ (B.subgroupOf XK)) := Nat.mul_dvd_mul_right h2 _
    have h5' : 6 * Nat.card (XK ⧸ (B.subgroupOf XK)) ∣ 6 * 8 := Nat.mul_dvd_mul_left 6 h5
    exact h2'.trans (by simpa using h5')
  calc Nat.card X
      = (Nat.card (X ⧸ XK.subgroupOf X) * Nat.card (XK ⧸ (B.subgroupOf XK))) *
          Nat.card (X ⊓ B : Subgroup ↥(LN z)) := by rw [h1, h3, h4, h6]; ring
    _ ∣ 48 * Nat.card (X ⊓ B : Subgroup ↥(LN z)) := Nat.mul_dvd_mul_right hkey _

private theorem isSolvable_LN {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : IsSolvable ↥(LN z) := by
  let K := (rhoHom h).ker
  let B := Bsub z
  have hBK : B ≤ K := Bsub_le_ker h
  have hBnorm : (B.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBK]
    intro k _
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      have hkN : (k : G) ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := k.2.2
      exact (Subgroup.mem_normalizer_iff.mp hkN (b : G)).mp (by simpa using hb)
    · intro hb
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      have hkN : (k : G)⁻¹ ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
        (Subgroup.normalizer _).inv_mem k.2.2
      have hmem : (k : G)⁻¹ * ((k : G) * (b : G) * (k : G)⁻¹) * (k : G)⁻¹⁻¹ ∈ bOne z :=
        (Subgroup.mem_normalizer_iff.mp hkN _).mp (by simpa using hb)
      simpa [mul_assoc, inv_inv] using hmem
  have : (B.subgroupOf K).Normal := hBnorm
  have hB_sol : IsSolvable ↥(B.subgroupOf K) :=
    Group.isSolvable_of_comm fun x y => by
      apply Subtype.ext
      apply Subtype.ext
      exact Bsub_comm h (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2)
  have : IsSolvable ↥(B.subgroupOf K) := hB_sol
  have hKB' : IsSolvable (K ⧸ (epsHom h).ker) := by
    have hpi : IsSolvable (Fin 3 → (ZMod 3)ˣ) :=
      Group.isSolvable_of_comm fun f g => by
        ext i
        simp [mul_comm]
    have : Group.IsSolvable ↥(epsHom h).range :=
      @Group.isSolvable_of_isSolvable_injective _ _ _ _ (Subgroup.subtype (epsHom h).range)
        (Subgroup.subtype_injective _) hpi
    exact Group.isSolvable_of_isSolvable_injective
      (QuotientGroup.quotientKerEquivRange (epsHom h)).injective
  have hKB : IsSolvable (K ⧸ B.subgroupOf K) :=
    @Group.isSolvable_of_isSolvable_injective (K ⧸ B.subgroupOf K) (K ⧸ (epsHom h).ker) _ _
      (QuotientGroup.quotientMulEquivOfEq (epsHom_ker h)).symm.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq (epsHom_ker h)).symm.injective hKB'
  have : IsSolvable (K ⧸ B.subgroupOf K) := hKB
  have hK : IsSolvable K :=
    @Group.isSolvable_of_subgroup_quotient _ _ (B.subgroupOf K) hBnorm hB_sol hKB
  have : IsSolvable K := hK
  have hMK : IsSolvable (↥(LN z) ⧸ K) := by
    have hperm : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Equiv.Perm.isSolvable (α := Fin 3)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have : Group.IsSolvable ↥(rhoHom h).range :=
      @Group.isSolvable_of_isSolvable_injective _ _ _ _ (Subgroup.subtype (rhoHom h).range)
        (Subgroup.subtype_injective _) hperm
    exact Group.isSolvable_of_isSolvable_injective
      (QuotientGroup.quotientKerEquivRange (rhoHom h)).injective
  have : IsSolvable (↥(LN z) ⧸ K) := hMK
  exact @Group.isSolvable_of_subgroup_quotient _ _ K inferInstance hK hMK

private noncomputable def dGrpHom {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ↥(Subgroup.zpowers b) × ↥(LN z) →* ↥(dGrp b z) :=
  MonoidHom.noncommCoprod
    (Subgroup.inclusion (show Subgroup.zpowers b ≤ dGrp b z from le_sup_left))
    (Subgroup.inclusion (show LN z ≤ dGrp b z from le_sup_right))
    (fun p q => by
      apply Subtype.ext
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp p.2
      show (p.1 : G) * (q.1 : G) = (q.1 : G) * (p.1 : G)
      rw [← hj]
      exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
        (h.hypA.le q.2.1)) j).symm).eq)

private theorem exists_mul_of_mem_sup {G : Type} [Group G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  have hx' : x ∈ Subgroup.closure ((H : Set G) ∪ (K : Set G)) := by
    rw [Subgroup.sup_eq_closure] at hx
    exact hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := iha
      obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := ihb
      exact ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, by
        rw [show y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ by group,
          hcomm y₂ hy₂ z₁ hz₁]
        group⟩
  | inv a _ iha =>
      obtain ⟨y, hy, z, hz, rfl⟩ := iha
      exact ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, by
        rw [mul_inv_rev]
        exact hcomm y⁻¹ (H.inv_mem hy) z⁻¹ (K.inv_mem hz)⟩

private theorem dGrpHom_surj {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : Function.Surjective (dGrpHom h) := by
  intro d
  obtain ⟨y, hy, w, hw, hyw⟩ :=
    exists_mul_of_mem_sup (H := Subgroup.zpowers b) (K := LN z) (fun y hy w hw => by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hj]
      exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
        (h.hypA.le hw.1)) j).symm).eq) d.2
  exact ⟨⟨⟨y, hy⟩, ⟨w, hw⟩⟩, Subtype.ext hyw⟩

private theorem dGrpHom_inj {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : Function.Injective (dGrpHom h) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro p hp
  rw [MonoidHom.mem_ker] at hp
  have hval : p.1.1 * p.2.1 = 1 := by
    have h := congrArg Subtype.val hp
    change p.1.1 * p.2.1 = 1 at h
    exact h
  have hbot : Subgroup.zpowers b ⊓ LN z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx.1
    rw [← hj] at hx ⊢
    exact h.settingCore.zpow_eq_one_of_mem hx.2.1
  have hp1L : p.1.1 ∈ LN z := by
    have h1 : p.1.1 = (p.2.1)⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact hval
    rw [h1]
    exact (LN z).inv_mem p.2.2
  have hp1 : p.1.1 = 1 := by
    have : p.1.1 ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨p.1.2, hp1L⟩
    simpa using this
  have hp2 : p.2.1 = 1 := by
    rw [hp1, one_mul] at hval
    exact hval
  exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)

private theorem card_dGrp {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    Nat.card ↥(dGrp b z) = 3 * Nat.card ↥(LN z) := by
  rw [← Nat.card_congr (Equiv.ofBijective (dGrpHom h) ⟨dGrpHom_inj h, dGrpHom_surj h⟩),
    Nat.card_prod, Nat.card_zpowers, h.hypA.ord]

private theorem card_LN_dvd {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : Nat.card ↥(LN z) ∣ 1296 := by
  have htop := card_subgroup_dvd h (⊤ : Subgroup ↥(LN z))
  rw [Nat.card_congr (Subgroup.topEquiv (G := ↥(LN z))).toEquiv, top_inf_eq, card_Bsub h,
    show 48 * 27 = 1296 from by norm_num] at htop
  exact htop

theorem isSolvable_dGrp {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : IsSolvable ↥(dGrp b z) := by
  have : Group.IsSolvable ↥(Subgroup.zpowers b) :=
    Group.isSolvable_of_comm fun x y => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      apply Subtype.ext
      change (x : G) * (y : G) = (y : G) * (x : G)
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow (Commute.refl b) i j).eq
  have : Group.IsSolvable ↥(LN z) := isSolvable_LN h
  have : Group.IsSolvable (↥(Subgroup.zpowers b) × ↥(LN z)) := inferInstance
  exact Group.isSolvable_of_surjective (f := dGrpHom h) (dGrpHom_surj h)

theorem prime_eq_two_or_three_of_dvd_dGrp {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(dGrp b z) → p = 2 ∨ p = 3 := by
  intro p hp hpD
  have hp' : p ∣ 3 * 1296 :=
    dvd_trans (card_dGrp h ▸ hpD) (Nat.mul_dvd_mul_left 3 (card_LN_dvd h))
  have h3888 : 3 * 1296 = 2 ^ 4 * 3 ^ 5 := by norm_num
  rw [h3888] at hp'
  rcases (Nat.Prime.dvd_mul hp).mp hp' with h | h
  · left
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)

theorem not_nine_dvd_card_cen_tau {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {τ : G} (hτL : τ ∈ L)
    (hτ2 : τ ^ 2 = 1) (hτz : ∀ i : Fin 3, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹) :
    ¬ 9 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({τ} : Set G)) := by
  have _ : τ ∈ L := hτL
  have _ : τ ^ 2 = 1 := hτ2
  intro h9
  let C : Subgroup G := L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) ⊓
    Subgroup.centralizer ({τ} : Set G)
  have hCM : C ≤ LN z := inf_le_left
  have hCB : C ⊓ bOne z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxC, hxB⟩ := hx
    rw [Subgroup.mem_inf] at hxC
    obtain ⟨_, hxτ⟩ := hxC
    have hxτ' : τ * x * τ⁻¹ = x := by
      have h := (Subgroup.mem_centralizer_iff.mp hxτ) τ (Set.mem_singleton τ)
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    have hxinv : τ * x * τ⁻¹ = x⁻¹ := tau_inv_bOne h.settingCore hτz hxB
    have hx1 : x = x⁻¹ := hxτ'.symm.trans hxinv
    have hx2 : x ^ 2 = 1 := by
      have h := congrArg (fun y => y * x) hx1
      rw [inv_mul_cancel] at h
      simpa [pow_two] using h
    have hx3 : x ^ 3 = 1 :=
      (GGFF.isElemAbelian_tor h.settingCore.zs_pow h.settingCore.zs_comm).2 x hxB
    have hx3x : x ^ 3 = x := by rw [pow_succ, hx2, one_mul]
    calc x = x ^ 3 := hx3x.symm
      _ = 1 := hx3
  have hXbot : (C.subgroupOf (LN z)) ⊓ Bsub z = ⊥ := by
    have hsub : (C.subgroupOf (LN z)) ⊓ Bsub z =
        (C ⊓ bOne z : Subgroup G).subgroupOf (LN z) := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hsub, hCB]
    simp
  have hXcard : Nat.card ↥(C.subgroupOf (LN z)) = Nat.card ↥C := by
    rw [← Subgroup.card_map_of_injective (LN z).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hCM]
  have hX := card_subgroup_dvd h (C.subgroupOf (LN z))
  rw [hXcard, hXbot, Subgroup.card_bot, mul_one] at hX
  exact absurd (h9.trans hX) (by norm_num)

end CFSG.StandardType.FF81.PropOne

end
