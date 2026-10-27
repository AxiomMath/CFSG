module

public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.Quasithin.Background.Ordering
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

@[expose] def IsQuotientOfSQTK (X : Type*) [Group X] : Prop :=
  ∃ (S : Type) (_ : Group S) (_ : Finite S), CFSG.SectionRank.IsSQTKCat S ∧
    ∃ φ : S →* X, Function.Surjective φ

namespace G6

variable {V : Type*} [CommGroup V]

@[expose] def IsHSubmodule (H : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∀ h ∈ H, ∀ u ∈ U, h u ∈ U

@[expose] def commOn (X : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup V :=
  Subgroup.closure {w | ∃ x ∈ X, ∃ u ∈ U, x u * u⁻¹ = w}

@[expose] def submoduleClosure (X : Subgroup (MulAut V)) (W : Subgroup V) : Subgroup V :=
  ⨆ g ∈ X, W.map (g : MulAut V).toMonoidHom

@[expose] def classClosure (X : Subgroup (MulAut V)) (a : MulAut V) : Subgroup (MulAut V) :=
  conjClosure (Subgroup.zpowers a) X

theorem commV_eq_commOn_top (X : Subgroup (MulAut V)) : commV X = commOn X ⊤ := by
  unfold commV commOn
  congr 1
  ext w
  simp

theorem mem_commOn_of_mem {X : Subgroup (MulAut V)} {U : Subgroup V} {x : MulAut V} (hx : x ∈ X)
    {u : V} (hu : u ∈ U) : x u * u⁻¹ ∈ commOn X U :=
  Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩

theorem commOn_le_iff {X : Subgroup (MulAut V)} {U W : Subgroup V} :
    commOn X U ≤ W ↔ ∀ x ∈ X, ∀ u ∈ U, x u * u⁻¹ ∈ W := by
  constructor
  · intro h x hx u hu
    exact h (mem_commOn_of_mem hx hu)
  · intro h
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, u, hu, rfl⟩
    exact h x hx u hu

theorem commV_closure_le {S : Set (MulAut V)} {W : Subgroup V}
    (h : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ W) : commV (Subgroup.closure S) ≤ W :=
  CFSG.Quasithin.FixVLat.commV_closure_le h

theorem zpowers_le_classClosure (X : Subgroup (MulAut V)) (a : MulAut V) :
    Subgroup.zpowers a ≤ classClosure X a :=
  le_conjClosure _ _

theorem mem_classClosure_self (X : Subgroup (MulAut V)) (a : MulAut V) :
    a ∈ classClosure X a :=
  zpowers_le_classClosure X a (Subgroup.mem_zpowers a)

theorem conj_mem_classClosure {X : Subgroup (MulAut V)} {a g : MulAut V} (hg : g ∈ X) :
    g * a * g⁻¹ ∈ classClosure X a :=
  mem_conjClosure hg (Subgroup.mem_zpowers a)

theorem classClosure_le {X : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ X) :
    classClosure X a ≤ X :=
  conjClosure_le fun _ hg _ hz =>
    X.mul_mem (X.mul_mem hg ((Subgroup.zpowers_le.2 ha) hz)) (X.inv_mem hg)

theorem conj_mem_classClosure_of_mem {X : Subgroup (MulAut V)} {a g k : MulAut V} (hg : g ∈ X)
    (hk : k ∈ classClosure X a) : g * k * g⁻¹ ∈ classClosure X a :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure (Subgroup.zpowers a) X hg) k).1 hk

theorem pResidual_normal_aux {Y : Type*} [Group Y] (p : ℕ) : (pResidual p Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  simp only [pResidual, Subgroup.mem_iInf] at hn ⊢
  intro N hN hp
  exact hN.conj_mem n (hn N hN hp) g

theorem exists_pow_mem_pResidual {Y : Type*} [Group Y] [Finite Y] (p : ℕ) (y : Y) :
    ∃ m : ℕ, y ^ p ^ m ∈ pResidual p Y := by
  classical
  set 𝒮 : Set (Subgroup Y) := {N | N.Normal ∧ ∀ x : Y, ∃ k : ℕ, x ^ p ^ k ∈ N} with h𝒮
  have htop : (⊤ : Subgroup Y) ∈ 𝒮 := ⟨inferInstance, fun x => ⟨0, trivial⟩⟩
  obtain ⟨N₀, hN₀, hmin⟩ := (wellFounded_lt (α := Subgroup Y)).has_min 𝒮 ⟨⊤, htop⟩
  have hnorm : N₀.Normal := hN₀.1
  have hle : pResidual p Y ≤ N₀ := pResidual_le hN₀.2
  have hge : N₀ ≤ pResidual p Y := by
    refine le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_
    have hmem : N ⊓ N₀ ∈ 𝒮 := by
      refine ⟨inferInstance, fun x => ?_⟩
      obtain ⟨k₁, hk₁⟩ := hp x
      obtain ⟨k₂, hk₂⟩ := hN₀.2 x
      refine ⟨k₁ + k₂, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
      · rw [pow_add, pow_mul]
        exact N.pow_mem hk₁ _
      · rw [pow_add, mul_comm, pow_mul]
        exact N₀.pow_mem hk₂ _
    have heq : N ⊓ N₀ = N₀ := by
      by_contra hne
      exact hmin _ hmem (lt_of_le_of_ne inf_le_right hne)
    calc N₀ = N ⊓ N₀ := heq.symm
      _ ≤ N := inf_le_left
  obtain ⟨m, hm⟩ := hN₀.2 y
  exact ⟨m, (le_antisymm hle hge).symm ▸ hm⟩

structure Hypothesis61 [Finite V] (X : Subgroup (MulAut V)) (a : MulAut V) : Prop where
  sq_eq_one : ∀ v : V, v ^ 2 = 1
  pCoreOf_eq_bot : pCoreOf 2 X = ⊥
  isQuotientOfSQTK : IsQuotientOfSQTK X
  mem : a ∈ X
  ne_one : a ≠ 1
  mul_self : a * a = 1
  card_commV_le : Nat.card (commV (Subgroup.zpowers a)) ≤ 4
  span : submoduleClosure X (commV (Subgroup.zpowers a)) = ⊤

variable {X : Subgroup (MulAut V)} {a : MulAut V}

theorem lemma_G62_1 [Finite V] (h : Hypothesis61 X a) : commV (classClosure X a) = ⊤ := by
  rw [eq_top_iff, ← h.span]
  refine iSup₂_le fun g hg => ?_
  rw [Subgroup.map_le_iff_le_comap, commV_le_iff]
  intro x hx v
  rw [Subgroup.mem_comap]
  have h1 := mem_commV_of_mem (X := classClosure X a) (mem_conjClosure hg hx) (g v)
  have h2 : (g * x * g⁻¹) (g v) * (g v)⁻¹ = g (x v * v⁻¹) := by simp
  rw [h2] at h1
  exact h1

theorem lemma_G62_3 [Finite V] (h : Hypothesis61 X a) {H : Subgroup (MulAut V)}
    (hK : conjClosure (Subgroup.zpowers a) H = classClosure X a) {U : Subgroup V}
    (hU : IsHSubmodule H U) (hUa : commV (Subgroup.zpowers a) ≤ U) : U = ⊤ := by
  have hle : commV (classClosure X a) ≤ U := by
    rw [← hK]
    refine commV_closure_le ?_
    rintro s ⟨k, hk, z, hz, rfl⟩ v
    have h1 : (k * z * k⁻¹) v * v⁻¹ = k (z (k⁻¹ v) * (k⁻¹ v)⁻¹) := by simp
    rw [h1]
    exact hU k hk _ (hUa (mem_commV_of_mem hz _))
  rw [lemma_G62_1 h] at hle
  exact eq_top_iff.2 hle

theorem lemma_G62_2 [Finite V] (h : Hypothesis61 X a) :
    commV (pResidualOf 2 (classClosure X a)) = ⊤ := by
  set K := classClosure X a with hKdef
  by_contra hN
  refine commV_ne_top_of_two_power h.sq_eq_one (K := K) (N := pResidualOf 2 K) ?_ ?_ hN
    (lemma_G62_1 h)
  · intro k hk n hn
    obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨k, hk⟩ * n' * ⟨k, hk⟩⁻¹, ?_, rfl⟩
    exact (pResidual_normal_aux 2).conj_mem n' hn' ⟨k, hk⟩
  · intro k hk
    obtain ⟨m, hm⟩ := exists_pow_mem_pResidual 2 (⟨k, hk⟩ : K)
    exact ⟨m, Subgroup.mem_map.2 ⟨_, hm, by simp⟩⟩

private def fixPtwise (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {k | ∀ u ∈ U, k u = u}
  one_mem' := fun u _ => rfl
  mul_mem' := fun {x y} hx hy u hu => by
    show x (y u) = u
    rw [hy u hu, hx u hu]
  inv_mem' := fun {x} hx u hu => by
    show x.symm u = u
    rw [MulEquiv.symm_apply_eq]
    exact (hx u hu).symm

theorem lemma_G63 [Finite V] (h : Hypothesis61 X a) {U : Subgroup V}
    (hU : IsHSubmodule (classClosure X a) U)
    (hcase : conjClosure (Subgroup.zpowers a) (classClosure X a) = classClosure X a ∨
      IsHSubmodule X U) :
    commOn (classClosure X a) U = ⊥ ∨ U = ⊤ ∨
      (Nat.card (commOn (Subgroup.zpowers a) U) = 2 ∧
        Nat.card ((commV (Subgroup.zpowers a)).map (QuotientGroup.mk' U)) = 2) := by
  obtain ⟨H, hKH, hUH⟩ : ∃ H : Subgroup (MulAut V),
      conjClosure (Subgroup.zpowers a) H = classClosure X a ∧ IsHSubmodule H U := by
    rcases hcase with h1 | h2
    · exact ⟨classClosure X a, h1, hU⟩
    · exact ⟨X, rfl, h2⟩
  by_cases hUa : commOn (Subgroup.zpowers a) U = ⊥
  ·
    left
    have hfix : ∀ z ∈ Subgroup.zpowers a, ∀ u ∈ U, z u = u := by
      intro z hz u hu
      have := mem_commOn_of_mem hz hu
      rw [hUa, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have hKfix : classClosure X a ≤ fixPtwise U := by
      rw [← hKH]
      refine conjClosure_le fun k hk z hz u hu => ?_
      show (k * z * k⁻¹) u = u
      have h1 : k⁻¹ u ∈ U := hUH k⁻¹ (H.inv_mem hk) u hu
      have h2 : (k * z * k⁻¹) u = k (z (k⁻¹ u)) := rfl
      rw [h2, hfix z hz _ h1]
      simp
    rw [eq_bot_iff, commOn_le_iff]
    intro k hk u hu
    rw [hKfix hk u hu]
    simp
  · by_cases hVa : commV (Subgroup.zpowers a) ≤ U
    · right; left
      exact lemma_G62_3 h hKH hUH hVa
    · right; right
      set A := commV (Subgroup.zpowers a) with hA
      set B := commOn (Subgroup.zpowers a) U with hB
      have hzK : Subgroup.zpowers a ≤ classClosure X a := zpowers_le_classClosure X a
      have hBA : B ≤ A := commOn_le_iff.2 fun x hx u _ => mem_commV_of_mem hx u
      have hBU : B ≤ U := commOn_le_iff.2 fun x hx u hu =>
        U.mul_mem (hU x (hzK hx) u hu) (U.inv_mem hu)
      have hBAU : B ≤ A ⊓ U := le_inf hBA hBU
      have hrel : U.relIndex A * Nat.card ↥(U ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card U A
      have hr1 : U.relIndex A ≠ 1 := fun h1 => hVa (Subgroup.relIndex_eq_one.1 h1)
      have hApos : 0 < Nat.card A := Nat.card_pos
      have hr0 : U.relIndex A ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hrel
        omega
      have hbpos : 0 < Nat.card B := Nat.card_pos
      have hb1 : Nat.card B ≠ 1 := fun h1 => hUa (Subgroup.card_eq_one.1 h1)
      have hbdvd : Nat.card B ∣ Nat.card ↥(U ⊓ A) := by
        have : B ≤ U ⊓ A := by rw [inf_comm]; exact hBAU
        exact Subgroup.card_dvd_of_le this
      have h2pos : 0 < Nat.card ↥(U ⊓ A) := Nat.card_pos
      have hble : Nat.card B ≤ Nat.card ↥(U ⊓ A) := Nat.le_of_dvd h2pos hbdvd
      have hA4 : Nat.card A ≤ 4 := h.card_commV_le
      have hr2 : 2 ≤ U.relIndex A := by omega
      have hb2 : 2 ≤ Nat.card B := by omega
      have hrel2 : U.relIndex A = 2 := by
        by_contra hne
        have : 3 ≤ U.relIndex A := by omega
        nlinarith
      have hbeq : Nat.card B = 2 := by
        have : Nat.card ↥(U ⊓ A) ≤ 2 := by
          rw [hrel2] at hrel
          omega
        omega
      refine ⟨hbeq, ?_⟩
      rw [← hrel2, ← QuotientGroup.ker_mk' U, Subgroup.relIndex_ker, QuotientGroup.ker_mk']

end G6

end CFSG.Quasithin
