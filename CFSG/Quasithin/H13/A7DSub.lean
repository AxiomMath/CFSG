module

public import CFSG.Quasithin.H13.A7XElement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem le_normalizer_of_conj_mem {H J : Subgroup G}
    (h : ∀ g ∈ J, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : J ≤ normalizer (H : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact h g hg x
  · intro hx
    have h1 := h g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 hx
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    rwa [inv_inv] at h1

theorem commutator_props {A J : Subgroup G} (hJA : J ≤ normalizer (A : Set G)) :
    J ≤ normalizer ((⁅A, J⁆ : Subgroup G) : Set G) ∧ ⁅A, J⁆ ≤ A := by
  refine ⟨le_normalizer_of_conj_mem fun g hg x hx => ?_, ?_⟩
  · have h1 : (⁅A, J⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⁅A, J⁆ := by
      rw [map_commutator, map_conj_eq_of_mem_normalizer (hJA hg),
        map_conj_eq_of_mem_normalizer (le_normalizer hg)]
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  · rw [commutator_le]
    intro a ha j hj
    rw [commutatorElement_def]
    have h1 : j * a⁻¹ * j⁻¹ ∈ A := (mem_normalizer_iff.1 (hJA hj) _).1 (inv_mem ha)
    have h2 := mul_mem ha h1
    rwa [← mul_assoc, ← mul_assoc] at h2

@[expose] def commSeq (X J : Subgroup G) : ℕ → Subgroup G
  | 0 => X
  | n + 1 => ⁅commSeq X J n, J⁆

theorem commSeq_props {X J : Subgroup G} (hJX : J ≤ normalizer (X : Set G)) (n : ℕ) :
    J ≤ normalizer (commSeq X J n : Set G) ∧ commSeq X J n ≤ X := by
  induction n with
  | zero => exact ⟨hJX, le_rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := commutator_props ih.1
    exact ⟨h1, h2.trans ih.2⟩

theorem exists_commutator_stable [Finite G] {X J : Subgroup G}
    (hJX : J ≤ normalizer (X : Set G)) :
    ∃ m, commSeq X J (m + 1) = commSeq X J m := by
  by_contra hc
  push Not at hc
  have hlt : ∀ n, Nat.card (commSeq X J (n + 1)) < Nat.card (commSeq X J n) := by
    intro n
    have hle : commSeq X J (n + 1) ≤ commSeq X J n := (commutator_props (commSeq_props hJX n).1).2
    refine lt_of_le_of_ne (card_le_of_le hle) fun h => hc n ?_
    exact eq_of_le_of_card_ge hle h.ge
  have hbound : ∀ n, Nat.card (commSeq X J n) + n ≤ Nat.card X := by
    intro n
    induction n with
    | zero => simp [commSeq]
    | succ n ih =>
      have := hlt n
      omega
  have h1 := hbound (Nat.card X)
  have h2 : 0 < Nat.card (commSeq X J (Nat.card X)) := Nat.card_pos
  omega

theorem word_conj_cyc016 : ∀ u, sevenWord u * cyc016 * (sevenWord u)⁻¹ = cyc016 ∨
    sevenWord u * cyc016 * (sevenWord u)⁻¹ = cyc016⁻¹ := by
  decide +kernel

theorem cyc016_comm_swap01 : ∀ i : Fin 3, i ≠ 0 → ∃ i' : Fin 3, i' ≠ 0 ∧
    cyc016 ^ (i : ℕ) * swap 0 1 * (cyc016 ^ (i : ℕ))⁻¹ * (swap 0 1)⁻¹ = cyc016 ^ (i' : ℕ) := by
  decide +kernel

@[expose] noncomputable def kerK {K : Subgroup G}
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) : Subgroup G :=
  (kAct eK).ker.map (normalizer (K : Set G)).subtype

theorem mem_kerK {K : Subgroup G} (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    {g : G} : g ∈ kerK eK ↔ ∃ hg : g ∈ normalizer (K : Set G), kAct eK ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem kerK_le_normalizer {K : Subgroup G}
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    kerK eK ≤ normalizer (K : Set G) := map_subtype_le _

theorem conj_mem_kerK {K : Subgroup G} (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    {g y : G} (hg : g ∈ normalizer (K : Set G)) (hy : y ∈ kerK eK) :
    g * y * g⁻¹ ∈ kerK eK := by
  obtain ⟨hyN, hy1⟩ := (mem_kerK eK).1 hy
  refine (mem_kerK eK).2 ⟨mul_mem (mul_mem hg hyN) (inv_mem hg), ?_⟩
  rw [show (⟨g * y * g⁻¹, mul_mem (mul_mem hg hyN) (inv_mem hg)⟩ : normalizer (K : Set G)) =
    ⟨g, hg⟩ * ⟨y, hyN⟩ * ⟨g, hg⟩⁻¹ from rfl, map_mul, map_mul, map_inv, hy1, mul_one,
    mul_inv_cancel]

theorem A7NatConfig.exists_D [Finite G] {T L V : Subgroup G}
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig T L V ψ)
    (hTL : T ≤ normalizer (L : Set G)) {e : V} (hTe : T ≤ centralizer ({(e : G)} : Set G))
    {K : Subgroup G} (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (hCK : centralizer ({(e : G)} : Set G) ≤ normalizer (K : Set G))
    (hTP : ∀ t ∈ T, ∃ u, IsCoordAct ψ t (sevenWord u))
    {J : Subgroup G} (hJT : J ≤ T) {j₀ : G} (hj₀ : j₀ ∈ J) (hj₀l : IsCoordAct ψ j₀ (swap 0 1))
    {x : G} (hxL : x ∈ L) (hxe : x ∈ centralizer ({(e : G)} : Set G))
    (hxK : kAct eK ⟨x, hCK hxe⟩ = 1) {i₀ : Fin 3} (hi₀ : i₀ ≠ 0)
    (hxl : IsCoordAct ψ x (cyc016 ^ (i₀ : ℕ))) :
    ∃ D : Subgroup G, D = ⁅D, J⁆ ∧ J ≤ normalizer (D : Set G) ∧ D ≤ L ∧
      D ≤ centralizer ({(e : G)} : Set G) ∧ D ≤ kerK eK ∧ D ≤ normalizer (V : Set G) ∧
      (∀ d ∈ D, ∃ σ ∈ zpowers cyc016, IsCoordAct ψ d σ) ∧
      ∃ d₀ ∈ D, ∃ i : Fin 3, i ≠ 0 ∧ IsCoordAct ψ d₀ (cyc016 ^ (i : ℕ)) := by
  classical
  set N := normalizer (V : Set G) with hNdef
  set lamN : N →* Perm (Fin 7) := coordRep ψ le_rfl h.Nact with hlamN
  have hspec : ∀ m : N, IsCoordAct ψ m (lamN m) := coordRep_spec ψ le_rfl h.Nact
  have heq : ∀ (m : N) {σ : Perm (Fin 7)}, IsCoordAct ψ m σ → lamN m = σ := fun m σ hσ =>
    IsCoordAct.unique ψ m.2 (hspec m) hσ
  have hJN : J ≤ N := hJT.trans h.T_le
  have hxN : x ∈ N := h.L_le hxL
  set X : Subgroup G := conjClosure (zpowers x) J with hXdef
  have hJX : J ≤ normalizer (X : Set G) := le_normalizer_conjClosure _ _
  have hXL : X ≤ L := conjClosure_le fun j hj y hy =>
    (mem_normalizer_iff.1 (hTL (hJT hj)) y).1 ((zpowers_le.2 hxL) hy)
  have hXe : X ≤ centralizer ({(e : G)} : Set G) := conjClosure_le fun j hj y hy =>
    mul_mem (mul_mem (hTe (hJT hj)) ((zpowers_le.2 hxe) hy)) (inv_mem (hTe (hJT hj)))
  have hxkerK : x ∈ kerK eK := (mem_kerK eK).2 ⟨hCK hxe, hxK⟩
  have hXK : X ≤ kerK eK := conjClosure_le fun j hj y hy =>
    conj_mem_kerK eK (hCK (hTe (hJT hj))) ((zpowers_le.2 hxkerK) hy)
  have hXN : X ≤ N := conjClosure_le fun j hj y hy =>
    mul_mem (mul_mem (hJN hj) ((zpowers_le.2 hxN) hy)) (inv_mem (hJN hj))
  set Zc : Subgroup G := ((zpowers cyc016).comap lamN).map N.subtype with hZcdef
  have hmemZc : ∀ g (hg : g ∈ N), lamN ⟨g, hg⟩ ∈ zpowers cyc016 → g ∈ Zc :=
    fun g hg h1 => ⟨⟨g, hg⟩, h1, rfl⟩
  have hxZc : x ∈ Zc := hmemZc x hxN ⟨(i₀ : ℤ), by rw [heq _ hxl]; exact zpow_natCast _ _⟩
  have hXZc : X ≤ Zc := by
    refine conjClosure_le fun j hj y hy => ?_
    have hyZc := (zpowers_le.2 hxZc) hy
    obtain ⟨⟨y', hy'N⟩, hy'c, hyy'⟩ := hyZc
    have hy'eq : y' = y := hyy'
    subst hy'eq
    have hjN := hJN hj
    refine hmemZc _ (mul_mem (mul_mem hjN hy'N) (inv_mem hjN)) ?_
    rw [show (⟨j * y' * j⁻¹, mul_mem (mul_mem hjN hy'N) (inv_mem hjN)⟩ : N) =
      ⟨j, hjN⟩ * ⟨y', hy'N⟩ * ⟨j, hjN⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
    obtain ⟨u, hu⟩ := hTP j (hJT hj)
    rw [heq _ hu]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy'c
    rw [← hk, ← conj_zpow]
    refine zpow_mem ?_ k
    rcases word_conj_cyc016 u with h1 | h1
    · rw [h1]
      exact mem_zpowers _
    · rw [h1]
      exact inv_mem (mem_zpowers _)
  obtain ⟨m, hm⟩ := exists_commutator_stable hJX
  obtain ⟨hJD, hDX⟩ := commSeq_props hJX m
  refine ⟨commSeq X J m, hm.symm, hJD, hDX.trans hXL, hDX.trans hXe, hDX.trans hXK,
    hDX.trans hXN, fun d hd => ?_, ?_⟩
  · obtain ⟨⟨d', hd'N⟩, hd'c, hd'⟩ := hXZc (hDX hd)
    refine ⟨lamN ⟨d', hd'N⟩, hd'c, ?_⟩
    rw [← hd']
    exact hspec ⟨d', hd'N⟩
  ·
    have key : ∀ n, ∃ d ∈ commSeq X J n, ∃ i : Fin 3, i ≠ 0 ∧
        IsCoordAct ψ d (cyc016 ^ (i : ℕ)) := by
      intro n
      induction n with
      | zero =>
        refine ⟨x, ?_, i₀, hi₀, hxl⟩
        have h1 := mem_conjClosure (one_mem J) (mem_zpowers x)
        rwa [one_mul, inv_one, mul_one] at h1
      | succ n ih =>
        obtain ⟨d, hd, i, hi, hdl⟩ := ih
        obtain ⟨i', hi', hii'⟩ := cyc016_comm_swap01 i hi
        refine ⟨⁅d, j₀⁆, commutator_mem_commutator hd hj₀, i', hi', ?_⟩
        have hdN : d ∈ N := hXN ((commSeq_props hJX n).2 hd)
        have hcN : ⁅d, j₀⁆ ∈ N := by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hdN (hJN hj₀)) (inv_mem hdN)) (inv_mem (hJN hj₀))
        have h1 : lamN ⟨⁅d, j₀⁆, hcN⟩ = cyc016 ^ (i' : ℕ) := by
          rw [show (⟨⁅d, j₀⁆, hcN⟩ : N) = ⁅(⟨d, hdN⟩ : N), ⟨j₀, hJN hj₀⟩⁆ from rfl,
            map_commutatorElement, heq _ hdl, heq _ hj₀l, commutatorElement_def, hii']
        rw [← h1]
        exact hspec ⟨⁅d, j₀⁆, hcN⟩
    exact key m

end CFSG.Quasithin.H13.A7
