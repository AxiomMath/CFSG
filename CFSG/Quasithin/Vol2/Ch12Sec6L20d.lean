module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19b S126L19d S126L20 S126L20a S126L20b S126L20c
  Equiv
open scoped IsMulCommutative commutatorElement

namespace S126L20d

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

section Facts

variable (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
  (F : Frame126 T L V) (hH : Hyp126 G T L V)
  (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
  {h : G} (hh : Hyp4 V h)

@[expose] noncomputable def permGrp : Subgroup (Perm (Fin 8)) :=
  (nu F hH (hh.le_M h331 h1222 F hH) hh.le_normalizer).range

theorem mem_permGrp {σ : Perm (Fin 8)} :
    σ ∈ permGrp h331 h1222 F hH hh ↔ ∃ y ∈ conjSubgroup V h, ActsAs F y σ :=
  mem_range_nu F hH _ _

include h1262 hfus in
theorem permGrp_fpf : ∀ σ ∈ permGrp h331 h1222 F hH hh, σ ≠ 1 → ∀ i, σ i ≠ i := by
  intro σ hσ hσ1
  obtain ⟨y, hy, hyσ⟩ := (mem_permGrp h331 h1222 F hH hh).1 hσ
  exact fpf_of_hyp4 h331 h1222 h1262 F hH hfus hh hy hyσ hσ1

theorem permGrp_inv : ∀ σ ∈ permGrp h331 h1222 F hH hh, σ * σ = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [← map_mul]
  have hx : x * x = 1 := Subtype.ext (mul_self_conj h1222 hH x.2)
  rw [hx, map_one]

theorem permGrp_comm : ∀ σ ∈ permGrp h331 h1222 F hH hh, ∀ τ ∈ permGrp h331 h1222 F hH hh,
    σ * τ = τ * σ := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [← map_mul, ← map_mul]
  have hxy : x * y = y * x := Subtype.ext (conj_comm x.2 y.2)
  rw [hxy]

theorem permGrp_ne_bot : permGrp h331 h1222 F hH hh ≠ ⊥ := by
  intro hB
  apply hh.ne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  have h1 : nu F hH (hh.le_M h331 h1222 F hH) hh.le_normalizer ⟨y, hy⟩ = 1 := by
    have : nu F hH (hh.le_M h331 h1222 F hH) hh.le_normalizer ⟨y, hy⟩ ∈
        permGrp h331 h1222 F hH hh := ⟨_, rfl⟩
    rw [hB] at this
    exact this
  exact (nu_eq_one_iff F hH _ _ _).1 h1

theorem card_permGrp_le_eight (h1262 : Theorem12_6_2)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹) :
    Nat.card (permGrp h331 h1222 F hH hh) ≤ 8 :=
  card_le_eight_of_fpf (permGrp_fpf h331 h1222 h1262 F hH hfus hh)

theorem card_fixD_le_sixteen (h1262 : Theorem12_6_2)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹) :
    Nat.card (fixD (permGrp h331 h1222 F hH hh)) ≤ 16 := by
  obtain ⟨σ, hσ, hσ1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (permGrp_ne_bot h331 h1222 F hH hh)
  have hfpf := permGrp_fpf h331 h1222 h1262 F hH hfus hh σ hσ hσ1
  have hinv : ∀ i, σ (σ i) = i := fun i => by
    rw [← Perm.mul_apply, permGrp_inv h331 h1222 F hH hh σ hσ, Perm.one_apply]
  refine (Subgroup.card_le_of_le fun y hy => ?_).trans (card_fix1_le hfpf hinv)
  exact (mem_fixD.1 hy) σ hσ

theorem card_fixD_le_eight' (h1262 : Theorem12_6_2)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (h3 : 3 ≤ Nat.card (permGrp h331 h1222 F hH hh)) :
    Nat.card (fixD (permGrp h331 h1222 F hH hh)) ≤ 8 := by
  classical
  set B := permGrp h331 h1222 F hH hh
  obtain ⟨σ₁, hσ₁, hσ₁1⟩ := (Subgroup.bot_or_exists_ne_one B).resolve_left
    (permGrp_ne_bot h331 h1222 F hH hh)
  obtain ⟨σ₂, hσ₂, hσ₂'⟩ : ∃ σ₂ ∈ B, σ₂ ∉ ({1, σ₁} : Finset (Perm (Fin 8))) := by
    by_contra hc
    push Not at hc
    have h1 := S126F.card_le_of_forall_mem B _ hc
    have h2 : ({1, σ₁} : Finset (Perm (Fin 8))).card ≤ 2 := Finset.card_le_two
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ₂'
  exact card_fixD_le_eight (permGrp_fpf h331 h1222 h1262 F hH hfus hh)
    (permGrp_inv h331 h1222 F hH hh) hσ₁ hσ₂ hσ₁1 hσ₂'.1 (Ne.symm hσ₂'.2)

theorem card_conj_eq :
    Nat.card (conjSubgroup V h) = Nat.card ↥(conjSubgroup V h ⊓
      Subgroup.centralizer (V : Set G)) * Nat.card (permGrp h331 h1222 F hH hh) :=
  card_eq_mul F hH _ _

theorem card_centralizer (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) =
      Nat.card (fixD (permGrp h331 h1222 F hH hh)) :=
  card_centralizer_eq F hH _ _ hZ

end Facts

theorem card_permGrp (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : Hyp4 V g) :
    Nat.card (permGrp h331 h1222 F hH hg) = 8 ∧
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) = 8 := by
  have hZ := bot_of_hyp4 h331 h1222 h1262 F hH hfus hg
  have hg' := hg.inv
  have hV : Nat.card V = 64 := by
    rw [card_V F, hZ, Subgroup.card_bot]
  have hVg : Nat.card (conjSubgroup V g) = 64 := by rw [E3.card_conjSubgroup, hV]
  have hVg' : Nat.card (conjSubgroup V g⁻¹) = 64 := by rw [E3.card_conjSubgroup, hV]
  have e1 := card_conj_eq h331 h1222 F hH hg
  have e2 := card_conj_eq h331 h1222 F hH hg'
  have n1 := card_centralizer h331 h1222 F hH hg hZ
  have n2 := card_centralizer h331 h1222 F hH hg' hZ
  have c1 : Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g⁻¹ : Set G)) := by
    have := E3.card_inf_centralizer_conj V (conjSubgroup V g⁻¹) g
    rw [E3.conjSubgroup_inv_conj] at this
    exact this
  have c2 : Nat.card ↥(conjSubgroup V g⁻¹ ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    have := E3.card_inf_centralizer_conj V (conjSubgroup V g) g⁻¹
    rw [E3.conjSubgroup_conj_inv] at this
    exact this
  have b1 := card_permGrp_le_eight h331 h1222 F hH hg h1262 hfus
  have b2 := card_permGrp_le_eight h331 h1222 F hH hg' h1262 hfus
  have f1 := card_fixD_le_sixteen h331 h1222 F hH hg h1262 hfus
  have f2 := card_fixD_le_sixteen h331 h1222 F hH hg' h1262 hfus
  have g1 := card_fixD_le_eight' h331 h1222 F hH hg h1262 hfus
  have g2 := card_fixD_le_eight' h331 h1222 F hH hg' h1262 hfus
  rw [hVg, c1, n2] at e1
  rw [hVg', c2, n1] at e2
  set A := Nat.card (permGrp h331 h1222 F hH hg)
  set A' := Nat.card (permGrp h331 h1222 F hH hg')
  set N := Nat.card (fixD (permGrp h331 h1222 F hH hg))
  set N' := Nat.card (fixD (permGrp h331 h1222 F hH hg'))
  have hA'4 : 3 ≤ A' := by
    by_contra hc
    push Not at hc
    have : N * A' ≤ 16 * 2 := Nat.mul_le_mul f1 (by omega)
    omega
  have hN'8 := g2 hA'4
  have hA4 : 3 ≤ A := by
    by_contra hc
    push Not at hc
    have : N' * A ≤ 16 * 2 := Nat.mul_le_mul f2 (by omega)
    omega
  have hN8 := g1 hA4
  have hA8 : A = 8 := by
    have : N' * A ≤ 8 * A := Nat.mul_le_mul_right _ hN'8
    omega
  refine ⟨hA8, ?_⟩
  rw [n1]
  have hA'8 : A' = 8 := by
    have : N * A' ≤ 8 * A' := Nat.mul_le_mul_right _ hN8
    omega
  rw [hA'8] at e2
  omega

theorem exists_conj (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : Hyp4 V g) :
    ∃ τ : Perm (Fin 8), ∀ σ, σ ∈ permGrp h331 h1222 F hH hg ↔ τ⁻¹ * σ * τ ∈ B0 :=
  exists_conj_B0 (card_permGrp h331 h1222 h1262 F hH hfus hg).1.ge
    (permGrp_fpf h331 h1222 h1262 F hH hfus hg) (permGrp_inv h331 h1222 F hH hg)
    (permGrp_comm h331 h1222 F hH hg)

theorem inter_eq (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : Hyp4 V g) :
    V ⊓ conjSubgroup V g = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) := by
  have hZ := bot_of_hyp4 h331 h1222 h1262 F hH hfus hg
  refine le_antisymm (fun u hu => ⟨hu.1, Subgroup.mem_centralizer_iff.2 fun y hy =>
    conj_comm hy hu.2⟩) (fun v hv => hg.le ?_)
  obtain ⟨τ, hτ⟩ := exists_conj h331 h1222 h1262 F hH hfus hg
  have hvB : F.β ⟨v, hv.1⟩ ∈ fixD (permGrp h331 h1222 F hH hg) :=
    (mem_centralizer_iff F hH _ _ hZ ⟨v, hv.1⟩).1 hv.2
  obtain ⟨k, x, hx⟩ := mem_comm_of_fixD ((mem_fixD_iff hτ).1 hvB)
  have hσ : τ * xt k * τ⁻¹ ∈ permGrp h331 h1222 F hH hg := (hτ _).2 (by
    rw [show τ⁻¹ * (τ * xt k * τ⁻¹) * τ = xt k by group]
    exact xt_mem k)
  obtain ⟨y, hy, hyσ⟩ := (mem_permGrp h331 h1222 F hH hg).1 hσ
  obtain ⟨w, hw⟩ := F.β_surj (dAct τ x)
  have hyN := hg.le_normalizer hy
  set w' : ↥V := ⟨y * w * y⁻¹, conj_mem hyN w⟩ with hw'
  have hβ : F.β ⟨v, hv.1⟩ = F.β (w * w') := by
    rw [map_mul, hyσ w w' rfl, hw]
    have h1 := congrArg (dAct τ) hx
    rw [dAct_dAct_inv] at h1
    rw [h1, map_mul, ← dAct_mul, ← dAct_mul,
      show τ * xt k * τ⁻¹ * τ = τ * xt k by group]
  have hvw : v = w * (y * w * y⁻¹) := congrArg Subtype.val (beta_inj F hZ hβ)
  have hww : (w : G) * w = 1 := mul_self_V h1222 hH w.2
  have e : v = w * y * (w : G)⁻¹ * y⁻¹ := by
    rw [hvw, show (w : G)⁻¹ = w from inv_eq_of_mul_eq_one_right hww]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator w.2 hy

theorem card_inter (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : Hyp4 V g) : Nat.card ↥(V ⊓ conjSubgroup V g) = 8 := by
  rw [inter_eq h331 h1222 h1262 F hH hfus hg]
  exact (card_permGrp h331 h1222 h1262 F hH hfus hg).2

end S126L20d

end CFSG.Quasithin.H13
