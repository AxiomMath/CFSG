module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeB
public import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_le_centralizer_of_relIndex_le_two {A P H : Subgroup G} (hHP : H ≤ P)
    (hidx : H.relIndex P ≤ 2) (hAN : A ≤ normalizer (P : Set G))
    (hAC : A ≤ centralizer (H : Set G)) (hA : A ≠ ⊥) (hcard : Nat.card P < 2 * Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ P ≤ centralizer ({a} : Set G) := by
  classical
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  by_cases h1 : H.relIndex P = 1
  · refine ⟨a₀, ha₀A, ha₀1, ?_⟩
    have hPleH : P ≤ H := Subgroup.relIndex_eq_one.mp h1
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (hAC ha₀A) p (hPleH hp)
  · have hrel : H.relIndex P = 2 := by
      have hpos : H.relIndex P ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      omega
    obtain ⟨t, htP, htH, ht⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hrel
    have hconjP : ∀ a : A, (a : G) * t * (a : G)⁻¹ ∈ P := fun a =>
      (Subgroup.mem_normalizer_iff.1 (hAN a.2) t).1 htP
    have hnotH : ∀ a : A, (a : G) * t * (a : G)⁻¹ ∉ H := by
      intro a haH
      have hcomm : (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * (a : G) =
          (a : G) * t * (a : G)⁻¹ := by
        have h1' : ((a : G) * t * (a : G)⁻¹) * (a : G) =
            (a : G) * ((a : G) * t * (a : G)⁻¹) :=
          Subgroup.mem_centralizer_iff.1 (hAC a.2) _ haH
        calc (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * (a : G)
            = (a : G)⁻¹ * (((a : G) * t * (a : G)⁻¹) * (a : G)) := by group
          _ = (a : G)⁻¹ * ((a : G) * ((a : G) * t * (a : G)⁻¹)) := by rw [h1']
          _ = (a : G) * t * (a : G)⁻¹ := by group
      have hteq : t = (a : G) * t * (a : G)⁻¹ := by
        calc t = (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * (a : G) := by group
          _ = (a : G) * t * (a : G)⁻¹ := hcomm
      exact htH (by rw [hteq]; exact haH)
    have hmap : ∀ a : A, t * (a : G) * t * (a : G)⁻¹ ∈ H := by
      intro a
      rcases ht _ (hconjP a) with h | h
      · simpa only [mul_assoc] using h
      · exact absurd h (hnotH a)
    let ψ : A → H := fun a => ⟨t * (a : G) * t * (a : G)⁻¹, hmap a⟩
    have hcardP : 2 * Nat.card H = Nat.card P := by
      have h := Subgroup.relIndex_mul_card (H := H) (K := P)
      rw [inf_of_le_left hHP, hrel] at h
      exact h
    have hHlt : Nat.card H < Nat.card A := by
      have : 2 * Nat.card H < 2 * Nat.card A := by rwa [hcardP]
      omega
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Fintype H := Fintype.ofFinite H
    have hcard' : Fintype.card H < Fintype.card A := by
      simpa only [Nat.card_eq_fintype_card] using hHlt
    obtain ⟨a₁, a₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt ψ hcard'
    have heq' : (a₁ : G) * t * (a₁ : G)⁻¹ = (a₂ : G) * t * (a₂ : G)⁻¹ := by
      have h : t * ((a₁ : G) * t * (a₁ : G)⁻¹) = t * ((a₂ : G) * t * (a₂ : G)⁻¹) := by
        simpa only [ψ, mul_assoc] using congrArg (fun x : H => (x : G)) heq
      exact mul_left_cancel h
    set b : G := (a₂ : G)⁻¹ * (a₁ : G) with hbdef
    have hbA : b ∈ A := A.mul_mem (A.inv_mem a₂.2) a₁.2
    have hbt : b * t = t * b := by
      calc b * t = (a₂ : G)⁻¹ * ((a₁ : G) * t * (a₁ : G)⁻¹) * (a₁ : G) := by
            rw [hbdef]; group
        _ = (a₂ : G)⁻¹ * ((a₂ : G) * t * (a₂ : G)⁻¹) * (a₁ : G) := by rw [heq']
        _ = t * b := by rw [hbdef]; group
    have hbtinv : t⁻¹ * b = b * t⁻¹ := by
      calc t⁻¹ * b = t⁻¹ * (b * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * b) * t⁻¹ := by rw [hbt]
        _ = b * t⁻¹ := by group
    refine ⟨b, hbA, ?_, ?_⟩
    · intro hb1
      apply hne
      apply Subtype.ext
      calc (a₁ : G) = (a₂ : G) * ((a₂ : G)⁻¹ * (a₁ : G)) := by group
        _ = (a₂ : G) * b := by rw [hbdef]
        _ = (a₂ : G) * 1 := by rw [hb1]
        _ = (a₂ : G) := by rw [mul_one]
    · intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases ht p hp with htp | hp
      · have hcommH : (t * p) * b = b * (t * p) :=
          Subgroup.mem_centralizer_iff.1 (hAC hbA) (t * p) htp
        have hbtinv' : b * t⁻¹ = t⁻¹ * b := hbtinv.symm
        have key : b * (t⁻¹ * (t * p)) = (t⁻¹ * (t * p)) * b := by
          calc b * (t⁻¹ * (t * p)) = (b * t⁻¹) * (t * p) := by group
            _ = (t⁻¹ * b) * (t * p) := by rw [hbtinv']
            _ = t⁻¹ * (b * (t * p)) := by group
            _ = t⁻¹ * ((t * p) * b) := by rw [← hcommH]
            _ = (t⁻¹ * (t * p)) * b := by group
        rw [show p = t⁻¹ * (t * p) by group]
        exact key.symm
      · exact Subgroup.mem_centralizer_iff.1 (hAC hbA) p hp

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem conj_eq_of_mem_centralizer (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g)
    {b : G} (hbM : b ∈ M)
    (hbU : b ∈ centralizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G)) :
    conjSubgroup W₁ b = W₁ ∧ conjSubgroup W₂ b = W₂ := by
  rcases h.perm b hbM with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exfalso
    have hle : W₁ ⊓ conjSubgroup M g ≤ V₀ := by
      intro w hw
      obtain ⟨hwW₁, hwMg⟩ := Subgroup.mem_inf.mp hw
      have hwU : w ∈ V ⊓ conjSubgroup M g := ⟨h.W₁_le hwW₁, hwMg⟩
      have hcomm : w * b = b * w := Subgroup.mem_centralizer_iff.1 hbU w hwU
      have hwb : b * w * b⁻¹ = w := by rw [← hcomm]; group
      have hwW₂ : w ∈ W₂ := by
        rw [← h1]
        exact mem_conjSubgroup_iff.2 (by rw [hwb]; exact hwW₁)
      rw [← h.inf_eq]
      exact ⟨hwW₁, hwW₂⟩
    have hcard := two_mul_card_le_card_inf h hg
    have hcardle : Nat.card (W₁ ⊓ conjSubgroup M g : Subgroup G) ≤ Nat.card V₀ :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hpos : 0 < Nat.card V₀ := Nat.card_pos
    omega

theorem le_U_of_not_mem_cTilde (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g)
    {b : G} (hbM : b ∈ M)
    (hbU : b ∈ centralizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G))
    (hb : b ∉ F11.CTilde M V₀ V) :
    W₁ ≤ V ⊓ conjSubgroup M g ∨ W₂ ≤ V ⊓ conjSubgroup M g := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hw₁le, hw₂le⟩ := hcon
  obtain ⟨w₁, hw₁W₁, hw₁U⟩ := SetLike.not_le_iff_exists.mp hw₁le
  obtain ⟨w₂, hw₂W₂, hw₂U⟩ := SetLike.not_le_iff_exists.mp hw₂le
  apply hb
  rw [CFSG.LocalAnalysis.WeakClosure81.FourteenTwo.mem_cTilde_iff_comm]
  obtain ⟨hfix₁, hfix₂⟩ := conj_eq_of_mem_centralizer h hg hbM hbU
  have hw₁norm : b ∈ normalizer (W₁ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hfix₁
  have hw₂norm : b ∈ normalizer (W₂ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hfix₂
  have hbw₁ : b * w₁ * b⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.1 hw₁norm w₁).1 hw₁W₁
  have hbw₂ : b * w₂ * b⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.1 hw₂norm w₂).1 hw₂W₂
  have hw₁V : w₁ ∈ V := h.W₁_le hw₁W₁
  have hw₂V : w₂ ∈ V := h.W₂_le hw₂W₂
  obtain ⟨t, htV, htU, ht⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp (relIndex_U h hg)
  have htw₁ : t * w₁ ∈ V ⊓ conjSubgroup M g := (ht w₁ hw₁V).resolve_right hw₁U
  have htw₂ : t * w₂ ∈ V ⊓ conjSubgroup M g := (ht w₂ hw₂V).resolve_right hw₂U
  have hw₁w₂U : w₁⁻¹ * w₂ ∈ V ⊓ conjSubgroup M g := by
    have := (V ⊓ conjSubgroup M g).mul_mem ((V ⊓ conjSubgroup M g).inv_mem htw₁) htw₂
    convert this using 1
    group
  have hbvv₂ : b * w₂ * b⁻¹ * w₂⁻¹ = b * w₁ * b⁻¹ * w₁⁻¹ := by
    have hw₂_eq : w₂ = w₁ * (w₁⁻¹ * w₂) := by group
    have hbh₂ : b * (w₁⁻¹ * w₂) * b⁻¹ = w₁⁻¹ * w₂ := by
      have hcomm := Subgroup.mem_centralizer_iff.1 hbU (w₁⁻¹ * w₂) hw₁w₂U
      rw [← hcomm]; group
    calc b * w₂ * b⁻¹ * w₂⁻¹
        = (b * w₁ * b⁻¹) * (b * (w₁⁻¹ * w₂) * b⁻¹) *
            ((w₁⁻¹ * w₂)⁻¹ * w₁⁻¹) := by rw [hw₂_eq]; group
      _ = (b * w₁ * b⁻¹) * (w₁⁻¹ * w₂) * ((w₁⁻¹ * w₂)⁻¹ * w₁⁻¹) := by rw [hbh₂]
      _ = b * w₁ * b⁻¹ * w₁⁻¹ := by group
  have heW₁ : b * w₁ * b⁻¹ * w₁⁻¹ ∈ W₁ := W₁.mul_mem hbw₁ (W₁.inv_mem hw₁W₁)
  have heW₂ : b * w₁ * b⁻¹ * w₁⁻¹ ∈ W₂ := by
    rw [← hbvv₂]
    exact W₂.mul_mem hbw₂ (W₂.inv_mem hw₂W₂)
  have heV₀ : b * w₁ * b⁻¹ * w₁⁻¹ ∈ V₀ := by
    rw [← h.inf_eq]
    exact ⟨heW₁, heW₂⟩
  refine ⟨hbM, h.le_normalizer₀ hbM, fun v hv => ?_⟩
  by_cases hvU : v ∈ V ⊓ conjSubgroup M g
  · have hbvv : b * v * b⁻¹ = v := by
      have hcomm := Subgroup.mem_centralizer_iff.1 hbU v hvU
      rw [← hcomm]; group
    have : b * v * b⁻¹ * v⁻¹ = 1 := by rw [hbvv, mul_inv_cancel]
    rw [this]
    exact V₀.one_mem
  · have htv : t * v ∈ V ⊓ conjSubgroup M g := (ht v hv).resolve_right hvU
    have hhU : w₁⁻¹ * v ∈ V ⊓ conjSubgroup M g := by
      have := (V ⊓ conjSubgroup M g).mul_mem ((V ⊓ conjSubgroup M g).inv_mem htw₁) htv
      convert this using 1
      group
    have hbh : b * (w₁⁻¹ * v) * b⁻¹ = w₁⁻¹ * v := by
      have hcomm := Subgroup.mem_centralizer_iff.1 hbU (w₁⁻¹ * v) hhU
      rw [← hcomm]; group
    have hv_eq : v = w₁ * (w₁⁻¹ * v) := by group
    have hbvv : b * v * b⁻¹ * v⁻¹ = b * w₁ * b⁻¹ * w₁⁻¹ := by
      calc b * v * b⁻¹ * v⁻¹
          = (b * w₁ * b⁻¹) * (b * (w₁⁻¹ * v) * b⁻¹) *
              ((w₁⁻¹ * v)⁻¹ * w₁⁻¹) := by rw [hv_eq]; group
        _ = (b * w₁ * b⁻¹) * (w₁⁻¹ * v) * ((w₁⁻¹ * v)⁻¹ * w₁⁻¹) := by rw [hbh]
        _ = b * w₁ * b⁻¹ * w₁⁻¹ := by group
    rw [hbvv]
    exact heV₀

theorem le_normalizer_W_of_le_U (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g)
    (hW : W₁ ≤ V ⊓ conjSubgroup M g) :
    conjSubgroup V g ⊓ M ≤ normalizer (W₁ : Set G) := by
  intro b hb
  rcases h.perm b hb.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact conjSubgroup_eq_iff_mem_normalizer.mp h1
  · exfalso
    have hbU : b ∈ normalizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) :=
      le_normalizer_U h hb
    have hUb : conjSubgroup (V ⊓ conjSubgroup M g) b = V ⊓ conjSubgroup M g :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hbU
    have hW₁b : conjSubgroup W₁ b ≤ conjSubgroup (V ⊓ conjSubgroup M g) b :=
      E3.conjSubgroup_mono_left b hW
    rw [h1, hUb] at hW₁b
    have hVleU : V ≤ V ⊓ conjSubgroup M g := by
      have hs : W₁ ⊔ W₂ ≤ V ⊓ conjSubgroup M g := sup_le hW hW₁b
      rwa [h.sup_eq] at hs
    have hidx1 : (V ⊓ conjSubgroup M g).relIndex V = 1 :=
      Subgroup.relIndex_eq_one.mpr hVleU
    have := relIndex_U h hg
    omega

theorem commute_of_le_U (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g)
    (hW : W₁ ≤ V ⊓ conjSubgroup M g) {w b : G} (hw : w ∈ W₁)
    (hb : b ∈ conjSubgroup V g ⊓ M) : w * b = b * w := by
  have hnormW : b ∈ normalizer (W₁ : Set G) := le_normalizer_W_of_le_U h hg hW hb
  have hbw : b * w⁻¹ * b⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.1 hnormW w⁻¹).1 (W₁.inv_mem hw)
  have hcW₁ : w * b * w⁻¹ * b⁻¹ ∈ W₁ := by
    rw [show w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) by group]
    exact W₁.mul_mem hw hbw
  have hnormVg : w ∈ normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V g, h.normalizer_eq]
    exact (hW hw).2
  have hcVg : w * b * w⁻¹ * b⁻¹ ∈ conjSubgroup V g := by
    have h1 : w * b * w⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hnormVg b).1 hb.1
    rw [show w * b * w⁻¹ * b⁻¹ = (w * b * w⁻¹) * b⁻¹ by group]
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem hb.1)
  have hbot : W₁ ⊓ conjSubgroup V g = ⊥ := (inf_conj_eq_bot' h (not_mem_of_inCalO h hg)).1
  have hcbot : w * b * w⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact ⟨hcW₁, hcVg⟩
  have hc1 : w * b * w⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp hcbot
  have : w * b = (w * b * w⁻¹ * b⁻¹) * (b * w) := by group
  rw [hc1, one_mul] at this
  exact this

theorem le_normalizer_conj_of_le_U (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g)
    (hW : W₁ ≤ V ⊓ conjSubgroup M g) :
    W₁ ≤ normalizer (conjSubgroup W₁ g : Set G) ∧
      W₁ ≤ normalizer (conjSubgroup W₂ g : Set G) := by
  have hconj := h.conj g
  have key : ∀ w ∈ W₁, conjSubgroup (conjSubgroup W₁ g) w = conjSubgroup W₂ g → False := by
    intro w hw h1
    have hle : conjSubgroup W₁ g ⊓ M ≤ conjSubgroup V₀ g := by
      intro y hy
      obtain ⟨hyW₁g, hyM⟩ := Subgroup.mem_inf.mp hy
      have hyVg : y ∈ conjSubgroup V g := E3.conjSubgroup_mono_left g h.W₁_le hyW₁g
      have hcomm : w * y = y * w := commute_of_le_U h hg hW hw ⟨hyVg, hyM⟩
      have hyW₂g : y ∈ conjSubgroup W₂ g := by
        rw [← h1]
        refine mem_conjSubgroup_iff.2 ?_
        rw [show w * y * w⁻¹ = y by rw [hcomm]; group]
        exact hyW₁g
      rw [← h.inf_eq, E3.conjSubgroup_inf]
      exact ⟨hyW₁g, hyW₂g⟩
    have hcard := two_mul_card_le_card_conj_inf h hg
    have hle' : Nat.card (conjSubgroup W₁ g ⊓ M : Subgroup G) ≤ Nat.card (conjSubgroup V₀ g) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [E3.card_conjSubgroup] at hle'
    have hpos : 0 < Nat.card V₀ := Nat.card_pos
    omega
  constructor
  · intro w hw
    rcases hconj.perm w (hW hw).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact conjSubgroup_eq_iff_mem_normalizer.mp h1
    · exact absurd h1 (key w hw)
  · intro w hw
    rcases hconj.perm w (hW hw).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact conjSubgroup_eq_iff_mem_normalizer.mp h2
    · exact absurd h1 (key w hw)

theorem conj_le_M_of_le_U (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g)
    (hW : W₁ ≤ V ⊓ conjSubgroup M g) : conjSubgroup V g ≤ M := by
  have hnorm := le_normalizer_conj_of_le_U h hg hW
  have hpos : 0 < Nat.card V₀ := Nat.card_pos
  have hW₁ne : W₁ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card W₁ = 1 := Subgroup.card_eq_one.mpr hbot
    rw [h.card₁] at h1
    omega
  have hcard₁ : Nat.card (conjSubgroup W₁ g) < 2 * Nat.card W₁ := by
    rw [E3.card_conjSubgroup, h.card₁]
    omega
  have hcard₂ : Nat.card (conjSubgroup W₂ g) < 2 * Nat.card W₁ := by
    rw [E3.card_conjSubgroup, h.card₂, h.card₁]
    omega
  have hW₁M : conjSubgroup W₁ g ≤ M := by
    obtain ⟨a, haW₁, ha1, hcent⟩ :=
      exists_ne_one_le_centralizer_of_relIndex_le_two (A := W₁) (P := conjSubgroup W₁ g)
        (H := conjSubgroup W₁ g ⊓ M) inf_le_left (relIndex_conj_inf_le h hg) hnorm.1
        (fun w hw => by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (commute_of_le_U h hg hW hw
            ⟨E3.conjSubgroup_mono_left g h.W₁_le hy.1, hy.2⟩).symm)
        hW₁ne hcard₁
    exact hcent.trans (h.centralizer_le a (Or.inl haW₁) ha1)
  have hW₂M : conjSubgroup W₂ g ≤ M := by
    obtain ⟨a, haW₁, ha1, hcent⟩ :=
      exists_ne_one_le_centralizer_of_relIndex_le_two (A := W₁) (P := conjSubgroup W₂ g)
        (H := conjSubgroup W₂ g ⊓ M) inf_le_left (relIndex_conj_inf_le h.swap hg) hnorm.2
        (fun w hw => by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (commute_of_le_U h hg hW hw
            ⟨E3.conjSubgroup_mono_left g h.W₂_le hy.1, hy.2⟩).symm)
        hW₁ne hcard₂
    exact hcent.trans (h.centralizer_le a (Or.inl haW₁) ha1)
  calc conjSubgroup V g = conjSubgroup (W₁ ⊔ W₂) g := by rw [h.sup_eq]
    _ = conjSubgroup W₁ g ⊔ conjSubgroup W₂ g :=
          Subgroup.map_sup W₁ W₂ (MulAut.conj g⁻¹).toMonoidHom
    _ ≤ M := sup_le hW₁M hW₂M

theorem oneFirst (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) :
    OneFirst M V₀ V g := by
  unfold OneFirst
  intro b hb
  by_contra hbC
  rcases le_U_of_not_mem_cTilde h hg hb.1.2 hb.2 hbC with hW | hW
  · exact hg.1.1 (conj_le_M_of_le_U h hg hW)
  · exact hg.1.1 (conj_le_M_of_le_U h.swap hg hW)

theorem oneDual (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) :
    OneDual M V₀ V g :=
  (oneFirst_swap M V₀ V g).1
    (oneFirst (h.conj g) (CFSG.LocalAnalysis.WeakClosure81.inCalO_swap hg))

theorem inCalO1 (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) :
    InCalO1 1 M V₀ V g :=
  ⟨hg, oneFirst h hg, oneDual h hg⟩

theorem hyp65 (h : Cfg1667Ne M V₀ V W₁ W₂) (hg : InCalO 1 M V₀ V g) :
    CFSG.LocalAnalysis.WeakClosure81.Hyp65 1 M V₀ V g :=
  ⟨h.elemAbelian, V₀_le h, h.ne_bot, h.normalizer_eq, h.normalizer₀, h.isTI, inCalO1 h hg⟩

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
