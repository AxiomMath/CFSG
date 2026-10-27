module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeB
public import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem hyp64 (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    CFSG.LocalAnalysis.WeakClosure81.Hyp64 1 M V₀ V g := by
  refine ⟨h.elemAbelian, V₀_le h, h.normalizer_eq, le_normalizer₀ h, fun _ => h.isTI,
    fun _ => h.normalizer₀, hs⟩

theorem V₀_le_U (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    V₀ ≤ V ⊓ conjSubgroup M g := by
  have h64 := hyp64 h hs
  exact CFSG.LocalAnalysis.WeakClosure81.V₀_le_UOf h64
    (CFSG.LocalAnalysis.WeakClosure81.genHyp_of_relIndex_two h64 (relIndex_U h hs.1))

theorem conj_V₀_le_B (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    conjSubgroup V₀ g ≤ conjSubgroup V g ⊓ M := by
  refine le_inf (E3.conjSubgroup_mono_left g (V₀_le h)) ?_
  rw [← h.normalizer_eq, Subgroup.le_normalizer_iff_commutator_le_right]
  obtain ⟨K, hKn, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hs.2
  exact hcomm.trans (V₀_le h)

theorem inf_centralizer_B_eq (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    V ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) =
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊔ V₀ := by
  obtain ⟨K, hKn, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hs.2
  rw [U_inf_B_eq h]
  exact hcen

theorem inf_cTilde_B_eq (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    (conjSubgroup V g ⊓ M) ⊓ F11.CTilde M V₀ V =
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊔ conjSubgroup V₀ g := by
  have h64 := hyp64 h hs
  exact CFSG.LocalAnalysis.WeakClosure81.six_four_four_centralizer_B_of_relIndex_two h64
    (relIndex_U h hs.1)

theorem not_le_normalizer_W (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ¬ conjSubgroup V g ⊓ M ≤ normalizer (W₁ : Set G) := by
  intro hB
  have hg : InCalO 1 M V₀ V g := hs.1
  have hg' : g ∉ M := not_mem_of_inCalO h hg
  have hbot : W₁ ⊓ conjSubgroup V g = ⊥ := (inf_conj_eq_bot' h hg').1
  have hle : W₁ ⊓ conjSubgroup M g ≤ V₀ := by
    intro u hu
    obtain ⟨huW₁, huMg⟩ := Subgroup.mem_inf.mp hu
    have huV : u ∈ V := W₁_le h huW₁
    have huU : u ∈ V ⊓ conjSubgroup M g := ⟨huV, huMg⟩
    have hcent : u ∈ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hcommW : ⁅u, b⁆ ∈ W₁ := by
        have hbu : b * u⁻¹ * b⁻¹ ∈ W₁ :=
          (Subgroup.mem_normalizer_iff.1 (hB hb) u⁻¹).1 (W₁.inv_mem huW₁)
        rw [commutatorElement_def,
          show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group]
        exact W₁.mul_mem huW₁ hbu
      have hcommUB : ⁅u, b⁆ ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) :=
        commutator_U_B_le h (Subgroup.commutator_mem_commutator huU hb)
      have hcomm1 : ⁅u, b⁆ = 1 := by
        have hmem : ⁅u, b⁆ ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact ⟨hcommW, hcommUB.2.1⟩
        exact Subgroup.mem_bot.mp hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
    have huN : u ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) ⊔ V₀ := by
      rw [← inf_centralizer_B_eq h hs]
      exact ⟨huV, hcent⟩
    have hNleV : (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) ≤ V :=
      inf_le_left.trans inf_le_left
    have hNnorm : ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) ≤
        normalizer (V₀ : Set G) := by
      rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
      intro x hx y hy
      have hcomm : ⁅x, y⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (IsElemAbelian.comm h.elemAbelian (hNleV hx) (V₀_le h hy))
      rw [hcomm]
      exact V₀.one_mem
    have hprod : u ∈ (((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) : Set G) *
        (V₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNnorm]
      exact huN
    rw [Set.mem_mul] at hprod
    obtain ⟨n, hnN, a, haV₀, hna⟩ := hprod
    have hnW₁ : n ∈ W₁ := by
      have hn_eq : n = u * a⁻¹ := by rw [← hna]; group
      rw [hn_eq]
      exact W₁.mul_mem huW₁ (W₁.inv_mem (V₀_le₁ h haV₀))
    have hnVg : n ∈ conjSubgroup V g := hnN.2.1
    have hn1 : n = 1 := by
      have hmem : n ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hnW₁, hnVg⟩
      exact Subgroup.mem_bot.mp hmem
    have hu_eq : u = a := by simpa [hn1] using hna.symm
    rw [hu_eq]
    exact haV₀
  have hcardle : Nat.card (W₁ ⊓ conjSubgroup M g : Subgroup G) ≤ Nat.card V₀ :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hcard := two_mul_card_le_card_inf h hg
  have hpos : 0 < Nat.card V₀ := Nat.card_pos
  omega

theorem U_inf_B_ne_bot (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) ≠ ⊥ := by
  intro hbot
  have hg : InCalO 1 M V₀ V g := hs.1
  have hUle : V ⊓ conjSubgroup M g ≤
      V ⊓ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := by
    intro u hu
    have hcent : u ∈ centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hcommUB : ⁅u, b⁆ ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) :=
        commutator_U_B_le h (Subgroup.commutator_mem_commutator hu hb)
      have hcomm1 : ⁅u, b⁆ = 1 := by
        have hmem : ⁅u, b⁆ ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hcommUB
        exact Subgroup.mem_bot.mp hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
    exact ⟨hu.1, hcent⟩
  have hV₀ : V ⊓ conjSubgroup M g ≤ V₀ := by
    have hh := hUle
    rw [inf_centralizer_B_eq h hs] at hh
    rwa [hbot, bot_sup_eq] at hh
  have hcardle : Nat.card (V ⊓ conjSubgroup M g : Subgroup G) ≤ Nat.card V₀ :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hV₀) (Subgroup.inclusion_injective hV₀)
  have hcard := card_U h hg
  have hpos : 0 < Nat.card V₀ := Nat.card_pos
  omega

theorem card_U_inf_B_ne_four (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    Nat.card ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) ≠ 4 := by
  intro hN4
  set N : Subgroup G := (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) with hNdef
  set B : Subgroup G := conjSubgroup V g ⊓ M with hBdef
  set C : Subgroup G := F11.CTilde M V₀ V with hCdef
  have hg : InCalO 1 M V₀ V g := hs.1
  have h64 := hyp64 h hs
  have hidx := relIndex_U h hs.1
  have hNleV : N ≤ V := by rw [hNdef]; exact inf_le_left.trans inf_le_left
  have hNbot : N ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ V := hNleV hx.1
    have hmem : x ∈ conjSubgroup V₀ g ⊓ V := ⟨hx.2, hxV⟩
    rwa [CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_V₀_inf_V_eq_bot h64] at hmem
  have hNcomm : ∀ x ∈ N, ∀ y ∈ conjSubgroup V₀ g, x * y = y * x := by
    intro x hx y hy
    have hxcent : x ∈ Subgroup.centralizer
        (CFSG.LocalAnalysis.WeakClosure81.LOf V g : Set G) :=
      CFSG.LocalAnalysis.WeakClosure81.NOf_le_centralizer_L h64 hx
    have hyL : y ∈ CFSG.LocalAnalysis.WeakClosure81.LOf V g :=
      Subgroup.mem_sup_right (E3.conjSubgroup_mono_left g (V₀_le h) hy)
    exact (Subgroup.mem_centralizer_iff.1 hxcent y hyL).symm
  have hNsup : Nat.card (N ⊔ conjSubgroup V₀ g : Subgroup G) = 4 * Nat.card V₀ := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute N
      (conjSubgroup V₀ g) hNcomm).1
    rw [hNbot, Subgroup.card_bot, mul_one, hN4, E3.card_conjSubgroup V₀ g] at hcard
    exact hcard
  have hBC : B ⊓ C = N ⊔ conjSubgroup V₀ g := by
    rw [hBdef, hCdef, hNdef]
    exact CFSG.LocalAnalysis.WeakClosure81.six_four_four_centralizer_B_of_relIndex_two h64 hidx
  have hcardBC : Nat.card (B ⊓ C : Subgroup G) = 4 * Nat.card V₀ := by rw [hBC, hNsup]
  have hcardB : Nat.card B = 8 * Nat.card V₀ := by rw [hBdef]; exact card_B h hg
  have hrel : (B ⊓ C).relIndex B = 2 := by
    have hmul := Subgroup.relIndex_mul_card (H := B ⊓ C) (K := B)
    rw [inf_of_le_left inf_le_left, hcardBC, hcardB] at hmul
    have hpos : 0 < 4 * Nat.card V₀ := Nat.mul_pos (by norm_num) (Nat.card_pos (α := V₀))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc (B ⊓ C).relIndex B * (4 * Nat.card V₀) = 8 * Nat.card V₀ := hmul
      _ = 2 * (4 * Nat.card V₀) := by ring
  obtain ⟨b, hbB, hbnotBC, hball⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hrel
  have hbB' : b ∈ conjSubgroup V g ⊓ M := hBdef ▸ hbB
  have hbM : b ∈ M := hbB'.2
  have hbVg : b ∈ conjSubgroup V g := hbB'.1
  have hbC : b ∉ C := fun hc => hbnotBC ⟨hbB, hc⟩
  have hbnot : ¬ B ≤ C := fun hle => hbC (hle hbB)
  have hb2 : b * b = 1 := by
    have := (E3.isElemAbelian_conjSubgroup h.elemAbelian g).2 b hbVg
    rwa [pow_two] at this
  have hmain : ∀ v ∈ V, v ∈ V ⊓ conjSubgroup M g := by
    intro v hv
    set w : G := ⁅v, b⁆ with hwdef
    have hbnorm : b ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hbM
    have hpvV : b * v * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hbnorm v).1 hv
    have hwV : w ∈ V := by
      have hpvinvV : b * v⁻¹ * b⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 hbnorm v⁻¹).1 (V.inv_mem hv)
      rw [hwdef, commutatorElement_def,
        show v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) by group]
      exact V.mul_mem hv hpvinvV
    have hw2 : w * w = 1 := by
      have := h.elemAbelian.2 w hwV
      rwa [pow_two] at this
    have hbwb : b * w = w * b := by
      have h1 : w * b * w * b⁻¹ = 1 := by
        have h2 := commutatorElement_mul_right_eq_mul_conj v b b
        rw [hb2, commutatorElement_one_right, ← hwdef] at h2
        exact h2.symm
      have h4 : b * w * b⁻¹ = w := by
        have h5 : w * w * (b * w * b⁻¹) = w := by
          calc w * w * (b * w * b⁻¹) = w * (w * b * w * b⁻¹) := by group
            _ = w := by rw [h1, mul_one]
        rwa [hw2, one_mul] at h5
      calc b * w = (b * w * b⁻¹) * b := by group
        _ = w * b := by rw [h4]
    have hctC : ∀ c ∈ B ⊓ C, ⁅w, c⁆ ∈ V₀ := by
      intro c hc
      have hcC : c ∈ C := hc.2
      have hcw : c * w * c⁻¹ * w⁻¹ ∈ V₀ :=
        (CFSG.LocalAnalysis.WeakClosure81.FourteenTwo.mem_cTilde_iff_comm.1 hcC).2.2 w hwV
      have hceq : ⁅w, c⁆ = (c * w * c⁻¹ * w⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [hceq]
      exact V₀.inv_mem hcw
    have hcommd : ∀ d ∈ B, ⁅w, d⁆ ∈ V₀ := by
      intro d hd
      rcases hball d hd with hbd | hd'
      · have hct : ⁅w, b * d⁆ ∈ V₀ := hctC (b * d) hbd
        have hx1 : ⁅w, b⁻¹⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          calc w * b⁻¹ = b⁻¹ * (b * w) * b⁻¹ := by group
            _ = b⁻¹ * (w * b) * b⁻¹ := by rw [hbwb]
            _ = b⁻¹ * w := by group
        have hd_eq : d = b⁻¹ * (b * d) := by group
        rw [hd_eq, commutatorElement_mul_right_eq_mul_conj, hx1, one_mul]
        exact (Subgroup.mem_normalizer_iff.1 (h.le_normalizer₀ (M.inv_mem hbM))
          (⁅w, b * d⁆)).1 hct
      · exact hctC d hd'
    have hwcent : w ∈ V ⊓ Subgroup.centralizer (B : Set G) :=
      (CFSG.LocalAnalysis.WeakClosure81.six_four_three_of_relIndex_two h64 hidx
        (D := B) le_rfl hbnot).2 w hwV hcommd
    exact (CFSG.LocalAnalysis.WeakClosure81.six_four_four_iff_of_relIndex_two h64 hidx
      hbB' hbC v hv).1 (hwdef ▸ hwcent)
  have hVleU : V ≤ conjSubgroup M g := fun v hv => (hmain v hv).2
  exact hs.1.2.1 hVleU

theorem card_U_inf_B (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    Nat.card ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) = 2 := by
  have hg : InCalO 1 M V₀ V g := hs.1
  set N : Subgroup G := (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) with hNdef
  have hNleV : N ≤ V := by rw [hNdef]; exact inf_le_left.trans inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp
    ((IsElemAbelian.isPGroup h.elemAbelian).to_le hNleV)
  have hle : Nat.card N ≤ 4 := by rw [hNdef]; exact card_U_inf_B_le h hg
  have hne1 : Nat.card N ≠ 1 := by
    intro h1
    exact U_inf_B_ne_bot h hs (Subgroup.card_eq_one.mp h1)
  have hne4 : Nat.card N ≠ 4 := by
    rw [hNdef]; exact card_U_inf_B_ne_four h hs
  have hk2 : k ≤ 2 := by
    have hp : 2 ^ k ≤ 2 ^ 2 := by rw [← hk]; simpa using hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hp
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by intro h0; exact hne1 (by rw [hk, h0]; norm_num)
    have hk2' : k ≠ 2 := by intro h2; exact hne4 (by rw [hk, h2]; norm_num)
    omega
  rw [hk, hk1]
  norm_num

theorem exists_eq_zpowers (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ∃ z : G, orderOf z = 2 ∧
      V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z := by
  set N : Subgroup G := V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) with hNdef
  have hcard : Nat.card N = 2 := by rw [hNdef]; exact card_U_inf_B h hs
  haveI : Nontrivial ↥N := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥N)
  have hzG : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hzV : (z : G) ∈ V := z.2.1.1
  have hz2 : (z : G) ^ 2 = 1 := h.elemAbelian.2 z hzV
  have hzord : orderOf (z : G) = 2 := orderOf_eq_prime hz2 hzG
  refine ⟨(z : G), hzord, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr z.2) ?_).symm
  exact le_of_eq (by rw [Nat.card_zpowers, hzord, hcard])

theorem relIndex_cTilde_B (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ((conjSubgroup V g ⊓ M) ⊓ F11.CTilde M V₀ V).relIndex (conjSubgroup V g ⊓ M) = 4 := by
  have hg : InCalO 1 M V₀ V g := hs.1
  have h64 := hyp64 h hs
  set N : Subgroup G := (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) with hNdef
  set B : Subgroup G := conjSubgroup V g ⊓ M with hBdef
  set C : Subgroup G := F11.CTilde M V₀ V with hCdef
  have hNleV : N ≤ V := by rw [hNdef]; exact inf_le_left.trans inf_le_left
  have hNcard : Nat.card N = 2 := by rw [hNdef]; exact card_U_inf_B h hs
  have hNbot : N ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ V := hNleV hx.1
    have hmem : x ∈ conjSubgroup V₀ g ⊓ V := ⟨hx.2, hxV⟩
    rwa [CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_V₀_inf_V_eq_bot h64] at hmem
  have hNcomm : ∀ x ∈ N, ∀ y ∈ conjSubgroup V₀ g, x * y = y * x := by
    intro x hx y hy
    have hxcent : x ∈ Subgroup.centralizer
        (CFSG.LocalAnalysis.WeakClosure81.LOf V g : Set G) :=
      CFSG.LocalAnalysis.WeakClosure81.NOf_le_centralizer_L h64 hx
    have hyL : y ∈ CFSG.LocalAnalysis.WeakClosure81.LOf V g :=
      Subgroup.mem_sup_right (E3.conjSubgroup_mono_left g (V₀_le h) hy)
    exact (Subgroup.mem_centralizer_iff.1 hxcent y hyL).symm
  have hNsup : Nat.card (N ⊔ conjSubgroup V₀ g : Subgroup G) = 2 * Nat.card V₀ := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute N
      (conjSubgroup V₀ g) hNcomm).1
    rw [hNbot, Subgroup.card_bot, mul_one, hNcard, E3.card_conjSubgroup V₀ g] at hcard
    exact hcard
  have hBC : B ⊓ C = N ⊔ conjSubgroup V₀ g := by
    rw [hBdef, hCdef, hNdef]
    exact CFSG.LocalAnalysis.WeakClosure81.six_four_four_centralizer_B_of_relIndex_two h64
      (relIndex_U h hs.1)
  have hcardBC : Nat.card (B ⊓ C : Subgroup G) = 2 * Nat.card V₀ := by rw [hBC, hNsup]
  have hcardB : Nat.card B = 8 * Nat.card V₀ := by rw [hBdef]; exact card_B h hg
  have hmul := Subgroup.relIndex_mul_card (H := B ⊓ C) (K := B)
  rw [inf_of_le_left inf_le_left, hcardBC, hcardB] at hmul
  have hpos : 0 < 2 * Nat.card V₀ := Nat.mul_pos (by norm_num) (Nat.card_pos (α := V₀))
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc (B ⊓ C).relIndex B * (2 * Nat.card V₀) = 8 * Nat.card V₀ := hmul
    _ = 4 * (2 * Nat.card V₀) := by ring

theorem card_barSub_B (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    Nat.card (barSub V₀ V h.elemAbelian (conjSubgroup V g ⊓ M)) = 4 := by
  rw [CFSG.LocalAnalysis.WeakClosure81.card_barSub_eq_relIndex h.elemAbelian
    h.normalizer_eq.symm.le (le_normalizer₀ h) inf_le_right, relIndex_cTilde_B h hs]

theorem rk_barSub_B (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    rk ↥(barSub V₀ V h.elemAbelian (conjSubgroup V g ⊓ M)) = 2 := by
  rw [rk, card_barSub_B h hs, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact padicValNat.prime_pow (p := 2) 2

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
