module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem commutator_conj_V₀_V_le (hs : InCalOStar 1 M V₀ V g) :
    ⁅conjSubgroup V₀ g, V⁆ ≤ V₀ := by
  obtain ⟨-, K, -, -, -, -, hcomm, -, -⟩ := hs
  exact hcomm

theorem commutator_V₀_conj_V_le
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    ⁅V₀, conjSubgroup V g⁆ ≤ conjSubgroup V₀ g := by
  obtain ⟨-, K, -, -, -, -, hcomm, -, -⟩ := hs'
  simpa only [conjSubgroup_conjSubgroup_inv] using hcomm

theorem commute_V₀_conj_V₀ (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ∀ a ∈ V₀, ∀ c ∈ conjSubgroup V₀ g, a * c = c * a := by
  intro a ha c hc
  have hgM : g ∉ M := not_mem_of_inCalO h hs.1
  have hcB : c ∈ conjSubgroup V g ⊓ M := conj_V₀_le_B h hs hc
  have hcaV₀ : c * a * c⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.1 (h.le_normalizer₀ hcB.2) a).1 ha
  have hcaV₀' : c * a * c⁻¹ * a⁻¹ ∈ V₀ := V₀.mul_mem hcaV₀ (V₀.inv_mem ha)
  have haU : a ∈ V ⊓ conjSubgroup M g := V₀_le_U h hs ha
  have hnorm : normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer V₀ g, h.normalizer₀]
  have haN : a ∈ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [hnorm]
    exact haU.2
  have hcaV₀g : a * c⁻¹ * a⁻¹ ∈ conjSubgroup V₀ g :=
    (Subgroup.mem_normalizer_iff.1 haN c⁻¹).1 ((conjSubgroup V₀ g).inv_mem hc)
  have hmem : c * a * c⁻¹ * a⁻¹ ∈ V₀ ⊓ conjSubgroup V₀ g :=
    ⟨hcaV₀', by
      rw [show c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) by group]
      exact (conjSubgroup V₀ g).mul_mem hc hcaV₀g⟩
  have hbot : V₀ ⊓ conjSubgroup V₀ g = ⊥ := by
    refine le_bot_iff.mp ?_
    calc V₀ ⊓ conjSubgroup V₀ g ≤ V₀ ⊓ conjSubgroup V g :=
          inf_le_inf_left _ (E3.conjSubgroup_mono_left g (V₀_le h))
      _ = ⊥ := V₀_inf_conj_eq_bot h hgM
  rw [hbot] at hmem
  have h1 : c * a * c⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp (by
    rw [commutatorElement_def]; exact h1)).symm

theorem E_le_X (h : Cfg1667Ne M V₀ V W₁ W₂) :
    V₀ ⊔ conjSubgroup V₀ g ≤ V ⊔ conjSubgroup V g := by
  exact sup_le_sup (V₀_le h) (E3.conjSubgroup_mono_left g (V₀_le h))

theorem X_le_normalizer_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    V ⊔ conjSubgroup V g ≤ normalizer ((V₀ ⊔ conjSubgroup V₀ g : Subgroup G) : Set G) := by
  have hV0g_norm : conjSubgroup V₀ g ≤ normalizer (V₀ : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl (V₀_le h)).trans (commutator_conj_V₀_V_le hs)
  have hV0_norm : V₀ ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    calc ⁅conjSubgroup V₀ g, V₀⁆ = ⁅V₀, conjSubgroup V₀ g⁆ :=
          Subgroup.commutator_comm (conjSubgroup V₀ g) V₀
      _ ≤ ⁅V₀, conjSubgroup V g⁆ :=
            Subgroup.commutator_mono le_rfl (E3.conjSubgroup_mono_left g (V₀_le h))
      _ ≤ conjSubgroup V₀ g := commutator_V₀_conj_V_le hs'
  refine sup_le ?_ ?_
  · rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro v hv y hy
    have hy' : y ∈ (↑(conjSubgroup V₀ g) : Set G) * (↑V₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup V₀ g) V₀ hV0g_norm,
        sup_comm]
      exact hy
    obtain ⟨b, hb, a, ha, rfl⟩ := hy'
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hva : ⁅v, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext_iff.mp (h.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨a, V₀_le h ha⟩))
    have hvb : ⁅v, b⁆ ∈ V₀ := by
      have h1 : ⁅b, v⁆ ∈ V₀ :=
        commutator_conj_V₀_V_le hs (Subgroup.commutator_mem_commutator hb hv)
      rw [← commutatorElement_inv b v]
      exact V₀.inv_mem h1
    rw [hva, mul_one, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_sup_left hvb
  · rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro x hx y hy
    have hy' : y ∈ (↑V₀ : Set G) * (↑(conjSubgroup V₀ g) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V₀ (conjSubgroup V₀ g) hV0_norm]
      exact hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hxb : ⁅x, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext_iff.mp ((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1.is_comm.comm
        ⟨x, hx⟩ ⟨b, E3.conjSubgroup_mono_left g (V₀_le h) hb⟩))
    have hxa : ⁅x, a⁆ ∈ conjSubgroup V₀ g := by
      have h1 : ⁅a, x⁆ ∈ conjSubgroup V₀ g :=
        commutator_V₀_conj_V_le hs' (Subgroup.commutator_mem_commutator ha hx)
      rw [← commutatorElement_inv a x]
      exact (conjSubgroup V₀ g).inv_mem h1
    rw [hxb, mul_one, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_sup_right hxa

theorem E_normal (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (E_le_X h)).2
    (X_le_normalizer_E h hs hs')

theorem E_le_K (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    V₀ ⊔ conjSubgroup V₀ g ≤ (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) := by
  exact sup_le_sup (V₀_le_U h hs) (conj_V₀_le_B h hs)

theorem V_inf_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    V ⊓ (V₀ ⊔ conjSubgroup V₀ g) = V₀ := by
  have hgM : g ∉ M := not_mem_of_inCalO h hs.1
  have hV0g_norm : conjSubgroup V₀ g ≤ normalizer (V₀ : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl (V₀_le h)).trans (commutator_conj_V₀_V_le hs)
  refine le_antisymm ?_ (le_inf (V₀_le h) le_sup_left)
  intro x hx
  obtain ⟨hxV, hxE⟩ := Subgroup.mem_inf.mp hx
  have hx' : x ∈ (↑(conjSubgroup V₀ g) : Set G) * (↑V₀ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup V₀ g) V₀ hV0g_norm,
      sup_comm]
    exact hxE
  obtain ⟨c, hc, a, ha, rfl⟩ := hx'
  have hcV : c ∈ V := by
    have hce : c = (c * a) * a⁻¹ := by group
    rw [hce]
    exact V.mul_mem hxV (V.inv_mem (V₀_le h ha))
  have hcbot : c ∈ (⊥ : Subgroup G) := by
    rw [← inf_conj_V₀_eq_bot h hgM]
    exact ⟨hcV, hc⟩
  rw [Subgroup.mem_bot.mp hcbot]
  simpa using ha

theorem conj_V_inf_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    conjSubgroup V g ⊓ (V₀ ⊔ conjSubgroup V₀ g) = conjSubgroup V₀ g := by
  have hgM : g ∉ M := not_mem_of_inCalO h hs.1
  have hV0_norm : V₀ ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro a ha c hc
    rw [commutatorElement_eq_one_iff_mul_comm.2 (commute_V₀_conj_V₀ h hs a ha c hc)]
    exact (conjSubgroup V₀ g).one_mem
  refine le_antisymm ?_ (le_inf (E3.conjSubgroup_mono_left g (V₀_le h)) le_sup_right)
  intro x hx
  obtain ⟨hxVg, hxE⟩ := Subgroup.mem_inf.mp hx
  have hx' : x ∈ (↑V₀ : Set G) * (↑(conjSubgroup V₀ g) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V₀ (conjSubgroup V₀ g) hV0_norm]
    exact hxE
  obtain ⟨a, ha, c, hc, rfl⟩ := hx'
  have haVg : a ∈ conjSubgroup V g := by
    have hae : a = (a * c) * c⁻¹ := by group
    rw [hae]
    exact (conjSubgroup V g).mul_mem hxVg
      ((conjSubgroup V g).inv_mem (E3.conjSubgroup_mono_left g (V₀_le h) hc))
  have habot : a ∈ (⊥ : Subgroup G) := by
    rw [← V₀_inf_conj_eq_bot h hgM]
    exact ⟨ha, haVg⟩
  rw [Subgroup.mem_bot.mp habot]
  simpa using hc

theorem U_inf_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    (V ⊓ conjSubgroup M g) ⊓ (V₀ ⊔ conjSubgroup V₀ g) = V₀ := by
  refine le_antisymm ?_ ?_
  · calc (V ⊓ conjSubgroup M g) ⊓ (V₀ ⊔ conjSubgroup V₀ g) ≤
        V ⊓ (V₀ ⊔ conjSubgroup V₀ g) := inf_le_inf_right _ inf_le_left
      _ = V₀ := V_inf_E h hs
  · exact le_inf (le_inf (V₀_le h) ((V₀_le_U h hs).trans inf_le_right)) le_sup_left

theorem B_inf_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    (conjSubgroup V g ⊓ M) ⊓ (V₀ ⊔ conjSubgroup V₀ g) = conjSubgroup V₀ g := by
  refine le_antisymm ?_ ?_
  · calc (conjSubgroup V g ⊓ M) ⊓ (V₀ ⊔ conjSubgroup V₀ g) ≤
        conjSubgroup V g ⊓ (V₀ ⊔ conjSubgroup V₀ g) := inf_le_inf_right _ inf_le_left
      _ = conjSubgroup V₀ g := conj_V_inf_E h hs
  · exact le_inf (le_inf (E3.conjSubgroup_mono_left g (V₀_le h))
      ((conj_V₀_le_B h hs).trans inf_le_right)) le_sup_right

theorem N_inf_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊓ (V₀ ⊔ conjSubgroup V₀ g) = ⊥ := by
  have hgM : g ∉ M := not_mem_of_inCalO h hs.1
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨hxN, hxE⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxU, hxB⟩ := Subgroup.mem_inf.mp hxN
  have hxV₀ : x ∈ V₀ := by
    have hmem : x ∈ V ⊓ (V₀ ⊔ conjSubgroup V₀ g) := ⟨hxU.1, hxE⟩
    rwa [V_inf_E h hs] at hmem
  have hbot : x ∈ (⊥ : Subgroup G) := by
    rw [← V₀_inf_conj_eq_bot h hgM]
    exact ⟨hxV₀, hxB.1⟩
  exact hbot

theorem exists_mem_N_of_inv_mul_mem_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    {u b : G} (hu : u ∈ V ⊓ conjSubgroup M g) (hb : b ∈ conjSubgroup V g ⊓ M)
    (hub : u⁻¹ * b ∈ V₀ ⊔ conjSubgroup V₀ g) :
    ∃ n ∈ (V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M), u⁻¹ * n ∈ V₀ ⊔ conjSubgroup V₀ g := by
  have hV0_norm : V₀ ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_le]
    intro a ha c hc
    rw [commutatorElement_eq_one_iff_mul_comm.2 (commute_V₀_conj_V₀ h hs a ha c hc)]
    exact (conjSubgroup V₀ g).one_mem
  have hd : u⁻¹ * b ∈ (↑V₀ : Set G) * (↑(conjSubgroup V₀ g) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V₀ (conjSubgroup V₀ g) hV0_norm]
    exact hub
  obtain ⟨a, ha, c, hc, hEq⟩ := hd
  change a * c = u⁻¹ * b at hEq
  have hn_eq : u * a = b * c⁻¹ := by
    have h2 : u * (a * c) = b := by rw [hEq]; group
    rw [← h2]
    group
  refine ⟨u * a, ⟨?_, ?_⟩, ?_⟩
  · exact (V ⊓ conjSubgroup M g).mul_mem hu (V₀_le_U h hs ha)
  · rw [hn_eq]
    exact (conjSubgroup V g ⊓ M).mul_mem hb
      ((conjSubgroup V g ⊓ M).inv_mem (conj_V₀_le_B h hs hc))
  · rw [show u⁻¹ * (u * a) = a by group]
    exact Subgroup.mem_sup_left ha

theorem stepF (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) {v b : G}
    (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hb : b ∈ conjSubgroup V g ⊓ M)
    (hvb : ⁅v, b⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M))) :
    b ∈ conjSubgroup V₀ g ⊔ ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) := by
  have h64 : CFSG.LocalAnalysis.WeakClosure81.Hyp64 1 M V₀ V g := hyp64 h hs
  have hstep := CFSG.LocalAnalysis.WeakClosure81.StepFHyp_of_genHyp h64
    (CFSG.LocalAnalysis.WeakClosure81.genHyp_of_relIndex_two h64 (relIndex_U h hs.1))
  have hb' : ⁅b, v⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) := by
    rw [← commutatorElement_inv v b]
    exact (((V₀ ⊔ conjSubgroup V₀ g) ⊔
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) : Subgroup G)).inv_mem hvb
  exact hstep v hv hvU b hb hb'

theorem stepF_dual (h : Cfg1667Ne M V₀ V W₁ W₂)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {i u : G} (hi : i ∈ conjSubgroup V g) (hiB : i ∉ conjSubgroup V g ⊓ M)
    (hu : u ∈ V ⊓ conjSubgroup M g)
    (hiu : ⁅i, u⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M))) :
    u ∈ V₀ ⊔ ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) := by
  have hdual := stepF (h.conj g) hs' (v := i) (b := u)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using hi)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using hiB)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using hu)
    (by simpa only [conjSubgroup_conjSubgroup_inv, sup_comm, inf_comm, inf_assoc] using hiu)
  simpa only [conjSubgroup_conjSubgroup_inv, sup_comm, inf_comm, inf_assoc] using hdual

theorem exists_not_commute (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ∃ u ∈ V ⊓ conjSubgroup M g, ∃ b ∈ conjSubgroup V g ⊓ M, u * b ≠ b * u := by
  by_contra hc
  push Not at hc
  have hgM : g ∉ M := not_mem_of_inCalO h hs.1
  have hUcent : V ⊓ conjSubgroup M g ≤ Subgroup.centralizer
      ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hc u hu b hb).symm
  have hUle : V ⊓ conjSubgroup M g ≤
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊔ V₀ := by
    have h1 : V ⊓ conjSubgroup M g ≤ V ⊓ Subgroup.centralizer
        ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := le_inf inf_le_left hUcent
    rwa [inf_centralizer_B_eq h hs] at h1
  have hcomm : ∀ x ∈ ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)),
      ∀ y ∈ V₀, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp (h.elemAbelian.1.is_comm.comm
      ⟨x, hx.1.1⟩ ⟨y, V₀_le h hy⟩)
  have hNbot : ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊓ V₀ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxN, hxV₀⟩ := Subgroup.mem_inf.mp hx
    have hxVg : x ∈ conjSubgroup V g := (Subgroup.mem_inf.mp hxN.2).1
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [← V₀_inf_conj_eq_bot h hgM]
      exact ⟨hxV₀, hxVg⟩
    exact Subgroup.mem_bot.mp hbot
  have hsupcard : Nat.card
      ((((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊔ V₀ : Subgroup G)) =
        2 * Nat.card V₀ := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) V₀ hcomm).1
    rw [hNbot, Subgroup.card_bot, card_U_inf_B h hs] at hcard
    simpa using hcard
  have hUle' := Subgroup.card_le_of_le hUle
  rw [hsupcard, card_U h hs.1] at hUle'
  have hpos : 0 < Nat.card V₀ := Nat.card_pos (α := V₀)
  omega

theorem K_le_X (h : Cfg1667Ne M V₀ V W₁ W₂) :
    (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) ≤ V ⊔ conjSubgroup V g := by
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

theorem K_le_M (h : Cfg1667Ne M V₀ V W₁ W₂) :
    (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) ≤ M := by
  exact sup_le (inf_le_left.trans (le_M h)) inf_le_right

theorem K_normal (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    (((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)).subgroupOf
      (V ⊔ conjSubgroup V g)).Normal := by
  have h64 : CFSG.LocalAnalysis.WeakClosure81.Hyp64 1 M V₀ V g := hyp64 h hs
  obtain ⟨-, K₀, hK₀n, hK₀set, -⟩ := hs
  obtain ⟨K', hK'_eq, -, -, -, hK'set⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.inCalOStar_K_facts h64
  have hKK' : K₀ = K' := SetLike.coe_injective (by
    rw [hK₀set, hK'set]
    simp only [CFSG.LocalAnalysis.WeakClosure81.BOf, CFSG.LocalAnalysis.WeakClosure81.UOf])
  have hK_eq : (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) = K₀ := by
    rw [hKK', hK'_eq]
    simp only [CFSG.LocalAnalysis.WeakClosure81.UOf, CFSG.LocalAnalysis.WeakClosure81.BOf]
  rwa [hK_eq]

theorem V_inf_K (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    V ⊓ ((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)) = V ⊓ conjSubgroup M g := by
  have h64 : CFSG.LocalAnalysis.WeakClosure81.Hyp64 1 M V₀ V g := hyp64 h hs
  obtain ⟨K', hK'_eq, -, -, -, hK'set⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.inCalOStar_K_facts h64
  have h := CFSG.LocalAnalysis.WeakClosure81.V_inf_K_eq_U h64 hK'set
  rw [hK'_eq] at h
  simpa only [CFSG.LocalAnalysis.WeakClosure81.UOf, CFSG.LocalAnalysis.WeakClosure81.BOf] using h

theorem K_inf_centralizer_V_le (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g) :
    ((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)) ⊓ centralizer (V : Set G) ≤
      V ⊓ conjSubgroup M g := by
  have h64 : CFSG.LocalAnalysis.WeakClosure81.Hyp64 1 M V₀ V g := hyp64 h hs
  intro k hk
  obtain ⟨hkK, hkV⟩ := Subgroup.mem_inf.mp hk
  have hKset : (((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) : Subgroup G) : Set G) =
      (↑(V ⊓ conjSubgroup M g) : Set G) * (↑(conjSubgroup V g ⊓ M) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_B h)
  have hk' : k ∈ (↑(V ⊓ conjSubgroup M g) : Set G) * (↑(conjSubgroup V g ⊓ M) : Set G) := by
    rw [← hKset]
    exact hkK
  obtain ⟨u, hu, b, hb, rfl⟩ := hk'
  have huC : u ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subtype.ext_iff.mp (h.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨u, hu.1⟩)
  have hbC : b ∈ Subgroup.centralizer (V : Set G) := by
    have h2 : u⁻¹ * (u * b) ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.centralizer (V : Set G)).mul_mem
        ((Subgroup.centralizer (V : Set G)).inv_mem huC) hkV
    rwa [inv_mul_cancel_left] at h2
  have hbCT : b ∈ F11.CTilde M V₀ V := by
    rw [CFSG.LocalAnalysis.WeakClosure81.FourteenTwo.mem_cTilde_iff_comm]
    refine ⟨hb.2, h.le_normalizer₀ hb.2, fun v hv => ?_⟩
    have hcomm : v * b = b * v := Subgroup.mem_centralizer_iff.1 hbC v hv
    have h1 : b * v * b⁻¹ * v⁻¹ = 1 := by rw [← hcomm]; group
    rw [h1]
    exact V₀.one_mem
  have hbN : b ∈ ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ⊔ conjSubgroup V₀ g := by
    have hmem : b ∈ (conjSubgroup V g ⊓ M) ⊓ F11.CTilde M V₀ V := ⟨hb, hbCT⟩
    rwa [inf_cTilde_B_eq h hs] at hmem
  have hNnorm : ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ≤
      normalizer (conjSubgroup V₀ g : Set G) := by
    have h1 : ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) ≤
        Subgroup.centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) := by
      simpa only [CFSG.LocalAnalysis.WeakClosure81.NOf,
        CFSG.LocalAnalysis.WeakClosure81.UOf, CFSG.LocalAnalysis.WeakClosure81.BOf,
        CFSG.LocalAnalysis.WeakClosure81.LOf]
        using CFSG.LocalAnalysis.WeakClosure81.NOf_le_centralizer_L h64
    refine h1.trans ?_
    refine (Subgroup.centralizer_le ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro y hy
    exact Subgroup.mem_sup_right (E3.conjSubgroup_mono_left g (V₀_le h) hy)
  have hb' : b ∈ (↑((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M)) : Set G) *
      (↑(conjSubgroup V₀ g) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNnorm]
    exact hbN
  obtain ⟨n, hn, y, hy, hb_eq⟩ := hb'
  change n * y = b at hb_eq
  have hnC : n ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : n ∈ Subgroup.centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) := by
      simpa only [CFSG.LocalAnalysis.WeakClosure81.NOf,
        CFSG.LocalAnalysis.WeakClosure81.UOf, CFSG.LocalAnalysis.WeakClosure81.BOf,
        CFSG.LocalAnalysis.WeakClosure81.LOf]
        using CFSG.LocalAnalysis.WeakClosure81.NOf_le_centralizer_L h64 hn
    exact (Subgroup.centralizer_le (by intro x hx; exact Subgroup.mem_sup_left hx)) h1
  have hyC : y ∈ Subgroup.centralizer (V : Set G) := by
    have hy_eq : y = n⁻¹ * b := by rw [← hb_eq]; group
    rw [hy_eq]
    exact (Subgroup.centralizer (V : Set G)).mul_mem
      ((Subgroup.centralizer (V : Set G)).inv_mem hnC) hbC
  by_cases hy1 : y = 1
  · have hbU : b ∈ V ⊓ conjSubgroup M g := by
      have hbn : b = n := by rw [← hb_eq, hy1, mul_one]
      rw [hbn]
      exact hn.1
    exact (V ⊓ conjSubgroup M g).mul_mem hu hbU
  · exfalso
    have hy_cen : V ≤ Subgroup.centralizer ({y} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (Subgroup.mem_centralizer_iff.1 hyC v hv).symm
    have hleMg : V ≤ conjSubgroup M g :=
      hy_cen.trans (CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_V₀_centralizer_le h64 hy hy1)
    exact hs.1.2.1 hleMg

theorem mem_M_of_commutator_mem_E (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    {c : G} (hc : ∀ u ∈ V ⊓ conjSubgroup M g, c * u * c⁻¹ * u⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ g) :
    c ∈ M := by
  have hgM : g ∉ M := not_mem_of_inCalO h hs.1
  by_contra hcM
  have hc'M : c⁻¹ ∉ M := fun hci => hcM (by simpa using M.inv_mem hci)
  have hcommUV0 : ∀ u ∈ V ⊓ conjSubgroup M g, ∀ y ∈ conjSubgroup V₀ g, u * y = y * u := by
    intro u hu y hy
    have hmem : ⁅u, y⁆ ∈ V ⊓ conjSubgroup V₀ g := by
      constructor
      · have hynorm : y ∈ normalizer (V : Set G) := by
          rw [h.normalizer_eq]
          exact (conj_V₀_le_B h hs hy).2
        have hyu : y * u⁻¹ * y⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 hynorm u⁻¹).1 (V.inv_mem hu.1)
        rw [commutatorElement_def, show u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹ * y⁻¹) by group]
        exact V.mul_mem hu.1 hyu
      · have hunorm : u ∈ normalizer (conjSubgroup V₀ g : Set G) := by
          have hnorm : normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup M g := by
            rw [← E3.conjSubgroup_normalizer V₀ g, h.normalizer₀]
          rw [hnorm]
          exact hu.2
        have huy : u * y * u⁻¹ ∈ conjSubgroup V₀ g :=
          (Subgroup.mem_normalizer_iff.1 hunorm y).1 hy
        rw [commutatorElement_def, show u * y * u⁻¹ * y⁻¹ = (u * y * u⁻¹) * y⁻¹ by group]
        exact (conjSubgroup V₀ g).mul_mem huy ((conjSubgroup V₀ g).inv_mem hy)
    have hbot : V ⊓ conjSubgroup V₀ g = ⊥ := inf_conj_V₀_eq_bot h hgM
    rw [hbot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hUbot : (V ⊓ conjSubgroup M g) ⊓ conjSubgroup V₀ g = ⊥ := by
    refine le_bot_iff.mp ?_
    calc (V ⊓ conjSubgroup M g) ⊓ conjSubgroup V₀ g ≤ V ⊓ conjSubgroup V₀ g :=
          inf_le_inf_right _ inf_le_left
      _ = ⊥ := inf_conj_V₀_eq_bot h hgM
  have hPcard : Nat.card ((V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g : Subgroup G) =
      8 * Nat.card V₀ * Nat.card V₀ := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (V ⊓ conjSubgroup M g) (conjSubgroup V₀ g) hcommUV0).1
    rw [hUbot, Subgroup.card_bot, card_U h hs.1, E3.card_conjSubgroup] at hcard
    simpa using hcard
  have hPset : (((V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g : Subgroup G) : Set G) =
      (↑(V ⊓ conjSubgroup M g) : Set G) * (↑(conjSubgroup V₀ g) : Set G) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (V ⊓ conjSubgroup M g) (conjSubgroup V₀ g) hcommUV0).2
  have hU'leP : conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ ≤
      (V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hx' : c⁻¹ * x * c ∈ V ⊓ conjSubgroup M g := by simpa using hx
    have hx_eq : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [hx_eq]
    have hEP : V₀ ⊔ conjSubgroup V₀ g ≤ (V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g :=
      sup_le ((V₀_le_U h hs).trans le_sup_left) le_sup_right
    have hE : c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹ ∈
        (V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g :=
      hEP (hc (c⁻¹ * x * c) hx')
    have hsplit : c * (c⁻¹ * x * c) * c⁻¹ =
        (c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹) * (c⁻¹ * x * c) := by group
    rw [hsplit]
    exact ((V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g).mul_mem hE
      (Subgroup.mem_sup_left hx')
  have hU'leV : conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ ≤ conjSubgroup V c⁻¹ :=
    E3.conjSubgroup_mono_left c⁻¹ inf_le_left
  have hcommUU' : ∀ x ∈ V ⊓ conjSubgroup M g,
      ∀ y ∈ conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹, x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ (↑(V ⊓ conjSubgroup M g) : Set G) * (↑(conjSubgroup V₀ g) : Set G) := by
      rw [← hPset]
      exact hU'leP hy
    obtain ⟨n, hn, v, hv, rfl⟩ := hy'
    have hxn : x * n = n * x := Subtype.ext_iff.mp (h.elemAbelian.1.is_comm.comm
      ⟨x, hx.1⟩ ⟨n, hn.1⟩)
    have hxv : x * v = v * x := hcommUV0 x hx v hv
    calc x * (n * v) = (x * n) * v := by group
      _ = (n * x) * v := by rw [hxn]
      _ = n * (x * v) := by group
      _ = n * (v * x) := by rw [hxv]
      _ = (n * v) * x := by group
  have hcardUU' := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (V ⊓ conjSubgroup M g) (conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹) hcommUU').1
  have hsup_le : Nat.card ((V ⊓ conjSubgroup M g) ⊔
      conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G) ≤
      8 * Nat.card V₀ * Nat.card V₀ := by
    have hle : (V ⊓ conjSubgroup M g) ⊔ conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ ≤
        (V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g := sup_le le_sup_left hU'leP
    calc Nat.card ((V ⊓ conjSubgroup M g) ⊔
          conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G)
        ≤ Nat.card ((V ⊓ conjSubgroup M g) ⊔ conjSubgroup V₀ g : Subgroup G) :=
          Subgroup.card_le_of_le hle
      _ = 8 * Nat.card V₀ * Nat.card V₀ := hPcard
  have hinf_le4 : Nat.card ((V ⊓ conjSubgroup M g) ⊓
      conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G) ≤ 4 := by
    have hle1 : (V ⊓ conjSubgroup M g) ⊓ conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ ≤ V :=
      (inf_le_left : (V ⊓ conjSubgroup M g) ⊓ conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ ≤
        V ⊓ conjSubgroup M g).trans (inf_le_left : V ⊓ conjSubgroup M g ≤ V)
    have hle2 : (V ⊓ conjSubgroup M g) ⊓ conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ ≤
        conjSubgroup V c⁻¹ := inf_le_right.trans hU'leV
    exact (Subgroup.card_le_of_le (le_inf hle1 hle2)).trans (card_inf_conj_le h hc'M)
  have hkey : Nat.card (V ⊓ conjSubgroup M g : Subgroup G) *
      Nat.card (V ⊓ conjSubgroup M g : Subgroup G) ≤
      (8 * Nat.card V₀ * Nat.card V₀) * 4 := by
    calc Nat.card (V ⊓ conjSubgroup M g : Subgroup G) *
          Nat.card (V ⊓ conjSubgroup M g : Subgroup G)
        = Nat.card (V ⊓ conjSubgroup M g : Subgroup G) *
          Nat.card (conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G) := by
          rw [E3.card_conjSubgroup]
      _ = Nat.card ((V ⊓ conjSubgroup M g) ⊔
            conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G) *
          Nat.card ((V ⊓ conjSubgroup M g) ⊓
            conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G) := hcardUU'.symm
      _ ≤ (8 * Nat.card V₀ * Nat.card V₀) *
          Nat.card ((V ⊓ conjSubgroup M g) ⊓
            conjSubgroup (V ⊓ conjSubgroup M g) c⁻¹ : Subgroup G) :=
          Nat.mul_le_mul_right _ hsup_le
      _ ≤ (8 * Nat.card V₀ * Nat.card V₀) * 4 := Nat.mul_le_mul_left _ hinf_le4
  rw [card_U h hs.1] at hkey
  have hpos : 0 < Nat.card V₀ := Nat.card_pos (α := V₀)
  nlinarith [hkey, hpos]

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
