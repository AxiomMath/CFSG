module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreConj

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

structure NatCounts (X S Z : Subgroup G) (m : ℕ) : Prop where
  offender_le : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
    (A ⊓ pCoreOf 2 X).relIndex A ≤ m
  offender_ge : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
    m ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z
  thompsonJ_le : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
    thompsonJ S ≤ A ⊔ pCoreOf 2 X
  residual_inf_le : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
    ∀ s ∈ pResidualOf 2 X ⊓ S, ∃ a ∈ A, ∃ q ∈ pCoreOf 2 X, s = a * q ∧
      ∀ z ∈ Z, (∀ j ∈ thompsonJ S,
        ⁅j, z⁆ ∈ Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)) → a * z * a⁻¹ = z
  generated : ∃ g ∈ pResidualOf 2 X,
    pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X
  index_ge : m ^ 2 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z

section Helpers

theorem relIndex_pos [Finite G] (H K : Subgroup G) : 0 < H.relIndex K :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

theorem relIndex_le_of_le [Finite G] {H K : Subgroup G} (L : Subgroup G) (h : H ≤ K) :
    K.relIndex L ≤ H.relIndex L :=
  Nat.le_of_dvd (relIndex_pos H L) (Subgroup.relIndex_dvd_of_le_left L h)

theorem exists_offender [Finite G] {S Q : Subgroup G} (hJ : ¬ thompsonJ S ≤ Q) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q := by
  by_contra hcon
  push Not at hcon
  exact hJ (iSup₂_le fun A hA => hcon A hA)

theorem omegaOneCenterOf_le_inf (J : Subgroup G) :
    omegaOneCenterOf J ≤ J ⊓ Subgroup.centralizer (J : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem relIndex_eq_of_le_sup [Finite G] {Z M D : Subgroup G} (hZM : Z ≤ M) (hDM : D ≤ M)
    (hDZ : D ≤ Subgroup.normalizer (Z : Set G)) (hM : M ≤ Z ⊔ D) :
    D.relIndex M = (Z ⊓ D).relIndex Z := by
  have h := relIndex_sup_centralizer hZM hDM hDZ
  have h1 : (Z ⊔ D).relIndex M = 1 := Subgroup.relIndex_eq_one.mpr hM
  rw [h, h1, mul_one]

theorem conj_mem_centralizer {g c : G} {L : Subgroup G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hl'
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * l := by group

theorem eq_sup_centralizer_of_count [Finite G] {Z M L : Subgroup G} {n : ℕ} (hZM : Z ≤ M)
    (hMN : M ≤ Subgroup.normalizer (Z : Set G))
    (hcount : (M ⊓ Subgroup.centralizer (L : Set G)).relIndex M ≤ n)
    (hge : n ≤ (Z ⊓ Subgroup.centralizer (L : Set G)).relIndex Z) :
    M ≤ Z ⊔ (M ⊓ Subgroup.centralizer (L : Set G)) ∧
      (Z ⊓ Subgroup.centralizer (L : Set G)).relIndex Z = n := by
  set D := M ⊓ Subgroup.centralizer (L : Set G) with hD
  have hDM : D ≤ M := inf_le_left
  have hDZ : D ≤ Subgroup.normalizer (Z : Set G) := hDM.trans hMN
  have hfac := relIndex_sup_centralizer hZM hDM hDZ
  have hZD : Z ⊓ D = Z ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hD, ← inf_assoc, inf_of_le_left hZM]
  rw [hZD] at hfac
  set a := (Z ⊓ Subgroup.centralizer (L : Set G)).relIndex Z with ha
  set b := (Z ⊔ D).relIndex M with hb
  have ha_pos : 0 < a := relIndex_pos _ _
  have hb_pos : 0 < b := relIndex_pos _ _
  have hb1 : b = 1 := by
    have h1 : a * b ≤ a * 1 := by rw [mul_one, ← hfac]; exact hcount.trans hge
    exact le_antisymm (Nat.le_of_mul_le_mul_left h1 ha_pos) hb_pos
  refine ⟨Subgroup.relIndex_eq_one.mp hb1, le_antisymm ?_ hge⟩
  rw [hb1, mul_one] at hfac
  exact hfac ▸ hcount

theorem mem_normalizer_sup_of_mem_centMod {W V Z : Subgroup G} (hWV : W ≤ V) {i : G}
    (hi : i ∈ centMod Z V) : i ∈ Subgroup.normalizer ((W ⊔ Z : Subgroup G) : Set G) := by
  have key : ∀ j ∈ centMod Z V, cj j (W ⊔ Z) ≤ W ⊔ Z := by
    intro j hj
    obtain ⟨hjN, hjc⟩ := hj
    rw [cj, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · intro x hx
      have hx' : j⁻¹ * x * j ∈ W := mem_cj.mp hx
      set w := j⁻¹ * x * j with hw
      have h1 : ⁅w, j⁆ ∈ Z := hjc w (hWV hx')
      have h2 : ⁅j, w⁆ ∈ Z := by
        rw [← commutatorElement_inv]; exact Z.inv_mem h1
      have : x = ⁅j, w⁆ * w := by
        simp only [hw, commutatorElement_def]; group
      rw [this]
      exact (W ⊔ Z).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hx')
    · exact (cj_le_of_le_of_mem_normalizer hjN le_rfl).trans le_sup_right
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    refine key i hi ?_
    rw [mem_cj]; simpa [mul_assoc] using hx
  · intro hx
    have hi' : i⁻¹ ∈ centMod Z V := Subgroup.inv_mem _ hi
    refine ?_
    have h2 : i⁻¹ * (i * x * i⁻¹) * i⁻¹⁻¹ ∈ cj i⁻¹ (W ⊔ Z) := by
      rw [mem_cj]; simpa [mul_assoc] using hx
    have := key i⁻¹ hi' h2
    simpa [mul_assoc] using this

end Helpers

section T3

variable [Finite G] {X S Z : Subgroup G}

theorem conjJoin_le_centMod (h : PushHyp X S Z)
    (hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A) :
    conjJoin X (thompsonJ S) ≤ centMod Z (omegaOneCenterOf (thompsonJ (pCoreOf 2 X))) := by
  have hJK := commutator_le_of_equality h hall
  refine conjJoin_le fun g hg x hx => ?_
  have hx' : g⁻¹ * x * g ∈ thompsonJ S := mem_cj.mp hx
  have := conj_mem_centMod (h.normal hg) (le_normalizer_omegaOneCenter_core X hg) (hJK hx')
  simpa [mul_assoc] using this

theorem conjJoin_le_normalizer_sup (h : PushHyp X S Z)
    (hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A)
    (hW : omegaOneCenterOf (thompsonJ S) ≤ omegaOneCenterOf (thompsonJ (pCoreOf 2 X))) :
    conjJoin X (thompsonJ S) ≤
      Subgroup.normalizer ((omegaOneCenterOf (thompsonJ S) ⊔ Z : Subgroup G) : Set G) :=
  fun _ hi => mem_normalizer_sup_of_mem_centMod hW (conjJoin_le_centMod h hall hi)

end T3

section Main

variable [Finite G] {X S Z : Subgroup G} {m : ℕ}

theorem pu1_of_counts (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X)
    (hN : NatCounts X S Z m) :
    pResidualOf 2 X ⊓ S ≤ baum S ∧ IsSylowTwoOf (baum S) (conjClosure (baum S) X) ∧
      (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z = m ^ 2 := by
  set J := thompsonJ S with hJdef
  set L := pResidualOf 2 X with hL
  set Q := pCoreOf 2 X with hQ
  set W := omegaOneCenterOf J with hW
  set WQ := omegaOneCenterOf (thompsonJ Q) with hWQ
  have hSX : S ≤ X := h.le_self
  have hJS : J ≤ S := thompsonJ_le_self S
  have hJX : J ≤ X := hJS.trans hSX
  have hLX : L ≤ X := pResidualOf_le_self X
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_pResidualOf X
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  have hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ Q →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ Q).relIndex A := fun A hA hAQ =>
    le_antisymm (offender_count h hA) ((hN.offender_le A hA hAQ).trans (hN.offender_ge A hA hAQ))
  obtain ⟨-, -, -, hWWQ⟩ := offender_equality h hA₀ (hall A₀ hA₀ hA₀Q)
  have hmeq : (Z ⊓ Subgroup.centralizer (A₀ : Set G)).relIndex Z = m :=
    le_antisymm ((hall A₀ hA₀ hA₀Q).le.trans (hN.offender_le A₀ hA₀ hA₀Q))
      (hN.offender_ge A₀ hA₀ hA₀Q)
  obtain ⟨g₀, hg₀, hgen⟩ := hN.generated
  obtain ⟨hIeq, hLI⟩ := conjJoin_eq_sup_cj h hg₀ hgen
  set I := conjJoin X J with hI
  set M := W ⊔ Z with hM
  have hIN : ∀ i ∈ I, i ∈ Subgroup.normalizer (M : Set G) := fun i hi =>
    conjJoin_le_normalizer_sup h hall hWWQ hi
  have hWJ : W ≤ J ⊓ Subgroup.centralizer (J : Set G) := omegaOneCenterOf_le_inf J
  have hWX : W ≤ X := hWJ.trans (inf_le_left.trans hJX)
  have hMX : M ≤ X := sup_le hWX (h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
  have hZM : Z ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (Z : Set G) := hMX.trans h.normal
  have hZL : Z ≤ M := hZM
  have hrJ : (M ⊓ Subgroup.centralizer (J : Set G)).relIndex M ≤ m := by
    set C := M ⊓ Subgroup.centralizer (J : Set G) with hC
    have hWC : W ≤ C := le_inf le_sup_left (hWJ.trans inf_le_right)
    have hMC : M ≤ Z ⊔ C := sup_le (hWC.trans le_sup_right) le_sup_left
    have h1 : C.relIndex M = (Z ⊓ C).relIndex Z :=
      relIndex_eq_of_le_sup hZM inf_le_left (inf_le_left.trans hMN) hMC
    have h2 : Z ⊓ C = Z ⊓ Subgroup.centralizer (J : Set G) := by
      rw [hC, ← inf_assoc, inf_of_le_left hZM]
    have h3 : Z ⊓ Subgroup.centralizer (A₀ : Set G) ≤ Z ⊓ Subgroup.centralizer (J : Set G) := by
      intro x ⟨hxZ, hxA⟩
      refine ⟨hxZ, ?_⟩
      have hle : J ≤ Subgroup.centralizer ({x} : Set G) := by
        refine (hN.thompsonJ_le A₀ hA₀ hA₀Q).trans (sup_le (fun a ha => ?_) (fun q hq => ?_))
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
          exact (Subgroup.mem_centralizer_iff.mp hxA a ha).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
          exact (h.core_le_centralizer hq x hxZ)
      show x ∈ Subgroup.centralizer (J : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) x rfl).symm
    rw [h1, h2, ← hmeq]
    exact relIndex_le_of_le Z h3
  have hg₀I : g₀ ∈ I := hLI hg₀
  have hg₀N : g₀ ∈ Subgroup.normalizer (M : Set G) := hIN g₀ hg₀I
  have hcount : (M ⊓ Subgroup.centralizer (I : Set G)).relIndex M ≤ m ^ 2 := by
    rw [hIeq]
    exact (relIndex_inf_centralizer_sup_cj_le hg₀N).trans (Nat.pow_le_pow_left hrJ 2)
  set D := M ⊓ Subgroup.centralizer (L : Set G) with hD
  have hDM : D ≤ M := inf_le_left
  have hDZ : D ≤ Subgroup.normalizer (Z : Set G) := hDM.trans hMN
  have hDle : D.relIndex M ≤ m ^ 2 := by
    refine le_trans (relIndex_le_of_le M ?_) hcount
    exact inf_le_inf_left M (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLI))
  obtain ⟨hMD, haeq⟩ := eq_sup_centralizer_of_count hZM hMN hDle hN.index_ge
  have hLS : pResidualOf 2 X ⊓ S ≤ baum S := by
    intro s hs
    rw [show baum S = S ⊓ Subgroup.centralizer (W : Set G) from rfl]
    refine ⟨hs.2, ?_⟩
    show s ∈ Subgroup.centralizer (W : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨z, hz, c, hc, hwzc⟩ := mem_sup_of_le_normalizer (N := Z) (K := D) hDZ
      (hMD (le_sup_left (a := W) (b := Z) hw))
    obtain ⟨hcM, hcL⟩ := hc
    obtain ⟨a', ha', q, hq, hsaq, hza'⟩ := hN.residual_inf_le A₀ hA₀ hA₀Q s hs
    have hzX : z ∈ X := h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hz
    have hprem : ∀ j ∈ J, ⁅j, z⁆ ∈ Z ⊓ Subgroup.centralizer (L : Set G) := by
      intro j hj
      have hjX : j ∈ X := hJX hj
      have hjZ : j ∈ Subgroup.normalizer (Z : Set G) := h.normal hjX
      have hjM : j ∈ Subgroup.normalizer (M : Set G) := hIN j (le_conjJoin hj)
      have hjw : j * w = w * j := (Subgroup.mem_centralizer_iff.mp (hWJ hw).2 j hj)
      rw [hwzc] at hjw
      have h1 : j * z = z * c * j * c⁻¹ := by
        calc j * z = j * (z * c) * c⁻¹ := by group
          _ = (z * c) * j * c⁻¹ := by rw [hjw]
          _ = z * c * j * c⁻¹ := by rfl
      have e : ⁅j, z⁆ = z * (c * (j * c * j⁻¹)⁻¹) * z⁻¹ := by
        rw [commutatorElement_def, show j * z * j⁻¹ * z⁻¹ = (j * z) * j⁻¹ * z⁻¹ by rfl, h1]
        group
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hjZ z).mp hz
        exact Z.mul_mem this (Z.inv_mem hz)
      · rw [e]
        have hjc : j * c * j⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
          conj_mem_centralizer (hXL hjX) hcL
        have hd : c * (j * c * j⁻¹)⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
          Subgroup.mul_mem _ hcL (Subgroup.inv_mem _ hjc)
        have := conj_mem_centralizer (hXL hzX) hd
        simpa [mul_assoc] using this
    have hzs : a' * z * a'⁻¹ = z := hza' z hz hprem
    have haz : a' * z = z * a' := by
      calc a' * z = a' * z * a'⁻¹ * a' := by group
        _ = z * a' := by rw [hzs]
    have hqz : z * q = q * z := (h.core_le_centralizer hq z hz)
    have hszs : s * z = z * s := by
      rw [hsaq]
      calc a' * q * z = a' * (q * z) := mul_assoc _ _ _
        _ = a' * (z * q) := by rw [hqz]
        _ = (a' * z) * q := (mul_assoc _ _ _).symm
        _ = (z * a') * q := by rw [haz]
        _ = z * (a' * q) := mul_assoc _ _ _
    have hcs : s * c = c * s := (Subgroup.mem_centralizer_iff.mp hcL s hs.1)
    rw [hwzc]
    calc z * c * s = z * (c * s) := mul_assoc _ _ _
      _ = z * (s * c) := by rw [hcs]
      _ = (z * s) * c := (mul_assoc _ _ _).symm
      _ = (s * z) * c := by rw [hszs]
      _ = s * (z * c) := mul_assoc _ _ _
  refine ⟨hLS, ?_, haeq⟩
  exact sylow_conjClosure_of_residual_inf_le h.sylow inf_le_left
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum S)) hLS

end Main

end CFSG.Quasithin.F53Push
