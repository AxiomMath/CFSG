module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveAxis
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFiveSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

private theorem conj_eq_self_of_isMulCommutative {V : Subgroup G}
    (hV : IsMulCommutative ↥V) {d w : G} (hd : d ∈ V) (hw : w ∈ V) :
    d * w * d⁻¹ = w := by
  have hcomm : d * w = w * d :=
    congrArg Subtype.val (mul_comm' (⟨d, hd⟩ : V) ⟨w, hw⟩)
  rw [hcomm]
  group

private theorem mem_normalizer_of_comm_mem {V₀ V I : Subgroup G} (hI : I ≤ V)
    (hV₀I : V₀ ≤ I) {x : G} (hx : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    (hxinv : ∀ v ∈ V, x⁻¹ * v * x * v⁻¹ ∈ V₀) :
    x ∈ Subgroup.normalizer (I : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hc : x * v * x⁻¹ * v⁻¹ ∈ V₀ := hx v (hI hv)
    rw [show x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v by group]
    exact I.mul_mem (hV₀I hc) hv
  · intro hv
    have hw : x * v * x⁻¹ ∈ V := hI hv
    have hc : x⁻¹ * (x * v * x⁻¹) * x * (x * v * x⁻¹)⁻¹ ∈ V₀ := hxinv _ hw
    rw [show v = (x⁻¹ * (x * v * x⁻¹) * x * (x * v * x⁻¹)⁻¹) * (x * v * x⁻¹) by
      group]
    exact I.mul_mem (hV₀I hc) hv

private theorem conj_mem_PSub {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    {x a : G} (hx : x ∈ F11.CTilde M V₀ V) (ha : a ∈ FourteenTwo.PSub M V₀ V) :
    x⁻¹ * a * x ∈ FourteenTwo.PSub M V₀ V := by
  have hxM : x ∈ M := cTilde_le_M M V₀ V hx
  have hxV₀ : x ∈ Subgroup.normalizer (V₀ : Set G) := cTilde_le_normalizer₀ hV hM hx
  have hMnormC : M ≤ Subgroup.normalizer (F11.CTilde M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
      (cTilde_subgroupOf_normal hV hM hM₀)
  obtain ⟨haC, haMC⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨haM, haCV₀⟩ := Subgroup.mem_inf.1 haMC
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · exact (Subgroup.mem_normalizer_iff''.1 (hMnormC hxM) a).1 haC
  · exact M.mul_mem (M.mul_mem (M.inv_mem hxM) haM) hxM
  · rw [Subgroup.mem_centralizer_iff] at haCV₀ ⊢
    intro w hw
    have hxw : x * w * x⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hxV₀ w).1 hw
    have hcomm : (x * w * x⁻¹) * a = a * (x * w * x⁻¹) := haCV₀ _ hxw
    calc w * (x⁻¹ * a * x) = x⁻¹ * ((x * w * x⁻¹) * a) * x := by group
      _ = x⁻¹ * (a * (x * w * x⁻¹)) * x := by rw [hcomm]
      _ = (x⁻¹ * a * x) * w := by group

private theorem normalizer_bot_eq_top :
    Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
  ext x
  rw [Subgroup.mem_normalizer_iff]
  simp only [Subgroup.mem_bot, Subgroup.mem_top, iff_true]
  intro h
  constructor
  · intro hh
    rw [hh]
    group
  · intro hh
    have h1 : h = x⁻¹ * (x * h * x⁻¹) * x := by group
    rw [hh] at h1
    simpa using h1

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

section Certified


theorem le_normalizer_Z0 (h15 : Hyp15 M V₀ V) (h : Hyp65 n M V₀ V g)
    (hV₀K : ¬ V₀ ≤ KOf M V g) (hn : (UOf M V g).relIndex V = 2) :
    M ≤ normalizer ((Z0Of M V₀ g : Subgroup G) : Set G) := by
  by_contra hnot
  rw [SetLike.not_le_iff_exists] at hnot
  obtain ⟨k, hkM, hkNot⟩ := hnot
  have hkD : conjSubgroup (Z0Of M V₀ g) k ≠ Z0Of M V₀ g :=
    fun hconj => hkNot (conjSubgroup_eq_iff_mem_normalizer.1 hconj)
  obtain ⟨x, hxCT, hxDk⟩ := exists_cTilde_conj_eq h hV₀K hn hkM hkD
  have hxD : conjSubgroup (Z0Of M V₀ g) x ≠ Z0Of M V₀ g := by
    rw [hxDk]
    exact hkD
  have hxM : x ∈ M := cTilde_le_M M V₀ V hxCT
  have hM : M ≤ Subgroup.normalizer (V : Set G) := le_of_eq h.normalizer_eq.symm
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := le_of_eq h.normalizer₀.symm
  have hxN₀ : x ∈ Subgroup.normalizer (V₀ : Set G) :=
    cTilde_le_normalizer₀ h.elemAbelian hM hxCT
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := hM hxM
  have hxV₀ : conjSubgroup V₀ x = V₀ := conjSubgroup_eq_iff_mem_normalizer.2 hxN₀
  obtain ⟨I, hIV, hV₀I, hIrelIndex, haxis⟩ := exists_axis h15 h hV₀K hn
  have hxI : x ∈ Subgroup.normalizer (I : Set G) :=
    mem_normalizer_of_comm_mem hIV hV₀I
      (FourteenTwo.mem_cTilde_iff_comm.1 hxCT).2.2
      (by
        simpa only [inv_inv] using
          (FourteenTwo.mem_cTilde_iff_comm.1 ((F11.CTilde M V₀ V).inv_mem hxCT)).2.2)
  have hxIiff : ∀ w : G, w ∈ I ↔ x * w * x⁻¹ ∈ I :=
    Subgroup.mem_normalizer_iff.1 hxI
  have hVcomm : IsMulCommutative ↥V := h.elemAbelian.1
  have hD_le_V₀ : Z0Of M V₀ g ≤ V₀ := inf_le_left
  have hDx_le_V₀ : conjSubgroup (Z0Of M V₀ g) x ≤ V₀ :=
    (E3.conjSubgroup_mono_left x hD_le_V₀).trans (le_of_eq hxV₀)
  have hsup_le : Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x ≤ V₀ :=
    sup_le hD_le_V₀ hDx_le_V₀
  have hDrel : (Z0Of M V₀ g).relIndex V₀ = 2 := relIndex_Z0_eq_two h hV₀K hn
  have hrel := Subgroup.relIndex_mul_relIndex (Z0Of M V₀ g)
    (Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x) V₀ le_sup_left hsup_le
  rw [hDrel] at hrel
  have hm_ne_one : (Z0Of M V₀ g).relIndex
      (Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x) ≠ 1 := by
    intro h1
    have hle : Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x ≤ Z0Of M V₀ g :=
      Subgroup.relIndex_eq_one.1 h1
    have hDxle : conjSubgroup (Z0Of M V₀ g) x ≤ Z0Of M V₀ g := le_sup_right.trans hle
    have hcard : Nat.card (conjSubgroup (Z0Of M V₀ g) x) = Nat.card (Z0Of M V₀ g) :=
      E3.card_conjSubgroup (Z0Of M V₀ g) x
    have heq : conjSubgroup (Z0Of M V₀ g) x = Z0Of M V₀ g :=
      Subgroup.eq_of_le_of_card_ge hDxle (le_of_eq hcard.symm)
    exact hxD heq
  have hDrel_sup : (Z0Of M V₀ g).relIndex
      (Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x) = 2 := by
    have hdvd : (Z0Of M V₀ g).relIndex
        (Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x) ∣ 2 := ⟨_, hrel.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hm_ne_one
    · exact h
  have hn_eq_one : (Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x).relIndex V₀ = 1 := by
    rw [hDrel_sup] at hrel
    omega
  have hV₀eq : Z0Of M V₀ g ⊔ conjSubgroup (Z0Of M V₀ g) x = V₀ :=
    le_antisymm hsup_le (Subgroup.relIndex_eq_one.1 hn_eq_one)
  have hDnorm : Z0Of M V₀ g ≤
      Subgroup.normalizer (conjSubgroup (Z0Of M V₀ g) x : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [conj_eq_self_of_isMulCommutative hVcomm (h.le (hD_le_V₀ hd))
        (h.le (hDx_le_V₀ hw))]
      exact hw
    · intro hw
      have hwV : d * w * d⁻¹ ∈ V := h.le (hDx_le_V₀ hw)
      have hd'V : d⁻¹ ∈ V := h.le (V₀.inv_mem (hD_le_V₀ hd))
      have hthis := conj_eq_self_of_isMulCommutative hVcomm hd'V hwV
      have hw_eq : w = d * w * d⁻¹ := by
        rw [← hthis]
        group
      rw [hw_eq]
      exact hw
  have haux : ∀ z' ∈ conjSubgroup (Z0Of M V₀ g) x,
      ∃ b ∈ FourteenTwo.PSub M V₀ V, FourteenTwo.InducesTransvection V I z' b := by
    intro z' hz'
    have hz : x * z' * x⁻¹ ∈ Z0Of M V₀ g := mem_conjSubgroup_iff.1 hz'
    obtain ⟨a, haP, haW, -⟩ := haxis (x * z' * x⁻¹) hz
    refine ⟨x⁻¹ * a * x, conj_mem_PSub h.elemAbelian hM hM₀ hxCT haP, ?_⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      have hxw : x * w * x⁻¹ ∈ I := (hxIiff w).1 hw
      calc (x⁻¹ * a * x) * w * (x⁻¹ * a * x)⁻¹
          = x⁻¹ * (a * (x * w * x⁻¹) * a⁻¹) * x := by group
        _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [haW.1 _ hxw]
        _ = w := by group
    · intro v hv hvI
      have hv' : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxV v).1 hv
      have hxvI : x * v * x⁻¹ ∉ I := fun h => hvI ((hxIiff v).2 h)
      have h2 : a * (x * v * x⁻¹) * a⁻¹ = (x * z' * x⁻¹) * (x * v * x⁻¹) :=
        haW.2 _ hv' hxvI
      calc (x⁻¹ * a * x) * v * (x⁻¹ * a * x)⁻¹
          = x⁻¹ * (a * (x * v * x⁻¹) * a⁻¹) * x := by group
        _ = x⁻¹ * ((x * z' * x⁻¹) * (x * v * x⁻¹)) * x := by rw [h2]
        _ = z' * v := by group
  have hAW : ∀ z ∈ V₀, ∃ a ∈ FourteenTwo.PSub M V₀ V,
      FourteenTwo.InducesTransvection V I z a := by
    intro z hz
    have hz_mul : z ∈ (Z0Of M V₀ g : Set G) *
        (conjSubgroup (Z0Of M V₀ g) x : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Z0Of M V₀ g)
        (conjSubgroup (Z0Of M V₀ g) x) hDnorm, hV₀eq]
      exact hz
    obtain ⟨z₁, hz₁, z₂, hz₂, hz_eq⟩ := Set.mem_mul.1 hz_mul
    obtain ⟨a₁, ha₁P, ha₁, -⟩ := haxis z₁ hz₁
    obtain ⟨a₂, ha₂P, ha₂⟩ := haux z₂ hz₂
    refine ⟨a₁ * a₂, (FourteenTwo.PSub M V₀ V).mul_mem ha₁P ha₂P, ?_⟩
    rw [← hz_eq]
    refine ⟨?_, ?_⟩
    · intro w hw
      calc (a₁ * a₂) * w * (a₁ * a₂)⁻¹
          = a₁ * (a₂ * w * a₂⁻¹) * a₁⁻¹ := by group
        _ = a₁ * w * a₁⁻¹ := by rw [ha₂.1 w hw]
        _ = w := ha₁.1 w hw
    · intro v hv hvI
      have h2 : a₂ * v * a₂⁻¹ = z₂ * v := ha₂.2 v hv hvI
      have hz₂I : z₂ ∈ I := hV₀I (hDx_le_V₀ hz₂)
      have h2V : z₂ * v ∈ V := V.mul_mem (hIV hz₂I) hv
      have h2notI : z₂ * v ∉ I := by
        intro h
        exact hvI (by
          rw [show v = z₂⁻¹ * (z₂ * v) by group]
          exact I.mul_mem (I.inv_mem hz₂I) h)
      calc (a₁ * a₂) * v * (a₁ * a₂)⁻¹
          = a₁ * (a₂ * v * a₂⁻¹) * a₁⁻¹ := by group
        _ = a₁ * (z₂ * v) * a₁⁻¹ := by rw [h2]
        _ = z₁ * (z₂ * v) := ha₁.2 (z₂ * v) h2V h2notI
        _ = (z₁ * z₂) * v := by group
  have hAV₁ : ∀ a ∈ FourteenTwo.PSub M V₀ V, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ V₀ := by
    intro a ha v hv
    exact (FourteenTwo.mem_cTilde_iff_comm.1 (Subgroup.mem_inf.1 ha).1).2.2 v hv
  have hNleV : NOf M V g ≤ V := inf_le_left.trans inf_le_left
  have hF : NOf M V g ∈ FourteenTwo.FamV V₀ (⊥ : Subgroup G) V :=
    ⟨hNleV, by rw [sup_comm, ← h.V_eq_V₀_sup_N hV₀K],
      by rw [inf_comm]; exact h.V₀_inf_N⟩
  have hprod := FourteenTwo.fourteen_two_product (M := M) (V₀ := V₀) (V₁ := V₀)
    (V₂ := (⊥ : Subgroup G)) (V := V) (A := FourteenTwo.PSub M V₀ V) (W := I)
    h.elemAbelian h.le le_rfl (inf_bot_eq V₀) (sup_bot_eq V₀) hM hM₀ hM₀
    (h15.h6.conjGenerated h15.ne_bot) le_rfl hAV₁ hIV hV₀I hIrelIndex hAW hF
  have hprod' : (M : Set G) =
      (FourteenTwo.CFixQuot (FourteenTwo.PSub M V₀ V) V₀ V : Set G) *
        ((M ⊓ Subgroup.normalizer (NOf M V g : Set G) : Subgroup G) : Set G) := by
    simpa only [normalizer_bot_eq_top, inf_top_eq] using hprod
  have hmul : ∀ m ∈ M, ∃ c ∈ F11.CTilde M V₀ V,
      ∃ y ∈ M ⊓ Subgroup.normalizer (NOf M V g : Set G), m = c * y := by
    intro m hm
    have hm' : m ∈ (FourteenTwo.CFixQuot (FourteenTwo.PSub M V₀ V) V₀ V : Set G) *
        ((M ⊓ Subgroup.normalizer (NOf M V g : Set G) : Subgroup G) : Set G) := by
      rw [← hprod']
      exact hm
    obtain ⟨c, hc, y, hy, hcy⟩ := Set.mem_mul.1 hm'
    obtain ⟨hcP, -, -⟩ := hc
    exact ⟨c, (show FourteenTwo.PSub M V₀ V ≤ F11.CTilde M V₀ V from inf_le_left) hcP,
      y, hy, hcy.symm⟩
  exact false_of_forall_eq_mul h15 h hV₀K hmul

end Certified

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81