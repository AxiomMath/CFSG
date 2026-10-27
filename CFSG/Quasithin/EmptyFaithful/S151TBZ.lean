module

public import CFSG.Quasithin.Background.FLc2UD
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.EmptyFaithful.S151V2
public import CFSG.Quasithin.Vol2.Ch1Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_blockU {L X U : Subgroup G} (hperf : ⁅L, L⁆ = L) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU2 : IsPGroup 2 U) :
    ⁅U, L⁆ ≤ blockU L := by
  have hUL_U : ⁅U, L⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : l * u⁻¹ * l⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hXU (hLX hl)) u⁻¹).1 (U.inv_mem hu)
    have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact U.mul_mem hu h1
  have hUL_L : ⁅U, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : u * l * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hXL (hUX hu)) l).1 hl
    have e : ⁅u, l⁆ = (u * l * u⁻¹) * l⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hUL_norm : L ≤ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hU' := Subgroup.mem_normalizer_iff.1 (hXU (hLX hl)) x
    have hL' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) x
    simp only [Subgroup.mem_inf] at hU' hL' ⊢
    exact and_congr hU' hL'
  have hUO : U ⊓ L ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hUL_norm
      (hU2.to_le inf_le_left)
  have hWQ : ⁅U, L⁆ ≤ pCoreOf 2 L := fun x hx => hUO ⟨hUL_U hx, hUL_L hx⟩
  have hLN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (hXL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hN1 : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hLN hx) (Subgroup.le_normalizer hx)
  have hN3 : U ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hXN (hUX hx)) (hXL (hUX hx))
  have hA : ⁅⁅L, U⁆, L⁆ ≤ blockU L := by
    rw [Subgroup.commutator_comm L U]
    exact Subgroup.commutator_mono hWQ le_rfl
  have hB : ⁅⁅U, L⁆, L⁆ ≤ blockU L := Subgroup.commutator_mono hWQ le_rfl
  have key : ⁅⁅L, L⁆, U⁆ ≤ blockU L :=
    s151v_three_subgroups_le hN1 hN1 hN3 hA hB
  rw [hperf, Subgroup.commutator_comm] at key
  exact key

theorem exists_zU {L SH Z : Subgroup G} (hLc : CharTwo L) (hperf : ⁅L, L⁆ = L)
    (hSH2 : IsPGroup 2 SH) (hSHN : SH ≤ Subgroup.normalizer (L : Set G))
    (hB : IsSylowTwoOf (SH ⊓ L) L) (hZ : Z ≤ quasithinOmegaOneCenter SH) :
    ∃ W : Subgroup G, W ≤ blockU L ∧ (∀ w ∈ W, ∀ s ∈ SH ⊓ L, s * w * s⁻¹ = w) ∧
      (∀ l ∈ L, l ∈ Subgroup.centralizer (Z : Set G) ↔ l ∈ Subgroup.centralizer (W : Set G)) ∧
      (∀ z ∈ Z, ∃ w ∈ W, ∀ l ∈ L, l * z = z * l ↔ l * w = w * l) := by
  set X := L ⊔ SH with hX
  have hLX : L ≤ X := le_sup_left
  have hSHX : SH ≤ X := le_sup_right
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSHN
  have hXc : CharTwo X := A4.charTwo_sup hLc hSHN hSH2
  have hT : IsSylowTwoOf SH X := isSylowTwoOf_sup_of_inf hSH2 hSHN hB
  obtain ⟨hle, hel, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hXc hZ
  set U := conjClosure Z X with hU
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Z X
  have hZU : Z ≤ U := le_conjClosure Z X
  have hZSH : Z ≤ SH := fun z hz => ((mem_quasithinOmegaOneCenter_iff.1 (hZ hz)).1)
  have hUX : U ≤ X := by
    refine conjClosure_le fun h hh z hz => ?_
    exact X.mul_mem (X.mul_mem hh (hSHX (hZSH hz))) (X.inv_mem hh)
  have hU2' : IsPGroup 2 U :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le (hle.trans inf_le_left)
  have := hel.1
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hU2 : ∀ a ∈ U, a ^ 2 = 1 := hel.2
  have hodd : Odd ((SH ⊓ L).relIndex L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hB.2.2)
  have hSL : ∀ s ∈ SH ⊓ L, ∀ z ∈ Z, s * z * s⁻¹ = z := by
    intro s hs z hz
    have h := (Subgroup.mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1 (hZ hz)).2.1) s
      hs.1
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [h]
      _ = z := by group
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := hLX.trans hXU
  have hd := FLc.ud_decomp (L := L) (SL := SH ⊓ L) (U := U) (Z₂ := Z) hLU hUc hU2 hodd hZU hSL
  have hUL : ⁅U, L⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : l * u⁻¹ * l⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hLU hl) u⁻¹).1 (U.inv_mem hu)
    have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact U.mul_mem hu h1
  have hWb : FLc.projZU Z L U ≤ blockU L :=
    inf_le_right.trans (commutator_le_blockU hperf hLX hXL hUX hXU hU2')
  refine ⟨FLc.projZU Z L U, hWb, ?_, fun l hl => FLc.centralizer_zU_eq hd hZU hUL l hl, ?_⟩
  · intro w hw s hs
    have hsup : Z ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) ≤
        Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun z hz => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hSL s hs z hz
        calc z * s = (s * z * s⁻¹) * s := by rw [this]
          _ = s * z := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hc.2 s hs.2).symm
    have h := hsup hw.1
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    calc s * w * s⁻¹ = (w * s) * s⁻¹ := by rw [h]
      _ = w := by group
  · intro z hz
    obtain ⟨u, hu, hfix⟩ := hd z hz
    have hc : z * u ∈ U ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨U.mul_mem (hZU hz) (hUL hu), Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have := hfix k hk
      calc k * (z * u) = (k * (z * u) * k⁻¹) * k := by group
        _ = (z * u) * k := by rw [this]
    have huW : u ∈ FLc.projZU Z L U := by
      refine ⟨?_, hu⟩
      have : u = z⁻¹ * (z * u) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (Z.inv_mem hz) hc
    refine ⟨u, huW, fun l hl => ?_⟩
    have hlzu : Commute l (z * u) := Subgroup.mem_centralizer_iff.1 hc.2 l hl
    constructor
    · intro h
      have hlz : Commute l z := h
      have hcu : Commute l (z⁻¹ * (z * u)) := (hlz.inv_right).mul_right hlzu
      have : z⁻¹ * (z * u) = u := by group
      rw [this] at hcu
      exact hcu
    · intro h
      have hlu : Commute l u := h
      have hcz : Commute l ((z * u) * u⁻¹) := hlzu.mul_right hlu.inv_right
      have : (z * u) * u⁻¹ = z := by group
      rw [this] at hcz
      exact hcz

end CFSG.Quasithin.S151TB
