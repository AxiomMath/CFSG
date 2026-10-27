module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_conj_le {H K : Subgroup G}
    (hn : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set G) :=
  fun x hx => Subgroup.mem_normalizer_iff.mpr fun k =>
    ⟨fun hk => hn x hx k hk, fun hk => by
      have := hn x⁻¹ (H.inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem mem_normalizer_conjClosure {Z H : Subgroup G} {d : G}
    (hZ : d ∈ Subgroup.normalizer (Z : Set G)) (hH : d ∈ Subgroup.normalizer (H : Set G)) :
    d ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ e : G, e ∈ Subgroup.normalizer (Z : Set G) →
      e ∈ Subgroup.normalizer (H : Set G) →
      ∀ x ∈ conjClosure Z H, e * x * e⁻¹ ∈ conjClosure Z H := by
    intro e hZe hHe x hx
    have hle : (conjClosure Z H).map (MulAut.conj e).toMonoidHom ≤ conjClosure Z H := by
      unfold conjClosure
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, hk, z, hz, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨e * k * e⁻¹, (Subgroup.mem_normalizer_iff.mp hHe k).mp hk,
        e * z * e⁻¹, (Subgroup.mem_normalizer_iff.mp hZe z).mp hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hle ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key d hZ hH x, fun hx => ?_⟩
  have := key d⁻¹ (inv_mem hZ) (inv_mem hH) _ hx
  simpa [mul_assoc] using this

namespace Hyp331

theorem commutator_qL_le_blockU (hshort : IsShort2 L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : ⁅qL L T, L⁆ ≤ blockU L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hQN : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hgen := L246C127.le_closure_oddPPow hshort.1
  have h1 := L246C127.commutator_le_commutator_commutator_two hQ2 (le_sup_left.trans hQN) hgen
  have hLQ : ⁅qL L T, L⁆ ≤ L ⊓ qL L T :=
    le_inf (commutator_le_right_of_le_normalizer (hQLT.trans hLN))
      (commutator_le_left_of_le_normalizer (le_sup_left.trans hQN))
  have hO : L ⊓ qL L T ≤ blockQ L := by
    show L ⊓ qL L T ≤ pCoreOf 2 L
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx)
        (hQN (le_sup_left (a := L) (b := T) hx))) ?_
    exact hQ2.to_le inf_le_right
  exact h1.trans (Subgroup.commutator_mono (hLQ.trans hO) le_rfl)

theorem blockU_le_vPlus
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hshort : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    blockU L ≤ vPlus L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hV2 : IsPGroup 2 ↥(vPlus L T) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le hVQ
  have hgen := L246C127.le_closure_oddPPow hshort.1
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (commutator_qL_le_blockU hshort hTL)
  have hVLL := L246C127.commutator_le_commutator_commutator_two hV2 hLV hgen
  have hLN1 : L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (hLV hx) (Subgroup.le_normalizer hx)
  have hLQb : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := fun x hx =>
    mem_normalizer_commutator (hLQb hx) (Subgroup.le_normalizer hx)
  have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set G) := fun x hx =>
    mem_normalizer_inf (hLU hx)
      (B2F.normalizer_le_normalizer_centralizer L (Subgroup.le_normalizer hx))
  have hUL' : blockU L ≤ L := commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
  have hZL : blockZ L ≤ L := inf_le_left.trans hUL'
  obtain ⟨-, -, -, -, -, hirr⟩ := hshort
  rcases hirr (⁅vPlus L T, L⁆ ⊔ blockZ L) le_sup_right (sup_le hVL inf_le_left)
      (fun x hx => mem_normalizer_sup (hLN1 hx) (hLZ hx)) with hW | hW
  ·
    exfalso
    apply h.not_L_le_centralizer h38 h39
    have h1 : ⁅vPlus L T, L⁆ ≤ blockZ L := le_sup_left.trans hW.le
    have h2 : ⁅⁅vPlus L T, L⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h1.trans inf_le_right
    have h3 : ⁅vPlus L T, L⁆ = ⊥ := le_bot_iff.mp (h2 ▸ hVLL)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    exact Subgroup.le_centralizer_iff.mp h3
  ·
    have hUL : ⁅blockU L, L⁆ ≤ ⁅vPlus L T, L⁆ := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      rw [← hW] at hu
      obtain ⟨a, ha, z, hz, rfl⟩ :=
        (B19Aux.mem_sup_iff_of_le_normalizer (hZL.trans hLN1)).mp hu
      have hzl : z * l = l * z := (Subgroup.mem_centralizer_iff.mp hz.2 l hl).symm
      rw [commutatorElement_mul_right_of_commute hzl]
      exact commutator_le_left_of_le_normalizer hLN1 (Subgroup.commutator_mem_commutator ha hl)
    have hUU := L246C127.commutator_le_commutator_commutator_two
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hLQb hgen
    exact hUU.trans (hUL.trans (commutator_le_left_of_le_normalizer hLV))

end Hyp331

theorem stmt3_3_26_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h25 : Stmt3_3_25) : Stmt3_3_26 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hshort : IsShort2 L := by
    rcases (h25 G T M L D h).1 with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQN : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hUV := h.blockU_le_vPlus h38 h39 hshort hTL
  have hQU := Hyp331.commutator_qL_le_blockU hshort hTL
  have hVd : ∀ d ∈ D, d ∈ M → CFSG.conjugate (vPlus L T) d = vPlus L T := by
    intro d hdD hdM
    have hZ : d ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      Hyp331.normalizer_le_normalizer_of_characteristic (L246C127.omegaOneCenter_le_self T)
        (L246C127.characteristic_omegaOneCenter T) (h.DN hdD)
    have hMp : d ∈ Subgroup.normalizer (mPlus L T : Set G) := by
      rw [← h.toSetup331.eq_normalizer h38 h39]
      exact hdM
    exact A38.map_conj_eq_iff.mpr (inv_mem (mem_normalizer_conjClosure hZ hMp))
  by_contra hcon
  have hall : ∀ d ∈ D, CFSG.conjugate (vPlus L T) d ≤ qL L T := by
    intro d hd
    by_cases hdM : d ∈ M
    · rw [hVd d hd hdM]
      exact hVQ
    · by_contra hle
      exact hcon ⟨d, hd, hdM, hle⟩
  set W := conjClosure (vPlus L T) (T ⊔ D) with hWdef
  have hWQ : W ≤ qL L T := by
    refine conjClosure_le fun x hx v hv => ?_
    obtain ⟨s, hs, d, hd, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer h.DN).mp hx
    have hdv : d * v * d⁻¹ ∈ qL L T := by
      refine hall d⁻¹ (D.inv_mem hd) ⟨v, hv, ?_⟩
      simp [MulAut.conj_apply]
    have := (Subgroup.mem_normalizer_iff.mp (hQN (Subgroup.mem_sup_right hs)) _).mp hdv
    simpa [mul_assoc] using this
  have hVne : vPlus L T ≠ ⊥ := by
    intro hb
    apply h.not_L_le_centralizer h38 h39
    rw [hb]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  have hWne : W ≠ ⊥ := fun hb => hVne (le_bot_iff.mp (hb ▸ le_conjClosure _ _))
  have hWN : T ⊔ D ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_le fun l hl w hw => ?_
    have hc : ⁅l, w⁆ ∈ W := by
      have h1 : ⁅l, w⁆ ∈ ⁅qL L T, L⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hl (hWQ hw)
      exact le_conjClosure _ _ (hUV (hQU h1))
    have e : l * w * l⁻¹ = ⁅l, w⁆ * w := by rw [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hc hw
  exact h.not_le_normalizer h38 h39 hWne (hWQ.trans hQLT)
    (sup_le hLW (le_sup_left.trans hWN)) (le_sup_right.trans hWN)

end CFSG.Quasithin.H13
