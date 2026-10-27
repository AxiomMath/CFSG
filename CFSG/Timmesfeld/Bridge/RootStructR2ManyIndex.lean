module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManyCore

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootMany

variable {G : Type} [Group G] {D : Set G} [Finite G] (C : ThinGateCounter G D) {q n : ℕ}
  (K : ThinGateCount G D q n 2) {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
  (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
include C K ha hd had hadD hdT

theorem le_card_nCore_inf_centralizer :
    q * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) ≤ Nat.card (nCore D a) := by
  have hD := C.hyp.root
  have hLS := lineSetting_of_counter C
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨L₁, hL₁, hL₁T⟩ := hLS.exists_ne_mem_rootLines ha hT
  obtain ⟨c, hc, hac, hacD, hcT, rfl⟩ := hL₁
  have hcL : c ∉ rootGroup D a ⊔ rootGroup D d := fun h' =>
    hL₁T (hLS.sup_rootGroup_eq_of_mem_sup ha hc hd hac hcT had hadD hdT h')
  have hcd : ¬ Commute c d := fun h' =>
    hcL (hLS.lineCentralizerEq a ha d hd had hadD hdT (hLS.lineTI ha hd had hadD hdT) c hc
      hac.symm h')
  have hAc : rootGroup D c ≤ nCore D a := le_sup_right.trans (hLS.sup_rootGroup_le_nCore ha hc hac)
  have hB : ∀ b ∈ rootGroup D c, Commute b d → b = 1 := by
    intro b hb hbd
    by_contra hb1
    have hbT := mem_rootSet_of_mem_rootGroup_of_ne_one hD C.closure hc hb hb1
    exact hcd ((hbT.2 d hd).1 hbd)
  have h := card_mul_card_inf_le ha hd (nCore_le_transv C ha hd had) hAc hB
  rwa [K.card_rootGroup c hc] at h

theorem le_card_inf_centralizer :
    q ^ n * Nat.card ↥(nCore D a ⊓ nCore D d) ≤
      Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) := by
  classical
  have hD := C.hyp.root
  have hLS := lineSetting_of_counter C
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haTd : a ∉ rootSet D d := fun h' => hdT (mem_rootSet_comm hd h')
  have hT : rootGroup D d ⊔ rootGroup D a ∈ rootLines D d :=
    ⟨a, ha, had.symm, hdaD, haTd, rfl⟩
  set Q := nCore D a ⊓ Subgroup.centralizer {d} with hQ
  have hQN : Q ≤ Subgroup.normalizer (rootGroup D d : Set G) :=
    inf_le_right.trans (centralizer_le_normalizer_rootGroup C.hyp.isClass d)
  let _ : MulAction Q (rootLines D d) :=
    MulAction.compHom _ ((hLS.lineAction hd).comp (Subgroup.inclusion hQN))
  have hsmul : ∀ (s : Q) (L : rootLines D d),
      ((s • L : rootLines D d) : Subgroup G) = L.1.map (MulAut.conj (s : G)).toMonoidHom :=
    fun s L => hLS.lineAction_apply hd _ L
  obtain ⟨L₁, hL₁, hL₁T⟩ := hLS.exists_ne_mem_rootLines hd hT
  have horbit : ({⟨_, hT⟩}ᶜ : Set (rootLines D d)) ⊆
      MulAction.orbit Q (⟨L₁, hL₁⟩ : rootLines D d) := by
    intro L hL
    have hLT : (L : Subgroup G) ≠ rootGroup D d ⊔ rootGroup D a := fun h => hL (Subtype.ext h)
    obtain ⟨b, hb, hdb, hdbD, hbT, hL₁eq⟩ := hL₁
    obtain ⟨c, hc, hdc, hdcD, hcT, hLeq⟩ := L.2
    have hbL : b ∉ rootGroup D d ⊔ rootGroup D a := by
      intro h'
      have := hLS.sup_rootGroup_eq_of_mem_sup hd hb ha hdb hbT had.symm hdaD haTd h'
      exact hL₁T (hL₁eq.trans this)
    have hcL : c ∉ rootGroup D d ⊔ rootGroup D a := by
      intro h'
      have := hLS.sup_rootGroup_eq_of_mem_sup hd hc ha hdc hcT had.symm hdaD haTd h'
      exact hLT (hLeq.trans this)
    obtain ⟨⟨k, hk, hkL⟩, -⟩ := rootLinesRegularStep G D hLS d hd a ha had.symm hdaD haTd b hb hdb
      hdbD hbL c hc hdc hdcD hcL
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    rw [hsmul]
    show L₁.map (MulAut.conj k).toMonoidHom = L
    rw [hL₁eq, hkL, hLeq]
  have hMQ : nCore D a ⊓ nCore D d ≤ Q := fun g hg =>
    ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_nCore hg.2).eq⟩
  have hstab : (nCore D a ⊓ nCore D d).subgroupOf Q ≤
      MulAction.stabilizer Q (⟨L₁, hL₁⟩ : rootLines D d) := by
    intro m hm
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [hsmul]
    exact hLS.map_conj_eq_of_mem_closure hd
      (nCore_le_closure_commute D d (Subgroup.mem_subgroupOf.1 hm).2) hL₁
  have h1 : Nat.card ↥(nCore D a ⊓ nCore D d) ≤
      Nat.card (MulAction.stabilizer Q (⟨L₁, hL₁⟩ : rootLines D d)) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMQ).toEquiv]
    exact Subgroup.card_le_of_le hstab
  have h2 : q ^ n ≤ (MulAction.orbit Q (⟨L₁, hL₁⟩ : rootLines D d)).ncard := by
    have hc : ({⟨_, hT⟩}ᶜ : Set (rootLines D d)).ncard = q ^ n := by
      rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_coe_set_eq, K.ncard_rootLines d hd]
      omega
    rw [← hc]
    exact Set.ncard_le_ncard horbit
  calc q ^ n * Nat.card ↥(nCore D a ⊓ nCore D d)
      ≤ (MulAction.orbit Q (⟨L₁, hL₁⟩ : rootLines D d)).ncard *
          Nat.card (MulAction.stabilizer Q (⟨L₁, hL₁⟩ : rootLines D d)) := Nat.mul_le_mul h2 h1
    _ = Nat.card Q := by
      rw [mul_comm, ← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem le_card_nCore :
    q ^ (n + 1) * Nat.card ↥(nCore D a ⊓ nCore D d) ≤ Nat.card (nCore D a) := by
  have h1 := le_card_nCore_inf_centralizer C K ha hd had hadD hdT
  have h2 := le_card_inf_centralizer C K ha hd had hadD hdT
  calc q ^ (n + 1) * Nat.card ↥(nCore D a ⊓ nCore D d)
      = q * (q ^ n * Nat.card ↥(nCore D a ⊓ nCore D d)) := by ring
    _ ≤ q * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) := Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card (nCore D a) := h1

end RootMany

end CFSG.Timmesfeld.Bridge
