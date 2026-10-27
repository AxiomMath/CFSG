module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoMod
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem seven_eight_core_mod_eq_or_eq_of_relIndex_prime {p : ℕ} (hp : p.Prime)
    {B D Y : Subgroup G} (hBD : B ≤ D) (hDY : D ≤ Y) (hB : B.relIndex Y = p) :
    D = B ∨ D = Y := by
  have hmul := Subgroup.relIndex_mul_relIndex B D Y hBD hDY
  rw [hB] at hmul
  have hdvd : D.relIndex Y ∣ p := ⟨B.relIndex D, by rw [← hmul, Nat.mul_comm]⟩
  rcases hp.eq_one_or_self_of_dvd (D.relIndex Y) hdvd with h1 | h1
  · exact Or.inr (le_antisymm hDY (Subgroup.relIndex_eq_one.mp h1))
  · left
    have h1' : B.relIndex D = 1 := by
      have h2 : B.relIndex D * p = 1 * p := by
        calc B.relIndex D * p = B.relIndex D * D.relIndex Y := by rw [h1]
          _ = p := hmul
          _ = 1 * p := (one_mul p).symm
      exact mul_right_cancel₀ hp.ne_zero h2
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1') hBD

private theorem seven_eight_core_mod_sup_eq_of_relIndex_eq_prime {p : ℕ} (hp : p.Prime)
    {B B' Y : Subgroup G} (hBY : B ≤ Y) (hB'Y : B' ≤ Y)
    (hB : B.relIndex Y = p) (hB' : B'.relIndex Y = p) (hne : B ≠ B') :
    B ⊔ B' = Y := by
  rcases seven_eight_core_mod_eq_or_eq_of_relIndex_prime hp le_sup_left (sup_le hBY hB'Y) hB
    with h | h
  · exfalso
    have hle : B' ≤ B := h ▸ le_sup_right
    have hmul := Subgroup.relIndex_mul_relIndex B' B Y hle hBY
    rw [hB, hB'] at hmul
    have h1 : B'.relIndex B = 1 := by
      have h2 : B'.relIndex B * p = 1 * p := by rw [hmul, one_mul]
      exact mul_right_cancel₀ hp.ne_zero h2
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle)
  · exact h

private theorem seven_eight_core_mod_eq_of_le_of_relIndex_eq_prime {p : ℕ} (hp : p.Prime)
    {B C Y : Subgroup G} (hBC : B ≤ C) (hCY : C ≤ Y)
    (hB : B.relIndex Y = p) (hC : C.relIndex Y = p) : B = C := by
  have hmul := Subgroup.relIndex_mul_relIndex B C Y hBC hCY
  rw [hB, hC] at hmul
  have h1 : B.relIndex C = 1 := by
    have h2 : B.relIndex C * p = 1 * p := by rw [hmul, one_mul]
    exact mul_right_cancel₀ hp.ne_zero h2
  exact le_antisymm hBC (Subgroup.relIndex_eq_one.mp h1)

private theorem seven_eight_core_mod_conj_mem_of_commutator_le {I B Y : Subgroup G}
    (hIB : I ≤ B) (hBY : B ≤ Y) (hYY : ⁅Y, Y⁆ ≤ I) {y : G} (hy : y ∈ Y) {b : G}
    (hb : b ∈ B) : y * b * y⁻¹ ∈ B := by
  have hcomm : ⁅y, b⁆ ∈ I := hYY (Subgroup.commutator_mem_commutator hy (hBY hb))
  have hyb : y * b * y⁻¹ = ⁅y, b⁆ * b := by rw [commutatorElement_def]; group
  rw [hyb]
  exact B.mul_mem (hIB hcomm) hb

private theorem seven_eight_core_mod_le_normalizer_of_commutator_le {I B Y : Subgroup G}
    (hIB : I ≤ B) (hBY : B ≤ Y) (hYY : ⁅Y, Y⁆ ≤ I) :
    Y ≤ Subgroup.normalizer (B : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hx
    rw [← hbx]
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      seven_eight_core_mod_conj_mem_of_commutator_le hIB hBY hYY hy hb
  · intro b hb
    have hy' : y⁻¹ ∈ Y := Y.inv_mem hy
    have hmem : y⁻¹ * b * y ∈ B := by
      simpa using seven_eight_core_mod_conj_mem_of_commutator_le hIB hBY hYY hy' hb
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * b * y, hmem, ?_⟩
    change y * (y⁻¹ * b * y) * y⁻¹ = b
    group

private theorem seven_eight_core_mod_le_normalizer_centralizer {B Y : Subgroup G}
    (hYB : Y ≤ Subgroup.normalizer (B : Set G)) :
    Y ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    rw [← hcx]
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro b hb
    have hb' : y⁻¹ * b * y ∈ B := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (B : Set G)).inv_mem (hYB hy)) b).mp hb
    have h1 := hc (y⁻¹ * b * y) hb'
    change b * (y * c * y⁻¹) = (y * c * y⁻¹) * b
    calc b * (y * c * y⁻¹) = y * ((y⁻¹ * b * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * b * y)) * y⁻¹ := by rw [h1]
      _ = (y * c * y⁻¹) * b := by group
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * x * y, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro b hb
      have hb' : y * b * y⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hYB hy) b).mp hb
      have h1 := hx (y * b * y⁻¹) hb'
      calc b * (y⁻¹ * x * y) = y⁻¹ * ((y * b * y⁻¹) * x) * y := by group
        _ = y⁻¹ * (x * (y * b * y⁻¹)) * y := by rw [h1]
        _ = (y⁻¹ * x * y) * b := by group
    · change y * (y⁻¹ * x * y) * y⁻¹ = x
      group

private theorem seven_eight_core_mod_le_normalizer_commutator {A Y : Subgroup G}
    (hYA : Y ≤ Subgroup.normalizer (A : Set G)) :
    Y ≤ Subgroup.normalizer (⁅A, Y⁆ : Subgroup G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator]
  have hA : A.map (MulAut.conj y) = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYA hy)
  have hY : Y.map (MulAut.conj y) = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := Y) hy)
  rw [hA, hY]

private theorem seven_eight_core_mod_mem_normalizer_of_conj_mem {H : Subgroup G} {v : G}
    (hv2 : v * v = 1) (h : ∀ c ∈ H, v * c * v⁻¹ ∈ H) :
    v ∈ Subgroup.normalizer (H : Set G) := by
  have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨h c, fun hc => ?_⟩
  have := h (v * c * v⁻¹) hc
  rwa [show v * (v * c * v⁻¹) * v⁻¹ = c from by
    calc v * (v * c * v⁻¹) * v⁻¹ = (v * v) * c * (v⁻¹ * v⁻¹) := by group
      _ = (v * v) * c * (v * v) := by rw [hv_inv]
      _ = c := by rw [hv2]; group] at this

private theorem seven_eight_core_mod_mem_centralizer_sup {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.centralizer (H : Set G))
    (hK : x ∈ Subgroup.centralizer (K : Set G)) :
    x ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hH' : Subgroup.zpowers x ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.zpowers_le.mpr hH
  have hK' : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hK
  have hsup : (H ⊔ K : Subgroup G) ≤
      Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp hH') (Subgroup.le_centralizer_iff.mp hK')
  exact Subgroup.zpowers_le.mp (Subgroup.le_centralizer_iff.mpr hsup)

private theorem seven_eight_core_mod_inf_centralizer_sup_eq {I B : Subgroup G}
    (hIcomm : IsMulCommutative I) :
    I ⊓ Subgroup.centralizer ((B ⊔ I : Subgroup G) : Set G)
      = I ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxI, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨hxI, Subgroup.centralizer_le (fun b hb => Subgroup.mem_sup_left hb) hxC⟩
  · intro x hx
    obtain ⟨hxI, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxI' : x ∈ Subgroup.centralizer (I : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      letI := hIcomm
      exact congrArg Subtype.val (mul_comm' (⟨i, hi⟩ : I) (⟨x, hxI⟩ : I))
    exact Subgroup.mem_inf.mpr
      ⟨hxI, seven_eight_core_mod_mem_centralizer_sup hxB hxI'⟩

private theorem seven_eight_core_mod_map_centralizer_eq {H : Subgroup G} (e : G ≃* G) :
    (Subgroup.centralizer (H : Set G)).map e.toMonoidHom
      = Subgroup.centralizer ((H.map e.toMonoidHom) : Set G) := by
  apply le_antisymm
  · have h := Subgroup.map_centralizer_le_centralizer_image (H : Set G) e.toMonoidHom
    simpa [Subgroup.coe_map] using h
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro h hh
      have hmem : e h ∈ H.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
      have h1 := hx (e h) hmem
      apply e.injective
      rw [map_mul, map_mul]
      simpa using h1
    · show e.toMonoidHom (e.symm x) = x
      simp

private theorem seven_eight_core_mod_commutator_inf_centralizer_eq_bot
    {I Y A : Subgroup G} (hI : IsElemAbelian 2 I) (hIY : I ≤ Y)
    (hYI : Y ≤ Subgroup.normalizer (I : Set G)) (hodd : Odd (I.relIndex Y))
    (hAI : A ≤ I) :
    ⁅A, Y⁆ ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  have hleI : ⁅A, Y⁆ ≤ I :=
    (Subgroup.commutator_mono hAI le_rfl).trans
      (CFSG.Quasithin.E1.commutator_le_of_le_normalizer hYI)
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxI : x ∈ I := hleI hxA
  have hxJ : x ∈ ⁅I, Y⁆ := (Subgroup.commutator_mono hAI le_rfl) hxA
  have hmem : x ∈ ⁅I, Y⁆ ⊓ (I ⊓ Subgroup.centralizer (Y : Set G)) :=
    Subgroup.mem_inf.mpr ⟨hxJ, Subgroup.mem_inf.mpr ⟨hxI, hxC⟩⟩
  rw [commutator_inf_centralizer_eq_bot_of_odd_relIndex hI hIY hYI hodd] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem seven_eight_core_mod_relIndex_sup_eq_prime {p : ℕ}
    {I S B₀ Y : Subgroup G} (hSY : S ≤ Y) (hIY : I ≤ Y)
    (hYI : Y ≤ Subgroup.normalizer (I : Set G))
    (hIS : I ⊓ S = ⊥) (hIsup : I ⊔ S = Y)
    (hB0S : B₀ ≤ S) (hB0card : Nat.card S = p * Nat.card B₀) :
    (B₀ ⊔ I).relIndex Y = p := by
  have hB0Y : B₀ ≤ Y := hB0S.trans hSY
  have hB0I : B₀ ⊓ I = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    obtain ⟨hxB0, hxI⟩ := Subgroup.mem_inf.mp hx
    have hxIS : x ∈ I ⊓ S := Subgroup.mem_inf.mpr ⟨hxI, hB0S hxB0⟩
    rw [hIS] at hxIS
    exact Subgroup.mem_bot.mp hxIS
  have hBY : B₀ ⊔ I ≤ Y := sup_le hB0Y hIY
  have hnorm : (I.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIY).mpr hYI
  haveI : (I.subgroupOf Y).Normal := hnorm
  have hIS_bot : I.subgroupOf S = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot]
    exact disjoint_iff.mpr hIS
  have hIrelS : I.relIndex S = Nat.card S := by
    change (I.subgroupOf S).index = Nat.card S
    rw [hIS_bot, Subgroup.index_bot]
  have hIrelY : I.relIndex Y = Nat.card S := by
    change (I.subgroupOf Y).index = Nat.card S
    have h1 := Subgroup.relIndex_sup_left (K := I.subgroupOf Y) (H := S.subgroupOf Y)
    rw [← Subgroup.subgroupOf_sup hIY hSY, hIsup, Subgroup.subgroupOf_self] at h1
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hSY, hIrelS] at h1
    exact h1
  have hB0I_bot : I.subgroupOf B₀ = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot]
    exact disjoint_iff.mpr (by rw [inf_comm]; exact hB0I)
  have hIrelB0 : I.relIndex B₀ = Nat.card B₀ := by
    change (I.subgroupOf B₀).index = Nat.card B₀
    rw [hB0I_bot, Subgroup.index_bot]
  have hIrelB : I.relIndex (B₀ ⊔ I) = Nat.card B₀ := by
    have h1 := Subgroup.relIndex_sup_right (K := I.subgroupOf Y) (H := B₀.subgroupOf Y)
    rw [← Subgroup.subgroupOf_sup hB0Y hIY, Subgroup.relIndex_subgroupOf hBY,
      Subgroup.relIndex_subgroupOf hB0Y, hIrelB0] at h1
    exact h1
  have hmul := Subgroup.relIndex_mul_relIndex I (B₀ ⊔ I) Y le_sup_right hBY
  rw [hIrelB, hIrelY, hB0card] at hmul
  have hpos : Nat.card B₀ ≠ 0 := by
    haveI : Nonempty B₀ := ⟨1⟩
    exact Nat.card_pos.ne'
  exact mul_left_cancel₀ hpos (hmul.trans (Nat.mul_comm p (Nat.card B₀)))

theorem exists_weight {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I Y : Subgroup G}
    (hI : IsElemAbelian 2 I) (hIY : I ≤ Y) (hYI : Y ≤ Subgroup.normalizer (I : Set G))
    (hodd : Odd (I.relIndex Y)) (hYab : ⁅Y, Y⁆ ≤ I) (hexp : ∀ y ∈ Y, y ^ p ∈ I)
    (hYne : I ≠ Y) (hfaith : Y ⊓ Subgroup.centralizer (I : Set G) ≤ I) :
    ∃ B : Subgroup G, I ≤ B ∧ B ≤ Y ∧ B.relIndex Y = p ∧
      ⁅I ⊓ Subgroup.centralizer (B : Set G), Y⁆ ≠ ⊥ := by
  have hIpg := hI.isPGroup
  obtain ⟨k, hk⟩ := hIpg.exists_card_eq
  have hcop : Nat.Coprime (Nat.card I) (I.relIndex Y) := by
    rw [hk]
    rcases k.eq_zero_or_pos with hk0 | hkpos
    · subst hk0; simp
    · rw [Nat.coprime_pow_left_iff hkpos]
      exact hodd.coprime_two_left
  obtain ⟨S, hSY, hIS, hIsup, _hcopSI, _hcommIY⟩ :=
    s762M_exists_complement hI hIY hYI hodd
  have hSSle : ⁅S, S⁆ ≤ I ⊓ S := by
    refine le_inf ?_ ?_
    · exact (Subgroup.commutator_mono hSY hSY).trans hYab
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hSSbot : ⁅S, S⁆ = ⊥ := by
    rw [hIS] at hSSle
    exact le_bot_iff.mp hSSle
  have hScomm : IsMulCommutative S := IsMulCommutative.of_comm fun x y => by
    have hmem : ⁅(x : G), (y : G)⁆ ∈ ⁅S, S⁆ :=
      Subgroup.commutator_mem_commutator x.2 y.2
    rw [hSSbot] at hmem
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))
  have hSexp : ∀ s ∈ S, s ^ p = 1 := by
    intro s hs
    have hsI : s ^ p ∈ I := hexp s (hSY hs)
    have hsS : s ^ p ∈ S := S.pow_mem hs p
    have hmem : s ^ p ∈ I ⊓ S := Subgroup.mem_inf.mpr ⟨hsI, hsS⟩
    rw [hIS] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hSEA : IsElemAbelian p S := ⟨hScomm, hSexp⟩
  have hSne : S ≠ ⊥ := by
    intro hSbot
    apply hYne
    rw [← hIsup, hSbot, sup_bot_eq]
  have hpS : p ≤ Nat.card S := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨j, hj⟩ := hSEA.isPGroup.exists_card_eq
    have hjpos : 0 < j := by
      by_contra hj0
      have hj0' : j = 0 := Nat.eq_zero_of_not_pos hj0
      rw [hj0', pow_zero] at hj
      exact hSne (Subgroup.eq_bot_of_card_eq S hj)
    rw [hj]
    exact le_self_pow hp.one_lt.le hjpos.ne'
  have hpI : Nat.Coprime p (Nat.card I) := by
    rw [hk]
    rcases k.eq_zero_or_pos with hk0 | hkpos
    · subst hk0; simp
    · rw [Nat.coprime_pow_right_iff hkpos]
      exact (hp.odd_of_ne_two hp2).coprime_two_right
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
    (p := p) hp (A := S) (X := I) hSEA hpS (hSY.trans hYI) hpI
  by_contra hgoal
  have hcon : ∀ B : Subgroup G, I ≤ B → B ≤ Y → B.relIndex Y = p →
      ⁅I ⊓ Subgroup.centralizer (B : Set G), Y⁆ = ⊥ := by
    intro B hIB hBY hB
    by_contra hne
    exact hgoal ⟨B, hIB, hBY, hB, hne⟩
  have hcon' : ∀ B₀ ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p S,
      ⁅I ⊓ Subgroup.centralizer (B₀ : Set G), Y⁆ = ⊥ := by
    intro B₀ hB₀
    by_contra hne
    have hB0Y : B₀ ≤ Y := hB₀.1.trans hSY
    have hBrel : (B₀ ⊔ I).relIndex Y = p :=
      seven_eight_core_mod_relIndex_sup_eq_prime hSY hIY hYI hIS hIsup hB₀.1 hB₀.2
    have hcent : I ⊓ Subgroup.centralizer ((B₀ ⊔ I : Subgroup G) : Set G)
        = I ⊓ Subgroup.centralizer (B₀ : Set G) :=
      seven_eight_core_mod_inf_centralizer_sup_eq hI.1
    have heq : ⁅I ⊓ Subgroup.centralizer ((B₀ ⊔ I : Subgroup G) : Set G), Y⁆ = ⊥ :=
      hcon (B₀ ⊔ I) le_sup_right (sup_le hB0Y hIY) hBrel
    rw [hcent] at heq
    exact hne heq
  have hle : I ≤ Subgroup.centralizer (Y : Set G) := by
    rw [← hgen]
    refine iSup_le fun B₀ => iSup_le fun hB₀ => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon' B₀ hB₀)
  have hYleI : Y ≤ I := by
    have hYC : Y ≤ Subgroup.centralizer (I : Set G) := Subgroup.le_centralizer_iff.mpr hle
    calc Y ≤ Y ⊓ Subgroup.centralizer (I : Set G) := le_inf le_rfl hYC
      _ ≤ I := hfaith
  exact hYne (le_antisymm hIY hYleI)

theorem eq_or_le_of_commutator_inf_centralizer_ne_bot {p : ℕ} (hp : p.Prime)
    {I Y B C M : Subgroup G} {v : G}
    (hI : IsElemAbelian 2 I) (hIY : I ≤ Y) (hYI : Y ≤ Subgroup.normalizer (I : Set G))
    (hodd : Odd (I.relIndex Y)) (hYab : ⁅Y, Y⁆ ≤ I)
    (hIB : I ≤ B) (hBY : B ≤ Y) (hB : B.relIndex Y = p)
    (hIC : I ≤ C) (hCY : C ≤ Y) (hC : C.relIndex Y = p)
    (hIM : I ≤ M) (hMY : M ≤ Y) (hM : I.relIndex M = p)
    (hv2 : v * v = 1) (hvY : v ∈ Subgroup.normalizer (Y : Set G))
    (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hYv : ∀ y ∈ Y, ⁅y, v⁆ ∈ M) (hCv : ∀ c ∈ C, ⁅c, v⁆ ∈ I)
    (hCfix : ∀ y ∈ Y, ⁅y, v⁆ ∈ I → y ∈ C)
    (hcent : ∀ c ∈ C, ∀ w ∈ I, c * ⁅w, v⁆ = ⁅w, v⁆ * c)
    (hZ : ⁅I ⊓ Subgroup.centralizer (B : Set G), Y⁆ ≠ ⊥) :
    B = C ∨ M ≤ B := by
  set A : Subgroup G := I ⊓ Subgroup.centralizer (B : Set G) with hAdef
  set Z : Subgroup G := ⁅A, Y⁆ with hZdef
  have hZne : Z ≠ ⊥ := by rw [hZdef, hAdef]; exact hZ
  have hYleNB : Y ≤ Subgroup.normalizer (B : Set G) :=
    seven_eight_core_mod_le_normalizer_of_commutator_le hIB hBY hYab
  have hYleNCB : Y ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
    seven_eight_core_mod_le_normalizer_centralizer hYleNB
  have hYleNA : Y ≤ Subgroup.normalizer (A : Set G) := by
    rw [hAdef]
    exact (le_inf hYI hYleNCB).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := I)
        (K := Subgroup.centralizer (B : Set G)))
  have hZleA : Z ≤ A := by
    rw [hZdef]
    exact CFSG.Quasithin.E1.commutator_le_of_le_normalizer hYleNA
  have hZleI : Z ≤ I := hZleA.trans inf_le_left
  have hZleCB : Z ≤ Subgroup.centralizer (B : Set G) := hZleA.trans inf_le_right
  have hYleNZ : Y ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef]
    exact seven_eight_core_mod_le_normalizer_commutator hYleNA
  have hZbot : Z ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
    rw [hZdef]
    exact seven_eight_core_mod_commutator_inf_centralizer_eq_bot hI hIY hYI hodd inf_le_left
  have hvC : v ∈ Subgroup.normalizer (C : Set G) := by
    refine seven_eight_core_mod_mem_normalizer_of_conj_mem hv2 ?_
    intro c hc
    have hcv : ⁅v, c⁆ ∈ I := by
      have h' : ⁅c, v⁆⁻¹ ∈ I := I.inv_mem (hCv c hc)
      rwa [(commutatorElement_inv (g₁ := c) (g₂ := v)).symm]
    have heq : v * c * v⁻¹ = ⁅v, c⁆ * c := by rw [commutatorElement_def]; group
    rw [heq]
    exact C.mul_mem (hIC hcv) hc
  by_cases hBinv : B.map (MulAut.conj v).toMonoidHom = B
  · by_cases hMB : M ≤ B
    · exact Or.inr hMB
    · left
      have hBinfM : B ⊓ M = I := by
        rcases seven_eight_core_mod_eq_or_eq_of_relIndex_prime hp
            (le_inf hIB hIM) inf_le_right hM with h | h
        · exact h
        · exact absurd (h ▸ inf_le_left) hMB
      have hvB : v ∈ Subgroup.normalizer (B : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hBinv
      have hBleC : B ≤ C := by
        intro b hb
        have hbvB : ⁅b, v⁆ ∈ B := by
          rw [commutatorElement_def]
          have hvb : v * b⁻¹ * v⁻¹ ∈ B :=
            (Subgroup.mem_normalizer_iff.mp hvB b⁻¹).mp (B.inv_mem hb)
          have heq : b * v * b⁻¹ * v⁻¹ = b * (v * b⁻¹ * v⁻¹) := by group
          rw [heq]
          exact B.mul_mem hb hvb
        have hbvM : ⁅b, v⁆ ∈ M := hYv b (hBY hb)
        have hbvI : ⁅b, v⁆ ∈ I := by
          rw [← hBinfM]
          exact Subgroup.mem_inf.mpr ⟨hbvB, hbvM⟩
        exact hCfix b (hBY hb) hbvI
      exact seven_eight_core_mod_eq_of_le_of_relIndex_eq_prime hp hBleC hCY hB hC
  · exfalso
    set B' : Subgroup G := B.map (MulAut.conj v).toMonoidHom with hB'def
    have hB'ne : B' ≠ B := by rw [hB'def]; exact hBinv
    have hI_le_B' : I ≤ B' := by
      rw [hB'def]
      calc I = I.map (MulAut.conj v).toMonoidHom :=
            (Subgroup.mem_normalizer_iff_map_conj_eq.mp hvI).symm
        _ ≤ B.map (MulAut.conj v).toMonoidHom := Subgroup.map_mono hIB
    have hYmap : Y.map (MulAut.conj v).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hvY
    have hB'Y : B' ≤ Y := by
      rw [hB'def, ← hYmap]
      exact Subgroup.map_mono hBY
    have hB' : B'.relIndex Y = p := by
      rw [hB'def, ← hYmap,
        Subgroup.relIndex_map_map_of_injective B Y (MulAut.conj v).injective, hB]
    set Z' : Subgroup G := Z.map (MulAut.conj v).toMonoidHom with hZ'def
    have hZ'leCB' : Z' ≤ Subgroup.centralizer (B' : Set G) := by
      intro x hx
      rw [hZ'def] at hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      rw [← hzx, hB'def]
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨b₀, hb₀, hbz⟩ := Subgroup.mem_map.mp hb
      rw [← hbz]
      have hzb : b₀ * z = z * b₀ :=
        (Subgroup.mem_centralizer_iff.mp (hZleCB hz)) b₀ hb₀
      change (v * b₀ * v⁻¹) * (v * z * v⁻¹) = (v * z * v⁻¹) * (v * b₀ * v⁻¹)
      calc (v * b₀ * v⁻¹) * (v * z * v⁻¹) = v * (b₀ * z) * v⁻¹ := by group
        _ = v * (z * b₀) * v⁻¹ := by rw [hzb]
        _ = (v * z * v⁻¹) * (v * b₀ * v⁻¹) := by group
    have hBC : B ≠ C := by
      intro h
      apply hB'ne
      calc B' = B.map (MulAut.conj v).toMonoidHom := hB'def
        _ = C.map (MulAut.conj v).toMonoidHom := by rw [h]
        _ = C := Subgroup.mem_normalizer_iff_map_conj_eq.mp hvC
        _ = B := h.symm
    have hBsupB' : B ⊔ B' = Y :=
      seven_eight_core_mod_sup_eq_of_relIndex_eq_prime hp hBY hB'Y hB hB' (Ne.symm hB'ne)
    have hBsupC : B ⊔ C = Y :=
      seven_eight_core_mod_sup_eq_of_relIndex_eq_prime hp hBY hCY hB hC hBC
    have hZZ' : Z ⊓ Z' = ⊥ := by
      refine le_bot_iff.mp ?_
      intro x hx
      obtain ⟨hxZ, hxZ'⟩ := Subgroup.mem_inf.mp hx
      have hxCBB' : x ∈ Subgroup.centralizer ((B ⊔ B' : Subgroup G) : Set G) :=
        seven_eight_core_mod_mem_centralizer_sup (hZleCB hxZ) (hZ'leCB' hxZ')
      rw [hBsupB'] at hxCBB'
      have hmem : x ∈ Z ⊓ Subgroup.centralizer (Y : Set G) :=
        Subgroup.mem_inf.mpr ⟨hxZ, hxCBB'⟩
      rw [hZbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hZCC : Z ⊓ Subgroup.centralizer (C : Set G) = ⊥ := by
      refine le_bot_iff.mp ?_
      intro x hx
      obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxCBC : x ∈ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) :=
        seven_eight_core_mod_mem_centralizer_sup (hZleCB hxZ) hxC
      rw [hBsupC] at hxCBC
      have hmem : x ∈ Z ⊓ Subgroup.centralizer (Y : Set G) :=
        Subgroup.mem_inf.mpr ⟨hxZ, hxCBC⟩
      rw [hZbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hZleCC : Z ≤ Subgroup.centralizer (C : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hzv : ⁅z, v⁆ = z * (v * z * v⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      have hcomm := hcent c hc z (hZleI hz)
      have hcu : c * (z * (v * z * v⁻¹)⁻¹) * c⁻¹ = z * (v * z * v⁻¹)⁻¹ := by
        rw [← hzv, hcomm]
        group
      have hαZ : c * z * c⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hYleNZ (hCY hc)) z).mp hz
      have hβZ' : c * (v * z * v⁻¹) * c⁻¹ ∈ Z' := by
        have hvc : v⁻¹ * c * v ∈ Y := by
          have hvin : v⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
            (Subgroup.normalizer (Y : Set G)).inv_mem hvY
          simpa using (Subgroup.mem_normalizer_iff.mp hvin c).mp (hCY hc)
        have hwzZ : (v⁻¹ * c * v) * z * (v⁻¹ * c * v)⁻¹ ∈ Z :=
          (Subgroup.mem_normalizer_iff.mp (hYleNZ hvc) z).mp hz
        refine Subgroup.mem_map.mpr
          ⟨(v⁻¹ * c * v) * z * (v⁻¹ * c * v)⁻¹, hwzZ, ?_⟩
        change v * ((v⁻¹ * c * v) * z * (v⁻¹ * c * v)⁻¹) * v⁻¹
          = c * (v * z * v⁻¹) * c⁻¹
        group
      have hβinvZ' : (c * (v * z * v⁻¹) * c⁻¹)⁻¹ ∈ Z' := Z'.inv_mem hβZ'
      have hEq : z⁻¹ * (c * z * c⁻¹)
          = (v * z * v⁻¹)⁻¹ * (c * (v * z * v⁻¹) * c⁻¹) := by
        have h : (c * z * c⁻¹) * (c * (v * z * v⁻¹) * c⁻¹)⁻¹
            = z * (v * z * v⁻¹)⁻¹ := by
          calc (c * z * c⁻¹) * (c * (v * z * v⁻¹) * c⁻¹)⁻¹
              = c * (z * (v * z * v⁻¹)⁻¹) * c⁻¹ := by group
            _ = z * (v * z * v⁻¹)⁻¹ := hcu
        calc z⁻¹ * (c * z * c⁻¹)
            = z⁻¹ * ((c * z * c⁻¹) * (c * (v * z * v⁻¹) * c⁻¹)⁻¹)
                * (c * (v * z * v⁻¹) * c⁻¹) := by group
          _ = z⁻¹ * (z * (v * z * v⁻¹)⁻¹) * (c * (v * z * v⁻¹) * c⁻¹) := by
                rw [h]
          _ = (v * z * v⁻¹)⁻¹ * (c * (v * z * v⁻¹) * c⁻¹) := by group
      have hmem : z⁻¹ * (c * z * c⁻¹) ∈ Z ⊓ Z' := by
        refine Subgroup.mem_inf.mpr ⟨Z.mul_mem (Z.inv_mem hz) hαZ, ?_⟩
        rw [hEq]
        exact Z'.mul_mem
          (Z'.inv_mem (Subgroup.mem_map.mpr ⟨z, hz, MulAut.conj_apply v z⟩)) hβZ'
      rw [hZZ'] at hmem
      have h1 : z⁻¹ * (c * z * c⁻¹) = 1 := Subgroup.mem_bot.mp hmem
      have hα : c * z * c⁻¹ = z := by
        have h2 := congrArg (fun t => z * t) h1
        simpa [mul_assoc] using h2
      calc c * z = (c * z * c⁻¹) * c := by group
        _ = z * c := by rw [hα]
    have hZeq : Z = ⊥ := by
      refine le_bot_iff.mp ?_
      intro z hz
      have hzC : z ∈ Subgroup.centralizer (C : Set G) := hZleCC hz
      have hmem : z ∈ Z ⊓ Subgroup.centralizer (C : Set G) :=
        Subgroup.mem_inf.mpr ⟨hz, hzC⟩
      rw [hZCC] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact hZne hZeq

theorem exists_map_conj_eq_of_weights {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I Y : Subgroup G}
    (hI : IsElemAbelian 2 I) (hIY : I ≤ Y) (hYI : Y ≤ Subgroup.normalizer (I : Set G))
    (hodd : Odd (I.relIndex Y)) (hYab : ⁅Y, Y⁆ ≤ I) (hexp : ∀ y ∈ Y, y ^ p ∈ I)
    (hYne : I ≠ Y) (hfaith : Y ⊓ Subgroup.centralizer (I : Set G) ≤ I)
    {ι : Type*} (v : ι → G) (M C : ι → Subgroup G)
    (hIC : ∀ i, I ≤ C i) (hCY : ∀ i, C i ≤ Y) (hC : ∀ i, (C i).relIndex Y = p)
    (hIM : ∀ i, I ≤ M i) (hMY : ∀ i, M i ≤ Y) (hM : ∀ i, I.relIndex (M i) = p)
    (hv2 : ∀ i, v i * v i = 1) (hvY : ∀ i, v i ∈ Subgroup.normalizer (Y : Set G))
    (hvI : ∀ i, v i ∈ Subgroup.normalizer (I : Set G))
    (hYv : ∀ i, ∀ y ∈ Y, ⁅y, v i⁆ ∈ M i) (hCv : ∀ i, ∀ c ∈ C i, ⁅c, v i⁆ ∈ I)
    (hCfix : ∀ i, ∀ y ∈ Y, ⁅y, v i⁆ ∈ I → y ∈ C i)
    (hcent : ∀ i, ∀ c ∈ C i, ∀ w ∈ I, c * ⁅w, v i⁆ = ⁅w, v i⁆ * c)
    (hgen : (⨆ i, M i) = Y) {g : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hgI : g ∈ Subgroup.normalizer (I : Set G)) :
    ∃ k l : ι, (C k).map (MulAut.conj g).toMonoidHom = C l := by
  have hweight_eq : ∀ B : Subgroup G, I ≤ B → B ≤ Y → B.relIndex Y = p →
      ⁅I ⊓ Subgroup.centralizer (B : Set G), Y⁆ ≠ ⊥ → ∃ i, B = C i := by
    intro B hIB hBY hB hZ
    by_contra hcon
    push Not at hcon
    have hMB : ∀ i, M i ≤ B := by
      intro i
      rcases eq_or_le_of_commutator_inf_centralizer_ne_bot hp hI hIY hYI hodd hYab
        hIB hBY hB (hIC i) (hCY i) (hC i) (hIM i) (hMY i) (hM i)
        (hv2 i) (hvY i) (hvI i) (hYv i) (hCv i) (hCfix i) (hcent i) hZ with h | h
      · exact absurd h (hcon i)
      · exact h
    have hYleB : Y ≤ B := by
      rw [← hgen]
      exact iSup_le hMB
    exact hp.one_lt.ne' (by rw [← hB, le_antisymm hYleB hBY, Subgroup.relIndex_self])
  obtain ⟨B0, hIB0, hB0Y, hB0, hZ0⟩ :=
    exists_weight hp hp2 hI hIY hYI hodd hYab hexp hYne hfaith
  obtain ⟨k, hk⟩ := hweight_eq B0 hIB0 hB0Y hB0 hZ0
  set B1 : Subgroup G := B0.map (MulAut.conj g).toMonoidHom with hB1def
  have hYmap : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgY
  have hImap : I.map (MulAut.conj g).toMonoidHom = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgI
  have hB1I : I ≤ B1 := by
    rw [hB1def]
    calc I = I.map (MulAut.conj g).toMonoidHom := hImap.symm
      _ ≤ B0.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hIB0
  have hB1Y : B1 ≤ Y := by
    rw [hB1def, ← hYmap]
    exact Subgroup.map_mono hB0Y
  have hB1 : B1.relIndex Y = p := by
    rw [hB1def, ← hYmap,
      Subgroup.relIndex_map_map_of_injective B0 Y (MulAut.conj g).injective, hB0]
  have hA1map : (I ⊓ Subgroup.centralizer (B0 : Set G)).map (MulAut.conj g).toMonoidHom
      = I ⊓ Subgroup.centralizer (B1 : Set G) := by
    rw [Subgroup.map_inf_eq I (Subgroup.centralizer (B0 : Set G)) _ (MulAut.conj g).injective,
      hImap, seven_eight_core_mod_map_centralizer_eq (H := B0) (MulAut.conj g), ← hB1def]
  have hZ1 : ⁅I ⊓ Subgroup.centralizer (B1 : Set G), Y⁆ ≠ ⊥ := by
    have hZmap : (⁅I ⊓ Subgroup.centralizer (B0 : Set G), Y⁆).map
        (MulAut.conj g).toMonoidHom
        = ⁅I ⊓ Subgroup.centralizer (B1 : Set G), Y⁆ := by
      rw [Subgroup.map_commutator, hA1map, hYmap]
    rw [← hZmap]
    intro hbot
    exact hZ0 ((Subgroup.map_eq_bot_iff_of_injective
      (⁅I ⊓ Subgroup.centralizer (B0 : Set G), Y⁆) (MulAut.conj g).injective).mp hbot)
  obtain ⟨l, hl⟩ := hweight_eq B1 hB1I hB1Y hB1 hZ1
  exact ⟨k, l, by rw [← hk, ← hB1def, hl]⟩

end CFSG.LocalAnalysis.WeakClosure81
