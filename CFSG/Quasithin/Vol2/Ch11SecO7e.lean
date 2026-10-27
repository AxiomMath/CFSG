module

public import CFSG.Quasithin.Vol2.Ch11SecO7d
public import CFSG.Quasithin.Vol2.Ch11SecAKE12
public import CFSG.Quasithin.Vol2.Ch11SecEFacts6
public import CFSG.Quasithin.Vol2.Ch11SecO7c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint


theorem a312L2pFact_holds : A312L2pFact := by
  intro Y _ _ B L p hp hp11 hB h
  obtain ⟨e⟩ := hB
  have : Fact p.Prime := ⟨hp⟩
  have hs : IsSimpleGroup ↥B := C10KH.isSimpleGroup_of_psl2 (by omega) e
  have hc : Nat.card ↥B = p * (p ^ 2 - 1) / 2 := C10KH.card_of_psl2 (by omega) e
  have hp2 : p ≠ 2 := by omega
  have hev : 2 ∣ p * (p ^ 2 - 1) :=
    Dvd.dvd.mul_left (even_iff_two_dvd.mp
      (Nat.Odd.sub_odd ((hp.odd_of_ne_two hp2).pow) odd_one)) p
  have hc2 : Nat.card ↥B * 2 = p * (p ^ 2 - 1) := by rw [hc]; exact Nat.div_mul_cancel hev
  have hge : 11 * (11 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := C10KH.cube_sub_le (by norm_num) hp11
  have hnp : ¬ (Nat.card ↥B).Prime := by rw [hc]; exact (SecA.C10KH.three_dvd_psl2 hp hp11).2
  have h3 : 3 ∣ Nat.card ↥B := by rw [hc]; exact (SecA.C10KH.three_dvd_psl2 hp hp11).1
  have hZ : Subgroup.center ↥B = ⊥ := C10KH.center_eq_bot_of_simple hnp
  have hpB : p ∣ Nat.card ↥B := by
    have h1 : p ∣ Nat.card ↥B * 2 := hc2 ▸ dvd_mul_right p _
    exact (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h1)
  have hO : CFSG.pCore 2 ↥B = ⊥ := C10KH.pCore_eq_bot_of_simple hp hp2 hpB
  have hcO : Nat.card (ModO2 B) = Nat.card ↥B := Nat.card_congr (C10KH.modO2EquivOfBot hO).toEquiv
  have hsmall : ∀ N : ℕ, N < 660 → Nat.card ↥B ≠ N := fun N hN h => by omega
  have hwin : ∀ N k : ℕ, 1 ≤ k → k * (k ^ 2 - 1) < 2 * N →
      2 * N < (k + 1) * ((k + 1) ^ 2 - 1) → Nat.card ↥B ≠ N :=
    fun N k hk h1 h2 hN => C10KH.cube_sub_ne hk h1 h2 (by rw [← hc2, hN, mul_comm])
  have hHat : ∀ (Q S : Type) [Group Q] [Group S], Nonempty (Q ≃* ↥B) → ¬ IsHat Q S := by
    intro Q S _ _ ⟨f⟩ hh
    have h1 := hh.2.1
    have hQ : Subgroup.center Q = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h2 : f z ∈ Subgroup.center ↥B := (MulEquivClass.apply_mem_center_iff f).2 hz
      rw [hZ, Subgroup.mem_bot] at h2
      rw [Subgroup.mem_bot]
      exact f.injective (h2.trans (map_one f).symm)
    rw [hQ, Subgroup.card_bot] at h1
    omega
  have hHatB : ∀ S : Type, ∀ [Group S], ¬ IsHat ↥B S := fun S _ =>
    hHat ↥B S ⟨MulEquiv.refl _⟩
  have hHatO : ∀ S : Type, ∀ [Group S], ¬ IsHat (ModO2 B) S := fun S _ =>
    hHat (ModO2 B) S ⟨C10KH.modO2EquivOfBot hO⟩
  have hA5 : ∀ (Q : Type) [Group Q], Nat.card Q = Nat.card ↥B → ¬ IsAlt 5 Q := by
    intro Q _ hQ ⟨f⟩
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hQ
    exact hsmall 60 (by norm_num) (hQ.symm.trans (by rfl))
  have hA6 : ∀ (Q : Type) [Group Q], Nat.card Q = Nat.card ↥B → ¬ IsAlt 6 Q := by
    intro Q _ hQ ⟨f⟩
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hQ
    exact hsmall 360 (by norm_num) (hQ.symm.trans (by rfl))
  have hL32 : ∀ (Q : Type) [Group Q], Nat.card Q = Nat.card ↥B → ¬ IsPSL 3 2 1 Q :=
    fun Q _ hQ hq => hsmall 168 (by norm_num)
      (hQ.symm.trans (SecA.C10KH.card_of_isPSL_three_two_one hq))
  have hL42 : ∀ (Q : Type) [Group Q], Nat.card Q = Nat.card ↥B → ¬ IsPSL 4 2 1 Q :=
    fun Q _ hQ hq => hwin 20160 34 (by norm_num) (by norm_num) (by norm_num)
      (hQ.symm.trans (C10KH.card_of_isPSL421 hq))
  have hext : ∀ {PV PY : ∀ (V : Type) [Group V], Prop},
      (∀ (V : Type) [Group V], PV V → Nontrivial V) →
      (∀ (Q : Type) [Group Q], PY Q → Nontrivial Q) → ¬ IsExt ↥B PV PY :=
    fun hV hY => C10KH.not_isExt_of_simple hV hY
  have nE : ∀ n, 1 ≤ n → ∀ (V : Type) [Group V], IsE2 n V → Nontrivial V :=
    fun n hn V _ hv => C10KH.nontrivial_of_isE2 hn hv
  have nX : ∀ m, ∀ (V : Type) [Group V], IsExtraspecial2 m V → Nontrivial V :=
    fun m V _ hv => C10KH.nontrivial_of_isExtraspecial2 hv
  have nA : ∀ n, 3 ≤ n → ∀ (Q : Type) [Group Q], IsAlt n Q → Nontrivial Q :=
    fun n hn Q _ hq => C10KH.nontrivial_of_isAlt hn hq
  have nH : ∀ (S : Type) [Group S], ∀ (Q : Type) [Group Q], IsHat Q S → Nontrivial Q :=
    fun S _ Q _ hq => C10KH.nontrivial_of_isHat hq
  have nL3 : ∀ (Q : Type) [Group Q], IsPSL 3 2 1 Q → Nontrivial Q :=
    fun Q _ hq => C10KH.nontrivial_of_isPSL321 hq
  rcases h with h | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    ·
      exfalso
      obtain ⟨⟨n, hn⟩, -⟩ := h
      obtain ⟨-, hcn⟩ := SecA.C10KH.card_of_isPSL_two_two hn
      apply C10KH.psl2_ne_two_pow (n := n) hp hp11
      rw [← hc2, ← hcO, hcn, mul_comm]
    ·
      exfalso
      obtain ⟨f, hf, -⟩ := h
      obtain ⟨a, -, hfa, hcard⟩ := H13.card_of_suzukiModel hf
      apply SecA.C10KH.not_three_dvd_suzuki a
      rw [← hfa, ← hcard, hcO]
      exact h3
    ·
      exact (hL32 (ModO2 B) hcO h.1).elim
    ·
      exact (hL42 (ModO2 B) hcO h.1).elim
    ·
      rcases h.1 with h1 | h1
      · exact absurd h1 (hA5 ↥B rfl)
      · exact absurd h1 (hL32 ↥B rfl)
    ·
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (hA6 ↥B rfl)
      · exact absurd h1 (hHatB _)
    ·
      rcases h with ⟨r, hr, hr3, h1, h2⟩ | ⟨h1, -⟩
      · have hcr := H13.NotLie.card_psl2 h1
        have hg : Nat.gcd 2 (r ^ 1 - 1) = 2 := by
          rw [pow_one]
          exact Nat.gcd_eq_left ((Nat.Prime.even_sub_one hr (by omega)).two_dvd)
        rw [hg, pow_one] at hcr
        have hevr : 2 ∣ r * (r ^ 2 - 1) :=
          Dvd.dvd.mul_left (even_iff_two_dvd.mp
            (Nat.Odd.sub_odd ((hr.odd_of_ne_two (by omega)).pow) odd_one)) r
        have hrp : r = p := by
          apply C10KH.eq_of_cube_sub (by omega) (by omega)
          rw [← hc2, hcr, Nat.div_mul_cancel hevr]
        rw [← hrp]
        exact h2
      · exact absurd h1 (hA5 ↥B rfl)
    ·
      exfalso
      rcases h with ⟨s, r, hr, hr3, ⟨f⟩, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact C10KH.false_of_surj_sl2 hZ (by omega) f.toMonoidHom f.surjective
      · exact hA6 ↥B rfl h1
      · exact hHatB _ h1
    ·
      exfalso
      obtain ⟨r, hr, hr3, h1, -⟩ := h
      exact hext (fun V _ hv => C10KH.nontrivial_of_isElemAbelianOfRank hr hv)
        (fun Q _ hq => C10KH.nontrivial_of_isSL2 (by omega) hq) h1
    ·
      exact absurd h.1 (hA6 ↥B rfl)
    ·
      exfalso
      rcases h with ⟨h1 | h1, -⟩ | ⟨h1 | h1, -⟩
      · exact hext (nE 4 (by norm_num)) (nA 5 (by norm_num)) h1
      · exact hext (nE 4 (by norm_num)) (nA 6 (by norm_num)) h1
      · exact hext (nE 4 (by norm_num)) (nA 5 (by norm_num)) h1
      · exact hext (nE 4 (by norm_num)) (nH _) h1
    ·
      exfalso
      rcases h.1 with h1 | h1 | h1 | h1 | h1 | h1 | h1
      · obtain ⟨f⟩ := h1
        exact hwin 443520 96 (by norm_num) (by norm_num) (by norm_num)
          ((Nat.card_congr f.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22)
      · exact hwin 20160 34 (by norm_num) (by norm_num) (by norm_num) (C10KH.card_of_isPSL322 h1)
      · exact hext (nE 4 (by norm_num)) (nA 7 (by norm_num)) h1
      · exact hext (nE 4 (by norm_num)) nL3 h1
      · exact hext (nE 3 (by norm_num)) nL3 h1
      · exact hext (nE 4 (by norm_num)) (nA 6 (by norm_num)) h1
      · exact hext (nE 4 (by norm_num)) (nA 5 (by norm_num)) h1
    ·
      exfalso
      rcases h.1 with h1 | h1 | h1 | h1
      · exact hext (nE 4 (by norm_num)) (fun Q _ hq => C10KH.nontrivial_of_isPSL421 hq) h1
      · exact hext (nE 6 (by norm_num)) nL3 h1
      · exact hext (nX 3) nL3 h1
      · exact hext (nE 6 (by norm_num)) (nH _) h1
    ·
      exact absurd h.1 (hA5 ↥B rfl)
    ·
      exact absurd h.1 (hext (nX 2) (nA 5 (by norm_num)))
    ·
      exfalso
      rcases h.2 with h1 | h1 | h1 | h1 | h1 | h1
      · exact hext (nX 6) (nH _) h1
      · exact hext (nE 11 (by norm_num)) (fun Q _ hq => C10KH.nontrivial_of_isM24 hq) h1
      · exact hA5 (ModO2 B) hcO h1
      · exact hHatO _ h1
      · exact hL42 (ModO2 B) hcO h1
      · exact hL32 (ModO2 B) hcO h1
    ·
      exfalso
      rcases h.1 with h1 | h1
      · exact hext (fun V _ hv => C10KH.nontrivial_of_isZ4StarExtra2 hv) (nA 5 (by norm_num)) h1
      · exact hext (fun V _ hv => C10KH.nontrivial_of_isZ4Cubed hv) nL3 h1
    ·
      exfalso
      rcases h.1 with h1 | h1
      · exact hext (nX 3) nL3 h1
      · exact hext (nE 6 (by norm_num)) (nH _) h1
    ·
      exfalso
      have h1 := h.2.1
      rw [hO, Subgroup.card_bot] at h1
      norm_num at h1
  ·
    exfalso
    dsimp only [A312Nonquasi] at h
    rcases h with ⟨-, hL, q, hq, hq2, ⟨f⟩⟩ | ⟨-, -, N, hNn, hN, ⟨f⟩⟩
    · have hBL : B ≤ L := hL ▸ le_sup_left
      have hsup : B.subgroupOf L ⊔ CFSG.oddCore ↥L = ⊤ := by
        have h1 := Subgroup.subgroupOf_sup (A := B) (A' := (CFSG.oddCore ↥L).map L.subtype)
          hBL (Subgroup.map_subtype_le _)
        have hO' : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
        rw [← hL, Subgroup.subgroupOf_self, hO'] at h1
        exact h1.symm
      have hsurj := C10KH.surjective_of_sup_eq hsup
      let φ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
        f.toMonoidHom.comp (((QuotientGroup.mk' (CFSG.oddCore ↥L)).comp
          (B.subgroupOf L).subtype).comp (Subgroup.subgroupOfEquivOfLe hBL).symm.toMonoidHom)
      have hφ : Function.Surjective φ :=
        f.surjective.comp (hsurj.comp (Subgroup.subgroupOfEquivOfLe hBL).symm.surjective)
      exact C10KH.false_of_surj_sl2 hZ (by have := hq.two_le; omega) φ hφ
    · have hsup : B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype) ⊔ N = ⊤ := by
        have h1 := Subgroup.subgroupOf_sup (A := B) (A' := (CFSG.oddCore ↥L).map L.subtype)
          (le_sup_left : B ≤ B ⊔ (CFSG.oddCore ↥L).map L.subtype) le_sup_right
        rw [Subgroup.subgroupOf_self, ← hN] at h1
        exact h1.symm
      have hsurj := C10KH.surjective_of_sup_eq hsup
      let φ : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
        f.toMonoidHom.comp (((QuotientGroup.mk' N).comp
          (B.subgroupOf (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).subtype).comp
          (Subgroup.subgroupOfEquivOfLe le_sup_left).symm.toMonoidHom)
      have hφ : Function.Surjective φ :=
        f.surjective.comp (hsurj.comp (Subgroup.subgroupOfEquivOfLe le_sup_left).symm.surjective)
      exact C10KH.false_of_surj_sl2 hZ (by norm_num) φ hφ

end CFSG.Quasithin.Vol2.Ch11.SecE
