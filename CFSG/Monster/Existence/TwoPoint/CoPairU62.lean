module

public import CFSG.Monster.Existence.TwoPoint.CoPairDefs
public import CFSG.Monster.Existence.TwoPoint.CoPairCertW2
public import CFSG.Monster.Existence.TwoPoint.CoPairKOrbit
public import CFSG.Monster.Existence.TwoPoint.CoPairKEquiv
public import CFSG.Monster.Existence.TwoPoint.CoPairCertU62
public import CFSG.Fischer.T46Simple
public import CFSG.Fischer.Classification.Recognition.PSU6

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.CoPair
  CFSG.Monster.Existence.CoPair.Native

theorem natCard_coPair_u62 :
    Nat.card ↥(Kstab v0 ⊓ Kstab coW2) = 9196830720 := by
  obtain ⟨D, hD⟩ := orbW2K_eq_true
  have h := natCard_inf_of_orbit (ncard_orbit_of_orbOK hD)
  rw [show dec seedW2 = coW2 from coW2_eq_dec.symm] at h
  omega

theorem coPair_u62_equiv :
    Nonempty (↥(Kstab v0 ⊓ Kstab coW2) ≃* CFSG.Fischer.T46) := by
  obtain ⟨D, hok, hSA, hSB⟩ := u62K_eq_true
  have hτ : ∀ (g : Equiv.Perm (Fin 693)) (T : CFSG.Sporadic.Th.Native.Table),
      CFSG.Sporadic.Th.Rep 693 T g → ∀ i : Fin 693,
        (g i : ℕ) = CFSG.Sporadic.Th.Native.ap T i :=
    fun g T hg i => by
      rw [hg i i.2, CFSG.Sporadic.Th.idx_of_lt g i.2]
      rfl
  have hcard : Nat.card (kvStab (dec 4096)) = Nat.card CFSG.Fischer.T46 := by
    rw [CFSG.Fischer.card_T46, Nat.card_congr (kvStabEquivInf (dec 4096)).toEquiv,
      ← coW2_eq_dec]
    exact natCard_coPair_u62
  let E : ℕ → Fin 693 := fun l => ⟨l % 693, Nat.mod_lt _ (by norm_num)⟩
  have hE : ∀ (g : Equiv.Perm (Fin 693)) (T : CFSG.Sporadic.Th.Native.Table) (S : ℕ),
      CFSG.Sporadic.Th.Rep 693 T g →
      (∀ i < 693, CFSG.KC.CoPair.f16 S i = CFSG.Sporadic.Th.Native.ap T i) →
      ∀ l < 693, E (CFSG.KC.CoPair.f16 S l) = g (E l) := fun g T S hg hS l hl => by
    have hEl : E l = ⟨l, hl⟩ := Fin.ext (Nat.mod_eq_of_lt hl)
    have h1 : (g ⟨l, hl⟩ : ℕ) = CFSG.KC.CoPair.f16 S l := by rw [hτ g T hg, hS l hl]
    rw [hEl]
    apply Fin.ext
    change CFSG.KC.CoPair.f16 S l % 693 = _
    rw [← h1, Nat.mod_eq_of_lt (Fin.isLt _)]
  obtain ⟨e⟩ := kvStab_equiv_of_eqOK (w := 4096) hok (by norm_num) E
    CFSG.Fischer.t46x CFSG.Fischer.t46y (hE _ _ _ CFSG.Fischer.rep_t46x hSA)
    (hE _ _ _ CFSG.Fischer.rep_t46y hSB)
    (fun j => ⟨j.val, j.isLt, Fin.ext (Nat.mod_eq_of_lt j.isLt)⟩)
    CFSG.Fischer.closure_t46x_t46y hcard
  rw [coW2_eq_dec]
  exact ⟨(kvStabEquivInf (dec 4096)).symm.trans e⟩

theorem coPair_u62 :
    CFSG.Blueprint.LieModel ↥(Kstab v0 ⊓ Kstab coW2) .PSU 6 2 1 := by
  obtain ⟨e⟩ := coPair_u62_equiv
  exact CFSG.Fischer.Classification.Recognition.lieModel_of_mulEquiv_PSU
    CFSG.Fischer.isNondegenerateHermitian_one
    (e.trans (CFSG.Fischer.suQuotEquiv.symm.trans CFSG.Fischer.psuEquiv))

theorem coPair_u62_simple :
    IsSimpleGroup ↥(Kstab v0 ⊓ Kstab coW2) := by
  obtain ⟨e⟩ := coPair_u62_equiv
  have := CFSG.Fischer.isSimpleGroup_T46
  exact e.isSimpleGroup

theorem coPair_u62_pCore :
    ∀ P : Subgroup ↥(Kstab v0 ⊓ Kstab coW2), P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hP hp
  have := hP
  have := coPair_u62_simple
  obtain ⟨e⟩ := coPair_u62_equiv
  have : Finite ↥(Kstab v0 ⊓ Kstab coW2) := Finite.of_equiv _ e.symm.toEquiv
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact h
  · exfalso
    subst h
    have hall : IsPGroup 2 ↥(Kstab v0 ⊓ Kstab coW2) := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hall
    rw [natCard_coPair_u62] at hn
    have h3 : 3 ∣ 2 ^ n := ⟨3065610240, by omega⟩
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

end CFSG.Monster.Existence
