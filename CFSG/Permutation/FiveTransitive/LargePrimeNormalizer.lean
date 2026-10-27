module

public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.LargePrimeNormalizer

open MulAction SubMulAction Subgroup
open FiveTransitive.Degree24

theorem sylowNormalizer_transitive_on_fixedPoints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {k : ℕ} (hk : k ≤ 5)
    (s : Set X) (hs : s.ncard = k)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s)) :
    ∀ a b : Fin k → sylowFixedPoints X P s S,
      Function.Injective a →
      Function.Injective b →
      ∃ c : sylowNormalizer X P s S,
        ∀ i, c • a i = b i := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  change
    ∀ a b : Fin k → F, Function.Injective a →
      Function.Injective b →
      ∃ c : N, ∀ i, c • a i = b i
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hPk :
      MulAction.IsMultiplyPretransitive P X k := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact
      MulAction.isMultiplyPretransitive_of_le
        (G := P) (α := X) (m := k) (n := 5)
          hk (by
            rw [Nat.card_eq_fintype_card]
            exact hcard)
  intro a b ha hb
  let aX : Fin k ↪ X := {
    toFun := fun i => (a i).1
    inj' := fun i j hij =>
      ha (Subtype.ext hij) }
  let bX : Fin k ↪ X := {
    toFun := fun i => (b i).1
    inj' := fun i j hij =>
      hb (Subtype.ext hij) }
  obtain ⟨q, hq⟩ :=
    hPk.exists_smul_eq aX bX
  let t : Set X := Set.range bX
  have ht : t.ncard = k := by
    rw [Set.ncard_range_of_injective bX.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let Ht : Subgroup P := fixingSubgroup P t
  have hHindex :
      H.index = (Nat.card X).descFactorial k := by
    have hPkS :
        MulAction.IsMultiplyPretransitive P X s.ncard := by
      simpa only [hs] using hPk
    calc
      H.index =
          (Nat.card X).choose k * k.factorial := by
        simpa only [H, hs] using
          hPkS.index_of_fixingSubgroup_eq s
      _ = (Nat.card X).descFactorial k := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          mul_comm]
  have hHtindex :
      Ht.index = (Nat.card X).descFactorial k := by
    have hPkT :
        MulAction.IsMultiplyPretransitive P X t.ncard := by
      simpa only [ht] using hPk
    calc
      Ht.index =
          (Nat.card X).choose k * k.factorial := by
        simpa only [Ht, ht] using
          hPkT.index_of_fixingSubgroup_eq t
      _ = (Nat.card X).descFactorial k := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          mul_comm]
  have hHcard : Nat.card H = Nat.card Ht := by
    have hHproduct := H.index_mul_card
    have hHtproduct := Ht.index_mul_card
    rw [hHindex] at hHproduct
    rw [hHtindex] at hHtproduct
    exact Nat.eq_of_mul_eq_mul_left
      (by exact Nat.descFactorial_pos.mpr (by
        rw [Nat.card_eq_fintype_card]
        exact hk.trans hcard))
      (hHproduct.trans hHtproduct.symm)
  have hSPleHt : SP ≤ Ht := by
    intro z hz
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i, rfl⟩
    let zN : N := ⟨z, SP.le_normalizer hz⟩
    let zSN : SN := ⟨zN, hz⟩
    exact
      MulAction.mem_fixedPoints.mp
        (b i).2 zSN
  have hSPsubgroupCard :
      Nat.card (SP.subgroupOf Ht) = Nat.card SP :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hSPleHt).toEquiv
  let QSP : Subgroup P :=
    SP.map (MulAut.conj q).toMonoidHom
  have hqPoint (i : Fin k) :
      q • aX i = bX i := by
    have hi :=
      congrArg (fun e : Fin k ↪ X => e i) hq
    exact hi
  have hQSPleHt : QSP ≤ Ht := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ :=
      Subgroup.mem_map.mp hz
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i, rfl⟩
    let wN : N := ⟨w, SP.le_normalizer hw⟩
    let wSN : SN := ⟨wN, hw⟩
    have hwFix :
        (w : P) • (a i).1 = (a i).1 :=
      MulAction.mem_fixedPoints.mp
        (a i).2 wSN
    calc
      (MulAut.conj q w : P) • bX i =
          q • ((w : P) • (q⁻¹ • bX i)) := by
        simp only [MulAut.conj_apply, mul_smul]
      _ = q • ((w : P) • aX i) := by
        rw [← hqPoint i, inv_smul_smul]
      _ = q • aX i :=
        congrArg (fun x : X => q • x) hwFix
      _ = bX i := hqPoint i
  have hQSPsubgroupCard :
      Nat.card (QSP.subgroupOf Ht) = Nat.card QSP :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hQSPleHt).toEquiv
  have hQSPcard : Nat.card QSP = Nat.card SP := by
    exact
      Nat.card_congr
        (SP.equivMapOfInjective
          (MulAut.conj q).toMonoidHom
          (MulAut.conj q).injective).toEquiv.symm
  have hSPcard : Nat.card SP = Nat.card S := by
    exact
      Nat.card_congr
        ((S : Subgroup H).equivMapOfInjective
          H.subtype H.subtype_injective).toEquiv.symm
  let SU : Subgroup Ht := SP.subgroupOf Ht
  let TU : Subgroup Ht := QSP.subgroupOf Ht
  have hSUcard : Nat.card SU = Nat.card S := by
    calc
      Nat.card SU = Nat.card SP := hSPsubgroupCard
      _ = Nat.card S := hSPcard
  have hTUcard : Nat.card TU = Nat.card S := by
    calc
      Nat.card TU = Nat.card QSP := hQSPsubgroupCard
      _ = Nat.card SP := hQSPcard
      _ = Nat.card S := hSPcard
  obtain ⟨n, hn⟩ :=
    S.isPGroup'.exists_card_eq
  have hSUisP : IsPGroup p SU := by
    exact IsPGroup.of_card (hSUcard.trans hn)
  have hTUisP : IsPGroup p TU := by
    exact IsPGroup.of_card (hTUcard.trans hn)
  obtain ⟨U, hSUleU⟩ :=
    hSUisP.exists_le_sylow
  obtain ⟨T, hTUleT⟩ :=
    hTUisP.exists_le_sylow
  have hUcard : Nat.card U = Nat.card S := by
    rw [U.card_eq_multiplicity,
      S.card_eq_multiplicity, ← hHcard]
  have hTcard : Nat.card T = Nat.card S := by
    exact
      (Nat.card_congr (Sylow.equiv T U).toEquiv).trans
        hUcard
  have hSUEq : SU = (U : Subgroup Ht) := by
    apply Subgroup.eq_of_le_of_card_ge hSUleU
    rw [hSUcard, hUcard]
  have hTUEq : TU = (T : Subgroup Ht) := by
    apply Subgroup.eq_of_le_of_card_ge hTUleT
    rw [hTUcard, hTcard]
  obtain ⟨k, hk⟩ :=
    exists_smul_eq Ht T U
  have hkSub :
      TU.map (MulAut.conj k).toMonoidHom = SU := by
    rw [hTUEq, hSUEq]
    exact congrArg Sylow.toSubgroup hk
  let kP : P := k
  have hkQSP :
      QSP.map (MulAut.conj kP).toMonoidHom = SP := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨z, hz, rfl⟩ :=
        Subgroup.mem_map.mp hy
      let zHt : Ht := ⟨z, hQSPleHt hz⟩
      have hzTU : zHt ∈ TU := hz
      have hkzSU :
          MulAut.conj k zHt ∈ SU := by
        rw [← hkSub]
        exact
          Subgroup.mem_map_of_mem
            (MulAut.conj k).toMonoidHom hzTU
      change
        (MulAut.conj kP z : P) ∈ SP
      exact hkzSU
    · calc
        Nat.card SP = Nat.card QSP :=
          hQSPcard.symm
        _ = Nat.card
            (QSP.map
              (MulAut.conj kP).toMonoidHom) :=
          Nat.card_congr
            (QSP.equivMapOfInjective
              (MulAut.conj kP).toMonoidHom
              (MulAut.conj kP).injective).toEquiv
        _ ≤ Nat.card
            (QSP.map
              (MulAut.conj kP).toMonoidHom) :=
          le_rfl
  let cP : P := kP * q
  have hcMap :
      SP.map (MulAut.conj cP).toMonoidHom = SP := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨z, hz, rfl⟩ :=
        Subgroup.mem_map.mp hy
      have hqz :
          MulAut.conj q z ∈ QSP :=
        Subgroup.mem_map_of_mem
          (MulAut.conj q).toMonoidHom hz
      have hkqz :
          MulAut.conj kP (MulAut.conj q z) ∈ SP := by
        rw [← hkQSP]
        exact
          Subgroup.mem_map_of_mem
            (MulAut.conj kP).toMonoidHom hqz
      have heq :
          MulAut.conj cP z =
            MulAut.conj kP (MulAut.conj q z) := by
        dsimp only [cP]
        simp only [MulAut.conj_apply]
        group
      change MulAut.conj cP z ∈ SP
      rw [heq]
      exact hkqz
    · calc
        Nat.card SP = Nat.card
            (SP.map
              (MulAut.conj cP).toMonoidHom) :=
          Nat.card_congr
            (SP.equivMapOfInjective
              (MulAut.conj cP).toMonoidHom
              (MulAut.conj cP).injective).toEquiv
        _ ≤ Nat.card
            (SP.map
              (MulAut.conj cP).toMonoidHom) :=
          le_rfl
  have hcNormalizer :
      cP ∈ Subgroup.normalizer SP :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      hcMap
  let cN : N := ⟨cP, hcNormalizer⟩
  refine ⟨cN, ?_⟩
  intro i
  apply Subtype.ext
  change cP • aX i = bX i
  calc
    cP • aX i = kP • (q • aX i) := by
      simp only [cP, mul_smul]
    _ = kP • bX i :=
      congrArg (fun x : X => kP • x) (hqPoint i)
    _ = bX i := by
      exact
        (mem_fixingSubgroup_iff P).mp
          k.prop (bX i) ⟨i, rfl⟩

end FiveTransitive.LargePrimeNormalizer

end CFSG
