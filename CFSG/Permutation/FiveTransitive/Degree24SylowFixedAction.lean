module

public import CFSG.Permutation.FiveTransitive.Degree24FixedSetSeven
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

abbrev sylowImage
    (X : Type) (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup P s)) : Subgroup P :=
  (S : Subgroup (fixingSubgroup P s)).map
    (fixingSubgroup P s).subtype

abbrev sylowNormalizer
    (X : Type) (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup P s)) : Subgroup P :=
  Subgroup.normalizer (sylowImage X P s S : Set P)

abbrev sylowInNormalizer
    (X : Type) (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup P s)) :
    Subgroup (sylowNormalizer X P s S) :=
  (sylowImage X P s S).subgroupOf
    (sylowNormalizer X P s S)

abbrev sylowFixedPoints
    (X : Type) (P : Subgroup (Equiv.Perm X)) (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup P s)) :=
  MulAction.fixedPoints (sylowInNormalizer X P s S) X

theorem sylowFixedPoints_eq_fixedPoints_generator
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s))
    (hScard : Nat.card S = p)
    (u : S) (huNe : u ≠ 1) :
    sylowFixedPoints X P s S =
      Function.fixedPoints
        (((u : fixingSubgroup P s) : P) :
          Equiv.Perm X) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  let uP : P := (u : H)
  let g : Equiv.Perm X := uP
  change F = Function.fixedPoints g
  ext x
  rw [MulAction.mem_fixedPoints,
    Function.mem_fixedPoints_iff]
  constructor
  · intro hx
    have huSP : uP ∈ SP :=
      Subgroup.mem_map_of_mem H.subtype u.prop
    let uN : N := ⟨uP, SP.le_normalizer huSP⟩
    let uSN : SN := ⟨uN, huSP⟩
    change uP • x = x
    exact hx uSN
  · intro hx z
    obtain ⟨zH, hzS, hzEq⟩ :=
      Subgroup.mem_map.mp z.prop
    let zS : S := ⟨zH, hzS⟩
    have hzPow : zS ∈ Subgroup.zpowers u :=
      mem_zpowers_of_prime_card hScard huNe
    obtain ⟨j, hj⟩ :=
      Subgroup.mem_zpowers_iff.mp hzPow
    have huStab :
        uP ∈ MulAction.stabilizer P x := by
      rw [MulAction.mem_stabilizer_iff]
      change g x = x at hx
      exact hx
    have hzPowers :
        ((zH : H) : P) ∈
          Subgroup.zpowers uP := by
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨j, ?_⟩
      let inclusion : S →* P :=
        H.subtype.comp (S : Subgroup H).subtype
      have hjP := congrArg inclusion hj
      rw [map_zpow] at hjP
      exact hjP
    have hzStab :
        ((zH : H) : P) ∈
          MulAction.stabilizer P x :=
      (Subgroup.zpowers_le.mpr huStab) hzPowers
    have hzFix :
        ((zH : H) : P) • x = x :=
      MulAction.mem_stabilizer_iff.mp hzStab
    have hzEqP :
        ((zH : H) : P) = ((z : N) : P) :=
      hzEq
    rw [hzEqP] at hzFix
    exact hzFix

theorem sylowNormalizer_five_transitive_on_fixedPoints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s)) :
    ∀ a b : Fin 5 → sylowFixedPoints X P s S,
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
    ∀ a b : Fin 5 → F, Function.Injective a →
      Function.Injective b →
      ∃ c : N, ∀ i, c • a i = b i
  intro a b ha hb
  let aX : Fin 5 ↪ X := {
    toFun := fun i => (a i).1
    inj' := fun i j hij =>
      ha (Subtype.ext hij) }
  let bX : Fin 5 ↪ X := {
    toFun := fun i => (b i).1
    inj' := fun i j hij =>
      hb (Subtype.ext hij) }
  obtain ⟨q, hq⟩ :=
    h5 aX bX aX.injective bX.injective
  let t : Set X := Set.range bX
  have ht : t.ncard = 5 := by
    rw [Set.ncard_range_of_injective bX.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let Ht : Subgroup P := fixingSubgroup P t
  have hHcard : Nat.card H = Nat.card Ht := by
    simpa only [H, Ht] using
      five_point_stabilizers_have_equal_card
        X P h5 s t hs ht
  have hSPleHt : SP ≤ Ht := by
    intro z hz
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i, rfl⟩
    let zN : N := ⟨z, SP.le_normalizer hz⟩
    let zSN : SN := ⟨zN, hz⟩
    exact
      MulAction.mem_fixedPoints.mp
        (b i).2 zSN
  let QSP : Subgroup P :=
    SP.map (MulAut.conj q).toMonoidHom
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
        rw [← hq i, inv_smul_smul]
      _ = q • aX i :=
        congrArg (fun x : X => q • x) hwFix
      _ = bX i := hq i
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
      Nat.card SU = Nat.card SP :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            hSPleHt).toEquiv
      _ = Nat.card S := hSPcard
  have hTUcard : Nat.card TU = Nat.card S := by
    calc
      Nat.card TU = Nat.card QSP :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            hQSPleHt).toEquiv
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
    _ = kP • bX i := by rw [hq i]
    _ = bX i := by
      exact
        (mem_fixingSubgroup_iff P).mp
          k.prop (bX i) ⟨i, rfl⟩

theorem sylow_card_mul_fixed_action_card_le
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s)) :
    Nat.card S *
        Nat.card
          (MulAction.toPermHom
            (sylowNormalizer X P s S)
            (sylowFixedPoints X P s S)).range ≤
      (Nat.card (sylowFixedPoints X P s S)).descFactorial 5 *
        Nat.card
          (Subgroup.normalizer
            (S : Set (fixingSubgroup P s))) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let J : Subgroup (Equiv.Perm F) := ρ.range
  let NL : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  change
    Nat.card S * Nat.card J ≤
      (Nat.card F).descFactorial 5 * Nat.card NL
  have hN5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ c : N, ∀ i, c • a i = b i := by
    simpa only [F, N, SN] using
      sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S
  have hNfive :
      MulAction.IsMultiplyPretransitive N F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      hN5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  let eX : Fin 5 ↪ X :=
    fiveEmbeddingOfSet X s hs
  have heXrange : Set.range eX = s :=
    range_fiveEmbeddingOfSet X s hs
  have heFixed (i : Fin 5) : eX i ∈ F := by
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨zH, hzS, hzEq⟩ :=
      Subgroup.mem_map.mp z.prop
    have hfix :
        H.subtype zH • eX i = eX i :=
      (mem_fixingSubgroup_iff P).mp zH.prop
        (eX i) (by
          rw [← heXrange]
          exact ⟨i, rfl⟩)
    rw [hzEq] at hfix
    exact hfix
  let eF : Fin 5 ↪ F := {
    toFun := fun i => ⟨eX i, heFixed i⟩
    inj' := fun i j hij =>
      eX.injective
        (congrArg (fun z : F => (z : X)) hij) }
  let sF : Set F := Set.range eF
  have hsF : sF.ncard = 5 := by
    rw [Set.ncard_range_of_injective eF.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let K : Subgroup N := fixingSubgroup N sF
  have hNfiveSF :
      MulAction.IsMultiplyPretransitive N F sF.ncard := by
    rw [hsF]
    exact hNfive
  have hKindexRaw :=
    hNfiveSF.index_of_fixingSubgroup_eq sF
  have hKindex :
      K.index = (Nat.card F).descFactorial 5 := by
    change
      (fixingSubgroup N sF).index =
        (Nat.card F).descFactorial 5
    rw [hKindexRaw,
      Nat.descFactorial_eq_factorial_mul_choose,
      hsF, mul_comm]
  have hNcardEq :
      Nat.card N =
        (Nat.card F).descFactorial 5 * Nat.card K := by
    have hproduct := K.index_mul_card
    rw [hKindex] at hproduct
    exact hproduct.symm
  let baseMap : K →* P :=
    N.subtype.comp K.subtype
  have hbaseMapMemH :
      ∀ q : K, baseMap q ∈ H := by
    intro q
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxi : x ∈ Set.range eX := by
      simpa only [heXrange] using hx
    obtain ⟨i, rfl⟩ := hxi
    have hqfix :=
      (mem_fixingSubgroup_iff N).mp q.prop
        (eF i) ⟨i, rfl⟩
    exact congrArg Subtype.val hqfix
  let localMap : K →* H :=
    baseMap.codRestrict H hbaseMapMemH
  have hSPcomap :
      SP.comap H.subtype = (S : Subgroup H) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ :=
        Subgroup.mem_map.mp hz
      have hwEq : w = z :=
        H.subtype_injective hwz
      rwa [← hwEq]
    · intro hz
      exact
        Subgroup.mem_map_of_mem H.subtype hz
  have hlocalMapMemNL :
      ∀ q : K, localMap q ∈ NL := by
    intro q
    have hcomap :
        localMap q ∈
          (Subgroup.normalizer SP).comap H.subtype :=
      q.1.prop
    have hnormal :=
      Subgroup.le_normalizer_comap H.subtype hcomap
    change localMap q ∈
      Subgroup.normalizer (SP.comap H.subtype) at hnormal
    rw [hSPcomap] at hnormal
    exact hnormal
  let normalizerMap : K →* NL :=
    localMap.codRestrict NL hlocalMapMemNL
  have hnormalizerMapInjective :
      Function.Injective normalizerMap := by
    intro a b hab
    apply K.subtype_injective
    apply N.subtype_injective
    exact
      congrArg
        (fun q : NL => ((q : H) : P)) hab
  have hKdvdNL : Nat.card K ∣ Nat.card NL :=
    Subgroup.card_dvd_of_injective
      normalizerMap hnormalizerMapInjective
  have hKle : Nat.card K ≤ Nat.card NL :=
    Nat.le_of_dvd Nat.card_pos hKdvdNL
  have hSPcard : Nat.card SP = Nat.card S := by
    exact
      Nat.card_congr
        ((S : Subgroup H).equivMapOfInjective
          H.subtype H.subtype_injective).toEquiv.symm
  have hSNleKer : SN ≤ ρ.ker := by
    intro z hz
    change ρ z = 1
    ext x
    let zSN : SN := ⟨z, hz⟩
    exact
      MulAction.mem_fixedPoints.mp x.prop zSN
  have hSNcard : Nat.card SN = Nat.card SP := by
    exact
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          SP.le_normalizer).toEquiv
  have hSPdvdKer :
      Nat.card SP ∣ Nat.card ρ.ker := by
    rw [← hSNcard]
    exact Subgroup.card_dvd_of_le hSNleKer
  have hSleKer : Nat.card S ≤ Nat.card ρ.ker := by
    rw [← hSPcard]
    exact Nat.le_of_dvd Nat.card_pos hSPdvdKer
  have hNcardRange :
      Nat.card N = Nat.card J * Nat.card ρ.ker := by
    have hproduct := ρ.ker.index_mul_card
    rw [Subgroup.index_ker] at hproduct
    simpa only [J] using hproduct.symm
  calc
    Nat.card S * Nat.card J ≤
        Nat.card ρ.ker * Nat.card J :=
      Nat.mul_le_mul_right (Nat.card J) hSleKer
    _ = Nat.card N := by
      rw [mul_comm, ← hNcardRange]
    _ = (Nat.card F).descFactorial 5 * Nat.card K :=
      hNcardEq
    _ ≤ (Nat.card F).descFactorial 5 * Nat.card NL :=
      Nat.mul_le_mul_left _ hKle

end FiveTransitive.Degree24

end CFSG
