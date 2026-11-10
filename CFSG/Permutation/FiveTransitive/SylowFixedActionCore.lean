module

public import CFSG.Permutation.FiveTransitive.Reduction
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.SylowFixedActionCore

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
    have htrans := FiveTransitive.isMultiplyPretransitive_of_explicit P X 5 h5
    have hsIndex := htrans.index_of_fixingSubgroup_mul hs
    have htIndex := htrans.index_of_fixingSubgroup_mul ht
    have hindices : H.index = Ht.index := by
      change (fixingSubgroup P s).index = (fixingSubgroup P t).index
      exact Nat.eq_of_mul_eq_mul_right
        (Nat.factorial_pos (Nat.card X - 5)) (hsIndex.trans htIndex.symm)
    have hmH := H.index_mul_card
    have hmT := Ht.index_mul_card
    rw [hindices] at hmH
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (hmH.trans hmT.symm)
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

theorem prime_not_dvd_range_card_of_sylow_le_ker
    {p : ℕ} [Fact p.Prime]
    {K Q : Type*} [Group K] [Finite K] [Group Q]
    (S : Sylow p K) (f : K →* Q)
    (hker : (S : Subgroup K) ≤ f.ker) :
    ¬p ∣ Nat.card f.range := by
  intro hp
  have hindexDvd : f.ker.index ∣ (S : Subgroup K).index :=
    Subgroup.index_dvd_of_le hker
  have hpIndex : p ∣ (S : Subgroup K).index := by
    rw [Subgroup.index_ker] at hindexDvd
    exact hp.trans hindexDvd
  exact S.not_dvd_index hpIndex

theorem odd_prime_dvd_alternating_card
    (Y : Type*) [Fintype Y] [DecidableEq Y]
    {p : ℕ} (hp : p.Prime) (hpTwo : p ≠ 2)
    (hle : p ≤ Fintype.card Y) :
    p ∣ Nat.card (alternatingGroup Y) := by
  let _ : Nontrivial Y :=
    Fintype.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le hp.one_lt hle)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  have htwoLe : 2 ≤ Fintype.card Y := hp.two_le.trans hle
  have htwoDvd : 2 ∣ (Fintype.card Y).factorial :=
    Nat.dvd_factorial (by norm_num) htwoLe
  apply (Nat.dvd_div_iff_mul_dvd htwoDvd).2
  exact
    (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hpTwo)).mul_dvd_of_dvd_of_dvd
      htwoDvd (Nat.dvd_factorial hp.pos hle)

private theorem two_dvd_alternating_card_of_four_le
    (Y : Type*) [Fintype Y] [DecidableEq Y]
    (hfour : 4 ≤ Fintype.card Y) :
    2 ∣ Nat.card (alternatingGroup Y) := by
  let _ : Nontrivial Y :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  have htwoDvd : 2 ∣ (Fintype.card Y).factorial :=
    Nat.dvd_factorial (by norm_num) (by omega)
  apply (Nat.dvd_div_iff_mul_dvd htwoDvd).2
  norm_num only [mul_comm]
  exact Nat.dvd_factorial (by norm_num) hfour

private theorem alternating_degree_lt_odd_sylow_prime
    {p : ℕ} [hpFact : Fact p.Prime]
    {K Q : Type*} [Group K] [Finite K] [Group Q]
    (S : Sylow p K) (f : K →* Q)
    (hker : (S : Subgroup K) ≤ f.ker)
    (Y : Type*) [Fintype Y] [DecidableEq Y]
    (i : alternatingGroup Y →* Q)
    (hi : Function.Injective i)
    (hRange : i.range ≤ f.range)
    (hpTwo : p ≠ 2) :
    Fintype.card Y < p := by
  by_contra hnot
  have hle : p ≤ Fintype.card Y := by omega
  have hpAlt : p ∣ Nat.card (alternatingGroup Y) :=
    odd_prime_dvd_alternating_card Y hpFact.out hpTwo hle
  have hcardRange :
      Nat.card i.range = Nat.card (alternatingGroup Y) :=
    Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm
  apply prime_not_dvd_range_card_of_sylow_le_ker S f hker
  exact hpAlt.trans (by
    rw [← hcardRange]
    exact Subgroup.card_dvd_of_le hRange)

private theorem alternating_degree_le_three_for_sylow_two
    {K Q : Type*} [Group K] [Finite K] [Group Q]
    (S : Sylow 2 K) (f : K →* Q)
    (hker : (S : Subgroup K) ≤ f.ker)
    (Y : Type*) [Fintype Y] [DecidableEq Y]
    (i : alternatingGroup Y →* Q)
    (hi : Function.Injective i)
    (hRange : i.range ≤ f.range) :
    Fintype.card Y ≤ 3 := by
  by_contra hnot
  have hfour : 4 ≤ Fintype.card Y := by omega
  have htwoAlt : 2 ∣ Nat.card (alternatingGroup Y) :=
    two_dvd_alternating_card_of_four_le Y hfour
  have hcardRange :
      Nat.card i.range = Nat.card (alternatingGroup Y) :=
    Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm
  apply prime_not_dvd_range_card_of_sylow_le_ker S f hker
  exact htwoAlt.trans (by
    rw [← hcardRange]
    exact Subgroup.card_dvd_of_le hRange)

private theorem fixed_complement_bound_of_alternating_normalizer_action
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X) (_hs : s.ncard = 5)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s))
    (hAlt :
      let N := sylowNormalizer X P s S
      let F := sylowFixedPoints X P s S
      let _ : Fintype F := Fintype.ofFinite F
      alternatingGroup F ≤
        (MulAction.toPermHom N F).range) :
    let F := sylowFixedPoints X P s S
    let _ : Fintype F := Fintype.ofFinite F
    let sF : Set F := {x | (x : X) ∈ s}
    let Y := (sFᶜ : Set F)
    let _ : Fintype Y := Fintype.ofFinite Y
    (p = 2 → Fintype.card Y ≤ 3) ∧
      (p ≠ 2 → Fintype.card Y < p) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := MulAction.toPermHom N F
  let L : Subgroup H := N.comap H.subtype
  let toN : L →* N :=
    { toFun := fun z ↦ ⟨((z : L) : H), z.prop⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let phi : L →* Equiv.Perm F := rho.comp toN
  have hsF : s ⊆ (F : Set X) := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.prop
    have hfix := (mem_fixingSubgroup_iff P).mp u.prop x hx
    change ((z : N) : P) • x = x
    rw [show ((z : N) : P) = (u : H) by exact hu.symm]
    exact hfix
  let sF : Set F := {x | (x : X) ∈ s}
  let Y := (sFᶜ : Set F)
  let : Fintype Y := Fintype.ofFinite Y
  have hSL : (S : Subgroup H) ≤ L := by
    intro z hz
    change ((z : H) : P) ∈ N
    exact SP.le_normalizer
      (Subgroup.mem_map_of_mem H.subtype hz)
  let SL : Sylow p L := S.subtype hSL
  have hSLker : (SL : Subgroup L) ≤ phi.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hzS : ((z : L) : H) ∈ S := hz
    have hzSP : (((z : L) : H) : P) ∈ SP :=
      Subgroup.mem_map_of_mem H.subtype hzS
    let zN : N :=
      ⟨(((z : L) : H) : P), SP.le_normalizer hzSP⟩
    let zSN : SN := ⟨zN, hzSP⟩
    have hx := MulAction.mem_fixedPoints.mp x.prop zSN
    exact hx
  let i : alternatingGroup Y →* Equiv.Perm F :=
    Equiv.Perm.ofSubtype.comp (alternatingGroup Y).subtype
  have hi : Function.Injective i :=
    Equiv.Perm.ofSubtype_injective.comp
      (alternatingGroup Y).subtype_injective
  have hiRange : i.range ≤ phi.range := by
    rintro q ⟨a, rfl⟩
    have hiAlt : i a ∈ alternatingGroup F := by
      rw [Equiv.Perm.mem_alternatingGroup]
      change Equiv.Perm.sign
          (Equiv.Perm.ofSubtype (a : Equiv.Perm Y)) = 1
      rw [Equiv.Perm.sign_ofSubtype]
      exact a.prop
    obtain ⟨n, hn⟩ := hAlt hiAlt
    have hnH : ((n : N) : P) ∈ H := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      let xF : F := ⟨x, hsF hx⟩
      have happ := congrArg (fun q : Equiv.Perm F ↦ q xF) hn
      have hxNotY : xF ∉ Y := by
        simp [Y, sF, xF, hx]
      have hiFix : i a xF = xF := by
        change Equiv.Perm.ofSubtype (a : Equiv.Perm Y) xF = xF
        exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hxNotY
      have happ' := congrArg Subtype.val (happ.trans hiFix)
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at happ'
      rw [coe_smul_fixedPoints_of_normal] at happ'
      simpa [rho, xF, Subgroup.smul_def,
        Equiv.Perm.smul_def] using happ'
    let l : L := ⟨⟨((n : N) : P), hnH⟩, n.prop⟩
    refine ⟨l, ?_⟩
    apply Equiv.ext
    intro x
    have happ := congrArg (fun q : Equiv.Perm F ↦ q x) hn
    simpa [phi, rho, toN, l] using happ
  constructor
  · intro hpTwo
    subst p
    exact alternating_degree_le_three_for_sylow_two
      SL phi hSLker Y i hi hiRange
  · intro hpTwo
    exact alternating_degree_lt_odd_sylow_prime
      SL phi hSLker Y i hi hiRange hpTwo

theorem fixed_card_bound_of_alternating_normalizer_action
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X) (hs : s.ncard = 5)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup P s))
    (hAlt :
      let N := sylowNormalizer X P s S
      let F := sylowFixedPoints X P s S
      let _ : Fintype F := Fintype.ofFinite F
      alternatingGroup F ≤
        (MulAction.toPermHom N F).range) :
    let F := sylowFixedPoints X P s S
    let _ : Fintype F := Fintype.ofFinite F
    (p = 2 → Fintype.card F ≤ 8) ∧
      (p ≠ 2 → Fintype.card F - 5 < p) := by
  classical
  let F := sylowFixedPoints X P s S
  let : Fintype F := Fintype.ofFinite F
  let sF : Set F := {x | (x : X) ∈ s}
  let Y := (sFᶜ : Set F)
  let : Fintype Y := Fintype.ofFinite Y
  have hsF : s ⊆ (F : Set X) := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.prop
    have hfix := (mem_fixingSubgroup_iff P).mp u.prop x hx
    change
      (((z : sylowInNormalizer X P s S) :
          sylowNormalizer X P s S) : P) • x = x
    rw [show
      (((z : sylowInNormalizer X P s S) :
          sylowNormalizer X P s S) : P) =
        (u : fixingSubgroup P s) by exact hu.symm]
    exact hfix
  let e : s ≃ sF :=
    { toFun := fun x ↦ ⟨⟨x.1, hsF x.2⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsFcard : Fintype.card sF = 5 := by
    calc
      Fintype.card sF = Fintype.card s := Fintype.card_congr e.symm
      _ = s.ncard := by rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      _ = 5 := hs
  have hYcard : Fintype.card Y = Fintype.card F - 5 := by
    change Fintype.card (sFᶜ : Set F) = Fintype.card F - 5
    rw [Fintype.card_compl_set, hsFcard]
  have hb :=
    fixed_complement_bound_of_alternating_normalizer_action
      X P s hs S hAlt
  change
    (p = 2 → Fintype.card F ≤ 8) ∧
      (p ≠ 2 → Fintype.card F - 5 < p)
  constructor
  · intro hpTwo
    have hY := hb.1 hpTwo
    rw [hYcard] at hY
    omega
  · intro hpTwo
    have hY := hb.2 hpTwo
    change Fintype.card Y < p at hY
    rwa [hYcard] at hY

end FiveTransitive.SylowFixedActionCore

end CFSG
