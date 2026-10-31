module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.GenericSylowFixedAction

open MulAction SubMulAction Subgroup
open FiveTransitive.SylowFixedActionCore

abbrev sylowImage
    (G X : Type) [Group G] [MulAction G X] (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup G s)) : Subgroup G :=
  (S : Subgroup (fixingSubgroup G s)).map
    (fixingSubgroup G s).subtype

abbrev sylowNormalizer
    (G X : Type) [Group G] [MulAction G X] (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup G s)) : Subgroup G :=
  Subgroup.normalizer (sylowImage G X s S : Set G)

abbrev sylowInNormalizer
    (G X : Type) [Group G] [MulAction G X] (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup G s)) :
    Subgroup (sylowNormalizer G X s S) :=
  (sylowImage G X s S).subgroupOf
    (sylowNormalizer G X s S)

abbrev sylowFixedPoints
    (G X : Type) [Group G] [MulAction G X] (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup G s)) :=
  MulAction.fixedPoints (sylowInNormalizer G X s S) X

theorem sylowNormalizer_transitive_on_fixedPoints
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] (k : ℕ)
    (hk : ∀ a b : Fin k → X, Function.Injective a →
      Function.Injective b →
      ∃ q : G, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = k)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G s)) :
    ∀ a b : Fin k → sylowFixedPoints G X s S,
      Function.Injective a →
      Function.Injective b →
      ∃ c : sylowNormalizer G X s S,
        ∀ i, c • a i = b i := by
  classical
  let H : Subgroup G := fixingSubgroup G s
  let SP : Subgroup G := sylowImage G X s S
  let N : Subgroup G := sylowNormalizer G X s S
  let SN : Subgroup N := sylowInNormalizer G X s S
  let F := MulAction.fixedPoints SN X
  change
    ∀ a b : Fin k → F, Function.Injective a →
      Function.Injective b →
      ∃ c : N, ∀ i, c • a i = b i
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
    hk aX bX aX.injective bX.injective
  let t : Set X := Set.range bX
  have ht : t.ncard = k := by
    rw [Set.ncard_range_of_injective bX.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let Ht : Subgroup G := fixingSubgroup G t
  have hHcard : Nat.card H = Nat.card Ht := by
    have htrans := FiveTransitive.isMultiplyPretransitive_of_explicit G X k hk
    have hsIndex := htrans.index_of_fixingSubgroup_mul hs
    have htIndex := htrans.index_of_fixingSubgroup_mul ht
    have hindices : H.index = Ht.index := by
      change (fixingSubgroup G s).index = (fixingSubgroup G t).index
      exact Nat.eq_of_mul_eq_mul_right
        (Nat.factorial_pos (Nat.card X - k)) (hsIndex.trans htIndex.symm)
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
  let QSP : Subgroup G :=
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
        (w : G) • (a i).1 = (a i).1 :=
      MulAction.mem_fixedPoints.mp
        (a i).2 wSN
    calc
      (MulAut.conj q w : G) • bX i =
          q • ((w : G) • (q⁻¹ • bX i)) := by
        simp only [MulAut.conj_apply, mul_smul]
      _ = q • ((w : G) • aX i) := by
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
  let kP : G := k
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
        (MulAut.conj kP z : G) ∈ SP
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
  let cP : G := kP * q
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
        (mem_fixingSubgroup_iff G).mp
          k.prop (bX i) ⟨i, rfl⟩

theorem base_subset_fixedPoints
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] (s : Set X)
    {p : ℕ} (S : Sylow p (fixingSubgroup G s)) :
    s ⊆ (sylowFixedPoints G X s S : Set X) := by
  intro x hx
  rw [MulAction.mem_fixedPoints]
  intro z
  obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.prop
  have hfix := (mem_fixingSubgroup_iff G).mp u.prop x hx
  change ((z : sylowNormalizer G X s S) : G) • x = x
  rw [show ((z : sylowNormalizer G X s S) : G) =
    (u : fixingSubgroup G s) by exact hu.symm]
  exact hfix

theorem prime_not_dvd_fixedAction_stabilizer_card
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] (s : Set X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G s)) :
    let N := sylowNormalizer G X s S
    let F := sylowFixedPoints G X s S
    let J := (MulAction.toPermHom N F).range
    let sF : Set F := {x | (x : X) ∈ s}
    ¬ p ∣ Nat.card (fixingSubgroup J sF) := by
  classical
  let H : Subgroup G := fixingSubgroup G s
  let SP : Subgroup G := sylowImage G X s S
  let N : Subgroup G := sylowNormalizer G X s S
  let SN : Subgroup N := sylowInNormalizer G X s S
  let F := sylowFixedPoints G X s S
  let rho : N →* Equiv.Perm F := MulAction.toPermHom N F
  let J : Subgroup (Equiv.Perm F) := rho.range
  let sF : Set F := {x | (x : X) ∈ s}
  let K : Subgroup J := fixingSubgroup J sF
  let L : Subgroup H := N.comap H.subtype
  let toN : L →* N :=
    { toFun := fun z ↦ ⟨((z : L) : H), z.prop⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let phi : L →* Equiv.Perm F := rho.comp toN
  have hsF : s ⊆ (F : Set X) := base_subset_fixedPoints G X s S
  have hSL : (S : Subgroup H) ≤ L := by
    intro z hz
    change ((z : H) : G) ∈ N
    exact SP.le_normalizer (Subgroup.mem_map_of_mem H.subtype hz)
  let SL : Sylow p L := S.subtype hSL
  have hSLker : (SL : Subgroup L) ≤ phi.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hzSP : (((z : L) : H) : G) ∈ SP :=
      Subgroup.mem_map_of_mem H.subtype hz
    let zN : N := ⟨(((z : L) : H) : G), SP.le_normalizer hzSP⟩
    let zSN : SN := ⟨zN, hzSP⟩
    exact MulAction.mem_fixedPoints.mp x.prop zSN
  let i : K →* Equiv.Perm F := J.subtype.comp K.subtype
  have hi : Function.Injective i :=
    J.subtype_injective.comp K.subtype_injective
  have hiRange : i.range ≤ phi.range := by
    rintro q ⟨a, rfl⟩
    obtain ⟨n, hn⟩ := a.val.property
    have hnH : ((n : N) : G) ∈ H := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      let xF : F := ⟨x, hsF hx⟩
      have happ := congrArg (fun q : Equiv.Perm F ↦ q xF) hn
      have hiFix : i a xF = xF :=
        (mem_fixingSubgroup_iff J).mp a.property xF hx
      have happ' := congrArg Subtype.val (happ.trans hiFix)
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at happ'
      rw [coe_smul_fixedPoints_of_normal] at happ'
      simpa [rho, xF, Subgroup.smul_def, Equiv.Perm.smul_def] using happ'
    let l : L := ⟨⟨((n : N) : G), hnH⟩, n.prop⟩
    refine ⟨l, ?_⟩
    apply Equiv.ext
    intro x
    have happ := congrArg (fun q : Equiv.Perm F ↦ q x) hn
    simpa [phi, rho, toN, l, i] using happ
  have hcardRange : Nat.card i.range = Nat.card K :=
    Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm
  change ¬ p ∣ Nat.card K
  intro hp
  apply prime_not_dvd_range_card_of_sylow_le_ker SL phi hSLker
  exact hp.trans (by
    rw [← hcardRange]
    exact Subgroup.card_dvd_of_le hiRange)

theorem fixed_degree_modEq
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] (s : Set X)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G s)) :
    Nat.card X ≡ Nat.card (sylowFixedPoints G X s S) [MOD p] := by
  let H : Subgroup G := fixingSubgroup G s
  let SP : Subgroup G := sylowImage G X s S
  let N : Subgroup G := sylowNormalizer G X s S
  let SN : Subgroup N := sylowInNormalizer G X s S
  have hSP : IsPGroup p SP := S.isPGroup'.map H.subtype
  let e : SN ≃* SP := Subgroup.subgroupOfEquivOfLe SP.le_normalizer
  have hSN : IsPGroup p SN := hSP.of_injective e.toMonoidHom e.injective
  exact hSN.card_modEq_card_fixedPoints X

theorem base_card_le_fixed_degree
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] (s : Set X)
    {p : ℕ} (S : Sylow p (fixingSubgroup G s)) :
    s.ncard ≤ Nat.card (sylowFixedPoints G X s S) := by
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (base_subset_fixedPoints G X s S)

end FiveTransitive.GenericSylowFixedAction

end CFSG
