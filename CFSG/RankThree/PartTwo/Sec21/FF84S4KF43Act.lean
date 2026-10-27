module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4KF43Layer

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG
open CFSG.Assembly (InCatalog)
open CFSG.Assembly.RankThreeEven (localRank)

abbrev KF43CompSet (Q : Type) [Group Q] : Type := {L : Subgroup Q // IsComponent L}

variable {Q : Type} [Group Q] {P : Type} [Group P]

@[expose] def kf43CompMap (α : MulAut Q) (L : KF43CompSet Q) : KF43CompSet Q :=
  ⟨L.1.map α.toMonoidHom, ((CFSG.LocalCores.component_isomorphism α).1 L.1).1 L.2⟩

@[expose, instance_reducible] def kf43CompAction (φ : P →* MulAut Q) : MulAction P (KF43CompSet Q) where
  smul p L := kf43CompMap (φ p) L
  one_smul L := Subtype.ext (Subgroup.ext fun x => by
    show x ∈ L.1.map (φ 1).toMonoidHom ↔ x ∈ L.1
    simp [Subgroup.mem_map])
  mul_smul p q L := Subtype.ext (Subgroup.ext fun x => by
    show x ∈ L.1.map (φ (p * q)).toMonoidHom ↔ x ∈ (L.1.map (φ q).toMonoidHom).map (φ p).toMonoidHom
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, map_mul, MulAut.mul_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ q y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩)

theorem kf43_comp_stable [Finite Q] (hcard : Nat.card (KF43CompSet Q) ≤ 4) (hP : Group.IsPerfect P)
    (φ : P →* MulAut Q) (p : P) (L : KF43CompSet Q) :
    L.1.map (φ p).toMonoidHom = L.1 := by
  letI := kf43CompAction φ
  haveI := hP
  let ψ : P →* Equiv.Perm (KF43CompSet Q) := MulAction.toPermHom P (KF43CompSet Q)
  haveI : Finite (KF43CompSet Q) := inferInstance
  have hsolv : Group.IsSolvable (Equiv.Perm (KF43CompSet Q)) := Equiv.Perm.isSolvable hcard
  haveI : Group.IsSolvable ψ.range := inferInstance
  haveI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hψ : ψ p = 1 := by
    rcases subsingleton_or_nontrivial ψ.range with hs | hn
    · exact congrArg Subtype.val (Subsingleton.elim (⟨ψ p, ψ.mem_range.2 ⟨p, rfl⟩⟩ : ψ.range) 1)
    · exact ((Group.IsPerfect.not_isSolvable ψ.range) inferInstance).elim
  have : p • L = L := by
    have := congrArg (fun f : Equiv.Perm (KF43CompSet Q) => f L) hψ
    simpa [ψ] using this
  exact congrArg Subtype.val this

theorem kf43_stab_mem (φ : P →* MulAut Q) {L : Subgroup Q} (h : ∀ p, L.map (φ p).toMonoidHom = L)
    (p : P) {x : Q} (hx : x ∈ L) : φ p x ∈ L := by
  have := Subgroup.mem_map_of_mem (φ p).toMonoidHom hx
  rwa [h p] at this

@[expose] def kf43RestrictAut (φ : P →* MulAut Q) (L : Subgroup Q) (h : ∀ p, L.map (φ p).toMonoidHom = L) :
    P →* MulAut L where
  toFun p :=
    { toFun := fun x => ⟨φ p x, kf43_stab_mem φ h p x.2⟩
      invFun := fun x => ⟨φ p⁻¹ x, kf43_stab_mem φ h p⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (by
        show (φ p⁻¹) ((φ p) (x : Q)) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv := fun x => Subtype.ext (by
        show (φ p) ((φ p⁻¹) (x : Q)) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl)
      map_mul' := fun x y => Subtype.ext (map_mul (φ p) (x : Q) (y : Q)) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    show (φ 1) (x : Q) = x
    rw [map_one]
    rfl)
  map_mul' p q := MulEquiv.ext fun x => Subtype.ext (by
    show (φ (p * q)) (x : Q) = (φ p) ((φ q) (x : Q))
    rw [map_mul]
    rfl)

theorem kf43_restrictAut_apply (φ : P →* MulAut Q) (L : Subgroup Q)
    (h : ∀ p, L.map (φ p).toMonoidHom = L) (p : P) (x : L) :
    ((kf43RestrictAut φ L h p x : L) : Q) = φ p x := rfl

theorem kf43_action_trivial_of_radical_free [Finite Q] (hSz : LemmaSz) (hrad : solvableRadical Q = ⊥)
    (hK : KCore.KGroupNonab InCatalog Q) (h3 : ¬ 3 ∣ Nat.card Q)
    (hrank : localRank 5 ↥(layer Q) ≤ 2)
    (hAut : ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup H → (∃ x y : H, x * y ≠ y * x) →
      KCore.KGroupNonab InCatalog H → ¬ 3 ∣ Nat.card H →
      ∀ (P : Type) [Group P] [Finite P], Group.IsPerfect P →
        IsSimpleGroup (P ⧸ Subgroup.center P) →
        (∃ x y : P ⧸ Subgroup.center P, x * y ≠ y * x) →
        3 ∣ Nat.card (P ⧸ Subgroup.center P) → ∀ φ : P →* MulAut H, φ = 1)
    [Finite P] (hPp : Group.IsPerfect P) (hPs : IsSimpleGroup (P ⧸ Subgroup.center P))
    (hPn : ∃ x y : P ⧸ Subgroup.center P, x * y ≠ y * x)
    (hP3 : 3 ∣ Nat.card (P ⧸ Subgroup.center P)) (φ : P →* MulAut Q) : φ = 1 := by
  have hcard : Nat.card (KF43CompSet Q) ≤ 4 := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    haveI : Fintype (KF43CompSet Q) := Fintype.ofFinite _
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := KF43CompSet Q)
      (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
    have hne : ∀ i j, i ≠ j → (e i).1 ≠ (e j).1 := fun i j hij h =>
      hij (e.injective (Subtype.ext h))
    have := kf43_three_le_localRank_layer hSz hrad hK h3 (e 0).2 (e 1).2 (e 2).2 (e 3).2
      (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
      (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide))
    omega
  have stab := kf43_comp_stable hcard hPp φ
  have hfixL : ∀ (p : P) (L : KF43CompSet Q), ∀ x ∈ L.1, φ p x = x := by
    intro p L x hx
    obtain ⟨hs, hn, -⟩ := kf43_comp_isSimple hrad L.2
    have h3L : ¬ 3 ∣ Nat.card L.1 := fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card L.1))
    have h1 := hAut L.1 hs hn (KCore.KGroupNonab.subgroup Assembly.inCatalog_isoInvariant hK L.1)
      h3L P hPp hPs hPn hP3 (kf43RestrictAut φ L.1 (fun p => stab p L))
    have e1 : ((kf43RestrictAut φ L.1 (fun p => stab p L) p ⟨x, hx⟩ : L.1) : Q) = x := by
      rw [h1]
      rfl
    exact (kf43_restrictAut_apply φ L.1 (fun p => stab p L) p ⟨x, hx⟩).symm.trans e1
  have hfixE : ∀ (p : P), ∀ x ∈ layer Q, φ p x = x := by
    intro p
    have hle : layer Q ≤ MonoidHom.eqLocus (φ p).toMonoidHom (MonoidHom.id Q) :=
      sSup_le fun K hK x hx => hfixL p ⟨K, hK⟩ x hx
    exact fun x hx => hle hx
  obtain ⟨hF, hFL⟩ := CFSG.LocalAnalysis.radical_free_generalized_fitting_layer hrad
  have hN : (layer Q).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Q)
    infer_instance
  refine MonoidHom.ext fun p => MulEquiv.ext fun x => ?_
  have hz : x⁻¹ * φ p x ∈ Subgroup.centralizer ((generalizedFitting Q : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    rw [hFL] at he
    have h1 : φ p x * e * (φ p x)⁻¹ = x * e * x⁻¹ := by
      have := hfixE p _ (hN.conj_mem e he x)
      simpa [map_mul, map_inv, hfixE p e he] using this
    calc e * (x⁻¹ * φ p x) = x⁻¹ * (x * e * x⁻¹) * φ p x := by group
      _ = x⁻¹ * (φ p x * e * (φ p x)⁻¹) * φ p x := by rw [h1]
      _ = x⁻¹ * φ p x * e := by group
  have h2 := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup Q hz
  rw [hF, Subgroup.mem_bot] at h2
  have : φ p x = x := by
    have := congrArg (fun z => x * z) h2
    simpa using this
  simpa using this

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
