module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSylowNormalizer
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Transfer

namespace CFSG
end CFSG
open CFSG

/-!
# Counting the three Dickson families

This module isolates the unique-family orbit counts and the Huppert II.8.22
counting equation.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u v

private theorem huppert_II_8_22_punctured_subgroup_card
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) :
    Nat.card {x : A // (x : H) ≠ 1} = Nat.card A - 1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype {x : A // (x : H) ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

private theorem huppert_II_8_22_conjugacy_orbit_card
    {H : Type*} [Group H] [Finite H] (A : Subgroup H) :
    Nat.card {W : Subgroup H // ∃ g : H,
      W = A.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (A : Set H)).index := by
  classical
  let : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
  have horbit :
      MulAction.orbit H A =
        {W : Subgroup H | ∃ g : H,
          W = A.map (MulAut.conj g).toMonoidHom} := by
    ext W
    constructor
    · intro hW
      rcases hW with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hstab : MulAction.stabilizer H A =
      Subgroup.normalizer (A : Set H) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set H)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := H) (H := Subgroup.normalizer A),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact
      forall_congr' fun h =>
        iff_congr Iff.rfl
          ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
            fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
              MulAut.apply_inv_self H (MulAut.conj g) h⟩⟩
  change Nat.card ↥{W : Subgroup H | ∃ g : H,
    W = A.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer H A, hstab]

public theorem huppert_II_8_22_partition_count_of_unique_family
    {H : Type*} [Group H] [Finite H] {p m r : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (hunique : ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H)) :
    Nat.card H =
      1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by
  classical
  let Family := (Sylow p H) ⊕
    (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
      W = (Z i).map (MulAut.conj g).toMonoidHom})
  let carrier : Family → Subgroup H := fun A =>
    match A with
    | Sum.inl Q => (Q : Subgroup H)
    | Sum.inr z => (z.2.1 : Subgroup H)
  have hunique' : ∀ x : H, x ≠ 1 → ∃! A : Family, x ∈ carrier A := by
    intro x hx
    exact hunique x hx
  let Piece := Σ A : Family, {x : carrier A // (x : H) ≠ 1}
  let decode : Unit ⊕ Piece → H := fun z =>
    match z with
    | Sum.inl _ => 1
    | Sum.inr y => (y.2.1 : H)
  have hdecode_bij : Function.Bijective decode := by
    constructor
    · intro a b hab
      rcases a with _ | a
      · rcases b with _ | b
        · rfl
        · exfalso
          exact b.2.2 (by simpa [decode] using hab.symm)
      · rcases b with _ | b
        · exfalso
          exact a.2.2 (by simpa [decode] using hab)
        · rcases a with ⟨A, x⟩
          rcases b with ⟨B, y⟩
          have hxy : (x.1 : H) = (y.1 : H) := by
            simpa [decode] using hab
          have hAB : A = B := by
            apply (hunique' (x.1 : H) x.2).unique
            · exact x.1.2
            · rw [hxy]
              exact y.1.2
          subst B
          have hxy' : x = y := by
            apply Subtype.ext
            apply Subtype.ext
            exact hxy
          subst y
          rfl
    · intro x
      by_cases hx : x = 1
      · exact ⟨Sum.inl (), by simp [decode, hx]⟩
      · obtain ⟨A, hxA⟩ := (hunique' x hx).exists
        refine ⟨Sum.inr ⟨A, ⟨⟨x, hxA⟩, hx⟩⟩, ?_⟩
        rfl
  let e : Unit ⊕ Piece ≃ H := Equiv.ofBijective decode hdecode_bij
  have hcard_decomp : Nat.card H = 1 + Nat.card Piece := by
    calc
      Nat.card H = Nat.card (Unit ⊕ Piece) := (Nat.card_congr e).symm
      _ = Nat.card Unit + Nat.card Piece := Nat.card_sum
      _ = 1 + Nat.card Piece := by rw [Nat.card_unique]
  have hSylow_card (Q : Sylow p H) : Nat.card Q = p ^ m := by
    calc
      Nat.card Q = Nat.card P := Nat.card_congr (Sylow.equiv Q P).toEquiv
      _ = p ^ m := hPcard
  have hConj_card (i : Fin r) :
      Nat.card {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom} =
        (Subgroup.normalizer (Z i : Set H)).index :=
    huppert_II_8_22_conjugacy_orbit_card (Z i)
  have hConj_subgroup_card (i : Fin r)
      (W : {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}) :
      Nat.card W.1 = Nat.card (Z i) := by
    rcases W.2 with ⟨g, hg⟩
    rw [hg]
    exact Nat.card_congr ((MulAut.conj g).subgroupMap (Z i)).toEquiv.symm
  let PPiece := Σ Q : Sylow p H,
    {x : (Q : Subgroup H) // (x : H) ≠ 1}
  let ZIndex := Σ i : Fin r, {W : Subgroup H // ∃ g : H,
    W = (Z i).map (MulAut.conj g).toMonoidHom}
  let ZPiece := Σ z : ZIndex,
    {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}
  have hPpiece_card :
      Nat.card PPiece = Nat.card (Sylow p H) * (p ^ m - 1) := by
    let : Fintype (Sylow p H) := Fintype.ofFinite (Sylow p H)
    let (Q : Sylow p H) :
        Fintype {x : (Q : Subgroup H) // (x : H) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ Q : Sylow p H,
      {x : (Q : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Nat.card_sigma]
    simp_rw [huppert_II_8_22_punctured_subgroup_card, hSylow_card]
    simp
  have hZpiece_card :
      Nat.card ZPiece =
        ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom} *
          (Nat.card (Z i) - 1) := by
    let (i : Fin r) :
        Fintype {W : Subgroup H // ∃ g : H,
          W = (Z i).map (MulAut.conj g).toMonoidHom} :=
      Fintype.ofFinite _
    let : Fintype ZIndex := inferInstance
    let (z : ZIndex) :
        Fintype {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ z :
      (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}),
      {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Nat.card_sigma]
    change (∑ z :
      (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g).toMonoidHom}),
      Nat.card {x : (z.2.1 : Subgroup H) // (x : H) ≠ 1}) = _
    rw [Fintype.sum_sigma]
    simp_rw [huppert_II_8_22_punctured_subgroup_card,
      hConj_subgroup_card]
    simp
    apply Finset.sum_congr rfl
    intro i hi
    let : Fintype {W : Subgroup H // ∃ g : H,
        W = (Z i).map (MulAut.conj g)} :=
      Fintype.ofFinite _
    apply congrArg (fun n => n * (Nat.card (Z i) - 1))
    exact Nat.card_eq_fintype_card.symm
  have hPiece_card :
      Nat.card Piece =
        Nat.card (Sylow p H) * (p ^ m - 1) +
          ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
              W = (Z i).map (MulAut.conj g).toMonoidHom} *
            (Nat.card (Z i) - 1) := by
    have hsplit : Nat.card Piece = Nat.card PPiece + Nat.card ZPiece := by
      let esplit := Equiv.sumSigmaDistrib
        (fun A : Family => {x : carrier A // (x : H) ≠ 1})
      calc
        Nat.card Piece = Nat.card (PPiece ⊕ ZPiece) := by
          simpa [Piece, PPiece, ZPiece, ZIndex, Family, carrier] using
            Nat.card_congr esplit
        _ = Nat.card PPiece + Nat.card ZPiece := Nat.card_sum
    rw [hsplit, hPpiece_card, hZpiece_card]
  calc
    Nat.card H = 1 + Nat.card Piece := hcard_decomp
    _ = 1 +
        (Nat.card (Sylow p H) * (p ^ m - 1) +
          ∑ i, Nat.card {W : Subgroup H // ∃ g : H,
              W = (Z i).map (MulAut.conj g).toMonoidHom} *
            (Nat.card (Z i) - 1)) := by rw [hPiece_card]
    _ = 1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by
      rw [P.card_eq_index_normalizer]
      simp_rw [hConj_card]
      ac_rfl

/-- The subgroup form of the unique partition used in Huppert II.8.22. -/
public theorem huppert_II_8_22_unique_family
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (_hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) :
    ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H) := by
  classical
  let : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
  let P0 : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P0
  have hmap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) (g : PSL2MatrixGroup F) :
      IsCyclic (A.map (MulAut.conj g).toMonoidHom) := by
    let : IsCyclic A := hA
    let e := (MulAut.conj g).subgroupMap A
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hcyclic_le_family
      {x : PSL2MatrixGroup F} (hx : x ≠ 1)
      {T V : Subgroup (PSL2MatrixGroup F)}
      (hxT : x ∈ T)
      (hTfamily :
        (∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = S.map (MulAut.conj g).toMonoidHom))
      (hxV : x ∈ V) (hVcyclic : IsCyclic V) : V ≤ T := by
    let : IsCyclic V := hVcyclic
    rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
    have hv_ne : (v : PSL2MatrixGroup F) ≠ 1 := by
      intro hv_one
      obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
      have hnval : (v ^ n : V) = ⟨x, hxV⟩ := hn
      have hnval' := congrArg Subtype.val hnval
      change ((v : PSL2MatrixGroup F) ^ n) = x at hnval'
      simp [hv_one] at hnval'
      exact hx hnval'.symm
    obtain ⟨Tv, hvTv, _hTv_unique⟩ :=
      hpartition (v : PSL2MatrixGroup F) hv_ne
    have hxTv : x ∈ Tv := by
      obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
      have hnval : (v : PSL2MatrixGroup F) ^ n = x :=
        congrArg Subtype.val hn
      have hvpow : (v : PSL2MatrixGroup F) ^ n ∈ Tv :=
        Tv.zpow_mem hvTv.1 n
      rwa [hnval] at hvpow
    have hTvT : Tv = T :=
      (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
    intro y hyV
    obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
    have hnval : (v : PSL2MatrixGroup F) ^ n = y :=
      congrArg Subtype.val hn
    have hypow : (v : PSL2MatrixGroup F) ^ n ∈ Tv :=
      Tv.zpow_mem hvTv.1 n
    rw [hTvT, hnval] at hypow
    exact hypow
  have hmap_cyclic_H (A : Subgroup H) (hA : IsCyclic A) (g : H) :
      IsCyclic (g • A : Subgroup H) := by
    change IsCyclic (A.map (MulAut.conj g).toMonoidHom)
    let : IsCyclic A := hA
    let e := (MulAut.conj g).subgroupMap A
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hconj_maximal (i : Fin r) (g : H) :
      ∀ V : Subgroup H, IsCyclic V →
        (g • Z i : Subgroup H) ≤ V → V = (g • Z i : Subgroup H) := by
    intro V hV hle
    have hback_cyclic : IsCyclic (g⁻¹ • V : Subgroup H) :=
      hmap_cyclic_H V hV g⁻¹
    have hback_le : Z i ≤ (g⁻¹ • V : Subgroup H) := by
      have hmap := Subgroup.map_mono
        (f := (MulAut.conj g⁻¹).toMonoidHom) hle
      change (g⁻¹ • (g • Z i) : Subgroup H) ≤
        (g⁻¹ • V : Subgroup H) at hmap
      simpa using hmap
    have heq : (g⁻¹ • V : Subgroup H) = Z i :=
      hmaximal i (g⁻¹ • V : Subgroup H) hback_cyclic hback_le
    have hfront := congrArg (fun W : Subgroup H => g • W) heq
    simpa using hfront
  have hindices_eq (i j : Fin r) (g h : H)
      (heq :
        (Z i).map (MulAut.conj g).toMonoidHom =
          (Z j).map (MulAut.conj h).toMonoidHom) : i = j := by
    have hcancel :
        ((Z i).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj h).symm.toMonoidHom = Z j :=
      (Subgroup.map_symm_eq_iff_map_eq
        (Z j) (e := MulAut.conj h)).mpr heq.symm
    have hsingle :
        (Z i).map (MulAut.conj (h⁻¹ * g)).toMonoidHom = Z j := by
      calc
        (Z i).map (MulAut.conj (h⁻¹ * g)).toMonoidHom =
            ((Z i).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj h).symm.toMonoidHom := by
                rw [Subgroup.map_map]
                congr 1
                ext y
                simp [MulAut.conj_apply, mul_assoc]
        _ = Z j := hcancel
    exact hdistinct i j (h⁻¹ * g) hsingle
  have hsylow_coprime_conj (Q : Sylow p H) (i : Fin r) (g : H) :
      Nat.Coprime (Nat.card Q) (Nat.card (g • Z i : Subgroup H)) := by
    rcases Q.isPGroup'.exists_card_eq with ⟨n, hQcard⟩
    rw [hQcard]
    change Nat.Coprime (p ^ n)
      (Nat.card ((Z i).map (MulAut.conj g).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact (hcoprime i).pow_left n
  have hmap_subtype_cyclic (A : Subgroup H) (hA : IsCyclic A) :
      IsCyclic (A.map H.subtype) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        A H.subtype H.subtype_injective)).mp hA
  have hcomap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) : IsCyclic (A.comap H.subtype) := by
    let : IsCyclic A := hA
    have hmap_cyclic : IsCyclic ((A.comap H.subtype).map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le H.subtype A)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        (A.comap H.subtype) H.subtype H.subtype_injective)).mpr hmap_cyclic
  have hcomap_card_dvd (A : Subgroup (PSL2MatrixGroup F)) :
      Nat.card (A.comap H.subtype) ∣ Nat.card A :=
    Subgroup.card_comap_dvd_of_injective
      A H.subtype H.subtype_injective
  intro x hx
  have hxG : (x : PSL2MatrixGroup F) ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    exact h
  obtain ⟨T, hxT, hTfamily⟩ :=
    (hpartition (x : PSL2MatrixGroup F) hxG).exists
  have hambient_sylow_family (R : Sylow p (PSL2MatrixGroup F)) :
      ∃ g, (R : Subgroup (PSL2MatrixGroup F)) =
        (P0 : Subgroup (PSL2MatrixGroup F)).map
          (MulAut.conj g).toMonoidHom := by
    obtain ⟨g, hg⟩ :=
      MulAction.exists_smul_eq (PSL2MatrixGroup F) P0 R
    refine ⟨g, ?_⟩
    have hg' := congrArg
      (fun Q : Sylow p (PSL2MatrixGroup F) =>
        (Q : Subgroup (PSL2MatrixGroup F))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hg'
    exact hg'.symm
  have hambient_eq_T (R : Sylow p (PSL2MatrixGroup F))
      (hxR : (x : PSL2MatrixGroup F) ∈
        (R : Subgroup (PSL2MatrixGroup F))) :
      (R : Subgroup (PSL2MatrixGroup F)) = T := by
    exact (hpartition (x : PSL2MatrixGroup F) hxG).unique
      ⟨hxR, Or.inl (hambient_sylow_family R)⟩
      ⟨hxT, hTfamily⟩
  have hsylow_eq_of_mem (Q₁ Q₂ : Sylow p H)
      (hx₁ : x ∈ (Q₁ : Subgroup H))
      (hx₂ : x ∈ (Q₂ : Subgroup H)) : Q₁ = Q₂ := by
    obtain ⟨R₁, hR₁⟩ := Q₁.exists_comap_subtype_eq
    obtain ⟨R₂, hR₂⟩ := Q₂.exists_comap_subtype_eq
    have hxR₁ : (x : PSL2MatrixGroup F) ∈
        (R₁ : Subgroup (PSL2MatrixGroup F)) := by
      change x ∈ (R₁ : Subgroup _).comap H.subtype
      rw [hR₁]
      exact hx₁
    have hxR₂ : (x : PSL2MatrixGroup F) ∈
        (R₂ : Subgroup (PSL2MatrixGroup F)) := by
      change x ∈ (R₂ : Subgroup _).comap H.subtype
      rw [hR₂]
      exact hx₂
    apply Sylow.ext
    calc
      (Q₁ : Subgroup H) = (R₁ : Subgroup _).comap H.subtype := hR₁.symm
      _ = T.comap H.subtype := congrArg
        (fun W : Subgroup (PSL2MatrixGroup F) => W.comap H.subtype)
        (hambient_eq_T R₁ hxR₁)
      _ = (R₂ : Subgroup _).comap H.subtype := congrArg
        (fun W : Subgroup (PSL2MatrixGroup F) => W.comap H.subtype)
        (hambient_eq_T R₂ hxR₂).symm
      _ = (Q₂ : Subgroup H) := hR₂
  rcases hTfamily with ⟨g, hTg⟩ | hTtorus
  · have hTp : IsPGroup p T := by
      rw [hTg]
      exact P0.isPGroup'.map (MulAut.conj g).toMonoidHom
    let I : Subgroup H := T.comap H.subtype
    have hIp : IsPGroup p I := hTp.comap_subtype
    obtain ⟨Q, hIQ⟩ := hIp.exists_le_sylow
    have hxI : x ∈ I := by
      change (x : PSL2MatrixGroup F) ∈ T
      exact hxT
    refine ⟨Sum.inl Q, hIQ hxI, ?_⟩
    intro A hA
    rcases A with Q' | z
    · exact congrArg Sum.inl (hsylow_eq_of_mem Q' Q hA (hIQ hxI))
    · rcases z with ⟨i, W, g', hW⟩
      exfalso
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) := by
        rw [hW]
        exact hsylow_coprime_conj Q i g'
      exact hx (hmem_eq_one_of_coprime_card
        (Q : Subgroup H) W hcop (hIQ hxI) hA)
  · have hTfamily' :
        ((∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) :=
      Or.inr hTtorus
    have hTcyclic : IsCyclic T := by
      rcases hTtorus with ⟨g, hg⟩ | ⟨g, hg⟩
      · rw [hg]
        exact hmap_cyclic U hUcyclic g
      · rw [hg]
        exact hmap_cyclic S hScyclic g
    have hpF : p ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self p
        (huppert_II_8_27_field_exponent_ne_zero hFcard)
    have hFTcoprime : Nat.Coprime (Nat.card F) (Nat.card T) := by
      rcases hTtorus with ⟨g, hg⟩ | ⟨g, hg⟩
      · rw [hg, Subgroup.card_map_of_injective
            (K := U) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective, hUcard]
        exact hq_coprime_split_order (Nat.card F) Nat.card_pos
      · rw [hg, Subgroup.card_map_of_injective
            (K := S) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective, hScard]
        exact hq_coprime_nonsplit_order (Nat.card F) Nat.card_pos
    have hTcoprime : Nat.Coprime p (Nat.card T) :=
      Nat.Coprime.of_dvd_left hpF hFTcoprime
    let W : Subgroup H := T.comap H.subtype
    have hxW : x ∈ W := by
      change (x : PSL2MatrixGroup F) ∈ T
      exact hxT
    have hWcyclic : IsCyclic W := hcomap_cyclic T hTcyclic
    have hWcard : 1 < Nat.card W := by
      apply (Subgroup.one_lt_card_iff_ne_bot W).2
      intro hW
      exact hx (Subgroup.mem_bot.mp (hW ▸ hxW))
    have hWcoprime : Nat.Coprime p (Nat.card W) :=
      Nat.Coprime.of_dvd_right (hcomap_card_dvd T) hTcoprime
    have hWmax :
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W := by
      intro V hV hWV
      have hVmap_cyclic : IsCyclic (V.map H.subtype) :=
        hmap_subtype_cyclic V hV
      have hxVmap :
          (x : PSL2MatrixGroup F) ∈ V.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (hWV hxW)
      have hVmap_le_T : V.map H.subtype ≤ T :=
        hcyclic_le_family hxG hxT hTfamily' hxVmap hVmap_cyclic
      have hVleW : V ≤ W :=
        Subgroup.map_le_iff_le_comap.mp hVmap_le_T
      exact le_antisymm hVleW hWV
    obtain ⟨i, g, hWrep⟩ :=
      hrepresentative W hWcyclic hWcard hWcoprime hWmax
    refine ⟨Sum.inr ⟨i, ⟨W, g, hWrep⟩⟩, hxW, ?_⟩
    intro A hA
    rcases A with Q | z
    · exfalso
      have hcop : Nat.Coprime (Nat.card Q) (Nat.card W) := by
        rw [hWrep]
        exact hsylow_coprime_conj Q i g
      exact hx (hmem_eq_one_of_coprime_card
        (Q : Subgroup H) W hcop hA hxW)
    · rcases z with ⟨j, W', h, hW'rep⟩
      have hW'cyclic : IsCyclic W' := by
        rw [hW'rep]
        exact hmap_cyclic_H (Z j) (hcyclic j) h
      have hxW'map :
          (x : PSL2MatrixGroup F) ∈ W'.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype hA
      have hW'map_le_T : W'.map H.subtype ≤ T :=
        hcyclic_le_family hxG hxT hTfamily' hxW'map
          (hmap_subtype_cyclic W' hW'cyclic)
      have hW'leW : W' ≤ W :=
        Subgroup.map_le_iff_le_comap.mp hW'map_le_T
      have hW'max :
          ∀ V : Subgroup H, IsCyclic V → W' ≤ V → V = W' := by
        rw [hW'rep]
        exact hconj_maximal j h
      have hWW' : W = W' := hW'max W hWcyclic hW'leW
      have hmaps :
          (Z i).map (MulAut.conj g).toMonoidHom =
            (Z j).map (MulAut.conj h).toMonoidHom := by
        rw [← hWrep, ← hW'rep, hWW']
      have hij : i = j := hindices_eq i j g h hmaps
      subst j
      subst W'
      rfl

/-- The disjoint-union count in Huppert II.8.22. -/
public theorem huppert_II_8_22_counting_equation
    {F : Type u} [Field F] [Finite F] {p f m r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H) (s : Fin r → ℕ)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    (hnormalizer : ∀ i,
      Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i) :
    Nat.card H =
      1 + ((p ^ m - 1) * Nat.card H) /
          Nat.card (Subgroup.normalizer (P : Set H)) +
        ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
          (Nat.card (Z i) * s i) := by
  classical
  have hpartition_count :
      Nat.card H =
        1 + (p ^ m - 1) *
            (Subgroup.normalizer (P : Set H)).index +
          ∑ i, (Nat.card (Z i) - 1) *
            (Subgroup.normalizer (Z i : Set H)).index := by
    apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
    intro x hx
    convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
      hcoprime hmaximal hrepresentative hdistinct x hx using 1
    funext A
    rcases A with Q | z <;> rfl
  have hPindex :
      (Subgroup.normalizer (P : Set H)).index =
        Nat.card H /
          Nat.card (Subgroup.normalizer (P : Set H)) :=
    Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.normalizer (P : Set H)).index_mul_card
  have hZindex :
      ∀ i, (Subgroup.normalizer (Z i : Set H)).index =
        Nat.card H /
          Nat.card (Subgroup.normalizer (Z i : Set H)) := by
    intro i
    exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Nat.card_pos)
      (Subgroup.normalizer (Z i : Set H)).index_mul_card
  nth_rewrite 1 [hpartition_count]
  congr 1
  · rw [Nat.mul_div_assoc _ (Subgroup.card_subgroup_dvd_card
      (Subgroup.normalizer (P : Set H))), ← hPindex]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← hnormalizer i,
      Nat.mul_div_assoc _ (Subgroup.card_subgroup_dvd_card
        (Subgroup.normalizer (Z i : Set H))), ← hZindex i]

/-- Huppert II.8.22: the counting equation for maximal cyclic `p`-prime subgroups. -/
public theorem huppert_II_8_22_dickson_counting
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H) (s : Fin r → ℕ),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) ∧
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i,
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (1 < p ^ m →
        (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
          ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
            p ^ m * Nat.card (Z i))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H =
        1 + ((p ^ m - 1) * Nat.card H) /
            Nat.card (Subgroup.normalizer (P : Set H)) +
          ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
            (Nat.card (Z i) * s i) := by
  rcases huppert_II_8_22_maximal_cyclic_representatives (H := H) p with
    ⟨r, Z, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct⟩
  rcases huppert_II_8_22_torus_normalizer_data
      hFcard H Z hcyclic hnontrivial hcoprime hmaximal with
    ⟨s, hs, hnormalizer, hdihedral, hdivides⟩
  refine ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
    hrepresentative, hdistinct, hs, hnormalizer, hdihedral, ?_, hdivides, ?_⟩
  · exact huppert_II_8_22_sylow_normalizer_shape
      hFcard H P hPcard Z hcyclic hcoprime hmaximal hrepresentative
  · exact huppert_II_8_22_counting_equation
      hFcard H P hPcard Z s hcyclic hnontrivial hcoprime hmaximal
        hrepresentative hdistinct hnormalizer
end Dickson
end CFSG.Glauberman
