module

public import CFSG.Quasithin.Vol2.Ch11SecBK11C
public import CFSG.RankThree.SubgroupLists.CentralThreeLift
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecAKE15
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.BK11

open CFSG.Open CFSG.QuasithinUnique
open CFSG.RankThree.SubgroupLists (negDiag3 exists_conj_negDiag3 exists_lift_pow_eq_one
  commute_of_commute_mk)

@[expose] def a5u : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩

@[expose] def a5v : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩

@[expose] def a5w : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩

theorem a5_four : a5u * a5u = 1 ∧ a5v * a5v = 1 ∧ a5u * a5v = a5v * a5u ∧ a5u ≠ 1 ∧
    a5v ≠ 1 ∧ a5u ≠ a5v := by
  decide

theorem a5_noncomm : a5u * a5w ≠ a5w * a5u := by
  decide

variable {S : Type} [Group S] {B : Subgroup S}

theorem coe_mem_pCoreOf_iff {x : ↥B} : (x : S) ∈ pCoreOf 2 B ↔ x ∈ CFSG.pCore 2 ↥B :=
  CFSG.mem_openPCoreOf_iff x

theorem relIndex_pCoreOf_eq : (pCoreOf 2 B).relIndex B = Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) := by
  rw [Subgroup.relIndex, pCoreOf, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective]
  rfl

theorem card_pCore_le_eight [Finite S] (h64 : ¬ 64 ∣ Nat.card S)
    (h60 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60) : Nat.card (CFSG.pCore 2 ↥B) ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  have hB' : Nat.card ↥B = 60 * 2 ^ k := by
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, h60, hk]
  have hdvd : 60 * 2 ^ k ∣ Nat.card S := by
    rw [← hB']
    exact Subgroup.card_subgroup_dvd_card B
  have hk3 : k ≤ 3 := by
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    exact h64 (dvd_trans ⟨15 * 2 ^ j, by ring⟩ hdvd)
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

variable [Finite S] {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
  {Z : Subgroup ↥H} [Z.Normal]

omit [Finite S] [Finite K] in
theorem false_of_pCore_eq_bot (h2 : (2 : K) ≠ 0)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZc : Z ≤ Subgroup.center ↥H) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (e : S ≃* ↥H ⧸ Z)
    (hO : CFSG.pCore 2 ↥B = ⊥) (eA : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5))
    {t : S} (ht2 : t * t = 1) (ht1 : t ≠ 1) (htB : ∀ y ∈ B, t * y = y * t) : False := by
  let eB : ↥B ≃* alternatingGroup (Fin 5) :=
    ((QuotientGroup.quotientBot (G := ↥B)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hO.symm)).trans eA
  have hZ : ∀ x ∈ B, (∀ y ∈ B, x * y = y * x) → x = 1 := by
    intro x hx hxy
    have h1 : eB ⟨x, hx⟩ = 1 := C10KH.a5_center _ fun y => by
      obtain ⟨⟨w, hw⟩, rfl⟩ := eB.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eB (Subtype.ext (hxy w hw))
    exact congrArg Subtype.val (eB.injective (h1.trans (map_one eB).symm))
  have htnB : t ∉ B := fun h => ht1 (hZ t h htB)
  obtain ⟨huu, hvv, huv, hu1, hv1, hne⟩ := a5_four
  have hcoe : ∀ a b : alternatingGroup (Fin 5),
      ((eB.symm a : ↥B) : S) * (eB.symm b : ↥B) = ((eB.symm (a * b) : ↥B) : S) := fun a b => by
    rw [map_mul, Subgroup.coe_mul]
  have hcoe1 : ∀ a : alternatingGroup (Fin 5), ((eB.symm a : ↥B) : S) = 1 → a = 1 := by
    intro a h
    have : eB.symm a = 1 := Subtype.ext h
    rw [← eB.apply_symm_apply a, this, map_one]
  have hcoeinj : ∀ a b : alternatingGroup (Fin 5),
      ((eB.symm a : ↥B) : S) = (eB.symm b : ↥B) → a = b := fun a b h =>
    eB.symm.injective (Subtype.ext h)
  set u : S := ((eB.symm a5u : ↥B) : S) with hu
  set v : S := ((eB.symm a5v : ↥B) : S) with hv
  have huB : u ∈ B := (eB.symm a5u).2
  have hvB : v ∈ B := (eB.symm a5v).2
  have hu2 : u * u = 1 := by rw [hu, hcoe, huu, map_one, Subgroup.coe_one]
  have hv2 : v * v = 1 := by rw [hv, hcoe, hvv, map_one, Subgroup.coe_one]
  have huv' : u * v = v * u := by rw [hu, hv, hcoe, hcoe, huv]
  have hu1' : u ≠ 1 := fun h => hu1 (hcoe1 _ h)
  have hv1' : v ≠ 1 := fun h => hv1 (hcoe1 _ h)
  have huvne : u ≠ v := fun h => hne (hcoeinj _ _ h)
  have hlift : ∀ s : S, s * s = 1 → ∃ x : ↥H, (x : ↥H ⧸ Z) = e s ∧ x ^ 2 = 1 := fun s hs =>
    exists_lift_pow_eq_one hZc hZ3 (by norm_num) (e s) (by rw [← map_pow, pow_two, hs, map_one])
  obtain ⟨u', hu'e, hu'2⟩ := hlift u hu2
  obtain ⟨v', hv'e, hv'2⟩ := hlift v hv2
  obtain ⟨t', ht'e, ht'2⟩ := hlift t ht2
  have hcm : ∀ (x y : ↥H) (s s' : S), (x : ↥H ⧸ Z) = e s → (y : ↥H ⧸ Z) = e s' → x ^ 2 = 1 →
      s * s' = s' * s → (x : GL (Fin 3) K) * y = y * x := fun x y s s' hx hy hx2 hss' =>
    congrArg Subtype.val (commute_of_commute_mk hZc hZ3 (by norm_num) hx2
      (by rw [hx, hy, ← map_mul, hss', map_mul]))
  have hsqGL : ∀ x : ↥H, x ^ 2 = 1 → (x : GL (Fin 3) K) * x = 1 := fun x hx => by
    rw [← Subgroup.coe_mul, ← pow_two, hx, Subgroup.coe_one]
  have hne1 : ∀ (x : ↥H) (s : S), (x : ↥H ⧸ Z) = e s → s ≠ 1 → (x : GL (Fin 3) K) ≠ 1 :=
    fun x s hx hs h => hs (e.injective (by
      rw [← hx, map_one, show x = 1 from Subtype.ext h, QuotientGroup.mk_one]))
  have hne' : (u' : GL (Fin 3) K) ≠ v' := fun h => huvne (e.injective (by
    rw [← hu'e, ← hv'e, show u' = v' from Subtype.ext h]))
  have hmem : ∀ (x : ↥H) (s : S), (x : ↥H ⧸ Z) = e s → (t' : GL (Fin 3) K) = x → s ∈ B →
      False := by
    intro x s hx h hs
    have htx : t' = x := Subtype.ext h
    have hts : t = s := e.injective (by rw [← ht'e, ← hx, htx])
    exact htnB (by rw [hts]; exact hs)
  rcases eq_of_commute_involutions h2 (hsqGL u' hu'2) (hsqGL v' hv'2) (hsqGL t' ht'2)
    (hne1 u' u hu'e hu1') (hne1 v' v hv'e hv1') hne' (hdet _ u'.2) (hdet _ v'.2) (hdet _ t'.2)
    (hcm u' v' u v hu'e hv'e hu'2 huv') (hcm u' t' u t hu'e ht'e hu'2 (htB u huB).symm)
    (hcm v' t' v t hv'e ht'e hv'2 (htB v hvB).symm) with h | h | h | h
  · exact hmem 1 1 (by rw [QuotientGroup.mk_one, map_one]) h (one_mem B)
  · exact hmem u' u hu'e h huB
  · exact hmem v' v hv'e h hvB
  · exact hmem (u' * v') (u * v) (by rw [QuotientGroup.mk_mul, hu'e, hv'e, map_mul]) h
      (mul_mem huB hvB)

end CFSG.Quasithin.Vol2.Ch11.SecA.BK11
