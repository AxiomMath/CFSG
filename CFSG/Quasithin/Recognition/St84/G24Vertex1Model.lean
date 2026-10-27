module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Complement
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open Certificates.A5GL42 (aO bO)
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem a5pre_of_orth [Finite G]
    {L1 L2 S E : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) (hZE : centerOf (dsQ L1 L2 S) ≤ E)
    (hEQ : E ≤ dsQ L1 L2 S) (hrel : (centerOf (dsQ L1 L2 S)).relIndex E = 16)
    (hL1E : L1 ≤ Subgroup.normalizer (E : Set G))
    (hntriv : ∃ l ∈ L1, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (dsQ L1 L2 S)) :
    A5Pre L1 L1 E (centerOf (dsQ L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ : pCoreOf 2 L1 = dsQ L1 L2 S := G24LocalData.pCoreOf_eq_dsQ_left hR hD.le_left
  refine
    { le := le_rfl
      norm_L := Subgroup.le_normalizer
      norm_E := hL1E
      norm_K := fun x hx => P_le_normalizer_centerOf_dsQ_left L1 L2 S
        ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hx)
      sec := ?_
      card := hrel
      core := ?_
      quot := h1
      nontriv := hntriv }
  · refine ⟨hZE, ?_, ?_⟩
    · exact (Subgroup.commutator_mono hEQ hEQ).trans
        hD.special_left.1.commutator_le_centerOf
    · intro e he
      exact G24Vertex1.sq_mem_centerOf_dsQ hD e (hEQ he)
  · intro q hq e he
    rw [hQ] at hq
    exact G24Vertex1.commutator_mem_centerOf_dsQ hD q hq e (hEQ he)

theorem G24Vertex1.exists_a5model [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h1 : VA5 L1) (hD : G24LocalData L1 L2 S) :
    ∃ (E : Subgroup G) (M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S))
        Certificates.A5GL42.HO),
      centerOf (dsQ L1 L2 S) ≤ E ∧ E ≤ dsQ L1 L2 S ∧
      (centerOf (dsQ L1 L2 S)).relIndex E = 16 ∧
      L1 ≤ Subgroup.normalizer (E : Set G) ∧
      (∃ l ∈ L1, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (dsQ L1 L2 S)) ∧
      ¬ NatSec L1 (centerOf (dsQ L1 L2 S)) E := by
  obtain ⟨E, hZE, hEQ, hrel, hL1E, hntriv, hnat⟩ := hD.orth_left
  have hpre : A5Pre L1 L1 E (centerOf (dsQ L1 L2 S)) :=
    a5pre_of_orth hF h1 hD hZE hEQ hrel hL1E hntriv
  rcases A5Pre.exists_model' (P := L1) (L := L1) (E := E)
    (K := centerOf (dsQ L1 L2 S)) hpre with ⟨hnatsec, -⟩ | ⟨-, ⟨M⟩⟩
  · exact absurd hnatsec hnat
  · exact ⟨E, M, hZE, hEQ, hrel, hL1E, hntriv, hnat⟩

private theorem exists_preimage_model [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hD : G24LocalData L1 L2 S) {k : G}
    (hdec : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c)
    {E : Subgroup G} {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S))
      Certificates.A5GL42.HO} {x : Certificates.A5GL42.Mat4}
    (hxO : x ∈ Certificates.A5GL42.HO) :
    ∃ c : G, ∃ hcL : c ∈ L1, c ∈ (L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G) ∧ glMat (M.F.M ⟨c, hcL⟩) = x := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ : pCoreOf 2 L1 = dsQ L1 L2 S := G24LocalData.pCoreOf_eq_dsQ_left hR hD.le_left
  obtain ⟨l, hlL, hlM⟩ := M.surjL x hxO
  obtain ⟨q, hq, c, hc, hlc⟩ := hdec l.val ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hlL)
  have hqQ : q ∈ pCoreOf 2 L1 := by rwa [hQ]
  have hqL : q ∈ L1 := CFSG.LieType.BorelTits.pCoreOf_le 2 L1 hqQ
  have hcL : c ∈ L1 := by
    have hc_eq : c = q⁻¹ * (l : G) := by rw [hlc]; group
    rw [hc_eq]
    exact L1.mul_mem (L1.inv_mem hqL) hlL
  have hMc : glMat (M.F.M ⟨c, hcL⟩) = x := by
    have hsub : (⟨l.val, l.2⟩ : ↥L1) = ⟨q, hqL⟩ * ⟨c, hcL⟩ := Subtype.ext hlc
    have hMl : M.F.M ⟨l.val, l.2⟩ = M.F.M ⟨q, hqL⟩ * M.F.M ⟨c, hcL⟩ := by
      rw [hsub, map_mul]
    have hMq : M.F.M ⟨q, hqL⟩ = 1 := M.core ⟨q, hqL⟩ hqQ
    rw [hMl, hMq, one_mul] at hlM
    exact hlM
  exact ⟨c, hcL, hc, hMc⟩

private theorem eq_one_of_model_eq_one [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hD : G24LocalData L1 L2 S) {k : G}
    (hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥)
    {E : Subgroup G} {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S))
      Certificates.A5GL42.HO} {w : G} (hwL : w ∈ L1)
    (hwC : w ∈ Subgroup.centralizer ({k} : Set G))
    (hwM : M.F.M ⟨w, hwL⟩ = 1) : w = 1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ : pCoreOf 2 L1 = dsQ L1 L2 S := G24LocalData.pCoreOf_eq_dsQ_left hR hD.le_left
  have hwQ : w ∈ dsQ L1 L2 S := by
    have h := (M.kerL ⟨w, hwL⟩ hwL).mp hwM
    rwa [hQ] at h
  have hmem : w ∈ dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) := ⟨hwQ, hwC⟩
  rw [hinf] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem G24Vertex1.exists_a_b_of_model [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hD : G24LocalData L1 L2 S) {k : G}
    (hdec : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c)
    (hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥)
    {E : Subgroup G} {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S))
      Certificates.A5GL42.HO} :
    ∃ a b : G,
      a ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
      b ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
      a ∈ L1 ∧ b ∈ L1 ∧
      (∀ ha : a ∈ L1, glMat (M.F.M ⟨a, ha⟩) = aO) ∧
      (∀ hb : b ∈ L1, glMat (M.F.M ⟨b, hb⟩) = bO) ∧
      a ^ 2 = 1 ∧ b ^ 3 = 1 ∧ (a * b) ^ 5 = 1 := by
  have haO : aO ∈ Certificates.A5GL42.HO := a5Facts.gens.2.2.1
  have hbO : bO ∈ Certificates.A5GL42.HO := a5Facts.gens.2.2.2
  obtain ⟨a, haL, haA, hMa⟩ := exists_preimage_model hF hD hdec haO
  obtain ⟨b, hbL, hbA, hMb⟩ := exists_preimage_model hF hD hdec hbO
  have ha2 : a ^ 2 = 1 := by
    have hsqM : M.F.M ⟨a * a, L1.mul_mem haL haL⟩ = 1 := by
      have h1' : (⟨a * a, L1.mul_mem haL haL⟩ : ↥L1) = ⟨a, haL⟩ * ⟨a, haL⟩ := rfl
      rw [h1', map_mul]
      apply Units.ext
      change glMat (M.F.M ⟨a, haL⟩) * glMat (M.F.M ⟨a, haL⟩) =
        (1 : Certificates.A5GL42.Mat4)
      rw [hMa]
      decide
    have h := eq_one_of_model_eq_one hF hD hinf (L1.mul_mem haL haL)
      ((Subgroup.centralizer ({k} : Set G)).mul_mem haA.2 haA.2) hsqM
    simpa [pow_two] using h
  have hb3 : b ^ 3 = 1 := by
    have hcubeM : M.F.M ⟨b * b * b, L1.mul_mem (L1.mul_mem hbL hbL) hbL⟩ = 1 := by
      have h1' : (⟨b * b * b, L1.mul_mem (L1.mul_mem hbL hbL) hbL⟩ : ↥L1) =
          ⟨b, hbL⟩ * ⟨b, hbL⟩ * ⟨b, hbL⟩ := rfl
      rw [h1', map_mul, map_mul]
      apply Units.ext
      change glMat (M.F.M ⟨b, hbL⟩) * glMat (M.F.M ⟨b, hbL⟩) *
        glMat (M.F.M ⟨b, hbL⟩) = (1 : Certificates.A5GL42.Mat4)
      rw [hMb]
      decide
    have h := eq_one_of_model_eq_one hF hD hinf
      (L1.mul_mem (L1.mul_mem hbL hbL) hbL)
      ((Subgroup.centralizer ({k} : Set G)).mul_mem
        ((Subgroup.centralizer ({k} : Set G)).mul_mem hbA.2 hbA.2) hbA.2) hcubeM
    simpa [pow_three, mul_assoc] using h
  have hab5 : (a * b) ^ 5 = 1 := by
    have hfiveM : M.F.M ⟨(a * b) ^ 5, L1.pow_mem (L1.mul_mem haL hbL) 5⟩ = 1 := by
      have hsub : (⟨(a * b) ^ 5, L1.pow_mem (L1.mul_mem haL hbL) 5⟩ : ↥L1) =
          (⟨a, haL⟩ * ⟨b, hbL⟩) ^ 5 := rfl
      rw [hsub, map_pow, map_mul]
      apply Units.ext
      change (glMat (M.F.M ⟨a, haL⟩) * glMat (M.F.M ⟨b, hbL⟩)) ^ 5 =
        (1 : Certificates.A5GL42.Mat4)
      rw [hMa, hMb]
      decide
    have h := eq_one_of_model_eq_one hF hD hinf
      (L1.pow_mem (L1.mul_mem haL hbL) 5)
      ((Subgroup.centralizer ({k} : Set G)).pow_mem
        ((Subgroup.centralizer ({k} : Set G)).mul_mem haA.2 hbA.2) 5) hfiveM
    simpa using h
  exact ⟨a, b, haA, hbA, haL, hbL, fun _ => hMa, fun _ => hMb, ha2, hb3, hab5⟩

private theorem conj_mem_conj_E {L1 L2 S E : Subgroup G}
    (hD : G24LocalData L1 L2 S) {k : G}
    (hkB : k ∈ bigB L1 L2 S)
    (hkc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S)
    (hZE : centerOf (dsQ L1 L2 S) ≤ E) (hEQ : E ≤ dsQ L1 L2 S)
    (hL1E : L1 ≤ Subgroup.normalizer (E : Set G)) {p y : G} (hp : p ∈ L1)
    (hy : y ∈ E.map (MulAut.conj k).toMonoidHom) :
    p * y * p⁻¹ ∈ E.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
  change p * (k * e * k⁻¹) * p⁻¹ ∈ E.map (MulAut.conj k).toMonoidHom
  have hpP : p ∈ L1 ⊔ bigB L1 L2 S := (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hp
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hkQ : k ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    P_le_normalizer_dsQ_left L1 L2 S hkP
  set c := k⁻¹ * p * k * p⁻¹ with hcdef
  have hcQ : c ∈ dsQ L1 L2 S := by
    have hcomm : ⁅k, p⁆ ∈ dsQ L1 L2 S := hkc p hpP
    have h1 : c = ⁅k⁻¹, p⁆ := by
      rw [hcdef, commutatorElement_def]
      group
    rw [h1, commutatorElement_inv_left]
    have h2 : ⁅p, k⁆ = ⁅k, p⁆⁻¹ := (commutatorElement_inv k p).symm
    rw [h2]
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkQ) _).mp
      ((dsQ L1 L2 S).inv_mem hcomm)
  have hkp : k⁻¹ * p * k = c * p := by
    rw [hcdef]
    group
  have hpk : p * k = k * c * p := by
    have h := congrArg (fun x => k * x) hkp
    simpa [mul_assoc] using h
  have he' : p * e * p⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hL1E hp) e).mp he
  have hcE : c ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hEQ).trans
        (hD.special_left.1.commutator_le_centerOf.trans hZE)) hcQ
  have hce' : c * (p * e * p⁻¹) * c⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hcE _).mp he'
  have hy_eq : p * (k * e * k⁻¹) * p⁻¹ = k * (c * (p * e * p⁻¹) * c⁻¹) * k⁻¹ := by
    calc p * (k * e * k⁻¹) * p⁻¹ = (p * k) * e * (p * k)⁻¹ := by group
      _ = (k * c * p) * e * (k * c * p)⁻¹ := by rw [hpk]
      _ = k * (c * (p * e * p⁻¹) * c⁻¹) * k⁻¹ := by group
  rw [hy_eq]
  simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hce'

theorem G24Vertex1.inter_conj_eq_center [Finite G]
    {L1 L2 S E : Subgroup G}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hkL : k ∉ L1)
    (hkc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S)
    (hZE : centerOf (dsQ L1 L2 S) ≤ E) (hEQ : E ≤ dsQ L1 L2 S)
    (hrel : (centerOf (dsQ L1 L2 S)).relIndex E = 16)
    (hL1E : L1 ≤ Subgroup.normalizer (E : Set G))
    (hntriv : ∃ l ∈ L1, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (dsQ L1 L2 S))
    (M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO) :
    E ⊓ E.map (MulAut.conj k).toMonoidHom = centerOf (dsQ L1 L2 S) := by
  let E' := E.map (MulAut.conj k).toMonoidHom
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hkZ : k ∈ Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) :=
    P_le_normalizer_centerOf_dsQ_left L1 L2 S hkP
  have hZX : centerOf (dsQ L1 L2 S) ≤ E ⊓ E' := by
    intro z hz
    refine ⟨hZE hz, ?_⟩
    refine Subgroup.mem_map.mpr ⟨k⁻¹ * z * k, hZE ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkZ) z).mp hz
    · show k * (k⁻¹ * z * k) * k⁻¹ = z
      group
  have hL1E' : L1 ≤ Subgroup.normalizer (E' : Set G) := by
    intro l hl
    exact Subgroup.mem_normalizer_fintype fun y hy => by
      simpa [E', MulAut.conj_apply] using
        conj_mem_conj_E hD hkB hkc hZE hEQ hL1E hl hy
  have hLX : L1 ≤ Subgroup.normalizer ((E ⊓ E') : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hL1E hl, hL1E' hl⟩
  have hpre := a5pre_of_orth hF h1 hD hZE hEQ hrel hL1E hntriv
  rcases A5Model.eq_or_eq_of_normalizes a5Facts a5Facts.groupO hpre M hZX inf_le_left hLX
    with h | h
  · exact h
  · exfalso
    have hEE' : E ≤ E' := by
      rw [← h]
      exact inf_le_right
    have hcardE' : Nat.card ↥E' = Nat.card ↥E := by
      simpa [E'] using Subgroup.card_map_of_injective
        (K := E) (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
    have hE'E : E' = E := (Subgroup.eq_of_le_of_card_ge hEE' (by rw [hcardE'])).symm
    have hkN : k ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hE'E
    have hPE : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (E : Set G) := by
      have hsup : L1 ⊔ Subgroup.zpowers k = L1 ⊔ bigB L1 L2 S :=
        G24Vertex1.sup_zpowers_eq_sup_bigB hF h1 hD hkB hkL
      rw [← hsup]
      exact sup_le hL1E (Subgroup.zpowers_le.mpr hkN)
    rcases hD.irr_left E hZE hEQ hPE with hEZ | hEQ'
    · rw [hEZ, Subgroup.relIndex_self] at hrel
      norm_num at hrel
    · have hcardE : Nat.card ↥E = Nat.card ↥(centerOf (dsQ L1 L2 S)) * 16 := by
        have h := Subgroup.relIndex_mul_card (H := centerOf (dsQ L1 L2 S)) (K := E)
        rw [inf_eq_left.mpr hZE, hrel] at h
        rw [← h, Nat.mul_comm]
      have hE64 : Nat.card ↥E = 64 := by
        rw [hcardE, hD.card_centerOf_dsQ_left]
      rw [hEQ'] at hE64
      rw [hD.card_dsQ_left] at hE64
      norm_num at hE64

end CFSG.Quasithin.F112R.St84
