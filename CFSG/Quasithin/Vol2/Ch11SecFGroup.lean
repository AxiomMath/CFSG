module

public import CFSG.Quasithin.Vol2.Ch11SecDDirect

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_inf_of_le_normalizer {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hB hb) a⁻¹).mp (A.inv_mem ha)
    have h2 := A.mul_mem ha h1
    simpa [mul_assoc] using h2
  · have h1 : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hA ha) b).mp hb
    exact B.mul_mem h1 (B.inv_mem hb)

@[expose] def commSub (A D : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (D : Set G) ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ D}
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨Subgroup.mul_mem _ hxN hyN, fun a ha => ?_⟩
    have heq : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact D.mul_mem (hx a ha) ((Subgroup.mem_normalizer_iff.mp hxN _).mp (hy a ha))
  one_mem' := ⟨Subgroup.one_mem _, fun a _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨Subgroup.inv_mem _ hxN, fun a ha => ?_⟩
    have heq : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp
      (D.inv_mem (hx a ha))

theorem mem_commSub {A D : Subgroup G} {x : G} :
    x ∈ commSub A D ↔ x ∈ Subgroup.normalizer (D : Set G) ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ D :=
  Iff.rfl

theorem commutator_sup_right_le {A B C D : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (D : Set G)) (hC : C ≤ Subgroup.normalizer (D : Set G))
    (h₁ : ⁅A, B⁆ ≤ D) (h₂ : ⁅A, C⁆ ≤ D) : ⁅A, B ⊔ C⁆ ≤ D := by
  have hBS : B ≤ commSub A D := fun b hb =>
    ⟨hB hb, fun a ha => Subgroup.commutator_le.mp h₁ a ha b hb⟩
  have hCS : C ≤ commSub A D := fun c hc =>
    ⟨hC hc, fun a ha => Subgroup.commutator_le.mp h₂ a ha c hc⟩
  rw [Subgroup.commutator_le]
  intro a ha x hx
  exact (sup_le hBS hCS hx).2 a ha

theorem pCoreOf_le_pCoreOf_of_le_normalizer [Finite G] {K H : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
    (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem pCoreOf_le_of_sylow [Finite G] {T H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) : pCoreOf 2 H ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  have hS' : IsPGroup 2 (T.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS'.toSylow hS.2.2
  have hN : (CFSG.Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal (G := H) 2
  have h1 : CFSG.Open.pCore 2 H ≤ (P : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup (G := H) 2) P
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  have h3 : (P : Subgroup H).map H.subtype = T := by
    change (T.subgroupOf H).map H.subtype = T
    exact Subgroup.map_subgroupOf_eq_of_le hTH
  exact h3 ▸ h2

theorem commutator_le_pCoreOf_of_le [Finite G] {P K T : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hP : P ≤ pCoreOf 2 (K ⊔ T)) :
    ⁅P, K⁆ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKT : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hO : pCoreOf 2 (K ⊔ T) ≤ K ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have h1 : ⁅pCoreOf 2 (K ⊔ T), K⁆ ≤ pCoreOf 2 (K ⊔ T) ⊓ K :=
    commutator_le_inf_of_le_normalizer (hO.trans hKT) hKO
  refine (Subgroup.commutator_mono hP le_rfl).trans (h1.trans ?_)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun k hk => SecD.mem_normalizer_inf (hKO hk) (Subgroup.le_normalizer hk))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

theorem conj_sup_le_of_commutator {P O : Subgroup G} {x : G}
    (hxO : x ∈ Subgroup.normalizer (O : Set G)) (hPx : ∀ p ∈ P, ⁅p, x⁆ ∈ O) :
    ∀ h ∈ P ⊔ O, x * h * x⁻¹ ∈ P ⊔ O := by
  have hle : P ⊔ O ≤ (P ⊔ O).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun p hp => ?_) (fun o ho => ?_)
    · change x * p * x⁻¹ ∈ P ⊔ O
      have heq : x * p * x⁻¹ = p * ⁅p⁻¹, x⁆ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp)
        (Subgroup.mem_sup_right (hPx _ (P.inv_mem hp)))
    · change x * o * x⁻¹ ∈ P ⊔ O
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hxO o).mp ho)
  exact fun h hh => hle hh

theorem le_pCoreOf_of_commutator_le [Finite G] {H N S P : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hSH : S ≤ H)
    (hdec : ∀ g ∈ H, ∃ x ∈ N, ∃ s ∈ S, g = x * s) (hPN : ⁅P, N⁆ ≤ pCoreOf 2 N) :
    P ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 N with hOdef
  have hON : O ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    hHN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N)
  have hR : IsPGroup 2 (P ⊔ O : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hP (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hPH.trans hHO)
  have hRH : P ⊔ O ≤ H := sup_le hPH (hON.trans hNH)
  have hNR : N ≤ Subgroup.normalizer ((P ⊔ O : Subgroup G) : Set G) := by
    intro x hx
    have hPx : ∀ y ∈ N, ∀ p ∈ P, ⁅p, y⁆ ∈ O := fun y hy p hp =>
      hPN (Subgroup.commutator_mem_commutator hp hy)
    refine SecD.mem_normalizer_of_conj
      (conj_sup_le_of_commutator (hHO (hNH hx)) (hPx x hx)) ?_
    have h := conj_sup_le_of_commutator (hHO (hNH (N.inv_mem hx))) (hPx _ (N.inv_mem hx))
    simpa using h
  have hSR : S ≤ Subgroup.normalizer ((P ⊔ O : Subgroup G) : Set G) :=
    SecD.le_normalizer_sup hSP (hSH.trans hHO)
  have hHR : H ≤ Subgroup.normalizer ((P ⊔ O : Subgroup G) : Set G) := by
    intro g hg
    obtain ⟨x, hx, s, hs, rfl⟩ := hdec g hg
    exact Subgroup.mul_mem _ (hNR hx) (hSR hs)
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRH hHR hR)

theorem frattini_map_eq_bot [Finite G] {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    (frattini ↥E).map E.subtype = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ y : ↥E, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using hE.2 y y.2)
  have : Fact (IsPGroup 2 ↥E) := ⟨fun y => ⟨1, by simpa using hsq y⟩⟩
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hbot : frattini ↥E = ⊥ := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), eq_bot_iff,
      Subgroup.closure_le]
    intro x hx
    rcases hx with hx | ⟨y, rfl⟩
    · have hc : (commutator ↥E : Subgroup ↥E) ≤ ⊥ := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        simp [commutatorElement_def, hcomm a b]
      exact hc hx
    · simp [hsq y]
  rw [hbot, Subgroup.map_bot]

end CFSG.Quasithin.Vol2.Ch11.SecF
