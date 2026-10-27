module

public import CFSG.Quasithin.Vol2.Ch10SecA312AW
public import CFSG.Quasithin.Vol2.Ch10SecA312AD
public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentBlock
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Hj
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
open CFSG.Quasithin.J4ZCent (nonempty_modO2_equiv_map false_of_central_pcore j4_center_of_alt5
  j4_false_of_psl32)

section Model

variable {X : Type} [Group X] [Finite X] {Γ : Type} [Group Γ] [Finite Γ] {P₀ : Subgroup Γ} {z₀ : Γ}

theorem zcent_model_data (hP₀ : IsSylowTwoOf P₀ ⊤)
    (hz : ∀ x ∈ P₀, (∀ p ∈ P₀, x * p = p * x) → x = 1 ∨ x = z₀) (φ : X ≃* Γ)
    {T B : Subgroup X} (hc : ZCentConf X T B) :
    ∃ e : X ≃* Γ, ⁅B.map e.toMonoidHom, B.map e.toMonoidHom⁆ = B.map e.toMonoidHom ∧
      B.map e.toMonoidHom ≠ ⊥ ∧ (∀ b ∈ B.map e.toMonoidHom, z₀ * b = b * z₀) ∧
      P₀ ≤ Subgroup.normalizer ((B.map e.toMonoidHom : Subgroup Γ) : Set Γ) := by
  obtain ⟨-, -, -, hT, hB, -, hTB, -, ⟨z, hzT, hz1, hzc, hzB⟩, -⟩ := hc
  obtain ⟨e, he⟩ := sylow_transport hP₀ φ hT
  have he' : T.map e.toMonoidHom = P₀ := he
  have hB' : B.map e.toMonoidHom ∈ cComp (B.map e.toMonoidHom ⊔ P₀) := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
    rwa [Subgroup.map_sup, he'] at h1
  refine ⟨e, perfect_of_mem_cComp hB', ne_bot_of_mem_cComp hB', ?_, ?_⟩
  · have hzP : e z ∈ P₀ := he' ▸ Subgroup.mem_map_of_mem _ hzT
    have hzcP : ∀ p ∈ P₀, e z * p = p * e z := by
      intro p hp
      rw [← he'] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      show e z * e t = e t * e z
      rw [← map_mul, ← map_mul, hzc t ht]
    have hez : e z = z₀ :=
      (hz _ hzP hzcP).resolve_left (fun h => hz1 (e.injective (by rw [h, map_one])))
    rintro _ ⟨b, hb, rfl⟩
    show z₀ * e b = e b * z₀
    rw [← hez, ← map_mul, ← map_mul, hzB b hb]
  · calc P₀ = T.map e.toMonoidHom := he'.symm
      _ ≤ (Subgroup.normalizer (B : Set X)).map e.toMonoidHom := Subgroup.map_mono hTB
      _ ≤ _ := Subgroup.le_normalizer_map _

theorem false_of_model_alt5 (hP₀ : IsSylowTwoOf P₀ ⊤)
    (hz : ∀ x ∈ P₀, (∀ p ∈ P₀, x * p = p * x) → x = 1 ∨ x = z₀)
    (hmodel : ∀ B' : Subgroup Γ, ⁅B', B'⁆ = B' → B' ≠ ⊥ → (∀ b ∈ B', z₀ * b = b * z₀) →
      P₀ ≤ Subgroup.normalizer (B' : Set Γ) → IsSimpleGroup (ModO2 B') →
      Nat.card (ModO2 B') = 60 → ∀ x ∈ pCoreOf 2 B', (∀ r ∈ pCoreOf 2 B', x * r = r * x) →
        ∀ b ∈ B', x * b = b * x)
    (φ : X ≃* Γ) {T B : Subgroup X} (hA5 : IsAlt 5 (ModO2 B)) (hc : ZCentConf X T B) : False := by
  have hc' := hc
  obtain ⟨e, hperf, hne, hzB, hP⟩ := zcent_model_data hP₀ hz φ hc
  obtain ⟨-, -, -, -, -, -, -, -, -, V, hVB, hV, hBV, hcomm, hV1, hcV, -⟩ := hc'
  obtain ⟨eM⟩ := nonempty_modO2_equiv_map e B
  have hS : IsSimpleGroup (ModO2 B) := isSimpleGroup_alt (Or.inl rfl) hA5
  have hcard : Nat.card (ModO2 B) = 60 := by
    obtain ⟨e5⟩ := hA5
    rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hS' : IsSimpleGroup (ModO2 (B.map e.toMonoidHom)) := eM.symm.isSimpleGroup
  have hcard' : Nat.card (ModO2 (B.map e.toMonoidHom)) = 60 :=
    (Nat.card_congr eM.symm.toEquiv).trans hcard
  have hZ' := hmodel _ hperf hne hzB hP hS' hcard'
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  refine false_of_central_pcore hVB hVp hBV hcomm hV1 hcV ?_
  intro x hx hxc b hb
  have hex : e x ∈ pCoreOf 2 (B.map e.toMonoidHom) := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e B]
    exact Subgroup.mem_map_of_mem _ hx
  have hcomm' : ∀ r' ∈ pCoreOf 2 (B.map e.toMonoidHom), e x * r' = r' * e x := by
    intro r' hr'
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e B] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    show e x * e r = e r * e x
    rw [← map_mul, ← map_mul, hxc r hr]
  have h := hZ' (e x) hex hcomm' (e b) (Subgroup.mem_map_of_mem _ hb)
  exact e.injective (by rw [map_mul, map_mul]; exact h)

theorem false_of_model_psl32 (hP₀ : IsSylowTwoOf P₀ ⊤)
    (hz : ∀ x ∈ P₀, (∀ p ∈ P₀, x * p = p * x) → x = 1 ∨ x = z₀)
    (hmodel : ∀ B' : Subgroup Γ, ⁅B', B'⁆ = B' → B' ≠ ⊥ → (∀ b ∈ B', z₀ * b = b * z₀) →
      P₀ ≤ Subgroup.normalizer (B' : Set Γ) → IsSimpleGroup (ModO2 B') →
      Nat.card (ModO2 B') = 168 → False)
    (φ : X ≃* Γ) {T B : Subgroup X} (hL : IsPSL 3 2 1 (ModO2 B)) (hc : ZCentConf X T B) :
    False := by
  obtain ⟨e, hperf, hne, hzB, hP⟩ := zcent_model_data hP₀ hz φ hc
  obtain ⟨eM⟩ := nonempty_modO2_equiv_map e B
  have hS : IsSimpleGroup (ModO2 B) := isSimpleGroup_of_stated hL
  have hcard : Nat.card (ModO2 B) = 168 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl]
    decide
  have hS' : IsSimpleGroup (ModO2 (B.map e.toMonoidHom)) := eM.symm.isSimpleGroup
  have hcard' : Nat.card (ModO2 (B.map e.toMonoidHom)) = 168 :=
    (Nat.card_congr eM.symm.toEquiv).trans hcard
  exact hmodel _ hperf hne hzB hP hS' hcard'

end Model

section J4

theorem j4_center_P0
    {x : J} (hx : x ∈ P0)
    (hxc : ∀ p ∈ P0, x * p = p * x) : x = 1 ∨ x = z0 :=
  CFSG.Quasithin.J4Local.eq_one_or_eq_zJ_of_mem_centerOf
    ⟨hx, Subgroup.mem_centralizer_iff.2 fun p hp => (hxc p hp).symm⟩

theorem a312ZCentRestJ4A5_holds :
    A312ZCentRestJ4A5 := by
  intro X _ _ T B hA5 hJ4 hc
  have hF : J4Facts := j4Facts
  obtain ⟨e₀⟩ := hJ4
  exact false_of_model_alt5 (Γ := J) (P₀ := P0) (z₀ := z0) isSylowTwoOf_P0 (fun x hx hxc =>
    j4_center_P0 hx hxc) (fun B' hB' hB1 hBz hPB hS hcard =>
      j4_center_of_alt5 hF hB' hB1 hBz hPB hS hcard)
    (((Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).trans e₀).trans (seedEquiv hF.mat)) hA5 hc

theorem a312ZCentRestJ4L32_holds :
    A312ZCentRestJ4L32 := by
  intro X _ _ T B hL hJ4 hc
  have hF : J4Facts := j4Facts
  obtain ⟨e₀⟩ := hJ4
  exact false_of_model_psl32 (Γ := J) (P₀ := P0) (z₀ := z0) isSylowTwoOf_P0 (fun x hx hxc =>
    j4_center_P0 hx hxc) (fun B' hB' hB1 hBz hPB hS hcard =>
      j4_false_of_psl32 hF hB' hB1 hBz hPB hS hcard)
    (((Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).trans e₀).trans (seedEquiv hF.mat)) hL hc

theorem a312ZCentRestJ4_holds :
    A312ZCentRestJ4 :=
  ⟨a312ZCentRestJ4A5_holds, a312ZCentRestJ4L32_holds⟩

end J4

end CFSG.Quasithin.Vol2.Ch10.A312A
