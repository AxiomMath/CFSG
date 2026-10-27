module

public import CFSG.Quasithin.Background.GoldschmidtE5TwoStab
public import CFSG.Quasithin.Background.GoldschmidtE1Transfer

public section

namespace CFSG.Quasithin
namespace E5

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem twoResidual_le_iSup_of_normal {j : ℕ} {H Y T S A K : Subgroup G}
    (hT : IsSylowIn 2 T H) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (h2 : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ Y) (hSTY : T ⊓ Y = S)
    (hA : IsMaxElemAbelian Y A) (hAS : A ≤ S) (hK : E1.IsE j H T A K) :
    twoResidual K ≤ ⨆ D₁ ∈ dFam j S, Y ⊓ Subgroup.centralizer (D₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSY : S ≤ Y := hSTY ▸ inf_le_right
  have hST : S ≤ T := hSTY ▸ inf_le_left
  set Qf := pCoreOf 2 K with hQfdef
  set Q := Qf ⊓ Y with hQdef
  set D := omegaOneCenterOf (H13.thompsonJk j S) with hDdef
  set A₁ := A ⊓ Q with hA₁def
  set Φ := ⨆ D₁ ∈ dFam j S, Y ⊓ Subgroup.centralizer (D₁ : Set G) with hΦ
  have hAmax : IsMaxElemAbelian S A :=
    ⟨hAS, hA.2.1, fun B hBS hB => hA.2.2 B (hBS.trans hSY) hB⟩
  obtain ⟨hAK, hAcardF⟩ := E3.card_le_of_isE hT (hAS.trans hST) hA.2.1 hK
  have hAcard : Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ Q) := by
    have e : A ⊓ Q = A ⊓ Qf := by
      ext x
      simp only [hQdef, Subgroup.mem_inf]
      exact ⟨fun ⟨ha, hq, _⟩ => ⟨ha, hq⟩, fun ⟨ha, hq⟩ => ⟨ha, hq, hA.1 ha⟩⟩
    rw [e]
    exact hAcardF
  have hKH : K ≤ H := hK.1
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := hKH.trans hHY
  have hPK : IsSylowIn 2 (T ⊓ K) K := hK.2.2.1
  have hKQf : K ≤ Subgroup.normalizer (Qf : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQfK : Qf ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hQf2 : IsPGroup 2 Qf := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hQfT : Qf ≤ T := (hPK.le_of_normal hQfK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQfK).2 hKQf) hQf2).trans inf_le_left
  have hQS : Q ≤ S := by
    rw [← hSTY]
    exact le_inf (inf_le_left.trans hQfT) inf_le_right
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hQdef, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.1 (hKQf hk) x, Subgroup.mem_normalizer_iff.1 (hKY hk) x]
  have hA₁ : A₁ ∈ wFam j S Q := ⟨inf_le_right, B2F.isElemAbelian_mono inf_le_left hA.2.1,
    fun B hBS hB => (hA.2.2 B (hBS.trans hSY) hB).trans hAcard⟩
  set W := wGen j S Q with hWdef
  have hA₁W : A₁ ≤ W := le_wGen hA₁
  have hWQ : W ≤ Q := wGen_le j S Q
  have hWJ : W ≤ H13.thompsonJk j S := wGen_le_thompsonJk hQS
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_wGen j hKQ
  have hDA : D ≤ A := omegaOneCenterOf_le_of_isMaxElemAbelian hAmax
  have hDK : D ≤ K := hDA.trans hAK
  have hDel : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hDW : D ≤ Subgroup.centralizer (W : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun w hw => mem_centralizer_of_mem_omegaOneCenterOf hd (hWJ hw)
  set X := K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W with hXdef
  have hXK : X ≤ K := inf_le_left.trans inf_le_left
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := le_normalizer_stabilizer hKQ hKW
  have hDX : D ≤ X := by
    intro d hd
    refine ⟨⟨hDK hd, hDW hd⟩, hKW (hDK hd), fun q hq => ?_⟩
    have hQD : q ∈ Subgroup.normalizer (D : Set G) :=
      normalizer_le_normalizer_omegaOneCenterOf _ (le_normalizer_thompsonJk j S (hQS hq))
    have h1 : ⁅d, q⁆ ∈ D := by
      have : q * d⁻¹ * q⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hQD _).1 (D.inv_mem hd)
      have e : ⁅d, q⁆ = d * (q * d⁻¹ * q⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem hd this
    have h2 : ⁅d, q⁆ ∈ Q := by
      have : d * q * d⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hKQ (hDK hd)) q).1 hq
      have e : ⁅d, q⁆ = (d * q * d⁻¹) * q⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Q.mul_mem this (Q.inv_mem hq)
    exact hA₁W ⟨hDA h1, h2⟩
  have hXres : twoResidual X ≤ Subgroup.centralizer (Q : Set G) :=
    twoResidual_stabilizer_le hWQ (hQf2.to_le inf_le_left) hKQ
  have hXY : twoResidual X ≤ Y := E1.twoResidual_le_of_normal_two (hXK.trans hKH) hHY h2
  have hXresF : twoResidual X ≤ Subgroup.centralizer (Qf : Set G) := by
    refine le_centralizer_of_stab (twoResidual_twoResidual X) hQf2
      (fun u hu => hKQf (hXK (twoResidual_le X hu))) hXres inf_le_left ?_
    intro u hu q hq
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : u * q * u⁻¹ ∈ Qf :=
        (Subgroup.mem_normalizer_iff.1 (hKQf (hXK (twoResidual_le X hu))) q).1 hq
      exact Qf.mul_mem h1 (Qf.inv_mem hq)
    · have h1 : q * u⁻¹ * q⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hKY (hQfK hq)) u⁻¹).1 (Y.inv_mem (hXY hu))
      have e : ⁅u, q⁆ = u * (q * u⁻¹ * q⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Y.mul_mem (hXY hu) h1
  have hdich : twoResidual K ≤ Subgroup.centralizer (Qf : Set G) ∨ D ≤ Qf := by
    have hXn : (X.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).2 hKX
    have hE : E1.EOne ↥K (A.subgroupOf K) ∨
        E1.ETwo ↥K ((T ⊓ K).subgroupOf K) (A.subgroupOf K) := by
      rcases hK.2.2.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hD2 : IsPGroup 2 (D.subgroupOf K) :=
      (B2F.isPGroup_of_isElemAbelian hDel).of_equiv (Subgroup.subgroupOfEquivOfLe hDK).symm
    have hXK' : twoResidual (X.subgroupOf K) ≤
        Subgroup.centralizer (CFSG.Open.pCore 2 ↥K : Set ↥K) := by
      intro y hy
      have hy' : (y : G) ∈ twoResidual X := by
        have h1 : (twoResidual (X.subgroupOf K)).map K.subtype = twoResidual X := by
          rw [E1.map_twoResidual, Subgroup.map_subgroupOf_eq_of_le hXK]
        rw [← h1]
        exact Subgroup.mem_map_of_mem _ hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzQ : (z : G) ∈ Qf := Subgroup.mem_map_of_mem K.subtype hz
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hXresF hy') _ hzQ)
    rcases dichotomy hE (Subgroup.subgroupOf_mono K hDA) hD2 (hXn := hXn)
      (Subgroup.subgroupOf_mono K hDX) hXK' with h | h
    · left
      rw [E1.twoResidual_eq_map_top K]
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (h hy) z hz)
    · right
      intro d hd
      have := h (show (⟨d, hDK hd⟩ : ↥K) ∈ D.subgroupOf K from hd)
      exact ⟨_, this, rfl⟩
  rcases hdich with h1 | h2'
  ·
    have hrel : Q.relIndex A ≤ 2 ^ j := by
      have h1 := Subgroup.relIndex_mul_card Q A
      have hQA : Q ⊓ A = A ⊓ Q := inf_comm Q A
      have h2 : Q.relIndex A * Nat.card ↥(Q ⊓ A) ≤ 2 ^ j * Nat.card ↥(Q ⊓ A) := by
        rw [h1, hQA]; exact hAcard
      exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
    have hD₁ : D ⊓ Q ∈ dFam j S := by
      refine ⟨inf_le_left, ?_⟩
      have h3 := Subgroup.relIndex_mul_card Q D
      have h4 : Q.relIndex D ≤ Q.relIndex A :=
        Subgroup.relIndex_le_of_le_right hDA (E3.relIndex_ne_zero' _ _)
      calc Nat.card ↥D = Q.relIndex D * Nat.card ↥(Q ⊓ D) := h3.symm
        _ ≤ 2 ^ j * Nat.card ↥(D ⊓ Q) := by
          rw [inf_comm]; exact Nat.mul_le_mul_right _ (h4.trans hrel)
    refine le_iSup₂_of_le (f := fun D₁ (_ : D₁ ∈ dFam j S) =>
      Y ⊓ Subgroup.centralizer (D₁ : Set G)) (D ⊓ Q) hD₁ ?_
    exact le_inf (E1.twoResidual_le_of_normal_two hKH hHY h2)
      (h1.trans (Subgroup.centralizer_le (fun x hx => hx.2.1)))
  ·
    have hDQ : D ≤ Q := fun d hd => ⟨h2' hd, hA.1 (hDA hd)⟩
    have hDW' : D ≤ W := fun d hd => hA₁W ⟨hDA hd, hDQ hd⟩
    set E := omegaOneCenterOf W with hEdef
    have hDE : D ≤ E := fun d hd =>
      mem_omegaOneCenterOf (hDW' hd)
        (fun w hw => (Subgroup.mem_centralizer_iff.1 (hDW hd) w hw)) (hDel.2 d hd)
    have hKE : K ≤ Subgroup.normalizer (E : Set G) :=
      hKW.trans (normalizer_le_normalizer_omegaOneCenterOf W)
    have hEel : IsElemAbelian 2 E := B2F.isElemAbelian_omegaOneCenterOf W
    have hEA₁ : IsElemAbelian 2 (E ⊔ A₁) :=
      B2F.isElemAbelian_sup_of_commute hEel hA₁.2.1 fun e he a ha =>
        (mem_centralizer_of_mem_omegaOneCenterOf he (hA₁W ha)).symm
    have hEA₁S : E ⊔ A₁ ≤ S :=
      sup_le (((omegaOneCenterOf_le W).trans hWQ).trans hQS) (inf_le_left.trans hAS)
    have hrelE : A₁.relIndex E ≤ 2 ^ j := by
      have h3 := Subgroup.relIndex_mul_card A₁ (E ⊔ A₁)
      have e : A₁ ⊓ (E ⊔ A₁) = A₁ := inf_eq_left.2 le_sup_right
      rw [e] at h3
      have h4 : A₁.relIndex (E ⊔ A₁) * Nat.card ↥A₁ ≤ 2 ^ j * Nat.card ↥A₁ := by
        rw [h3]; exact (hA.2.2 _ (hEA₁S.trans hSY) hEA₁).trans hAcard
      exact (Subgroup.relIndex_le_of_le_right le_sup_left (E3.relIndex_ne_zero' _ _)).trans
        (Nat.le_of_mul_le_mul_right h4 Nat.card_pos)
    have hconjE : ∀ k ∈ K, cjSub k E = E := fun k hk =>
      Subgroup.eq_of_le_of_card_ge (cjSub_le (hKE hk) le_rfl) (by rw [card_cjSub])
    have hgen : ∀ k ∈ K, cjSub k A ≤ Φ := by
      intro k hk
      have hD₁ : D ⊓ cjSub k A₁ ∈ dFam j S := by
        refine ⟨inf_le_left, ?_⟩
        have h5 : (cjSub k A₁).relIndex E = A₁.relIndex E := by
          conv_lhs => rw [← hconjE k hk]
          exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k).injective
        have h6 : (cjSub k A₁).relIndex D ≤ (cjSub k A₁).relIndex E :=
          Subgroup.relIndex_le_of_le_right hDE (E3.relIndex_ne_zero' _ _)
        have h7 := Subgroup.relIndex_mul_card (cjSub k A₁) D
        calc Nat.card ↥D = (cjSub k A₁).relIndex D * Nat.card ↥(cjSub k A₁ ⊓ D) := h7.symm
          _ ≤ 2 ^ j * Nat.card ↥(D ⊓ cjSub k A₁) := by
            rw [inf_comm]; exact Nat.mul_le_mul_right _ (h6.trans (h5 ▸ hrelE))
      refine le_iSup₂_of_le (f := fun D₁ (_ : D₁ ∈ dFam j S) =>
        Y ⊓ Subgroup.centralizer (D₁ : Set G)) (D ⊓ cjSub k A₁) hD₁ ?_
      refine le_inf (cjSub_le (hKY hk) hA.1) ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy2 : y ∈ cjSub k A₁ := (Subgroup.mem_inf.1 hy).2
      rw [mem_cjSub] at hx hy2
      have hc : (k⁻¹ * y * k) * (k⁻¹ * x * k) = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by
        have := hA.2.1.1
        exact setLike_mul_comm (Subgroup.mem_inf.1 hy2).1 hx
      have e1 : y * x = k * ((k⁻¹ * y * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
      have e2 : x * y = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
      rw [e1, e2, hc]
    calc twoResidual K ≤ conjClosure A K := E1.twoResidual_le_conjClosure ⟨j, hK⟩
      _ ≤ Φ := conjClosure_le fun k hk a ha =>
          hgen k hk (by rw [mem_cjSub]; simpa [mul_assoc] using ha)

end E5
end CFSG.Quasithin
