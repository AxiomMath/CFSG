module

public import CFSG.Quasithin.Background.B1MoreTenD
public import CFSG.Quasithin.Background.B1MoreElevenC
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B1Red

section Step

variable {V : Type} [CommGroup V] [Finite V]

theorem B1_10_step (hV : ∀ v : V, v ^ 2 = 1) {G K A : Subgroup (MulAut V)}
    (ih : B110Below (Nat.card ↥G)) (hO2 : pCoreOf 2 G = ⊥) (hKG : K ≤ G)
    (hA : IsFFStarOffender G A) (hKA : ⁅K, A⁆ = K)
    (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) : ⁅fittingOf G, K⁆ = ⊥ := by
  by_contra hFK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := fittingOf G with hFdef
  have hFG : F ≤ G := fittingOf_le G
  have hFn : ∀ g ∈ G, ∀ f ∈ F, g * f * g⁻¹ ∈ F := fun g hg f hf => conj_mem_fittingOf hg hf
  have hFodd : ∀ f ∈ F, Odd (orderOf f) := B19Aux.odd_orderOf_of_mem_fittingOf hO2
  have hAG : A ≤ G := hA.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hAnK : A ≤ Subgroup.normalizer (K : Set (MulAut V)) := le_normalizer_of_commutator_eq hKA
  have hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun a ha k hk =>
    B19Aux.conj_mem_of_le_normalizer hAnK ha hk
  have hbotF : ∀ B : Subgroup (MulAut V), B ≤ F → IsElemAbelian2 B → B = ⊥ := by
    intro B hBF hB
    refine (Subgroup.eq_bot_iff_forall B).2 fun b hb => ?_
    exact B19Aux.eq_one_of_odd_orderOf_of_pow (hFodd b (hBF hb)) (k := 1)
      (by rw [pow_one]; exact hB.2 b hb)
  have hG1 : G ≤ F ⊔ (K ⊔ A) := le_sup_of_below hV ih hO2 hKG hA hKA hK le_rfl hFn hFK
  have hC : G ⊓ Subgroup.centralizer (F : Set (MulAut V)) ≤ F :=
    centralizer_fittingOf_le_fittingOf hKG hAG hAel.2 hAK hK hFK hG1
  obtain ⟨B, hBmin, hBA⟩ := exists_isFFStarMin_below hA
  have hBoff : IsFFStarOffender G B := hBmin.1
  set J := ffJP {A | IsFFStarMin G A} G with hJdef
  have hJG : J ≤ G := iSup_le fun A => iSup_le fun _ => iSup_le fun hAG => hAG
  have hBJ : B ≤ J := B19.le_ffJP hBmin hBoff.1
  have hB2 : IsElemAbelian2 B := hBoff.2.2.1
  have hBne : B ≠ ⊥ := hBoff.2.1
  have hF₀ne : ⁅F, J⁆ ≠ ⊥ := by
    intro h
    apply hBne
    apply hbotF B _ hB2
    have h1 : J ≤ Subgroup.centralizer (F : Set (MulAut V)) := by
      rw [Subgroup.commutator_comm] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    intro b hb
    exact hC ⟨hBoff.1 hb, h1 (hBJ hb)⟩
  obtain ⟨s, Hs, hGi, hdir1, hdir2, hcard3, hdirF, -, -, -, -, h5⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.inputB19_holds V hV G hO2 hF₀ne
  set F₀ := ⁅F, J⁆ with hF₀def
  have hKJ : K ≤ ffJ G := K_le_ffJ hKG hA hKA
  have hKF₀ : ∀ k ∈ K, ∀ f ∈ F₀, k * f = f * k :=
    le_centralizer_of_innerDirectProduct (C₀ := ffJP {A | IsFFStarOffender G A}
      (G ⊓ Subgroup.centralizer (F₀ : Set (MulAut V))))
      (fun x hx => (iSup_le fun A => iSup_le fun _ => iSup_le fun hAH => hAH :
        ffJP {A | IsFFStarOffender G A} (G ⊓ Subgroup.centralizer (F₀ : Set (MulAut V))) ≤
          G ⊓ Subgroup.centralizer (F₀ : Set (MulAut V))) hx |>.2)
      hdir1 hdir2 hcard3 hKJ hK
  set E := F ⊓ Subgroup.centralizer (J : Set (MulAut V)) with hEdef
  have hEF : E ≤ fittingOf G := inf_le_left
  have hstable : IsStableFF G {A | IsFFStarMin G A} := B1_7 hV (isFFModule_of_offender hA)
  have hJn : ∀ g ∈ G, ∀ j ∈ J, g * j * g⁻¹ ∈ J := fun g hg j hj => ffJP_conj_mem hstable hg hj
  have hEn : ∀ g ∈ G, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    refine ⟨hFn g hg e he.1, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    have hj' : g⁻¹ * j * g ∈ J := by simpa using hJn g⁻¹ (G.inv_mem hg) j hj
    have h1 : (g⁻¹ * j * g) * e = e * (g⁻¹ * j * g) := Subgroup.mem_centralizer_iff.1 he.2 _ hj'
    calc j * (g * e * g⁻¹) = g * ((g⁻¹ * j * g) * e) * g⁻¹ := by group
      _ = g * (e * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
      _ = (g * e * g⁻¹) * j := by group
  have hFle : F ≤ F₀ ⊔ E := by
    have h2 : fittingOfSub G ≤ F₀ ⊔ E := by
      rw [← hdirF.2.2]
      exact iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩)
    exact h2
  have hEK : ⁅E, K⁆ ≠ ⊥ := by
    intro h
    apply hFK
    have hKE : ∀ k ∈ K, ∀ e ∈ E, k * e = e * k := by
      intro k hk e he
      have h1 : ⁅e, k⁆ ∈ ⁅E, K⁆ := Subgroup.commutator_mem_commutator he hk
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro f hf k hk
    show ⁅f, k⁆ ∈ (⊥ : Subgroup (MulAut V))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hsup : F₀ ⊔ E ≤ Subgroup.centralizer ({k} : Set (MulAut V)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hKF₀ k hk x hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hKE k hk x hx).symm
    have := hsup (hFle hf)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hG2 : G ≤ E ⊔ (K ⊔ A) := le_sup_of_below hV ih hO2 hKG hA hKA hK hEF hEn hEK
  have hKnE : K ≤ Subgroup.normalizer (E : Set (MulAut V)) :=
    le_normalizer_of_conj fun k hk e he => hEn k (hKG hk) e he
  have hAnEK : A ≤ Subgroup.normalizer ((E ⊔ K : Subgroup (MulAut V)) : Set (MulAut V)) :=
    le_normalizer_of_conj fun a ha x hx =>
      conj_mem_sup_of_conj_mem hKnE (fun e he => hEn a (hAG ha) e he)
        (fun k hk => hAK a ha k hk) x hx
  have hG2' : G ≤ (E ⊔ K) ⊔ A := by rw [sup_assoc]; exact hG2
  have hF₀F : F₀ ≤ F :=
    commutator_le_of_normalizes (le_normalizer_of_conj fun j hj f hf => hFn j (hJG hj) f hf)
  have hF₀EK : F₀ ≤ E ⊔ K := fun x hx =>
    mem_of_sq_mem_of_odd (sq_mem_of_mem_sup hAnEK hAel.2 x (hG2' (hFG (hF₀F hx))))
      (hFodd x (hF₀F hx))
  have hFEK : F ≤ E ⊔ K := fun f hf => (sup_le hF₀EK le_sup_left) (hFle hf)
  have hBK : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk => hAK b (hBA hb) k hk
  rcases commutator_eq_or_commute hK hBK with hKB | hcomm
  · have hK5 := h5 B K hBmin hKG hKB
    apply hFK
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro f hf k hk
    show ⁅f, k⁆ ∈ (⊥ : Subgroup (MulAut V))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.1 (hK5 hk).2 f hf
  · have hBE : ∀ b ∈ B, ∀ e ∈ E, b * e = e * b := fun b hb e he =>
      Subgroup.mem_centralizer_iff.1 he.2 b (hBJ hb)
    have hBF : ∀ b ∈ B, ∀ f ∈ F, f * b = b * f := by
      intro b hb f hf
      have hsup : E ⊔ K ≤ Subgroup.centralizer ({b} : Set (MulAut V)) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hBE b hb x hx).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hcomm b hb x hx).symm
      have := hsup (hFEK hf)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    have hBle : B ≤ F := fun b hb =>
      hC ⟨hAG (hBA hb), Subgroup.mem_centralizer_iff.2 fun f hf => hBF b hb f hf⟩
    exact hBne (hbotF B hBle hB2)

end Step

end B1Red

end CFSG.Quasithin
