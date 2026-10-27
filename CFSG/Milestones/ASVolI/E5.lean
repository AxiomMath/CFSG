module

public import CFSG.Quasithin.Background.VolIE54
import CFSG.Quasithin.EmptyFaithful.S14113bFStar
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.Quasithin.Background.RonanE51
import CFSG.Quasithin.Background.RonanE52
import CFSG.Quasithin.Background.RonanE53
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI

namespace ChE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1

@[expose] def oTwoPhiFStar {G : Type} [Group G] (K : Subgroup G) : Subgroup G :=
  (((frattiniIn (CFSG.generalizedFitting (↥K ⧸ CFSG.pCore 2 ↥K))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype)

end ChE

open ChE CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.E3

@[expose] def E_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (i j : ℕ), 0 < j → IsSylowIn 2 P ⊤ →
    ∀ A K : Subgroup G, IsElemAbelianCorank P i A → IsE j ⊤ P A K →
      (EOne ↥K (A.subgroupOf K) →
        twoResidual K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ oTwoPhiFStar K) →
      (ETwo ↥K ((P ⊓ K).subgroupOf K) (A.subgroupOf K) →
        twoResidual K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ solvRad K) →
      ∀ W : Subgroup G,
        W = ⨆ (B : Subgroup G) (_ : IsElemAbelianCorank P (i + j) B ∧ B ≤ pCoreOf 2 K), B →
        omegaOneCenterOf (thompsonJi P (i + j)) ≤ omegaOneCenterOf W ∧
          K ≤ Subgroup.normalizer (W : Set G)

theorem as_E_5_1 : E_5_1 := by
  intro G _ _ P i j _ hP A K hA hK h1 h2 W hW
  exact CFSG.Quasithin.RonanE51.e5_1 hP hA hK h1 h2 hW

@[expose] def E_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (i j : ℕ), 0 < j → IsSylowIn 2 P ⊤ →
    nParam (⊤ : Subgroup G) = (j : ℕ∞) → i + j < twoRank G →
      ∀ D : Subgroup G, D = omegaOneCenterOf (thompsonJi P (i + j)) →
        Subgroup.normalizer (thompsonJi P i : Set G) ⊔
          (⨆ (D₁ : Subgroup G) (_ : D₁ ≤ D ∧ mQuot D D₁ ≤ i + j),
            thompsonJi (Subgroup.centralizer (D₁ : Set G)) i) = ⊤

theorem as_E_5_2 : E_5_2 := by
  intro G _ _ P i j hj hP hn hlt D hD
  exact CFSG.Quasithin.RonanE52.e5_2 hj hP hn hlt hD

@[expose] def E_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G), IsSylowIn 2 P ⊤ → Group.IsSolvable G →
    ∀ D : Subgroup G, D = omegaOneCenterOf (thompsonJi P 1) →
      Subgroup.normalizer (thompsonJ P : Set G) ⊔
        (⨆ (D₁ : Subgroup G) (_ : D₁ ≤ D ∧ mQuot D D₁ ≤ 1),
          thompsonJ (Subgroup.centralizer (D₁ : Set G))) = ⊤

theorem as_E_5_3 : E_5_3 := by
  intro G _ _ P hP hG D hD
  subst hD
  exact CFSG.Quasithin.RonanE53.e5_3 hP hG

@[expose] def E_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (j : ℕ), 0 < j → IsSylowIn 2 P ⊤ →
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup G) →
    CFSG.IsQuasisimple ↥(CFSG.generalizedFitting (G ⧸ CFSG.pCore 2 G)) →
    (∀ q : G ⧸ CFSG.pCore 2 G, ∃ e : ℕ, q ^ 2 ^ e ∈ CFSG.generalizedFitting (G ⧸ CFSG.pCore 2 G)) →
    CFSG.Open.pRank 2 (⊤ : Subgroup (G ⧸ CFSG.pCore 2 G)) ≤ j →
    (∀ X : Subgroup G, X.Normal → pCoreOf 2 (⊤ : Subgroup G) ≤ X → X ≤ solvRad (⊤ : Subgroup G) →
      HasNoFaithfulFFModulesMod (⊤ : Subgroup G) X) →
    (Subgroup.normalizer (thompsonJ P : Set G) = ⊤ ∨
      (oTwoUpper (⊤ : Subgroup G) ≤
          Subgroup.centralizer (omegaOneCenterOf (thompsonJi P j) : Set G) ∧
        Subgroup.normalizer (omegaOneCenterOf (thompsonJi P j) : Set G) = ⊤))

private theorem e54_qgf_top_eq (Q : Type) [Group Q] :
    CFSG.Open.quasithinGenFitting (⊤ : Subgroup Q) = CFSG.generalizedFitting Q := by
  have h1 : CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥(⊤ : Subgroup Q) =
      CFSG.generalizedFitting ↥(⊤ : Subgroup Q) :=
    (CFSG.generalizedFitting_eq_componentClassification _).symm
  have h2 := CFSG.WholeGroup.generalizedFitting_map_mulEquiv (Subgroup.topEquiv (G := Q))
  rw [CFSG.Quasithin.quasithinGenFitting_eq_map_subtype, h1, ← h2]
  rfl

private theorem e54_isQuasisimple_gf {Q Q' : Type} [Group Q] [Group Q'] (ψ : Q ≃* Q')
    (h : CFSG.IsQuasisimple ↥(CFSG.generalizedFitting Q')) :
    CFSG.IsQuasisimple ↥(CFSG.generalizedFitting Q) := by
  have hq : CFSG.IsQuasisimple ↥((CFSG.generalizedFitting Q).map ψ.toMonoidHom) := by
    rw [CFSG.WholeGroup.generalizedFitting_map_mulEquiv ψ]
    exact h
  exact CFSG.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective) hq

private theorem e54_mem_gf {Q Q' : Type} [Group Q] [Group Q'] (ψ : Q ≃* Q') {q : Q}
    (h : ψ q ∈ CFSG.generalizedFitting Q') : q ∈ CFSG.generalizedFitting Q := by
  rw [← CFSG.WholeGroup.generalizedFitting_map_mulEquiv ψ] at h
  obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp h
  have hx' : x = q := ψ.injective hxq
  exact hx' ▸ hx

private theorem e54_pRank_top {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (ψ : Q ≃* Q') :
    CFSG.Open.pRank 2 (⊤ : Subgroup Q) = CFSG.Open.pRank 2 (⊤ : Subgroup Q') := by
  rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank 2 (⊤ : Subgroup Q),
    ← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank 2 (⊤ : Subgroup Q')]
  exact CFSG.pRank_congr_of_mulEquiv
    ((Subgroup.topEquiv (G := Q)).trans (ψ.trans (Subgroup.topEquiv (G := Q')).symm)) 2

set_option linter.unusedVariables false in
theorem as_E_5_4 : E_5_4 := by
  intro G _ _ P j hj hP hchar hqs hgen hrank hFF
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have hpc : (CFSG.pCore 2 ↥(⊤ : Subgroup G)).map e.toMonoidHom = CFSG.pCore 2 G :=
    CFSG.pCore_map_iso 2 e
  let ψ : (↥(⊤ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup G)) ≃* (G ⧸ CFSG.pCore 2 G) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥(⊤ : Subgroup G)) (CFSG.pCore 2 G) e hpc
  have hqs' : CFSG.IsQuasisimple ↥(CFSG.Open.quasithinGenFitting
      (⊤ : Subgroup (↥(⊤ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup G)))) := by
    rw [e54_qgf_top_eq]
    exact e54_isQuasisimple_gf ψ hqs
  have h2' : ∀ q : ↥(⊤ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup G),
      ∃ n : ℕ, q ^ 2 ^ n ∈ CFSG.Open.quasithinGenFitting
        (⊤ : Subgroup (↥(⊤ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup G))) := by
    intro q
    obtain ⟨n, hn⟩ := hgen (ψ q)
    refine ⟨n, ?_⟩
    rw [e54_qgf_top_eq]
    apply e54_mem_gf ψ
    rw [map_pow]
    exact hn
  have hrank' : CFSG.Open.pRank 2
      (⊤ : Subgroup (↥(⊤ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup G))) ≤ j := by
    rw [e54_pRank_top ψ]
    exact hrank
  have key := CFSG.Quasithin.VolI.AS_I_E_5_4'_holds G ⊤ P j hj hP hchar hqs' h2' hrank'
    (fun Y hYn hY1 hY2 => hFF Y (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : Y ≤ ⊤)).mp hYn))) hY1 hY2)
  rcases key with hk1 | ⟨hk2, hk3⟩
  · exact Or.inl (top_le_iff.mp hk1)
  · exact Or.inr ⟨hk2, top_le_iff.mp hk3⟩

@[expose] def E_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G →
    ∀ (Q V : Subgroup G) [Q.Normal] [V.Normal] (j : ℕ), V ≤ omegaOneCenterOf Q →
      (∀ Ab : Subgroup (G ⧸ Q), IsElemAbelian 2 Ab → Ab ≠ ⊥ →
        rk ↥Ab + j < mQuot V (V ⊓ Subgroup.centralizer ((Ab.comap (QuotientGroup.mk' Q) : Subgroup G) : Set G))) →
      thompsonJi (⊤ : Subgroup G) j ≤ Q

private theorem e55_card_pow {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : ∃ k : ℕ, Nat.card E = 2 ^ k := by
  have : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  exact (IsPGroup.iff_card (p := 2)).mp this

private theorem e55_card_le_two_pow {G : Type} [Group G] [Finite G] {E H : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ CFSG.Open.pRank 2 H := by
  obtain ⟨k, hk⟩ := e55_card_pow hE
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num)
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hEH hE hk)

set_option linter.unusedVariables false in
theorem as_E_5_5 : E_5_5 := by
  intro G _ _ _ Q V _ _ j hV hyp
  have hVea : IsElemAbelian 2 V :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hV (CFSG.Quasithin.B2F.isElemAbelian_omegaOneCenterOf Q)
  have hVQ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := by
    intro v hv q hq
    have hvc : v ∈ centerOf Q := by
      have hle : omegaOneCenterOf Q ≤ centerOf Q := by
        unfold omegaOneCenterOf omegaOneOf
        exact (Subgroup.closure_le _).2 fun x hx => hx.1
      exact hle (hV hv)
    exact (Subgroup.mem_centralizer_iff.1 hvc.2 q hq).symm
  unfold thompsonJi
  refine iSup₂_le fun A hA => ?_
  obtain ⟨-, hAea, hAcard⟩ := hA
  by_contra hAQ
  set Ab : Subgroup (G ⧸ Q) := A.map (QuotientGroup.mk' Q) with hAbdef
  have hAbea : IsElemAbelian 2 Ab :=
    CFSG.Quasithin.E1.isElemAbelian_map' (QuotientGroup.mk' Q) hAea
  have hAbne : Ab ≠ ⊥ := by
    intro h
    apply hAQ
    rw [hAbdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have hyp' := hyp Ab hAbea hAbne
  set Cz : Subgroup G := V ⊓ Subgroup.centralizer
    (((Ab.comap (QuotientGroup.mk' Q) : Subgroup G)) : Set G) with hCz
  have hdec : ∀ y ∈ Ab.comap (QuotientGroup.mk' Q), ∃ a ∈ A, ∃ q ∈ Q, y = a * q := by
    intro y hy
    have hy' : (QuotientGroup.mk' Q) y ∈ A.map (QuotientGroup.mk' Q) := hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hy'
    exact ⟨a, ha, a⁻¹ * y, QuotientGroup.eq.1 hay, (mul_inv_cancel_left a y).symm⟩
  have hcomm : ∀ v ∈ V, ∀ b ∈ A ⊓ Q, v * b = b * v := fun v hv b hb => hVQ v hv b hb.2
  have hVKCz : V ⊓ (A ⊓ Q) ≤ Cz := by
    intro x hx
    obtain ⟨hxV, hxAQ⟩ := hx
    have hxC : x ∈ Subgroup.centralizer
        (((Ab.comap (QuotientGroup.mk' Q) : Subgroup G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, ha, q, hq, rfl⟩ := hdec y hy
      have hax : a * x = x * a := CFSG.Quasithin.B2F.isElemAbelian_comm hAea ha hxAQ.1
      have hxq : x * q = q * x := hVQ x hxV q hq
      calc a * q * x = a * (q * x) := by group
        _ = a * (x * q) := by rw [hxq]
        _ = (a * x) * q := by group
        _ = (x * a) * q := by rw [hax]
        _ = x * (a * q) := by group
    have hxmem : x ∈ V ⊓ Subgroup.centralizer
        (((Ab.comap (QuotientGroup.mk' Q) : Subgroup G)) : Set G) :=
      Subgroup.mem_inf.2 ⟨hxV, hxC⟩
    exact hxmem
  have hAeq : Nat.card A = Nat.card Ab * Nat.card ↥(A ⊓ Q) := by
    have h1 : Q.relIndex A * Nat.card ↥(Q ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card Q A
    have h2 : Q.relIndex A = Nat.card Ab := by
      have := Subgroup.relIndex_ker (QuotientGroup.mk' Q) (K := A)
      rw [QuotientGroup.ker_mk'] at this
      exact this
    rw [inf_comm] at h1
    rw [← h1, h2]
  obtain ⟨ρ, hρ⟩ := e55_card_pow hAbea
  have hrk : CFSG.Quasithin.rk ↥Ab = ρ := by
    unfold CFSG.Quasithin.rk
    rw [hρ, padicValNat.prime_pow]
  rw [hrk] at hyp'
  have hBea : IsElemAbelian 2 (V ⊔ (A ⊓ Q)) :=
    B2F.isElemAbelian_sup_of_commute hVea (CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left hAea)
      hcomm
  have hBle : Nat.card ↥(V ⊔ (A ⊓ Q)) ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
    e55_card_le_two_pow le_top hBea
  have hprod : Nat.card ↥(V ⊔ (A ⊓ Q)) * Nat.card ↥(V ⊓ (A ⊓ Q)) =
      Nat.card V * Nat.card ↥(A ⊓ Q) :=
    B2F.card_sup_mul_card_inf_of_commute hcomm
  have hKpos : 0 < Nat.card ↥(A ⊓ Q) := Nat.card_pos
  have hVKle : Nat.card V ≤ 2 ^ ρ * 2 ^ j * Nat.card ↥(V ⊓ (A ⊓ Q)) := by
    have h1 : Nat.card V * Nat.card ↥(A ⊓ Q) ≤
        (2 ^ ρ * 2 ^ j * Nat.card ↥(V ⊓ (A ⊓ Q))) * Nat.card ↥(A ⊓ Q) := by
      rw [← hprod]
      calc Nat.card ↥(V ⊔ (A ⊓ Q)) * Nat.card ↥(V ⊓ (A ⊓ Q))
          ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup G) * Nat.card ↥(V ⊓ (A ⊓ Q)) :=
            Nat.mul_le_mul_right _ hBle
        _ = Nat.card A * 2 ^ j * Nat.card ↥(V ⊓ (A ⊓ Q)) := by rw [← hAcard]
        _ = (Nat.card Ab * Nat.card ↥(A ⊓ Q)) * 2 ^ j * Nat.card ↥(V ⊓ (A ⊓ Q)) := by
            rw [hAeq]
        _ = (2 ^ ρ * 2 ^ j * Nat.card ↥(V ⊓ (A ⊓ Q))) * Nat.card ↥(A ⊓ Q) := by
            rw [hρ]; ring
    exact Nat.le_of_mul_le_mul_right h1 hKpos
  have hCzrel : Cz.relIndex V * Nat.card ↥(Cz ⊓ V) = Nat.card V :=
    Subgroup.relIndex_mul_card Cz V
  have hCzpos : 0 < Nat.card ↥(Cz ⊓ V) := Nat.card_pos
  have hmono : Nat.card ↥(V ⊓ (A ⊓ Q)) ≤ Nat.card ↥(Cz ⊓ V) :=
    Subgroup.card_le_of_le (le_inf hVKCz inf_le_left)
  have hIle : Cz.relIndex V ≤ 2 ^ ρ * 2 ^ j := by
    have h1 : Cz.relIndex V * Nat.card ↥(Cz ⊓ V) ≤ (2 ^ ρ * 2 ^ j) * Nat.card ↥(Cz ⊓ V) := by
      rw [hCzrel]
      exact hVKle.trans (Nat.mul_le_mul_left _ hmono)
    exact Nat.le_of_mul_le_mul_right h1 hCzpos
  have hI0 : Cz.relIndex V ≠ 0 := by
    intro h
    rw [h, zero_mul] at hCzrel
    exact Nat.card_pos.ne' hCzrel.symm
  have hle : 2 ^ padicValNat 2 (Cz.relIndex V) ≤ Cz.relIndex V :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hI0) pow_padicValNat_dvd
  have hfin : padicValNat 2 (Cz.relIndex V) ≤ ρ + j := by
    have h2 := hle.trans hIle
    rw [← pow_add] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  change ρ + j < padicValNat 2 (Cz.relIndex V) at hyp'
  omega

end CFSG.ASVolI
