module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Count
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CosetGeom
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_inf_of {g : G} {B C : Subgroup G}
    (hB : g ∈ Subgroup.normalizer (B : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((B ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hB hC ⊢
  intro x
  exact ⟨fun hx => ⟨(hB x).mp hx.1, (hC x).mp hx.2⟩, fun hx => ⟨(hB x).mpr hx.1, (hC x).mpr hx.2⟩⟩

theorem mem_normalizer_sup_of {g : G} {B C : Subgroup G}
    (hB : g ∈ Subgroup.normalizer (B : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) :=
  mem_normalizer_of_cj_le (by
    have : cj g (B ⊔ C) = cj g B ⊔ cj g C := Subgroup.map_sup _ _ _
    rw [this, cj_eq_of_mem_normalizer hB, cj_eq_of_mem_normalizer hC])

namespace SitSigma

variable {δ μ : Geo H M} {X : Subgroup G}

theorem omegaOneCenter_le_Qv (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) :
    quasithinOmegaOneCenter (Qv μ ⊓ X) ≤ Qv δ := by
  obtain ⟨-, -, hQA2, -⟩ := h.counts hA hPn hQ0
  set W := quasithinOmegaOneCenter (Qv μ ⊓ X) with hW
  have hWQ : W ≤ pCoreOf 2 X :=
    ((CFSG.Quasithin.le_conjClosure W X).trans (h.pushHyp hA).le_core)
  have hQP : pCoreOf 2 X ≤ Qv μ ⊓ X := h.R_le_P
  have hQn : pCoreOf 2 X ≤ Subgroup.normalizer (Qv δ : Set G) :=
    (hQP.trans (inf_le_right.trans h.le_stab)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ))
  have hrel : (Qv δ).relIndex (Qv δ ⊔ pCoreOf 2 X) = 2 := by
    rw [relIndex_sup_eq_relIndex_inf_right hQn, inf_comm]
    have : (pCoreOf 2 X ⊓ Qv δ) = Qv μ ⊓ X ⊓ Qv δ :=
      le_antisymm (inf_le_inf_right _ hQP) (le_inf h.inf_inf_Qv_le_core inf_le_right)
    rw [this]; exact hQA2
  have hAW : Qv δ ≤ Qv δ ⊔ W := le_sup_left
  have hWle : Qv δ ⊔ W ≤ Qv δ ⊔ pCoreOf 2 X := sup_le_sup_left hWQ _
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hAW hWle
  rw [hrel] at hmul
  have hdvd : (Qv δ).relIndex (Qv δ ⊔ W) ∣ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h2] at hmul
    have h3 : (Qv δ ⊔ W).relIndex (Qv δ ⊔ pCoreOf 2 X) = 1 := by omega
    have hle := Subgroup.relIndex_eq_one.mp h3
    have heq : Qv δ ⊔ W = pCoreOf 2 X ⊔ Qv δ := by
      rw [sup_comm (pCoreOf 2 X)]; exact le_antisymm hWle hle
    refine h.not_edge_le_normalizer_sup hA hQ0 ?_
    rw [← heq]
    intro e he
    refine mem_normalizer_sup_of ?_ ?_
    · exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)) he.1
    · exact A4.normalizer_le_normalizer_omegaOneCenterOf (Qv μ ⊓ X) (hPn he.2)

theorem conjClosure_le_Qv (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) :
    CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X ≤ Qv δ := by
  refine CFSG.Quasithin.conjClosure_le fun x hx z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ) (h.le_stab hx)) z).mp
    (h.omegaOneCenter_le_Qv hA hPn hQ0 hz)

theorem conj_edge_le (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) {s : G} (hs : s ∈ stab δ ⊓ stab μ) :
    cj s (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X) ≤ pCoreOf 2 X ∧
      CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X ≤ cj s (pCoreOf 2 X) := by
  set Z := CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X with hZ
  have hZA : Z ≤ Qv δ := h.conjClosure_le_Qv hA hPn hQ0
  have hZQ : Z ≤ pCoreOf 2 X := (h.pushHyp hA).le_core
  have hQP : pCoreOf 2 X ≤ Qv μ ⊓ X := h.R_le_P
  have hZPA : Z ≤ Qv μ ⊓ X ⊓ Qv δ := le_inf (hZQ.trans hQP) hZA
  have key : ∀ t ∈ stab δ ⊓ stab μ, cj t Z ≤ pCoreOf 2 X := by
    intro t ht
    have hn : t ∈ Subgroup.normalizer ((Qv μ ⊓ X ⊓ Qv δ : Subgroup G) : Set G) :=
      mem_normalizer_inf_of (hPn ht.2)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ) ht.1)
    exact (cj_le_of_le_of_mem_normalizer hn hZPA).trans h.inf_inf_Qv_le_core
  refine ⟨key s hs, ?_⟩
  have h1 := cj_mono s (key s⁻¹ ((stab δ ⊓ stab μ).inv_mem hs))
  rwa [cj_cj, mul_inv_cancel, cj_one] at h1

theorem relIndex_edge_stab_true (hA : F53Amalgam H M S) {δ μ : Geo H M}
    (hμ : (graph (H ⊔ M) H M).Adj δ μ) (hv : vtype δ = false) :
    vtype μ = true ∧ (stab δ ⊓ stab μ).relIndex (stab μ) = 3 ∧
      (Qv μ).relIndex (stab δ ⊓ stab μ) = 2 := by
  have hne := vtype_ne_of_adj hμ
  have hvμ : vtype μ = true := by
    cases h' : vtype μ
    · exact absurd (hv.trans h'.symm) hne
    · rfl
  have hδ : δ ∈ nbrs μ := hμ.symm
  refine ⟨hvμ, ?_, ?_⟩
  · have h1 := card_nbrs_eq_relIndex_geom hδ
    rw [card_nbrs_true hA hvμ, inf_comm] at h1
    exact h1.symm
  · rw [inf_comm]
    exact relIndex_Qv_inf_true hA hδ hvμ

theorem mem_normalizer_of_le {Q : Subgroup G} {g : G} {K : Subgroup G} (hg : g ∈ K)
    (hn : ∀ n ∈ K, n ∈ Subgroup.normalizer (Q : Set G) → n ∈ Subgroup.normalizer ((cj g Q : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.normalizer (Q : Set G) ⊓ K : Subgroup G) : Set G) := by
  set N0 : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ K with hN0
  have hcj : cj g⁻¹ N0 ≤ N0 := by
    intro x hx
    rw [mem_cj] at hx
    simp only [inv_inv] at hx
    have h1 := hn _ hx.2 hx.1
    rw [mem_normalizer_cj_iff] at h1
    refine ⟨?_, ?_⟩
    · have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h1
    · have := K.mul_mem (K.mul_mem (K.inv_mem hg) hx.2) hg
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at this
  have := mem_normalizer_of_cj_le hcj
  simpa using Subgroup.inv_mem _ this

theorem conj_le_core (hBau : BaumannS3 G) (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) (hQδ : ¬ Qv δ ≤ Qv μ)
    (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) {y : G} (hy : y ∈ stab μ) :
    cj y (CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X) ≤ pCoreOf 2 X := by
  by_contra hyZ
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hB := hBau _ _ _ hPH he hnc
  obtain ⟨hv, -, -, hAP2⟩ := h.counts hA hPn hQ0
  obtain ⟨hvμ, hE3, hEμ2⟩ := relIndex_edge_stab_true hA h.adj hv
  set Z := CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ X)) X with hZ
  set Q := pCoreOf 2 X with hQ
  have hne := commutator_ne_bot_of_not_le hPH (hPn hy) hyZ
  obtain ⟨h1, h2, -, h4⟩ := prop41_s3 hPH he hnc hB (hPn hy) hne
  have h4' : ∀ n ∈ stab μ, n ∈ Subgroup.normalizer (Q : Set G) →
      n ∈ Subgroup.normalizer ((cj y Q : Subgroup G) : Set G) :=
    fun n hn hnQ => h4 n (hPn hn) hnQ
  set Nμ : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ stab μ with hNμ
  have hev : 2 ∣ Nμ.relIndex (stab μ) := two_dvd_relIndex hy h1 h2 h4'
  have hyN : y ∈ Subgroup.normalizer (Nμ : Set G) := mem_normalizer_of_le hy h4'
  have hEQ : ¬ stab δ ⊓ stab μ ≤ Subgroup.normalizer (Q : Set G) := fun hE =>
    h.not_edge_le_normalizer_sup hA hQ0 fun e he => mem_normalizer_sup_of (hE he)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ) he.1)
  obtain ⟨s, hsE, hsQ⟩ : ∃ s ∈ stab δ ⊓ stab μ, s ∉ Subgroup.normalizer (Q : Set G) := by
    by_contra hcon
    exact hEQ fun g hg => by_contra fun hn => hcon ⟨g, hg, hn⟩
  set T₀ : Subgroup G := Qv δ ⊔ (Qv μ ⊓ X) with hT₀
  have hT₀E : T₀ ≤ stab δ ⊓ stab μ := sup_le (h.Qv_le_edge hA) (h.P_le_edge hA)
  have hT₀N : T₀ ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (h.Qv_le_normalizer_core hA hPn) (P_le_normalizer_core μ X)
  have hT₀Nμ : T₀ ≤ Nμ := le_inf hT₀N (hT₀E.trans inf_le_right)
  have hNE : Subgroup.normalizer (Q : Set G) ⊓ (stab δ ⊓ stab μ) = T₀ := by
    refine le_antisymm ?_ (le_inf hT₀N hT₀E)
    have hmul := Subgroup.relIndex_mul_relIndex T₀
      (Subgroup.normalizer (Q : Set G) ⊓ (stab δ ⊓ stab μ)) (stab δ ⊓ stab μ)
      (le_inf hT₀N hT₀E) inf_le_right
    rw [hAP2] at hmul
    have hb1 : (Subgroup.normalizer (Q : Set G) ⊓ (stab δ ⊓ stab μ)).relIndex
        (stab δ ⊓ stab μ) ≠ 1 := fun hh =>
      hEQ (fun e he => (Subgroup.relIndex_eq_one.mp hh he).1)
    have hdvd : (Subgroup.normalizer (Q : Set G) ⊓ (stab δ ⊓ stab μ)).relIndex
        (stab δ ⊓ stab μ) ∣ 2 := ⟨_, hmul.symm.trans (mul_comm _ _)⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
    · exact absurd hh hb1
    · rw [hh] at hmul
      have : T₀.relIndex (Subgroup.normalizer (Q : Set G) ⊓ (stab δ ⊓ stab μ)) = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp this
  have hT₀6 : T₀.relIndex (stab μ) = 6 := by
    rw [← Subgroup.relIndex_mul_relIndex T₀ (stab δ ⊓ stab μ) (stab μ) hT₀E inf_le_right,
      hAP2, hE3]
  have hdvd6 : Nμ.relIndex (stab μ) ∣ 6 := hT₀6 ▸ Subgroup.relIndex_dvd_of_le_left (stab μ) hT₀Nμ
  have hn2 : Nμ.relIndex (stab μ) ≠ 2 := by
    intro h2'
    have hidx : (Nμ.subgroupOf (stab μ)).index = 2 := h2'
    have hsμ : s ∈ stab μ := hsE.2
    have hsN : s ∉ Nμ := fun hh => hsQ hh.1
    have hyNμ : y ∉ Nμ := fun hh => h2 hh.1
    have key := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨s, hsμ⟩ : ↥(stab μ))⁻¹) (b := ⟨y, hy⟩)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
    have hmem : s⁻¹ * y ∈ Nμ := by
      have := key.mpr (by
        constructor
        · intro hh; exact absurd (by simpa using hh) hsN
        · intro hh; exact absurd hh hyNμ)
      simpa using this
    have hcj : cj y Q = cj s Q := by
      have := cj_mul_of_mem_normalizer (a := s) (H := Q) hmem.1
      simpa using this
    have hZs := (h.conj_edge_le hA hPn hQ0 hsE).2
    rw [← hcj] at hZs
    apply hyZ
    calc cj y Z ≤ cj y (cj y Q) := cj_mono y hZs
      _ = Q := by rw [cj_cj, cj_eq_of_mem_normalizer h1]
  have h6 : Nμ.relIndex (stab μ) = 6 := by
    have hmem : Nμ.relIndex (stab μ) ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hdvd6, by norm_num⟩
    rw [show Nat.divisors 6 = {1, 2, 3, 6} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hNμT : Nμ ≤ T₀ := by
    have := Subgroup.relIndex_mul_relIndex T₀ Nμ (stab μ) hT₀Nμ inf_le_right
    rw [hT₀6, h6] at this
    have h1' : T₀.relIndex Nμ = 1 := by omega
    exact (Subgroup.relIndex_eq_one.mp h1')
  have hyT : y ∈ Subgroup.normalizer (T₀ : Set G) := by
    have : Nμ = T₀ := le_antisymm hNμT hT₀Nμ
    rwa [this] at hyN
  have hyQμ : y ∈ Subgroup.normalizer (Qv μ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab μ) hy
  have hyTQ := mem_normalizer_sup_of hyT hyQμ
  have hQμE : Qv μ ≤ stab δ ⊓ stab μ := by
    rw [inf_comm]; exact Qv_le_inf hA h.adj.symm
  have hTE : T₀ ⊔ Qv μ ≤ stab δ ⊓ stab μ := sup_le hT₀E hQμE
  have hEeq : T₀ ⊔ Qv μ = stab δ ⊓ stab μ := by
    refine le_antisymm hTE ?_
    have hmul := Subgroup.relIndex_mul_relIndex (Qv μ) (T₀ ⊔ Qv μ) (stab δ ⊓ stab μ)
      le_sup_right hTE
    rw [hEμ2] at hmul
    have hb1 : (Qv μ).relIndex (T₀ ⊔ Qv μ) ≠ 1 := fun hh =>
      hQδ ((le_sup_left.trans le_sup_left).trans (Subgroup.relIndex_eq_one.mp hh))
    have hdvd : (Qv μ).relIndex (T₀ ⊔ Qv μ) ∣ 2 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
    · exact absurd hh hb1
    · rw [hh] at hmul
      have : (T₀ ⊔ Qv μ).relIndex (stab δ ⊓ stab μ) = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp this
  rw [hEeq] at hyTQ
  have hyE : y ∈ stab δ ⊓ stab μ := by
    set M₂ : Subgroup G := Subgroup.normalizer ((stab δ ⊓ stab μ : Subgroup G) : Set G) ⊓ stab μ
      with hM₂
    have hEM : stab δ ⊓ stab μ ≤ M₂ := le_inf Subgroup.le_normalizer inf_le_right
    have hmul := Subgroup.relIndex_mul_relIndex (stab δ ⊓ stab μ) M₂ (stab μ) hEM inf_le_right
    rw [hE3] at hmul
    have hdvd : (stab δ ⊓ stab μ).relIndex M₂ ∣ 3 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hh | hh
    · exact (Subgroup.relIndex_eq_one.mp hh) ⟨hyTQ, hy⟩
    · exfalso
      rw [hh] at hmul
      have h1' : M₂.relIndex (stab μ) = 1 := by omega
      have hμN : stab μ ≤ Subgroup.normalizer ((stab δ ⊓ stab μ : Subgroup G) : Set G) :=
        fun g hg => (Subgroup.relIndex_eq_one.mp h1' hg).1
      have hle : stab δ ⊓ stab μ ≤ Qv μ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_right : stab δ ⊓ stab μ ≤ stab μ) hμN (h.isPGroup_edge hA)
      have := Subgroup.relIndex_eq_one.mpr hle
      rw [hEμ2] at this
      omega
  exact hyZ (h.conj_edge_le hA hPn hQ0 hyE).1

theorem false_of_D12 (hBau : BaumannS3 G) (hA : F53Amalgam H M S) (h : SitSigma δ μ X)
    (hPn : stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ X : Subgroup G) : Set G))
    (hQ0 : ¬ pCoreOf 2 X ≤ Qv δ) (hQδ : ¬ Qv δ ≤ Qv μ)
    (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) : False := by
  have hPH := h.pushHyp hA
  have hnc := h.noCharNormal hA hPn
  have hB := hBau _ _ _ hPH he hnc
  have hle : conjJoinOf (stab μ) (CFSG.Quasithin.conjClosure
      (quasithinOmegaOneCenter (Qv μ ⊓ X)) X) ≤ pCoreOf 2 X :=
    iSup₂_le fun g hg => h.conj_le_core hBau hA hPn hQ0 hQδ he hg
  refine h.false_of_cor hA (h.Zv_le_conjClosure hA) ⟨hle, le_normalizer_of_core hPH hB ?_ hle ?_⟩
  · exact (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans
      (le_normalizer_conjJoin (stab μ) _)
  · exact F53Push.le_conjJoin

end SitSigma

end CFSG.Quasithin.F53
