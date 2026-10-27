module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushNatMain
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Off

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

namespace F53.Stellmacher.S29

variable {G : Type} [Group G] [Finite G]

namespace S29Count

set_option maxRecDepth 100000 in
theorem fixW_That_aux : ∀ u : orth.W, (∀ σ ∈ S5ThatF, orth.act σ u = u) →
    ∀ σ ∈ S5TF, ∀ τ ∈ S5SylF, orth.act τ (orth.act σ u * u⁻¹) = orth.act σ u * u⁻¹ := by
  unfold S5ThatF S5TF S5SylF
  decide +kernel

theorem commutator_mem_fixW_Syl {u : orth.W} (hu : u ∈ fixW orth S5That) {σ : Equiv.Perm (Fin 5)}
    (hσ : σ ∈ S5T) : orth.act σ u * u⁻¹ ∈ fixW orth S5Syl := by
  rw [mem_S5T_iff] at hσ
  intro τ hτ
  exact fixW_That_aux u (fun ρ hρ => hu ρ ((mem_S5That_iff ρ).mpr hρ)) σ hσ τ
    ((mem_S5Syl_iff τ).mp hτ)

omit [Finite G] in
theorem cSecIn_bot_eq (X Z : Subgroup G) :
    cSecIn X ⊥ Z = X ⊓ Subgroup.centralizer (Z : Set G) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro f ⟨hfX, hf⟩
    refine ⟨hfX, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have h1 := hf z hz
    rw [Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · rintro f ⟨hfX, hf⟩
    refine Subgroup.subset_closure ⟨hfX, fun x hx => ?_⟩
    rw [Subgroup.mem_bot]
    have h1 : x * f = f * x := Subgroup.mem_centralizer_iff.mp hf x hx
    rw [show f * x = x * f from h1.symm]
    group

theorem pushHyp {X S Z : Subgroup G} (hS : IsSylowTwoOf S X)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)))
    (hZ : IsOrthSec X ⊥ Z ∨ IsNatSec X ⊥ Z) (hZX : Z ≤ X) : PushHyp X S Z := by
  have hza := zaFacts_of_modelSec hS hq hZ
  obtain ⟨M, hM⟩ : ∃ M : Model 5, IsModelSec M X ⊥ Z := by
    rcases hZ with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have hcS : cSecIn X ⊥ Z = pCoreOf 2 X := hM.cSecIn_eq_pCoreOf hq
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, by
    have := hza.elemAbelian.2 g.1 g.2
    exact Subtype.ext (by simpa using this)⟩
  refine ⟨hS, hza.normal, hza.elemAbelian,
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZX hza.normal hZ2, ?_⟩
  rw [← hcS, cSecIn_bot_eq]

section Core

variable {X S Z : Subgroup G}

theorem core (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X)
    (hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A)
    (h4 : (Z ⊓ Subgroup.centralizer (thompsonJ S : Set G)).relIndex Z ≤ 4)
    (hgen : ∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X)
    (hidx : 16 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z)
    (hC : Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) = ⊥) :
    Z ≤ thompsonJ S ∧
      Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) ≤ omegaOneCenterOf (thompsonJ S) ∧
      ∀ w ∈ omegaOneCenterOf (thompsonJ S),
        ∃ z ∈ Z ⊓ Subgroup.centralizer (thompsonJ S : Set G),
          ∃ c ∈ Subgroup.centralizer (pResidualOf 2 X : Set G), w = z * c := by
  set J := thompsonJ S with hJdef
  set L := pResidualOf 2 X with hL
  set Q := pCoreOf 2 X with hQ
  set W := omegaOneCenterOf J with hW
  have hSX : S ≤ X := h.le_self
  have hJS : J ≤ S := thompsonJ_le_self S
  have hJX : J ≤ X := hJS.trans hSX
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_pResidualOf X
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  obtain ⟨hmS, -, -, hWWQ⟩ := offender_equality h hA₀ (hall A₀ hA₀ hA₀Q)
  have hZJ : Z ≤ J := le_sup_right.trans (le_thompsonJ_of_isMax' hmS)
  obtain ⟨g₀, hg₀, hgen'⟩ := hgen
  obtain ⟨hIeq, hLI⟩ := conjJoin_eq_sup_cj h hg₀ hgen'
  set I := CFSG.Quasithin.F53Push.conjJoin X J with hI
  set M := W ⊔ Z with hM
  have hIN : ∀ i ∈ I, i ∈ Subgroup.normalizer (M : Set G) := fun i hi =>
    conjJoin_le_normalizer_sup h hall hWWQ hi
  have hWJ : W ≤ J ⊓ Subgroup.centralizer (J : Set G) := omegaOneCenterOf_le_inf J
  have hWX : W ≤ X := hWJ.trans (inf_le_left.trans hJX)
  have hMX : M ≤ X := sup_le hWX (h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
  have hZM : Z ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (Z : Set G) := hMX.trans h.normal
  have hrJ : (M ⊓ Subgroup.centralizer (J : Set G)).relIndex M ≤ 4 := by
    set C := M ⊓ Subgroup.centralizer (J : Set G) with hC
    have hWC : W ≤ C := le_inf le_sup_left (hWJ.trans inf_le_right)
    have hMC : M ≤ Z ⊔ C := sup_le (hWC.trans le_sup_right) le_sup_left
    have h1 : C.relIndex M = (Z ⊓ C).relIndex Z :=
      relIndex_eq_of_le_sup hZM inf_le_left (inf_le_left.trans hMN) hMC
    have h2 : Z ⊓ C = Z ⊓ Subgroup.centralizer (J : Set G) := by
      rw [hC, ← inf_assoc, inf_of_le_left hZM]
    rw [h1, h2]
    exact h4
  have hg₀N : g₀ ∈ Subgroup.normalizer (M : Set G) := hIN g₀ (hLI hg₀)
  have hcount : (M ⊓ Subgroup.centralizer (I : Set G)).relIndex M ≤ 16 := by
    rw [hIeq]
    exact (relIndex_inf_centralizer_sup_cj_le hg₀N).trans
      ((Nat.pow_le_pow_left hrJ 2).trans (by norm_num))
  set D := M ⊓ Subgroup.centralizer (L : Set G) with hD
  have hDM : D ≤ M := inf_le_left
  have hDZ : D ≤ Subgroup.normalizer (Z : Set G) := hDM.trans hMN
  have hDle : D.relIndex M ≤ 16 := by
    refine le_trans (relIndex_le_of_le M ?_) hcount
    exact inf_le_inf_left M (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLI))
  obtain ⟨hMD, -⟩ := eq_sup_centralizer_of_count hZM hMN hDle hidx
  refine ⟨hZJ, ?_, ?_⟩
  · intro z hz
    refine Subgroup.subset_closure ⟨⟨hZJ hz.1, hz.2⟩, ?_⟩
    exact h.elemAbelian.2 z hz.1
  · intro w hw
    obtain ⟨z, hz, c, hc, hwzc⟩ := mem_sup_of_le_normalizer (N := Z) (K := D) hDZ
      (hMD (le_sup_left (a := W) (b := Z) hw))
    refine ⟨z, ⟨hz, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩, c, hc.2, hwzc⟩
    have hjX : j ∈ X := hJX hj
    have hjw : j * w = w * j := Subgroup.mem_centralizer_iff.mp (hWJ hw).2 j hj
    have hjz : j * z * j⁻¹ ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (h.normal hjX) z).mp hz
      exact this
    have hjc : j * c * j⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      conj_mem_centralizer (hXL hjX) hc.2
    have hwj : w = (j * z * j⁻¹) * (j * c * j⁻¹) := by
      calc w = j * w * j⁻¹ := by rw [hjw]; group
        _ = (j * z * j⁻¹) * (j * c * j⁻¹) := by rw [hwzc]; group
    have hmem : z⁻¹ * (j * z * j⁻¹) ∈ Z ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨Z.mul_mem (Z.inv_mem hz) hjz, ?_⟩
      have e : z⁻¹ * (j * z * j⁻¹) = c * (j * c * j⁻¹)⁻¹ := by
        calc z⁻¹ * (j * z * j⁻¹) = z⁻¹ * ((j * z * j⁻¹) * (j * c * j⁻¹)) * (j * c * j⁻¹)⁻¹ := by
              group
          _ = z⁻¹ * w * (j * c * j⁻¹)⁻¹ := by rw [← hwj]
          _ = c * (j * c * j⁻¹)⁻¹ := by rw [hwzc]; group
      rw [e]
      exact Subgroup.mul_mem _ hc.2 (Subgroup.inv_mem _ hjc)
    rw [hC, Subgroup.mem_bot] at hmem
    have e2 : j * z * j⁻¹ = z := by
      calc j * z * j⁻¹ = z * (z⁻¹ * (j * z * j⁻¹)) := by group
        _ = z := by rw [hmem, mul_one]
    calc j * z = (j * z * j⁻¹) * j := by group
      _ = z * j := by rw [e2]

end Core

section Orth

variable {X S Z : Subgroup G}

theorem exists_orthFacts_sec [((⊥ : Subgroup G).subgroupOf Z).Normal] (h : PushHyp X S Z)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hO : IsOrthSec X ⊥ Z) :
    ∃ (θ : ↥X →* Equiv.Perm (Fin 5)) (β : orth.W →* ↥Z ⧸ (⊥ : Subgroup G).subgroupOf Z),
      OrthFacts X S Z ⊥ θ ∧ SecData orth X ⊥ Z θ β := by
  obtain ⟨e⟩ := hq
  obtain ⟨_hn, θ₀, β₀, hθ₀s, hθ₀k, hsd₀⟩ := id hO
  have hZ₀Z : (⊥ : Subgroup G) ≤ Z := bot_le
  have hle : (pCoreOf 2 X).subgroupOf X ≤ θ₀.ker := by
    intro x hx
    have hxQ : (x : G) ∈ pCoreOf 2 X := hx
    rw [hθ₀k, Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨x.2, fun y hy => ?_⟩
    have hc : y * (x : G) = (x : G) * y :=
      Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hxQ) y hy
    have e1 : (x : G) * y * (x : G)⁻¹ * y⁻¹ = 1 := by rw [← hc]; group
    rw [e1]
    exact (⊥ : Subgroup G).one_mem
  have hidx0 : θ₀.ker.index = 120 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθ₀s, Subgroup.card_top, Nat.card_perm]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hker : θ₀.ker = (pCoreOf 2 X).subgroupOf X := by
    have h1 := Subgroup.relIndex_mul_index hle
    have h2 : ((pCoreOf 2 X).subgroupOf X).index = 120 := relIndex_core_eq_120 e
    rw [hidx0, h2] at h1
    have h3 : ((pCoreOf 2 X).subgroupOf X).relIndex θ₀.ker = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) hle
  have hcard : Nat.card ((S.subgroupOf X).map θ₀) = 8 := by
    rw [← Subgroup.relIndex_ker (S.subgroupOf X) θ₀, hker, Subgroup.relIndex_subgroupOf h.le_self]
    exact relIndex_core_sylow_eq_eight h e
  obtain ⟨g, hg⟩ := exists_conj_S5Syl hcard
  have hsd := secData_twist hsd₀ g
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp θ₀, β₀.comp (orth.act g).toMonoidHom,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hsd⟩
  · exact (MulAut.conj g⁻¹).surjective.comp hθ₀s
  · intro x hx
    show (MulAut.conj g⁻¹) (θ₀ ⟨x, hx⟩) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  · rw [← Subgroup.map_map, hg]
    ext σ
    rw [mem_map_conj, mem_map_conj]
    simp [mul_assoc]
  · exact fun A hA => hsd.relIndex_fixSecIn hZ₀Z hA
  · exact fun A z => X1512.mem_fixSecIn hZ₀Z
  · exact (IsModelSec.isSec hO hZ₀Z).normL
  · exact hsd₀.relIndex_eq.trans card_orth

omit [Finite G] in
theorem eq_of_mk_eq_bot [((⊥ : Subgroup G).subgroupOf Z).Normal] {a b : ↥Z}
    (h : (QuotientGroup.mk a : ↥Z ⧸ (⊥ : Subgroup G).subgroupOf Z) = QuotientGroup.mk b) :
    a = b := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.mp (Subtype.ext h)

theorem orth_comm [((⊥ : Subgroup G).subgroupOf Z).Normal] {θ : ↥X →* Equiv.Perm (Fin 5)}
    {β : orth.W →* ↥Z ⧸ (⊥ : Subgroup G).subgroupOf Z}
    (h : PushHyp X S Z) (hF : OrthFacts X S Z ⊥ θ) (hsd : SecData orth X ⊥ Z θ β)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) {k z : G} (hk : k ∈ pResidualOf 2 X ⊓ S)
    (hz : z ∈ Z ⊓ Subgroup.centralizer (thompsonJ S : Set G)) :
    k * z * k⁻¹ * z⁻¹ ∈ Z ⊓ Subgroup.centralizer (S : Set G) := by
  have hkX : k ∈ X := h.le_self hk.2
  have hzZ : z ∈ Z := hz.1
  obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨z, hzZ⟩ : ↥Z))
  have hufix : u ∈ fixW orth S5That := by
    intro σ hσ
    obtain ⟨j, hjX, hjJ, hjθ⟩ := exists_mem_thompsonJ h hF hJ hσ
    obtain ⟨hjz, h1⟩ := hsd.equiv ⟨j, hjX⟩ u ⟨z, hzZ⟩ hu
    have e : j * z * j⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp hz.2 j hjJ]; group
    apply hsd.inj
    rw [← hjθ, h1, hu]
    exact congrArg QuotientGroup.mk (Subtype.ext e)
  have hθS : θ ⟨k, hkX⟩ ∈ S5Syl := by
    rw [← hF.map_S]
    exact ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk.2, rfl⟩
  obtain ⟨_hX, hsgn⟩ := sign_eq_one_of_mem_pResidualOf θ hk.1
  have hθT : θ ⟨k, hkX⟩ ∈ S5T :=
    Subgroup.mem_inf.mpr ⟨hθS, Equiv.Perm.mem_alternatingGroup.mpr hsgn⟩
  have hv := commutator_mem_fixW_Syl hufix hθT
  obtain ⟨hax, hβ⟩ := hsd.beta_comm hkX hu
  refine ⟨hax, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
  have hsX : s ∈ X := h.le_self hs
  obtain ⟨hsy, h2⟩ := hsd.equiv ⟨s, hsX⟩ _ ⟨k * z * k⁻¹ * z⁻¹, hax⟩ hβ
  have hθs : θ ⟨s, hsX⟩ ∈ S5Syl := by
    rw [← hF.map_S]
    exact ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  rw [hv _ hθs, hβ] at h2
  have h3 := congrArg Subtype.val (eq_of_mk_eq_bot h2)
  have h4 : s * (k * z * k⁻¹ * z⁻¹) * s⁻¹ = k * z * k⁻¹ * z⁻¹ := h3.symm
  calc s * (k * z * k⁻¹ * z⁻¹) = (s * (k * z * k⁻¹ * z⁻¹) * s⁻¹) * s := by group
    _ = (k * z * k⁻¹ * z⁻¹) * s := by rw [h4]

end Orth

section Nat

variable {X S Z : Subgroup G}

theorem nat_counts (h : PushHyp X S Z) (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)))
    (hnat : IsNatSec X (zZero X Z) Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    NatCounts X S Z 4 := by
  obtain ⟨e⟩ := he
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := hnat
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_of_quot e
  have hle : φ.ker ≤ θ.ker := fun x hx =>
    (mem_cSecIn_iff_of_ker_hom hθk x.2).mpr (core_le_cSecIn h _ ((hφk x).mp hx))
  have hker : ∀ x : ↥X, θ x = 1 → (x : G) ∈ pCoreOf 2 X := fun x hx =>
    (hφk x).mp (ker_le_of_surjective hφs hθs hle hx)
  have hev : ∀ x : ↥X, (x : G) ∈ pResidualOf 2 X → Equiv.Perm.sign (θ x) = 1 := fun x hx => by
    obtain ⟨hX, hs⟩ := sign_eq_one_of_mem_pResidualOf θ hx
    exact hs
  exact natCounts_of_secData h hJ hsd hker hev (fun τ _ => hθs τ)

theorem hyps_of_natCounts (h : PushHyp X S Z) (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X)
    (hN : NatCounts X S Z 4) :
    (∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A) ∧
    (Z ⊓ Subgroup.centralizer (thompsonJ S : Set G)).relIndex Z ≤ 4 ∧
    (∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X) ∧
    16 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z := by
  have hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A :=
    fun A hA hAQ => le_antisymm (offender_count h hA)
      ((hN.offender_le A hA hAQ).trans (hN.offender_ge A hA hAQ))
  refine ⟨hall, ?_, hN.generated, le_of_eq_of_le (by norm_num) hN.index_ge⟩
  obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
  have hmeq : (Z ⊓ Subgroup.centralizer (A₀ : Set G)).relIndex Z = 4 :=
    le_antisymm ((hall A₀ hA₀ hA₀Q).le.trans (hN.offender_le A₀ hA₀ hA₀Q))
      (hN.offender_ge A₀ hA₀ hA₀Q)
  have h3 : Z ⊓ Subgroup.centralizer (A₀ : Set G) ≤
      Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) := by
    intro x ⟨hxZ, hxA⟩
    refine ⟨hxZ, ?_⟩
    have hle : thompsonJ S ≤ Subgroup.centralizer ({x} : Set G) := by
      refine (hN.thompsonJ_le A₀ hA₀ hA₀Q).trans (sup_le (fun a ha => ?_) (fun q hq => ?_))
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        exact (Subgroup.mem_centralizer_iff.mp hxA a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
        exact (h.core_le_centralizer hq x hxZ)
    show x ∈ Subgroup.centralizer (thompsonJ S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) x rfl).symm
  rw [← hmeq]
  exact relIndex_le_of_le Z h3

end Nat

omit [Finite G] in
theorem four_le_card {Z C : Subgroup G} (hCZ : C ≤ Z) (hZ : Nat.card Z = 16)
    (h4 : C.relIndex Z ≤ 4) : 4 ≤ Nat.card C := by
  have h1 := Subgroup.relIndex_mul_card (H := C) (K := Z)
  rw [inf_of_le_left hCZ, hZ] at h1
  by_contra hlt
  push Not at hlt
  have : C.relIndex Z * Nat.card C ≤ 4 * 3 := Nat.mul_le_mul h4 (by omega)
  omega

end S29Count

theorem step7_counting {X S Z : Subgroup G} (hS : IsSylowTwoOf S X)
    (hq : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)))
    (hZ : IsOrthSec X ⊥ Z ∨ IsNatSec X ⊥ Z) (hZX : Z ≤ X)
    (hC : Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) = ⊥)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    4 ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer (thompsonJ S : Set G)) ∧
    Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) ≤ omegaOneCenterOf (thompsonJ S) ∧
    ∀ k ∈ pResidualOf 2 X ⊓ S, ∀ w ∈ omegaOneCenterOf (thompsonJ S),
      k * w * k⁻¹ * w⁻¹ ∈ Z ⊓ Subgroup.centralizer (S : Set G) := by
  have h := S29Count.pushHyp hS hq hZ hZX
  have hcard : Nat.card Z = 16 := (zaFacts_of_modelSec hS hq hZ).card_eq
  rcases hZ with hO | hN
  · obtain ⟨hn, -⟩ := id hO
    obtain ⟨θ, β, hF, hsd⟩ := S29Count.exists_orthFacts_sec h hq hO
    have hcj := centralizer_thompsonJ h hF hJ
    have hidx : 16 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z := by
      rw [hC, Subgroup.relIndex_bot_left, hcard]
    obtain ⟨-, hCW, hdec⟩ := S29Count.core h hJ
      (fun A hA hAQ => (offender_image h hF hA hAQ).2.2.1) hcj.2.le
      (exists_generated h hF hJ) hidx hC
    refine ⟨S29Count.four_le_card inf_le_left hcard hcj.2.le, hCW, fun k hk w hw => ?_⟩
    obtain ⟨z, hz, c, hc, rfl⟩ := hdec w hw
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc k hk.1
    have hck : c * k⁻¹ = k⁻¹ * c := by
      calc c * k⁻¹ = k⁻¹ * (k * c) * k⁻¹ := by group
        _ = k⁻¹ * (c * k) * k⁻¹ := by rw [hkc]
        _ = k⁻¹ * c := by group
    have e : k * (z * c) * k⁻¹ * (z * c)⁻¹ = k * z * k⁻¹ * z⁻¹ := by
      calc k * (z * c) * k⁻¹ * (z * c)⁻¹ = k * z * (c * k⁻¹) * c⁻¹ * z⁻¹ := by group
        _ = k * z * (k⁻¹ * c) * c⁻¹ * z⁻¹ := by rw [hck]
        _ = k * z * k⁻¹ * z⁻¹ := by group
    rw [e]
    exact S29Count.orth_comm h hF hsd hJ hk hz
  · have hnat : IsNatSec X (zZero X Z) Z := by
      unfold zZero
      rw [hC]
      exact hN
    have hNC := S29Count.nat_counts h hq hnat hJ
    obtain ⟨hall, h4, hgen, hidx⟩ := S29Count.hyps_of_natCounts h hJ hNC
    obtain ⟨-, hCW, -⟩ := S29Count.core h hJ hall h4 hgen hidx hC
    obtain ⟨hLS, -, -⟩ := pu1_of_counts h hJ hNC
    refine ⟨S29Count.four_le_card inf_le_left hcard h4, hCW, fun k hk w hw => ?_⟩
    have hkb : k ∈ baum S := hLS hk
    have hkw : w * k = k * w :=
      Subgroup.mem_centralizer_iff.mp (show k ∈ Subgroup.centralizer (omegaOneCenterOf
        (thompsonJ S) : Set G) from hkb.2) w hw
    have e : k * w * k⁻¹ * w⁻¹ = 1 := by rw [← hkw]; group
    rw [e]
    exact one_mem _

end F53.Stellmacher.S29

end CFSG.Quasithin
