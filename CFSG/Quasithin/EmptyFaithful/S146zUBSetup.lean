module

public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.F918C7
public import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.Quasithin.EmptyFaithful.SBc16SAut

public section

namespace CFSG.Quasithin.S146zU.UB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section KBar

variable {G : Type} [Group G]

noncomputable def kbarEquivOTwo (K : Subgroup G) : KBar K ≃* OTwoQuot K :=
  (kbarEquiv K).trans (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K))

theorem isSimpleGroup_kbar_of_equiv_L216 {K : Subgroup G}
    (e : Nonempty (OTwoQuot K ≃* SBc16.L216)) : IsSimpleGroup (KBar K) := by
  obtain ⟨e⟩ := e
  have := SBc16.isSimpleGroup_L216
  exact ((kbarEquivOTwo K).trans e).isSimpleGroup

theorem not_isPSL_three_two_of_L216 {X : Type} [Group X] (e : Nonempty (X ≃* SBc16.L216))
    (h : IsPSL 3 2 1 X) : False := by
  obtain ⟨e⟩ := e
  have h1 : Nat.card X = 168 := card_eq_168_of_isPSL_three_two h
  have h2 : Nat.card X = 4080 := by
    rw [Nat.card_congr e.toEquiv]
    exact SBc16.card_L216
  omega

end KBar

section Conj

variable {G : Type} [Group G]

theorem conjClosure_ne_self {K T : Subgroup G} {s : G} (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K : Set G)) : conjClosure K T ≠ K := by
  intro h
  apply hsN
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have := mem_conjClosure hsT hz
    rwa [h] at this
  · intro hz
    have := mem_conjClosure (T.inv_mem hsT) hz
    rw [h] at this
    simpa [mul_assoc] using this

theorem conjClosure_eq_sup_conjSub {K T Kz : Subgroup G} {s : G} (hsT : s ∈ T)
    (hKz : Kz = K ⊔ conjSub s K) (hTn : T ≤ Subgroup.normalizer (Kz : Set G)) :
    conjClosure K T = K ⊔ conjSub s K := by
  apply le_antisymm
  · refine conjClosure_le fun t ht z hz => ?_
    have hzK : z ∈ Kz := hKz ▸ Subgroup.mem_sup_left hz
    have := (Subgroup.mem_normalizer_iff.mp (hTn ht) z).mp hzK
    rwa [hKz] at this
  · refine sup_le (le_conjClosure K T) fun x hx => ?_
    have := mem_conjClosure hsT (mem_conjSub.mp hx)
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at this

theorem conjClosure_sup_eq {G₁ K T Kz : Subgroup G} {s : G} (hsT : s ∈ T)
    (hKz : Kz = K ⊔ conjSub s K) (hn : G₁ ≤ Subgroup.normalizer (Kz : Set G))
    (hG₁ : G₁ = Kz ⊔ T) : conjClosure K T ⊔ T = G₁ := by
  have hTG : T ≤ G₁ := hG₁ ▸ le_sup_right
  rw [conjClosure_eq_sup_conjSub hsT hKz (hTG.trans hn), ← hKz, ← hG₁]

end Conj

section Hyp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem hypF918_mcOf (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (S : Setting146 G T M)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hs : IsSimpleGroup (KBar K₁))
    (hK₀ : conjClosure K₁ T ⊔ T = mcOf T) :
    HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) K₁ := by
  have h := hypF918_of_setting146 hA37 hA38 S hK₁ hs
  rwa [hK₀] at h

end Hyp

section Act

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem autIH_ne_bot_of_irrPlusU (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W) :
    autIH V₁ I H K ≠ ⊥ := by
  have hF := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) :=
    isIrrPlusTildeT_of_ambient h hIU W hW hirr
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  rw [autIH_eq_map h (le_of_mem_cComp h.K_cComp)]
  exact map_K_ne_bot h hIU hnt

theorem nonempty_autIH_equiv_L216 (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hne : autIH V₁ I H K ≠ ⊥) (e : Nonempty (OTwoQuot K ≃* SBc16.L216)) :
    Nonempty (↥(autIH V₁ I H K) ≃* SBc16.L216) := by
  obtain ⟨e₁⟩ := e
  have hKbar : IsSimpleGroup (KBar K) := isSimpleGroup_kbar_of_equiv_L216 ⟨e₁⟩
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := MulEquiv.isSimpleGroup (kbarEquiv K).symm
  obtain ⟨e₂⟩ := nonempty_mulEquiv_quotient_autI h hIU hS hne
  exact ⟨e₂.symm.trans ((QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).trans e₁)⟩

omit [Finite G] in
theorem conjSub_le {K : Subgroup G} (hKH : K ≤ H) {t : G} (ht : t ∈ H) : conjSub t K ≤ H := by
  rintro _ ⟨z, hz, rfl⟩
  exact H.mul_mem (H.mul_mem ht (hKH hz)) (H.inv_mem ht)

omit [Finite G] in
theorem conjAutSub_autIH [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hKH : K ≤ H) {t : G} (ht : t ∈ H) :
    conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, ht⟩)
        (autIH V₁ I H K) = autIH V₁ I H (conjSub t K) := by
  rw [autIH_eq_map h hKH, autIH_eq_map h (conjSub_le hKH ht)]
  exact conjAutSub_map_subgroupOf _ ht

omit [Finite G] in
theorem autIH_conjClosure_eq (h : HypF918 T V L V₁ Vp H K) {s : G} (hs : s ∈ H)
    (hK₀ : conjClosure K T = K ⊔ conjSub s K) :
    autIH V₁ I H (conjClosure K T) = autIH V₁ I H K ⊔ autIH V₁ I H (conjSub s K) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKsH : conjSub s K ≤ H := conjSub_le hKH hs
  rw [hK₀, autIH_eq_map h (sup_le hKH hKsH), autIH_eq_map h hKH, autIH_eq_map h hKsH,
    Subgroup.subgroupOf_sup hKH hKsH, Subgroup.map_sup]

end Act

end CFSG.Quasithin.S146zU.UB
