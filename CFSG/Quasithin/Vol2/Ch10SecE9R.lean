module

public import CFSG.Quasithin.Vol2.Ch10SecE9P
public import CFSG.Quasithin.Vol2.Ch10SecE9Q
public import CFSG.Quasithin.Vol2.Ch10SecB5EvMain
public import CFSG.Quasithin.Vol2.Ch10SecQ5G1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def Gap10_2_5E9Pt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → ∀ P P' : Subgroup G,
      IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P → IsMaxSubgroupIn (fsuL0 T L ⊔ T) P' → T ≤ P' →
      P ≠ P' → E9Core T L P → E9Core T L P' → False

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem normalizer_le_or_core
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hRed : HeReduce) (hF : H13.FactAutHeSylow)
    (hFa : FactL33M11) (hFc : FactL4L5)
    (h311 : Theorem311Stmt) (hobl : Obl10_2_5Even) (h : MaxCtx T L I t Ψ c)
    (h3 : Case10_1_1Three T L I) (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) ∨
      E9Core T L (preIn Ψ (A.prod A) ⊔ T) := by
  have hP : IsMaxSubgroupIn (fsuL0 T L ⊔ T) (preIn Ψ (A.prod A) ⊔ T) :=
    isMax_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hA
  have hTP : T ≤ preIn Ψ (A.prod A) ⊔ T := le_sup_right
  have hH : InH (XOf T L Ψ A ⊔ T)
      (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) :=
    ⟨(sup_le (oTwoUpper_le _) le_sup_right).trans le_sup_right, pCoreOf_GA_ne_bot h311 h hD hA⟩
  rcases kof_cases h134 hFa hFc h hD hH with hK |
      ⟨K₁, s, hs, hK₁, hsn, hK, htype⟩ | ⟨hK, k, hk45, hk, haut⟩ | ⟨K₁, hK₁, hHK, hXK, he⟩
  · left
    intro g hg
    have h1 := le_normalizer_conjClosure (XOf T L Ψ A)
      (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T))
      (Subgroup.mem_sup_left hg)
    rwa [hK] at h1
  · rcases htype with heven | ⟨p, hp, hp2, ⟨e⟩⟩
    · exact Or.inl (hobl G T L I h.hyp h3 _ hP hTP (Or.inl ⟨K₁, s, hs, hK₁, hsn, hK, heven⟩))
    · by_cases hbad : (p % 8 = 3 ∨ p % 8 = 5) ∧
          pCoreOf 2 (XOf T L Ψ A) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)
      · by_cases hcore : E9Core T L (preIn Ψ (A.prod A) ⊔ T)
        · exact Or.inr hcore
        · left
          have hodd : ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
              n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := fun n hn hno =>
            (mem_normalizer_or_core h311 h hD hA hs hK₁ hsn hK hp hbad.1 e hbad.2 hn
              hno).resolve_right hcore
          have hTN := T1_normal h.h37 h.h38 h.hyp
          have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (T1 T L : Set G)) :=
            ⟨hTN, h.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le h.hyp.fsu.sylow hTN⟩
          refine (C10P34.le_oTwoUpper_sup hTsyl).trans (sup_le ?_ (isXi_XOf h hD).2.1)
          exact (Subgroup.closure_le _).mpr fun n hn => hodd n hn.1 hn.2
      · exact Or.inl (normalizer_T1_le_XOf_L2p h311 h hD hA hs hK₁ hsn hK hp hp2 e
          fun h8 hle => hbad ⟨h8, hle⟩)
  · exact Or.inl (hobl G T L I h.hyp h3 _ hP hTP (Or.inr ⟨hK, k, hk45, hk, haut⟩))
  · exact Or.inl (normalizer_T1_le_XOf_of_he hRed hF h h3 hD hA hH hK₁ hHK hXK he)

omit [Finite G] in
theorem ka_ne_kb : L32.Ka ≠ L32.Kb := by
  intro h
  have hmem : ∀ g : L32.Γ, L32.IsKa g ↔ L32.IsKb g := fun g => by
    rw [show L32.IsKa g ↔ g ∈ L32.Ka from Iff.rfl, h]; rfl
  have : ∃ g : L32.Γ, L32.IsKa g ∧ ¬ L32.IsKb g := by decide +kernel
  obtain ⟨g, h1, h2⟩ := this
  exact h2 ((hmem g).mp h1)

theorem preIn_pa_ne_pb (h : MaxCtx T L I t Ψ c) :
    preIn Ψ (L32.Pa.prod L32.Pa) ⊔ T ≠ preIn Ψ (L32.Pb.prod L32.Pb) ⊔ T := by
  intro heq
  have h1 := imgIn_XOf h parData_a
  have h2 := imgIn_XOf h parData_b
  rw [XOf, heq] at h1
  rw [XOf] at h2
  rw [h1] at h2
  apply ka_ne_kb
  ext g
  constructor
  · intro hg
    have : (g, (1 : L32.Γ)) ∈ L32.Kb.prod L32.Kb := h2 ▸ ⟨hg, L32.Ka.one_mem⟩
    exact this.1
  · intro hg
    have : (g, (1 : L32.Γ)) ∈ L32.Ka.prod L32.Ka := h2.symm ▸ ⟨hg, L32.Kb.one_mem⟩
    exact this.1

theorem normalizer_T1_le_of_bad
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hRed : HeReduce) (hF : H13.FactAutHeSylow)
    (hFa : FactL33M11) (hFc : FactL4L5)
    (h311 : Theorem311Stmt) (hobl : Obl10_2_5Even) (hpt : Gap10_2_5E9Pt)
    (h : MaxCtx T L I t Ψ c) (h3 : Case10_1_1Three T L I) (hD : ParData A K E)
    (hA : A = L32.Pa ∨ A = L32.Pb) {A' K' E' : Subgroup L32.Γ} (hD' : ParData A' K' E')
    (hD2' : ParData2 K' E') (hA' : A' = L32.Pa ∨ A' = L32.Pb)
    (hne : preIn Ψ (A.prod A) ⊔ T ≠ preIn Ψ (A'.prod A') ⊔ T) {K₁ : Subgroup G} {s : G}
    (hs : s ∈ T)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK : conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
      K₁ ⊔ CFSG.conjugate K₁ s)
    {p : ℕ} (hp : p.Prime) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))
    (hbad : pCoreOf 2 (XOf T L Ψ A) ≤ pCoreOf 2 (K₁ ⊔ CFSG.conjugate K₁ s)) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  have hodd : ∀ n ∈ Subgroup.normalizer (T1 T L : Set G), Odd (orderOf n) →
      n ∈ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
    intro n hn hno
    rcases mem_normalizer_or_core h311 h hD hA hs hK₁ hsn hK hp h8 e hbad hn hno with h1 | hcore
    · exact h1
    · exfalso
      rcases normalizer_le_or_core h134 hRed hF hFa hFc h311 hobl h h3 hD' hA' with
        hle | hcore'
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, y, -, hy3, hyT, -⟩ := hcore
        exact E9.false_of_normalizes_XOf h hD' hD2' hy3 hyT (hle hyT)
      · exact hpt G T L I h.hyp h3 _ _ (isMax_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hA)
          le_sup_right (isMax_preIn_sup h.h37 h.h38 h.hyp h.ht h.htn h.hC hA') le_sup_right hne
          hcore hcore'
  have hTN := T1_normal h.h37 h.h38 h.hyp
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (T1 T L : Set G)) :=
    ⟨hTN, h.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le h.hyp.fsu.sylow hTN⟩
  refine (C10P34.le_oTwoUpper_sup hTsyl).trans (sup_le ?_ (isXi_XOf h hD).2.1)
  exact (Subgroup.closure_le _).mpr fun n hn => hodd n hn.1 hn.2

theorem gap10_2_5L2pE9'_of_pt
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hRed : HeReduce) (hF : H13.FactAutHeSylow)
    (hFa : FactL33M11) (hFc : FactL4L5) (h311 : Theorem311Stmt) (hLk : Fact10_2_5Lk2)
    (hpt : Gap10_2_5E9Pt) : Gap10_2_5L2pE9' := by
  intro G _ _ T L I hyp h3 P hP hTP K₁ s hs hK₁ hsn hK hpe hbad
  obtain ⟨p, hp, h8, ⟨e⟩⟩ := hpe
  have hobl := obl10_2_5Even_of hLk h37 h38 h311
  have hinner : T1Inner T L := fun s hs => by
    obtain ⟨x₀, hx₀, hx, -⟩ := inner_of_case3 hyp h3 hs
    exact ⟨x₀, hx₀, hx⟩
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, c, hC⟩ := exists_L0Coord h37 h38 hyp h3.1 hinner ht htn
  have h : MaxCtx T L I t Ψ c := ⟨h37, h38, hyp, ht, htn, hC⟩
  rcases maximal_classify h37 h38 hyp ht htn hC hP hTP with rfl | rfl
  · exact normalizer_T1_le_of_bad h134 hRed hF hFa hFc h311 hobl hpt h h3 parData_a (Or.inl rfl)
      parData_b parData2_b (Or.inr rfl) (preIn_pa_ne_pb h) hs hK₁ hsn hK hp h8 e hbad
  · exact normalizer_T1_le_of_bad h134 hRed hF hFa hFc h311 hobl hpt h h3 parData_b (Or.inr rfl)
      parData_a parData2_a (Or.inl rfl) (preIn_pa_ne_pb h).symm hs hK₁ hsn hK hp h8 e hbad

end CFSG.Quasithin.Vol2.Ch10.SecB
