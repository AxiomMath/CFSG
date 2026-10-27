module

public import CFSG.Quasithin.Vol2.Ch9Lem936
public import CFSG.Quasithin.Vol2.Ch9Sec3KX
public import CFSG.Quasithin.Vol2.Ch9Lem935
public import CFSG.Quasithin.Vol2.Ch9Sec3DSB

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem commutator_thompsonJ_eq' (h3108 : Stmt3_2_10_eight) {K : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hs : IsSimpleGroup (O2Q K))
    (hJK : thompsonJ T ≤ Subgroup.normalizer (K : Set G)) (hOK : pCoreOf 2 K ≤ T)
    (hKM : ¬ K ≤ fsuM T L) : ⁅K, thompsonJ T⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hVp : IsVplus T L I (fsuV T I) := by
    by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
    · exact Or.inl ⟨hc'.1, hc'.2, S.hVM⟩
    · exact Or.inr ⟨hc', rfl⟩
  have hJK' : ¬ ⁅K, thompsonJ T⁆ ≤ pCoreOf 2 K := by
    intro hle
    set Sx := thompsonJ T ⊔ pCoreOf 2 K with hSx
    have hSxT : Sx ≤ T := sup_le hJT hOK
    have hKN : K ≤ Subgroup.normalizer (Sx : Set G) := by
      intro k hk
      refine mem_normalizer_sup_of_map_le ?_ ?_
      · rintro _ ⟨j, hj, rfl⟩
        show (MulAut.conj k) j ∈ Sx
        rw [MulAut.conj_apply]
        have hc1 : k * j * k⁻¹ * j⁻¹ ∈ pCoreOf 2 K :=
          hle (Subgroup.commutator_mem_commutator hk hj)
        have e : k * j * k⁻¹ = (k * j * k⁻¹ * j⁻¹) * j := by group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_right hc1) (Subgroup.mem_sup_left hj)
      · rw [show (pCoreOf 2 K).map (MulAut.conj k).toMonoidHom = pCoreOf 2 K from
          Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk)]
        exact le_sup_right
    have hNS := (h3108 G T L I (fsuV T I) hfsu hVp S.hJ Sx (hfsu.sylow.1.to_le hSxT)
      le_sup_left).2
    exact hKM (hKN.trans hNS)
  by_contra hne
  apply hJK'
  refine le_pCoreOf_of_normal_of_ne hperf hs ?_ (Subgroup.normalizer_commutator_ge_left K _) hne
  rw [Subgroup.commutator_le]
  intro k hk j hj
  have h3 : j * k⁻¹ * j⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hJK hj) _).mp (K.inv_mem hk)
  rw [commutatorElement_def]
  have e : k * j * k⁻¹ * j⁻¹ = k * (j * k⁻¹ * j⁻¹) := by group
  rw [e]
  exact K.mul_mem hk h3

theorem commutator_thompsonJ_eq (h3108 : Stmt3_2_10_eight) {H K : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    ⁅K, thompsonJ T⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hOK : pCoreOf 2 K ≤ T :=
    (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (hHKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans (F7.isSylowTwoOf_pCoreOf_le hTHs)
  have hs : IsSimpleGroup (O2Q K) := by
    obtain ⟨eA⟩ := hKA
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eA.isSimpleGroup
  exact S.commutator_thompsonJ_eq' h3108 (perfect_of_mem_cComp hKc) hs
    ((thompsonJ_le_self T).trans hTK) hOK
    (fun h => hH.2.1 (by rw [hHK]; exact sup_le h Setup.T_le_fsuM))

theorem isTwoReducedIn_U (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (h1 : zQ T I = fsuV T I) {K D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hchar : CharTwo (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) :
    IsTwoReducedIn (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)
        (conjClosure (quasithinOmegaOneCenter T) (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer
          (L : Set G)) ⊔ K)) ∧
      fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) ≤
        conjClosure (quasithinOmegaOneCenter T) (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer
          (L : Set G)) ⊔ K) ∧
      conjClosure (quasithinOmegaOneCenter T) (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer
          (L : Set G)) ⊔ K) ⊓ Subgroup.centralizer ((T ⊓ Subgroup.normalizer (L : Set G) :
            Subgroup G) : Set G) ≤
        fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hDM₀ : D ≤ M₀ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hQT₁ : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ T₁ :=
    le_inf inf_le_left (le_sup_right.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hTL₀T₁ : T ⊓ fsuL0 T L ≤ T₁ :=
    le_inf inf_le_left (le_sup_left.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hZ := S.omegaOneCenter_T_le h1
  have hZT₁ : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter T₁ := by
    refine (Subgroup.closure_le _).mpr fun z hz => Subgroup.subset_closure ⟨⟨?_, ?_⟩, hz.2⟩
    · exact hQT₁ (S.fsuV_le_Q (hZ (Subgroup.subset_closure hz)).1)
    · exact Subgroup.centralizer_le inf_le_left hz.1.2
  obtain ⟨hUO, hUe, hUr⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hchar hZT₁
  refine ⟨hUr, fun v hv => ?_, ?_⟩
  · obtain ⟨d, hd, z, hz, rfl⟩ := hc.exists_conj_of_mem_V1 h2 h1 hdiag hv
    exact Subgroup.subset_closure ⟨d, hDM₀ hd, z, hz, rfl⟩
  · rintro u ⟨huU, huC⟩
    have huT₁ : u ∈ T₁ := (hUO.trans (inf_le_left.trans (F7.isSylowTwoOf_pCoreOf_le hsyl))) huU
    have huZ : u ∈ omegaOneCenterOf T₁ := Subgroup.subset_closure ⟨⟨huT₁, huC⟩, hUe.2 u huU⟩
    have huV := S.omegaOneCenter_le h1 hQT₁ inf_le_left huZ
    exact ⟨huV.1, Subgroup.centralizer_le hTL₀T₁ huV.2⟩

theorem lem937' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hFB : A314FFFactE9) (hFD : A7FFNoA5Fact) (h3108 : Stmt3_2_10_eight) (h2 : n = 2)
    (h1 : zQ T I = fsuV T I) {K D K₀ : Subgroup G}
    (hKl₁ : K ∈ lFamily (T ⊓ Subgroup.normalizer (L : Set G)))
    (hT₁K : T ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (hKMN : K ⊓ fsuM T L ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hKV : K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hchar : CharTwo (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G)) :
    IsSL3 4 (O2Q K₀) ∨ IsPSp4 2 2 (O2Q K₀) ∨ IsG2 2 2 (O2Q K₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  set U := conjClosure (quasithinOmegaOneCenter T) M₀ with hU
  have hLM₀ : L ≤ M₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hKM₀ : K ≤ M₀ := le_sup_right
  obtain ⟨hUr, hV₁U, hUC⟩ := S.isTwoReducedIn_U h37 h38 h37c h38c h2 h1 hD hsyl hchar
  have hV₂U : conjClosure V₁ L ≤ U := conjClosure_le fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ M₀ (hLM₀ hl)) v).mp (hV₁U hv)
  have hKU : ¬ K ≤ Subgroup.centralizer (U : Set G) := fun hle =>
    hc.not_le_centralizer_conjClosure h37c h38c h2 hdiag
      ((hBK.trans hle).trans (Subgroup.centralizer_le hV₂U))
  have hJT₁ : thompsonJ T ≤ T₁ :=
    le_inf (thompsonJ_le_self T) fun j hj => hc.r0_le_normalizer_L h37 h38 h37c h38c
      (Subgroup.mem_sup_right ⟨thompsonJ_le_self T hj, S.hJ hj⟩)
  have hVp : IsVplus T L I (fsuV T I) := by
    by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
    · exact Or.inl ⟨hc'.1, hc'.2, S.hVM⟩
    · exact Or.inr ⟨hc', rfl⟩
  have hJ : thompsonJ T = thompsonJ T₁ :=
    (h3108 G T L I (fsuV T I) hfsu hVp S.hJ T₁ (hfsu.sylow.1.to_le inf_le_left) hJT₁).1
  have hJC : ¬ ⁅K, thompsonJ T₁⁆ ≤ Subgroup.centralizer (U : Set G) := by
    rw [← hJ, hKJ]
    exact hKU
  have hlt : K < K₀ := by
    refine lt_of_le_of_ne hKK₀ fun hKeq => ?_
    have hLK : L ≤ K := hKeq ▸ hLK₀
    have hLN : L ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      (le_inf hLK S.L_le_fsuM).trans hKMN
    have hTLs := hc.isSylowTwoOf_inf_L h37 h38 h37c h38c
    have hTLO : T ⊓ L ≤ pCoreOf 2 L := by
      refine (le_inf (inf_le_inf_left T hLK) inf_le_right).trans
        (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right ?_
          (hfsu.sylow.1.to_le (inf_le_left.trans inf_le_left)))
      intro l hl
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLN hl, Subgroup.le_normalizer hl⟩
    have hodd : ¬ 2 ∣ (pCoreOf 2 L).relIndex L := by
      intro h2d
      apply hTLs.2.2
      show 2 ∣ (T ⊓ L).relIndex L
      rw [← Subgroup.relIndex_mul_relIndex (T ⊓ L) (pCoreOf 2 L) L hTLO
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]
      exact h2d.mul_left _
    apply hodd
    have h60 := (oTwoQuot_facts_of_alt_five (S.oTwoQuot_L_facts h37c h38c h2)).1
    have hidxL : (pCoreOf 2 L).relIndex L = Nat.card (oTwoQuot ↥L) := by
      rw [Subgroup.relIndex, ← Subgroup.index_eq_card]
      congr 1
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [hidxL, h60]
    norm_num
  have hDK₀ : D ≤ K₀ := (hc.le_sup_L h37 h38 h37c h38c hD hdiag).trans
    (sup_le (hBK.trans hKK₀) hLK₀)
  obtain ⟨a, haD, b, hbD, hab, ha3, hb3, ha1, hba⟩ := hc.exists_e9 h37c h38c h2 hD hdiag
  have hSQ : SQTKGroup ↥M₀ := sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hM₀O
  rcases hFB G M₀ T₁ K K₀ U hSQ hsyl hKM₀ hKl₁ hT₁K hKA hK₀ hlt hK₀n hUr hJC
      ⟨a, hDK₀ haD, b, hDK₀ hbD, hab, ha3, hb3, ha1, hba⟩ with hL | hL | hL | hA7
  · exact Or.inl hL
  · exact Or.inr (Or.inl hL)
  · exact Or.inr (Or.inr hL)
  exfalso
  exact hFD G M₀ T₁ K K₀ U hSQ hsyl hlt.le (le_of_mem_cComp hK₀) hK₀n (perfect_of_mem_cComp hKl₁)
    hKA hT₁K hUr hA7 hJC (hKV.trans (Subgroup.centralizer_le hUC))

theorem lem937 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hFB : A314FFFactE9) (hFD : A7FFNoA5Fact) (h3108 : Stmt3_2_10_eight) (h2 : n = 2)
    (h1 : zQ T I = fsuV T I) {H K D K₀ : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hHK : H = K ⊔ T) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (hKHM : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ⊔ (T ⊓ K) =
        K ⊓ (H ⊓ fsuM T L))
    (hBTK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hKV : K ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hchar : CharTwo (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G)) :
    IsSL3 4 (O2Q K₀) ∨ IsPSp4 2 2 (O2Q K₀) ∨ IsG2 2 2 (O2Q K₀) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKl : K ∈ lFamily T := by
    show K ∈ cComp (K ⊔ T)
    rw [← hHK]
    exact hKc
  have hKl₁ : K ∈ lFamily (T ⊓ Subgroup.normalizer (L : Set G)) :=
    cComp_mem_of_le (X := K ⊔ T) hKl le_sup_left (sup_le_sup_left inf_le_left K)
  have hKMN : K ⊓ fsuM T L ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    refine (le_inf inf_le_left (le_inf (inf_le_left.trans hKH) inf_le_right)).trans ?_
    rw [← hKHM]
    exact sup_le hBTK Subgroup.le_normalizer
  exact S.lem937' h37 h38 h37c h38c hFB hFD h3108 h2 h1 hKl₁ (inf_le_left.trans hTK) hKA hD hBK
    hKMN (S.commutator_thompsonJ_eq h3108 hH hHK hKc hTK hKA) hKV hM₀O hsyl hchar hK₀ hLK₀ hKK₀
    hK₀n

end Setup

end CFSG.Quasithin.H13.Ch9
