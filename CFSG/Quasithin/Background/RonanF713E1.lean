module

public import CFSG.Quasithin.Background.F7E1

public section

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G G' : Type*} [Group G] [Group G']

private abbrev restrictEquivLoc (e : G ≃* G') (K : Subgroup G) : ↥K ≃* ↥(K.map e.toMonoidHom) :=
  e.subgroupMap K

private theorem map_subgroupOf_restrictEquivLoc (e : G ≃* G') (A K : Subgroup G) :
    (A.subgroupOf K).map (restrictEquivLoc e K).toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_map_equiv]
  exact Iff.rfl

private theorem finite_of_le_loc {K H : Subgroup G} [Finite ↥H] (hKH : K ≤ H) : Finite ↥K :=
  Finite.of_injective (Subgroup.inclusion hKH) (Subgroup.inclusion_injective hKH)

private theorem finite_map_loc (e : G ≃* G') (K : Subgroup G) [Finite ↥K] :
    Finite ↥(K.map e.toMonoidHom) :=
  Finite.of_equiv ↥K (restrictEquivLoc e K).toEquiv

theorem inE_one_of_nParam_eq_one_loc {H : Subgroup G} (h : E1.nParam H = 1) : E1.InE 1 H := by
  by_contra h1
  unfold E1.nParam at h
  split_ifs at h with hodd
  · simp at h
  · have h2 : (2 : ℕ∞) ≤ ⨅ i ∈ {i : ℕ | 0 < i ∧ E1.InE i H}, (i : ℕ∞) := by
      refine le_iInf₂ fun i hi => ?_
      have hi1 : i ≠ 1 := fun e => h1 (e ▸ hi.2)
      have : 2 ≤ i := by have := hi.1; omega
      exact_mod_cast this
    rw [h] at h2
    norm_num at h2

theorem isE_map_mulEquiv_loc (e : G ≃* G') {i : ℕ} {H T A K : Subgroup G} [Finite ↥K] :
    E1.IsE i (H.map e.toMonoidHom) (T.map e.toMonoidHom) (A.map e.toMonoidHom)
      (K.map e.toMonoidHom) ↔ E1.IsE i H T A K := by
  haveI : Finite ↥(K.map e.toMonoidHom) := finite_map_loc e K
  unfold E1.IsE
  rw [← Subgroup.map_inf T K e.toMonoidHom e.injective, E1.tauOf_map_mulEquiv,
    ← map_subgroupOf_restrictEquivLoc e A K, ← map_subgroupOf_restrictEquivLoc e (T ⊓ K) K,
    E1.map_le_map_iff_mulEquiv, E1.map_le_map_iff_mulEquiv, E1.isSylowIn_map_mulEquiv,
    ← E1.eOne_map, ← E1.eTwo_map, E1.card_barO2_map, E1.card_barRad_map]

theorem isE_conj_loc (g : G) {i : ℕ} {H T A K : Subgroup G} [Finite ↥K] :
    E1.IsE i (conjSub g H) (conjSub g T) (conjSub g A) (conjSub g K) ↔ E1.IsE i H T A K :=
  isE_map_mulEquiv_loc (MulAut.conj g)

private theorem exists_eq_image_conjSub_loc (g : G) (Ω' : Set (Subgroup G)) :
    ∃ Ω : Set (Subgroup G), Ω' = conjSub g '' Ω := by
  refine ⟨conjSub g⁻¹ '' Ω', ?_⟩
  ext A
  exact ⟨fun hA => ⟨conjSub g⁻¹ A, ⟨A, hA, rfl⟩, CFSG.Quasithin.conjSub_inv_conjSub g A⟩, by
    rintro ⟨B, ⟨C, hC, rfl⟩, rfl⟩
    rwa [CFSG.Quasithin.conjSub_inv_conjSub]⟩

theorem eGen_conj_image_loc (i : ℕ) (g : G) (H T : Subgroup G) [Finite ↥H]
    (Ω : Set (Subgroup G)) :
    E1.eGen i (conjSub g H) (conjSub g T) (conjSub g '' Ω) = conjSub g (E1.eGen i H T Ω) := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K' hK' => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    obtain ⟨K, rfl⟩ : ∃ K : Subgroup G, conjSub g K = K' :=
      ⟨conjSub g⁻¹ K', CFSG.Quasithin.conjSub_inv_conjSub g K'⟩
    have hK'' : E1.IsE i (conjSub g H) (conjSub g T) (conjSub g A) (conjSub g K) := hK'
    have hKH : K ≤ H := by
      have h2 := CFSG.Quasithin.conjSub_mono g⁻¹ hK''.1
      rwa [CFSG.Quasithin.conjSub_conjSub_inv, CFSG.Quasithin.conjSub_conjSub_inv] at h2
    have hAT : A ≤ T := by
      have h2 := CFSG.Quasithin.conjSub_mono g⁻¹ hA'T
      rwa [CFSG.Quasithin.conjSub_conjSub_inv, CFSG.Quasithin.conjSub_conjSub_inv] at h2
    haveI : Finite ↥K := finite_of_le_loc hKH
    have hK : E1.IsE i H T A K := (isE_conj_loc g).mp hK''
    exact CFSG.Quasithin.conjSub_mono g
      (le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hK le_rfl)))
  · show Subgroup.map (MulAut.conj g).toMonoidHom (E1.eGen i H T Ω) ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    have hK0 : E1.IsE i H T A K := hK
    haveI : Finite ↥K := finite_of_le_loc hK0.1
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (conjSub g A) ⟨A, hA, rfl⟩ (le_iSup_of_le
      (CFSG.Quasithin.conjSub_mono g hAT)
      (le_iSup₂_of_le (conjSub g K) ((isE_conj_loc g).mpr hK0) le_rfl))

private theorem weakClosure_conj_image_loc (g : G) (X : Subgroup G) (Ω : Set (Subgroup G)) :
    E1.weakClosure (conjSub g X) (conjSub g '' Ω) = conjSub g (E1.weakClosure X Ω) :=
  E1.weakClosure_map_image (MulAut.conj g) X Ω

theorem inEFor_conj_loc {i : ℕ} (g : G) {H T : Subgroup G} [Finite ↥H] (h : E1.InEFor i H T) :
    E1.InEFor i (conjSub g H) (conjSub g T) := by
  intro Ω' hΩ'
  obtain ⟨Ω, rfl⟩ := exists_eq_image_conjSub_loc g Ω'
  have key := congrArg (conjSub g) (h Ω ((E1.isInvColl_conj g).mp hΩ'))
  rw [CFSG.Quasithin.conjSub_sup, CFSG.Quasithin.conjSub_inf,
    ← CFSG.Quasithin.conjSub_normalizer] at key
  rw [eGen_conj_image_loc, weakClosure_conj_image_loc]
  exact key

theorem exists_isE_not_le_of_inEFor_one_loc {X TX M A : Subgroup G} [Finite ↥X]
    (hX : E1.InEFor 1 X TX) (hT : IsSylowTwoOf TX X) (hM : M < X)
    (hunique : ∀ K : Subgroup G, K ≤ X → K ≠ X → TX ≤ K → K ≤ M)
    (hATX : A ≤ TX) (hAel : IsElemAbelian 2 A) (hnot : ¬ A ≤ pCoreOf 2 X) :
    ∃ y ∈ X, A ≤ conjSub y TX ∧
      ∃ H : Subgroup G, E1.IsE 1 X (conjSub y TX) A H ∧ ¬ H ≤ conjSub y M := by
  classical
  have hAX : A ≤ X := hATX.trans hT.1
  set Ω : Set (Subgroup G) := {B | ∃ x ∈ X, B = conjSub x A} with hΩ
  have hAΩ : A ∈ Ω := ⟨1, X.one_mem, (conjSub_one A).symm⟩
  have hΩinv : E1.IsInvColl X Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro B ⟨x, hx, rfl⟩
      have := conjSub_mono x hAX
      rwa [F7.conjSub_eq_of_mem hx] at this
    · rintro B ⟨x, hx, rfl⟩
      exact isElemAbelian_conjSub hAel
    · rintro B ⟨x, hx, rfl⟩ h hh
      exact ⟨h * x, X.mul_mem hh hx, by rw [conjSub_mul]; rfl⟩
  set W₀ := E1.weakClosure TX Ω with hW₀
  have hW₀T : W₀ ≤ TX := iSup₂_le fun B _ => iSup_le fun hB => hB
  have hAW : A ≤ W₀ := le_iSup₂_of_le A hAΩ (le_iSup_of_le hATX le_rfl)
  have hconj : ∀ t ∈ TX, conjSub t W₀ ≤ W₀ := by
    intro t ht
    show Subgroup.map (MulAut.conj t).toMonoidHom W₀ ≤ W₀
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun B hB => iSup_le fun hBT => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨x, hx, rfl⟩ := hB
    have hBt : conjSub t (conjSub x A) ≤ TX := by
      have := conjSub_mono t hBT
      rwa [F7.conjSub_eq_of_mem ht] at this
    have hmem : conjSub t (conjSub x A) ∈ Ω :=
      ⟨t * x, X.mul_mem (hT.1 ht) hx, by rw [conjSub_mul]⟩
    exact le_iSup₂_of_le (conjSub t (conjSub x A)) hmem (le_iSup_of_le hBt le_rfl)
  have hTN : TX ≤ Subgroup.normalizer (W₀ : Set G) := fun t ht =>
    F7.mem_normalizer_of_conj_le (hconj t ht) (hconj t⁻¹ (TX.inv_mem ht))
  have hXN : ¬ X ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro hXN
    exact hnot (hAW.trans ((le_pCoreOf_of_le_normalizer 2 (hW₀T.trans hT.1) hXN
      (hT.2.1.to_le hW₀T))))
  have hKM : X ⊓ Subgroup.normalizer (W₀ : Set G) ≤ M := by
    refine hunique _ inf_le_left (fun e => hXN (e ▸ inf_le_right)) (le_inf hT.1 hTN)
  have hE := hX Ω hΩinv
  have hex : ∃ A₀ ∈ Ω, A₀ ≤ TX ∧ ∃ H₀ : Subgroup G, E1.IsE 1 X TX A₀ H₀ ∧ ¬ H₀ ≤ M := by
    by_contra hcon
    push Not at hcon
    have hgen : E1.eGen 1 X TX Ω ≤ M := by
      refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun K hK => hcon B hB hBT K hK
    have : X ≤ M := by
      rw [← hE]
      exact sup_le hgen hKM
    exact absurd (hM.trans_le this) (lt_irrefl _)
  obtain ⟨A₀, ⟨x, hx, rfl⟩, hA₀T, H₀, hH₀, hH₀M⟩ := hex
  refine ⟨x⁻¹, X.inv_mem hx, ?_, conjSub x⁻¹ H₀, ?_, ?_⟩
  · have := conjSub_mono x⁻¹ hA₀T
    rwa [conjSub_conjSub_inv] at this
  · have hH₀X : H₀ ≤ X := hH₀.1
    haveI : Finite ↥H₀ := finite_of_le_loc hH₀X
    have h1 : E1.IsE 1 (conjSub x⁻¹ X) (conjSub x⁻¹ TX) (conjSub x⁻¹ (conjSub x A))
        (conjSub x⁻¹ H₀) := (isE_conj_loc x⁻¹).mpr hH₀
    have e1 : conjSub x⁻¹ X = X := F7.conjSub_eq_of_mem (X.inv_mem hx)
    have e2 : conjSub x⁻¹ (conjSub x A) = A := conjSub_conjSub_inv x A
    rw [e1, e2] at h1
    exact h1
  · intro hle
    apply hH₀M
    have := conjSub_mono x hle
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem exists_index_two_of_isE_loc {H T A K : Subgroup G} [Finite ↥K] (hAel : IsElemAbelian 2 A)
    (hAK : A ≤ K) (hK : E1.IsE 1 H T A K) :
    ∃ R : Subgroup G, R ≤ A ∧ R ≤ pCoreOf 2 K ∧ R.relIndex A = 2 := by
  obtain ⟨-, -, -, hcase⟩ := hK
  rcases hcase with ⟨⟨p, hp, hp2, -, -, -, hcard⟩, -⟩ | ⟨hE2, hle⟩
  · refine ⟨pCoreOf 2 K ⊓ A, inf_le_right, inf_le_left, ?_⟩
    exact relIndex_inf_map_subtype_eq hAK (CFSG.Open.pCore 2 ↥K) hcard
  · obtain ⟨h2c, -, -, L, hL, -, hcase⟩ := hE2
    have hbar : Nat.card (E1.barRad ↥K (A.subgroupOf K)) = 2 := by
      rcases hcase with h1 | ⟨-, h2⟩
      · have hne : E1.barRad ↥K (A.subgroupOf K) ≠ ⊥ := by
          intro hbot
          have hL' : L = ⊥ := by rw [h1, hbot, Subgroup.commutator_bot_right]
          obtain ⟨a, b, hab⟩ := hL.1.2.2
          apply hab
          subst hL'
          have hs : Subsingleton (↥(⊥ : Subgroup ↥K) ⧸ Subgroup.center ↥(⊥ : Subgroup ↥K)) := by
            infer_instance
          exact Subsingleton.elim _ _
        have h1' : Nat.card (E1.barRad ↥K (A.subgroupOf K)) ≠ 1 := fun h =>
          hne (Subgroup.card_eq_one.mp h)
        have h0 : 0 < Nat.card (E1.barRad ↥K (A.subgroupOf K)) := Nat.card_pos
        have h2 := hle
        omega
      · exact h2
    have hidx := relIndex_inf_map_subtype_eq hAK (CFSG.solvableRadical ↥K) hbar
    refine ⟨(CFSG.solvableRadical ↥K).map K.subtype ⊓ A, inf_le_right, ?_, hidx⟩
    obtain ⟨P, hPsyl, hPn⟩ := h2c
    have hradN : (CFSG.solvableRadical ↥K).Normal := inferInstance
    have hP2 : IsPGroup 2 P := hPsyl.2.1
    have hPrad : P ≤ CFSG.solvableRadical ↥K := hPsyl.1
    have hPQ : ∀ q : ↥K, conjSub q P ≤ P := by
      intro q
      have h1 : conjSub q P ≤ CFSG.solvableRadical ↥K := by
        intro y hy
        rw [mem_conjSub] at hy
        have : q⁻¹ * y * q ∈ CFSG.solvableRadical ↥K := hPrad hy
        have := hradN.conj_mem _ this q
        simpa [mul_assoc] using this
      exact le_of_normal_sylow hPsyl hPn h1 (isPGroup_conjSub hP2)
    have hPnorm : P.Normal := ⟨fun n hn g => hPQ g (mul_mem_conjSub hn)⟩
    have hPK : P.map K.subtype ≤ pCoreOf 2 K := by
      refine le_pCoreOf 2 (Subgroup.map_subtype_le P) ?_ (hP2.map K.subtype)
      have e : (P.map K.subtype).subgroupOf K = P :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
      rw [e]
      exact hPnorm
    have hB2 : IsPGroup 2 (A.subgroupOf K) :=
      (isPGroup_of_isElemAbelian hAel).of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
    rintro x ⟨⟨k, hk, rfl⟩, hxA⟩
    refine hPK ⟨k, ?_, rfl⟩
    have hkB : k ∈ A.subgroupOf K := hxA
    exact le_of_normal_sylow hPsyl hPn (X := (A.subgroupOf K) ⊓ CFSG.solvableRadical ↥K)
      inf_le_right (hB2.to_le inf_le_left) ⟨hkB, hk⟩

theorem twoResidual_le_conjClosure_loc {H T A K : Subgroup G} [Finite ↥K]
    (hK : E1.IsEAny H T A K) : twoResidual K ≤ conjClosure A K := by
  obtain ⟨i, -, -, -, hcase⟩ := hK
  have hab : twoResidual (⊤ : Subgroup ↥K) ≤ conjClosure (A.subgroupOf K) ⊤ := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact E1.twoResidual_le_conjClosure_of_eOne h
    · exact E1.twoResidual_le_conjClosure_of_eTwo h
  set M : Subgroup ↥K := twoResidual (⊤ : Subgroup ↥K) with hM
  have hMnorm : Subgroup.normalizer (M : Set ↥K) = ⊤ :=
    top_le_iff.mp (le_normalizer_twoResidual ⊤)
  have h1 : twoResidual K ≤ M.map K.subtype := by
    refine twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le _) ?_ ?_
    · intro x hx
      exact Subgroup.le_normalizer_map K.subtype
        (Subgroup.mem_map_of_mem K.subtype
          (show (⟨x, hx⟩ : ↥K) ∈ Subgroup.normalizer (M : Set ↥K) from
            hMnorm ▸ Subgroup.mem_top _))
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup ↥K) ⟨y, hy⟩ (Subgroup.mem_top _)
      exact ⟨k, ⟨_, hk, by simp⟩⟩
  have h2 : (conjClosure (A.subgroupOf K) ⊤).map K.subtype ≤ conjClosure A K := by
    refine Subgroup.map_le_iff_le_comap.mpr (conjClosure_le fun h _ z hz => ?_)
    exact mem_conjClosure h.2 hz
  exact h1.trans ((Subgroup.map_mono hab).trans h2)

end CFSG.Quasithin.RonanF713
