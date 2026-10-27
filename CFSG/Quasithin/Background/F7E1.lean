module

public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.E1Residual

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

namespace F7

theorem relIndex_inf_map_subtype_eq {K A : Subgroup G} (hAK : A ≤ K) (N : Subgroup ↥K) [N.Normal]
    (h : Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' N)) = 2) :
    (N.map K.subtype ⊓ A).relIndex A = 2 := by
  have h1 : (QuotientGroup.mk' N).ker.relIndex (A.subgroupOf K) = 2 := by
    rw [Subgroup.relIndex_ker]; exact h
  rw [QuotientGroup.ker_mk'] at h1
  have h2 := Subgroup.relIndex_map_map_of_injective (f := K.subtype) N (A.subgroupOf K)
    K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hAK] at h2
  rw [Subgroup.inf_relIndex_right, h2, h1]

theorem conj_mem_of_normal_subgroupOf {Q : Type*} [Group Q] {P R : Subgroup Q} (hPR : P ≤ R)
    (hn : (P.subgroupOf R).Normal) {x p : Q} (hx : x ∈ R) (hp : p ∈ P) : x * p * x⁻¹ ∈ P := by
  have := hn.conj_mem ⟨p, hPR hp⟩ (by simpa [Subgroup.mem_subgroupOf] using hp) ⟨x, hx⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem le_of_normal_sylow {Q : Type*} [Group Q] [Finite Q] {P R : Subgroup Q}
    (hP : IsSylowTwoOf P R) (hn : (P.subgroupOf R).Normal) {X : Subgroup Q} (hXR : X ≤ R)
    (hX : IsPGroup 2 X) : X ≤ P := by
  obtain ⟨x, hx, hle⟩ := isSylowTwoOf_exists_conj_le hP hXR hX
  refine hle.trans fun y hy => ?_
  rw [mem_conjSub] at hy
  have := conj_mem_of_normal_subgroupOf hP.1 hn hx hy
  simpa [mul_assoc] using this

theorem exists_index_two_of_isE [Finite G] {H T A K : Subgroup G} (hAel : IsElemAbelian 2 A)
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

theorem inE_one_of_nParam_eq_one [Finite G] {H : Subgroup G} (h : E1.nParam H = 1) :
    E1.InE 1 H := by
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

theorem exists_isE_not_le_of_inE_one [Finite G] {X TX M A : Subgroup G}
    (hX : E1.InE 1 X) (hT : IsSylowTwoOf TX X) (hM : M < X)
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
    have hmem : conjSub t (conjSub x A) ∈ Ω := ⟨t * x, X.mul_mem (hT.1 ht) hx, by rw [conjSub_mul]⟩
    exact le_iSup₂_of_le (conjSub t (conjSub x A)) hmem (le_iSup_of_le hBt le_rfl)
  have hTN : TX ≤ Subgroup.normalizer (W₀ : Set G) := fun t ht =>
    F7.mem_normalizer_of_conj_le (hconj t ht) (hconj t⁻¹ (TX.inv_mem ht))
  have hXN : ¬ X ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro hXN
    exact hnot (hAW.trans ((le_pCoreOf_of_le_normalizer 2 (hW₀T.trans hT.1) hXN
      (hT.2.1.to_le hW₀T))))
  have hKM : X ⊓ Subgroup.normalizer (W₀ : Set G) ≤ M := by
    refine hunique _ inf_le_left (fun e => hXN (e ▸ inf_le_right)) (le_inf hT.1 hTN)
  have hEF : E1.InEFor 1 X TX := hX TX hT
  have hE := hEF Ω hΩinv
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
  · have h1 : E1.IsE 1 (conjSub x⁻¹ X) (conjSub x⁻¹ TX) (conjSub x⁻¹ (conjSub x A))
        (conjSub x⁻¹ H₀) := (E1.isE_conj x⁻¹).mpr hH₀
    have e1 : conjSub x⁻¹ X = X := F7.conjSub_eq_of_mem (X.inv_mem hx)
    have e2 : conjSub x⁻¹ (conjSub x A) = A := conjSub_conjSub_inv x A
    rw [e1, e2] at h1
    exact h1
  · intro hle
    apply hH₀M
    have := conjSub_mono x hle
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

end F7

namespace CosetGeom

variable {G₀ G₁ G₂ T V : Subgroup G}

theorem exists_edge_conj_sylow [Finite G] (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {β γ : CosetGeom G₀ G₁ G₂} (hadj : (graph G₀ G₁ G₂).Adj β γ) (hvt : vtype γ = true)
    {A : Subgroup G} (hAstab : A ≤ stab β ⊓ stab γ) (hA : IsPGroup 2 A) :
    ∃ g : ↥G₀, g • γ₀ G₀ G₁ G₂ = β ∧ g • γ₁ G₀ G₁ G₂ = γ ∧ A ≤ conjSub (g : G) T := by
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
  · have hSyl : IsSylowTwoOf (conjSub (g : G) T) (stab β ⊓ stab γ) := by
      rw [← hg0, ← hg1, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, ← conjSub_inf]
      exact isSylowTwoOf_conj hyp.sylow_inf _
    obtain ⟨x, hx, hAx⟩ := isSylowTwoOf_exists_conj_le hSyl hAstab hA
    have hx0 : x ∈ G₀ := stab_le β hx.1
    refine ⟨⟨x, hx0⟩ * g, ?_, ?_, ?_⟩
    · rw [mul_smul, hg0]
      exact smul_eq_of_mem_stab (g := ⟨x, hx0⟩) hx.1
    · rw [mul_smul, hg1]
      exact smul_eq_of_mem_stab (g := ⟨x, hx0⟩) hx.2
    · rw [Subgroup.coe_mul, conjSub_mul]
      exact hAx
  · exfalso
    have := congrArg vtype hg0
    rw [vtype_smul, vtype_γ₀, hvt] at this
    exact absurd this (by decide)

theorem exists_nbr_relIndex_two [Finite G] (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ : CosetGeom G₀ G₁ G₂} (hγ : IsCriticalVertex G₀ G₁ G₂ V γ)
    (ha₃ : 3 ≤ critDist G₀ G₁ G₂ V) (ha₂ : Odd (critDist G₀ G₁ G₂ V))
    (hb : IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)))
    (hc : E1.nParam G₂ = 1) {A : Subgroup G} (hA₁ : A ≤ Vv V (γ₁ G₀ G₁ G₂))
    (hA₂ : ¬ A ≤ ballStab 1 γ) :
    ∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2 := by
  have hb2 : 2 ≤ critDist G₀ G₁ G₂ V := by omega
  obtain ⟨⟨β, hβnb, hdβ⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic hb2
  have hAel : IsElemAbelian 2 A :=
    isElemAbelian_mono (isElemAbelian_Vv_γ₁ hyp hV (by omega)) hA₁
  have hAp : IsPGroup 2 A := isPGroup_of_isElemAbelian hAel
  have hAstab : A ≤ stab β ⊓ stab γ :=
    hA₁.trans ((Vv_γ₁_le_pCoreOf_stab_inf hyp hV hβnb hdβ).trans (pCoreOf_le 2 _))
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact ha₂)
  have hadj : (graph G₀ G₁ G₂).Adj β γ := hβnb
  obtain ⟨g, hg0, hg1, hAg⟩ := exists_edge_conj_sylow hyp.toAmalgamHyp hadj hvt hAstab hAp
  have hstabγ : stab γ = conjSub (g : G) G₂ := by rw [← hg1, stab_smul, stab_γ₁ hyp.le₂]
  have hVβ : Vv V β = conjSub (g : G) V := by rw [← hg0]; exact Vv_smul_γ₀ hyp.normalizes g
  set N₀ := G₂ ⊓ Subgroup.normalizer (V : Set G) with hN₀
  set M := stab γ ⊓ Subgroup.normalizer (Vv V β : Set G) with hM
  have hMeq : M = conjSub (g : G) N₀ := by
    rw [hM, hstabγ, hVβ, conjSub_inf, conjSub_normalizer]
  obtain ⟨hmax, hTN₀, huniq⟩ := isUniqueMaxOver_iff.mp hb
  have hMlt : M < stab γ := by
    rw [hMeq, hstabγ]
    exact lt_of_le_of_ne (conjSub_mono _ hmax.1.le) fun e => hmax.1.ne ((conjSub_inj _).mp e)
  have hunique : ∀ K : Subgroup G, K ≤ stab γ → K ≠ stab γ → conjSub (g : G) T ≤ K → K ≤ M := by
    intro K hK hKne hTK
    have hK' : conjSub (g : G)⁻¹ K ≤ G₂ := by
      rw [hstabγ] at hK
      exact (le_conjSub_iff _).mp hK
    have hKne' : conjSub (g : G)⁻¹ K ≠ G₂ := by
      intro e
      apply hKne
      rw [hstabγ, ← e, conjSub_inv_conjSub]
    have hTK' : T ≤ conjSub (g : G)⁻¹ K := (conjSub_le_iff _).mp hTK
    obtain ⟨N, hN, hKN⟩ := exists_isMaxSubgroupIn (lt_of_le_of_ne hK' hKne')
    have hNN₀ : N = N₀ := huniq N hN (hTK'.trans hKN)
    rw [hMeq]
    have := conjSub_mono (g : G) (hNN₀ ▸ hKN)
    rwa [conjSub_inv_conjSub] at this
  have hInE : E1.InE 1 (stab γ) := by
    rw [hstabγ]
    exact (E1.inE_conj 1 (g : G) G₂).mpr (inE_one_of_nParam_eq_one hc)
  have hTγ : IsSylowTwoOf (conjSub (g : G) T) (stab γ) := by
    rw [hstabγ]; exact isSylowTwoOf_conj hyp.sylow₂ _
  have hnot : ¬ A ≤ pCoreOf 2 (stab γ) := fun h =>
    hA₂ (h.trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp γ))
  obtain ⟨y, hy, hAS, H, hH, hHM⟩ :=
    exists_isE_not_le_of_inE_one hInE hTγ hMlt hunique hAg hAel hnot
  set S := conjSub y (conjSub (g : G) T) with hSdef
  have hS : IsSylowTwoOf S (stab γ) := by
    have := isSylowTwoOf_conj hTγ y
    rwa [F7.conjSub_eq_of_mem hy] at this
  have hHγ : H ≤ stab γ := hH.1
  have hAH : A ≤ H := by
    have h1 : A ⊔ pCoreOf 2 (stab γ) ≤ E1.tauOf (stab γ) S A := E1.le_tauOf hS hAS hAel
    exact (le_sup_left.trans h1).trans (hH.2.1.trans inf_le_right)
  obtain ⟨R, hRA, hRH, hRidx⟩ := exists_index_two_of_isE hAel hAH hH
  have hSH : IsSylowTwoOf (S ⊓ H) H := hH.2.2.1
  have hres : twoResidual H ≤ conjClosure A H := E1.twoResidual_le_conjClosure ⟨1, hH⟩
  have hHle : H ≤ (S ⊓ H) ⊔ conjClosure A H :=
    calc H = (S ⊓ H) ⊔ twoResidual H := (sup_twoResidual_eq hSH).symm
      _ ≤ (S ⊓ H) ⊔ conjClosure A H := sup_le_sup_left hres _
  set W := conjSub y (Vv V β) with hW
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW, hVβ]
    have hT1 : T ≤ Subgroup.normalizer (V : Set G) := hyp.sylow₁.1.trans hyp.normalizes
    exact conjSub_le_normalizer (conjSub_le_normalizer hT1)
  have hex : ∃ h ∈ H, ¬ A ≤ Subgroup.normalizer (conjSub h W : Set G) := by
    by_contra hcon
    push Not at hcon
    have hcl : conjClosure A H ≤ Subgroup.normalizer (W : Set G) := by
      refine conjClosure_le fun h hh a ha => ?_
      have h1 := hcon h⁻¹ (H.inv_mem hh) ha
      rw [conjSub_normalizer, mem_conjSub] at h1
      simpa using h1
    have hHN : H ≤ Subgroup.normalizer (W : Set G) :=
      hHle.trans (sup_le (inf_le_left.trans hSW) hcl)
    apply hHM
    have e : conjSub y M = stab γ ⊓ Subgroup.normalizer (W : Set G) := by
      rw [hM, conjSub_inf, F7.conjSub_eq_of_mem hy, hW, conjSub_normalizer]
    rw [e]
    exact le_inf hHγ hHN
  obtain ⟨h, hhH, hhnot⟩ := hex
  have hh0 : h ∈ G₀ := stab_le γ (hHγ hhH)
  have hy0 : y ∈ G₀ := stab_le γ hy
  set kk : ↥G₀ := ⟨h, hh0⟩ * ⟨y, hy0⟩ * g with hkk
  have hkkv : (kk : G) = h * y * (g : G) := rfl
  have hkk1 : kk • γ₁ G₀ G₁ G₂ = γ := by
    rw [hkk, mul_smul, mul_smul, hg1, smul_eq_of_mem_stab (g := ⟨y, hy0⟩) hy]
    exact smul_eq_of_mem_stab (g := ⟨h, hh0⟩) (hHγ hhH)
  refine ⟨kk • γ₀ G₀ G₁ G₂, ?_, ?_⟩
  · have := (smul_adj kk).mpr (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂))
    rw [hkk1] at this
    exact this.symm
  · have hVα : Vv V (kk • γ₀ G₀ G₁ G₂) = conjSub h W := by
      rw [Vv_smul_γ₀ hyp.normalizes, hkkv, conjSub_mul, conjSub_mul, hW, hVβ]
    rw [hVα]
    have hstabα : stab (kk • γ₀ G₀ G₁ G₂) = conjSub h (conjSub y (conjSub (g : G) G₁)) := by
      rw [stab_smul, stab_γ₀ hyp.le₁, hkkv, conjSub_mul, conjSub_mul]
    have hSG₁ : S ≤ conjSub y (conjSub (g : G) G₁) :=
      conjSub_mono y (conjSub_mono _ hyp.sylow₁.1)
    have hQS : pCoreOf 2 H ≤ S := (isSylowTwoOf_pCoreOf_le hSH).trans inf_le_left
    have hRstab : R ≤ stab (kk • γ₀ G₀ G₁ G₂) := by
      rw [hstabα]
      refine hRH.trans ?_
      rw [le_conjSub_iff]
      have e : conjSub h⁻¹ (pCoreOf 2 H) = pCoreOf 2 H :=
        F7.conjSub_eq_of_mem_normalizer (inv_mem (le_normalizer_pCoreOf 2 H hhH))
      rw [e]
      exact hQS.trans hSG₁
    have hRN : R ≤ A ⊓ Subgroup.normalizer (conjSub h W : Set G) := by
      refine le_inf hRA ?_
      rw [← hVα]
      exact hRstab.trans (stab_le_normalizer_Vv hyp.normalizes _)
    have hne : ¬ A ≤ A ⊓ Subgroup.normalizer (conjSub h W : Set G) := fun hle =>
      hhnot (hle.trans inf_le_right)
    have h1 := Subgroup.relIndex_mul_relIndex R (A ⊓ Subgroup.normalizer (conjSub h W : Set G)) A
      hRN inf_le_left
    rw [hRidx] at h1
    have hd : (A ⊓ Subgroup.normalizer (conjSub h W : Set G)).relIndex A ∣ 2 :=
      ⟨(R.relIndex (A ⊓ Subgroup.normalizer (conjSub h W : Set G))), by rw [← h1, mul_comm]⟩
    have h1' : (A ⊓ Subgroup.normalizer (conjSub h W : Set G)).relIndex A ≠ 1 := fun e =>
      hne (Subgroup.relIndex_eq_one.mp e)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with e | e
    · exact absurd e h1'
    · exact e

end CosetGeom

end CFSG.Quasithin
