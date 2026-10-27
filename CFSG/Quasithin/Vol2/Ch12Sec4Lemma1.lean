module

public import CFSG.Quasithin.Vol2.Ch12Sec4A5Sum
public import CFSG.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

theorem pCore_autI_eq_bot_of_reduced {H V : Subgroup G} (hred : IsTwoReducedIn H V)
    (hV : IsElemAbelian 2 V) : CFSG.Open.pCore 2 ↥(autI hV H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMN := hred.2.1
  have hPX : pCoreOf 2 (autI hV H) ≤ autI hV H := LieType.BorelTits.pCoreOf_le 2 _
  have hP2 : IsPGroup 2 (pCoreOf 2 (autI hV H)) := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXn : autI hV H ≤ Subgroup.normalizer
      ((pCoreOf 2 (autI hV H) : Subgroup (MulAut (IntMod V hV))) :
        Set (MulAut (IntMod V hV))) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hDM : preI hV H hMN (pCoreOf 2 (autI hV H)) ≤ H := preI_le hV
  have key : ∀ m ∈ H, ∀ d ∈ preI hV H hMN (pCoreOf 2 (autI hV H)),
      m * d * m⁻¹ ∈ preI hV H hMN (pCoreOf 2 (autI hV H)) := by
    intro m hm d hd
    obtain ⟨hdM, hdP⟩ := (mem_preI hV).1 hd
    have hmem : m * d * m⁻¹ ∈ H := H.mul_mem (H.mul_mem hm hdM) (H.inv_mem hm)
    refine (mem_preI hV).2 ⟨hmem, ?_⟩
    have e : (⟨m * d * m⁻¹, hmem⟩ : ↥H) = ⟨m, hm⟩ * ⟨d, hdM⟩ * ⟨m, hm⟩⁻¹ := rfl
    have hmX : convHom hV H hMN ⟨m, hm⟩ ∈ autI hV H := by
      rw [convHom_apply]
      exact convI_mem_autI hV hm (hMN hm)
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXn hmX) _).mp hdP
  have hDn : H ≤ Subgroup.normalizer
      ((preI hV H hMN (pCoreOf 2 (autI hV H)) : Subgroup G) : Set G) := fun m hm =>
    B6.mem_normalizer_of_forall_mem (key m hm)
      (fun x hx => by simpa using key m⁻¹ (H.inv_mem hm) x hx)
  have hD2 : ∀ d ∈ preI hV H hMN (pCoreOf 2 (autI hV H)),
      ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨hdM, hdP⟩ := (mem_preI hV).1 hd
    obtain ⟨k, hk⟩ := hP2 ⟨convHom hV H hMN ⟨d, hdM⟩, hdP⟩
    refine ⟨k, ?_⟩
    have h2 : (⟨d, hdM⟩ : ↥H) ^ 2 ^ k ∈ (convHom hV H hMN).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hk
    rw [ker_convHom hV H hMN, Subgroup.mem_subgroupOf] at h2
    simpa using h2.2
  have hDC := hred.2.2.2 _ hDM hDn hD2
  have hPbot : pCoreOf 2 (autI hV H) = ⊥ := by
    refine eq_bot_iff.mpr fun φ hφ => ?_
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 (hPX hφ)
    have hgD : (g : G) ∈ preI hV H hMN (pCoreOf 2 (autI hV H)) :=
      (mem_preI hV).2 ⟨hgM, by rw [convHom_apply]; exact hφ⟩
    exact Subgroup.mem_bot.mpr ((convI_eq_one_iff hV g).2 (hDC hgD))
  exact (Subgroup.map_eq_bot_iff_of_injective _ (autI hV H).subtype_injective).mp hPbot

omit [Finite G] in
theorem isSolvable_autI {H V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : H ≤ Subgroup.normalizer (V : Set G)) (hs : Group.IsSolvable ↥H) :
    Group.IsSolvable ↥(autI hV H) := by
  rw [← range_convHom hV H hH]
  exact Group.isSolvable_of_surjective (f := (convHom hV H hH).rangeRestrict)
    (convHom hV H hH).rangeRestrict_surjective

omit [Finite G] in
theorem conjClosure_eq_of_le_normalizer {V T : Subgroup G}
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) : conjClosure V T = V :=
  le_antisymm (conjClosure_le fun _ ht v hv => (Subgroup.mem_normalizer_iff.1 (hTV ht) v).1 hv)
    (le_conjClosure V T)

theorem amalgamHypV_of_hyp1223 (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    {T L V H : Subgroup G} (hyp : Hyp1223 G T L V)
    (huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
      M' = Subgroup.normalizer (L : Set G))
    (hTH : T ≤ H) (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) :
    AmalgamHypV ((L ⊔ T) ⊔ H) (L ⊔ T) H T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
  rw [hyp.conjClosure_eq, conjClosure_eq_of_le_normalizer hTV] at hO
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hyp.irrPlus.2.2.1 hTV
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVLT hLTV hVp
  have hO1 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h => hyp.irrPlus.2.1 (le_bot_iff.1 (h ▸ hVO))
  refine ⟨⟨rfl, charTwo_of_inH hyp.qtke.2.1 (hyp.sylow.1.toSylow hyp.sylow.2)
      ⟨le_sup_right, hO1⟩, isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right,
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH, ?_⟩,
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hred⟩, ?_⟩
  · by_contra hne
    obtain ⟨M', hM', hle⟩ := exists_inM_of_pCoreOf_ne_bot hne
    rw [huniq M' hM' (le_sup_left.trans hle)] at hle
    exact hHM (le_sup_right.trans hle)
  · rw [← hO]
    have hCN : L ⊔ T ≤ Subgroup.normalizer
        (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTV)
    refine le_antisymm ?_ (F7.pCoreOf_mono_of_le_normalizer inf_le_left hCN)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hO ▸ inf_le_right)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

omit [Finite G] in
theorem commutator_le_of_le_normalizer {V K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G)) : ⁅V, K⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv k hk
  rw [commutatorElement_def, show v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) by group]
  exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.1 (hK hk) _).1 (inv_mem hv))

omit [Finite G] in
theorem inf_centralizer_le_of_a5Module {K VH W : Subgroup G} (hW : IsA5ModuleUnder K W)
    (hWV : W ≤ VH) (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hO2K : pCoreOf 2 K ≤ Subgroup.centralizer (VH : Set G)) :
    K ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (VH : Set G) := by
  obtain ⟨d⟩ := A5Mod.exists_data hW
  have hKCW : K ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
    d.normalizes.trans (F7.normalizer_le_normalizer_centralizer W)
  have hNn : ((Subgroup.centralizer (W : Set G)).subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKCW
  have hN' : (((Subgroup.centralizer (W : Set G)).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
  have hpc : ∀ x : ↥K, x ∈ CFSG.pCore 2 ↥K → (x : G) ∈ Subgroup.centralizer (VH : Set G) := by
    intro x hx
    exact hO2K ⟨x, hx, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Subgroup.centralizer (W : Set G)).subgroupOf
      K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
  · intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx.1⟩ ∈ ((Subgroup.centralizer
        (W : Set G)).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx.2)
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hpc _ h1
  · exfalso
    have hall : ∀ k : ↥K, (k : G) ∈ Subgroup.centralizer (W : Set G) := by
      intro k
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) k ∈ ((Subgroup.centralizer
          (W : Set G)).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
        ht ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 h1
      have h2 : c⁻¹ * k ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.1 (by simpa using hce)
      have h3 : ((c⁻¹ * k : ↥K) : G) ∈ Subgroup.centralizer (W : Set G) :=
        Subgroup.centralizer_le hWV (hpc _ h2)
      have h5 : (c : G) ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_subgroupOf.1 hc
      have e : (k : G) = (c : G) * ((c⁻¹ * k : ↥K) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact Subgroup.mul_mem _ h5 h3
    obtain ⟨g, hg, x, -, hgx⟩ := A5Mod.nontrivial
    obtain ⟨k, hk⟩ := d.exists_q_eq hg
    have h1 := (d.q_eq_one k).2 (hall k)
    rw [h1] at hk
    apply hgx
    rw [← hk]
    exact A5Mod.act5_one x

theorem lemma12_4_1_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (h1227 : Stmt12_2_7) (h1232 : Cor12_3_2) : Lemma12_4_1 := by
  intro G _ _ T L V hyp hCZ hV hs
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -, ⟨H, hH⟩, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq hH
  have hTH : T ≤ H := hH.1.1
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := hH.2.1
  have hamal := amalgamHypV_of_hyp1223 h1222 h3228 hyp huniq hTH hHM
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  by_cases hW : weakClosureW0 T V ≤ pCoreOf 2 H
  ·
    have hb := even_critDist_of_weakClosureW0_le_G₂ hamal hV1 hW
    obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hamal hV1
    have hc := commutator_V_Vv_of_even hamal hV1 hb hγ hVγ
    obtain ⟨x, rfl⟩ := exists_smul_eq_γ₀ (vtype_eq_false_of_even hamal.gen (by rw [hγ]; exact hb))
    rw [Vv_smul_γ₀ hamal.normalizes] at hc
    obtain ⟨hne, hcl, -, -⟩ := hc
    have e1 : conjSub (x : G) V = CFSG.conjugate V (x : G)⁻¹ := by
      ext y
      show y ∈ conjSub (x : G) V ↔ y ∈ conjSubgroup V (x : G)⁻¹
      rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
    rw [e1] at hne hcl
    exact hcon _ hne hcl
  obtain ⟨g, hgT, hgO⟩ : ∃ g : G, conjSub g V ≤ T ∧ ¬ conjSub g V ≤ pCoreOf 2 H := by
    by_contra h
    push Not at h
    exact hW (iSup₂_le fun g hg => h g hg)
  have hAeq : conjSub g V = conjSubgroup V g⁻¹ := by
    ext y
    rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
  rw [hAeq] at hgT hgO
  set A := conjSubgroup V g⁻¹ with hAdef
  have hAel : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hV g⁻¹
  have hsA : E3.sParam hAel = E3.sParam hV := E3.sParam_conj hV g⁻¹ hAel
  obtain ⟨⟨hred2, hCT, -, -⟩, -⟩ := h1227 G T L V H hyp hCZ hH
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_left
  have hVHH : VZ T H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hTH (hZT hz))) (H.inv_mem hh)
  have hredVH : IsTwoReducedIn H (VZ T H) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVHH, hred2⟩
  have hVHel : IsElemAbelian 2 (VZ T H) := hredVH.2.2.1
  have hVHp : IsPGroup 2 (VZ T H) := fun x => ⟨1, Subtype.ext (by simpa using hVHel.2 x x.2)⟩
  have hAH : A ≤ H := hgT.trans hTH
  have hAV : ¬ A ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
    hgO (by rw [← hCT]; exact le_inf hgT h)
  have hA2 : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B ≤ 1 →
      VZ T H ⊓ Subgroup.centralizer (B : Set G) = VZ T H ⊓ Subgroup.centralizer (A : Set G) := by
    intro B hBA hm
    have hs' : E3.mQuot A B < E3.sParam hAel := by
      rw [hsA]
      omega
    exact (E3.e3_6 hAel hBA le_rfl hs' hVHp).1.symm
  by_cases hsolv : Group.IsSolvable ↥H
  ·
    have hHN := hredVH.2.1
    have hX : E3.aSet 2 (autI hVHel H) = ∅ :=
      E3.aSet_two_eq_empty (fun w => IntMod.sq_eq_one w) (isSolvable_autI hVHel hHN hsolv)
        (pCore_autI_eq_bot_of_reduced hredVH hVHel)
    have hAN : A ≤ Subgroup.normalizer (VZ T H : Set G) := hAH.trans hHN
    have hbar1 : autI hVHel A ≠ ⊥ := fun hb => hAV ((autI_eq_bot_iff hVHel hAN).1 hb)
    obtain ⟨B', hB'A, hmB', hfix⟩ : ∃ B' ≤ autI hVHel A, E3.mQuot (autI hVHel A) B' < 2 ∧
        fixV B' ≠ fixV (autI hVHel A) := by
      by_contra hcon'
      push Not at hcon'
      have hmem : autI hVHel A ∈ E3.aSet 2 (autI hVHel H) :=
        ⟨autI_mono hVHel hAH, hbar1, isElemAbelian2_autI hVHel hAel hAN, hcon'⟩
      rw [hX] at hmem
      exact hmem
    have hBA : preI hVHel A hAN B' ≤ A := preI_le hVHel
    have hmAB : E3.mQuot A (preI hVHel A hAN B') ≤ 1 := by
      rw [← E3.mQuot_autI_preI hVHel hAN hB'A]
      omega
    have hC := hA2 _ hBA hmAB
    apply hfix
    rw [← autI_preI hVHel (hA := hAN) hB'A]
    ext v
    rw [mem_fixV_autI hVHel (hBA.trans hAN) v, mem_fixV_autI hVHel hAN v]
    constructor
    · intro hv
      have h1 : v.val ∈ VZ T H ⊓ Subgroup.centralizer
          ((preI hVHel A hAN B' : Subgroup G) : Set G) := ⟨v.val_mem, hv⟩
      rw [hC] at h1
      exact h1.2
    · intro hv
      have h1 : v.val ∈ VZ T H ⊓ Subgroup.centralizer (A : Set G) := ⟨v.val_mem, hv⟩
      rw [← hC] at h1
      exact h1.2
  rcases h1232 G T L V H hyp hCZ hH with h | ⟨hLie, -, -, hsum⟩
  · exact hsolv h
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hsylH : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  rw [← VZ_eq_VZ_oTwoUpper hsylH] at hsum
  obtain ⟨W, hW, hWle⟩ : ∃ W : Subgroup G, IsA5ModuleUnder (oTwoUpper H) W ∧
      W ≤ ⁅VZ T H, oTwoUpper H⁆ := by
    rcases hsum with h | ⟨W₁, W₂, hW₁, -, -, hsup⟩
    · exact ⟨_, h, le_rfl⟩
    · exact ⟨W₁, hW₁, hsup ▸ le_sup_left⟩
  have hWV : W ≤ VZ T H :=
    hWle.trans (commutator_le_of_le_normalizer (hKH.trans hredVH.2.1))
  have hO2K : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.centralizer (VZ T H : Set G) := by
    have h1 : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := F7.pCoreOf_mono_of_le_normalizer hKH hHK
    rw [← hCT] at h1
    exact h1.trans inf_le_right
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hLie
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hCW := inf_centralizer_le_of_a5Module hW hWV e.isSimpleGroup hO2K
  exact A5Mod.false_of_a5Module hKH hHK (fun h hh => exists_pow_mem_oTwoUpper H hh) hredVH hWV hW
    hCW hAH hAel hAV hA2

end CFSG.Quasithin.H13
