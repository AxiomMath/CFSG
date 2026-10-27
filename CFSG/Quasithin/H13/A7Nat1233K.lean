module

public import CFSG.Quasithin.H13.A7Nat1233KInputs
public import CFSG.Quasithin.H13.A7Nat1233KCases
public import CFSG.Quasithin.H13.A7Nat1233KXi
public import CFSG.Quasithin.H13.A7Nat1233Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem autOn_Kv_four (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    (hyp : Hyp1223 G T L V) (hS : Setting1233Four hyp) {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hzZ : z ∈ quasithinOmegaOneCenter T) :
    ∃ S : Subgroup (MulAut ↥V), autOn (Kv hyp z) V = S ∧ autOn (Kv hyp z ⊔ T) V = S ∧
      IsSimpleGroup S ∧ Nat.card S = 168 ∧ pCoreOf 2 S = ⊥ ∧ V = ⁅V, Kv hyp z⁆ := by
  classical
  obtain ⟨-, hcard, φ, hφs, hφk⟩ := hS
  obtain ⟨-, hTV, hab, hsq⟩ := facts1233Four h1222 hyp
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hΓ : Nat.card (autOn L V) = 2520 := card_autOn_of_ker hLV hφs hφk
  have hW2 : ∀ w : ↥V, w * w = 1 := fun w => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hsq w w.2)
  have hz' : (⟨z, hzV⟩ : ↥V) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hCzV : L ⊓ centralizer ({z} : Set G) ≤ normalizer (V : Set G) := inf_le_left.trans hLV
  have hLzV : hyp.Lv z ≤ normalizer (V : Set G) := (oTwoUpper_le _).trans hCzV
  have hLz : autOn (hyp.Lv z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    change autOn (oTwoUpper (L ⊓ centralizer ({z} : Set G))) V = _
    rw [autOn_oTwoUpper_eq hCzV, autOn_inf_centralizer_eq hLV hzV,
      oTwoUpper_fourStab hW2 hcard hΓ hz']
  have hSperf := commutator_fourStab hW2 hcard hΓ hz'
  have hKz : autOn (Kv hyp z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    change autOn (perfectCore (hyp.Lv z)) V = _
    rw [autOn_perfectCore_eq hLzV, hLz, perfectCore_eq_self_of_perfect hSperf]
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hT : autOn T V ≤ fourStab (autOn L V) ⟨z, hzV⟩ := by
    intro a ha
    obtain ⟨t, rfl⟩ := (A4.mem_autOn_iff hTV).1 ha
    refine ⟨mem_of_mem_normalizer_four hW2 hcard hΓ
      (autOn_le_normalizer_autOn hLV hTV hyp.normalizes
        ((A4.mem_autOn_iff hTV).2 ⟨t, rfl⟩)), MulAction.mem_stabilizer_iff.2 ?_⟩
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    rw [mem_centralizer_iff.1 (hZC hzZ) t t.2, mul_inv_cancel_right]
  have hKzV : Kv hyp z ≤ normalizer (V : Set G) := (Kv_le_L hyp z).trans hLV
  refine ⟨fourStab (autOn L V) ⟨z, hzV⟩, hKz, ?_, isSimpleGroup_fourStab hW2 hcard hΓ hz',
    card_fourStab hcard hΓ hz', pCoreOf_fourStab hW2 hcard hΓ hz',
    eq_commutator_of_commV_eq_top hKzV
      (by rw [hKz]; exact commV_fourStab_eq_top hW2 hcard hΓ hz')⟩
  rw [autOn_sup_eq_sup_autOn hKzV hTV, hKz]
  exact sup_eq_left.2 hT

theorem insp1233K_of
    (h1222 : Stmt12_2_2) (h1225 : Stmt12_2_5)
    (hC41 : ∀ (G : Type) [Group G] [Finite G], ASC41Statement G)
    (h3214 : Stmt3_2_14) (hLin : Insp1233KLin) : Insp1233K := by
  intro G _ _ T L V hyp hS z hzV hz1 hzZ hC28 K hK hKzK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : Kv hyp z < K := lt_of_le_of_ne hKzK hne
  obtain ⟨hVT, hTV, -, hsq⟩ := facts1233Four h1222 hyp
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hKzV : Kv hyp z ≤ normalizer (V : Set G) := (Kv_le_L hyp z).trans hLV
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTz : T ≤ hyp.Gv z := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hzZ) t ht))
  have hTMz : T ≤ hyp.Mv z := le_inf hyp.normalizes hTz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hsq z hzV) hz1
  have hTKz : T ≤ normalizer (Kv hyp z : Set G) := T_le_normalizer_Kv hyp h1225 hzV hz1 hzZ
  obtain ⟨S, hKzS, hKzTS, hSs, hScard, hSp, hVc⟩ := autOn_Kv_four h1222 hyp hS hzV hz1 hzZ
  have hKzL : Kv hyp z ∈ lFamily T := cComp_subset_lFamily hTMz hC28.comp
  have hlocz : quasithinIsLocal T (Kv hyp z) :=
    ⟨hyp.sylow.1, hKzL, (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2,
      pCoreOf_ne_bot_of_le_centralizer hz2 ((le_sup_right : T ≤ Kv hyp z ⊔ T) (hVT hzV))
        (sup_le (Kv_le_centralizer hyp z) hTz)⟩
  have hKH : K ≤ hyp.Gv z := le_of_mem_cComp hK
  have hlocK : quasithinIsLocal T K :=
    ⟨hyp.sylow.1, cComp_subset_lFamily hTz hK, (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2,
      pCoreOf_ne_bot_of_le_centralizer hz2 ((le_sup_right : T ≤ K ⊔ T) (hVT hzV))
        (sup_le hKH hTz)⟩
  have := hyp.simple
  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hH2 : pCoreOf 2 (hyp.Gv z) ≠ ⊥ :=
    pCoreOf_ne_bot_of_le_centralizer hz2 (mem_centralizer_singleton_iff.2 rfl) le_rfl
  have hTK : T ≤ normalizer (K : Set G) := by
    intro t ht
    have hKt := map_conj_mem_cComp hK (hTz ht)
    have hKzt : Kv hyp z ≤ K.map (MulAut.conj t).toMonoidHom := by
      intro k hk
      have hk' : t⁻¹ * k * t ∈ Kv hyp z := by
        have := (mem_normalizer_iff.1 (hTKz (T.inv_mem ht)) k).1 hk
        simpa using this
      exact ⟨t⁻¹ * k * t, hKzK hk', by simp [MulAut.conj_apply, mul_assoc]⟩
    have heq := QuasithinUnique.Vol2Native.lemma_1_2_4_unique hLocal
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved hH2 hKzL hKt hK hKzt hKzK
    exact A38.map_conj_eq_iff.1 heq
  have hKM : ¬ K ≤ hyp.Mv z := by
    intro hKM
    obtain ⟨-, hMzN, -, -, -⟩ := h1225 G T L V hyp z hzV hz1
    have hKN : K ≤ normalizer (Kv hyp z : Set G) :=
      hKM.trans (hMzN.trans (normalizer_le_normalizer_perfectCore _))
    exact not_subnormal_of_mem_cComp hK hlt (ne_bot_of_mem_cComp hC28.comp)
      (Kv_perfect hyp z) (IsSubnormal.step hKzK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hKzK).2 hKN) (subnormal_of_mem_cComp hK))
  have hKzTV : Kv hyp z ⊔ T ≤ normalizer (V : Set G) := sup_le hKzV hTV
  have hO2V : pCoreOf 2 (Kv hyp z ⊔ T) ≤ centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_autOn hKzTV hKzTS hSp
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hsq x x.2)⟩
  have hVP : V ≤ pCoreOf 2 (Kv hyp z ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) hKzTV hV2
  have hVZ : V ≤ omegaOneCenterOf (pCoreOf 2 (Kv hyp z ⊔ T)) := fun v hv =>
    Subgroup.subset_closure ⟨⟨hVP hv, (Subgroup.le_centralizer_iff.1 hO2V) hv⟩, hsq v hv⟩
  have hTN : T ⊓ normalizer (Kv hyp z : Set G) = T := inf_eq_left.2 hTKz
  have hsylNT : ∀ Y : Subgroup G, QuasithinUnique.IsSylowTwoOf
      (T ⊓ normalizer (Kv hyp z : Set G)) ((Y ⊔ T) ⊓ normalizer (Kv hyp z : Set G)) :=
    fun Y => by
      rw [hTN]
      exact isSylowTwoOf_of_le hyp.sylow (le_inf le_sup_right hTKz)
  have hA : A410Hyp (Kv hyp z) K T :=
    { xclass := isXClass_of_isLocal hyp.qtke hyp.sylow hlocz
      yclass := isXClass_of_isLocal hyp.qtke hyp.sylow hlocK
      xy := hKzK
      normalizes := hTK
      sylowT := isSylowTwoOf_of_le hyp.sylow le_sup_right
      o2le := by
        rw [hTN]
        exact QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
          (isSylowTwoOf_of_le hyp.sylow le_sup_right)
      sylowNT := hsylNT K }
  have hA' : A410Hyp (Kv hyp z) (Kv hyp z) T :=
    { xclass := isXClass_of_isLocal hyp.qtke hyp.sylow hlocz
      yclass := isXClass_of_isLocal hyp.qtke hyp.sylow hlocz
      xy := le_rfl
      normalizes := hTKz
      sylowT := isSylowTwoOf_of_le hyp.sylow le_sup_right
      o2le := by
        rw [hTN]
        exact QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
          (isSylowTwoOf_of_le hyp.sylow le_sup_right)
      sylowNT := hsylNT (Kv hyp z) }
  have h410 := a4_10_2 hA
  rw [← pCoreOf_sup_eq_centralizerSection hA'] at h410
  have hVK : V ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), K⁆ :=
    hVc.le.trans ((commutator_mono hVZ le_rfl).trans h410)
  have hCM : K ⊓ centralizer (V : Set G) ≤ hyp.Mv z := fun x hx =>
    hC28.V_norm ⟨hKH hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  have hKzM : Kv hyp z ≤ hyp.Mv z := le_of_mem_cComp hC28.comp
  obtain ⟨θ, hθs, hθ1⟩ := exists_surj_autOn hKzV hKzS
  have hPKz : pCoreOf 2 (Kv hyp z) ≤ centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_autOn hKzV hKzS hSp
  by_cases hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  ·
    obtain ⟨hL0, -, -, hcase⟩ := hC41 G (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V K hC28 hK
      (charTwo_of_isLocal hyp.qtke hyp.sylow hlocK) hq hKM
    have hO2 : CFSG.pCore 2 ↥(Kv hyp z) ≤ θ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, hθ1]
      apply hPKz
      rw [pCoreOf_eq_map_cfsgPCore]
      exact ⟨x, hx, rfl⟩
    have hθ's : Function.Surjective (QuotientGroup.lift _ θ hO2) :=
      QuotientGroup.lift_surjective_of_surjective _ _ hθs hO2
    have hdvd : 168 ∣ Nat.card (ModO2 (Kv hyp z)) :=
      hScard ▸ Subgroup.card_dvd_of_surjective hθ's
    rcases hcase with ⟨n, hn, hblock, -⟩ | ⟨-, F, _, _, -, -, -, -, -, -, -, h2⟩ |
        ⟨n, F, _, _, -, -, -, -, -, -, h3, -⟩ | h4
    ·
      rw [← hL0] at hblock
      obtain ⟨-, α, hαs, hαk, -⟩ := hblock
      have hc : Nat.card (ModO2 (Kv hyp z)) = Nat.card (alternatingGroup (Fin n)) :=
        Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαs)).toEquiv
      rw [hc] at hdvd
      rcases hn with rfl | rfl
      · rw [nat_card_alternatingGroup, Nat.card_fin] at hdvd
        norm_num [Nat.factorial] at hdvd
      · rw [nat_card_alternatingGroup, Nat.card_fin] at hdvd
        norm_num [Nat.factorial] at hdvd
    ·
      obtain ⟨X, hX, h2'⟩ : ∃ X, X = Kv hyp z ∧ IsPSL 2 2 2 (ModO2 X) := ⟨_, hL0.symm, h2⟩
      subst hX
      exact false_of_isPSL_two_two_of_surj h2' _ hθ's hScard
    ·
      obtain ⟨X, hX, h3'⟩ : ∃ X, X = Kv hyp z ∧ IsPSL 2 2 n (ModO2 X) := ⟨_, hL0.symm, h3⟩
      subst hX
      exact false_of_isPSL_two_two_of_surj h3' _ hθ's hScard
    ·
      exact hLin G T L V hyp hS z hzV hz1 hzZ hC28 K hK hlt hTK hKM hVK hO2V h4
  ·
    have hNQ := a312Nonquasi_of_isLocal hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hlocK hKzL
      hKzK hq
    unfold A312Nonquasi at hNQ
    dsimp only at hNQ
    rcases hNQ with ⟨-, hLB, -⟩ | ⟨-, -, N, hN, hNeq, hSL5⟩
    ·
      have hKA : K ≤ normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) :=
        le_sup_left.trans ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf _))
      have hVA : V ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) :=
        hVK.trans (le_normalizer_iff_commutator_le_left.mp hKA)
      have hC : oddPre K T ≤ centralizer (V : Set G) :=
        (oddPre_le_centralizer h3214 hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hlocK hTK
          hq).trans (centralizer_le hVA)
      exact hKM ((le_sup_of_le_sup_oddPre hKzK hC hLB.le).trans (sup_le hCM hKzM))
    ·
      have := hSs
      have hKzP : ∀ k : ↥(Kv hyp z), (k : G) ∈ pCoreOf 2 (K ⊔ T) → θ k = 1 := by
        intro k hk
        rw [hθ1]
        apply hPKz
        have hKN : Kv hyp z ≤ normalizer (pCoreOf 2 (K ⊔ T) ⊓ Kv hyp z : Set G) := fun x hx =>
          A4.mem_normalizer_inf
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)
              ((le_sup_left : K ≤ K ⊔ T) (hKzK hx)))
            (le_normalizer hx)
        exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hKN
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)).to_le inf_le_left) ⟨hk, k.2⟩
      exact false_of_isSL2_five_of_surj hKzK le_sup_left hScard θ hθs hKzP N hNeq hSL5

end CFSG.Quasithin.H13.A7
