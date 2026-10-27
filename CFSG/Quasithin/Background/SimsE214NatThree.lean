module

public import CFSG.Quasithin.Background.SimsE214NatCoord
public import CFSG.Quasithin.Background.SimsE214Eleven
public import CFSG.Quasithin.Background.SimsE213M
public import CFSG.Quasithin.Vol2.E2FourteenB
public import CFSG.Quasithin.EmptyFaithful.SBd8Psl2
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1

public section

open scoped commutatorElement MatrixGroups

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank SL2Model

namespace E214N

variable {G : Type} [Group G] [Finite G]

theorem exists_isSum_of_pair {T M V I : Subgroup G} {g : G} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (hPJ : (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) = kerIn (M ⊓ I) I)
    {F : Type} [Field F] [Finite F] [CharP F 2] (θ : E2.StarQuot (M ⊓ I) I ≃* SL(2, F))
    (hθV : ∀ t, t ∈ E2.star (M ⊓ I) I V ↔ θ t ∈ Rg F)
    (hNV : ∀ x : ↥I, θ (E2P.starMap (M ⊓ I) I x) ∈ Subgroup.normalizer (Rg F : Set SL(2, F)) →
      (x : G) ∈ Subgroup.normalizer (V : Set G))
    (hPZ : ∃ x ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V),
      x ∉ V ⊓ B6.conjSub g V) :
    ∃ s : ℕ, IsSumOfNaturalSections s I
      ((kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V)) (V ⊓ B6.conjSub g V)
      (kerIn (M ⊓ I) I) (StatedSL 2 F) := by
  let β : ↥I →* SL(2, F) := θ.toMonoidHom.comp (E2P.starMap (M ⊓ I) I)
  have hβapp : ∀ x, β x = θ (E2P.starMap (M ⊓ I) I x) := fun x => rfl
  have hβs : Function.Surjective β := θ.surjective.comp (E2P.starMap_surjective _ _)
  have hβker : ∀ x : ↥I, β x = 1 ↔ (x : G) ∈ kerIn (M ⊓ I) I := by
    intro x
    rw [hβapp, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, E2P.ker_starMap,
      Subgroup.mem_subgroupOf]
  have hRU : ∀ r ∈ Rg F, ∃ u : ↥I, (u : G) ∈ V ∧ β u = r := by
    intro r hr
    obtain ⟨t, rfl⟩ := θ.surjective r
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ((hθV t).2 hr)
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, rfl⟩
  have hinv : ∀ i : ↥I, (β i).1 1 0 = 0 → ∀ w ∈ kerIn (M ⊓ I) I ⊓ V,
      (i : G) * w * (i : G)⁻¹ ∈ kerIn (M ⊓ I) I ⊓ V := by
    intro i hi w hw
    have hiN := hNV i (E2.mem_normalizer_Rg_of_lower_left_eq_zero hi)
    exact ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn (M ⊓ I) I i.2) w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp hiN w).mp hw.2⟩
  have hh : (β ⟨g, hp.mem⟩).1 1 0 ≠ 0 := by
    intro h0
    have hgN := hNV ⟨g, hp.mem⟩ (E2.mem_normalizer_Rg_of_lower_left_eq_zero h0)
    have hIV : ∀ x ∈ I, x ∈ V := by
      intro x hx
      rw [hp.gen, B6.conjSub_eq_self hgN, sup_idem] at hx
      exact hx
    obtain ⟨a', ha'⟩ := hβs (e12 1)
    obtain ⟨b', hb'⟩ := hβs (e21 1)
    apply e12_mul_e21_ne (F := F)
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hp.comm (hIV _ a'.2) (hIV _ b'.2))
  have hcomm : ∀ u ∈ V, ∀ x ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V),
      ⁅u, x⁆ ∈ kerIn (M ⊓ I) I ⊓ V := fun u hu x hx => by
    rw [commutatorElement_def]
    exact hp.commutator_mem_B hu (hp.P_le_pCoreOf hx)
  have hfix : ∀ u ∈ V, ∀ w ∈ kerIn (M ⊓ I) I ⊓ V, ⁅u, w⁆ ∈ V ⊓ B6.conjSub g V :=
    fun u hu w hw => by
      rw [commutatorElement_def, hp.comm hu hw.2, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hPX : (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V) ≤ I :=
    hp.P_le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
  have Q : QuotSetting I ((kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g (kerIn (M ⊓ I) I ⊓ V))
      (V ⊓ B6.conjSub g V) :=
    ⟨hp.inf_conj_le_P, hPX,
      fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_P hx) y).mp hy,
      fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hp.le_normalizer_Z hx) y).mp hy,
      fun a ha b hb => (hp.commutator_sq_mem_Z ha hb).1,
      fun a ha => by
        rw [← pow_two]
        exact (hp.commutator_sq_mem_Z ha ha).2⟩
  obtain ⟨s, φ, hφs, hφk, hφe, -, -⟩ := exists_sum_natural_of_halves
    (G1.theorem_G_1_3_two (F := F)) Q β hβs
    (fun x hx => by rw [hPJ]; exact (hβker x).1 hx)
    hp.inf_conj_le_kerIn_inf le_sup_left ⟨g, hp.mem⟩ hh (fun y => B6.mem_conjSub) hinv hRU
    hcomm hfix hp.B_inf_A rfl
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · exfalso
      subst hs0
      obtain ⟨x, hxP, hxZ⟩ := hPZ
      exact hxZ ((hφk ⟨x, hxP⟩).1 (Multiplicative.toAdd.injective (funext fun j => j.elim0)))
    · exact hs0
  exact ⟨s, isSumOfNaturalSections_of_coord φ hp.inf_conj_le_P (kerIn_le.trans inf_le_right)
    hp.le_normalizer_P hp.le_normalizer_Z β hβs hβker hs hφs hφk hφe⟩

end E214N

open E214N E214E

theorem e214_three
    {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V) :
    CharTwo H → IsTISetIn V M →
    ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
      V ⊓ conjSubgroup V g ≠ ⊥ →
      ∀ (MI TI JI B A P Z : Subgroup Γ) (k : ℕ),
        MI = M ⊓ I → TI = T ⊓ I → JI = kerIn MI I → B = V ⊓ pCoreOf 2 I →
        A = conjSubgroup V g ⊓ pCoreOf 2 I → P = A ⊔ B → Z = V ⊓ conjSubgroup V g →
        E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞) →
        ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
            Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) →
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
            ∃ r : ℕ, IsSumOfNaturalSections r I P Z JI (CFSG.Open.StatedSL 2 F)) := by
  intro hc hTI I g hI hg hgen hZ MI TI JI B A P Z k hMI _ hJI hB hA hP hZdef _ hSL
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hSL
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  subst hMI hJI hB hA hP hZdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have := E2P.finite_starQuot (M ⊓ I) I
  have hgen' : I = V ⊔ B6.conjSub g⁻¹ V := by
    rw [← conjSubgroup_eq_conjSub_inv]
    exact hgen
  have hZ' : V ⊓ B6.conjSub g⁻¹ V ≠ ⊥ := by
    rw [← conjSubgroup_eq_conjSub_inv]
    exact hZ
  obtain ⟨hp, hVZ, -, -, hJ, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) (I.inv_mem hg) hgen'
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen'] at this
  have h1 : M ⊓ I = I ⊓ Subgroup.normalizer (V : Set Γ) :=
    E2.inf_eq_inf_normalizer_of_central hTI (hp.normalizer_le.trans inf_le_left) hZ' inf_le_left
      fun z hz x hx => hp.mem_center hz hx
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set Γ) := h1.le.trans inf_le_right
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨θ, hθT⟩ :=
    exists_equiv_mem_Rg_iff hS (e₀.trans (specialLinearGroupEquivStatedSL 2 F).symm)
  have hTab : ∀ t ∈ E2.star (M ⊓ I) I (T ⊓ I), ∀ t' ∈ E2.star (M ⊓ I) I (T ⊓ I),
      t * t' = t' * t := by
    intro t ht t' ht'
    apply θ.injective
    rw [map_mul, map_mul]
    exact comm_of_mem_Rg ((hθT t).1 ht) ((hθT t').1 ht')
  have hTR : (E2.star (M ⊓ I) I (T ⊓ I)).map θ.toMonoidHom = Rg F := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (hθT t).1 ht
    · intro hr
      obtain ⟨t, rfl⟩ := θ.surjective r
      exact Subgroup.mem_map.2 ⟨t, (hθT t).2 hr, rfl⟩
  have hcardT : Nat.card (E2.star (M ⊓ I) I (T ⊓ I)) = Nat.card F := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective, hTR, Rg_card]
  have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hMIN : ∀ x : ↥I, E2P.starMap (M ⊓ I) I x ∈ E2.star (M ⊓ I) I (M ⊓ I) →
      (x : Γ) ∈ Subgroup.normalizer (V : Set Γ) := by
    intro x hx
    obtain ⟨m, hm, hmx⟩ := hx
    replace hm : (m : Γ) ∈ M ⊓ I := hm
    have hmx' : (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) m : E2.StarQuot (M ⊓ I) I) =
        QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) x := hmx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hmx'
    have hj : (m : Γ)⁻¹ * x ∈ pCoreOf 2 I := by
      rw [hJ]
      simpa using hmx'
    have e : (x : Γ) = m * ((m : Γ)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hMN hm) (hp.pCoreOf_le_normalizer hj)
  obtain ⟨hPJ, hVeq, hNV⟩ : (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) =
        kerIn (M ⊓ I) I ∧ E2.star (M ⊓ I) I V = E2.star (M ⊓ I) I (T ⊓ I) ∧
      ∀ x : ↥I, θ (E2P.starMap (M ⊓ I) I x) ∈ Subgroup.normalizer (Rg F : Set SL(2, F)) →
        (x : Γ) ∈ Subgroup.normalizer (V : Set Γ) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    ·
      have hk1 : k = 1 := by
        have := SBd8.Psl2.one_le_of_card_two_pow hF
        omega
      have hF2 : Nat.card F = 2 := by rw [hF, hk1, pow_one]
      have : Nontrivial SL(2, F) :=
        ⟨⟨e12 1, 1, fun h1 => one_ne_zero (e12_injective (h1.trans e12_zero.symm))⟩⟩
      have : Nontrivial (E2.StarQuot (M ⊓ I) I) := θ.toEquiv.nontrivial
      have hVne : E2.star (M ⊓ I) I V ≠ ⊥ := E2.star_ne_bot_of_gen (I.inv_mem hg) hgen'
      have hcardV : Nat.card (E2.star (M ⊓ I) I V) = 2 := by
        have h2 := Subgroup.card_le_of_le hVT
        have h3 : Nat.card (E2.star (M ⊓ I) I V) ≠ 1 := fun h4 => hVne (Subgroup.card_eq_one.1 h4)
        have h4 := Nat.card_pos (α := E2.star (M ⊓ I) I V)
        rw [hcardT, hF2] at h2
        omega
      have hVeq : E2.star (M ⊓ I) I V = E2.star (M ⊓ I) I (T ⊓ I) :=
        Subgroup.eq_of_le_of_card_ge hVT (by rw [hcardV, hcardT, hF2])
      have hidx : (kerIn (M ⊓ I) I ⊓ V).relIndex V = 2 := by
        rw [← E2.card_star_of_le hp.V_le]
        exact hcardV
      obtain ⟨hPO, hOJ, -⟩ := hp.e2_10_six hidx
      refine ⟨hPO.trans hOJ, hVeq, fun x hx => ?_⟩
      have hR := mem_Rg_of_lower_left_eq_zero hF2 (E2.lower_left_eq_zero_of_mem_normalizer_Rg hx)
      obtain ⟨v, hv, hvx⟩ := (hVeq ▸ (hθT _).2 hR : E2P.starMap (M ⊓ I) I x ∈ E2.star (M ⊓ I) I V)
      replace hv : (v : Γ) ∈ V := hv
      have hvx' : (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) v :
          E2.StarQuot (M ⊓ I) I) = QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) x := hvx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at hvx'
      have hj : (v : Γ)⁻¹ * x ∈ pCoreOf 2 I := by
        rw [hJ]
        simpa using hvx'
      have e : (x : Γ) = v * ((v : Γ)⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer hv) (hp.pCoreOf_le_normalizer hj)
    ·
      have hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) := SBd8.Psl2.isPSL_of_statedSL hk hF e₀
      have hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) := by
        obtain ⟨-, -, -, -, k', -, hc⟩ := hI
        rcases hc with ⟨-, -, hB⟩ | ⟨-, p, a, hp', hp2, -, ⟨d⟩⟩ | ⟨-, -, -, hB, -⟩
        · exact hB
        · exfalso
          have h2 := E2.card_le_two_of_isPGroup_dihedral (hp'.odd_of_ne_two hp2).pow d hS.2.1
          rw [hcardT, hF] at h2
          have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
          omega
        · exact hB
      obtain ⟨hPJ', hVZT⟩ := E2.star_eq_center_of_psl_or_sz E2.kgSz8CoverInvolutions_holds
        E2.kgI22One_holds hp hsyl hTMI (I.inv_mem hg) hgen' hVZ hMN hBorel hk (Or.inl hY)
      have hVeq : E2.star (M ⊓ I) I V = E2.star (M ⊓ I) I (T ⊓ I) := by
        rw [hVZT]
        exact le_antisymm inf_le_left fun t ht =>
          ⟨ht, Subgroup.mem_centralizer_iff.mpr fun x hx => hTab x hx t ht⟩
      have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel
      refine ⟨hPJ'.resolve_right (E2.not_isSz_three_of_isPSL hY), hVeq, fun x hx => hMIN x ?_⟩
      rw [hBor, Subgroup.mem_normalizer_iff]
      intro t
      rw [hθT, hθT, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hx) (θ t)
  obtain ⟨hIV, -⟩ := E213M.ne_and_rank h hI hp hcharI
  obtain ⟨-, -, -, -, hnc, -⟩ := Ch3n.exists_cubic_of_pair hp hcharI hIV
  have hPZ : ∃ x ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V),
      x ∉ V ⊓ B6.conjSub g⁻¹ V := by
    obtain ⟨a, ha, hac⟩ := SetLike.not_le_iff_exists.1 hnc
    refine ⟨a, le_sup_right (b := B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V)) ha, fun haZ => hac ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hp.comm hv haZ.1
  obtain ⟨s, hs⟩ := exists_isSum_of_pair hp hPJ θ (fun t => by rw [hVeq]; exact hθT t) hNV hPZ
  refine ⟨s, ?_⟩
  have hPeq : B6.conjSub g⁻¹ V ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm]
  rw [conjSubgroup_eq_conjSub_inv V g, hPeq]
  exact hs

end CFSG.Quasithin.SimsE2
