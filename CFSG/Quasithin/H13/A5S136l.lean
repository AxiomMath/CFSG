module

public import CFSG.Quasithin.H13.A5S136j
public import CFSG.Quasithin.H13.A5S136h
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Fstar
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped commutatorElement

@[expose] def c0 : W5 →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) 0)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def W23 : Subgroup W5 := c0.ker ⊓ c01.ker

theorem mem_W23 {x : W5} : x ∈ W23 ↔ c0 x = 1 ∧ c01 x = 1 := Iff.rfl

theorem perm_odd_fix_E12 : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → pact σ E12 = E12 →
    σ ^ 15 = 1 → σ = 1 ∨ σ = c234 ∨ σ = c234⁻¹ := by
  decide +kernel

theorem comm_mem_W23 : ∀ x : W5,
    (c0 (x * (pact c234 x)⁻¹) = 1 ∧ c01 (x * (pact c234 x)⁻¹) = 1) ∧
      (c0 (x * (pact c234⁻¹ x)⁻¹) = 1 ∧ c01 (x * (pact c234⁻¹ x)⁻¹) = 1) := by
  decide +kernel

theorem W23_gen : ∀ y : W5, c0 y = 1 → c01 y = 1 →
    (∃ w : W5, (c0 w = 1 ∧ c01 w = 1) ∧ y = w * (pact c234 w)⁻¹) ∧
      (∃ w : W5, (c0 w = 1 ∧ c01 w = 1) ∧ y = w * (pact c234⁻¹ w)⁻¹) := by
  decide +kernel

theorem W4_E12_mem : c0 (W4 * E12⁻¹) = 1 ∧ c01 (W4 * E12⁻¹) = 1 := by
  decide +kernel

theorem mem_zpowers_c234 {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ Subgroup.zpowers c234) :
    σ = 1 ∨ σ = c234 ∨ σ = c234⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have h3 : c234 ^ (3 : ℤ) = 1 := by decide
  have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have e : c234 ^ k = c234 ^ (k % 3) := by
    conv_lhs => rw [hk, zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rw [e]
  interval_cases h : k % 3
  · left
    exact zpow_zero c234
  · right; left
    exact zpow_one c234
  · right; right
    decide

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem v12_mem_pCoreOf {X : Subgroup G} (hX : X ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hv : S.v12 ∈ X) : S.v12 ∈ pCoreOf 2 X := by
  have hv2 : S.v12 ^ 2 = 1 := S.elemAbelian_V.2 _ S.v12_mem_V
  have hle : Subgroup.zpowers S.v12 ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.zpowers_le.mpr hv) (fun x hx => ?_) ?_
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hX hx)).symm
        k).eq
    · exact S.isPGroup_V.to_le (Subgroup.zpowers_le.mpr S.v12_mem_V)
  exact hle (Subgroup.mem_zpowers _)

theorem lemma115Hyp_Gv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) :
    Lemma115Hyp (Subgroup.centralizer ({S.v12} : Set G)) S.Tv S.G1 S.z := by
  have hTG1 : T ≤ S.G1 := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := S.conj_z_of_mem_T ht
      calc t * S.z = t * S.z * t⁻¹ * t := by group
        _ = S.z * t := by rw [this])
  have hzGv : S.z ∈ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (S.elemAbelian_V.1.is_comm.comm ⟨S.z, S.z_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
  have hG1 : InH T S.G1 := ⟨hTG1, fun h => S.z_ne_one (by
    have := S.V1_le_pCoreOf_G1 (Subgroup.mem_zpowers S.z)
    rw [h] at this
    exact Subgroup.mem_bot.mp this)⟩
  have hvGv : S.v12 ∈ Subgroup.centralizer ({S.v12} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine
    { pCore_ne_bot := fun h => S.v12_ne_one (by
        have := S.v12_mem_pCoreOf le_rfl hvGv
        rw [h] at this
        exact Subgroup.mem_bot.mp this)
      sylow := S.isSylowTwoOf_centralizer h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
      charTwo := S.charTwo_of_inH hG1
      pCore_M_ne_bot := hG1.2
      le := inf_le_left.trans hTG1
      centralizer_le := fun x hx => ?_
      centralizer_z_le := le_rfl
      z_ne_one := S.z_ne_one
      z_mem := ⟨S.V_le_T S.z_mem_V, hzGv⟩
      z_central := ?_
      z_sq := S.z_sq }
  ·
    have hv : S.v12 ∈ pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G) ⊓ S.G1) :=
      S.v12_mem_pCoreOf inf_le_left ⟨hvGv, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val
          (S.elemAbelian_V.1.is_comm.comm ⟨S.v12, S.v12_mem_V⟩ ⟨S.z, S.z_mem_V⟩))⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 S.v12 hv).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]

theorem rho_Lv {x : G} (hx : x ∈ S.Lv) : ∃ h : x ∈ Subgroup.normalizer (V : Set G),
    S.frame.ρ ⟨x, h⟩ = 1 ∨ S.frame.ρ ⟨x, h⟩ = c234 ∨ S.frame.ρ ⟨x, h⟩ = c234⁻¹ := by
  set P : Subgroup G :=
    ((Subgroup.zpowers c234).comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype
    with hP
  have hLvP : S.Lv ≤ P := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨hyL', hyv'⟩, m, hm, hym⟩
    have hyL : y ∈ L := hyL'
    have hyv : y ∈ Subgroup.centralizer ({S.v12} : Set G) := hyv'
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hyL
    set σ := S.frame.ρ ⟨y, hyN⟩ with hσ
    have hsign : σ.sign = 1 := (S.frame.image_L σ).1 ⟨⟨y, hyN⟩, hyL, rfl⟩
    have hfix : pact σ E12 = E12 := by
      have h1 : y * S.v12 * y⁻¹ = S.v12 := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hyv
        rw [hyv]
        group
      have h2 := (S.conj_eq_iff ⟨y, hyN⟩ ⟨S.v12, S.v12_mem_V⟩).1 h1
      rwa [S.psi_v12] at h2
    have hσm : σ ^ m = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ m = 1 :=
        Subtype.ext (by simpa using hym)
      rw [this, map_one]
    have h15 : σ ^ 15 = 1 := by
      have h1 : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hσm
      have h2 : orderOf σ ∣ 8 * 15 := by
        have := orderOf_dvd_natCard σ
        rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
      have hodd : Odd (orderOf σ) := Odd.of_dvd_nat hm h1
      have hcop : Nat.Coprime (orderOf σ) 8 :=
        Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd) |>.symm.symm
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h2)
    have hmem := perm_odd_fix_E12 σ hsign hfix h15
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    show σ ∈ Subgroup.zpowers c234
    rcases hmem with h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers c234
    · rw [h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c234)
  obtain ⟨y, hy, rfl⟩ := hLvP hx
  exact ⟨y.2, mem_zpowers_c234 hy⟩

theorem exists_Lv_c234 : ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ S.Lv ∧
    (S.frame.ρ l = c234 ∨ S.frame.ρ l = c234⁻¹) := by
  obtain ⟨l₀, hl₀L, hl₀σ⟩ := (S.frame.image_L c234).2 c234_sign
  have hl₀ : (l₀ : G) ∈ L ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
    ⟨hl₀L, S.mem_centralizer_v12 l₀ (by rw [hl₀σ]; exact pact_c234_E12)⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ hl₀
  rw [← oTwoRes_eq_oTwoUpper] at hk
  have hk' : (l₀ : G) ^ 2 ^ k ∈ S.Lv := hk
  refine ⟨l₀ ^ 2 ^ k, by simpa using hk', ?_⟩
  rw [map_pow, hl₀σ]
  exact c234_pow_two_pow k

theorem commutator_V_Lv : ⁅V, S.Lv⁆ = S.pre W23 ∧ ⁅S.pre W23, S.Lv⁆ = S.pre W23 := by
  have hup : ⁅V, S.Lv⁆ ≤ S.pre W23 := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    obtain ⟨hlN, hρ⟩ := S.rho_Lv hl
    obtain ⟨h, hψ⟩ := S.psi_commutator ⟨u, hu⟩ ⟨l, hlN⟩
    refine S.mem_pre.2 ⟨h, ?_⟩
    rw [hψ, mem_W23]
    rcases hρ with hρ | hρ | hρ <;> rw [hρ]
    · simp
    · exact (comm_mem_W23 _).1
    · exact (comm_mem_W23 _).2
  obtain ⟨l₀, hl₀, hl₀σ⟩ := S.exists_Lv_c234
  have hlow : S.pre W23 ≤ ⁅S.pre W23, S.Lv⁆ := by
    intro y hy
    obtain ⟨hyV, hyW⟩ := S.mem_pre.1 hy
    obtain ⟨w, hwW, hw⟩ : ∃ w : W5, (c0 w = 1 ∧ c01 w = 1) ∧
        S.frame.ψ ⟨y, hyV⟩ = w * (pact (S.frame.ρ l₀) w)⁻¹ := by
      rcases hl₀σ with h | h <;> rw [h]
      · exact (W23_gen _ hyW.1 hyW.2).1
      · exact (W23_gen _ hyW.1 hyW.2).2
    set w' : ↥V := S.frame.ψ.symm w with hw'
    have hψw' : S.frame.ψ ⟨(w' : G), w'.2⟩ = w := by
      rw [Subtype.coe_eta, hw', MulEquiv.apply_symm_apply]
    have hw'W : (w' : G) ∈ S.pre W23 := S.mem_pre.2 ⟨w'.2, by rw [hψw']; exact mem_W23.mpr hwW⟩
    obtain ⟨h, hψ⟩ := S.psi_commutator w' l₀
    have heq : ⁅(w' : G), (l₀ : G)⁆ = y := by
      have : (⟨_, h⟩ : ↥V) = ⟨y, hyV⟩ := by
        apply S.frame.ψ.injective
        rw [hψ, hw, hw', MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val this
    rw [← heq]
    exact Subgroup.commutator_mem_commutator hw'W hl₀
  have hmono : ⁅S.pre W23, S.Lv⁆ ≤ ⁅V, S.Lv⁆ := Subgroup.commutator_mono (S.pre_le_V _) le_rfl
  exact ⟨le_antisymm hup (hlow.trans hmono), le_antisymm (hmono.trans hup) hlow⟩

theorem opResidual_two_Lv : opResidual 2 S.Lv = S.Lv := by
  refine le_antisymm (opResidual_le 2 _) ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hx, m, hm, hxm⟩
  refine mem_opResidual_of_coprime (Subgroup.subset_closure ⟨hx, m, hm, hxm⟩) ?_
  exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm))

theorem oddCoreIn_Gv (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) :
    oddCoreIn (Subgroup.centralizer ({S.v12} : Set G)) = ⊥ := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hHyp := S.lemma115Hyp_Gv h1222 h517
  have hVGv : V ≤ Gv := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨u, hu⟩ ⟨S.v12, S.v12_mem_V⟩))
  have hLvGv : S.Lv ≤ Gv := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact (oTwoUpper_le _).trans inf_le_right
  obtain ⟨hcomm, hcomm2⟩ := S.commutator_V_Lv
  have hWV : S.pre W23 ≤ V := S.pre_le_V _
  have hWel : IsElemAbelian 2 (S.pre W23) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => S.elemAbelian_V.2 x (hWV hx)⟩
    have hc : (a : G) * b = b * a :=
      congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨a, hWV a.2⟩ ⟨b, hWV b.2⟩)
    exact Subtype.ext hc
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p Gv) ≤ 2 := by
    intro p hp hp2
    have hO2 : pCoreOf 2 Gv ≠ ⊥ := hHyp.pCore_ne_bot
    have hsqt : CFSG.IsStronglyQuasithin ↥Gv := (hloc Gv hO2).1
    have h1 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hsqt) p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    rw [pRank_top_subtype] at h1
    exact (CFSG.SectionRank.pRank_mono hp.one_lt (CFSG.LieType.BorelTits.pCoreOf_le p Gv)).trans
      h1
  have hWC : S.pre W23 ≤ Subgroup.centralizer (fusionOddCoreOf Gv : Set G) :=
    a126_one hLvGv S.opResidual_two_Lv (hWV.trans hVGv) (S.isPGroup_V.to_le hWV) hcomm2 hrank
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hWel)
  have hzv : S.z * S.v12⁻¹ ∈ S.pre W23 := by
    refine S.mem_pre.2 ⟨V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V), ?_⟩
    have e : (⟨S.z * S.v12⁻¹, V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V)⟩ : ↥V) =
        ⟨S.z, S.z_mem_V⟩ * (⟨S.v12, S.v12_mem_V⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_z, S.psi_v12]
    exact W4_E12_mem
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyGv : y ∈ Gv := oddCoreIn_le Gv hy
  have hc1 : (S.z * S.v12⁻¹) * y = y * (S.z * S.v12⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (hWC hzv) y hy).symm
  have hc2 : S.v12 * y = y * S.v12 := (Subgroup.mem_centralizer_singleton_iff.mp hyGv).symm
  have hzy : S.z * y = y * S.z := by
    have e1 : S.z = (S.z * S.v12⁻¹) * S.v12 := by group
    rw [e1, mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
  have hinv := hHyp.inverts_oddCoreIn y hy
  have hyy : y = y⁻¹ := by
    rw [← hinv]
    calc y = S.z⁻¹ * (S.z * y) := by group
      _ = S.z⁻¹ * (y * S.z) := by rw [hzy]
      _ = S.z⁻¹ * y * S.z := by group
  have hy2 : y ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hyy]
    exact mul_inv_cancel y
  have hodd : Odd (orderOf y) := by
    have h1 := Subgroup.orderOf_dvd_natCard (oddCoreIn Gv) hy
    exact Odd.of_dvd_nat (odd_card_oddCoreIn Gv) h1
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have h2 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h2)

theorem exists_component_Gv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : ¬ CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    ∃ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) := by
  by_contra hE
  push Not at hE
  exact hF (DoubleA3.charTwo_of_no_component hE (S.oddCoreIn_Gv h1222 h517))

end Setting

@[expose] def Elim1366AB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (Lemma115CaseA K S.z ∨ Lemma115CaseB K S.z) → False

@[expose] def Elim1366CD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (Lemma115CaseC K S.z ∨ Lemma115CaseD K S.z) → False

@[expose] def Elim1366EF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (Lemma115CaseE K S.z ∨ Lemma115CaseF K S.z) → False

theorem lemma1366_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (hlist : Lemma115_3_List) (hAB : Elim1366AB) (hCD : Elim1366CD) (hEF : Elim1366EF) :
    Lemma1366 := by
  intro G _ _ T L V S hab
  by_contra hF
  have : IsSimpleGroup G := S.h13.simple
  obtain ⟨K, hK⟩ := S.exists_component_Gv h1222 h517 hF
  have hcases := hlist G S.h13.simple S.h13.nonabelian (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke)
    _ _ _ _ (S.lemma115Hyp_Gv h1222 h517) K hK
  rcases hcases with h | h | h | h | h | h
  · exact hAB G T L V S hab K hK (Or.inl h)
  · exact hAB G T L V S hab K hK (Or.inr h)
  · exact hCD G T L V S hab K hK (Or.inl h)
  · exact hCD G T L V S hab K hK (Or.inr h)
  · exact hEF G T L V S hab K hK (Or.inl h)
  · exact hEF G T L V S hab K hK (Or.inr h)

end CFSG.Quasithin.H13.A5
