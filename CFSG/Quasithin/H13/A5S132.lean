module

public import CFSG.Quasithin.H13.A5Producer
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs
public import CFSG.Quasithin.H13.A5F91

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

section Group

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centralizer' (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
    have := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * x := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ H
    have : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    rw [this]
    exact hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem isSylowTwoOf_map_conj {S H : Subgroup G} (h : IsSylowTwoOf S H) (g : G) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  have := Subgroup.relIndex_map_map_of_injective S H
    (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _)
  show ¬ 2 ∣ (S.map _).relIndex (H.map _)
  rw [this]
  exact h.2.2

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.mp hg x).mp hx, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

variable [Finite G]

theorem exists_mem_normalizer_not_mem {R P : Subgroup G} (hP : IsPGroup 2 P) (hRP : R < P) :
    ∃ x ∈ P, x ∉ R ∧ x ∈ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : R.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hRP.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ R.subgroupOf P := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyR⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt)
  refine ⟨y, y.2, fun h => hyR (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (R : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hRP.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem exists_mem_normalizer_of_isSylowTwoOf {R C : Subgroup G} (hR : IsSylowTwoOf R C) {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) :
    ∃ c ∈ C, c⁻¹ * g ∈ Subgroup.normalizer (R : Set G) := by
  have h' := isSylowTwoOf_map_conj hR g
  rw [map_conj_eq_of_mem_normalizer hg] at h'
  obtain ⟨c, hc, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hR h'
  refine ⟨c, hc, A4.mem_normalizer_of_conj_mem fun r hr => ?_⟩
  have hr' : g * r * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
  have := (hconj _).mp hr'
  have e : c⁻¹ * g * r * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * r * g⁻¹) * c := by group
  rw [e]
  exact this

theorem exists_isHStar_le' {T M X : Subgroup G} (hX : InH T X) (hXM : ¬ X ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ X := by
  obtain ⟨H, ⟨hHH, hHM, hHX⟩, hmin⟩ :=
    (Set.toFinite {Y : Subgroup G | InH T Y ∧ ¬ Y ≤ M ∧ Y ≤ X}).exists_minimal
      ⟨X, hX, hXM, le_rfl⟩
  exact ⟨H, ⟨hHH, hHM, fun Y hY hYH hYM =>
    le_antisymm hYH (hmin ⟨hY, hYM, hYH.trans hHX⟩ hYH)⟩, hHX⟩

end Group

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem not_alt12_2_2 : ¬ Alt12_2_2 G := by
  intro h
  apply S.h13.not_excluded
  rcases h with ⟨t, n, f, hf, -, hadm, hLie⟩ | hU | hM | hM | hM
  · exact Or.inl ⟨t, n, f, hf, hadm, hLie⟩
  · exact Or.inl ⟨.PSU, 5, 2, le_rfl, ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, hU⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl hM)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hM))))))

theorem conjugate_eq_or_inf_eq_bot (h1222 : Stmt12_2_2) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥ := by
  rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
  · exact absurd h S.not_alt12_2_2
  · exact ((h L S.maximal S.h13.faithful S.fsu.quasisimple).2.2 V S.irr).2.1 m hm

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have := S.card_V
  rw [h, Subgroup.card_bot] at this
  norm_num at this

theorem V3_ne_bot : S.V3 ≠ ⊥ := by
  intro h
  have := S.card_V3
  rw [h, Subgroup.card_bot] at this
  norm_num at this

theorem mem_normalizer_V_of (h1222 : Stmt12_2_2) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hmU : m ∈ Subgroup.normalizer (U : Set G)) : m ∈ Subgroup.normalizer (V : Set G) := by
  rcases S.conjugate_eq_or_inf_eq_bot h1222 hm with h | h
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff', h]
  · exfalso
    apply hU
    rw [eq_bot_iff, ← h]
    intro u hu
    exact ⟨hUV hu, mem_conjugate_iff'.mpr (hUV ((Subgroup.mem_normalizer_iff.mp hmU u).mp hu))⟩

theorem R_ne_bot : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h =>
  S.V_ne_bot (le_bot_iff.mp (h ▸ S.V_le_pCoreOf_LT))

theorem cLT_V3 : (L ⊔ T) ⊓ Subgroup.centralizer (S.V3 : Set G) = pCoreOf 2 (L ⊔ T) := by
  rw [← S.cLT]
  apply le_antisymm
  · rintro x ⟨hx, hxC⟩
    exact ⟨hx, S.mem_centralizer_V_of_V3 (S.reduced.2.1 hx) hxC⟩
  · exact inf_le_inf_left _ (Subgroup.centralizer_le S.V3_le_V)

theorem R_le_CV3 : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (S.V3 : Set G) :=
  S.cLT_V3 ▸ inf_le_right

theorem M_inf_centralizer_V3_le (h1222 : Stmt12_2_2) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (S.V3 : Set G) ≤
      Subgroup.centralizer (V : Set G) := by
  rintro m ⟨hm, hmC⟩
  have hmN := S.mem_normalizer_V_of h1222 hm S.V3_ne_bot S.V3_le_V
    (Subgroup.centralizer_le_normalizer _ hmC)
  exact S.mem_centralizer_V_of_V3 hmN hmC

theorem R_sylow_CV : IsSylowTwoOf (pCoreOf 2 (L ⊔ T)) (Subgroup.centralizer (V : Set G)) := by
  rw [← S.cT]
  exact A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_le S.h13.sylow S.frame.T_le)
    (Subgroup.centralizer_le_normalizer _) (normalizer_le_normalizer_centralizer' V)

theorem normalizer_R_le :
    Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨_, S.R_ne_bot, pCoreOf_isPGroup 2 _, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)))
  have h := S.uniqueM.2 M' ⟨hM', (le_normalizer_pCoreOf 2 _).trans hM'le⟩
  exact h ▸ hM'le

theorem R_sylow_CV3 (h1222 : Stmt12_2_2) :
    IsSylowTwoOf (pCoreOf 2 (L ⊔ T)) (Subgroup.centralizer (S.V3 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨S.R_le_CV3, pCoreOf_isPGroup 2 _, fun P hPC hP hRP => ?_⟩
  by_contra hPR
  obtain ⟨x, hxP, hxR, hxN⟩ := exists_mem_normalizer_not_mem hP
    (lt_of_le_of_ne hRP fun h => hPR h.ge)
  have hxCV : x ∈ Subgroup.centralizer (V : Set G) :=
    S.M_inf_centralizer_V3_le h1222 ⟨S.normalizer_R_le hxN, hPC hxP⟩
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp S.R_sylow_CV).2.2
  have hle : pCoreOf 2 (L ⊔ T) ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set G) :=
    sup_le S.R_sylow_CV.1 (Subgroup.zpowers_le.mpr hxCV)
  have h2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T) ⊔ Subgroup.zpowers x) :=
    hP.to_le (sup_le hRP (Subgroup.zpowers_le.mpr hxP))
  exact hxR (hmax _ hle h2 le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

theorem centralizer_V3_le (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2) :
    Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hCM
  have hTC : T ≤ Subgroup.normalizer (Subgroup.centralizer (S.V3 : Set G) : Set G) :=
    S.T_le_NV3.trans (normalizer_le_normalizer_centralizer' _)
  have hV3X : S.V3 ≤ pCoreOf 2 (Subgroup.centralizer (S.V3 : Set G) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((S.V3_le_V.trans S.V_le_T).trans le_sup_right)
      (sup_le (Subgroup.centralizer_le_normalizer _) S.T_le_NV3) (S.isPGroup_V.to_le S.V3_le_V)
  have hX : InH T (Subgroup.centralizer (S.V3 : Set G) ⊔ T) :=
    ⟨le_sup_right, fun h => S.V3_ne_bot (le_bot_iff.mp (h ▸ hV3X))⟩
  obtain ⟨H, hH, hHX⟩ := exists_isHStar_le' (M := Subgroup.normalizer (L : Set G)) hX
    fun h => hCM (le_sup_left.trans h)
  have hO2H : oTwoUpper H ≤ Subgroup.centralizer (S.V3 : Set G) := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    have hx' : x ∈ ((Subgroup.centralizer (S.V3 : Set G) : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T hTC]
      exact hHX hx
    obtain ⟨c, hc, t, ht, rfl⟩ := hx'
    obtain ⟨a, ha⟩ := S.isPGroup_T ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨c', hc', he⟩ := pow_mem_mul_of_normalizes hc (hTC ht) (2 ^ a)
    rw [hta, mul_one] at he
    exact ⟨a, he ▸ hc'⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have hU : IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ S.T_le_NL)
    rwa [hP] at this
  obtain ⟨R0, hR0, hR0R, hN⟩ := h311 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow
    (L ⊔ T) H (pCoreOf 2 (L ⊔ T)) ⟨le_sup_right, S.R_ne_bot⟩ hH.1 ⟨_, hU⟩ S.R_ne_bot
    S.pCoreOf_LT_le_T
    (A4.isSylowTwoOf_mono (S.R_sylow_CV3 h1222) le_sup_right (sup_le hO2H S.R_le_CV3))
    (le_normalizer_pCoreOf 2 _)
  have hR02 : IsPGroup 2 R0 := (pCoreOf_isPGroup 2 _).to_le hR0R
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨R0, hR0, hR02, rfl⟩ : IsTwoLocal (Subgroup.normalizer (R0 : Set G)))
  have hM'M := S.uniqueM.2 M' ⟨hM', (le_sup_left.trans hN).trans hM'le⟩
  exact hH.2.1 ((le_sup_right.trans hN).trans (hM'M ▸ hM'le))

theorem normalizer_V3_le (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2) :
    Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  obtain ⟨c, hc, hcg⟩ := exists_mem_normalizer_of_isSylowTwoOf (S.R_sylow_CV3 h1222)
    (normalizer_le_normalizer_centralizer' _ hg)
  have hgM : g ∈ Subgroup.normalizer (L : Set G) := by
    have := (Subgroup.normalizer (L : Set G)).mul_mem (S.centralizer_V3_le h311 h1222 hc)
      (S.normalizer_R_le hcg)
    simpa using this
  exact S.mem_normalizer_V_of h1222 hgM S.V3_ne_bot S.V3_le_V hg

end Setting

theorem input1323Two_of (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2) : Input1323Two :=
  fun _ _ _ _ _ _ S => S.normalizer_V3_le h311 h1222

end CFSG.Quasithin.H13.A5
