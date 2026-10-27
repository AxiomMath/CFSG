module

public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecAVi2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

theorem index_eq_of_realizesVia {W : Type*} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)}
    {Z : Subgroup W} {π : D.Gam →* ↥H} (hπ : D.RealizesVia H ⊤ Z π) :
    Z.index = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hker : β.ker = Z.subgroupOf ⊤ := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have e := QuotientGroup.quotientKerEquivOfSurjective β hβs
  rw [← Nat.card_congr e.toEquiv, hker, ← Subgroup.index_eq_card, ← Subgroup.relIndex,
    Subgroup.relIndex_top_right]

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem relIndex_fsuV_of_SL3 (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : KindSL3 L (fsuV T I) n) :
    (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex (fsuV T I) = 2 ^ (3 * n) := by
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
  rcases hc with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
  · rw [Subgroup.relIndex, inf_centralizer_subgroupOf, index_eq_of_realizesVia hπ]
    change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤) = _
    rw [Subgroup.bot_subgroupOf, ← Subgroup.index_eq_card, Subgroup.index_bot,
      Subgroup.card_top]
    change Nat.card (Fin 3 → K) = _
    rw [Nat.card_fun, Nat.card_fin, hK, ← pow_mul, mul_comm]
  · exact (kind_not_SL3_Sp4 (by have := h.one_lt; omega) hk ⟨K, inferInstance, inferInstance,
      hK, he⟩).elim
  · exact (kind_not_SL3_G2 hG2 h.one_lt hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem IsVi.eq_fsuV_of_SL3 (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : KindSL3 L (fsuV T I) n) {U : Subgroup G}
    (hU : IsVi T L I n 3 U) : U = fsuV T I := by
  have h1 := relIndex_fsuV_of_SL3 hG2 h1102 h hk
  have h2 := IsVi.relIndex_eq hU
  have hle := IsVi.le_fsuV hU
  have hCU := IsVi.cV_le hU
  have h3 := Subgroup.relIndex_mul_relIndex _ _ _ hCU hle
  rw [h1, h2, mul_comm n 3] at h3
  have h4 : U.relIndex (fsuV T I) = 1 := by
    have hpos : 0 < 2 ^ (3 * n) := by positivity
    nlinarith
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h4)

omit [Finite G] in
theorem mem_normalizer_of_isTISetIn {V U M : Subgroup G} (hTI : IsTISetIn V M) (hU : U ≤ V)
    (hU1 : U ≠ ⊥) {m : G} (hm : m ∈ M) (hmU : m ∈ Subgroup.normalizer (U : Set G)) :
    m ∈ Subgroup.normalizer (V : Set G) := by
  by_contra hmV
  apply hU1
  rw [eq_bot_iff, ← hTI.2 m hm hmV]
  intro u hu
  refine Subgroup.mem_inf.mpr ⟨hU hu, ?_⟩
  rw [mem_conjSubgroup_iff]
  exact hU ((Subgroup.mem_normalizer_iff.mp hmU u).mp hu)

omit [Finite G] in
theorem conjV_mem_stabW_centralizer {L V : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) (hmV : m ∈ Subgroup.normalizer (V : Set G)) :
    conjV V m hmV ∈ stabW ((Subgroup.centralizer (L : Set G)).subgroupOf V) := by
  intro z
  simp only [Subgroup.mem_subgroupOf, conjV_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hm) z)

omit [Finite G] in
theorem conjV_normalizes_autOn {L V : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) (hmV : m ∈ Subgroup.normalizer (V : Set G)) :
    ∀ g ∈ autOn L V, conjV V m hmV * g * (conjV V m hmV)⁻¹ ∈ autOn L V := by
  intro g hg
  obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
  rw [conjV_conj]
  exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hm x).mp hx) _

theorem normalizer_V₃_eq (hF : NatFacts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n) {U₁ U₃ : Subgroup G}
    (hU₁ : IsVi T L I n 1 U₁) (hU₃ : IsVi T L I n 3 U₃) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (U₃ : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (U₁ : Set G) := by
  have hTI : IsTISetIn (fsuV T I) (Subgroup.normalizer (L : Set G)) :=
    (h1103 G T L I n h).2.2.2.1
  have key : ∀ m ∈ Subgroup.normalizer (L : Set G),
      ∀ hmV : m ∈ Subgroup.normalizer (fsuV T I : Set G),
      (m ∈ Subgroup.normalizer (U₁ : Set G) ↔ m ∈ Subgroup.normalizer (U₃ : Set G)) := by
    intro m hm hmV
    have hτZ := conjV_mem_stabW_centralizer hm hmV
    have hτH := conjV_normalizes_autOn hm hmV
    have hflag1 := isFlagW_of_isVi h hU₁
    have hflag3 := isFlagW_of_isVi h hU₃
    have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
      Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
    rw [← conjV_mem_stabW_iff (IsVi.le_fsuV hU₁) hmV,
      ← conjV_mem_stabW_iff (IsVi.le_fsuV hU₃) hmV]
    obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
    rcases hc with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
    · exact (hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim
    · exact hF.n13Sp4 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ _ hflag1 hflag3 _
        hτZ hτH
    · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
      exact hF.n13G2 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ _ hflag1 hflag3 _
        hτZ hτH
  ext m
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hm, hm3⟩
    have hmV := mem_normalizer_of_isTISetIn hTI (IsVi.le_fsuV hU₃)
      (IsVi.ne_bot h hU₃ (by norm_num)) hm hm3
    exact ⟨hm, (key m hm hmV).mpr hm3⟩
  · rintro ⟨hm, hm1⟩
    have hmV := mem_normalizer_of_isTISetIn hTI (IsVi.le_fsuV hU₁) (IsVi.ne_bot h hU₁ le_rfl)
      hm hm1
    exact ⟨hm, (key m hm hmV).mp hm1⟩

theorem stmt11_1_0_of (hF : NatFacts) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) : Stmt11_1_0 := by
  intro G _ _ T L I n h
  exact ⟨fun i hi1 hi3 => isVi_existsUnique hF h1102 h hi1 hi3,
    fun i hi U hU => lOf_quot_SL2 hF h1102 h hi hU, fun U₁ U₃ hU₁ hU₃ =>
      ⟨fun hk => IsVi.eq_fsuV_of_SL3 hG2 h1102 h hk hU₃,
        fun hk => normalizer_V₃_eq hF h1102 h1103 h hk hU₁ hU₃⟩⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
