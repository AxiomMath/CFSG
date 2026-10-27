module

public import CFSG.Quasithin.Vol2.Ch3Sec3Par32S6
public import CFSG.Quasithin.Vol2.Ch3Sec3Mod32
public import CFSG.GH74.M12.HypGroup
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

namespace Par32

variable {G : Type} [Group G]

theorem four_dvd_relIndex [Finite G] {X A B : Subgroup G} (hc : IsTwoChiefFactor X A B)
    (hn : ¬ ⁅A, X⁆ ≤ B) : 4 ∣ B.relIndex A := by
  obtain ⟨hBA, hAX, hXA, hXB, -, h2⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBn : (B.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hAX.trans hXB)
  have hp : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨k, hk⟩ := h2 a a.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hrel : B.relIndex A = 2 ^ m := hm
  rcases m with _ | _ | m
  · rw [pow_zero, Subgroup.relIndex_eq_one] at hrel
    exact absurd hrel (not_le_of_gt hBA)
  · exfalso
    apply hn
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hidx : (B.subgroupOf A).index = 2 := hrel
    have hxa : x * a⁻¹ * x⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hXA hx) a⁻¹).mp (A.inv_mem ha)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩)
      (b := ⟨_, hxa⟩)).mpr (by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        show a ∈ B ↔ x * a⁻¹ * x⁻¹ ∈ B
        rw [← (Subgroup.mem_normalizer_iff.mp (hXB hx) a⁻¹), inv_mem_iff])
    rw [Subgroup.mem_subgroupOf] at key
    have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact key
  · rw [hrel]
    exact ⟨2 ^ m, by ring⟩

theorem four_pow_dvd_card [Finite G] {X : Subgroup G} {k : ℕ} (h : HasNoncentralTwoChief X k) :
    4 ^ k ∣ Nat.card X := by
  obtain ⟨A, B, hAB, hle⟩ := h
  rcases k with _ | k
  · simp
  have hcard : ∀ i : Fin (k + 1), Nat.card (A i) = (B i).relIndex (A i) * Nat.card (B i) := by
    intro i
    have := Subgroup.relIndex_mul_card (H := B i) (K := A i)
    rw [inf_of_le_left (hAB i).1.1.le] at this
    exact this.symm
  have key : ∀ i (hi : i < k + 1), 4 ^ (i + 1) ∣ Nat.card (A ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [hcard, zero_add, pow_one]
      exact Dvd.dvd.mul_right (four_dvd_relIndex (hAB _).1 (hAB _).2) _
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 : Nat.card (A ⟨i, by omega⟩) ∣ Nat.card (B ⟨i + 1, hi⟩) :=
        Subgroup.card_dvd_of_le (hle _ _ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i)))
      rw [hcard, pow_succ, mul_comm (4 ^ (i + 1)) 4]
      exact Nat.mul_dvd_mul (four_dvd_relIndex (hAB _).1 (hAB _).2) (h1.trans h2)
  exact (key k (Nat.lt_succ_self k)).trans (Subgroup.card_dvd_of_le (hAB _).1.2.1)

theorem not_hasNoncentralTwoChief [Finite G] {T : Subgroup G} (hT : ¬ 2 ∣ T.index) {k : ℕ}
    (hk : Nat.card T < 4 ^ k) (X : Subgroup G) : ¬ HasNoncentralTwoChief X k := by
  intro h
  have h1 := (four_pow_dvd_card h).trans (Subgroup.card_subgroup_dvd_card X)
  rw [← Subgroup.card_mul_index T] at h1
  have hcop : Nat.Coprime (4 ^ k) T.index := by
    have h2 : Nat.Coprime 2 T.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hT
    have h4 : Nat.Coprime 4 T.index := by
      have := Nat.Coprime.pow_left 2 h2
      norm_num at this
      exact this
    exact Nat.Coprime.pow_left k h4
  exact absurd (Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right h1)) (not_le.mpr hk)

omit [Group G] in
theorem nonempty_quot_pCore_congr {G : Type} [Group G] {K₁ K₂ : Subgroup G} (h : K₁ = K₂)
    {Q : Type} [Group Q] (e : Nonempty (↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* Q)) :
    Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Q) := by
  subst h
  exact e

section Pre

variable {Γ : Type} [Group Γ] {T L : Subgroup G} (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ)
  (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))

@[expose] def pre (Q : Subgroup Γ) : Subgroup G :=
  (Q.comap (ρ.comp (Subgroup.inclusion hLTN))).map (L ⊔ T).subtype

theorem mem_pre {Q : Subgroup Γ} {g : G} :
    g ∈ pre ρ hLTN Q ↔ ∃ hg : g ∈ L ⊔ T, ρ ⟨g, hLTN hg⟩ ∈ Q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hQ⟩
    exact ⟨⟨g, hg⟩, hQ, rfl⟩

theorem pre_le_sup (Q : Subgroup Γ) : pre ρ hLTN Q ≤ L ⊔ T :=
  fun _ hg => ((mem_pre ρ hLTN).mp hg).1

theorem pre_mono {Q₁ Q₂ : Subgroup Γ} (h : Q₁ ≤ Q₂) :
    pre ρ hLTN Q₁ ≤ pre ρ hLTN Q₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem pre_inf (Q₁ Q₂ : Subgroup Γ) :
    pre ρ hLTN (Q₁ ⊓ Q₂) = pre ρ hLTN Q₁ ⊓ pre ρ hLTN Q₂ := by
  ext g
  rw [Subgroup.mem_inf, mem_pre, mem_pre, mem_pre]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, hg, h2⟩
  · rintro ⟨⟨hg, h1⟩, hg', h2⟩
    exact ⟨hg, h1, h2⟩

theorem pre_le_normalizer {Q₁ Q₂ : Subgroup Γ}
    (h : Q₁ ≤ Subgroup.normalizer (Q₂ : Set Γ)) :
    pre ρ hLTN Q₁ ≤ Subgroup.normalizer (pre ρ hLTN Q₂ : Set G) := by
  intro g hg
  obtain ⟨hgLT, hgQ⟩ := (mem_pre ρ hLTN).mp hg
  have hn := Subgroup.mem_normalizer_iff.mp (h hgQ)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_pre, mem_pre]
  constructor
  · rintro ⟨hx, hxQ⟩
    have hm : g * x * g⁻¹ ∈ L ⊔ T :=
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem hgLT hx) ((L ⊔ T).inv_mem hgLT)
    refine ⟨hm, ?_⟩
    have e : (⟨g * x * g⁻¹, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hLTN hgLT⟩ * ⟨x, hLTN hx⟩ * (⟨g, hLTN hgLT⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (hn _).mp hxQ
  · rintro ⟨hm, hmQ⟩
    have hx : x ∈ L ⊔ T := by
      have h1 := (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem hgLT) hm) hgLT
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h1
    refine ⟨hx, ?_⟩
    have e : (⟨g * x * g⁻¹, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hLTN hgLT⟩ * ⟨x, hLTN hx⟩ * (⟨g, hLTN hgLT⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_inv] at hmQ
    exact (hn _).mpr hmQ

theorem pre_isPGroup [Finite G] {Q : Subgroup Γ} (hQ : ∀ x ∈ Q, x * x = 1)
    (hK : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 → g ∈ qL L T) :
    IsPGroup 2 ↥(pre ρ hLTN Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  rintro ⟨g, hg⟩
  obtain ⟨hgLT, hgQ⟩ := (mem_pre ρ hLTN).mp hg
  have hgg : g * g ∈ L ⊔ T := (L ⊔ T).mul_mem hgLT hgLT
  have hsq : g * g ∈ qL L T := by
    apply hK (g * g) hgg
    have e : (⟨g * g, hLTN hgg⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨g, hLTN hgLT⟩ * ⟨g, hLTN hgLT⟩ := rfl
    rw [e, map_mul]
    exact hQ _ hgQ
  obtain ⟨k, hk⟩ := hQ2 ⟨g * g, hsq⟩
  have hk' : (g * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ, pow_mul', sq]
  exact hk'

theorem card_pre [Finite G] (Q : Subgroup Γ) :
    Nat.card ↥(pre ρ hLTN Q) =
      Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ Q) *
        Nat.card ↥(ρ.comp (Subgroup.inclusion hLTN)).ker := by
  set f := ρ.comp (Subgroup.inclusion hLTN) with hf
  have h1 : Nat.card ↥(pre ρ hLTN Q) = Nat.card ↥(Q.comap f) :=
    Subgroup.card_map_of_injective (L ⊔ T).subtype_injective
  set K := Q.comap f with hK
  let g : ↥K →* Γ := f.comp K.subtype
  have hrange : g.range = f.range ⊓ Q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
  have hkerK : f.ker ≤ K := fun x hx => by
    show f x ∈ Q
    rw [MonoidHom.mem_ker.mp hx]
    exact Q.one_mem
  have hker : g.ker = f.ker.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerK).toEquiv] at h2
  rw [h1, h2]

end Pre

theorem parabolic_gen [Finite G] {Γ : Type} [Group Γ] [Finite Γ] {T L : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ)
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index)
    (hK : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 → g ∈ qL L T)
    {p r : Subgroup Γ}
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ ∈ p) (hrp : r ≤ p)
    (hpr : p ≤ Subgroup.normalizer (r : Set Γ)) (hr2 : ∀ x ∈ r, x * x = 1)
    (h6 : Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ p) =
      6 * Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ r))
    {ℓa ℓb : G} (hℓa : ℓa ∈ L) (hℓb : ℓb ∈ L)
    (hap : ρ ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩ ∈ p)
    (hbp : ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩ ∈ p)
    (hab : (ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩ * ρ ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩)⁻¹ *
      (ρ ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩ * ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩) ∉ r) :
    oTwoUpper (oTwoUpper (pre ρ hLTN p)) = oTwoUpper (pre ρ hLTN p) ∧
      T ≤ Subgroup.normalizer (oTwoUpper (pre ρ hLTN p) : Set G) ∧
      oTwoUpper (pre ρ hLTN p) ⊔ T = pre ρ hLTN p ∧
      Nonempty (↥(pre ρ hLTN p) ⧸ CFSG.pCore 2 ↥(pre ρ hLTN p) ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 (pre ρ hLTN p) = pre ρ hLTN r ∧ pre ρ hLTN r ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pre ρ hLTN p with hPdef
  set R := pre ρ hLTN r with hRdef
  have hTP : T ≤ P := fun t ht =>
    (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_right ht, hρT t ht⟩
  have hRP : R ≤ P := pre_mono ρ hLTN hrp
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := pre_le_normalizer ρ hLTN hpr
  have hR2 : IsPGroup 2 ↥R := pre_isPGroup ρ hLTN hr2 hK
  have hTsyl : IsSylowTwoOf T P :=
    ⟨hTP, hT2, fun h2 => hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le hTP))⟩
  have hRT : R ≤ T := hTsyl.le_of_normalizes hRP hPN hR2
  have h6' : Nat.card ↥P = 6 * Nat.card ↥R := by
    rw [card_pre ρ hLTN p, card_pre ρ hLTN r, h6]
    ring
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  have hrel : R.relIndex P = 6 := by
    have := Subgroup.relIndex_mul_card (H := R) (K := P)
    rw [inf_of_le_left hRP, h6'] at this
    exact Nat.eq_of_mul_eq_mul_right hRpos (by rw [this])
  have hNn : (R.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hQ6 : Nat.card (↥P ⧸ R.subgroupOf P) = 6 := hrel
  have hℓaP : ℓa ∈ P := (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓa, hap⟩
  have hℓbP : ℓb ∈ P := (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓb, hbp⟩
  have hne : (QuotientGroup.mk ⟨ℓa, hℓaP⟩ : ↥P ⧸ R.subgroupOf P) * QuotientGroup.mk ⟨ℓb, hℓbP⟩ ≠
      QuotientGroup.mk ⟨ℓb, hℓbP⟩ * QuotientGroup.mk ⟨ℓa, hℓaP⟩ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    intro h
    have h1 := QuotientGroup.eq.mp h.symm
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨hm, hmr⟩ := (mem_pre ρ hLTN).mp h1
    apply hab
    have e : (⟨_, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩ * ⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩)⁻¹ *
          (⟨ℓa, hLTN (Subgroup.mem_sup_left hℓa)⟩ *
            ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓb)⟩) := rfl
    rw [e, map_mul, map_inv, map_mul, map_mul] at hmr
    exact hmr
  obtain ⟨ψ⟩ := CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hQ6 _ _ hne
  have hRp : IsPGroup 2 ↥(R.subgroupOf P) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hR2 ⟨x, hx⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hcore : ∀ C : Subgroup ↥P, C.Normal → IsPGroup 2 ↥C → C ≤ R.subgroupOf P := by
    intro C hCn hCp
    have h1 : C.map (QuotientGroup.mk' (R.subgroupOf P)) = ⊥ :=
      CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot ψ _
        (hCn.map _ (QuotientGroup.mk'_surjective _)) (hCp.map _)
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact h1
  have hcore1 : CFSG.pCore 2 ↥P = R.subgroupOf P :=
    le_antisymm (hcore _ CFSG.pCore_normal CFSG.pCore_isPGroup)
      (le_sSup ⟨hNn, hRp⟩)
  have hcore2 : CFSG.Open.pCore 2 ↥P = R.subgroupOf P :=
    le_antisymm (hcore _ (CFSG.LieType.BorelTits.pCore_normal 2)
      (CFSG.LieType.BorelTits.pCore_isPGroup 2)) (CFSG.LieType.BorelTits.le_pCore 2 hNn hRp)
  refine ⟨CFSG.Quasithin.A4.oTwoUpper_oTwoUpper P, hTP.trans (le_normalizer_oTwoUpper P), ?_,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcore1).trans ψ⟩, ?_, hRT⟩
  · rw [sup_comm, ← CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper]
    exact CFSG.Quasithin.sup_twoResidual_eq hTsyl
  · rw [pCoreOf, hcore2]
    exact Subgroup.map_subgroupOf_eq_of_le hRP

theorem parabolic [Finite G] {T L : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index)
    (hK : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 → g ∈ qL L T)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ ∈ sylowS6)
    (hρL : ∀ s ∈ alternatingGroup (Fin 6), ∃ ℓ, ∃ hℓ : ℓ ∈ L,
      ρ ⟨ℓ, hLTN (Subgroup.mem_sup_left hℓ)⟩ = s)
    (hH : (ρ.comp (Subgroup.inclusion hLTN)).range = alternatingGroup (Fin 6) ∨
      (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤)
    {p r : Subgroup (Equiv.Perm (Fin 6))} (hSp : sylowS6 ≤ p) (hrp : r ≤ p)
    (hpr : p ≤ Subgroup.normalizer (r : Set (Equiv.Perm (Fin 6)))) (hr2 : ∀ x ∈ r, x * x = 1)
    (hp48 : Nat.card p = 48) (hr8 : Nat.card r = 8) (hc : c45 ∈ r)
    {a b : Equiv.Perm (Fin 6)} (ha : a ∈ alternatingGroup (Fin 6))
    (hb : b ∈ alternatingGroup (Fin 6)) (hap : a ∈ p) (hbp : b ∈ p)
    (hab : (b * a)⁻¹ * (a * b) ∉ r) :
    oTwoUpper (oTwoUpper (pre ρ hLTN p)) = oTwoUpper (pre ρ hLTN p) ∧
      T ≤ Subgroup.normalizer (oTwoUpper (pre ρ hLTN p) : Set G) ∧
      oTwoUpper (pre ρ hLTN p) ⊔ T = pre ρ hLTN p ∧
      Nonempty (↥(pre ρ hLTN p) ⧸ CFSG.pCore 2 ↥(pre ρ hLTN p) ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 (pre ρ hLTN p) = pre ρ hLTN r ∧ pre ρ hLTN r ≤ T := by
  have hsc : 2 * Nat.card ↥(r ⊓ alternatingGroup (Fin 6)) = 8 := by
    rw [two_mul_card_inf_alternatingGroup hc sign_c45, hr8]
  have hsp : 2 * Nat.card ↥(p ⊓ alternatingGroup (Fin 6)) = 48 := by
    rw [two_mul_card_inf_alternatingGroup (hrp hc) sign_c45, hp48]
  have h6 : Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ p) =
      6 * Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ r) := by
    rcases hH with hA | hT
    · rw [hA, inf_comm, inf_comm (alternatingGroup (Fin 6))]
      omega
    · rw [hT, top_inf_eq, top_inf_eq, hp48, hr8]
  obtain ⟨ℓa, hℓa, hρa⟩ := hρL a ha
  obtain ⟨ℓb, hℓb, hρb⟩ := hρL b hb
  refine parabolic_gen ρ hLTN hT2 hTidx hK (fun t ht => hSp (hρT t ht)) hrp hpr hr2 h6 hℓa hℓb
    (hρa ▸ hap) (hρb ▸ hbp) ?_
  rw [hρa, hρb]
  exact hab

theorem exists_rho [Finite G] {T L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 6)} (hA : IsAltBlockTypeWith L 6 α)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T) :
    ∃ (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
      (β : ↥(blockU L) →* Multiplicative (AltHeart 6)),
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = g * u * g⁻¹ →
          Multiplicative.toAdd (β u') = heartAct 6 (ρ g) (Multiplicative.toAdd (β u))) ∧
      (∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sylowS6) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ alternatingGroup (Fin 6)) ∧
      (∀ s ∈ alternatingGroup (Fin 6), ∃ ℓ, ∃ hℓ : ℓ ∈ L,
        ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = s) ∧
      (∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
        g ∈ qL L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := id hA
  set ρ₀ := A6Trans.rho hA with hρ₀
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 6),
      ∀ t (ht : t ∈ T), σ * ρ₀ ⟨t, hTL ht⟩ * σ⁻¹ ∈ sylowS6 := by
    let f : ↥T →* Equiv.Perm (Fin 6) := ρ₀.comp (Subgroup.inclusion hTL)
    have hf : IsPGroup 2 ↥f.range := hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hSp : IsPGroup 2 ↥sylowS6 := IsPGroup.of_card (n := 4) (by rw [S6Syl.card_sylowS6]; rfl)
    have hSidx : ¬ 2 ∣ sylowS6.index := by
      have := Subgroup.card_mul_index sylowS6
      rw [S6Syl.card_sylowS6, h720] at this
      omega
    let P : Sylow 2 (Equiv.Perm (Fin 6)) := hSp.toSylow hSidx
    obtain ⟨Q, hQ⟩ := hf.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) Q P
    refine ⟨g, fun t ht => ?_⟩
    have h1 : f ⟨t, ht⟩ ∈ (Q : Subgroup (Equiv.Perm (Fin 6))) := hQ ⟨⟨t, ht⟩, rfl⟩
    have h2 : g * f ⟨t, ht⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 _) : Subgroup (Equiv.Perm (Fin 6))) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨_, h1, rfl⟩
    rw [hg] at h2
    exact h2
  let β' : ↥(blockU L) →* Multiplicative (AltHeart 6) :=
    (AddMonoidHom.toMultiplicative (heartAct 6 σ)).comp β
  have hβ' : ∀ u, Multiplicative.toAdd (β' u) = heartAct 6 σ (Multiplicative.toAdd (β u)) :=
    fun _ => rfl
  refine ⟨(MulAut.conj σ).toMonoidHom.comp ρ₀, β', ?_, ?_, ?_, hσ, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (heartAct 6 σ⁻¹ (Multiplicative.toAdd y)))
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hβ', hu]
    show heartAct 6 σ (heartAct 6 σ⁻¹ (Multiplicative.toAdd y)) = Multiplicative.toAdd y
    rw [← heartAct_mul, mul_inv_cancel, heartAct_one]
  · ext u
    rw [MonoidHom.mem_ker, ← hβk, MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : heartAct 6 σ (Multiplicative.toAdd (β u)) = 0 := by
        rw [← hβ', h1]
        rfl
      have h3 := congrArg (heartAct 6 σ⁻¹) h2
      rw [← heartAct_mul, inv_mul_cancel, heartAct_one, map_zero] at h3
      exact Multiplicative.toAdd.injective h3
    · intro h1
      apply Multiplicative.toAdd.injective
      rw [hβ', h1]
      exact map_zero (heartAct 6 σ)
  · intro g u u' h
    have e := A6Trans.rho_heart hA hβs hβk hβe g u u' h
    rw [hβ', hβ', e]
    show heartAct 6 σ (heartAct 6 (ρ₀ g) (Multiplicative.toAdd (β u))) =
      heartAct 6 (σ * ρ₀ g * σ⁻¹) (heartAct 6 σ (Multiplicative.toAdd (β u)))
    rw [← heartAct_mul, ← heartAct_mul, mul_assoc (σ * ρ₀ g), inv_mul_cancel, mul_one]
  · intro ℓ hℓ
    have e : ρ₀ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = (α ⟨ℓ, hℓ⟩ : Equiv.Perm (Fin 6)) :=
      A6Trans.rho_of_mem hA ⟨ℓ, hℓ⟩
    show σ * ρ₀ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ * σ⁻¹ ∈ alternatingGroup (Fin 6)
    rw [e]
    exact (alternatingGroup.normal (α := Fin 6)).conj_mem _ (α ⟨ℓ, hℓ⟩).2 σ
  · intro s hs
    have hs' : σ⁻¹ * s * σ ∈ alternatingGroup (Fin 6) := by
      have := (alternatingGroup.normal (α := Fin 6)).conj_mem s hs σ⁻¹
      simpa using this
    obtain ⟨ℓ, hℓ⟩ := hA.1 ⟨_, hs'⟩
    refine ⟨ℓ, ℓ.2, ?_⟩
    have e := A6Trans.rho_of_mem hA ℓ
    rw [hℓ] at e
    show σ * ρ₀ ⟨(ℓ : G), Subgroup.le_normalizer ℓ.2⟩ * σ⁻¹ = s
    rw [e]
    group
  · intro g hg hgN h1
    apply Mod32.mem_qL_of_rho hA hTL hT2 hg hgN
    have h1' : σ * ρ₀ ⟨g, hgN⟩ * σ⁻¹ = 1 := h1
    calc ρ₀ ⟨g, hgN⟩ = σ⁻¹ * (σ * ρ₀ ⟨g, hgN⟩ * σ⁻¹) * σ := by group
      _ = 1 := by rw [h1']; group

end Par32

open Par32

theorem insp3_3_32Par_holds
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    Insp3_3_32Par := by
  intro G _ _ T M L D h hA6 hTL hTC hQ5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, α, hA⟩ := id hA6
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hUQ : blockU L ≤ qL L T := (C1.blockU_le_blockQ hshort).trans hOQ
  have hZ : blockZ L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ tC L T := ⟨hQT (hUQ hz.1), hz.2⟩
    rw [hTC] at hz'
    exact hz'
  have hU16 := A6Block.card_blockU_of_blockZ_eq_bot hA6 hZ
  have hQe : IsElemAbelian 2 (qL L T) := by
    have hΦ := h.frattini_qL_le_tC h38 h39 hshort hTL
    rw [hTC] at hΦ
    refine Lem3328.isElemAbelian_of_frattini_eq_bot
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
    rw [eq_bot_iff]
    intro x hx
    have := hΦ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hrel := h.relIndex_qL_le_two h38 h39 hA6 hTL
  rw [hTC, sup_bot_eq] at hrel
  have hcardQ : Nat.card ↥(qL L T) = (blockU L).relIndex (qL L T) * 16 := by
    have h2 := Subgroup.relIndex_mul_card (H := blockU L) (K := qL L T)
    rw [inf_of_le_left hUQ, hU16] at h2
    exact h2.symm
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hshort hTL
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  obtain ⟨ρ, β', hβs', hβk', hβe', hρT', -, hρL', hK'⟩ := exists_rho hA hTL hT2
  have hK : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 → g ∈ qL L T :=
    fun g hg h1 => hK' g hg (hLTN hg) h1
  have hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ ∈ sylowS6 :=
    fun t ht => hρT' t ht
  have hρL : ∀ s ∈ alternatingGroup (Fin 6), ∃ ℓ, ∃ hℓ : ℓ ∈ L,
      ρ ⟨ℓ, hLTN (Subgroup.mem_sup_left hℓ)⟩ = s := hρL'
  have hβinj := Mod32.beta_injective hβk' hZ
  have hcent : ∀ g (hgN : g ∈ Subgroup.normalizer (L : Set G)),
      (∀ u ∈ blockU L, g * u * g⁻¹ = u) → ρ ⟨g, hgN⟩ = 1 := by
    intro g hgN hu
    apply A6Coc.eq_of_heartAct_eq
    intro y
    rw [heartAct_one]
    obtain ⟨u, hu'⟩ := hβs' (Multiplicative.ofAdd y)
    have hy : y = Multiplicative.toAdd (β' u) := by rw [hu']; rfl
    rw [hy]
    exact (hβe' ⟨g, hgN⟩ u u (hu u u.2).symm).symm
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  set f := ρ.comp (Subgroup.inclusion hLTN) with hfdef
  have hAH : alternatingGroup (Fin 6) ≤ f.range := fun s hs => by
    obtain ⟨ℓ, hℓ, e⟩ := hρL s hs
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have hH := eq_alternatingGroup_or_eq_top hAH
  have hT9 : Nat.card T ≤ 2 ^ 9 := by
    let fT : ↥T →* Equiv.Perm (Fin 6) := ρ.comp (Subgroup.inclusion (le_sup_right.trans hLTN))
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup fT.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange fT).toEquiv] at h1
    have h2 : Nat.card fT.range ≤ 16 := by
      rw [← S6Syl.card_sylowS6]
      apply Subgroup.card_le_of_le
      rintro _ ⟨⟨t, ht⟩, rfl⟩
      exact hρT t ht
    have h3 : Nat.card fT.ker ≤ 2 ^ 5 := by
      refine le_trans ?_ hQ5
      refine Nat.card_le_card_of_injective (fun x : ↥fT.ker =>
        (⟨((x : ↥T) : G), hK _ (Subgroup.mem_sup_right (x : ↥T).2) (MonoidHom.mem_ker.mp x.2)⟩ :
          ↥(qL L T))) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    calc Nat.card T = _ := h1
      _ ≤ 16 * 2 ^ 5 := Nat.mul_le_mul h2 h3
      _ = 2 ^ 9 := by norm_num
  have h1024 : Nat.card T < 4 ^ 5 := by
    have : (2 : ℕ) ^ 9 < 4 ^ 5 := by norm_num
    omega
  obtain ⟨hX₁, hTX₁, hXT₁, ⟨e₁⟩, hO₁, hRT₁⟩ := parabolic ρ hLTN hT2 hTidx hK hρT hρL hH
    sylowS6_le_p1 r1_le_p1 p1_le_normalizer (fun x hx => sq_eq_one_of_mem_r1 hx) card_p1 card_r1
    c45_mem_r1 s1_mem_alt t1_mem_alt s1_mem_p1 t1_mem_p1 comm_not_mem_r1
  obtain ⟨hX₂, hTX₂, hXT₂, ⟨e₂⟩, hO₂, hRT₂⟩ := parabolic ρ hLTN hT2 hTidx hK hρT hρL hH
    sylowS6_le_p2 r2_le_p2 p2_le_normalizer (fun x hx => sq_eq_one_of_mem_r2 hx) card_p2 card_r2
    c45_mem_r2 b1_mem_alt w2_mem_alt b1_mem_p2 w2_mem_p2 comm_not_mem_r2
  refine ⟨by omega, oTwoUpper (pre ρ hLTN p1), oTwoUpper (pre ρ hLTN p2),
    ⟨hX₁, hTX₁, nonempty_quot_pCore_congr hXT₁ ⟨e₁⟩, not_hasNoncentralTwoChief hTidx h1024 _⟩,
    ⟨hX₂, hTX₂, nonempty_quot_pCore_congr hXT₂ ⟨e₂⟩, not_hasNoncentralTwoChief hTidx h1024 _⟩, ?_⟩
  rw [hXT₁, hXT₂, hO₁, hO₂, ← pre_inf, r1_inf_r2]
  have hST : pre ρ hLTN aBar2 ≤ T :=
    (pre_mono ρ hLTN (r1_inf_r2 ▸ inf_le_left : aBar2 ≤ r1)).trans hRT₁
  have hQker : ∀ q (hq : q ∈ qL L T), ρ ⟨q, hLTN (hQLT hq)⟩ = 1 := by
    intro q hq
    exact hcent q _ fun u hu => by
      have hc := hQab q hq u (hUQ hu)
      calc q * u * q⁻¹ = u * q * q⁻¹ := by rw [hc]
        _ = u := by group
  rcases hH with hHA | hHT
  ·
    right
    intro B hB
    have hQS : qL L T ≤ pre ρ hLTN aBar2 := fun q hq =>
      (mem_pre ρ hLTN).mpr ⟨hQLT hq, by rw [hQker q hq]; exact aBar2.one_mem⟩
    have hQB : Nat.card ↥(qL L T) ≤ Nat.card ↥B := hB.2.2 _ hQS hQe
    by_contra hne
    have hBQ : ¬ B ≤ qL L T := fun hle => hne (Subgroup.eq_of_le_of_card_ge hle hQB)
    obtain ⟨b, hbB, hbQ⟩ := Set.not_subset.mp hBQ
    obtain ⟨hbLT, hbA⟩ := (mem_pre ρ hLTN).mp (hB.1 hbB)
    have hbH : ρ ⟨b, hLTN hbLT⟩ ∈ alternatingGroup (Fin 6) := by
      rw [← hHA]
      exact ⟨⟨b, hbLT⟩, rfl⟩
    have hρb : ρ ⟨b, hLTN hbLT⟩ = a1 := by
      have hbr : ρ ⟨b, hLTN hbLT⟩ ∈ r1 ⊓ r2 := by rw [r1_inf_r2]; exact hbA
      rcases eq_of_mem_r1_inf_r2 hbr hbH with h1 | h1
      · exact absurd (hK b hbLT h1) hbQ
      · exact h1
    have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => by
      have := hB.2.1.1
      exact setLike_mul_comm hx hy
    have hUC : Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({b} : Set G)) = 4 := by
      set θ : ↥(blockU L) → A6Coc.Vec4 := fun u => A6Coc.eps (Multiplicative.toAdd (β' u))
        with hθ
      have hθinj : Function.Injective θ := by
        intro u v huv
        exact hβinj (Multiplicative.toAdd.injective (A6Coc.eps_injective huv))
      have hθsurj : Function.Surjective θ := by
        intro v
        obtain ⟨u, hu⟩ := hβs' (Multiplicative.ofAdd (A6Coc.epsInv v))
        refine ⟨u, ?_⟩
        show A6Coc.eps (Multiplicative.toAdd (β' u)) = v
        rw [hu]
        exact A6Coc.eps_epsInv v
      have hθb : ∀ u : ↥(blockU L),
          θ ⟨b * u * b⁻¹, Mod32.conj_mem_blockU (hLTN hbLT) u⟩ = A6Coc.act a1 (θ u) := by
        intro u
        have e := hβe' ⟨b, hLTN hbLT⟩ u ⟨b * u * b⁻¹, Mod32.conj_mem_blockU (hLTN hbLT) u⟩ rfl
        show A6Coc.eps (Multiplicative.toAdd (β'
          ⟨b * u * b⁻¹, Mod32.conj_mem_blockU (hLTN hbLT) u⟩)) =
            A6Coc.act a1 (A6Coc.eps (Multiplicative.toAdd (β' u)))
        rw [e, A6Coc.eps_heartAct, hρb]
      have key : ∀ u : ↥(blockU L), (u : G) ∈ Subgroup.centralizer ({b} : Set G) ↔
          A6Coc.act a1 (θ u) = θ u := by
        intro u
        rw [Subgroup.mem_centralizer_singleton_iff, ← hθb]
        constructor
        · intro hc
          congr 1
          apply Subtype.ext
          show b * u * b⁻¹ = u
          rw [← hc]
          group
        · intro hc
          have h1 : b * u * b⁻¹ = u := congrArg Subtype.val (hθinj hc)
          calc (u : G) * b = b * u * b⁻¹ * b := by rw [h1]
            _ = b * u := by group
      let e : ↥(blockU L ⊓ Subgroup.centralizer ({b} : Set G)) ≃
          {v : A6Coc.Vec4 // A6Coc.act a1 v = v} :=
        Equiv.ofBijective (fun x => ⟨θ ⟨x, x.2.1⟩, (key ⟨x, x.2.1⟩).mp x.2.2⟩)
          ⟨fun x y hxy => by
              have h1 : θ ⟨x, x.2.1⟩ = θ ⟨y, y.2.1⟩ := congrArg Subtype.val hxy
              have h2 := hθinj h1
              have h3 := congrArg Subtype.val h2
              exact Subtype.ext h3,
            fun ⟨v, hv⟩ => by
              obtain ⟨u, rfl⟩ := hθsurj v
              exact ⟨⟨u, u.2, (key u).mpr hv⟩, rfl⟩⟩
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, card_fix_a1]
    set C := qL L T ⊓ Subgroup.centralizer ({b} : Set G) with hC
    have hBLT : B ≤ L ⊔ T := hB.1.trans (pre_le_sup ρ hLTN aBar2)
    let fB : ↥B →* Equiv.Perm (Fin 6) := f.comp (Subgroup.inclusion hBLT)
    have hrB : Nat.card fB.range ≤ 2 := by
      have ha12 : orderOf a1 = 2 := orderOf_eq_prime (by decide) (by decide)
      have hle : fB.range ≤ Subgroup.zpowers a1 := by
        rintro _ ⟨x, rfl⟩
        obtain ⟨hxLT, hxA⟩ := (mem_pre ρ hLTN).mp (hB.1 x.2)
        have hxH : ρ ⟨x, hLTN hxLT⟩ ∈ alternatingGroup (Fin 6) := by
          rw [← hHA]
          exact ⟨⟨x, hxLT⟩, rfl⟩
        have hxr : ρ ⟨x, hLTN hxLT⟩ ∈ r1 ⊓ r2 := by rw [r1_inf_r2]; exact hxA
        show ρ ⟨x, hLTN hxLT⟩ ∈ Subgroup.zpowers a1
        rcases eq_of_mem_r1_inf_r2 hxr hxH with h1 | h1
        · rw [h1]
          exact Subgroup.one_mem _
        · rw [h1]
          exact Subgroup.mem_zpowers a1
      calc Nat.card fB.range ≤ Nat.card (Subgroup.zpowers a1) := Subgroup.card_le_of_le hle
        _ = 2 := by rw [Nat.card_zpowers, ha12]
    have hkB : Nat.card fB.ker ≤ Nat.card C := by
      refine Nat.card_le_card_of_injective (fun x : ↥fB.ker =>
        (⟨((x : ↥B) : G), hK _ (hBLT (x : ↥B).2) (MonoidHom.mem_ker.mp x.2),
          Subgroup.mem_centralizer_singleton_iff.mpr (hBab _ (x : ↥B).2 b hbB)⟩ : ↥C)) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    have hcardB : Nat.card B ≤ 2 * Nat.card C := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup fB.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange fB).toEquiv] at h1
      rw [h1]
      exact Nat.mul_le_mul hrB hkB
    have hpos : 0 < (blockU L).relIndex (qL L T) := by
      rcases Nat.eq_zero_or_pos ((blockU L).relIndex (qL L T)) with h0 | h0
      · have := hcardQ
        rw [h0, zero_mul] at this
        exact absurd this (Nat.card_pos).ne'
      · exact h0
    have hCbound : Nat.card C ≤ (blockU L).relIndex (qL L T) * 4 := by
      have h1 := Subgroup.relIndex_mul_card (H := blockU L) (K := C)
      have h2 : blockU L ⊓ C = blockU L ⊓ Subgroup.centralizer ({b} : Set G) := by
        rw [hC, ← inf_assoc, inf_of_le_left hUQ]
      rw [h2, hUC] at h1
      have h3 : (blockU L).relIndex C ≤ (blockU L).relIndex (qL L T) :=
        Subgroup.relIndex_le_of_le_right inf_le_left hpos.ne'
      calc Nat.card C = (blockU L).relIndex C * 4 := h1.symm
        _ ≤ _ := Nat.mul_le_mul_right 4 h3
    have hfin : Nat.card ↥(qL L T) ≤ (blockU L).relIndex (qL L T) * 8 := by
      calc _ ≤ Nat.card B := hQB
        _ ≤ 2 * Nat.card C := hcardB
        _ ≤ 2 * ((blockU L).relIndex (qL L T) * 4) := Nat.mul_le_mul_left 2 hCbound
        _ = _ := by ring
    rw [hcardQ] at hfin
    omega
  · left
    have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp hHT
    set f₁ := InternalSec.autOnHom hLTV with hf₁def
    have hs₁ := InternalSec.autOnHom_surjective hLTV
    have hker : f₁.ker = f.ker := by
      ext x
      rw [InternalSec.mem_ker_autOnHom, MonoidHom.mem_ker]
      constructor
      · intro hx
        exact hcent x (hLTN x.2) fun u hu => by
          have hc := Subgroup.mem_centralizer_iff.mp hx u (hUV hu)
          calc (x : G) * u * (x : G)⁻¹ = u * x * (x : G)⁻¹ := by rw [← hc]
            _ = u := by group
      · intro hx
        have hxQ := hK x x.2 hx
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact hQab _ (hVQ hv) _ hxQ
    let φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6) :=
      (QuotientGroup.quotientKerEquivOfSurjective f₁ hs₁).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivOfSurjective f hsurj))
    have hφ : ∀ x : ↥(L ⊔ T), φ (f₁ x) = f x := by
      intro x
      have h1 : (QuotientGroup.quotientKerEquivOfSurjective f₁ hs₁).symm (f₁ x) =
          (QuotientGroup.mk x : ↥(L ⊔ T) ⧸ f₁.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      show (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
        ((QuotientGroup.quotientMulEquivOfEq hker)
          ((QuotientGroup.quotientKerEquivOfSurjective f₁ hs₁).symm (f₁ x))) = f x
      rw [h1]
      rfl
    have hTsylLT : ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index :=
      fun h2 => hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
    have hfT : (T.subgroupOf (L ⊔ T)).map f = sylowS6 := by
      have hle : (T.subgroupOf (L ⊔ T)).map f ≤ sylowS6 := by
        rintro _ ⟨x, hx, rfl⟩
        exact hρT x hx
      have hidx := Subgroup.index_map_dvd (H := T.subgroupOf (L ⊔ T)) hsurj
      have hodd : ¬ 2 ∣ ((T.subgroupOf (L ⊔ T)).map f).index :=
        fun h2 => hTsylLT (h2.trans hidx)
      have hdvd : Nat.card ↥((T.subgroupOf (L ⊔ T)).map f) ∣ 16 := by
        rw [← S6Syl.card_sylowS6]
        exact Subgroup.card_dvd_of_le hle
      have hmul := Subgroup.card_mul_index ((T.subgroupOf (L ⊔ T)).map f)
      rw [h720] at hmul
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [S6Syl.card_sylowS6]
      obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥((T.subgroupOf (L ⊔ T)).map f) = c := ⟨_, rfl⟩
      rw [hc] at hdvd hmul ⊢
      have hc16 : c ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases c <;> omega
    have hmapT : ((autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T))).map
        φ.toMonoidHom = (T.subgroupOf (L ⊔ T)).map f := by
      ext s
      constructor
      · rintro ⟨a, ha, rfl⟩
        have ha' : (a : MulAut ↥(vPlus L T)) ∈ autOn T (vPlus L T) := ha
        obtain ⟨g, hgT, hga⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp ha'
        have hgLT : (g : G) ∈ L ⊔ T := Subgroup.mem_sup_right hgT
        have e : a = f₁ ⟨g, hgLT⟩ := by
          apply Subtype.ext
          rw [← hga]
          rfl
        refine ⟨⟨g, hgLT⟩, hgT, ?_⟩
        rw [e]
        exact (hφ _).symm
      · rintro ⟨x, hx, rfl⟩
        refine ⟨f₁ x, ?_, hφ x⟩
        show (f₁ x : MulAut ↥(vPlus L T)) ∈ autOn T (vPlus L T)
        exact CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨x, hLTV x.2⟩, hx, rfl⟩
    have hpre : pre ρ hLTN aBar2 = preimageA2 T L φ := by
      ext g
      constructor
      · intro hg
        obtain ⟨hgLT, hgA⟩ := (mem_pre ρ hLTN).mp hg
        refine ⟨hST hg, ⟨⟨g, hLTV hgLT⟩, ?_, rfl⟩⟩
        show conjAct (vPlus L T) ⟨g, hLTV hgLT⟩ ∈
          (aBar2.map φ.symm.toMonoidHom).map (autOn (L ⊔ T) (vPlus L T)).subtype
        refine ⟨f₁ ⟨g, hgLT⟩, ⟨f ⟨g, hgLT⟩, hgA, ?_⟩, rfl⟩
        show φ.symm (f ⟨g, hgLT⟩) = f₁ ⟨g, hgLT⟩
        rw [← hφ]
        exact φ.symm_apply_apply _
      · rintro ⟨hgT, y, hy, rfl⟩
        obtain ⟨a, ⟨c, hc, hca⟩, hay⟩ := hy
        have hgLT : (y : G) ∈ L ⊔ T := Subgroup.mem_sup_right hgT
        refine (mem_pre ρ hLTN).mpr ⟨hgLT, ?_⟩
        have e : a = f₁ ⟨y, hgLT⟩ := by
          apply Subtype.ext
          show (a : MulAut ↥(vPlus L T)) = _
          rw [show (a : MulAut ↥(vPlus L T)) = conjAct (vPlus L T) y from hay]
          rfl
        have hfc : f ⟨y, hgLT⟩ = c := by
          rw [← hφ, ← e, ← hca]
          exact φ.apply_symm_apply c
        rw [← hfc] at hc
        exact hc
    exact ⟨φ, hmapT.trans hfT, hpre⟩

end CFSG.Quasithin.H13
