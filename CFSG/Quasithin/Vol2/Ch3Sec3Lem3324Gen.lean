module

public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport
public import CFSG.GH74.M12.HypGroup
public import CFSG.Quasithin.Background.A4Local
public import CFSG.Quasithin.Background.B1ChiefCount
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open scoped commutatorElement Pointwise

namespace Gen3324

variable {G : Type} [Group G]

section Pre

variable {Γ : Type} [Group Γ] {K : Subgroup G} (ρ : ↥K →* Γ)

@[expose] def pre₀ (Q : Subgroup Γ) : Subgroup G := (Q.comap ρ).map K.subtype

theorem mem_pre₀ {Q : Subgroup Γ} {g : G} : g ∈ pre₀ ρ Q ↔ ∃ hg : g ∈ K, ρ ⟨g, hg⟩ ∈ Q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hQ⟩
    exact ⟨⟨g, hg⟩, hQ, rfl⟩

theorem pre₀_le (Q : Subgroup Γ) : pre₀ ρ Q ≤ K := fun _ hg => ((mem_pre₀ ρ).mp hg).1

theorem pre₀_mono {Q₁ Q₂ : Subgroup Γ} (h : Q₁ ≤ Q₂) : pre₀ ρ Q₁ ≤ pre₀ ρ Q₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem pre₀_inf (Q₁ Q₂ : Subgroup Γ) : pre₀ ρ (Q₁ ⊓ Q₂) = pre₀ ρ Q₁ ⊓ pre₀ ρ Q₂ := by
  ext g
  rw [Subgroup.mem_inf, mem_pre₀, mem_pre₀, mem_pre₀]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, hg, h2⟩
  · rintro ⟨⟨hg, h1⟩, hg', h2⟩
    exact ⟨hg, h1, h2⟩

theorem pre₀_le_normalizer {Q₁ Q₂ : Subgroup Γ} (h : Q₁ ≤ Subgroup.normalizer (Q₂ : Set Γ)) :
    pre₀ ρ Q₁ ≤ Subgroup.normalizer (pre₀ ρ Q₂ : Set G) := by
  intro g hg
  obtain ⟨hgK, hgQ⟩ := (mem_pre₀ ρ).mp hg
  have hn := Subgroup.mem_normalizer_iff.mp (h hgQ)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_pre₀, mem_pre₀]
  constructor
  · rintro ⟨hx, hxQ⟩
    have hm : g * x * g⁻¹ ∈ K := K.mul_mem (K.mul_mem hgK hx) (K.inv_mem hgK)
    refine ⟨hm, ?_⟩
    have e : (⟨g * x * g⁻¹, hm⟩ : ↥K) = ⟨g, hgK⟩ * ⟨x, hx⟩ * (⟨g, hgK⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (hn _).mp hxQ
  · rintro ⟨hm, hmQ⟩
    have hx : x ∈ K := by
      have h1 := K.mul_mem (K.mul_mem (K.inv_mem hgK) hm) hgK
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rwa [e] at h1
    refine ⟨hx, ?_⟩
    have e : (⟨g * x * g⁻¹, hm⟩ : ↥K) = ⟨g, hgK⟩ * ⟨x, hx⟩ * (⟨g, hgK⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hmQ
    exact (hn _).mpr hmQ

theorem pre₀_isPGroup [Finite G] {Q : Subgroup Γ} (hQ : ∀ x ∈ Q, x * x = 1)
    (hker : ∀ g : ↥K, ρ g = 1 → (g : G) ∈ pCoreOf 2 K) : IsPGroup 2 ↥(pre₀ ρ Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  rintro ⟨g, hg⟩
  obtain ⟨hgK, hgQ⟩ := (mem_pre₀ ρ).mp hg
  have hsq : g * g ∈ pCoreOf 2 K := by
    apply hker ⟨g * g, K.mul_mem hgK hgK⟩
    have e : (⟨g * g, K.mul_mem hgK hgK⟩ : ↥K) = ⟨g, hgK⟩ * ⟨g, hgK⟩ := rfl
    rw [e, map_mul]
    exact hQ _ hgQ
  obtain ⟨k, hk⟩ := hQ2 ⟨g * g, hsq⟩
  have hk' : (g * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ, pow_mul', sq]
  exact hk'

theorem card_pre₀ [Finite G] (Q : Subgroup Γ) :
    Nat.card ↥(pre₀ ρ Q) = Nat.card ↥(ρ.range ⊓ Q) * Nat.card ↥ρ.ker := by
  have h1 : Nat.card ↥(pre₀ ρ Q) = Nat.card ↥(Q.comap ρ) :=
    Subgroup.card_map_of_injective K.subtype_injective
  set H := Q.comap ρ with hH
  let g : ↥H →* Γ := ρ.comp H.subtype
  have hrange : g.range = ρ.range ⊓ Q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
  have hkerH : ρ.ker ≤ H := fun x hx => by
    show ρ x ∈ Q
    rw [MonoidHom.mem_ker.mp hx]
    exact Q.one_mem
  have hker : g.ker = ρ.ker.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerH).toEquiv] at h2
  rw [h1, h2]

end Pre

theorem parabolic_gen₀ [Finite G] {Γ : Type} [Group Γ] [Finite Γ] {T K : Subgroup G}
    (ρ : ↥K →* Γ) (hTK : T ≤ K) (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hker : ∀ g : ↥K, ρ g = 1 → (g : G) ∈ pCoreOf 2 K)
    {p r : Subgroup Γ} (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTK ht⟩ ∈ p) (hrp : r ≤ p)
    (hpr : p ≤ Subgroup.normalizer (r : Set Γ)) (hr2 : ∀ x ∈ r, x * x = 1)
    (h6 : Nat.card ↥(ρ.range ⊓ p) = 6 * Nat.card ↥(ρ.range ⊓ r))
    {ka kb : ↥K} (hap : ρ ka ∈ p) (hbp : ρ kb ∈ p) (hab : (ρ kb * ρ ka)⁻¹ * (ρ ka * ρ kb) ∉ r) :
    oTwoUpper (oTwoUpper (pre₀ ρ p)) = oTwoUpper (pre₀ ρ p) ∧
      T ≤ Subgroup.normalizer (oTwoUpper (pre₀ ρ p) : Set G) ∧
      oTwoUpper (pre₀ ρ p) ⊔ T = pre₀ ρ p ∧
      Nonempty (↥(pre₀ ρ p) ⧸ CFSG.pCore 2 ↥(pre₀ ρ p) ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 (pre₀ ρ p) = pre₀ ρ r ∧ pre₀ ρ r ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pre₀ ρ p with hPdef
  set R := pre₀ ρ r with hRdef
  have hTP : T ≤ P := fun t ht => (mem_pre₀ ρ).mpr ⟨hTK ht, hρT t ht⟩
  have hRP : R ≤ P := pre₀_mono ρ hrp
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := pre₀_le_normalizer ρ hpr
  have hR2 : IsPGroup 2 ↥R := pre₀_isPGroup ρ hr2 hker
  have hTsyl : IsSylowTwoOf T P :=
    ⟨hTP, hT2, fun h2 => hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le hTP))⟩
  have hRT : R ≤ T := hTsyl.le_of_normalizes hRP hPN hR2
  have h6' : Nat.card ↥P = 6 * Nat.card ↥R := by
    rw [card_pre₀ ρ p, card_pre₀ ρ r, h6]
    ring
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  have hrel : R.relIndex P = 6 := by
    have := Subgroup.relIndex_mul_card (H := R) (K := P)
    rw [inf_of_le_left hRP, h6'] at this
    exact Nat.eq_of_mul_eq_mul_right hRpos (by rw [this])
  have hNn : (R.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hQ6 : Nat.card (↥P ⧸ R.subgroupOf P) = 6 := hrel
  have haP : (ka : G) ∈ P := (mem_pre₀ ρ).mpr ⟨ka.2, hap⟩
  have hbP : (kb : G) ∈ P := (mem_pre₀ ρ).mpr ⟨kb.2, hbp⟩
  have hne : (QuotientGroup.mk ⟨ka, haP⟩ : ↥P ⧸ R.subgroupOf P) * QuotientGroup.mk ⟨kb, hbP⟩ ≠
      QuotientGroup.mk ⟨kb, hbP⟩ * QuotientGroup.mk ⟨ka, haP⟩ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    intro h
    have h1 := QuotientGroup.eq.mp h.symm
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨hm, hmr⟩ := (mem_pre₀ ρ).mp h1
    apply hab
    have e : (⟨_, hm⟩ : ↥K) = (kb * ka)⁻¹ * (ka * kb) := rfl
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

variable [Finite G]

theorem exists_max {K U A : Subgroup G} (hUA : U < A) (hKU : K ≤ Subgroup.normalizer (U : Set G)) :
    ∃ B : Subgroup G, U ≤ B ∧ B < A ∧ K ≤ Subgroup.normalizer (B : Set G) ∧
      ∀ C : Subgroup G, B < C → C < A → ¬ K ≤ Subgroup.normalizer (C : Set G) := by
  classical
  let S : Set (Subgroup G) := {B | U ≤ B ∧ B < A ∧ K ≤ Subgroup.normalizer (B : Set G)}
  have hS : S.toFinite.toFinset.Nonempty := ⟨U, by simpa using ⟨le_rfl, hUA, hKU⟩⟩
  obtain ⟨B, hB, hmax⟩ := S.toFinite.toFinset.exists_max_image (fun B => Nat.card B) hS
  rw [Set.Finite.mem_toFinset] at hB
  refine ⟨B, hB.1, hB.2.1, hB.2.2, fun C hBC hCA hKC => ?_⟩
  have h1 := hmax C (by rw [Set.Finite.mem_toFinset]; exact ⟨hB.1.trans hBC.le, hCA, hKC⟩)
  have h2 : Nat.card B < Nat.card C := Subgroup.card_lt_of_lt hBC
  omega

theorem commutator_le_of_ncAtMost {K U A : Subgroup G} (hK : oTwoUpper K = K) (hUA : U ≤ A)
    (hAK : A ≤ K) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hA2 : IsPGroup 2 A)
    (h0 : NCAtMost K U A 0) : ⁅A, K⁆ ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hn : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  by_cases hAU : A = U
  · subst hAU
    exact commutator_le_of_le_normalizer hKA
  obtain ⟨B, hUB, hBA, hKB, hmax⟩ := exists_max (lt_of_le_of_ne hUA (Ne.symm hAU)) hKU
  have hc : IsTwoChiefFactor K A B := ⟨hBA, hAK, hKA, hKB, hmax, fun a ha => by
    obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
    exact ⟨k, by
      have : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact B.one_mem⟩⟩
  have hAB : ⁅A, K⁆ ≤ B := by
    by_contra hnc
    exact h0 ⟨![A], ![B], fun i => by fin_cases i; exact ⟨hc, hnc, hUB, le_rfl⟩,
      fun i j hij => absurd hij (by fin_cases i; fin_cases j; decide)⟩
  have hBK : ⁅B, K⁆ ≤ U :=
    ih (Nat.card B) (hn ▸ Subgroup.card_lt_of_lt hBA) hUB (hBA.le.trans hAK) hKB
      (hA2.to_le hBA.le) (fun h => h0 (h.mono le_rfl hBA.le)) rfl
  have hodd : ∀ y ∈ K, Odd (orderOf y) → ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ U := by
    intro y hy hyo a ha
    set c := y * a * y⁻¹ * a⁻¹ with hcdef
    have hya : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hy) a).mp ha
    have hcA : c ∈ A := A.mul_mem hya (A.inv_mem ha)
    have hcB : c ∈ B := by
      have h2 : ⁅a, y⁆ ∈ B := hAB (Subgroup.commutator_mem_commutator ha hy)
      have hc' : c = (⁅a, y⁆)⁻¹ := by
        simp only [commutatorElement_def, hcdef]
        group
      rw [hc']
      exact B.inv_mem h2
    have hcN : c ∈ Subgroup.normalizer (U : Set G) := hKU (hAK hcA)
    have hu₁ : y * c * y⁻¹ * c⁻¹ ∈ U := by
      have := hBK (Subgroup.commutator_mem_commutator hcB hy)
      have e : y * c * y⁻¹ * c⁻¹ = (⁅c, y⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact U.inv_mem this
    have hstep : ∀ j : ℕ, ∃ w ∈ U, y ^ j * a * (y ^ j)⁻¹ = w * c ^ j * a := by
      intro j
      induction j with
      | zero => exact ⟨1, U.one_mem, by simp⟩
      | succ j ihj =>
        obtain ⟨w, hw, e⟩ := ihj
        set u₁' := c⁻¹ * (y * c * y⁻¹ * c⁻¹) * c with hu₁'
        have hu₁'U : u₁' ∈ U := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) _).mp hu₁
          simpa [hu₁', mul_assoc] using this
        have hyc : y * c * y⁻¹ = c * u₁' := by
          rw [hu₁']
          group
        obtain ⟨n', hn', e'⟩ := ChiefCount.pow_mul_mem hcN hu₁'U j
        have hyw : y * w * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hKU hy) w).mp hw
        have hcn : c ^ j * n' * (c ^ j)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hcN j) n').mp hn'
        refine ⟨(y * w * y⁻¹) * (c ^ j * n' * (c ^ j)⁻¹), U.mul_mem hyw hcn, ?_⟩
        have h1 : y * c ^ j * y⁻¹ = (c * u₁') ^ j := by
          rw [← hyc, conj_pow]
        have h2 : y * a * y⁻¹ = c * a := by
          rw [hcdef]
          group
        calc y ^ (j + 1) * a * (y ^ (j + 1))⁻¹ = y * (y ^ j * a * (y ^ j)⁻¹) * y⁻¹ := by
              rw [pow_succ']
              group
          _ = y * (w * c ^ j * a) * y⁻¹ := by rw [e]
          _ = (y * w * y⁻¹) * (y * c ^ j * y⁻¹) * (y * a * y⁻¹) := by group
          _ = (y * w * y⁻¹) * (c ^ j * n') * (c * a) := by rw [h1, e', h2]
          _ = (y * w * y⁻¹) * (c ^ j * n' * (c ^ j)⁻¹) * c ^ (j + 1) * a := by
              rw [pow_succ]
              group
    obtain ⟨w, hw, e⟩ := hstep (orderOf y)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at e
    have hcm : c ^ orderOf y ∈ U := by
      have h1 : c ^ orderOf y = w⁻¹ := by
        have := congrArg (fun z => w⁻¹ * z * a⁻¹) e
        simp only [mul_inv_cancel_right] at this
        rw [this]
        group
      rw [h1]
      exact U.inv_mem hw
    obtain ⟨s, hs⟩ := hA2 ⟨c, hcA⟩
    have hs' : c ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
    exact Lem3328.mem_of_pow_odd hyo hcm (by rw [hs']; exact U.one_mem)
  let C' : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (U : Set G) ∧ g ∈ Subgroup.normalizer (A : Set G) ∧
        ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ U}
      mul_mem' := by
        rintro g h ⟨hgU, hgA, hg⟩ ⟨hhU, hhA, hh⟩
        refine ⟨Subgroup.mul_mem _ hgU hhU, Subgroup.mul_mem _ hgA hhA, fun a ha => ?_⟩
        have h1 : g * (h * a * h⁻¹ * a⁻¹) * g⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp hgU _).mp (hh a ha)
        have e : g * h * a * (g * h)⁻¹ * a⁻¹ =
            g * (h * a * h⁻¹ * a⁻¹) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) := by group
        rw [e]
        exact U.mul_mem h1 (hg a ha)
      one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun a _ => by simp⟩
      inv_mem' := by
        rintro g ⟨hgU, hgA, hg⟩
        refine ⟨Subgroup.inv_mem _ hgU, Subgroup.inv_mem _ hgA, fun a ha => ?_⟩
        have ha' : g⁻¹ * a * g ∈ A := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgA) a).mp ha
          simpa using this
        have h1 := U.inv_mem (hg _ ha')
        have e : g⁻¹ * a * g⁻¹⁻¹ * a⁻¹ = (g * (g⁻¹ * a * g) * g⁻¹ * (g⁻¹ * a * g)⁻¹)⁻¹ := by
          group
        rw [e]
        exact h1 }
  have hKC : K ≤ C' := by
    rw [← hK]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, hyo⟩
    exact ⟨hKU hy, hKA hy, hodd y hy hyo⟩
  rw [Subgroup.commutator_le]
  intro a ha k hk
  obtain ⟨-, -, hk'⟩ := hKC hk
  have h1 := U.inv_mem (hk' a ha)
  have e : ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem exists_top_factor {K U : Subgroup G} (hUK : U ≤ K)
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hUc : U ≤ ⁅U, K⁆) : ∃ B : Subgroup G, IsTwoChiefFactor K U B ∧ ¬ ⁅U, K⁆ ≤ B := by
  have hKbot : K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun y => by simp
  obtain ⟨B, -, hBU, hKB, hmax⟩ := exists_max (bot_lt_iff_ne_bot.mpr hU1) hKbot
  refine ⟨B, ⟨hBU, hUK, hKU, hKB, hmax, fun a ha => ?_⟩, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := hU2 ⟨a, ha⟩
    exact ⟨k, by
      have : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact B.one_mem⟩
  · exact (not_le_of_gt hBU) (hUc.trans h)

theorem le_oTwoUpper_sup {H S : Subgroup G} (hS : IsSylowTwoOf S H) : H ≤ oTwoUpper H ⊔ S := by
  have h := CFSG.Quasithin.sup_twoResidual_eq hS
  rw [CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper] at h
  rw [sup_comm] at h
  exact h.ge

theorem dih_check : ∀ g : DihedralGroup 6, g ≠ 1 → g ≠ DihedralGroup.r 3 →
    ∃ h : DihedralGroup 6, g * (h * g * h⁻¹) ≠ 1 ∧ (g * (h * g * h⁻¹)) ^ 3 = 1 := by
  decide

theorem r3_sq : DihedralGroup.r 3 * DihedralGroup.r 3 = (1 : DihedralGroup 6) := by
  decide

end Gen3324

end CFSG.Quasithin.H13
