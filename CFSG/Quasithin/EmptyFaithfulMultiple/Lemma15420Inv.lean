module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Quot
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Xi

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace L15420

omit [Finite G] in
theorem card_quot_eq_relIndex (L : Subgroup G) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = (pCoreOf 2 L).relIndex L := by
  rw [Subgroup.relIndex, ← Subgroup.index_eq_card]
  congr 1
  ext x
  rw [Subgroup.mem_subgroupOf, pCoreOf]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

end L15420

namespace Setting15419

variable (s : Setting15419 G T)

theorem diag_action (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) {a : G}
    (haJ : a ∈ thompsonJ T) (ha2 : a * a = 1)
    (haC₂ : a ∈ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₂⁆ : Subgroup G) : Set G))
    (haC₁ : a ∉ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₁⁆ : Subgroup G) : Set G)) :
    (∀ x ∈ s.X₁, a * x * a⁻¹ * x ∈ pCoreOf 2 s.X₁) ∧
      ∀ x ∈ s.X₂, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 s.X₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hO₁, hO₂, hi₁, hi₂, -, -, hc₁, hc₂, -, -, hS₁, hS₂, -⟩ := s.dataX
  set V := VZ T s.M₁ with hVdef
  set V₁ := (⁅V, s.X₁⁆ : Subgroup G) with hV₁def
  set V₂ := (⁅V, s.X₂⁆ : Subgroup G) with hV₂def
  have hV := s.isElemAbelian_VZ hyp
  have hVN : s.M₁ ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hX₁V : s.X₁ ≤ Subgroup.normalizer (V : Set G) := (s.X₁_le_X.trans s.le_X).trans hVN
  have hX₂V : s.X₂ ≤ Subgroup.normalizer (V : Set G) := (s.X₂_le_X.trans s.le_X).trans hVN
  have hV₁V : V₁ ≤ V := commutator_le_of_le_normalizer hX₁V
  have hV₁2 : ∀ v ∈ V₁, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v (hV₁V hv)
  have hXV₁ : s.X ≤ Subgroup.normalizer (V₁ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₁ hx)
  have hXV₂ : s.X ≤ Subgroup.normalizer (V₂ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₂ hx)
  have haS : a ∈ baum T := L15420.thompsonJ_le_baum T haJ
  have haM : a ∈ s.M₁ := s.inM₁.2 haS.1
  have haX₁ : a ∈ Subgroup.normalizer (s.X₁ : Set G) := hS₁ haS
  have haX₂ : a ∈ Subgroup.normalizer (s.X₂ : Set G) := hS₂ haS
  have haN₁ : a ∈ Subgroup.normalizer (V₁ : Set G) :=
    A4.mem_normalizer_commutator (hVN haM) haX₁
  have hNC : pCoreOf 2 s.X ≤ Subgroup.centralizer (V : Set G) :=
    s.pCoreOf_X_le_centralizer hyp h12
  have hQ₁ : pCoreOf 2 s.X₁ ≤ pCoreOf 2 s.X := s.pCoreOf_le_pCoreOf_X s.X₁_le_X s.X_le_normalizer_X₁
  refine ⟨?_, fun x hx => ?_⟩
  swap
  ·
    have hcX : a * x * a⁻¹ * x⁻¹ ∈ s.X₂ :=
      s.X₂.mul_mem ((Subgroup.mem_normalizer_iff.mp haX₂ x).mp hx) (s.X₂.inv_mem hx)
    have hcC : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V₂ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hxX : x ∈ s.X := s.X₂_le_X hx
      have hw : x⁻¹ * v * x ∈ V₂ := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXV₂ hxX)) v).mp hv
        simpa using this
      have hav : a⁻¹ * (x⁻¹ * v * x) * a = x⁻¹ * v * x := by
        have := Subgroup.mem_centralizer_iff.mp haC₂ _ hw
        calc a⁻¹ * (x⁻¹ * v * x) * a = a⁻¹ * ((x⁻¹ * v * x) * a) := by group
          _ = a⁻¹ * (a * (x⁻¹ * v * x)) := by rw [this]
          _ = x⁻¹ * v * x := by group
      have hav' : a * v * a⁻¹ = v := by
        have := Subgroup.mem_centralizer_iff.mp haC₂ _ hv
        calc a * v * a⁻¹ = v * a * a⁻¹ := by rw [this]
          _ = v := by group
      have key : (a * x * a⁻¹ * x⁻¹) * v * (a * x * a⁻¹ * x⁻¹)⁻¹ = v := by
        calc (a * x * a⁻¹ * x⁻¹) * v * (a * x * a⁻¹ * x⁻¹)⁻¹ =
              a * x * (a⁻¹ * (x⁻¹ * v * x) * a) * x⁻¹ * a⁻¹ := by group
          _ = a * v * a⁻¹ := by rw [hav]; group
          _ = v := hav'
      set c := a * x * a⁻¹ * x⁻¹ with hcdef
      calc v * c = c * v * c⁻¹ * c := by rw [key]
        _ = c * v := by group
    exact inf_centralizer_commutator_le_pCoreOf hV hX₂V hO₂ hi₂ hc₂ ⟨hcX, hcC⟩
  ·
    obtain ⟨x₀, hx₀X, hx₀o, hx₀C⟩ : ∃ x₀ ∈ s.X₁, Odd (orderOf x₀) ∧
        x₀ ∉ Subgroup.centralizer (V₁ : Set G) := by
      by_contra h
      push Not at h
      have hX₁C : s.X₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
        rw [hO₁]
        exact (Subgroup.closure_le _).mpr fun x hx => h x hx.1 hx.2
      have hbot := commutator_inf_centralizer_eq_bot_of_card_eq_four hV hX₁V hO₁ hc₁
      have : V₁ ⊓ Subgroup.centralizer (s.X₁ : Set G) = V₁ := by
        refine inf_eq_left.mpr fun v hv => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp (hX₁C hx) v hv).symm
      rw [← hV₁def, this] at hbot
      rw [hbot, Subgroup.card_bot] at hc₁
      omega
    have hx₀Q : x₀ ∉ pCoreOf 2 s.X₁ := fun h => hx₀C (Subgroup.centralizer_le hV₁V (hNC (hQ₁ h)))
    have hX₁le := L15420.le_sup_zpowers_of_relIndex_three hi₁ hx₀X hx₀Q
    have hzQ : Subgroup.zpowers x₀ ≤ Subgroup.normalizer (pCoreOf 2 s.X₁ : Set G) :=
      (Subgroup.zpowers_le.mpr hx₀X).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hax₀ : a * x₀ * a⁻¹ ∈ s.X₁ := (Subgroup.mem_normalizer_iff.mp haX₁ x₀).mp hx₀X
    set α := L15420.quotConj s.X₁ a haX₁ with hαdef
    set xb : ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁ :=
      QuotientGroup.mk (s := CFSG.pCore 2 ↥s.X₁) (⟨x₀, hx₀X⟩ : s.X₁) with hxbdef
    have hcard : Nat.card (↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁) = 3 := by
      rw [L15420.card_quot_eq_relIndex, hi₁]
    have hxb1 : xb ≠ 1 := fun h => hx₀Q (L15420.mk_eq_one_iff.mp h)
    have hxb3 : xb ^ 3 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have hgen : ∀ w : ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁, w ∈ Subgroup.zpowers xb := by
      intro w
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨q, hq, m, hm, hwe⟩ :=
        (Ch1Sec3.mem_sup_iff_of_le_normalizer hzQ).1 (hX₁le w.2)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      refine ⟨k, ?_⟩
      have h1 : (⟨q, (CFSG.LieType.BorelTits.pCoreOf_le 2 s.X₁) hq⟩ : s.X₁) * ⟨x₀, hx₀X⟩ ^ k =
          w := Subtype.ext (by simp [hwe])
      rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      have h2 : ((⟨q, (CFSG.LieType.BorelTits.pCoreOf_le 2 s.X₁) hq⟩ : s.X₁) :
          ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁) = 1 := L15420.mk_eq_one_iff.mpr hq
      rw [h2, one_mul]
    have hαx : α xb = xb⁻¹ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen (α xb))
      have hk3 : α xb = xb ^ (k % 3) := by
        rw [← hk]
        conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
        rw [zpow_add, zpow_mul, show xb ^ (3 : ℤ) = 1 from by exact_mod_cast hxb3, one_zpow,
          mul_one]
      have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
      have hnn : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
      interval_cases h : k % 3
      ·
        exfalso
        rw [zpow_zero] at hk3
        exact hxb1 (α.injective (by rw [hk3, map_one]))
      ·
        exfalso
        rw [zpow_one] at hk3
        have hc : a * x₀ * a⁻¹ * x₀⁻¹ ∈ pCoreOf 2 s.X₁ := by
          have : ((⟨a * x₀ * a⁻¹, hax₀⟩ : s.X₁) : ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁) = xb := hk3
          have h2 : ((⟨a * x₀ * a⁻¹, hax₀⟩ * (⟨x₀, hx₀X⟩ : s.X₁)⁻¹ : s.X₁) :
              ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁) = 1 := by
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, this, ← hxbdef, mul_inv_cancel]
          exact L15420.mk_eq_one_iff.mp h2
        have hcV := hNC (hQ₁ hc)
        have hcard₂ := L15420.card_inf_centralizer_eq_two hc₁
          (L15420.isPGroup_zpowers_of_mul_self ha2) haN₁ haC₁
        obtain ⟨f, hf, hf1⟩ := (Subgroup.bot_or_exists_ne_one
          (V₁ ⊓ Subgroup.centralizer ({a} : Set G))).resolve_left (by
            intro h
            rw [h, Subgroup.card_bot] at hcard₂
            omega)
        have hfa : a * f * a⁻¹ = f := by
          have := Subgroup.mem_centralizer_singleton_iff.mp hf.2
          calc a * f * a⁻¹ = f * a * a⁻¹ := by rw [this]
            _ = f := by group
        have hx₀f : x₀ * f * x₀⁻¹ ∈ V₁ :=
          (Subgroup.mem_normalizer_iff.mp (hXV₁ (s.X₁_le_X hx₀X)) f).mp hf.1
        set c := a * x₀ * a⁻¹ * x₀⁻¹ with hcdef
        have hcv : ∀ v ∈ V, c * v = v * c := fun v hv =>
          (Subgroup.mem_centralizer_iff.mp hcV v hv).symm
        have hfix : a * (x₀ * f * x₀⁻¹) * a⁻¹ = x₀ * f * x₀⁻¹ := by
          have e : a * (x₀ * f * x₀⁻¹) * a⁻¹ = c * (x₀ * (a * f * a⁻¹) * x₀⁻¹) * c⁻¹ := by
            rw [hcdef]; group
          rw [e, hfa]
          have := hcv _ (hV₁V hx₀f)
          calc c * (x₀ * f * x₀⁻¹) * c⁻¹ = (x₀ * f * x₀⁻¹) * c * c⁻¹ := by rw [this]
            _ = x₀ * f * x₀⁻¹ := by group
        have hx₀f1 : x₀ * f * x₀⁻¹ ≠ 1 := fun h => hf1 (by
          calc f = x₀⁻¹ * (x₀ * f * x₀⁻¹) * x₀ := by group
            _ = 1 := by rw [h]; group)
        have hx₀fC : x₀ * f * x₀⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc x₀ * f * x₀⁻¹ * a = a * (x₀ * f * x₀⁻¹) * a⁻¹ * a := by rw [hfix]
            _ = a * (x₀ * f * x₀⁻¹) := by group
        have he := L15420.eq_of_card_eq_two hcard₂ ⟨hx₀f, hx₀fC⟩ hf hx₀f1 hf1
        have hcomm : x₀ * f = f * x₀ := by
          calc x₀ * f = x₀ * f * x₀⁻¹ * x₀ := by group
            _ = f * x₀ := by rw [he]
        exact hx₀C (mem_centralizer_of_card_eq_four hc₁ hV₁2 (hXV₁ (s.X₁_le_X hx₀X)) hx₀o hf.1
          hf1 hcomm)
      ·
        rw [hk3]
        calc xb ^ (2 : ℤ) = xb ^ (3 : ℤ) * xb⁻¹ := by group
          _ = xb⁻¹ := by rw [show xb ^ (3 : ℤ) = 1 from by exact_mod_cast hxb3, one_mul]
    intro x hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen ((⟨x, hx⟩ : s.X₁) : _))
    have hαw : α ((⟨x, hx⟩ : s.X₁) : ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁) =
        ((⟨x, hx⟩ : s.X₁) : ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁)⁻¹ := by
      rw [← hj, map_zpow, hαx, inv_zpow]
    rw [hαdef, L15420.quotConj_mk] at hαw
    have h1 : ((L15420.conjRestr s.X₁ a haX₁ ⟨x, hx⟩ * ⟨x, hx⟩ : s.X₁) :
        ↥s.X₁ ⧸ CFSG.pCore 2 ↥s.X₁) = 1 := by
      rw [QuotientGroup.mk_mul, hαw, inv_mul_cancel]
    have h2 := L15420.mk_eq_one_iff.mp h1
    simpa [L15420.conjRestr_apply_coe] using h2

end Setting15419

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem exists_inverting (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) :
    ∃ g ∈ T ⊓ I₀, ∀ x ∈ s.X, g * x * g⁻¹ * x ∈ pCoreOf 2 s.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX, -, -, -, -, -, -, -, -, -, -, hS₁, hS₂, -⟩ := s.dataX
  obtain ⟨a, haJ, ha2, haC₂, haC₁⟩ := s.exists_diag hyp
  obtain ⟨hinv₁, hcen₂⟩ := s.diag_action hyp h12 haJ ha2 haC₂ haC₁
  have haTI : a ∈ T ⊓ I₀ := c.lt.le (s.baum_le_T₀ (L15420.thompsonJ_le_baum T haJ))
  have haS : a ∈ baum T := L15420.thompsonJ_le_baum T haJ
  have haX₁ : a ∈ Subgroup.normalizer (s.X₁ : Set G) := hS₁ haS
  have haX₂ : a ∈ Subgroup.normalizer (s.X₂ : Set G) := hS₂ haS
  obtain ⟨u, huTI, hu₁, hu₂⟩ := c.exists_swap' hyp h12
  set N := pCoreOf 2 s.X with hNdef
  set Q₁ := pCoreOf 2 s.X₁ with hQ₁def
  set Q₂ := pCoreOf 2 s.X₂ with hQ₂def
  have hQ₁N : Q₁ ≤ N := s.pCoreOf_le_pCoreOf_X s.X₁_le_X s.X_le_normalizer_X₁
  have hQ₂N : Q₂ ≤ N := s.pCoreOf_le_pCoreOf_X s.X₂_le_X s.X_le_normalizer_X₂
  have huQ₁ : Q₁.map (MulAut.conj u).toMonoidHom = Q₂ := by
    rw [hQ₁def, ← pCoreOf_map_equiv, hu₁]
  have huQ₂ : Q₂.map (MulAut.conj u).toMonoidHom = Q₁ := by
    rw [hQ₂def, ← pCoreOf_map_equiv, hu₂]
  have hconj_mem : ∀ {A B : Subgroup G}, A.map (MulAut.conj u).toMonoidHom = B →
      ∀ x ∈ A, u * x * u⁻¹ ∈ B := by
    intro A B h x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hconj_mem' : ∀ {A B : Subgroup G}, A.map (MulAut.conj u).toMonoidHom = B →
      ∀ x ∈ B, u⁻¹ * x * u ∈ A := by
    intro A B h x hx
    rw [← h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hy
  set b := u * a * u⁻¹ with hbdef
  have hbTI : b ∈ T ⊓ I₀ := (T ⊓ I₀).mul_mem ((T ⊓ I₀).mul_mem huTI haTI) ((T ⊓ I₀).inv_mem huTI)
  have hcen₁ : ∀ x ∈ s.X₁, b * x * b⁻¹ * x⁻¹ ∈ Q₁ := by
    intro x hx
    have h1 := hcen₂ _ (hconj_mem' hu₂ x hx)
    have h2 := hconj_mem huQ₂ _ h1
    have e : u * (a * (u⁻¹ * x * u) * a⁻¹ * (u⁻¹ * x * u)⁻¹) * u⁻¹ = b * x * b⁻¹ * x⁻¹ := by
      rw [hbdef]; group
    rwa [e] at h2
  have hinv₂ : ∀ x ∈ s.X₂, b * x * b⁻¹ * x ∈ Q₂ := by
    intro x hx
    have h1 := hinv₁ _ (hconj_mem' hu₁ x hx)
    have h2 := hconj_mem huQ₁ _ h1
    have e : u * (a * (u⁻¹ * x * u) * a⁻¹ * (u⁻¹ * x * u)) * u⁻¹ = b * x * b⁻¹ * x := by
      rw [hbdef]; group
    rwa [e] at h2
  set g := a * b with hgdef
  have hgTI : g ∈ T ⊓ I₀ := (T ⊓ I₀).mul_mem haTI hbTI
  have hQ₂n : ∀ x ∈ s.X₂, ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₂ := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.X₂ hx) q).mp hq
  have haQ₁ : ∀ q ∈ Q₁, a * q * a⁻¹ ∈ Q₁ := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.X₁ haX₁) q).mp hq
  have haQ₂ : ∀ q ∈ Q₂, a * q * a⁻¹ ∈ Q₂ := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.X₂ haX₂) q).mp hq
  have hg₁ : ∀ x ∈ s.X₁, g * x * g⁻¹ * x ∈ Q₁ := by
    intro x hx
    set n := b * x * b⁻¹ * x⁻¹ with hn
    have e : g * x * g⁻¹ * x = (a * n * a⁻¹) * (a * x * a⁻¹ * x) := by rw [hgdef, hn]; group
    rw [e]
    exact Q₁.mul_mem (haQ₁ n (hcen₁ x hx)) (hinv₁ x hx)
  have hg₂ : ∀ x ∈ s.X₂, g * x * g⁻¹ * x ∈ Q₂ := by
    intro x hx
    set n := b * x * b⁻¹ * x with hn
    set m := a * x * a⁻¹ * x⁻¹ with hm
    have e : g * x * g⁻¹ * x = (a * n * a⁻¹) * (x⁻¹ * m⁻¹ * x⁻¹⁻¹) := by
      rw [hgdef, hn, hm]; group
    rw [e]
    refine Q₂.mul_mem (haQ₂ n (hinv₂ x hx)) ?_
    exact hQ₂n _ (s.X₂.inv_mem hx) _ (Q₂.inv_mem (hcen₂ x hx))
  have hcommX : ∀ x₁ ∈ s.X₁, ∀ x₂ ∈ s.X₂, x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ N := by
    intro x₁ hx₁ x₂ hx₂
    have h1 : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ s.X₂ :=
      s.X₂.mul_mem ((Subgroup.mem_normalizer_iff.mp
        (s.X_le_normalizer_X₂ (s.X₁_le_X hx₁)) x₂).mp hx₂) (s.X₂.inv_mem hx₂)
    have h2 : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ s.X₁ := by
      have h3 : x₂ * x₁⁻¹ * x₂⁻¹ ∈ s.X₁ := (Subgroup.mem_normalizer_iff.mp
        (s.X_le_normalizer_X₁ (s.X₂_le_X hx₂)) x₁⁻¹).mp (s.X₁.inv_mem hx₁)
      have e : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ = x₁ * (x₂ * x₁⁻¹ * x₂⁻¹) := by group
      rw [e]
      exact s.X₁.mul_mem hx₁ h3
    have hC : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ Subgroup.centralizer
        ((⁅VZ T s.M₁, s.X₁⁆ : Subgroup G) : Set G) := s.X₂_le_centralizer_V₁ h1
    obtain ⟨-, hO₁, -, hi₁, -, -, -, hc₁, -⟩ := s.dataX
    have hVN : s.M₁ ≤ Subgroup.normalizer (VZ T s.M₁ : Set G) := le_normalizer_conjClosure _ _
    exact hQ₁N (inf_centralizer_commutator_le_pCoreOf (s.isElemAbelian_VZ hyp)
      ((s.X₁_le_X.trans s.le_X).trans hVN) hO₁ hi₁ hc₁ ⟨h2, hC⟩)
  refine ⟨g, hgTI, fun x hx => ?_⟩
  have hx' : x ∈ s.X₁ ⊔ s.X₂ := hX ▸ hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer
    (s.X₂_le_X.trans s.X_le_normalizer_X₁)).1 hx'
  set n₁ := g * x₁ * g⁻¹ * x₁ with hn₁
  set n₂ := g * x₂ * g⁻¹ * x₂ with hn₂
  have hn₁N : n₁ ∈ N := hQ₁N (hg₁ x₁ hx₁)
  have hn₂N : n₂ ∈ N := hQ₂N (hg₂ x₂ hx₂)
  have hNn : ∀ y ∈ s.X, ∀ q ∈ N, y * q * y⁻¹ ∈ N := fun y hy q hq =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.X hy) q).mp hq
  have hx₁X := s.X₁_le_X hx₁
  have hx₂X := s.X₂_le_X hx₂
  have e : g * (x₁ * x₂) * g⁻¹ * (x₁ * x₂) =
      n₁ * (x₁⁻¹ * n₂ * x₁⁻¹⁻¹) * (x₁⁻¹ * x₂⁻¹ * x₁⁻¹⁻¹ * x₂⁻¹⁻¹) := by
    rw [hn₁, hn₂]; group
  rw [e]
  exact N.mul_mem (N.mul_mem hn₁N (hNn _ (s.X.inv_mem hx₁X) _ hn₂N))
    (hcommX _ (s.X₁.inv_mem hx₁) _ (s.X₂.inv_mem hx₂))

end Config15420

end CFSG.Quasithin.EmptyFaithfulMultiple
