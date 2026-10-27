module

public import CFSG.Quasithin.Vol2.Ch11SecGOdd1
public import CFSG.Quasithin.Vol2.Ch11SecG556Key
public import CFSG.Quasithin.Vol2.Ch11SecD556O

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem kOne_le (L V₁ : Subgroup G) (p : ℕ) :
    oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ≤ KOf L V₁ V₁ :=
  sup_le (SecD.oTwoPrime_le _ p) (le_conjClosure _ _)

theorem T_le_normalizer_kOne (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (p : ℕ) :
    T ≤ Subgroup.normalizer ((oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ : Subgroup G) : Set G) := by
  have hTN := SecA.IsVi.le_normalizer hV₁
  exact SecD.le_normalizer_sup ((hTN.trans (SecD.normalizer_le_normalizer_kOf L V₁ V₁)).trans
    (SecD.normalizer_le_normalizer_oTwoPrime _ p))
    (fun t ht => SecD.mem_normalizer_lOf (h.normal ht) (hTN ht))

omit [Finite G] in
theorem h1p_le_normalizer {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (p : ℕ) :
    oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
  sup_le ((kOne_le L V₁ p).trans Subgroup.le_normalizer)
    ((SecA.IsVi.le_normalizer hV₁).trans (SecD.normalizer_le_normalizer_kOf L V₁ V₁))

theorem le_normalizer_kOne (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (p : ℕ) :
    oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T ≤
      Subgroup.normalizer ((oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ : Subgroup G) : Set G) :=
  sup_le Subgroup.le_normalizer (T_le_normalizer_kOne h hV₁ p)

theorem isSylowTwoOf_h1p (h : Hyp11 G T L I n) (V₁ : Subgroup G) (p : ℕ) :
    QuasithinUnique.IsSylowTwoOf T (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) :=
  isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right

theorem mem_pCoreOf_prime (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF2 : ∀ y ∈ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁,
      (∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) →
        y ∈ oTwoPrime (KOf L V₁ V₁) p)
    {a : G} (ha : a ∈ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) {e : ℕ} (hae : a ^ 2 ^ e = 1)
    (hc : ∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) :
    a ∈ pCoreOf 2 (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) :=
  mem_pCoreOf_of_centralizes hp hp2 (SecD.pCoreOf_le_oTwoPrime _ p) le_sup_left (kOne_le L V₁ p)
    (fun _ hx => SecD.exists_pow_mem_pCoreOf_of_mem_oTwoPrime hx)
    ((h1p_le_normalizer hV₁ p).trans (SecD.normalizer_le_normalizer_oTwoPrime _ p))
    (h1p_le_normalizer hV₁ p) le_sup_left (le_normalizer_kOne h hV₁ p)
    (isSylowTwoOf_h1p h V₁ p) rfl hF2 ha hae hc

theorem le_pCoreOf_prime (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF2 : ∀ y ∈ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁,
      (∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) →
        y ∈ oTwoPrime (KOf L V₁ V₁) p)
    {X : Subgroup G} (hXH : X ≤ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T)
    (hX2 : IsPGroup 2 X)
    (hc : ∀ a ∈ X, ∀ x ∈ oTwoPrime (KOf L V₁ V₁) p,
      a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) :
    X ≤ pCoreOf 2 (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) :=
  le_pCoreOf_of_centralizes hp hp2 (SecD.pCoreOf_le_oTwoPrime _ p) le_sup_left (kOne_le L V₁ p)
    (fun _ hx => SecD.exists_pow_mem_pCoreOf_of_mem_oTwoPrime hx)
    ((h1p_le_normalizer hV₁ p).trans (SecD.normalizer_le_normalizer_oTwoPrime _ p))
    (h1p_le_normalizer hV₁ p) le_sup_left (le_normalizer_kOne h hV₁ p)
    (isSylowTwoOf_h1p h V₁ p) rfl hF2 hXH hX2 hc

theorem inf_conjSub_eq_bot_prime (hTI : SecD.PointsTIFact) (hPt : PointConjFact)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2)
    (h1151 : Stmt11_5_1) (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF2 : ∀ y ∈ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁,
      (∀ x ∈ oTwoPrime (KOf L V₁ V₁) p, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (KOf L V₁ V₁)) →
        y ∈ oTwoPrime (KOf L V₁ V₁) p)
    {g : G} (hgO : ¬ fsuV T I ≤ conjSub g (pCoreOf 2 (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T)))
    (hU : ∃ k ∈ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T,
      conjClosure (fsuV T I) (oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T) ≤
        conjSub (g * k) (ROf T L V₁)) :
    V₁ ⊓ conjSub g V₁ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set P := oTwoPrime K p with hPdef
  set Q := pCoreOf 2 K with hQdef
  set H₁ := P ⊔ LOf L V₁ ⊔ T with hH₁def
  set U := conjClosure (fsuV T I) H₁ with hUdef
  by_contra hne
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hKg := conjSub_kOf_eq_of_mem hTI hPt h331 h1102 h1141 h1142 h1151 h hV₁ hzmem.1 hzmem.2
    hz1'
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSub_eq hKg
  have hgP : g ∈ Subgroup.normalizer (P : Set G) := SecD.normalizer_le_normalizer_oTwoPrime K p hgK
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hgK
  obtain ⟨k, hk, hUk⟩ := hU
  have hH₁K := h1p_le_normalizer hV₁ p
  have hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le ((kOne_le L V₁ p).trans (SecD.kOf_le_normalizer (SecD.lOf_le_normalizer L V₁)))
      (SecA.IsVi.le_normalizer hV₁)
  have hU2 : IsPGroup 2 U := F7.isPGroup_of_isElemAbelian (isElemAbelian_U_of_le h1157 h hV₁ hH₁N)
  have hUg : U ≤ conjSub g H₁ := by
    have hTH : T ≤ H₁ := le_sup_right
    have h1 : conjSub (g * k) (ROf T L V₁) ≤ conjSub g H₁ := by
      rw [conjSub_mul]
      exact conjSub_mono g ((conjSub_mono k ((SecD.ROf_le_T h V₁).trans hTH)).trans
        (F7.conjSub_eq_of_mem hk).le)
    exact hUk.trans h1
  have hUP : ∀ u ∈ U, ∀ x ∈ P, u * x * u⁻¹ * x⁻¹ ∈ Q := by
    intro u hu x hx
    have huK : u ∈ Subgroup.normalizer (K : Set G) := by
      have h1 := conjSub_le_normalizer (g := g) hH₁K
      rw [hKg] at h1
      exact h1 (hUg hu)
    have huP := SecD.normalizer_le_normalizer_oTwoPrime K p huK
    have hPH : P ≤ H₁ := le_sup_left.trans le_sup_left
    have hxH : x ∈ H₁ := hPH hx
    have hcP : u * x * u⁻¹ * x⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp huP x).mp hx) (P.inv_mem hx)
    have hcU : u * x * u⁻¹ * x⁻¹ ∈ U := by
      have h1 : x * u⁻¹ * x⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hxH) _).mp (U.inv_mem hu)
      have e : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
      rw [e]
      exact U.mul_mem hu h1
    obtain ⟨j, hj⟩ := hU2 ⟨_, hcU⟩
    exact SecD.mem_pCoreOf_of_mem_oTwoPrime hp hp2 hcP (k := j)
      (by simpa using congrArg Subtype.val hj)
  have hXH : conjSub g⁻¹ U ≤ H₁ := by
    rw [conjSub_le_iff, inv_inv]
    exact hUg
  have hX : conjSub g⁻¹ U ≤ pCoreOf 2 H₁ := by
    refine le_pCoreOf_prime h hV₁ hp hp2 hF2 hXH (F7.isPGroup_conjSub hU2) fun a ha x hx => ?_
    rw [mem_conjSub, inv_inv] at ha
    have hx' : g * x * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hgP x).mp hx
    have h1 := hUP _ ha _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgQ) _).mp h1
    convert h2 using 1
    group
  apply hgO
  have h1 := conjSub_mono g hX
  rw [conjSub_inv_conjSub] at h1
  exact (le_conjClosure _ _).trans h1

end CFSG.Quasithin.Vol2.Ch11.SecG
