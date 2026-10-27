module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixLift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem conjN_eq_self_of_diag {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t v : Fin d → K}
    (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    conjN D hD s = s := by
  refine Subtype.ext ?_
  rw [coe_conjN]
  have hcomm : D * (s : GL (Fin d) K) = (s : GL (Fin d) K) * D := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hDt, hs]
    exact Matrix.commute_diagonal t v
  rw [hcomm]
  group

private theorem commute_of_diag {K : Type} [Field K]
    {x y : ↥(unitarySU 2 1 K 6)}
    (hx : ∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v)
    (hy : ∃ v : Fin 6 → K, ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) :
    Commute x y := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨w, hw⟩ := hy
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hv, hw]
  exact Matrix.commute_diagonal v w

private theorem exists_pow_pow_mul_eq_one {G : Type*} [Group G] {p : ℕ} {a b : G}
    (h : Commute a b) (ha : ∃ k : ℕ, a ^ p ^ k = 1) (hb : ∃ k : ℕ, b ^ p ^ k = 1) :
    ∃ k : ℕ, (a * b) ^ p ^ k = 1 := by
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  refine ⟨max ka kb, ?_⟩
  rw [h.mul_pow (p ^ max ka kb)]
  have h1 : a ^ p ^ max ka kb = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr hka).trans (pow_dvd_pow p (le_max_left ka kb)))
  have h2 : b ^ p ^ max ka kb = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr hkb).trans (pow_dvd_pow p (le_max_right ka kb)))
  rw [h1, h2, mul_one]

private theorem isPGroup_closure_of_commute_pow {G : Type*} [Group G] {p : ℕ} {s : Set G}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, Commute x y)
    (hpow : ∀ x ∈ s, ∃ k : ℕ, x ^ p ^ k = 1) :
    IsPGroup p (Subgroup.closure s) := by
  have hpair : s.Pairwise Commute := by
    intro x hx y hy _
    exact hcomm x hx y hy
  haveI : IsMulCommutative (Subgroup.closure s) := Subgroup.isMulCommutative_closure hpair
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  have hg : ∃ k : ℕ, (g : G) ^ p ^ k = 1 := by
    refine Subgroup.closure_induction (p := fun x _ => ∃ k : ℕ, x ^ p ^ k = 1)
      (fun x hx => hpow x hx) ⟨0, by simp⟩ ?_ ?_ g.2
    · intro a b ha hb ia ib
      obtain ⟨ka, hka⟩ := ia
      obtain ⟨kb, hkb⟩ := ib
      have hcab : Commute a b := by
        have hmul : (⟨a, ha⟩ : Subgroup.closure s) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
          mul_comm' _ _
        exact Subtype.ext_iff.mp hmul
      exact exists_pow_pow_mul_eq_one hcab ⟨ka, hka⟩ ⟨kb, hkb⟩
    · intro a ha ia
      obtain ⟨ka, hka⟩ := ia
      refine ⟨ka, ?_⟩
      rw [inv_pow, hka, inv_one]
  obtain ⟨k, hk⟩ := hg
  exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩

private theorem lift_commute {p : ℕ} {L' : Type} [Group L'] (Z : Subgroup L') [Z.Normal]
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) {a b : L'}
    (ha : ∃ k : ℕ, orderOf a = p ^ k) (hb : ∃ k : ℕ, orderOf b = p ^ k)
    (hcomm : Commute ((QuotientGroup.mk' Z) a) ((QuotientGroup.mk' Z) b)) :
    Commute a b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcZ : a * b * a⁻¹ * b⁻¹ ∈ Z := by
    have h1 : (QuotientGroup.mk' Z) (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, (commute_iff_eq _ _).mp hcomm]
      group
    rw [← QuotientGroup.ker_mk' Z]
    exact MonoidHom.mem_ker.mpr h1
  obtain ⟨hc_center, hc2⟩ := (hZ (a * b * a⁻¹ * b⁻¹)).mp hcZ
  have hcb : Commute (a * b * a⁻¹ * b⁻¹) b :=
    ((Subgroup.mem_center_iff.mp hc_center) b).symm
  have hconj : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
  have hc_pow : ∃ k : ℕ, (a * b * a⁻¹ * b⁻¹) ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hb
    refine ⟨k, ?_⟩
    have hsem : SemiconjBy a b (a * b * a⁻¹) := by
      show a * b = (a * b * a⁻¹) * a
      group
    have ho : orderOf (a * b * a⁻¹) = p ^ k :=
      (SemiconjBy.orderOf_eq a hsem).symm.trans hk
    have h1 : (a * b * a⁻¹) ^ p ^ k = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    have h2 : ((a * b * a⁻¹ * b⁻¹) * b) ^ p ^ k = 1 := by rw [← hconj]; exact h1
    have hb1 : b ^ p ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one b
    rw [hcb.mul_pow (p ^ k), hb1, mul_one] at h2
    exact h2
  obtain ⟨j, hj⟩ := hc2
  obtain ⟨l, hl⟩ := hc_pow
  have hcop2p : Nat.Coprime 2 p :=
    ((hp.coprime_iff_not_dvd).mpr fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)).symm
  have hcop : Nat.Coprime (2 ^ j) (p ^ l) := Nat.Coprime.pow j l hcop2p
  have hgcd : (2 ^ j).gcd (p ^ l) = 1 := hcop
  have hpow : (a * b * a⁻¹ * b⁻¹) ^ ((2 ^ j).gcd (p ^ l)) = 1 :=
    pow_gcd_eq_one.mpr ⟨hj, hl⟩
  rw [hgcd, pow_one] at hpow
  have h2 : a * b * a⁻¹ = b := mul_inv_eq_one.mp hpow
  show a * b = b * a
  calc a * b = (a * b * a⁻¹) * a := by group
    _ = b * a := by rw [h2]

private theorem isPGroup_two_of_hZ {L' : Type} [Group L'] {Z : Subgroup L'}
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1) :
    IsPGroup 2 ↥Z := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro z
  obtain ⟨k, hk⟩ := ((hZ (z : L')).mp z.2).2
  exact ⟨k, Subtype.ext (by simp only [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩

private theorem not_dvd_card_of_isPGroup_two {Z : Type*} [Group Z] [Finite Z]
    (hZ2 : IsPGroup 2 Z) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hpdvd
  obtain ⟨m, hm⟩ := hZ2.exists_card_eq
  have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow (hm ▸ hpdvd)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2)

private theorem mem_of_map_of_pElement {p : ℕ} {L' G : Type} [Group L'] [Group G] [Finite L']
    (π : L' →* G) (Z : Subgroup L') [Z.Normal]
    (hker : π.ker = Z)
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Subgroup L') {u : G} (hu : u ∈ K.map π) {ℓ' : L'}
    (hℓ' : π ℓ' = u) (hpow : ∃ k : ℕ, orderOf ℓ' = p ^ k) :
    ℓ' ∈ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hkK, hkπ⟩ := Subgroup.mem_map.mp hu
  let πK : K →* G := π.comp K.subtype
  have hkerK : ∀ x : πK.ker, (((x : K) : L')) ∈ Z := by
    intro x
    have hx : πK (x : K) = 1 := x.2
    change π (((x : K) : L')) = 1 at hx
    rw [← hker, MonoidHom.mem_ker]
    exact hx
  have hK2 : IsPGroup 2 πK.ker := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨m, hm⟩ := ((hZ (((x : K) : L'))).mp (hkerK x)).2
    refine ⟨m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, hm, Subgroup.coe_one]
  have hCK : ¬ p ∣ Nat.card πK.ker := not_dvd_card_of_isPGroup_two hK2 hp hp2
  have hπKk : πK ⟨k, hkK⟩ = u := by
    change π k = u
    exact hkπ
  obtain ⟨n, hn⟩ := CFSG.LieType.CentralExt.exists_orderOf_map_eq_pow (p := p) π hpow
  have hn' : orderOf (πK ⟨k, hkK⟩) = p ^ n := by rw [hπKk, ← hℓ', hn]
  obtain ⟨x, hxπ, m, hm⟩ :=
    CFSG.LieType.CentralExt.exists_pElement_lift (π := πK) hCK ⟨k, hkK⟩ hn'
  have hx_eq : ((x : K) : L') = ℓ' := by
    refine CFSG.LieType.CentralExt.eq_of_pElement (π := π) ?_ ?_ ?_ ?_ hpow
    · rw [hker]
      intro z hz
      exact ((hZ z).mp hz).1
    · rw [hker]
      exact not_dvd_card_of_isPGroup_two (isPGroup_two_of_hZ hZ) hp hp2
    · rw [show π ((x : K) : L') = πK x from rfl, hxπ, hπKk]
      exact hℓ'.symm
    · exact ⟨m, (Subgroup.orderOf_coe x).trans hm⟩
  simpa only [hx_eq] using x.2

theorem pLift_block_torus_props
    {p : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] [Finite M] {L' E J' : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE) (hp : p.Prime)
    (hp2 : p ≠ 2) (Z : Subgroup L') [Z.Normal]
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    {φ : ↥(unitarySU 2 1 K 6) →* L' ⧸ Z}
    (hdiag : ∀ e : E, ∃ (t : Fin 6 → K) (D : GL (Fin 6) K)
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        (D : Matrix (Fin 6) (Fin 6) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K 6)) (l : L'), (QuotientGroup.mk l : L' ⧸ Z) = φ s →
          (QuotientGroup.mk (L'.normalizerMonoidHom ⟨e, hE e.2⟩ l) : L' ⧸ Z) =
            φ (conjN D hD s))
    (I₀ : Finset (Fin 6)) (hJL : J' ≤ L')
    (hJ : (J'.subgroupOf L').map (QuotientGroup.mk' Z) =
      (TableBUE.blockSU (K := K) (n := 1) I₀).map φ)
    (S : Subgroup M)
    (hS : S = Subgroup.closure {ℓ : M | ∃ ℓ' : L', (ℓ' : M) = ℓ ∧ (∃ k : ℕ, orderOf ℓ' = p ^ k) ∧
      ∃ x ∈ TableBUE.blockSU (K := K) (n := 1) I₀,
        (∃ v : Fin 6 → K, ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal v) ∧
        (QuotientGroup.mk ℓ' : L' ⧸ Z) = φ x}) :
    IsPGroup p S ∧ S ≤ J' ∧ S ≤ Subgroup.centralizer (E : Set M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ2 : IsPGroup 2 ↥Z := isPGroup_two_of_hZ hZ
  have hCker : ¬ p ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    exact not_dvd_card_of_isPGroup_two hZ2 hp hp2
  have hcen : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact ((hZ z).mp hz).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]
    refine isPGroup_closure_of_commute_pow ?_ ?_
    · intro ℓ₁ h₁ ℓ₂ h₂
      obtain ⟨ℓ₁', hℓ₁'eq, hℓ₁'pow, x₁, hx₁mem, hx₁diag, hπ₁⟩ := h₁
      obtain ⟨ℓ₂', hℓ₂'eq, hℓ₂'pow, x₂, hx₂mem, hx₂diag, hπ₂⟩ := h₂
      have hxy : Commute x₁ x₂ := commute_of_diag hx₁diag hx₂diag
      have hπcomm : Commute ((QuotientGroup.mk' Z) ℓ₁') ((QuotientGroup.mk' Z) ℓ₂') := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hπ₁, hπ₂]
        exact hxy.map φ
      have hcommL : Commute ℓ₁' ℓ₂' := lift_commute Z hZ hp hp2 hℓ₁'pow hℓ₂'pow hπcomm
      rw [← hℓ₁'eq, ← hℓ₂'eq]
      exact hcommL.map L'.subtype
    · intro ℓ hℓ
      obtain ⟨ℓ', hℓ'eq, hℓ'pow, x, hxmem, hxdiag, hπ⟩ := hℓ
      obtain ⟨k, hk⟩ := hℓ'pow
      refine ⟨k, ?_⟩
      have h1 : ℓ' ^ p ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one ℓ'
      rw [← hℓ'eq]
      show (L'.subtype ℓ') ^ p ^ k = 1
      rw [← map_pow L'.subtype ℓ' (p ^ k), h1, map_one]
  · rw [hS]
    rw [Subgroup.closure_le]
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ'eq, hℓ'pow, x, hxmem, hxdiag, hπ⟩ := hℓ
    have hℓ'J : ℓ' ∈ J'.subgroupOf L' := by
      refine mem_of_map_of_pElement (QuotientGroup.mk' Z) Z (QuotientGroup.ker_mk' Z) hZ hp hp2
        (J'.subgroupOf L') (u := φ x) ?_ ?_ hℓ'pow
      · rw [hJ]
        exact Subgroup.mem_map.mpr ⟨x, hxmem, rfl⟩
      · rw [QuotientGroup.mk'_apply]
        exact hπ
    have hmemJ : (ℓ' : M) ∈ J' := Subgroup.mem_subgroupOf.mp hℓ'J
    rwa [← hℓ'eq]
  · rw [hS]
    rw [Subgroup.closure_le]
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ'eq, hℓ'pow, x, hxmem, hxdiag, hπ⟩ := hℓ
    obtain ⟨k, hk⟩ := hℓ'pow
    intro e he
    obtain ⟨t, D, hD, hDt, hact⟩ := hdiag ⟨e, he⟩
    obtain ⟨v, hv⟩ := hxdiag
    have hconjfix : conjN D hD x = x := conjN_eq_self_of_diag D hD hDt x hv
    have hadiag := hact x ℓ' hπ
    rw [hconjfix] at hadiag
    have horderL : orderOf (L'.normalizerMonoidHom ⟨e, hE he⟩ ℓ') = orderOf ℓ' := by
      have hsem : SemiconjBy e (ℓ' : M) (e * (ℓ' : M) * e⁻¹) := by
        show e * (ℓ' : M) = (e * (ℓ' : M) * e⁻¹) * e
        group
      have horderM : orderOf (((L'.normalizerMonoidHom ⟨e, hE he⟩ ℓ' : L')) : M) =
          orderOf (ℓ' : M) := by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact (SemiconjBy.orderOf_eq e hsem).symm
      exact (Subgroup.orderOf_coe _).symm.trans (horderM.trans (Subgroup.orderOf_coe _))
    have hnorm_eq : L'.normalizerMonoidHom ⟨e, hE he⟩ ℓ' = ℓ' := by
      refine CFSG.LieType.CentralExt.eq_of_pElement (π := QuotientGroup.mk' Z) hcen hCker ?_ ?_ ⟨k, hk⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hadiag, hπ]
      · exact ⟨k, horderL.trans hk⟩
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE he⟩ ℓ'
    have hidx : e * (ℓ' : M) * e⁻¹ = (ℓ' : M) := by
      rw [← hcoe, hnorm_eq]
    have hidx' : e * (ℓ' : M) = (ℓ' : M) * e := by
      calc e * (ℓ' : M) = (e * (ℓ' : M) * e⁻¹) * e := by group
        _ = (ℓ' : M) * e := by rw [hidx]
    rw [← hℓ'eq]
    exact hidx'

end CFSG.StandardType
