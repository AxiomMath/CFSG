module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_pow_mul_of_commutator {H : Type*} [Group H] {x y c : H} (hyx : y * x = x * y * c)
    (hcy : Commute c y) (n : ℕ) : y ^ n * x = x * y ^ n * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (x * y ^ n * c ^ n) := by rw [ih]
      _ = (y * x) * y ^ n * c ^ n := by simp only [mul_assoc]
      _ = x * y * c * y ^ n * c ^ n := by rw [hyx]
      _ = x * y * (c * y ^ n) * c ^ n := by simp only [mul_assoc]
      _ = x * y * (y ^ n * c) * c ^ n := by rw [(hcy.pow_right n).eq]
      _ = x * y ^ (n + 1) * c ^ (n + 1) := by
        rw [pow_succ' y n, pow_succ' c n]; simp only [mul_assoc]

theorem uc22p22u_mul_pow_of_commutator {H : Type*} [Group H] {x y c : H} (hyx : y * x = x * y * c)
    (hcx : Commute c x) (hcy : Commute c y) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * c ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hck : Commute (c ^ n.choose 2) x := hcx.pow_left _
    have hcky : Commute (c ^ n.choose 2) y := hcy.pow_left _
    have hcc : Commute (c ^ n * c ^ n.choose 2) y := (hcy.pow_left n).mul_left hcky
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * c ^ n.choose 2 * (x * y) := by rw [ih]
      _ = x ^ n * y ^ n * (c ^ n.choose 2 * x) * y := by simp only [mul_assoc]
      _ = x ^ n * y ^ n * (x * c ^ n.choose 2) * y := by rw [hck.eq]
      _ = x ^ n * (y ^ n * x) * c ^ n.choose 2 * y := by simp only [mul_assoc]
      _ = x ^ n * (x * y ^ n * c ^ n) * c ^ n.choose 2 * y := by
        rw [uc22p22u_pow_mul_of_commutator hyx hcy n]
      _ = x ^ (n + 1) * y ^ n * (c ^ n * c ^ n.choose 2) * y := by
        rw [pow_succ x n]; simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ n * y * (c ^ n * c ^ n.choose 2) := by
        rw [mul_assoc _ (c ^ n * c ^ n.choose 2) y, hcc.eq, ← mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + 1).choose 2 := by
        have hch : (n + 1).choose 2 = n + n.choose 2 := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right]
        rw [hch, pow_add c, pow_succ y n]
        simp only [mul_assoc]

theorem uc22p22u_omega1p_exponent {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) (hcl : ⁅⁅R, R⁆, R⁆ = ⊥) : ∀ x ∈ F11.Omega1p p R, x ^ p = 1 := by
  have _ := hR
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hmul : ∀ x ∈ R, x ^ p = 1 → ∀ y ∈ R, y ^ p = 1 → (x * y) ^ p = 1 := by
    intro x hx hx1 y hy hy1
    set c := (x * y)⁻¹ * (y * x) with hc
    have hyx : y * x = x * y * c := by rw [hc]; group
    have hcR : c ∈ ⁅R, R⁆ := by
      have h := Subgroup.commutator_mem_commutator (R.inv_mem hy) (R.inv_mem hx)
      convert h using 1
      rw [hc, commutatorElement_def]; group
    have hcen : ∀ g ∈ R, Commute c g := by
      intro g hg
      have hmem : ⁅c, g⁆ ∈ ⁅⁅R, R⁆, R⁆ := Subgroup.commutator_mem_commutator hcR hg
      rw [hcl, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.1 hmem
    have hcx := hcen x hx
    have hcy := hcen y hy
    have hcp : c ^ p = 1 := by
      have h := uc22p22u_pow_mul_of_commutator hyx hcy p
      rw [hy1, one_mul, mul_one] at h
      exact mul_eq_left.1 h.symm
    rw [uc22p22u_mul_pow_of_commutator hyx hcx hcy p, hx1, hy1, one_mul, one_mul]
    obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero hp3
    rw [hk, pow_mul, hcp, one_pow]
  intro x hx
  have key : x ∈ R ∧ x ^ p = 1 := by
    refine Subgroup.closure_induction (p := fun x _ => x ∈ R ∧ x ^ p = 1) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨hxR, hx1⟩
      exact ⟨hxR, hx1⟩
    · exact ⟨R.one_mem, one_pow p⟩
    · rintro x y - - ⟨hxR, hx1⟩ ⟨hyR, hy1⟩
      exact ⟨R.mul_mem hxR hyR, hmul x hxR hx1 y hyR hy1⟩
    · rintro x - ⟨hxR, hx1⟩
      exact ⟨R.inv_mem hxR, by rw [inv_pow, hx1, inv_one]⟩
  exact key.2

theorem uc22p22u_card_le_mul_card_centralizer {Y Y₁ : Subgroup G} (hcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥)
    (hY₁ : Y₁ ≤ Y) {s : G} (hs : s ∈ Y) :
    Nat.card Y₁ ≤ Nat.card ↥⁅Y, Y⁆ * Nat.card ↥(Y₁ ⊓ centralizer ({s} : Set G)) := by
  have hcen : ∀ c ∈ ⁅Y, Y⁆, ∀ g ∈ Y, g * c = c * g := by
    intro c hc g hg
    have hmem : ⁅c, g⁆ ∈ ⁅⁅Y, Y⁆, Y⁆ := Subgroup.commutator_mem_commutator hc hg
    rw [hcl, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
  have hYY : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le.2 fun a ha b hb =>
    Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  let φ : ↥Y₁ →* ↥⁅Y, Y⁆ :=
    { toFun := fun a => ⟨⁅(a : G), s⁆, Subgroup.commutator_mem_commutator (hY₁ a.2) hs⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ⁅(a : G) * b, s⁆ = ⁅(a : G), s⁆ * ⁅(b : G), s⁆
        have hb : ⁅(b : G), s⁆ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator (hY₁ b.2) hs
        have ha : ⁅(a : G), s⁆ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator (hY₁ a.2) hs
        have h1 : (a : G) * ⁅(b : G), s⁆ = ⁅(b : G), s⁆ * a := hcen _ hb a (hY₁ a.2)
        have h2 : ⁅(b : G), s⁆ * ⁅(a : G), s⁆ = ⁅(a : G), s⁆ * ⁅(b : G), s⁆ :=
          hcen _ ha _ (hYY hb)
        calc ⁅(a : G) * b, s⁆ = (a : G) * ⁅(b : G), s⁆ * (a : G)⁻¹ * ⁅(a : G), s⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅(b : G), s⁆ * ⁅(a : G), s⁆ := by rw [h1]; group
          _ = ⁅(a : G), s⁆ * ⁅(b : G), s⁆ := h2) }
  have hker : φ.ker = (centralizer ({s} : Set G)).subgroupOf Y₁ := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : ⁅(a : G), s⁆ = 1 := congrArg Subtype.val h
      exact commutatorElement_eq_one_iff_mul_comm.1 h'
    · intro h
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.2 h)
  have h1 : Nat.card Y₁ = Nat.card φ.ker * Nat.card φ.range := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
  have h2 : Nat.card φ.range ≤ Nat.card ↥⁅Y, Y⁆ := Subgroup.card_le_card_group _
  have h3 : Nat.card φ.ker = Nat.card ↥(Y₁ ⊓ centralizer ({s} : Set G)) := by
    rw [hker, ← Subgroup.card_map_of_injective Y₁.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem uc22p22u_card_le_pow_pRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup G}
    (hexp : ∀ y ∈ Y, y ^ p = 1) (hcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥) (hY' : Nat.card ↥⁅Y, Y⁆ ≤ p) (hne : Y ≠ ⊥) :
    Nat.card Y ≤ p ^ (2 * CFSG.Open.pRank p Y - 1) := by
  have _ := hp2
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, hEY, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 Y
  set m := CFSG.Open.pRank p Y
  have hpow : ∀ B : Subgroup G, B ≤ E → ∃ i, Nat.card B = p ^ i := fun B hB => by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (hEcard ▸ Subgroup.card_dvd_of_le hB)
    exact ⟨i, hi⟩
  have hmax : ∀ y ∈ Y, (∀ e ∈ E, y * e = e * y) → y ∈ E := by
    intro y hy hc
    have hEy : IsElemAbelian p (E ⊔ zpowers y) :=
      IsElemAbelian.sup_of_commute hE (isElemAbelian_zpowers (hexp y hy)) fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        have hay : Commute a y := (hc a ha).symm
        exact (hay.zpow_right k).eq
    have hle : E ⊔ zpowers y ≤ Y := sup_le hEY (Subgroup.zpowers_le.2 hy)
    obtain ⟨k, hk⟩ := hEy.isPGroup.exists_card_eq
    have hkm : k ≤ m := CFSG.SectionRank.le_pRank hp1 hle hEy hk
    have hcard : Nat.card (E ⊔ zpowers y : Subgroup G) ≤ Nat.card E := by
      rw [hk, hEcard]
      exact Nat.pow_le_pow_right hp.pos hkm
    have hEq : E ⊔ zpowers y = E := (Subgroup.eq_of_le_of_card_ge le_sup_left hcard).symm
    rw [← hEq]
    exact mem_sup_right (mem_zpowers y)
  have hCE : Y ⊓ centralizer (E : Set G) = E := by
    refine le_antisymm (fun y hy => hmax y hy.1 fun e he => ?_) fun e he =>
      ⟨hEY he, Subgroup.mem_centralizer_iff.2 fun a ha => (hE.comm he ha).symm⟩
    exact (mem_centralizer_iff.1 hy.2 e he).symm
  set Z : Subgroup G := Y ⊓ centralizer (Y : Set G)
  have hZE : Z ≤ E := fun z hz =>
    hmax z hz.1 fun e he => (mem_centralizer_iff.1 hz.2 e (hEY he)).symm
  have hpZ : p ≤ Nat.card Z := by
    haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hne
    have hYp : IsPGroup p ↥Y := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
    haveI := hYp.center_nontrivial
    obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center ↥Y)
    have hzZ : (z : G) ∈ Z := ⟨z.2, mem_centralizer_iff.2 fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨g, hg⟩)⟩
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    have hord : orderOf (z : G) = p := orderOf_eq_prime (hexp z z.2) hz1'
    have := Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hzZ)
    rwa [Nat.card_zpowers, hord] at this
  have hind : ∀ B : Subgroup G, B ≤ E →
      Nat.card ↥(Y ⊓ centralizer (B : Set G)) * Nat.card B ≤ Nat.card E ^ 2 := by
    intro B
    induction B using WellFoundedGT.induction with
    | _ B ih =>
      intro hBE
      by_cases hBeq : B = E
      · rw [hBeq, hCE, pow_two]
      · obtain ⟨s, hsE, hsB⟩ : ∃ s ∈ E, s ∉ B :=
          IsConcreteLE.not_le_iff_exists.1 fun h => hBeq (le_antisymm hBE h)
        have hB'E : B ⊔ zpowers s ≤ E := sup_le hBE (Subgroup.zpowers_le.2 hsE)
        have hBB' : B < B ⊔ zpowers s := lt_of_le_of_ne le_sup_left fun h =>
          hsB (h ▸ mem_sup_right (mem_zpowers s))
        have ih' := ih _ hBB' hB'E
        obtain ⟨i, hi⟩ := hpow B hBE
        obtain ⟨j, hj⟩ := hpow _ hB'E
        have hlt : Nat.card B < Nat.card ↥(B ⊔ zpowers s) := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) fun h => ?_
          exact hBB'.ne (Subgroup.eq_of_le_of_card_ge le_sup_left h.symm.le)
        have hij : i < j := by
          rw [hi, hj] at hlt
          exact (Nat.pow_lt_pow_iff_right hp1).1 hlt
        have hge : p * Nat.card B ≤ Nat.card ↥(B ⊔ zpowers s) := by
          rw [hi, hj, ← pow_succ']
          exact Nat.pow_le_pow_right hp.pos hij
        have h1 := uc22p22u_card_le_mul_card_centralizer hcl
          (inf_le_left : Y ⊓ centralizer (B : Set G) ≤ Y) (hEY hsE)
        have h2 : Y ⊓ centralizer (B : Set G) ⊓ centralizer ({s} : Set G) ≤
            Y ⊓ centralizer ((B ⊔ zpowers s : Subgroup G) : Set G) := by
          intro x hx
          have hxB : ∀ b ∈ B, b * x = x * b := fun b hb => mem_centralizer_iff.1 hx.1.2 b hb
          have hxs : s * x = x * s := mem_centralizer_iff.1 hx.2 s rfl
          have hle : B ⊔ zpowers s ≤ centralizer ({x} : Set G) := sup_le
            (fun b hb => Subgroup.mem_centralizer_iff.2 fun h hh => by
              rw [Set.mem_singleton_iff.1 hh]; exact (hxB b hb).symm)
            (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => by
              rw [Set.mem_singleton_iff.1 hh]; exact hxs.symm))
          exact ⟨hx.1.1, Subgroup.mem_centralizer_iff.2 fun g hg =>
            (mem_centralizer_iff.1 (hle hg) x rfl).symm⟩
        have h3 := Subgroup.card_le_of_le h2
        calc Nat.card ↥(Y ⊓ centralizer (B : Set G)) * Nat.card B
            ≤ (Nat.card ↥⁅Y, Y⁆ * Nat.card ↥(Y ⊓ centralizer (B : Set G) ⊓
                centralizer ({s} : Set G))) * Nat.card B := Nat.mul_le_mul_right _ h1
          _ ≤ (p * Nat.card ↥(Y ⊓ centralizer ((B ⊔ zpowers s : Subgroup G) : Set G))) *
                Nat.card B := Nat.mul_le_mul_right _ (Nat.mul_le_mul hY' h3)
          _ = Nat.card ↥(Y ⊓ centralizer ((B ⊔ zpowers s : Subgroup G) : Set G)) *
                (p * Nat.card B) := by ring
          _ ≤ Nat.card ↥(Y ⊓ centralizer ((B ⊔ zpowers s : Subgroup G) : Set G)) *
                Nat.card ↥(B ⊔ zpowers s) := Nat.mul_le_mul_left _ hge
          _ ≤ Nat.card E ^ 2 := ih'
  have hZ' := hind Z hZE
  have hYZ : Y ⊓ centralizer (Z : Set G) = Y := by
    refine le_antisymm inf_le_left fun y hy => ⟨hy, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    exact (mem_centralizer_iff.1 hz.2 y hy).symm
  rw [hYZ] at hZ'
  have hm1 : 1 ≤ m := by
    have h := hpZ.trans (Subgroup.card_le_of_le hZE)
    rw [hEcard] at h
    exact (Nat.pow_le_pow_iff_right hp1).1 (by simpa using h)
  have hfin : p * Nat.card Y ≤ p ^ (2 * m - 1 + 1) := by
    have h1 : Nat.card Y * p ≤ Nat.card Y * Nat.card Z := Nat.mul_le_mul_left _ hpZ
    have h2 : (Nat.card E) ^ 2 = p ^ (2 * m - 1 + 1) := by
      rw [hEcard, ← pow_mul]
      congr 1
      omega
    calc p * Nat.card Y = Nat.card Y * p := mul_comm _ _
      _ ≤ Nat.card Y * Nat.card Z := h1
      _ ≤ Nat.card E ^ 2 := hZ'
      _ = p ^ (2 * m - 1 + 1) := h2
  rw [pow_succ'] at hfin
  exact Nat.le_of_mul_le_mul_left hfin hp.pos

theorem uc22p22u_exists_noncyclic_critical {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    [Finite Q] (hQ : IsPGroup p Q) (hnc : ¬ IsCyclic Q) :
    ∃ D : Subgroup Q, D.Characteristic ∧ ¬ IsCyclic ↥D ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ⁅D, (⊤ : Subgroup Q)⁆ ≤ D ⊓ centralizer (D : Set Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial Q := Nontrivial.of_not_isCyclic hnc
  obtain ⟨D, hDc, hD1, hDexp, hDZ, htors, -⟩ := CFSG.SectionRank.Ccomm.supercritical_witness hp2 hQ
  refine ⟨D, hDc, fun hDcyc => ?_, hDexp, hDZ⟩
  have hdvd : Nat.card D ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hDexp x x.2)
  have hDcard : Nat.card D = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq D h) hD1
    · exact h
  haveI : Fact (IsPGroup p Q) := ⟨hQ⟩
  have hDcen : D ≤ Subgroup.center Q := CFSG.normal_subgroup_card_eq_prime_le_center D hDcard
  obtain ⟨S, -, hScard, hS⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hSel : IsElemAbelian p S := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hS
  have hSD : S ≤ D := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact D.one_mem
    · refine htors x (Subgroup.mem_centralizer_iff.2 fun d hd => ?_) (orderOf_eq_prime (hSel.2 x hx) hx1)
      exact ((Subgroup.mem_center_iff.1 (hDcen hd)) x).symm
  have hle := Subgroup.card_le_of_le hSD
  rw [hScard, hDcard] at hle
  have := hp.one_lt
  nlinarith

theorem uc22p22u_exists_elemAbelian_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic ↥R) :
    ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p ↥R) := ⟨hR⟩
  obtain ⟨S, -, hScard, hS⟩ := CFSG.lemma_4_5_a (R := ↥R) hp2 hnc
  have hSel : IsElemAbelian p S := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hS
  refine ⟨S.map R.subtype, Subgroup.map_subtype_le S, hSel.map R.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective R.subtype_injective, hScard]

theorem uc22p22u_two_le_pRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic ↥R) : 2 ≤ CFSG.Open.pRank p R := by
  obtain ⟨E, hER, hE, hEcard⟩ := uc22p22u_exists_elemAbelian_sq hp hp2 hR hnc
  exact CFSG.SectionRank.le_pRank hp.one_lt hER hE hEcard

end CFSG.LocalAnalysis.UniquenessCase.UC22
