module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypes
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Res5Types

section Rigid

variable {X : Type*} [Group X]

theorem pow_apply_ne_of_cube {τ : MulAut X} {a : X} (h3 : (τ ^ 3) a = a) (h1 : τ a ≠ a)
    (h2 : (τ ^ 2) a ≠ a) {n : ℕ} (hn : ¬ 3 ∣ n) : (τ ^ n) a ≠ a := by
  have hk : ∀ m r : ℕ, (τ ^ (3 * m + r)) a = (τ ^ r) a := by
    intro m r
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 3 * (m + 1) + r = 3 + (3 * m + r) by ring, pow_add, MulAut.mul_apply, ih]
      rw [show (τ ^ 3) ((τ ^ r) a) = (τ ^ r) ((τ ^ 3) a) by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm], h3]
  have hn' : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hr : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [hn', hk]
  rcases hr with hr | hr <;> rw [hr]
  · simpa using h1
  · exact h2

theorem fix_klein {τ : MulAut X} {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : τ ^ n = 1) {a b t : X}
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) (hτt : τ t = t) (hta : t * a * t⁻¹ = a * b) (htb : t * b * t⁻¹ = a)
    (hτa : τ a = 1 ∨ τ a = a ∨ τ a = b ∨ τ a = a * b) : τ a = a ∧ τ b = b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hconj : ∀ v, τ (t * v * t⁻¹) = t * τ v * t⁻¹ := fun v => by
    rw [map_mul, map_mul, map_inv, hτt]
  have hτab : τ (a * b) = t * τ a * t⁻¹ := by rw [← hta, hconj]
  have hτb : τ b = (τ a)⁻¹ * τ (a * b) := by rw [map_mul]; group
  have hτa1 : τ a ≠ 1 := fun h => ha1 (τ.injective (h.trans (map_one τ).symm))
  rcases hτa with h | h | h | h
  · exact absurd h hτa1
  · refine ⟨h, ?_⟩
    rw [hτb, hτab, h, hta, hainv, ← mul_assoc, haa, one_mul]
  · exfalso
    have h2 : τ (a * b) = a := by rw [hτab, h, htb]
    have h3 : τ b = a * b := by rw [hτb, h, h2, hbinv, hab]
    have hpow2 : (τ ^ 2) a = a * b := by rw [pow_two, MulAut.mul_apply, h, h3]
    have hpow3 : (τ ^ 3) a = a := by
      rw [pow_succ, MulAut.mul_apply, h, pow_two, MulAut.mul_apply, h3, h2]
    have hfix : (τ ^ n) a = a := by rw [hτn, MulAut.one_apply]
    refine pow_apply_ne_of_cube hpow3 (by rw [h]; exact hne.symm) ?_ hn hfix
    rw [hpow2]
    intro h'
    apply hb1
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h', inv_mul_cancel]
  · exfalso
    have h2 : τ (a * b) = b := by
      rw [hτab, h, ← mul_assoc, show t * a * b = (t * a * t⁻¹) * (t * b * t⁻¹) * t by group,
        hta, htb, mul_assoc a b a, ← hab, ← mul_assoc, haa, one_mul, mul_assoc, mul_inv_cancel,
        mul_one]
    have h3 : τ b = a := by
      rw [hτb, h, h2, mul_inv_rev, hbinv, hainv]
      calc b * a * b = a * b * b := by rw [← hab]
        _ = a := by rw [mul_assoc, hbb, mul_one]
    have hpow2 : (τ ^ 2) a = b := by rw [pow_two, MulAut.mul_apply, h, h2]
    have hpow3 : (τ ^ 3) a = a := by
      rw [pow_succ, MulAut.mul_apply, h, pow_two, MulAut.mul_apply, h2, h3]
    have hfix : (τ ^ n) a = a := by rw [hτn, MulAut.one_apply]
    refine pow_apply_ne_of_cube hpow3 ?_ (by rw [hpow2]; exact hne.symm) hn hfix
    rw [h]
    intro h'
    apply hb1
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h', inv_mul_cancel]

theorem fix_four {τ : MulAut X} {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : τ ^ n = 1) {V : Subgroup X}
    {a b t : X} (hV : ∀ v, v ∈ V ↔ v = 1 ∨ v = a ∨ v = b ∨ v = a * b)
    (hτV : ∀ v ∈ V, τ v ∈ V) (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hτt : τ t = t) (hta : t * a * t⁻¹ = a * b)
    (htb : t * b * t⁻¹ = a) : ∀ v ∈ V, τ v = v := by
  have hτa := (hV _).mp (hτV a ((hV a).mpr (Or.inr (Or.inl rfl))))
  obtain ⟨h1, h2⟩ := fix_klein hn hτn haa hbb hab ha1 hb1 hne hτt hta htb hτa
  intro v hv
  rcases (hV v).mp hv with rfl | rfl | rfl | rfl
  · exact map_one τ
  · exact h1
  · exact h2
  · rw [map_mul, h1, h2]

@[expose] def fixSubgroup (τ : MulAut X) : Subgroup X where
  carrier := {g | τ g = g}
  mul_mem' := fun {x y} hx hy => by
    change τ (x * y) = x * y
    rw [map_mul, show τ x = x from hx, show τ y = y from hy]
  one_mem' := map_one τ
  inv_mem' := fun {x} hx => by
    change τ x⁻¹ = x⁻¹
    rw [map_inv, show τ x = x from hx]

theorem mem_fixSubgroup {τ : MulAut X} {g : X} : g ∈ fixSubgroup τ ↔ τ g = g := Iff.rfl

theorem eq_one_of_top_le_fixSubgroup {τ : MulAut X} (h : ⊤ ≤ fixSubgroup τ) : τ = 1 :=
  MulEquiv.ext fun g => h (Subgroup.mem_top g)

theorem map_theta_centralizer_eq [Finite X] {τ : MulAut X} {e : X} (he : τ e = e) :
    (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set X))).map
        τ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set X)) := by
  rw [Sec6.map_inSubgroup_theta_of_injective τ.toMonoidHom τ.injective,
    CFSG.RankThree.PartTwo.map_centralizer_singleton τ e, he]

end Rigid

theorem exists_equiv_map_eq_of_conj {X Γ : Type*} [Group X] [Group Γ] [Finite Γ] (φ : X ≃* Γ)
    {E : Subgroup X} {P : Subgroup Γ} {g : Γ} (hg : ∀ x ∈ E, ∃ p ∈ P, g * p * g⁻¹ = φ x)
    (hcard : Nat.card P ≤ Nat.card E) : ∃ φ' : X ≃* Γ, E.map φ'.toMonoidHom = P := by
  refine ⟨φ.trans (MulAut.conj g)⁻¹, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hpx⟩ := hg x hx
    change g⁻¹ * φ x * g ∈ P
    rw [← hpx]
    simpa [mul_assoc] using hp
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hcard

theorem exists_equiv_map_eq {X Γ : Type*} [Group X] [Group Γ] [Finite Γ] (φ : X ≃* Γ)
    {E : Subgroup X} {P : Subgroup Γ} (hP : Nat.card P = 9) (hE : Nat.card E = 9)
    (hfac : (Nat.card Γ).factorization 3 = 2) : ∃ φ' : X ≃* Γ, E.map φ'.toMonoidHom = P := by
  obtain ⟨g, hg⟩ := Res5Gen.exists_conj_mem_of_card hP (E' := E.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hE]) hfac
  exact exists_equiv_map_eq_of_conj φ (fun x hx => hg (φ x) ⟨x, hx, rfl⟩) (by rw [hP, hE])

variable {G : Type} [Group G] [Finite G]

theorem cent_of_rigid
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Γ : Type*} [Group Γ] (φ' : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* Γ) {P : Subgroup Γ}
    (hφ'E : (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map φ'.toMonoidHom = P)
    (hrigid : ∀ τ : MulAut Γ, (∀ p ∈ P, τ p = p) → ∀ n : ℕ, ¬ 3 ∣ n → τ ^ n = 1 → τ = 1) :
    ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  intro r hr l hl
  have hrA : r ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr
  have hrc : r ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A) hrA
  have hrN : r ∈ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h h3L hrc
  set σ := Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨r, hrN⟩) with hσ
  have hσE : ∀ e ∈ Eb, σ e = e := by
    rintro _ ⟨β, hβ, rfl⟩
    have hβA : (β : G) ∈ A := (Subgroup.mem_subgroupOf.mp hβ).1
    have hrβ : r * (β : G) * r⁻¹ = β := by
      rw [← Subgroup.mem_centralizer_iff.mp hrA _ hβA]
      group
    change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨r, hrN⟩ β) = QuotientGroup.mk' θ β
    congr 1
    exact Subtype.ext hrβ
  set n := orderOf r with hn
  have hn3 : ¬ 3 ∣ n := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.orderOf_dvd_natCard _ hr))
  have hσn : σ ^ n = 1 := by
    have h1 : (⟨r, hrN⟩ : Subgroup.normalizer (L : Set G)) ^ n = 1 :=
      Subtype.ext (by simp [hn, pow_orderOf_eq_one])
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  set τ := MulAut.congr φ' σ with hτ
  have hτP : ∀ p ∈ P, τ p = p := by
    intro p hp
    rw [← hφ'E] at hp
    obtain ⟨e, he, rfl⟩ := hp
    change φ' (σ (φ'.symm (φ' e))) = φ' e
    rw [MulEquiv.symm_apply_apply, hσE e he]
  have hτn : τ ^ n = 1 := by rw [hτ, ← map_pow, hσn, map_one]
  have hσ1 : σ = 1 :=
    (MulAut.congr φ').injective ((hrigid τ hτP n hn3 hτn).trans (map_one _).symm)
  have h1 := congrArg (fun f : MulAut (↥L ⧸ θ) => f (QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩))
    hσ1
  change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨r, hrN⟩ ⟨l⁻¹, inv_mem hl⟩) =
    QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩ at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  refine ⟨_, h1, ?_⟩
  simp [commutatorElement_def, mul_assoc]

namespace Inner142

variable {A L : Subgroup G} {c : G} (d : Inner142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem thetaCA_eq_bot
    (hC : IsPGroup 3 (Subgroup.centralizer
      ((((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
        Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))) :
    thetaCA142 A (lB A) c = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := img142 A (lB A) c (k142 A (lB A) c) ⊓
    Subgroup.centralizer (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))
    with hW
  have hWL : W ≤ img142 A (lB A) c L := inf_le_left.trans d.img_k.le
  have hWb : d.bar W ≤ Subgroup.centralizer
      ((((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
        Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    rw [SetLike.mem_coe, ← d.bar_A] at he
    obtain ⟨a, ha, rfl⟩ := he
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hw' := (Subgroup.mem_subgroupOf.mp hw).2
    have ha' := Subgroup.mem_subgroupOf.mp ha
    exact (Subgroup.mem_centralizer_iff.mp hw' _ ha')
  have hWp : IsPGroup 3 W := by
    obtain ⟨e⟩ := d.nonempty_bar_equiv hWL
    exact (hC.to_le hWb).of_equiv e.symm
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥W)
    Nat.prime_three
  have hθp : IsPGroup 3 (aschbacherSolvableCore 3 ↥W) := hWp.to_subgroup _
  obtain ⟨k, hk⟩ := hθp.exists_card_eq
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exact absurd (hk ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)) hθ3
  have hbot : aschbacherSolvableCore 3 ↥W = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  rw [thetaCA142, ← hW, inSubgroup, hbot, Subgroup.map_bot]

theorem typesOne_of_model {Γ : Type*} [Group Γ] [Finite Γ]
    (φ' : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* Γ) {P : Subgroup Γ}
    (hφ'E : (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map φ'.toMonoidHom = P)
    {ι : Type*} (V : ι → Subgroup Γ) (e : ι → Γ) (heP : ∀ i, e i ∈ P) (he1 : ∀ i, e i ≠ 1)
    (hθV : ∀ i, inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({e i} : Set Γ)) = V i)
    (hV3 : ∀ i, ¬ 3 ∣ Nat.card (V i)) (hVN : ∀ i, P ≤ Subgroup.normalizer (V i : Set Γ))
    (hle : ∀ Y : Subgroup Γ, ¬ 3 ∣ Nat.card Y → P ≤ Subgroup.normalizer (Y : Set Γ) →
      ∃ i, Y ≤ V i)
    (hCP : IsPGroup 3 (Subgroup.centralizer (P : Set Γ))) {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  obtain ⟨hQL, hQ3, hQE, hQmax⟩ := d.maximal_bar hQ
  set Qb := d.bar (img142 A (lB A) c Q) with hQb
  set Y := Qb.map φ'.toMonoidHom with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hY, Subgroup.card_map_of_injective φ'.injective]
    exact hQ3
  have hEbP : Eb = P.map φ'.symm.toMonoidHom := by
    rw [← hφ'E, Subgroup.map_map]
    ext x
    simp
  have hYP : P ≤ Subgroup.normalizer (Y : Set Γ) := by
    rw [← hφ'E, hY, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hQE
  have hYmax : ∀ Y' : Subgroup Γ, ¬ 3 ∣ Nat.card Y' →
      P ≤ Subgroup.normalizer (Y' : Set Γ) → Y ≤ Y' → Y' = Y := by
    intro Y' h3 hP hle'
    have hY'' := hQmax (Y'.map φ'.symm.toMonoidHom)
      (by rwa [Subgroup.card_map_of_injective φ'.symm.injective]) (by
        change Eb ≤ _
        rw [hEbP, ← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.map_mono hP) (by
        intro x hx
        exact ⟨φ' x, hle' ⟨x, hx, rfl⟩, by simp⟩)
    rw [hY, ← hY'', Subgroup.map_map]
    ext x
    simp
  obtain ⟨i, hi⟩ := hle Y hY3 hYP
  have hYi : V i = Y := hYmax (V i) (hV3 i) (hVN i) hi
  obtain ⟨β, hβ, hβi⟩ : ∃ β : G, ∃ hβ : β ∈ A ⊓ L,
      φ' (QuotientGroup.mk' θ ⟨β, hβ.2⟩) = e i := by
    have hk : e i ∈ Eb.map φ'.toMonoidHom := hφ'E ▸ heP i
    obtain ⟨x, hx, hxe⟩ := hk
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨b, Subgroup.mem_subgroupOf.mp hb, hxe⟩
  have hid : φ'.symm.toMonoidHom.comp φ'.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => φ'.symm_apply_apply x
  have hθβ : d.bar (thetaC142 A (lB A) c (alpha142 A (lB A) c β hβ.1)) =
      (V i).map φ'.symm.toMonoidHom := by
    rw [(d.thetaC_bar β hβ).2, ← hθV i, ← hβi,
      ← CFSG.RankThree.PartTwo.map_centralizer_singleton φ',
      ← Sec6.map_inSubgroup_theta_of_injective φ'.toMonoidHom φ'.injective, Subgroup.map_map,
      hid, Subgroup.map_id]
  have hQbV : Qb = (V i).map φ'.symm.toMonoidHom := by
    rw [hYi, hY, Subgroup.map_map]
    ext x
    simp
  have hCA : thetaCA142 A (lB A) c = ⊥ := by
    refine d.thetaCA_eq_bot ?_
    have h1 : (Subgroup.centralizer (Eb : Set (↥L ⧸ θ))).map φ'.toMonoidHom ≤
        Subgroup.centralizer (P : Set Γ) := by
      refine (Subgroup.map_centralizer_le_centralizer_image _ _).trans ?_
      rw [← Subgroup.coe_map, hφ'E]
    exact (hCP.to_le h1).of_equiv
      ((Subgroup.centralizer (Eb : Set (↥L ⧸ θ))).equivMapOfInjective _ φ'.injective).symm
  have halpha_mem : alpha142 A (lB A) c β hβ.1 ∈ img142 A (lB A) c L :=
    ⟨⟨β, Subgroup.mem_sup_right hβ.1⟩, Subgroup.mem_subgroupOf.mpr hβ.2, rfl⟩
  have halpha_bar : d.lbarEquiv.symm ⟨alpha142 A (lB A) c β hβ.1, halpha_mem⟩ =
      QuotientGroup.mk' θ ⟨β, hβ.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (d.lbarEquiv_mk ⟨β, hβ.2⟩).symm
  refine ⟨β, hβ.1, fun h1 => he1 i ?_, ?_⟩
  · have h2 : (⟨alpha142 A (lB A) c β hβ.1, halpha_mem⟩ : ↥(img142 A (lB A) c L)) = 1 :=
      Subtype.ext h1
    rw [← hβi, ← halpha_bar, h2, map_one, map_one]
  · rw [hCA, sup_bot_eq]
    refine d.bar_injective hQL (d.thetaC_bar β hβ).1 ?_
    rw [← hQb, hQbV, hθβ]

end Inner142

end Res5Types

end CFSG.RankThree.PartTwo.Sec14
