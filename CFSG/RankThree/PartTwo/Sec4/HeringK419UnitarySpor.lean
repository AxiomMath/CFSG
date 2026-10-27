module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofUnitary
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.Sporadic.ON.Simple
public import CFSG.Sporadic.Ru
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.J1
import CFSG.Sporadic.J2
import CFSG.Sporadic.J3
import CFSG.Sporadic.J4
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.HS
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.Schreier.J4SSylowBase
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace HeringUnitarySpor

theorem ker_eq_center {L S : Type*} [Group L] [Group S] (hL : CFSG.IsQuasisimple L)
    [IsSimpleGroup S] (hS : ∃ x y : S, x * y ≠ y * x) (π : L →* S)
    (hπ : Function.Surjective π) : π.ker = Subgroup.center L := by
  obtain ⟨-, hsimp, -⟩ := hL
  have hZS : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hS
      apply hxy
      have hx : x ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top x
      exact ((Subgroup.mem_center_iff.mp hx) y).symm
  have hle : Subgroup.center L ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hπz : π z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨g, rfl⟩ := hπ s
      have key : g * z = z * g := (Subgroup.mem_center_iff.mp hz) g
      calc π g * π z = π (g * z) := (map_mul π g z).symm
        _ = π (z * g) := by rw [key]
        _ = π z * π g := map_mul π z g
    rw [hZS] at hπz
    exact Subgroup.mem_bot.mp hπz
  have hK : π.ker ≤ Subgroup.center L := by
    have hMn : (Subgroup.map (QuotientGroup.mk' (Subgroup.center L)) π.ker).Normal :=
      Subgroup.Normal.map (MonoidHom.normal_ker π) (QuotientGroup.mk' (Subgroup.center L))
        (QuotientGroup.mk'_surjective (Subgroup.center L))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.map (QuotientGroup.mk' (Subgroup.center L)) π.ker) with hbot | htop
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
      exact hbot
    · exfalso
      obtain ⟨x, y, hxy⟩ := hS
      apply hxy
      have hcov : ∀ g : L, ∃ z ∈ Subgroup.center L, π g = π z := by
        intro g
        have hmem : QuotientGroup.mk' (Subgroup.center L) g ∈
            Subgroup.map (QuotientGroup.mk' (Subgroup.center L)) π.ker := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hmem
        obtain ⟨z, hz, hkz⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center L)).mp hkg
        refine ⟨z, hz, ?_⟩
        rw [← hkz, map_mul, MonoidHom.mem_ker.mp hk, one_mul]
      obtain ⟨g, rfl⟩ := hπ x
      obtain ⟨h, rfl⟩ := hπ y
      obtain ⟨z, hz, hgz⟩ := hcov g
      obtain ⟨z', -, hhz'⟩ := hcov h
      have hcomm : z * z' = z' * z := ((Subgroup.mem_center_iff.mp hz) z').symm
      have e1 : π g * π h = π (z * z') := by rw [hgz, hhz', map_mul]
      have e2 : π h * π g = π (z' * z) := by rw [hgz, hhz', map_mul]
      rw [e1, e2, hcomm]
  exact le_antisymm hK hle

private theorem eq_one_of_mod_center_conj_central {L : Type*} [Group L] {z : L}
    (hz : z ∈ Subgroup.center L) (x : L) : z * x * z⁻¹ = x := by
  have hx : x * z = z * x := Subgroup.mem_center_iff.mp hz x
  rw [← hx, mul_inv_cancel_right]

private theorem eq_one_of_mod_center_comm_twist {L : Type*} [Group L] {c d : L}
    (hc : c ∈ Subgroup.center L) (hd : d ∈ Subgroup.center L) (g k : L) :
    c * g * (d * k) * (c * g)⁻¹ * (d * k)⁻¹ = g * k * g⁻¹ * k⁻¹ := by
  have h1 : c * g * (d * k) * (c * g)⁻¹ = g * (d * k) * g⁻¹ := by
    calc c * g * (d * k) * (c * g)⁻¹ = c * (g * (d * k) * g⁻¹) * c⁻¹ := by group
      _ = g * (d * k) * g⁻¹ := eq_one_of_mod_center_conj_central hc _
  have h2 : g * (d * k) * g⁻¹ * (d * k)⁻¹ = g * k * g⁻¹ * k⁻¹ := by
    have e : g * (d * k) * g⁻¹ * (d * k)⁻¹ = d * (g * k * g⁻¹ * k⁻¹) * d⁻¹ := by
      calc g * (d * k) * g⁻¹ * (d * k)⁻¹ = (g * d) * k * g⁻¹ * k⁻¹ * d⁻¹ := by group
        _ = (d * g) * k * g⁻¹ * k⁻¹ * d⁻¹ := by rw [Subgroup.mem_center_iff.mp hd g]
        _ = d * (g * k * g⁻¹ * k⁻¹) * d⁻¹ := by group
    rw [e]
    exact eq_one_of_mod_center_conj_central hd _
  rw [h1]
  exact h2

theorem eq_one_of_mod_center {L : Type*} [Group L] (hperf : Group.IsPerfect L) (σ : MulAut L)
    (h : ∀ l, σ l * l⁻¹ ∈ Subgroup.center L) : σ = 1 := by
  let Fix : Subgroup L :=
    { carrier := {x | σ x = x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : σ a = a := ha
        have hb' : σ b = b := hb
        show σ (a * b) = a * b
        rw [map_mul, ha', hb']
      one_mem' := by
        show σ 1 = 1
        exact map_one σ
      inv_mem' := fun {a} ha => by
        have ha' : σ a = a := ha
        show σ a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  have memFix : ∀ x : L, x ∈ Fix ↔ σ x = x := fun x => Iff.rfl
  have hcomm : ∀ g k : L, σ (g * k * g⁻¹ * k⁻¹) = g * k * g⁻¹ * k⁻¹ := by
    intro g k
    obtain ⟨c, hc, hgc⟩ : ∃ c ∈ Subgroup.center L, σ g = c * g :=
      ⟨σ g * g⁻¹, h g, by group⟩
    obtain ⟨d, hd, hkd⟩ : ∃ d ∈ Subgroup.center L, σ k = d * k :=
      ⟨σ k * k⁻¹, h k, by group⟩
    simp only [map_mul, map_inv]
    rw [hgc, hkd]
    exact eq_one_of_mod_center_comm_twist hc hd g k
  have hle : commutator L ≤ Fix := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun g _ k _ => (memFix _).mpr (hcomm g k)
  have htop : (⊤ : Subgroup L) ≤ Fix := by
    rw [← hperf.commutator_eq_top]
    exact hle
  ext x
  have hx : x ∈ Fix := htop (Subgroup.mem_top x)
  rw [MulAut.one_apply]
  exact (memFix x).mp hx

theorem exists_descend {L S : Type*} [Group L] [Group S] (π : L →* S)
    (hπ : Function.Surjective π) (σ : MulAut L) (hker : ∀ x ∈ π.ker, σ x ∈ π.ker)
    (hker' : ∀ x ∈ π.ker, σ.symm x ∈ π.ker) : ∃ α : MulAut S, ∀ l, α (π l) = π (σ l) := by
  have key : ∀ τ : MulAut L, (∀ x ∈ π.ker, τ x ∈ π.ker) →
      ∀ l l' : L, π l = π l' → π (τ l) = π (τ l') := by
    intro τ hτ l l' h
    have h1 : l⁻¹ * l' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h2 := MonoidHom.mem_ker.mp (hτ _ h1)
    simp only [map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  have key2 : ∀ τ : MulAut L, (∀ x ∈ π.ker, τ x ∈ π.ker) → ∀ l : L,
      π (τ (Function.surjInv hπ (π l))) = π (τ l) :=
    fun τ hτ l => key τ hτ _ _ (Function.surjInv_eq hπ (π l))
  refine ⟨{ toFun := fun s => π (σ (Function.surjInv hπ s)),
            invFun := fun s => π (σ.symm (Function.surjInv hπ s)),
            left_inv := ?_,
            right_inv := ?_,
            map_mul' := ?_ }, fun l => key2 σ hker l⟩
  · intro s
    obtain ⟨l, rfl⟩ := hπ s
    dsimp only
    rw [key2 σ hker l, key2 σ.symm hker' (σ l), MulEquiv.symm_apply_apply]
  · intro s
    obtain ⟨l, rfl⟩ := hπ s
    dsimp only
    rw [key2 σ hker (σ.symm (Function.surjInv hπ (π l))), MulEquiv.apply_symm_apply,
      Function.surjInv_eq hπ (π l)]
  · intro s t
    obtain ⟨a, rfl⟩ := hπ s
    obtain ⟨b, rfl⟩ := hπ t
    rw [← map_mul π a b, key2 σ hker (a * b), key2 σ hker a, key2 σ hker b, map_mul σ a b,
      map_mul π (σ a) (σ b)]

theorem three_mul_card_dvd {S : Type*} [Group S] [Finite S] {T : Subgroup S}
    (hT : IsSimpleGroup T) (hTna : ∃ x y : T, x * y ≠ y * x) {y : S} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyT : ∀ t ∈ T, y * t = t * y) : 3 * Nat.card T ∣ Nat.card S := by
  have hyT' : y ∉ T := by
    intro hmem
    have hcne : Subgroup.center T ≠ ⊤ := by
      intro htop
      obtain ⟨x, z, hxz⟩ := hTna
      apply hxz
      have hx : x ∈ Subgroup.center T := by
        rw [htop]
        exact Subgroup.mem_top x
      exact ((Subgroup.mem_center_iff.mp hx) z).symm
    have hcb : Subgroup.center T = ⊥ :=
      (hT.eq_bot_or_eq_top_of_normal (Subgroup.center T)).resolve_right hcne
    have hyc : (⟨y, hmem⟩ : T) ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hyT g.1 g.2).symm
    rw [hcb, Subgroup.mem_bot] at hyc
    exact hy1 (congrArg Subtype.val hyc)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hinf : Subgroup.zpowers y ⊓ T = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers y ⊓ T : Subgroup S) ∣ Nat.card (Subgroup.zpowers y) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [Nat.card_zpowers, hord] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hle : Subgroup.zpowers y ⊓ T = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left
          (le_of_eq (by rw [h3, Nat.card_zpowers, hord]))
      have hyK : y ∈ Subgroup.zpowers y ⊓ T := by
        rw [hle]
        exact Subgroup.mem_zpowers y
      exact hyT' (Subgroup.mem_inf.mp hyK).2
  have hcomm : ∀ a ∈ Subgroup.zpowers y, ∀ t ∈ T, a * t = t * a := by
    intro a ha t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute y t from hyT t ht).zpow_left k).eq
  have key : ∀ a ∈ Subgroup.zpowers y, ∀ a' ∈ Subgroup.zpowers y, ∀ t ∈ T, ∀ t' ∈ T,
      (a * t) * (a' * t') = (a * a') * (t * t') := by
    intro a _ a' ha' t ht t' _
    have h1 : t * a' = a' * t := (hcomm a' ha' t ht).symm
    calc (a * t) * (a' * t') = a * ((t * a') * t') := by simp only [mul_assoc]
      _ = a * ((a' * t) * t') := by rw [h1]
      _ = (a * a') * (t * t') := by simp only [mul_assoc]
  let prodMap : (Subgroup.zpowers y) × T →* S :=
    { toFun := fun p => (p.1 : S) * (p.2 : S)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        exact (key _ p.1.2 _ q.1.2 _ p.2.2 _ q.2.2).symm }
  have hinj : Function.Injective prodMap := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, t⟩ h
    change (a : S) * (t : S) = 1 at h
    have ha_bot : (a : S) ∈ Subgroup.zpowers y ⊓ T := by
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      have hat : (a : S) = (t : S)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [hat]
      exact T.inv_mem t.2
    rw [hinf, Subgroup.mem_bot] at ha_bot
    rw [ha_bot, one_mul] at h
    exact Prod.ext (Subtype.ext ha_bot) (Subtype.ext h)
  have hcard : Nat.card (Subgroup.zpowers y × T) = 3 * Nat.card T := by
    rw [Nat.card_prod, Nat.card_zpowers, hord]
  have hdvd := Subgroup.card_dvd_of_injective prodMap hinj
  rw [hcard] at hdvd
  exact hdvd

theorem three_dvd_card_outer {S : Type*} [Group S] [Finite S] (α : MulAut S) (h3 : α ^ 3 = 1)
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S) :
    3 ∣ Nat.card (Outer S) := by
  have hq3 : (QuotientGroup.mk α : Outer S) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
  have hq1 : (QuotientGroup.mk α : Outer S) ≠ 1 := by
    intro h
    exact hα ((QuotientGroup.eq_one_iff α).mp h)
  have hord : orderOf (QuotientGroup.mk α : Outer S) = 3 :=
    orderOf_eq_prime hq3 hq1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk α : Outer S)
  rwa [hord] at hdvd

theorem exists_noncomm_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (h2 : 2 ∣ Nat.card S) (hn2 : Nat.card S ≠ 2) : ∃ x y : S, x * y ≠ y * x := by
  by_contra h
  push Not at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2
  have hN : (Subgroup.zpowers x).Normal := by
    refine ⟨fun g hg k => ?_⟩
    have hk : k * g * k⁻¹ = g := by rw [h k g, mul_inv_cancel_right]
    rw [hk]
    exact hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with hb | ht
  · have hx1 : x = 1 := by
      have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [hb, Subgroup.mem_bot] at this
      exact this
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · apply hn2
    rw [← Subgroup.card_top (G := S), ← ht, Nat.card_zpowers, hx]

theorem false_of_J4 {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G} {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G)))) {m : ℕ}
    (hm : Odd m) (e : K ≃* projSU 3 2 m)
    (hM : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ 86775571046077562880) : False := by
  obtain ⟨hm3, hdvd⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item419Res3.unitary_component_facts hKle hKc hm e
  have hKM : Nat.card (projSU 3 2 m) ∣ 86775571046077562880 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hdvd.trans hM
  have hodd : m % 2 = 1 := Nat.odd_iff.mp hm
  rcases (show m = 3 ∨ m = 5 ∨ m = 7 ∨ 9 ≤ m by omega) with rfl | rfl | rfl | h9
  · have h19 : 19 ∣ Nat.card (projSU 3 2 3) := by
      rw [CFSG.RankThree.PartTwo.Sec4.Item419Res3.card_projSU_three_two_three]
      norm_num
    exact (show ¬ (19 : ℕ) ∣ 86775571046077562880 by norm_num) (h19.trans hKM)
  · have h1 : 331 ∣ Nat.card (projSU 3 2 5) * 3 := by
      rw [CFSG.RankThree.PartTwo.Sec4.Item419Res3.card_projSU_three_two_mul_three hm]
      norm_num
    have h2 : 331 ∣ Nat.card (projSU 3 2 5) :=
      Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h1
    exact (show ¬ (331 : ℕ) ∣ 86775571046077562880 by norm_num) (h2.trans hKM)
  · have h1 : 127 ∣ Nat.card (projSU 3 2 7) * 3 := by
      rw [CFSG.RankThree.PartTwo.Sec4.Item419Res3.card_projSU_three_two_mul_three hm]
      norm_num
    have h2 : 127 ∣ Nat.card (projSU 3 2 7) :=
      Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h1
    exact (show ¬ (127 : ℕ) ∣ 86775571046077562880 by norm_num) (h2.trans hKM)
  · have h27 : 2 ^ 27 ∣ Nat.card (projSU 3 2 m) :=
      (pow_dvd_pow 2 (by omega : 27 ≤ 3 * m)).trans
        (CFSG.RankThree.PartTwo.Sec4.Item419Res3.two_pow_dvd_card_projSU_three_two hm)
    exact (show ¬ (2 : ℕ) ^ 27 ∣ 86775571046077562880 by norm_num) (h27.trans hKM)

theorem false_of_cover_generic {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hSna : ∃ x y : S, x * y ≠ y * x) (hdiv : ¬ 3 * 5515776 ∣ Nat.card S)
    (hout : ¬ 3 ∣ Nat.card (Outer S)) {L : Subgroup G} (hL : IsComponent L)
    (π : L →* S) (hπ : Function.Surjective π)
    {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (e : K ≃* projSU 3 2 3) : False := by
  classical
  have hZS : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hSna
      have hx : x ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)
  have hker : π.ker = Subgroup.center L := ker_eq_center hL.1 hSna π hπ
  let σ : MulAut L := L.normalizerMonoidHom ⟨a, haN⟩
  have hσ : ∀ l : L, ((σ l : L) : G) = a * l * a⁻¹ := fun l => rfl
  have hcen : ∀ (τ : MulAut L) (x : L), x ∈ Subgroup.center L → τ x ∈ Subgroup.center L := by
    intro τ x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have h1 := hx (τ.symm g)
    calc g * τ x = τ (τ.symm g * x) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = τ (x * τ.symm g) := by rw [h1]
      _ = τ x * g := by rw [map_mul, MulEquiv.apply_symm_apply]
  obtain ⟨α, hα⟩ := exists_descend π hπ σ
    (fun x hx => by rw [hker] at hx ⊢; exact hcen σ x hx)
    (fun x hx => by rw [hker] at hx ⊢; exact hcen σ.symm x hx)
  have hpow : ∀ n : ℕ, ∀ l : L, (α ^ n) (π l) = π ((σ ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp only [pow_zero, MulAut.one_apply]
    | succ n ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hα, ih]
  have hσ3 : σ ^ 3 = 1 := by
    have h3 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← ha3]
      exact pow_orderOf_eq_one a
    show (L.normalizerMonoidHom ⟨a, haN⟩) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  have hα3 : α ^ 3 = 1 := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨l, rfl⟩ := hπ s
    rw [hpow 3 l, hσ3, MulAut.one_apply, MulAut.one_apply]
  have hα1 : α ≠ 1 := by
    intro h1
    apply haC
    have hmod : ∀ l : L, σ l * l⁻¹ ∈ Subgroup.center L := by
      intro l
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hα, h1, MulAut.one_apply,
        mul_inv_cancel]
    have hσ1 := eq_one_of_mod_center hL.1.1 σ hmod
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 : ((σ ⟨l, hl⟩ : L) : G) = l := by rw [hσ1, MulAut.one_apply]
    rw [hσ] at h2
    calc l * a = a * l * a⁻¹ * a := by rw [h2]
      _ = a * l := by group
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKa : ∀ k ∈ K, a * k * a⁻¹ = k := fun k hk => by
    have := Subgroup.mem_centralizer_singleton_iff.mp ((hKle hk).2)
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]
  haveI hUs : IsSimpleGroup (projSU 3 2 3) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 3 (by norm_num) (by norm_num)
  haveI hKs : IsSimpleGroup K := e.isSimpleGroup
  have hKcard : Nat.card K = 5515776 := by
    rw [Nat.card_congr e.toEquiv]
    exact Item419Res3.card_projSU_three_two_three
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have hKna : ∃ x y : K, x * y ≠ y * x := by
    by_contra h
    push Not at h
    letI : CommGroup K := { (inferInstance : Group K) with mul_comm := h }
    have hp : (Nat.card K).Prime := IsSimpleGroup.prime_card
    rw [hKcard] at hp
    norm_num at hp
  let πK : K →* S := π.comp (Subgroup.inclusion hKL)
  have hπK : Function.Injective πK := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal πK.ker with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hKna
      apply hxy
      have hz : ∀ k : K, Subgroup.inclusion hKL k ∈ Subgroup.center L := fun k => by
        rw [← hker]
        have hk : k ∈ πK.ker := by rw [h]; exact Subgroup.mem_top k
        exact hk
      apply Subgroup.inclusion_injective hKL
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp (hz y) _
  let eT : K ≃* πK.range := MonoidHom.ofInjective hπK
  haveI hTs : IsSimpleGroup πK.range := eT.symm.isSimpleGroup
  have hTcard : Nat.card πK.range = 5515776 := by rw [← Nat.card_congr eT.toEquiv, hKcard]
  have hTna : ∃ x y : πK.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hKna
    exact ⟨eT x, eT y, fun h => hxy (eT.injective (by rw [map_mul, map_mul, h]))⟩
  have hαT : ∀ t ∈ πK.range, α t = t := by
    rintro _ ⟨k, rfl⟩
    show α (π (Subgroup.inclusion hKL k)) = π (Subgroup.inclusion hKL k)
    rw [hα]
    congr 1
    apply Subtype.ext
    rw [hσ]
    exact hKa k k.2
  by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S
  · obtain ⟨y, hy⟩ := hin
    have hyT : ∀ t ∈ πK.range, y * t = t * y := by
      intro t ht
      have h1 := hαT t ht
      rw [← hy, MulAut.conj_apply] at h1
      calc y * t = y * t * y⁻¹ * y := by group
        _ = t * y := by rw [h1]
    have hy3 : y ^ 3 = 1 := by
      have hc : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, hy, hα3]
      have hzc : y ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg (fun φ : MulAut S => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
          _ = y ^ 3 * g := by group
      rw [hZS, Subgroup.mem_bot] at hzc
      exact hzc
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hα1
      rw [← hy, map_one]
    have hdvd := three_mul_card_dvd hTs hTna hy3 hy1 hyT
    rw [hTcard] at hdvd
    exact hdiv hdvd
  · exact hout (three_dvd_card_outer α hα3 hin)

set_option maxRecDepth 20000 in
theorem false_of_ON_cover
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsComponent L)
    (hext : IsExtOf (L ⧸ aschbacherSolvableCore 3 L) NativeSporadic.ON (Multiplicative (ZMod 3)))
    {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (e : K ≃* projSU 3 2 3) : False := by
  obtain ⟨N, hNn, -, ⟨eQ⟩⟩ := hext
  haveI : IsSimpleGroup NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have hScard : Nat.card NativeSporadic.ON = 460815505920 := CFSG.Sporadic.ON.card_ON_eq
  haveI : Finite NativeSporadic.ON := Nat.finite_of_card_ne_zero (by rw [hScard]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer NativeSporadic.ON) := fun h3 =>
    absurd (Nat.dvd_trans h3 (CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four).1)
      (by norm_num)
  have h2 : 2 ∣ Nat.card NativeSporadic.ON := by rw [hScard]; norm_num
  have hn2 : Nat.card NativeSporadic.ON ≠ 2 := by rw [hScard]; norm_num
  have hSna := exists_noncomm_of_simple (S := NativeSporadic.ON) h2 hn2
  have hdiv : ¬ 3 * 5515776 ∣ Nat.card NativeSporadic.ON := by
    rw [hScard]
    norm_num
  exact false_of_cover_generic (S := NativeSporadic.ON) hSna hdiv hout hL
    (eQ.toMonoidHom.comp ((QuotientGroup.mk' N).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L))))
    (eQ.surjective.comp ((QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective _)))
    haN ha3 haC hKle e

end HeringUnitarySpor

section Main


set_option linter.unusedSectionVars false in
set_option maxRecDepth 20000 in
theorem k419UnitarySpor_holds :
    K419UnitarySpor := by
  intro G _ _ L hL h5 a haN ha3 haC K hKle hKc hm'
  obtain ⟨m, hm, ⟨e⟩⟩ := hm'
  exfalso
  have hm23 : Nat.card NativeSporadic.M23 = 10200960 :=
    (CFSG.Sporadic.Schreier.fam_m23_order).choose_spec.2.2.2.choose_spec.2.2.2.2
  have nine : ∀ M : ℕ, Nat.card (L ⧸ aschbacherSolvableCore 3 L) = M → ¬ 2 ^ 9 ∣ M → False :=
    fun M hM h9 =>
      Item419Res3.false_of_two_pow_nine hKle hKc hm e (M := M) ⟨1, by rw [hM, mul_one]⟩ h9
  have fifteen : ∀ M : ℕ, Nat.card (L ⧸ aschbacherSolvableCore 3 L) = M → ¬ 2 ^ 15 ∣ M →
      ¬ 19 ∣ M → False :=
    fun M hM h15 h19 =>
      Item419Res3.false_of_two_pow_fifteen hKle hKc hm e (M := M) ⟨1, by rw [hM, mul_one]⟩ h15 h19
  rcases h5 with ⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩
  · have hc : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = Nat.card (NativeSporadic.Carrier s) :=
      Nat.card_congr φ.toEquiv
    simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact nine 7920 (hc.trans CFSG.Sporadic.Mathieu.card_M11) (by norm_num)
    · exact nine 95040 (hc.trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM12) (by norm_num)
    · exact nine 443520 (hc.trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22) (by norm_num)
    · exact nine 10200960 (hc.trans hm23) (by norm_num)
    · exact fifteen 244823040 (hc.trans CFSG.Sporadic.Mathieu.card_M24) (by norm_num) (by norm_num)
    · exact nine 175560 (hc.trans CFSG.Sporadic.J1.card_J1) (by norm_num)
    · exact nine 604800 (hc.trans CFSG.Sporadic.J2.card_J2) (by norm_num)
    · exact nine 50232960 (hc.trans CFSG.Sporadic.J3.card_J3) (by norm_num)
    · exact HeringUnitarySpor.false_of_J4 hKle hKc hm e ⟨1, by
        rw [hc, show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
          CFSG.Sporadic.J4.card_J4, mul_one]⟩
    · exact nine 898128000 (hc.trans CFSG.Sporadic.McL.card_McL) (by norm_num)
    · exact fifteen 44352000 (hc.trans CFSG.Sporadic.HS.card_HS) (by norm_num) (by norm_num)
    · exact fifteen 4030387200 (hc.trans CFSG.Sporadic.He.card_He) (by norm_num) (by norm_num)
    · exact fifteen 145926144000 (hc.trans CFSG.Sporadic.Ru.card_Ru) (by norm_num) (by norm_num)
  · have hc : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
        3 * Nat.card (NativeSporadic.Carrier s) := by
      obtain ⟨N, hNn, ⟨eN⟩, ⟨eQ⟩⟩ := hext
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
        Nat.card_congr eN.toEquiv, mul_comm]
      congr 1
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact nine (3 * 443520) (by
        rw [hc, show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
          CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22]) (by norm_num)
    · exact nine (3 * 50232960) (by
        rw [hc, show Nat.card (NativeSporadic.Carrier .J3) = 50232960 from
          CFSG.Sporadic.J3.card_J3]) (by norm_num)
    · exact nine (3 * 898128000) (by
        rw [hc, show Nat.card (NativeSporadic.Carrier .McL) = 898128000 from
          CFSG.Sporadic.McL.card_McL]) (by norm_num)
    · obtain ⟨hm3, hdvd⟩ := Item419Res3.unitary_component_facts hKle hKc hm e
      rcases (show m = 3 ∨ 5 ≤ m by obtain ⟨j, rfl⟩ := hm; omega) with rfl | h5
      · exact HeringUnitarySpor.false_of_ON_cover hL hext haN ha3 haC hKle e
      · have hK15 : 2 ^ 15 ∣ Nat.card K := by
          rw [Nat.card_congr e.toEquiv]
          exact (pow_dvd_pow 2 (by omega)).trans (Item419Res3.two_pow_dvd_card_projSU_three_two hm)
        have h := hK15.trans hdvd
        rw [hc, show Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 from
          CFSG.Sporadic.ON.card_ON_eq] at h
        norm_num at h

end Main

end CFSG.RankThree.PartTwo.Sec4
