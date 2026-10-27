module

public import CFSG.Quasithin.H13.U3S1347E
public import CFSG.Quasithin.H13.U3S1348S

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem relIndex_pCoreOf_T {H : Subgroup G} (hq : quasithinO2QuotientIso H (Perm (Fin 3)))
    (hTH : T ≤ H) (h3 : T.relIndex H = 3) (hOT : pCoreOf 2 H ≤ T) :
    (pCoreOf 2 H).relIndex T = 2 := by
  have h6 : (pCoreOf 2 H).relIndex H = 6 := by
    rw [relIndex_pCoreOf_of_quot hq, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hm := relIndex_mul_relIndex (pCoreOf 2 H) T H hOT hTH
  rw [h6, h3] at hm
  omega

omit [Finite G] in
theorem card_pCoreOf_of_relIndex_two {H : Subgroup G} (h2 : (pCoreOf 2 H).relIndex T = 2)
    (hOT : pCoreOf 2 H ≤ T) : 2 * Nat.card ↥(pCoreOf 2 H) = Nat.card T := by
  have := relIndex_mul_card (pCoreOf 2 H) T
  rwa [inf_eq_left.2 hOT, h2] at this

theorem s1347_relIndex_H0 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hN₁ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G)) :
    T.relIndex (H₁ ⊔ H₂) = 9 := by
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hH₁ := le_oTwoRes_sup_of_isSylowTwoOf hsyl₁
  have hsup : oTwoRes H₁ ⊔ H₂ = H₁ ⊔ H₂ :=
    le_antisymm (sup_le ((oTwoRes_le H₁).trans le_sup_left) le_sup_right)
      (sup_le (hH₁.trans (sup_le le_sup_left (h.inH₂.1.trans le_sup_right))) le_sup_right)
  have hinf : oTwoRes H₁ ⊓ H₂ = oTwoRes H₁ ⊓ T := by
    refine le_antisymm (fun x hx => ⟨hx.1, ?_⟩) (inf_le_inf_left _ h.inH₂.1)
    rw [← s1347_inf_eq S h]
    exact ⟨oTwoRes_le H₁ hx.1, hx.2⟩
  have hK3 : (oTwoRes H₁ ⊓ T).relIndex (oTwoRes H₁) = 3 := by
    have hsup' : oTwoRes H₁ ⊔ T = H₁ :=
      le_antisymm (sup_le (oTwoRes_le H₁) h.inH₁.1) hH₁
    rw [← relIndex_sup_eq (h.inH₁.1.trans (le_normalizer_oTwoRes H₁)), hsup', h3₁]
  have h1 := relIndex_sup_eq (le_sup_right.trans hN₁ : H₂ ≤ normalizer (oTwoRes H₁ : Set G))
  rw [hsup, hinf, hK3] at h1
  rw [← relIndex_mul_relIndex T H₂ (H₁ ⊔ H₂) h.inH₂.1 le_sup_right, h3₂, h1]

theorem s1347_quot_of_ne (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hN₁ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G))
    (hN₂ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₂ : Set G)) (hne : pCoreOf 2 H₁ ≠ pCoreOf 2 H₂) :
    quasithinO2QuotientIso (H₁ ⊔ H₂) (Perm (Fin 3) × Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hsyl₂ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1
  have hO₁T := pCoreOf_two_le_of_isSylowTwoOf hsyl₁
  have hO₂T := pCoreOf_two_le_of_isSylowTwoOf hsyl₂
  have h2₁ := relIndex_pCoreOf_T h.s3₁ h.inH₁.1 h3₁ hO₁T
  have h2₂ := relIndex_pCoreOf_T h.s3₂ h.inH₂.1 h3₂ hO₂T
  have hc₁ := card_pCoreOf_of_relIndex_two h2₁ hO₁T
  have hc₂ := card_pCoreOf_of_relIndex_two h2₂ hO₂T
  have hH₁ := le_oTwoRes_sup_of_isSylowTwoOf hsyl₁
  have hH₂ := le_oTwoRes_sup_of_isSylowTwoOf hsyl₂
  have hTQ : pCoreOf 2 H₁ ⊔ pCoreOf 2 H₂ = T := by
    have hm := relIndex_mul_relIndex (pCoreOf 2 H₁) (pCoreOf 2 H₁ ⊔ pCoreOf 2 H₂) T
      le_sup_left (sup_le hO₁T hO₂T)
    rw [h2₁] at hm
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro _ hm) with e | e
    · exfalso
      have hle : pCoreOf 2 H₂ ≤ pCoreOf 2 H₁ := le_sup_right.trans (relIndex_eq_one.1 e)
      exact hne (eq_of_le_of_card_ge hle (by omega)).symm
    · rw [e] at hm
      exact le_antisymm (sup_le hO₁T hO₂T) (relIndex_eq_one.1 (by omega))
  have hH₂A : H₂ ≤ normalizer ((oTwoRes H₁ ⊔ pCoreOf 2 H₂ : Subgroup G) : Set G) :=
    fun g hg => F6.mem_normalizer_sup (hN₁ (mem_sup_right hg)) (le_normalizer_pCoreOf 2 H₂ hg)
  have hH₁B : H₁ ≤ normalizer ((oTwoRes H₂ ⊔ pCoreOf 2 H₁ : Subgroup G) : Set G) :=
    fun g hg => F6.mem_normalizer_sup (hN₂ (mem_sup_left hg)) (le_normalizer_pCoreOf 2 H₁ hg)
  have hNA : H₁ ⊔ H₂ ≤ normalizer ((oTwoRes H₁ ⊔ pCoreOf 2 H₂ : Subgroup G) : Set G) :=
    sup_le (hH₁.trans (sup_le (le_sup_left.trans le_normalizer) (h.inH₂.1.trans hH₂A))) hH₂A
  have hNB : H₁ ⊔ H₂ ≤ normalizer ((oTwoRes H₂ ⊔ pCoreOf 2 H₁ : Subgroup G) : Set G) :=
    sup_le hH₁B (hH₂.trans (sup_le (le_sup_left.trans le_normalizer) (h.inH₁.1.trans hH₁B)))
  have hAH : oTwoRes H₁ ⊔ pCoreOf 2 H₂ ≤ H₁ ⊔ H₂ :=
    sup_le ((oTwoRes_le H₁).trans le_sup_left) ((pCoreOf_le 2 H₂).trans le_sup_right)
  have hBH : oTwoRes H₂ ⊔ pCoreOf 2 H₁ ≤ H₁ ⊔ H₂ :=
    sup_le ((oTwoRes_le H₂).trans le_sup_right) ((pCoreOf_le 2 H₁).trans le_sup_left)
  have hAT : (oTwoRes H₁ ⊔ pCoreOf 2 H₂) ⊔ T = H₁ :=
    le_antisymm (sup_le (sup_le (oTwoRes_le H₁) (hO₂T.trans h.inH₁.1)) h.inH₁.1)
      (hH₁.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hBT : (oTwoRes H₂ ⊔ pCoreOf 2 H₁) ⊔ T = H₂ :=
    le_antisymm (sup_le (sup_le (oTwoRes_le H₂) (hO₁T.trans h.inH₂.1)) h.inH₂.1)
      (hH₂.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hfac : ∀ {Hi Hj : Subgroup G}, T ≤ Hi → T.relIndex Hi = 3 →
      pCoreOf 2 Hj ≠ pCoreOf 2 Hi → Nat.card ↥(pCoreOf 2 Hj) = Nat.card ↥(pCoreOf 2 Hi) →
      pCoreOf 2 Hj ≤ T →
      oTwoRes Hi ⊔ pCoreOf 2 Hj ≤ H₁ ⊔ H₂ →
      H₁ ⊔ H₂ ≤ normalizer ((oTwoRes Hi ⊔ pCoreOf 2 Hj : Subgroup G) : Set G) →
      (oTwoRes Hi ⊔ pCoreOf 2 Hj) ⊔ T = Hi →
      quasithinO2QuotientIso (oTwoRes Hi ⊔ pCoreOf 2 Hj) (Perm (Fin 3)) := by
    intro Hi Hj hTi h3i hneij hcard hOjT hXH hNX hXT
    have hTX : T ≤ normalizer ((oTwoRes Hi ⊔ pCoreOf 2 Hj : Subgroup G) : Set G) :=
      hH₀.1.trans hNX
    have hsylX := A4.isSylowTwoOf_inf_normal hsyl₀ hXH hNX
    have h3X : (T ⊓ (oTwoRes Hi ⊔ pCoreOf 2 Hj)).relIndex (oTwoRes Hi ⊔ pCoreOf 2 Hj) = 3 := by
      rw [inf_comm, ← relIndex_sup_eq hTX, hXT, h3i]
    refine quot_S3_of_index_three hsylX h3X fun hN => hneij ?_
    have hHiN : Hi ≤ normalizer ((T ⊓ (oTwoRes Hi ⊔ pCoreOf 2 Hj) : Subgroup G) : Set G) := by
      exact hXT.symm.le.trans
        (sup_le hN fun t ht => mem_normalizer_inf_of (le_normalizer ht) (hTX ht))
    have hle : T ⊓ (oTwoRes Hi ⊔ pCoreOf 2 Hj) ≤ pCoreOf 2 Hi :=
      le_pCoreOf_of_le_normalizer (inf_le_left.trans hTi) hHiN
        (S.h13.sylow.1.to_le inf_le_left)
    exact eq_of_le_of_card_ge (fun x hx => hle ⟨hOjT hx, mem_sup_right hx⟩) hcard.ge
  have hfacA := hfac h.inH₁.1 h3₁ (Ne.symm hne) (by omega) hO₂T hAH hNA hAT
  have hfacB := hfac h.inH₂.1 h3₂ hne (by omega) hO₁T hBH hNB hBT
  have hAB : (oTwoRes H₁ ⊔ pCoreOf 2 H₂) ⊓ (oTwoRes H₂ ⊔ pCoreOf 2 H₁) ≤
      pCoreOf 2 (H₁ ⊔ H₂) := by
    have hT' : (oTwoRes H₁ ⊔ pCoreOf 2 H₂) ⊓ (oTwoRes H₂ ⊔ pCoreOf 2 H₁) ≤ T := by
      rw [← s1347_inf_eq S h]
      exact inf_le_inf (le_sup_left.trans hAT.le) (le_sup_left.trans hBT.le)
    exact le_pCoreOf_of_le_normalizer (inf_le_left.trans hAH)
      (fun g hg => mem_normalizer_inf_of (hNA hg) (hNB hg)) (S.h13.sylow.1.to_le hT')
  have hdec : ∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ oTwoRes H₁ ⊔ pCoreOf 2 H₂,
      ∃ b ∈ oTwoRes H₂ ⊔ pCoreOf 2 H₁, x = a * b := by
    intro x hx
    have hTAB : T ≤ (oTwoRes H₁ ⊔ pCoreOf 2 H₂) ⊔ (oTwoRes H₂ ⊔ pCoreOf 2 H₁) :=
      hTQ.symm.le.trans (sup_le (le_sup_right.trans le_sup_right)
        (le_sup_right.trans le_sup_left))
    have hle : H₁ ⊔ H₂ ≤ (oTwoRes H₁ ⊔ pCoreOf 2 H₂) ⊔ (oTwoRes H₂ ⊔ pCoreOf 2 H₁) :=
      sup_le (hH₁.trans (sup_le (le_sup_left.trans le_sup_left) hTAB))
        (hH₂.trans (sup_le (le_sup_left.trans le_sup_right) hTAB))
    exact Vol2.Ch11.SecC.mem_sup_of_le_normalizer (hBH.trans hNA) (hle hx)
  have hQ₀₁ : pCoreOf 2 (H₁ ⊔ H₂) ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer ((pCoreOf_two_le_of_isSylowTwoOf hsyl₀).trans h.inH₁.1)
      (le_sup_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hOA : pCoreOf 2 (oTwoRes H₁ ⊔ pCoreOf 2 H₂) =
      (oTwoRes H₁ ⊔ pCoreOf 2 H₂) ⊓ pCoreOf 2 (H₁ ⊔ H₂) :=
    le_antisymm (le_inf (pCoreOf_le 2 _) (pCoreOf_le_pCoreOf hAH hNA))
      (le_pCoreOf_of_le_normalizer inf_le_left (fun g hg => mem_normalizer_inf_of
        (le_normalizer hg) (le_normalizer_pCoreOf 2 _ (hAH hg)))
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right))
  have hOB : pCoreOf 2 (oTwoRes H₂ ⊔ pCoreOf 2 H₁) = pCoreOf 2 (H₁ ⊔ H₂) :=
    le_antisymm (pCoreOf_le_pCoreOf hBH hNB)
      (le_pCoreOf_of_le_normalizer (hQ₀₁.trans le_sup_right)
        (fun g hg => le_normalizer_pCoreOf 2 _ (hBH hg)) (pCoreOf_isPGroup 2 _))
  exact quasithinO2QuotientIso_prod hAH hBH hNA hNB hdec hAB hfacA hfacB hOA hOB

@[expose] def e9Hom {M : Type*} [Group M] (a b : M) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Commute a b) : Multiplicative (ZMod 3 × ZMod 3) →* M where
  toFun p := a ^ (Multiplicative.toAdd p).1.val * b ^ (Multiplicative.toAdd p).2.val
  map_one' := by simp
  map_mul' p q := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_add, pow_add]
    calc a ^ (Multiplicative.toAdd p).1.val * a ^ (Multiplicative.toAdd q).1.val *
          (b ^ (Multiplicative.toAdd p).2.val * b ^ (Multiplicative.toAdd q).2.val) =
        a ^ (Multiplicative.toAdd p).1.val * (a ^ (Multiplicative.toAdd q).1.val *
          b ^ (Multiplicative.toAdd p).2.val) * b ^ (Multiplicative.toAdd q).2.val := by
          simp only [mul_assoc]
      _ = a ^ (Multiplicative.toAdd p).1.val * (b ^ (Multiplicative.toAdd p).2.val *
          a ^ (Multiplicative.toAdd q).1.val) * b ^ (Multiplicative.toAdd q).2.val := by
          rw [(hab.pow_pow (Multiplicative.toAdd q).1.val (Multiplicative.toAdd p).2.val).eq]
      _ = _ := by simp only [mul_assoc]

theorem isExtensionOf_E9_of {X E : Subgroup G} (hEX : E ≤ X)
    (hXE : X ≤ normalizer (E : Set G)) (hOE : pCoreOf 2 X ≤ E)
    (h18 : (pCoreOf 2 X).relIndex X = 18) (h9 : (pCoreOf 2 X).relIndex E = 9) {y₁ y₂ : G}
    (hy₁ : y₁ ∈ E) (hy₂ : y₂ ∈ E) (h3₁ : y₁ ^ 3 = 1) (h3₂ : y₂ ^ 3 = 1)
    (hc : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ pCoreOf 2 X)
    (hind : ∀ i j : ℕ, i < 3 → j < 3 → y₁ ^ i * y₂ ^ j ∈ pCoreOf 2 X → i = 0 ∧ j = 0) :
    F6.IsExtensionOf (↥X ⧸ CFSG.Open.pCore 2 ↥X) (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3 × ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 ↥X := by
    rw [pCoreOf]
    exact comap_map_eq_self_of_injective X.subtype_injective _
  obtain ⟨π, hπ⟩ : ∃ f : ↥X →* (↥X ⧸ CFSG.Open.pCore 2 ↥X), f = QuotientGroup.mk' _ :=
    ⟨_, rfl⟩
  have hπs : Function.Surjective π := hπ ▸ QuotientGroup.mk'_surjective _
  have hπk : π.ker = CFSG.Open.pCore 2 ↥X := hπ ▸ QuotientGroup.ker_mk' _
  have hπ1 : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ pCoreOf 2 X := fun x => by
    rw [← MonoidHom.mem_ker, hπk, ← hO, mem_subgroupOf]
  obtain ⟨Eb, hEb⟩ : ∃ Y : Subgroup (↥X ⧸ CFSG.Open.pCore 2 ↥X),
      Y = (E.subgroupOf X).map π := ⟨_, rfl⟩
  have hEn : (E.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hEX).2 hXE
  have hEbn : Eb.Normal := hEb ▸ hEn.map π hπs
  have hcardX : Nat.card (↥X ⧸ CFSG.Open.pCore 2 ↥X) = 18 := by
    rw [← h18, relIndex, hO]
    rfl
  have hE2 : E.relIndex X = 2 := by
    have hm := relIndex_mul_relIndex (pCoreOf 2 X) E X hOE hEX
    rw [h9, h18] at hm
    omega
  have hindex : Eb.index = 2 := by
    rw [hEb, index_map_eq _ hπs (by
      rw [hπk, ← hO]
      exact fun x hx => mem_subgroupOf.2 (hOE (mem_subgroupOf.1 hx)))]
    exact hE2
  have hcardE : Nat.card Eb = 9 := by
    have := card_mul_index Eb
    rw [hindex, hcardX] at this
    omega
  have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hE9 : Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 9 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  let e2 : (↥X ⧸ CFSG.Open.pCore 2 ↥X) ⧸ Eb ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hindex hZ2
  refine ⟨e2.toMonoidHom.comp (QuotientGroup.mk' Eb),
    e2.surjective.comp (QuotientGroup.mk'_surjective Eb), ?_⟩
  have hker : (e2.toMonoidHom.comp (QuotientGroup.mk' Eb)).ker = Eb := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hb₁ : π ⟨y₁, hEX hy₁⟩ ∈ Eb := hEb ▸ ⟨⟨y₁, hEX hy₁⟩, mem_subgroupOf.2 hy₁, rfl⟩
  have hb₂ : π ⟨y₂, hEX hy₂⟩ ∈ Eb := hEb ▸ ⟨⟨y₂, hEX hy₂⟩, mem_subgroupOf.2 hy₂, rfl⟩
  have hpow : ∀ {y : G} (hy : y ∈ X) (n : ℕ), (⟨y, hy⟩ : ↥X) ^ n = ⟨y ^ n, pow_mem hy n⟩ :=
    fun hy n => Subtype.ext (by simp)
  have hc3 : ∀ {y : G} (hy : y ∈ X) (hyE : π ⟨y, hy⟩ ∈ Eb), y ^ 3 = 1 →
      (⟨π ⟨y, hy⟩, hyE⟩ : ↥Eb) ^ 3 = 1 := fun {y} hy hyE h3 => Subtype.ext (by
    rw [Subgroup.coe_pow, ← map_pow, hpow, Subgroup.coe_one]
    refine (hπ1 _).2 ?_
    show y ^ 3 ∈ pCoreOf 2 X
    rw [h3]
    exact one_mem _)
  have hab : Commute (⟨π ⟨y₁, hEX hy₁⟩, hb₁⟩ : ↥Eb) ⟨π ⟨y₂, hEX hy₂⟩, hb₂⟩ := by
    refine Subtype.ext ?_
    have h1 : π (⟨y₁, hEX hy₁⟩ * ⟨y₂, hEX hy₂⟩ * (⟨y₁, hEX hy₁⟩)⁻¹ * (⟨y₂, hEX hy₂⟩)⁻¹) = 1 :=
      (hπ1 _).2 hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    show π ⟨y₁, hEX hy₁⟩ * π ⟨y₂, hEX hy₂⟩ = π ⟨y₂, hEX hy₂⟩ * π ⟨y₁, hEX hy₁⟩
    calc π ⟨y₁, hEX hy₁⟩ * π ⟨y₂, hEX hy₂⟩ = (π ⟨y₁, hEX hy₁⟩ * π ⟨y₂, hEX hy₂⟩ *
          (π ⟨y₁, hEX hy₁⟩)⁻¹ * (π ⟨y₂, hEX hy₂⟩)⁻¹) * (π ⟨y₂, hEX hy₂⟩ * π ⟨y₁, hEX hy₁⟩) := by
          group
      _ = π ⟨y₂, hEX hy₂⟩ * π ⟨y₁, hEX hy₁⟩ := by rw [h1, one_mul]
  have hinj : Function.Injective
      (e9Hom _ _ (hc3 (hEX hy₁) hb₁ h3₁) (hc3 (hEX hy₂) hb₂ h3₂) hab) := by
    refine (injective_iff_map_eq_one _).2 fun p hp => ?_
    have hp' := congrArg Subtype.val hp
    simp only [e9Hom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_pow,
      Subgroup.coe_one] at hp'
    rw [← map_pow, ← map_pow, ← map_mul, hπ1, hpow, hpow] at hp'
    obtain ⟨hi, hj⟩ := hind _ _ (ZMod.val_lt _) (ZMod.val_lt _) hp'
    rw [ZMod.val_eq_zero] at hi hj
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext hi hj
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcardE, hE9])
  exact ⟨(MulEquiv.subgroupCongr hker).trans (MulEquiv.ofBijective _ hbij).symm⟩

theorem s1347_quot_of_eq (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hN₁ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G))
    (hN₂ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₂ : Set G))
    (hcomm : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ pCoreOf 2 (oTwoRes H₁) ⊓ pCoreOf 2 (oTwoRes H₂))
    (heq : pCoreOf 2 H₁ = pCoreOf 2 H₂) :
    F6.IsExtensionOf (↥(H₁ ⊔ H₂) ⧸ CFSG.Open.pCore 2 ↥(H₁ ⊔ H₂)) (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3 × ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hsyl₂ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1
  have hO₁T := pCoreOf_two_le_of_isSylowTwoOf hsyl₁
  have hO₀T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have h2₁ := relIndex_pCoreOf_T h.s3₁ h.inH₁.1 h3₁ hO₁T
  have hH₁ := le_oTwoRes_sup_of_isSylowTwoOf hsyl₁
  have hH₂ := le_oTwoRes_sup_of_isSylowTwoOf hsyl₂
  have hQ₀₁ : pCoreOf 2 (H₁ ⊔ H₂) ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer (hO₀T.trans h.inH₁.1)
      (le_sup_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hQ : pCoreOf 2 H₁ = pCoreOf 2 (H₁ ⊔ H₂) :=
    le_antisymm (le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 H₁).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 H₁) (heq ▸ le_normalizer_pCoreOf 2 H₂))
      (pCoreOf_isPGroup 2 H₁)) hQ₀₁
  have hQ₂ : pCoreOf 2 H₂ = pCoreOf 2 (H₁ ⊔ H₂) := heq ▸ hQ
  have hEH : oTwoRes H₁ ⊔ oTwoRes H₂ ⊔ pCoreOf 2 (H₁ ⊔ H₂) ≤ H₁ ⊔ H₂ :=
    sup_le (sup_le ((oTwoRes_le H₁).trans le_sup_left) ((oTwoRes_le H₂).trans le_sup_right))
      (pCoreOf_le 2 _)
  have hNE : H₁ ⊔ H₂ ≤ normalizer ((oTwoRes H₁ ⊔ oTwoRes H₂ ⊔ pCoreOf 2 (H₁ ⊔ H₂) :
      Subgroup G) : Set G) := fun g hg =>
    F6.mem_normalizer_sup (F6.mem_normalizer_sup (hN₁ hg) (hN₂ hg))
      (le_normalizer_pCoreOf 2 _ hg)
  have hET : (oTwoRes H₁ ⊔ oTwoRes H₂ ⊔ pCoreOf 2 (H₁ ⊔ H₂)) ⊔ T = H₁ ⊔ H₂ := by
    refine le_antisymm (sup_le hEH hH₀.1) (sup_le ?_ ?_)
    · exact hH₁.trans (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
    · exact hH₂.trans (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left)) le_sup_right)
  have hEinfT : (oTwoRes H₁ ⊔ oTwoRes H₂ ⊔ pCoreOf 2 (H₁ ⊔ H₂)) ⊓ T =
      pCoreOf 2 (H₁ ⊔ H₂) := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hO₀T)
    obtain ⟨hxE, hxT⟩ := mem_inf.1 hx
    have hQN : pCoreOf 2 (H₁ ⊔ H₂) ≤
        normalizer ((oTwoRes H₁ ⊔ oTwoRes H₂ : Subgroup G) : Set G) := fun g hg =>
      F6.mem_normalizer_sup (hN₁ (pCoreOf_le 2 _ hg)) (hN₂ (pCoreOf_le 2 _ hg))
    obtain ⟨u, hu, q, hq, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hQN hxE
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
      ((oTwoRes_le H₂).trans (le_sup_right.trans hN₁)) hu
    have hqT := hO₀T hq
    have hk₂T : k₂ ∈ T := by
      rw [← s1347_inf_eq S h]
      refine mem_inf.2 ⟨?_, oTwoRes_le H₂ hk₂⟩
      have e : k₂ = k₁⁻¹ * (k₁ * k₂ * q) * q⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (oTwoRes_le H₁ hk₁)) (h.inH₁.1 hxT))
        (inv_mem (h.inH₁.1 hqT))
    have hk₂Q : k₂ ∈ pCoreOf 2 (H₁ ⊔ H₂) := by
      obtain ⟨n, hn⟩ := S.h13.sylow.1 ⟨k₂, hk₂T⟩
      rw [← hQ₂]
      exact mem_pCoreOf_of_mem_oTwoRes h.s3₂ hk₂ (by simpa using congrArg Subtype.val hn)
    have hk₁T : k₁ ∈ T := by
      have e : k₁ = k₁ * k₂ * q * q⁻¹ * k₂⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem hxT (inv_mem hqT)) (inv_mem hk₂T)
    have hk₁Q : k₁ ∈ pCoreOf 2 (H₁ ⊔ H₂) := by
      obtain ⟨n, hn⟩ := S.h13.sylow.1 ⟨k₁, hk₁T⟩
      rw [← hQ]
      exact mem_pCoreOf_of_mem_oTwoRes h.s3₁ hk₁ (by simpa using congrArg Subtype.val hn)
    exact mul_mem (mul_mem hk₁Q hk₂Q) hq
  have h9 : T.relIndex (H₁ ⊔ H₂) = 9 := s1347_relIndex_H0 S h hN₁
  have h18 : (pCoreOf 2 (H₁ ⊔ H₂)).relIndex (H₁ ⊔ H₂) = 18 := by
    rw [← relIndex_mul_relIndex _ T _ hO₀T hH₀.1, ← hQ, h2₁, h9]
  have h9E : (pCoreOf 2 (H₁ ⊔ H₂)).relIndex
      (oTwoRes H₁ ⊔ oTwoRes H₂ ⊔ pCoreOf 2 (H₁ ⊔ H₂)) = 9 := by
    have := relIndex_sup_eq (hH₀.1.trans hNE)
    rw [hET, h9, hEinfT] at this
    exact this.symm
  obtain ⟨y₁, hy₁K, hy₁3, hy₁T, -⟩ :=
    s1347_exists_gen S hH₀ le_sup_left h.inH₁.1 h3₁ h.s3₁ h.index₁ hN₁
  obtain ⟨y₂, hy₂K, hy₂3, hy₂T, -⟩ :=
    s1347_exists_gen S hH₀ le_sup_right h.inH₂.1 h3₂ h.s3₂ h.index₂ hN₂
  have hO₁ : pCoreOf 2 (oTwoRes H₁) ≤ pCoreOf 2 (H₁ ⊔ H₂) :=
    pCoreOf_le_pCoreOf ((oTwoRes_le H₁).trans le_sup_left) hN₁
  have hcube : ∀ {y : G} {n : ℕ}, y ^ 3 = 1 → (y ^ n) ^ 3 = 1 := fun {y n} h3 => by
    rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have hzero : ∀ {y : G} {n : ℕ}, y ∉ T → y ^ 3 = 1 → n < 3 → y ^ n = 1 → n = 0 :=
    fun {y n} hyT h3 hn hyn => by
      by_contra hn0
      have ho : orderOf y = 3 := orderOf_eq_prime h3 fun e => hyT (e ▸ one_mem T)
      exact pow_ne_one_of_lt_orderOf hn0 (ho ▸ hn) hyn
  refine isExtensionOf_E9_of hEH hNE le_sup_right h18 h9E (mem_sup_left (mem_sup_left hy₁K))
    (mem_sup_left (mem_sup_right hy₂K)) hy₁3 hy₂3
    (hO₁ (hcomm (commutator_mem_commutator hy₁K hy₂K)).1) fun i j hi hj hij => ?_
  have hK1 : y₁ ^ i ∈ T := by
    rw [← s1347_inf_eq S h]
    refine mem_inf.2 ⟨oTwoRes_le H₁ (pow_mem hy₁K i), ?_⟩
    have e : y₁ ^ i = y₁ ^ i * y₂ ^ j * (y₂ ^ j)⁻¹ := by group
    rw [e]
    exact mul_mem (h.inH₂.1 (hO₀T hij)) (inv_mem (oTwoRes_le H₂ (pow_mem hy₂K j)))
  have hy₁i : y₁ ^ i = 1 := eq_one_of_mem_of_cube S.h13.sylow.1 hK1 (hcube hy₁3)
  rw [hy₁i, one_mul] at hij
  have hy₂j : y₂ ^ j = 1 := eq_one_of_mem_of_cube S.h13.sylow.1 (hO₀T hij) (hcube hy₂3)
  exact ⟨hzero hy₁T hy₁3 hi hy₁i, hzero hy₂T hy₂3 hj hy₂j⟩

theorem s1347_quot_of_normal (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hN₁ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G))
    (hN₂ : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₂ : Set G))
    (hcomm : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ pCoreOf 2 (oTwoRes H₁) ⊓ pCoreOf 2 (oTwoRes H₂)) :
    quasithinO2QuotientIso (H₁ ⊔ H₂) (Perm (Fin 3) × Perm (Fin 3)) ∨
      F6.IsExtensionOf (↥(H₁ ⊔ H₂) ⧸ CFSG.Open.pCore 2 ↥(H₁ ⊔ H₂)) (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 3 × ZMod 3)) := by
  by_cases heq : pCoreOf 2 H₁ = pCoreOf 2 H₂
  · exact Or.inr (s1347_quot_of_eq S h hH₀ hN₁ hN₂ hcomm heq)
  · exact Or.inl (s1347_quot_of_ne S h hH₀ hN₁ hN₂ heq)

theorem s1347_concl_i (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂)
    (hcomm : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    Concl1347i T H₁ H₂ := by
  obtain ⟨hH₀, -, -, hsup, hinf, hc₁, hc₂⟩ :=
    s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨hN₁, hN₂⟩ := s1347_normal_of_comm S h hH₀ hcomm
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hK := s1347_comm_le_of_normal S h ((oTwoRes_le H₂).trans (le_sup_right.trans hN₁))
    ((oTwoRes_le H₁).trans (le_sup_left.trans hN₂))
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := s1347_V0_of_normal S h hH₀ hsup hinf hc₁ hc₂ hN₁ hN₂
  exact ⟨s1347_mul_of_normal h.inH₂.1 (le_oTwoRes_sup_of_isSylowTwoOf hsyl₁) hN₁, hK,
    s1347_quot_of_normal S h hH₀ hN₁ hN₂ hK, v1, v2, v3, v4, v5, v6⟩

end CFSG.Quasithin.H13.U3
