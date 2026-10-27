module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqT6
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful
import CFSG.Quasithin.Recognition.St84.Gen.NatSecCoord
import CFSG.Quasithin.Recognition.St84.Gen.NatSecLines
import CFSG.Quasithin.Recognition.St84.Gen.NatSecModule
import CFSG.Quasithin.Recognition.Stroth.Str83G4Reduction
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzModule
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz
import TauCeti.GroupTheory.PGroup
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem r4d_matrix {F : Type} [Field F] [Finite F] (hF : 2 ∣ Nat.card F)
    {U : Subgroup SL(2, F)} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧
      (∀ w : Fin 2 → F, (∀ A ∈ U, (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w) ↔
        ∃ c : F, w = c • v) ∧
      (∀ A ∈ U, ∀ w : Fin 2 → F, ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F).mulVec w - w = c • v) ∧
      (∀ A ∈ U, A ≠ 1 → ∀ w : Fin 2 → F, (A : Matrix (Fin 2) (Fin 2) F).mulVec w = w →
        ∃ c : F, w = c • v) := by
  obtain ⟨v, hv0, hv⟩ := CFSG.Quasithin.H13.exists_fixed_vector hF U hU
  refine ⟨v, hv0, fun w => ⟨fun hw => CFSG.Quasithin.H13.fixed_eq_line U hU1 hv0 hv hw, ?_⟩,
    fun A hA w => CFSG.Quasithin.H13.sub_mem_line_of_mem_sl2Stab hv0 (hv A hA) w, ?_⟩
  · rintro ⟨c, rfl⟩ A hA
    rw [Matrix.mulVec_smul, hv A hA]
  · intro A hA hA1 w hw
    have hzp : Subgroup.zpowers A ≠ ⊥ := fun h => hA1 (Subgroup.zpowers_eq_bot.mp h)
    have hAv : A ∈ CFSG.Quasithin.H13.sl2Stab v := hv A hA
    have hAw : A ∈ CFSG.Quasithin.H13.sl2Stab w := hw
    refine CFSG.Quasithin.H13.fixed_eq_line (Subgroup.zpowers A) hzp hv0 (fun B hB => ?_)
      (fun B hB => ?_)
    · exact (CFSG.Quasithin.H13.mem_sl2Stab).mp ((Subgroup.zpowers_le.mpr hAv) hB)
    · exact (CFSG.Quasithin.H13.mem_sl2Stab).mp ((Subgroup.zpowers_le.mpr hAw) hB)

private theorem r4d_card_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h : Fintype.card {x : α // x ≠ a} = Fintype.card α - Fintype.card {x : α // x = a} :=
    Fintype.card_subtype_compl (fun x : α => x = a)
  rw [Fintype.card_subtype_eq] at h
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  omega

private theorem r4d_core {L Z Q S D : Subgroup G} {f : ℕ} (hf : f ≠ 0)
    {α : ↥L →* SL(2, GaloisField 2 f)}
    (hnat : CFSG.Quasithin.F112R.St84.IsNatSecOf L Z ⊥ α)
    (hZL : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ * z * ℓ⁻¹ ∈ Z)
    (hQZ : ∀ q ∈ Q, ∀ z ∈ Z, q * z * q⁻¹ = z)
    (hSdec : ∀ s ∈ S, ∃ q ∈ Q, ∃ τ ∈ S ⊓ L, s = q * τ)
    (hSp : IsPGroup 2 ↥(S ⊓ L))
    (hkerQ : ∀ ℓ : ↥L, α ℓ = 1 → (ℓ : G) ∈ Q)
    (hSQ : ¬ S ⊓ L ≤ Q)
    (hDL : D ≤ L) (hDS : ∀ d ∈ D, ∀ s ∈ S, d⁻¹ * s * d ∈ S)
    (hDZ : ∀ d ∈ D, ∀ z ∈ Z, d * z * d⁻¹ ∈ Z)
    (hDodd : Odd (Nat.card D)) (hDcard : Nat.card D = 2 ^ f - 1)
    (hDker : ∀ d ∈ D, ∀ hd : d ∈ L, α ⟨d, hd⟩ = 1 → d = 1) :
    Nat.card Z = 2 ^ f * 2 ^ f ∧
      Nat.card (Z ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f ∧
      (∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ * z⁻¹ ∈ Z ⊓ centralizer (S : Set G)) ∧
      (∀ s ∈ S, s ∉ Q → ∀ z ∈ Z, s * z * s⁻¹ = z → z ∈ Z ⊓ centralizer (S : Set G)) ∧
      (∀ z ∈ Z ⊓ centralizer (S : Set G), z ≠ 1 →
        ∀ z' ∈ Z ⊓ centralizer (S : Set G), z' ≠ 1 → ∃ d ∈ D, d * z * d⁻¹ = z') := by
  classical
  have hnat' := hnat
  obtain ⟨β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let crd : ↥Z → (Fin 2 → GaloisField 2 f) := fun z => Multiplicative.toAdd (β z)
  have hcrdinj : Function.Injective crd := fun x y h =>
    hβinj (Multiplicative.toAdd.injective h)
  have hcrdsurj : Function.Surjective crd := fun w => by
    obtain ⟨z, hz⟩ := hβs (Multiplicative.ofAdd w)
    exact ⟨z, by simp [crd, hz]⟩
  have hcrd_mul : ∀ x y : ↥Z, crd (x * y⁻¹) = crd x - crd y := by
    intro x y
    simp [crd, map_mul, map_inv, sub_eq_add_neg]
  have hcrd_conj : ∀ (ℓ : ↥L) (z : ↥Z) (hz : (ℓ : G) * z * (ℓ : G)⁻¹ ∈ Z),
      crd ⟨(ℓ : G) * z * (ℓ : G)⁻¹, hz⟩ =
        (α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec (crd z) :=
    fun ℓ z hz => hβe ℓ z ⟨_, hz⟩ rfl
  have hF2 : 2 ∣ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f hf]
    exact dvd_pow_self 2 hf
  let U : Subgroup SL(2, GaloisField 2 f) := ((S ⊓ L).subgroupOf L).map α
  have hUp : IsPGroup 2 U :=
    (hSp.comap_of_injective L.subtype L.subtype_injective).map α
  have hmemU : ∀ τ (hτL : τ ∈ L), τ ∈ S → α ⟨τ, hτL⟩ ∈ U := fun τ hτL hτS =>
    mem_map.mpr ⟨⟨τ, hτL⟩, mem_subgroupOf.mpr ⟨hτS, hτL⟩, rfl⟩
  have hU_mem : ∀ A ∈ U, ∃ τ, ∃ hτL : τ ∈ L, τ ∈ S ∧ α ⟨τ, hτL⟩ = A := by
    intro A hA
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hA
    exact ⟨x, x.2, (mem_subgroupOf.mp hx).1, rfl⟩
  have hU1 : U ≠ ⊥ := by
    obtain ⟨τ, hτ, hτQ⟩ := SetLike.not_le_iff_exists.mp hSQ
    have hne : α ⟨τ, hτ.2⟩ ≠ 1 := fun h => hτQ (hkerQ _ h)
    intro hU
    have hm := hmemU τ hτ.2 hτ.1
    rw [hU, Subgroup.mem_bot] at hm
    exact hne hm
  obtain ⟨v, hv0, hline, hF3, hF4⟩ := r4d_matrix hF2 hUp hU1
  have hconjS : ∀ q ∈ Q, ∀ τ z : G, z ∈ Z → τ * z * τ⁻¹ ∈ Z →
      (q * τ) * z * (q * τ)⁻¹ = τ * z * τ⁻¹ := by
    intro q hq τ z _ hτz
    calc q * τ * z * (q * τ)⁻¹ = q * (τ * z * τ⁻¹) * q⁻¹ := by group
      _ = τ * z * τ⁻¹ := hQZ q hq _ hτz
  have hF1 : ∀ z : ↥Z, ((z : G) ∈ centralizer (S : Set G)) ↔
      ∀ A ∈ U, (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec (crd z) = crd z := by
    intro z
    constructor
    · intro hz A hA
      obtain ⟨τ, hτL, hτS, rfl⟩ := hU_mem A hA
      have hτz : τ * (z : G) * τ⁻¹ = z := by
        rw [mem_centralizer_iff.mp hz τ hτS]
        group
      have h1 : τ * (z : G) * τ⁻¹ ∈ Z := by rw [hτz]; exact z.2
      have h2 := hcrd_conj ⟨τ, hτL⟩ z h1
      have h3 : (⟨τ * (z : G) * τ⁻¹, h1⟩ : ↥Z) = z := Subtype.ext hτz
      rw [h3] at h2
      exact h2.symm
    · intro hfix
      rw [mem_centralizer_iff]
      intro s hs
      obtain ⟨q, hq, τ, hτ, rfl⟩ := hSdec s hs
      have hτz : τ * (z : G) * τ⁻¹ ∈ Z := hZL τ hτ.2 z z.2
      have h2 := hcrd_conj ⟨τ, hτ.2⟩ z hτz
      rw [hfix _ (hmemU τ hτ.2 hτ.1)] at h2
      have h3 : (⟨τ * (z : G) * τ⁻¹, hτz⟩ : ↥Z) = z := hcrdinj h2
      have h4 : τ * (z : G) = z * τ := by
        have := congrArg Subtype.val h3
        simp only at this
        calc τ * (z : G) = (τ * z * τ⁻¹) * τ := by group
          _ = z * τ := by rw [this]
      have h5 : q * (z : G) = z * q := by
        have := hQZ q hq z z.2
        calc q * (z : G) = (q * z * q⁻¹) * q := by group
          _ = z * q := by rw [this]
      calc q * τ * (z : G) = q * (τ * z) := by group
        _ = q * (z * τ) := by rw [h4]
        _ = (q * z) * τ := by group
        _ = (z * q) * τ := by rw [h5]
        _ = z * (q * τ) := by group
  have h1 : Nat.card Z = 2 ^ f * 2 ^ f := by
    have e : ↥Z ≃ (Fin 2 → GaloisField 2 f) := Equiv.ofBijective crd ⟨hcrdinj, hcrdsurj⟩
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin, GaloisField.card 2 f hf]
    ring
  have hline_mem : ∀ z : ↥Z, ((z : G) ∈ centralizer (S : Set G)) ↔ ∃ c : GaloisField 2 f,
      crd z = c • v := fun z => (hF1 z).trans (hline (crd z))
  have h2 : Nat.card (Z ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f := by
    let g : ↥(Z ⊓ centralizer (S : Set G)) →
        {w : Fin 2 → GaloisField 2 f // ∃ c : GaloisField 2 f, w = c • v} :=
      fun x => ⟨crd ⟨x, (mem_inf.mp x.2).1⟩, (hline_mem ⟨x, (mem_inf.mp x.2).1⟩).mp
        (mem_inf.mp x.2).2⟩
    have hg_inj : Function.Injective g := by
      intro x y hxy
      have h : crd ⟨x, (mem_inf.mp x.2).1⟩ = crd ⟨y, (mem_inf.mp y.2).1⟩ :=
        congrArg Subtype.val hxy
      have h' := congrArg Subtype.val (hcrdinj h)
      exact Subtype.ext h'
    have hg_surj : Function.Surjective g := by
      rintro ⟨w, hw⟩
      obtain ⟨z, hz⟩ := hcrdsurj w
      have hzC : (z : G) ∈ centralizer (S : Set G) := (hline_mem z).mpr (hz ▸ hw)
      exact ⟨⟨z, mem_inf.mpr ⟨z.2, hzC⟩⟩, Subtype.ext hz⟩
    let g2 : GaloisField 2 f →
        {w : Fin 2 → GaloisField 2 f // ∃ c : GaloisField 2 f, w = c • v} :=
      fun c => ⟨c • v, c, rfl⟩
    have hg2_bij : Function.Bijective g2 := by
      refine ⟨fun c c' h => ?_, fun ⟨w, c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩⟩
      have h' : c • v = c' • v := congrArg Subtype.val h
      exact smul_left_injective _ hv0 h'
    rw [Nat.card_congr (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩),
      ← Nat.card_congr (Equiv.ofBijective g2 hg2_bij), GaloisField.card 2 f hf]
  have h3 : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ * z⁻¹ ∈ Z ⊓ centralizer (S : Set G) := by
    intro s hs z hz
    obtain ⟨q, hq, τ, hτ, rfl⟩ := hSdec s hs
    have hτz : τ * z * τ⁻¹ ∈ Z := hZL τ hτ.2 z hz
    rw [hconjS q hq τ z hz hτz]
    have hc : τ * z * τ⁻¹ * z⁻¹ ∈ Z := Z.mul_mem hτz (Z.inv_mem hz)
    refine ⟨hc, (hline_mem ⟨_, hc⟩).mpr ?_⟩
    have e : (⟨τ * z * τ⁻¹ * z⁻¹, hc⟩ : ↥Z) = ⟨τ * z * τ⁻¹, hτz⟩ * (⟨z, hz⟩ : ↥Z)⁻¹ := rfl
    rw [e, hcrd_mul, hcrd_conj ⟨τ, hτ.2⟩ ⟨z, hz⟩ hτz]
    exact hF3 _ (hmemU τ hτ.2 hτ.1) _
  have h4 : ∀ s ∈ S, s ∉ Q → ∀ z ∈ Z, s * z * s⁻¹ = z → z ∈ Z ⊓ centralizer (S : Set G) := by
    intro s hs hsQ z hz hszs
    obtain ⟨q, hq, τ, hτ, rfl⟩ := hSdec s hs
    have hτz : τ * z * τ⁻¹ ∈ Z := hZL τ hτ.2 z hz
    rw [hconjS q hq τ z hz hτz] at hszs
    have hτQ : τ ∉ Q := fun h => hsQ (Q.mul_mem hq h)
    have hα1 : α ⟨τ, hτ.2⟩ ≠ 1 := fun h => hτQ (hkerQ _ h)
    have hfix : (α ⟨τ, hτ.2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec
        (crd ⟨z, hz⟩) = crd ⟨z, hz⟩ := by
      have h2 := hcrd_conj ⟨τ, hτ.2⟩ ⟨z, hz⟩ hτz
      have e : (⟨τ * z * τ⁻¹, hτz⟩ : ↥Z) = ⟨z, hz⟩ := Subtype.ext hszs
      rw [e] at h2
      exact h2.symm
    obtain ⟨c, hc⟩ := hF4 _ (hmemU τ hτ.2 hτ.1) hα1 _ hfix
    exact ⟨hz, (hline_mem ⟨z, hz⟩).mpr ⟨c, hc⟩⟩
  have hDact : ∀ d ∈ D, ∀ y ∈ Z ⊓ centralizer (S : Set G),
      d * y * d⁻¹ ∈ Z ⊓ centralizer (S : Set G) := by
    intro d hd y hy
    refine mem_inf.mpr ⟨hDZ d hd y (mem_inf.mp hy).1, ?_⟩
    rw [mem_centralizer_iff]
    intro s hs
    have h1 := mem_centralizer_iff.mp (mem_inf.mp hy).2 _ (hDS d hd s hs)
    calc s * (d * y * d⁻¹) = d * ((d⁻¹ * s * d) * y) * d⁻¹ := by group
      _ = d * (y * (d⁻¹ * s * d)) * d⁻¹ := by rw [h1]
      _ = (d * y * d⁻¹) * s := by group
  have h5 : ∀ z ∈ Z ⊓ centralizer (S : Set G), z ≠ 1 →
      ∀ z' ∈ Z ⊓ centralizer (S : Set G), z' ≠ 1 → ∃ d ∈ D, d * z * d⁻¹ = z' := by
    intro z hz hz1 z' hz' hz'1
    have hne : ∀ d : ↥D, (⟨(d : G) * z * (d : G)⁻¹, hDact d d.2 z hz⟩ :
        ↥(Z ⊓ centralizer (S : Set G))) ≠ 1 := by
      intro d h
      apply hz1
      have h' := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at h'
      have := congrArg (fun y => (d : G)⁻¹ * y * d) h'
      simpa [mul_assoc] using this
    let φ : ↥D → {x : ↥(Z ⊓ centralizer (S : Set G)) // x ≠ 1} := fun d =>
      ⟨⟨(d : G) * z * (d : G)⁻¹, hDact d d.2 z hz⟩, hne d⟩
    have hφinj : Function.Injective φ := by
      intro d₁ d₂ h
      by_contra hne12
      have h' : (d₁ : G) * z * (d₁ : G)⁻¹ = (d₂ : G) * z * (d₂ : G)⁻¹ :=
        congrArg (fun x : {x : ↥(Z ⊓ centralizer (S : Set G)) // x ≠ 1} => ((x.1 : _) : G)) h
      have hkD : (d₂ : G)⁻¹ * d₁ ∈ D := D.mul_mem (D.inv_mem d₂.2) d₁.2
      have hk1 : (d₂ : G)⁻¹ * d₁ ≠ 1 := by
        intro hk
        apply hne12
        have : (d₁ : G) = d₂ := by
          have := congrArg (fun y => (d₂ : G) * y) hk
          simpa using this
        exact Subtype.ext this
      have hkL : (d₂ : G)⁻¹ * d₁ ∈ L := hDL hkD
      have hcomm : (d₂ : G)⁻¹ * d₁ * z = z * ((d₂ : G)⁻¹ * d₁) := by
        have e : (d₂ : G)⁻¹ * (d₁ * z * (d₁ : G)⁻¹) * d₂ = z := by
          rw [h']
          group
        calc (d₂ : G)⁻¹ * d₁ * z = ((d₂ : G)⁻¹ * (d₁ * z * (d₁ : G)⁻¹) * d₂) *
              ((d₂ : G)⁻¹ * d₁) := by group
          _ = z * ((d₂ : G)⁻¹ * d₁) := by rw [e]
      have hodd : Odd (orderOf (⟨(d₂ : G)⁻¹ * d₁, hkL⟩ : ↥L)) := by
        rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_mk _ hkD]
        exact hDodd.of_dvd_nat (orderOf_dvd_natCard _)
      have hα : α ⟨(d₂ : G)⁻¹ * d₁, hkL⟩ ≠ 1 := fun h1 => hk1 (hDker _ hkD hkL h1)
      have hzbot := hnat'.mem_of_commute_of_odd hodd hα hz.1 hcomm
      exact hz1 (Subgroup.mem_bot.mp hzbot)
    have hcard : Nat.card {x : ↥(Z ⊓ centralizer (S : Set G)) // x ≠ 1} ≤ Nat.card ↥D := by
      have := r4d_card_ne (1 : ↥(Z ⊓ centralizer (S : Set G)))
      rw [h2] at this
      rw [hDcard]
      omega
    obtain ⟨d, hd⟩ := (hφinj.bijective_of_nat_card_le hcard).2
      ⟨⟨z', hz'⟩, fun h => hz'1 (congrArg Subtype.val h)⟩
    refine ⟨d, d.2, ?_⟩
    exact congrArg (fun x : {x : ↥(Z ⊓ centralizer (S : Set G)) // x ≠ 1} => ((x.1 : _) : G)) hd
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem D2_le_K : t.D2 ≤ t.K := le_sup_right

private theorem D2_le_Gv (i : ℤ) : t.D2 ≤ t.Gv i := t.D2_le_K.trans (t.K_le_Gv i)

private theorem K_le_normalizer_pCoreOf_Gw (a b : ℤ) :
    t.K ≤ normalizer (pCoreOf 2 (t.Gw a b) : Set G) :=
  (t.K_le_Gw a b).trans (le_normalizer_pCoreOf 2 _)

private theorem Q2_le_S (hF : F112HypW L1 L2 S) : Q2 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)

private theorem Q1_le_S (hF : F112HypW L1 L2 S) : Q1 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)

private theorem S_le_Gw_zero_one (hF : F112HypW L1 L2 S) :
    S ≤ t.Gw 0 1 := by
  rw [t.Gw_zero_one hF]
  exact le_sup_right

private theorem Qv_one_le_Gv_two {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ t.Gv 2 := by
  have hX : t.Qv 1 ≤ t.Gw (1 - 1) 1 := by
    rw [show (1 : ℤ) - 1 = 0 by norm_num, t.Qv_one]
    exact (Q2_le_S hfr.hF).trans (t.S_le_Gw_zero_one hfr.hF)
  have h := (t.inf_Gv_eq_inf_Qv hfr 1 (t.isPGroup_Qv 1)).1 hX
  rw [inf_idem] at h
  have h2 := inf_eq_left.mp h
  rwa [show (1 : ℤ) + 1 = 2 by norm_num] at h2

private theorem r4a_P2_le_normalizer_L2 (hF : Hyp111 L1 L2 S) :
    P2 L1 L2 S ≤ normalizer (L2 : Set G) := by
  have h := bigB_le_normalizer_of_hyp111 hF.symm
  rw [bigB_comm] at h
  exact sup_le le_normalizer h

private theorem r4a_P2_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : P2 L1 L2 S ≤ (L2 ⊔ Q2 L1 L2 S) ⊔ t.K := by
  have hS : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hSle : S ≤ L2 ⊔ Q2 L1 L2 S :=
    hS.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  rw [t.hBsplit]
  exact sup_le (sup_le (hSle.trans le_sup_left) (le_sup_left.trans le_sup_right))
    (le_sup_right.trans le_sup_right)

private theorem r4a_K_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
  have hK : t.K ≤ P2 L1 L2 S := by
    rw [← t.Gv_one]
    exact t.K_le_Gv 1
  have hQ : P2 L1 L2 S ≤ normalizer (Q2 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  exact F1.le_normalizer_sup (hK.trans (r4a_P2_le_normalizer_L2 hfr.hF.1)) (hK.trans hQ)

include t in
private theorem r4a_mem_of_pow_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {x : G} (hx : x ∈ P2 L1 L2 S) {j : ℕ} (hxj : x ^ 2 ^ j = 1) :
    x ∈ L2 ⊔ Q2 L1 L2 S := by
  have hK := t.r4a_K_le_normalizer hfr
  obtain ⟨n, hn, k, hk, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hK).1 (t.r4a_P2_le_sup hfr hx)
  have hkodd : Odd (orderOf k) :=
    t.hHall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨n', hn', h⟩ := A4.exists_pow_mul_eq hn (hK hk) (2 ^ j)
  rw [hxj] at h
  have hkj : k ^ 2 ^ j ∈ L2 ⊔ Q2 L1 L2 S := by
    have : k ^ 2 ^ j = n'⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this]
    exact inv_mem hn'
  exact mul_mem hn (B1Red.mem_of_two_pow_mem_of_odd hkj hkodd)

theorem not_le_centralizer_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₁ : ℕ} (hb₁ : Odd b₁) (hZ1 : t.Zv 0 ≤ t.Gv (-(b₁ : ℤ)))
    (hna : ¬ ⁅t.Zv 0, t.Zv (-(b₁ : ℤ))⁆ ≤ t.Zv 0 ⊓ t.Zv (-(b₁ : ℤ))) :
    ¬ L2 ≤ centralizer (t.Zv 1 : Set G) := by
  intro hL2
  have hQ : Q2 L1 L2 S ≤ centralizer (t.Zv 1 : Set G) := by
    have h := le_centralizer_iff.mp (t.Zv_le_centralizer 1)
    rwa [t.Qv_one] at h
  have hN : L2 ⊔ Q2 L1 L2 S ≤ centralizer (t.Zv 1 : Set G) := sup_le hL2 hQ
  obtain ⟨m, hm⟩ := hb₁
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 + 2 * k = -(b₁ : ℤ) := ⟨-((m : ℤ) + 1), by rw [hm]; push_cast; ring⟩
  have hZmap : (t.Zv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (-(b₁ : ℤ)) := by
    rw [← hk]
    exact map_qv_tau_pow 1 k
  have hGmap : (t.Gv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Gv (-(b₁ : ℤ)) := by
    rw [← hk]
    exact map_qv_tau_pow 1 k
  have hcent : t.Zv 0 ≤ centralizer (t.Zv (-(b₁ : ℤ)) : Set G) := by
    intro z hz w hw
    set g : G := (t.x₂ * t.x₁) ^ k with hg
    have hzG : g⁻¹ * z * g ∈ t.Gv 1 :=
      mem_map_conj_iff.mp (hGmap ▸ hZ1 hz)
    have hwZ : g⁻¹ * w * g ∈ t.Zv 1 := mem_map_conj_iff.mp (hZmap ▸ hw)
    obtain ⟨j, hj⟩ := t.isPGroup_Zv 0 ⟨z, hz⟩
    have hzj : z ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hzj' : (g⁻¹ * z * g) ^ 2 ^ j = 1 := by
      have h := conj_pow (a := g⁻¹) (b := z) (i := 2 ^ j)
      rw [inv_inv] at h
      rw [h, hzj]
      group
    have hmem : g⁻¹ * z * g ∈ L2 ⊔ Q2 L1 L2 S :=
      t.r4a_mem_of_pow_eq_one hfr (by rwa [t.Gv_one] at hzG) hzj'
    have h := mem_centralizer_iff.mp (hN hmem) (g⁻¹ * w * g) hwZ
    calc w * z = g * (g⁻¹ * w * g * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = z * w := by group
  exact hna ((commutator_eq_bot_iff_le_centralizer.mpr hcent).le.trans bot_le)

include t in
theorem mem_L2_sup_Q2_of_pow_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {x : G} (hx : x ∈ P2 L1 L2 S) {j : ℕ} (hxj : x ^ 2 ^ j = 1) :
    x ∈ L2 ⊔ Q2 L1 L2 S := by
  exact t.r4a_mem_of_pow_eq_one hfr hx hxj

private theorem r4b_conj_mem {H : Subgroup G} {g y : G} (hg : g ∈ normalizer (H : Set G))
    (hy : y ∈ H) : g * y * g⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hg y).mp hy

private theorem r4b_mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer ((centralizer (H : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ centralizer (H : Set G),
      g * y * g⁻¹ ∈ centralizer (H : Set G) := by
    intro g hg y hy
    rw [mem_centralizer_iff] at hy ⊢
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
      rwa [inv_inv] at this
    have hcomm := hy _ hh'
    calc h * (g * y * g⁻¹) = g * ((g⁻¹ * h * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
      _ = g * y * g⁻¹ * h := by group
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

private theorem r4b_map_Zv (i k : ℤ) :
    (t.Zv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (i + 2 * k) :=
  map_qv_tau_pow i k

private theorem r4b_map_Gv (i k : ℤ) :
    (t.Gv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Gv (i + 2 * k) :=
  map_qv_tau_pow i k

private theorem r4b_map_Gw (a b k : ℤ) :
    (t.Gw a b).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
      t.Gw (a + 2 * k) (b + 2 * k) :=
  map_win_tau_pow a b k

private theorem Zv_one_sub_le_Gw {b₀ : ℕ} (hb₀ : Even b₀) (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) :
    t.Zv (1 - b₀) ≤ t.Gw (1 - 2 * b₀) 1 := by
  obtain ⟨c, hc⟩ := hb₀
  have h := Subgroup.map_mono
    (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (-(c : ℤ)))).toMonoidHom) hZ0
  rw [t.r4b_map_Zv, t.r4b_map_Gw] at h
  have e1 : (1 : ℤ) + 2 * (-(c : ℤ)) = 1 - b₀ := by omega
  have e2 : (1 : ℤ) - b₀ + 2 * (-(c : ℤ)) = 1 - 2 * b₀ := by omega
  have e3 : (1 : ℤ) + b₀ + 2 * (-(c : ℤ)) = 1 := by omega
  rwa [e1, e2, e3] at h

private theorem Zv_one_sub_not_le_Gv_two {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀)) :
    ¬ t.Zv (1 - b₀) ≤ t.Gv 2 := by
  obtain ⟨c, hc⟩ := hb₀
  intro h
  apply hZ0'
  have h' := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (c : ℤ))).toMonoidHom) h
  rw [t.r4b_map_Zv, t.r4b_map_Gv] at h'
  have e1 : (1 : ℤ) - b₀ + 2 * (c : ℤ) = 1 := by omega
  have e2 : (2 : ℤ) + 2 * (c : ℤ) = 2 + b₀ := by omega
  rwa [e1, e2] at h'

theorem commutator_Zv_one_le_inf {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) :
    ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≤ t.Zv 1 ⊓ t.Zv (1 - b₀) := by
  have hY1 : t.Zv (1 - b₀) ≤ t.Gv 1 :=
    (t.Zv_one_sub_le_Gw hb₀ hZ0).trans (win_le_qv (by omega) le_rfl)
  have hZ1 : t.Zv 1 ≤ t.Gv (1 - b₀) := hZ0.trans (win_le_qv le_rfl (by omega))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine mem_inf.mpr ⟨?_, ?_⟩
  · have hyN : y ∈ normalizer (t.Zv 1 : Set G) := t.Gv_le_normalizer_Zv 1 (hY1 hy)
    have h1 : y * x⁻¹ * y⁻¹ ∈ t.Zv 1 := r4b_conj_mem hyN (inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hx h1
  · have hxN : x ∈ normalizer (t.Zv (1 - b₀) : Set G) :=
      t.Gv_le_normalizer_Zv _ (hZ1 hx)
    rw [commutatorElement_def]
    exact mul_mem (r4b_conj_mem hxN hy) (inv_mem hy)

theorem le_centralizer_of_commutator_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀))
    (h : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ = ⊥) : L2 ≤ centralizer (t.Zv 1 : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 1 ≤ b₀ := by
    by_contra hb
    have h0 : b₀ = 0 := by omega
    apply hZ0'
    rw [h0, Nat.cast_zero, add_zero]
    exact (t.Zv_le_Qv 1).trans (t.Qv_one_le_Gv_two hfr)
  have hYG : t.Zv (1 - b₀) ≤ t.Gw 0 1 :=
    (t.Zv_one_sub_le_Gw hb₀ hZ0).trans (win_mono (by omega) le_rfl)
  have hYS : t.Zv (1 - b₀) ≤ S := by
    have := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv _) hYG
    rwa [t.pCoreOf_Gw_zero_one hfr] at this
  have hYD : t.D2 ≤ normalizer (t.Zv (1 - b₀) : Set G) :=
    (t.D2_le_Gv _).trans (t.Gv_le_normalizer_Zv _)
  have hYQ : ¬ t.Zv (1 - b₀) ≤ t.Qv 1 := by
    intro hle
    have h2 := (t.Qv_le_Gv hfr 1).2
    rw [show (1 : ℤ) + 1 = 2 by norm_num] at h2
    exact t.Zv_one_sub_not_le_Gv_two hb₀ hZ0' (hle.trans h2)
  have hS : S ≤ t.Zv (1 - b₀) ⊔ t.Qv 1 := t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ
  have hYC : t.Zv (1 - b₀) ≤ centralizer (t.Zv 1 : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h
  have hQC : t.Qv 1 ≤ centralizer (t.Zv 1 : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 hz) q hq).symm
  have hx₂ : t.x₂ ∈ normalizer ((centralizer (t.Zv 1 : Set G) : Subgroup G) : Set G) := by
    have hx : t.x₂ ∈ t.Gv 1 := by
      rw [t.Gv_one]
      exact t.track.x₂_mem
    exact r4b_mem_normalizer_centralizer (t.Gv_le_normalizer_Zv 1 hx)
  have hT : S ⊓ L2 ≤ centralizer (t.Zv 1 : Set G) ⊔ t.Qv 1 :=
    inf_le_left.trans (hS.trans (sup_le_sup hYC le_rfl))
  have hL := t.L2_le_sup_Qv_one_of_sylow hfr hT hx₂
  rwa [sup_eq_left.mpr hQC] at hL

theorem L2_le_centralizer_of_l2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {Y C : Subgroup G} (hYS : Y ≤ S)
    (hYD : t.D2 ≤ normalizer (Y : Set G)) (hYQ : ¬ Y ≤ t.Qv 1) (hCZ : C ≤ t.Zv 1)
    (hY : Y ≤ centralizer (C : Set G)) (hx₂ : t.x₂ ∈ normalizer (C : Set G)) :
    L2 ≤ centralizer (C : Set G) := by
  have hS : S ≤ Y ⊔ t.Qv 1 := t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ
  have hQC : t.Qv 1 ≤ centralizer (C : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 (hCZ hz)) q hq).symm
  have hx : t.x₂ ∈ normalizer ((centralizer (C : Set G) : Subgroup G) : Set G) :=
    r4b_mem_normalizer_centralizer hx₂
  have hT : S ⊓ L2 ≤ centralizer (C : Set G) ⊔ t.Qv 1 :=
    inf_le_left.trans (hS.trans (sup_le_sup hY le_rfl))
  have hL := t.L2_le_sup_Qv_one_of_sylow hfr hT hx
  rwa [sup_eq_left.mpr hQC] at hL

private theorem r4c_map_conj_eq_of_mem {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

private theorem r4c_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite (G := ↥K) (H := H.subgroupOf K)

private theorem r4c_two_pow_mul (n : ℕ) : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
  rw [two_mul, pow_add]

private theorem r4c_P1_le_normalizer_Z1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem r4c_P2_le_normalizer_Z2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem r4c_Zv_comm (i : ℤ) {x y : G} (hx : x ∈ t.Zv i) (hy : y ∈ t.Zv i) :
    x * y = y * x :=
  (mem_centralizer_iff.mp (t.Zv_le_centralizer i hx) y (t.Zv_le_Qv i hy)).symm

private theorem r4c_sq_eq_one (i : ℤ) {e : G} (he : e ∈ t.Zv i) : e ^ 2 = 1 := by
  rw [t.Zv_eq i] at he
  exact A4.sq_eq_one_of_mem_omegaOneCenterOf he

private theorem r4c_pCoreOf_le_Qv_one (hF : Hyp111 L1 L2 S) : pCoreOf 2 L2 ≤ t.Qv 1 := by
  have h := Hyp111.pCoreOf_le_pCoreOf_vertex hF.symm
  rw [bigB_comm] at h
  rw [t.Qv_one]
  exact h

private theorem r4c_L2_le_Gv_one : L2 ≤ t.Gv 1 := by
  rw [t.Gv_one]
  exact le_sup_left

private theorem r4c_S_eq_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S = t.Qv 1 ⊔ (S ⊓ L2) := by
  have h := eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
    (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  rw [sup_comm] at h
  rw [t.Qv_one]
  exact h

private theorem r4c_ne_conj_x₂ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    S ⊓ L2 ≠ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hSQ : S = t.Qv 1 ⊔ (S ⊓ L2) := t.r4c_S_eq_sup_Qv_one hfr
  intro heq
  have hTG01 : S ⊓ L2 ≤ t.Gw 0 1 := inf_le_left.trans (t.S_le_Gw_zero_one hfr.hF)
  have hT'G12 : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ t.Gw 1 2 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hTG01
    have e := t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1
    rw [show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num] at e
    exact h.trans e.le
  have hTG02 : S ⊓ L2 ≤ t.Gw 0 2 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ 1 ∨ i = 2 by omega) with h3 | rfl
    · exact mem_win_iff.mp (hTG01 hy) i h1 h3
    · have hy' : y ∈ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := heq ▸ hy
      exact mem_win_iff.mp (hT'G12 hy') 2 (by norm_num) le_rfl
  have hTQ : S ⊓ L2 ≤ t.Qv 1 :=
    t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1) (by norm_num) (by norm_num)
      hTsyl.2.1 hTG02
  have hSle : S ≤ t.Qv 1 := hSQ.le.trans (sup_le le_rfl hTQ)
  have hQS : (t.Qv 1).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 1).1
  rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one, hQS] at h9
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

private theorem r4c_relCent_eq {L Q E : Subgroup G} (hQE : Q ≤ centralizer (E : Set G))
    (hL : L ≤ ⁅L, L⁆ ⊔ Q) :
    St84.relCent E (E ⊓ centralizer (L : Set G)) L = E ⊓ centralizer (L : Set G) := by
  set Z : Subgroup G := E ⊓ centralizer (L : Set G) with hZ
  have hZL : Z ≤ centralizer (L : Set G) := inf_le_right
  refine le_antisymm ?_ ?_
  · intro g hg
    have hg' : g ∈ St84.relCent E Z L := hg
    obtain ⟨hgE, -, -⟩ := hg'
    have hLgZ : ⁅L, zpowers g⁆ ≤ Z := by
      refine Subgroup.commutator_le.mpr fun a ha k hk => ?_
      have hk' : k ∈ St84.relCent E Z L := zpowers_le.mpr hg hk
      have h1 : ⁅k, a⁆ ∈ Z := hk'.2.2 a ha
      rw [← commutatorElement_inv]
      exact Z.inv_mem h1
    have h1 : ⁅⁅L, zpowers g⁆, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hLgZ.trans hZL)
    have h2 : ⁅⁅zpowers g, L⁆, L⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm (zpowers g) L] using h1
    have hLLcent : ⁅L, L⁆ ≤ centralizer (zpowers g : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
    have hLcent : L ≤ centralizer (zpowers g : Set G) :=
      hL.trans (sup_le hLLcent (hQE.trans (Subgroup.centralizer_le (zpowers_le.mpr hgE))))
    refine mem_inf.mpr ⟨hgE, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hLcent ha) g (Subgroup.mem_zpowers g)).symm
  · intro g hg
    obtain ⟨hgE, hgC⟩ := mem_inf.mp hg
    refine ⟨hgE, Subgroup.le_normalizer hg, fun a ha => ?_⟩
    have h1 : ⁅g, a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.mp hgC a ha).symm
    rw [h1]
    exact Z.one_mem

private theorem r4c_Zv_le_Gw {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) : t.Zv (1 - b₀) ≤ t.Gw (1 - 2 * b₀) 1 := by
  have h := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (-(c : ℤ)))).toMonoidHom) hZ0
  have e1 : (t.Zv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ (-(c : ℤ)))).toMonoidHom =
      t.Zv (1 - b₀) := by
    have := map_qv_tau_pow (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂)
      1 (-(c : ℤ))
    rw [show (1 : ℤ) + 2 * -(c : ℤ) = 1 - b₀ by omega] at this
    exact this
  have e2 : (t.Gw (1 - b₀) (1 + b₀)).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ (-(c : ℤ)))).toMonoidHom = t.Gw (1 - 2 * b₀) 1 := by
    have := map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂)
      (1 - b₀) (1 + b₀) (-(c : ℤ))
    rw [show (1 : ℤ) - b₀ + 2 * -(c : ℤ) = 1 - 2 * b₀ by omega,
      show (1 : ℤ) + b₀ + 2 * -(c : ℤ) = 1 by omega] at this
    exact this
  rw [e1, e2] at h
  exact h

private theorem r4c_not_Zv_le_Gv_two {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c)
    (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀)) : ¬ t.Zv (1 - b₀) ≤ t.Gv 2 := by
  intro h
  apply hZ0'
  have h' := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (c : ℤ))).toMonoidHom) h
  have e1 : (t.Zv (1 - b₀)).map (MulAut.conj ((t.x₂ * t.x₁) ^ (c : ℤ))).toMonoidHom =
      t.Zv 1 := by
    have := map_qv_tau_pow (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂)
      (1 - b₀) (c : ℤ)
    rw [show (1 : ℤ) - b₀ + 2 * (c : ℤ) = 1 by omega] at this
    exact this
  have e2 : (t.Gv 2).map (MulAut.conj ((t.x₂ * t.x₁) ^ (c : ℤ))).toMonoidHom =
      t.Gv (2 + b₀) := by
    have := map_qv_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂)
      2 (c : ℤ)
    rw [show (2 : ℤ) + 2 * (c : ℤ) = 2 + b₀ by omega] at this
    exact this
  rw [e1, e2] at h'
  exact h'

private theorem r4c_S_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c) (hb : 1 ≤ b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀)) :
    S ≤ t.Zv (1 - b₀) ⊔ t.Qv 1 := by
  refine t.S_le_sup_Qv_one_of_torus hfr (Y := t.Zv (1 - b₀)) ?_ ?_ ?_
  · have h1 : t.Zv (1 - b₀) ≤ t.Gw 0 1 :=
      (t.r4c_Zv_le_Gw hc hZ0).trans (win_mono (by omega) le_rfl)
    have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv _) h1
    rwa [t.pCoreOf_Gw_zero_one hfr] at h2
  · exact (t.D2_le_Gv _).trans (t.Gv_le_normalizer_Zv _)
  · intro h
    exact t.r4c_not_Zv_le_Gv_two hc hZ0' (h.trans (t.Qv_one_le_Gv_two hfr))

private theorem r4c_Zv_le_normalizer_C :
    t.Zv 1 ≤ normalizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) :=
  fun e he => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun c hc =>
    t.r4c_Zv_comm 1 (mem_inf.mp hc).1 he)

private theorem r4c_L2_le_normalizer_C :
    L2 ≤ normalizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) := by
  have h : L2 ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  exact h.trans (Subgroup.centralizer_le_normalizer _)

private theorem r4c_Qv_one_le_centralizer_Zv : t.Qv 1 ≤ centralizer (t.Zv 1 : Set G) :=
  Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1)

private theorem r4c_pCoreOf_le_centralizer_Zv (hF : Hyp111 L1 L2 S) :
    pCoreOf 2 L2 ≤ centralizer (t.Zv 1 : Set G) :=
  (t.r4c_pCoreOf_le_Qv_one hF).trans t.r4c_Qv_one_le_centralizer_Zv

private theorem r4c_isElemSec : CFSG.GH74.QTGen4.DSGen4.IsElemSec
    (t.Zv 1 ⊓ centralizer (L2 : Set G)) (t.Zv 1) := by
  refine ⟨inf_le_left, ?_, fun e he => ?_⟩
  · have h : ⁅t.Zv 1, t.Zv 1⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun e he =>
        mem_centralizer_iff.mpr fun h hh => t.r4c_Zv_comm 1 hh he
    rw [h]
    exact bot_le
  · rw [t.r4c_sq_eq_one 1 he]
    exact Subgroup.one_mem _

private theorem r4c_core (hF : Hyp111 L1 L2 S) :
    ∀ x ∈ pCoreOf 2 L2, ∀ e ∈ t.Zv 1, ⁅x, e⁆ ∈ t.Zv 1 ⊓ centralizer (L2 : Set G) := by
  intro x hx e he
  have h1 : ⁅x, e⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp (t.r4c_pCoreOf_le_centralizer_Zv hF hx) e he).symm
  rw [h1]
  exact Subgroup.one_mem _

private theorem r4c_core' (hF : Hyp111 L1 L2 S) :
    ⁅t.Zv 1, pCoreOf 2 L2⁆ ≤ t.Zv 1 ⊓ centralizer (L2 : Set G) := by
  have h : ⁅t.Zv 1, pCoreOf 2 L2⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mpr (t.r4c_pCoreOf_le_centralizer_Zv hF))
  rw [h]
  exact bot_le

private theorem r4c_relCent_L2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    St84.relCent (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G)) L2 =
      t.Zv 1 ⊓ centralizer (L2 : Set G) :=
  r4c_relCent_eq (Q := pCoreOf 2 L2) (t.r4c_pCoreOf_le_centralizer_Zv hfr.hF.1)
    (CFSG.Quasithin.F112R.le_commutator_sup_pCoreOf_of_isL2Quot hfr.hf hfr.hL2)

private theorem r4c_L2_le_normalizer_Zv : L2 ≤ normalizer (t.Zv 1 : Set G) :=
  (t.r4c_L2_le_Gv_one).trans (t.Gv_le_normalizer_Zv 1)

private theorem r4c_nontriv {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hC : ¬ L2 ≤ centralizer (t.Zv 1 : Set G)) :
    ∃ l ∈ L2, ∃ e ∈ t.Zv 1, ⁅l, e⁆ ∉ t.Zv 1 ⊓ centralizer (L2 : Set G) := by
  by_contra h
  push Not at h
  apply hC
  have hE : t.Zv 1 ≤ t.Zv 1 ⊓ centralizer (L2 : Set G) := by
    intro e he
    refine (t.r4c_relCent_L2 hfr).le ?_
    refine (St84.mem_relCent t.r4c_Zv_le_normalizer_C).mpr ⟨he, fun l hl => ?_⟩
    have h1 := h l hl e he
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ h1
  exact Subgroup.le_centralizer_iff.mp (hE.trans inf_le_right)

private theorem r4c_relIndex_relCent_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : ¬ Even v) {T₀ : Subgroup G}
    (hT₀ : T₀ ≤ t.Zv v ⊔ t.Qv 1)
    (hXw : t.Zv 1 ≤ t.Gw (v - 1) v ∨ t.Zv 1 ≤ t.Gw v (v + 1)) :
    (St84.relCent (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G)) T₀).relIndex (t.Zv 1) ≤ 2 ^ f := by
  have h1 : t.Zv 1 ⊓ t.Qv v ≤
      St84.relCent (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G)) T₀ := by
    intro e he
    obtain ⟨heE, heQ⟩ := mem_inf.mp he
    refine (St84.mem_relCent t.r4c_Zv_le_normalizer_C).mpr ⟨heE, fun x hx => ?_⟩
    have hK : T₀ ≤ centralizer ({e} : Set G) := by
      refine hT₀.trans (sup_le ?_ ?_)
      · intro y hy
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact mem_centralizer_iff.mp (t.Zv_le_centralizer v hy) _ heQ
      · intro q hq
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 heE) q hq).symm
    have h2 : e * x = x * e := mem_centralizer_iff.mp (hK hx) e (Set.mem_singleton e)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h2]
    exact Subgroup.one_mem _
  have h2 := Subgroup.relIndex_le_of_le_left (L := t.Zv 1) h1 (r4c_relIndex_ne_zero _ _)
  rw [Subgroup.inf_relIndex_left] at h2
  have h3 := t.relIndex_Qv_le hfr v (t.isPGroup_Zv 1) hXw
  rw [if_neg hv] at h3
  exact h2.trans h3

private theorem r4c_main {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀))
    (hC : ¬ L2 ≤ centralizer (t.Zv 1 : Set G)) :
    (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex (t.Zv 1) = 2 ^ (2 * f) ∧
      (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex
        (St84.relCent (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G)) (S ⊓ L2)) = 2 ^ f := by
  obtain ⟨c, hc'⟩ := hb₀
  have hc : (b₀ : ℤ) = 2 * c := by omega
  have hb : 1 ≤ b₀ := by
    by_contra h
    apply hZ0'
    rw [show (2 : ℤ) + b₀ = 2 by omega]
    exact (t.Zv_le_Qv 1).trans (t.Qv_one_le_Gv_two hfr)
  have hSY := t.r4c_S_le_sup hfr hc hb hZ0 hZ0'
  have hTY : S ⊓ L2 ≤ t.Zv (1 - b₀) ⊔ t.Qv 1 := inf_le_left.trans hSY
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hx₂L2 : t.x₂ ∈ normalizer (L2 : Set G) :=
    r4a_P2_le_normalizer_L2 hfr.hF.1 t.track.x₂_mem
  have hT'syl : IsSylowTwoOf ((S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) L2 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₂) hTsyl
    rwa [r4c_map_conj_eq_of_mem hx₂L2] at h
  have hT'Y : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ t.Zv (1 + b₀) ⊔ t.Qv 1 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hTY
    have hmZ : (t.Zv (1 - b₀)).map (MulAut.conj t.x₂).toMonoidHom = t.Zv (1 + b₀) := by
      have := t.track.map_qv_x₂ (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S)
        r4c_P1_le_normalizer_Z1 r4c_P2_le_normalizer_Z2 (1 - b₀)
      rw [show (2 : ℤ) - (1 - b₀) = 1 + b₀ by omega] at this
      exact this
    have hmQ : (t.Qv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 1 := by
      have := t.track.map_qv_x₂ (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S)
        (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) 1
      rw [show (2 : ℤ) - 1 = 1 by norm_num] at this
      exact this
    rw [Subgroup.map_sup, hmZ, hmQ] at h
    exact h
  have hgen : L2 ≤ ((S ⊓ L2) ⊔ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) ⊔ pCoreOf 2 L2 :=
    le_sup_pCoreOf_of_sylow_ne_of_l2
      (X := (S ⊓ L2) ⊔ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom)
      hfr.hf hfr.hL2 hTsyl hT'syl (t.r4c_ne_conj_x₂ hfr)
      (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hTq : (St84.relCent (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G)) (S ⊓ L2)).relIndex
      (t.Zv 1) ≤ 2 ^ f := by
    refine t.r4c_relIndex_relCent_le hfr (v := 1 - b₀) ?_ hTY (Or.inr ?_)
    · rw [Int.even_iff]
      omega
    · exact hZ0.trans (win_mono le_rfl (by omega))
  have hT'q : (St84.relCent (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G))
      ((S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom)).relIndex (t.Zv 1) ≤ 2 ^ f := by
    refine t.r4c_relIndex_relCent_le hfr (v := 1 + b₀) ?_ hT'Y (Or.inl ?_)
    · rw [Int.even_iff]
      omega
    · exact hZ0.trans (win_mono (by omega) le_rfl)
  have hne : t.Zv 1 ⊓ centralizer (L2 : Set G) ≠ t.Zv 1 := by
    intro h
    exact hC (Subgroup.le_centralizer_iff.mp (inf_eq_left.mp h))
  exact St84.relIndex_eq_two_pow_of_lines (L := L2) (E := t.Zv 1)
    (Z := t.Zv 1 ⊓ centralizer (L2 : Set G)) (T := S ⊓ L2)
    (T' := (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) (n := f)
    (by have := hfr.hf; omega) hfr.hL2 inf_le_left t.r4c_Zv_le_normalizer_C
    t.r4c_L2_le_normalizer_Zv t.r4c_L2_le_normalizer_C (t.isPGroup_Zv 1)
    (t.r4c_core' hfr.hF.1) inf_le_right hT'syl.1 hgen (t.r4c_relCent_L2 hfr) hne hTq hT'q

theorem exists_isNatSecOf_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀))
    (hC : ¬ L2 ≤ centralizer (t.Zv 1 : Set G)) :
    ∃ α : ↥L2 →* SL(2, GaloisField 2 f), Function.Surjective α ∧
      α.ker = (pCoreOf 2 L2).subgroupOf L2 ∧
      CFSG.Quasithin.F112R.St84.IsNatSecOf L2 (t.Zv 1) (t.Zv 1 ⊓ centralizer (L2 : Set G)) α := by
  obtain ⟨hcard, hline⟩ := t.r4c_main hfr hb₀ hZ0 hZ0' hC
  exact St84.exists_isNatSecOf_of_two_pow_le hfr.hf hfr.hL2 t.r4c_isElemSec
    (le_inf t.r4c_L2_le_normalizer_Zv t.r4c_L2_le_normalizer_C)
    (t.r4c_core hfr.hF.1) hcard (t.r4c_nontriv hfr hC) hfr.hF.1.h2.sylow hline.ge

theorem L2_le_centralizer_Zv_one_of_relIndex_lt {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hrel : (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex (t.Zv 1) < 2 ^ f * 2 ^ f) :
    L2 ≤ centralizer (t.Zv 1 : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hC
  have h := St84.two_pow_le_relIndex_of_nontrivial (by have := hfr.hf; omega) hfr.hL2
    t.r4c_isElemSec (le_inf t.r4c_L2_le_normalizer_Zv t.r4c_L2_le_normalizer_C)
    (t.r4c_core hfr.hF.1) (t.r4c_nontriv hfr hC)
  rw [r4c_two_pow_mul] at h
  omega

private theorem natural_Zv_one_of_isNatSecOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {α : ↥L2 →* SL(2, GaloisField 2 f)}
    (hα : Function.Surjective α) (hker : α.ker = (pCoreOf 2 L2).subgroupOf L2)
    (hnat : CFSG.Quasithin.F112R.St84.IsNatSecOf L2 (t.Zv 1) ⊥ α) :
    Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f ∧
      Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f ∧
      (∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 1 ⊓ centralizer (S : Set G)) ∧
      (∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z →
        z ∈ t.Zv 1 ⊓ centralizer (S : Set G)) ∧
      (∀ z ∈ t.Zv 1 ⊓ centralizer (S : Set G), z ≠ 1 →
        ∀ z' ∈ t.Zv 1 ⊓ centralizer (S : Set G), z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2G : L2 ≤ t.Gv 1 := by
    rw [t.Gv_one]
    exact le_sup_left
  have hZL : ∀ ℓ ∈ L2, ∀ z ∈ t.Zv 1, ℓ * z * ℓ⁻¹ ∈ t.Zv 1 := fun ℓ hℓ z hz =>
    (mem_normalizer_iff.mp (t.Gv_le_normalizer_Zv 1 (hL2G hℓ)) z).mp hz
  have hQZ : ∀ q ∈ t.Qv 1, ∀ z ∈ t.Zv 1, q * z * q⁻¹ = z := fun q hq z hz => by
    rw [mem_centralizer_iff.mp (t.Zv_le_centralizer 1 hz) q hq]
    group
  have hS_eq : S = t.Qv 1 ⊔ (S ⊓ L2) := by
    have h := eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
      (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
    rw [sup_comm] at h
    rw [t.Qv_one]
    exact h
  have hTnorm : S ⊓ L2 ≤ normalizer (t.Qv 1 : Set G) := by
    have h : P2 L1 L2 S ≤ normalizer (t.Qv 1 : Set G) := by
      rw [← t.Gv_one]
      exact t.Gv_le_normalizer_Qv 1
    exact inf_le_right.trans (le_sup_left.trans h)
  have hSdec : ∀ s ∈ S, ∃ q ∈ t.Qv 1, ∃ τ ∈ S ⊓ L2, s = q * τ := fun s hs =>
    (F1.mem_sup_iff_exists_mul_of_normalizes hTnorm).mp (hS_eq ▸ hs)
  have hSp : IsPGroup 2 ↥(S ⊓ L2) := hfr.hF.1.h2.sylow.2.1
  have hQ2le : pCoreOf 2 L2 ≤ t.Qv 1 := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
    rw [bigB_comm] at h
    rw [t.Qv_one]
    exact h
  have hkerQ : ∀ ℓ : ↥L2, α ℓ = 1 → (ℓ : G) ∈ t.Qv 1 := fun ℓ h => by
    have hm : ℓ ∈ α.ker := MonoidHom.mem_ker.mpr h
    rw [hker] at hm
    exact hQ2le (mem_subgroupOf.mp hm)
  have hSQ : ¬ S ⊓ L2 ≤ t.Qv 1 := by
    intro hTQ
    have hSle : S ≤ t.Qv 1 := hS_eq.le.trans (sup_le le_rfl hTQ)
    have hQS : (t.Qv 1).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
    have h9 := (t.relIndex_Qv_pCoreOf hfr 1).1
    rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one, hQS] at h9
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
    omega
  have hDL : t.D2 ≤ L2 := t.hD2hall.1.trans inf_le_left
  have hD2B : t.D2 ≤ bigB L1 L2 S := by
    rw [t.hBsplit]
    exact le_sup_right
  have hDS : ∀ d ∈ t.D2, ∀ s ∈ S, d⁻¹ * s * d ∈ S := fun d hd s hs => by
    have h := (mem_normalizer_iff.mp (inv_mem (hfr.hN (hD2B hd))) s).mp hs
    simpa using h
  have hDZ : ∀ d ∈ t.D2, ∀ z ∈ t.Zv 1, d * z * d⁻¹ ∈ t.Zv 1 := fun d hd z hz =>
    (mem_normalizer_iff.mp (t.Gv_le_normalizer_Zv 1 (t.D2_le_Gv 1 hd)) z).mp hz
  have hBt2 : BenderType (oTwoQuot ↥L2) f 1 1 :=
    BenderType.linear f hfr.hf (Classical.choice hfr.hL2)
  have hDcard : Nat.card t.D2 = 2 ^ f - 1 :=
    (card_isCyclic_of_hallTwoPrime hfr.hF.1.h2.sylow t.hD2hall t.hD2sup hBt2).1
  have hDker : ∀ d ∈ t.D2, ∀ hd : d ∈ L2, α ⟨d, hd⟩ = 1 → d = 1 := by
    intro d hd hdL h
    have hm : (⟨d, hdL⟩ : ↥L2) ∈ α.ker := MonoidHom.mem_ker.mpr h
    rw [hker] at hm
    have hbot : pCoreOf 2 L2 ⊓ t.D2 = ⊥ :=
      RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 L2) t.hD2hall.2.1
    have hmb : d ∈ (⊥ : Subgroup G) := hbot ▸ mem_inf.mpr ⟨mem_subgroupOf.mp hm, hd⟩
    exact Subgroup.mem_bot.mp hmb
  have hf0 : f ≠ 0 := by
    have := hfr.hf
    omega
  exact r4d_core hf0 hnat hZL hQZ hSdec hSp hkerQ hSQ hDL hDS hDZ t.hD2hall.2.1 hDcard hDker

private theorem r4e_map_Qv (i k : ℤ) :
    (t.Qv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Qv (i + 2 * k) :=
  map_qv_tau_pow i k

private theorem r4e_map_Gw_x₁ (a b : ℤ) :
    (t.Gw a b).map (MulAut.conj t.x₁).toMonoidHom = t.Gw (-b) (-a) :=
  t.track.map_win_x₁ Subgroup.le_normalizer Subgroup.le_normalizer a b

private theorem r4e_map_Qv_x₁ (i : ℤ) :
    (t.Qv i).map (MulAut.conj t.x₁).toMonoidHom = t.Qv (-i) :=
  t.track.map_qv_x₁ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i

private theorem r4e_conj_mul (g h : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem r4e_K_le_normalizer_map {Y : Subgroup G} {g : G}
    (hg : g ∈ normalizer (t.K : Set G)) (hY : t.K ≤ normalizer (Y : Set G)) :
    t.K ≤ normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro h hh
  have hh' : g⁻¹ * h * g ∈ t.K := by
    have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    rwa [inv_inv] at this
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have key : g⁻¹ * (h * y * h⁻¹) * g =
      (g⁻¹ * h * g) * (g⁻¹ * y * g) * (g⁻¹ * h * g)⁻¹ := by group
  rw [key]
  exact mem_normalizer_iff.mp (hY hh') _

private theorem r4e_S_le_Gv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S ≤ t.Gv 1 :=
  (t.S_le_Gw_zero_one hfr.hF).trans (win_le_qv (by norm_num) le_rfl)

private theorem r4e_relIndex_Qv_one_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : (t.Qv 1).relIndex S = 2 ^ f := by
  have h := (t.relIndex_Qv_pCoreOf hfr 1).1
  rwa [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one] at h

private theorem r4e_KI_of_conj {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {g : G} (hg : g ∈ normalizer (t.K : Set G)) {c : ℤ}
    {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYK : t.K ≤ normalizer (Y : Set G))
    (hYw : Y.map (MulAut.conj g).toMonoidHom ≤ t.Gw 0 1)
    (hQ : (t.Qv c).map (MulAut.conj g).toMonoidHom = t.Qv 1) :
    Y ≤ t.Qv c ∨ (t.Qv c).relIndex Y = 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY'2 : IsPGroup 2 (Y.map (MulAut.conj g).toMonoidHom) := hY2.map _
  have hY'S : Y.map (MulAut.conj g).toMonoidHom ≤ S := by
    have := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) hY'2 hYw
    rwa [t.pCoreOf_Gw_zero_one hfr] at this
  have hY'D : t.D2 ≤ normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    t.D2_le_K.trans (t.r4e_K_le_normalizer_map hg hYK)
  by_cases h : Y.map (MulAut.conj g).toMonoidHom ≤ t.Qv 1
  · left
    rw [← hQ] at h
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp h
  · right
    have hS := t.S_le_sup_Qv_one_of_torus hfr hY'S hY'D h
    have hQS : t.Qv 1 ≤ S := by
      rw [t.Qv_one]
      exact Q2_le_S hfr.hF
    have hYQ : Y.map (MulAut.conj g).toMonoidHom ⊔ t.Qv 1 = S :=
      le_antisymm (sup_le hY'S hQS) hS
    have hYN : Y.map (MulAut.conj g).toMonoidHom ≤ normalizer (t.Qv 1 : Set G) :=
      hY'S.trans ((t.r4e_S_le_Gv_one hfr).trans (t.Gv_le_normalizer_Qv 1))
    have h1 := C5.relIndex_sup_eq_of_le_normalizer hYN
    rw [hYQ, t.r4e_relIndex_Qv_one_S hfr] at h1
    rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) (t.Qv c) Y
      (MulAut.conj g).injective, hQ]
    exact h1.symm

private theorem r4e_KI_right {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : Odd v) {Y : Subgroup G} (hY2 : IsPGroup 2 Y)
    (hYK : t.K ≤ normalizer (Y : Set G)) (hYw : Y ≤ t.Gw (v - 1) v) :
    Y ≤ t.Qv v ∨ (t.Qv v).relIndex Y = 2 ^ f := by
  obtain ⟨j, rfl⟩ := hv
  refine t.r4e_KI_of_conj hfr (g := (t.x₂ * t.x₁) ^ (-j))
    (zpow_mem t.track.tau_mem_normalizer _) hY2 hYK ?_ ?_
  · have hmap : (t.Gw (2 * j + 1 - 1) (2 * j + 1)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ (-j))).toMonoidHom = t.Gw 0 1 := by
      rw [t.r4b_map_Gw, show 2 * j + 1 - 1 + 2 * -j = 0 by ring,
        show 2 * j + 1 + 2 * -j = 1 by ring]
    exact (Subgroup.map_mono hYw).trans hmap.le
  · rw [t.r4e_map_Qv, show 2 * j + 1 + 2 * -j = 1 by ring]

private theorem r4e_KI_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : Odd v) {Y : Subgroup G} (hY2 : IsPGroup 2 Y)
    (hYK : t.K ≤ normalizer (Y : Set G)) (hYw : Y ≤ t.Gw v (v + 1)) :
    Y ≤ t.Qv v ∨ (t.Qv v).relIndex Y = 2 ^ f := by
  obtain ⟨j, rfl⟩ := hv
  refine t.r4e_KI_of_conj hfr (g := (t.x₂ * t.x₁) ^ (j + 1) * t.x₁)
    (mul_mem (zpow_mem t.track.tau_mem_normalizer _) t.track.x₁_norm) hY2 hYK ?_ ?_
  · have hmap : (t.Gw (2 * j + 1) (2 * j + 1 + 1)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ (j + 1) * t.x₁)).toMonoidHom = t.Gw 0 1 := by
      rw [r4e_conj_mul, t.r4e_map_Gw_x₁, t.r4b_map_Gw,
        show -(2 * j + 1 + 1) + 2 * (j + 1) = 0 by ring,
        show -(2 * j + 1) + 2 * (j + 1) = 1 by ring]
    exact (Subgroup.map_mono hYw).trans hmap.le
  · rw [r4e_conj_mul, t.r4e_map_Qv_x₁, t.r4e_map_Qv, show -(2 * j + 1) + 2 * (j + 1) = 1 by ring]

private theorem r4e_inf_Gv_sub_le {Y : Subgroup G} {u w : ℤ} (h : u - 1 ≤ w)
    (hY : Y ≤ t.Gw u w) : Y ⊓ t.Gv (u - 1) ≤ t.Gw (u - 1) w := by
  rw [show t.Gw (u - 1) w = t.Gv (u - 1) ⊓ t.Gw u w from win_sub_one_left h, inf_comm]
  exact inf_le_inf_left _ hY

private theorem r4e_inf_Gv_add_le {Y : Subgroup G} {u w : ℤ} (h : u ≤ w + 1)
    (hY : Y ≤ t.Gw u w) : Y ⊓ t.Gv (w + 1) ≤ t.Gw u (w + 1) := by
  rw [show t.Gw u (w + 1) = t.Gw u w ⊓ t.Gv (w + 1) from win_add_one_right h]
  exact inf_le_inf_right _ hY

private theorem r4e_Zv_eq_bot_of_m_zero {m : ℕ} (hm0 : m = 0)
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥) : t.Zv 0 = ⊥ := by
  have h0 : pCoreOf 2 (t.Gv 0) = ⊥ := by
    have h := hwlog 0
    simp only [hm0, Nat.cast_zero, mul_zero, sub_zero] at h
    rwa [show t.Gw 0 0 = t.Gv 0 from win_self 0] at h
  refine le_bot_iff.mp ((t.Zv_le_Qv 0).trans ?_)
  rw [t.Qv_eq 0, h0]

private theorem r4e_pCoreOf_Gw_eq_bot {m : ℕ} (hm : Even m)
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥) :
    pCoreOf 2 (t.Gw (-m) m) = ⊥ := by
  obtain ⟨c, hc⟩ := hm
  have h := hwlog (c : ℤ)
  rwa [show 2 * (c : ℤ) - 2 * m = -m by omega, show 2 * (c : ℤ) = m by omega] at h

private theorem r4e_Zv_le_Gw {m : ℕ} (hm2 : 2 ≤ m) (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1)) :
    t.Zv 0 ≤ t.Gw (1 - m) (1 - m + 1) :=
  hZ1.trans (win_mono le_rfl (by omega))

private theorem r4e_X_le_Gw_full {m : ℕ} (hm2 : 2 ≤ m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1)) : t.Zv 0 ⊓ t.Gv (-m) ≤ t.Gw (-m) (m - 1) := by
  have h := t.r4e_inf_Gv_sub_le (u := 1 - m) (w := m - 1) (by omega) hZ1
  rwa [show (1 : ℤ) - m - 1 = -m by ring] at h

private theorem r4e_X_le_Gw {m : ℕ} (hm2 : 2 ≤ m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1)) :
    t.Zv 0 ⊓ t.Gv (-m) ≤ t.Gw (m - 1 - 1) (m - 1) :=
  (t.r4e_X_le_Gw_full hm2 hZ1).trans (win_mono (by omega) le_rfl)

private theorem r4e_X_inf_Gv_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥) :
    (t.Zv 0 ⊓ t.Gv (-m)) ⊓ t.Gv m = ⊥ := by
  have h := t.r4e_inf_Gv_add_le (u := -m) (w := m - 1) (by omega) (t.r4e_X_le_Gw_full hm2 hZ1)
  rw [show (m : ℤ) - 1 + 1 = m by ring] at h
  have h2 := t.le_pCoreOf_Gw hfr (u := -m) (w := m) (by omega)
    ((t.isPGroup_Zv 0).to_le (inf_le_left.trans inf_le_left)) h
  rw [t.r4e_pCoreOf_Gw_eq_bot hm hwlog] at h2
  exact le_bot_iff.mp h2

private theorem r4e_card_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥) :
    Nat.card (t.Zv 0) ≤ 2 ^ f * Nat.card ↥(t.Zv 0 ⊓ t.Gv (-m)) ∧
      Nat.card ↥(t.Zv 0 ⊓ t.Gv (-m)) ≤ 2 ^ f := by
  obtain ⟨c, hc⟩ := hm
  have hodd1 : ¬ Even (1 - (m : ℤ)) := by
    rintro ⟨d, hd⟩
    omega
  have hodd2 : ¬ Even ((m : ℤ) - 1) := by
    rintro ⟨d, hd⟩
    omega
  have h1 := t.card_le_mul_card_inf_Gv_sub_one hfr (1 - m) (t.isPGroup_Zv 0)
    (t.r4e_Zv_le_Gw hm2 hZ1)
  rw [if_neg hodd1, show (1 : ℤ) - m - 1 = -m by ring] at h1
  have h2 := t.card_le_mul_card_inf_Gv_add_one hfr (m - 1)
    ((t.isPGroup_Zv 0).to_le inf_le_left) (t.r4e_X_le_Gw hm2 hZ1)
  rw [if_neg hodd2, show (m : ℤ) - 1 + 1 = m by ring,
    t.r4e_X_inf_Gv_eq_bot hfr ⟨c, hc⟩ hm2 hZ1 hwlog, Subgroup.card_bot, mul_one] at h2
  exact ⟨h1, h2⟩

theorem card_Zv_zero_le_of_B {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m : ℕ} (hm : Even m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥) :
    Nat.card (t.Zv 0) ≤ 2 ^ f * 2 ^ f := by
  by_cases hm0 : m = 0
  · rw [t.r4e_Zv_eq_bot_of_m_zero hm0 hwlog, Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · have hm2 : 2 ≤ m := by
      obtain ⟨c, hc⟩ := hm
      omega
    obtain ⟨h1, h2⟩ := t.r4e_card_le hfr hm hm2 hZ1 hwlog
    exact h1.trans (Nat.mul_le_mul_left _ h2)

theorem eq_or_eq_of_B {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m : ℕ} (hm : Even m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (hcard : Nat.card (t.Zv 0) = 2 ^ f * 2 ^ f) {A B : Subgroup G} (hA : Nat.card A = 2 ^ f)
    (hAK : t.K ≤ normalizer (A : Set G)) (hAB : A ≤ B) (hB : B ≤ t.Zv 0)
    (hBK : t.K ≤ normalizer (B : Set G)) : B = A ∨ B = t.Zv 0 := by
  have hr : 0 < 2 ^ f := by positivity
  have hr4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  have hm0 : m ≠ 0 := by
    intro hm0
    have h1 := hcard
    rw [t.r4e_Zv_eq_bot_of_m_zero hm0 hwlog, Subgroup.card_bot] at h1
    have h2 := Nat.mul_le_mul hr4 hr4
    omega
  obtain ⟨c, hc⟩ := hm
  have hm2 : 2 ≤ m := by omega
  have hodd1 : Odd (1 - (m : ℤ)) := ⟨-(c : ℤ), by omega⟩
  have hodd2 : Odd ((m : ℤ) - 1) := ⟨(c : ℤ) - 1, by omega⟩
  have hm' : Even m := ⟨c, hc⟩
  obtain ⟨hc1, hc2⟩ := t.r4e_card_le hfr hm' hm2 hZ1 hwlog
  have hXbot := t.r4e_X_inf_Gv_eq_bot hfr hm' hm2 hZ1 hwlog
  have hXw := t.r4e_X_le_Gw hm2 hZ1
  have hZw := t.r4e_Zv_le_Gw hm2 hZ1
  set X : Subgroup G := t.Zv 0 ⊓ t.Gv (-m) with hX
  have hXZ : X ≤ t.Zv 0 := inf_le_left
  have hXG : X ≤ t.Gv (-m) := inf_le_right
  have hXp : IsPGroup 2 X := (t.isPGroup_Zv 0).to_le hXZ
  have hXr : Nat.card X = 2 ^ f := by
    have h : 2 ^ f * 2 ^ f ≤ 2 ^ f * Nat.card X := hcard ▸ hc1
    exact le_antisymm hc2 (Nat.le_of_mul_le_mul_left h hr)
  have hXK : t.K ≤ normalizer (X : Set G) := fun h hh =>
    A4.mem_normalizer_inf (t.Gv_le_normalizer_Zv 0 (t.K_le_Gv 0 hh))
      (Subgroup.le_normalizer (t.K_le_Gv (-m) hh))
  have partA : ∀ Y : Subgroup G, Y ≤ X → t.K ≤ normalizer (Y : Set G) → Y = ⊥ ∨ Y = X := by
    intro Y hYX hYK
    have hYp : IsPGroup 2 Y := hXp.to_le hYX
    rcases t.r4e_KI_right hfr hodd2 hYp hYK (hYX.trans hXw) with h | h
    · left
      have h1 := (t.inf_Gv_eq_inf_Qv hfr (m - 1) hXp).1 hXw
      rw [show (m : ℤ) - 1 + 1 = m by ring, hXbot] at h1
      exact le_bot_iff.mp (le_trans (le_inf hYX h) h1.symm.le)
    · right
      have h2 := Subgroup.relIndex_mul_card (t.Qv (m - 1)) Y
      rw [h] at h2
      have h3 : 2 ^ f ≤ Nat.card Y := by
        rw [← h2]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      exact Subgroup.eq_of_le_of_card_ge hYX (hXr ▸ h3)
  have partB : ∀ Y : Subgroup G, X ≤ Y → Y ≤ t.Zv 0 → t.K ≤ normalizer (Y : Set G) →
      Y = X ∨ Y = t.Zv 0 := by
    intro Y hXY hYZ hYK
    have hYp : IsPGroup 2 Y := (t.isPGroup_Zv 0).to_le hYZ
    have hYw : Y ≤ t.Gw (1 - m) (1 - m + 1) := hYZ.trans hZw
    have hYX : Y ⊓ t.Qv (1 - m) = X := by
      have h1 := (t.inf_Gv_eq_inf_Qv hfr (1 - m) hYp).2 hYw
      rw [show (1 : ℤ) - m - 1 = -m by ring] at h1
      rw [← h1]
      exact le_antisymm (le_inf (inf_le_left.trans hYZ) inf_le_right) (le_inf hXY hXG)
    rcases t.r4e_KI_left hfr hodd1 hYp hYK hYw with h | h
    · left
      rw [← hYX]
      exact (inf_eq_left.mpr h).symm
    · right
      have h2 := Subgroup.relIndex_mul_card (t.Qv (1 - m)) Y
      rw [h, inf_comm, hYX, hXr] at h2
      exact Subgroup.eq_of_le_of_card_ge hYZ (by rw [hcard, h2])
  have hBXK : t.K ≤ normalizer ((B ⊓ X : Subgroup G) : Set G) := fun h hh =>
    A4.mem_normalizer_inf (hBK hh) (hXK hh)
  rcases partA (B ⊓ X) inf_le_right hBXK with h | h
  · left
    have h1 : Nat.card B ≤ 2 ^ f := by
      have h2 := Subgroup.relIndex_mul_card X B
      rw [inf_comm, h, Subgroup.card_bot, mul_one] at h2
      have h3 := Subgroup.relIndex_mul_card X (t.Zv 0)
      rw [inf_eq_left.mpr hXZ, hXr, hcard] at h3
      have h4 : X.relIndex (t.Zv 0) = 2 ^ f := Nat.eq_of_mul_eq_mul_right hr h3
      have h5 : X.relIndex B ≤ X.relIndex (t.Zv 0) :=
        Subgroup.relIndex_le_of_le_right hB (by rw [h4]; exact hr.ne')
      rw [← h2]
      exact h5.trans h4.le
    exact (Subgroup.eq_of_le_of_card_ge hAB (by rw [hA]; exact h1)).symm
  · have hXB : X ≤ B := inf_eq_right.mp h
    rcases partB B hXB hB hBK with h' | h'
    · left
      have hAX : A = X :=
        Subgroup.eq_of_le_of_card_ge (h' ▸ hAB) (by rw [hXr, hA])
      exact h'.trans hAX.symm
    · right
      exact h'

private theorem r4f_mem_normalizer_of_map_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have h1 : g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * (g * y * g⁻¹) * g ∈ H :=
    mem_map_conj_iff
  rw [h, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  exact h1.symm

private theorem r4f_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf, hA x, hB x]

private theorem r4f_mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

private theorem r4f_mem_Gv_neg_iff (i : ℤ) {y : G} :
    y ∈ t.Gv i ↔ t.x₁⁻¹ * y * t.x₁ ∈ t.Gv (-i) :=
  t.track.mem_qv_neg_iff Subgroup.le_normalizer Subgroup.le_normalizer i

private theorem r4f_mem_Gv_two_sub_iff (i : ℤ) {y : G} :
    y ∈ t.Gv i ↔ t.x₂⁻¹ * y * t.x₂ ∈ t.Gv (2 - i) :=
  t.track.mem_qv_two_sub_iff Subgroup.le_normalizer Subgroup.le_normalizer i

private theorem r4f_map_Zv_of_map_Gv {i j : ℤ} {g : G}
    (h : (t.Gv i).map (MulAut.conj g).toMonoidHom = t.Gv j) :
    (t.Zv i).map (MulAut.conj g).toMonoidHom = t.Zv j := by
  rw [t.Zv_eq i, t.Zv_eq j, t.Qv_eq i, t.Qv_eq j,
    omegaOneCenterOf_map_mulEquiv (MulAut.conj g),
    ← pCoreOf_map_mulEquiv 2 (MulAut.conj g), h]

private theorem r4f_Zv_zero_ne_bot (hF : F112HypW L1 L2 S) :
    t.Zv 0 ≠ ⊥ := by
  rw [t.Zv_zero]
  intro hbot
  have h1 : omegaOneCenterOf S ≤ Z1 L1 L2 S := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf hF.1
  exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1 (le_bot_iff.mp (hbot ▸ h1))

private theorem r4f_exists_L2_not_mem_bigB
    (hF : Hyp111 L1 L2 S) : ∃ g ∈ L2, g ∉ bigB L1 L2 S := by
  have hR' : Hyp111R L2 L1 S := Hyp111R.symm (Hyp111R.of_hyp111 rankOneListedFacts hF)
  have hlt : L2 ⊓ bigB L2 L1 S < L2 := by
    rw [CFSG.Quasithin.F1.inf_bigB_eq_borelOf hR']
    exact CFSG.Quasithin.F1.lt_borelOf hR'
  obtain ⟨g0, hg0L2, hg0B⟩ := SetLike.exists_of_lt hlt
  exact ⟨g0, hg0L2, fun h => hg0B ⟨hg0L2, by rwa [bigB_comm]⟩⟩

private theorem r4f_bruhat_base {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {p : G} (hp : p ∈ P2 L1 L2 S) (hpB : p ∉ bigB L1 L2 S) :
    ∃ b ∈ bigB L1 L2 S, ∃ e ∈ bigB L1 L2 S, b * p = t.x₂ * e := by
  obtain ⟨g, hgL2, hgB⟩ := r4f_exists_L2_not_mem_bigB hfr.hF.1
  have hx₂B : t.x₂ ∉ bigB L1 L2 S := fun h =>
    t.track.x₂_not_mem ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) h)
  have hp' := (mem_bigB_or_mem_doubleCoset_p2 hfr.hf hfr.hF hfr.hL2 hgL2 hgB hp).resolve_left hpB
  have hx' := (mem_bigB_or_mem_doubleCoset_p2 hfr.hf hfr.hF hfr.hL2 hgL2 hgB
    t.track.x₂_mem).resolve_left hx₂B
  rw [Set.mem_mul] at hp' hx'
  obtain ⟨y, hy, b3, hb3, hp_eq⟩ := hp'
  obtain ⟨z, hz, c3, hc3, hx_eq⟩ := hx'
  rw [Set.mem_mul] at hy hz
  obtain ⟨b1, hb1, g1, hg1, hy_eq⟩ := hy
  obtain ⟨c1, hc1, g2, hg2, hz_eq⟩ := hz
  rw [Set.mem_singleton_iff] at hg1 hg2
  rw [hg1] at hy_eq
  rw [hg2] at hz_eq
  have hp_eq' : p = b1 * g * b3 := by rw [← hp_eq, ← hy_eq]
  have hx_eq' : t.x₂ = c1 * g * c3 := by rw [← hx_eq, ← hz_eq]
  refine ⟨c1 * b1⁻¹, mul_mem hc1 (inv_mem hb1), c3⁻¹ * b3, mul_mem (inv_mem hc3) hb3, ?_⟩
  rw [hp_eq', hx_eq']
  group

private theorem r4f_bruhat_neg_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {p : G} (hp : p ∈ t.Gv (-1)) (hp0 : p ∉ t.Gv 0) :
    ∃ b ∈ t.Gv (-1), b ∈ t.Gv 0 ∧
      (t.Gv 0).map (MulAut.conj (b * p)).toMonoidHom = t.Gv (-2) := by
  have hx₁0 : t.x₁ ∈ t.Gv 0 := by
    rw [t.Gv_zero]
    exact t.track.x₁_mem
  have hp' : t.x₁⁻¹ * p * t.x₁ ∈ P2 L1 L2 S := by
    have h := (t.r4f_mem_Gv_neg_iff (-1)).mp hp
    rwa [neg_neg, t.Gv_one] at h
  have hp'B : t.x₁⁻¹ * p * t.x₁ ∉ bigB L1 L2 S := by
    intro h
    apply hp0
    have h0 : t.x₁⁻¹ * p * t.x₁ ∈ t.Gv 0 := by
      rw [t.Gv_zero]
      exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) h
    have := mul_mem (mul_mem hx₁0 h0) (inv_mem hx₁0)
    rwa [show t.x₁ * (t.x₁⁻¹ * p * t.x₁) * t.x₁⁻¹ = p by group] at this
  obtain ⟨b', hb', e, he, hbe⟩ := t.r4f_bruhat_base hfr hp' hp'B
  have hb'1 : b' ∈ t.Gv 0 := by
    rw [t.Gv_zero]
    exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hb'
  have hb'2 : b' ∈ t.Gv 1 := by
    rw [t.Gv_one]
    exact (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hb'
  have he0 : e ∈ t.Gv 0 := by
    rw [t.Gv_zero]
    exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) he
  refine ⟨t.x₁ * b' * t.x₁⁻¹, ?_, mul_mem (mul_mem hx₁0 hb'1) (inv_mem hx₁0), ?_⟩
  · rw [t.r4f_mem_Gv_neg_iff (-1), neg_neg,
      show t.x₁⁻¹ * (t.x₁ * b' * t.x₁⁻¹) * t.x₁ = b' by group]
    exact hb'2
  · ext y
    rw [mem_map_conj_iff]
    have hbp : (t.x₁ * b' * t.x₁⁻¹) * p = t.x₁ * (t.x₂ * e) * t.x₁⁻¹ := by
      rw [← hbe]
      group
    have hc : t.x₁ * e⁻¹ ∈ t.Gv 0 := mul_mem hx₁0 (inv_mem he0)
    have key : (t.x₁ * (t.x₂ * e) * t.x₁⁻¹)⁻¹ * y * (t.x₁ * (t.x₂ * e) * t.x₁⁻¹) =
        (t.x₁ * e⁻¹) * (t.x₂⁻¹ * (t.x₁⁻¹ * y * t.x₁) * t.x₂) * (t.x₁ * e⁻¹)⁻¹ := by
      group
    rw [hbp, key]
    have hcw : ∀ w : G, (t.x₁ * e⁻¹) * w * (t.x₁ * e⁻¹)⁻¹ ∈ t.Gv 0 ↔ w ∈ t.Gv 0 := by
      intro w
      constructor
      · intro h
        have := mul_mem (mul_mem (inv_mem hc) h) hc
        rwa [show (t.x₁ * e⁻¹)⁻¹ * ((t.x₁ * e⁻¹) * w * (t.x₁ * e⁻¹)⁻¹) * (t.x₁ * e⁻¹) = w by
          group] at this
      · intro h
        exact mul_mem (mul_mem hc h) (inv_mem hc)
    rw [hcw]
    have h1 := t.r4f_mem_Gv_two_sub_iff 2 (y := t.x₁⁻¹ * y * t.x₁)
    have h2 := t.r4f_mem_Gv_neg_iff (-2) (y := y)
    rw [sub_self] at h1
    rw [neg_neg] at h2
    exact h1.symm.trans h2.symm

private theorem r4f_le_Gv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hO4 : t.GT = t.K) {b₁ : ℕ} (hb₁ : Odd b₁)
    (hZ1 : t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) b₁) (hZh : t.Zv (-(b₁ : ℤ)) ≤ t.Gv (-1)) :
    t.Zv (-(b₁ : ℤ)) ⊓ centralizer (t.Zv 0 : Set G) ≤ t.Gv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  by_contra hx0
  obtain ⟨hxZ, hxC⟩ := mem_inf.mp hx
  obtain ⟨b, -, hb0, hmap⟩ := t.r4f_bruhat_neg_one hfr (hZh hxZ) hx0
  have hZmap := t.r4f_map_Zv_of_map_Gv hmap
  have hbN : b ∈ normalizer (t.Zv 0 : Set G) := t.Gv_le_normalizer_Zv 0 hb0
  have hxN : x ∈ normalizer (t.Zv 0 : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  have hZeq : t.Zv (-2) = t.Zv 0 := by
    rw [← hZmap]
    exact r4c_map_conj_eq_of_mem (mul_mem hbN hxN)
  have hτinv : (t.x₂ * t.x₁) ^ (-1 : ℤ) ∈ normalizer (t.Zv 0 : Set G) := by
    apply r4f_mem_normalizer_of_map_eq
    rw [t.r4b_map_Zv, show (0 : ℤ) + 2 * (-1) = -2 by norm_num]
    exact hZeq
  have hτ : t.x₂ * t.x₁ ∈ normalizer (t.Zv 0 : Set G) := by
    have := inv_mem hτinv
    rwa [zpow_neg_one, inv_inv] at this
  have hZk : ∀ k : ℤ, t.Zv (0 + 2 * k) = t.Zv 0 := fun k => by
    rw [← t.r4b_map_Zv 0 k]
    exact r4c_map_conj_eq_of_mem (zpow_mem hτ k)
  have hb₁pos : 1 ≤ (b₁ : ℤ) := by
    have := hb₁.pos
    omega
  have hZ0G : t.Zv 0 ≤ t.Gv 0 := hZ1.trans (win_le_qv (by omega) (by omega))
  have hZ1G : t.Zv 0 ≤ t.Gv 1 := hZ1.trans (win_le_qv (by omega) (by omega))
  have hZG : ∀ i : ℤ, t.Zv 0 ≤ t.Gv i := by
    intro i
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · have h := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) hZ0G
      rw [t.r4b_map_Zv, t.r4b_map_Gv, hZk k] at h
      rwa [zero_add] at h
    · have h := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) hZ1G
      rw [t.r4b_map_Zv, t.r4b_map_Gv, hZk k] at h
      rwa [add_comm] at h
  have hZK : t.Zv 0 ≤ t.K := by
    rw [← hO4]
    exact le_iInf hZG
  have hdisj : Disjoint t.K (t.Zv 0) :=
    TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup t.hHall.2.1.not_two_dvd_nat (t.isPGroup_Zv 0)
  exact t.r4f_Zv_zero_ne_bot hfr.hF ((Subgroup.eq_bot_iff_forall _).mpr fun z hz =>
    Subgroup.disjoint_def.mp hdisj (hZK hz) hz)

private theorem r4f_K_le_normalizer_map {H : Subgroup G} (hH : t.K ≤ normalizer (H : Set G)) :
    t.K ≤ normalizer ((H.map (MulAut.conj t.x₁).toMonoidHom : Subgroup G) : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have hk' : t.x₁⁻¹ * k * t.x₁ ∈ t.K := by
    have := (mem_normalizer_iff.mp (inv_mem t.track.x₁_norm) k).mp hk
    rwa [inv_inv] at this
  have key : t.x₁⁻¹ * (k * y * k⁻¹) * t.x₁ =
      (t.x₁⁻¹ * k * t.x₁) * (t.x₁⁻¹ * y * t.x₁) * (t.x₁⁻¹ * k * t.x₁)⁻¹ := by
    group
  rw [key]
  exact mem_normalizer_iff.mp (hH hk') _

private theorem r4f_L1_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {Y : Subgroup G} (hYS : Y ≤ S)
    (hYC : Y ≤ centralizer (t.Zv 0 : Set G)) (hYQ : ¬ Y ≤ t.Qv 0)
    (hYD : t.D1 ≤ normalizer (Y : Set G)) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hQ1le : pCoreOf 2 L1 ≤ t.Qv 0 := by
    rw [t.Qv_zero]
    exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1
  have hL1P : L1 ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact le_sup_left
  have hSP : S ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hQC : t.Qv 0 ≤ t.Gv 0 ⊓ centralizer (t.Zv 0 : Set G) := by
    refine le_inf (t.Qv_le_Gv_self 0) fun q hq => ?_
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hz) q hq).symm
  have hPC : t.Gv 0 ≤ normalizer ((t.Gv 0 ⊓ centralizer (t.Zv 0 : Set G) : Subgroup G) : Set G) :=
    fun p hp => r4f_mem_normalizer_inf (Subgroup.le_normalizer hp)
      (r4b_mem_normalizer_centralizer (t.Gv_le_normalizer_Zv 0 hp))
  have hSQ : S = t.Qv 0 ⊔ (S ⊓ L1) := by
    have h := eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
    rw [sup_comm] at h
    rw [t.Qv_zero]
    exact h
  have hTN : S ⊓ L1 ≤ normalizer (t.Qv 0 : Set G) :=
    (inf_le_right.trans hL1P).trans (t.Gv_le_normalizer_Qv 0)
  have hD1T : t.D1 ≤ normalizer ((S ⊓ L1 : Subgroup G) : Set G) := t.hD1hall.1.trans inf_le_right
  have hD1Q : t.D1 ≤ normalizer (t.Qv 0 : Set G) :=
    (le_sup_left : t.D1 ≤ t.K).trans ((t.K_le_Gv 0).trans (t.Gv_le_normalizer_Qv 0))
  have hXN : t.D1 ≤ normalizer (((Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) : Subgroup G) : Set G) := by
    intro d hd
    exact r4f_mem_normalizer_inf (r4f_mem_normalizer_sup (hYD hd) (hD1Q hd)) (hD1T hd)
  have hXnot : ¬ ((Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) ≤ pCoreOf 2 L1) := by
    intro hX
    apply hYQ
    intro y hy
    have hyS : y ∈ t.Qv 0 ⊔ (S ⊓ L1) := hSQ.le (hYS hy)
    obtain ⟨q, hq, τ, hτ, hyqτ⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTN).mp hyS
    have hτy : τ = q⁻¹ * y := by
      rw [hyqτ]
      group
    have hτX : τ ∈ (Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) := by
      refine ⟨?_, hτ⟩
      rw [hτy]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hy)
    rw [hyqτ]
    exact mul_mem hq (hQ1le (hX hτX))
  have hKI := mem_sup_pCoreOf_of_torus_of_sz hfr.ha hfr.hSz hTsyl t.hD1hall inf_le_right hXN hXnot
  have hXC : (Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) ⊔ pCoreOf 2 L1 ≤ t.Gv 0 ⊓ centralizer (t.Zv 0 : Set G) :=
    sup_le (inf_le_left.trans (sup_le (le_inf (hYS.trans hSP) hYC) hQC)) (hQ1le.trans hQC)
  have hKIC : ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 →
      x ∈ t.Gv 0 ⊓ centralizer (t.Zv 0 : Set G) := fun x hx hxx => hXC (hKI x hx hxx)
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hfr.hF.1
  obtain ⟨g, hgL1, hgB⟩ := SetLike.exists_of_lt (CFSG.Quasithin.F1.lt_borelOf hR)
  have hgN : g ∉ normalizer ((S ⊓ L1 : Subgroup G) : Set G) := fun h => hgB ⟨hgL1, h⟩
  have hL1N : g ∈ normalizer (L1 : Set G) := Subgroup.le_normalizer hgL1
  have hT'syl : IsSylowTwoOf ((S ⊓ L1).map (MulAut.conj g).toMonoidHom) L1 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj g) hTsyl
    rwa [r4c_map_conj_eq_of_mem hL1N] at h
  have hne : (S ⊓ L1) ≠ (S ⊓ L1).map (MulAut.conj g).toMonoidHom := fun h =>
    hgN (r4f_mem_normalizer_of_map_eq h.symm)
  have hgC := hPC (hL1P hgL1)
  have hgQ : g⁻¹ ∈ normalizer (pCoreOf 2 L1 : Set G) := inv_mem (le_normalizer_pCoreOf 2 L1 hgL1)
  have hKIC' : ∀ x ∈ (S ⊓ L1).map (MulAut.conj g).toMonoidHom, x * x ∈ pCoreOf 2 L1 →
      x ∈ t.Gv 0 ⊓ centralizer (t.Zv 0 : Set G) := by
    intro x hx hxx
    rw [mem_map_conj_iff] at hx
    have hxx' : (g⁻¹ * x * g) * (g⁻¹ * x * g) ∈ pCoreOf 2 L1 := by
      have := (mem_normalizer_iff.mp hgQ (x * x)).mp hxx
      rwa [inv_inv, show g⁻¹ * (x * x) * g = (g⁻¹ * x * g) * (g⁻¹ * x * g) by group] at this
    have h0 := hKIC _ hx hxx'
    have := (mem_normalizer_iff.mp hgC _).mp h0
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  have hL := le_sup_pCoreOf_of_sylow_ne_of_sz hfr.ha hfr.hSz hTsyl hT'syl hne
    (fun x hx hxx => mem_sup_left (hKIC x hx hxx))
    (fun x hx hxx => mem_sup_left (hKIC' x hx hxx))
  exact (hL.trans (sup_le le_rfl (hQ1le.trans hQC))).trans inf_le_right

private theorem r4f_C0_eq_bot {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hL1 : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpB : pCoreOf 2 (bigB L1 L2 S) = S := by
    have := t.pCoreOf_Gw_zero_one hfr
    rwa [t.Gw_zero_one hfr.hF] at this
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hSC : S ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) := by
    refine hS2.le.trans (sup_le ?_ ?_)
    · intro s hs
      rw [mem_centralizer_iff]
      intro c hc
      exact ((mem_centralizer_iff.mp (mem_inf.mp hc).2) s (mem_inf.mp hs).2).symm
    · intro q hq
      rw [mem_centralizer_iff]
      intro c hc
      have hq' : q ∈ t.Qv 1 := by
        rw [t.Qv_one]
        exact hq
      exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 (mem_inf.mp hc).1) q hq').symm
  have hC₀S : t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mp hSC
  have hC₀Z : t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ t.Zv 0 := by
    have h := z2_inf_centralizer_le_z1 hfr.hF.1
    rw [hpB] at h
    refine (le_inf ?_ hC₀S).trans (h.trans t.Zv_zero.symm.le)
    exact inf_le_left.trans t.Zv_one.le
  have hC₀B : t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ bigB L1 L2 S :=
    inf_le_left.trans ((t.Zv_le_Qv 1).trans (t.Qv_one.le.trans
      ((Q2_le_S hfr.hF).trans le_sup_right)))
  refine eq_bot_of_le_bigB hfr.hF.1 hC₀B ?_ ?_
  · refine le_sup_of_le_left (le_inf le_sup_left ?_)
    intro l hl
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro c hc
    exact mem_centralizer_iff.mp (hL1 hl) c (hC₀Z hc)
  · refine le_sup_of_le_left (le_inf le_sup_left ?_)
    intro l hl
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro c hc
    exact ((mem_centralizer_iff.mp (mem_inf.mp hc).2) l hl).symm

private theorem r4f_step2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₁ : ℕ} {H : Subgroup G}
    (hHZ : H ≤ t.Zv (-(b₁ : ℤ))) (hHC : H ≤ centralizer (t.Zv 0 : Set G))
    (hZh : t.Zv (-(b₁ : ℤ)) ≤ t.Gv (-1)) (hH0 : H ≤ t.Gv 0)
    (hHK : t.K ≤ normalizer (H : Set G)) (hHQ : ¬ H ≤ t.Qv 0) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx₁0 : t.x₁ ∈ t.Gv 0 := by
    rw [t.Gv_zero]
    exact t.track.x₁_mem
  have hHw : H ≤ t.Gw (-1) 0 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -1 ∨ i = 0 by omega) with rfl | rfl
    · exact hZh (hHZ hy)
    · exact hH0 hy
  have hHp : IsPGroup 2 H := (t.isPGroup_Zv _).to_le hHZ
  have hYp : IsPGroup 2 (H.map (MulAut.conj t.x₁).toMonoidHom) := hHp.map _
  have hYw : H.map (MulAut.conj t.x₁).toMonoidHom ≤ t.Gw 0 1 := by
    have hmapw := t.track.map_win_x₁ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer (-1) 0
    rw [neg_zero, neg_neg] at hmapw
    exact (Subgroup.map_mono hHw).trans hmapw.le
  have hYS : H.map (MulAut.conj t.x₁).toMonoidHom ≤ S := by
    have h := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) hYp hYw
    rwa [t.pCoreOf_Gw_zero_one hfr] at h
  have hYC : H.map (MulAut.conj t.x₁).toMonoidHom ≤ centralizer (t.Zv 0 : Set G) := by
    intro y hy
    rw [mem_map_conj_iff] at hy
    rw [mem_centralizer_iff]
    intro z hz
    have hz' : t.x₁⁻¹ * z * t.x₁ ∈ t.Zv 0 := by
      have := (mem_normalizer_iff.mp (inv_mem (t.Gv_le_normalizer_Zv 0 hx₁0)) z).mp hz
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.mp (hHC hy) _ hz'
    calc z * y = t.x₁ * ((t.x₁⁻¹ * z * t.x₁) * (t.x₁⁻¹ * y * t.x₁)) * t.x₁⁻¹ := by group
      _ = t.x₁ * ((t.x₁⁻¹ * y * t.x₁) * (t.x₁⁻¹ * z * t.x₁)) * t.x₁⁻¹ := by rw [hc]
      _ = y * z := by group
  have hYQ : ¬ H.map (MulAut.conj t.x₁).toMonoidHom ≤ t.Qv 0 := by
    intro hle
    apply hHQ
    intro h hh
    have hy : t.x₁ * h * t.x₁⁻¹ ∈ H.map (MulAut.conj t.x₁).toMonoidHom := by
      rw [mem_map_conj_iff, show t.x₁⁻¹ * (t.x₁ * h * t.x₁⁻¹) * t.x₁ = h by group]
      exact hh
    have hN := t.Gv_le_normalizer_Qv 0 hx₁0
    have := (mem_normalizer_iff.mp (inv_mem hN) _).mp (hle hy)
    rwa [inv_inv, show t.x₁⁻¹ * (t.x₁ * h * t.x₁⁻¹) * t.x₁ = h by group] at this
  have hYD : t.D1 ≤ normalizer ((H.map (MulAut.conj t.x₁).toMonoidHom : Subgroup G) : Set G) :=
    (le_sup_left : t.D1 ≤ t.K).trans (t.r4f_K_le_normalizer_map hHK)
  exact t.r4f_C0_eq_bot hfr (t.r4f_L1_le_centralizer hfr hYS hYC hYQ hYD)

private theorem Zv_inf_centralizer_le_Qv_zero_or_of_cert43
    {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hO4 : t.GT = t.K) {b₁ : ℕ} (hb₁ : Odd b₁)
    (hZ1 : t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) b₁) (hZh : t.Zv (-(b₁ : ℤ)) ≤ t.Gv (-1)) :
    t.Zv (-(b₁ : ℤ)) ⊓ centralizer (t.Zv 0 : Set G) ≤ t.Qv 0 ∨
      t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
  by_cases hQ : t.Zv (-(b₁ : ℤ)) ⊓ centralizer (t.Zv 0 : Set G) ≤ t.Qv 0
  · exact Or.inl hQ
  · refine Or.inr (t.r4f_step2 hfr (H := t.Zv (-(b₁ : ℤ)) ⊓ centralizer (t.Zv 0 : Set G))
      inf_le_left inf_le_right hZh (t.r4f_le_Gv_zero hfr hO4 hb₁ hZ1 hZh) ?_ hQ)
    intro k hk
    exact r4f_mem_normalizer_inf (t.Gv_le_normalizer_Zv _ (t.K_le_Gv _ hk))
      (r4b_mem_normalizer_centralizer (t.Gv_le_normalizer_Zv 0 (t.K_le_Gv 0 hk)))

theorem Zv_inf_centralizer_le_Qv_zero_or {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hO4 : t.GT = t.K) {b₁ : ℕ} (hb₁ : Odd b₁)
    (hZ1 : t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) b₁) (hZh : t.Zv (-(b₁ : ℤ)) ≤ t.Gv (-1)) :
    t.Zv (-(b₁ : ℤ)) ⊓ centralizer (t.Zv 0 : Set G) ≤ t.Qv 0 ∨
      t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
  exact t.Zv_inf_centralizer_le_Qv_zero_or_of_cert43 hfr hO4 hb₁ hZ1 hZh

private theorem r4g_K_le_P2 : t.K ≤ P2 L1 L2 S := by
  rw [← t.Gv_one]
  exact t.K_le_Gv 1

private theorem r4g_P2_le_normalizer_C0 (hF : Hyp111 L1 L2 S) :
    P2 L1 L2 S ≤ normalizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) := by
  intro x hx
  refine A4.mem_normalizer_inf ?_ (r4b_mem_normalizer_centralizer (r4a_P2_le_normalizer_L2 hF hx))
  exact t.Gv_le_normalizer_Zv 1 (by rw [t.Gv_one]; exact hx)

private theorem r4g_S_le_centralizer_C0 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    S ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  refine hS2.le.trans (sup_le ?_ ?_)
  · intro s hs
    rw [mem_centralizer_iff]
    intro c hc
    exact ((mem_centralizer_iff.mp (mem_inf.mp hc).2) s (mem_inf.mp hs).2).symm
  · intro q hq
    rw [mem_centralizer_iff]
    intro c hc
    have hq' : q ∈ t.Qv 1 := by
      rw [t.Qv_one]
      exact hq
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 (mem_inf.mp hc).1) q hq').symm

private theorem r4g_C0_le_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ t.Zv 0 := by
  have hpB : pCoreOf 2 (bigB L1 L2 S) = S := by
    have := t.pCoreOf_Gw_zero_one hfr
    rwa [t.Gw_zero_one hfr.hF] at this
  have hC₀S : t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.r4g_S_le_centralizer_C0 hfr)
  have h := z2_inf_centralizer_le_z1 hfr.hF.1
  rw [hpB] at h
  refine (le_inf ?_ hC₀S).trans (h.trans t.Zv_zero.symm.le)
  exact inf_le_left.trans t.Zv_one.le

private theorem r4g_exists_fixed_coset {S N C : Subgroup G} (hS : IsPGroup 2 S)
    (hNS : N ≤ S) (hN : S ≤ normalizer (N : Set G)) (hCN : C ≤ N)
    (hC : S ≤ centralizer (C : Set G)) (hlt : C < N) :
    ∃ z ∈ N, z ∉ C ∧ ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCS : C ≤ S := hCN.trans hNS
  haveI hNn : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNS).mpr hN
  haveI hCn : (C.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).mpr
      (hC.trans (Subgroup.centralizer_le_normalizer _))
  haveI : Group.IsNilpotent (↥S ⧸ C.subgroupOf S) :=
    (hS.to_quotient (C.subgroupOf S)).isNilpotent
  set M : Subgroup (↥S ⧸ C.subgroupOf S) :=
    (N.subgroupOf S).map (QuotientGroup.mk' (C.subgroupOf S)) with hM
  haveI : M.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hMne : M ≠ ⊥ := by
    intro hbot
    rw [hM, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    apply hlt.not_ge
    intro n hn
    exact hbot (show (⟨n, hNS hn⟩ : ↥S) ∈ N.subgroupOf S from hn)
  obtain ⟨⟨q, hq⟩, hq1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hMne)
  obtain ⟨hqM, hqc⟩ := Subgroup.mem_inf.mp hq
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hqM
  refine ⟨(n : G), hn, fun hnC => hq1' ?_, fun s hs => ?_⟩
  · exact (QuotientGroup.eq_one_iff n).mpr hnC
  · have hcomm := Subgroup.mem_center_iff.mp hqc (QuotientGroup.mk' (C.subgroupOf S) ⟨s, hs⟩)
    have h1 : QuotientGroup.mk' (C.subgroupOf S) (⟨s, hs⟩ * n * ⟨s, hs⟩⁻¹ * n⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact h2

private theorem r4g_map_conj_inv (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [← r4e_conj_mul, inv_mul_cancel]
  ext x
  rw [mem_map_conj_iff]
  simp

private theorem r4g_exists_B {Z C S : Subgroup G} (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hCZ : C ≤ Z) :
    ∃ B : Subgroup G, ∀ z, z ∈ B ↔ (z ∈ Z ∧ ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ C) := by
  refine ⟨{ carrier := {z | z ∈ Z ∧ ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ C}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun z => Iff.rfl⟩
  · rintro z z' ⟨hz, hzs⟩ ⟨hz', hzs'⟩
    refine ⟨mul_mem hz hz', fun s hs => ?_⟩
    have key : s * (z * z') * s⁻¹ * (z * z')⁻¹ =
        (s * z * s⁻¹ * z⁻¹) * (z * (s * z' * s⁻¹ * z'⁻¹) * z⁻¹) := by group
    have hc' := hzs' s hs
    have hcomm : z * (s * z' * s⁻¹ * z'⁻¹) * z⁻¹ = s * z' * s⁻¹ * z'⁻¹ := by
      rw [hZab z hz _ (hCZ hc')]
      group
    rw [key, hcomm]
    exact mul_mem (hzs s hs) hc'
  · refine ⟨one_mem Z, fun s hs => ?_⟩
    simpa using one_mem C
  · rintro z ⟨hz, hzs⟩
    refine ⟨inv_mem hz, fun s hs => ?_⟩
    have hc := hzs s hs
    have key : s * z⁻¹ * s⁻¹ * (z⁻¹)⁻¹ = z⁻¹ * (s * z * s⁻¹ * z⁻¹)⁻¹ * z := by group
    have hcomm : z⁻¹ * (s * z * s⁻¹ * z⁻¹)⁻¹ * z = (s * z * s⁻¹ * z⁻¹)⁻¹ := by
      rw [mul_assoc, ← hZab z hz _ (hCZ (inv_mem hc))]
      group
    rw [key, hcomm]
    exact inv_mem hc

theorem Zv_one_inf_centralizer_L2_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hO4 : t.GT = t.K) {m b₀ : ℕ}
    (hb₀ : Even b₀) (hm1 : m ≤ b₀ + 2)
    (hmax : ∀ u w : ℤ, ((2 * m : ℕ) : ℤ) < w - u → pCoreOf 2 (t.Gw u w) = ⊥)
    (hQ : Nat.card (pCoreOf 2 (t.Gw (1 - 2 * m) 1)) = 2 ^ f)
    (hKQ : ∀ X : Subgroup G, X ≤ pCoreOf 2 (t.Gw (1 - 2 * m) 1) → X ≠ ⊥ →
      t.K ≤ normalizer (X : Set G) → X = pCoreOf 2 (t.Gw (1 - 2 * m) 1))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀))
    (hZ1 : t.Zv 0 ≤ t.Gw (-((b₀ + 1 : ℕ) : ℤ)) (b₀ + 1)) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set C₀ : Subgroup G := t.Zv 1 ⊓ centralizer (L2 : Set G) with hC₀
  obtain ⟨c, hc⟩ : ∃ c, b₀ = c + c := hb₀
  have hb₁ : Odd (b₀ + 1) := ⟨c, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = -((c : ℤ) + 1) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : G, g = (t.x₂ * t.x₁) ^ k := ⟨_, rfl⟩
  have hgK : g ∈ normalizer (t.K : Set G) := by
    rw [hg]
    exact zpow_mem t.track.tau_mem_normalizer k
  have hmZ : ∀ i : ℤ, (t.Zv i).map (MulAut.conj g).toMonoidHom = t.Zv (i + 2 * k) := by
    intro i
    rw [hg]
    exact map_qv_tau_pow i k
  have hmG : ∀ i : ℤ, (t.Gv i).map (MulAut.conj g).toMonoidHom = t.Gv (i + 2 * k) := by
    intro i
    rw [hg]
    exact map_qv_tau_pow i k
  have hmW : ∀ a b : ℤ, (t.Gw a b).map (MulAut.conj g).toMonoidHom =
      t.Gw (a + 2 * k) (b + 2 * k) := by
    intro a b
    rw [hg]
    exact map_win_tau_pow a b k
  have hmW' : ∀ a b : ℤ, (t.Gw a b).map (MulAut.conj g⁻¹).toMonoidHom =
      t.Gw (a + 2 * -k) (b + 2 * -k) := by
    intro a b
    rw [hg, ← zpow_neg]
    exact map_win_tau_pow a b (-k)
  have hk1 : (1 : ℤ) + 2 * k = -((b₀ + 1 : ℕ) : ℤ) := by push_cast; omega
  have hP2C := t.r4g_P2_le_normalizer_C0 hfr.hF.1
  have hKC₀ : t.K ≤ normalizer (C₀ : Set G) := t.r4g_K_le_P2.trans hP2C
  have hC₀Z1 : C₀ ≤ t.Zv 1 := inf_le_left
  have hC₀Z0 : C₀ ≤ t.Zv 0 := t.r4g_C0_le_Zv_zero hfr
  have hSC₀ : S ≤ centralizer (C₀ : Set G) := t.r4g_S_le_centralizer_C0 hfr
  have hC₀p : IsPGroup 2 C₀ := (t.isPGroup_Zv 1).to_le hC₀Z1
  have hLQ : L2 ⊔ Q2 L1 L2 S ≤ centralizer (C₀ : Set G) := by
    refine sup_le ?_ ?_
    · intro l hl
      rw [mem_centralizer_iff]
      intro c hc
      exact ((mem_centralizer_iff.mp (mem_inf.mp hc).2) l hl).symm
    · intro q hq
      rw [mem_centralizer_iff]
      intro c hc
      have hq' : q ∈ t.Qv 1 := by
        rw [t.Qv_one]
        exact hq
      exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 (mem_inf.mp hc).1) q hq').symm
  have hZw : t.Zv (1 + 2 * k) ≤ t.Gw (1 - b₀ + 2 * k) (1 + b₀ + 2 * k) := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hZ0
    rwa [hmZ, hmW] at h
  have hZh : t.Zv (-((b₀ + 1 : ℕ) : ℤ)) ≤ t.Gv (-1) := by
    rw [← hk1]
    exact hZw.trans (win_le_qv (by omega) (by omega))
  have hZ1' : t.Zv 0 ≤ t.Gw (-((b₀ + 1 : ℕ) : ℤ)) ((b₀ + 1 : ℕ) : ℤ) := by
    have e : ((b₀ + 1 : ℕ) : ℤ) = (b₀ : ℤ) + 1 := by push_cast; ring
    rw [e]
    rw [e] at hZ1
    exact hZ1
  obtain hH | hbot := t.Zv_inf_centralizer_le_Qv_zero_or hfr hO4 hb₁ hZ1' hZh
  swap
  · exact hne hbot
  obtain ⟨Ch, hCh⟩ : ∃ Ch : Subgroup G, Ch = C₀.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hChZ : Ch ≤ t.Zv (1 + 2 * k) := by
    rw [hCh, ← hmZ 1]
    exact Subgroup.map_mono hC₀Z1
  have hChne : Ch ≠ ⊥ := by
    rw [hCh]
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h)
  have hChK : t.K ≤ normalizer (Ch : Set G) := by
    rw [hCh]
    exact t.r4e_K_le_normalizer_map hgK hKC₀
  have hChp : IsPGroup 2 Ch := (t.isPGroup_Zv _).to_le hChZ
  have hZ1G : t.Zv 0 ≤ t.Gv (1 + 2 * k) := by
    rw [hk1]
    exact hZ1'.trans (win_le_qv le_rfl (by omega))
  have hChC : Ch ≤ centralizer (t.Zv 0 : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro z hz
    rw [hCh] at hx
    have hx' : g⁻¹ * x * g ∈ C₀ := mem_map_conj_iff.mp hx
    have hzG : g⁻¹ * z * g ∈ t.Gv 1 := by
      have h1 : z ∈ t.Gv (1 + 2 * k) := hZ1G hz
      rw [← hmG 1] at h1
      exact mem_map_conj_iff.mp h1
    obtain ⟨j, hj⟩ := t.isPGroup_Zv 0 ⟨z, hz⟩
    have hzj : z ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hzj' : (g⁻¹ * z * g) ^ 2 ^ j = 1 := by
      have h := conj_pow (a := g⁻¹) (b := z) (i := 2 ^ j)
      rw [inv_inv] at h
      rw [h, hzj]
      group
    have hmem : g⁻¹ * z * g ∈ L2 ⊔ Q2 L1 L2 S :=
      t.r4a_mem_of_pow_eq_one hfr (by rwa [t.Gv_one] at hzG) hzj'
    have h := mem_centralizer_iff.mp (hLQ hmem) (g⁻¹ * x * g) hx'
    calc z * x = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [h]
      _ = x * z := by group
  have hChQ0 : Ch ≤ t.Qv 0 :=
    (le_inf (by rw [← hk1]; exact hChZ) hChC : Ch ≤ _).trans hH
  have hQ0Gv0 : t.Qv 0 ≤ t.Gv 0 := t.Qv_le_Gv_self 0
  have hQ0Gv1 : t.Qv 0 ≤ t.Gv 1 := by
    have h := (t.Qv_le_Gv hfr 0).2
    rwa [zero_add] at h
  have hChw1 : Ch ≤ t.Gw (1 - b₀ + 2 * k) 1 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ -1 ∨ i = 0 ∨ i = 1 by omega) with h3 | rfl | rfl
    · exact mem_win_iff.mp (hZw (hChZ hy)) i h1 (by omega)
    · exact hQ0Gv0 (hChQ0 hy)
    · exact hQ0Gv1 (hChQ0 hy)
  obtain ⟨y, hy⟩ : ∃ y : G, y = g * t.x₂ * g⁻¹ := ⟨_, rfl⟩
  have hyN : y ∈ normalizer (Ch : Set G) := by
    have hx₂C : t.x₂ ∈ normalizer (C₀ : Set G) := hP2C t.track.x₂_mem
    rw [mem_normalizer_iff]
    intro z
    rw [hCh, mem_map_conj_iff, mem_map_conj_iff, hy]
    have key : g⁻¹ * (g * t.x₂ * g⁻¹ * z * (g * t.x₂ * g⁻¹)⁻¹) * g =
        t.x₂ * (g⁻¹ * z * g) * t.x₂⁻¹ := by group
    rw [key]
    exact mem_normalizer_iff.mp hx₂C _
  have hyW : ∀ a b : ℤ, (t.Gw a b).map (MulAut.conj y).toMonoidHom =
      t.Gw (2 + 4 * k - b) (2 + 4 * k - a) := by
    intro a b
    rw [hy, r4e_conj_mul (g * t.x₂) g⁻¹, r4e_conj_mul g t.x₂, hmW' a b,
      t.track.map_win_x₂ Subgroup.le_normalizer Subgroup.le_normalizer, hmW]
    congr 1 <;> ring
  have hChw2 : Ch ≤ t.Gw (2 + 4 * k - 1) (2 + 4 * k - (1 - b₀ + 2 * k)) := by
    have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hChw1
    rwa [hyW, r4c_map_conj_eq_of_mem hyN] at h
  have hChW : Ch ≤ t.Gw (1 + 4 * k) 1 := by
    intro x hx
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    by_cases hi : i ≤ -1
    · exact mem_win_iff.mp (hChw2 hx) i (by omega) (by omega)
    · exact mem_win_iff.mp (hChw1 hx) i (by omega) h2
  obtain rfl : m = b₀ + 2 := by
    by_contra hmne
    have hlt : m < b₀ + 2 := lt_of_le_of_ne hm1 hmne
    have hbot : pCoreOf 2 (t.Gw (1 + 4 * k) 1) = ⊥ := hmax _ _ (by push_cast; omega)
    have h := t.le_pCoreOf_Gw hfr (u := 1 + 4 * k) (w := 1) (by omega) hChp hChW
    rw [hbot] at h
    exact hChne (le_bot_iff.mp h)
  have hwin : (1 : ℤ) - 2 * ((b₀ + 2 : ℕ) : ℤ) = 1 + 4 * k := by push_cast; omega
  rw [hwin] at hQ hKQ
  have hChle : Ch ≤ pCoreOf 2 (t.Gw (1 + 4 * k) 1) :=
    t.le_pCoreOf_Gw hfr (by omega) hChp hChW
  have hChQ : Ch = pCoreOf 2 (t.Gw (1 + 4 * k) 1) := hKQ Ch hChle hChne hChK
  have hcard : Nat.card C₀ = 2 ^ f := by
    have h1 : Nat.card Ch = Nat.card C₀ := by
      rw [hCh]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [← h1, hChQ]
    exact hQ
  have hC₀w : C₀ ≤ t.Gw (1 - ((b₀ + 2 : ℕ) : ℤ)) (1 + ((b₀ + 2 : ℕ) : ℤ)) := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hChW
    rw [hCh, r4g_map_conj_inv, hmW'] at h
    refine h.trans (le_of_eq ?_)
    congr 1 <;> push_cast <;> omega
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : Subgroup G, C₂ = C₀.map (MulAut.conj t.x₁).toMonoidHom := ⟨_, rfl⟩
  have hC₂w : C₂ ≤ t.Gw (-(1 + ((b₀ + 2 : ℕ) : ℤ))) (-(1 - ((b₀ + 2 : ℕ) : ℤ))) := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hC₀w
    rwa [← hC₂, t.track.map_win_x₁ Subgroup.le_normalizer Subgroup.le_normalizer] at h
  have hx₁0 : t.x₁ ∈ t.Gv 0 := by
    rw [t.Gv_zero]
    exact t.track.x₁_mem
  have hC₂Z : C₂ ≤ t.Zv 0 := by
    intro x hx
    rw [hC₂] at hx
    have hx' : t.x₁⁻¹ * x * t.x₁ ∈ C₀ := mem_map_conj_iff.mp hx
    have h1 : t.x₁⁻¹ * x * t.x₁ ∈ t.Zv 0 := hC₀Z0 hx'
    have := (mem_normalizer_iff.mp (t.Gv_le_normalizer_Zv 0 hx₁0) _).mp h1
    rwa [show t.x₁ * (t.x₁⁻¹ * x * t.x₁) * t.x₁⁻¹ = x by group] at this
  have hC₂card : Nat.card C₂ = 2 ^ f := by
    rw [hC₂, Subgroup.card_map_of_injective (MulAut.conj t.x₁).injective]
    exact hcard
  have hinf : C₀ ⊓ C₂ = ⊥ := by
    have hw : C₀ ⊓ C₂ ≤ t.Gw (-1 - ((b₀ + 2 : ℕ) : ℤ)) (1 + ((b₀ + 2 : ℕ) : ℤ)) := by
      intro x hx
      refine mem_win_iff.mpr fun i h1 h2 => ?_
      by_cases hi : 1 - ((b₀ + 2 : ℕ) : ℤ) ≤ i
      · exact mem_win_iff.mp (hC₀w (mem_inf.mp hx).1) i hi h2
      · refine mem_win_iff.mp (hC₂w (mem_inf.mp hx).2) i ?_ ?_
        · push_cast at h1 ⊢
          omega
        · push_cast at hi ⊢
          omega
    have hbot : pCoreOf 2 (t.Gw (-1 - ((b₀ + 2 : ℕ) : ℤ)) (1 + ((b₀ + 2 : ℕ) : ℤ))) = ⊥ :=
      hmax _ _ (by push_cast; omega)
    have h := t.le_pCoreOf_Gw hfr (by push_cast; omega) (hC₀p.to_le inf_le_left) hw
    rw [hbot] at h
    exact le_bot_iff.mp h
  have hZ1m : t.Zv 0 ≤ t.Gw (1 - ((b₀ + 2 : ℕ) : ℤ)) (((b₀ + 2 : ℕ) : ℤ) - 1) := by
    refine hZ1'.trans (le_of_eq ?_)
    congr 1 <;> push_cast <;> ring
  have hmEven : Even (b₀ + 2) := ⟨c + 1, by omega⟩
  have hcardZ : Nat.card (t.Zv 0) = 2 ^ f * 2 ^ f := by
    have hle := t.card_Zv_zero_le_of_B hfr hmEven hZ1m hwlog
    have hab : C₀ ≤ normalizer (C₂ : Set G) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [mem_centralizer_iff]
      intro z hz
      exact mem_centralizer_iff.mp (t.Zv_le_centralizer 0 (hC₀Z0 hx)) z (t.Zv_le_Qv 0 (hC₂Z hz))
    have h := C5.card_sup_mul_card_inf_of_le_normalizer hab
    rw [hinf, Subgroup.card_bot, mul_one, hC₂card, hcard] at h
    have hsup : Nat.card ↥(C₀ ⊔ C₂) ≤ Nat.card (t.Zv 0) :=
      Subgroup.card_le_of_le (sup_le hC₀Z0 hC₂Z)
    rw [h] at hsup
    exact le_antisymm hle hsup
  have hZcent : t.Zv 0 ≤ centralizer (t.Zv 0 : Set G) :=
    fun x hx => Subgroup.centralizer_le (fun w hw => t.Zv_le_Qv 0 hw) (t.Zv_le_centralizer 0 hx)
  obtain ⟨Bsub, hBsub⟩ := r4g_exists_B (Z := t.Zv 0) (C := C₀) (S := S)
    (fun x hx y hy => (mem_centralizer_iff.mp (hZcent hx) y hy).symm) hC₀Z0
  have hBK1 : ∀ κ ∈ t.K, ∀ z ∈ Bsub, κ * z * κ⁻¹ ∈ Bsub := by
    intro κ hκ z hz
    obtain ⟨hzZ, hzB⟩ := (hBsub z).mp hz
    refine (hBsub _).mpr ⟨?_, fun s hs => ?_⟩
    · exact (mem_normalizer_iff.mp (t.Gv_le_normalizer_Zv 0 (t.K_le_Gv 0 hκ)) z).mp hzZ
    · have hκN : κ ∈ normalizer (S : Set G) := hfr.hN (t.hHall.1 hκ)
      have hs' : κ⁻¹ * s * κ ∈ S := by
        have := (mem_normalizer_iff.mp (inv_mem hκN) s).mp hs
        rwa [inv_inv] at this
      have h2 := (mem_normalizer_iff.mp (hKC₀ hκ) _).mp (hzB _ hs')
      have key : s * (κ * z * κ⁻¹) * s⁻¹ * (κ * z * κ⁻¹)⁻¹ =
          κ * ((κ⁻¹ * s * κ) * z * (κ⁻¹ * s * κ)⁻¹ * z⁻¹) * κ⁻¹ := by group
      rw [key]
      exact h2
  have hBK : t.K ≤ normalizer (Bsub : Set G) := fun κ hκ =>
    mem_normalizer_iff.mpr fun z => ⟨fun hz => hBK1 κ hκ z hz, fun hz => by
      have := hBK1 κ⁻¹ (inv_mem hκ) _ hz
      rwa [show κ⁻¹ * (κ * z * κ⁻¹) * κ⁻¹⁻¹ = z by group] at this⟩
  have hCB : C₀ ≤ Bsub := by
    intro z hz
    refine (hBsub z).mpr ⟨hC₀Z0 hz, fun s hs => ?_⟩
    have h := mem_centralizer_iff.mp (hSC₀ hs) z hz
    have h1 : s * z * s⁻¹ * z⁻¹ = 1 := by
      rw [← h]
      group
    rw [h1]
    exact one_mem _
  have hBZ : Bsub ≤ t.Zv 0 := fun z hz => ((hBsub z).mp hz).1
  have hZS : t.Zv 0 ≤ S := (t.Zv_le_Qv 0).trans (t.Qv_zero.le.trans (Q1_le_S hfr.hF))
  have hSP : S ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSZ : S ≤ normalizer (t.Zv 0 : Set G) := hSP.trans (t.Gv_le_normalizer_Zv 0)
  have hlt : C₀ < t.Zv 0 := by
    refine lt_of_le_of_ne hC₀Z0 fun h => ?_
    have h1 := hcardZ
    rw [← h, hcard] at h1
    have hr4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
    have h2 := Nat.mul_le_mul_right (2 ^ f) hr4
    omega
  obtain ⟨z₀, hz₀N, hz₀C, hz₀S⟩ :=
    r4g_exists_fixed_coset hfr.hF.1.h1.pgroup hZS hSZ hC₀Z0 hSC₀ hlt
  have hz₀B : z₀ ∈ Bsub := (hBsub z₀).mpr ⟨hz₀N, hz₀S⟩
  rcases t.eq_or_eq_of_B hfr hmEven hZ1m hwlog hcardZ (A := C₀) (B := Bsub) hcard hKC₀ hCB hBZ
    hBK with h | h
  · exact hz₀C (by rw [← h]; exact hz₀B)
  have hquad : ∀ s ∈ S, ∀ z ∈ t.Zv 0, s * z * s⁻¹ * z⁻¹ ∈ C₀ := fun s hs z hz =>
    ((hBsub z).mp (by rw [h]; exact hz)).2 s hs
  have hL1 : L1 ≤ centralizer (t.Zv 0 : Set G) := by
    have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup G) (t.Zv 0) := by
      show (⊥ : Subgroup G) ≤ t.Zv 0 ∧ ⁅t.Zv 0, t.Zv 0⁆ ≤ (⊥ : Subgroup G) ∧
        ∀ e ∈ t.Zv 0, e ^ 2 ∈ (⊥ : Subgroup G)
      refine ⟨bot_le, (commutator_eq_bot_iff_le_centralizer.mpr hZcent).le, fun e he => ?_⟩
      rw [Subgroup.mem_bot]
      exact A4.sq_eq_one_of_mem_omegaOneCenterOf (by rw [← t.Zv_eq 0]; exact he)
    have hL1P : L1 ≤ t.Gv 0 := by
      rw [t.Gv_zero]
      exact le_sup_left
    have hL : L1 ≤ normalizer (t.Zv 0 : Set G) ⊓ normalizer ((⊥ : Subgroup G) : Set G) :=
      le_inf (hL1P.trans (t.Gv_le_normalizer_Zv 0))
        (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
    have hQ1le : pCoreOf 2 L1 ≤ t.Qv 0 := by
      rw [t.Qv_zero]
      exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1
    have hQ' : ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.Zv 0, ⁅p, v⁆ ∈ (⊥ : Subgroup G) := by
      intro p hp v hv
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hv) p (hQ1le hp)
    have hquad' : ∀ s ∈ S ⊓ L1, ∀ v ∈ t.Zv 0, ⁅s, ⁅s, v⁆⁆ ∈ (⊥ : Subgroup G) := by
      intro s hs v hv
      have hc := hquad s (mem_inf.mp hs).1 v hv
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.mp (hSC₀ (mem_inf.mp hs).1) _ hc).symm
    have key := commutator_mem_of_quadratic_of_sz (L := L1) (T := S ⊓ L1) (V := t.Zv 0)
      (Z := ⊥) hfr.ha hfr.hSz hfr.hF.1.h1.sylow hsec hL hQ' hquad'
    intro l hl
    rw [mem_centralizer_iff]
    intro z hz
    have h1 := key l hl z hz
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  exact hne (t.r4f_C0_eq_bot hfr hL1)

private theorem r4h_inf_le_Gw {b₀ : ℕ} (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀))
    (hZb : t.Zv (1 - b₀) ≤ t.Gw (1 - 2 * b₀) 1) :
    t.Zv 1 ⊓ t.Zv (1 - b₀) ≤ t.Gw (1 - 2 * b₀) (1 + b₀) := by
  intro y hy
  rw [mem_inf] at hy
  rw [mem_win_iff]
  intro i hi1 hi2
  by_cases h : i ≤ 1
  · exact mem_win_iff.mp (hZb hy.2) i hi1 h
  · exact mem_win_iff.mp (hZ0 hy.1) i (by omega) hi2

theorem three_mul_le_of_commutator_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {n b₀ : ℕ} (hb₀ : Even b₀)
    (hmax : ∀ u w : ℤ, (n : ℤ) < w - u → pCoreOf 2 (t.Gw u w) = ⊥)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hX : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≠ ⊥) :
    3 * b₀ ≤ n := by
  by_contra hlt
  have hlt : n < 3 * b₀ := not_le.mp hlt
  have hXle : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≤ t.Zv 1 ⊓ t.Zv (1 - b₀) :=
    t.commutator_Zv_one_le_inf hb₀ hZ0
  have hXw : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≤ t.Gw (1 - 2 * b₀) (1 + b₀) :=
    hXle.trans (t.r4h_inf_le_Gw hZ0 (t.Zv_one_sub_le_Gw hb₀ hZ0))
  have hXp : IsPGroup 2 (⁅t.Zv 1, t.Zv (1 - b₀)⁆ : Subgroup G) :=
    (t.isPGroup_Zv 1).to_le (hXle.trans inf_le_left)
  have hcore := t.le_pCoreOf_Gw hfr (u := 1 - 2 * b₀) (w := 1 + b₀) (by omega) hXp hXw
  rw [hmax _ _ (by omega)] at hcore
  exact hX (le_bot_iff.mp hcore)

private theorem r4i_card_dichotomy {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (hr : 2 ^ f ≤ Nat.card (t.Zv 0)) :
    Nat.card (t.Zv 0) = 2 ^ f ∨ Nat.card (t.Zv 0) = 2 ^ f * 2 ^ f := by
  have hr0 : 0 < 2 ^ f := by positivity
  obtain ⟨c, hc⟩ := hm
  have hodd1 : Odd (1 - (m : ℤ)) := ⟨-(c : ℤ), by omega⟩
  have hodd2 : Odd ((m : ℤ) - 1) := ⟨(c : ℤ) - 1, by omega⟩
  have hm' : Even m := ⟨c, hc⟩
  obtain ⟨hc1, hc2⟩ := t.r4e_card_le hfr hm' hm2 hZ1 hwlog
  have hXbot := t.r4e_X_inf_Gv_eq_bot hfr hm' hm2 hZ1 hwlog
  have hXw := t.r4e_X_le_Gw hm2 hZ1
  have hZw := t.r4e_Zv_le_Gw hm2 hZ1
  have hZp : IsPGroup 2 (t.Zv 0) := t.isPGroup_Zv 0
  have hZK : t.K ≤ normalizer (t.Zv 0 : Set G) := fun h hh =>
    t.Gv_le_normalizer_Zv 0 (t.K_le_Gv 0 hh)
  set X : Subgroup G := t.Zv 0 ⊓ t.Gv (-m) with hX
  have hXZ : X ≤ t.Zv 0 := inf_le_left
  have hXG : X ≤ t.Gv (-m) := inf_le_right
  have hXp : IsPGroup 2 X := hZp.to_le hXZ
  have hXK : t.K ≤ normalizer (X : Set G) := fun h hh =>
    A4.mem_normalizer_inf (t.Gv_le_normalizer_Zv 0 (t.K_le_Gv 0 hh))
      (Subgroup.le_normalizer (t.K_le_Gv (-m) hh))
  rcases t.r4e_KI_right hfr hodd2 hXp hXK hXw with h | h
  ·
    left
    have h1 := (t.inf_Gv_eq_inf_Qv hfr (m - 1) hXp).1 hXw
    rw [show (m : ℤ) - 1 + 1 = m by ring, hXbot, inf_eq_left.mpr h] at h1
    rw [← h1, Subgroup.card_bot, mul_one] at hc1
    exact le_antisymm hc1 hr
  ·
    have hXr : Nat.card X = 2 ^ f := by
      have h2 := Subgroup.relIndex_mul_card (t.Qv (m - 1)) X
      rw [h] at h2
      have h3 : 2 ^ f ≤ Nat.card X := by
        rw [← h2]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      exact le_antisymm hc2 h3
    have hZX : t.Zv 0 ⊓ t.Qv (1 - m) = X := by
      have h1 := (t.inf_Gv_eq_inf_Qv hfr (1 - m) hZp).2 hZw
      rw [show (1 : ℤ) - m - 1 = -m by ring] at h1
      exact h1.symm
    rcases t.r4e_KI_left hfr hodd1 hZp hZK hZw with h | h
    · left
      have : t.Zv 0 = X := by
        rw [← hZX]
        exact (inf_eq_left.mpr h).symm
      rw [this, hXr]
    · right
      have h2 := Subgroup.relIndex_mul_card (t.Qv (1 - m)) (t.Zv 0)
      rw [h, inf_comm, hZX, hXr] at h2
      rw [← h2]

private theorem r4i_le_normalizer_of_forall {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ y ∈ H, k * y * k⁻¹ ∈ H) : K ≤ normalizer (H : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h k hk y hy, fun hy => ?_⟩
  have := h k⁻¹ (inv_mem hk) _ hy
  rwa [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at this

private theorem r4i_Qv_zero_le_S (hF : F112HypW L1 L2 S) :
    t.Qv 0 ≤ S := by
  rw [t.Qv_zero]
  exact Q1_le_S hF

private theorem r4i_Zv_zero_le_S (hF : F112HypW L1 L2 S) :
    t.Zv 0 ≤ S :=
  (t.Zv_le_Qv 0).trans (t.r4i_Qv_zero_le_S hF)

private theorem r4i_S_le_Gv_zero : S ≤ t.Gv 0 := by
  rw [t.Gv_zero]
  exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right

include t in
private theorem r4i_isPGroup_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsPGroup 2 S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pCoreOf_isPGroup 2 (t.Gw 0 1)
  rwa [t.pCoreOf_Gw_zero_one hfr] at this

private theorem r4i_A_le_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Zv 1 ⊓ centralizer (S : Set G) ≤ t.Zv 0 := by
  have hB : pCoreOf 2 (bigB L1 L2 S) = S := by
    rw [← t.Gw_zero_one hfr.hF]
    exact t.pCoreOf_Gw_zero_one hfr
  have h := z2_inf_centralizer_le_z1 hfr.hF.1
  rw [hB] at h
  rw [t.Zv_one, t.Zv_zero]
  exact h

private theorem r4i_K_le_normalizer_A {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer ((t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := fun k hk =>
  A4.mem_normalizer_inf (t.Gv_le_normalizer_Zv 1 (t.K_le_Gv 1 hk))
    (r4b_mem_normalizer_centralizer (hfr.hN (t.hHall.1 hk)))

private theorem r4i_exists_fixed_mod {P Y N : Subgroup G} (hP : IsPGroup 2 P)
    (hYP : Y ≤ P) (hNP : N ≤ P) (hPY : P ≤ normalizer (Y : Set G))
    (hPN : P ≤ normalizer (N : Set G)) (hY : ¬ Y ≤ N) :
    ∃ y ∈ Y, y ∉ N ∧ ∀ p ∈ P, ⁅p, y⁆ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup ↥P := N.subgroupOf P with hN'def
  have hN' : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hPN
  set Y' : Subgroup ↥P := Y.subgroupOf P with hY'def
  have hY' : Y'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).2 hPY
  have hQ : IsPGroup 2 (↥P ⧸ N') := hP.to_quotient N'
  have : Group.IsNilpotent (↥P ⧸ N') := hQ.isNilpotent
  set Y'' : Subgroup (↥P ⧸ N') := Y'.map (QuotientGroup.mk' N') with hY''def
  have hY'' : Y''.Normal := hY'.map _ (QuotientGroup.mk'_surjective N')
  have hne : Y'' ≠ ⊥ := by
    intro h0
    apply hY
    intro y hy
    have hyY' : (⟨y, hYP hy⟩ : ↥P) ∈ Y' := hy
    have h1 : QuotientGroup.mk' N' ⟨y, hYP hy⟩ ∈ Y'' := ⟨_, hyY', rfl⟩
    rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨⟨y, hyP⟩, hyY, hyz⟩ := (Subgroup.mem_inf.1 z.2).1
  have hzc := (Subgroup.mem_inf.1 z.2).2
  refine ⟨y, hyY, fun hyN => hz1 ?_, fun p hp => ?_⟩
  · apply Subtype.ext
    change (z : ↥P ⧸ N') = 1
    rw [← hyz]
    exact (QuotientGroup.eq_one_iff _).2 hyN
  · have hc := Subgroup.mem_center_iff.1 hzc (QuotientGroup.mk' N' ⟨p, hp⟩)
    rw [← hyz] at hc
    have h1 : QuotientGroup.mk' N' ⁅(⟨p, hp⟩ : ↥P), (⟨y, hyP⟩ : ↥P)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact h2

private theorem r4i_exists_B {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {A : Subgroup G} (hAZ : A ≤ t.Zv 0) (hAS : A ≤ centralizer (S : Set G))
    (hAK : t.K ≤ normalizer (A : Set G)) (hZA : ¬ t.Zv 0 ≤ A) :
    ∃ B : Subgroup G, A ≤ B ∧ B ≤ t.Zv 0 ∧ t.K ≤ normalizer (B : Set G) ∧ B ≠ A ∧
      ∀ z ∈ B, ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ A := by
  have hZS : t.Zv 0 ≤ S := t.r4i_Zv_zero_le_S hfr.hF
  have hAc : ∀ w ∈ S, ∀ c ∈ A, w * c * w⁻¹ = c := fun w hw c hc => by
    have := mem_centralizer_iff.mp (hAS hc) w hw
    rw [this]
    group
  have hZK : t.K ≤ normalizer (t.Zv 0 : Set G) := fun h hh =>
    t.Gv_le_normalizer_Zv 0 (t.K_le_Gv 0 hh)
  let B : Subgroup G :=
    { carrier := {z | z ∈ t.Zv 0 ∧ ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ A}
      mul_mem' := by
        rintro z w ⟨hz, hzc⟩ ⟨hw, hwc⟩
        refine ⟨mul_mem hz hw, fun s hs => ?_⟩
        have e : s * (z * w) * s⁻¹ * (z * w)⁻¹ =
            (s * z * s⁻¹ * z⁻¹) * (z * (s * w * s⁻¹ * w⁻¹) * z⁻¹) := by group
        rw [e, hAc z (hZS hz) _ (hwc s hs)]
        exact mul_mem (hzc s hs) (hwc s hs)
      one_mem' := ⟨one_mem _, fun s _ => by simp⟩
      inv_mem' := by
        rintro z ⟨hz, hzc⟩
        refine ⟨inv_mem hz, fun s hs => ?_⟩
        have e : s * z⁻¹ * s⁻¹ * z⁻¹⁻¹ = z⁻¹ * (s * z * s⁻¹ * z⁻¹)⁻¹ * z⁻¹⁻¹ := by group
        rw [e, hAc z⁻¹ (inv_mem (hZS hz)) _ (inv_mem (hzc s hs))]
        exact inv_mem (hzc s hs) }
  have hBmem : ∀ z, z ∈ B ↔ z ∈ t.Zv 0 ∧ ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ A := fun z => Iff.rfl
  have hAB : A ≤ B := fun a ha => (hBmem a).mpr ⟨hAZ ha, fun s hs => by
    rw [hAc s hs a ha]
    simp⟩
  have hBZ : B ≤ t.Zv 0 := fun z hz => ((hBmem z).mp hz).1
  have hBK : t.K ≤ normalizer (B : Set G) := by
    refine r4i_le_normalizer_of_forall fun k hk y hy => ?_
    obtain ⟨hyZ, hyc⟩ := (hBmem y).mp hy
    refine (hBmem _).mpr ⟨(mem_normalizer_iff.mp (hZK hk) y).mp hyZ, fun s hs => ?_⟩
    have hs' : k⁻¹ * s * k ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem (hfr.hN (t.hHall.1 hk))) s).mp hs
      rwa [inv_inv] at this
    have e : s * (k * y * k⁻¹) * s⁻¹ * (k * y * k⁻¹)⁻¹ =
        k * ((k⁻¹ * s * k) * y * (k⁻¹ * s * k)⁻¹ * y⁻¹) * k⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hAK hk) _).mp (hyc _ hs')
  obtain ⟨y, hyZ, hyA, hy⟩ := r4i_exists_fixed_mod (r4i_isPGroup_S t hfr) hZS (hAZ.trans hZS)
    (fun s hs => t.Gv_le_normalizer_Zv 0 (t.r4i_S_le_Gv_zero hs))
    (Subgroup.le_centralizer_iff.mp hAS |>.trans (Subgroup.centralizer_le_normalizer _)) hZA
  refine ⟨B, hAB, hBZ, hBK, fun hBA => hyA ?_, fun z hz => ((hBmem z).mp hz).2⟩
  rw [← hBA]
  exact (hBmem y).mpr ⟨hyZ, fun s hs => by simpa [commutatorElement_def] using hy s hs⟩

private theorem r4i_L1_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hSC : S ≤ centralizer (t.Zv 0 : Set G)) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hQ1le : pCoreOf 2 L1 ≤ t.Qv 0 := by
    rw [t.Qv_zero]
    exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1
  have hL1P : L1 ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact le_sup_left
  have hQC : t.Qv 0 ≤ centralizer (t.Zv 0 : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0)
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hfr.hF.1
  obtain ⟨g, hgL1, hgB⟩ := SetLike.exists_of_lt (CFSG.Quasithin.F1.lt_borelOf hR)
  have hgN : g ∉ normalizer ((S ⊓ L1 : Subgroup G) : Set G) := fun h => hgB ⟨hgL1, h⟩
  have hL1N : g ∈ normalizer (L1 : Set G) := Subgroup.le_normalizer hgL1
  have hT'syl : IsSylowTwoOf ((S ⊓ L1).map (MulAut.conj g).toMonoidHom) L1 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj g) hTsyl
    rwa [r4c_map_conj_eq_of_mem hL1N] at h
  have hne : (S ⊓ L1) ≠ (S ⊓ L1).map (MulAut.conj g).toMonoidHom := fun h =>
    hgN (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hgZ : g ∈ normalizer (t.Zv 0 : Set G) := t.Gv_le_normalizer_Zv 0 (hL1P hgL1)
  have hL := le_sup_pCoreOf_of_sylow_ne_of_sz (X := centralizer (t.Zv 0 : Set G)) hfr.ha hfr.hSz
    hTsyl hT'syl hne (fun x hx _ => mem_sup_left (hSC (mem_inf.mp hx).1))
    (fun x hx _ => mem_sup_left (by
      rw [mem_map_conj_iff] at hx
      rw [mem_centralizer_iff]
      intro z hz
      have hw : g⁻¹ * z * g ∈ t.Zv 0 := by
        have := (mem_normalizer_iff.mp (inv_mem hgZ) z).mp hz
        rwa [inv_inv] at this
      have h := mem_centralizer_iff.mp (hSC (mem_inf.mp hx).1) _ hw
      calc z * x = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [h]
        _ = x * z := by group))
  exact hL.trans (sup_le le_rfl (hQ1le.trans hQC))

private theorem r4i_L1_le_centralizer_of_quadratic {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A : Subgroup G} (hAS : A ≤ centralizer (S : Set G))
    (hquad : ∀ z ∈ t.Zv 0, ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ A) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  have hAc : ∀ w ∈ S, ∀ c ∈ A, w * c * w⁻¹ = c := fun w hw c hc => by
    have := mem_centralizer_iff.mp (hAS hc) w hw
    rw [this]
    group
  have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup G) (t.Zv 0) := by
    refine ⟨bot_le, ?_, fun e he => ?_⟩
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (t.r4c_Zv_comm 0 hx hy)
    · rw [t.r4c_sq_eq_one 0 he]
      exact one_mem _
  have hL1P : L1 ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact le_sup_left
  have hL : L1 ≤ normalizer (t.Zv 0 : Set G) ⊓ normalizer ((⊥ : Subgroup G) : Set G) := by
    refine le_inf (hL1P.trans (t.Gv_le_normalizer_Zv 0)) fun g _ => ?_
    rw [mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  have hQ1le : pCoreOf 2 L1 ≤ t.Qv 0 := by
    rw [t.Qv_zero]
    exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1
  have hQ : ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.Zv 0, ⁅p, v⁆ ∈ (⊥ : Subgroup G) := by
    intro p hp v hv
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hv) p (hQ1le hp))
  have hq : ∀ s ∈ S ⊓ L1, ∀ v ∈ t.Zv 0, ⁅s, ⁅s, v⁆⁆ ∈ (⊥ : Subgroup G) := by
    intro s hs v hv
    have hsS : s ∈ S := (mem_inf.mp hs).1
    have hc : s * v * s⁻¹ * v⁻¹ ∈ A := hquad v hv s hsS
    have h := hAc s hsS _ hc
    rw [Subgroup.mem_bot]
    simp only [commutatorElement_def]
    rw [h]
    simp
  have key := CFSG.Quasithin.Stroth.commutator_mem_of_quadratic_of_sz hfr.ha hfr.hSz
    hfr.hF.1.h1.sylow hsec hL hQ hq
  intro l hl
  rw [mem_centralizer_iff]
  intro z hz
  have h := Subgroup.mem_bot.mp (key l hl z hz)
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

private theorem r4i_S_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hL1 : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    S ≤ centralizer (t.Zv 0 : Set G) := by
  have hSQ : S = t.Qv 0 ⊔ (S ⊓ L1) := by
    have h := eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
    rw [sup_comm] at h
    rw [t.Qv_zero]
    exact h
  have hQC : t.Qv 0 ≤ centralizer (t.Zv 0 : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0)
  exact hSQ.le.trans (sup_le hQC (inf_le_right.trans hL1))

private theorem r4i_Zv_zero_eq_of_m_three {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hQ : Nat.card (pCoreOf 2 (t.Gw (-5) 1)) = 2 ^ f)
    (hZ1 : t.Zv 0 ≤ t.Gw (-3) 3)
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f) :
    t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := t.le_pCoreOf_Gw hfr (u := -3) (w := 3) (by norm_num) (t.isPGroup_Zv 0) hZ1
  have hmap : pCoreOf 2 (t.Gw (-3) 3) =
      (pCoreOf 2 (t.Gw (-5) 1)).map (MulAut.conj ((t.x₂ * t.x₁) ^ (1 : ℤ))).toMonoidHom := by
    rw [← pCoreOf_map_mulEquiv 2 (MulAut.conj ((t.x₂ * t.x₁) ^ (1 : ℤ))) (t.Gw (-5) 1),
      t.r4b_map_Gw]
    norm_num
  have hcard : Nat.card (pCoreOf 2 (t.Gw (-3) 3)) = 2 ^ f := by
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj _).injective, hQ]
  have hle : Nat.card (t.Zv 0) ≤ 2 ^ f := hcard ▸ Subgroup.card_le_of_le h2
  exact (Subgroup.eq_of_le_of_card_ge (t.r4i_A_le_Zv_zero hfr) (by rw [hcardA]; exact hle)).symm

private theorem r4i_Zv_zero_eq_of_even {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m)
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (hZ1 : t.Zv 0 ≤ t.Gw (1 - m) (m - 1))
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f) :
    t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAZ : t.Zv 1 ⊓ centralizer (S : Set G) ≤ t.Zv 0 := t.r4i_A_le_Zv_zero hfr
  have hr : 2 ^ f ≤ Nat.card (t.Zv 0) := hcardA ▸ Subgroup.card_le_of_le hAZ
  have hr4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  rcases t.r4i_card_dichotomy hfr hm (by omega) hZ1 hwlog hr with hcard | hcard
  · exact (Subgroup.eq_of_le_of_card_ge hAZ (by rw [hcard, hcardA])).symm
  · exfalso
    have hAK := t.r4i_K_le_normalizer_A hfr
    have hZA : ¬ t.Zv 0 ≤ t.Zv 1 ⊓ centralizer (S : Set G) := by
      intro hle
      have h := Subgroup.card_le_of_le hle
      rw [hcard, hcardA] at h
      nlinarith
    obtain ⟨B, hAB, hBZ, hBK, hBA, hBq⟩ := t.r4i_exists_B hfr hAZ inf_le_right hAK hZA
    have hBZ' : B = t.Zv 0 :=
      (t.eq_or_eq_of_B hfr hm hZ1 hwlog hcard hcardA hAK hAB hBZ hBK).resolve_left hBA
    have hquad : ∀ z ∈ t.Zv 0, ∀ s ∈ S, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 1 ⊓ centralizer (S : Set G) :=
      fun z hz s hs => hBq z (hBZ' ▸ hz) s hs
    have hL1 := t.r4i_L1_le_centralizer_of_quadratic hfr inf_le_right hquad
    have hSC := t.r4i_S_le_centralizer hfr hL1
    have hZQ : t.Zv 0 ≤ t.Qv 1 :=
      t.le_Qv_of_le_Gw hfr (u := 1 - m) (w := m - 1) (j := 1) (by omega) (by omega)
        (t.isPGroup_Zv 0) hZ1
    have hQ1S : t.Qv 1 ≤ S := by
      rw [t.Qv_one]
      exact Q2_le_S hfr.hF
    have hZZ : t.Zv 0 ≤ t.Zv 1 := by
      intro z hz
      rw [t.Zv_eq 1]
      refine CFSG.Quasithin.mem_omegaOneCenterOf (hZQ hz) (fun y hy => ?_)
        (t.r4c_sq_eq_one 0 hz)
      exact (mem_centralizer_iff.mp (hSC (hQ1S hy)) z hz).symm
    exact hZA (le_inf hZZ (Subgroup.le_centralizer_iff.mpr hSC))

theorem Zv_zero_eq_and_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {m b₀ : ℕ} (hb₀ : Even b₀) (hb₀1 : 1 ≤ b₀) (hm1 : m ≤ b₀ + 2)
    (hm2 : b₀ < m)
    (h3 : 3 * b₀ ≤ 2 * m)
    (hQ : Nat.card (pCoreOf 2 (t.Gw (1 - 2 * m) 1)) = 2 ^ f)
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (hZ1 : t.Zv 0 ≤ t.Gw (-((b₀ + 1 : ℕ) : ℤ)) (b₀ + 1))
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f) :
    t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G) ∧ L1 ≤ centralizer (t.Zv 0 : Set G) := by
  have harith : (m = 3 ∧ b₀ = 2) ∨ (b₀ + 2 = m ∧ Even m) := by
    obtain ⟨c, hc⟩ := hb₀
    by_cases h : m = b₀ + 2
    · exact Or.inr ⟨h.symm, ⟨c + 1, by omega⟩⟩
    · exact Or.inl ⟨by omega, by omega⟩
  have hZA : t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G) := by
    rcases harith with ⟨hm3, hb2⟩ | ⟨hmb, hm⟩
    · subst hm3
      subst hb2
      have hQ' : Nat.card (pCoreOf 2 (t.Gw (-5) 1)) = 2 ^ f := by simpa using hQ
      have hZ1' : t.Zv 0 ≤ t.Gw (-3) 3 := by simpa using hZ1
      exact t.r4i_Zv_zero_eq_of_m_three hfr hQ' hZ1' hcardA
    · have hm4 : 4 ≤ m := by
        obtain ⟨c, hc⟩ := hb₀
        omega
      have hZ1' : t.Zv 0 ≤ t.Gw (1 - m) (m - 1) := by
        have e1 : -((b₀ + 1 : ℕ) : ℤ) = 1 - (m : ℤ) := by omega
        have e2 : (b₀ : ℤ) + 1 = (m : ℤ) - 1 := by omega
        rwa [e1, e2] at hZ1
      exact t.r4i_Zv_zero_eq_of_even hfr hm hm4 hwlog hZ1' hcardA
  refine ⟨hZA, t.r4i_L1_le_centralizer hfr ?_⟩
  exact Subgroup.le_centralizer_iff.mp (hZA.le.trans inf_le_right)

private theorem r4j_map_Zv_x₁ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₁).toMonoidHom = t.Zv (-i) :=
  t.track.map_qv_x₁ r4c_P1_le_normalizer_Z1 r4c_P2_le_normalizer_Z2 i

private theorem r4j_map_Zv_x₂ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₂).toMonoidHom = t.Zv (2 - i) :=
  t.track.map_qv_x₂ r4c_P1_le_normalizer_Z1 r4c_P2_le_normalizer_Z2 i

private theorem r4j_map_conj_mul (K : Subgroup G) (g h : G) :
    K.map (MulAut.conj (g * h)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [mem_map_conj_iff, mul_inv_rev, mul_assoc]

private theorem r4j_reflect (c : ℤ) :
    ∃ y : G, ∀ i : ℤ, (t.Zv i).map (MulAut.conj y).toMonoidHom = t.Zv (2 * c - i) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' c
  · refine ⟨(t.x₂ * t.x₁) ^ k * t.x₁ * (t.x₂ * t.x₁) ^ (-k), fun i => ?_⟩
    rw [r4j_map_conj_mul, r4j_map_conj_mul, t.r4b_map_Zv, t.r4j_map_Zv_x₁, t.r4b_map_Zv]
    congr 1
    ring
  · refine ⟨(t.x₂ * t.x₁) ^ k * t.x₂ * (t.x₂ * t.x₁) ^ (-k), fun i => ?_⟩
    rw [r4j_map_conj_mul, r4j_map_conj_mul, t.r4b_map_Zv, t.r4j_map_Zv_x₂, t.r4b_map_Zv]
    congr 1
    ring

private theorem r4j_exists_hom {Z : Subgroup G}
    (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) {s : G} (hs : s ∈ normalizer (Z : Set G)) :
    ∃ φ : ↥Z →* ↥Z, ∀ z : ↥Z, (φ z : G) = s * (z : G) * s⁻¹ * (z : G)⁻¹ := by
  refine ⟨MonoidHom.mk' (fun z : ↥Z => (⟨s * (z : G) * s⁻¹ * (z : G)⁻¹,
    mul_mem (r4b_conj_mem hs z.2) (inv_mem z.2)⟩ : ↥Z)) ?_, fun z => rfl⟩
  intro x y
  apply Subtype.ext
  have hy := r4b_conj_mem hs y.2
  have hc : (x : G)⁻¹ * (s * y * s⁻¹ * (y : G)⁻¹) = (s * y * s⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ :=
    hcomm _ (inv_mem x.2) _ (mul_mem hy (inv_mem y.2))
  have e1 : s * ((x : G) * y) * s⁻¹ * ((x : G) * y)⁻¹ =
      (s * x * s⁻¹) * ((s * y * s⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) := by group
  have e2 : (s * x * s⁻¹ * (x : G)⁻¹) * (s * y * s⁻¹ * (y : G)⁻¹) =
      (s * x * s⁻¹) * ((x : G)⁻¹ * (s * y * s⁻¹ * (y : G)⁻¹)) := by group
  simp only [Subgroup.coe_mul]
  rw [e1, e2, hc]

private theorem r4j_surj_comm {Z A : Subgroup G} {s : G} {r : ℕ} (hr : 0 < r)
    (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hs : s ∈ normalizer (Z : Set G))
    (hAZ : A ≤ Z) (hAc : ∀ z ∈ A, s * z * s⁻¹ = z)
    (hker : ∀ z ∈ Z, s * z * s⁻¹ = z → z ∈ A) (hcom : ∀ z ∈ Z, s * z * s⁻¹ * z⁻¹ ∈ A)
    (hZ : Nat.card Z = r * r) (hA : Nat.card A = r) :
    ∀ a ∈ A, ∃ z ∈ Z, s * z * s⁻¹ * z⁻¹ = a := by
  obtain ⟨φ, hφ⟩ := r4j_exists_hom hcomm hs
  have hker_eq : φ.ker = A.subgroupOf Z := by
    ext z
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : s * (z : G) * s⁻¹ * (z : G)⁻¹ = 1 := by
        rw [← hφ z, h]
        rfl
      exact hker z z.2 (mul_inv_eq_one.mp h1)
    · intro h
      apply Subtype.ext
      rw [hφ z, hAc z h]
      simp
  have hrange_le : φ.range ≤ A.subgroupOf Z := by
    rintro _ ⟨z, rfl⟩
    rw [mem_subgroupOf, hφ z]
    exact hcom z z.2
  have hcardsub : Nat.card (A.subgroupOf Z) = r := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hkr := card_ker_mul_card_range φ
  rw [hker_eq, hcardsub, hZ] at hkr
  have hrange_card : Nat.card φ.range = r := Nat.eq_of_mul_eq_mul_left hr hkr
  have hrange_eq : φ.range = A.subgroupOf Z :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hcardsub, hrange_card])
  intro a ha
  have hmem : (⟨a, hAZ ha⟩ : ↥Z) ∈ A.subgroupOf Z := mem_subgroupOf.mpr ha
  rw [← hrange_eq] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, z.2, by rw [← hφ z, hz]⟩

private theorem r4j_Y_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {b₀ : ℕ} (hb₀ : Even b₀) (hb : 1 ≤ b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) : t.Zv (1 - b₀) ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYG : t.Zv (1 - b₀) ≤ t.Gw 0 1 :=
    (t.Zv_one_sub_le_Gw hb₀ hZ0).trans (win_mono (by omega) le_rfl)
  have h := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv _) hYG
  rwa [t.pCoreOf_Gw_zero_one hfr] at h

private theorem r4j_commutator_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀) (hb : 1 ≤ b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀))
    (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f)
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 1 ⊓ centralizer (S : Set G))
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z →
      z ∈ t.Zv 1 ⊓ centralizer (S : Set G)) :
    ⁅t.Zv 1, t.Zv (1 - b₀)⁆ = t.Zv 1 ⊓ centralizer (S : Set G) := by
  have hYS := t.r4j_Y_le_S hfr hb₀ hb hZ0
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro z hz y hy
    have h := inv_mem (hN1 y (hYS hy) z hz)
    rwa [show (y * z * y⁻¹ * z⁻¹)⁻¹ = ⁅z, y⁆ by rw [commutatorElement_def]; group] at h
  · have hYQ : ¬ t.Zv (1 - b₀) ≤ t.Qv 1 := by
      intro hle
      have h2 := (t.Qv_le_Gv hfr 1).2
      rw [show (1 : ℤ) + 1 = 2 by norm_num] at h2
      exact t.Zv_one_sub_not_le_Gv_two hb₀ hZ0' (hle.trans h2)
    obtain ⟨s, hsY, hsQ⟩ := SetLike.not_le_iff_exists.mp hYQ
    have hsS : s ∈ S := hYS hsY
    have hsG : s ∈ t.Gv 1 :=
      ((t.Zv_one_sub_le_Gw hb₀ hZ0).trans (win_le_qv (by omega) le_rfl)) hsY
    have hsN : s ∈ normalizer (t.Zv 1 : Set G) := t.Gv_le_normalizer_Zv 1 hsG
    have hr : 0 < 2 ^ f := by positivity
    have key := r4j_surj_comm hr (fun x hx y hy => t.r4c_Zv_comm 1 hx hy) hsN
      (inf_le_left : t.Zv 1 ⊓ centralizer (S : Set G) ≤ t.Zv 1)
      (fun z hz => by
        have := mem_centralizer_iff.mp hz.2 s hsS
        calc s * z * s⁻¹ = z * s * s⁻¹ := by rw [this]
          _ = z := by group)
      (fun z hz h => hN2 s hsS hsQ z hz h) (fun z hz => hN1 s hsS z hz) hcard0 hcardA
    intro a ha
    obtain ⟨z, hz, rfl⟩ := key a ha
    have hcm := inv_mem (Subgroup.commutator_mem_commutator hz hsY)
    rwa [show (⁅z, s⁆)⁻¹ = s * z * s⁻¹ * z⁻¹ by rw [commutatorElement_def]; group] at hcm

theorem eq_two_of_Zv_zero_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hO4 : t.GT = t.K) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀))
    (hZ1 : t.Zv 0 ≤ t.Gw (-((b₀ + 1 : ℕ) : ℤ)) (b₀ + 1))
    (hA : t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G))
    (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f)
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 1 ⊓ centralizer (S : Set G))
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z →
      z ∈ t.Zv 1 ⊓ centralizer (S : Set G)) :
    b₀ = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 1 ≤ b₀ := by
    by_contra hb
    have h0 : b₀ = 0 := by omega
    apply hZ0'
    rw [h0, Nat.cast_zero, add_zero]
    exact (t.Zv_le_Qv 1).trans (t.Qv_one_le_Gv_two hfr)
  have hX : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ = t.Zv 0 := by
    rw [hA]
    exact t.r4j_commutator_eq hfr hb₀ hb hZ0 hZ0' hcard0 hcardA hN1 hN2
  have hb₀' := hb₀
  obtain ⟨c', hc'⟩ := hb₀'
  obtain ⟨y, hy⟩ := t.r4j_reflect (1 - (c' : ℤ))
  have hy1 : (t.Zv 1).map (MulAut.conj y).toMonoidHom = t.Zv (1 - b₀) := by
    rw [hy]
    congr 1
    omega
  have hy2 : (t.Zv (1 - b₀)).map (MulAut.conj y).toMonoidHom = t.Zv 1 := by
    rw [hy]
    congr 1
    omega
  have hy0 : (t.Zv 0).map (MulAut.conj y).toMonoidHom = t.Zv (2 - b₀) := by
    rw [hy]
    congr 1
    omega
  have hXinv : (⁅t.Zv 1, t.Zv (1 - b₀)⁆).map (MulAut.conj y).toMonoidHom =
      ⁅t.Zv 1, t.Zv (1 - b₀)⁆ := by
    rw [Subgroup.map_commutator, hy1, hy2, Subgroup.commutator_comm]
  have hZ2 : t.Zv (2 - b₀) = t.Zv 0 := by
    rw [← hy0, ← hX]
    exact hXinv
  by_contra hne
  have hb4 : 4 ≤ b₀ := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (c' : ℤ) - 1 := ⟨_, rfl⟩
  have hnorm : (t.Zv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv 0 := by
    have h1 := t.r4b_map_Zv (2 - b₀) k
    rw [hZ2] at h1
    rw [h1]
    congr 1
    omega
  have hτN : (t.x₂ * t.x₁) ^ k ∈ normalizer ((t.Zv 0 : Subgroup G) : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr hnorm
  have hall : ∀ m : ℤ,
      (t.Zv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ (k * m))).toMonoidHom = t.Zv 0 := by
    intro m
    have h := zpow_mem hτN m
    rw [← zpow_mul] at h
    exact mem_normalizer_iff_map_conj_eq.mp h
  have hGv : ∀ i : ℤ, t.Zv 0 ≤ t.Gv i := by
    intro i
    have hkpos : 0 < 2 * k := by omega
    obtain ⟨m, r, hr0, hr1, hmr⟩ : ∃ m r : ℤ, 0 ≤ r ∧ r < 2 * k ∧ i = r + (2 * k) * m :=
      ⟨i / (2 * k), i % (2 * k), Int.emod_nonneg _ hkpos.ne', Int.emod_lt_of_pos _ hkpos,
        (Int.emod_add_mul_ediv i (2 * k)).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n = k * m := ⟨_, rfl⟩
    have hin : i = r + 2 * n := by rw [hmr, hn]; ring
    have h := Subgroup.map_mono
      (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (k * m))).toMonoidHom) hZ1
    rw [hall m, t.r4b_map_Gw] at h
    exact h.trans (win_le_qv (by omega) (by omega))
  have hK : t.Zv 0 ≤ t.K := by
    rw [← hO4]
    exact le_iInf hGv
  have hdvd : Nat.card (t.Zv 0) ∣ Nat.card t.K := Subgroup.card_dvd_of_le hK
  rw [hA, hcardA] at hdvd
  have h2 : 2 ∣ Nat.card t.K := (dvd_pow_self 2 (by have := hfr.hf; omega)).trans hdvd
  exact (t.hHall.2.1 : Odd (Nat.card t.K)).not_two_dvd_nat h2

private theorem r4k_map_Gv_x₁ (i : ℤ) :
    (t.Gv i).map (MulAut.conj t.x₁).toMonoidHom = t.Gv (-i) :=
  t.track.map_qv_x₁ Subgroup.le_normalizer Subgroup.le_normalizer i

private theorem r4k_P1_le_normalizer_L1 (hF : Hyp111 L1 L2 S) :
    P1 L1 L2 S ≤ normalizer (L1 : Set G) :=
  sup_le le_normalizer (bigB_le_normalizer_of_hyp111 hF)

private theorem r4k_P1_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : P1 L1 L2 S ≤ (L1 ⊔ Q1 L1 L2 S) ⊔ t.K := by
  have hS : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hSle : S ≤ L1 ⊔ Q1 L1 L2 S :=
    hS.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  rw [t.hBsplit]
  exact sup_le (sup_le (hSle.trans le_sup_left) (le_sup_left.trans le_sup_right))
    (le_sup_right.trans le_sup_right)

private theorem r4k_K_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer ((L1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
  have hK : t.K ≤ P1 L1 L2 S := by
    rw [← t.Gv_zero]
    exact t.K_le_Gv 0
  have hQ : P1 L1 L2 S ≤ normalizer (Q1 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  exact F1.le_normalizer_sup (hK.trans (r4k_P1_le_normalizer_L1 hfr.hF.1)) (hK.trans hQ)

include t in
private theorem r4k_mem_of_pow_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {x : G} (hx : x ∈ P1 L1 L2 S) {j : ℕ} (hxj : x ^ 2 ^ j = 1) :
    x ∈ L1 ⊔ Q1 L1 L2 S := by
  have hK := t.r4k_K_le_normalizer hfr
  obtain ⟨n, hn, k, hk, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hK).1 (t.r4k_P1_le_sup hfr hx)
  have hkodd : Odd (orderOf k) :=
    t.hHall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨n', hn', h⟩ := A4.exists_pow_mul_eq hn (hK hk) (2 ^ j)
  rw [hxj] at h
  have hkj : k ^ 2 ^ j ∈ L1 ⊔ Q1 L1 L2 S := by
    have : k ^ 2 ^ j = n'⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this]
    exact inv_mem hn'
  exact mul_mem hn (B1Red.mem_of_two_pow_mem_of_odd hkj hkodd)

private theorem r4k_not_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₁ : ℕ} (hb₁ : Odd b₁) (hZ1 : t.Zv 1 ≤ t.Gv (1 + b₁))
    (hna : ¬ ⁅t.Zv 1, t.Zv (1 + b₁)⁆ ≤ t.Zv 1 ⊓ t.Zv (1 + b₁)) :
    ¬ L1 ≤ centralizer (t.Zv 0 : Set G) := by
  intro hL1
  have hQ : Q1 L1 L2 S ≤ centralizer (t.Zv 0 : Set G) := by
    have h := le_centralizer_iff.mp (t.Zv_le_centralizer 0)
    rwa [t.Qv_zero] at h
  have hN : L1 ⊔ Q1 L1 L2 S ≤ centralizer (t.Zv 0 : Set G) := sup_le hL1 hQ
  obtain ⟨m, hm⟩ := hb₁
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 0 + 2 * k = 1 + (b₁ : ℤ) := ⟨(m : ℤ) + 1, by rw [hm]; push_cast; ring⟩
  have hZmap : (t.Zv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (1 + b₁) := by
    rw [← hk]
    exact t.r4b_map_Zv 0 k
  have hGmap : (t.Gv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Gv (1 + b₁) := by
    rw [← hk]
    exact t.r4b_map_Gv 0 k
  have hcent : t.Zv 1 ≤ centralizer (t.Zv (1 + b₁) : Set G) := by
    intro z hz w hw
    set g : G := (t.x₂ * t.x₁) ^ k
    have hzG : g⁻¹ * z * g ∈ t.Gv 0 :=
      mem_map_conj_iff.mp (hGmap ▸ hZ1 hz)
    have hwZ : g⁻¹ * w * g ∈ t.Zv 0 := mem_map_conj_iff.mp (hZmap ▸ hw)
    obtain ⟨j, hj⟩ := t.isPGroup_Zv 1 ⟨z, hz⟩
    have hzj : z ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hzj' : (g⁻¹ * z * g) ^ 2 ^ j = 1 := by
      have h := conj_pow (a := g⁻¹) (b := z) (i := 2 ^ j)
      rw [inv_inv] at h
      rw [h, hzj]
      group
    have hmem : g⁻¹ * z * g ∈ L1 ⊔ Q1 L1 L2 S :=
      t.r4k_mem_of_pow_eq_one hfr (by rwa [t.Gv_zero] at hzG) hzj'
    have h := mem_centralizer_iff.mp (hN hmem) (g⁻¹ * w * g) hwZ
    calc w * z = g * (g⁻¹ * w * g * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = z * w := by group
  exact hna ((commutator_eq_bot_iff_le_centralizer.mpr hcent).le.trans bot_le)

private theorem r4k_one_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1)) : 1 ≤ b₀ := by
  by_contra h
  have hb : b₀ = 0 := by omega
  subst hb
  apply hZ0'
  have h1 := (t.Qv_le_Gv hfr 0).2
  rw [zero_add] at h1
  simpa using (t.Zv_le_Qv 0).trans h1

private theorem r4k_Zv_le_Gw {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c)
    (hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀) : t.Zv b₀ ≤ t.Gw 0 (2 * b₀) := by
  have h := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (c : ℤ))).toMonoidHom) hZ0
  rw [t.r4b_map_Zv, t.r4b_map_Gw] at h
  rw [show (0 : ℤ) + 2 * (c : ℤ) = b₀ by omega,
    show -(b₀ : ℤ) + 2 * (c : ℤ) = 0 by omega,
    show (b₀ : ℤ) + 2 * (c : ℤ) = 2 * b₀ by omega] at h
  exact h

private theorem r4k_Zv_le_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c) (hb : 1 ≤ b₀)
    (hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀) : t.Zv b₀ ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : t.Zv b₀ ≤ t.Gw 0 1 :=
    (t.r4k_Zv_le_Gw hc hZ0).trans (win_mono le_rfl (by omega))
  have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv _) h1
  rwa [t.pCoreOf_Gw_zero_one hfr] at h2

private theorem r4k_not_Zv_le_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c)
    (hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1)) : ¬ t.Zv b₀ ≤ t.Qv 0 := by
  intro h
  apply hZ0'
  have h1 := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (-(c : ℤ)))).toMonoidHom) h
  rw [t.r4b_map_Zv, t.r4e_map_Qv, show (b₀ : ℤ) + 2 * -(c : ℤ) = 0 by omega,
    show (0 : ℤ) + 2 * -(c : ℤ) = -(b₀ : ℤ) by omega] at h1
  have h2 := h1.trans (t.Qv_le_Gv hfr (-(b₀ : ℤ))).1
  have h3 := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) h2
  rw [t.r4j_map_Zv_x₁, t.r4k_map_Gv_x₁, neg_zero,
    show -(-(b₀ : ℤ) - 1) = (b₀ : ℤ) + 1 by ring] at h3
  exact h3

private theorem r4k_relIndex_Zv_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hY : t.Zv b₀ ≤ S) :
    (t.Qv 0).relIndex (t.Zv b₀) ≤ 2 ^ (2 * a + 1) := by
  obtain ⟨Ω, hΩmem, -, hΩidx⟩ := t.exists_omega_of_sz hfr
  have hle : t.Zv b₀ ≤ Ω := by
    intro y hy
    refine (hΩmem y).mpr ⟨hY hy, ?_⟩
    rw [t.r4c_sq_eq_one b₀ hy]
    exact one_mem _
  exact (Subgroup.relIndex_le_of_le_right hle (r4c_relIndex_ne_zero _ _)).trans hΩidx

private theorem r4k_relIndex_neg {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c) :
    (t.Qv (-(b₀ : ℤ))).relIndex (t.Zv 0) = (t.Qv 0).relIndex (t.Zv b₀) := by
  rw [← Subgroup.relIndex_map_map_of_injective
    (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (-(c : ℤ)))).toMonoidHom) (t.Qv 0) (t.Zv b₀)
    (MulAut.conj _).injective, t.r4e_map_Qv, t.r4b_map_Zv,
    show (0 : ℤ) + 2 * -(c : ℤ) = -(b₀ : ℤ) by omega,
    show (b₀ : ℤ) + 2 * -(c : ℤ) = 0 by omega]

private theorem r4k_relIndex_pos (b₀ : ℤ) :
    (t.Qv b₀).relIndex (t.Zv 0) = (t.Qv (-b₀)).relIndex (t.Zv 0) := by
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t.x₁).toMonoidHom) (t.Qv b₀)
    (t.Zv 0) (MulAut.conj _).injective, t.r4e_map_Qv_x₁, t.r4j_map_Zv_x₁, neg_zero]

private theorem r4k_mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (X := Subgroup.zpowers g) (zpowers_le.mpr hH) (zpowers_le.mpr hK)
    (mem_zpowers g)

private theorem r4k_pCoreOf_le_Qv_zero (hF : Hyp111 L1 L2 S) : pCoreOf 2 L1 ≤ t.Qv 0 := by
  rw [t.Qv_zero]
  exact Hyp111.pCoreOf_le_pCoreOf_vertex hF

private theorem r4k_D1_le_normalizer_T : t.D1 ≤ normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
  t.hD1hall.1.trans inf_le_right

private theorem r4k_T_le_normalizer_Qv_zero : S ⊓ L1 ≤ normalizer (t.Qv 0 : Set G) := by
  have h : P1 L1 L2 S ≤ normalizer (t.Qv 0 : Set G) := by
    rw [← t.Gv_zero]
    exact t.Gv_le_normalizer_Qv 0
  exact inf_le_right.trans (le_sup_left.trans h)

private theorem r4k_S_eq_sup_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S = t.Qv 0 ⊔ (S ⊓ L1) := by
  have h := eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  rw [sup_comm] at h
  rw [t.Qv_zero]
  exact h

private theorem r4k_x₁_mem_normalizer_L1 (hF : Hyp111 L1 L2 S) :
    t.x₁ ∈ normalizer (L1 : Set G) :=
  r4k_P1_le_normalizer_L1 hF t.track.x₁_mem

private theorem r4k_ne_conj_x₁ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    S ⊓ L1 ≠ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hSQ : S = t.Qv 0 ⊔ (S ⊓ L1) := t.r4k_S_eq_sup_Qv_zero hfr
  intro heq
  have hTG01 : S ⊓ L1 ≤ t.Gw 0 1 := inf_le_left.trans (t.S_le_Gw_zero_one hfr.hF)
  have hT'G : (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom ≤ t.Gw (-1) 0 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hTG01
    have e := t.track.map_win_x₁ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1
    rw [neg_zero] at e
    exact h.trans e.le
  have hTG : S ⊓ L1 ≤ t.Gw (-1) 1 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ 0 ∨ i = 1 by omega) with h3 | rfl
    · have hy' : y ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom := heq ▸ hy
      exact mem_win_iff.mp (hT'G hy') i h1 h3
    · exact mem_win_iff.mp (hTG01 hy) 1 (by norm_num) le_rfl
  have hTQ : S ⊓ L1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num)
      hTsyl.2.1 hTG
  have hSle : S ≤ t.Qv 0 := hSQ.le.trans (sup_le le_rfl hTQ)
  have hQS : (t.Qv 0).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 0).2
  rw [zero_add, t.pCoreOf_Gw_zero_one hfr, if_pos (by decide), hQS] at h9
  have h4 : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  omega

private theorem r4k_KI {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {Y : Subgroup G} (hYS : Y ≤ S)
    (hYD : t.D1 ≤ normalizer (Y : Set G)) (hYQ : ¬ Y ≤ t.Qv 0) :
    ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 → x ∈ Y ⊔ t.Qv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hQ1le : pCoreOf 2 L1 ≤ t.Qv 0 := t.r4k_pCoreOf_le_Qv_zero hfr.hF.1
  have hTQ' : S ⊓ L1 ≤ normalizer (t.Qv 0 : Set G) := t.r4k_T_le_normalizer_Qv_zero
  have hSQ : S = t.Qv 0 ⊔ (S ⊓ L1) := t.r4k_S_eq_sup_Qv_zero hfr
  have hXN : t.D1 ≤ normalizer (((Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) : Subgroup G) : Set G) := by
    intro d hd
    refine A4.mem_normalizer_inf ?_ (t.r4k_D1_le_normalizer_T hd)
    exact r4k_mem_normalizer_sup (hYD hd)
      (((le_sup_left : t.D1 ≤ t.K).trans (t.K_le_Gv 0)).trans (t.Gv_le_normalizer_Qv 0) hd)
  have hXnot : ¬ ((Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) ≤ pCoreOf 2 L1) := by
    intro hX
    apply hYQ
    intro y hy
    have hyS : y ∈ t.Qv 0 ⊔ (S ⊓ L1) := hSQ.le (hYS hy)
    obtain ⟨q, hq, τ, hτ, hyqτ⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTQ').mp hyS
    have hτy : τ = q⁻¹ * y := by rw [hyqτ]; group
    have hτX : τ ∈ (Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) := by
      refine ⟨?_, hτ⟩
      rw [hτy]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hy)
    rw [hyqτ]
    exact mul_mem hq (hQ1le (hX hτX))
  have hKI := mem_sup_pCoreOf_of_torus_of_sz hfr.ha hfr.hSz hTsyl t.hD1hall inf_le_right hXN hXnot
  intro x hx hx2
  exact (sup_le inf_le_left (hQ1le.trans le_sup_right) :
    (Y ⊔ t.Qv 0) ⊓ (S ⊓ L1) ⊔ pCoreOf 2 L1 ≤ Y ⊔ t.Qv 0) (hKI x hx hx2)

private theorem r4k_L1_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G}
    (hT : ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 → x ∈ X ⊔ pCoreOf 2 L1)
    (hT' : ∀ x ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom, x * x ∈ pCoreOf 2 L1 →
      x ∈ X ⊔ pCoreOf 2 L1) :
    L1 ≤ X ⊔ pCoreOf 2 L1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hT'syl : IsSylowTwoOf ((S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom) L1 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₁) hTsyl
    rwa [r4c_map_conj_eq_of_mem (t.r4k_x₁_mem_normalizer_L1 hfr.hF.1)] at h
  exact le_sup_pCoreOf_of_sylow_ne_of_sz hfr.ha hfr.hSz hTsyl hT'syl (t.r4k_ne_conj_x₁ hfr) hT hT'

private theorem r4k_comm_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ c : ℕ} (hc : (b₀ : ℤ) = 2 * c) (hb : 1 ≤ b₀)
    (hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀) (hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1)) :
    t.Zv 0 ⊓ (t.Qv b₀ ⊓ t.Qv (-(b₀ : ℤ))) ≤ centralizer (L1 : Set G) := by
  set C' : Subgroup G := t.Zv 0 ⊓ (t.Qv b₀ ⊓ t.Qv (-(b₀ : ℤ))) with hC'
  have hC'Z : C' ≤ t.Zv 0 := inf_le_left
  have hZ1 : t.Zv b₀ ≤ centralizer (C' : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro g hg
    exact mem_centralizer_iff.mp (t.Zv_le_centralizer b₀ hz) g (mem_inf.mp (mem_inf.mp hg).2).1
  have hZ2 : t.Zv (-(b₀ : ℤ)) ≤ centralizer (C' : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro g hg
    exact mem_centralizer_iff.mp (t.Zv_le_centralizer (-(b₀ : ℤ)) hz) g
      (mem_inf.mp (mem_inf.mp hg).2).2
  have hQ0 : t.Qv 0 ≤ centralizer (C' : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro g hg
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 0 (hC'Z hg)) q hq).symm
  have hYS : t.Zv b₀ ≤ S := t.r4k_Zv_le_S hfr hc hb hZ0
  have hYD : t.D1 ≤ normalizer (t.Zv b₀ : Set G) :=
    ((le_sup_left : t.D1 ≤ t.K).trans (t.K_le_Gv b₀)).trans (t.Gv_le_normalizer_Zv b₀)
  have hKI := t.r4k_KI hfr hYS hYD (t.r4k_not_Zv_le_Qv hfr hc hZ0')
  have hYQ : t.Zv b₀ ⊔ t.Qv 0 ≤ centralizer (C' : Set G) := sup_le hZ1 hQ0
  have hcenl : pCoreOf 2 L1 ≤ centralizer (C' : Set G) :=
    (t.r4k_pCoreOf_le_Qv_zero hfr.hF.1).trans hQ0
  have hx₁N : t.x₁ ∈ normalizer (pCoreOf 2 L1 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L1 (t.r4k_x₁_mem_normalizer_L1 hfr.hF.1)
  have h1 : ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 →
      x ∈ centralizer (C' : Set G) ⊔ pCoreOf 2 L1 :=
    fun x hx hx2 => mem_sup_left (hYQ (hKI x hx hx2))
  have h2 : ∀ x ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom, x * x ∈ pCoreOf 2 L1 →
      x ∈ centralizer (C' : Set G) ⊔ pCoreOf 2 L1 := by
    intro x hx hx2
    rw [mem_map_conj_iff] at hx
    have hy2 : (t.x₁⁻¹ * x * t.x₁) * (t.x₁⁻¹ * x * t.x₁) ∈ pCoreOf 2 L1 := by
      have e : (t.x₁⁻¹ * x * t.x₁) * (t.x₁⁻¹ * x * t.x₁) = t.x₁⁻¹ * (x * x) * t.x₁ := by group
      have h := r4b_conj_mem (inv_mem hx₁N) hx2
      rwa [inv_inv, ← e] at h
    have hy := hKI _ hx hy2
    have hxm : x ∈ (t.Zv b₀ ⊔ t.Qv 0).map (MulAut.conj t.x₁).toMonoidHom := by
      rw [mem_map_conj_iff]
      exact hy
    rw [Subgroup.map_sup, t.r4j_map_Zv_x₁, t.r4e_map_Qv_x₁, neg_zero] at hxm
    exact mem_sup_left ((sup_le hZ2 hQ0) hxm)
  have hL := t.r4k_L1_le_sup hfr h1 h2
  have hLC : L1 ≤ centralizer (C' : Set G) := hL.trans (sup_le le_rfl hcenl)
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_iff.mp (hLC hh) g hg).symm

private theorem r4k_isPerfect_oTwoQuot {L : Subgroup G} {a : ℕ} (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L ≃* Sz a)) : Group.IsPerfect (oTwoQuot ↥L) := by
  obtain ⟨e⟩ := hSz
  haveI hpS := CFSG.SectionRank.suzukiMatrixGroup_isPerfect a (by omega)
  haveI : Group.IsPerfect (Sz a) :=
    Group.IsPerfect.ofSurjective
      (f := (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm.toMonoidHom)
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm.surjective
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem r4k_le_commutator_sup_pCoreOf {L : Subgroup G}
    (hperf : Group.IsPerfect (oTwoQuot ↥L)) : L ≤ ⁅L, L⁆ ⊔ pCoreOf 2 L := by
  haveI := hperf
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hsup : commutator ↥L ⊔ pCore 2 ↥L = ⊤ := by
    have := Subgroup.comap_map_eq π (commutator ↥L)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  have := congrArg (Subgroup.map L.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at this
  exact this.ge

private theorem r4k_isElemSec :
    CFSG.GH74.QTGen4.DSGen4.IsElemSec (t.Zv 0 ⊓ centralizer (L1 : Set G)) (t.Zv 0) := by
  refine ⟨inf_le_left, ?_, fun e he => ?_⟩
  · have h : ⁅t.Zv 0, t.Zv 0⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun e he =>
        mem_centralizer_iff.mpr fun h hh => t.r4c_Zv_comm 0 hh he
    rw [h]
    exact bot_le
  · rw [t.r4c_sq_eq_one 0 he]
    exact Subgroup.one_mem _

private theorem r4k_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hrel : (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) < 2 ^ (4 * (2 * a + 1))) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  have hL1G : L1 ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact le_sup_left
  have hLV : L1 ≤ normalizer (t.Zv 0 : Set G) := hL1G.trans (t.Gv_le_normalizer_Zv 0)
  have hLC : L1 ≤ normalizer ((t.Zv 0 ⊓ centralizer (L1 : Set G) : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hQcent : pCoreOf 2 L1 ≤ centralizer (t.Zv 0 : Set G) :=
    (t.r4k_pCoreOf_le_Qv_zero hfr.hF.1).trans
      (Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0))
  have hQ : ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.Zv 0, ⁅p, v⁆ ∈ t.Zv 0 ⊓ centralizer (L1 : Set G) := by
    intro p hp v hv
    have h1 : ⁅p, v⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp (hQcent hp) v hv).symm
    rw [h1]
    exact Subgroup.one_mem _
  have hnt : ¬ ∃ l ∈ L1, ∃ v ∈ t.Zv 0, ⁅l, v⁆ ∉ t.Zv 0 ⊓ centralizer (L1 : Set G) := by
    intro hnt
    have h := two_pow_le_relIndex_of_nontrivial_of_sz hfr.ha hfr.hSz t.r4k_isElemSec
      (le_inf hLV hLC) hQ hnt
    omega
  push Not at hnt
  have hZL : ∀ l ∈ L1, ∀ v ∈ t.Zv 0, ⁅l, v⁆ ∈ t.Zv 0 ⊓ centralizer (L1 : Set G) := hnt
  have hLVZ : ⁅L1, t.Zv 0⁆ ≤ t.Zv 0 ⊓ centralizer (L1 : Set G) :=
    Subgroup.commutator_le.mpr hZL
  have hcL : ⁅L1, t.Zv 0⁆ ≤ centralizer (L1 : Set G) := hLVZ.trans inf_le_right
  have h1 : ⁅⁅L1, t.Zv 0⁆, L1⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcL
  have h2 : ⁅⁅t.Zv 0, L1⁆, L1⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (t.Zv 0) L1]
    exact h1
  have h3 : ⁅L1, L1⁆ ≤ centralizer (t.Zv 0 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
  exact (r4k_le_commutator_sup_pCoreOf (r4k_isPerfect_oTwoQuot hfr.ha hfr.hSz)).trans
    (sup_le h3 hQcent)

theorem L1_le_centralizer_Zv_zero_of_even {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀) (hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1)) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  obtain ⟨c, hc⟩ := hb₀
  have hc' : (b₀ : ℤ) = 2 * c := by omega
  have hb : 1 ≤ b₀ := t.r4k_one_le hfr hZ0'
  have hY : t.Zv b₀ ≤ S := t.r4k_Zv_le_S hfr hc' hb hZ0
  have h1 : (t.Qv 0).relIndex (t.Zv b₀) ≤ 2 ^ (2 * a + 1) := t.r4k_relIndex_Zv_le hfr hY
  have hle : t.Zv 0 ⊓ (t.Qv b₀ ⊓ t.Qv (-(b₀ : ℤ))) ≤ t.Zv 0 ⊓ centralizer (L1 : Set G) :=
    le_inf inf_le_left (t.r4k_comm_le hfr hc' hb hZ0 hZ0')
  have hK : (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) ≤
      2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
    calc (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0)
        ≤ (t.Zv 0 ⊓ (t.Qv b₀ ⊓ t.Qv (-(b₀ : ℤ)))).relIndex (t.Zv 0) :=
          Subgroup.relIndex_le_of_le_left hle (r4c_relIndex_ne_zero _ _)
      _ = (t.Qv b₀ ⊓ t.Qv (-(b₀ : ℤ))).relIndex (t.Zv 0) := by
          rw [inf_comm, Subgroup.inf_relIndex_right]
      _ ≤ (t.Qv b₀).relIndex (t.Zv 0) * (t.Qv (-(b₀ : ℤ))).relIndex (t.Zv 0) :=
          Subgroup.relIndex_inf_le
      _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
          rw [t.r4k_relIndex_pos b₀, t.r4k_relIndex_neg hc']
          exact Nat.mul_le_mul h1 h1
  refine t.r4k_le_centralizer hfr (lt_of_le_of_lt hK ?_)
  have hq : 2 ≤ 2 ^ (2 * a + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (4 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 4 := by
    rw [← pow_mul, mul_comm]
  rw [e]
  nlinarith [Nat.mul_le_mul hq hq, Nat.pos_of_ne_zero (show 2 ^ (2 * a + 1) ≠ 0 by positivity)]

theorem commutator_le_inf_of_even_of_sz {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ b₁ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀) (hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1))
    (hb₁ : Odd b₁) (hZ1 : t.Zv 1 ≤ t.Gv (1 + b₁)) :
    ⁅t.Zv 1, t.Zv (1 + b₁)⁆ ≤ t.Zv 1 ⊓ t.Zv (1 + b₁) := by
  by_contra hna
  exact t.r4k_not_le_centralizer hfr hb₁ hZ1 hna
    (t.L1_le_centralizer_Zv_zero_of_even hfr hb₀ hZ0 hZ0')

theorem commutator_Zv_zero_eq_bot_of_even {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀) (hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1)) {h : ℤ}
    (hZh : t.Zv h ≤ t.Gv 0) : ⁅t.Zv 0, t.Zv h⁆ = ⊥ := by
  have hL := t.L1_le_centralizer_Zv_zero_of_even hfr hb₀ hZ0 hZ0'
  have hQ : Q1 L1 L2 S ≤ centralizer (t.Zv 0 : Set G) := by
    rw [← t.Qv_zero]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0)
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  obtain ⟨j, hj⟩ := t.isPGroup_Zv h ⟨z, hz⟩
  have hz1 : z ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hzP : z ∈ P1 L1 L2 S := by
    rw [← t.Gv_zero]
    exact hZh hz
  exact sup_le hL hQ (t.r4k_mem_of_pow_eq_one hfr hzP hz1)

include t in
theorem mem_L1_sup_Q1_of_pow_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {x : G} (hx : x ∈ P1 L1 L2 S) {j : ℕ} (hxj : x ^ 2 ^ j = 1) :
    x ∈ L1 ⊔ Q1 L1 L2 S := by
  exact t.r4k_mem_of_pow_eq_one hfr hx hxj

theorem L1_le_centralizer_Zv_zero_of_relIndex_lt {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hrel : (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) < 2 ^ (4 * (2 * a + 1))) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  exact t.r4k_le_centralizer hfr hrel

theorem L1_le_centralizer_of_sz {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {Y C : Subgroup G} (hYS : Y ≤ S)
    (hYD : t.D1 ≤ normalizer (Y : Set G)) (hYQ : ¬ Y ≤ t.Qv 0) (hCZ : C ≤ t.Zv 0)
    (hY : Y ≤ centralizer (C : Set G))
    (hY' : Y.map (MulAut.conj t.x₁).toMonoidHom ≤ centralizer (C : Set G)) :
    L1 ≤ centralizer (C : Set G) := by
  have hQ0 : t.Qv 0 ≤ centralizer (C : Set G) := by
    intro q hq
    rw [mem_centralizer_iff]
    intro g hg
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 0 (hCZ hg)) q hq).symm
  have hKI := t.r4k_KI hfr hYS hYD hYQ
  have hYQ' : Y ⊔ t.Qv 0 ≤ centralizer (C : Set G) := sup_le hY hQ0
  have hcenl : pCoreOf 2 L1 ≤ centralizer (C : Set G) :=
    (t.r4k_pCoreOf_le_Qv_zero hfr.hF.1).trans hQ0
  have hx₁N : t.x₁ ∈ normalizer (pCoreOf 2 L1 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L1 (t.r4k_x₁_mem_normalizer_L1 hfr.hF.1)
  have h1 : ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 →
      x ∈ centralizer (C : Set G) ⊔ pCoreOf 2 L1 :=
    fun x hx hx2 => mem_sup_left (hYQ' (hKI x hx hx2))
  have h2 : ∀ x ∈ (S ⊓ L1).map (MulAut.conj t.x₁).toMonoidHom, x * x ∈ pCoreOf 2 L1 →
      x ∈ centralizer (C : Set G) ⊔ pCoreOf 2 L1 := by
    intro x hx hx2
    rw [mem_map_conj_iff] at hx
    have hy2 : (t.x₁⁻¹ * x * t.x₁) * (t.x₁⁻¹ * x * t.x₁) ∈ pCoreOf 2 L1 := by
      have e : (t.x₁⁻¹ * x * t.x₁) * (t.x₁⁻¹ * x * t.x₁) = t.x₁⁻¹ * (x * x) * t.x₁ := by group
      have h := r4b_conj_mem (inv_mem hx₁N) hx2
      rwa [inv_inv, ← e] at h
    have hy := hKI _ hx hy2
    have hxm : x ∈ (Y ⊔ t.Qv 0).map (MulAut.conj t.x₁).toMonoidHom := by
      rw [mem_map_conj_iff]
      exact hy
    rw [Subgroup.map_sup, t.r4e_map_Qv_x₁, neg_zero] at hxm
    exact mem_sup_left ((sup_le hY' hQ0) hxm)
  exact (t.r4k_L1_le_sup hfr h1 h2).trans (sup_le le_rfl hcenl)

theorem natural_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b₀ : ℕ} (hb₀ : Even b₀)
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀)) (hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀))
    (hC0 : t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥) :
    Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f ∧
      Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f ∧
      (∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 1 ⊓ centralizer (S : Set G)) ∧
      (∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z →
        z ∈ t.Zv 1 ⊓ centralizer (S : Set G)) ∧
      (∀ z ∈ t.Zv 1 ⊓ centralizer (S : Set G), z ≠ 1 →
        ∀ z' ∈ t.Zv 1 ⊓ centralizer (S : Set G), z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') := by
  have hC : ¬ L2 ≤ centralizer (t.Zv 1 : Set G) := fun h => t.Zv_ne_bot hfr.hF 1 <| by
    rw [← hC0, eq_comm, inf_eq_left]
    intro z hz
    exact mem_centralizer_iff.mpr fun l hl => (mem_centralizer_iff.mp (h hl) z hz).symm
  obtain ⟨α, hα, hker, hnat⟩ := t.exists_isNatSecOf_Zv_one hfr hb₀ hZ0 hZ0' hC
  rw [hC0] at hnat
  exact t.natural_Zv_one_of_isNatSecOf hfr hα hker hnat

end Track

end CFSG.Quasithin.Stroth.Rq
