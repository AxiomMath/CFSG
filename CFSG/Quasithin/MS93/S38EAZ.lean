module

public import CFSG.Quasithin.MS93.S38EFFHyp
public import CFSG.Quasithin.MS93.S38OffHat
public import CFSG.Quasithin.MS93.S38OffVI

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S38E
  CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

section Gen

theorem exists_pow_two_pow_invol {H : Type*} [Group H] {x : H} (hx : x ≠ 1) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : ∃ j : ℕ, x ^ 2 ^ j ≠ 1 ∧ x ^ 2 ^ j * x ^ 2 ^ j = 1 := by
  classical
  have hex : ∃ j, x ^ 2 ^ j = 1 := ⟨k, hk⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀1 : j₀ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj₀, h0, pow_zero, pow_one] at this
    exact hx this
  refine ⟨j₀ - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_add, ← two_mul, ← pow_succ', show j₀ - 1 + 1 = j₀ by omega]
  exact Nat.find_spec hex

theorem card_mul_card_le_of_inf_eq_bot {Y : Type*} [CommGroup Y] [Finite Y] {A B : Subgroup Y}
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card Y := by
  let f : ↥A × ↥B → Y := fun p => (p.1 : Y) * p.2
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : Y) * b = a' * b' := hab
    have h2 : (a' : Y)⁻¹ * a = b' * (b : Y)⁻¹ :=
      calc (a' : Y)⁻¹ * a = (a' : Y)⁻¹ * (a * b * (b : Y)⁻¹) := by rw [mul_inv_cancel_right]
        _ = (a' : Y)⁻¹ * (a' * b' * (b : Y)⁻¹) := by rw [h1]
        _ = b' * (b : Y)⁻¹ := by group
    have hA : (a' : Y)⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸
      B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hA
    have hB : b = b' := by
      apply Subtype.ext
      rw [← hA] at h1
      exact mul_left_cancel h1
    rw [show a = a' from Subtype.ext hA.symm, hB]
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h1

end Gen

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section NoTransv

theorem four_le_relIndex_of_a6Data (h : PUHyp M T L) (D : OffVI.A6Data M T L) {t : G}
    (htT : t ∈ T) (htO : t ∉ pCoreOf 2 M) :
    4 ≤ (Uq M T L ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) := by
  have htM : t ∈ M := h.le htT
  set r := OffVI.psi D h with hr
  set σ := OffVI.homOf r t with hσ
  have hσ1 : σ ≠ 1 := fun h1 => htO ((OffVI.psi_eq_one_iff h htT).mp h1)
  obtain ⟨k, hk⟩ := h.isPGroup ⟨t, htT⟩
  have hσk : σ ^ 2 ^ k = 1 := by
    rw [hσ, ← OffVI.homOf_pow htM]
    have : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, OffVI.homOf_one]
  obtain ⟨j, hj1, hj2⟩ := exists_pow_two_pow_invol hσ1 hσk
  set t' := t ^ 2 ^ j with ht'
  have ht'M : t' ∈ M := M.pow_mem htM _
  have hσ' : OffVI.homOf r t' = σ ^ 2 ^ j := OffVI.homOf_pow htM _
  set σ' := σ ^ 2 ^ j with hσ'def
  have hsign : Equiv.Perm.sign σ = 1 := OffVI.sign_psi h htM
  have hP : IsPGroup 2 ↥(Subgroup.zpowers σ') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hj2) hj1
  have hPA : ∀ x ∈ Subgroup.zpowers σ', Equiv.Perm.sign x = 1 := by
    rintro _ ⟨n, rfl⟩
    rw [map_zpow, map_pow, hsign, one_pow, one_zpow]
  have hfix := A6F.card_fix_of_mem hP hPA (Subgroup.mem_zpowers σ') hj2 hj1
  have hcK : Nat.card (OffVI.fixSub σ') = 4 := by rw [OffVI.card_fixSub, hfix]
  have hpre := OffVI.relIndex_preU D.surj (OffVI.fixSub σ')
  rw [hcK] at hpre
  have hpre4 : (OffVI.preU D.β₀ (OffVI.fixSub σ')).relIndex (Uq M T L) = 4 := by omega
  have hle : Uq M T L ⊓ Subgroup.centralizer ({t} : Set G) ≤
      OffVI.preU D.β₀ (OffVI.fixSub σ') := by
    rintro u ⟨hu, hut⟩
    rw [OffVI.mem_preU]
    refine ⟨hu, ?_⟩
    rw [OffVI.mem_fixSub, toAdd_ofAdd]
    have htu : t * u = u * t := Subgroup.mem_centralizer_iff.mp hut t rfl
    have ht'u : t' * u * t'⁻¹ = u := by
      have : Commute t u := htu
      rw [ht', (this.pow_left (2 ^ j)).eq, mul_inv_cancel_right]
    have h1 := OffVI.psi_spec (D := D) h ht'M hu
    rw [ht'u, hσ'] at h1
    exact h1.symm
  rw [← hpre4]
  exact Subgroup.relIndex_le_of_le_left hle (Subgroup.index_ne_zero_of_finite)

theorem conj_mem_center {X : Type*} [Group X] {H : Subgroup X} {y : X}
    (hy : y ∈ Subgroup.normalizer (H : Set X)) {c : ↥H} (hc : c ∈ Subgroup.center ↥H) :
    (⟨y * c * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy c).mp c.2⟩ : ↥H) ∈
      Subgroup.center ↥H := by
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have hk : y⁻¹ * (k : X) * y ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) k).mp k.2
    simpa using this
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨_, hk⟩)
  simp only [Subgroup.coe_mul] at h1
  calc (k : X) * (y * c * y⁻¹) = y * ((y⁻¹ * k * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
    _ = y * c * y⁻¹ * k := by group

theorem four_le_relIndex_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L) {t : G}
    (htT : t ∈ T) (htO : t ∉ pCoreOf 2 M) :
    4 ≤ (Uq M T L ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) := by
  classical
  obtain ⟨-, -, hU, h6⟩ := hX
  have hH := S38H.HatMod.of_tripleA6Six IntMod.sq_eq_one h6
  have : Finite (IntMod (Uq M T L) hU) := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have htN : t ∈ Subgroup.normalizer (Uq M T L : Set G) := S38H.le_normalizer_Uq_T h htT
  set x := convI hU ⟨t, htN⟩ with hx
  have hx1 : x ≠ 1 := fun h1 =>
    htO (S38H.mem_pCoreOf_of_mem_centralizer h htT ((convI_eq_one_iff hU _).mp h1))
  have hxN : x ∈ Subgroup.normalizer (autI hU L : Set (MulAut (IntMod (Uq M T L) hU))) :=
    S38H.autI_le_normalizer hU h.le_normalizer h.le (convI_mem_autI hU htT htN)
  have hAN : Subgroup.zpowers t ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (Subgroup.zpowers_le).mpr htN
  set E := autI hU (Subgroup.zpowers t) with hE
  have hxE : x ∈ E := convI_mem_autI hU (Subgroup.mem_zpowers t) htN
  have hEpow : ∀ b ∈ E, ∃ n : ℤ, b = x ^ n := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hb
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨n, ?_⟩
    rw [hx, ← map_zpow]
    congr 1
    apply Subtype.ext
    rw [← hn]
    rfl
  have hE1 : E ≠ ⊥ := fun hb => hx1 (by rw [hb] at hxE; exact (Subgroup.mem_bot).mp hxE)
  have hz1 : (zH : MulAut (IntMod (Uq M T L) hU)) ≠ 1 := by
    intro h1
    have hall : ∀ v : IntMod (Uq M T L) hU, v = 1 := fun v => hfp v (by rw [h1]; rfl)
    have hc1 : Nat.card (IntMod (Uq M T L) hU) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    rw [hH.card] at hc1
    norm_num at hc1
  have hord : orderOf (zH : MulAut (IntMod (Uq M T L) hU)) = 3 :=
    orderOf_eq_prime h3 hz1
  have hzc : zH ∈ Subgroup.center ↥(autI hU L) := hcen ▸ Subgroup.mem_zpowers zH
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcen ▸ conj_mem_center hxN hzc)
  have hconj : x * zH * x⁻¹ = (zH : MulAut (IntMod (Uq M T L) hU)) ^ (n % 3) := by
    have h1 := congrArg Subtype.val hn
    simp only [Subgroup.coe_zpow] at h1
    rw [← h1, ← zpow_mod_orderOf, hord]
    rfl
  have hfix16 : Nat.card (fixV E) ≤ 16 := by
    have hn3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hn3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hconj
      apply hz1
      have : x * (zH : MulAut (IntMod (Uq M T L) hU)) = x := mul_inv_eq_one.mp hconj
      exact mul_eq_left.mp this
    ·
      rw [h1, zpow_one] at hconj
      have hxz : x * zH = zH * x := mul_inv_eq_iff_eq_mul.mp hconj
      refine hH.card_fixV_le h3 hfp (fun b hb => ?_) hE1
      obtain ⟨m, rfl⟩ := hEpow b hb
      exact (Commute.zpow_left hxz m).eq
    ·
      rw [h2] at hconj
      have hxz : x * zH = (zH : MulAut (IntMod (Uq M T L) hU)) ^ (2 : ℤ) * x :=
        mul_inv_eq_iff_eq_mul.mp hconj
      set C : Subgroup (IntMod (Uq M T L) hU) := fixV E
      have hCx : ∀ v ∈ C, x v = v := fun v hv => hv x hxE
      have hinf : C ⊓ C.map (zH : MulAut (IntMod (Uq M T L) hU)).toMonoidHom = ⊥ := by
        rw [eq_bot_iff]
        rintro c ⟨hc, d, hd, rfl⟩
        rw [Subgroup.mem_bot]
        have h1 : x ((zH : MulAut _) d) = (zH : MulAut _) d := hCx _ hc
        have h2 : x ((zH : MulAut _) d) = ((zH : MulAut _) ^ (2 : ℤ)) d := by
          have := congrArg (fun y : MulAut (IntMod (Uq M T L) hU) => y d) hxz
          simp only [MulAut.mul_apply] at this
          rw [this, hCx d hd]
        rw [h1] at h2
        have h3' : (zH : MulAut (IntMod (Uq M T L) hU)) ((zH : MulAut _) d) =
            (zH : MulAut _) d := by
          have e : ((zH : MulAut (IntMod (Uq M T L) hU)) ^ (2 : ℤ)) d =
              (zH : MulAut _) ((zH : MulAut _) d) := by
            rw [zpow_two, MulAut.mul_apply]
          rw [← e, ← h2]
        have h4 := hfp _ h3'
        show (MulEquiv.toMonoidHom (zH : MulAut _)) d = 1
        exact h4
      have hcard := card_mul_card_le_of_inf_eq_bot hinf
      rw [Subgroup.card_map_of_injective (zH : MulAut (IntMod (Uq M T L) hU)).injective,
        hH.card] at hcard
      by_contra hlt
      push Not at hlt
      nlinarith
  have hC := card_fixV_autI hU hAN
  rw [show Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
    Subgroup.centralizer ({t} : Set G) by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]] at hC
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer ({t} : Set G)) (Uq M T L)
  have hU64 : Nat.card ↥(Uq M T L) = 64 := by
    have := hH.card
    rw [show Nat.card (IntMod (Uq M T L) hU) = Nat.card ↥(Uq M T L) from rfl] at this
    rw [this]
    norm_num
  rw [inf_comm, ← hC, hU64] at hmul
  rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [← hE] at hmul
  by_contra hlt
  push Not at hlt
  have : (Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) * Nat.card (fixV E) ≤ 3 * 16 :=
    Nat.mul_le_mul (by omega) hfix16
  omega

theorem four_le_relIndex (h : PUHyp M T L)
    (hcase : IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (hnSp4 : ¬ IsSp4U M T L) {t : G} (htT : t ∈ T) (htO : t ∉ pCoreOf 2 M) :
    4 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Uq M T L) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, ← Subgroup.inf_relIndex_right,
    inf_comm]
  rcases hcase with hX | hX
  · exact four_le_relIndex_of_isHatA6U h hX htT htO
  · obtain ⟨D⟩ := OffVI.PUHyp.nonempty_a6Data h hX hnSp4
    exact four_le_relIndex_of_a6Data h D htT htO

end NoTransv

section Comm

variable {X : Type*} [Group X]

theorem relIndex_le_card_commutator {U : Subgroup X} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    {t : X} (htN : t ∈ Subgroup.normalizer (U : Set X)) [Finite ↥U] :
    (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup X) : Set X)).relIndex U ≤
      Nat.card ↥⁅U, Subgroup.zpowers t⁆ := by
  have hconj : ∀ u ∈ U, t * u⁻¹ * t⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp htN _).mp (U.inv_mem hu)
  have hmemU : ∀ u ∈ U, ⁅u, t⁆ ∈ U := fun u hu => by
    rw [show ⁅u, t⁆ = u * (t * u⁻¹ * t⁻¹) by rw [commutatorElement_def]; group]
    exact U.mul_mem hu (hconj u hu)
  have hle : ⁅U, Subgroup.zpowers t⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu g hg
    have hgN : g ∈ Subgroup.normalizer (U : Set X) := (Subgroup.zpowers_le.mpr htN) hg
    rw [show ⁅u, g⁆ = u * (g * u⁻¹ * g⁻¹) by rw [commutatorElement_def]; group]
    exact U.mul_mem hu ((Subgroup.mem_normalizer_iff.mp hgN _).mp (U.inv_mem hu))
  have : Finite ↥⁅U, Subgroup.zpowers t⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hC : ∀ x : X, x ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup X) : Set X) ↔
      ⁅x, t⁆ = 1 := by
    intro x
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]
  let φ : ↥U →* ↥⁅U, Subgroup.zpowers t⁆ :=
    { toFun := fun u => ⟨⁅(u : X), t⁆, Subgroup.commutator_mem_commutator u.2
        (Subgroup.mem_zpowers t)⟩
      map_one' := Subtype.ext (commutatorElement_one_left t)
      map_mul' := fun u v => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have e : ⁅(u : X) * v, t⁆ = u * ⁅(v : X), t⁆ * (t * (u : X)⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, mul_assoc, hU _ (hmemU _ v.2) _ (hconj _ u.2), ← mul_assoc]
        congr 1
        rw [commutatorElement_def]
        group }
  have hker : φ.ker = (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup X) : Set X)).subgroupOf
      U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hC]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact Subgroup.card_le_card_group _

end Comm

end CFSG.Quasithin.MS93.S38EA
