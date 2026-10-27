module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HLin
public import CFSG.RankThree.GF2n.Stroth80.Sec83Vec
public import CFSG.RankThree.GF2n.Stroth80.Sec83Count

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Cnt

variable {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
  {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}

theorem sec8_card_LB (hpts : Sec8Pts hc t r m K φ u u') (ht : t ∈ LB M Q B) :
    Nat.card ↥(LB M Q B) * Nat.card Z = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (2 * m) := by
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have h1 := card_inf_mul_card_map hLR φ hpts.ker
  rw [hpts.hL, card_LspGL hpts.u_ne_zero, hpts.card] at h1
  have hm := hpts.two_le
  have e : Nat.card Z ^ (2 * m) = Nat.card Z ^ (2 * m - 1) * Nat.card Z := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e, ← h1]
  ring

theorem sec8_card_isotropic_sub (hpts : Sec8Pts hc t r m K φ u u')
    (ht : t ∈ LB M Q B) {S : Subgroup G} (hSL : S ≤ LB M Q B)
    (hS : ∀ (l : G) (hl : l ∈ S) (y : Fin m ⊕ Fin m → K),
      spForm m K y ((φ ⟨l, le_Rt (M := M) (LB M Q B) ht (hSL hl)⟩ :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = 0) :
    Nat.card ↥S * Nat.card Z ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ m := by
  haveI := hpts.charP
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hSR : S ≤ Rt M (LB M Q B) t := hSL.trans hLR
  have h1 := card_inf_mul_card_map hSR φ hpts.ker
  have hP : (S.subgroupOf (Rt M (LB M Q B) t)).map φ ≤ LspGL m K u := by
    rw [← hpts.hL]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hSL (Subgroup.mem_subgroupOf.mp hx)))
  have hno : ∀ A ∈ (S.subgroupOf (Rt M (LB M Q B) t)).map φ, ∀ y : Fin m ⊕ Fin m → K,
      spForm m K y ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = 0 := by
    rintro A ⟨x, hx, rfl⟩ y
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have := hS (x : G) hxS y
    simpa using this
  have h2 := card_le_of_forall_isotropic_LspGL hpts.u_ne_zero hpts.two_le _ hP hno
  rw [← h1]
  have hle : Nat.card ↥(S ⊓ hc.CN t) ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) :=
    Subgroup.card_le_of_le (inf_le_inf hSL le_rfl)
  rw [← hpts.card]
  have hm := hpts.two_le
  have e : m = (m - 1) + 1 := by omega
  calc Nat.card ↥(S ⊓ hc.CN t) * Nat.card ↥((S.subgroupOf (Rt M (LB M Q B) t)).map φ) *
        Nat.card K ≤ Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card K ^ (m - 1) * Nat.card K :=
        Nat.mul_le_mul (Nat.mul_le_mul hle h2) le_rfl
    _ = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card K ^ m := by
        conv_rhs => rw [e, pow_succ]
        ring

end Cnt

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_card_index {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hpts : Sec8Pts hc t r m K φ u u') (ht : t ∈ LB M Q B)
    (κ : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative (Fin m ⊕ Fin m → K))
    (hκ : @IsSecMod G _ (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (Fin m ⊕ Fin m → K) _
      hpts.vecAct κ)
    {D : Subgroup G} (hZD : Z ≤ D) (hDV : D ≤ Vt M (LB M Q B) B Z t)
    (hDK : ∀ (c : K) (d : ↥(Vt M (LB M Q B) B Z t)), (d : G) ∈ D →
      ∃ d' : ↥(Vt M (LB M Q B) B Z t), (d' : G) ∈ D ∧
        Multiplicative.toAdd (κ d') = c • Multiplicative.toAdd (κ d))
    (huD : ∃ d : ↥(Vt M (LB M Q B) B Z t), (d : G) ∈ D ∧ Multiplicative.toAdd (κ d) = u)
    (hDu : ∀ d : ↥(Vt M (LB M Q B) B Z t), (d : G) ∈ D →
      spForm m K u (Multiplicative.toAdd (κ d)) = 0)
    {S : Subgroup G} (hSL : S ≤ LB M Q B)
    (hS : ∀ l ∈ LB M Q B, l ∈ S ↔ ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, l⁆ ∈ D) :
    Nat.card ↥(LB M Q B) * Nat.card ↥D ≤ Nat.card ↥S * Nat.card Z ^ (2 * m) := by
  letI := hpts.vecAct
  have hconj : ∀ (s : ↥(Rt M (LB M Q B) t)) (v : ↥(Vt M (LB M Q B) B Z t)),
      (s : G) * (v : G) * (s : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := fun s v =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht s.2) (v : G)).mp v.2
  have hact : ∀ (s : ↥(Rt M (LB M Q B) t)) (v : ↥(Vt M (LB M Q B) B Z t)),
      (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ Multiplicative.toAdd (κ v) =
        Multiplicative.toAdd (κ ⟨(s : G) * (v : G) * (s : G)⁻¹, hconj s v⟩) := by
    intro s v
    have h := hκ.act s v ⟨(s : G) * (v : G) * (s : G)⁻¹, hconj s v⟩ rfl
    rw [h, toAdd_ofAdd]
    rfl
  have hsub : ∀ (s : ↥(Rt M (LB M Q B) t)) (v : ↥(Vt M (LB M Q B) B Z t)),
      ∃ c : ↥(Vt M (LB M Q B) B Z t), (c : G) = (s : G) * (v : G) * (s : G)⁻¹ * (v : G)⁻¹ ∧
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ Multiplicative.toAdd (κ v) -
          Multiplicative.toAdd (κ v) = Multiplicative.toAdd (κ c) := by
    intro s v
    have hw : (s : G) * (v : G) * (s : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := hconj s v
    refine ⟨(⟨(s : G) * (v : G) * (s : G)⁻¹, hw⟩ : ↥(Vt M (LB M Q B) B Z t)) * v⁻¹, rfl, ?_⟩
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hact s v, sub_eq_add_neg]
  obtain ⟨D'', hD''⟩ : ∃ D'' : Submodule K (Fin m ⊕ Fin m → K),
      ∀ a : Fin m ⊕ Fin m → K, a ∈ D'' ↔ a ∈ secSub κ D := by
    refine ⟨{ carrier := {a | a ∈ secSub κ D}
              add_mem' := fun ha hb => (secSub κ D).add_mem ha hb
              zero_mem' := (secSub κ D).zero_mem
              smul_mem' := fun c a ha => ?_ }, fun a => Iff.rfl⟩
    show c • a ∈ secSub κ D
    have ha' : a ∈ secSub κ D := ha
    obtain ⟨x, hxD, hxa⟩ := mem_secSub.mp ha'
    obtain ⟨d, hdD, hdc⟩ := hDK c x hxD
    refine mem_secSub.mpr ⟨d, hdD, ?_⟩
    have h2 : Multiplicative.toAdd (κ x) = a := by rw [hxa, toAdd_ofAdd]
    apply Multiplicative.toAdd.injective
    rw [hdc, toAdd_ofAdd, h2]
  have hD''mem : ∀ a : Fin m ⊕ Fin m → K, a ∈ D'' ↔
      ∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ D ∧ κ w = Multiplicative.ofAdd a :=
    fun a => (hD'' a).trans mem_secSub
  have hu_mem : u ∈ D'' := by
    obtain ⟨d, hdD, hdu⟩ := huD
    refine (hD''mem u).mpr ⟨d, hdD, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hdu, toAdd_ofAdd]
  have hD''perp : ∀ d ∈ D'', spForm m K u d = 0 := by
    intro d hd
    obtain ⟨x, hxD, hxd⟩ := (hD''mem d).mp hd
    have h2 : Multiplicative.toAdd (κ x) = d := by rw [hxd, toAdd_ofAdd]
    rw [← h2]
    exact hDu x hxD
  have hS'' : ∀ A : GL (Fin m ⊕ Fin m) K,
      A ∈ (S.subgroupOf (Rt M (LB M Q B) t)).map φ ↔
        A ∈ LspGL m K u ∧ ∀ x : Fin m ⊕ Fin m → K,
          (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x ∈ D'' := by
    intro A
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hsL : (s : G) ∈ LB M Q B := hSL hsS
      have hmemD : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, (s : G)⁆ ∈ D := (hS _ hsL).mp hsS
      refine ⟨?_, fun x => ?_⟩
      · rw [← hpts.hL]
        exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hsL)
      · obtain ⟨v, hv⟩ := hκ.surj (Multiplicative.ofAdd x)
        have hx : x = Multiplicative.toAdd (κ v) := by rw [hv, toAdd_ofAdd]
        subst hx
        obtain ⟨c, hcG, hcact⟩ := hsub s v
        rw [hcact, hD''mem]
        refine ⟨c, ?_, (ofAdd_toAdd (κ c)).symm⟩
        have e : (s : G) * (v : G) * (s : G)⁻¹ * (v : G)⁻¹ = (⁅(v : G), (s : G)⁆)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [hcG, e]
        exact D.inv_mem (hmemD _ v.2)
    · rintro ⟨hAL, hA⟩
      rw [← hpts.hL] at hAL
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hAL
      have hsL : (s : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hs
      refine Subgroup.mem_map.mpr
        ⟨s, Subgroup.mem_subgroupOf.mpr ((hS _ hsL).mpr fun v hv => ?_), rfl⟩
      obtain ⟨w, hwD, hwκ⟩ := (hD''mem _).mp (hA (Multiplicative.toAdd (κ ⟨v, hv⟩)))
      obtain ⟨c, hcG, hcact⟩ := hsub s ⟨v, hv⟩
      rw [hcact] at hwκ
      have hwc : κ w = κ c := by rw [hwκ, ofAdd_toAdd]
      have hZ : (w : G) * (c : G)⁻¹ ∈ Z := (hκ.eq_iff w c).mp hwc
      have hcD : (c : G) ∈ D := by
        have h1 : ((w : G) * (c : G)⁻¹)⁻¹ * (w : G) ∈ D :=
          D.mul_mem (D.inv_mem (hZD hZ)) hwD
        have e : ((w : G) * (c : G)⁻¹)⁻¹ * (w : G) = (c : G) := by group
        rwa [e] at h1
      have hcG' : (c : G) = (s : G) * v * (s : G)⁻¹ * v⁻¹ := hcG
      have e : (c : G) = (⁅v, (s : G)⁆)⁻¹ := by
        rw [hcG']
        simp only [commutatorElement_def]
        group
      rw [e] at hcD
      have h3 := D.inv_mem hcD
      rwa [inv_inv] at h3
  have hDD : Nat.card ↥D'' * Nat.card Z = Nat.card ↥D := by
    have e : Nat.card ↥D'' = Nat.card ↥(secSub κ D) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun a => hD'' a)
    rw [e]
    exact natCard_secSub_mul (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t) hκ hZD hDV
  have hLNS : LB M Q B ⊓ hc.CN t ≤ S := by
    intro n hn
    obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.mp hn
    have hnV := (Ctx.mem_CN.mp hnN).2
    refine (hS n hnL).mpr fun v hv => ?_
    have h1 : ⁅v, n⁆ ∈ Z := by
      have e : ⁅v, n⁆ = (⁅n, v⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Z.inv_mem (hnV v hv)
    exact hZD h1
  have hle1 : Nat.card ↥(LB M Q B ⊓ hc.CN t) ≤ Nat.card ↥(S ⊓ hc.CN t) :=
    Subgroup.card_le_of_le (le_inf hLNS inf_le_right)
  have hSR : S ≤ Rt M (LB M Q B) t := hSL.trans (le_Rt (M := M) (LB M Q B) ht)
  have hSS := card_inf_mul_card_map hSR φ hpts.ker
  have hD''S := card_le_card_of_LspGL_move hpts.u_ne_zero D'' hu_mem hD''perp
    ((S.subgroupOf (Rt M (LB M Q B) t)).map φ) hS''
  have hL := sec8_card_LB hpts ht
  calc Nat.card ↥(LB M Q B) * Nat.card ↥D
      = Nat.card ↥(LB M Q B) * Nat.card Z * Nat.card ↥D'' := by rw [← hDD]; ring
    _ = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (2 * m) * Nat.card ↥D'' := by rw [hL]
    _ ≤ Nat.card ↥(S ⊓ hc.CN t) * Nat.card Z ^ (2 * m) *
          Nat.card ↥((S.subgroupOf (Rt M (LB M Q B) t)).map φ) :=
        Nat.mul_le_mul (Nat.mul_le_mul hle1 le_rfl) hD''S
    _ = Nat.card ↥S * Nat.card Z ^ (2 * m) := by rw [← hSS]; ring

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_card_comm_smul_sub {R P I : Subgroup G} {Md : Type} [AddCommGroup Md]
    [DistribMulAction ↥R Md] {κ : ↥P →* Multiplicative Md} (hκ : IsSecMod R P I Md κ)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (l : ↥R) (x : ↥P) (hc : ⁅(l : G), (x : G)⁆ ∈ P) :
    l • Multiplicative.toAdd (κ x) - Multiplicative.toAdd (κ x) =
      Multiplicative.toAdd (κ ⟨⁅(l : G), (x : G)⁆, hc⟩) := by
  have h1 := hκ.act l x ⟨(l : G) * x * (l : G)⁻¹, hP l l.2 x x.2⟩ rfl
  have h2 : (⟨(l : G) * x * (l : G)⁻¹, hP l l.2 x x.2⟩ : ↥P) = ⟨⁅(l : G), (x : G)⁆, hc⟩ * x :=
    Subtype.ext (by simp [commutatorElement_def])
  rw [h2, map_mul] at h1
  have h3 : Multiplicative.toAdd (κ ⟨⁅(l : G), (x : G)⁆, hc⟩ * κ x) =
      l • Multiplicative.toAdd (κ x) := by rw [h1, toAdd_ofAdd]
  rw [toAdd_mul] at h3
  rw [← h3]
  abel

theorem sec8_card_comm {hc : Ctx M Q Z B} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hpts : Sec8Pts hc t r m K φ u u') (ht : t ∈ LB M Q B)
    {D : Subgroup G} (hZD : Z ≤ D) (hDV : D ≤ Vt M (LB M Q B) B Z t)
    (hD : ∀ l ∈ LB M Q B, ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, l⁆ ∈ D) :
    Nat.card Z ^ (2 * m) ≤ Nat.card ↥D := by
  haveI := hpts.charP
  obtain ⟨κ, hκ⟩ := hpts.isSecMod
  letI : DistribMulAction ↥(Rt M (LB M Q B) t) (Fin m ⊕ Fin m → K) := hpts.vecAct
  have hRV : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      r * y * r⁻¹ ∈ Vt M (LB M Q B) B Z t := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hpts.act.1 hr) y).mp hy
  have hD' : ∀ A ∈ LspGL m K u, ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x - x ∈ secSub κ D := by
    intro A hA x
    have hA' : A ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ := by
      rw [hpts.hL]
      exact hA
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hA'
    have hsLB : (s : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨v, hv⟩ := hκ.surj (Multiplicative.ofAdd x)
    have hvx : Multiplicative.toAdd (κ v) = x := by
      rw [hv, toAdd_ofAdd]
    have hsv : ⁅(s : G), (v : G)⁆ ∈ Vt M (LB M Q B) B Z t := by
      rw [commutatorElement_def]
      exact (Vt M (LB M Q B) B Z t).mul_mem (hRV (s : G) s.2 (v : G) v.2)
        ((Vt M (LB M Q B) B Z t).inv_mem v.2)
    have hzD : ⁅(s : G), (v : G)⁆ ∈ D := by
      have e : ⁅(s : G), (v : G)⁆ = (⁅(v : G), (s : G)⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact D.inv_mem (hD (s : G) hsLB (v : G) v.2)
    have hmem : Multiplicative.toAdd (κ ⟨⁅(s : G), (v : G)⁆, hsv⟩) ∈ secSub κ D :=
      (toAdd_mem_secSub_iff hκ hZD _).mpr hzD
    rw [← sec8_card_comm_smul_sub hκ hRV s v hsv, hvx] at hmem
    exact hmem
  have key := card_le_of_comm_mem_LspGL hpts.u_ne_zero (secSub κ D) hD'
  have e1 : Nat.card ↥(secSub κ D) * Nat.card ↥Z = Nat.card ↥D :=
    natCard_secSub_mul (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t) hκ hZD hDV
  have hm := hpts.two_le
  have e2 : Nat.card Z ^ (2 * m) = Nat.card Z ^ (2 * m - 1) * Nat.card Z := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpts.card] at key
  calc Nat.card Z ^ (2 * m) = Nat.card Z ^ (2 * m - 1) * Nat.card Z := e2
    _ ≤ Nat.card ↥(secSub κ D) * Nat.card Z := Nat.mul_le_mul key le_rfl
    _ = Nat.card ↥D := e1

end

end

section

theorem sec8_caseB_arith {m a b c d q : ℕ} (hq : 2 ≤ q) (ha : 0 < a)
    (hL : b * q = a * q ^ (2 * m)) (hS : c * q ≤ a * q ^ m)
    (hidx : b * d ≤ c * q ^ (2 * m)) (hD : q ^ (m + 1) ≤ d) : False := by
  have hqpos : 0 < q := by omega
  have h1 : b * q ^ (m + 1) ≤ c * q ^ (2 * m) := le_trans (Nat.mul_le_mul_left b hD) hidx
  have h2 : b * q * q ^ (m + 1) ≤ c * q * q ^ (2 * m) := by
    calc b * q * q ^ (m + 1) = (b * q ^ (m + 1)) * q := by ring
      _ ≤ (c * q ^ (2 * m)) * q := Nat.mul_le_mul_right q h1
      _ = c * q * q ^ (2 * m) := by ring
  have h3 : c * q * q ^ (2 * m) ≤ a * q ^ m * q ^ (2 * m) := Nat.mul_le_mul_right _ hS
  rw [hL] at h2
  have h4 : a * q ^ (2 * m) * q ^ (m + 1) ≤ a * q ^ m * q ^ (2 * m) := le_trans h2 h3
  have e1 : a * q ^ (2 * m) * q ^ (m + 1) = a * q ^ (2 * m) * q ^ m * q := by ring
  have e2 : a * q ^ m * q ^ (2 * m) = a * q ^ (2 * m) * q ^ m := by ring
  rw [e1, e2] at h4
  have hpos : 0 < a * q ^ (2 * m) * q ^ m := by positivity
  have h5 : q ≤ 1 := by
    by_contra h
    push Not at h
    have : a * q ^ (2 * m) * q ^ m * 1 < a * q ^ (2 * m) * q ^ m * q :=
      Nat.mul_lt_mul_of_pos_left h hpos
    omega
  omega

end

end CFSG.RankThree.GF2n.Stroth80
