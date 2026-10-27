module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Red2a
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

private theorem piKT614_conj_apply_b {Γ : Type} [Group Γ] {K T : Subgroup Γ}
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) {k e : Γ} (hk : k ∈ K ⊔ T) (he : e ∈ K ⊔ T)
    (hke : k * e * k⁻¹ ∈ K ⊔ T) :
    (MulAut.conj (piKT614 hTK ⟨k, hk⟩)).toMonoidHom (piKT614 hTK ⟨e, he⟩) =
      piKT614 hTK ⟨k * e * k⁻¹, hke⟩ := by
  have e3 : (⟨k * e * k⁻¹, hke⟩ : ↥(K ⊔ T)) =
      (⟨k, hk⟩ : ↥(K ⊔ T)) * (⟨e, he⟩ : ↥(K ⊔ T)) * (⟨k, hk⟩ : ↥(K ⊔ T))⁻¹ := rfl
  rw [e3, map_mul, map_mul, map_inv] <;> rfl

private theorem mem_of_piKT614_mem_of_mem_X614_b {Γ : Type} [Group Γ] [Finite Γ] {K T : Subgroup Γ}
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hTs : IsSylowTwoOf T (K ⊔ T))
    {X : Subgroup Γ} (hXK : X ≤ K) (hXO : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal)
    (hXN : ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ)) {x : Γ} (hx : x ∈ X)
    (hxKT : x ∈ K ⊔ T) (hφ : piKT614 hTK ⟨x, hxKT⟩ ∈ imKT614 hTK T) : x ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, he⟩ := hφ
  have htT : (t : Γ) ∈ T := Subgroup.mem_subgroupOf.mp ht
  obtain ⟨m, hm⟩ := hTs.2.1 ⟨(t : Γ), htT⟩
  have htm : (t : Γ) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hxm : x ^ 2 ^ m ∈ K ⊔ T := (K ⊔ T).pow_mem hxKT _
  have ht1 : t ^ 2 ^ m = 1 := Subtype.ext (by simpa using htm)
  have hπ1 : piKT614 hTK ⟨x ^ 2 ^ m, hxm⟩ = 1 := by
    have e1 : (⟨x ^ 2 ^ m, hxm⟩ : ↥(K ⊔ T)) = (⟨x, hxKT⟩ : ↥(K ⊔ T)) ^ 2 ^ m := rfl
    rw [e1, map_pow, ← he, ← map_pow, ht1, map_one]
  have hxmT : x ^ 2 ^ m ∈ T :=
    mem_of_piKT614_eq_one_of_mem614 hTK hTs hXK hXO hX5 hXn hXN (X.pow_mem hx (2 ^ m)) hxm hπ1
  haveI : ((X ⊓ T).subgroupOf X).Normal := hXn
  have hQ5 : ((X ⊓ T).subgroupOf X).index = 5 := hX5
  have h2m : (QuotientGroup.mk' ((X ⊓ T).subgroupOf X) (⟨x, hx⟩ : ↥X)) ^ 2 ^ m = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨X.pow_mem hx (2 ^ m), hxmT⟩)
  have h5 : (QuotientGroup.mk' ((X ⊓ T).subgroupOf X) (⟨x, hx⟩ : ↥X)) ^ 5 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h := Subgroup.pow_index_mem ((X ⊓ T).subgroupOf X) (⟨x, hx⟩ : ↥X)
    rwa [hQ5] at h
  have hx1 : QuotientGroup.mk' ((X ⊓ T).subgroupOf X) (⟨x, hx⟩ : ↥X) = 1 :=
    eq_one_of_pow_two_of_odd614 h2m h5 ⟨2, by norm_num⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx1)).2

theorem exists_mem_K_conj_le_of_imKT614 {Γ : Type} [Group Γ] [Finite Γ] {K T : Subgroup Γ}
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hTs : IsSylowTwoOf T (K ⊔ T))
    {E : Subgroup Γ} (hE2 : IsPGroup 2 E) (hEKT : E ≤ K ⊔ T) {k₀ : Γ} (hk₀ : k₀ ∈ K)
    (hle : (imKT614 hTK E).map (MulAut.conj (piKT614 hTK ⟨k₀, (le_sup_left : K ≤ K ⊔ T) hk₀⟩)).toMonoidHom
      ≤ imKT614 hTK T) :
    ∃ z ∈ kerAct614 hTK ⊓ K, E.map (MulAut.conj (z * k₀)).toMonoidHom ≤ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk₀KT : k₀ ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) hk₀
  have hCK : kerAct614 hTK ≤ K ⊔ T := kerAct614_le_sup hTK
  have hTC : T ≤ Subgroup.normalizer (kerAct614 hTK : Set Γ) :=
    (le_sup_right : T ≤ K ⊔ T).trans (kerAct614_normal hTK)
  have hFCT : E.map (MulAut.conj k₀).toMonoidHom ≤ kerAct614 hTK ⊔ T := by
    rintro _ ⟨e, he, rfl⟩
    have heKT : e ∈ K ⊔ T := hEKT he
    have hfKT : k₀ * e * k₀⁻¹ ∈ K ⊔ T :=
      (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hk₀KT heKT) ((K ⊔ T).inv_mem hk₀KT)
    have himg := hle (Subgroup.mem_map_of_mem (MulAut.conj (piKT614 hTK ⟨k₀, hk₀KT⟩)).toMonoidHom
      (mem_imKT614 hTK he heKT))
    obtain ⟨s, hs, hse⟩ := himg
    have hsT : (s : Γ) ∈ T := Subgroup.mem_subgroupOf.mp hs
    have hπs : piKT614 hTK ⟨k₀ * e * k₀⁻¹, hfKT⟩ = piKT614 hTK s :=
      (piKT614_conj_apply_b hTK hk₀KT heKT hfKT).symm.trans hse.symm
    have hcKT : k₀ * e * k₀⁻¹ * (s : Γ)⁻¹ ∈ K ⊔ T :=
      (K ⊔ T).mul_mem hfKT ((K ⊔ T).inv_mem s.2)
    have hcC : k₀ * e * k₀⁻¹ * (s : Γ)⁻¹ ∈ kerAct614 hTK := by
      rw [mem_kerAct614 hTK hcKT]
      have e2 : (⟨k₀ * e * k₀⁻¹ * (s : Γ)⁻¹, hcKT⟩ : ↥(K ⊔ T)) =
          (⟨k₀ * e * k₀⁻¹, hfKT⟩ : ↥(K ⊔ T)) * (s : ↥(K ⊔ T))⁻¹ := rfl
      rw [e2, map_mul, map_inv, hπs, mul_inv_cancel]
    have hfeq : k₀ * e * k₀⁻¹ = (k₀ * e * k₀⁻¹ * (s : Γ)⁻¹) * (s : Γ) := by group
    show k₀ * e * k₀⁻¹ ∈ kerAct614 hTK ⊔ T
    rw [hfeq]
    exact (kerAct614 hTK ⊔ T).mul_mem
      ((le_sup_left : kerAct614 hTK ≤ kerAct614 hTK ⊔ T) hcC)
      ((le_sup_right : T ≤ kerAct614 hTK ⊔ T) hsT)
  have hTM : IsSylowTwoOf T (kerAct614 hTK ⊔ T) := by
    refine ⟨le_sup_right, hTs.2.1, fun h2 => hTs.2.2 ?_⟩
    have hrel := Subgroup.relIndex_mul_relIndex T (kerAct614 hTK ⊔ T) (K ⊔ T) le_sup_right
      (sup_le hCK le_sup_right)
    show 2 ∣ T.relIndex (K ⊔ T)
    rw [← hrel]
    exact dvd_mul_of_dvd_left h2 _
  obtain ⟨S₀, hS₀, hFS₀⟩ := EscapingLocal.exists_isSylowTwoOf_ge hFCT (hE2.map _)
  obtain ⟨h, hh, hSh⟩ := hTM.exists_conj hS₀
  have hcoe : ((kerAct614 hTK ⊔ T : Subgroup Γ) : Set Γ) =
      (kerAct614 hTK : Set Γ) * (T : Set Γ) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (kerAct614 hTK) T hTC
  have hh' : h ∈ ((kerAct614 hTK ⊔ T : Subgroup Γ) : Set Γ) := hh
  rw [hcoe] at hh'
  obtain ⟨c, hc, t₁, ht₁, hct⟩ := hh'
  have hcf : ∀ f ∈ E.map (MulAut.conj k₀).toMonoidHom, c⁻¹ * f * c⁻¹⁻¹ ∈ T := by
    intro f hf
    have hfS : f ∈ S₀ := hFS₀ hf
    rw [hSh] at hfS
    obtain ⟨t, ht, rfl⟩ := hfS
    rw [← hct]
    have e3 : c⁻¹ * (MulAut.conj (c * t₁)).toMonoidHom t * c⁻¹⁻¹ = t₁ * t * t₁⁻¹ := by
      show c⁻¹ * (c * t₁ * t * (c * t₁)⁻¹) * c⁻¹⁻¹ = t₁ * t * t₁⁻¹
      group
    rw [e3]
    exact T.mul_mem (T.mul_mem ht₁ ht) (T.inv_mem ht₁)
  obtain ⟨t, ht, z, hz, hcz⟩ := exists_mul_of_mem_kerAct614 hTK hTs ((kerAct614 hTK).inv_mem hc)
  have htT : t ∈ T := (Subgroup.mem_inf.mp ht).2
  refine ⟨z, hz, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have h1 := hcf (k₀ * e * k₀⁻¹) ⟨e, he, rfl⟩
  rw [hcz] at h1
  have h2 : z * (k₀ * e * k₀⁻¹) * z⁻¹ =
      t⁻¹ * (t * z * (k₀ * e * k₀⁻¹) * (t * z)⁻¹) * t := by
    group
  show z * k₀ * e * (z * k₀)⁻¹ ∈ T
  have e5 : z * k₀ * e * (z * k₀)⁻¹ = z * (k₀ * e * k₀⁻¹) * z⁻¹ := by group
  rw [e5, h2]
  exact T.mul_mem (T.mul_mem (T.inv_mem htT) h1) htT

theorem kg614Fusion_conclusion_of_locFusL3 {Γ : Type} [Group Γ] [Finite Γ] {K T : Subgroup Γ}
    (hloc : LocFusL3 (MulAut (ModO2 K)) (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range)
    {X : Subgroup Γ} (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hTs : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hXO : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    (hXN : ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ))
    {E : Subgroup Γ} (hE : E ≤ pCoreOf 2 (X ⊔ T)) (hEa : IsElemAbelian 2 E)
    (hEK : ¬ E ≤ pCoreOf 2 (K ⊔ T)) :
    ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
      ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXKT : X ≤ K ⊔ T := hXK.trans le_sup_left
  have hTKT : T ≤ K ⊔ T := le_sup_right
  have hXTKT : X ⊔ T ≤ K ⊔ T := sup_le hXKT hTKT
  have hOXT : pCoreOf 2 (X ⊔ T) ≤ X ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hO2 : IsPGroup 2 (pCoreOf 2 (X ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hEKT : E ≤ K ⊔ T := (hE.trans hOXT).trans hXTKT
  have hE2 : IsPGroup 2 E := hO2.to_le hE
  have hO' : imKT614 hTK (pCoreOf 2 (X ⊔ T)) ≤
      pCoreOf 2 (imKT614 hTK X ⊔ imKT614 hTK T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · rw [← imKT614_sup hTK hXKT hTKT]
      exact imKT614_mono hTK hOXT
    · rw [← imKT614_sup hTK hXKT hTKT]
      refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (piKT614 hTK))
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ T) hg) h
    · have : IsPGroup 2 ((pCoreOf 2 (X ⊔ T)).subgroupOf (K ⊔ T)) :=
        hO2.of_equiv (Subgroup.subgroupOfEquivOfLe (hOXT.trans hXTKT)).symm
      exact this.map _
  set X' := imKT614 hTK X with hX'def
  set T' := imKT614 hTK T with hT'def
  set E' := imKT614 hTK E with hE'def
  have hTs' := isSylowTwoOf_imKT614' hTK hTs
  have hX'N : X' ≤ (MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range :=
    (imKT614_mono hTK hXK).trans (imKT614_self hTK).le
  set πX := (piKT614 hTK).comp (Subgroup.inclusion hXKT) with hπX
  have hX'eq : X' = (⊤ : Subgroup ↥X).map πX := by
    rw [hX'def, imKT614_eq_map hTK le_rfl hXKT, Subgroup.subgroupOf_self]
  have hXTeq : X' ⊓ T' = ((X ⊓ T).subgroupOf X).map πX := by
    rw [hπX, ← imKT614_eq_map hTK inf_le_left hXKT]
    refine le_antisymm ?_ ?_
    · rintro φ ⟨⟨⟨x, hxKT⟩, hx, rfl⟩, hφT⟩
      exact ⟨⟨x, hxKT⟩, ⟨hx, mem_of_piKT614_mem_of_mem_X614_b hTK hTs hXK hXO hX5 hXn hXN hx
        hxKT hφT⟩, rfl⟩
    · exact le_inf (imKT614_mono hTK inf_le_left) (imKT614_mono hTK inf_le_right)
  have hkerX : πX.ker ≤ (X ⊓ T).subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, mem_of_piKT614_eq_one_of_mem614 hTK hTs hXK hXO hX5 hXn hXN x.2 (hXKT x.2)
      (MonoidHom.mem_ker.mp hx)⟩
  have hX5' : (X' ⊓ T').relIndex X' = 5 := by
    rw [hXTeq, hX'eq, Subgroup.relIndex_map_map, sup_eq_left.mpr hkerX, top_sup_eq,
      Subgroup.relIndex_top_right]
    exact hX5
  have hXn' : ((X' ⊓ T').subgroupOf X').Normal := by
    have hsub : (X' ⊓ T').subgroupOf X' = ((X ⊓ T).subgroupOf X).map
        (πX.codRestrict X' fun x => by rw [hX'eq]; exact ⟨x, Subgroup.mem_top x, rfl⟩) := by
      ext ⟨φ, hφ⟩
      rw [Subgroup.mem_subgroupOf, hXTeq, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, he⟩
        exact ⟨x, hx, Subtype.ext he⟩
      · rintro ⟨x, hx, he⟩
        exact ⟨x, hx, congrArg Subtype.val he⟩
    rw [hsub]
    refine hXn.map _ ?_
    rintro ⟨φ, hφ⟩
    rw [hX'eq] at hφ
    obtain ⟨x, -, rfl⟩ := hφ
    exact ⟨x, rfl⟩
  have hXO' : X' = oTwoUpper X' := by
    have h1 : oTwoUpper (X.subgroupOf (K ⊔ T)) = (oTwoUpper X).subgroupOf (K ⊔ T) := by
      apply Subgroup.map_injective (K ⊔ T).subtype_injective
      rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le hXKT,
        Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le X).trans hXKT)]
    show (X.subgroupOf (K ⊔ T)).map (piKT614 hTK) =
      oTwoUpper ((X.subgroupOf (K ⊔ T)).map (piKT614 hTK))
    rw [oTwoUpper_map, h1, ← hXO]
  have hTX' : T' ≤ Subgroup.normalizer (X' : Set (MulAut (ModO2 K))) := by
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (piKT614 hTK))
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hTX ht) h
  have hE' : E' ≤ pCoreOf 2 (X' ⊔ T') := (imKT614_mono hTK hE).trans hO'
  have hEa' : IsElemAbelian 2 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show piKT614 hTK x * piKT614 hTK y = piKT614 hTK y * piKT614 hTK x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := hEa.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩
      have h2 : (x : Γ) * y = y * x := congrArg Subtype.val this
      exact h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hEa.2 _ hx)
      rw [this, map_one]
  have hE'ne : E' ≠ ⊥ := imKT614_ne_bot_of_two_group hTK hTs hE2 hEKT hEK
  have hXN' := not_le_normalizer_imKT614 hTK hTs hXK hXN
  obtain ⟨φ, hφN, hφT, hφO⟩ :=
    hloc T' X' E' hTs' hX'N hXO' hX5' hXn' hTX' hXN' hE' hEa' hE'ne
  obtain ⟨s, rfl⟩ := hφN
  obtain ⟨⟨k₀, hk₀⟩, rfl⟩ := QuotientGroup.mk_surjective s
  have hk₀KT : k₀ ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) hk₀
  have hle : (imKT614 hTK E).map (MulAut.conj (piKT614 hTK ⟨k₀, hk₀KT⟩)).toMonoidHom ≤
      imKT614 hTK T := by
    rw [piKT614_of_mem hTK hk₀]
    exact hφT
  obtain ⟨z, hz, hzE⟩ := exists_mem_K_conj_le_of_imKT614 hTK hTs hE2 hEKT hk₀ hle
  have hzK : z ∈ K := (Subgroup.mem_inf.mp hz).2
  have hzKT : z ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) hzK
  have hπz : piKT614 hTK ⟨z, hzKT⟩ = 1 :=
    (mem_kerAct614 hTK hzKT).mp (Subgroup.mem_inf.mp hz).1
  refine ⟨z * k₀, K.mul_mem hzK hk₀, hzE, ?_⟩
  intro hle2
  apply hφO
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨⟨e, heKT⟩, he, rfl⟩ := hψ
  have hfKT : k₀ * e * k₀⁻¹ ∈ K ⊔ T :=
    (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hk₀KT heKT) ((K ⊔ T).inv_mem hk₀KT)
  have hg₂KT : z * k₀ * e * (z * k₀)⁻¹ ∈ K ⊔ T :=
    (K ⊔ T).mul_mem ((K ⊔ T).mul_mem ((K ⊔ T).mul_mem hzKT hk₀KT) heKT)
      ((K ⊔ T).inv_mem ((K ⊔ T).mul_mem hzKT hk₀KT))
  have hg₂ : z * k₀ * e * (z * k₀)⁻¹ ∈ pCoreOf 2 (X ⊔ T) := hle2 ⟨e, he, rfl⟩
  have hπ₂ : piKT614 hTK ⟨z * k₀ * e * (z * k₀)⁻¹, hg₂KT⟩ =
      piKT614 hTK ⟨k₀ * e * k₀⁻¹, hfKT⟩ := by
    have e4 : (⟨z * k₀ * e * (z * k₀)⁻¹, hg₂KT⟩ : ↥(K ⊔ T)) =
        (⟨z, hzKT⟩ : ↥(K ⊔ T)) * (⟨k₀ * e * k₀⁻¹, hfKT⟩ : ↥(K ⊔ T)) *
          (⟨z, hzKT⟩ : ↥(K ⊔ T))⁻¹ :=
      Subtype.ext (show z * k₀ * e * (z * k₀)⁻¹ = z * (k₀ * e * k₀⁻¹) * z⁻¹ by group)
    rw [e4, map_mul, map_mul, map_inv, hπz, one_mul, inv_one, mul_one]
  have hmem := hO' (mem_imKT614 hTK hg₂ hg₂KT)
  rw [hπ₂] at hmem
  rw [← piKT614_of_mem hTK hk₀, piKT614_conj_apply_b hTK hk₀KT heKT hfKT]
  exact hmem

theorem kg614FusionL3_of_locFusL3
    (hloc : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
      (∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 δ p 1 (Q ⧸ Subgroup.center Q)) →
      LocFusL3 (MulAut Q) (MulAut.conj : Q →* MulAut Q).range) :
    KG614FusionL3 := by
  intro Γ _ _ K T X hKq hKt hTK hTs hXK hXO hX5 hXn hTX hXN E hE hEa hEK
  exact kg614Fusion_conclusion_of_locFusL3 (hloc (ModO2 K) hKq hKt) hTK hTs hXK hXO hX5 hXn hTX
    hXN hE hEa hEK

end CFSG.Quasithin.H13
