module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.SzR1FamCenter

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem vBeta_le_K1_gen [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hodd : Odd (Fintype.card Ω)) {a b : Ω} (hab : a ≠ b)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs) :
    vBeta K1 L2 S Zs ≤ K1 := by
  classical
  have hXN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) := sup_le Subgroup.le_normalizer C.hSK
  have hNn : (K1.subgroupOf (K1 ⊔ S)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  let φ : ↥(K1 ⊔ S) →* ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) := QuotientGroup.mk' _
  let ψ : ↥(vBeta K1 L2 S Zs) →* ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) :=
    φ.comp (Subgroup.inclusion C.U_le_sup)
  have hψ1 : ∀ x : ↥(vBeta K1 L2 S Zs), ψ x = 1 → (x : G) ∈ K1 := by
    intro x hx
    have := (QuotientGroup.eq_one_iff (⟨(x : G), C.U_le_sup x.2⟩ : ↥(K1 ⊔ S))).mp hx
    exact Subgroup.mem_subgroupOf.mp this
  have hψK : ∀ k : ↥K1, ∀ x : ↥(vBeta K1 L2 S Zs), ψ x = φ ⟨(k : G) * x * (k : G)⁻¹,
      (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem (Subgroup.mem_sup_left k.2) (C.U_le_sup x.2))
        ((K1 ⊔ S).inv_mem (Subgroup.mem_sup_left k.2))⟩ := by
    intro k x
    have hk1 : φ ⟨(k : G), Subgroup.mem_sup_left k.2⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr k.2)
    have e : (⟨(k : G) * x * (k : G)⁻¹, (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem
        (Subgroup.mem_sup_left k.2) (C.U_le_sup x.2))
        ((K1 ⊔ S).inv_mem (Subgroup.mem_sup_left k.2))⟩ : ↥(K1 ⊔ S)) =
        ⟨(k : G), Subgroup.mem_sup_left k.2⟩ * ⟨(x : G), C.U_le_sup x.2⟩ *
          ⟨(k : G), Subgroup.mem_sup_left k.2⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hk1, one_mul, inv_one, mul_one]
    rfl
  set c := ψ (C.zU a b) with hc
  set w : Ω → ↥(K1 ⊔ S) ⧸ K1.subgroupOf (K1 ⊔ S) := fun i => ψ (C.wU i) with hw
  have hG := C.gramRel hab
  have key : ∀ i j : Ω, ∃ n : ℤ, w i = w j * c ^ n := by
    intro i j
    let k : ↥K1 := C.D.kf j * (C.D.kf i)⁻¹
    have hk : C.D.act k i = j := by
      show C.D.act (C.D.kf j * (C.D.kf i)⁻¹) i = j
      have h1 : C.D.act (C.D.kf i)⁻¹ i = C.D.pt := by
        rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
        exact (C.D.kf_spec i).symm
      rw [map_mul, Equiv.Perm.mul_apply, h1, C.D.kf_spec]
    obtain ⟨ε, hε, hconj⟩ := C.conj_zf k i
    rw [hk] at hconj
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      ((C.Zs_eq_zpowers (C.cm_mem a b) (C.cm_ne_one hab)).le hε)
    refine ⟨n, ?_⟩
    have h1 := hψK k (C.wU i)
    have e : (⟨(k : G) * ((C.wU i : ↥(vBeta K1 L2 S Zs)) : G) * (k : G)⁻¹,
        (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem (Subgroup.mem_sup_left k.2)
          (C.U_le_sup (C.wU i).2)) ((K1 ⊔ S).inv_mem (Subgroup.mem_sup_left k.2))⟩ : ↥(K1 ⊔ S)) =
        (Subgroup.inclusion C.U_le_sup) (C.wU j * C.zU a b ^ n) := by
      apply Subtype.ext
      show (k : G) * C.zf i * (k : G)⁻¹ = C.zf j * (C.cm a b) ^ n
      rw [hconj, hn]
    rw [e] at h1
    have : φ ((Subgroup.inclusion C.U_le_sup) (C.wU j * C.zU a b ^ n)) =
        ψ (C.wU j * C.zU a b ^ n) := rfl
    rw [this, map_mul, map_zpow] at h1
    exact h1
  have hcomm : ∀ j, w j * c = c * w j := by
    intro j
    have h := hG.z_comm (C.wU j)
    have := congrArg ψ h
    rwa [map_mul, map_mul] at this
  have hc_def : c = w a * w b * (w a)⁻¹ * (w b)⁻¹ := by
    have e : C.zU a b = C.wU a * C.wU b * (C.wU a)⁻¹ * (C.wU b)⁻¹ := Subtype.ext rfl
    rw [hc, e, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hc1 : c = 1 := by
    obtain ⟨n, hn⟩ := key a b
    have hw' : c ^ n * w b = w b * c ^ n := ((Commute.symm (show Commute (w b) c from hcomm b)).zpow_left n).eq
    rw [hc_def, hn]
    calc w b * c ^ n * w b * (w b * c ^ n)⁻¹ * (w b)⁻¹
        = w b * (c ^ n * w b) * (c ^ n)⁻¹ * (w b)⁻¹ * (w b)⁻¹ := by group
      _ = w b * (w b * c ^ n) * (c ^ n)⁻¹ * (w b)⁻¹ * (w b)⁻¹ := by rw [hw']
      _ = 1 := by group
  have hall : ∀ i j, w i = w j := by
    intro i j
    obtain ⟨n, hn⟩ := key i j
    rw [hn, hc1, one_zpow, mul_one]
  have ha2 : w a * w a = 1 := by
    have := congrArg ψ (hG.w_sq a)
    rwa [map_mul, map_one] at this
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : List Ω, l₀ = Finset.univ.toList := ⟨_, rfl⟩
  have hnd : l₀.Nodup := by rw [hl₀]; exact Finset.nodup_toList _
  have hallm : ∀ i, i ∈ l₀ := by intro i; rw [hl₀]; simp
  have hlen : l₀.length = Fintype.card Ω := by
    rw [hl₀, Finset.length_toList, Finset.card_univ]
  obtain ⟨y, hy⟩ : ∃ y : ↥(vBeta K1 L2 S Zs), y = SzR1.gprod C.wU l₀ := ⟨_, rfl⟩
  have hyc : ∀ u : ↥(vBeta K1 L2 S Zs), u * y = y * u := by
    intro u
    have hu : u ∈ Subgroup.closure (insert (C.zU a b) (Set.range C.wU)) := by
      rw [C.closure_wU hab]; exact Subgroup.mem_top u
    rw [hy]
    exact hG.commute_gprod_univ_closure hodd l₀ hnd hallm hu
  have hyZ : (y : G) ∈ Zs := by
    apply hcen (y : G) y.2
    intro u hu
    exact congrArg Subtype.val (hyc ⟨u, hu⟩).symm
  have hyZ' : (y : G) ∈ Subgroup.zpowers (C.cm a b) := by
    rw [← C.Zs_eq_zpowers (C.cm_mem a b) (C.cm_ne_one hab)]
    exact hyZ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyZ'
  have hyz : y = C.zU a b ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
  have hprod : ψ y = w a ^ Fintype.card Ω := by
    rw [hy, SzR1.gprod, map_list_prod, List.map_map, ← hlen]
    have := List.prod_eq_pow_length (l := List.map (⇑ψ ∘ C.wU) l₀) (m := w a) (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hall i a)
    rwa [List.length_map] at this
  have hlhs : ψ y = 1 := by
    rw [hyz, map_zpow]
    show c ^ m = 1
    rw [hc1, one_zpow]
  have hwa : w a = 1 := by
    rw [hlhs] at hprod
    obtain ⟨r, hr⟩ := hodd
    rw [hr, pow_succ, pow_mul, pow_two, ha2, one_pow, one_mul] at hprod
    exact hprod.symm
  have hzK : ∀ i, C.zf i ∈ K1 := fun i => hψ1 (C.wU i) (by
    have := hall i a
    simp only [hw] at this
    rw [this]
    exact hwa)
  have hcK : C.cm a b ∈ K1 := hψ1 (C.zU a b) hc1
  rw [C.U_eq_closure (C.cm_mem a b) (C.cm_ne_one hab), Subgroup.closure_le]
  rintro x (rfl | ⟨j, rfl⟩)
  · exact hcK
  · exact hzK j

end CFSG.Quasithin.Background.Harris.R1
