module

public import CFSG.Quasithin.H13.AS91Sec8KautZ
public import CFSG.Quasithin.H13.AS91Sec8Cocycle
public import CFSG.Quasithin.H13.AS91Sec8Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem index_G3_subgroupOf_K (hJ : HypJ4 G z) : (c.G3.subgroupOf c.K).index = 7 := by
  classical
  let zz : ↥c.Z := ⟨z, c.z_mem_Z⟩
  letI : MulAction ↥c.K ↥c.Z := MulAction.compHom ↥c.Z c.actKZ
  have hsm : ∀ (k : ↥c.K) (x : ↥c.Z), ((k • x : ↥c.Z) : G) = k * x * (k : G)⁻¹ := fun k x => by
    show ((c.actKZ k x : ↥c.Z) : G) = _
    rw [c.actKZ_apply, Subgroup.coe_inv]
  have hstab : MulAction.stabilizer ↥c.K zz = c.G3.subgroupOf c.K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Loc49.G3, H,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 := congrArg Subtype.val h
      rw [hsm] at h1
      have : (k : G) * z = z * k := by
        have := congrArg (· * (k : G)) h1
        simpa [mul_assoc] using this
      exact this.symm
    · intro h
      apply Subtype.ext
      rw [hsm]
      have := h z (Set.mem_singleton z)
      show (k : G) * z * (k : G)⁻¹ = z
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
  have hz1 : z ≠ 1 := Loc49.z_ne_one hJ
  have horb : MulAction.orbit ↥c.K zz = {w | w ≠ 1} := by
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩ h
      have h1 := congrArg Subtype.val h
      rw [hsm] at h1
      apply hz1
      have : (k : G) * z * (k : G)⁻¹ = 1 := h1
      calc z = (k : G)⁻¹ * ((k : G) * z * (k : G)⁻¹) * k := by group
        _ = 1 := by rw [this]; group
    · intro hw
      have hzz : zz ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
      obtain ⟨f, hf⟩ := elem8_exists_mulAut_apply_eq c.Z_comm' c.Z_sq' c.card_Z hzz hw
      obtain ⟨k, rfl⟩ := c.actKZ_surjective f
      exact ⟨k, hf⟩
  rw [← hstab, MulAction.index_stabilizer, horb]
  have h8 : Nat.card ↥c.Z = 8 := c.card_Z
  have : ({w | w ≠ (1 : ↥c.Z)} : Set ↥c.Z) = Set.univ \ {1} := by
    ext w; simp
  rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _),
    Set.ncard_univ, h8]

theorem kaut (hJ : HypJ4 G z) (α : ↥c.K ≃* ↥c.K)
    (hα : ∀ k : ↥c.K, (k : G) ∈ c.G3 → α k = k) :
    ∃ w : G, w ∈ c.G3 ∧ w ∈ normalizer (c.K : Set G) ∧ (∀ i ∈ c.G3, w * i = i * w) ∧
      ∀ k : ↥c.K, ((α k : ↥c.K) : G) = w * k * w⁻¹ := by
  classical
  have hαR : ∀ r : ↥c.K, (r : G) ∈ c.R → α r = r := fun r hr => hα r (c.R_le_G3 hr)
  have hmemZ : ∀ k : ↥c.K, ((α k : ↥c.K) : G) * (k : G)⁻¹ ∈ c.Z := by
    intro k
    refine c.K_cent_R_le_Z (mul_mem (α k).2 (inv_mem k.2)) ?_
    intro r hr
    have hr' : (k : G)⁻¹ * r * k ∈ c.R := by
      simpa using c.R_conj (inv_mem k.2) hr
    let rK : ↥c.K := ⟨r, c.R_le_K hr⟩
    let r'K : ↥c.K := ⟨(k : G)⁻¹ * r * k, c.R_le_K hr'⟩
    have e1 : rK = k * r'K * k⁻¹ := by
      apply Subtype.ext
      show r = (k : G) * ((k : G)⁻¹ * r * k) * (k : G)⁻¹
      group
    have e2 : α rK = α k * r'K * (α k)⁻¹ := by
      have := congrArg α e1
      rwa [map_mul, map_mul, map_inv, hαR r'K hr'] at this
    rw [hαR rK hr] at e2
    have e3 := congrArg Subtype.val e2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e3
    change r = ((α k : ↥c.K) : G) * ((k : G)⁻¹ * r * k) * ((α k : ↥c.K) : G)⁻¹ at e3
    show r * (((α k : ↥c.K) : G) * (k : G)⁻¹) = (((α k : ↥c.K) : G) * (k : G)⁻¹) * r
    have e4 : r * (((α k : ↥c.K) : G) * (k : G)⁻¹) = ((α k : ↥c.K) : G) * (k : G)⁻¹ * r := by
      have e5 : ((α k : ↥c.K) : G)⁻¹ * r * ((α k : ↥c.K) : G) = (k : G)⁻¹ * r * k := by
        calc ((α k : ↥c.K) : G)⁻¹ * r * ((α k : ↥c.K) : G)
            = ((α k : ↥c.K) : G)⁻¹ * (((α k : ↥c.K) : G) * ((k : G)⁻¹ * r * k) *
                ((α k : ↥c.K) : G)⁻¹) * ((α k : ↥c.K) : G) := by
              conv_lhs => rw [e3]
          _ = (k : G)⁻¹ * r * k := by group
      calc r * (((α k : ↥c.K) : G) * (k : G)⁻¹)
          = ((α k : ↥c.K) : G) * (((α k : ↥c.K) : G)⁻¹ * r * ((α k : ↥c.K) : G)) *
              (k : G)⁻¹ := by group
        _ = ((α k : ↥c.K) : G) * ((k : G)⁻¹ * r * k) * (k : G)⁻¹ := by rw [e5]
        _ = ((α k : ↥c.K) : G) * (k : G)⁻¹ * r := by group
    exact e4
  let e : ↥c.K → ↥c.Z := fun k => ⟨((α k : ↥c.K) : G) * (k : G)⁻¹, hmemZ k⟩
  have hcoc : ∀ k l, e (k * l) = e k * (c.actKZ k) (e l) := by
    intro k l
    apply Subtype.ext
    show ((α (k * l) : ↥c.K) : G) * ((k * l : ↥c.K) : G)⁻¹ =
      (((α k : ↥c.K) : G) * (k : G)⁻¹) *
        ((k : G) * (((α l : ↥c.K) : G) * (l : G)⁻¹) * ((k⁻¹ : ↥c.K) : G))
    simp only [map_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hT : ∀ t ∈ c.G3.subgroupOf c.K, e t = 1 := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    apply Subtype.ext
    show ((α t : ↥c.K) : G) * (t : G)⁻¹ = 1
    rw [hα t ht]
    simp
  letI : CommGroup ↥c.Z :=
    { (inferInstance : Group ↥c.Z) with mul_comm := fun a b => c.Z_comm' a b }
  have hodd : Odd (c.G3.subgroupOf c.K).index := by
    rw [c.index_G3_subgroupOf_K hJ]; decide
  obtain ⟨w, hw⟩ := cocycle_odd_index c.actKZ (c.G3.subgroupOf c.K) hodd c.Z_sq' e hcoc hT
  have hαw : ∀ k : ↥c.K, ((α k : ↥c.K) : G) = (w : G) * k * (w : G)⁻¹ := by
    intro k
    have h1 := congrArg Subtype.val (hw k)
    have h2 : ((α k : ↥c.K) : G) * (k : G)⁻¹ =
        (w : G) * ((k : G) * (w : G) * (k : G)⁻¹)⁻¹ := by
      have := h1
      simp only [e, Subgroup.coe_mul, Subgroup.coe_inv, c.actKZ_apply] at this
      convert this using 2
    calc ((α k : ↥c.K) : G) = (((α k : ↥c.K) : G) * (k : G)⁻¹) * k := by group
      _ = (w : G) * ((k : G) * (w : G) * (k : G)⁻¹)⁻¹ * k := by rw [h2]
      _ = (w : G) * k * (w : G)⁻¹ := by group
  have hwz : (w : G) = 1 ∨ (w : G) = z := by
    by_contra hcon
    replace hcon := not_or.mp hcon
    have hw1 : w ≠ 1 := fun h => hcon.1 (by rw [h]; rfl)
    have hzz : (⟨z, c.z_mem_Z⟩ : ↥c.Z) ≠ 1 := fun h => Loc49.z_ne_one hJ (congrArg Subtype.val h)
    have hwzz : w ≠ (⟨z, c.z_mem_Z⟩ : ↥c.Z) := fun h => hcon.2 (congrArg Subtype.val h)
    obtain ⟨f, hfz, hfw⟩ := elem8_exists_mulAut_fix c.Z_comm' c.Z_sq' c.card_Z hzz hw1 hwzz
    obtain ⟨k, hk⟩ := c.exists_mem_K_conj_eq f
    have hkz : (k : G) ∈ c.G3 := by
      rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := congrArg Subtype.val hfz
      rw [hk] at h1
      have : (k : G) * y * (k : G)⁻¹ = y := h1
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have h1 := hα k hkz
    have h2 := hαw k
    rw [h1] at h2
    apply hfw
    apply Subtype.ext
    rw [hk]
    have h3 : (k : G) * w = w * k := by
      have := congrArg (· * (w : G)) h2
      simpa [mul_assoc] using this
    rw [mul_inv_eq_iff_eq_mul]
    exact h3
  refine ⟨(w : G), ?_, ?_, ?_, hαw⟩
  · rcases hwz with h | h
    · rw [h]; exact one_mem _
    · rw [h]
      rw [Loc49.G3, H, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
  · exact Subgroup.le_normalizer (c.R_le_K (c.Z_le_R w.2))
  · intro i hi
    rcases hwz with h | h
    · rw [h]; simp
    · rw [h]
      rw [Loc49.G3, H, Subgroup.mem_centralizer_iff] at hi
      exact hi z (Set.mem_singleton z)

end Loc49

theorem stmt8_Kaut : Stmt8_Kaut := by
  intro G _ _ z hJ c α hα
  exact c.kaut hJ α hα

end CFSG.Quasithin.H13.AS91
