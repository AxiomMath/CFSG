module

public import CFSG.Quasithin.Vol2.Ch11SecHEnd1
public import CFSG.Quasithin.Vol2.Ch11SecHG16b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem comm_aux {G : Type*} [Group G] {a β ζ m : G} (h1 : β * ζ = ζ * β) (h2 : β * m = m * β)
    (h3 : a * ζ = ζ * a) (h4 : ζ * (a * m * a⁻¹ * m⁻¹) = (a * m * a⁻¹ * m⁻¹) * ζ) :
    (a * β) * (ζ * m) * (a * β)⁻¹ * (ζ * m)⁻¹ = a * m * a⁻¹ * m⁻¹ := by
  have hβ : β * (ζ * m) * β⁻¹ = ζ * m := by
    calc β * (ζ * m) * β⁻¹ = (β * ζ) * m * β⁻¹ := by group
      _ = ζ * (β * m) * β⁻¹ := by rw [h1]; group
      _ = ζ * m := by rw [h2]; group
  calc (a * β) * (ζ * m) * (a * β)⁻¹ * (ζ * m)⁻¹ =
      a * (β * (ζ * m) * β⁻¹) * a⁻¹ * m⁻¹ * ζ⁻¹ := by group
    _ = (a * ζ) * m * a⁻¹ * m⁻¹ * ζ⁻¹ := by rw [hβ]; group
    _ = ζ * (a * m * a⁻¹ * m⁻¹) * ζ⁻¹ := by rw [h3]; group
    _ = a * m * a⁻¹ * m⁻¹ := by rw [h4, mul_inv_cancel_right]

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem summand_line (i : Inp32) [IsMulCommutative ↥(fsuV T I)]
    [IsMulCommutative ↥(pOf T I H h)] {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π)
    {φ : ↥(fsuV T I) → (Fin 3 → F)} (hφadd : ∀ a b, φ (a * b) = φ a + φ b)
    (hφbij : Function.Bijective φ)
    (hφeq : ∀ (γ : ↥(StatedSL 3 F)) (w : ↥(fsuV T I)), φ ((π γ : MulAut ↥(fsuV T I)) w) =
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ w))
    (γy : Matrix (Fin 3) (Fin 3) F) (hγy : ∀ w : ↥(fsuV T I),
      φ (conjAct (fsuV T I) ⟨y, d.y_mem_normalizer_V⟩ w) = γy.mulVec (φ w))
    (hγyU : IsUnit γy) (v₀ : ↥(fsuV T I)) (hv₀ : (v₀ : G) ∉ bOf T I H)
    {W : Subgroup ↥(pOf T I H h)}
    (hW : BinaryNaturalSL (autOn (oTwoUpper H) (pOf T I H h)) W ⊥ 2 n) :
    ∃ u : Fin 3 → F, u ≠ 0 ∧
      (∀ c : F, ∃ z : ↥(fsuV T I), (z : G) ∈ bOf T I H ∧
        ∃ hzP : (z : G) ∈ pOf T I H h, (⟨z, hzP⟩ : ↥(pOf T I H h)) ∈ W ∧ φ z = c • u) ∧
      ∃ α : F, γy.mulVec u = α • u ∧
        ∀ (α₃ : F) (β : ↥(fsuV T I)), (β : G) ∈ bOf T I H →
          γy.mulVec (φ v₀) = α₃ • φ v₀ + φ β → α ^ 2 = α₃ := by
  have hn := d.c.two_le
  have hPab := d.isElemAbelian_P i
  have hsq : ∀ u : ↥(pOf T I H h), u ^ 2 = 1 := fun u =>
    Subtype.ext (by simpa using hPab.2 u u.2)
  have hVP := d.fsuV_le_normalizer_P i
  have hKP := d.K_le_normalizer_P i
  have hRGm := d.autOn_V_le_autOn_K i
  have hRsyl := d.sylow_autOn_V_P i hF hπ
  have hyNP : y ∈ Subgroup.normalizer (pOf T I H h : Set G) := hKP d.y_mem_K
  have hyGm : conjAct (pOf T I H h) ⟨y, hyNP⟩ ∈ autOn (oTwoUpper H) (pOf T I H h) :=
    ⟨⟨y, hyNP⟩, Subgroup.mem_subgroupOf.mpr d.y_mem_K, rfl⟩
  have hyN := conjAct_mem_normalizer_autOn hyNP d.y_mem_normalizer_V
  have hyodd : Odd (orderOf (conjAct (pOf T I H h) ⟨y, hyNP⟩)) :=
    d.yodd.of_dvd_nat ((orderOf_map_dvd (conjAct (pOf T I H h)) _).trans
      (by rw [Subgroup.orderOf_mk]))
  obtain ⟨K₀, _, _, hK₀, π₀, hπ₀⟩ := hW
  obtain ⟨μ, hμW, hμcomm, hcardℓ, hμy, hyμ, -⟩ := i.hKF3 K₀ n hn hK₀ ↥(pOf T I H h) hsq
    (autOn (oTwoUpper H) (pOf T I H h)) W π₀ hπ₀ (autOn (fsuV T I) (pOf T I H h)) hRsyl
    _ hyGm hyN hyodd
  have hWinv : ∀ σ ∈ autOn (oTwoUpper H) (pOf T I H h), ∀ u ∈ W, σ u ∈ W :=
    fun σ hσ u hu => hπ₀.2.2.2.1 ⟨σ, hσ⟩ u hu
  have hfixR : ∀ u : ↥(pOf T I H h), (∀ s ∈ autOn (fsuV T I) (pOf T I H h), s u = u) ↔
      (u : G) ∈ bOf T I H := by
    intro u
    change u ∈ fixV (autOn (fsuV T I) (pOf T I H h)) ↔ _
    rw [mem_fixV_autOn_iff hVP, ← d.P_inf_centralizer_V i]
    exact ⟨fun hu => ⟨u.2, hu⟩, fun hu => hu.2⟩
  have hcardW : Nat.card W = (2 ^ n) ^ 2 := by
    have hc := G64.RealizesVia.card_eq hπ₀
    rw [G64.card_natMod, Subgroup.card_bot, mul_one, hK₀] at hc
    exact hc
  obtain ⟨w, hwW, hwB⟩ : ∃ w : ↥(pOf T I H h), w ∈ W ∧ (w : G) ∉ bOf T I H := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hle : Nat.card W ≤ 2 ^ n := by
      rw [← hcardℓ]
      refine Nat.card_le_card_of_injective (fun u : ↥W => (⟨u.1, u.2, (hfixR u.1).mpr
        (hall u.1 u.2)⟩ : {u : ↥(pOf T I H h) // u ∈ W ∧
          ∀ s ∈ autOn (fsuV T I) (pOf T I H h), s u = u})) ?_
      intro a b hab
      exact Subtype.ext (congrArg (fun x => x.1) hab)
    rw [hcardW] at hle
    have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    nlinarith
  have hwNV : (w : G) ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    d.pCoreOf_le_normalizer_V (d.P_le_pCoreOf i w.2)
  have hwL := d.conjAct_P_mem i hF π hπ w.2 hwNV
  obtain ⟨γw, hγw⟩ : ∃ γw : ↥(StatedSL 3 F), π γw = ⟨_, hwL⟩ := hπ.1 ⟨_, hwL⟩
  have hσw : ∀ x : ↥(fsuV T I), φ (conjAct (fsuV T I) ⟨w, hwNV⟩ x) =
      ((γw : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ x) := by
    intro x
    rw [← hφeq γw x, hγw]
  choose vc hvc using fun c : F => hφbij.2 (c • φ v₀)
  set u : Fin 3 → F := φ v₀ - ((γw : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ v₀)
    with hu
  have hzV : ∀ c, (vc c : G) * w * (vc c : G)⁻¹ * (w : G)⁻¹ ∈ fsuV T I := fun c =>
    d.comm_mem_V i (vc c).2 w.2
  have hzB : ∀ c, (vc c : G) * w * (vc c : G)⁻¹ * (w : G)⁻¹ ∈ bOf T I H := fun c =>
    d.comm_mem_B i (vc c).2 w.2
  have hzP : ∀ c, (vc c : G) * w * (vc c : G)⁻¹ * (w : G)⁻¹ ∈ pOf T I H h := fun c =>
    Subgroup.mem_sup_left (hzB c)
  have hzW : ∀ c, (⟨_, hzP c⟩ : ↥(pOf T I H h)) ∈ W := by
    intro c
    have hvcR : conjAct (pOf T I H h) ⟨vc c, hVP (vc c).2⟩ ∈ autOn (oTwoUpper H) (pOf T I H h) :=
      hRGm ⟨⟨vc c, hVP (vc c).2⟩, Subgroup.mem_subgroupOf.mpr (vc c).2, rfl⟩
    have : (⟨_, hzP c⟩ : ↥(pOf T I H h)) =
        conjAct (pOf T I H h) ⟨vc c, hVP (vc c).2⟩ w * w⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, conjAct_apply_coe, Subgroup.coe_inv]
    rw [this]
    exact W.mul_mem (hWinv _ hvcR w hwW) (W.inv_mem hwW)
  have hzφ : ∀ c, φ ⟨_, hzV c⟩ = c • u := by
    intro c
    have h1 : (⟨_, hzV c⟩ : ↥(fsuV T I)) = vc c * (conjAct (fsuV T I) ⟨w, hwNV⟩ (vc c))⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe]
      group
    rw [h1, coords_comm hφadd _ _ hσw, hvc, Matrix.mulVec_smul, hu, smul_sub]
  have hv1 : vc 1 = v₀ := hφbij.1 (by rw [hvc, one_smul])
  have hu0 : u ≠ 0 := by
    intro hu0
    apply hwB
    have h1 : φ ⟨_, hzV 1⟩ = φ 1 := by rw [hzφ, hu0, smul_zero, coords_one hφadd]
    have h2 := congrArg Subtype.val (hφbij.1 h1)
    simp only [OneMemClass.coe_one] at h2
    rw [hv1] at h2
    exact d.mem_B_of_comm i hF hπ v₀.2 hv₀ w.2 (by
      calc (v₀ : G) * w = ((v₀ : G) * w * (v₀ : G)⁻¹ * (w : G)⁻¹) * (w * v₀) := by group
        _ = w * v₀ := by rw [h2, one_mul])
  let f : F → {u : ↥(pOf T I H h) // u ∈ W ∧ ∀ s ∈ autOn (fsuV T I) (pOf T I H h), s u = u} :=
    fun c => ⟨⟨_, hzP c⟩, hzW c, (hfixR _).mpr (hzB c)⟩
  have hfinj : Function.Injective f := by
    intro c c' hcc
    have h1 : (vc c : G) * w * (vc c : G)⁻¹ * (w : G)⁻¹ =
        (vc c' : G) * w * (vc c' : G)⁻¹ * (w : G)⁻¹ :=
      congrArg (fun x : {u : ↥(pOf T I H h) // u ∈ W ∧
        ∀ s ∈ autOn (fsuV T I) (pOf T I H h), s u = u} => ((x.1 : ↥(pOf T I H h)) : G)) hcc
    have h2 : φ ⟨_, hzV c⟩ = φ ⟨_, hzV c'⟩ := congrArg φ (Subtype.ext h1)
    rw [hzφ, hzφ] at h2
    exact smul_left_injective F hu0 h2
  have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by rw [hcardℓ, hF])
  have hyB : ∀ b ∈ bOf T I H, y * b * y⁻¹ ∈ bOf T I H := by
    intro b hb
    rw [d.bOf_eq i] at hb ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp d.y_mem_normalizer_V b).mp hb.1,
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H d.yH) b).mp hb.2⟩
  have hyz : conjAct (pOf T I H h) ⟨y, hyNP⟩ ⟨_, hzP 1⟩ ∈ W ∧
      ∀ s ∈ autOn (fsuV T I) (pOf T I H h),
        s (conjAct (pOf T I H h) ⟨y, hyNP⟩ ⟨_, hzP 1⟩) =
          conjAct (pOf T I H h) ⟨y, hyNP⟩ ⟨_, hzP 1⟩ := by
    refine ⟨hWinv _ hyGm _ (hzW 1), (hfixR _).mpr ?_⟩
    rw [conjAct_apply_coe]
    exact hyB _ (hzB 1)
  obtain ⟨α, hα⟩ := hfbij.2 ⟨_, hyz⟩
  have hαG : (vc α : G) * w * (vc α : G)⁻¹ * (w : G)⁻¹ =
      y * ((vc 1 : G) * w * (vc 1 : G)⁻¹ * (w : G)⁻¹) * y⁻¹ := by
    have := congrArg (fun x : {u : ↥(pOf T I H h) // u ∈ W ∧
      ∀ s ∈ autOn (fsuV T I) (pOf T I H h), s u = u} => ((x.1 : ↥(pOf T I H h)) : G)) hα
    simpa [f, conjAct_apply_coe] using this
  have hγu : γy.mulVec u = α • u := by
    have h1 := hγy ⟨_, hzV 1⟩
    rw [hzφ, one_smul] at h1
    rw [← h1, ← hzφ α]
    congr 1
    apply Subtype.ext
    rw [conjAct_apply_coe]
    exact hαG.symm
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hγu
    exact hu0 ((Matrix.mulVec_injective_iff_isUnit.mpr hγyU)
      (hγu.trans (Matrix.mulVec_zero γy).symm))
  refine ⟨u, hu0, fun c => ⟨⟨_, hzV c⟩, hzB c, hzP c, hzW c, hzφ c⟩, α, hγu, ?_⟩
  intro α₃ β hβ hrel
  have hVab := SecA.isElemAbelian_fsuV d.c.s.hyp
  have hyv : conjAct (fsuV T I) ⟨y, d.y_mem_normalizer_V⟩ v₀ = vc α₃ * β :=
    hφbij.1 (by rw [hγy, hrel, hφadd, hvc])
  have e1 : y * (v₀ : G) * y⁻¹ = (vc α₃ : G) * β := by
    have := congrArg Subtype.val hyv
    rwa [conjAct_apply_coe, Subgroup.coe_mul] at this
  have hζ := hyμ w hwW
  have hζB : ((conjAct (pOf T I H h) ⟨y, hyNP⟩ w * (μ w)⁻¹ : ↥(pOf T I H h)) : G) ∈
      bOf T I H := (hfixR _).mp hζ
  have e2 : y * (w : G) * y⁻¹ =
      ((conjAct (pOf T I H h) ⟨y, hyNP⟩ w * (μ w)⁻¹ : ↥(pOf T I H h)) : G) * (μ w : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe]
    group
  have hβP : (β : G) ∈ pOf T I H h := Subgroup.mem_sup_left hβ
  have hζP : ((conjAct (pOf T I H h) ⟨y, hyNP⟩ w * (μ w)⁻¹ : ↥(pOf T I H h)) : G) ∈
      pOf T I H h := Subtype.mem _
  have hkey : y * ((vc 1 : G) * w * (vc 1 : G)⁻¹ * (w : G)⁻¹) * y⁻¹ =
      (vc α₃ : G) * (μ w : G) * (vc α₃ : G)⁻¹ * (μ w : G)⁻¹ := by
    rw [hv1]
    calc y * ((v₀ : G) * w * (v₀ : G)⁻¹ * (w : G)⁻¹) * y⁻¹ =
        (y * (v₀ : G) * y⁻¹) * (y * (w : G) * y⁻¹) * (y * (v₀ : G) * y⁻¹)⁻¹ *
          (y * (w : G) * y⁻¹)⁻¹ := by group
      _ = _ := by
        rw [e1, e2]
        refine comm_aux (comm_of_isElemAbelian hPab hβP hζP)
          (comm_of_isElemAbelian hPab hβP (μ w).2)
          (comm_of_isElemAbelian hVab (vc α₃).2 ((inf_le_left : bOf T I H ≤ fsuV T I) hζB))
          (comm_of_isElemAbelian hPab hζP (d.comm_mem_P i (vc α₃).2 (μ w).2))
  have hμrel : (vc α₃ : G) * (μ w : G) * (vc α₃ : G)⁻¹ * (μ w : G)⁻¹ =
      (μ ⟨_, hzP α₃⟩ : G) := by
    have hãGm : conjAct (pOf T I H h) ⟨vc α₃, hVP (vc α₃).2⟩ ∈
        autOn (oTwoUpper H) (pOf T I H h) :=
      hRGm ⟨⟨vc α₃, hVP (vc α₃).2⟩, Subgroup.mem_subgroupOf.mpr (vc α₃).2, rfl⟩
    have hz : (⟨_, hzP α₃⟩ : ↥(pOf T I H h)) =
        conjAct (pOf T I H h) ⟨vc α₃, hVP (vc α₃).2⟩ w * w⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, conjAct_apply_coe, Subgroup.coe_inv]
    rw [hz, map_mul, map_inv, hμcomm _ hãGm w hwW, Subgroup.coe_mul, conjAct_apply_coe,
      Subgroup.coe_inv]
  have hyz' : conjAct (pOf T I H h) ⟨y, hyNP⟩ ⟨_, hzP (α⁻¹ * α₃)⟩ = ⟨_, hzP α₃⟩ := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    have h1 := hγy ⟨_, hzV (α⁻¹ * α₃)⟩
    rw [hzφ, Matrix.mulVec_smul, hγu, smul_smul,
      show α⁻¹ * α₃ * α = α₃ by field_simp, ← hzφ α₃] at h1
    have h2 := congrArg Subtype.val (hφbij.1 h1)
    rwa [conjAct_apply_coe] at h2
  have hμz : μ ⟨_, hzP α₃⟩ = ⟨_, hzP (α⁻¹ * α₃)⟩ := by
    rw [← hyz']
    exact hμy _ (hzW _) ((hfixR _).mpr (hzB _))
  have hfin : (vc α : G) * w * (vc α : G)⁻¹ * (w : G)⁻¹ =
      (vc (α⁻¹ * α₃) : G) * w * (vc (α⁻¹ * α₃) : G)⁻¹ * (w : G)⁻¹ := by
    rw [hαG, hkey, hμrel, hμz]
  have hαeq : α = α⁻¹ * α₃ := hfinj (Subtype.ext (Subtype.ext hfin))
  have h3 : α * α = α₃ := by
    calc α * α = α * (α⁻¹ * α₃) := by rw [← hαeq]
      _ = α₃ := by rw [← mul_assoc, mul_inv_cancel₀ hα0, one_mul]
  rw [sq]
  exact h3

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
