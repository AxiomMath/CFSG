module

public import CFSG.Quasithin.Vol2.Ch11SecA15GO3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.SU2
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace OnanData

variable {Z Y T V₁ C : Subgroup G} {d : G}

theorem goPair (D : OnanData Z Y T V₁ C d) : GOPair ↥Z (Subgroup.zpowers D.dstar) := by
  classical
  have hfix := D.fixSub_eq
  have : Fintype ↥(Subgroup.zpowers D.dstar) := Fintype.ofFinite _
  have hexp : ∀ v : ↥Z, v * v = 1 := fun v => Subtype.ext (D.exp2 v v.2)
  obtain ⟨m, hm, hmz⟩ := D.odd
  have hord : Odd (Nat.card ↥(Subgroup.zpowers D.dstar)) := by
    rw [Nat.card_zpowers]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one (D.dstar_pow_eq_one hmz))
  have hoddF : Odd (Fintype.card ↥(Subgroup.zpowers D.dstar)) := by
    rwa [← Nat.card_eq_fintype_card]
  let instC : CommGroup ↥Z :=
    { (inferInstance : Group ↥Z) with mul_comm := fun a b => Subtype.ext (D.comm _ a.2 _ b.2) }
  have hci := @SU2.commSub_inf_fixSub _ _ ↥Z instC _ (Subgroup.zpowers D.dstar) _ hexp hoddF
  have hmemC : ∀ u ∈ SU2.commSub ↥Z (Subgroup.zpowers D.dstar), (u : G) ∈ C → u = 1 := by
    intro u hu huC
    have hu' : u ∈ fixSub ↥Z (Subgroup.zpowers D.dstar) := by
      rw [hfix, Subgroup.mem_subgroupOf]; exact huC
    have h1 : u ∈ (@SU2.commSub _ _ ↥Z instC.toGroup _ (Subgroup.zpowers D.dstar)) ⊓
        (@fixSub _ _ ↥Z instC.toGroup _ (Subgroup.zpowers D.dstar)) := ⟨hu, hu'⟩
    rw [hci] at h1
    exact h1
  obtain ⟨v₀, hv₀, w₀, hw₀, hv₀C, hw₀C, hvw₀⟩ := D.three
  refine ⟨hexp, ?_, inferInstance, hord, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact hx v
  ·
    intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    obtain ⟨k, hk⟩ := D.trans v₀ hv₀ w₀ hw₀ hv₀C hw₀C
    have h1 : d ^ k * v₀ * (d ^ k)⁻¹ = v₀ := by
      have := D.dstar_pow_smul_coe k ⟨v₀, D.VZ hv₀⟩
      rw [hbot, one_pow, one_smul] at this
      exact this.symm
    rw [h1] at hk
    exact hvw₀ hk
  ·
    intro v hv hv1 w hw hw1
    have hvC : (v : G) ∉ C := fun h => hv1 (hmemC v hv h)
    have hwC : (w : G) ∉ C := fun h => hw1 (hmemC w hw h)
    have hvV : (v : G) ∈ V₁ := (Subgroup.mem_subgroupOf).mp (D.commSub_le hv)
    have hwV : (w : G) ∈ V₁ := (Subgroup.mem_subgroupOf).mp (D.commSub_le hw)
    obtain ⟨k, hk⟩ := D.trans v hvV w hwV hvC hwC
    have hgk : D.dstar ^ k ∈ Subgroup.zpowers D.dstar :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k
    refine ⟨D.dstar ^ k, hgk, ?_⟩
    have hu : (D.dstar ^ k • v) * w⁻¹ ∈ SU2.commSub ↥Z (Subgroup.zpowers D.dstar) :=
      Subgroup.mul_mem _ (D.smul_mem_commSub hgk hv) (Subgroup.inv_mem _ hw)
    have huC : (((D.dstar ^ k • v) * w⁻¹ : ↥Z) : G) ∈ C := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, dstar_pow_smul_coe]
      exact hk
    exact mul_inv_eq_one.mp (hmemC _ hu huC)
  ·
    rw [hfix]
    intro hbot
    apply D.Cne
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact le_bot_iff.mp fun c hc => hbot.le_bot ⟨hc, D.CZ hc⟩
  ·
    intro x₁ x₂ hne
    rw [hfix] at hne ⊢
    obtain ⟨y₁, rfl⟩ := D.ystar_surj x₁
    obtain ⟨y₂, rfl⟩ := D.ystar_surj x₂
    erw [D.smul_eq y₁ D.CZ, D.smul_eq y₂ D.CZ] at hne ⊢
    by_contra hne'
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
    obtain ⟨hu₁', hu₂'⟩ := hu
    have hu₁ : (y₁ : G)⁻¹ * u * y₁ ∈ C := mem_map_conj_iff.mp (Subgroup.mem_subgroupOf.mp hu₁')
    have hu₂ : (y₂ : G)⁻¹ * u * y₂ ∈ C := mem_map_conj_iff.mp (Subgroup.mem_subgroupOf.mp hu₂')
    set y : G := (y₁ : G)⁻¹ * y₂ with hy
    have hyY : y ∈ Y := Y.mul_mem (Y.inv_mem y₁.2) y₂.2
    have hinter : C ⊓ C.map (MulAut.conj y).toMonoidHom ≠ ⊥ := by
      rw [Ne, eq_bot_iff, IsConcreteLE.not_le_iff_exists]
      refine ⟨(y₁ : G)⁻¹ * u * y₁, ⟨hu₁, ?_⟩, ?_⟩
      · refine mem_map_conj_iff.mpr ?_
        rw [hy]
        simpa [mul_assoc] using hu₂
      · intro h1
        rw [Subgroup.mem_bot] at h1
        apply hu1
        apply Subtype.ext
        apply Subtype.ext
        change (u : G) = 1
        calc (u : G) = (y₁ : G) * ((y₁ : G)⁻¹ * u * y₁) * (y₁ : G)⁻¹ := by group
          _ = 1 := by rw [h1]; group
    have hCy := D.TI y hyY hinter
    apply hne
    congr 1
    calc C.map (MulAut.conj (y₁ : G)).toMonoidHom =
        (C.map (MulAut.conj y).toMonoidHom).map (MulAut.conj (y₁ : G)).toMonoidHom := by rw [hCy]
      _ = C.map (MulAut.conj (y₂ : G)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext g
        simp [hy, mul_assoc]
  ·
    intro x hx g hg
    rw [hfix] at hx
    obtain ⟨y, rfl⟩ := D.ystar_surj x
    erw [D.smul_eq_iff y] at hx
    obtain ⟨k, hk⟩ := D.norm y y.2 hx
    have hconj : D.ystar y * D.dstar * (D.ystar y)⁻¹ = D.dstar ^ k := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change (((D.ystar y * D.dstar * (D.ystar y)⁻¹) • v : ↥Z) : G) = ((D.dstar ^ k • v : ↥Z) : G)
      have hd1 : ∀ w : ↥Z, ((D.dstar • w : ↥Z) : G) = d * w * d⁻¹ := fun w => by
        have := D.dstar_pow_smul_coe 1 w
        simpa using this
      have hinv : (((D.ystar y)⁻¹ • v : ↥Z) : G) = (y : G)⁻¹ * v * y := by
        have : (D.ystar y)⁻¹ = D.ystar y⁻¹ := by
          apply Subtype.ext
          simp [ystar]
        rw [this, D.ystar_smul_coe]
        simp
      rw [dstar_pow_smul_coe, ← hk v v.2, mul_smul, mul_smul, D.ystar_smul_coe, hd1, hinv]
      group
    obtain ⟨j, rfl⟩ := exists_pow_of_mem_zpowers hg
    rw [← conj_pow, hconj, ← pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end OnanData

end CFSG.Quasithin.Vol2.Ch11.SecA
