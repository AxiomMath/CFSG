module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.GGFFEleven
import CFSG.LocalAnalysis.StandardType.GGFFP51
import CFSG.LocalAnalysis.StandardType.GGFFTen
import CFSG.RankThree.PartTwo.Sec21.FF81P51Ten

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.StandardType.FF81

open Matrix
open CFSG.RankThree.PartTwo.Sec21.FF79 (Nor)
open CFSG.RankThree.PartTwo.Sec21.FF81 (autOrder)
open CFSG.RankThree.PartTwo.Sec21.FF81.P51 (V Mat GL4 e Hyp Om mA mB W cfgOf)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

theorem xs_mem_Bt {G : Type} [Group G] {K : Subgroup G} (b : G) (z : Fin 3 → K) (i : Fin 4) :
    xs b z i ∈ GGFF.Bt b z := by
  fin_cases i
  · exact GGFF.SettingCore.b_mem_Bt b z
  · exact GGFF.SettingCore.zs_mem_Bt b z 0
  · exact GGFF.SettingCore.zs_mem_Bt b z 1
  · exact GGFF.SettingCore.zs_mem_Bt b z 2

theorem four_mem_Bt {G : Type} [Group G] {K : Subgroup G} (b : G) (z : Fin 3 → K) (k : ℕ)
    (w : Fin 3 → ZMod 3) : b ^ k * vecElt (GGFF.zs z) w ∈ GGFF.Bt b z :=
  (GGFF.Bt b z).mul_mem ((GGFF.Bt b z).pow_mem (GGFF.SettingCore.b_mem_Bt b z) k)
    (GGFF.SettingCore.tor_le_Bt b z (GGFF.vecElt_mem_tor (GGFF.zs z) w))

theorem zeta_mem_Bt {G : Type} [Group G] {K : Subgroup G} (b : G) (z : Fin 3 → K) :
    GGFF.zetaOf (GGFF.zs z) ∈ GGFF.Bt b z :=
  (GGFF.Bt b z).mul_mem ((GGFF.Bt b z).mul_mem (GGFF.SettingCore.zs_mem_Bt b z 0)
    (GGFF.SettingCore.zs_mem_Bt b z 1)) (GGFF.SettingCore.zs_mem_Bt b z 2)

structure BCoordModel {G : Type} [Group G] {K : Subgroup G} (b : G) (z : Fin 3 → K)
    (Γ : Subgroup GL4) (cv : G → V) : Prop where
  hyp : Hyp Γ
  inj : ∀ x ∈ GGFF.Bt b z, ∀ y ∈ GGFF.Bt b z, cv x = cv y → x = y
  mul : ∀ x ∈ GGFF.Bt b z, ∀ y ∈ GGFF.Bt b z, cv (x * y) = cv x + cv y
  basis : ∀ i, cv (xs b z i) = e i
  of_nor : ∀ n ∈ Nor (GGFF.Bt b z), ∃ g ∈ Γ, ∀ i, (g : Mat) *ᵥ e i = cv (n * xs b z i * n⁻¹)
  to_nor : ∀ g ∈ Γ, ∃ n ∈ Nor (GGFF.Bt b z), ∀ i, (g : Mat) *ᵥ e i = cv (n * xs b z i * n⁻¹)

theorem BCoordModel.cv_one {G : Type} [Group G] {K : Subgroup G} {b : G} {z : Fin 3 → K}
    {Γ : Subgroup GL4} {cv : G → V} (hM : BCoordModel b z Γ cv) : cv 1 = 0 := by
  have h := hM.mul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem exists_bCoordModel_cases {G : Type} [Group G] [Finite G]
    {b : G} {K : Subgroup G} {z : Fin 3 → K} (h : GGFF.Setting b K z) (hN : GGFF.ModelN K z)
    (hchar : CFSG.Open.IsCharTwoType G) :
    ∃ (Γ : Subgroup GL4) (cv : G → V), BCoordModel b z Γ cv ∧
      (((cfgOf Γ).1 = mA ∧ autOrder (GGFF.Bt b z) = 384) ∨
        ((cfgOf Γ).1 = mB ∧ W (cfgOf Γ) ∧ autOrder (GGFF.Bt b z) = 1152)) := by
  open CFSG.RankThree.PartTwo.Sec21.FF81 CFSG.RankThree.PartTwo.Sec21.FF81.P51T
    CFSG.RankThree.PartTwo.Sec21.FF81.P51 in
  have hH0 := h.hasH0
  have : CFSG.IsElementaryAbelian 3 (GGFF.Bt b z) := hH0.1.1
  obtain ⟨β, hβ⟩ := exists_basis (B := GGFF.Bt b z) hH0.1.2 hH0.2.1
  have hyp := P51T.hyp_of hH0 h.stab h.meetB β hβ
  have h5 := ne_mC_mE hyp (h.fiveInv β hβ)
  set Γ := (ρU β).range with hΓdef
  have hcard := card_eq hyp
  have haut : autOrder (GGFF.Bt b z) = Nat.card Γ := autOrder_eq β
  have hOm : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m →
      Om Γ = ↑((nonzeroL.filter fun v => m (tab v).1).toFinset) := by
    intro m hm
    ext v
    rw [om_iff hyp, hm]
    simp
  have hautm : ∀ m : Fin 7 → Bool, (m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) →
      (cfgOf Γ).1 = m → autOrder (GGFF.Bt b z) = 96 * lineCount m := by
    intro m hm hcm
    rw [haut, hcard, hOm m hcm, Set.ncard_coe_finset, vecCount m hm]
    ring
  have hcol : ∀ (n : G) (hn : n ∈ Nor (GGFF.Bt b z)) (i : Fin 4),
      ((ρU β ⟨n, hn⟩ : GL4) : Mat) *ᵥ e i = cvG β (n * xs b z i * n⁻¹) := fun n hn i => by
    rw [coe_ρU, ρM_col]
    exact congrArg (fun x => cvG β (n * x * n⁻¹)) (hβ i)
  have hM : BCoordModel b z Γ (cvG β) :=
    { hyp := hyp
      inj := fun x hx y hy => cvG_inj β hx hy
      mul := fun x hx y hy => cvG_mul β hx hy
      basis := fun i => by
        have h1 : cvG β ((Additive.toMul (β i) : GGFF.Bt b z) : G) = e i := by
          rw [cvG_of_mem β (Additive.toMul (β i)).2]
          exact cv_basis β i
        rw [show xs b z i = ((Additive.toMul (β i) : GGFF.Bt b z) : G) from (hβ i).symm]
        exact h1
      of_nor := fun n hn => ⟨ρU β ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩, hcol n hn⟩
      to_nor := fun g hg => by
        obtain ⟨⟨n, hn⟩, rfl⟩ := hg
        exact ⟨n, hn, hcol n hn⟩ }
  refine ⟨Γ, cvG β, hM, ?_⟩
  rcases cfgOf_good hyp with hA | ⟨hB, hW⟩ | ⟨hC, -⟩ | hD | hE
  · exact Or.inl ⟨hA, by rw [hautm mA (Or.inl rfl) hA, lineCount_mA]⟩
  · exact Or.inr ⟨hB, hW, by rw [hautm mB (by simp) hB, lineCount_mB]⟩
  · exact absurd hC h5.1
  · exact absurd (by rw [hautm mD (by simp) hD, lineCount_mD]) (h.autOrder_ne_1440 hN hchar)
  · exact absurd hE h5.2

theorem BCoordModel.cv_xs_pow {G : Type} [Group G] {K : Subgroup G} {b : G} {z : Fin 3 → K}
    {Γ : Subgroup GL4} {cv : G → V} (hM : BCoordModel b z Γ cv) (i : Fin 4) (k : ℕ) :
    cv (xs b z i ^ k) = (k : ZMod 3) • e i := by
  induction k with
  | zero => simp [hM.cv_one]
  | succ k ih =>
    rw [pow_succ, hM.mul _ ((GGFF.Bt b z).pow_mem (xs_mem_Bt b z i) k) _ (xs_mem_Bt b z i), ih,
      hM.basis i]
    push_cast
    rw [add_smul, one_smul]

theorem BCoordModel.xs_pow_three {G : Type} [Group G] {K : Subgroup G} {b : G} {z : Fin 3 → K}
    {Γ : Subgroup GL4} {cv : G → V} (hM : BCoordModel b z Γ cv) (i : Fin 4) :
    xs b z i ^ 3 = 1 := by
  refine hM.inj _ ((GGFF.Bt b z).pow_mem (xs_mem_Bt b z i) 3) 1 (GGFF.Bt b z).one_mem ?_
  rw [hM.cv_xs_pow i 3, hM.cv_one]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  rw [h3, zero_smul]

theorem BCoordModel.cv_four {G : Type} [Group G] {K : Subgroup G} {b : G} {z : Fin 3 → K}
    {Γ : Subgroup GL4} {cv : G → V} (hM : BCoordModel b z Γ cv) (ε : ZMod 3)
    (w : Fin 3 → ZMod 3) : cv (b ^ ε.val * vecElt (GGFF.zs z) w) = ![ε, w 0, w 1, w 2] := by
  have p0 : cv (b ^ ε.val) = ε • e 0 := by
    simpa [ZMod.natCast_zmod_val] using hM.cv_xs_pow 0 ε.val
  have p1 : cv (GGFF.zs z 0 ^ (w 0).val) = w 0 • e 1 := by
    simpa [ZMod.natCast_zmod_val] using hM.cv_xs_pow 1 (w 0).val
  have p2 : cv (GGFF.zs z 1 ^ (w 1).val) = w 1 • e 2 := by
    simpa [ZMod.natCast_zmod_val] using hM.cv_xs_pow 2 (w 1).val
  have p3 : cv (GGFF.zs z 2 ^ (w 2).val) = w 2 • e 3 := by
    simpa [ZMod.natCast_zmod_val] using hM.cv_xs_pow 3 (w 2).val
  have m0 : b ^ ε.val ∈ GGFF.Bt b z := (GGFF.Bt b z).pow_mem (xs_mem_Bt b z 0) _
  have m1 : GGFF.zs z 0 ^ (w 0).val ∈ GGFF.Bt b z := (GGFF.Bt b z).pow_mem (xs_mem_Bt b z 1) _
  have m2 : GGFF.zs z 1 ^ (w 1).val ∈ GGFF.Bt b z := (GGFF.Bt b z).pow_mem (xs_mem_Bt b z 2) _
  have m3 : GGFF.zs z 2 ^ (w 2).val ∈ GGFF.Bt b z := (GGFF.Bt b z).pow_mem (xs_mem_Bt b z 3) _
  unfold vecElt
  rw [hM.mul _ m0 _ ((GGFF.Bt b z).mul_mem ((GGFF.Bt b z).mul_mem m1 m2) m3),
    hM.mul _ ((GGFF.Bt b z).mul_mem m1 m2) _ m3, hM.mul _ m1 _ m2, p0, p1, p2, p3]
  ext j
  fin_cases j <;> simp [e]

theorem BCoordModel.cv_zeta {G : Type} [Group G] {K : Subgroup G} {b : G} {z : Fin 3 → K}
    {Γ : Subgroup GL4} {cv : G → V} (hM : BCoordModel b z Γ cv) :
    cv (GGFF.zetaOf (GGFF.zs z)) = e 1 + e 2 + e 3 := by
  have h1 : GGFF.zs z 0 ∈ GGFF.Bt b z := xs_mem_Bt b z 1
  have h2 : GGFF.zs z 1 ∈ GGFF.Bt b z := xs_mem_Bt b z 2
  have h3 : GGFF.zs z 2 ∈ GGFF.Bt b z := xs_mem_Bt b z 3
  have c1 : cv (GGFF.zs z 0) = e 1 := hM.basis 1
  have c2 : cv (GGFF.zs z 1) = e 2 := hM.basis 2
  have c3 : cv (GGFF.zs z 2) = e 3 := hM.basis 3
  unfold GGFF.zetaOf
  rw [hM.mul _ ((GGFF.Bt b z).mul_mem h1 h2) _ h3, hM.mul _ h1 _ h2, c1, c2, c3]

theorem BCoordModel.conj_iff_mem_Om {G : Type} [Group G] [Finite G] {K : Subgroup G} {b : G}
    {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V} (h : GGFF.SettingCore b K z)
    (hM : BCoordModel b z Γ cv) {x : G} (hx : x ∈ GGFF.Bt b z) :
    (∃ g : G, g * b * g⁻¹ = x) ↔ cv x ∈ Om Γ := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn, hnb⟩ := h.fusion hx hg
    obtain ⟨g', hg', hcol⟩ := hM.of_nor n hn
    exact ⟨g', hg', by rw [hcol 0]; show cv (n * b * n⁻¹) = cv x; rw [hnb]⟩
  · rintro ⟨g, hg, hgx⟩
    obtain ⟨n, hn, hcol⟩ := hM.to_nor g hg
    have hnb : n * b * n⁻¹ ∈ GGFF.Bt b z :=
      (Subgroup.mem_normalizer_iff.mp hn b).mp (xs_mem_Bt b z 0)
    refine ⟨n, hM.inj _ hnb _ hx ?_⟩
    rw [← hgx, hcol 0]
    rfl

end CFSG.StandardType.FF81

end
