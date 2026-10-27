module

public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenRoots
public import CFSG.RankThree.GF2n.Stroth80.Sec10Six
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem exists_root_group_of_comm {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y X : Subgroup G} {y : G} (hsy : Sit M Q Z X y)
    (hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, y * v = v * y)
    (hVX : Vt M (LB M Q B) B Z t ⊓ QB X ≤ Q ⊓ QB Y ⊓ QB X)
    {x : G} (hxV : ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hxC : ⁅x, y⁆ ∉ (Q ⊓ QB Y ⊓ QB X) ⊔ Z) :
    ∃ A' : Subgroup G, Ctx M Q Z A' ∧ ⁅x, y⁆ ∈ A' ∧ A' ⊓ QB X = ⊥ ∧
      y ∉ QB A' ∧ y ∈ Subgroup.normalizer (A' : Set G) ∧ ⁅x, y⁆ ≠ 1 := by
  have haZ : ⁅x, y⁆ ∉ Z := fun h => hxC (Subgroup.mem_sup_right h)
  have ha1 : ⁅x, y⁆ ≠ 1 := fun h => haZ (by rw [h]; exact Z.one_mem)
  obtain ⟨A', hA', haA'⟩ := Good101.exists_root_of_mem_Vt H ht hxV haZ
  have haX : ⁅x, y⁆ ∉ QB X := fun h =>
    hxC (Subgroup.mem_sup_left (hVX (Subgroup.mem_inf.mpr ⟨hxV, h⟩)))
  have hXQB : X ≤ QB X := by
    obtain ⟨g, rfl⟩ := hsy.conj
    rw [QB_conj_eq hsy.hyp g]
    exact Subgroup.map_mono hsy.hyp.Z_normal.1
  have hne : A' ≠ X := by
    intro h
    have hmem : ⁅x, y⁆ ∈ X := by rw [← h]; exact haA'
    exact haX (hXQB hmem)
  have hA'X : A' ⊓ QB X = ⊥ := by
    rw [eq_bot_iff]
    intro γ hγ
    rw [Subgroup.mem_bot]
    by_contra hγ1
    exact haX ((hc.hyp.le_QB_of_mem_of_mem_QB hA'.conj hsy.conj hne hγ.1 hγ1 hγ.2) haA')
  have hyA' : y ∉ QB A' := by
    intro h
    exact haX (hc.hyp.le_QB_of_mem_QB hA'.conj hsy.conj hsy.mem hsy.ne_one h haA')
  have hTI : IsTI A' := by
    obtain ⟨g, rfl⟩ := hA'.conj
    exact isTI_conjSubgroup hc.hyp.ti g
  exact ⟨A', hA', haA', hA'X, hyA', Tim77.mem_normalizer_of_commute_of_isTI hTI haA' ha1
    (hyV _ hxV), ha1⟩

private theorem root_group_le_of_mem_C (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {X : Subgroup G} {y : G} (hsy : Sit M Q Z X y) {x : G}
    (hxV : ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t) {A' : Subgroup G} (hA' : Ctx M Q Z A')
    (haA' : ⁅x, y⁆ ∈ A') (ha1 : ⁅x, y⁆ ≠ 1) (hA'X : A' ⊓ QB X = ⊥)
    {D : Subgroup G} (hD : Ctx M Q Z D) (hDC : D ≤ Q ⊓ QB Y ⊓ QB X) :
    D ≤ QB A' ∧ D ≠ A' ∧ y ∈ QB D := by
  have hVD : Vt M (LB M Q B) B Z t ≤ QB D :=
    ht.Vt_le_QB_of_root h34 hspread H hs hD (hDC.trans (inf_le_left.trans inf_le_right))
  have hne : D ≠ A' := by
    intro h
    have hAle : A' ≤ QB X := by rw [← h]; exact hDC.trans inf_le_right
    have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hA'X]
      exact ⟨haA', hAle haA'⟩
    exact ha1 (Subgroup.mem_bot.mp hmem)
  have hAD : A' ≤ QB D :=
    hc.hyp.le_QB_of_mem_of_mem_QB hA'.conj hD.conj (Ne.symm hne) haA' ha1 (hVD hxV)
  exact ⟨hc.hyp.le_QB_of_le_QB hA'.conj hD.conj (Ne.symm hne) hAD, hne,
    Sit.mem_QB_of_le_QB hsy hD (hDC.trans inf_le_right)⟩

private theorem root_witness_conj {M Q Z X : Subgroup G} {y : G} (hsy : Sit M Q Z X y)
    (k : G) : ∃ g, ∃ z ∈ conjSubgroup k Z, z ≠ 1 ∧ g * z * g⁻¹ = y := by
  obtain ⟨g, hg⟩ := hsy.conj
  have hyX : y ∈ conjSubgroup g Z := by rw [← hg]; exact hsy.mem
  have hzg : g⁻¹ * y * g ∈ Z := mem_conjSubgroup.mp hyX
  have hz1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply hsy.ne_one
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  refine ⟨g * k⁻¹, k * (g⁻¹ * y * g) * k⁻¹, ?_, ?_, ?_⟩
  · exact mem_conjSubgroup.mpr (by
      rw [show k⁻¹ * (k * (g⁻¹ * y * g) * k⁻¹) * k = g⁻¹ * y * g by group]
      exact hzg)
  · intro h
    apply hz1
    have := congrArg (fun t => k⁻¹ * t * k) h
    simpa [mul_assoc] using this
  · calc (g * k⁻¹) * (k * (g⁻¹ * y * g) * k⁻¹) * (g * k⁻¹)⁻¹
        = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = y := by group

private theorem conj_root_Rt (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {Y X : Subgroup G} {y : G} {A' D₁ D₂ : Subgroup G} (hD₂ : Ctx M Q Z D₂)
    (hA'X : A' ⊓ QB X = ⊥) (hyN : y ∈ Subgroup.normalizer (A' : Set G))
    (hyA' : y ∉ QB A') (hD₁C : D₁ ≤ Q ⊓ QB Y ⊓ QB X)
    (hD₂C : D₂ ≤ Q ⊓ QB Y ⊓ QB X) (hD₁A' : D₁ ≤ QB A') (hD₂A' : D₂ ≤ QB A')
    (hD₂ne : D₂ ≠ A') (hyD₂ : y ∈ QB D₂) (hne : D₁ ≠ D₂) {k : G}
    (hkZ : conjSubgroup k Z = A') (hkB : conjSubgroup k B = D₁) :
    y ∈ conjSubgroup k M ∧ y ∉ conjSubgroup k Q ∧
      Rt (conjSubgroup k M) (LB (conjSubgroup k M) (conjSubgroup k Q)
        (conjSubgroup k B)) y ≠
        LB (conjSubgroup k M) (conjSubgroup k Q) (conjSubgroup k B) := by
  subst A'
  subst D₁
  have hQBA' : conjSubgroup k Q = QB (conjSubgroup k Z) :=
    (QB_conj_eq hc.hyp k).symm
  have hM' : conjSubgroup k M =
      Subgroup.normalizer ((conjSubgroup k Z : Subgroup G) : Set G) :=
    (normalizer_conj_eq hc.hyp k).symm
  have hD₂'' : Ctx (conjSubgroup k M) (conjSubgroup k Q) (conjSubgroup k Z) D₂ := by
    refine ⟨(hc.conjBy k).hyp, ?_, ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hD₂.conj
      refine ⟨g * k⁻¹, ?_⟩
      rw [hg, conjSubgroup_mul, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
        show g * k⁻¹ * k = g by group]
    · rw [hQBA']; exact hD₂A'
    · exact hD₂ne
  obtain ⟨r, hr, hrD⟩ := Sec10Hyp.rootTrans h34 hspread (H.conjG k) D₂ hD₂''
  have hZ'QB : conjSubgroup k Z ≤ QB (conjSubgroup k Z) := by
    rw [QB_conj_eq hc.hyp k]
    exact Subgroup.map_mono hc.hyp.Z_normal.1
  have hPZ : (QB (conjSubgroup k Z) ⊓ QB X) ⊓ conjSubgroup k Z = ⊥ := by
    rw [inf_comm (QB (conjSubgroup k Z)) (QB X), inf_assoc,
      inf_comm (QB (conjSubgroup k Z)) (conjSubgroup k Z), inf_eq_left.mpr hZ'QB,
      inf_comm, hA'X]
  have hsup : (conjSubgroup k B ⊔ conjSubgroup k Z) ⊓
      (conjSubgroup r (conjSubgroup k B) ⊔ conjSubgroup k Z) = conjSubgroup k Z := by
    rw [hrD]
    exact (hc.conjBy k).hyp.sup_inf_sup_eq (A := conjSubgroup k B) (B := D₂)
      (P := QB (conjSubgroup k Z) ⊓ QB X) (hc.conjBy k).conj hD₂''.conj hne
      (le_inf hD₁A' (hD₁C.trans inf_le_right))
      (le_inf hD₂A' (hD₂C.trans inf_le_right))
      (inf_le_left.trans (le_of_eq hQBA'.symm)) hPZ
  have hyM' : y ∈ conjSubgroup k M := by rw [hM']; exact hyN
  have hyQ' : y ∉ conjSubgroup k Q := by rw [hQBA']; exact hyA'
  have hR : Rt (conjSubgroup k M) (LB (conjSubgroup k M) (conjSubgroup k Q)
      (conjSubgroup k B)) y ≠
      LB (conjSubgroup k M) (conjSubgroup k Q) (conjSubgroup k B) :=
    Sec10Hyp.Rt_ne_LB_of_mem_QB h34 (H.conjG k) hr hsup hyM'
      (by rw [hrD]; exact hyD₂)
  exact ⟨hyM', hyQ', hR⟩

theorem Good101.n_eq_six_of_comm (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (h103b : Stroth103bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    (hge3 : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {X : Subgroup G} {y : G} (hsy : Sit M Q Z X y)
    (hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, y * v = v * y)
    (hVX : Vt M (LB M Q B) B Z t ⊓ QB X ≤ Q ⊓ QB Y ⊓ QB X)
    {D₁ D₂ : Subgroup G} (hD₁ : Ctx M Q Z D₁) (hD₂ : Ctx M Q Z D₂)
    (hD₁C : D₁ ≤ Q ⊓ QB Y ⊓ QB X) (hD₂C : D₂ ≤ Q ⊓ QB Y ⊓ QB X) (hne : D₁ ≠ D₂)
    {x : G} (hxV : ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hxC : ⁅x, y⁆ ∉ (Q ⊓ QB Y ⊓ QB X) ⊔ Z) : n = 6 := by
  obtain ⟨A', hA', haA', hA'X, hyA', hyN, ha1⟩ :=
    exists_root_group_of_comm H ht hsy hyV hVX hxV hxC
  obtain ⟨hD₁A', hD₁ne, hyD₁⟩ :=
    root_group_le_of_mem_C h34 hspread H ht hs hsy hxV hA' haA' ha1 hA'X hD₁ hD₁C
  obtain ⟨hD₂A', hD₂ne, hyD₂⟩ :=
    root_group_le_of_mem_C h34 hspread H ht hs hsy hxV hA' haA' ha1 hA'X hD₂ hD₂C
  obtain ⟨k, hkZ, hkB⟩ :=
    Sec10Hyp.exists_conj_pair h34 hspread H hA'.conj hD₁.conj hD₁A' hD₁ne
  have hfields := conj_root_Rt h34 hspread H hD₂ hA'X hyN hyA' hD₁C hD₂C hD₁A' hD₂A'
    hD₂ne hyD₂ hne hkZ hkB
  have hy101 : Good101 (conjSubgroup k M) (conjSubgroup k Q) (conjSubgroup k Z)
      (conjSubgroup k B) y :=
    ⟨root_witness_conj hsy k, hfields.1, hfields.2.1, by rw [hkB]; exact hyD₁,
      hfields.2.2⟩
  have hy103 : Good103 (conjSubgroup k M) (conjSubgroup k Q) (conjSubgroup k Z)
      (conjSubgroup k B) y :=
    ⟨hy101, h103b G (conjSubgroup k M) (conjSubgroup k Q) (conjSubgroup k Z)
      (conjSubgroup k B) (hc.conjBy k) n (H.conjG k) (noSL2_conjG hge3 k) y hy101⟩
  have hfuse : ∃ g : G, ∃ z ∈ conjSubgroup k Z, z ≠ 1 ∧ g * y * g⁻¹ = y * z := by
    refine ⟨x, ⁅x, y⁆, ?_, ha1, ?_⟩
    · rw [hkZ]; exact haA'
    · calc x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
        _ = y * ⁅x, y⁆ := (hyV ⁅x, y⁆ hxV).symm
  exact ((stroth_10_6b h34 h311a hspread) G (conjSubgroup k M) (conjSubgroup k Q)
    (conjSubgroup k Z) (conjSubgroup k B) (hc.conjBy k) n y (H.conjG k)
    (noSL2_conjG hge3 k) hy103 hfuse).1

end CFSG.RankThree.GF2n.Stroth80
