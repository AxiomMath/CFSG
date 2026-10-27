module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T2L

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem mul_mem_iff_relIndex_two {Y W : Subgroup G} (h : Y.relIndex W = 2) {a b : G}
    (ha : a ∈ W) (hb : b ∈ W) : a * b ∈ Y ↔ (a ∈ Y ↔ b ∈ Y) := by
  have := Subgroup.mul_mem_iff_of_index_two (H := Y.subgroupOf W) h (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [Subgroup.mem_subgroupOf] using this

omit [Finite G] in
theorem relIndex_ne_zero' [Finite G] (A W : Subgroup G) : A.relIndex W ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem eq_of_relIndex_le_two {A B W : Subgroup G} (hA : A.relIndex W ≤ 2) (hAB : A ≤ B)
    (hBW : B ≤ W) (hne : B ≠ W) : A = B ∧ B.relIndex W = 2 := by
  have h := Subgroup.relIndex_mul_relIndex A B W hAB hBW
  have hB1 : B.relIndex W ≠ 1 := fun h1 => hne (le_antisymm hBW (Subgroup.relIndex_eq_one.mp h1))
  have hB0 : B.relIndex W ≠ 0 := relIndex_ne_zero' B W
  have hA0 : A.relIndex W ≠ 0 := relIndex_ne_zero' A W
  have hdvd : B.relIndex W ∣ A.relIndex W := ⟨A.relIndex B, by rw [← h, mul_comm]⟩
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hdvd
  have hB2 : B.relIndex W = 2 := by omega
  refine ⟨?_, hB2⟩
  have hAW : A.relIndex W = 2 := by
    have hpos : 0 < A.relIndex B := Nat.pos_of_ne_zero (relIndex_ne_zero' A B)
    rw [hB2] at h
    nlinarith
  have h1 : A.relIndex B = 1 := by
    rw [hAW, hB2] at h
    omega
  exact le_antisymm hAB (Subgroup.relIndex_eq_one.mp h1)

omit [Finite G] in
theorem Wl_smul (g : ↥(H ⊔ M)) (l : Geo H M) : Wl (g • l) = conjSub (g : G) (Wl l) := by
  unfold Wl
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs l := (smul_mem_nbrs_iff' g).mp hδ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs l) => Vn δ)
      δ' hδ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs (g • l)) => Vn δ)
      (g • δ) ((smul_mem_nbrs_iff' g).mpr hδ) le_rfl

theorem exists_Qv_smul (hS : Sit H M S) {β l δ δ'' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hδ : l ∈ nbrs δ) (hδ'' : δ'' ∈ nbrs l) (hne : δ ≠ β) (hne'' : δ'' ≠ β) :
    ∃ q : ↥(H ⊔ M), (q : G) ∈ Qv β ∧ q • δ = δ'' := by
  by_cases hd : δ'' = δ
  · exact ⟨1, (Qv β).one_mem, by simp [hd]⟩
  obtain ⟨g, hg, hgδ, hgQ⟩ := swap_nbrs hS hβ hl hδ hne hδ'' hne''
  have hgQ := hgQ hd
  have hsup : (g : G) ∈ Qv l ⊔ Qv β := by
    rw [sup_comm, ← stab_inf_eq hS hβ hl]; exact hg
  have hN : Qv β ≤ Subgroup.normalizer ((Qv l : Subgroup G) : Set G) :=
    (Qv_le_stab hS hl).trans (le_normalizer_pCoreOf 2 (stab l))
  obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp hsup
  have hbl : b ∈ stab l := Qv_le_stab hS hl hb
  have hbG : b ∈ H ⊔ M := stab_le β (pCoreOf_le 2 _ hb)
  have haG : a ∈ H ⊔ M := stab_le l (pCoreOf_le 2 _ ha)
  have hδl : δ ∈ nbrs l := mem_nbrs_symm.mp hδ
  have hbδ : (⟨b, hbG⟩ : ↥(H ⊔ M)) • δ ∈ nbrs l := smul_mem_nbrs_of_stab hbl hδl
  have hag : (⟨a, haG⟩ : ↥(H ⊔ M)) • ((⟨b, hbG⟩ : ↥(H ⊔ M)) • δ) = (⟨b, hbG⟩ : ↥(H ⊔ M)) • δ :=
    smul_eq_of_mem_stab (Qv_le_stab hS hbδ ha)
  have hge : g = ⟨a, haG⟩ * ⟨b, hbG⟩ := Subtype.ext hab
  refine ⟨⟨b, hbG⟩, hb, ?_⟩
  rw [← hgδ, hge, mul_smul, hag]

@[expose] def HypAt (β l : Geo H M) (Y : Subgroup G) : Prop :=
  Vn β ≤ Y ∧ Y ≤ Wl l ∧ Y.relIndex (Wl l) = 2 ∧ Qv β ≤ Subgroup.normalizer (Y : Set G)

omit [Finite G] in
theorem le_normalizer_of_forall {T Y : Subgroup G} (h : ∀ g ∈ T, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    T ≤ Subgroup.normalizer (Y : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (T.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem Vn_not_le_of_hyp (hS : Sit H M S) {β l δ : Geo H M} {Y : Subgroup G}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hY : HypAt β l Y) (hδ : δ ∈ nbrs l)
    (hne : δ ≠ β) : ¬ Vn δ ≤ Y := by
  intro hle
  have hW : Wl l ≤ Y := Wl_le fun ρ hρ => by
    by_cases hρβ : ρ = β
    · subst hρβ; exact hY.1
    obtain ⟨q, hq, hqδ⟩ := exists_Qv_smul hS hβ hl (mem_nbrs_symm.mpr hδ) hρ hne hρβ
    rw [← hqδ, Vn_smul]
    calc conjSub (q : G) (Vn δ) ≤ conjSub (q : G) Y := conjSub_mono _ hle
      _ = Y := conjSub_eq_of_mem_normalizer (hY.2.2.2 hq)
  have h1 := Subgroup.relIndex_eq_one.mpr hW
  rw [hY.2.2.1] at h1
  omega

omit [Finite G] in
theorem hyp_smul {β l : Geo H M} {Y : Subgroup G} (hY : HypAt β l Y) (g : ↥(H ⊔ M))
    (hg : (g : G) ∈ stab β) : HypAt β (g • l) (conjSub (g : G) Y) := by
  have hgβ : g • β = β := smul_eq_of_mem_stab hg
  have hV : conjSub (g : G) (Vn β) = Vn β := by rw [← Vn_smul, hgβ]
  have hQ : conjSub (g : G) (Qv β) = Qv β := by rw [← Qv_smul, hgβ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Vn β = conjSub (g : G) (Vn β) := hV.symm
      _ ≤ conjSub (g : G) Y := conjSub_mono _ hY.1
  · rw [Wl_smul]; exact conjSub_mono _ hY.2.1
  · rw [Wl_smul, relIndex_conjSub]; exact hY.2.2.1
  · rw [conjSub_normalizer]
    calc Qv β = conjSub (g : G) (Qv β) := hQ.symm
      _ ≤ _ := conjSub_mono _ hY.2.2.2

structure Inputs (H M : Subgroup G) : Prop where
  maximal : ∀ β l : Geo H M, vtype β = false → l ∈ nbrs β → ∀ P : Subgroup G, P ≤ stab β →
    stab β ⊓ stab l ≤ P → P = stab β ∨ P ≤ Subgroup.normalizer (Zv l : Set G)
  plane : ∀ δ l : Geo H M, vtype δ = false → l ∈ nbrs δ →
    (⁅Vn δ, stab δ ⊓ stab l⁆ ⊔ Zv l).relIndex (Vn δ) ≤ 2

theorem hyperplane_unique (I : Inputs H M) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) {Y₁ Y₂ : Subgroup G} (h1 : Y₁ ≤ Vn δ) (h2 : Y₂ ≤ Vn δ)
    (r1 : Y₁.relIndex (Vn δ) = 2) (r2 : Y₂.relIndex (Vn δ) = 2)
    (z1 : Zv l ≤ Y₁) (z2 : Zv l ≤ Y₂)
    (n1 : stab δ ⊓ stab l ≤ Subgroup.normalizer (Y₁ : Set G))
    (n2 : stab δ ⊓ stab l ≤ Subgroup.normalizer (Y₂ : Set G)) : Y₁ = Y₂ := by
  have key : ∀ Y : Subgroup G, Y ≤ Vn δ → Y.relIndex (Vn δ) = 2 → Zv l ≤ Y →
      stab δ ⊓ stab l ≤ Subgroup.normalizer (Y : Set G) →
      ⁅Vn δ, stab δ ⊓ stab l⁆ ⊔ Zv l = Y := by
    intro Y hY hr hz hn
    have hA : ⁅Vn δ, stab δ ⊓ stab l⁆ ⊔ Zv l ≤ Y := by
      refine sup_le (Subgroup.commutator_le.mpr fun v hv d hd => ?_) hz
      have hdV : d * v⁻¹ * d⁻¹ ∈ Vn δ :=
        (Subgroup.mem_normalizer_iff.mp (Vn_normal δ hd.1) _).mp ((Vn δ).inv_mem hv)
      have e : ⁅v, d⁆ = v * (d * v⁻¹ * d⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e, mul_mem_iff_relIndex_two hr hv hdV, ← Subgroup.mem_normalizer_iff.mp (hn hd) v⁻¹,
        Subgroup.inv_mem_iff]
    exact (eq_of_relIndex_le_two (I.plane δ l hδ hl) hA hY (fun h => by
      rw [h] at hr; simp at hr)).1
  rw [← key Y₁ h1 r1 z1 n1, ← key Y₂ h2 r2 z2 n2]

theorem hyp_inf_Vn (hS : Sit H M S) (hN : S35.II.NbarFull H M) {β l ρ : Geo H M} {Y : Subgroup G}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hY : HypAt β l Y) (hρ : ρ ∈ nbrs l)
    (hne : ρ ≠ β) :
    (Y ⊓ Vn ρ).relIndex (Vn ρ) = 2 ∧ Zv l ≤ Y ⊓ Vn ρ ∧
      stab ρ ⊓ stab l ≤ Subgroup.normalizer ((Y ⊓ Vn ρ : Subgroup G) : Set G) := by
  have hl3 : vtype l = true := vtype_nbr_S5 hβ hl
  have hρ5 : vtype ρ = false := vtype_nbr_S3 hl3 hρ
  have hlρ : l ∈ nbrs ρ := mem_nbrs_symm.mpr hρ
  refine ⟨?_, le_inf ((Zv_le_Vn hl).trans hY.1) (Zv_le_Vn hlρ), ?_⟩
  · rw [Subgroup.inf_relIndex_right]
    have hle : Y.relIndex (Vn ρ) ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := Y) (Vn_le_Wl hρ) (relIndex_ne_zero' Y _)
      rwa [hY.2.2.1] at this
    have h1 : Y.relIndex (Vn ρ) ≠ 1 := fun h =>
      Vn_not_le_of_hyp hS hβ hl hY hρ hne (Subgroup.relIndex_eq_one.mp h)
    have h0 := relIndex_ne_zero' Y (Vn ρ)
    omega
  · have hZ : Zv l ≤ Y ⊓ Vn ρ := le_inf ((Zv_le_Vn hl).trans hY.1) (Zv_le_Vn hlρ)
    have hQ1 : Qv β ⊓ Qv l ≤ Subgroup.normalizer ((Y ⊓ Vn ρ : Subgroup G) : Set G) := fun g hg =>
      mem_normalizer_inf (hY.2.2.2 hg.1) (Vn_normal ρ (Qv_le_stab hS hρ hg.2))
    have hQ2 : Qv ρ ≤ Subgroup.normalizer ((Y ⊓ Vn ρ : Subgroup G) : Set G) := by
      refine le_normalizer_of_forall fun g hg v hv => ?_
      have hgs : g ∈ stab ρ := pCoreOf_le 2 _ hg
      have hcomm : g * v * g⁻¹ * v⁻¹ ∈ Zv ρ := by
        have h := Subgroup.commutator_mem_commutator hg hv.2
        rw [Subgroup.commutator_comm, Std.comm_Vn_Qv hS hρ5] at h
        simpa [commutatorElement_def] using h
      have hz : g * v * g⁻¹ * v⁻¹ ∈ Y ⊓ Vn ρ := hZ (Zv_le_Zv_of_nbr hS hρ5 hlρ hcomm)
      have e : g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v := by group
      rw [e]
      exact (Y ⊓ Vn ρ).mul_mem hz hv
    exact (hN β l ρ hβ hl hlρ hne).trans (sup_le hQ1 hQ2)

theorem hyp_unique (hS : Sit H M S) (hN : S35.II.NbarFull H M) (I : Inputs H M)
    {β l : Geo H M} {Y₁ Y₂ : Subgroup G} (hβ : vtype β = false) (hl : l ∈ nbrs β)
    (h1 : HypAt β l Y₁) (h2 : HypAt β l Y₂) : Y₁ = Y₂ := by
  have hl3 : vtype l = true := vtype_nbr_S5 hβ hl
  have hmain : ∀ {Y₁ Y₂ : Subgroup G}, HypAt β l Y₁ → HypAt β l Y₂ → Y₁ ≤ Y₂ := by
    intro Y₁ Y₂ h1 h2
    let Ξ : Subgroup G :=
      { carrier := {w | w ∈ Wl l ∧ (w ∈ Y₁ ↔ w ∈ Y₂)}
        one_mem' := ⟨(Wl l).one_mem, by simp⟩
        mul_mem' := fun {x y} hx hy => ⟨(Wl l).mul_mem hx.1 hy.1, by
          rw [mul_mem_iff_relIndex_two h1.2.2.1 hx.1 hy.1,
            mul_mem_iff_relIndex_two h2.2.2.1 hx.1 hy.1, hx.2, hy.2]⟩
        inv_mem' := fun {x} hx => ⟨(Wl l).inv_mem hx.1, by simp [hx.2]⟩ }
    have hW : Wl l ≤ Ξ := Wl_le fun ρ hρ w hw => by
      refine ⟨Vn_le_Wl hρ hw, ?_⟩
      by_cases hρβ : ρ = β
      · subst hρβ; exact iff_of_true (h1.1 hw) (h2.1 hw)
      have hρ5 : vtype ρ = false := vtype_nbr_S3 hl3 hρ
      have hlρ : l ∈ nbrs ρ := mem_nbrs_symm.mpr hρ
      obtain ⟨r1, z1, n1⟩ := hyp_inf_Vn hS hN hβ hl h1 hρ hρβ
      obtain ⟨r2, z2, n2⟩ := hyp_inf_Vn hS hN hβ hl h2 hρ hρβ
      have heq := hyperplane_unique I hρ5 hlρ inf_le_right inf_le_right r1 r2 z1 z2 n1 n2
      have e1 : w ∈ Y₁ ↔ w ∈ Y₁ ⊓ Vn ρ := ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩
      have e2 : w ∈ Y₂ ↔ w ∈ Y₂ ⊓ Vn ρ := ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩
      rw [e1, e2, heq]
    intro y hy
    exact (hW (h1.2.1 hy)).2.mp hy
  exact le_antisymm (hmain h1 h2) (hmain h2 h1)

end S35.T2L

end F53.Stellmacher

end CFSG.Quasithin
