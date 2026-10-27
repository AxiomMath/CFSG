module

public import CFSG.Quasithin.Vol2.Ch11SecD557J
public import CFSG.Quasithin.Background.G13Perm
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups IsMulCommutative commutatorElement

variable {G : Type} [Group G] {n : ℕ} {L K V V₁ : Subgroup G}

theorem inf_centralizer_eq_bot_of_natData (D : NatData3 n L K V V₁) :
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvC⟩
  set w := Multiplicative.toAdd (D.ψ ⟨v, hvV⟩) with hw
  have hfix : ∀ A : SL(3, GaloisField 2 n), A • w = w := by
    intro A
    obtain ⟨l, rfl⟩ := D.surj A
    have h1 := D.equiv l ⟨v, hvV⟩
    have h2 : conjAct V ⟨l, D.hnorm l.2⟩ ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
      apply Subtype.ext
      rw [conjAct_coe_apply, Subgroup.mem_centralizer_iff.mp hvC l l.2, mul_inv_cancel_right]
    rw [h2, natAct3_apply] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at h3
    exact h3.symm
  have h1 := congrFun (hfix (tq 1 0)) 0
  have h2 := congrFun (hfix (tq 0 1)) 0
  have h3 := congrFun (hfix (CFSG.Quasithin.G1.wS (GaloisField 2 n) (by decide : (0 : Fin 3) ≠ 1)))
    0
  rw [tq_smul] at h1 h2
  rw [CFSG.Quasithin.G1.wS_smul, Equiv.swap_apply_left] at h3
  simp only [Matrix.cons_val_zero, one_mul, zero_mul, add_zero, add_eq_left] at h1 h2
  have hw0 : w = 0 := by
    funext i
    fin_cases i
    · exact h3.symm.trans h1
    · exact h1
    · exact h2
  have hψ : D.ψ ⟨v, hvV⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [← hw, hw0, toAdd_one]
  have h4 : (⟨v, hvV⟩ : ↥V) = 1 := D.ψ.injective (hψ.trans (map_one _).symm)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h4)

variable [Finite G]

theorem le_sup_centralizer_of_I16 (hI16 : ASInputs.AS_I_1_6) (hn : 1 < n)
    (D : NatData3 n L K V V₁) {S : Subgroup G} (hVS : V ≤ S)
    (hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hSsq : ∀ a ∈ S, a ^ 2 = 1)
    (hLS : ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ * s⁻¹ ∈ V)
    (hKS : ∀ k ∈ L, k ∈ K → ∀ s ∈ S, k * s * k⁻¹ = s) (hVL : V ≤ ⁅V, L⁆) :
    S ≤ V ⊔ (S ⊓ Subgroup.centralizer (L : Set G)) := by
  intro s hs
  set W := V ⊔ Subgroup.zpowers s with hWdef
  have hWS : W ≤ S := sup_le hVS (Subgroup.zpowers_le.mpr hs)
  have : IsMulCommutative ↥W :=
    ⟨⟨fun a b => Subtype.ext (hScomm a (hWS a.2) b (hWS b.2))⟩⟩
  have hWdesc : ∀ w ∈ W, w ∈ V ∨ s * w ∈ V := by
    let B : Subgroup G :=
      { carrier := {w | w ∈ S ∧ (w ∈ V ∨ s * w ∈ V)}
        one_mem' := ⟨S.one_mem, Or.inl V.one_mem⟩
        mul_mem' := fun {a b} ⟨haS, ha⟩ ⟨hbS, hb⟩ => by
          refine ⟨S.mul_mem haS hbS, ?_⟩
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (V.mul_mem ha hb)
          · right
            have e : s * (a * b) = a * (s * b) := by
              rw [← mul_assoc, ← mul_assoc, hScomm s hs a haS]
            rw [e]
            exact V.mul_mem ha hb
          · right
            rw [← mul_assoc]
            exact V.mul_mem ha hb
          · left
            have e : a * b = (s * a) * (s * b) := by
              have hs2 : s * s = 1 := by rw [← pow_two]; exact hSsq s hs
              rw [show (s * a) * (s * b) = s * (a * s) * b by group, ← hScomm s hs a haS,
                show s * (s * a) * b = (s * s) * a * b by group, hs2, one_mul]
            rw [e]
            exact V.mul_mem ha hb
        inv_mem' := fun {a} ⟨haS, ha⟩ => by
          refine ⟨S.inv_mem haS, ?_⟩
          rcases ha with ha | ha
          · exact Or.inl (V.inv_mem ha)
          · right
            have hs2 : s⁻¹ = s := by
              rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hSsq s hs
            have e : s * a⁻¹ = (s * a)⁻¹ := by
              rw [mul_inv_rev, hs2]
              exact (hScomm s hs _ (S.inv_mem haS))
            rw [e]
            exact V.inv_mem ha }
    have hsB : s ∈ B := ⟨hs, Or.inr (by rw [← pow_two, hSsq s hs]; exact V.one_mem)⟩
    have hWB : W ≤ B := sup_le (fun v hv => ⟨hVS hv, Or.inl hv⟩) (Subgroup.zpowers_le.mpr hsB)
    exact fun w hw => (hWB hw).2
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    A4.mem_normalizer_of_conj_mem fun w hw => by
      have e : l * w * l⁻¹ = (l * w * l⁻¹ * w⁻¹) * w := by group
      rw [e]
      exact W.mul_mem (Subgroup.mem_sup_left (hLS l hl w (hWS hw))) hw
  have hcommV : commV (autOn L W) = V.subgroupOf W := by
    refine le_antisymm ?_ fun u hu => ?_
    · rw [commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, w, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, conjAct_coe_apply,
        Subgroup.coe_inv]
      exact hLS x hx w (hWS w.2)
    · have hle : ⁅V, L⁆ ≤ (commV (autOn L W)).map W.subtype := by
        rw [Subgroup.commutator_le]
        intro v hv l hl
        have hvW : v ∈ W := Subgroup.mem_sup_left hv
        have hgen : (autOnHom hLW ⟨l, hl⟩ : MulAut ↥W) ⟨v, hvW⟩ * (⟨v, hvW⟩ : ↥W)⁻¹ ∈
            commV (autOn L W) := Subgroup.subset_closure ⟨_, (autOnHom hLW ⟨l, hl⟩).2, _, rfl⟩
        refine ⟨_, (commV (autOn L W)).inv_mem hgen, ?_⟩
        rw [map_inv, map_mul, Subgroup.coe_subtype, autOnHom_apply]
        show (l * v * l⁻¹ * v⁻¹)⁻¹ = ⁅v, l⁆
        rw [commutatorElement_def]
        group
      obtain ⟨u', hu', hu'u⟩ := hle (hVL (Subgroup.mem_subgroupOf.mp hu))
      rwa [← Subtype.ext hu'u]
  by_cases hfix : fixV (autOn L W) = ⊥
  ·
    have hmod : ASInputs.I16Module (autOn L W) (commV (autOn L W)) ⊥ 0 :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl, by
        rw [hcommV]
        exact binaryNaturalSL_autOn (by omega) D (le_sup_left : V ≤ W) hLW
          fun k hk hkK w hw => hKS k hk hkK w (hWS hw)⟩))))
    have hidx := (hI16 ↥W (fun w => Subtype.ext (hSsq w (hWS w.2))) (autOn L W) 0).2 hfix hmod
    have htop : commV (autOn L W) = ⊤ := Subgroup.index_eq_one.mp (by
      have h1 := Subgroup.index_ne_zero_of_finite (H := commV (autOn L W))
      rw [pow_zero] at hidx
      omega)
    have hsW : (⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩ : ↥W) ∈
        commV (autOn L W) := htop ▸ Subgroup.mem_top _
    rw [hcommV, Subgroup.mem_subgroupOf] at hsW
    exact Subgroup.mem_sup_left hsW
  ·
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfix
    have hwC : ((w : ↥W) : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val ((mem_fixV.mp hw) _ (autOnHom hLW ⟨l, hl⟩).2)
      rw [autOnHom_apply] at h1
      calc l * ((w : ↥W) : G) = l * w * l⁻¹ * l := by group
        _ = w * l := by rw [h1]
    rcases hWdesc _ (w : ↥W).2 with hwV | hwV
    · exfalso
      have h1 : ((w : ↥W) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hwV, hwC⟩
      rw [inf_centralizer_eq_bot_of_natData D, Subgroup.mem_bot] at h1
      exact hw1 (Subtype.ext (Subtype.ext h1))
    · have e : s = (s * w) * (w : G)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwV) (Subgroup.mem_sup_right
        ⟨hWS (Subgroup.inv_mem _ (w : ↥W).2), Subgroup.inv_mem _ hwC⟩)

end CFSG.Quasithin.Vol2.Ch11.SecD
