module

public import CFSG.Quasithin.Vol2.Ch3Sec3ThreeL32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace HatB

variable {G : Type} [Group G]

theorem vPlus_eq_qL_of_hat [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hH : CFSG.Quasithin.IsHatA6Block L)
    (hTC : tC L T = ⊥) : vPlus L T = qL L T := by
  classical
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQle : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hH.1 hTL
  have hUQ : blockU L ≤ qL L T := hUV.trans hVQle
  have hZL : blockZ L = ⊥ := ThreeL32.blockZ_eq_bot h hTL hH.1 hTC
  have hQe : IsElemAbelian 2 (qL L T) := ThreeL32.isElemAbelian_qL h38 h39 h hH.1 hTL hTC
  have hQc : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hQe ha hb
  have hQLU : ⁅qL L T, L⁆ ≤ blockU L := Hyp331.commutator_qL_le_blockU hH.1 hTL
  have hOQ : pCoreOf 2 L ≤ qL L T := ThreeL32.pCoreOf_le_qL hTL
  have hOU : pCoreOf 2 L ≤ Subgroup.centralizer (blockU L : Set G) := by
    rw [← hH.2.2.2]
    exact inf_le_right
  have hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L := fun ℓ hℓ u hu =>
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hℓ)) u).mp hu
  have hMp := Hyp331.mPlus_eq_of_le (L := L) (T := T) hTL
  obtain ⟨-, -, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L := (Subgroup.commutator_mono hVQle le_rfl).trans hQLU
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le T).mpr fun y hy => hy.1.1
  have hVU : vPlus L T = blockU L := by
    refine le_antisymm ?_ hUV
    rw [hV4]
    refine sup_le hVL fun z hz => ?_
    have h1 : z ∈ tC L T := ⟨hZT hz.1, hz.2⟩
    rw [hTC, Subgroup.mem_bot] at h1
    rw [h1]
    exact (blockU L).one_mem
  have hcen : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := hH.2.1.2.1
  obtain ⟨zb, hzb1⟩ : ∃ zb : ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)), zb ≠ 1 := by
    have : Nontrivial ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcen]; norm_num)
    exact exists_ne 1
  obtain ⟨z₀, hz₀⟩ := QuotientGroup.mk_surjective (zb : ↥L ⧸ CFSG.pCore 2 ↥L)
  set z : G := (z₀ : G) with hzdef
  have hzL : z ∈ L := z₀.2
  have hmemO : ∀ x : ↥L, (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 →
      (x : G) ∈ pCoreOf 2 L := by
    intro x hx
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by
      exact (QuotientGroup.eq_one_iff x).mp hx
    exact ⟨x, hx', rfl⟩
  have hzO : z ∉ pCoreOf 2 L := by
    intro hz
    apply hzb1
    apply Subtype.ext
    rw [← hz₀, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
    obtain ⟨x, hx, hxz⟩ := hz
    have : x = z₀ := Subtype.ext hxz
    rw [← this]
    exact hx
  have hcomm : ∀ ℓ ∈ L, ℓ * z * ℓ⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
    intro ℓ hℓ
    have h1 := hmemO (⟨ℓ, hℓ⟩ * z₀ * ⟨ℓ, hℓ⟩⁻¹ * z₀⁻¹) (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hz₀]
      have hc := Subgroup.mem_center_iff.mp zb.2 (QuotientGroup.mk ⟨ℓ, hℓ⟩)
      rw [hc]
      group)
    exact h1
  set W := blockU L ⊓ Subgroup.centralizer ({z} : Set G) with hWdef
  have hkey : ∀ ℓ ∈ L, ∀ w ∈ W, ℓ * w * ℓ⁻¹ ∈ W := by
    intro ℓ hℓ w hw
    refine Subgroup.mem_inf.mpr ⟨hLU ℓ hℓ w hw.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwz : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
    have hp : ℓ⁻¹ * z * ℓ * z⁻¹ ∈ pCoreOf 2 L := by
      simpa using hcomm ℓ⁻¹ (L.inv_mem hℓ)
    have hpw : w * (ℓ⁻¹ * z * ℓ * z⁻¹) = (ℓ⁻¹ * z * ℓ * z⁻¹) * w :=
      Subgroup.mem_centralizer_iff.mp (hOU hp) w hw.1
    calc ℓ * w * ℓ⁻¹ * z = ℓ * (w * (ℓ⁻¹ * z * ℓ * z⁻¹)) * z * ℓ⁻¹ := by group
      _ = ℓ * ((ℓ⁻¹ * z * ℓ * z⁻¹) * w) * z * ℓ⁻¹ := by rw [hpw]
      _ = ℓ * (ℓ⁻¹ * z * ℓ * z⁻¹) * (w * z) * ℓ⁻¹ := by group
      _ = ℓ * (ℓ⁻¹ * z * ℓ * z⁻¹) * (z * w) * ℓ⁻¹ := by rw [hwz]
      _ = z * (ℓ * w * ℓ⁻¹) := by group
  have hWN : L ≤ Subgroup.normalizer (W : Set G) := by
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hkey ℓ hℓ w, fun hw => ?_⟩
    have h1 := hkey ℓ⁻¹ (L.inv_mem hℓ) _ hw
    rwa [show ℓ⁻¹ * (ℓ * w * ℓ⁻¹) * ℓ⁻¹⁻¹ = w by group] at h1
  have hW : W = ⊥ := by
    rcases hH.1.2.2.2.2.2 W (by rw [hZL]; exact bot_le) inf_le_left hWN with hW | hW
    · rw [hW, hZL]
    · exfalso
      apply hzO
      rw [← hH.2.2.2]
      refine ⟨hzL, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      rw [← hW] at hu
      exact (Subgroup.mem_centralizer_singleton_iff.mp hu.2)
  have hW1 : ∀ x ∈ blockU L, x * z = z * x → x = 1 := by
    intro x hx hxz
    have h1 : x ∈ W := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩
    rw [hW, Subgroup.mem_bot] at h1
    exact h1
  let φ : ↥(blockU L) → ↥(blockU L) := fun v =>
    ⟨z * v * z⁻¹ * (v : G)⁻¹, (blockU L).mul_mem (hLU z hzL v v.2) ((blockU L).inv_mem v.2)⟩
  have hφi : Function.Injective φ := by
    intro v v' hvv
    have h1 : z * (v : G) * z⁻¹ * (v : G)⁻¹ = z * (v' : G) * z⁻¹ * (v' : G)⁻¹ :=
      congrArg Subtype.val hvv
    have h2 : (v' : G)⁻¹ * v ∈ blockU L := (blockU L).mul_mem ((blockU L).inv_mem v'.2) v.2
    have h3 : (v' : G)⁻¹ * v * z = z * ((v' : G)⁻¹ * v) := by
      have e : z * ((v' : G)⁻¹ * v) * z⁻¹ = (v' : G)⁻¹ * v := by
        calc z * ((v' : G)⁻¹ * v) * z⁻¹ =
            (z * (v' : G) * z⁻¹)⁻¹ * (z * (v : G) * z⁻¹ * (v : G)⁻¹) * v := by group
          _ = (z * (v' : G) * z⁻¹)⁻¹ * (z * (v' : G) * z⁻¹ * (v' : G)⁻¹) * v := by rw [h1]
          _ = (v' : G)⁻¹ * v := by group
      calc (v' : G)⁻¹ * v * z = (z * ((v' : G)⁻¹ * v) * z⁻¹) * z := by rw [e]
        _ = z * ((v' : G)⁻¹ * v) := by group
    have h4 := hW1 _ h2 h3
    exact Subtype.ext (inv_mul_eq_one.mp h4).symm
  have : Finite ↥(blockU L) := inferInstance
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφi
  have hQU : qL L T ≤ blockU L := by
    intro q hq
    have hcz : z * q * z⁻¹ * q⁻¹ ∈ blockU L := by
      have h1 : ⁅z, q⁆ ∈ ⁅L, qL L T⁆ := Subgroup.commutator_mem_commutator hzL hq
      rw [Subgroup.commutator_comm] at h1
      have h2 := hQLU h1
      rwa [commutatorElement_def] at h2
    obtain ⟨v, hv⟩ := hφs ⟨_, hcz⟩
    have hv' : z * (v : G) * z⁻¹ * (v : G)⁻¹ = z * q * z⁻¹ * q⁻¹ := congrArg Subtype.val hv
    set q' := (v : G)⁻¹ * q with hq'def
    have hq'Q : q' ∈ qL L T := (qL L T).mul_mem ((qL L T).inv_mem (hUQ v.2)) hq
    have hzq : z * q' = q' * z := by
      have e : z * q' * z⁻¹ = q' := by
        calc z * q' * z⁻¹ = (z * (v : G) * z⁻¹)⁻¹ * (z * q * z⁻¹ * q⁻¹) * q := by
              rw [hq'def]
              group
          _ = (z * (v : G) * z⁻¹)⁻¹ * (z * (v : G) * z⁻¹ * (v : G)⁻¹) * q := by rw [hv']
          _ = q' := by
              rw [hq'def]
              group
      calc z * q' = (z * q' * z⁻¹) * z := by group
        _ = q' * z := by rw [e]
    have hzi : z * q'⁻¹ = q'⁻¹ * z := by
      calc z * q'⁻¹ = q'⁻¹ * (q' * z) * q'⁻¹ := by group
        _ = q'⁻¹ * (z * q') * q'⁻¹ := by rw [hzq]
        _ = q'⁻¹ * z := by group
    have hcL : ∀ ℓ ∈ L, ℓ * q' = q' * ℓ := by
      intro ℓ hℓ
      have hcU : ℓ * q' * ℓ⁻¹ * q'⁻¹ ∈ blockU L := by
        have h1 : ⁅ℓ, q'⁆ ∈ ⁅L, qL L T⁆ := Subgroup.commutator_mem_commutator hℓ hq'Q
        rw [Subgroup.commutator_comm] at h1
        have h2 := hQLU h1
        rwa [commutatorElement_def] at h2
      have hp : ℓ⁻¹ * z * ℓ * z⁻¹ ∈ pCoreOf 2 L := by
        simpa using hcomm ℓ⁻¹ (L.inv_mem hℓ)
      have hpq : (ℓ⁻¹ * z * ℓ * z⁻¹) * q' = q' * (ℓ⁻¹ * z * ℓ * z⁻¹) := hQc _ (hOQ hp) _ hq'Q
      have hcz' : ℓ * q' * ℓ⁻¹ * q'⁻¹ * z = z * (ℓ * q' * ℓ⁻¹ * q'⁻¹) := by
        symm
        calc z * (ℓ * q' * ℓ⁻¹ * q'⁻¹) =
            ℓ * (ℓ⁻¹ * z * ℓ * z⁻¹) * (z * q') * ℓ⁻¹ * q'⁻¹ := by group
          _ = ℓ * (ℓ⁻¹ * z * ℓ * z⁻¹) * (q' * z) * ℓ⁻¹ * q'⁻¹ := by rw [hzq]
          _ = ℓ * ((ℓ⁻¹ * z * ℓ * z⁻¹) * q') * z * ℓ⁻¹ * q'⁻¹ := by group
          _ = ℓ * (q' * (ℓ⁻¹ * z * ℓ * z⁻¹)) * z * ℓ⁻¹ * q'⁻¹ := by rw [hpq]
          _ = ℓ * q' * ℓ⁻¹ * (z * q'⁻¹) := by group
          _ = ℓ * q' * ℓ⁻¹ * (q'⁻¹ * z) := by rw [hzi]
          _ = ℓ * q' * ℓ⁻¹ * q'⁻¹ * z := by group
      have h1 := hW1 _ hcU hcz'
      calc ℓ * q' = (ℓ * q' * ℓ⁻¹ * q'⁻¹) * q' * ℓ := by group
        _ = q' * ℓ := by rw [h1, one_mul]
    have hq'1 : q' = 1 := ThreeL32.eq_one_of_mem_centralizer h hTC hq'Q
      (Subgroup.mem_centralizer_iff.mpr hcL)
    have hqv : q = v := by
      rw [hq'def, inv_mul_eq_one] at hq'1
      exact hq'1.symm
    rw [hqv]
    exact v.2
  rw [hVU]
  exact le_antisymm hUQ hQU

@[expose] def Insp3_3_25HatRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → CFSG.Quasithin.IsHatA6Block L →
    (∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2
        (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T)) A →
      A ≤ qL L T) ∧
    (vPlus L T = qL L T →
      (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(vPlus L T)) ∧
      (∀ B : Subgroup G, IsMaxElemAbelian T B → ¬ B ≤ vPlus L T →
        ∃ b ∈ B, vPlus L T ⊓ Subgroup.centralizer (B : Set G) =
          vPlus L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      ∀ B B' : Subgroup G, IsMaxElemAbelian T B → IsMaxElemAbelian T B' →
        ¬ B ≤ vPlus L T → ¬ B' ≤ vPlus L T → B ⊔ vPlus L T = B' ⊔ vPlus L T)

theorem insp3_3_25Hat_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Insp3_3_25HatRest) : Insp3_3_25Hat := by
  intro G _ _ T M L D h hTL hH
  obtain ⟨ha, hc⟩ := hR G T M L D h hTL hH
  exact ⟨ha, fun hTC => vPlus_eq_qL_of_hat h38 h39 h hTL hH hTC, hc⟩

end HatB

end CFSG.Quasithin.H13
