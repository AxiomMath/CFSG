module

public import CFSG.Quasithin.H13.AS91Sec4SixModel
public import CFSG.Quasithin.H13.AS91Sec4Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_z_cases (S : Setting G) {c : G} (hc : c ∈ zpowers S.z) :
    c = 1 ∨ c = S.z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  rw [← zpow_mod_orderOf, S.orderOf_z]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem conj_eq_mul_z_of_polar (S : Setting G) {q u : G} (hq : q ∈ S.QG) (hu : u ∈ S.QG)
    (h1 : QuadraticMap.polar S.q (S.cl q) (S.cl u) = 1) : q * u * q⁻¹ = u * S.z := by
  have hne := (S.polar_cl_eq_one_iff hq hu).mp h1
  rcases S.commutator_eq_one_or_z hq hu with h | h
  · exact absurd (by
      calc q * u = q * u * q⁻¹ * u⁻¹ * (u * q) := by group
        _ = u * q := by rw [h, one_mul]) hne
  · calc q * u * q⁻¹ = q * u * q⁻¹ * u⁻¹ * u := by group
      _ = S.z * u := by rw [h]
      _ = u * S.z := (S.z_comm (S.QG_le_M hu)).symm

theorem exists_centralize (S : Setting G) {U : Subgroup G} (hU : U ≤ S.QG) (m : S.M)
    (hm : ∀ u ∈ U, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) = S.cl u) :
    ∃ s : S.M, S.ρ s = S.ρ m ∧ ∀ u ∈ U, (s : G) * u * (s : G)⁻¹ = u := by
  classical
  have hc2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  obtain ⟨ε, hε0, hε1⟩ : ∃ ε : ZMod 2 → G, ε 0 = 1 ∧ ε 1 = S.z :=
    ⟨fun a => if a = 0 then 1 else S.z, if_pos rfl, if_neg one_ne_zero⟩
  have hεadd : ∀ a b : ZMod 2, ε (a + b) = ε a * ε b := by
    intro a b
    rcases hc2 a with rfl | rfl <;> rcases hc2 b with rfl | rfl
    · rw [add_zero, hε0, mul_one]
    · rw [zero_add, hε0, one_mul]
    · rw [add_zero, hε0, mul_one]
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl, hε0, hε1, S.z_mul_z]
  have hεinj : ∀ a b : ZMod 2, ε a = ε b → a = b := by
    intro a b hab
    rcases hc2 a with rfl | rfl <;> rcases hc2 b with rfl | rfl
    · rfl
    · rw [hε0, hε1] at hab
      exact absurd hab.symm S.z_ne_one
    · rw [hε0, hε1] at hab
      exact absurd hab S.z_ne_one
    · rfl
  have hεc : ∀ (a : ZMod 2) {g : G}, g ∈ S.M → g * ε a = ε a * g := by
    intro a g hg
    rcases hc2 a with rfl | rfl
    · rw [hε0, mul_one, one_mul]
    · rw [hε1]
      exact S.z_comm hg
  have hqconj : ∀ q ∈ S.QG, ∀ u ∈ S.QG,
      q * u * q⁻¹ = u * ε (QuadraticMap.polar S.q (S.cl q) (S.cl u)) := by
    intro q hq u hu
    rcases hc2 (QuadraticMap.polar S.q (S.cl q) (S.cl u)) with h0 | h1
    · rw [h0, hε0, mul_one, (S.polar_cl_eq_zero_iff hq hu).mp h0, mul_inv_cancel_right]
    · rw [h1, hε1]
      exact conj_eq_mul_z_of_polar S hq hu h1
  obtain ⟨δ, hδ⟩ : ∃ δ : G → ZMod 2, ∀ x, δ x = 0 ↔ (m : G) * x * (m : G)⁻¹ = x :=
    ⟨fun x => if (m : G) * x * (m : G)⁻¹ = x then 0 else 1, fun x => by
      by_cases hx : (m : G) * x * (m : G)⁻¹ = x <;> simp [hx]⟩
  have hkey : ∀ x ∈ S.QG, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x →
      (m : G) * x * (m : G)⁻¹ = x * ε (δ x) := by
    intro x hx hfx
    rcases hc2 (δ x) with h0 | h1
    · rw [h0, hε0, mul_one]
      exact (hδ x).mp h0
    · rw [h1, hε1]
      have hne : (m : G) * x * (m : G)⁻¹ ≠ x := fun e => by
        have := (hδ x).mpr e
        rw [h1] at this
        exact one_ne_zero this
      rw [S.ρ_cl m hx] at hfx
      rcases (S.cl_eq_cl_iff hx (S.conj_mem_QG m.2 hx)).mp hfx.symm with e | e
      · exact absurd e hne
      · exact e
  have hfixmul : ∀ x ∈ S.QG, ∀ y ∈ S.QG,
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x →
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) = S.cl y →
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (x * y)) = S.cl (x * y) := by
    intro x hx y hy hfx hfy
    rw [S.cl_mul hx hy, map_add, hfx, hfy]
  have hδmul : ∀ x ∈ S.QG, ∀ y ∈ S.QG,
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x →
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) = S.cl y → δ (x * y) = δ x + δ y := by
    intro x hx y hy hfx hfy
    apply hεinj
    have h1 := hkey _ (S.QG.mul_mem hx hy) (hfixmul x hx y hy hfx hfy)
    have h2 : (m : G) * (x * y) * (m : G)⁻¹ = x * y * (ε (δ x) * ε (δ y)) := by
      calc (m : G) * (x * y) * (m : G)⁻¹ =
          ((m : G) * x * (m : G)⁻¹) * ((m : G) * y * (m : G)⁻¹) := by group
        _ = x * ε (δ x) * (y * ε (δ y)) := by rw [hkey x hx hfx, hkey y hy hfy]
        _ = x * (ε (δ x) * y) * ε (δ y) := by group
        _ = x * (y * ε (δ x)) * ε (δ y) := by rw [← hεc (δ x) (S.QG_le_M hy)]
        _ = x * y * (ε (δ x) * ε (δ y)) := by group
    rw [hεadd]
    exact mul_left_cancel (h1.symm.trans h2)
  have hδz : δ S.z = 0 := (hδ S.z).mpr (by rw [S.z_comm m.2, mul_inv_cancel_right])
  have hδcl : ∀ x ∈ S.QG, ∀ y ∈ S.QG,
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x → S.cl x = S.cl y →
      δ y = δ x := by
    intro x hx y hy hfx hxy
    rcases (S.cl_eq_cl_iff hx hy).mp hxy with rfl | rfl
    · rfl
    · have hfz : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl S.z) = S.cl S.z := by
        rw [S.cl_z, map_zero]
      rw [hδmul x hx S.z S.z_mem_QG hfx hfz, hδz, add_zero]
  obtain ⟨lift, hlift⟩ : ∃ lift : S.Qt → G, ∀ v, lift v ∈ S.QG ∧ S.cl (lift v) = v :=
    ⟨fun v => (S.exists_cl v).choose, fun v => (S.exists_cl v).choose_spec⟩
  have hfixL : ∀ v ∈ S.clSub U,
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (lift v)) = S.cl (lift v) := by
    intro v hv
    obtain ⟨u, huU, -, hu⟩ := S.mem_clSub_iff.mp hv
    rw [(hlift v).2, ← hu]
    exact hm u huU
  let f : S.clSub U →+ ZMod 2 := AddMonoidHom.mk' (fun v => δ (lift v)) fun v w => by
    have hv := hlift (v : S.Qt)
    have hw := hlift (w : S.Qt)
    show δ (lift ((v : S.Qt) + w)) = δ (lift v) + δ (lift w)
    rw [← hδmul _ hv.1 _ hw.1 (hfixL v v.2) (hfixL w w.2)]
    refine hδcl _ (S.QG.mul_mem hv.1 hw.1) _ (hlift _).1
      (hfixmul _ hv.1 _ hw.1 (hfixL v v.2) (hfixL w w.2)) ?_
    rw [S.cl_mul hv.1 hw.1, hv.2, hw.2, (hlift _).2]
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (f.toZModLinearMap 2)
  have hgv : ∀ v (hv : v ∈ S.clSub U), g v = δ (lift v) := fun v hv =>
    LinearMap.congr_fun hg ⟨v, hv⟩
  obtain ⟨q, hq, hqw⟩ := S.exists_cl
    ((LinearMap.BilinForm.toDual (QuadraticMap.polarBilin S.q) S.q_nondegenerate).symm g)
  have hpol : ∀ v, QuadraticMap.polar S.q (S.cl q) v = g v := by
    intro v
    rw [hqw, ← QuadraticMap.polarBilin_apply_apply,
      ← LinearMap.BilinForm.toDual_def S.q_nondegenerate, LinearEquiv.apply_symm_apply]
  have hconj : ∀ u ∈ U, q * u * q⁻¹ = (m : G) * u * (m : G)⁻¹ := by
    intro u hu
    have huQ := hU hu
    have hmem := S.cl_mem_clSub hu huQ
    rw [hqconj q hq u huQ, hkey u huQ (hm u hu), hpol, hgv _ hmem,
      ← hδcl _ (hlift _).1 _ huQ (hfixL _ hmem) (hlift _).2]
  refine ⟨(⟨q, S.QG_le_M hq⟩ : S.M)⁻¹ * m, ?_, fun u hu => ?_⟩
  · rw [map_mul, map_inv, (S.ρ_eq_one_iff _).mpr hq, inv_one, one_mul]
  · have e : (((⟨q, S.QG_le_M hq⟩ : S.M)⁻¹ * m : S.M) : G) = q⁻¹ * (m : G) := rfl
    rw [e]
    calc q⁻¹ * (m : G) * u * (q⁻¹ * (m : G))⁻¹ = q⁻¹ * ((m : G) * u * (m : G)⁻¹) * q := by
          group
      _ = q⁻¹ * (q * u * q⁻¹) * q := by rw [hconj u hu]
      _ = u := by group

theorem mul_comm_eq_of_sq {x y z : G} (hz : z * z = 1) (hzy : z * y = y * z) (hx : x * x = z)
    (hy : y * y = z) (hxy : x * y * (x * y) = z) : y * x = x * y * z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hxi : x⁻¹ = x * z := by
    calc x⁻¹ = x * (x * x)⁻¹ := by group
      _ = x * z := by rw [hx, hzi]
  have hyi : y⁻¹ = y * z := by
    calc y⁻¹ = y * (y * y)⁻¹ := by group
      _ = y * z := by rw [hy, hzi]
  calc y * x = x⁻¹ * (x * y * (x * y)) * y⁻¹ := by group
    _ = x * z * z * (y * z) := by rw [hxy, hxi, hyi]
    _ = x * (z * z) * (y * z) := by group
    _ = x * y * z := by rw [hz]; group

theorem eq_one_of_sq {a b c z : G} (hz : z * z = 1) (hzb : z * b = b * z) (hzc : z * c = c * z)
    (ha : a * a = z) (hb : b * b = z) (hc : c * c = z) (hab : a * b * (a * b) = z)
    (hac : a * c * (a * c) = z) (hbc : b * c * (b * c) = z)
    (habc : a * (b * c) * (a * (b * c)) = z) : z = 1 := by
  have h1 := mul_comm_eq_of_sq hz hzb ha hb hab
  have h2 := mul_comm_eq_of_sq hz hzc ha hc hac
  have hzbc : z * (b * c) = b * c * z := by
    rw [← mul_assoc, hzb, mul_assoc, hzc, mul_assoc]
  have h3 := mul_comm_eq_of_sq hz hzbc ha hbc habc
  have h4 : b * c * a = a * b * c := by
    calc b * c * a = b * (c * a) := by group
      _ = b * (a * c * z) := by rw [h2]
      _ = b * a * c * z := by group
      _ = a * b * z * c * z := by rw [h1]
      _ = a * b * (z * c) * z := by group
      _ = a * b * (c * z) * z := by rw [hzc]
      _ = a * b * c * (z * z) := by group
      _ = a * b * c := by rw [hz, mul_one]
  rw [h4] at h3
  have h5 : a * b * c * z = a * b * c * 1 := by
    calc a * b * c * z = a * (b * c) * z := by group
      _ = a * b * c := h3.symm
      _ = a * b * c * 1 := (mul_one _).symm
  exact mul_left_cancel h5

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem q0_ψV (v : h.setting.Qt) :
    q0 (D.ψV v) = h.setting.q v := by
  rw [← D.q_ψV_symm, AddEquiv.symm_apply_apply]

section E1


@[expose] noncomputable def W1q : Submodule (ZMod 2) h.setting.Qt where
  carrier := {v | D.ψV v ∈ Two.W1}
  add_mem' {v w} hv hw := by
    show D.ψV (v + w) ∈ Two.W1
    rw [map_add]
    exact Two.add_mem_W1 hv hw
  zero_mem' := by
    show D.ψV 0 ∈ Two.W1
    rw [map_zero]
    exact Two.zero_mem_W1
  smul_mem' c v hv := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]
      show D.ψV 0 ∈ Two.W1
      rw [map_zero]
      exact Two.zero_mem_W1
    · rw [one_smul]
      exact hv

theorem mem_W1q {v : h.setting.Qt} : v ∈ D.W1q ↔ D.ψV v ∈ Two.W1 := Iff.rfl

theorem card_W1q : Nat.card D.W1q = 64 := by
  rw [← Two.card_W1sub]
  exact Nat.card_congr (D.ψV.toEquiv.subtypeEquiv fun _ => Iff.rfl)

@[expose] noncomputable def E1 : Subgroup G := h.setting.clPre D.W1q

@[expose] noncomputable def E : Subgroup G := centralizer (D.E1 : Set G)

theorem mem_E1 {x : G} : x ∈ D.E1 ↔ x ∈ h.setting.QG ∧ D.ψV (h.setting.cl x) ∈ Two.W1 :=
  Iff.rfl

theorem mem_E {x : G} : x ∈ D.E ↔ ∀ y ∈ D.E1, y * x = x * y := mem_centralizer_iff

theorem E1_le_QG : D.E1 ≤ h.setting.QG := h.setting.clPre_le_QG _

theorem z_mem_E1 : z ∈ D.E1 := h.setting.z_mem_clPre _

theorem card_E1 : Nat.card D.E1 = 2 ^ 7 := by
  rw [E1, h.setting.card_clPre, D.card_W1q]
  norm_num

theorem E1_comm {x y : G} (hx : x ∈ D.E1) (hy : y ∈ D.E1) :
    x * y = y * x := by
  refine (h.setting.polar_cl_eq_zero_iff hx.1 hy.1).mp ?_
  rw [D.polar_ψV, QuadraticMap.polar, Two.q0_of_mem_W1 (Two.add_mem_W1 hx.2 hy.2),
    Two.q0_of_mem_W1 hx.2, Two.q0_of_mem_W1 hy.2, sub_zero, sub_zero]

theorem E1_sq {x : G} (hx : x ∈ D.E1) : x * x = 1 := by
  rw [← pow_two, ← h.setting.q_cl_eq_zero_iff hx.1, ← D.q0_ψV]
  exact Two.q0_of_mem_W1 hx.2

theorem E_le_M : D.E ≤ h.setting.M := fun x hx =>
  h.setting.mem_M_iff.mpr ((D.mem_E.mp hx) z D.z_mem_E1).symm

theorem E1_le_E : D.E1 ≤ D.E := fun x hx =>
  D.mem_E.mpr fun _ hy => D.E1_comm hy hx

theorem z_comm_E {x : G} (hx : x ∈ D.E) : z * x = x * z := (D.mem_E.mp hx) z D.z_mem_E1

theorem QG_inf_E : h.setting.QG ⊓ D.E = D.E1 := by
  have h1 := card_QG_inf_centralizer_mul h.setting D.E1_le_QG D.z_mem_E1
  rw [D.card_E1, h.setting_width] at h1
  refine (Subgroup.eq_of_le_of_card_ge (le_inf D.E1_le_QG D.E1_le_E) ?_).symm
  have e : h.setting.QG ⊓ D.E = h.setting.QG ⊓ centralizer (D.E1 : Set G) := rfl
  rw [e, D.card_E1]
  norm_num at h1 ⊢
  omega

theorem mem_E1_of_mem_E {x : G} (hxQ : x ∈ h.setting.QG)
    (hx : x ∈ D.E) : x ∈ D.E1 := by
  rw [← D.QG_inf_E]
  exact ⟨hxQ, hx⟩

end E1

section Model

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem Φo_mem_eb {x : G} (hx : x ∈ D.E) (hxM : x ∈ h.setting.M) :
    D.Φo (h.setting.ρ ⟨x, hxM⟩) ∈ Two.ebGrp := by
  refine Two.mem_ebGrp_of_fix (D.stabIn_three hOut hTw) (D.Φo_mem_nGrp hOut hTw ⟨_, rfl⟩)
    fun v hv => ?_
  obtain ⟨y, hyQ, hyv⟩ := h.setting.exists_cl (D.ψV.symm v)
  have hyE : y ∈ D.E1 := ⟨hyQ, by rw [hyv, D.mem_W1q, AddEquiv.apply_symm_apply]; exact hv⟩
  have hc : x * y * x⁻¹ = y := by
    rw [← (D.mem_E.mp hx) y hyE, mul_inv_cancel_right]
  rw [← AddEquiv.apply_symm_apply D.ψV v, ← hyv, Φo_apply_ψV, h.setting.ρ_cl _ hyQ]
  show D.ψV (h.setting.cl (x * y * x⁻¹)) = _
  rw [hc]

theorem exists_mem_E {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ Two.ebGrp) :
    ∃ s : h.setting.M, (s : G) ∈ D.E ∧ D.Φo (h.setting.ρ s) = U := by
  have hUN := Two.pGrp_le_nGrp (Two.ebGrp_le_pGrp hU)
  rw [← D.map_Mbar_Φo hOut hTw] at hUN
  obtain ⟨m, hmM, rfl⟩ := hUN
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hmM
  obtain ⟨s, hs, hsc⟩ := exists_centralize h.setting D.E1_le_QG t fun u hu => by
    apply D.ψV.injective
    rw [← Φo_apply_ψV]
    exact Two.ebGrp_fix hU hu.2
  exact ⟨s, D.mem_E.mpr fun u hu => comm_of_conj_eq (hsc u hu), by rw [hs]⟩

theorem card_E : Nat.card D.E = 2 ^ 11 := by
  let f : ↥D.E →* ↥Two.ebGrp :=
    ((D.Φo.comp h.setting.ρ).comp (Subgroup.inclusion D.E_le_M)).codRestrict Two.ebGrp
      fun x => D.Φo_mem_eb hOut hTw x.2 (D.E_le_M x.2)
  have hsurj : Function.Surjective f := by
    rintro ⟨U, hU⟩
    obtain ⟨s, hsE, hsU⟩ := D.exists_mem_E hOut hTw hU
    exact ⟨⟨s, hsE⟩, Subtype.ext hsU⟩
  have hker : f.ker = D.E1.subgroupOf D.E := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← D.QG_inf_E, mem_inf]
    constructor
    · intro h1
      have h2 : D.Φo (h.setting.ρ (Subgroup.inclusion D.E_le_M x)) = D.Φo 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact ⟨(h.setting.ρ_eq_one_iff _).mp (D.Φo_injective h2), x.2⟩
    · rintro ⟨hxQ, -⟩
      apply Subtype.ext
      show D.Φo (h.setting.ρ (Subgroup.inclusion D.E_le_M x)) = 1
      rw [(h.setting.ρ_eq_one_iff _).mpr hxQ, map_one]
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Two.card_ebGrp,
    hker, card_subgroupOf_eq, inf_of_le_right D.E1_le_E, D.card_E1] at h1
  calc Nat.card D.E = 2 ^ 7 * 16 := h1.symm
    _ = 2 ^ 11 := by norm_num

theorem E_le_T : D.E ≤ D.T := fun x hx =>
  mem_pre_of_rho ⟨x, D.E_le_M hx⟩ (Two.ebGrp_le_pGrp (D.Φo_mem_eb hOut hTw hx (D.E_le_M hx)))

theorem E_le_G13 : D.E ≤ D.G13 := (D.E_le_T hOut hTw).trans D.T_le_G13

end Model

section Normal


theorem conj_mem_E1 {g : G} (hg : g ∈ D.G13) {x : G} (hx : x ∈ D.E1) : g * x * g⁻¹ ∈ D.E1 := by
  obtain ⟨hgM, hgρ⟩ := mem_pre.mp hg
  have hgρ' : D.Φo (h.setting.ρ ⟨g, hgM⟩) ∈ Two.g13Grp := hgρ
  refine ⟨h.setting.conj_mem_QG hgM hx.1, ?_⟩
  rw [D.mem_W1q, ← h.setting.ρ_cl ⟨g, hgM⟩ hx.1, ← Φo_apply_ψV, ← (Two.mem_g13Grp.mp hgρ').2]
  exact Set.mem_image_of_mem _ hx.2

theorem conj_mem_E {g : G} (hg : g ∈ D.G13) {e : G} (he : e ∈ D.E) : g * e * g⁻¹ ∈ D.E := by
  refine D.mem_E.mpr fun y hy => ?_
  have hc := (D.mem_E.mp he) _ (D.conj_mem_E1 (inv_mem hg) hy)
  calc y * (g * e * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * e) * g⁻¹ := by group
    _ = g * (e * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
    _ = g * e * g⁻¹ * y := by group

end Normal

section Elem

variable
  (hHat : HatM22SmallModules) (hOut : KG82HatM22Out)
  (hTw : KG82HatM22Twelve)

include hOut hTw

theorem Φo_θ_comm {A : V12 ≃ₗ[ZMod 2] V12} (hA : A ∈ Two.ebGrp) :
    D.Φo D.θ * A = A * D.Φo D.θ := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Φo_apply]
  rcases D.Φ_θ with hθ | hθ
  · rw [hθ, hθ, Two.ebGrp_theta0 hA]
  · rw [hθ, hθ, Two.ebGrp_theta0 hA, Two.ebGrp_theta0 hA]

theorem commutator_c_mem_E1 {a : G} (ha : a ∈ D.E) :
    (D.c : G) * a * (D.c : G)⁻¹ * a⁻¹ ∈ D.E1 := by
  have haM := D.E_le_M ha
  have hcG := D.QX_le hOut hTw (mem_sup_right (mem_zpowers _))
  refine D.mem_E1_of_mem_E ?_ (mul_mem (D.conj_mem_E hcG ha) (inv_mem ha))
  have hcomm : D.Φo (h.setting.ρ D.c) * D.Φo (h.setting.ρ ⟨a, haM⟩) =
      D.Φo (h.setting.ρ ⟨a, haM⟩) * D.Φo (h.setting.ρ D.c) := by
    rw [D.ρ_c]
    exact D.Φo_θ_comm hOut hTw (D.Φo_mem_eb hOut hTw ha haM)
  have h1 : h.setting.ρ (D.c * ⟨a, haM⟩ * D.c⁻¹ * (⟨a, haM⟩ : h.setting.M)⁻¹) = 1 := by
    apply D.Φo_injective
    rw [map_one, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv, hcomm]
    group
  exact (h.setting.ρ_eq_one_iff _).mp h1

theorem sq_mem_QG {a : G} (ha : a ∈ D.E) : a * a ∈ h.setting.QG := by
  have haM := D.E_le_M ha
  have h1 : h.setting.ρ (⟨a, haM⟩ * ⟨a, haM⟩) = 1 := by
    apply D.Φo_injective
    rw [map_mul, map_mul, Two.ebGrp_sq (D.Φo_mem_eb hOut hTw ha haM), map_one]
  exact (h.setting.ρ_eq_one_iff _).mp h1

theorem c_comm_sq {a : G} (ha : a ∈ D.E) : Commute (D.c : G) (a * a) := by
  obtain ⟨k, hk, e⟩ : ∃ k ∈ D.E1, (D.c : G) * a * (D.c : G)⁻¹ = k * a :=
    ⟨_, D.commutator_c_mem_E1 hOut hTw ha, by group⟩
  have hka : k * a = a * k := (D.mem_E.mp ha) k hk
  have h1 : (D.c : G) * (a * a) * (D.c : G)⁻¹ = a * a := by
    calc (D.c : G) * (a * a) * (D.c : G)⁻¹ =
        ((D.c : G) * a * (D.c : G)⁻¹) * ((D.c : G) * a * (D.c : G)⁻¹) := by group
      _ = k * a * (k * a) := by rw [e]
      _ = k * (a * k) * a := by group
      _ = k * (k * a) * a := by rw [← hka]
      _ = k * k * (a * a) := by group
      _ = a * a := by rw [D.E1_sq hk, one_mul]
  show (D.c : G) * (a * a) = a * a * D.c
  calc (D.c : G) * (a * a) = (D.c : G) * (a * a) * (D.c : G)⁻¹ * D.c := by group
    _ = a * a * D.c := by rw [h1]

include hHat in
theorem sq_eq_one_or_z {a : G} (ha : a ∈ D.E) : a * a = 1 ∨ a * a = z := by
  have hC : a * a ∈ centralizer (zpowers (D.c : G) : Set G) := by
    rw [mem_centralizer_iff]
    rintro y ⟨k, rfl⟩
    exact ((D.c_comm_sq hOut hTw ha).zpow_left k).eq
  have h1 := inf_centralizer_eq hHat h.setting_width D.ρ_c D.θ_mem D.θ_ne D.hat
  have h2 : a * a ∈ zpowers h.setting.z := by
    rw [← h1]
    exact ⟨D.sq_mem_QG hOut hTw ha, hC⟩
  exact mem_zpowers_z_cases h.setting h2

include hHat in
theorem sq_eq_sq {a b : G} (ha : a ∈ D.E) (hb : b ∈ D.E)
    (ha1 : D.Φo (h.setting.ρ ⟨a, D.E_le_M ha⟩) ≠ 1)
    (hb1 : D.Φo (h.setting.ρ ⟨b, D.E_le_M hb⟩) ≠ 1) : a * a = b * b := by
  have haM := D.E_le_M ha
  have hbM := D.E_le_M hb
  obtain ⟨Ua, hUa, hUae⟩ := Two.exists_conj_eb (D.Φo_mem_eb hOut hTw ha haM) ha1
  obtain ⟨Ub, hUb, hUbe⟩ := Two.exists_conj_eb (D.Φo_mem_eb hOut hTw hb hbM) hb1
  have hU : Ub * Ua⁻¹ ∈ Two.g13Grp := Two.g13Gens_le_g13Grp (mul_mem hUb (inv_mem hUa))
  have hUN := Two.g13Grp_le_nGrp hU
  rw [← D.map_Mbar_Φo hOut hTw] at hUN
  obtain ⟨m, hmM, hmU⟩ := hUN
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hmM
  have htG : (t : G) ∈ D.G13 :=
    mem_pre_of_rho t (show D.Φo (h.setting.ρ t) ∈ Two.g13Grp by rw [hmU]; exact hU)
  have hk : b⁻¹ * ((t : G) * a * (t : G)⁻¹) ∈ D.E1 := by
    refine D.mem_E1_of_mem_E ?_ (mul_mem (inv_mem hb) (D.conj_mem_E htG ha))
    have h1 : h.setting.ρ ((⟨b, hbM⟩ : h.setting.M)⁻¹ * (t * ⟨a, haM⟩ * t⁻¹)) = 1 := by
      apply D.Φo_injective
      simp only [map_mul, map_inv, map_one]
      rw [hmU, ← hUae, ← hUbe]
      group
    exact (h.setting.ρ_eq_one_iff _).mp h1
  obtain ⟨k, hk, e⟩ : ∃ k ∈ D.E1, (t : G) * a * (t : G)⁻¹ = b * k := ⟨_, hk, by group⟩
  have hsq : (t : G) * (a * a) * (t : G)⁻¹ = a * a := by
    have hzt : (t : G) * z = z * t := h.setting.z_comm t.2
    rcases D.sq_eq_one_or_z hHat hOut hTw ha with h1 | h1 <;> rw [h1]
    · group
    · rw [hzt, mul_inv_cancel_right]
  have hkb : k * b = b * k := (D.mem_E.mp hb) k hk
  calc a * a = (t : G) * (a * a) * (t : G)⁻¹ := hsq.symm
    _ = ((t : G) * a * (t : G)⁻¹) * ((t : G) * a * (t : G)⁻¹) := by group
    _ = b * k * (b * k) := by rw [e]
    _ = b * (k * b) * k := by group
    _ = b * (b * k) * k := by rw [hkb]
    _ = b * b * (k * k) := by group
    _ = b * b := by rw [D.E1_sq hk, mul_one]

include hHat in
theorem E_sq {a : G} (ha : a ∈ D.E) : a * a = 1 := by
  classical
  by_contra hne
  have haz : a * a = z := (D.sq_eq_one_or_z hHat hOut hTw ha).resolve_left hne
  have haM := D.E_le_M ha
  have hAeb := D.Φo_mem_eb hOut hTw ha haM
  have ha1 : D.Φo (h.setting.ρ ⟨a, haM⟩) ≠ 1 := by
    intro h1
    have haQ : a ∈ h.setting.QG :=
      (h.setting.ρ_eq_one_iff _).mp (D.Φo_injective (h1.trans (map_one _).symm))
    exact hne (D.E1_sq (D.mem_E1_of_mem_E haQ ha))
  have hall : ∀ y : h.setting.M, (y : G) ∈ D.E → D.Φo (h.setting.ρ y) ≠ 1 → (y : G) * y = z :=
    fun y hy hy1 => (D.sq_eq_sq hHat hOut hTw ha hy ha1 hy1).symm.trans haz
  have hcard : (Set.toFinite (Two.ebGrp : Set (V12 ≃ₗ[ZMod 2] V12))).toFinset.card = 16 := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _), ← Nat.card_coe_set_eq]
    exact Two.card_ebGrp
  set A := D.Φo (h.setting.ρ ⟨a, haM⟩) with hA
  obtain ⟨B, hB, hBn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {1, A}) (t := (Set.toFinite (Two.ebGrp : Set (V12 ≃ₗ[ZMod 2] V12))).toFinset)
    (by rw [hcard]; exact Finset.card_le_two.trans_lt (by norm_num))
  obtain ⟨C, hC, hCn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {1, A, B, A * B}) (t := (Set.toFinite (Two.ebGrp : Set (V12 ≃ₗ[ZMod 2] V12))).toFinset)
    (by rw [hcard]; exact Finset.card_le_four.trans_lt (by norm_num))
  rw [Set.Finite.mem_toFinset] at hB hC
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hBn hCn
  obtain ⟨hB1, hBA⟩ := hBn
  obtain ⟨hC1, hCA, hCB, hCAB⟩ := hCn
  obtain ⟨bM, hbE, hbB⟩ := D.exists_mem_E hOut hTw hB
  obtain ⟨cM, hcE, hcC⟩ := D.exists_mem_E hOut hTw hC
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right (Two.ebGrp_sq hAeb)
  have hBinv : B⁻¹ = B := inv_eq_of_mul_eq_one_right (Two.ebGrp_sq hB)
  have hAB : A * B ≠ 1 := fun e => hBA (by rw [eq_inv_of_mul_eq_one_right e, hAinv])
  have hAC : A * C ≠ 1 := fun e => hCA (by rw [eq_inv_of_mul_eq_one_right e, hAinv])
  have hBC : B * C ≠ 1 := fun e => hCB (by rw [eq_inv_of_mul_eq_one_right e, hBinv])
  have hABC : A * (B * C) ≠ 1 := fun e => hCAB (by
    have e1 : B * C = A := by rw [eq_inv_of_mul_eq_one_right e, hAinv]
    calc C = B⁻¹ * (B * C) := by group
      _ = B * A := by rw [e1, hBinv]
      _ = A * B := Two.ebGrp_comm hB hAeb)
  have hsb := hall bM hbE (by rw [hbB]; exact hB1)
  have hsc := hall cM hcE (by rw [hcC]; exact hC1)
  have hsab := hall (⟨a, haM⟩ * bM) (mul_mem ha hbE) (by
    rw [map_mul, map_mul, hbB]; exact hAB)
  have hsac := hall (⟨a, haM⟩ * cM) (mul_mem ha hcE) (by
    rw [map_mul, map_mul, hcC]; exact hAC)
  have hsbc := hall (bM * cM) (mul_mem hbE hcE) (by
    rw [map_mul, map_mul, hbB, hcC]; exact hBC)
  have hsabc := hall (⟨a, haM⟩ * (bM * cM)) (mul_mem ha (mul_mem hbE hcE)) (by
    rw [map_mul, map_mul, map_mul, map_mul, hbB, hcC]; exact hABC)
  exact h.setting.z_ne_one (eq_one_of_sq h.setting.z_mul_z (D.z_comm_E hbE) (D.z_comm_E hcE)
    haz hsb hsc hsab hsac hsbc hsabc)

include hHat in
theorem isElemAbelian_E : IsElemAbelian 2 D.E := by
  have hsq : ∀ x ∈ D.E, x * x = 1 := fun x hx => D.E_sq hHat hOut hTw hx
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
  have ha := hsq _ a.2
  have hb := hsq _ b.2
  show (a : G) * b = b * a
  calc (a : G) * b = (a : G) * b * (b * a) * (b * a) := by
        rw [mul_assoc ((a : G) * b), hsq _ (mul_mem b.2 a.2), mul_one]
    _ = (b : G) * a := by
        rw [show (a : G) * b * (b * a) * (b * a) = a * (b * b) * a * (b * a) by group, hb,
          mul_one, ha, one_mul]

end Elem

end Data41

end CFSG.Quasithin.H13.AS91
