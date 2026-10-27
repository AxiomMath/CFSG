module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KMeetA
public import CFSG.Quasithin.H13.GoldschmidtC137SQL32
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8k_b_sup_o {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) (hker : ρ.ker = O) : B ⊔ O = ⊤ := by
  classical
  have hQO : CFSG.pCore 2 Γ ≤ O := nat.q_le.trans nat.z_le
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hO_sol : Group.IsSolvable ↥O := by
    let Q' : Subgroup ↥O := (CFSG.pCore 2 Γ).subgroupOf O
    haveI hQ'n : Q'.Normal := CFSG.pCore_normal.subgroupOf O
    have hQ'2 : IsPGroup 2 Q' :=
      (CFSG.pCore_isPGroup (G := Γ) (p := 2)).comap_subtype (K := O)
    haveI : Group.IsNilpotent ↥Q' := hQ'2.isNilpotent
    have hQ'7 : IsPGroup 7 (↥O ⧸ Q') := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q' x
      obtain ⟨n, hn⟩ := nat.seven (y : Γ) y.2
      refine ⟨n, ?_⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      show ((y ^ 7 ^ n : ↥O) : Γ) ∈ CFSG.pCore 2 Γ
      simpa using hn
    haveI : Group.IsNilpotent (↥O ⧸ Q') := hQ'7.isNilpotent
    exact Group.isSolvable_of_subgroup_quotient Q'
  have hmap_nsolv : ¬ Group.IsSolvable ↥(B.map ρ) := by
    intro hBsol
    haveI : Group.IsSolvable ↥(B.map ρ) := hBsol
    have hB_sol : Group.IsSolvable ↥B := by
      haveI : Group.IsSolvable ↥(O.subgroupOf B) := by
        let incl : ↥(O.subgroupOf B) →* ↥O :=
          { toFun := fun x => ⟨x.1.1, x.2⟩
            map_one' := rfl
            map_mul' := fun x y => rfl }
        exact Group.isSolvable_of_isSolvable_injective (f := incl) fun x y hxy =>
          Subtype.ext (Subtype.ext (by simpa [incl] using congrArg Subtype.val hxy))
      exact Group.isSolvable_of_ker_le_range (O.subgroupOf B).subtype (ρ.subgroupMap B)
        (by rw [ker_subgroupMap, hker, Subgroup.range_subtype])
    obtain ⟨P, _, φ, hφs, _, hE64, _⟩ := conf.p0
    haveI : Group.IsSolvable P := Group.isSolvable_of_surjective (f := φ) hφs
    obtain ⟨N, hNn, _, hL3⟩ := hE64
    haveI : N.Normal := hNn
    obtain ⟨hsimple, hcard168⟩ :=
      CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two (Y := P ⧸ N) hL3
    haveI : IsSimpleGroup (P ⧸ N) := hsimple
    have hcomm : ∀ a b : P ⧸ N, a * b = b * a :=
      (IsSimpleGroup.comm_iff_isSolvable (G := P ⧸ N)).mpr inferInstance
    haveI : IsMulCommutative (P ⧸ N) := IsMulCommutative.of_comm hcomm
    have hprime : Nat.Prime (Nat.card (P ⧸ N)) :=
      (Group.is_simple_iff_prime_card (α := P ⧸ N)).mp inferInstance
    exact absurd (hcard168 ▸ hprime) (by norm_num)
  have hmap_top : B.map ρ = ⊤ := c8k_sl27_eq_top_of_not_solvable hmap_nsolv
  rw [eq_top_iff]
  intro γ _
  have hmem : ρ γ ∈ B.map ρ := by rw [hmap_top]; trivial
  rw [Subgroup.mem_map] at hmem
  obtain ⟨b, hb, hbγ⟩ := hmem
  have hker' : b⁻¹ * γ ∈ O := by
    have h1 : ρ (b⁻¹ * γ) = 1 := by rw [map_mul, map_inv, hbγ, inv_mul_cancel]
    have h2 : b⁻¹ * γ ∈ ρ.ker := MonoidHom.mem_ker.mpr h1
    rwa [hker] at h2
  have : γ = b * (b⁻¹ * γ) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hb hker'

theorem c8k_o_inf_b_le_z {Γ : Type} [Group Γ] [Finite Γ] {B : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (nat : C8KNat Γ d ρ O Z)
    (hqB : CFSG.pCore 2 Γ ≤ B) (hBO : B ⊔ O = ⊤) (hOB : ¬ O ≤ B) : O ⊓ B ≤ Z := by
  classical
  haveI hOn : O.Normal := nat.normal
  haveI hZn : Z.Normal := nat.z_normal
  set W : Subgroup Γ := (O ⊓ B) ⊔ Z with hW
  have hZW : Z ≤ W := by rw [hW]; exact le_sup_right
  have hWO : W ≤ O := by rw [hW]; exact sup_le inf_le_left nat.z_le
  have hBinv : ∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W := by
    intro b hb w hw
    rw [hW] at hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    have hyO : b * y * b⁻¹ ∈ O := hOn.conj_mem y hy.1 b
    have hyB : b * y * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hy.2) (B.inv_mem hb)
    have hzZ : b * z * b⁻¹ ∈ Z := hZn.conj_mem z hz b
    rw [hW]
    have h1 : b * (y * z) * b⁻¹ = (b * y * b⁻¹) * (b * z * b⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem_sup ⟨hyO, hyB⟩ hzZ
  have hOinv : ∀ o ∈ O, ∀ w ∈ W, o * w * o⁻¹ ∈ W := by
    intro o ho w hw
    rw [hW] at hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    have hcy : o * y * o⁻¹ ∈ W := by
      have h1 : o * y * o⁻¹ * y⁻¹ ∈ Z := nat.comm o ho y hy.1
      have h2 : o * y * o⁻¹ = (o * y * o⁻¹ * y⁻¹) * y := by group
      rw [h2, hW, ← sup_comm]
      exact Subgroup.mul_mem_sup h1 hy
    have hcz : o * z * o⁻¹ ∈ Z := hZn.conj_mem z hz o
    rw [hW]
    have h3 : o * (y * z) * o⁻¹ = (o * y * o⁻¹) * (o * z * o⁻¹) := by group
    rw [h3]
    exact W.mul_mem hcy (hZW hcz)
  have hinv : ∀ γ : Γ, ∀ w ∈ W, γ * w * γ⁻¹ ∈ W := by
    intro γ w hw
    have hmem : γ ∈ (B ⊔ O : Subgroup Γ) := by rw [hBO]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨b, hb, o, ho, rfl⟩ := hmem
    have hbo : b * o * w * (b * o)⁻¹ = b * (o * w * o⁻¹) * b⁻¹ := by group
    rw [hbo]
    exact hBinv b hb _ (hOinv o ho w hw)
  rcases nat.irred W hZW hWO hinv with h | h
  · have : O ⊓ B ≤ W := by rw [hW]; exact le_sup_left
    exact this.trans_eq h
  · exfalso
    apply hOB
    have hsup : (O ⊓ B) ⊔ Z = O := hW ▸ h
    have hngen := nat.ngen (O ⊓ B) inf_le_left hsup
    have hle : (O ⊓ B) ⊔ CFSG.pCore 2 Γ ≤ B := sup_le inf_le_right hqB
    exact hngen.symm.trans_le hle

theorem c8k_exists_W {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ} (hS : IsSylowIn 2 S ⊤)
    (hc : centralizer (CFSG.pCore 2 Γ : Set Γ) ≤ CFSG.pCore 2 Γ) {w : Γ} (hwS : w ∈ S)
    (hw2 : w ^ 2 = 1) (hwc : ∀ s ∈ S, w * s = s * w) :
    ∃ W : Subgroup Γ, W.Normal ∧ IsElemAbelian 2 W ∧ W ≤ CFSG.pCore 2 Γ ∧
      (∀ x ∈ W, ∀ q ∈ CFSG.pCore 2 Γ, x * q = q * x) ∧ w ∈ W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQle : CFSG.pCore 2 Γ ≤ S :=
    hS.le_of_normal le_top (CFSG.pCore_normal.subgroupOf ⊤) CFSG.pCore_isPGroup
  have hwcent : w ∈ centralizer (CFSG.pCore 2 Γ : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hwc q (hQle hq)).symm
  have hwQ : w ∈ CFSG.pCore 2 Γ := hc hwcent
  let W : Subgroup Γ :=
    { carrier := {x | x ∈ CFSG.pCore 2 Γ ∧ x ^ 2 = 1 ∧
        ∀ q ∈ CFSG.pCore 2 Γ, x * q = q * x}
      one_mem' := ⟨(CFSG.pCore 2 Γ).one_mem, by simp, by intro q _; simp⟩
      mul_mem' := by
        rintro x y ⟨hxQ, hx2, hxc⟩ ⟨hyQ, hy2, hyc⟩
        refine ⟨(CFSG.pCore 2 Γ).mul_mem hxQ hyQ, ?_, ?_⟩
        · have hcomm : Commute x y := (hyc x hxQ).symm
          rw [hcomm.mul_pow, hx2, hy2, one_mul]
        · intro q hq
          calc (x * y) * q = x * (y * q) := by group
            _ = x * (q * y) := by rw [hyc q hq]
            _ = (x * q) * y := by group
            _ = (q * x) * y := by rw [hxc q hq]
            _ = q * (x * y) := by group
      inv_mem' := by
        rintro x ⟨hxQ, hx2, hxc⟩
        refine ⟨(CFSG.pCore 2 Γ).inv_mem hxQ, ?_, ?_⟩
        · rw [inv_pow, hx2, inv_one]
        · intro q hq
          have h := congrArg Inv.inv (hxc q⁻¹ ((CFSG.pCore 2 Γ).inv_mem hq))
          simpa [mul_inv_rev] using h.symm }
  have hWnormal : W.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxQ, hx2, hxc⟩ := hx
    refine ⟨CFSG.pCore_normal.conj_mem x hxQ g, ?_, ?_⟩
    · rw [show (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group, hx2]
      group
    · intro q hq
      have hq' : g⁻¹ * q * g ∈ CFSG.pCore 2 Γ := by
        simpa using CFSG.pCore_normal.conj_mem q hq g⁻¹
      have h := hxc (g⁻¹ * q * g) hq'
      calc (g * x * g⁻¹) * q = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by rw [h]
        _ = q * (g * x * g⁻¹) := by group
  have hWabel : IsElemAbelian 2 W := by
    refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (a.2.2.2 b.1 b.2.1)), ?_⟩
    intro x hx
    exact hx.2.1
  exact ⟨W, hWnormal, hWabel, fun x hx => hx.1, fun x hx q hq => hx.2.2 q hq,
    ⟨hwQ, hw2, fun q hq => hwc q (hQle hq)⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
