module

public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailBasic
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2n_closure_two_part {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p = 3)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {Z F : Subgroup G} (hZBs : Z ≤ Bs)
    (hFBs : F ≤ Bs) (hZ : Nat.card ↥Z ≤ p ^ 2) (hZF : Z ⊓ F ≠ ⊥) (S : Set (MulAut ↥Bs))
    (hS : ∀ φ ∈ S, (∀ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∈ Z) ∧
      ∀ f : ↥Bs, (f : G) ∈ F → φ f = f) :
    ¬ 4 ∣ Nat.card ↥(Subgroup.closure S) := by
  subst hp
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  letI : CommGroup ↥Bs := { (inferInstance : Group ↥Bs) with mul_comm := hcomm }
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  letI : Module (ZMod 3) (Additive ↥Bs) :=
    AddCommGroup.zmodModule (n := 3) fun a => by
      have h : (Additive.toMul a) ^ 3 = 1 := Subtype.ext (hBs.2 _ (Additive.toMul a).2)
      rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  let Zb : Subgroup ↥Bs := Z.subgroupOf Bs
  let Fb : Subgroup ↥Bs := F.subgroupOf Bs
  let Z' : Submodule (ZMod 3) (Additive ↥Bs) :=
    AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup Zb)
  let F' : Submodule (ZMod 3) (Additive ↥Bs) :=
    AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup Fb)
  have memZ' : ∀ b : ↥Bs, Additive.ofMul b ∈ Z' ↔ b ∈ Zb := by
    intro b; rw [AddSubgroup.mem_toZModSubmodule]; exact Iff.rfl
  have memF' : ∀ b : ↥Bs, Additive.ofMul b ∈ F' ↔ b ∈ Fb := by
    intro b; rw [AddSubgroup.mem_toZModSubmodule]; exact Iff.rfl
  let P : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | (∀ b : ↥Bs, b⁻¹ * φ b ∈ Zb) ∧ ∀ f : ↥Bs, f ∈ Fb → φ f = f}
      one_mem' := by
        refine ⟨fun b => ?_, fun f hf => ?_⟩
        · show b⁻¹ * (1 : MulAut ↥Bs) b ∈ Zb
          simp
        · rfl
      mul_mem' := by
        intro φ ψ hφ hψ
        refine ⟨fun b => ?_, fun f hf => ?_⟩
        · have h1 : b⁻¹ * ψ b ∈ Zb := hψ.1 b
          have h2 : (ψ b)⁻¹ * φ (ψ b) ∈ Zb := hφ.1 (ψ b)
          rw [show b⁻¹ * (φ * ψ) b = (b⁻¹ * ψ b) * ((ψ b)⁻¹ * φ (ψ b)) by
            rw [MulAut.mul_apply]; group]
          exact Zb.mul_mem h1 h2
        · show φ (ψ f) = f
          rw [hψ.2 f hf, hφ.2 f hf]
      inv_mem' := by
        intro φ hφ
        refine ⟨fun b => ?_, fun f hf => ?_⟩
        · have h := hφ.1 (φ⁻¹ b)
          rw [show b⁻¹ * φ⁻¹ b = ((φ⁻¹ b)⁻¹ * φ (φ⁻¹ b))⁻¹ by
            rw [MulAut.apply_inv_self]; group]
          exact Zb.inv_mem h
        · have hfix : φ f = f := hφ.2 f hf
          calc φ⁻¹ f = φ⁻¹ (φ f) := by rw [hfix]
            _ = f := by simp }
  have hSP : Subgroup.closure S ≤ P := by
    rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨h1, h2⟩ := hS φ hφ
    refine ⟨fun b => ?_, fun f hf => ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact h1 b
    · exact h2 f (Subgroup.mem_subgroupOf.mp hf)
  let Φ : MulAut ↥Bs →* (Additive ↥Bs ≃ₗ[ZMod 3] Additive ↥Bs) :=
    ggLin (p := 3) (AddEquiv.refl (Additive ↥Bs))
  let H : Subgroup (Additive ↥Bs ≃ₗ[ZMod 3] Additive ↥Bs) := (Subgroup.closure S).map Φ
  have hcardH : Nat.card ↥H = Nat.card ↥(Subgroup.closure S) :=
    Subgroup.card_map_of_injective (f := Φ) (ggLin_injective (AddEquiv.refl (Additive ↥Bs)))
  have hH : ∀ ν ∈ H, (∀ v, ν v - v ∈ Z') ∧ ∀ f ∈ F', ν f = f := by
    intro ν hν
    rw [Subgroup.mem_map] at hν
    obtain ⟨φ, hφ, rfl⟩ := hν
    have hφP : φ ∈ P := hSP hφ
    refine ⟨fun v => ?_, fun f hf => ?_⟩
    · set b : ↥Bs := Additive.toMul v with hb
      have hvb : v = Additive.ofMul b := by rw [hb, ofMul_toMul]
      have hval : Φ φ v = Additive.ofMul (φ b) := by
        show ggLin (p := 3) (AddEquiv.refl (Additive ↥Bs)) φ v = _
        rw [ggLin_apply]
        simp only [AddEquiv.refl_symm, AddEquiv.refl_apply]
        rw [← hb]
      rw [hval, hvb]
      have hsub : Additive.ofMul (φ b) - Additive.ofMul b
          = Additive.ofMul (φ b * b⁻¹) := by
        rw [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
      rw [hsub, memZ', mul_comm]
      exact hφP.1 b
    · have hb : Additive.toMul f ∈ Fb := (memF' (Additive.toMul f)).mp (by simpa using hf)
      have hfix : φ (Additive.toMul f) = Additive.toMul f := hφP.2 _ hb
      have hval : Φ φ f = Additive.ofMul (φ (Additive.toMul f)) := by
        show ggLin (p := 3) (AddEquiv.refl (Additive ↥Bs)) φ f = _
        rw [ggLin_apply]; rfl
      rw [hval, hfix, ofMul_toMul]
  have hZF' : Z' ⊓ F' ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZF
    have hwZ : ((w : G)) ∈ Z := (Subgroup.mem_inf.mp w.2).1
    have hwF : ((w : G)) ∈ F := (Subgroup.mem_inf.mp w.2).2
    have hwBs : ((w : G)) ∈ Bs := hZBs hwZ
    let w' : ↥Bs := ⟨(w : G), hwBs⟩
    have hw'Z : w' ∈ Zb := Subgroup.mem_subgroupOf.mpr hwZ
    have hw'F : w' ∈ Fb := Subgroup.mem_subgroupOf.mpr hwF
    refine ⟨Additive.ofMul w', ?_, ?_⟩
    · rw [Submodule.mem_inf, memZ', memF']; exact ⟨hw'Z, hw'F⟩
    · intro hzero
      apply hw
      have h1 : w' = 1 := by
        have := congrArg Additive.toMul hzero
        simpa using this
      have h2 : (w : G) = 1 := by simpa [w'] using congrArg (fun x : ↥Bs => (x : G)) h1
      exact Subtype.ext h2
  have hZ' : Module.finrank (ZMod 3) Z' ≤ 2 := by
    have hcardZ' : Nat.card ↥Z' = Nat.card ↥Z := by
      have e1 : ↥Z' ≃ ↥Zb :=
        { toFun := fun v => ⟨Additive.toMul v.1, (memZ' _).mp v.2⟩
          invFun := fun b => ⟨Additive.ofMul b.1, (memZ' _).mpr b.2⟩
          left_inv := by intro v; ext; simp
          right_inv := by intro b; ext; simp }
      calc Nat.card ↥Z' = Nat.card ↥Zb := Nat.card_congr e1
        _ = Nat.card ↥Z := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZBs).toEquiv
    have hpow : 3 ^ Module.finrank (ZMod 3) Z' ≤ 3 ^ 2 := by
      rw [FiniteField.pow_finrank_eq_natCard, hcardZ']; exact hZ
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  have hpadic := ggQ2n_P_two_part Z' F' hZF' hZ' H hH
  rw [hcardH] at hpadic
  intro h4
  have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(Subgroup.closure S)) := by
    rw [← padicValNat_dvd_iff_le (p := 2) (n := 2)
      (a := Nat.card ↥(Subgroup.closure S)) Nat.card_pos.ne']
    simpa using h4
  omega

end CFSG.StandardType

end
