module

public import CFSG.Quasithin.Background.B4ModelsSporadic

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Matrix

namespace FFModel

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

abbrev Sec (D : FFModel) : Type := ↥D.sec ⧸ D.ker.subgroupOf D.sec

@[expose] def Witness (D : FFModel) (ρ : Representation (ZMod 2) Γ W) (θ : Γ ≃* D.Gam)
    (β : W ≃+ Additive D.Sec) : Prop :=
  D.ker ≤ D.sec ∧ (∀ g : D.Gam, ∀ m ∈ D.sec, D.act g m ∈ D.sec) ∧
    (∀ g : D.Gam, ∀ m ∈ D.ker, D.act g m ∈ D.ker) ∧
    ∀ (γ : Γ) (w : W) (m : ↥D.sec) (hm : D.act (θ γ) m ∈ D.sec),
      β w = Additive.ofMul (QuotientGroup.mk m : D.Sec) →
        β (ρ γ w) = Additive.ofMul (QuotientGroup.mk ⟨D.act (θ γ) m, hm⟩ : D.Sec)

@[expose] def IsModel (D : FFModel) (ρ : Representation (ZMod 2) Γ W) : Prop :=
  ∃ (θ : Γ ≃* D.Gam) (β : W ≃+ Additive D.Sec), D.Witness ρ θ β

@[expose] def repMulAut (ρ : Representation (ZMod 2) Γ W) : Γ →* MulAut (Multiplicative W) where
  toFun γ :=
    { toFun := fun x => Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (ρ γ⁻¹ (Multiplicative.toAdd x))
      left_inv := fun x => by
        simp only [toAdd_ofAdd]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
          ofAdd_toAdd]
      right_inv := fun x => by
        simp only [toAdd_ofAdd]
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
          ofAdd_toAdd]
      map_mul' := fun x y => by simp }
  map_one' := by
    ext x
    simp
  map_mul' γ δ := by
    ext x
    simp

theorem repMulAut_apply (ρ : Representation (ZMod 2) Γ W) (γ : Γ) (x : Multiplicative W) :
    repMulAut ρ γ x = Multiplicative.ofAdd (ρ γ (Multiplicative.toAdd x)) := rfl

theorem Witness.realizesVia {D : FFModel} {ρ : Representation (ZMod 2) Γ W} {θ : Γ ≃* D.Gam}
    {β : W ≃+ Additive D.Sec} (h : D.Witness ρ θ β) :
    D.RealizesVia (repMulAut ρ).range ⊤ ⊥
      ((repMulAut ρ).rangeRestrict.comp θ.symm.toMonoidHom) := by
  obtain ⟨hks, hsec, hker, hint⟩ := h
  have hint' : ∀ (g : D.Gam) (w : W) (m : ↥D.sec) (hm : D.act g m ∈ D.sec),
      β w = Additive.ofMul (QuotientGroup.mk m : D.Sec) →
        β (ρ (θ.symm g) w) = Additive.ofMul (QuotientGroup.mk ⟨D.act g m, hm⟩ : D.Sec) := by
    intro g w m hm hw
    have hm' : D.act (θ (θ.symm g)) m ∈ D.sec := by rwa [θ.apply_symm_apply]
    have e : (⟨D.act (θ (θ.symm g)) m, hm'⟩ : ↥D.sec) = ⟨D.act g m, hm⟩ :=
      Subtype.ext (congrArg (fun x => D.act x (m : D.Amb)) (θ.apply_symm_apply g))
    rw [hint (θ.symm g) w m hm' hw, e]
  refine ⟨?_, bot_le, hks, fun _ _ _ => Subgroup.mem_top _, fun h z hz => ?_, hsec, hker, ?_⟩
  · exact (MonoidHom.rangeRestrict_surjective _).comp θ.symm.surjective
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · refine ⟨(MulEquiv.toAdditiveRight.symm β).toMonoidHom.comp
      (⊤ : Subgroup (Multiplicative W)).subtype, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := (MulEquiv.toAdditiveRight.symm β).surjective y
      exact ⟨⟨x, Subgroup.mem_top x⟩, hx⟩
    · intro u
      rw [Subgroup.mem_bot]
      change MulEquiv.toAdditiveRight.symm β (u : Multiplicative W) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
    · intro g u m hu hm hum
      change Additive.toMul (β (ρ (θ.symm g) (Multiplicative.toAdd (u : Multiplicative W)))) = _
      have hw : β (Multiplicative.toAdd (u : Multiplicative W)) =
          Additive.ofMul (QuotientGroup.mk m : D.Sec) := by
        change Additive.toMul (β (Multiplicative.toAdd (u : Multiplicative W))) = _ at hum
        rw [← hum]
        rfl
      rw [hint' g _ m hm hw]
      rfl

theorem IsModel.realizesMod {D : FFModel} {ρ : Representation (ZMod 2) Γ W} (h : D.IsModel ρ) :
    D.RealizesMod (repMulAut ρ).range := by
  obtain ⟨θ, β, hw⟩ := h
  exact ⟨_, hw.realizesVia⟩

end FFModel

namespace Explicit

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def matModel (Γ₀ : Subgroup (GL ι K)) (μ : ↥Γ₀ → Matrix ι ι K) : FFModel where
  Gam := ↥Γ₀
  Amb := Multiplicative (ι → K)
  act g x := Multiplicative.ofAdd (μ g *ᵥ Multiplicative.toAdd x)
  sec := ⊤
  ker := ⊥

inductive NatDual : Type
  | natural
  | dual
deriving DecidableEq

@[expose] def natDual (Γ₀ : Subgroup (GL ι K)) : NatDual → FFModel
  | .natural => FFModel.nat Γ₀
  | .dual => FFModel.dualNat Γ₀

end Matrix

@[expose] def BinaryNaturalSL (ρ : Representation (ZMod 2) Γ W) (d : ℕ) (F : Type) [Field F]
    (ε : NatDual) : Prop :=
  (natDual (StatedSL d F) ε).IsModel ρ

@[expose] def spJ (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks 0 1 1 0

@[expose] def sp4 (F : Type) [Field F] : Subgroup (GL (Fin 2 ⊕ Fin 2) F) where
  carrier := {g | (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F * g = spJ F}
  mul_mem' {g h} hg hh := by
    have hg' : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F * g = spJ F := hg
    have hh' : (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F * h = spJ F := hh
    change ((g * h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      spJ F * ((g * h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = spJ F
    rw [Units.val_mul, Matrix.transpose_mul]
    set M := (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    set N := (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    calc Nᵀ * Mᵀ * spJ F * (M * N) = Nᵀ * (Mᵀ * spJ F * M) * N := by simp only [Matrix.mul_assoc]
      _ = spJ F := by rw [hg', hh']
  one_mem' := by
    change ((1 : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F *
      ((1 : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = spJ F
    simp
  inv_mem' {g} hg := by
    have hg' : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F * g = spJ F := hg
    change ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * spJ F *
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = spJ F
    set N := ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    set M := (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    have hMN : M * N = 1 := Units.mul_inv g
    calc Nᵀ * spJ F * N = Nᵀ * (Mᵀ * spJ F * M) * N := by rw [hg']
      _ = (M * N)ᵀ * spJ F * (M * N) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = spJ F := by rw [hMN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

@[expose] def BinaryNaturalSp4 (ρ : Representation (ZMod 2) Γ W) (F : Type) [Field F] : Prop :=
  ∃ (α : MulAut ↥(sp4 F)) (θ : Γ ≃* ↥(sp4 F)) (β : W ≃+ Additive (FFModel.nat (sp4 F)).Sec),
    (FFModel.nat (sp4 F)).Witness ρ (θ.trans α) β

@[expose] def BinaryNaturalSp4Derived (ρ : Representation (ZMod 2) Γ W) (F : Type) [Field F] :
    Prop :=
  (FFModel.nat ⁅sp4 F, sp4 F⁆).IsModel ρ

@[expose] def SL5ExteriorTwo (ρ : Representation (ZMod 2) Γ W) : Prop :=
  ∃ (α : MulAut ↥(StatedSL 5 (ZMod 2))) (θ : Γ ≃* ↥(StatedSL 5 (ZMod 2)))
    (β : W ≃+ Additive (FFModel.extSq (ZMod 2) 5).Sec),
    (FFModel.extSq (ZMod 2) 5).Witness ρ (θ.trans α) β

@[expose] def SL4ExteriorTwo (ρ : Representation (ZMod 2) Γ W) : Prop :=
  ∃ (α : MulAut ↥(StatedSL 4 (ZMod 2))) (θ : Γ ≃* ↥(StatedSL 4 (ZMod 2)))
    (β : W ≃+ Additive (FFModel.extSq (ZMod 2) 4).Sec),
    (FFModel.extSq (ZMod 2) 4).Witness ρ (θ.trans α) β

inductive AltSym : Type
  | alternating
  | symmetric
deriving DecidableEq

@[expose] def dnModel (n : ℕ) : AltSym → FFModel
  | .alternating => FFModel.altDn n
  | .symmetric => FFModel.symDn n

@[expose] def AlternatingNatural (ρ : Representation (ZMod 2) Γ W) (n : ℕ) (ε : AltSym) : Prop :=
  ∃ (α : MulAut (dnModel n ε).Gam) (θ : Γ ≃* (dnModel n ε).Gam)
    (β : W ≃+ Additive (dnModel n ε).Sec), (dnModel n ε).Witness ρ (θ.trans α) β

@[expose] def coordSum (n : ℕ) : G6.PermMod n →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.sum_add_distrib]

theorem ker_coordSum (n : ℕ) : (coordSum n).ker = G6.coreMod n := by
  ext x
  rw [MonoidHom.mem_ker, G6.mem_coreMod]
  exact ofAdd_eq_one

theorem card_coreMod {n : ℕ} (hn : 1 ≤ n) : Nat.card (G6.coreMod n) = 2 ^ (n - 1) := by
  have hsurj : Function.Surjective (coordSum n) := by
    intro c
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c)), ?_⟩
    change Multiplicative.ofAdd (∑ i, (Pi.single ⟨0, hn⟩ (Multiplicative.toAdd c) :
      Fin n → ZMod 2) i) = c
    rw [Finset.sum_pi_single']
    simp only [Finset.mem_univ, ↓reduceIte, ofAdd_toAdd]
  have h := Subgroup.card_ker_mul_card_range (coordSum n)
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, ker_coordSum] at h
  have h1 : Nat.card (G6.PermMod n) = 2 ^ n := by
    change Nat.card (Fin n → ZMod 2) = 2 ^ n
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  rw [h1, h2] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ] at h
  simp only [add_tsub_cancel_right]
  omega

theorem allOnes_mem_coreMod_iff (n : ℕ) : G6.allOnes n ∈ G6.coreMod n ↔ Even n := by
  rw [G6.mem_coreMod]
  change ∑ _i : Fin n, (1 : ZMod 2) = 0 ↔ Even n
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ZMod.natCast_eq_zero_iff_even]

theorem allOnes_ne_one {n : ℕ} (hn : 1 ≤ n) : G6.allOnes n ≠ 1 := fun h => by
  have h0 := congrFun (congrArg Multiplicative.toAdd h) ⟨0, hn⟩
  change (1 : ZMod 2) = 0 at h0
  exact absurd h0 (by decide)

theorem card_dnZ {n : ℕ} (hn : 1 ≤ n) :
    Nat.card ↥(Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) = if Even n then 2 else 1 := by
  have hz2 : G6.allOnes n * G6.allOnes n = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    change (1 : ZMod 2) + 1 = 0
    decide
  have hord : orderOf (G6.allOnes n) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hz2) (allOnes_ne_one hn)
  split_ifs with he
  · have hle : Subgroup.zpowers (G6.allOnes n) ≤ G6.coreMod n :=
      (Subgroup.zpowers_le).mpr ((allOnes_mem_coreMod_iff n).mpr he)
    rw [inf_eq_left.mpr hle, Nat.card_zpowers, hord]
  · have hbot : Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨k, rfl⟩, hk⟩
      rw [Subgroup.mem_bot]
      have hk' : (G6.allOnes n) ^ k = G6.allOnes n ^ (k % 2) := by
        rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
      change (G6.allOnes n) ^ k ∈ G6.coreMod n at hk
      change (G6.allOnes n) ^ k = 1
      rw [hk'] at hk ⊢
      rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] at hk ⊢
      · exact zpow_zero _
      · rw [zpow_one] at hk
        exact absurd ((allOnes_mem_coreMod_iff n).mp hk) he
    rw [hbot, Subgroup.card_bot]

theorem card_dn_sec {n : ℕ} (hn : 1 ≤ n) (ε : AltSym) :
    Nat.card (dnModel n ε).Sec = if Even n then 2 ^ (n - 2) else 2 ^ (n - 1) := by
  have key : Nat.card (↥(G6.coreMod n) ⧸ (Subgroup.zpowers (G6.allOnes n) ⊓
      G6.coreMod n).subgroupOf (G6.coreMod n)) = if Even n then 2 ^ (n - 2) else 2 ^ (n - 1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, card_dnZ hn,
      card_coreMod hn] at h
    split_ifs at h ⊢ with he
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
        obtain ⟨r, hr⟩ := he
        exact ⟨n - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega, add_tsub_cancel_right, pow_succ] at h ⊢
      omega
    · omega
  cases ε <;> exact key

@[expose] def altLift7At (p : Fin 8) :
    ↥(alternatingGroup (Fin 7)) →* ↥(alternatingGroup (Fin 8)) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.succAboveEmb p)).comp
      (alternatingGroup (Fin 7)).subtype).codRestrict (alternatingGroup (Fin 8)) fun σ => by
    have h := σ.2
    rw [Equiv.Perm.mem_alternatingGroup] at h ⊢
    have key : Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (Fin.succAboveEmb p)
        (σ : Equiv.Perm (Fin 7))) = Equiv.Perm.sign (σ : Equiv.Perm (Fin 7)) := by
      classical
      rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
      convert Equiv.Perm.sign_extendDomain (σ : Equiv.Perm (Fin 7))
        (Equiv.ofInjective (Fin.succAboveEmb p).1 (Fin.succAboveEmb p).2)
    exact key.trans h

theorem altLift7At_apply_self (p : Fin 8) (σ : ↥(alternatingGroup (Fin 7))) :
    ((altLift7At p σ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) p = p := by
  change Equiv.Perm.viaEmbedding (σ : Equiv.Perm (Fin 7)) (Fin.succAboveEmb p) p = p
  exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ fun ⟨i, hi⟩ => Fin.succAbove_ne p i hi

@[expose] def a7FourModel (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)) (p : Fin 8)
    (ε : NatDual) : FFModel where
  Gam := ↥(alternatingGroup (Fin 7))
  Amb := Multiplicative (Fin 4 → ZMod 2)
  act σ x := Multiplicative.ofAdd
    ((match ε with
      | .natural => ((α (altLift7At p σ) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
      | .dual => (((α (altLift7At p σ))⁻¹ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ) *ᵥ Multiplicative.toAdd x)
  sec := ⊤
  ker := ⊥

@[expose] def A7Four (ρ : Representation (ZMod 2) Γ W) (p : Fin 8) (ε : NatDual) : Prop :=
  ∃ α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2), (a7FourModel α p ε).IsModel ρ

inductive TripleTwist : Type
  | natural
  | dual
  | frobenius
  | dualFrobenius
deriving DecidableEq

@[expose] def tripleTwistMat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (ε : TripleTwist)
    (g : GL ι K) : Matrix ι ι K :=
  match ε with
  | .natural => g
  | .dual => ((g⁻¹ : GL ι K) : Matrix ι ι K)ᵀ
  | .frobenius => (g : Matrix ι ι K).map (· ^ 2)
  | .dualFrobenius => (((g⁻¹ : GL ι K) : Matrix ι ι K)ᵀ).map (· ^ 2)

@[expose] def IsTripleCover (P : Type*) [Group P] (S : Type*) [Group S] : Prop :=
  commutator P = ⊤ ∧ Nonempty (↥(Subgroup.center P) ≃* Multiplicative (ZMod 3)) ∧
    Nonempty (P ⧸ Subgroup.center P ≃* S)

@[expose] def TripleA6Six (ρ : Representation (ZMod 2) Γ W) (ε : TripleTwist) : Prop :=
  ∃ (P : Type) (_ : Group P), IsTripleCover P ↥(alternatingGroup (Fin 6)) ∧
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 4 ∧
    ∃ (τ : P →* GL (Fin 3) K) (hτ : Function.Injective τ),
      (∀ x, ((τ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) ∧
      (∀ g : GL (Fin 3) K, g ∈ (Subgroup.center P).map τ ↔
        ∃ c : K, c ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) = c • 1) ∧
      ∃ (θ : Γ ≃* P)
        (β : W ≃+ Additive (matModel τ.range fun g => tripleTwistMat ε (g : GL (Fin 3) K)).Sec),
        (matModel τ.range fun g => tripleTwistMat ε (g : GL (Fin 3) K)).Witness ρ
          (θ.trans (MonoidHom.ofInjective hτ)) β

section Cayley

variable (F : Type) [Field F]

@[expose] def cayleyOne : quasithinZorn F := (1, 0, 0, 1)

variable {F}

@[expose] def cayleyTr (x : quasithinZorn F) : F := x.1 + x.2.2.2

@[expose] def cayleyNorm (x : quasithinZorn F) : F := x.1 * x.2.2.2 + ∑ i, x.2.1 i * x.2.2.1 i

@[expose] def cayleyMul (x y : quasithinZorn F) : quasithinZorn F :=
  (x.1 * y.1 + ∑ i, x.2.1 i * y.2.2.1 i,
    x.1 • y.2.1 + y.2.2.2 • x.2.1 + quasithinCross x.2.2.1 y.2.2.1,
    y.1 • x.2.2.1 + x.2.2.2 • y.2.2.1 + quasithinCross x.2.1 y.2.1,
    x.2.2.2 * y.2.2.2 + ∑ i, x.2.2.1 i * y.2.1 i)

variable (F)

@[expose] def cayleyGroup : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F) where
  carrier := {g | g (cayleyOne F) = cayleyOne F ∧
    (∀ x y, g (cayleyMul x y) = cayleyMul (g x) (g y)) ∧
    (∀ x, cayleyTr (g x) = cayleyTr x) ∧ ∀ x, cayleyNorm (g x) = cayleyNorm x}
  mul_mem' {g h} hg hh := by
    obtain ⟨hg1, hgm, hgt, hgn⟩ := hg
    obtain ⟨hh1, hhm, hht, hhn⟩ := hh
    refine ⟨?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
    · change g (h (cayleyOne F)) = _
      rw [hh1, hg1]
    · change g (h (cayleyMul x y)) = cayleyMul (g (h x)) (g (h y))
      rw [hhm, hgm]
    · change cayleyTr (g (h x)) = _
      rw [hgt, hht]
    · change cayleyNorm (g (h x)) = _
      rw [hgn, hhn]
  one_mem' := ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  inv_mem' {g} hg := by
    obtain ⟨hg1, hgm, hgt, hgn⟩ := hg
    refine ⟨?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
    · change g.symm (cayleyOne F) = cayleyOne F
      rw [LinearEquiv.symm_apply_eq, hg1]
    · change g.symm (cayleyMul x y) = cayleyMul (g.symm x) (g.symm y)
      rw [LinearEquiv.symm_apply_eq, hgm, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    · change cayleyTr (g.symm x) = cayleyTr x
      conv_rhs => rw [← g.apply_symm_apply x]
      rw [hgt]
    · change cayleyNorm (g.symm x) = cayleyNorm x
      conv_rhs => rw [← g.apply_symm_apply x]
      rw [hgn]

variable {F}

@[expose] def cayleyPolar (x y : quasithinZorn F) : F :=
  cayleyNorm (x + y) - cayleyNorm x - cayleyNorm y

theorem cayleyPolar_eq (x y : quasithinZorn F) :
    cayleyPolar x y = x.1 * y.2.2.2 + y.1 * x.2.2.2 +
      ∑ i, (x.2.1 i * y.2.2.1 i + y.2.1 i * x.2.2.1 i) := by
  simp only [cayleyPolar, cayleyNorm, Fin.sum_univ_three, Prod.fst_add, Prod.snd_add,
    Pi.add_apply]
  ring

theorem cayleyPolar_radical [CharP F 2] {x : quasithinZorn F} (hx : cayleyTr x = 0) :
    (∀ y, cayleyTr y = 0 → cayleyPolar x y = 0) ↔ ∃ c : F, x = (c, 0, 0, c) := by
  have hs : x.2.2.2 = x.1 := by
    have h := hx
    rw [cayleyTr, add_comm] at h
    exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq x.1)
  constructor
  · intro h
    have hu : x.2.1 = 0 := funext fun i => by
      have hi := h (0, 0, Pi.single i 1, 0) (by simp [cayleyTr])
      rw [cayleyPolar_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at hi
      simpa using hi
    have hv : x.2.2.1 = 0 := funext fun i => by
      have hi := h (0, Pi.single i 1, 0, 0) (by simp [cayleyTr])
      rw [cayleyPolar_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at hi
      simpa using hi
    exact ⟨x.1, Prod.ext rfl (Prod.ext hu (Prod.ext hv hs))⟩
  · rintro ⟨c, rfl⟩ y hy
    rw [cayleyPolar_eq]
    simp only [Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
    rw [mul_comm y.1 c, ← mul_add, add_comm, ← cayleyTr, hy, mul_zero]

end Cayley

inductive FullDerived : Type
  | full
  | derived
deriving DecidableEq

@[expose] def cayleyActor (F : Type) [Field F] :
    FullDerived → Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)
  | .full => cayleyGroup F
  | .derived => ⁅cayleyGroup F, cayleyGroup F⁆

@[expose] def G2Natural (ρ : Representation (ZMod 2) Γ W) (F : Type) [Field F] (ε : FullDerived) :
    Prop :=
  (FFModel.zornQ (cayleyActor F ε)).IsModel ρ

inductive SLSp : Type
  | sl
  | sp
deriving DecidableEq

@[expose] def TwistedTensorNatural (ρ : Representation (ZMod 2) Γ W) (d : ℕ) (F : Type) [Field F]
    [CharP F 2] (a : ℕ) : SLSp → Prop
  | .sl => (FFModel.twistTensor a (StatedSL d F)).IsModel ρ
  | .sp => d = 4 ∧ (FFModel.twistTensor a (sp4 F)).IsModel ρ

@[expose] def BinaryNineTensor (ρ : Representation (ZMod 2) Γ W) (F : Type) [Field F] [CharP F 2]
    (a : ℕ) : Prop :=
  TwistedTensorNatural ρ 3 F a .sl

@[expose] def BinaryOrthogonalFour (ρ : Representation (ZMod 2) Γ W) (F : Type) [Field F]
    [CharP F 2] (a : ℕ) : Prop :=
  TwistedTensorNatural ρ 2 F a .sl

@[expose] def hermDet {F : Type} [Field F] (X : Matrix (Fin 2) (Fin 2) F) : F := X.det

theorem hermDet_pow {F : Type} [Field F] [CharP F 2] {a : ℕ} {X : Matrix (Fin 2) (Fin 2) F}
    (hX : Multiplicative.ofAdd X ∈ hermSub a (Fin 2) F) : hermDet X ^ 2 ^ a = hermDet X := by
  have hX' : (frobPow a X)ᵀ = X := hX
  have hmap : frobPow a X = (iterateFrobenius F 2 a).mapMatrix X := by
    ext i j
    simp [frobPow, iterateFrobenius_def]
  conv_rhs => rw [hermDet, ← hX', Matrix.det_transpose, hmap, ← RingHom.map_det]
  rw [iterateFrobenius_def]
  rfl

theorem hermDet_twistAct {F : Type} [Field F] [CharP F 2] {a : ℕ} (g : ↥(StatedSL 2 F))
    (X : Matrix (Fin 2) (Fin 2) F) :
    hermDet (Multiplicative.toAdd (twistAct a (StatedSL 2 F) g (Multiplicative.ofAdd X))) =
      hermDet X := by
  have hdet : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    obtain ⟨x, hx⟩ := g
    rw [statedSL_eq_range_toGL] at hx
    obtain ⟨A, hA⟩ := hx
    change ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1
    rw [← hA]
    exact A.2
  have hmap : frobPow a ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (iterateFrobenius F 2 a).mapMatrix ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    simp [frobPow, iterateFrobenius_def]
  simp only [hermDet, twistAct, toAdd_ofAdd, Matrix.det_mul, Matrix.det_transpose, hmap,
    ← RingHom.map_det, hdet, map_one, one_mul, mul_one]

@[expose] def MathieuCode24 (ρ : Representation (ZMod 2) Γ W) : Prop :=
  (FFModel.golaySec CFSG.Monster.Code.AutPerm golayC (Subgroup.zpowers (G6.allOnes 24))).IsModel ρ

@[expose] def MathieuCocode24 (ρ : Representation (ZMod 2) Γ W) : Prop :=
  (FFModel.golaySec CFSG.Monster.Code.AutPerm (G6.coreMod 24) golayC).IsModel ρ

@[expose] def mathieuStab (x : Fin 24) : Subgroup (Equiv.Perm (Fin 24)) :=
  CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x

@[expose] def mathieuStab2 (x y : Fin 24) : Subgroup (Equiv.Perm (Fin 24)) :=
  mathieuStab x ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) y

@[expose] def MathieuCode23 (ρ : Representation (ZMod 2) Γ W) (x : Fin 24) : Prop :=
  (FFModel.golaySec (mathieuStab x) golayC (Subgroup.zpowers (G6.allOnes 24))).IsModel ρ

@[expose] def MathieuCocode23 (ρ : Representation (ZMod 2) Γ W) (x : Fin 24) : Prop :=
  (FFModel.golaySec (mathieuStab x) (G6.coreMod 24) golayC).IsModel ρ

@[expose] def MathieuCode22 (ρ : Representation (ZMod 2) Γ W) (x y : Fin 24) : Prop :=
  x ≠ y ∧ (FFModel.golaySec (mathieuStab2 x y) (golayC ⊓ pairKer x y)
    (Subgroup.zpowers (G6.allOnes 24))).IsModel ρ

@[expose] def MathieuCocode22 (ρ : Representation (ZMod 2) Γ W) (x y : Fin 24) : Prop :=
  x ≠ y ∧ (FFModel.golaySec (mathieuStab2 x y) (G6.coreMod 24)
    (golayC ⊔ Subgroup.zpowers (pairVec x y))).IsModel ρ

@[expose] def M12Ten (ρ : Representation (ZMod 2) Γ W) (H : Subgroup (Equiv.Perm (Fin 24)))
    (eY : G6.PermMod 24) : Prop :=
  eY ∈ golayC ∧ hammingNorm (Multiplicative.toAdd eY) = 12 ∧ H ≤ CFSG.Monster.Code.AutPerm ∧
    (∀ σ ∈ H, G6.permAct 24 σ eY = eY ∨ G6.permAct 24 σ eY = eY * G6.allOnes 24) ∧
    (FFModel.golaySec H golayC (Subgroup.closure {G6.allOnes 24, eY})).IsModel ρ

@[expose] def IsIndexTwoExtension {P G : Type*} [Group P] [Group G] (ι : P →* G) (t : G) : Prop :=
  Function.Injective ι ∧ ι.range.Normal ∧ ι.range.index = 2 ∧ t ∉ ι.range ∧ t ^ 2 ∈ ι.range

@[expose] def IsMhat22Datum (P : Type) [Group P] (K : Type) [Field K] [Fintype K]
    (τ : P →* GL (Fin 6) K) (B : Matrix (Fin 6) (Fin 6) K) : Prop :=
  IsTripleCover P ↥quasithinM22 ∧ Fintype.card K = 4 ∧ Function.Injective τ ∧ B.det ≠ 0 ∧
    (frobPow 1 B)ᵀ = B ∧
    ∀ x, (frobPow 1 ((τ x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))ᵀ * B *
      ((τ x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = B

@[expose] def Mhat22Twelve (ρ : Representation (ZMod 2) Γ W) : Prop :=
  ∃ (P : Type) (_ : Group P) (K : Type) (_ : Field K) (_ : Fintype K) (τ : P →* GL (Fin 6) K)
    (B : Matrix (Fin 6) (Fin 6) K) (h : IsMhat22Datum P K τ B) (θ : Γ ≃* P)
    (β : W ≃+ Additive (FFModel.nat τ.range).Sec),
    (FFModel.nat τ.range).Witness ρ (θ.trans (MonoidHom.ofInjective h.2.2.1)) β

@[expose] def mulAutModel {G : Type} [Group G] {ι K : Type} [Field K]
    (ψ : G →* MulAut (Multiplicative (ι → K))) : FFModel where
  Gam := G
  Amb := Multiplicative (ι → K)
  act g x := ψ g x
  sec := ⊤
  ker := ⊥

@[expose] def J2Twelve (ρ : Representation (ZMod 2) Γ W) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (ι : quasithinJ2 →* ↥(cayleyGroup K))
    (hι : Function.Injective ((cayleyGroup K).subtype.comp ι)) (θ : Γ ≃* quasithinJ2)
    (β : W ≃+ Additive (FFModel.zornQ ((cayleyGroup K).subtype.comp ι).range).Sec),
    Fintype.card K = 4 ∧
      (FFModel.zornQ ((cayleyGroup K).subtype.comp ι).range).Witness ρ
        (θ.trans (MonoidHom.ofInjective hι)) β

@[expose] def zornModel {G : Type} [Group G] {F : Type} [Field F]
    (ψ : G →* MulAut (Multiplicative (quasithinZorn F))) : FFModel where
  Gam := G
  Amb := Multiplicative (quasithinZorn F)
  act g x := ψ g x
  sec := zornO0 F
  ker := zornR F

section Bridge

open FFModel

theorem sp4_eq_statedSp (F : Type) [Field F] [CharP F 2] : sp4 F = StatedSp 2 F := by
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = spJ F := by
    rw [spJ, CharTwo.neg_eq]
  rw [StatedSp, hJ]
  exact (Subgroup.closure_eq (sp4 F)).symm

theorem BinaryNaturalSL.realizes {ρ : Representation (ZMod 2) Γ W} {d : ℕ} {F : Type} [Field F]
    [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ a) (h : BinaryNaturalSL ρ d F .natural) :
    CFSG.Quasithin.BinaryNaturalSL (repMulAut ρ).range ⊤ ⊥ d a :=
  ⟨F, inferInstance, inferInstance, hF, h.realizesMod⟩

theorem BinaryNaturalSp4.realizes {ρ : Representation (ZMod 2) Γ W} {F : Type} [Field F]
    [Finite F] [CharP F 2] {a : ℕ} (hF : Nat.card F = 2 ^ a) (h : BinaryNaturalSp4 ρ F) :
    CFSG.Quasithin.BinaryNaturalSp4 (repMulAut ρ).range ⊤ ⊥ a := by
  obtain ⟨α, θ, β, hw⟩ := h
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  have hm : (FFModel.nat (sp4 F)).RealizesMod (repMulAut ρ).range := ⟨_, hw.realizesVia⟩
  rwa [sp4_eq_statedSp] at hm

theorem SL5ExteriorTwo.realizes {ρ : Representation (ZMod 2) Γ W} (h : SL5ExteriorTwo ρ) :
    CFSG.Quasithin.SLExteriorTwo (repMulAut ρ).range ⊤ ⊥ 5 := by
  obtain ⟨α, θ, β, hw⟩ := h
  exact ⟨_, hw.realizesVia⟩

theorem SL4ExteriorTwo.realizes {ρ : Representation (ZMod 2) Γ W} (h : SL4ExteriorTwo ρ) :
    CFSG.Quasithin.SLExteriorTwo (repMulAut ρ).range ⊤ ⊥ 4 := by
  obtain ⟨α, θ, β, hw⟩ := h
  exact ⟨_, hw.realizesVia⟩

theorem AlternatingNatural.realizes_alternating {ρ : Representation (ZMod 2) Γ W} {n : ℕ}
    (h : AlternatingNatural ρ n .alternating) :
    CFSG.Quasithin.AlternatingNatural (repMulAut ρ).range ⊤ ⊥ n := by
  obtain ⟨α, θ, β, hw⟩ := h
  exact ⟨_, hw.realizesVia⟩

theorem AlternatingNatural.realizes_symmetric {ρ : Representation (ZMod 2) Γ W} {n : ℕ}
    (h : AlternatingNatural ρ n .symmetric) :
    CFSG.Quasithin.SymmetricNatural (repMulAut ρ).range ⊤ ⊥ n := by
  obtain ⟨α, θ, β, hw⟩ := h
  exact ⟨_, hw.realizesVia⟩

theorem TwistedTensorNatural.realizes_sl {ρ : Representation (ZMod 2) Γ W} {d : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a))
    (h : TwistedTensorNatural ρ d F a .sl) :
    CFSG.Quasithin.TwistedTensorSL (repMulAut ρ).range ⊤ ⊥ d a :=
  ⟨F, inferInstance, inferInstance, inferInstance, hF, IsModel.realizesMod h⟩

theorem TwistedTensorNatural.realizes_sp {ρ : Representation (ZMod 2) Γ W} {F : Type} [Field F]
    [Finite F] [CharP F 2] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a))
    (h : TwistedTensorNatural ρ 4 F a .sp) :
    CFSG.Quasithin.TwistedTensorSp4 (repMulAut ρ).range ⊤ ⊥ a := by
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ?_⟩
  have hm := IsModel.realizesMod h.2
  rwa [sp4_eq_statedSp] at hm

theorem BinaryNineTensor.realizes {ρ : Representation (ZMod 2) Γ W} {F : Type} [Field F]
    [Finite F] [CharP F 2] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (h : BinaryNineTensor ρ F a) :
    CFSG.Quasithin.BinaryNineTensor (repMulAut ρ).range ⊤ ⊥ a :=
  TwistedTensorNatural.realizes_sl hF h

theorem BinaryOrthogonalFour.realizes {ρ : Representation (ZMod 2) Γ W} {F : Type} [Field F]
    [Finite F] [CharP F 2] {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a))
    (h : BinaryOrthogonalFour ρ F a) :
    CFSG.Quasithin.BinaryOrthogonalFour (repMulAut ρ).range ⊤ ⊥ a :=
  TwistedTensorNatural.realizes_sl hF h

theorem altLift7At_last : altLift7At (Fin.last 7) = altLift7 := by
  have he : Fin.succAboveEmb (Fin.last 7) = (Fin.castSuccEmb : Fin 7 ↪ Fin 8) :=
    Function.Embedding.ext fun i => Fin.succAbove_last_apply i
  ext σ i
  simp only [altLift7At, altLift7, he]

theorem A7Four.realizes_last {ρ : Representation (ZMod 2) Γ W}
    (h : A7Four ρ (Fin.last 7) .natural) : CFSG.Quasithin.A7Four (repMulAut ρ).range ⊤ ⊥ := by
  obtain ⟨α, hm⟩ := h
  have he : a7FourModel α (Fin.last 7) .natural = FFModel.a7Four α := by
    unfold a7FourModel FFModel.a7Four a7Act
    rw [altLift7At_last]
  rw [he] at hm
  exact ⟨α, hm.realizesMod⟩

theorem MathieuCode24.realizes {ρ : Representation (ZMod 2) Γ W} (h : MathieuCode24 ρ) :
    CFSG.Quasithin.MathieuCode24 (repMulAut ρ).range ⊤ ⊥ :=
  h.realizesMod

theorem MathieuCocode24.realizes {ρ : Representation (ZMod 2) Γ W} (h : MathieuCocode24 ρ) :
    CFSG.Quasithin.MathieuCocode24 (repMulAut ρ).range ⊤ ⊥ :=
  h.realizesMod

theorem MathieuCode23.realizes {ρ : Representation (ZMod 2) Γ W} {x : Fin 24}
    (h : MathieuCode23 ρ x) : CFSG.Quasithin.MathieuCode23 (repMulAut ρ).range ⊤ ⊥ :=
  ⟨x, h.realizesMod⟩

theorem MathieuCocode23.realizes {ρ : Representation (ZMod 2) Γ W} {x : Fin 24}
    (h : MathieuCocode23 ρ x) : CFSG.Quasithin.MathieuCocode23 (repMulAut ρ).range ⊤ ⊥ :=
  ⟨x, h.realizesMod⟩

theorem MathieuCode22.realizes {ρ : Representation (ZMod 2) Γ W} {x y : Fin 24}
    (h : MathieuCode22 ρ x y) : CFSG.Quasithin.MathieuCode22 (repMulAut ρ).range ⊤ ⊥ :=
  ⟨x, y, h.1, h.2.realizesMod⟩

theorem MathieuCocode22.realizes {ρ : Representation (ZMod 2) Γ W} {x y : Fin 24}
    (h : MathieuCocode22 ρ x y) : CFSG.Quasithin.MathieuCocode22 (repMulAut ρ).range ⊤ ⊥ :=
  ⟨x, y, h.1, h.2.realizesMod⟩

end Bridge

end Explicit

end CFSG.Quasithin
