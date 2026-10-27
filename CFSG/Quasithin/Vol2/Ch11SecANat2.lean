module

public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Quasithin.Vol2.Ch11SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

section Flags

variable {W : Type*} [Group W]

theorem mem_map_mulAut {U : Subgroup W} {τ : MulAut W} {w : W} :
    w ∈ U.map τ.toMonoidHom ↔ τ⁻¹ w ∈ U := by
  rw [Subgroup.mem_map_equiv]
  rfl

theorem map_eq_of_mem_stabW {Z : Subgroup W} {τ : MulAut W} (hτ : τ ∈ stabW Z) :
    Z.map τ.toMonoidHom = Z := by
  ext w
  rw [mem_map_mulAut, (mem_stabW.mp hτ) (τ⁻¹ w), MulAut.apply_inv_self]

theorem inv_mem_stabW {Z : Subgroup W} {τ : MulAut W} (hτ : τ ∈ stabW Z) {w : W} :
    τ⁻¹ w ∈ Z ↔ w ∈ Z :=
  ((mem_stabW.mp ((stabW Z).inv_mem hτ)) w).symm

theorem endStableW_map {H : Subgroup (MulAut W)} {Z U : Subgroup W} {τ : MulAut W}
    (hτZ : τ ∈ stabW Z) (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) (hU : EndStableW H Z U) :
    EndStableW H Z (U.map τ.toMonoidHom) := by
  intro φ hφZ hφH u hu
  rw [mem_map_mulAut] at hu ⊢
  set φ' : W →* W := (τ⁻¹).toMonoidHom.comp (φ.comp τ.toMonoidHom)
  have hφ' : ∀ w, φ' w = τ⁻¹ (φ (τ w)) := fun _ => rfl
  have hZ' : ∀ z ∈ Z, φ' z ∈ Z := by
    intro z hz
    rw [hφ', inv_mem_stabW hτZ]
    exact hφZ _ ((mem_stabW.mp hτZ z).mp hz)
  have hH' : ∀ h ∈ H, ∀ w : W, φ' (h w) * (h (φ' w))⁻¹ ∈ Z := by
    intro h hh w
    have h1 := hφH (τ * h * τ⁻¹) (hτH h hh) (τ w)
    have e1 : (τ * h * τ⁻¹) (τ w) = τ (h w) := by simp [MulAut.mul_apply]
    have e2 : h (φ' w) = τ⁻¹ ((τ * h * τ⁻¹) (φ (τ w))) := by
      simp [MulAut.mul_apply, hφ']
    rw [e1] at h1
    rw [hφ', e2, ← map_inv, ← map_mul, inv_mem_stabW hτZ]
    exact h1
  have := hU φ' hZ' hH' _ hu
  rw [hφ'] at this
  simpa using this

theorem isFlagW_map {H P : Subgroup (MulAut W)} {Z U : Subgroup W} {q i : ℕ} {τ : MulAut W}
    (hU : IsFlagW H P Z q i U) (hτZ : τ ∈ stabW Z) (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H)
    (hτP : ∀ g ∈ P, τ⁻¹ * g * τ ∈ P) : IsFlagW H P Z q i (U.map τ.toMonoidHom) := by
  obtain ⟨hZU, hE, hidx, hP⟩ := hU
  refine ⟨?_, endStableW_map hτZ hτH hE, ?_, ?_⟩
  · intro z hz
    rw [mem_map_mulAut]
    exact hZU ((inv_mem_stabW hτZ).mpr hz)
  · rw [← map_eq_of_mem_stabW hτZ, Subgroup.relIndex_map_map_of_injective _ _ τ.injective, hidx]
  · intro g hg w
    rw [mem_map_mulAut, mem_map_mulAut]
    have := (mem_stabW.mp (hP (hτP g hg))) (τ⁻¹ w)
    simpa [MulAut.mul_apply] using this

end Flags

variable {G : Type} [Group G]

@[expose] noncomputable def conjHomL (V A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    ↥A →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hA)

theorem conjHomL_apply {V A : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) (a : ↥A) :
    conjHomL V A hA a = conjV V a (hA a.2) :=
  rfl

theorem range_conjHomL (V A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (conjHomL V A hA).range = autOn A V := by
  unfold conjHomL autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem ker_conjHomL (V A : Subgroup G) (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    (conjHomL V A hA).ker = (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, conjHomL_apply]
  constructor
  · intro h
    refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h
    simp only [conjV_apply_coe, MulAut.one_apply] at this
    calc v * (a : G) = ((a : G) * v * (a : G)⁻¹) * a := by rw [this]
      _ = a * v := by group
  · rintro ⟨-, hc⟩
    ext v
    rw [conjV_apply_coe, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hc v v.2
    rw [← h, mul_inv_cancel_right]

variable [Finite G]

theorem inf_centralizer_eq_pCoreOf {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L V)) :
    L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := L ⊓ Subgroup.centralizer (V : Set G)
  set f := (conjHomL V L hL).rangeRestrict
  have hf : Function.Surjective f := (conjHomL V L hL).rangeRestrict_surjective
  have hker : f.ker = N.subgroupOf L := by
    rw [MonoidHom.ker_rangeRestrict, ker_conjHomL]
  have hle : CFSG.pCore 2 ↥L ≤ N.subgroupOf L := by
    rw [← hker]
    intro x hx
    set e' : ↥(conjHomL V L hL).range ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
      (MulEquiv.subgroupCongr (range_conjHomL V L hL)).trans e.symm
    set K := ((CFSG.pCore 2 ↥L).map f).map e'.toMonoidHom
    have hKn : K.Normal :=
      ((CFSG.pCore_normal (p := 2) (G := ↥L)).map f hf).map e'.toMonoidHom e'.surjective
    have hKp : IsPGroup 2 K := ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map f).map _
    have hK : K ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (CFSG.LieType.BorelTits.le_pCore 2 hKn hKp).trans_eq (open_pCore_eq 2 _)
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff] at hK
    have hfx : f x ∈ (CFSG.pCore 2 ↥L).map f := Subgroup.mem_map_of_mem f hx
    have : e' (f x) ∈ K := Subgroup.mem_map_of_mem e'.toMonoidHom hfx
    rw [hK, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
    exact this
  have hcard : Nat.card (N.subgroupOf L) = Nat.card (CFSG.pCore 2 ↥L) := by
    have h1 : Nat.card (autOn L V) = N.relIndex L := card_autOn_eq_relIndex hL
    have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (autOn L V) :=
      Nat.card_congr e.toEquiv
    have h3 := (N.subgroupOf L).card_mul_index
    have h4 := (CFSG.pCore 2 ↥L).card_mul_index
    rw [Subgroup.relIndex] at h1
    have h5 : (N.subgroupOf L).index = (CFSG.pCore 2 ↥L).index := by
      rw [← h1, ← h2, Subgroup.index_eq_card]
    have hpos : 0 < (N.subgroupOf L).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [h5] at h3 hpos
    exact Nat.eq_of_mul_eq_mul_right hpos (h3.trans h4.symm)
  have heq : N.subgroupOf L = CFSG.pCore 2 ↥L :=
    (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
  have hNL : N ≤ L := inf_le_left
  calc N = (N.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hNL).symm
    _ = pCoreOf 2 L := by rw [heq, pCoreOf]

end CFSG.Quasithin.Vol2.Ch11.SecA
