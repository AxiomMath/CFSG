module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTD_linearData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hm : Odd m) (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G))
      (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs)
      (α : Fin N → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (ggTDρB X Bs (ggTDnH w hnk i)) v =
        v - α i v • ι (Additive.ofMul ⟨_, hbk i⟩)) ∧
      (∀ i j, α i (ι (Additive.ofMul ⟨_, hbk j⟩)) = (C i j : ZMod p)) ∧
      (∀ i (b : ↥Bs), ggGamma X hN b = 1 → α i (ι (Additive.ofMul b)) = 0) ∧
      (∀ v, (∀ i, α i v = 0) → ggGamma X hN (Additive.toMul (ι.symm v)) = 1) := by
  obtain ⟨hnk, hbk, F, hFadd, hFφ, hFC, hF1, hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Fin N → Additive ↥Bs →+ ZMod p := fun k =>
    AddMonoidHom.mk' (fun b => F k (Additive.toMul b)) (fun b b' => hFadd k _ _)
  let α : Fin N → Module.Dual (ZMod p) V := fun k =>
    ((f k).comp ι.symm.toAddMonoidHom).toZModLinearMap p
  have hα : ∀ k v, α k v = F k (Additive.toMul (ι.symm v)) := fun _ _ => rfl
  refine ⟨hnk, hbk, α, fun i v => ?_, fun i j => ?_, fun i b hb => ?_, fun v hv => ?_⟩
  · rw [ggLin_apply]
    have hφb : ggTDρB X Bs (ggTDnH w hnk i) (Additive.toMul (ι.symm v)) =
        ((⟨_, hbk i⟩ : ↥Bs) ^ (F i (Additive.toMul (ι.symm v))).val)⁻¹ *
          Additive.toMul (ι.symm v) := by
      apply Subtype.ext
      rw [ggTDρB_apply]
      push_cast
      exact hFφ i _
    rw [hφb, ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, ofMul_toMul,
      AddEquiv.apply_symm_apply, hα, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hFC i j
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hF1 i b hb
  · exact hFsep _ fun k => (hα k v).symm.trans (hv k)

theorem ggTD_card_range_le_pow {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hm : Odd m) (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M)
    : Nat.card (ggGamma X hN).range ≤ p ^ N := by
  classical
  obtain ⟨hnk,hbk,F,hFadd,hFphi,hpair,hFone,hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Bs →* Multiplicative (Fin N → ZMod p) := MonoidHom.mk'
    (fun b => Multiplicative.ofAdd (fun i => F i b))
    (by intro b c; apply Multiplicative.ofAdd.injective; funext i; exact hFadd i b c)
  have hker : f.ker = (ggGamma X hN).ker := by
    ext b
    simp only [MonoidHom.mem_ker]
    change (fun i => F i b) = 0 ↔ ggGamma X hN b = 1
    constructor
    · intro h
      exact hFsep b (fun i => congrFun h i)
    · intro h
      funext i
      exact hFone i b h
  have heq : Nat.card f.range = Nat.card (ggGamma X hN).range := by
    have he1 := Subgroup.card_ker_mul_card_range f
    have he2 := Subgroup.card_ker_mul_card_range (ggGamma X hN)
    rw [hker] at he1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (he1.trans he2.symm)
  have hu : Nat.card f.range ≤ p ^ N := by
    calc Nat.card f.range ≤ Nat.card (Multiplicative (Fin N → ZMod p)) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = p ^ N := by
        rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_zmod,Nat.card_fin]
  exact heq ▸ hu

theorem ggResXDatum_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hM : GGIsWeylMatrix M) (hMC : GGIntCartan M C)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) : GGResXDatum p Bs X := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ :=
    exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin N, inferInstance, inferInstance, M, C, V, hVadd, hVmod, ι,
    (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, hM, hMC, hlin, ?_, hpair,
    ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

end CFSG.StandardType
