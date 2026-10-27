module

public import CFSG.Quasithin.Background.SmithB45ExcL2

public section

namespace CFSG.Quasithin.B45Exc

open CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X3
  CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin

variable {p : ℕ} [hpf : Fact p.Prime]

theorem primeLinearTwoExclusion2F
    (hp11 : 11 ≤ p) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) [Nontrivial W] {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : CQ L ≃* projectiveSL 2 (ZMod p)) :
    ∀ A : Subgroup (MulAut W),
      A ≤ Subgroup.normalizer (L : Set (MulAut W)) → A ≠ ⊥ → IsElemAbelian2 A →
        Nat.card A ^ 2 * Nat.card (fixV A) < Nat.card W := by
  have hp5 : 5 ≤ p := by omega
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have := hperf
  have hodd := odd_card_center_of_irreducible hW hL
  let π : ↥L →* projectiveSL 2 (ZMod p) :=
    α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπs : Function.Surjective π := α.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk x : CQ L) = 1 := α.injective (by rw [map_one]; exact h)
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro h
      have h1 : (QuotientGroup.mk x : CQ L) = 1 := (QuotientGroup.eq_one_iff x).2 h
      show α (QuotientGroup.mk x) = 1
      rw [h1, map_one]
  have hbound : Nat.card π.ker ≤ 2 := p2_central_kernel_bound hp5 π hπs hπk.le
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [hπk] at hbound
    have h1 : Nat.card (Subgroup.center ↥L) = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Subgroup.card_eq_one.1 h1
  intro A hA hA1 hA2
  by_contra hne
  push Not at hne
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (hπk.trans hcenter)
  let θ : ↥L ≃* PSL2 (ZMod p) := (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).trans (p2Equiv (ZMod p))
  have hHn : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hA
  have hNnormal : (L.subgroupOf (L ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  let θ' : (L.subgroupOf (L ⊔ A)) ≃* PSL2 (ZMod p) :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).trans θ
  have hC : ∀ z : ↥(L ⊔ A), (∀ n ∈ L.subgroupOf (L ⊔ A), z * n = n * z) → z = 1 := by
    intro z hz
    obtain ⟨l, hl, a, ha, hzla⟩ := mem_sup_of_le_normalizer hA z.2
    have hzc : ∀ y ∈ L, (z : MulAut W) * y = y * (z : MulAut W) := by
      intro y hy
      have hyN : (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := hy
      exact congrArg Subtype.val (hz _ hyN)
    have ha2 : a * a = 1 := by
      have := hA2.2 a ha
      rwa [pow_two] at this
    have hzl : (z : MulAut W) * l⁻¹ = l⁻¹ * (z : MulAut W) := hzc _ (L.inv_mem hl)
    have hal : a = l⁻¹ * (z : MulAut W) := by rw [hzla]; group
    have hkey : (l⁻¹ * (z : MulAut W)) * (l⁻¹ * (z : MulAut W)) =
        l⁻¹ * l⁻¹ * ((z : MulAut W) * (z : MulAut W)) := by
      calc (l⁻¹ * (z : MulAut W)) * (l⁻¹ * (z : MulAut W))
          = l⁻¹ * ((z : MulAut W) * l⁻¹) * (z : MulAut W) := by group
        _ = l⁻¹ * (l⁻¹ * (z : MulAut W)) * (z : MulAut W) := by rw [hzl]
        _ = l⁻¹ * l⁻¹ * ((z : MulAut W) * (z : MulAut W)) := by group
    have hzz : (z : MulAut W) * (z : MulAut W) = l * l := by
      rw [← hal, ha2] at hkey
      have := eq_inv_of_mul_eq_one_right hkey.symm
      simpa using this
    have hzzL : (z : MulAut W) * (z : MulAut W) ∈ L := by rw [hzz]; exact L.mul_mem hl hl
    have hzz1 : (z : MulAut W) * (z : MulAut W) = 1 := by
      have hcen : (⟨(z : MulAut W) * (z : MulAut W), hzzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        show (y : MulAut W) * ((z : MulAut W) * (z : MulAut W)) =
          ((z : MulAut W) * (z : MulAut W)) * (y : MulAut W)
        have hy := hzc y y.2
        calc (y : MulAut W) * ((z : MulAut W) * (z : MulAut W))
            = ((y : MulAut W) * (z : MulAut W)) * (z : MulAut W) := by rw [mul_assoc]
          _ = ((z : MulAut W) * (y : MulAut W)) * (z : MulAut W) := by rw [← hy]
          _ = (z : MulAut W) * ((y : MulAut W) * (z : MulAut W)) := by rw [mul_assoc]
          _ = (z : MulAut W) * ((z : MulAut W) * (y : MulAut W)) := by rw [← hy]
          _ = ((z : MulAut W) * (z : MulAut W)) * (y : MulAut W) := by rw [mul_assoc]
      rw [hcenter, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    have hz1 : (z : MulAut W) = 1 :=
      eq_one_of_centralizes_irreducible hW hL (fun l hl => (hzc l hl)) hzz1
    exact Subtype.ext hz1
  obtain ⟨Y, e, hY, he⟩ := aut_structure hp5 θ' hC
  have hAH : A ≤ L ⊔ A := le_sup_right
  let ρH : ↥(L ⊔ A) →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp (L ⊔ A).subtype
  have hN : ∀ n ∈ L.subgroupOf (L ⊔ A), ((e n : Y) : PGL2 (ZMod p)) ∈ pglS (ZMod p) := by
    intro n hn
    have := he ⟨n, hn⟩
    rw [show (((⟨n, hn⟩ : L.subgroupOf (L ⊔ A)) : ↥(L ⊔ A))) = n from rfl] at this
    rw [this]
    exact ⟨_, rfl⟩
  have hρH : ∀ (g : ↥(L ⊔ A)) (v : Additive W), ρH g v = Additive.ofMul ((g : MulAut W)
      (Additive.toMul v)) := fun g v => rfl
  have hcomm : QuasithinUnique.Setup.Family.commSub ρH (L.subgroupOf (L ⊔ A)) = ⊤ := by
    set D := QuasithinUnique.Setup.Family.commSub ρH (L.subgroupOf (L ⊔ A)) with hD
    have hDinv : ∀ g ∈ L, ∀ x ∈ D, binaryLin g x ∈ D := by
      intro g hg x hx
      have hgH : g ∈ L ⊔ A := Subgroup.mem_sup_left hg
      have hle : D ≤ D.comap (binaryLin g : Additive W →ₗ[ZMod 2] Additive W) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨n, hn, v, rfl⟩
        have hn' : (⟨g, hgH⟩ * n * ⟨g, hgH⟩⁻¹ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := by
          have hnL : (n : MulAut W) ∈ L := hn
          show g * (n : MulAut W) * g⁻¹ ∈ L
          exact L.mul_mem (L.mul_mem hg hnL) (L.inv_mem hg)
        have hgg : ∀ u : Additive W, binaryLin g⁻¹ (binaryLin g u) = u := fun u => by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        have hkey : binaryLin g (ρH n v - v) =
            ρH (⟨g, hgH⟩ * n * ⟨g, hgH⟩⁻¹) (binaryLin g v) - binaryLin g v := by
          rw [map_sub]
          congr 1
          show binaryLin g (binaryLin (n : MulAut W) v) =
            binaryLin (g * (n : MulAut W) * g⁻¹) (binaryLin g v)
          rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgg]
        show binaryLin g (ρH n v - v) ∈ D
        rw [hkey]
        exact Submodule.subset_span ⟨_, hn', binaryLin g v, rfl⟩
      exact hle hx
    rcases irr_module_of_irr hL D hDinv with h | h
    · exfalso
      have hLne : ∃ l ∈ L, l ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hsub : Subsingleton ↥L := ⟨fun x y => Subtype.ext
          ((hcon x x.2).trans (hcon y y.2).symm)⟩
        have : Subsingleton (CQ L) := inferInstance
        have hnt := (p2_isSimpleGroup (p := p) hp5).toNontrivial
        have : Subsingleton (projectiveSL 2 (ZMod p)) := α.symm.injective.subsingleton
        exact not_subsingleton _ this
      obtain ⟨l, hl, hl1⟩ := hLne
      obtain ⟨w, hw⟩ : ∃ w : W, l w ≠ w := by
        by_contra hcon
        push Not at hcon
        exact hl1 (MulEquiv.ext hcon)
      have hlN : (⟨l, Subgroup.mem_sup_left hl⟩ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := hl
      have hmem : ρH ⟨l, Subgroup.mem_sup_left hl⟩ (Additive.ofMul w) - Additive.ofMul w ∈ D :=
        Submodule.subset_span ⟨_, hlN, Additive.ofMul w, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      apply hw
      have h1 := congrArg Additive.toMul hmem
      simp only [hρH, toMul_sub, toMul_ofMul, toMul_zero] at h1
      exact div_eq_one.1 h1
    · exact h
  have hB1 : A.subgroupOf (L ⊔ A) ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨a, hAH a.2⟩, a.2⟩, fun h => ha ?_⟩
    exact Subtype.ext (congrArg (fun x : ↥(A.subgroupOf (L ⊔ A)) => ((x : ↥(L ⊔ A)) : MulAut W)) h)
  have hBc : ∀ a ∈ A.subgroupOf (L ⊔ A), ∀ b ∈ A.subgroupOf (L ⊔ A), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hA2.1 _ ha _ hb)
  have hB2 : ∀ a ∈ A.subgroupOf (L ⊔ A), a * a = 1 := fun a ha => by
    apply Subtype.ext
    have := hA2.2 _ ha
    rwa [pow_two] at this
  have hfix : Nat.card (fixedSub ρH (A.subgroupOf (L ⊔ A))) = Nat.card (fixV A) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => ?_⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun b hb => ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
    · have h1 := x.2 ⟨a, hAH ha⟩ ha
      exact congrArg Additive.toMul h1
    · have hb' : (b : MulAut W) ∈ A := hb
      have h1 := w.2 (b : MulAut W) hb'
      exact congrArg Additive.ofMul h1
  have hcardB : Nat.card (A.subgroupOf (L ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hpgrp : IsPGroup 2 (A.subgroupOf (L ⊔ A)) := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB2 (a : ↥(L ⊔ A)) a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) -
      Module.finrank (ZMod 2) (fixedSub ρH (A.subgroupOf (L ⊔ A))) ≤
        2 * Nat.log 2 (Nat.card (A.subgroupOf (L ⊔ A))) := by
    refine finrank_sub_le_two_log_of_card_le _ hk ?_
    rw [hcardE, hcardB, hfix]
    exact hne
  exact p2_module_data2F hp11 ρH e hY hN hcomm hB1 hBc hB2 hoff

end CFSG.Quasithin.B45Exc
