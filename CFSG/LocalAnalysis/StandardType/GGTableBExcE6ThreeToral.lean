module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableBExc.E6Three

theorem index_eq_relIndex_of_sup_eq_top {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    [N.Normal] (h : H ⊔ N = ⊤) : H.index = H.relIndex N := by
  have h1 := Subgroup.index_mul_card H
  have h2 := Subgroup.index_mul_card N
  have h3 : N.index = N.relIndex H := by
    rw [← Subgroup.relIndex_sup_right H N, h, Subgroup.relIndex_top_right]
  have h4 := Subgroup.relIndex_mul_card N H
  have h5 := Subgroup.relIndex_mul_card H N
  rw [inf_comm] at h5
  have hc : 0 < Nat.card (N ⊓ H : Subgroup G) := Nat.card_pos
  have hr : 0 < N.relIndex H := by
    unfold Subgroup.relIndex
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have e1 : H.index * (N.relIndex H * Nat.card (N ⊓ H : Subgroup G)) = Nat.card G := by
    rw [h4, h1]
  have e2 : H.relIndex N * (N.relIndex H * Nat.card (N ⊓ H : Subgroup G)) = Nat.card G := by
    rw [← h2, h3, ← h5]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hr hc) (e1.trans e2.symm)

section RootGroup

variable {τ : Tag} {K : Type} [Field K]

theorem exists_rootGroup_normalized_diag [CharP K 2] (i₀ : Fin τ.rank) :
    ∃ U : Subgroup (adjointGroup τ K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ b : Fin τ.rank → Kˣ, ∀ u ∈ U,
        rootDiagUnit τ b * (u : ModGL τ K) * (rootDiagUnit τ b)⁻¹ ∈
          U.map (adjointGroup τ K).subtype := by
  let xh : Multiplicative K →* adjointGroup τ K :=
    { toFun := fun c => ⟨pinnedX τ K (Pi.single i₀ 1) (Multiplicative.toAdd c),
        pinnedX_mem_adjointGroup _ _⟩
      map_one' := Subtype.ext (pinnedX_zero τ K _)
      map_mul' := fun c c' => Subtype.ext (pinnedX_add τ K _ _ _) }
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨xh.range, fun h => ?_, ?_, ?_⟩
  · have h1 : xh (.ofAdd 1) ∈ xh.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : pinnedX τ K (Pi.single i₀ 1) 1 = pinnedX τ K (Pi.single i₀ 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (pinnedX_injective τ K _ h2)
  · rintro ⟨_, ⟨c, rfl⟩⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    change (pinnedX τ K (Pi.single i₀ 1) (Multiplicative.toAdd c)) ^ 2 = 1
    rw [pow_two, ← pinnedX_add, ← two_mul, htwo, zero_mul, pinnedX_zero]
  · rintro b _ ⟨c, rfl⟩
    refine ⟨xh (.ofAdd ((rootChar b (Pi.single i₀ 1) : K) * Multiplicative.toAdd c)), ⟨_, rfl⟩, ?_⟩
    change pinnedX τ K (Pi.single i₀ 1) (Multiplicative.toAdd (Multiplicative.ofAdd
        ((rootChar b (Pi.single i₀ 1) : K) * Multiplicative.toAdd c))) =
      rootDiagUnit τ b * pinnedX τ K (Pi.single i₀ 1) (Multiplicative.toAdd c) *
        (rootDiagUnit τ b)⁻¹
    rw [rootDiagUnit_conj_pinnedX b (isRoot_single τ i₀)]
    rfl

end RootGroup

section Count

variable {τ : Tag} {K : Type} [Field K]

theorem card_le_mul_card_fix_of_le_xHat {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {S : Subgroup (WeylGroup τ)} {E : Subgroup (ModGL τ K)} [Finite E]
    (hE : IsElemAbelian p E) (hEX : E ≤ xHat τ K S) :
    ∃ A : Subgroup (WeylGroup τ), A ≤ S ∧ IsElemAbelian p A ∧
      (A = ⊥ → ∀ e ∈ E, ∃ x, e = rootDiagUnit τ (zetaVec ζ hζ x)) ∧
      Nat.card E ≤
        Nat.card A * Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ A, adAct τ p a x = x} := by
  have hEM : E ≤ monoHat τ K := hEX.trans (xHat_le_monoHat S)
  set ψE : E →* WeylGroup τ := (psiHat τ K).comp (Subgroup.inclusion hEM) with hψE
  have hψS : ∀ e : E, ψE e ∈ S := fun e => (mem_xHat.mp (hEX e.2)).2
  have hker : ∀ e : E, ψE e = 1 → ∃ x, (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) := by
    intro e he
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one (x := Subgroup.inclusion hEM e) he
    have hb' : (e : ModGL τ K) = rootDiagUnit τ b := hb
    have hbp : b ^ p = 1 := by
      have h1 : (e : ModGL τ K) ^ p = 1 := hE.2 _ e.2
      rw [hb', rootDiagUnit_pow] at h1
      exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    obtain ⟨x, hx⟩ := exists_zetaVec_eq hζo hζ hbp
    exact ⟨x, by rw [hb', hx]⟩
  have hfix : ∀ (e₀ : E) (e : E) (x : Fin τ.rank → ZMod p),
      (e : ModGL τ K) = rootDiagUnit τ (zetaVec ζ hζ x) → adAct τ p (ψE e₀) x = x := by
    intro e₀ e x hx
    have hc := conj_rootDiagUnit_of_mem_monoHat (Subgroup.inclusion hEM e₀) (zetaVec ζ hζ x)
    have hcomm : (e₀ : ModGL τ K) * e * (e₀ : ModGL τ K)⁻¹ = e := by
      rw [TableB.IsElemAbelian.comm hE e₀.2 e.2, mul_inv_cancel_right]
    rw [weylTuple_zetaVec] at hc
    have h2 : rootDiagUnit τ (zetaVec ζ hζ (adAct τ p (ψE e₀) x)) =
        rootDiagUnit τ (zetaVec ζ hζ x) := by
      rw [← hx, ← hcomm, hx]
      exact hc.symm
    exact zetaVec_injective hζo hζ (rootDiagUnit_injective h2)
  refine ⟨ψE.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, rfl⟩
    exact hψS e
  · exact isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ψE
  · intro hbot e he
    have h1 : ψE ⟨e, he⟩ ∈ ψE.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact hker ⟨e, he⟩ h1
  · have hcardE := TableB.card_range_mul_card_ker ψE
    choose xf hxf using fun e : ψE.ker => hker e e.2
    have hk : Nat.card ψE.ker ≤
        Nat.card {x : Fin τ.rank → ZMod p // ∀ a ∈ ψE.range, adAct τ p a x = x} := by
      refine Nat.card_le_card_of_injective (fun e => ⟨xf e, ?_⟩) fun a b hab => ?_
      · rintro _ ⟨e₀, rfl⟩
        exact hfix e₀ e (xf e) (hxf e)
      · apply Subtype.ext
        apply Subtype.ext
        have h1 := congrArg Subtype.val hab
        simp only at h1
        rw [hxf a, hxf b, h1]
    calc Nat.card E = Nat.card ψE.range * Nat.card ψE.ker := hcardE.symm
      _ ≤ _ := Nat.mul_le_mul_left _ hk

end Count

theorem card_map_eq_of_ker {G M : Type*} [Group G] [Group M] (f : G →* M) {P : Subgroup G}
    (h : ∀ p ∈ P, f p = 1 → p = 1) : Nat.card (P.map f) = Nat.card P := by
  have hinj : Function.Injective (f.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    exact Subtype.ext (h p p.2 hp)
  have hr : (f.comp P.subtype).range = P.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

section Fin

variable {K : Type} [Field K]

theorem finite_hatGroup [Finite K] : Finite (hatGroup .E6 K) := by
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  refine Finite.of_surjective (fun q : adjointGroup .E6 K × (Fin Tag.E6.rank → Kˣ) =>
    (⟨q.1 * rootDiagUnit .E6 q.2, ⟨q.1, q.1.2, q.2, rfl⟩⟩ : hatGroup .E6 K)) ?_
  rintro ⟨_, g, hg, a, rfl⟩
  exact ⟨(⟨g, hg⟩, a), rfl⟩

end Fin

section Main

variable {K : Type} [Field K]

theorem not_three_dvd_index_xHat [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ ((xHat .E6 K modelHomE6.range).subgroupOf (hatGroup .E6 K)).index := by
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  have hN : ((adjointGroup .E6 K).subgroupOf (hatGroup .E6 K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer adjointGroup_le_hatGroup).2
      hatGroup_le_normalizer
  have hsup : (xHat .E6 K modelHomE6.range).subgroupOf (hatGroup .E6 K) ⊔
      (adjointGroup .E6 K).subgroupOf (hatGroup .E6 K) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨g, hg, y, hy, rfl⟩ := exists_mul_of_mem_hatGroup modelHomE6.range hx
    have e : (⟨g * y, hx⟩ : hatGroup .E6 K) = ⟨g, adjointGroup_le_hatGroup hg⟩ *
        ⟨y, xHat_le_hatGroup _ hy⟩ := rfl
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hg) (Subgroup.mem_subgroupOf.mpr hy)
  rw [index_eq_relIndex_of_sup_eq_top hsup, Subgroup.relIndex_subgroupOf adjointGroup_le_hatGroup]
  have heq : (xHat .E6 K modelHomE6.range).subgroupOf (adjointGroup .E6 K) =
      weylX .E6 K modelHomE6.range := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_weylX_iff_mem_xHat]
  rw [Subgroup.relIndex, heq]
  exact not_three_dvd_index_E6 h3

theorem card_le_and_normalizes_of_le_hatAut [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) :
    Nat.card X ≤ 3 ^ 6 ∧ (3 ^ 6 ≤ Nat.card X →
      ∃ U : Subgroup (adjointGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) := by
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  set κ := hatAut .E6 K with hκ
  set Y : Subgroup (hatGroup .E6 K) := X.comap κ with hY
  set f : Y →* X := (κ.comp Y.subtype).codRestrict X (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hXI hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hXp : IsPGroup 3 (⊤ : Subgroup X) := fun g => by
    obtain ⟨k, hk⟩ := TableB.isPGroup_of_isElemAbelian hX ⟨g.1, g.1.2⟩
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hXp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPX : P.map κ = X := by
    have hcomp : κ.comp Y.subtype = X.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨c, hc⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    (not_three_dvd_index_xHat h3) hP3
  set P' := P.map (MulAut.conj c).toMonoidHom with hP'
  set E : Subgroup (ModGL .E6 K) := P'.map (hatGroup .E6 K).subtype with hEdef
  have hEX : E ≤ xHat .E6 K modelHomE6.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hc hp)
  have hker : ∀ p ∈ P', κ p = 1 → p = 1 := fun p hp h1 =>
    eq_one_of_hatAut_eq_one (xHat_le_monoHat _ (hEX ⟨p, hp, rfl⟩)) h1
  have hP'X : P'.map κ = X.map (MulAut.conj (κ c)).toMonoidHom := by
    have hcomp : κ.comp (MulAut.conj c).toMonoidHom = (MulAut.conj (κ c)).toMonoidHom.comp κ :=
      MonoidHom.ext fun p => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv]
    rw [hP', Subgroup.map_map, hcomp, ← Subgroup.map_map, hPX]
  have hcardP' : Nat.card P' = Nat.card X := by
    rw [← card_map_eq_of_ker κ hker, hP'X,
      Subgroup.card_map_of_injective (MulAut.conj (κ c)).injective]
  have hcardE : Nat.card E = Nat.card X := by
    rw [hEdef, Subgroup.card_map_of_injective (hatGroup .E6 K).subtype_injective, hcardP']
  have hXc : IsElemAbelian 3 (X.map (MulAut.conj (κ c)).toMonoidHom) :=
    TableB.isElemAbelian_map hX _
  have hP'ab : ∀ p ∈ P', ∀ p' ∈ P', p * p' = p' * p := by
    intro p hp p' hp'
    have h1 : κ (p * p' * (p' * p)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul,
        TableB.IsElemAbelian.comm hXc (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
          (hP'X ▸ ⟨p', hp', rfl⟩ : κ p' ∈ _), mul_inv_cancel]
    have h2 := hker _ (mul_mem (mul_mem hp hp') (inv_mem (mul_mem hp' hp))) h1
    exact mul_inv_eq_one.mp h2
  have hP'3 : ∀ p ∈ P', p ^ 3 = 1 := by
    intro p hp
    refine hker _ (pow_mem hp 3) ?_
    rw [map_pow]
    exact hXc.2 _ (hP'X ▸ ⟨p, hp, rfl⟩ : κ p ∈ _)
  have hP'el : IsElemAbelian 3 P' :=
    ⟨⟨⟨fun a b => Subtype.ext (hP'ab a a.2 b b.2)⟩⟩, hP'3⟩
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map hP'el _
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have : Finite E := Finite.of_surjective (fun p : P' => (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : E))
    (by rintro ⟨_, ⟨p, hp, rfl⟩⟩; exact ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨A, hAS, hA, hA1, hcount⟩ := card_le_mul_card_fix_of_le_xHat hζo hζ hE hEX
  by_cases hAb : A = ⊥
  · have hall := hA1 hAb
    choose xf hxf using fun e : E => hall e e.2
    have hle : Nat.card E ≤ 3 ^ 6 := by
      have h := Nat.card_le_card_of_injective xf fun a b hab => Subtype.ext (by
        rw [hxf a, hxf b, hab])
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
      exact h
    refine ⟨hcardE ▸ hle, fun _ => ?_⟩
    obtain ⟨U₀, hU₀, hU₀2, hU₀n⟩ :=
      exists_rootGroup_normalized_diag (τ := .E6) (K := K) ⟨0, by decide⟩
    refine ⟨U₀.map (κ c)⁻¹.toMonoidHom, fun h => hU₀ ?_, hU₀2.map _, ?_⟩
    · rwa [Subgroup.map_eq_bot_iff_of_injective _ (κ c)⁻¹.injective] at h
    · rintro φ hφ _ ⟨u₀, hu₀, rfl⟩
      have hψ : κ c * φ * (κ c)⁻¹ ∈ P'.map κ := by
        rw [hP'X]
        exact ⟨φ, hφ, by simp [MulAut.conj_apply]⟩
      obtain ⟨p, hp, hpψ⟩ := hψ
      have e1 : φ ((κ c)⁻¹ u₀) = (κ c)⁻¹ ((κ c * φ * (κ c)⁻¹) u₀) := by
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [MulEquiv.coe_toMonoidHom, e1, ← hpψ]
      refine ⟨κ p u₀, ?_, rfl⟩
      obtain ⟨v, hv, hveq⟩ := hU₀n (zetaVec ζ hζ (xf ⟨_, ⟨p, hp, rfl⟩⟩)) u₀ hu₀
      have hpx := hxf ⟨_, ⟨p, hp, rfl⟩⟩
      have e2 : κ p u₀ = v := Subtype.ext (by
        rw [coe_hatAut_apply, show ((p : ModGL .E6 K)) = rootDiagUnit .E6 (zetaVec ζ hζ
          (xf ⟨_, ⟨p, hp, rfl⟩⟩)) from hpx]
        exact hveq.symm)
      rw [e2]
      exact hv
  · have hlt := noOffender_E6ad A hAS hA hAb
    have hXlt : Nat.card X < 3 ^ 6 := by
      rw [← hcardE]
      exact lt_of_le_of_lt hcount hlt
    exact ⟨hXlt.le, fun h => absurd h (not_le.mpr hXlt)⟩

end Main

end TableBExc.E6Three

end CFSG.StandardType
