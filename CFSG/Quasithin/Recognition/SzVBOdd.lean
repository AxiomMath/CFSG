module

public import CFSG.Quasithin.Recognition.SzVBCount
public import CFSG.Quasithin.Recognition.SzVBPermComm
public import CFSG.Quasithin.Recognition.SzVBLocal
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

@[expose] def kerAct (P V : Subgroup G) : Subgroup ↥P :=
  (MulAction.toPermHom ↥P (ConjSet P V)).ker

structure BenderLocalFacts (P S V : Subgroup G) : Prop where
  card_odd : Odd (Nat.card (ConjSet P V))
  five_le : 5 ≤ Nat.card (ConjSet P V)
  S_le : S ≤ P
  S_pGroup : IsPGroup 2 S
  S_le_normalizer : S ≤ Subgroup.normalizer (V : Set G)
  ker_inv_le : ∀ x : ↥P, x * x = 1 → x ∈ kerAct P V → (x : G) ∈ pCoreOf 2 P
  S_transitive : ∀ U U' : ConjSet P V, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
    ∃ s : ↥P, (s : G) ∈ S ∧ s • U = U'
  orbit_le_four : ∀ E : Subgroup ↥P,
    (∀ e ∈ E, ∀ e' ∈ E, ∀ U : ConjSet P V, e • U = U ∨ e' • U = U ∨ e • U = e' • U) →
    (kerAct P V).relIndex E ≤ 4
  four_cycles : ∀ y : ↥P, y * y = 1 → y ∉ kerAct P V →
    ∃ R : Finset (ConjSet P V), 4 ≤ R.card ∧ ∀ U ∈ R, y • U ≠ U ∧ y • U ∉ R

namespace OddAux

theorem conjSub_eq_of_mem_normalizer' {k : G} {V : Subgroup G}
    (hk : k ∈ Subgroup.normalizer (V : Set G)) : conjSub k V = V := by
  ext y
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hk) y
  simpa using this.symm

theorem conjSet_isPretransitive (P V : Subgroup G) :
    MulAction.IsPretransitive ↥P (ConjSet P V) := by
  refine ⟨fun U U' => ?_⟩
  obtain ⟨x, hx, hU⟩ := U.2
  obtain ⟨x', hx', hU'⟩ := U'.2
  refine ⟨⟨x' * x⁻¹, P.mul_mem hx' (P.inv_mem hx)⟩, Subtype.ext ?_⟩
  show conjSub (x' * x⁻¹) U.1 = U'.1
  rw [hU, hU', ← conjSub_mul, inv_mul_cancel_right]

theorem mem_kerAct {P V : Subgroup G} {s : ↥P} :
    s ∈ kerAct P V ↔ ∀ U : ConjSet P V, s • U = U := by
  unfold kerAct
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  simp [MulAction.toPermHom_apply, MulAction.toPerm_apply]

theorem conjAct_coe (W : Subgroup G) (x : Subgroup.normalizer (W : Set G)) (a : ↥W) :
    ((conjAct W x a : ↥W) : G) = x * a * (x : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply W x a

theorem wSide [Finite G] {P S V W : Subgroup G} {z g : G} {t : ConjSet P V → G}
    (hB : BenderLocalFacts P S V) (hW : IsElemAbelian 2 W)
    (hPN : P ≤ Subgroup.normalizer (W : Set G)) (ht : TDataG P W t z)
    (hquad : ⁅⁅W, conjSub g W⁆, conjSub g W⁆ = ⊥) :
    (∀ E : Subgroup ↥P, (∀ e ∈ E, (e : G) ∈ conjSub g W) →
        (kerAct P V).relIndex E ≤ 4) ∧
    ∀ y : ↥P, y * y = 1 → y ∉ kerAct P V →
      ∃ ψ : ↥W →* ↥W, (∀ a : ↥W, ((ψ a : ↥W) : G) = y * a * (y : G)⁻¹ * (a : G)⁻¹) ∧
        2 ^ 4 ≤ Nat.card ψ.range := by
  classical
  have : Fintype (ConjSet P V) := Fintype.ofFinite _
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  have hmul : ∀ a b : ↥W, ((a * b : ↥W) : G) = (a : G) * (b : G) := fun a b => rfl
  have hinvW : ∀ a : ↥W, ((a⁻¹ : ↥W) : G) = (a : G)⁻¹ := fun a => rfl
  have honeW : ((1 : ↥W) : G) = 1 := rfl
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥P →* MulAut ↥W,
      ∀ (x : ↥P) (a : ↥W), ((ρ x a : ↥W) : G) = x * a * (x : G)⁻¹ :=
    ⟨(conjAct W).comp (Subgroup.inclusion hPN),
      fun x a => conjAct_coe W (Subgroup.inclusion hPN x) a⟩
  obtain ⟨tW, htW⟩ : ∃ tW : ConjSet P V → ↥W, ∀ a, ((tW a : ↥W) : G) = t a :=
    ⟨fun a => ⟨t a, ht.t_mem a⟩, fun a => rfl⟩
  obtain ⟨zW, hzW⟩ : ∃ zW : ↥W, (zW : G) = z := ⟨⟨z, ht.z_mem⟩, rfl⟩
  have hT : TData ρ tW zW := by
    refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, fun h => ht.z_ne_one ?_,
      fun x => Subtype.ext ?_, fun x a => ?_, fun a b hab => ?_⟩
    · rw [hmul, htW, honeW]
      exact ht.t_sq a
    · rw [hmul, hzW, honeW]
      exact ht.z_sq
    · rw [← hzW, h, honeW]
    · rw [hρ, hzW]
      calc (x : G) * z * (x : G)⁻¹ = z * x * (x : G)⁻¹ := by rw [ht.z_cent x x.2]
        _ = z := mul_inv_cancel_right _ _
    · rcases ht.act x a with h | h
      · refine Or.inl (Subtype.ext ?_)
        rw [hρ, htW, htW]
        exact h
      · refine Or.inr (Subtype.ext ?_)
        rw [hρ, hmul, htW, htW, hzW]
        exact h
    · refine ⟨fun h => (ht.distinct a b hab).1 ?_, fun h => (ht.distinct a b hab).2 ?_⟩
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, honeW] at this
      · have := congrArg Subtype.val h
        rwa [hmul, htW, htW, hzW] at this
  have hΩodd : Odd (Fintype.card (ConjSet P V)) := by
    rw [← Nat.card_eq_fintype_card]
    exact hB.card_odd
  have hΩ5 : 5 ≤ Fintype.card (ConjSet P V) := by
    rw [← Nat.card_eq_fintype_card]
    exact hB.five_le
  have hker : KerProp tW zW := by
    refine kerProp_of_tData hT (conjSet_isPretransitive P V) (S.subgroupOf P)
      (hB.S_pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hB.S_le).symm) (ConjSet.base P V)
      ?_ ?_ hΩodd
    · intro r hr
      exact Subtype.ext
        (conjSub_eq_of_mem_normalizer' (hB.S_le_normalizer (Subgroup.mem_subgroupOf.mp hr)))
    · intro a b ha hb
      obtain ⟨s, hs, h⟩ := hB.S_transitive a b ha hb
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, h⟩
  have hcomm_coe : ∀ (s : ↥P) (a : ↥W), ((commMap ρ s a : ↥W) : G) =
      (s : G) * a * (s : G)⁻¹ * (a : G)⁻¹ := by
    intro s a
    rw [commMap_apply, hmul, hinvW, hρ]
  refine ⟨?_, ?_⟩
  · intro E hE
    refine hB.orbit_le_four E fun e he e' he' U => ?_
    refine orbit_le_two_of_quadratic hT hker hΩ5 e e' U (Or.inl ?_)
    have h1 : ((e : G) * t U * (e : G)⁻¹ * (t U)⁻¹) ∈ ⁅W, conjSub g W⁆ := by
      rw [Subgroup.commutator_comm W (conjSub g W)]
      exact Subgroup.commutator_mem_commutator (hE e he) (ht.t_mem U)
    have h2 : ((e' : G) * ((e : G) * t U * (e : G)⁻¹ * (t U)⁻¹) * (e' : G)⁻¹ *
        ((e : G) * t U * (e : G)⁻¹ * (t U)⁻¹)⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hquad, Subgroup.commutator_comm ⁅W, conjSub g W⁆ (conjSub g W)]
      exact Subgroup.commutator_mem_commutator (hE e' he') h1
    apply Subtype.ext
    rw [hcomm_coe, hcomm_coe, htW, honeW]
    exact Subgroup.mem_bot.mp h2
  · intro y hyy hy
    obtain ⟨R, hR4, hR⟩ := hB.four_cycles y hyy hy
    refine ⟨commMap ρ y, hcomm_coe y, ?_⟩
    have hψ : ∀ x : ConjSet P V, commMap ρ y (tW x) = tW (y • x) * tW x ∨
        commMap ρ y (tW x) = tW (y • x) * tW x * zW := by
      intro x
      have hinv : (tW x)⁻¹ = tW x := inv_eq_of_mul_eq_one_right (hT.t_sq x)
      rw [commMap_apply, hinv]
      rcases hT.act y x with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h]; exact mul_right_comm _ _ _)
    calc 2 ^ 4 ≤ 2 ^ R.card := Nat.pow_le_pow_right (by norm_num) hR4
      _ ≤ Nat.card (commMap ρ y).range :=
        card_range_ge_of_indep hker hΩodd hT.t_sq hT.z_sq (commMap ρ y) (fun x => y • x)
          (MulAction.injective y) R hR hψ

theorem card_subgroupOf_zpowers_le [Finite G] (W : Subgroup G) {u : G} (hu : u * u = 1) :
    Nat.card ((Subgroup.zpowers u).subgroupOf W) ≤ 2 := by
  have h1 : Nat.card ((Subgroup.zpowers u).subgroupOf W) ≤ Nat.card (Subgroup.zpowers u) := by
    refine Nat.card_le_card_of_injective
      (fun t => (⟨t.1.1, Subgroup.mem_subgroupOf.mp t.2⟩ : ↥(Subgroup.zpowers u))) ?_
    intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu)
  rw [Nat.card_zpowers] at h1
  exact h1.trans (Nat.le_of_dvd (by norm_num) h2)

def conjInto (g : G) (W P : Subgroup G) (h : conjSub g W ≤ P) : ↥W →* ↥P where
  toFun a := ⟨g * a * g⁻¹, h (mul_mem_conjSub a.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem card_range_le_eight [Finite G] {P V : Subgroup G} {z g w : G} (hK : KleinData P V z)
    (hW'P : conjSub g (conjClosure V P) ≤ P) (hw : w ∈ conjClosure V P)
    (hrel : ∀ E : Subgroup ↥P, (∀ e ∈ E, (e : G) ∈ conjSub g (conjClosure V P)) →
      (kerAct P V).relIndex E ≤ 4)
    (ψ : ↥(conjClosure V P) →* ↥(conjClosure V P))
    (hψ : ∀ a : ↥(conjClosure V P), ((ψ a : ↥(conjClosure V P)) : G) =
      (g⁻¹ * w * g) * a * (g⁻¹ * w * g)⁻¹ * (a : G)⁻¹) :
    Nat.card ψ.range ≤ 8 := by
  have hu : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hK.z_mul_self]; group
  have hT : Nat.card ((Subgroup.zpowers (g⁻¹ * z * g)).subgroupOf (conjClosure V P)) ≤ 2 :=
    card_subgroupOf_zpowers_le _ hu
  have hD : ((kerAct P V).comap (conjInto g (conjClosure V P) P hW'P)).index ≤ 4 := by
    rw [Subgroup.index_comap]
    refine hrel _ ?_
    rintro _ ⟨a, rfl⟩
    exact mul_mem_conjSub a.2
  have hDT : ∀ d ∈ (kerAct P V).comap (conjInto g (conjClosure V P) P hW'P),
      ψ d ∈ (Subgroup.zpowers (g⁻¹ * z * g)).subgroupOf (conjClosure V P) := by
    intro d hd
    have hc : g * (d : G) * g⁻¹ ∈ P := hW'P (mul_mem_conjSub d.2)
    have hfix : ∀ U : ConjSet P V, (⟨g * (d : G) * g⁻¹, hc⟩ : ↥P) • U = U :=
      mem_kerAct.mp (Subgroup.mem_comap.mp hd)
    have hcomm := commutator_mem_of_fixes hK hc hfix hw
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hψ d]
    have e1 : (g⁻¹ * w * g) * (d : G) * (g⁻¹ * w * g)⁻¹ * (d : G)⁻¹ =
        g⁻¹ * (g * (d : G) * g⁻¹ * w * (g * (d : G) * g⁻¹)⁻¹ * w⁻¹)⁻¹ * g := by group
    rw [e1]
    rcases hcomm with h | h
    · rw [h]
      simp
    · rw [h]
      have e2 : g⁻¹ * z⁻¹ * g = (g⁻¹ * z * g)⁻¹ := by group
      rw [e2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  calc Nat.card ψ.range
      ≤ ((kerAct P V).comap (conjInto g (conjClosure V P) P hW'P)).index *
        Nat.card ((Subgroup.zpowers (g⁻¹ * z * g)).subgroupOf (conjClosure V P)) :=
        card_range_le_index_mul ψ _ _ hDT
    _ ≤ 4 * 2 := Nat.mul_le_mul hD hT
    _ = 8 := by norm_num

end OddAux

theorem odd_case_false [Finite G] {P S V : Subgroup G} {z g : G} (hK : KleinData P V z)
    (hB : BenderLocalFacts P S V) (hW : IsElemAbelian 2 (conjClosure V P))
    (hWP : conjSub g P ≥ conjClosure V P) (hW'P : conjSub g (conjClosure V P) ≤ P)
    (hcomm : ⁅conjClosure V P, conjSub g (conjClosure V P)⁆ ≤
      conjClosure V P ⊓ conjSub g (conjClosure V P))
    (hquad : ⁅⁅conjClosure V P, conjSub g (conjClosure V P)⁆, conjSub g (conjClosure V P)⁆ = ⊥)
    (hnontriv : ∃ w ∈ conjClosure V P, ∃ hy : g⁻¹ * w * g ∈ P,
      (⟨g⁻¹ * w * g, hy⟩ : ↥P) ∉ kerAct P V) : False := by
  have _ := hWP
  have _ := hcomm
  obtain ⟨w, hw, hy, hnot⟩ := hnontriv
  obtain ⟨t, ht⟩ := exists_tDataG hK
  have hwsq : w * w = 1 := by
    have := F7.isElemAbelian_pow_eq_one hW hw
    rwa [pow_two] at this
  have hyy : (⟨g⁻¹ * w * g, hy⟩ : ↥P) * ⟨g⁻¹ * w * g, hy⟩ = 1 := by
    refine Subtype.ext ?_
    show g⁻¹ * w * g * (g⁻¹ * w * g) = 1
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hwsq]; group
  obtain ⟨hrel, hlow⟩ := OddAux.wSide (g := g) hB hW (le_normalizer_conjClosure V P) ht hquad
  obtain ⟨ψ, hψ, hcard⟩ := hlow _ hyy hnot
  have hup := OddAux.card_range_le_eight hK hW'P hw hrel ψ hψ
  exact absurd (hcard.trans hup) (by norm_num)

end CFSG.Quasithin.SzVB
