module

public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.D36Support
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Perm

variable {W : Type} [CommGroup W]

private theorem three_map_inv_of_map_eq {x : MulAut W} {J J' : Subgroup W}
    (h : J.map x.toMonoidHom = J') : J'.map x⁻¹.toMonoidHom = J := by
  rw [← h, ← map_mul_aut', inv_mul_cancel]
  ext u
  simp

private def threePermSub (U U' : Subgroup W) : Subgroup (MulAut W) where
  carrier := {x | (U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
    (U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U)}
  one_mem' := by
    left
    constructor <;> (ext u; simp)
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, map_mul_aut'] at hx hy ⊢
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp only [h1, h2, h3, h4, and_self, true_or, or_true]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨three_map_inv_of_map_eq h1, three_map_inv_of_map_eq h2⟩
    · exact Or.inr ⟨three_map_inv_of_map_eq h2, three_map_inv_of_map_eq h1⟩

private theorem three_mem_permSub_iff {U U' : Subgroup W} {x : MulAut W} :
    x ∈ threePermSub U U' ↔ (U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
      (U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U) := Iff.rfl

end Perm

section Three

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem d3Std_Mp_le (hD : D3Std M Mp T L V) : Mp ≤ M := by
  rw [hD.hyp.Mp_eq]
  exact conjClosure_le fun s hs z hz =>
    M.mul_mem (M.mul_mem (hD.hyp.sylow.1 hs) (le_of_mem_cComp hD.hyp.comp hz))
      (M.inv_mem (hD.hyp.sylow.1 hs))

theorem d35_three (hD : D3Std M Mp T L V) (hMp : Mp = L) {t : MulAut W} (ht : t ∈ T)
    (htV : t ∉ stabSub V) (hTs : ∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V)
    (hsum : IsSumMod (orbSup T V ⊓ fixV L) V (V.map t.toMonoidHom) (orbSup T V))
    (hC : orbSup T V ⊓ fixV Mp = ⊥) (A : Subgroup (MulAut W)) (hA : A ≤ T)
    (hQ : autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V))) : A ≤ stabSub V := by
  subst hMp
  have hD' := hD.hyp
  rw [hC] at hsum
  obtain ⟨hsup0, hinf0⟩ := hsum
  have hsup : V ⊔ V.map t.toMonoidHom = orbSup T V := by rw [hsup0, sup_bot_eq]
  have hinf : V ⊓ V.map t.toMonoidHom = ⊥ := by
    rw [sup_bot_eq, sup_bot_eq] at hinf0
    exact le_bot_iff.mp hinf0
  have hVle : V ≤ orbSup T V := le_orbSup T V
  have hVtle : V.map t.toMonoidHom ≤ orbSup T V := map_le_orbSup ht
  have hVinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hD'.irr.2.1 ⟨x, hx⟩ v hv
  have hMpS : Mp ≤ stabSub V := le_stabSub_of_forall_memQ2 hVinv
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := fun s hs =>
    hD'.Mp_normal (hD'.sylow.1 hs)
  have hMpP : Mp ≤ threePermSub V (V.map t.toMonoidHom) := by
    intro x hx
    refine Or.inl ⟨mem_stabSub_iff_map_eq.mp (hMpS hx), ?_⟩
    have hx' : t⁻¹ * x * t ∈ Mp :=
      (Subgroup.mem_normalizer_iff''.mp (hTn ht) x).mp hx
    have e : x * t = t * (t⁻¹ * x * t) := by group
    rw [← map_mul_aut', e, map_mul_aut', mem_stabSub_iff_map_eq.mp (hMpS hx')]
  have key : ∀ y ∈ T, y ∉ stabSub V → V.map y.toMonoidHom = V.map t.toMonoidHom := by
    intro y hy hyV
    rcases hTs y hy with h | h
    · exact absurd h hyV
    · have e : y = t * (t⁻¹ * y) := by group
      rw [e, map_mul_aut', mem_stabSub_iff_map_eq.mp h]
  have hTP : T ≤ threePermSub V (V.map t.toMonoidHom) := by
    intro s hs
    rw [three_mem_permSub_iff]
    by_cases hsV : s ∈ stabSub V
    · left
      refine ⟨mem_stabSub_iff_map_eq.mp hsV, ?_⟩
      have hst : s * t ∉ stabSub V := fun h => htV (by
        have h1 := (stabSub V).mul_mem ((stabSub V).inv_mem hsV) h
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1)
      rw [← map_mul_aut', key (s * t) (T.mul_mem hs ht) hst]
    · right
      refine ⟨key s hs hsV, ?_⟩
      rw [← map_mul_aut']
      rcases hTs (s * t) (T.mul_mem hs ht) with h | h
      · exact mem_stabSub_iff_map_eq.mp h
      · exfalso
        have e : s * t = t * (t⁻¹ * (s * t)) := by group
        have h1 : V.map (s * t).toMonoidHom = V.map t.toMonoidHom := by
          rw [e, map_mul_aut', mem_stabSub_iff_map_eq.mp h]
        rw [map_mul_aut'] at h1
        have h2 : (V.map t.toMonoidHom).map s.toMonoidHom = V.map s.toMonoidHom :=
          h1.trans (key s hs hsV).symm
        have h3 : V.map t.toMonoidHom = V :=
          Subgroup.map_injective (f := s.toMonoidHom) s.injective h2
        exact htV (mem_stabSub_iff_map_eq.mpr h3)
  have hTS : TwoSummands (autSub (Mp ⊔ T) (orbSup T V)) (V.subgroupOf (orbSup T V))
      ((V.map t.toMonoidHom).subgroupOf (orbSup T V)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have h : (x : W) ∈ V ⊓ V.map t.toMonoidHom := ⟨hx.1, hx.2⟩
      rw [hinf, Subgroup.mem_bot] at h
      exact (Subgroup.mem_bot).mpr (Subtype.ext h)
    · rw [← Subgroup.subgroupOf_sup hVle hVtle, hsup, Subgroup.subgroupOf_self]
    · intro g hg
      obtain ⟨x, hxX, rfl⟩ := mem_autSub.mp hg
      have hxP := sup_le hMpP hTP hxX
      rw [map_subgroupOf_resHomQ2, map_subgroupOf_resHomQ2]
      rcases three_mem_permSub_iff.mp hxP with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
      · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
  have hrk : 2 < rk ↥(V.subgroupOf (orbSup T V)) := by
    have hrkeq : rk ↥(V.subgroupOf (orbSup T V)) = rk ↥V := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv]
    rw [hrkeq]
    by_contra hle
    push Not at hle
    have hcard : Nat.card ↥V ≤ 4 := by
      rw [card_eq_two_pow hD'.exp V]
      calc 2 ^ rk ↥V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
        _ = 4 := by norm_num
    let ρ : ↥Mp →* MulAut ↥V := (resHom V).comp (Subgroup.inclusion hMpS)
    have : Group.IsPerfect ↥Mp := hD'.quasi.1
    have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hcard
    have : Group.IsSolvable (MulAut ↥V) :=
      Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b h =>
        MulEquiv.ext fun u => congrArg (fun e : Equiv.Perm _ => e u) h
    have hsub : Subsingleton ρ.range := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
    obtain ⟨l, hl, v, hv, hne⟩ := lred3_exists_ne hD' rfl
    apply hne
    have h1 : ρ ⟨l, hl⟩ = 1 := by
      have : (⟨ρ ⟨l, hl⟩, ⟨l, hl⟩, rfl⟩ : ρ.range) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val this
    exact congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) h1
  have hQ' : autSub A (orbSup T V) ∈ QhatStar (autSub (Mp ⊔ T) (orbSup T V)) := by
    have hMpM : Mp ≤ M := d3Std_Mp_le hD
    have hSyl : IsSylowTwoOf T (Mp ⊔ T) :=
      F7.isSylowTwoOf_mono_right hD'.sylow le_sup_right (sup_le hMpM hD'.sylow.1)
    obtain ⟨r, hr, hr2⟩ := D36.exists_rat_of_qhatOf_le hD.qhat
    have hTX : autSub T (orbSup T V) ≤ autSub (Mp ⊔ T) (orbSup T V) := autSub_mono le_sup_right _
    have hstab : Mp ⊔ T ≤ stabSub (orbSup T V) :=
      sup_le (D36.le_stabSub_orbSup_Mp hTn hVinv) (le_stabSub_orbSup T V)
    have hSyl' : IsSylowTwoOf (autSub T (orbSup T V)) (autSub (Mp ⊔ T) (orbSup T V)) :=
      D36.isSylowTwoOf_autSub hstab le_sup_right hSyl
    obtain ⟨B, hB⟩ := QhatStar_nonempty hr hr2
    obtain ⟨x, hx, hBx⟩ := F7.isSylowTwoOf_exists_conj_le hSyl' (QhatStar_le hB)
      (D36.isPGroup_of_mem_QhatStar hB)
    have hA₀ : conjBy x⁻¹ B ∈ QhatStar (autSub (Mp ⊔ T) (orbSup T V)) :=
      conjBy_mem_QhatStar hB ((autSub (Mp ⊔ T) (orbSup T V)).inv_mem hx)
    have hA₀T : conjBy x⁻¹ B ≤ autSub T (orbSup T V) := by
      intro y hy
      rw [mem_conjBy_iff] at hy
      have := hBx hy
      rw [mem_conjSub] at this
      simpa [mul_assoc] using this
    rw [QhatStar_of_le216 hr hr2 hA₀ hA₀T hTX] at hQ
    exact hQ.1
  have hexp : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
    Subtype.ext (by simpa using hD'.exp y.1)
  have hle : autSub A (orbSup T V) ≤ stabSub (V.subgroupOf (orbSup T V)) :=
    d29_six hexp hTS hrk (D31.pCoreOf_autSub_orbSup_eq_bot hD') _ hQ'
  intro a ha u
  have haS : a ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V (hA ha)
  by_cases hu : u ∈ orbSup T V
  · exact hle (mem_autSub.mpr ⟨⟨a, haS⟩, ha, rfl⟩) ⟨u, hu⟩
  · have h1 : u ∉ V := fun h => hu (hVle h)
    have h2 : a u ∉ orbSup T V := fun h => hu ((haS u).mp h)
    exact ⟨fun h => absurd (hVle h) h2, fun h => absurd h h1⟩

end Three

end CFSG.Quasithin.RonanD35
