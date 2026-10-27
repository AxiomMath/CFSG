module

public import CFSG.Quasithin.Background.F918Q2
public import CFSG.Quasithin.Background.D36Support
public import CFSG.Quasithin.Background.F918M5
public import CFSG.Quasithin.Background.F918M7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def D36ActsDirect : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      A ≤ stabSub (commSub (orbSup T V) L)

@[expose] def D36ActsGlued : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ¬ IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V) →
    ∀ A : Subgroup (MulAut W), A ≤ T → autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      A ≤ stabSub (commSub (orbSup T V) L)

theorem d36Acts_of_split (h1 : D36ActsDirect) (h2 : D36ActsGlued) : D36Acts := by
  intro W _ _ M Mp T L V t n A hA hQ
  by_cases hd : IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V)
  · exact h1 W M Mp T L V t n hd A hA hQ
  · exact h2 W M Mp T L V t n hd A hA hQ

section Perm

variable {W : Type} [CommGroup W]

private theorem map_inv_of_map_eqM6 {x : MulAut W} {J J' : Subgroup W}
    (h : J.map x.toMonoidHom = J') : J'.map x⁻¹.toMonoidHom = J := by
  rw [← h, ← map_mul_aut', inv_mul_cancel]
  ext u
  simp

private def permSubM6 (U U' : Subgroup W) : Subgroup (MulAut W) where
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
    · exact Or.inl ⟨map_inv_of_map_eqM6 h1, map_inv_of_map_eqM6 h2⟩
    · exact Or.inr ⟨map_inv_of_map_eqM6 h2, map_inv_of_map_eqM6 h1⟩

private theorem mem_permSubM6_iff {U U' : Subgroup W} {x : MulAut W} :
    x ∈ permSubM6 U U' ↔ (U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
      (U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U) := Iff.rfl

private theorem mem_permSubM6 {U U' : Subgroup W} {x : MulAut W}
    (h1 : U.map x.toMonoidHom = U ∨ U.map x.toMonoidHom = U')
    (h2 : U'.map x.toMonoidHom = U ∨ U'.map x.toMonoidHom = U') : x ∈ permSubM6 U U' := by
  have hinj : ∀ J J' : Subgroup W, J.map x.toMonoidHom = J'.map x.toMonoidHom → J = J' :=
    fun J J' h => Subgroup.map_injective (f := x.toMonoidHom) x.injective h
  rw [mem_permSubM6_iff]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have := hinj U U' (h1.trans h2.symm)
    subst this
    exact Or.inl ⟨h1, h1⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · have := hinj U U' (h1.trans h2.symm)
    subst this
    exact Or.inl ⟨h1, h1⟩

private theorem map_subgroupOf_resHomM6 {Y J : Subgroup W} (x : stabSub Y) :
    (J.subgroupOf Y).map (resHom Y x).toMonoidHom =
      (J.map (x : MulAut W).toMonoidHom).subgroupOf Y :=
  CFSG.Quasithin.map_subgroupOf_resHomQ2 x

private theorem map_commSub_of_stabM6 {Y : Subgroup W} {L : Subgroup (MulAut W)} {x : MulAut W}
    (hx : x ∈ stabSub Y) : (commSub Y L).map x.toMonoidHom = commSub Y (conjAutSub x L) := by
  have h := commSub_conjBy x Y L
  rw [mem_stabSub_iff_map_eq.mp hx] at h
  exact h.symm

end Perm

section SylowM6

variable {W : Type} [CommGroup W]

private theorem isSylowTwoOf_autSubM6 {X T : Subgroup (MulAut W)} {U : Subgroup W}
    (hXS : X ≤ stabSub U) (hTX : T ≤ X) (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (autSub T U) (autSub X U) :=
  D36.isSylowTwoOf_autSub hXS hTX hT

private theorem exists_rat_of_qhatOf_leM6 [Finite W] {X : Subgroup (MulAut W)} {c : ℚ}
    (h : qhatOf X ≤ (c : WithTop ℚ)) : ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) ∧ r ≤ c :=
  D36.exists_rat_of_qhatOf_le h

private theorem isPGroup_of_mem_QhatStarM6 [Finite W] {X A : Subgroup (MulAut W)}
    (hA : A ∈ QhatStar X) : IsPGroup 2 A :=
  D36.isPGroup_of_mem_QhatStar hA

end SylowM6

section D36

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

private theorem clauseM6 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    A38Types ↥L ∧ ⁅L, conjAutSub t L⁆ = ⊥ ∧ L ⊓ conjAutSub t L = ⊥ ∧
      ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L :=
  hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq

private theorem L_le_MpM6 (n : D36Norm M Mp T L V t) : L ≤ Mp := by
  rw [n.Mp_eq]; exact le_sup_left

private theorem Mp_le_MM6 (n : D36Norm M Mp T L V t) : Mp ≤ M := by
  have hD := n.std.hyp
  rw [hD.Mp_eq]
  exact conjClosure_le fun s hs z hz =>
    M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hz)) (M.inv_mem (hD.sylow.1 hs))

private theorem T_le_normalizer_MpM6 (n : D36Norm M Mp T L V t) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [n.std.hyp.Mp_eq]; exact le_normalizer_conjClosure L T

private theorem Mp_le_stab_orbSupM6 (n : D36Norm M Mp T L V t) : Mp ≤ stabSub (orbSup T V) :=
  CFSG.Quasithin.Mp_le_stab_orbSupQ2 n

private theorem sup_le_stab_orbSupM6 (n : D36Norm M Mp T L V t) :
    Mp ⊔ T ≤ stabSub (orbSup T V) :=
  sup_le (Mp_le_stab_orbSupM6 n) (le_stabSub_orbSup T V)

private theorem Mp_le_normalizerM6 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hc := (clauseM6 hL38 n).2.1
  rw [n.Mp_eq]
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hh
  exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm

private theorem U_le_orbSupM6 (n : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L ≤ orbSup T V :=
  commSub_le_of_invariant fun _ hx w hw => ((Mp_le_stab_orbSupM6 n (L_le_MpM6 n hx)) w).mpr hw

private theorem L_le_stabUM6 (n : D36Norm M Mp T L V t) :
    L ≤ stabSub (commSub (orbSup T V) L) := fun l hl => by
  have h : conjAutSub l L = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)
  rw [mem_stabSub_iff_map_eq, map_commSub_of_stabM6 (Mp_le_stab_orbSupM6 n (L_le_MpM6 n hl)), h]

private theorem map_t_UM6 (n : D36Norm M Mp T L V t) :
    (commSub (orbSup T V) L).map t.toMonoidHom = commSub (orbSup T V) (conjAutSub t L) :=
  map_commSub_of_stabM6 (le_stabSub_orbSup T V n.tT)

private theorem T_le_permM6 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    T ≤ permSubM6 (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom) := by
  intro s hs
  have key : ∀ x ∈ T, (commSub (orbSup T V) L).map x.toMonoidHom = commSub (orbSup T V) L ∨
      (commSub (orbSup T V) L).map x.toMonoidHom =
        (commSub (orbSup T V) L).map t.toMonoidHom := by
    intro x hx
    rw [map_commSub_of_stabM6 (le_stabSub_orbSup T V hx), map_t_UM6 n]
    rcases (clauseM6 hL38 n).2.2.2 x hx with h | h
    · left; rw [h]
    · right; rw [h]
  refine mem_permSubM6 (key s hs) ?_
  rw [← map_mul_aut']
  exact key (s * t) (T.mul_mem hs n.tT)

private theorem Mp_le_permM6 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ permSubM6 (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom) := by
  have hU : ∀ m ∈ Mp, (commSub (orbSup T V) L).map m.toMonoidHom = commSub (orbSup T V) L := by
    intro m hm
    have h : conjAutSub m L = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Mp_le_normalizerM6 hL38 n hm)
    rw [map_commSub_of_stabM6 (Mp_le_stab_orbSupM6 n hm), h]
  intro m hm
  refine Or.inl ⟨hU m hm, ?_⟩
  have hm' : t⁻¹ * m * t ∈ Mp :=
    (Subgroup.mem_normalizer_iff''.mp (T_le_normalizer_MpM6 n n.tT) m).mp hm
  have e : m * t = t * (t⁻¹ * m * t) := by group
  rw [← map_mul_aut', e, map_mul_aut', hU _ hm']

theorem d36_twoSummands (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    (hdir : IsIntDirect (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom)
      (orbSup T V)) :
    TwoSummands (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) := by
  obtain ⟨hsup, hinf⟩ := hdir
  have hU : commSub (orbSup T V) L ≤ orbSup T V := le_sup_left.trans hsup.le
  have hUt : (commSub (orbSup T V) L).map t.toMonoidHom ≤ orbSup T V := le_sup_right.trans hsup.le
  refine ⟨?_, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have h : (x : W) ∈ commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom :=
      ⟨hx.1, hx.2⟩
    rw [hinf, Subgroup.mem_bot] at h
    exact (Subgroup.mem_bot).mpr (Subtype.ext h)
  · rw [← Subgroup.subgroupOf_sup hU hUt, hsup, Subgroup.subgroupOf_self]
  · intro g hg
    obtain ⟨x, hxX, rfl⟩ := mem_autSub.mp hg
    have hxP := sup_le (Mp_le_permM6 hL38 n) (T_le_permM6 hL38 n) hxX
    rw [map_subgroupOf_resHomM6, map_subgroupOf_resHomM6]
    rcases mem_permSubM6_iff.mp hxP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

private theorem nontrivM6 (n : D36Norm M Mp T L V t) : ∃ l ∈ L, ∃ v ∈ V, l v ≠ v := by
  by_contra hcon
  push Not at hcon
  have hMp : Mp ≤ centSub V := by
    rw [n.Mp_eq]
    exact sup_le (fun l hl v hv => hcon l hl v hv) (fun g hg v hv => n.triv v hv g hg)
  have hfix : V ≤ XMod.fixed ↥Mp V := fun v hv => ⟨hv, fun a => hMp a.2 v hv⟩
  exact absurd hfix (not_le_of_gt n.std.hyp.irr.2.2.2.1)

theorem d36_rank (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    2 < rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V)) := by
  have hUV := U_le_orbSupM6 n
  have hrk : rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V)) =
      rk ↥(commSub (orbSup T V) L) := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv]
  rw [hrk]
  by_contra hle
  push Not at hle
  have hcard : Nat.card ↥(commSub (orbSup T V) L) ≤ 4 := by
    rw [card_eq_two_pow n.std.hyp.exp (commSub (orbSup T V) L)]
    calc 2 ^ rk ↥(commSub (orbSup T V) L) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
      _ = 4 := by norm_num
  have hLS := L_le_stabUM6 n
  let ρ : ↥L →* MulAut ↥(commSub (orbSup T V) L) := (resHom _).comp (Subgroup.inclusion hLS)
  have : Group.IsPerfect ↥L := n.std.hyp.quasi.1
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have : Group.IsSolvable (Equiv.Perm ↥(commSub (orbSup T V) L)) := Equiv.Perm.isSolvable hcard
  have : Group.IsSolvable (MulAut ↥(commSub (orbSup T V) L)) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b h =>
      MulEquiv.ext fun u => congrArg (fun e : Equiv.Perm _ => e u) h
  have hsub : Subsingleton ρ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
  obtain ⟨l, hl, v, hv, hne⟩ := nontrivM6 n
  apply hne
  have h1 : ρ ⟨l, hl⟩ = 1 := by
    have : (⟨ρ ⟨l, hl⟩, ⟨l, hl⟩, rfl⟩ : ρ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 := congrArg (fun φ : MulAut ↥(commSub (orbSup T V) L) =>
    ((φ ⟨v, d36_V_le_U hL38 n hv⟩ : ↥(commSub (orbSup T V) L)) : W)) h1
  exact h2

theorem d36_qhatStar_transfer (n : D36Norm M Mp T L V t) {A : Subgroup (MulAut W)} (hA : A ≤ T)
    (h : autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V))) :
    autSub A (orbSup T V) ∈ QhatStar (autSub (Mp ⊔ T) (orbSup T V)) := by
  have _hAT : autSub A (orbSup T V) ≤ autSub T (orbSup T V) := autSub_mono hA _
  have hD := n.std.hyp
  have hSyl : IsSylowTwoOf T (Mp ⊔ T) :=
    F7.isSylowTwoOf_mono_right hD.sylow le_sup_right (sup_le (Mp_le_MM6 n) hD.sylow.1)
  obtain ⟨r, hr, hr2⟩ := exists_rat_of_qhatOf_leM6 n.std.qhat
  have hTX : autSub T (orbSup T V) ≤ autSub (Mp ⊔ T) (orbSup T V) := autSub_mono le_sup_right _
  have hSyl' : IsSylowTwoOf (autSub T (orbSup T V)) (autSub (Mp ⊔ T) (orbSup T V)) :=
    isSylowTwoOf_autSubM6 (sup_le_stab_orbSupM6 n) le_sup_right hSyl
  obtain ⟨B, hB⟩ := QhatStar_nonempty hr hr2
  obtain ⟨x, hx, hBx⟩ := F7.isSylowTwoOf_exists_conj_le hSyl' (QhatStar_le hB)
    (isPGroup_of_mem_QhatStarM6 hB)
  have hA₀ : conjBy x⁻¹ B ∈ QhatStar (autSub (Mp ⊔ T) (orbSup T V)) :=
    conjBy_mem_QhatStar hB ((autSub (Mp ⊔ T) (orbSup T V)).inv_mem hx)
  have hA₀T : conjBy x⁻¹ B ≤ autSub T (orbSup T V) := by
    intro y hy
    rw [mem_conjBy_iff] at hy
    have := hBx hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  rw [QhatStar_of_le216 hr hr2 hA₀ hA₀T hTX] at h
  exact h.1

theorem d36ActsDirect_of (hL38 : D3L38) : D36ActsDirect := by
  intro W _ _ M Mp T L V t n hdir A hA hQ
  have hexp : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
    Subtype.ext (by simpa using n.std.hyp.exp y.1)
  have hle : autSub A (orbSup T V) ≤ stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)) :=
    d29_six hexp (d36_twoSummands hL38 n hdir) (d36_rank hL38 n) (d36_pCoreOf_eq_bot hL38 n) _
      (d36_qhatStar_transfer n hA hQ)
  have hUV := U_le_orbSupM6 n
  intro a ha u
  have haS : a ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V (hA ha)
  by_cases hu : u ∈ orbSup T V
  · exact hle (mem_autSub.mpr ⟨⟨a, haS⟩, ha, rfl⟩) ⟨u, hu⟩
  · have h1 : u ∉ commSub (orbSup T V) L := fun h => hu (hUV h)
    have h2 : a u ∉ orbSup T V := fun h => hu ((haS u).mp h)
    exact ⟨fun h => absurd (hUV h) h2, fun h => absurd h h1⟩

end D36

end CFSG.Quasithin
