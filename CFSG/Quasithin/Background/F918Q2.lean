module

public import CFSG.Quasithin.Background.F918H1
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.D2Conj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section PermQ2

variable {W : Type} [CommGroup W]

private theorem map_inv_of_map_eqQ2 {x : MulAut W} {J J' : Subgroup W}
    (h : J.map x.toMonoidHom = J') : J'.map x⁻¹.toMonoidHom = J := by
  rw [← h, ← map_mul_aut', inv_mul_cancel]
  ext u
  simp

private def permSubQ2 (U U' : Subgroup W) : Subgroup (MulAut W) where
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
    · exact Or.inl ⟨map_inv_of_map_eqQ2 h1, map_inv_of_map_eqQ2 h2⟩
    · exact Or.inr ⟨map_inv_of_map_eqQ2 h2, map_inv_of_map_eqQ2 h1⟩

private theorem mem_permSubQ2_iff {U U' : Subgroup W} {x : MulAut W} :
    x ∈ permSubQ2 U U' ↔ (U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
      (U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U) := Iff.rfl

private theorem mem_permSubQ2 {U U' : Subgroup W} {x : MulAut W}
    (h1 : U.map x.toMonoidHom = U ∨ U.map x.toMonoidHom = U')
    (h2 : U'.map x.toMonoidHom = U ∨ U'.map x.toMonoidHom = U') : x ∈ permSubQ2 U U' := by
  have hinj : ∀ J J' : Subgroup W, J.map x.toMonoidHom = J'.map x.toMonoidHom → J = J' :=
    fun J J' h => Subgroup.map_injective (f := x.toMonoidHom) x.injective h
  rw [mem_permSubQ2_iff]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have := hinj U U' (h1.trans h2.symm)
    subst this
    exact Or.inl ⟨h1, h1⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · have := hinj U U' (h1.trans h2.symm)
    subst this
    exact Or.inl ⟨h1, h1⟩

theorem le_stabSub_of_forall_memQ2 {X : Subgroup (MulAut W)} {Y : Subgroup W}
    (h : ∀ x ∈ X, ∀ w ∈ Y, x w ∈ Y) : X ≤ stabSub Y := by
  intro x hx u
  refine ⟨fun hu => ?_, fun hu => h x hx u hu⟩
  have := h x⁻¹ (X.inv_mem hx) _ hu
  simpa using this

theorem map_subgroupOf_resHomQ2 {Y J : Subgroup W} (x : stabSub Y) :
    (J.subgroupOf Y).map (resHom Y x).toMonoidHom =
      (J.map (x : MulAut W).toMonoidHom).subgroupOf Y := by
  ext v
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(w : W), hw, rfl⟩
  · rintro ⟨j, hj, hjv⟩
    have hjY : j ∈ Y := (x.2 j).mp (hjv ▸ v.2)
    exact ⟨⟨j, hjY⟩, hj, Subtype.ext hjv⟩

private theorem map_commSub_of_stabQ2 {Y : Subgroup W} {L : Subgroup (MulAut W)} {x : MulAut W}
    (hx : x ∈ stabSub Y) : (commSub Y L).map x.toMonoidHom = commSub Y (conjAutSub x L) := by
  have h := commSub_conjBy x Y L
  rw [mem_stabSub_iff_map_eq.mp hx] at h
  exact h.symm

end PermQ2

section Plumbing

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

private theorem clauseQ2 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ⁅L, conjAutSub t L⁆ = ⊥ ∧ ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L :=
  have h := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  ⟨h.2.1, h.2.2.2⟩

private theorem L_le_MpQ2 (n : D36Norm M Mp T L V t) : L ≤ Mp := by
  rw [n.Mp_eq]; exact le_sup_left

private theorem T_le_normalizer_MpQ2 (n : D36Norm M Mp T L V t) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [n.std.hyp.Mp_eq]; exact le_normalizer_conjClosure L T

theorem Mp_le_stab_orbSupQ2 (n : D36Norm M Mp T L V t) : Mp ≤ stabSub (orbSup T V) := by
  refine le_stabSub_of_forall_memQ2 fun x hx w hw => ?_
  have key : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    show x (s v) ∈ orbSup T V
    have hx' : s⁻¹ * x * s ∈ Mp :=
      (Subgroup.mem_normalizer_iff''.mp (T_le_normalizer_MpQ2 n hs) x).mp hx
    have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
    rw [h1]
    exact map_le_orbSup hs ⟨_, n.std.hyp.irr.2.1 ⟨_, hx'⟩ v hv, rfl⟩
  exact key hw

private theorem Mp_le_normalizerQ2 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hc := (clauseQ2 hL38 n).1
  rw [n.Mp_eq]
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hh
  exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm

private theorem U_le_orbSupQ2 (n : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L ≤ orbSup T V :=
  commSub_le_of_invariant fun _ hx w hw => ((Mp_le_stab_orbSupQ2 n (L_le_MpQ2 n hx)) w).mpr hw

private theorem Ut_le_orbSupQ2 (n : D36Norm M Mp T L V t) :
    (commSub (orbSup T V) L).map t.toMonoidHom ≤ orbSup T V := by
  rintro _ ⟨u, hu, rfl⟩
  exact mem_orbSup_of_mem_map n.tT (U_le_orbSupQ2 n hu)

private theorem T_map_UQ2 (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W} (hx : x ∈ T) :
    (commSub (orbSup T V) L).map x.toMonoidHom = commSub (orbSup T V) L ∨
      (commSub (orbSup T V) L).map x.toMonoidHom =
        (commSub (orbSup T V) L).map t.toMonoidHom := by
  rw [map_commSub_of_stabQ2 (le_stabSub_orbSup T V hx),
    map_commSub_of_stabQ2 (le_stabSub_orbSup T V n.tT)]
  rcases (clauseQ2 hL38 n).2 x hx with h | h
  · left; rw [h]
  · right; rw [h]

private theorem T_le_permQ2 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    T ≤ permSubQ2 (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom) := by
  intro s hs
  refine mem_permSubQ2 (T_map_UQ2 hL38 n hs) ?_
  rw [← map_mul_aut']
  exact T_map_UQ2 hL38 n (T.mul_mem hs n.tT)

private theorem Mp_le_permQ2 (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    Mp ≤ permSubQ2 (commSub (orbSup T V) L) ((commSub (orbSup T V) L).map t.toMonoidHom) := by
  have hU : ∀ m ∈ Mp, (commSub (orbSup T V) L).map m.toMonoidHom = commSub (orbSup T V) L := by
    intro m hm
    have h : conjAutSub m L = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Mp_le_normalizerQ2 hL38 n hm)
    rw [map_commSub_of_stabQ2 (Mp_le_stab_orbSupQ2 n hm), h]
  intro m hm
  refine Or.inl ⟨hU m hm, ?_⟩
  have hm' : t⁻¹ * m * t ∈ Mp :=
    (Subgroup.mem_normalizer_iff''.mp (T_le_normalizer_MpQ2 n n.tT) m).mp hm
  have e : m * t = t * (t⁻¹ * m * t) := by group
  rw [← map_mul_aut', e, map_mul_aut', hU _ hm']

theorem d36_orbSup_eq_sup (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L ⊔ (commSub (orbSup T V) L).map t.toMonoidHom = orbSup T V := by
  refine le_antisymm (sup_le (U_le_orbSupQ2 n) (Ut_le_orbSupQ2 n)) (orbSup_le fun x hx => ?_)
  have hVx : V.map x.toMonoidHom ≤ (commSub (orbSup T V) L).map x.toMonoidHom :=
    Subgroup.map_mono (d36_V_le_U hL38 n)
  rcases T_map_UQ2 hL38 n hx with h | h
  · rw [h] at hVx
    exact hVx.trans le_sup_left
  · rw [h] at hVx
    exact hVx.trans le_sup_right

theorem d36_sup_Y (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊔
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup (U_le_orbSupQ2 n) (Ut_le_orbSupQ2 n), d36_orbSup_eq_sup hL38 n,
    Subgroup.subgroupOf_self]

theorem d36_perm_Y (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∀ g ∈ autSub (Mp ⊔ T) (orbSup T V),
      (g ∈ stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)) ∧
        g ∈ stabSub (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V))) ∨
      (((commSub (orbSup T V) L).subgroupOf (orbSup T V)).map g.toMonoidHom =
          ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) ∧
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)).map g.toMonoidHom =
          (commSub (orbSup T V) L).subgroupOf (orbSup T V)) := by
  intro g hg
  obtain ⟨x, hxX, rfl⟩ := mem_autSub.mp hg
  have hxP := sup_le (Mp_le_permQ2 hL38 n) (T_le_permQ2 hL38 n) hxX
  rw [mem_stabSub_iff_map_eq, mem_stabSub_iff_map_eq, map_subgroupOf_resHomQ2,
    map_subgroupOf_resHomQ2]
  rcases mem_permSubQ2_iff.mp hxP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

theorem d36_swap_Y (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    ∃ s ∈ autSub (Mp ⊔ T) (orbSup T V),
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V)).map s.toMonoidHom =
          ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) ∧
        (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)).map s.toMonoidHom =
          (commSub (orbSup T V) L).subgroupOf (orbSup T V) := by
  have htS : t ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V n.tT
  have htt : ((commSub (orbSup T V) L).map t.toMonoidHom).map t.toMonoidHom =
      commSub (orbSup T V) L := by
    rcases mem_permSubQ2_iff.mp (T_le_permQ2 hL38 n n.tT) with ⟨h1, h2⟩ | ⟨-, h2⟩
    · exact h2.trans h1
    · exact h2
  refine ⟨resHom (orbSup T V) ⟨t, htS⟩,
    mem_autSub.mpr ⟨⟨t, htS⟩, Subgroup.mem_sup_right n.tT, rfl⟩, ?_, ?_⟩
  · exact map_subgroupOf_resHomQ2 ⟨t, htS⟩
  · rw [map_subgroupOf_resHomQ2 ⟨t, htS⟩]
    exact congrArg (fun J => J.subgroupOf (orbSup T V)) htt

end Plumbing

end CFSG.Quasithin
