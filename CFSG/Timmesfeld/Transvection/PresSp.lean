module

public import CFSG.Timmesfeld.Transvection.PresSpRoots
import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Steinberg.Isogeny.Lift

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spElt (a b : Fin n ⊕ Fin n) (c : K) : StatedSp n K :=
  elt (rtIdx a b) c

theorem spElt_add (a b : Fin n ⊕ Fin n) (c d : K) :
    spElt a b (c + d) = spElt a b c * spElt a b d :=
  elt_add _ c d

theorem spElt_zero (a b : Fin n ⊕ Fin n) : spElt a b (0 : K) = 1 :=
  elt_zero _

@[expose] noncomputable def spEltHom (a b : Fin n ⊕ Fin n) : Multiplicative K →* StatedSp n K where
  toFun c := spElt a b (Multiplicative.toAdd c)
  map_one' := spElt_zero a b
  map_mul' _ _ := spElt_add a b _ _

theorem spEltHom_apply (a b : Fin n ⊕ Fin n) (c : Multiplicative K) :
    spEltHom a b c = spElt a b (Multiplicative.toAdd c) := rfl

theorem spElt_comm {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    spElt b a c = spElt a b c := by
  rw [spElt, spElt, rtIdx_comm hab]

namespace Pres

theorem E_eq_of_charTwo [CharP K 2] (r : RootSubgroupIndex n) :
    E K r = if pos2 r = pos1 r then single (pos1 r).1 (pos1 r).2 1
      else single (pos1 r).1 (pos1 r).2 1 + single (pos2 r).1 (pos2 r).2 1 := by
  cases r with
  | positiveLong i => simp [E, pos1, pos2]
  | negativeLong i => simp [E, pos1, pos2]
  | difference i j hij =>
    simp only [E, pos1, pos2, Prod.mk.injEq, reduceCtorEq, false_and, ite_false]
    ext x y
    simp only [Matrix.sub_apply, Matrix.add_apply, CharTwo.sub_eq_add]
  | positiveSum i j hij => simp [E, pos1, pos2, hij.ne']
  | negativeSum i j hij => simp [E, pos1, pos2, hij.ne']

end Pres

theorem mat_spElt [CharP K 2] {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    mat n K (spElt a b c) = 1 + c • (if b = a then single a (Sum.swap a) 1
      else single a (Sum.swap b) 1 + single b (Sum.swap a) 1) := by
  rw [spElt, mat_elt, E_eq_of_charTwo]
  set r := rtIdx a b
  have hw : wt a - wt (Sum.swap b) = stdVec r := by
    rw [stdVec_rtIdx hab, Sp.wt_swap, sub_neg_eq_add, rt]
  have h2 := pos2_eq r
  congr 2
  rcases eq_pos_of_wt_sub r a (Sum.swap b) hw with h1 | h1
  ·
    rw [← h1] at h2
    simp only [Sum.swap_swap] at h2
    rw [← h1, h2]
    by_cases hba : b = a
    · subst hba
      simp
    · simp only [Prod.mk.injEq, hba, false_and, ite_false]
  ·
    have e : pos1 r = (b, Sum.swap a) := by
      rw [h2, Prod.mk.injEq] at h1
      obtain ⟨h1, h1'⟩ := h1
      refine Prod.ext ?_ ?_
      · simpa using congrArg Sum.swap h1'.symm
      · simp only
        rw [h1, Sum.swap_swap]
    rw [← h1, e]
    by_cases hba : b = a
    · subst hba
      simp
    · simp only [Prod.mk.injEq, Ne.symm hba, false_and, ite_false, hba]
      exact add_comm _ _

namespace Pres

theorem exists_root_eq_rt {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) :
    ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = rt a b := by
  obtain ⟨γ, hγ, h⟩ := Sp.exists_root_of_stdVec (rtIdx a b)
  exact ⟨γ, hγ, h.trans (stdVec_rtIdx hab)⟩

end Pres

theorem rootGroup_eq_range_spEltHom {γ : Fin n → ℤ} {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hγ : toStd n γ = rt a b) : (rootDatum n K).rootGroup γ = (spEltHom a b).range := by
  ext g
  change g ∈ rootGroup n K γ ↔ _
  rw [mem_rootGroup_iff ((stdVec_rtIdx hab).trans hγ.symm), MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩

theorem spElt_mem_rootGroup {γ : Fin n → ℤ} {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hγ : toStd n γ = rt a b) (c : K) : spElt a b c ∈ (rootDatum n K).rootGroup γ :=
  elt_mem_rootGroup ((stdVec_rtIdx hab).trans hγ.symm) c

theorem x_eq_spElt {γ : Fin n → ℤ} {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hγ : toStd n γ = rt a b) (c : K) : Sp.x n K γ c = spElt a b c :=
  Sp.x_eq ((stdVec_rtIdx hab).trans hγ.symm) c

theorem toStd_single_last (hn : 1 ≤ n) :
    toStd n (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) =
      rt (Sum.inl ⟨n - 1, by omega⟩) (Sum.inl ⟨n - 1, by omega⟩) := by
  rw [toStd_single_of_not_lt' (by simp only; omega), rt_inl_inl]

theorem rootGroup_single_last (hn : 1 ≤ n) :
    (rootDatum n K).rootGroup (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) =
      (spEltHom (Sum.inl ⟨n - 1, by omega⟩) (Sum.inl ⟨n - 1, by omega⟩)).range :=
  rootGroup_eq_range_spEltHom (swap_ne_self _).symm (toStd_single_last hn)

theorem hom_ext_spElt {H : Type*} [Group H]
    {Ψ Ψ' : StatedSp n K →* H}
    (h : ∀ a b : Fin n ⊕ Fin n, b ≠ Sum.swap a → ∀ c : K, Ψ (spElt a b c) = Ψ' (spElt a b c)) :
    Ψ = Ψ' := by
  have hle : ∀ γ ∈ roots (isFiniteType_cartanC n) ∅,
      rootGroup n K γ ≤ MonoidHom.eqLocus Ψ Ψ' := by
    intro γ hγ
    obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
    have hγe : toStd n γ = rt (sp r).1 (sp r).2 := by rw [rt_sp, hr]
    rw [show rootGroup n K γ = (rootDatum n K).rootGroup γ from rfl,
      rootGroup_eq_range_spEltHom (sp_ne r) hγe]
    rintro _ ⟨c, rfl⟩
    exact h _ _ (sp_ne r) _
  ext g
  have hg : g ∈ ⨆ γ ∈ roots (isFiniteType_cartanC n) ∅, rootGroup n K γ := by
    rw [(isCTGroupDatum n K).iSup_eq_top]
    exact Subgroup.mem_top g
  exact (iSup₂_le hle) hg

namespace Pres

open Classical in
@[expose] noncomputable def xEps (e : Fin n → ℤ) (c : K) : StatedSp n K :=
  if h : ∃ r : RootSubgroupIndex n, stdVec r = e then elt h.choose c else 1

theorem x_eq_xEps (γ : Fin n → ℤ) (c : K) : Sp.x n K γ c = xEps (toStd n γ) c := rfl

theorem xEps_stdVec (r : RootSubgroupIndex n) (c : K) : xEps (stdVec r) c = elt r c := by
  have h : ∃ r' : RootSubgroupIndex n, stdVec r' = stdVec r := ⟨r, rfl⟩
  rw [xEps, dite_eq_left h, stdVec_injective h.choose_spec]

theorem xEps_rt {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    xEps (rt a b) c = spElt a b c := by
  rw [← stdVec_rtIdx hab, xEps_stdVec, spElt]

theorem xEps_zero (e : Fin n → ℤ) : xEps e (0 : K) = 1 := by
  rw [xEps]
  split_ifs
  · exact elt_zero _
  · rfl

theorem prod_spOrder_eq [CharP K 2] {G : Type*} [Group G] (ξ : (Fin n → ℤ) → K → G)
    {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) (s t : K) :
    (((spOrder n K).list α β).map fun p =>
        ξ (toStd n (p.1 • α + p.2 • β)) ((Sp.commC α β p : K) * s ^ p.1 * t ^ p.2)).prod =
      epsWord ξ (toStd n α) (toStd n β) s t := by
  rw [epsWord]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  rw [Sp.toStd_comb, cast_commC hα hβ hαβ (((spOrder n K).mem_iff α hα β hβ hαβ p).1 hp)]

theorem commutatorFormula_iff [CharP K 2] {G : Type*} [Group G] (ξ : (Fin n → ℤ) → K → G) :
    CommutatorFormula (fun γ c => ξ (toStd n γ) c) (spOrder n K) Sp.commC ↔
      ∀ u ∈ Set.range (stdVec (n := n)), ∀ v ∈ Set.range (stdVec (n := n)), u + v ≠ 0 →
        ∀ s t : K, ⁅ξ u s, ξ v t⁆ = epsWord ξ u v s t := by
  constructor
  · rintro h _ ⟨r, rfl⟩ _ ⟨r', rfl⟩ huv s t
    obtain ⟨α, hα, hαr⟩ := Sp.exists_root_of_stdVec r
    obtain ⟨β, hβ, hβr⟩ := Sp.exists_root_of_stdVec r'
    have hαβ : α + β ≠ 0 := fun h0 => huv (by rw [← hαr, ← hβr, ← toStd_add', h0, toStd_zero'])
    have := h α hα β hβ hαβ s t
    dsimp only at this
    rw [prod_spOrder_eq ξ hα hβ hαβ s t, hαr, hβr] at this
    exact this
  · intro h α hα β hβ hαβ s t
    rw [prod_spOrder_eq ξ hα hβ hαβ s t]
    exact h _ ((mem_roots_iff α).1 hα) _ ((mem_roots_iff β).1 hβ)
      (Sp.toStd_add_ne_zero hαβ) s t

theorem xEps_commutator [CharP K 2] {u v : Fin n → ℤ} (hu : u ∈ Set.range (stdVec (n := n)))
    (hv : v ∈ Set.range (stdVec (n := n))) (huv : u + v ≠ 0) (s t : K) :
    ⁅xEps u s, xEps v t⁆ = epsWord xEps u v s t :=
  (commutatorFormula_iff (K := K) xEps).1 (Sp.commutatorFormula (spOrder n K)) u hu v hv huv s t

theorem rt_ne_zero {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) : rt a b ≠ 0 := by
  intro h
  have h1 := rt_dot_rt a b
  have h2 := wt_dot_nonneg hab
  rw [h, zero_dotProduct] at h1
  omega

theorem rt_add_ne_zero {a b c d : Fin n ⊕ Fin n} (hcd : d ≠ Sum.swap c) (hca : c ≠ Sum.swap a)
    (hcb : c ≠ Sum.swap b) : rt a b + rt c d ≠ 0 := by
  intro h
  have e : rt (Sum.swap a) (Sum.swap b) = rt c d := by
    rw [rt_swap_swap]
    exact (neg_eq_of_add_eq_zero_right h)
  rcases (rt_eq_rt_iff hcd).1 e with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hca h1
  · exact hcb h1

end Pres

structure SpRelations (n : ℕ) (K : Type) [Field K] (G : Type*) [Group G] where
  ξ : Fin n ⊕ Fin n → Fin n ⊕ Fin n → K → G
  symm : ∀ a b, b ≠ Sum.swap a → ∀ c, ξ b a c = ξ a b c
  add : ∀ a b, b ≠ Sum.swap a → ∀ s t, ξ a b (s + t) = ξ a b s * ξ a b t
  short : ∀ a b d, idx a ≠ idx b → idx b ≠ idx d → idx a ≠ idx d → ∀ s t,
    ⁅ξ a b s, ξ (Sum.swap b) d t⁆ = ξ a d (s * t)
  shortLong : ∀ a b, idx a ≠ idx b → ∀ s t,
    ⁅ξ a b s, ξ (Sum.swap b) (Sum.swap b) t⁆ = ξ a (Sum.swap b) (s * t) * ξ a a (s ^ 2 * t)
  commLong : ∀ a b, idx a ≠ idx b → ∀ s t, ⁅ξ a b s, ξ a (Sum.swap b) t⁆ = 1
  comm : ∀ a b c d, b ≠ Sum.swap a → d ≠ Sum.swap c → c ≠ Sum.swap a → c ≠ Sum.swap b →
    d ≠ Sum.swap a → d ≠ Sum.swap b → ∀ s t, ⁅ξ a b s, ξ c d t⁆ = 1

@[expose] def SpRelations.ofSplit {G : Type*} [Group G] (ξ : Fin n ⊕ Fin n → Fin n ⊕ Fin n → K → G)
    (symm : ∀ a b, b ≠ Sum.swap a → ∀ c, ξ b a c = ξ a b c)
    (add : ∀ a b, b ≠ Sum.swap a → ∀ s t, ξ a b (s + t) = ξ a b s * ξ a b t)
    (short : ∀ a b d, idx a ≠ idx b → idx b ≠ idx d → idx a ≠ idx d → ∀ s t,
      ⁅ξ a b s, ξ (Sum.swap b) d t⁆ = ξ a d (s * t))
    (shortLong : ∀ a b, idx a ≠ idx b → ∀ s t,
      ⁅ξ a b s, ξ (Sum.swap b) (Sum.swap b) t⁆ = ξ a (Sum.swap b) (s * t) * ξ a a (s ^ 2 * t))
    (commLong : ∀ a b, idx a ≠ idx b → ∀ s t, ⁅ξ a b s, ξ a (Sum.swap b) t⁆ = 1)
    (commLL : ∀ a c, c ≠ Sum.swap a → ∀ s t, ⁅ξ a a s, ξ c c t⁆ = 1)
    (commLS : ∀ a c d, idx c ≠ idx d → c ≠ Sum.swap a → d ≠ Sum.swap a → ∀ s t,
      ⁅ξ a a s, ξ c d t⁆ = 1)
    (commSS : ∀ a b c d, idx a ≠ idx b → idx c ≠ idx d → c ≠ Sum.swap a → c ≠ Sum.swap b →
      d ≠ Sum.swap a → d ≠ Sum.swap b → ∀ s t, ⁅ξ a b s, ξ c d t⁆ = 1) :
    SpRelations n K G where
  ξ := ξ
  symm := symm
  add := add
  short := short
  shortLong := shortLong
  commLong := commLong
  comm a b c d hab hcd hca hcb hda hdb s t := by
    by_cases hba : b = a
    · subst hba
      by_cases hdc : d = c
      · subst hdc
        exact commLL b d hca s t
      · exact commLS b c d (idx_ne_of_ne hdc hcd) hca hda s t
    · have hidx : idx a ≠ idx b := idx_ne_of_ne hba hab
      by_cases hdc : d = c
      · subst hdc
        have h1 : a ≠ Sum.swap d := fun e => hca (by rw [e, Sum.swap_swap])
        have h2 : b ≠ Sum.swap d := fun e => hcb (by rw [e, Sum.swap_swap])
        rw [← commutatorElement_inv, commLS d a b hidx h1 h2 t s, inv_one]
      · exact commSS a b c d hidx (idx_ne_of_ne hdc hcd) hca hcb hda hdb s t

namespace SpRelations

variable {G : Type*} [Group G] (R : SpRelations n K G)

theorem map_zero {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) : R.ξ a b 0 = 1 := by
  have h := R.add a b hab 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem inv_eq [CharP K 2] {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    (R.ξ a b c)⁻¹ = R.ξ a b c := by
  have h := R.add a b hab c c
  rw [CharTwo.add_self_eq_zero, R.map_zero hab] at h
  exact (inv_eq_of_mul_eq_one_left h.symm)

theorem longShort [CharP K 2] {a d : Fin n ⊕ Fin n} (had : idx a ≠ idx d) (s t : K) :
    ⁅R.ξ a a s, R.ξ (Sum.swap a) d t⁆ = R.ξ a d (s * t) * R.ξ d d (s * t ^ 2) := by
  have hda : idx d ≠ idx (Sum.swap a) := by rw [idx_swap]; exact had.symm
  have h := R.shortLong d (Sum.swap a) hda t s
  rw [Sum.swap_swap] at h
  have v1 : d ≠ Sum.swap (Sum.swap a) := by rw [Sum.swap_swap]; exact ne_of_idx_ne had
  have v2 : a ≠ Sum.swap d := ne_swap_of_idx_ne had.symm
  have v3 : d ≠ Sum.swap a := ne_swap_of_idx_ne had
  have v4 : d ≠ Sum.swap d := (swap_ne_self d).symm
  have hcomm : ⁅R.ξ d a (t * s), R.ξ d d (t ^ 2 * s)⁆ = 1 :=
    R.comm d a d d v2 v4 v4 v3 v4 v3 _ _
  rw [commutatorElement_eq_one_iff_mul_comm] at hcomm
  calc ⁅R.ξ a a s, R.ξ (Sum.swap a) d t⁆ = ⁅R.ξ (Sum.swap a) d t, R.ξ a a s⁆⁻¹ := by
        rw [commutatorElement_inv]
    _ = (R.ξ d a (t * s) * R.ξ d d (t ^ 2 * s))⁻¹ := by rw [← R.symm _ _ v1, h]
    _ = R.ξ d d (t ^ 2 * s) * R.ξ d a (t * s) := by
        rw [_root_.mul_inv_rev, R.inv_eq v4, R.inv_eq v2]
    _ = R.ξ a d (s * t) * R.ξ d d (s * t ^ 2) := by
        rw [← hcomm, R.symm d a v2, mul_comm t s, mul_comm (t ^ 2) s]

open Classical in
@[expose] noncomputable def toEps (e : Fin n → ℤ) (c : K) : G :=
  if h : ∃ r : RootSubgroupIndex n, stdVec r = e then R.ξ (sp h.choose).1 (sp h.choose).2 c
  else 1

theorem toEps_stdVec (r : RootSubgroupIndex n) (c : K) :
    R.toEps (stdVec r) c = R.ξ (sp r).1 (sp r).2 c := by
  have h : ∃ r' : RootSubgroupIndex n, stdVec r' = stdVec r := ⟨r, rfl⟩
  rw [toEps, dite_eq_left h, stdVec_injective h.choose_spec]

theorem toEps_rt {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    R.toEps (rt a b) c = R.ξ a b c := by
  rw [← stdVec_rtIdx hab, toEps_stdVec]
  rcases eq_sp_of_rt_eq (stdVec_rtIdx hab).symm with h | h
  · rw [← h]
  · rw [← h, R.symm a b hab]

theorem toEps_zero (e : Fin n → ℤ) : R.toEps e (0 : K) = 1 := by
  rw [toEps]
  split_ifs with h
  · exact R.map_zero (sp_ne _)
  · rfl

theorem toEps_add {e : Fin n → ℤ} (he : e ∈ Set.range (stdVec (n := n))) (s t : K) :
    R.toEps e (s + t) = R.toEps e s * R.toEps e t := by
  obtain ⟨r, rfl⟩ := he
  rw [toEps_stdVec, toEps_stdVec, toEps_stdVec, R.add _ _ (sp_ne r)]

private theorem comm_swap_eq [CharP K 2] {a b d : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hda : d ≠ a) (hne : rt a b + rt (Sum.swap a) d ≠ 0) (s t : K) :
    ⁅R.ξ a b s, R.ξ (Sum.swap a) d t⁆ = epsWord R.toEps (rt a b) (rt (Sum.swap a) d) s t := by
  have hv : d ≠ Sum.swap (Sum.swap a) := by rw [Sum.swap_swap]; exact hda
  by_cases h1 : d = Sum.swap b
  · subst h1
    exact absurd (by rw [rt_swap_swap, add_neg_cancel]) hne
  by_cases h2 : d = Sum.swap a
  · subst h2
    by_cases hba : b = a
    · subst hba
      exact absurd (by rw [rt_swap_swap, add_neg_cancel]) hne
    have hidx : idx b ≠ idx a := (idx_ne_of_ne hba hab).symm
    rw [← R.symm a b hab, R.shortLong b a hidx, rt_comm a b, epsWord_shortLong _ hidx,
      R.toEps_rt (ne_swap_of_idx_ne (by rwa [idx_swap])),
      R.toEps_rt (swap_ne_self b).symm]
  by_cases h3 : d = b
  · subst h3
    have hba : d ≠ a := hda
    have hidx : idx d ≠ idx a := (idx_ne_of_ne hba hab).symm
    rw [← R.symm a d hab, ← R.symm (Sum.swap a) d hv, R.commLong d a hidx, rt_comm a d,
      rt_comm (Sum.swap a) d, epsWord_commLong _ R.toEps_zero hidx]
  have had : idx a ≠ idx d := idx_ne_of_ne hda h2
  by_cases hba : b = a
  · subst hba
    rw [R.longShort had, epsWord_longShort _ had, R.toEps_rt (ne_swap_of_idx_ne had),
      R.toEps_rt (swap_ne_self d).symm]
  · have hidx : idx b ≠ idx a := (idx_ne_of_ne hba hab).symm
    have hbd : idx b ≠ idx d := idx_ne_of_ne h3 h1
    rw [← R.symm a b hab, R.short b a d hidx had hbd, rt_comm a b, epsWord_short _ hidx had hbd,
      R.toEps_rt (ne_swap_of_idx_ne hbd)]

theorem comm_eq_epsWord [CharP K 2] {a b c d : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hcd : d ≠ Sum.swap c) (hne : rt a b + rt c d ≠ 0) (s t : K) :
    ⁅R.ξ a b s, R.ξ c d t⁆ = epsWord R.toEps (rt a b) (rt c d) s t := by
  have hba : a ≠ Sum.swap b := ofPos_ne hab
  have hdc : c ≠ Sum.swap d := ofPos_ne hcd
  by_cases h1 : c = Sum.swap a
  · subst h1
    exact R.comm_swap_eq hab (by simpa using hcd) hne s t
  by_cases h2 : c = Sum.swap b
  · subst h2
    rw [← R.symm a b hab, rt_comm a b]
    exact R.comm_swap_eq hba (by simpa using hcd) (by rwa [rt_comm b a]) s t
  by_cases h3 : d = Sum.swap a
  · subst h3
    rw [← R.symm c (Sum.swap a) hcd, rt_comm c (Sum.swap a)]
    exact R.comm_swap_eq hab (fun e => hcd (by rw [e])) (by rwa [rt_comm (Sum.swap a) c]) s t
  by_cases h4 : d = Sum.swap b
  · subst h4
    rw [← R.symm a b hab, ← R.symm c (Sum.swap b) hcd, rt_comm a b, rt_comm c (Sum.swap b)]
    exact R.comm_swap_eq hba (fun e => hcd (by rw [e]))
      (by rwa [rt_comm b a, rt_comm (Sum.swap b) c]) s t
  rw [R.comm a b c d hab hcd h1 h2 h3 h4, epsWord_comm _ R.toEps_zero hab hcd h1 h2 h3 h4]

theorem commutatorFormula [CharP K 2] :
    CommutatorFormula (fun γ c => R.toEps (toStd n γ) c) (spOrder n K) Sp.commC := by
  rw [commutatorFormula_iff]
  rintro _ ⟨r, rfl⟩ _ ⟨r', rfl⟩ huv s t
  rw [← rt_sp r, ← rt_sp r'] at huv ⊢
  rw [R.toEps_rt (sp_ne r), R.toEps_rt (sp_ne r')]
  exact R.comm_eq_epsWord (sp_ne r) (sp_ne r') huv s t

@[expose] def rootHom {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) : Multiplicative K →* G where
  toFun c := R.ξ a b (Multiplicative.toAdd c)
  map_one' := R.map_zero hab
  map_mul' _ _ := R.add a b hab _ _

theorem rootHom_apply {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : Multiplicative K) :
    R.rootHom hab c = R.ξ a b (Multiplicative.toAdd c) := rfl

@[expose] noncomputable def toHom [Finite K] [CharP K 2] (hn : 2 ≤ n) : StatedSp n K →* G :=
  liftOfPresentationB (Sp.presentationB hn) (spOrder n K) (Sp.commutatorFormula _)
    (fun γ hγ c d => R.toEps_add ((mem_roots_iff γ).1 hγ) c d) R.commutatorFormula

variable [Finite K] [CharP K 2] (hn : 2 ≤ n)

theorem toHom_x {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) (c : K) :
    R.toHom hn (Sp.x n K γ c) = R.toEps (toStd n γ) c :=
  liftOfPresentationB_apply _ _ _ _ _ hγ c

theorem toHom_spElt {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a) (c : K) :
    R.toHom hn (spElt a b c) = R.ξ a b c := by
  obtain ⟨γ, hγ, hγe⟩ := exists_root_eq_rt hab
  rw [← x_eq_spElt hab hγe, R.toHom_x hn hγ, hγe, R.toEps_rt hab]

theorem toHom_x_eq {γ : Fin n → ℤ} {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hγ : toStd n γ = rt a b) (c : K) : R.toHom hn (Sp.x n K γ c) = R.ξ a b c := by
  rw [x_eq_spElt hab hγ, R.toHom_spElt hn hab]

theorem map_rootGroup {γ : Fin n → ℤ} {a b : Fin n ⊕ Fin n} (hab : b ≠ Sum.swap a)
    (hγ : toStd n γ = rt a b) :
    ((rootDatum n K).rootGroup γ).map (R.toHom hn) = (R.rootHom hab).range := by
  rw [rootGroup_eq_range_spEltHom hab hγ, MonoidHom.map_range]
  congr 1
  ext c
  exact R.toHom_spElt hn hab _

theorem map_rootGroup_single_last :
    ((rootDatum n K).rootGroup (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)).map (R.toHom hn) =
      (R.rootHom (a := Sum.inl ⟨n - 1, by omega⟩) (b := Sum.inl ⟨n - 1, by omega⟩)
        (swap_ne_self _).symm).range :=
  R.map_rootGroup hn _ (toStd_single_last (by omega))

include hn in
theorem existsUnique_hom :
    ∃! Ψ : StatedSp n K →* G, ∀ a b, b ≠ Sum.swap a → ∀ c, Ψ (spElt a b c) = R.ξ a b c :=
  ⟨R.toHom hn, fun _ _ hab c => R.toHom_spElt hn hab c, fun Ψ' hΨ' =>
    hom_ext_spElt fun a b hab c => by rw [hΨ' a b hab c, R.toHom_spElt hn hab]⟩

@[expose] def Generates : Prop :=
  Subgroup.closure {g | ∃ a b : Fin n ⊕ Fin n, b ≠ Sum.swap a ∧ ∃ c : K, R.ξ a b c = g} = ⊤

theorem toHom_surjective (hgen : R.Generates) : Function.Surjective (R.toHom hn) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, c, rfl⟩
  exact ⟨spElt a b c, R.toHom_spElt hn hab c⟩

end SpRelations

theorem center_statedSp_eq_bot [CharP K 2] (hn : 1 ≤ n) : Subgroup.center (StatedSp n K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [center_eq n K, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨u, hu⟩ := hg
  have hmem : (g : GL (Fin n ⊕ Fin n) K) ∈ TauCeti.GLSymplectic (Fin n) K :=
    CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n) (K := K) ▸ g.2
  rw [TauCeti.GLSymplectic.mem_iff, ← hu] at hmem
  have h := congrFun (congrFun hmem (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.J] at h
  have hu1 : (u : K) = 1 := by
    have e : ((u : K) + 1) * ((u : K) + 1) = (u : K) * u + 1 + ((u : K) + u) := by ring
    rw [h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero] at e
    have h0 := mul_self_eq_zero.1 e
    rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
  have hu' : u = 1 := Units.ext hu1
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hu, hu', map_one]; rfl)

namespace SpRelations

variable {G : Type*} [Group G] (R : SpRelations n K G) [Finite K] [CharP K 2] (hn : 2 ≤ n)

theorem toHom_bijective (hq : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 3 ≤ n)) [Nontrivial G]
    (hgen : R.Generates) : Function.Bijective (R.toHom hn) := by
  have hsurj := R.toHom_surjective hn hgen
  have hK : IsQuasisimple (StatedSp n K) := Symplectic.isQuasisimple n K (by omega) (by
    rcases hq with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h))
  have hnt : ∃ k, R.toHom hn k ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨k, rfl⟩ := hsurj g
    exact ⟨k, hg⟩
  have hker := CurtisTits.ker_le_center_of_isQuasisimple hK hnt
  rw [center_statedSp_eq_bot (by omega)] at hker
  exact ⟨(MonoidHom.ker_eq_bot_iff _).1 (le_bot_iff.1 hker), hsurj⟩

include hn in
theorem exists_mulEquiv (hq : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 3 ≤ n)) [Nontrivial G]
    (hgen : R.Generates) :
    ∃ Ψ : StatedSp n K ≃* G, ∀ a b, b ≠ Sum.swap a → ∀ c, Ψ (spElt a b c) = R.ξ a b c :=
  ⟨MulEquiv.ofBijective _ (R.toHom_bijective hn hq hgen), fun _ _ hab c =>
    R.toHom_spElt hn hab c⟩

end SpRelations

@[expose] noncomputable def spRelationsModel [CharP K 2] : SpRelations n K (StatedSp n K) where
  ξ := spElt
  symm _ _ hab c := spElt_comm hab c
  add a b _ s t := spElt_add a b s t
  short a b d hab hbd had s t := by
    have v1 : b ≠ Sum.swap a := ne_swap_of_idx_ne hab
    have v2 : d ≠ Sum.swap (Sum.swap b) := by rw [Sum.swap_swap]; exact ne_of_idx_ne hbd
    have v3 : d ≠ Sum.swap a := ne_swap_of_idx_ne had
    have e : rt a b + rt (Sum.swap b) d = rt a d := by simp only [rt, Sp.wt_swap]; abel
    rw [← xEps_rt v1, ← xEps_rt v2, ← xEps_rt v3,
      xEps_commutator (rt_mem v1) (rt_mem v2) (by rw [e]; exact rt_ne_zero v3),
      epsWord_short _ hab hbd had]
  shortLong a b hab s t := by
    have v1 : b ≠ Sum.swap a := ne_swap_of_idx_ne hab
    have v2 : Sum.swap b ≠ Sum.swap (Sum.swap b) := (swap_ne_self _).symm
    have v3 : Sum.swap b ≠ Sum.swap a := fun h =>
      ne_of_idx_ne hab (by simpa using congrArg Sum.swap h)
    have v4 : a ≠ Sum.swap a := (swap_ne_self a).symm
    have e : rt a b + rt (Sum.swap b) (Sum.swap b) = rt a (Sum.swap b) := by
      simp only [rt, Sp.wt_swap]; abel
    rw [← xEps_rt v1, ← xEps_rt v2, ← xEps_rt v3, ← xEps_rt v4,
      xEps_commutator (rt_mem v1) (rt_mem v2) (by rw [e]; exact rt_ne_zero v3),
      epsWord_shortLong _ hab]
  commLong a b hab s t := by
    have v1 : b ≠ Sum.swap a := ne_swap_of_idx_ne hab
    have v2 : Sum.swap b ≠ Sum.swap a := fun h =>
      ne_of_idx_ne hab (by simpa using congrArg Sum.swap h)
    have v4 : a ≠ Sum.swap a := (swap_ne_self a).symm
    have e : rt a b + rt a (Sum.swap b) = rt a a := by simp only [rt, Sp.wt_swap]; abel
    rw [← xEps_rt v1, ← xEps_rt v2,
      xEps_commutator (rt_mem v1) (rt_mem v2) (by rw [e]; exact rt_ne_zero v4),
      epsWord_commLong _ xEps_zero hab]
  comm a b c d hab hcd hca hcb hda hdb s t := by
    rw [← xEps_rt hab, ← xEps_rt hcd,
      xEps_commutator (rt_mem hab) (rt_mem hcd) (rt_add_ne_zero hcd hca hcb),
      epsWord_comm _ xEps_zero hab hcd hca hcb hda hdb]

theorem spRelationsModel_ξ [CharP K 2] : (spRelationsModel (n := n) (K := K)).ξ = spElt := rfl

end CFSG.Timmesfeld.Transvection
