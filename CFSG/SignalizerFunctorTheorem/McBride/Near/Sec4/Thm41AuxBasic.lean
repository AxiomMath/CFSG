module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAux46

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm41Aux

section Iso

variable {A B : Type*} [Group A] [Group B]

theorem card_quot_eq_of_surjective [Finite A] {f : A →* B} (hf : Function.Surjective f)
    (hk : Group.IsSolvable f.ker) :
    Nat.card (A ⧸ CFSG.solvableRadical A) = Nat.card (B ⧸ CFSG.solvableRadical B) :=
  Nat.card_congr (KAPI.solQuotEquiv hf hk).toEquiv

theorem oStar_eq_top_iff_of_surjective [Finite A] {f : A →* B} (hf : Function.Surjective f)
    (hk : Group.IsSolvable f.ker) : oStar A = ⊤ ↔ oStar B = ⊤ := by
  have : Finite B := Finite.of_surjective f hf
  refine ⟨fun h => KAPI.oStar_eq_top_of_surjective h hf, fun h => ?_⟩
  rw [KAPI.oStar_eq_top_iff] at h ⊢
  exact CFSG.LocalCores.layer_eq_top_of_surjective h (KAPI.solQuotEquiv hf hk).symm.toMonoidHom
    (KAPI.solQuotEquiv hf hk).symm.surjective

theorem isSolvable_ker_equiv (e : A ≃* B) : Group.IsSolvable e.toMonoidHom.ker := by
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [this]
  infer_instance

theorem card_quot_congr [Finite A] (e : A ≃* B) :
    Nat.card (A ⧸ CFSG.solvableRadical A) = Nat.card (B ⧸ CFSG.solvableRadical B) :=
  card_quot_eq_of_surjective e.surjective (isSolvable_ker_equiv e)

theorem oStar_eq_top_iff_congr [Finite A] (e : A ≃* B) : oStar A = ⊤ ↔ oStar B = ⊤ :=
  oStar_eq_top_iff_of_surjective e.surjective (isSolvable_ker_equiv e)

end Iso

section MulSol

variable {G : Type*} [Group G] [Finite G]

theorem mul_sol_eq_props {X Z : Subgroup G} (hZ : (Z : Set G) * (sol X : Set G) = (X : Set G)) :
    Z ≤ X ∧ deg ↥Z = deg ↥X ∧
      Nat.card (↥Z ⧸ CFSG.solvableRadical ↥Z) = Nat.card (↥X ⧸ CFSG.solvableRadical ↥X) ∧
      (oStar ↥X = ⊤ → oStar ↥Z = ⊤) := by
  have hZX : Z ≤ X := fun z hz => by
    have : z ∈ (Z : Set G) * (sol X : Set G) := ⟨z, hz, 1, one_mem _, mul_one z⟩
    rw [hZ] at this
    exact this
  set q : ↥X →* ↥X ⧸ CFSG.solvableRadical ↥X := QuotientGroup.mk' _ with hq
  set f : ↥Z →* ↥X ⧸ CFSG.solvableRadical ↥X := q.comp (Subgroup.inclusion hZX) with hf
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqk : Group.IsSolvable q.ker := by
    rw [hq, QuotientGroup.ker_mk']
    exact isSolvable_solvableRadical
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hqs y
    have hx : (x : G) ∈ (Z : Set G) * (sol X : Set G) := by rw [hZ]; exact x.2
    obtain ⟨z, hz, s, hs, hzs⟩ := hx
    obtain ⟨r, hr, hrs⟩ := Subgroup.mem_map.mp hs
    refine ⟨⟨z, hz⟩, ?_⟩
    simp only [hf, hq, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have : (Subgroup.inclusion hZX ⟨z, hz⟩)⁻¹ * x = r := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hzs, ← hrs]
      simp [Subgroup.inclusion]
    rw [this]
    exact hr
  have hfk : Group.IsSolvable f.ker := by
    have : Group.IsSolvable (CFSG.solvableRadical ↥X) := isSolvable_solvableRadical
    let g : f.ker →* CFSG.solvableRadical ↥X :=
      ((Subgroup.inclusion hZX).comp f.ker.subtype).codRestrict _ (fun x => by
        have hx := MonoidHom.mem_ker.mp x.2
        exact (QuotientGroup.eq_one_iff _).mp hx)
    refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
    intro x y hxy
    have h1 : Subgroup.inclusion hZX x.1 = Subgroup.inclusion hZX y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subgroup.inclusion_injective hZX h1)
  have h1 := KAPI.deg_eq_of_surjective hfs hfk
  have h2 := KAPI.deg_eq_of_surjective hqs hqk
  refine ⟨hZX, h1.trans h2.symm, ?_, fun hX => ?_⟩
  · exact (card_quot_eq_of_surjective hfs hfk).trans (card_quot_eq_of_surjective hqs hqk).symm
  · exact (oStar_eq_top_iff_of_surjective hfs hfk).mpr
      ((oStar_eq_top_iff_of_surjective hqs hqk).mp hX)

end MulSol

section Normalizer

variable {G : Type*} [Group G]

theorem admits_iff {Q X : Subgroup G} :
    Admits Q X ↔ ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X := by
  constructor
  · intro h q hq x hx
    exact (Subgroup.mem_normalizer_iff.mp (h hq) x).mp hx
  · intro h q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h q hq x hx, fun hx => ?_⟩
    have := h q⁻¹ (inv_mem hq) _ hx
    simpa [mul_assoc] using this

theorem admits_sup {Q X Y : Subgroup G} (hX : Admits Q X) (hY : Admits Q Y) :
    Admits Q (X ⊔ Y) := by
  rw [admits_iff]
  intro q hq x hx
  have h : X ⊔ Y ≤ (X ⊔ Y).comap (MulAut.conj q).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_sup_left ((admits_iff.mp hX) q hq x hx)
    · exact Subgroup.mem_sup_right ((admits_iff.mp hY) q hq y hy)
  exact h hx

theorem map_conj_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    X.map ((MulAut.conj g : G ≃* G) : G →* G) = X := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map ((MulAut.conj g : G ≃* G) : G →* G) = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rw [← this]
    exact hy

theorem admits_sSup_of_forall {Q : Subgroup G} {S : Set (Subgroup G)}
    (h : ∀ q ∈ Q, ∀ M ∈ S, M.map ((MulAut.conj q : G ≃* G) : G →* G) ∈ S) :
    Admits Q (sSup S) := by
  rw [admits_iff]
  intro q hq x hx
  have hle : sSup S ≤ (sSup S).comap ((MulAut.conj q : G ≃* G) : G →* G) := by
    refine sSup_le fun M hM y hy => ?_
    exact le_sSup (h q hq M hM) ⟨y, hy, rfl⟩
  exact hle hx

theorem map_conj_mem_of_admits {Z T M : Subgroup G} {q : G}
    (hqZ : q ∈ Subgroup.normalizer (Z : Set G)) (hqT : q ∈ Subgroup.normalizer (T : Set G))
    (hM : M ≤ T ∧ Admits Z M) :
    M.map ((MulAut.conj q : G ≃* G) : G →* G) ≤ T ∧
      Admits Z (M.map ((MulAut.conj q : G ≃* G) : G →* G)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hqT m).mp (hM.1 hm)
  · rw [admits_iff]
    rintro z hz _ ⟨m, hm, rfl⟩
    have hz' : q⁻¹ * z * q ∈ Z := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hqZ) z).mp hz
    refine ⟨(q⁻¹ * z * q) * m * (q⁻¹ * z * q)⁻¹, (admits_iff.mp hM.2) _ hz' m hm, ?_⟩
    simp only [MulAut.conj_apply, MonoidHom.coe_ofClass]
    group

end Normalizer

section SolK

variable {G : Type*} [Group G]

theorem mul_sol_self (X : Subgroup G) : (X : Set G) * (sol X : Set G) = (X : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem ha (sol_le X hb)
  · intro hx
    exact ⟨x, hx, 1, one_mem _, mul_one x⟩

theorem le_normalizer_sol (X : Subgroup G) : X ≤ Subgroup.normalizer (sol X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (sol_le X)).mp (normal_sol_subgroupOf X)

theorem le_sol_of_normal_solvable {S X : Subgroup G} (hSX : S ≤ X)
    (hn : X ≤ Subgroup.normalizer (S : Set G)) (hs : Group.IsSolvable S) : S ≤ sol X := by
  have hnorm : (S.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr hn
  have hsolv : Group.IsSolvable (S.subgroupOf X) :=
    isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  have hle := le_solvableRadical hnorm hsolv
  intro s hs'
  exact ⟨⟨s, hSX hs'⟩, hle (Subgroup.mem_subgroupOf.mpr hs'), rfl⟩

theorem sol_map_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') (X : Subgroup G) :
    sol (X.map (e : G →* G')) = (sol X).map (e : G →* G') := by
  have h1 : (CFSG.solvableRadical ↥X).map (e.subgroupMap X).toMonoidHom =
      CFSG.solvableRadical ↥(X.map (e : G →* G')) := solvableRadical_map_mulEquiv _
  have hcomp : (X.map (e : G →* G')).subtype.comp (e.subgroupMap X).toMonoidHom =
      (e : G →* G').comp X.subtype := by
    ext x
    rfl
  calc sol (X.map (e : G →* G'))
      = ((CFSG.solvableRadical ↥X).map (e.subgroupMap X).toMonoidHom).map
          (X.map (e : G →* G')).subtype := by
        rw [h1]
        rfl
    _ = (CFSG.solvableRadical ↥X).map
          ((X.map (e : G →* G')).subtype.comp (e.subgroupMap X).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (CFSG.solvableRadical ↥X).map ((e : G →* G').comp X.subtype) := by rw [hcomp]
    _ = (sol X).map (e : G →* G') := by
        rw [← Subgroup.map_map]
        rfl

theorem mem_normalizer_sol_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : g ∈ Subgroup.normalizer (sol X : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  have h := sol_map_mulEquiv (MulAut.conj g) X
  rw [map_conj_eq_of_mem_normalizer hg] at h
  exact h.symm

end SolK

section SolKFinite

variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_kOf (X : Subgroup G) : X ≤ Subgroup.normalizer (kOf X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (kOf_le X)).mp (normal_kOf_subgroupOf X)

theorem mem_normalizer_kOf_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : g ∈ Subgroup.normalizer (kOf X : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  have h := KAPI.kOf_map_mulEquiv (MulAut.conj g) X
  rw [map_conj_eq_of_mem_normalizer hg] at h
  exact h.symm

theorem admits_kOf {Q X : Subgroup G} (h : Admits Q X) : Admits Q (kOf X) :=
  fun _ hg => mem_normalizer_kOf_of_mem_normalizer (h hg)

theorem sol_kOf_eq (X : Subgroup G) : sol (kOf X) = sol X := by
  apply le_antisymm
  · refine le_sol_of_normal_solvable ((sol_le _).trans (kOf_le X)) (fun x hx => ?_)
      (isSolvable_sol _)
    exact mem_normalizer_sol_of_mem_normalizer (le_normalizer_kOf X hx)
  · exact le_sol_of_normal_solvable (sol_le_kOf X) ((kOf_le X).trans (le_normalizer_sol X))
      (isSolvable_sol X)

end SolKFinite

section Transfer

variable {G : Type*} [Group G] [Finite G]

theorem deg_kOf (U : Subgroup G) : deg ↥(kOf U) = deg ↥(oStar ↥U) :=
  (KAPI.deg_congr (Subgroup.equivMapOfInjective (oStar ↥U) U.subtype U.subtype_injective)).symm

theorem card_quot_kOf (U : Subgroup G) :
    Nat.card (↥(kOf U) ⧸ CFSG.solvableRadical ↥(kOf U)) =
      Nat.card (↥(oStar ↥U) ⧸ CFSG.solvableRadical ↥(oStar ↥U)) :=
  (card_quot_congr (Subgroup.equivMapOfInjective (oStar ↥U) U.subtype U.subtype_injective)).symm

theorem deg_subgroupOf {U Z : Subgroup G} (hZU : Z ≤ U) : deg ↥(Z.subgroupOf U) = deg ↥Z :=
  KAPI.deg_congr (Subgroup.subgroupOfEquivOfLe hZU)

theorem card_quot_subgroupOf {U Z : Subgroup G} (hZU : Z ≤ U) :
    Nat.card (↥(Z.subgroupOf U) ⧸ CFSG.solvableRadical ↥(Z.subgroupOf U)) =
      Nat.card (↥Z ⧸ CFSG.solvableRadical ↥Z) :=
  card_quot_congr (Subgroup.subgroupOfEquivOfLe hZU)

theorem oStar_subgroupOf_eq_top_iff {U Z : Subgroup G} (hZU : Z ≤ U) :
    oStar ↥(Z.subgroupOf U) = ⊤ ↔ oStar ↥Z = ⊤ :=
  oStar_eq_top_iff_congr (Subgroup.subgroupOfEquivOfLe hZU)

omit [Finite G] in
theorem mul_sol_eq_of_subgroupOf {U Z : Subgroup G} (hZU : Z ≤ U)
    (h : ((Z.subgroupOf U : Subgroup ↥U) : Set ↥U) * (CFSG.solvableRadical ↥U : Set ↥U) =
      (oStar ↥U : Set ↥U)) : (Z : Set G) * (sol U : Set G) = (kOf U : Set G) := by
  ext g
  constructor
  · rintro ⟨z, hz, s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hs
    have hmem : (⟨z, hZU hz⟩ : ↥U) * r ∈ ((Z.subgroupOf U : Subgroup ↥U) : Set ↥U) *
        (CFSG.solvableRadical ↥U : Set ↥U) :=
      ⟨⟨z, hZU hz⟩, hz, r, hr, rfl⟩
    rw [h] at hmem
    exact ⟨_, hmem, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk' : k ∈ ((Z.subgroupOf U : Subgroup ↥U) : Set ↥U) *
        (CFSG.solvableRadical ↥U : Set ↥U) := by rw [h]; exact hk
    obtain ⟨z, hz, r, hr, hzr⟩ := hk'
    exact ⟨z, hz, r, ⟨r, hr, rfl⟩, by rw [← hzr]; rfl⟩

end Transfer

section Pos

theorem permDeg_pos_of_nontrivial {J : Type*} [Group J] [Finite J] [Nontrivial J] :
    0 < permDeg J := by
  by_contra h0
  have h0' : permDeg J = 0 := Nat.eq_zero_of_not_pos h0
  obtain ⟨f, hf⟩ := exists_injective_permDeg (H := J)
  have key : ∀ k : ℕ, k = 0 → ∀ f : J →* Equiv.Perm (Fin k), Function.Injective f →
      Subsingleton J := by
    intro k hk f hf
    subst hk
    exact ⟨fun a b => hf (Subsingleton.elim _ _)⟩
  exact not_subsingleton J (key _ h0' f hf)

theorem pos_deg_oStar {H : Type*} [Group H] [Finite H] (h : ¬ Group.IsSolvable H) :
    0 < deg ↥(oStar H) := by
  set Q := H ⧸ CFSG.solvableRadical H with hQ
  have hQsol : CFSG.solvableRadical Q = ⊥ := solvableRadical_quotient
  have hQnt : Nontrivial Q := by
    by_contra hQ'
    rw [not_nontrivial_iff_subsingleton] at hQ'
    apply h
    have htop : CFSG.solvableRadical H = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : (QuotientGroup.mk x : Q) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp this
    have hs : Group.IsSolvable (CFSG.solvableRadical H) := isSolvable_solvableRadical
    rw [htop] at hs
    exact isSolvable_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
  have hlayer : CFSG.layer Q ≠ ⊥ := by
    intro hl
    have hc := centralizer_layer_eq_bot hQsol
    rw [hl] at hc
    obtain ⟨a, ha⟩ := exists_ne (1 : Q)
    have : a ∈ Subgroup.centralizer (((⊥ : Subgroup Q) : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
      rw [hy]
      simp
    rw [hc] at this
    exact ha (Subgroup.mem_bot.mp this)
  have hcard : 1 < Nat.card ↥(CFSG.layer Q) := by
    by_contra h1
    apply hlayer
    rw [← Subgroup.card_eq_one]
    have := Nat.card_pos (α := ↥(CFSG.layer Q))
    omega
  have hq : Nat.card (↥(oStar H) ⧸ CFSG.solvableRadical ↥(oStar H)) =
      Nat.card ↥(CFSG.layer Q) := BAux.card_quot_oStar_eq
  have hnt : Nontrivial (↥(oStar H) ⧸ CFSG.solvableRadical ↥(oStar H)) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  exact permDeg_pos_of_nontrivial

end Pos

section Exist

variable {H : Type*} [Group H] [Finite H]

theorem bOne_nonempty {T : Set (Subgroup H)} (hT : T.Nonempty) : (bOne T).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image T (fun Y => deg ↥Y) (Set.toFinite T) hT
  exact ⟨a, ha, hmax⟩

theorem bTwo_nonempty {T : Set (Subgroup H)} (hT : (bOne T).Nonempty) : (bTwo T).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image (bOne T)
    (fun Y => Nat.card (↥Y ⧸ CFSG.solvableRadical ↥Y)) (Set.toFinite _) hT
  exact ⟨a, ha, hmax⟩

theorem bStar_nonempty_of_bTwo {T : Set (Subgroup H)} (hT : (bTwo T).Nonempty) :
    (bStar T).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image (bTwo T) (fun Y => Nat.card ↥Y)
    (Set.toFinite _) hT
  exact ⟨a, ha, hmax⟩

theorem bStar_nonempty {T : Set (Subgroup H)} (hT : T.Nonempty) : (bStar T).Nonempty :=
  bStar_nonempty_of_bTwo (bTwo_nonempty (bOne_nonempty hT))

end Exist

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm41Aux
