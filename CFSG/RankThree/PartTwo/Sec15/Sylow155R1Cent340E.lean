module

public import CFSG.Foundations.Basic
public import CFSG.RankThree.S4Free.StellmacherHosts
import CFSG.Certificates.PerfectCoverBound
import CFSG.GroupTheory.LocalCores.Components
import CFSG.RankThree.PartTwo.KFacts.KS44OutSz

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem res1340_ker_le {X : Type*} [Group X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (hsimple : IsSimpleGroup (X ⧸ N)) {M : Type*} [Monoid M]
    (ρ : X →* M) (hρ : ∃ x, ρ x ≠ 1) : ρ.ker ≤ N := by
  by_contra hK
  have hnorm : (ρ.ker.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map ρ.normal_ker _ (QuotientGroup.mk'_surjective N)
  have hsup : ρ.ker ⊔ N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map (QuotientGroup.mk' N)) with h | h
    · exact absurd (by rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h) hK
    · rw [← QuotientGroup.ker_mk' N, ← Subgroup.comap_map_eq, h, Subgroup.comap_top]
  have hg : Function.Surjective ((QuotientGroup.mk' ρ.ker).comp N.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q
    obtain ⟨k, hk, n, hn, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top x)
    refine ⟨⟨n, hn⟩, ?_⟩
    simp [(QuotientGroup.eq_one_iff k).2 hk]
  have : Group.IsSolvable N := hN
  have : Group.IsSolvable (X ⧸ ρ.ker) := Group.isSolvable_of_surjective hg
  have : Nontrivial (X ⧸ ρ.ker) := by
    obtain ⟨x, hx⟩ := hρ
    refine ⟨⟨QuotientGroup.mk' ρ.ker x, 1, fun h => hx ?_⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_ker] at h
    exact h
  exact Group.IsPerfect.not_isSolvable (X ⧸ ρ.ker) inferInstance

private theorem res1340_eq_one_of_mem {L : Type*} [Group L] {N : Subgroup L}
    (hN3 : ¬ 3 ∣ Nat.card N) {g : L} (hgN : g ∈ N) (hg3 : g ^ 3 = 1) : g = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hg3) with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ Subgroup.orderOf_dvd_natCard N hgN) hN3

theorem res1340_hom_eq_one_of_not_three_dvd {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {N : Subgroup L} [N.Normal] (hN : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) (hsimple : IsSimpleGroup (L ⧸ N)) {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {H : Type*} [Group H] [Finite H] (hH : ¬ 3 ∣ Nat.card H) (f : L →* H) : f = 1 := by
  by_contra hne
  have hker : f.ker ≤ N := by
    refine res1340_ker_le hN hsimple f ?_
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  have hinj : Function.Injective (f.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxker : (x : L) ∈ f.ker := hx
    exact Subtype.ext (res1340_eq_one_of_mem hN3 (hker hxker) (hE.2 x x.2))
  have hdvd : Nat.card E ∣ Nat.card H := Subgroup.card_dvd_of_injective _ hinj
  rw [hE9] at hdvd
  exact hH (dvd_trans (by norm_num) hdvd)

section Layer

variable {S : Type} [Group S]

private def res1340RestrictAut (σ : MulAut S) {J : Subgroup S}
    (h : ∀ x, x ∈ J ↔ σ x ∈ J) : MulAut ↥J where
  toFun j := ⟨σ (j : S), (h j).mp j.2⟩
  invFun j := ⟨σ.symm (j : S), (h _).mpr (by simp)⟩
  left_inv j := Subtype.ext (σ.symm_apply_apply j)
  right_inv j := Subtype.ext (σ.apply_symm_apply j)
  map_mul' a b := Subtype.ext (map_mul σ (a : S) (b : S))

private def res1340RestrictHom {L : Type*} [Group L] (φ : L →* MulAut S) {J : Subgroup S}
    (h : ∀ l : L, ∀ x, x ∈ J ↔ φ l x ∈ J) : L →* MulAut ↥J where
  toFun l := res1340RestrictAut (φ l) (h l)
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    change (φ 1) (x : S) = (x : S)
    rw [map_one]
    rfl
  map_mul' l m := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    change (φ (l * m)) (x : S) = (φ l) ((φ m) (x : S))
    rw [map_mul]
    rfl

private def res1340ComponentPerm (σ : MulAut S) :
    Equiv.Perm {J : Subgroup S // CFSG.IsComponent J} where
  toFun J := ⟨J.1.map σ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv σ J.2⟩
  invFun J := ⟨J.1.map σ.symm.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv σ.symm J.2⟩
  left_inv J := Subtype.ext (CFSG.LocalCores.map_map_symm σ J.1)
  right_inv J := Subtype.ext (CFSG.LocalCores.map_map_symm σ.symm J.1)

private def res1340ComponentPermHom {L : Type*} [Group L] (φ : L →* MulAut S) :
    L →* Equiv.Perm {J : Subgroup S // CFSG.IsComponent J} where
  toFun l := res1340ComponentPerm (φ l)
  map_one' := by
    refine Equiv.ext fun J => Subtype.ext ?_
    change J.1.map (φ 1).toMonoidHom = J.1
    rw [map_one]
    exact Subgroup.map_id J.1
  map_mul' l m := by
    refine Equiv.ext fun J => Subtype.ext ?_
    change J.1.map (φ (l * m)).toMonoidHom = (J.1.map (φ m).toMonoidHom).map (φ l).toMonoidHom
    rw [map_mul, Subgroup.map_map]
    rfl

private theorem res1340_conj_injective {J : Type*} [Group J] (hZ : Subgroup.center J = ⊥) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut J => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

private theorem res1340_map_component_eq {L : Type*} [Group L] [Group.IsPerfect L] [Finite S]
    (hthree : ∀ J₁ J₂ J₃ : Subgroup S, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ →
      CFSG.IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃)
    (φ : L →* MulAut S) {J : Subgroup S} (hJ : CFSG.IsComponent J) (l : L) :
    J.map (φ l).toMonoidHom = J := by
  classical
  have hcard : Nat.card {J : Subgroup S // CFSG.IsComponent J} ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have := Fintype.ofFinite {J : Subgroup S // CFSG.IsComponent J}
    rw [Nat.card_eq_fintype_card] at hlt
    have h2 : 2 < Fintype.card {J : Subgroup S // CFSG.IsComponent J} := by omega
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
    rcases hthree a.1 b.1 c.1 a.2 b.2 c.2 with h | h | h
    · exact hab (Subtype.ext h)
    · exact hac (Subtype.ext h)
    · exact hbc (Subtype.ext h)
  have h := CFSG.Certificates.perfect_perm_trivial hcard (res1340ComponentPermHom φ) l
  exact congrArg (fun p : Equiv.Perm {J : Subgroup S // CFSG.IsComponent J} =>
    (p ⟨J, hJ⟩ : {J : Subgroup S // CFSG.IsComponent J}).1) h

private theorem res1340_fixed_of_isComponent {L : Type*} [Group L]
    [Finite L] [Group.IsPerfect L] {N : Subgroup L} [N.Normal] (hN : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) (hsimple : IsSimpleGroup (L ⧸ N)) {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) [Finite S]
    (hS3 : ¬ 3 ∣ Nat.card S) (hSz : CFSG.RankThree.S4Free.SzSections S)
    (φ : L →* MulAut S) {J : Subgroup S} (hJ : CFSG.IsComponent J)
    (hZJ : Subgroup.center ↥J = ⊥) (hmap : ∀ l : L, J.map (φ l).toMonoidHom = J) (l : L) :
    ∀ x ∈ J, φ l x = x := by
  have hstab : ∀ l : L, ∀ x, x ∈ J ↔ φ l x ∈ J := by
    intro l x
    have h : φ l x ∈ J.map (φ l).toMonoidHom ↔ x ∈ J := by simp
    rw [hmap l] at h
    exact h.symm
  let ρ : L →* MulAut ↥J := res1340RestrictHom φ hstab
  obtain ⟨a, ha, K, _, _, hK, ⟨e⟩⟩ := hSz J (Subgroup.center ↥J) hJ.1.2.1 hJ.1.2.2
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot
  have hmodel : CFSG.Blueprint.SuzukiModel ↥J 2 (2 * a + 1) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨eQ.symm.trans e⟩⟩
  have hcomm := KFacts.commutator_le_inner_of_suzukiModel hmodel
  have hrange : ρ.range ≤ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    refine le_trans ?_ hcomm
    have h1 : (commutator L).map ρ ≤ commutator (MulAut ↥J) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rwa [Group.isPerfect_def.mp ‹Group.IsPerfect L›, ← MonoidHom.range_eq_map] at h1
  have hinj : Function.Injective (MulAut.conj : ↥J →* MulAut ↥J) :=
    res1340_conj_injective hZJ
  have hex : ∀ l : L, ∃ j : ↥J, MulAut.conj j = ρ l := fun l => hrange ⟨l, rfl⟩
  choose γ hγ using hex
  let g : L →* ↥J :=
    { toFun := γ
      map_one' := hinj (by rw [hγ, map_one, map_one])
      map_mul' := fun l m => hinj (by rw [hγ, map_mul, map_mul, hγ, hγ]) }
  have hJ3 : ¬ 3 ∣ Nat.card ↥J := fun h => hS3 (h.trans (Subgroup.card_subgroup_dvd_card J))
  have hg : g = 1 :=
    res1340_hom_eq_one_of_not_three_dvd hN hN3 hsimple hE hE9 (H := ↥J) hJ3 g
  have hρ : ρ l = 1 := by
    rw [← hγ]
    have h1 : γ l = 1 := congrArg (fun f : L →* ↥J => f l) hg
    rw [h1, map_one]
  intro x hx
  exact congrArg (fun f : MulAut ↥J => ((f ⟨x, hx⟩ : ↥J) : S)) hρ

end Layer

theorem res1340_fixes_layer {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {N : Subgroup L} [N.Normal] (hN : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) (hsimple : IsSimpleGroup (L ⧸ N)) {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {S : Type} [Group S] [Finite S] (hS3 : ¬ 3 ∣ Nat.card S)
    (hSz : CFSG.RankThree.S4Free.SzSections S)
    (hZ : ∀ J : Subgroup S, CFSG.IsComponent J → Subgroup.center ↥J = ⊥)
    (hthree : ∀ J₁ J₂ J₃ : Subgroup S, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ →
      CFSG.IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃)
    (φ : L →* MulAut S) : ∀ l : L, ∀ s ∈ CFSG.layer S, φ l s = s := by
  intro l
  have hle : CFSG.layer S ≤ (φ l).toMonoidHom.eqLocus (MonoidHom.id S) := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun J hJ x hx =>
      res1340_fixed_of_isComponent hN hN3 hsimple hE hE9 hS3 hSz φ hJ (hZ J hJ)
        (res1340_map_component_eq hthree φ hJ) l x hx
  exact fun s hs => hle hs

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
