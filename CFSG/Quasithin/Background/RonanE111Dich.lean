module

public import CFSG.Quasithin.Background.RonanE111Semi

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b
open scoped commutatorElement

section Solvable

variable {Q : Type} [Group Q]

theorem top_mem_sFamily {S X Y : Subgroup Q} (hXS : X ⊔ S = ⊤)
    (hK : ∀ K : Subgroup Q, S ≤ K → K ⊔ Y = ⊤ → K = ⊤) :
    (⊤ : Subgroup Q) ∈ E1.sFamily S X Y := by
  show (⊤ : Subgroup Q) ≤ X ⊔ S ∧ S ≤ ⊤ ∧ X ⊔ S = ⊤ ⊔ Y ∧
    ∀ K' : Subgroup Q, K' ≤ X ⊔ S → S ≤ K' → X ⊔ S = K' ⊔ Y → K' ≤ ⊤ → K' = ⊤
  exact ⟨le_of_eq hXS.symm, le_top, hXS.trans (top_sup_eq Y).symm,
    fun K' _ hSK' hEq _ => hK K' hSK' (hEq.symm.trans hXS)⟩

theorem le_preO2_top (Y : Subgroup Q) [Y.Normal] : Y ≤ E1.preO2 (⊤ : Subgroup Q) Y := by
  intro y hy
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top y, ?_⟩
  rw [Subgroup.mem_comap]
  have h1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [h1]
  exact Subgroup.one_mem _

theorem isSolvable_of_Y [Finite Q] {S X Y : Subgroup Q} [Y.Normal] (hS : IsSylowIn 2 S ⊤)
    (hXS : X ⊔ S = ⊤) (hK : ∀ K : Subgroup Q, S ≤ K → K ⊔ Y = ⊤ → K = ⊤) :
    Group.IsSolvable ↥Y := by
  have h2 : E1.IsTwoClosed (E1.preO2 (⊤ : Subgroup Q) Y) :=
    E1.ten_two hS le_top (top_mem_sFamily hXS hK)
  haveI : Group.IsSolvable ↥(E1.preO2 (⊤ : Subgroup Q) Y) := E1.isSolvable_of_isTwoClosed h2
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (le_preO2_top Y))
    (Subgroup.inclusion_injective _)

theorem isSolvable_of_map_mk {X Y : Subgroup Q} [X.Normal] [Y.Normal] (hYX : Y ≤ X)
    (hY : Group.IsSolvable ↥Y) (hN : Group.IsSolvable ↥(X.map (QuotientGroup.mk' Y))) :
    Group.IsSolvable ↥X := by
  let f : ↥X →* Q ⧸ Y := (QuotientGroup.mk' Y).comp X.subtype
  have hker : f.ker = Y.subgroupOf X := by
    ext x
    simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = X.map (QuotientGroup.mk' Y) := by
    simp [f, MonoidHom.range_comp]
  let e : (↥X ⧸ Y.subgroupOf X) ≃* ↥(X.map (QuotientGroup.mk' Y)) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)
  haveI : Group.IsSolvable ↥(Y.subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYX).injective
  haveI : Group.IsSolvable (↥X ⧸ Y.subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_subgroup_quotient (Y.subgroupOf X)

end Solvable

section MinimalQuot

variable {Q : Type} [Group Q]

theorem comap_map_mk {X Y : Subgroup Q} [Y.Normal] (hYX : Y ≤ X) :
    (X.map (QuotientGroup.mk' Y)).comap (QuotientGroup.mk' Y) = X := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hYX]

theorem map_minimal {X Y : Subgroup Q} [Y.Normal] (hYX : Y ≤ X)
    (hmin : ∀ N : Subgroup Q, N.Normal → Y ≤ N → N ≤ X → N = Y ∨ N = X) :
    ∀ M : Subgroup (Q ⧸ Y), M.Normal → M ≤ X.map (QuotientGroup.mk' Y) →
      M = ⊥ ∨ M = X.map (QuotientGroup.mk' Y) := by
  intro M hM hMX
  have hπs : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  have hYM : Y ≤ M.comap (QuotientGroup.mk' Y) := by
    intro y hy
    have h1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [Subgroup.mem_comap, h1]
    exact M.one_mem
  have hMX' : M.comap (QuotientGroup.mk' Y) ≤ X := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hMX (Subgroup.mem_comap.mp hq)
    have h1 : x⁻¹ * q ∈ Y := QuotientGroup.eq.mp hxq
    have h2 : x * (x⁻¹ * q) ∈ X := X.mul_mem hx (hYX h1)
    simpa using h2
  have hMeq : M = (M.comap (QuotientGroup.mk' Y)).map (QuotientGroup.mk' Y) :=
    (Subgroup.map_comap_eq_self_of_surjective hπs M).symm
  rcases hmin _ inferInstance hYM hMX' with h | h
  · left
    rw [hMeq, h, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (QuotientGroup.eq_one_iff y).mpr hy
  · right
    rw [hMeq, h]

theorem map_mk_ne_bot {X Y : Subgroup Q} [Y.Normal] (hYX : Y ≤ X) (hne : Y ≠ X) :
    X.map (QuotientGroup.mk' Y) ≠ ⊥ := by
  intro h
  apply hne
  refine le_antisymm hYX fun x hx => ?_
  have h1 : QuotientGroup.mk' Y x ∈ X.map (QuotientGroup.mk' Y) := Subgroup.mem_map_of_mem _ hx
  rw [h, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).mp h1

end MinimalQuot

section Commute

variable {G : Type} [Group G]

theorem conj_mem_of_subgroupOf {N S : Subgroup G} (hSN : S ≤ N)
    (hSn : (S.subgroupOf N).Normal) : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
  intro n hn s hs
  have h := hSn.conj_mem ⟨s, hSN hs⟩ (Subgroup.mem_subgroupOf.mpr hs) ⟨n, hn⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem commute_of_normal_simple {N K K' : Subgroup G} (hK : K ≤ N) (hK' : K' ≤ N)
    (hKn : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K) (hK'n : ∀ n ∈ N, ∀ k ∈ K', n * k * n⁻¹ ∈ K')
    (hsK : IsSimpleGroup ↥K) (hsK' : IsSimpleGroup ↥K') (hne : K ≠ K') {x y : G}
    (hx : x ∈ K) (hy : y ∈ K') : x * y = y * x := by
  haveI := hsK
  haveI := hsK'
  have hI : ((K ⊓ K').subgroupOf K).Normal :=
    normal_subgroupOf_of_conj inf_le_left fun s hs n hn =>
      Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hs (Subgroup.mem_inf.mp hn).1) (K.inv_mem hs),
        hK'n _ (hK hs) _ (Subgroup.mem_inf.mp hn).2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ K').subgroupOf K) with h | h
  · have hdisj : K ⊓ K' = ⊥ := by
      have h3 := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      rwa [inf_eq_left.mpr inf_le_left] at h3
    have hc1 : x * y * x⁻¹ * y⁻¹ ∈ K := by
      have h4 := K.mul_mem hx (hKn y (hK' hy) x⁻¹ (K.inv_mem hx))
      simpa [mul_assoc] using h4
    have hc2 : x * y * x⁻¹ * y⁻¹ ∈ K' :=
      K'.mul_mem (hK'n x (hK hx) y hy) (K'.inv_mem hy)
    have hc : x * y * x⁻¹ * y⁻¹ ∈ K ⊓ K' := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
    rw [hdisj, Subgroup.mem_bot] at hc
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)
  · exfalso
    have hle : K ≤ K' := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right
    haveI : (K.subgroupOf K').Normal :=
      normal_subgroupOf_of_conj hle fun s hs n hn => hKn s (hK' hs) n hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf K') with h2 | h2
    · have hK0 : K = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp (Subgroup.subgroupOf_eq_bot.mp h2) hz
          (hle hz))
      exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hK0
    · exact hne (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h2))

theorem conjSub_le_of_normal {N S : Subgroup G} (hN : N.Normal) (hS : S ≤ N) (g : G) :
    A1b.conjSub g S ≤ N := by
  intro x hx
  rw [A1b.mem_conjSub_iff] at hx
  have h := hN.conj_mem _ (hS hx) g
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h

theorem conjSub_eq_of_normalized {N K : Subgroup G} (hK : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    {n : G} (hn : n ∈ N) : A1b.conjSub n K = K := by
  ext x
  rw [A1b.mem_conjSub_iff]
  constructor
  · intro hx
    have h := hK n hn _ hx
    have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rwa [e] at h
  · intro hx
    have h := hK n⁻¹ (N.inv_mem hn) x hx
    rwa [inv_inv] at h

theorem conjSub_normalized {N S0 : Subgroup G} (hN : N.Normal)
    (hS0 : ∀ n ∈ N, ∀ s ∈ S0, n * s * n⁻¹ ∈ S0) (g : G) :
    ∀ n ∈ N, ∀ k ∈ A1b.conjSub g S0, n * k * n⁻¹ ∈ A1b.conjSub g S0 := by
  intro n hn k hk
  rw [A1b.mem_conjSub_iff] at hk ⊢
  have hm : g⁻¹ * n * g ∈ N := by
    have h := hN.conj_mem n hn g⁻¹
    rwa [inv_inv] at h
  have h := hS0 _ hm _ hk
  have e : g⁻¹ * (n * k * n⁻¹) * g = (g⁻¹ * n * g) * (g⁻¹ * k * g) * (g⁻¹ * n * g)⁻¹ := by
    group
  rw [e]
  exact h

theorem noncomm_conjSub {S0 : Subgroup G} {a b : G} (ha : a ∈ S0) (hb : b ∈ S0)
    (hab : a * b ≠ b * a) (g : G) :
    ∃ x ∈ A1b.conjSub g S0, ∃ y ∈ A1b.conjSub g S0, x * y ≠ y * x := by
  refine ⟨g * a * g⁻¹, A1b.mem_conjSub_of_mem ha, g * b * g⁻¹, A1b.mem_conjSub_of_mem hb,
    fun h => hab ?_⟩
  calc a * b = g⁻¹ * (g * a * g⁻¹ * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * b * g⁻¹ * (g * a * g⁻¹)) * g := by rw [h]
    _ = b * a := by group

theorem isSimpleGroup_conjSub {S0 : Subgroup G} [IsSimpleGroup ↥S0] (g : G) :
    IsSimpleGroup ↥(A1b.conjSub g S0) :=
  MulEquiv.isSimpleGroup
    (S0.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

end Commute

section Preimage

variable {Q : Type} [Group Q]

def preimConj (Y : Subgroup Q) [Y.Normal] (S0 : Subgroup (Q ⧸ Y)) (g : Q ⧸ Y) : Subgroup Q :=
  (A1b.conjSub g S0).comap (QuotientGroup.mk' Y)

theorem conjSub_comap_mk {Y : Subgroup Q} [Y.Normal] (K : Subgroup (Q ⧸ Y)) (t : Q) :
    A1b.conjSub t (K.comap (QuotientGroup.mk' Y)) =
      (A1b.conjSub (QuotientGroup.mk' Y t) K).comap (QuotientGroup.mk' Y) := by
  ext x
  simp only [A1b.mem_conjSub_iff, Subgroup.mem_comap, map_mul, map_inv]

theorem conjSub_preimConj {Y : Subgroup Q} [Y.Normal] (S0 : Subgroup (Q ⧸ Y)) (t : Q)
    (g : Q ⧸ Y) :
    A1b.conjSub t (preimConj Y S0 g) = preimConj Y S0 (QuotientGroup.mk' Y t * g) := by
  unfold preimConj
  rw [conjSub_comap_mk, A1b.conjSub_mul]

end Preimage

section Factors

theorem exists_noncomm_factor {G : Type} [Group G] {N : Subgroup G} {r : ℕ}
    {Sf : Fin r → Subgroup G} (i0 : Fin r)
    (hconj : ∀ i, ∃ g : G, Sf i = CFSG.conjugate (Sf i0) g)
    (e : ((i : Fin r) → Sf i) ≃* ↥N) (hN : ¬ Group.IsSolvable ↥N) :
    ∃ a ∈ Sf i0, ∃ b ∈ Sf i0, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcommF : ∀ i, ∀ a ∈ Sf i, ∀ b ∈ Sf i, a * b = b * a := by
    intro i a ha b hb
    obtain ⟨g, hg⟩ := hconj i
    rw [hg] at ha hb
    unfold CFSG.conjugate at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, hcon a' ha' b' hb']
  have hcommPi : ∀ u v : (i : Fin r) → Sf i, u * v = v * u := by
    intro u v
    funext i
    apply Subtype.ext
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    exact hcommF i _ (u i).2 _ (v i).2
  have hcommN : ∀ x y : ↥N, x * y = y * x := by
    intro x y
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    rw [← map_mul e u v, ← map_mul e v u, hcommPi u v]
  exact hN (Group.isSolvable_of_comm hcommN)

end Factors

section Family

variable {Q : Type} [Group Q]

theorem exists_semisimpleMod {S X Y : Subgroup Q} [X.Normal] [Y.Normal]
    (hYX : Y ≤ X) (hmin : ∀ N : Subgroup Q, N.Normal → Y ≤ N → N ≤ X → N = Y ∨ N = X)
    (hXS : X ⊔ S = ⊤) {S0 : Subgroup (Q ⧸ Y)} (hS0N : S0 ≤ X.map (QuotientGroup.mk' Y))
    (hS0s : IsSimpleGroup ↥S0) (hS0n : (S0.subgroupOf (X.map (QuotientGroup.mk' Y))).Normal)
    (hS0nab : ∃ a ∈ S0, ∃ b ∈ S0, a * b ≠ b * a) :
    ∃ ℒ : Set (Subgroup Q), ℒ.Nonempty ∧ SemisimpleMod S X Y ℒ := by
  have hπs : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  have hN : (X.map (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.map ‹X.Normal› _ hπs
  have hS0n' : ∀ n ∈ X.map (QuotientGroup.mk' Y), ∀ s ∈ S0, n * s * n⁻¹ ∈ S0 :=
    conj_mem_of_subgroupOf hS0N hS0n
  have hKn : ∀ g : Q ⧸ Y, ∀ n ∈ X.map (QuotientGroup.mk' Y), ∀ k ∈ A1b.conjSub g S0,
      n * k * n⁻¹ ∈ A1b.conjSub g S0 :=
    fun g => conjSub_normalized hN hS0n' g
  have hKle : ∀ g : Q ⧸ Y, A1b.conjSub g S0 ≤ X.map (QuotientGroup.mk' Y) :=
    fun g => conjSub_le_of_normal hN hS0N g
  have hKs : ∀ g : Q ⧸ Y, IsSimpleGroup ↥(A1b.conjSub g S0) :=
    fun g => isSimpleGroup_conjSub g
  have hS0ne : S0 ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hS0nab
    apply hab
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hfix : ∀ g : Q ⧸ Y, ∀ x ∈ X,
      A1b.conjSub x (preimConj Y S0 g) = preimConj Y S0 g := by
    intro g x hx
    unfold preimConj
    rw [conjSub_comap_mk, conjSub_eq_of_normalized (hKn g) (Subgroup.mem_map_of_mem _ hx)]
  have hY_le : ∀ L ∈ Set.range (preimConj Y S0), Y ≤ L := by
    rintro _ ⟨g, rfl⟩ y hy
    have h1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    show QuotientGroup.mk' Y y ∈ A1b.conjSub g S0
    rw [h1]
    exact (A1b.conjSub g S0).one_mem
  have hL_le : ∀ L ∈ Set.range (preimConj Y S0), L ≤ X := by
    rintro _ ⟨g, rfl⟩
    calc preimConj Y S0 g ≤ (X.map (QuotientGroup.mk' Y)).comap (QuotientGroup.mk' Y) :=
          Subgroup.comap_mono (hKle g)
      _ = X := comap_map_mk hYX
  have hsimple : ∀ L ∈ Set.range (preimConj Y S0), ∀ N' : Subgroup Q, Y ≤ N' → N' ≤ L →
      (N'.subgroupOf L).Normal → N' = Y ∨ N' = L := by
    rintro _ ⟨g, rfl⟩ N' hYN' hN'L hnorm
    haveI := hKs g
    have hMK : N'.map (QuotientGroup.mk' Y) ≤ A1b.conjSub g S0 := by
      rw [Subgroup.map_le_iff_le_comap]
      exact hN'L
    have hMn : ∀ k ∈ A1b.conjSub g S0, ∀ m ∈ N'.map (QuotientGroup.mk' Y),
        k * m * k⁻¹ ∈ N'.map (QuotientGroup.mk' Y) := by
      intro k hk m hm
      obtain ⟨l, rfl⟩ := hπs k
      obtain ⟨n, hn, rfl⟩ := hm
      have hl : l ∈ preimConj Y S0 g := hk
      have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' Y)
        (conj_mem_of_subgroupOf hN'L hnorm l hl n hn)
      simpa only [map_mul, map_inv] using h1
    haveI : ((N'.map (QuotientGroup.mk' Y)).subgroupOf (A1b.conjSub g S0)).Normal :=
      normal_subgroupOf_of_conj hMK hMn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N'.map (QuotientGroup.mk' Y)).subgroupOf (A1b.conjSub g S0)) with h | h
    · left
      have hM0 : N'.map (QuotientGroup.mk' Y) = ⊥ := by
        rw [← inf_eq_left.mpr hMK]
        exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      refine le_antisymm (fun n hn => ?_) hYN'
      have h1 : QuotientGroup.mk' Y n ∈ N'.map (QuotientGroup.mk' Y) :=
        Subgroup.mem_map_of_mem _ hn
      rw [hM0, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff n).mp h1
    · right
      have hKM : A1b.conjSub g S0 ≤ N'.map (QuotientGroup.mk' Y) :=
        Subgroup.subgroupOf_eq_top.mp h
      refine le_antisymm hN'L (fun l hl => ?_)
      have hl' : QuotientGroup.mk' Y l ∈ A1b.conjSub g S0 := hl
      obtain ⟨n, hn, hnl⟩ := hKM hl'
      have h2 : n⁻¹ * l ∈ Y := QuotientGroup.eq.mp hnl
      have h3 := N'.mul_mem hn (hYN' h2)
      rwa [mul_inv_cancel_left] at h3
  have hnonab : ∀ L ∈ Set.range (preimConj Y S0), ¬ ⁅L, L⁆ ≤ Y := by
    rintro _ ⟨g, rfl⟩ hle
    obtain ⟨a, ha, b, hb, hab⟩ := hS0nab
    obtain ⟨x1, hx1, x2, hx2, hx12⟩ := noncomm_conjSub ha hb hab g
    obtain ⟨l1, rfl⟩ := hπs x1
    obtain ⟨l2, rfl⟩ := hπs x2
    have hl1 : l1 ∈ preimConj Y S0 g := hx1
    have hl2 : l2 ∈ preimConj Y S0 g := hx2
    have hc : ⁅l1, l2⁆ ∈ ⁅preimConj Y S0 g, preimConj Y S0 g⁆ :=
      Subgroup.commutator_mem_commutator hl1 hl2
    have h1 : QuotientGroup.mk' Y ⁅l1, l2⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hle hc)
    apply hx12
    simp only [commutatorElement_def, map_mul, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hcomm : ∀ L ∈ Set.range (preimConj Y S0), ∀ L' ∈ Set.range (preimConj Y S0),
      L ≠ L' → ⁅L, L'⁆ ≤ Y := by
    rintro _ ⟨g1, rfl⟩ _ ⟨g2, rfl⟩ hne
    have hne' : A1b.conjSub g1 S0 ≠ A1b.conjSub g2 S0 := fun h =>
      hne (by unfold preimConj; rw [h])
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hx' : QuotientGroup.mk' Y x ∈ A1b.conjSub g1 S0 := hx
    have hy' : QuotientGroup.mk' Y y ∈ A1b.conjSub g2 S0 := hy
    have hc : QuotientGroup.mk' Y x * QuotientGroup.mk' Y y =
        QuotientGroup.mk' Y y * QuotientGroup.mk' Y x :=
      commute_of_normal_simple (hKle g1) (hKle g2) (hKn g1) (hKn g2) (hKs g1) (hKs g2) hne'
        hx' hy'
    have h1 : QuotientGroup.mk' Y ⁅x, y⁆ = 1 := by
      simp only [commutatorElement_def, map_mul, map_inv]
      rw [hc]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hgen : (⨆ L ∈ Set.range (preimConj Y S0), L) = X := by
    refine le_antisymm (iSup₂_le fun L hL => hL_le L hL) ?_
    have hUn : (⨆ L ∈ Set.range (preimConj Y S0), L).Normal := by
      refine ⟨fun n hn q => ?_⟩
      have hmap : (⨆ L ∈ Set.range (preimConj Y S0), L).map (MulAut.conj q).toMonoidHom ≤
          ⨆ L ∈ Set.range (preimConj Y S0), L := by
        rw [Subgroup.map_iSup]
        refine iSup_le fun L => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun hL => ?_
        obtain ⟨g, rfl⟩ := hL
        show A1b.conjSub q (preimConj Y S0 g) ≤ _
        rw [conjSub_preimConj]
        exact le_iSup₂ (f := fun L (_ : L ∈ Set.range (preimConj Y S0)) => L)
          (preimConj Y S0 (QuotientGroup.mk' Y q * g)) ⟨_, rfl⟩
      exact hmap (Subgroup.mem_map_of_mem _ hn)
    have hYU : Y ≤ ⨆ L ∈ Set.range (preimConj Y S0), L :=
      (hY_le (preimConj Y S0 1) ⟨1, rfl⟩).trans
        (le_iSup₂ (f := fun L (_ : L ∈ Set.range (preimConj Y S0)) => L) (preimConj Y S0 1)
          ⟨1, rfl⟩)
    have hUX : (⨆ L ∈ Set.range (preimConj Y S0), L) ≤ X :=
      iSup₂_le fun L hL => hL_le L hL
    rcases hmin _ hUn hYU hUX with h | h
    · exfalso
      obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS0ne
      have hs1' : s ≠ 1 := fun h' => hs1 (Subtype.ext h')
      obtain ⟨q, rfl⟩ := hπs s
      have hq1 : q ∈ preimConj Y S0 1 := by
        show QuotientGroup.mk' Y q ∈ A1b.conjSub 1 S0
        rw [A1b.conjSub_one]
        exact hs
      have hqU : q ∈ ⨆ L ∈ Set.range (preimConj Y S0), L :=
        le_iSup₂ (f := fun L (_ : L ∈ Set.range (preimConj Y S0)) => L) (preimConj Y S0 1)
          ⟨1, rfl⟩ hq1
      rw [h] at hqU
      exact hs1' ((QuotientGroup.eq_one_iff q).mpr hqU)
    · exact h.symm.le
  have hconj : ∀ L ∈ Set.range (preimConj Y S0), ∀ t ∈ S,
      A1b.conjSub t L ∈ Set.range (preimConj Y S0) := by
    rintro _ ⟨g, rfl⟩ t _
    exact ⟨QuotientGroup.mk' Y t * g, (conjSub_preimConj S0 t g).symm⟩
  have htrans : ∀ L ∈ Set.range (preimConj Y S0), ∀ L' ∈ Set.range (preimConj Y S0),
      ∃ t ∈ S, A1b.conjSub t L = L' := by
    rintro _ ⟨g1, rfl⟩ _ ⟨g2, rfl⟩
    obtain ⟨q, hq⟩ := hπs (g2 * g1⁻¹)
    have hqXS : q ∈ X ⊔ S := by
      rw [hXS]
      exact Subgroup.mem_top q
    obtain ⟨x, hx, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hqXS
    refine ⟨s, hs, ?_⟩
    have hxs : A1b.conjSub (x * s) (preimConj Y S0 g1) = preimConj Y S0 g2 := by
      rw [conjSub_preimConj, hq, inv_mul_cancel_right]
    have hsX : A1b.conjSub (x * s) (preimConj Y S0 g1) = A1b.conjSub s (preimConj Y S0 g1) := by
      rw [A1b.conjSub_mul, conjSub_preimConj S0 s g1, hfix _ x hx]
    exact hsX.symm.trans hxs
  exact ⟨Set.range (preimConj Y S0), Set.range_nonempty _,
    { Y_le := hY_le, le_D := hL_le, simple := hsimple, nonab := hnonab, comm := hcomm,
      gen := hgen, conj := hconj, trans := htrans }⟩

end Family

section Pgroup

variable {Q : Type} [Group Q]

theorem pGroup_commutator_le [Finite Q] {X Y : Subgroup Q} [X.Normal] [Y.Normal]
    (hYX : Y ≤ X) (hYsolv : Group.IsSolvable ↥Y) (hXns : ¬ Group.IsSolvable ↥X)
    (hNmin : ∀ M : Subgroup (Q ⧸ Y), M.Normal → M ≤ X.map (QuotientGroup.mk' Y) →
      M = ⊥ ∨ M = X.map (QuotientGroup.mk' Y))
    {W : Subgroup Q} (hWn : W.Normal) (hW : IsPGroup 2 W) : ⁅X, W⁆ ≤ Y := by
  have hπs : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  have hWn' : (W.map (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.map hWn _ hπs
  have hNn : (X.map (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.map ‹X.Normal› _ hπs
  have hW2 : IsPGroup 2 (W.map (QuotientGroup.mk' Y)) := IsPGroup.map hW (QuotientGroup.mk' Y)
  rcases hNmin (W.map (QuotientGroup.mk' Y) ⊓ X.map (QuotientGroup.mk' Y)) inferInstance
    inf_le_right with h | h
  · refine Subgroup.commutator_le.mpr fun x hx w hw => ?_
    have hxN : QuotientGroup.mk' Y x ∈ X.map (QuotientGroup.mk' Y) :=
      Subgroup.mem_map_of_mem _ hx
    have hwW : QuotientGroup.mk' Y w ∈ W.map (QuotientGroup.mk' Y) :=
      Subgroup.mem_map_of_mem _ hw
    have key : QuotientGroup.mk' Y ⁅x, w⁆ = QuotientGroup.mk' Y x * QuotientGroup.mk' Y w *
        (QuotientGroup.mk' Y x)⁻¹ * (QuotientGroup.mk' Y w)⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv]
    have hc : QuotientGroup.mk' Y ⁅x, w⁆ ∈
        W.map (QuotientGroup.mk' Y) ⊓ X.map (QuotientGroup.mk' Y) := by
      rw [key]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (W.map (QuotientGroup.mk' Y)).mul_mem
          (hWn'.conj_mem _ hwW _) ((W.map (QuotientGroup.mk' Y)).inv_mem hwW)
      · have h2 := (X.map (QuotientGroup.mk' Y)).mul_mem hxN
          (hNn.conj_mem _ ((X.map (QuotientGroup.mk' Y)).inv_mem hxN) (QuotientGroup.mk' Y w))
        simpa [mul_assoc] using h2
    rw [h, Subgroup.mem_bot] at hc
    exact (QuotientGroup.eq_one_iff _).mp hc
  · exfalso
    have hle : X.map (QuotientGroup.mk' Y) ≤ W.map (QuotientGroup.mk' Y) := by
      have h3 := inf_le_left (a := W.map (QuotientGroup.mk' Y)) (b := X.map (QuotientGroup.mk' Y))
      rwa [h] at h3
    haveI : Group.IsSolvable ↥(W.map (QuotientGroup.mk' Y)) :=
      E1.isSolvable_of_isPGroup_two hW2
    exact hXns (isSolvable_of_map_mk hYX hYsolv
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)))

end Pgroup

theorem chief_dichotomy {Q : Type} [Group Q] [Finite Q] {S X Y : Subgroup Q} [X.Normal]
    [Y.Normal] (hS : IsSylowIn 2 S ⊤) (hYX : Y ≤ X) (hne : Y ≠ X)
    (hmin : ∀ N : Subgroup Q, N.Normal → Y ≤ N → N ≤ X → N = Y ∨ N = X)
    (hXS : X ⊔ S = ⊤) (hK : ∀ K : Subgroup Q, S ≤ K → K ⊔ Y = ⊤ → K = ⊤) :
    Group.IsSolvable ↥Y ∧ (Group.IsSolvable ↥X ∨
      (∃ ℒ : Set (Subgroup Q), ℒ.Nonempty ∧ SemisimpleMod S X Y ℒ ∧
        ∀ W : Subgroup Q, W.Normal → IsPGroup 2 W → ⁅X, W⁆ ≤ Y)) := by
  have hYsolv : Group.IsSolvable ↥Y := isSolvable_of_Y hS hXS hK
  refine ⟨hYsolv, ?_⟩
  by_cases hXsolv : Group.IsSolvable ↥X
  · exact Or.inl hXsolv
  · right
    have hNn : (X.map (QuotientGroup.mk' Y)).Normal :=
      Subgroup.Normal.map ‹X.Normal› _ (QuotientGroup.mk'_surjective Y)
    have hNbot := map_mk_ne_bot hYX hne
    have hNmin := map_minimal hYX hmin
    have hNns : ¬ Group.IsSolvable ↥(X.map (QuotientGroup.mk' Y)) :=
      fun h => hXsolv (isSolvable_of_map_mk hYX hYsolv h)
    obtain ⟨r, Sf, hr, hSfN, hSfs, hSfconj, hSfn, e, -⟩ :=
      CFSG.LocalCores.minimal_normal_simple_factors hNn hNbot hNmin
    have hr0 : 0 < r := by omega
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_noncomm_factor (N := X.map (QuotientGroup.mk' Y)) ⟨0, hr0⟩
        (fun i => hSfconj ⟨0, hr0⟩ i) e hNns
    obtain ⟨ℒ, hℒne, hsm⟩ := exists_semisimpleMod hYX hmin hXS (hSfN ⟨0, hr0⟩)
      (hSfs ⟨0, hr0⟩) (hSfn ⟨0, hr0⟩) ⟨a, ha, b, hb, hab⟩
    exact ⟨ℒ, hℒne, hsm, fun W hWn hW => pGroup_commutator_le hYX hYsolv hXsolv hNmin hWn hW⟩

end CFSG.Quasithin.RonanE111
