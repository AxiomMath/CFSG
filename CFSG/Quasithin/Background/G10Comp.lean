module

public import CFSG.Quasithin.Background.G10Ten
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Comp

variable {G : Type} [Group G]

theorem mem_map_conj {t x : G} {K : Subgroup G} :
    x ∈ K.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * x * t ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    refine ⟨t⁻¹ * x * t, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_mul {s t : G} {K : Subgroup G} :
    K.map (MulAut.conj (s * t)).toMonoidHom =
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
  ext x
  simp only [mem_map_conj]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem map_conj_one {K : Subgroup G} : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

theorem map_conj_inv_map_conj {t : G} {K : Subgroup G} :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = K := by
  rw [← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem map_conj_eq_self_iff {t : G} {K : Subgroup G} :
    K.map (MulAut.conj t).toMonoidHom = K ↔ t ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := SetLike.ext_iff.1 h (t * y * t⁻¹)
    rw [mem_map_conj] at h1
    have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
    rw [e] at h1
    exact h1
  · intro h
    ext x
    rw [mem_map_conj]
    have := h (t⁻¹ * x * t)
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rw [e] at this
    exact this

def nclos (L : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ γ : G, ∃ l ∈ L, x = γ * l * γ⁻¹}

theorem conj_le_nclos (L : Subgroup G) (γ : G) : L.map (MulAut.conj γ).toMonoidHom ≤ nclos L := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact Subgroup.subset_closure ⟨γ, l, hl, by simp [MulAut.conj_apply]⟩

theorem le_nclos (L : Subgroup G) : L ≤ nclos L := by
  have := conj_le_nclos L 1
  rwa [map_conj_one] at this

theorem nclos_normal (L : Subgroup G) : (nclos L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, l, hl, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨g * δ, l, hl, by group⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have := (nclos L).mul_mem hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := (nclos L).inv_mem hx
    convert this using 1
    group

theorem nclos_le {L N : Subgroup G} (h : ∀ γ : G, L.map (MulAut.conj γ).toMonoidHom ≤ N) :
    nclos L ≤ N := by
  rw [nclos, Subgroup.closure_le]
  rintro _ ⟨γ, l, hl, rfl⟩
  exact h γ ⟨l, hl, by simp [MulAut.conj_apply]⟩

theorem comm_map_conj {H X : Subgroup G} {τ : G} (hH : H.map (MulAut.conj τ).toMonoidHom = H)
    (hX : X.map (MulAut.conj τ).toMonoidHom = X) :
    ⁅H, X⁆.map (MulAut.conj τ).toMonoidHom = ⁅H, X⁆ := by
  rw [Subgroup.map_commutator, hH, hX]

theorem gwQuasisimple_of_open {K : Subgroup G} (h : CFSG.Open.IsQuasisimple ↥K) :
    CFSG.GorensteinWalter.IsQuasisimple ↥K := by
  refine ⟨?_, h.1, h.2⟩
  obtain ⟨a, b, hab⟩ := h.2.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h' => hab (by rw [h'])⟩

theorem isSubnormal_of_open {H : Subgroup G} (h : CFSG.Open.IsSubnormal H ⊤) : H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff.1 h

theorem quasisimple_map_conj {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L) (γ : G) :
    CFSG.Open.IsQuasisimple ↥(L.map (MulAut.conj γ).toMonoidHom) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective L (MulAut.conj γ).toMonoidHom (MulAut.conj γ).injective).symm hL

variable [Finite G]

def conjSet (L : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ γ : G, M = L.map (MulAut.conj γ).toMonoidHom}

theorem index_normalizer_le (L : Subgroup G) :
    (Subgroup.normalizer (L : Set G)).index ≤ (conjSet L).ncard := by
  classical
  set S0 := Subgroup.normalizer (L : Set G) with hS0
  have hwd : ∀ a b : G, (QuotientGroup.leftRel S0).r a b →
      L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have h1 := map_conj_eq_self_iff.2 hab
    have : b = a * (a⁻¹ * b) := by group
    rw [this, map_conj_mul, h1]
  let f : G ⧸ S0 → conjSet L := fun q =>
    ⟨Quotient.liftOn' q (fun g => L.map (MulAut.conj g).toMonoidHom) hwd, by
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b =>
        have h' : L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom :=
          congrArg Subtype.val h
        rw [QuotientGroup.eq]
        rw [← map_conj_eq_self_iff]
        have h2 : L.map (MulAut.conj (a⁻¹ * b)).toMonoidHom = L := by
          rw [map_conj_mul, ← h']
          exact map_conj_inv_map_conj
        exact h2
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_coe_set_eq] at this
  exact this

theorem exists_trans {L T : Subgroup G} (hcard : (conjSet L).ncard ≤ 2) (hT : ¬ 2 ∣ T.index)
    (γ : G) : ∃ τ ∈ T, L.map (MulAut.conj γ).toMonoidHom = L.map (MulAut.conj τ).toMonoidHom := by
  classical
  by_cases hS0 : Subgroup.normalizer (L : Set G) = ⊤
  · refine ⟨1, T.one_mem, ?_⟩
    rw [map_conj_one]
    exact map_conj_eq_self_iff.2 (hS0 ▸ Subgroup.mem_top γ)
  · have h1 : (Subgroup.normalizer (L : Set G)).index ≠ 1 := fun h =>
      hS0 (Subgroup.index_eq_one.1 h)
    have hle := (index_normalizer_le L).trans hcard
    have hpos : (Subgroup.normalizer (L : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : (Subgroup.normalizer (L : Set G)).index = 2 := by omega
    have hTnot : ¬ T ≤ Subgroup.normalizer (L : Set G) := by
      intro hle'
      apply hT
      have := Subgroup.relIndex_mul_index hle'
      rw [h2] at this
      exact ⟨T.relIndex _, by rw [← this, mul_comm]⟩
    obtain ⟨t, htT, htn⟩ := IsConcreteLE.not_le_iff_exists.1 hTnot
    have hne : L.map (MulAut.conj t).toMonoidHom ≠ L := fun h => htn (map_conj_eq_self_iff.1 h)
    have hsub : ({L, L.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)) ⊆ conjSet L := by
      intro M hM
      rcases hM with rfl | rfl
      · exact ⟨1, map_conj_one.symm⟩
      · exact ⟨t, rfl⟩
    have hpair : ({L, L.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)).ncard = 2 :=
      Set.ncard_pair (Ne.symm hne)
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; exact hcard)
    have hγ : L.map (MulAut.conj γ).toMonoidHom ∈ conjSet L := ⟨γ, rfl⟩
    rw [← heq] at hγ
    rcases hγ with h | h
    · exact ⟨1, T.one_mem, by rw [h, map_conj_one]⟩
    · exact ⟨t, htT, h⟩

theorem core_top {L X T : Subgroup G} (hLsn : L.IsSubnormal) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hnc : ⁅L, X⁆ ≠ ⊥) (hcard : (conjSet L).ncard ≤ 2) (hT : ¬ 2 ∣ T.index)
    (hTn : T ≤ Subgroup.normalizer (X : Set G)) : ⁅nclos L, X⁆ = nclos L := by
  classical
  set H := nclos L with hH
  have hHn : H.Normal := nclos_normal L
  have hLH : L ≤ H := le_nclos L
  have hNle : ⁅H, X⁆ ≤ H := Subgroup.commutator_le_left H X
  by_contra hne
  set N := ⁅H, X⁆ with hN
  have hNnorm : (N.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left H X)
  have hNsub : N.IsSubnormal := Subgroup.IsSubnormal.step N H hNle hHn.isSubnormal hNnorm
  have hTN : ∀ τ ∈ T, N.map (MulAut.conj τ).toMonoidHom = N := by
    intro τ hτ
    apply comm_map_conj
    · exact map_conj_eq_self_iff.2 (by rw [Subgroup.normalizer_eq_top_iff.2 hHn]; trivial)
    · exact map_conj_eq_self_iff.2 (hTn hτ)
  have hcomp : ∀ γ : G, CFSG.GorensteinWalter.IsComponentOf
      (L.map (MulAut.conj γ).toMonoidHom) (⊤ : Subgroup G) := by
    intro γ
    refine ⟨le_top, ?_, gwQuasisimple_of_open (quasisimple_map_conj hLq γ)⟩
    exact (hLsn.map (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).surjective).subgroupOf
  have htrans := fun γ => exists_trans hcard hT γ
  have hLN : ¬ L ≤ N := by
    intro hLN
    have hHN : H ≤ N := by
      refine nclos_le fun γ => ?_
      obtain ⟨τ, hτ, hγ⟩ := htrans γ
      rw [hγ]
      exact (Subgroup.map_mono hLN).trans (hTN τ hτ).le
    exact hne (le_antisymm hNle hHN)
  have hcent : ∀ γ : G, ⁅L.map (MulAut.conj γ).toMonoidHom, N⁆ = ⊥ := by
    intro γ
    rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot (hcomp γ) hNsub with hle | hbot
    · exfalso
      apply hLN
      obtain ⟨τ, hτ, hγ⟩ := htrans γ
      have h1 : L.map (MulAut.conj τ).toMonoidHom ≤ N := hγ ▸ hle
      have h2 := Subgroup.map_mono (f := (MulAut.conj τ⁻¹).toMonoidHom) h1
      rw [map_conj_inv_map_conj, hTN τ⁻¹ (T.inv_mem hτ)] at h2
      exact h2
    · exact hbot
  have hHN : ⁅H, N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine nclos_le fun γ => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcent γ)
  have h1 : ⁅⁅H, X⁆, H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hHN
  have h2 : ⁅⁅X, H⁆, H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm X H]
    exact h1
  have h3 : ⁅⁅H, H⁆, X⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := H) (H₂ := H) (H₃ := X) h1 h2
  have hHH : ⁅H, H⁆ = H := by
    refine le_antisymm (Subgroup.commutator_le_left H H) (nclos_le fun γ => ?_)
    have hKq := quasisimple_map_conj hLq γ
    have hKperf : Group.IsPerfect ↥(L.map (MulAut.conj γ).toMonoidHom) :=
      (Group.isPerfect_def).2 hKq.1
    have hKK := Subgroup.isPerfect_iff.1 hKperf
    calc L.map (MulAut.conj γ).toMonoidHom = ⁅L.map (MulAut.conj γ).toMonoidHom,
          L.map (MulAut.conj γ).toMonoidHom⁆ := hKK.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono (conj_le_nclos L γ) (conj_le_nclos L γ)
  rw [hHH] at h3
  apply hnc
  rw [eq_bot_iff, ← h3]
  exact Subgroup.commutator_mono hLH le_rfl


end Comp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g10_comp : G10ComponentStmt := by
  intro V _ _ _ Γ X L T hL hXΓ hnc hcard hT hTn
  have hLΓ : L ≤ Γ := hL.1
  have hLcomp : CFSG.Open.IsComponentOf (L.subgroupOf Γ) (⊤ : Subgroup ↥Γ) :=
    (isComponentOf_iff_subgroupOf.1 hL).2
  have hLsn' : (L.subgroupOf Γ).IsSubnormal := Comp.isSubnormal_of_open hLcomp.2.1
  have hLq' : CFSG.Open.IsQuasisimple ↥(L.subgroupOf Γ) := hLcomp.2.2
  have hnc' : ⁅L.subgroupOf Γ, X.subgroupOf Γ⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, l, hl, hxl⟩ := hnc
    apply hxl
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot)
      (show (⟨l, hLΓ hl⟩ : ↥Γ) ∈ L.subgroupOf Γ from hl)
    have := Subgroup.mem_centralizer_iff.1 hc ⟨x, hXΓ hx⟩
      (show (⟨x, hXΓ hx⟩ : ↥Γ) ∈ X.subgroupOf Γ from hx)
    exact congrArg Subtype.val this
  have hcard' : (Comp.conjSet (L.subgroupOf Γ)).ncard ≤ 2 := by
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun M' => M'.map Γ.subtype) ?_ ?_ ?_) hcard
    · rintro M' ⟨γ', rfl⟩
      refine ⟨γ', γ'.2, ?_⟩
      ext x
      rw [Comp.mem_map_conj, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Comp.mem_map_conj] at hy
        exact hy
      · intro h
        have hxΓ : x ∈ Γ := by
          have h1 : (γ' : GLV V) * ((γ' : GLV V)⁻¹ * x * γ') * (γ' : GLV V)⁻¹ ∈ Γ :=
            Γ.mul_mem (Γ.mul_mem γ'.2 (hLΓ h)) (Γ.inv_mem γ'.2)
          simpa [mul_assoc] using h1
        refine ⟨⟨x, hxΓ⟩, ?_, rfl⟩
        rw [Comp.mem_map_conj]
        exact h
    · intro M₁ _ M₂ _ h
      exact Subgroup.map_injective Γ.subtype_injective h
    · exact Set.toFinite _
  have hT' : ¬ 2 ∣ (T.subgroupOf Γ).index := hT.2.2
  have hTn' : T.subgroupOf Γ ≤ Subgroup.normalizer ((X.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.1 (hTn ht)) (x : GLV V)
    simpa [Subgroup.mem_subgroupOf] using this
  have key := Comp.core_top hLsn' hLq' hnc' hcard' hT' hTn'
  have hH : (Comp.nclos (L.subgroupOf Γ)).map Γ.subtype = normalClosure Γ L := by
    unfold Comp.nclos normalClosure
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨γ', l', hl', rfl⟩, rfl⟩
      exact ⟨γ', γ'.2, l', hl', by simp⟩
    · rintro ⟨γ, hγ, l, hl, rfl⟩
      exact ⟨⟨γ, hγ⟩ * ⟨l, hLΓ hl⟩ * ⟨γ, hγ⟩⁻¹, ⟨⟨γ, hγ⟩, ⟨l, hLΓ hl⟩, hl, rfl⟩, by simp⟩
  have hX : (X.subgroupOf Γ).map Γ.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXΓ
  have := congrArg (Subgroup.map Γ.subtype) key
  rw [Subgroup.map_commutator, hH, hX] at this
  exact this

theorem g10_10_of_g10_4 (h4 : G1004Stmt) : G1010Stmt := g10_10 h4 g10_comp

end G11

end CFSG.Quasithin
