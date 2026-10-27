module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltSigma

import CFSG.Alternating.Multipliers.DoubleCoverSquares
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec3SevenFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem inv_mul_mem_zpowers_of_mem_ZQ (S : Setting z E F) (hZ : Nat.card ↥(ZQ z) = 4)
    {b u : G} (hb : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z) (hu : u ∈ ZQ z)
    (huz : u ∉ Subgroup.zpowers z) : b⁻¹ * u ∈ Subgroup.zpowers z := by
  have hKle : Subgroup.zpowers z ≤ ZQ z := Subgroup.zpowers_le.mpr (z_mem_ZQ S)
  set K : Subgroup ↥(ZQ z) := (Subgroup.zpowers z).subgroupOf (ZQ z) with hK
  have hidx : K.index = 2 := by
    have h1 := Subgroup.card_mul_index K
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, hZ, Nat.card_zpowers,
      S.hyp.orderOf_z] at h1
    omega
  have h1 : (⟨b, hb⟩ : ↥(ZQ z))⁻¹ * ⟨u, hu⟩ ∈ K := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    refine iff_of_false ?_ ?_
    · intro hmem
      apply hbz
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    · intro hmem
      exact huz (Subgroup.mem_subgroupOf.mp hmem)
  exact Subgroup.mem_subgroupOf.mp h1

theorem mem_FsubH_or_inv_mul_mem (S : Setting z E F) (a : G) (hZ : Nat.card ↥(ZQ z) = 4)
    {b : G} (hbZ : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z)
    (hFsup : FsubH S a ⊔ ZQ z = Q z) {q : G} (hq : q ∈ Q z) :
    q ∈ FsubH S a ∨ b⁻¹ * q ∈ FsubH S a := by
  rw [← hFsup] at hq
  have hcomm : ∀ f ∈ FsubH S a, ∀ u ∈ ZQ z, f * u = u * f := fun f hf u hu =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 f (FsubH_le_Q S a hf)
  obtain ⟨f, hf, u, hu, rfl⟩ := CFSG.CGT.T75H.exists_mul_of_mem_sup_of_comm hcomm hq
  by_cases huz : u ∈ Subgroup.zpowers z
  · left
    exact (FsubH S a).mul_mem hf (Subgroup.zpowers_le.mpr (z_mem_FsubH S a) huz)
  · right
    have h1 := inv_mul_mem_zpowers_of_mem_ZQ S hZ hbZ hbz hu huz
    have hbf : b⁻¹ * f = f * b⁻¹ :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ((ZQ z).inv_mem hbZ)).2 f
        (FsubH_le_Q S a hf))).symm
    have e : b⁻¹ * (f * u) = f * (b⁻¹ * u) := by
      rw [← mul_assoc, hbf, mul_assoc]
    rw [e]
    exact (FsubH S a).mul_mem hf (Subgroup.zpowers_le.mpr (z_mem_FsubH S a) h1)

theorem inv_mul_conj_mem_zpowers_of_card_ZQ_eq_four (S : Setting z E F) (hZ : Nat.card ↥(ZQ z) = 4)
    {b : G} (hbZ : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z) {h : G} (hh : h ∈ H z) :
    b⁻¹ * (h * b * h⁻¹) ∈ Subgroup.zpowers z := by
  refine inv_mul_mem_zpowers_of_mem_ZQ S hZ hbZ hbz (conj_mem_ZQ_of_mem_H S hh hbZ) ?_
  intro hmem
  apply hbz
  have hcz : h⁻¹ * z = z * h⁻¹ := Subgroup.mem_centralizer_singleton_iff.mp ((H z).inv_mem hh)
  have hconj : h⁻¹ * (h * b * h⁻¹) * h ∈ Subgroup.zpowers z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk]
    have hc : h⁻¹ * z ^ k = z ^ k * h⁻¹ := (Commute.zpow_right (show Commute h⁻¹ z from hcz) k).eq
    calc z ^ k = z ^ k * h⁻¹ * h := by group
      _ = h⁻¹ * z ^ k * h := by rw [← hc]
  have e : h⁻¹ * (h * b * h⁻¹) * h = b := by group
  rwa [e] at hconj

theorem FsubH_le_commutator_XsubHat (S : Setting z E F) (a : G) :
    FsubH S a ≤ ⁅XsubHat S a, XsubHat S a⁆ :=
  Subgroup.commutator_mono (Q_le_XsubHat S a) le_rfl

theorem commutator_XsubHat_eq_map (S : Setting z E F) (a : G) :
    ⁅XsubHat S a, XsubHat S a⁆ =
      (_root_.commutator ↥(XsubPre S a)).map ((H z).subtype.comp (XsubPre S a).subtype) := by
  have h1 : ⁅XsubHat S a, XsubHat S a⁆ = (⁅XsubPre S a, XsubPre S a⁆).map (H z).subtype := by
    rw [Subgroup.map_commutator]
    rfl
  rw [h1, ← Subgroup.map_subtype_commutator (XsubPre S a), Subgroup.map_map]

theorem conj_mem_commutator_XsubHat (S : Setting z E F) (a : G) {h d : G} (hh : h ∈ H z)
    (hd : d ∈ ⁅XsubHat S a, XsubHat S a⁆) : h * d * h⁻¹ ∈ ⁅XsubHat S a, XsubHat S a⁆ := by
  rw [Subgroup.commutator_def] at hd ⊢
  induction hd using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨h * x₁ * h⁻¹, conj_mem_XsubHat S a hh hx₁,
      h * x₂ * h⁻¹, conj_mem_XsubHat S a hh hx₂, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihx

theorem mem_commutator_or_of_mem_XsubHat (S : Setting z E F) (a : G)
    (hperf : ⁅Xsub S a, Xsub S a⁆ = Xsub S a) (hZ : Nat.card ↥(ZQ z) = 4)
    {b : G} (hbZ : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z)
    (hFsup : FsubH S a ⊔ ZQ z = Q z) {x : G} (hx : x ∈ XsubHat S a) :
    x ∈ ⁅XsubHat S a, XsubHat S a⁆ ∨ b⁻¹ * x ∈ ⁅XsubHat S a, XsubHat S a⁆ := by
  obtain ⟨hxH, hxX⟩ := (mem_XsubHat_iff S a).mp hx
  set π := QuotientGroup.mk' ((Q z).subgroupOf (H z)) with hπ
  have hmap : (XsubPre S a).map π = Xsub S a :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hcomm : ⁅Xsub S a, Xsub S a⁆ = (⁅XsubPre S a, XsubPre S a⁆).map π := by
    rw [Subgroup.map_commutator, hmap]
  have hx' : (QuotientGroup.mk (⟨x, hxH⟩ : ↥(H z)) : Hbar z) ∈
      (⁅XsubPre S a, XsubPre S a⁆).map π := by
    rw [← hcomm, hperf]
    exact hxX
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
  have hyD : (y : G) ∈ ⁅XsubHat S a, XsubHat S a⁆ := by
    have : (y : G) ∈ (⁅XsubPre S a, XsubPre S a⁆).map (H z).subtype := ⟨y, hy, rfl⟩
    rwa [Subgroup.map_commutator] at this
  have hq : x * (y : G)⁻¹ ∈ Q z := by
    have h1 : π ((⟨x, hxH⟩ : ↥(H z)) * y⁻¹) = 1 := by
      rw [map_mul, map_inv]
      have : π (⟨x, hxH⟩ : ↥(H z)) = π y := hyx.symm
      rw [this, mul_inv_cancel]
    have h2 : (⟨x, hxH⟩ : ↥(H z)) * y⁻¹ ∈ (Q z).subgroupOf (H z) := by
      rw [← QuotientGroup.ker_mk' ((Q z).subgroupOf (H z))]
      exact MonoidHom.mem_ker.mpr h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hFD := FsubH_le_commutator_XsubHat S a
  have e1 : x = (x * (y : G)⁻¹) * y := by group
  have e2 : b⁻¹ * x = (b⁻¹ * (x * (y : G)⁻¹)) * y := by group
  rcases mem_FsubH_or_inv_mul_mem S a hZ hbZ hbz hFsup hq with h1 | h1
  · left
    rw [e1]
    exact Subgroup.mul_mem _ (hFD h1) hyD
  · right
    rw [e2]
    exact Subgroup.mul_mem _ (hFD h1) hyD

theorem b_not_mem_commutator_XsubHat (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hZ : Nat.card ↥(ZQ z) = 4) (hperf : ⁅Xsub S a, Xsub S a⁆ = Xsub S a)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8)) (ι : Hbar z ≃* Equiv.Perm (Fin 8))
    (hι : ∀ x : ↥(Xsub S a), ι (x : Hbar z) = ((e x : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)))
    (hFinf : FsubH S a ⊓ ZQ z = Subgroup.zpowers z) (hFsup : FsubH S a ⊔ ZQ z = Q z)
    {b : G} (hbZ : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z)
    {t : G} (htL : t ∈ L0 S a) (htH : t ∈ H z)
    (htX : (QuotientGroup.mk (⟨t, htH⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a)
    (ht : (ι (QuotientGroup.mk (⟨t, htH⟩ : ↥(H z)))).cycleType = {2, 2}) :
    b ∉ ⁅XsubHat S a, XsubHat S a⁆ := by
  classical
  intro hbD
  have hbQ : b ∈ Q z := (inf_le_left : ZQ z ≤ Q z) hbZ
  have hbH : b ∈ H z := Q_le_H S hbQ
  have hbX : (QuotientGroup.mk (⟨b, hbH⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a := by
    have h1 : (QuotientGroup.mk (⟨b, hbH⟩ : ↥(H z)) : Hbar z) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hbQ)
    rw [h1]
    exact (Xsub S a).one_mem
  let ε : ↥(XsubPre S a) →* G := (H z).subtype.comp (XsubPre S a).subtype
  have hε : ∀ g : ↥(XsubPre S a), ε g = (((g : ↥(H z))) : G) := fun g => rfl
  have hεinj : Function.Injective ε := fun g₁ g₂ h12 =>
    Subtype.ext (Subtype.ext h12)
  have hεH : ∀ g : ↥(XsubPre S a), ε g ∈ H z := fun g => (g : ↥(H z)).2
  have hεX : ∀ g : ↥(XsubPre S a), ε g ∈ XsubHat S a := fun g =>
    (mem_XsubHat_iff S a).mpr ⟨(g : ↥(H z)).2, g.2⟩
  let N : Subgroup ↥(XsubPre S a) := (FsubH S a).comap ε
  haveI hNn : N.Normal := ⟨fun n hn g => by
    change ε (g * n * g⁻¹) ∈ FsubH S a
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_FsubH S a (hεH g) hn⟩
  let π₀ : ↥(XsubPre S a) →* alternatingGroup (Fin 8) := e.toMonoidHom.comp (toXsub S a)
  have hπ₀N : ∀ n ∈ N, π₀ n = 1 := by
    intro n hn
    have : toXsub S a n = 1 := (toXsub_eq_one_iff S a n).mpr (FsubH_le_Q S a hn)
    simp [π₀, this]
  let π : (↥(XsubPre S a) ⧸ N) →* alternatingGroup (Fin 8) := QuotientGroup.lift N π₀ hπ₀N
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨g, hg⟩ := toXsub_surjective S a (e.symm y)
    refine ⟨QuotientGroup.mk g, ?_⟩
    change π₀ g = y
    simp [π₀, hg]
  let bL : ↥(XsubPre S a) := ⟨⟨b, hbH⟩, hbX⟩
  have hbL : ε bL = b := rfl
  have hker : ∀ x : ↥(XsubPre S a) ⧸ N,
      π x = 1 ↔ x = 1 ∨ x = (QuotientGroup.mk bL : ↥(XsubPre S a) ⧸ N) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hπg : π (QuotientGroup.mk g) = π₀ g := rfl
      constructor
      · intro h1
        rw [hπg] at h1
        have h2 : toXsub S a g = 1 := by
          have : e (toXsub S a g) = 1 := h1
          exact (MulEquiv.map_eq_one_iff e).mp this
        have hgQ : ε g ∈ Q z := (toXsub_eq_one_iff S a g).mp h2
        rcases mem_FsubH_or_inv_mul_mem S a hZ hbZ hbz hFsup hgQ with h3 | h3
        · left
          exact (QuotientGroup.eq_one_iff g).mpr h3
        · right
          refine QuotientGroup.eq.mpr ?_
          change ε (g⁻¹ * bL) ∈ FsubH S a
          rw [map_mul, map_inv, hbL]
          have h4 := (FsubH S a).inv_mem h3
          simpa using h4
      · rintro (h1 | h1)
        · rw [h1, map_one]
        · rw [h1]
          change π₀ bL = 1
          have : toXsub S a bL = 1 := (toXsub_eq_one_iff S a bL).mpr hbQ
          simp [π₀, this]
  have hζc : (QuotientGroup.mk bL : ↥(XsubPre S a) ⧸ N) ∈
      Subgroup.center (↥(XsubPre S a) ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have h1 : ⁅bL, g⁆ ∈ N := by
        change ε ⁅bL, g⁆ ∈ FsubH S a
        rw [map_commutatorElement, hbL]
        exact Subgroup.commutator_mem_commutator hbQ (hεX g)
      have h2 : ⁅(QuotientGroup.mk bL : ↥(XsubPre S a) ⧸ N),
          (QuotientGroup.mk g : ↥(XsubPre S a) ⧸ N)⁆ = 1 := by
        have := map_commutatorElement (QuotientGroup.mk' N) bL g
        rw [← QuotientGroup.mk'_apply N bL, ← QuotientGroup.mk'_apply N g, ← this]
        exact (QuotientGroup.eq_one_iff _).mpr h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hζ1 : (QuotientGroup.mk bL : ↥(XsubPre S a) ⧸ N) ≠ 1 := by
    intro h1
    have h2 : ε bL ∈ FsubH S a := (QuotientGroup.eq_one_iff bL).mp h1
    rw [hbL] at h2
    have h3 : b ∈ FsubH S a ⊓ ZQ z := ⟨h2, hbZ⟩
    rw [hFinf] at h3
    exact hbz h3
  have hLperf : Group.IsPerfect ↥(XsubPre S a) := by
    rw [Group.isPerfect_def]
    have hXperf : Group.IsPerfect ↥(Xsub S a) := Subgroup.isPerfect_iff.mpr hperf
    have hCmap : (_root_.commutator ↥(XsubPre S a)).map (toXsub S a) = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (toXsub_surjective S a), ← _root_.commutator_def]
      exact hXperf.commutator_eq_top
    have hCε : (_root_.commutator ↥(XsubPre S a)).map ε = ⁅XsubHat S a, XsubHat S a⁆ :=
      (commutator_XsubHat_eq_map S a).symm
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp (hCmap ▸ Subgroup.mem_top (toXsub S a g))
    have hkQ : ε (c⁻¹ * g) ∈ Q z := by
      refine (toXsub_eq_one_iff S a (c⁻¹ * g)).mp ?_
      rw [map_mul, map_inv, hcg, inv_mul_cancel]
    have hkD : ε (c⁻¹ * g) ∈ ⁅XsubHat S a, XsubHat S a⁆ := by
      rcases mem_FsubH_or_inv_mul_mem S a hZ hbZ hbz hFsup hkQ with h1 | h1
      · exact FsubH_le_commutator_XsubHat S a h1
      · have h2 := FsubH_le_commutator_XsubHat S a h1
        have e1 : ε (c⁻¹ * g) = b * (b⁻¹ * ε (c⁻¹ * g)) := by group
        rw [e1]
        exact Subgroup.mul_mem _ hbD h2
    rw [← hCε] at hkD
    obtain ⟨c', hc', hc'k⟩ := Subgroup.mem_map.mp hkD
    have hc'eq : c' = c⁻¹ * g := hεinj hc'k
    have hkC : c⁻¹ * g ∈ _root_.commutator ↥(XsubPre S a) := hc'eq ▸ hc'
    have e2 : g = c * (c⁻¹ * g) := by group
    rw [e2]
    exact Subgroup.mul_mem _ hc hkC
  haveI : Group.IsPerfect ↥(XsubPre S a) := hLperf
  have hsq := (CFSG.Alternating.Multipliers.Spin.sq_eq_of_perfect_double_cover (n := 8)
    le_rfl π hπsurj hker hζc hζ1).1
  let tL : ↥(XsubPre S a) := ⟨⟨t, htH⟩, htX⟩
  have hct : (((π (QuotientGroup.mk tL) : alternatingGroup (Fin 8))) :
      Equiv.Perm (Fin 8)).cycleType = {2, 2} := by
    have h1 : ((π (QuotientGroup.mk tL) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        ι (QuotientGroup.mk (⟨t, htH⟩ : ↥(H z))) := by
      show ((e (toXsub S a tL) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) = _
      rw [← hι]
      rfl
    rw [h1]
    exact ht
  have h2 := hsq (QuotientGroup.mk tL) hct
  have h3 : bL⁻¹ * tL ^ 2 ∈ N := by
    have h4 : (QuotientGroup.mk (tL ^ 2) : ↥(XsubPre S a) ⧸ N) = QuotientGroup.mk bL := by
      rw [← h2]
      rfl
    exact QuotientGroup.eq.mp h4.symm
  change ε (bL⁻¹ * tL ^ 2) ∈ FsubH S a at h3
  rw [map_mul, map_inv, map_pow, hbL] at h3
  have ht2 : t ^ 2 ∈ FsubH S a :=
    Subgroup.zpowers_le.mpr (a_mem_FsubH S h hZ) (sq_mem_zpowers_of_mem_L0 S h.isConj htL)
  have hεt : ε tL = t := rfl
  rw [hεt] at h3
  have h4 : b⁻¹ ∈ FsubH S a := by
    have := (FsubH S a).mul_mem h3 ((FsubH S a).inv_mem ht2)
    simpa using this
  have hbF : b ∈ FsubH S a := by simpa using (FsubH S a).inv_mem h4
  have h5 : b ∈ FsubH S a ⊓ ZQ z := ⟨hbF, hbZ⟩
  rw [hFinf] at h5
  exact hbz h5


theorem index_Xsub_eq_two (S : Setting z E F) (a : G) (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8))
    (ι : Hbar z ≃* Equiv.Perm (Fin 8)) : (Xsub S a).index = 2 := by
  have hX : Nat.card ↥(Xsub S a) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hH : Nat.card (Hbar z) = 40320 := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have h1 := Subgroup.card_mul_index (Xsub S a)
  rw [hX, hH] at h1
  omega

theorem exists_index_two_not_mem_of_pointMaps (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hw : w = 4) (hZ : Nat.card ↥(ZQ z) = 4)
    (hX1 : ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u)
    (hperf : ⁅Xsub S a, Xsub S a⁆ = Xsub S a)
    (hC : Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥)
    (hLle : Nat.card ↥(Lbar S a) ≤ 16) (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8))
    (hFinf : FsubH S a ⊓ ZQ z = Subgroup.zpowers z) (hFsup : FsubH S a ⊔ ZQ z = Q z)
    {b : G} (hbZ : b ∈ ZQ z) (hbz : b ∉ Subgroup.zpowers z) :
    ∃ H₁ : Subgroup G, H₁ ≤ H z ∧ H₁.relIndex (H z) = 2 ∧ b ∉ H₁ ∧
      ⁅XsubHat S a, XsubHat S a⁆ ≤ H₁ := by
  classical
  haveI := Xsub_normal S a
  have hbQ : b ∈ Q z := (inf_le_left : ZQ z ≤ Q z) hbZ
  have hbH : b ∈ H z := Q_le_H S hbQ
  obtain ⟨r, hrL0, hrX⟩ := exists_mem_L0_not_mem_XsubHat S h hZ hX1
  have hrH : r ∈ H z := (Subgroup.mem_inf.mp hrL0).2
  have hrL : (QuotientGroup.mk (⟨r, hrH⟩ : ↥(H z)) : Hbar z) ∈ Lbar S a :=
    mem_Lbar_of_mem_L0 S (ℓ := ⟨r, hrH⟩) hrL0
  have hrXb : (QuotientGroup.mk (⟨r, hrH⟩ : ↥(H z)) : Hbar z) ∉ Xsub S a := fun hmem =>
    hrX ((mem_XsubHat_iff S a).mpr ⟨hrH, hmem⟩)
  obtain ⟨ι, hι⟩ := exists_mulEquiv_perm_eight S a e hC ⟨_, hrXb⟩
  obtain ⟨t', htL, htX, ht⟩ := exists_mem_Lbar_inf_Xsub_cycleType_two_two S h hw hLle e ι hι
    hrL hrXb
  obtain ⟨t, htL0, htt⟩ := exists_mem_L0_of_mem_Lbar S htL
  have hbD : b ∉ ⁅XsubHat S a, XsubHat S a⁆ :=
    b_not_mem_commutator_XsubHat S h hZ hperf e ι hι hFinf hFsup hbZ hbz htL0 t.2
      (by rw [htt]; exact htX) (by rw [htt]; exact ht)
  set D := ⁅XsubHat S a, XsubHat S a⁆ with hD
  have hDX : D ≤ XsubHat S a := Subgroup.commutator_le_self _
  have hDH : D ≤ H z := hDX.trans (XsubHat_le_H S a)
  have hzD : Subgroup.zpowers z ≤ D :=
    Subgroup.zpowers_le.mpr (FsubH_le_commutator_XsubHat S a (z_mem_FsubH S a))
  have hr2 : r ^ 2 ∈ D := by
    have h1 := sq_mem_zpowers_of_mem_L0 S h.isConj hrL0
    exact FsubH_le_commutator_XsubHat S a (Subgroup.zpowers_le.mpr (a_mem_FsubH S h hZ) h1)
  have hconj : ∀ x ∈ D, r * x * r⁻¹ ∈ D := fun x hx =>
    conj_mem_commutator_XsubHat S a hrH hx
  have hconj' : ∀ x ∈ D, r⁻¹ * x * r ∈ D := fun x hx => by
    have := conj_mem_commutator_XsubHat S a ((H z).inv_mem hrH) hx
    simpa using this
  let H₁ : Subgroup G :=
    { carrier := {x | x ∈ H z ∧ (x ∈ D ∨ r⁻¹ * x ∈ D)}
      mul_mem' := by
        rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨(H z).mul_mem hxH hyH, ?_⟩
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (D.mul_mem hx hy)
        · right
          have e1 : r⁻¹ * (x * y) = (r⁻¹ * x * r) * (r⁻¹ * y) := by group
          rw [e1]
          exact D.mul_mem (hconj' x hx) hy
        · right
          have e1 : r⁻¹ * (x * y) = (r⁻¹ * x) * y := by group
          rw [e1]
          exact D.mul_mem hx hy
        · left
          have e1 : x * y = r ^ 2 * (r⁻¹ * (r⁻¹ * x) * r) * (r⁻¹ * y) := by group
          rw [e1]
          exact D.mul_mem (D.mul_mem hr2 (hconj' _ hx)) hy
      one_mem' := ⟨(H z).one_mem, Or.inl D.one_mem⟩
      inv_mem' := by
        rintro x ⟨hxH, hx⟩
        refine ⟨(H z).inv_mem hxH, ?_⟩
        rcases hx with hx | hx
        · exact Or.inl (D.inv_mem hx)
        · right
          have e1 : r⁻¹ * x⁻¹ = (r⁻¹ * (r⁻¹ * x)⁻¹ * r) * (r ^ 2)⁻¹ := by group
          rw [e1]
          exact D.mul_mem (hconj' _ (D.inv_mem hx)) (D.inv_mem hr2) }
  have hH₁mem : ∀ x : G, x ∈ H₁ ↔ x ∈ H z ∧ (x ∈ D ∨ r⁻¹ * x ∈ D) := fun x => Iff.rfl
  have hDH₁ : D ≤ H₁ := fun x hx => (hH₁mem x).mpr ⟨hDH hx, Or.inl hx⟩
  have hbH₁ : b ∉ H₁ := by
    intro hb
    rcases ((hH₁mem b).mp hb).2 with h1 | h1
    · exact hbD h1
    · apply hrX
      have h2 : r⁻¹ ∈ XsubHat S a := by
        have := (XsubHat S a).mul_mem (hDX h1) ((XsubHat S a).inv_mem (Q_le_XsubHat S a hbQ))
        simpa using this
      simpa using (XsubHat S a).inv_mem h2
  have hcover : ∀ x ∈ H z, x ∈ XsubHat S a ∨ r⁻¹ * x ∈ XsubHat S a := by
    intro x hx
    have hidx2 := index_Xsub_eq_two S a e ι
    by_cases hxX : (QuotientGroup.mk (⟨x, hx⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a
    · exact Or.inl ((mem_XsubHat_iff S a).mpr ⟨hx, hxX⟩)
    · right
      have hmem : (QuotientGroup.mk (⟨r, hrH⟩ : ↥(H z)) : Hbar z)⁻¹ *
          (QuotientGroup.mk (⟨x, hx⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx2]
        exact iff_of_false (fun hm => hrXb (inv_mem_iff.mp hm)) hxX
      refine (mem_XsubHat_iff S a).mpr ⟨(H z).mul_mem ((H z).inv_mem hrH) hx, ?_⟩
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hmem
      exact hmem
  have hcov : ∀ x ∈ H z, x ∈ H₁ ∨ b⁻¹ * x ∈ H₁ := by
    intro x hx
    rcases hcover x hx with h1 | h1
    · rcases mem_commutator_or_of_mem_XsubHat S a hperf hZ hbZ hbz hFsup h1 with h2 | h2
      · exact Or.inl ((hH₁mem x).mpr ⟨hx, Or.inl h2⟩)
      · exact Or.inr ((hH₁mem _).mpr ⟨(H z).mul_mem ((H z).inv_mem hbH) hx, Or.inl h2⟩)
    · rcases mem_commutator_or_of_mem_XsubHat S a hperf hZ hbZ hbz hFsup h1 with h2 | h2
      · exact Or.inl ((hH₁mem x).mpr ⟨hx, Or.inr h2⟩)
      · right
        have hc := inv_mul_conj_mem_zpowers_of_card_ZQ_eq_four S hZ hbZ hbz ((H z).inv_mem hrH)
        refine (hH₁mem _).mpr ⟨(H z).mul_mem ((H z).inv_mem hbH) hx, Or.inr ?_⟩
        have e1 : r⁻¹ * (b⁻¹ * x) =
            (b⁻¹ * (r⁻¹ * b * r⁻¹⁻¹))⁻¹ * (b⁻¹ * (r⁻¹ * x)) := by group
        rw [e1]
        exact D.mul_mem (D.inv_mem (hzD hc)) h2
  have hidx : (H₁.subgroupOf (H z)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨b, hbH⟩, fun x => ?_⟩
    by_cases hx1 : (x : G) ∈ H₁
    · right
      refine ⟨Subgroup.mem_subgroupOf.mpr hx1, fun hxb => ?_⟩
      apply hbH₁
      have h1 : ((x * ⟨b, hbH⟩ : ↥(H z)) : G) ∈ H₁ := Subgroup.mem_subgroupOf.mp hxb
      have h2 : (x : G)⁻¹ * ((x : G) * b) ∈ H₁ := H₁.mul_mem (H₁.inv_mem hx1) h1
      simpa using h2
    · left
      refine ⟨?_, fun hx' => hx1 (Subgroup.mem_subgroupOf.mp hx')⟩
      rcases hcov (x : G)⁻¹ ((H z).inv_mem x.2) with h1 | h1
      · exact absurd (by simpa using H₁.inv_mem h1) hx1
      · have h2 := H₁.inv_mem h1
        refine Subgroup.mem_subgroupOf.mpr ?_
        simpa using h2
  exact ⟨H₁, fun x hx => ((hH₁mem x).mp hx).1, hidx, hbH₁, hDH₁⟩

end CFSG.RankThree.GF2n.Stroth78
