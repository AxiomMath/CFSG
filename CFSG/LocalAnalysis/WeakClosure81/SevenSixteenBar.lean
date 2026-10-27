module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenSetup
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem isTI_barSub_iSub (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} (hφ : IsBarMap (kSub V H E) (iSub V H E) φ) :
    IsTI (barSub (kSub V H E) φ V) := by
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let J : Subgroup G := iSub V H E
  have hJleK : J ≤ K := iSub_le_kSub V H E
  have hKleH : K ≤ H := kSub_le_of_forall_le h.omega_le
  let T : Subgroup Q := barSub K φ V
  have hT : T = barSub K φ V := rfl
  change IsTI T
  intro g
  obtain ⟨k, rfl⟩ := hφ.surjective g
  by_cases hbot : T ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (φ k) T = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hwV : (w : Q) ∈ T := (Subgroup.mem_inf.mp w.2).1
    have hwC : (w : Q) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup (φ k) T :=
      (Subgroup.mem_inf.mp w.2).2
    have hwne' : (w : Q) ≠ 1 := fun h => hwne (Subtype.ext h)
    have hwC' : (w : Q) ∈ conjSubgroup T (φ k)⁻¹ := by
      rw [← t75_conjSubgroup_eq]
      exact hwC
    have hwT : (φ k)⁻¹ * (w : Q) * (φ k) ∈ T := by
      simpa using mem_conjSubgroup_iff.mp hwC'
    obtain ⟨a, haV, haφ⟩ := mem_barSub.mp hwV
    obtain ⟨b, hbV, hbφ⟩ := mem_barSub.mp hwT
    have haJ : (a : G) ∉ J := by
      intro haJ'
      exact hwne' (by rw [← haφ]; exact (hφ.ker_iff a).mpr haJ')
    let a'K : ↥K := k * b * k⁻¹
    have ha' : (a'K : G) ∈ conjSubgroup V (k : G)⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hkey : (k : G)⁻¹ * (a'K : G) * ((k : G)⁻¹)⁻¹ = (b : G) := by
        change (k : G)⁻¹ * ((k : G) * (b : G) * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ = (b : G)
        group
      rw [hkey]
      exact hbV
    have hphi_a' : φ a'K = (w : Q) := by
      change φ (k * b * k⁻¹) = (w : Q)
      rw [map_mul, map_mul, map_inv, hbφ]
      group
    have haJ' : (a : G)⁻¹ * (a'K : G) ∈ J := by
      have h1 : φ (a⁻¹ * a'K) = 1 := by
        rw [map_mul, map_inv, haφ, hphi_a']
        group
      simpa using (hφ.ker_iff (a⁻¹ * a'K)).mp h1
    obtain ⟨y, hyJ, hyEq⟩ :=
      seven_three_four_ti h.elemAbelian h.ti h.abelian h.le h.normal h.mem h.omega_le
        h.pcore_le h.jnormal h.iSub_le (h := (k : G)⁻¹) (hKleH (K.inv_mem k.2))
        haV haJ ha' haJ'
    have hbar1 : barSub K φ (conjSubgroup V (k : G)⁻¹) = conjSubgroup T (φ k)⁻¹ := by
      have hh := barSub_conjSubgroup (K := K) φ V k⁻¹
      simpa [hT] using hh
    have hbar2 : barSub K φ (conjSubgroup V y) = T := by
      have hphi_y : φ (⟨y, hJleK hyJ⟩ : ↥K) = 1 := (hφ.ker_iff _).mpr hyJ
      have hh := barSub_conjSubgroup (K := K) φ V ⟨y, hJleK hyJ⟩
      simpa [hT, hphi_y, CFSG.Quasithin.conjSubgroup_one] using hh
    have hconj : conjSubgroup T (φ k)⁻¹ = T :=
      calc conjSubgroup T (φ k)⁻¹ = barSub K φ (conjSubgroup V (k : G)⁻¹) := hbar1.symm
        _ = barSub K φ (conjSubgroup V y) := by rw [hyEq]
        _ = T := hbar2
    have hconjT : CFSG.CGT.Timmesfeld75.conjSubgroup (φ k) T = T := by
      rw [t75_conjSubgroup_eq]
      exact hconj
    rw [hconjT]
    exact inf_eq_left.mpr le_rfl

theorem normalClosure_barSub_iSub_eq_top (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} (hφ : IsBarMap (kSub V H E) (iSub V H E) φ) :
    Subgroup.normalClosure (barSub (kSub V H E) φ V : Set Q) = ⊤ := by
  let K : Subgroup G := kSub V H E
  let T : Subgroup Q := barSub K φ V
  have hT : T = barSub K φ V := rfl
  let N : Subgroup Q := Subgroup.normalClosure (T : Set Q)
  have hN : N = Subgroup.normalClosure (T : Set Q) := rfl
  have hNnorm : N.Normal := by rw [hN]; exact Subgroup.normalClosure_normal
  have hNconj : ∀ g : Q, conjSubgroup N g = N := by
    intro g
    rw [conjSubgroup_eq_iff_mem_normalizer, Subgroup.normalizer_eq_top_iff.mpr hNnorm]
    exact Subgroup.mem_top g
  have hNle : T ≤ N := by rw [hN]; exact Subgroup.subset_normalClosure
  have hKle : K ≤ (N.comap φ).map K.subtype := by
    change kSub V H E ≤ (N.comap φ).map K.subtype
    refine iSup₂_le fun U hU => ?_
    obtain ⟨k, hk, hUk⟩ := h.transitive U hU
    have hbarU : barSub K φ U = conjSubgroup T (φ ⟨k, hk⟩) := by
      rw [hUk]
      simpa [hT] using barSub_conjSubgroup (K := K) φ V ⟨k, hk⟩
    have hleN : barSub K φ U ≤ N := by
      rw [hbarU]
      calc conjSubgroup T (φ ⟨k, hk⟩) ≤ conjSubgroup N (φ ⟨k, hk⟩) :=
            Subgroup.map_mono hNle
        _ = N := hNconj (φ ⟨k, hk⟩)
    intro u hu
    refine Subgroup.mem_map.mpr ⟨⟨u, le_kSub hU hu⟩, ?_, rfl⟩
    exact hleN (mem_barSub.mpr ⟨⟨u, le_kSub hU hu⟩, hu, rfl⟩)
  have hcomap : N.comap φ = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hxmap : (x : G) ∈ (N.comap φ).map K.subtype := hKle x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  have hmap := Subgroup.map_comap_eq_self_of_surjective hφ.surjective N
  rw [hcomap, Subgroup.map_top, MonoidHom.range_eq_top.mpr hφ.surjective] at hmap
  exact hmap.symm

theorem barSub_inf_center_eq_bot (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} (hφ : IsBarMap (kSub V H E) (iSub V H E) φ)
    [Nontrivial (Q ⧸ Subgroup.center Q)] :
    barSub (kSub V H E) φ V ⊓ Subgroup.center Q = ⊥ := by
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  by_contra hne
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzT : (z : Q) ∈ barSub (kSub V H E) φ V := (Subgroup.mem_inf.mp z.2).1
  have hzZ : (z : Q) ∈ Subgroup.center Q := (Subgroup.mem_inf.mp z.2).2
  have hz1 : (z : Q) ≠ 1 := fun h1 => hz (Subtype.ext h1)
  have hconj : ∀ g : Q, CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V) =
      barSub (kSub V H E) φ V := by
    intro g
    have hzC : (z : Q) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V) := by
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      have hc := Subgroup.mem_center_iff.mp hzZ g
      have e : g⁻¹ * (z : Q) * g = (z : Q) := by
        rw [mul_assoc, ← hc, inv_mul_cancel_left]
      rw [e]
      exact hzT
    have hne' : barSub (kSub V H E) φ V ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V) ≠ ⊥ := by
      intro hbot
      have hmem : (z : Q) ∈ barSub (kSub V H E) φ V ⊓
          CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V) :=
        Subgroup.mem_inf.mpr ⟨hzT, hzC⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hz1 hmem
    have hTT : barSub (kSub V H E) φ V ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V) =
        barSub (kSub V H E) φ V := (isTI_barSub_iSub h hφ g).resolve_left hne'
    have hle : barSub (kSub V H E) φ V ≤
        CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V) := inf_eq_left.mp hTT
    have hcard : Nat.card ↥(CFSG.CGT.Timmesfeld75.conjSubgroup g (barSub (kSub V H E) φ V)) ≤
        Nat.card ↥(barSub (kSub V H E) φ V) := by
      rw [t75_conjSubgroup_eq, card_conjSubgroup']
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hNormal : (barSub (kSub V H E) φ V).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [← hconj g]
    exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr (by
      rw [show g⁻¹ * (g * n * g⁻¹) * g = n by group]
      exact hn)
  have htop : barSub (kSub V H E) φ V = ⊤ := by
    have h1 := normalClosure_barSub_iSub_eq_top h hφ
    rwa [Subgroup.normalClosure_eq_self] at h1
  haveI hab : IsMulCommutative ↥(barSub (kSub V H E) φ V) :=
    (isElemAbelian_barSub h.elemAbelian φ).1
  have hcenter : Subgroup.center Q = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    have hx : x ∈ barSub (kSub V H E) φ V := by rw [htop]; exact Subgroup.mem_top x
    have hg : g ∈ barSub (kSub V H E) φ V := by rw [htop]; exact Subgroup.mem_top g
    exact setLike_mul_comm hg hx
  have : Subsingleton (Q ⧸ Subgroup.center Q) := by
    rw [hcenter]
    exact QuotientGroup.subsingleton_quotient_top
  exact false_of_nontrivial_of_subsingleton (Q ⧸ Subgroup.center Q)

theorem card_barSub_eq_two_pow (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} {n : ℕ} (hn : rk ↥(barSub (kSub V H E) φ V) = n) :
    Nat.card ↥(barSub (kSub V H E) φ V) = 2 ^ n := by
  have hab : IsElemAbelian 2 (barSub (kSub V H E) φ V) := isElemAbelian_barSub h.elemAbelian φ
  haveI : Finite ↥(barSub (kSub V H E) φ V) :=
    Finite.of_surjective
      (fun x : ↥(V.subgroupOf (kSub V H E)) =>
        (⟨φ x, Subgroup.mem_map_of_mem φ x.2⟩ : ↥(barSub (kSub V H E) φ V)))
      (by
        rintro ⟨_, ⟨y, hy, rfl⟩⟩
        exact ⟨⟨y, hy⟩, rfl⟩)
  rw [← hn]
  exact card_eq_two_pow_of_isPGroup (isPGroup_two_of_isElemAbelian hab)

theorem barSub_comp {K A : Subgroup G} {Q P : Type} [Group Q] [Group P] (φ : ↥K →* Q)
    (f : Q →* P) : barSub K (f.comp φ) A = (barSub K φ A).map f := by
  unfold barSub
  rw [Subgroup.map_map]

theorem card_barSub_comp_mk {K A : Subgroup G} {Q : Type} [Group Q] (φ : ↥K →* Q)
    (hA : barSub K φ A ⊓ Subgroup.center Q = ⊥) :
    Nat.card ↥(barSub K ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) A) =
      Nat.card ↥(barSub K φ A) := by
  let f : ↥(barSub K φ A) →* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.mk' (Subgroup.center Q)).domRestrict (barSub K φ A)
  have hker : f.ker = ⊥ := by
    have h1 : f.ker = (Subgroup.center Q).subgroupOf (barSub K φ A) := by
      simp only [f, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [h1, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    exact hA
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hrange : f.range = barSub K ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) A := by
    rw [barSub_comp]
    exact MonoidHom.domRestrict_range _ _
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CFSG.LocalAnalysis.WeakClosure81
