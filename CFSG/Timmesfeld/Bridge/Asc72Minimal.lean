module

public import CFSG.Timmesfeld.Bridge.Asc72Local
public import CFSG.Timmesfeld.Bridge.Asc72Width

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] {D : Set G}

@[expose] def conjOrbit (M : Subgroup G) (u : G) : Set G := {x | ∃ m ∈ M, x = m * u * m⁻¹}

theorem self_mem_conjOrbit (M : Subgroup G) (u : G) : u ∈ conjOrbit M u :=
  ⟨1, M.one_mem, by group⟩

theorem conj_mem_closure {S : Set G} {g : G} (hg : ∀ x ∈ S, g * x * g⁻¹ ∈ S) {k : G}
    (hk : k ∈ Subgroup.closure S) : g * k * g⁻¹ ∈ Subgroup.closure S := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hg x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem commute_of_mem_closure {S T : Set G} (h : ∀ x ∈ S, ∀ y ∈ T, Commute x y) {a b : G}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure T) : Commute a b := by
  have hb' : b ∈ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr (fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (h x hx y hy).eq) hb
  have ha' : a ∈ Subgroup.centralizer {b} :=
    (Subgroup.closure_le _).mpr (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hb' x hx)) ha
  exact Subgroup.mem_centralizer_singleton_iff.mp ha'

theorem commutator_mem_closure_conjOrbit {M : Subgroup G} [M.Normal] (u : G) {m : G}
    (hm : m ∈ M) : m * u * m⁻¹ * u⁻¹ ∈ Subgroup.closure (conjOrbit M u) ⊓ M := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.subset_closure ⟨m, hm, rfl⟩)
    (Subgroup.inv_mem _ (Subgroup.subset_closure (self_mem_conjOrbit M u))), ?_⟩
  have h := M.mul_mem hm (‹M.Normal›.conj_mem m⁻¹ (M.inv_mem hm) u)
  simpa [mul_assoc] using h

theorem mem_centralizer_of_inf_eq_bot {M : Subgroup G} [M.Normal] {u : G}
    (h : Subgroup.closure (conjOrbit M u) ⊓ M = ⊥) : u ∈ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h1 := commutator_mem_closure_conjOrbit u hm
  rw [h, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem conj_mem_closure_conjOrbit_inf {M : Subgroup G} [M.Normal] {u m x : G} (hm : m ∈ M)
    (hx : x ∈ Subgroup.closure (conjOrbit M u) ⊓ M) :
    m * x * m⁻¹ ∈ Subgroup.closure (conjOrbit M u) ⊓ M := by
  refine ⟨conj_mem_closure ?_ hx.1, ‹M.Normal›.conj_mem x hx.2 m⟩
  rintro _ ⟨m', hm', rfl⟩
  exact ⟨m * m', M.mul_mem hm hm', by group⟩

theorem eq_bot_of_le_center (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {N : Subgroup G} [N.Normal] (h : N ≤ Subgroup.center G) : N = ⊥ :=
  hrad N inferInstance (Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (h b.2) a))

theorem Setup.le_center_of_mem_centralizer (hS : Setup G D) {N : Subgroup G} [N.Normal] {u : G}
    (hu : u ∈ D) (huN : u ∈ Subgroup.centralizer (N : Set G)) : N ≤ Subgroup.center G := by
  have htop : Subgroup.centralizer (N : Set G) = ⊤ := by
    rcases hS.subset_or_disjoint (Subgroup.centralizer (N : Set G)) with h | h
    · exact hS.eq_top_of_subset _ h
    · exact absurd huN (h u hu)
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (N : Set G) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg n hn).symm

theorem not_mem_centralizer_of_ne_bot (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : M ≠ ⊥) {u : G} (hu : u ∈ D) : u ∉ Subgroup.centralizer (M : Set G) := fun h =>
  hM (eq_bot_of_le_center hrad (hS.le_center_of_mem_centralizer hu h))

theorem commute_of_mem_conjOrbit (hS : Setup G D) {M : Subgroup G} [M.Normal] {u v : G}
    (hu : u ∈ D) (hv : v ∈ D) (huv : Commute u v) (hne : u⁻¹ * v ∉ M) {x y : G}
    (hx : x ∈ conjOrbit M u) (hy : y ∈ conjOrbit M v) : Commute x y := by
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨m', hm', rfl⟩ := hy
  by_contra hc
  obtain ⟨g, hg, hgxy⟩ := hS.oddT.exists_conj (hS.conj_mem m hu) (hS.conj_mem m' hv) hc
  set π := QuotientGroup.mk' M
  have hπm : π m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
  have hπm' : π m' = 1 := (QuotientGroup.eq_one_iff m').mpr hm'
  have hπx : π (m * u * m⁻¹) = π u := by
    rw [map_mul, map_mul, map_inv, hπm, one_mul, inv_one, mul_one]
  have hπy : π (m' * v * m'⁻¹) = π v := by
    rw [map_mul, map_mul, map_inv, hπm', one_mul, inv_one, mul_one]
  have hle : Subgroup.closure {m * u * m⁻¹, m' * v * m'⁻¹} ≤
      (Subgroup.centralizer {π u}).comap π := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · show π (m * u * m⁻¹) ∈ Subgroup.centralizer {π u}
      rw [hπx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · show π (m' * v * m'⁻¹) ∈ Subgroup.centralizer {π u}
      rw [hπy]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (huv.map π).eq.symm
  have hπg : π g * π u = π u * π g :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (hle hg))
  apply hne
  rw [← QuotientGroup.eq]
  show π u = π v
  rw [← hπy, ← hgxy, map_mul, map_mul, map_inv, hπx, hπg, mul_inv_cancel_right]

variable [Finite G]

theorem eq_bot_of_le_of_isSolvable
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    {N : Subgroup G} (hNM : N ≤ M) (hN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hNs : Group.IsSolvable N) : N = ⊥ := by
  obtain ⟨R, hRn, hRs, hR⟩ := exists_solvableRadical M
  have hconj : ∀ (g : G) (x : M), x ∈ R → MulAut.conjNormal g x ∈ R := by
    intro g x hx
    have h1 : (R.map (MulAut.conjNormal g).toMonoidHom).Normal :=
      hRn.map _ (MulAut.conjNormal g).surjective
    have h2 : Group.IsSolvable (R.map (MulAut.conjNormal g).toMonoidHom) :=
      Group.isSolvable_of_surjective ((MulAut.conjNormal g).toMonoidHom.subgroupMap_surjective R)
    exact hR _ h1 h2 (Subgroup.mem_map_of_mem _ hx)
  have hRG : (R.map M.subtype).Normal := ⟨fun y hy g => by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨MulAut.conjNormal g x, hconj g x hx, by simp⟩⟩
  have hRGs : Group.IsSolvable (R.map M.subtype) :=
    Group.isSolvable_of_surjective (M.subtype.subgroupMap_surjective R)
  have hbot := hrad _ hRG hRGs
  have hN' : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hNM).mpr fun n m hn hm => hN m hm n hn
  have hNs' : Group.IsSolvable (N.subgroupOf M) := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom) ?_
    exact (Subgroup.subgroupOfEquivOfLe hNM).injective
  have hle := hR _ hN' hNs'
  rw [eq_bot_iff]
  intro x hx
  have hxR : (⟨x, hNM hx⟩ : M) ∈ R := hle (show (⟨x, hNM hx⟩ : M) ∈ N.subgroupOf M from hx)
  have hx' : x ∈ R.map M.subtype := ⟨_, hxR, rfl⟩
  rwa [hbot] at hx'

theorem exists_commute_conj_of_normal (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : M ≠ ⊥) {u : G} (hu : u ∈ D) :
    ∃ m ∈ M, m * u * m⁻¹ ≠ u ∧ Commute u (m * u * m⁻¹) := by
  by_contra hcon
  push Not at hcon
  set S := conjOrbit M u
  set K := Subgroup.closure S
  have hSD : S ⊆ D := by
    rintro _ ⟨m, -, rfl⟩
    exact hS.conj_mem m hu
  have huK : u ∈ K := Subgroup.subset_closure (self_mem_conjOrbit M u)
  have hKle : K ≤ M ⊔ Subgroup.zpowers u := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hm)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))) (Subgroup.mem_sup_left (M.inv_mem hm))
  have hconjK : ∀ k ∈ K, k * u * k⁻¹ ∈ S := by
    intro k hk
    obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hKle hk)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨m, hm, by group⟩
  set d : K := ⟨u, huK⟩
  have hiso : ∀ g : K, Commute (g * d * g⁻¹) d → g * d * g⁻¹ = d := by
    intro g hg
    obtain ⟨m, hm, hmeq⟩ := hconjK g g.2
    have hg' : Commute u (m * u * m⁻¹) := by
      rw [← hmeq]
      exact (hg.map K.subtype).symm
    apply Subtype.ext
    show (g : G) * u * (g : G)⁻¹ = u
    rw [hmeq]
    by_contra hne
    exact hcon m hm hne hg'
  have hd1 : d ≠ 1 := fun h => hS.oddT.ne_one hu (congrArg Subtype.val h)
  have hd2 : d * d = 1 := Subtype.ext (hS.oddT.mul_self_eq_one hu)
  have hsol := isSolvable_closure_isConj_of_isolated hd1 hd2 hiso
  have htop : Subgroup.closure {x : K | IsConj d x} = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : Subgroup K) = Subgroup.closure (((↑) : K → G) ⁻¹' S) :=
          Subgroup.closure_closure_coe_preimage.symm
      _ ≤ Subgroup.closure {x : K | IsConj d x} := by
        apply Subgroup.closure_mono
        intro x hx
        have hxS : (x : G) ∈ S := hx
        obtain ⟨m, hm, hxm⟩ := id hxS
        by_cases hxu : (x : G) = u
        · rw [show x = d from Subtype.ext hxu]
          exact IsConj.refl d
        · have hnc : ¬ Commute u x := by
            rw [hxm] at hxu ⊢
            exact hcon m hm hxu
          obtain ⟨g, hg, hgx⟩ := hS.oddT.exists_conj hu (hSD hxS) hnc
          have hgK : g ∈ K := (Subgroup.closure_le K).mpr (by
            rintro _ (rfl | rfl)
            · exact huK
            · exact Subgroup.subset_closure hxS) hg
          exact isConj_iff.mpr ⟨⟨g, hgK⟩, Subtype.ext hgx⟩
  have hKsol : Group.IsSolvable K := by
    rw [htop] at hsol
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup K).subtype)
      (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hKM : K ⊓ M = ⊥ := by
    refine eq_bot_of_le_of_isSolvable hrad inf_le_right
      (fun m hm x hx => conj_mem_closure_conjOrbit_inf hm hx) ?_
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : K ⊓ M ≤ K))
  exact not_mem_centralizer_of_ne_bot hS hrad hM hu (mem_centralizer_of_inf_eq_bot hKM)

theorem centralizer_eq_bot_of_normal (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G} [M.Normal]
    (hM : M ≠ ⊥) : Subgroup.centralizer (M : Set G) = ⊥ := by
  obtain ⟨u, hu⟩ := hS.nonempty
  obtain ⟨m, hm, hne, hc⟩ := exists_commute_conj_of_normal hS hrad hM hu
  have hvD : m * u * m⁻¹ ∈ D := hS.conj_mem m hu
  have huvM : u * (m * u * m⁻¹) ∈ M := by
    have e : u * (m * u * m⁻¹) = u * m * u⁻¹ * m⁻¹ := by
      rw [hS.oddT.inv_eq hu]
      group
    rw [e]
    exact M.mul_mem (‹M.Normal›.conj_mem m hm u) (M.inv_mem hm)
  have hCn : (Subgroup.centralizer (M : Set G)).Normal := inferInstance
  set C := Subgroup.centralizer (M : Set G)
  have hcu : ∀ n ∈ C, Commute (n * u * n⁻¹) u := by
    intro n hn
    have h1 : n * (u * (m * u * m⁻¹)) * n⁻¹ = u * (m * u * m⁻¹) := by
      rw [← Subgroup.mem_centralizer_iff.mp hn _ huvM, mul_inv_cancel_right]
    have h2 := (Commute.conj_iff n).mpr ((Commute.refl u).mul_right hc)
    rw [h1] at h2
    exact ((hS.oddT.commute_mul_iff hu hvD (hS.conj_mem n hu) hne.symm hc).mp h2).1
  have hpair : ∀ x ∈ conjOrbit C u, ∀ y ∈ conjOrbit C u, Commute x y := by
    rintro _ ⟨n₁, hn₁, rfl⟩ _ ⟨n₂, hn₂, rfl⟩
    have h := (Commute.conj_iff n₂).mpr (hcu (n₂⁻¹ * n₁) (C.mul_mem (C.inv_mem hn₂) hn₁))
    have e : n₂ * (n₂⁻¹ * n₁ * u * (n₂⁻¹ * n₁)⁻¹) * n₂⁻¹ = n₁ * u * n₁⁻¹ := by group
    rwa [e] at h
  have hAC : Subgroup.closure (conjOrbit C u) ⊓ C = ⊥ := by
    refine eq_bot_of_le_of_isSolvable hrad inf_le_right
      (fun c hc x hx => conj_mem_closure_conjOrbit_inf hc hx) ?_
    exact Group.isSolvable_of_comm fun a b =>
      Subtype.ext (commute_of_mem_closure hpair a.2.1 b.2.1).eq
  exact eq_bot_of_le_center hrad
    (hS.le_center_of_mem_centralizer hu (mem_centralizer_of_inf_eq_bot hAC))

theorem centralizer_eq_bot_of_minimal (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G}
    (hM : IsMinimalNormal M) : Subgroup.centralizer (M : Set G) = ⊥ :=
  have := hM.1
  centralizer_eq_bot_of_normal hS hrad hM.2.1

theorem eq_of_minimal (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M N : Subgroup G}
    (hM : IsMinimalNormal M) (hN : IsMinimalNormal N) : N = M := by
  have := hM.1
  have := hN.1
  rcases hN.2.2 (N ⊓ M) inferInstance inf_le_left with h | h
  ·
    exfalso
    apply hN.2.1
    rw [eq_bot_iff, ← centralizer_eq_bot_of_minimal hS hrad hM]
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact (Subgroup.commute_of_normal_of_disjoint N M hN.1 hM.1 (disjoint_iff.mpr h) n m hn
      hm).eq.symm
  · exact (hM.2.2 N hN.1 (inf_eq_left.mp h)).resolve_left hN.2.1

theorem exists_minimalNormal (hS : Setup G D) : ∃ M : Subgroup G, IsMinimalNormal M := by
  obtain ⟨d, hd⟩ := hS.nonempty
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro h
    have hdtop := Subgroup.mem_top d
    rw [h, Subgroup.mem_bot] at hdtop
    exact hS.oddT.ne_one hd hdtop
  obtain ⟨M, -, hMmin⟩ := Finite.exists_le_minimal
    (p := fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) (a := ⊤) ⟨inferInstance, htop⟩
  refine ⟨M, hMmin.1.1, hMmin.1.2, fun N hN hNM => ?_⟩
  by_cases hNb : N = ⊥
  · exact Or.inl hNb
  · exact Or.inr (hMmin.eq_of_le ⟨hN, hNb⟩ hNM)

theorem le_closure_conjOrbit (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G}
    (hM : IsMinimalNormal M) (hMs : IsSimpleGroup M) {u : G} (hu : u ∈ D) :
    M ≤ Subgroup.closure (conjOrbit M u) := by
  have := hM.1
  rcases (Subgroup.isSimpleGroup_iff.mp hMs).2 (Subgroup.closure (conjOrbit M u) ⊓ M)
      inf_le_right ((Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun x m hx hm =>
        conj_mem_closure_conjOrbit_inf hm hx) with h | h
  · exfalso
    have h1 := mem_centralizer_of_inf_eq_bot h
    rw [centralizer_eq_bot_of_minimal hS hrad hM, Subgroup.mem_bot] at h1
    exact hS.oddT.ne_one hu h1
  · exact inf_eq_right.mp h

theorem simple_minimal_cases (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G}
    (hM : IsMinimalNormal M) (hMs : IsSimpleGroup M) :
    D ⊆ M ∨ ((∀ x ∈ D, x ∉ M) ∧ ∀ u ∈ D, ∀ v ∈ D, Commute u v → u⁻¹ * v ∈ M) := by
  have := hM.1
  refine (hS.subset_or_disjoint M).imp_right fun hdisj => ⟨hdisj, fun u hu v hv huv => ?_⟩
  by_contra hne
  have hMu := le_closure_conjOrbit hS hrad hM hMs hu
  have hMv := le_closure_conjOrbit hS hrad hM hMs hv
  apply hM.2.1
  refine hrad M hM.1 (Group.isSolvable_of_comm fun a b => Subtype.ext ?_)
  exact (commute_of_mem_closure (fun x hx y hy => commute_of_mem_conjOrbit hS hu hv huv hne hx hy)
    (hMu a.2) (hMv b.2)).eq

theorem widthOne_of_disjoint (hS : Setup G D) {M : Subgroup G} [M.Normal]
    (hdisj : ∀ x ∈ D, x ∉ M) (hcong : ∀ u ∈ D, ∀ v ∈ D, Commute u v → u⁻¹ * v ∈ M) :
    WidthOne (QuotientGroup.mk' M '' D) := by
  have h1 : ∀ d ∈ D, QuotientGroup.mk' M d ≠ 1 := fun d hd h =>
    hdisj d hd ((QuotientGroup.eq_one_iff d).mp h)
  have hSQ := hS.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M) h1
  refine widthOne_of_forall_not_commute hSQ.oddT hSQ.normal hSQ.nonempty ?_
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hc
  rcases hS.oddT.commute_or_odd hu hv with huv | hodd
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hcong u hu v hv huv
  ·
    have hx := hSQ.oddT.mul_self_eq_one ⟨u, hu, rfl⟩
    have hy := hSQ.oddT.mul_self_eq_one ⟨v, hv, rfl⟩
    have hsq : (QuotientGroup.mk' M u * QuotientGroup.mk' M v) ^ 2 = 1 := by
      rw [hc.mul_pow, pow_two, pow_two, hx, hy, one_mul]
    have hodd' : Odd (orderOf (QuotientGroup.mk' M u * QuotientGroup.mk' M v)) := by
      rw [← map_mul]
      exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
    have hord : orderOf (QuotientGroup.mk' M u * QuotientGroup.mk' M v) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact hSQ.oddT.eq_of_mul_eq_one ⟨u, hu, rfl⟩ (orderOf_eq_one_iff.mp hord)

theorem isOddTranspClass_conjSet (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G}
    (hM : IsMinimalNormal M) (hMs : IsSimpleGroup M) {u : G} (hu : u ∈ D) :
    IsOddTranspClass (conjSet M u) := by
  have := hM.1
  have huL : u ∈ M ⊔ Subgroup.zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hmemL : ∀ m ∈ M, m * u * m⁻¹ ∈ M ⊔ Subgroup.zpowers u := fun m hm =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) huL)
      (Subgroup.mem_sup_left (M.inv_mem hm))
  refine ⟨⟨⟨u, huL⟩, ?_⟩, ?_, ?_⟩
  ·
    ext k
    constructor
    · rintro ⟨m, hm, hk⟩
      exact isConj_iff.mpr ⟨⟨m, Subgroup.mem_sup_left hm⟩, Subtype.ext hk.symm⟩
    · intro hk
      obtain ⟨c, rfl⟩ := isConj_iff.mp hk
      obtain ⟨m, hm, z, hz, hc⟩ := Subgroup.mem_sup_of_normal_left.mp c.2
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine ⟨m, hm, ?_⟩
      show (c : G) * u * (c : G)⁻¹ = m * u * m⁻¹
      rw [← hc]
      group
  · refine (hS.oddT.preimage _).mono ?_
    rintro k ⟨m, hm, hk⟩
    show (k : G) ∈ D
    rw [hk]
    exact hS.conj_mem m hu
  ·
    rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective
      (Subgroup.subtype_injective (M ⊔ Subgroup.zpowers u)), MonoidHom.map_closure,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have himage : (M ⊔ Subgroup.zpowers u).subtype '' conjSet M u = conjOrbit M u := by
      ext x
      constructor
      · rintro ⟨k, ⟨m, hm, hk⟩, rfl⟩
        exact ⟨m, hm, hk⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨_, hmemL m hm⟩, ⟨m, hm, rfl⟩, rfl⟩
    rw [himage]
    exact sup_le (le_closure_conjOrbit hS hrad hM hMs hu)
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (self_mem_conjOrbit M u)))

end CFSG.Timmesfeld.Bridge.Asc72
