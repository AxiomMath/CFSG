module

public import CFSG.Timmesfeld.Bridge.RootSetsConn7

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem false_of_triple (h3 : Step6ThreeProduct D x P) (hC : ConnCex D)
    (h : Step6 D a b c x z P) {a₁ a₂ y : G} (ha₁ : a₁ ∈ D) (ha₂ : a₂ ∈ D) (ha₁P : a₁ ∈ P)
    (ha₂P : a₂ ∈ P) (hne : a₁ ≠ a₂) (hq : a₁ * a₂ ∈ qcore D x P) (hy : y ∈ D)
    (hay : ¬ Reach D a₁ y) {n : ℕ} (hn : Odd n) (hord : orderOf (y * (a₁ * a₂)) = 2 * n)
    (hcP : (y * (a₁ * a₂)) ^ n * (a₁ * a₂) ∈ P) : False := by
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hc12 : Commute a₁ a₂ := h.commute_of_mem hC ha₁ ha₂ ha₁P ha₂P
  obtain ⟨hcD, -, hca₁, hca₂⟩ := hC.thirdKind_commute ha₁ ha₂ hne hc12 hy hay hn hord
  have hu2 := hC.mul_mul_self_of_commute ha₁ ha₂ hc12
  set u := a₁ * a₂ with hu
  set r := y * u with hr
  set t := r ^ n with ht
  set c' := t * u with hc'
  have hy2 := hD.mul_self_eq_one hy
  have hyr : y * r * y⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, hD.inv_eq hy, ← mul_assoc, hy2, one_mul]
  have hr2n : r ^ (2 * n) = 1 := by rw [← hord]; exact pow_orderOf_eq_one r
  have ht2 : t * t = 1 := by rw [ht, ← pow_add, ← two_mul, hr2n]
  have hyt : Commute y t := by
    have h1 : y * t * y⁻¹ = t := by
      rw [ht, ← conj_pow, hyr, inv_pow, inv_eq_of_mul_eq_one_right ht2]
    show y * t = t * y
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [h1]
  have htu : t = c' * u := by rw [hc', mul_assoc, hu2, mul_one]
  obtain ⟨v, hvD, hvP, w, hw, hdec⟩ := h3 a₁ ha₁ ha₁P c' hcD hcP a₂ ha₂ ha₂P hq
  have htv : t = v * w := by
    rw [htu, hu, ← hdec, ← mul_assoc, hca₁.eq]
  have htP : t ∈ P := by
    rw [htu, hu]
    exact P.mul_mem hcP (P.mul_mem ha₁P ha₂P)
  have hvt : Commute v t := by
    rw [htu, hu]
    exact (h.commute_of_mem hC hvD hcD hvP hcP).mul_right
      ((h.commute_of_mem hC hvD ha₁ hvP ha₁P).mul_right (h.commute_of_mem hC hvD ha₂ hvP ha₂P))
  have ha₁t : Commute a₁ t := by
    rw [htu, hu]
    exact hca₁.symm.mul_right ((Commute.refl a₁).mul_right hc12)
  have hva₁ : Reach D a₁ v := reach_trans (reach_symm (h.reach_of_mem hC ha₁ ha₁P))
    (h.reach_of_mem hC hvD hvP)
  have hvy : ¬ Reach D y v := fun hr' => hay (reach_trans hva₁ (reach_symm hr'))
  obtain ⟨-, hodd₁⟩ := opposite_of_not_reach hD ha₁ hy hay
  obtain ⟨-, hodd₂⟩ := opposite_of_not_reach hD hy hvD hvy
  obtain ⟨g₁, hg₁, hg₁e⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one ha₁) hy2 hodd₁
  obtain ⟨g₂, hg₂, hg₂e⟩ := exists_conj_of_odd_orderOf_mul hy2 (hD.mul_self_eq_one hvD) hodd₂
  have hcen : ∀ p q : G, Commute p t → Commute q t →
      ∀ k ∈ Subgroup.closure ({p, q} : Set G), Commute k t := by
    intro p q hp hq' k hk
    have hle : Subgroup.closure ({p, q} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      rintro s (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hp.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2 hq'.eq
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
  have hgt : Commute (g₂ * g₁) t :=
    (hcen y v hyt hvt g₂ hg₂).mul_left (hcen a₁ y ha₁t hyt g₁ hg₁)
  have hgv : g₂ * g₁ * a₁ * (g₂ * g₁)⁻¹ = v := by
    rw [show g₂ * g₁ * a₁ * (g₂ * g₁)⁻¹ = g₂ * (g₁ * a₁ * g₁⁻¹) * g₂⁻¹ by group, hg₁e, hg₂e]
  have hw_eq : w = (g₂ * g₁) * c' * (g₂ * g₁)⁻¹ * ((g₂ * g₁) * a₂ * (g₂ * g₁)⁻¹) := by
    have h1 : w = v * t := by rw [htv, ← mul_assoc, hD.mul_self_eq_one hvD, one_mul]
    have h2 : a₁ * t = c' * a₂ := by
      rw [htu, hu, ← mul_assoc, ← mul_assoc, ← hca₁.eq, mul_assoc c' a₁ a₁,
        hD.mul_self_eq_one ha₁, mul_one]
    rw [h1, ← hgv]
    calc g₂ * g₁ * a₁ * (g₂ * g₁)⁻¹ * t
        = g₂ * g₁ * a₁ * (g₂ * g₁)⁻¹ * ((g₂ * g₁) * t * (g₂ * g₁)⁻¹) := by
          rw [hgt.eq, mul_inv_cancel_right]
      _ = (g₂ * g₁) * (a₁ * t) * (g₂ * g₁)⁻¹ := by group
      _ = (g₂ * g₁) * (c' * a₂) * (g₂ * g₁)⁻¹ := by rw [h2]
      _ = _ := by group
  have hca : c' ≠ a₂ := by
    intro he
    have hta : t = a₁ := by
      rw [htu, hu, he, ← mul_assoc, ← hc12.eq, mul_assoc, hD.mul_self_eq_one ha₂, mul_one]
    exact hay (reach_of_commute ha₁ hy (hta ▸ hyt.symm))
  obtain ⟨ww, ⟨hwc, -⟩, hww⟩ := hw
  have hcen' : ∀ s ∈ lsub D x P, Commute s w := fun s hs => by
    rw [← hww]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hwc ⟨s, hs⟩)
  have hwa := hcen' a (mem_lsub_of_mem h.ha h.haP)
  have hwx := hcen' x mem_lsub_x
  rw [hw_eq] at hwa hwx
  exact h.false_of_commute_mul hC (hN _ c' hcD) (hN _ a₂ ha₂)
    (fun h' => hca (mul_left_cancel (mul_right_cancel h'))) ((Commute.conj_iff _).2 hca₂) hwa hwx

theorem le_lsub (h : Step6 D a b c x z P) : P ≤ lsub D x P := by
  intro p hp
  rw [h.hPL] at hp
  exact (Subgroup.closure_le _).2 (fun y hy => mem_lsub_of_mem hy.1 hy.2) hp

theorem isPGroup_sup_qcore (hC : ConnCex D) (h : Step6 D a b c x z P) :
    IsPGroup 2 (P ⊔ qcore D x P : Subgroup G) := by
  have := hC.setting.finite
  have hQ2 : IsPGroup 2 (qcore D x P) := (CFSG.pCore_isPGroup).map _
  refine h.hP2.to_sup_of_normal_right' hQ2 fun p hp => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro q
  have hpX : p ∈ lsub D x P := h.le_lsub hp
  constructor
  · rintro ⟨q', hq', rfl⟩
    exact ⟨⟨p, hpX⟩ * q' * ⟨p, hpX⟩⁻¹, CFSG.pCore_normal.conj_mem _ hq' _, rfl⟩
  · rintro ⟨q', hq', hq'e⟩
    refine ⟨⟨p, hpX⟩⁻¹ * q' * ⟨p, hpX⟩, ?_, ?_⟩
    · simpa using CFSG.pCore_normal.conj_mem _ hq' (⟨p, hpX⟩⁻¹)
    · have := congrArg (fun w => p⁻¹ * w * p) hq'e
      simpa [mul_assoc] using this

theorem exists_pair_mem_qcore (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∃ d ∈ D, d ∈ P ∧ d ≠ a ∧ a * d ∈ qcore D x P := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hex : ∃ q ∈ CFSG.pCore 2 (lsub D x P), ¬ Commute (q : G) a := by
    by_contra hall
    push Not at hall
    apply h.pCore_not_le_center hB hC
    intro q hq
    have hE : ∀ e ∈ lclass D x P, Commute q e := by
      intro e he
      have he' : (e : G) ∈ classIn (lsub D x P) a := by
        rw [classIn_eq_of_mem (h.mem_classIn hC h.ha h.haP)]
        exact he
      obtain ⟨g, hg, hge⟩ := he'
      have hq' := hall _ (CFSG.pCore_normal.conj_mem q hq (⟨g, hg⟩ : lsub D x P)⁻¹)
      have hc : Commute (q : G) (g * a * g⁻¹) := by
        have := (Commute.conj_iff g).2 hq'
        simpa [mul_assoc] using this
      exact Subtype.ext (hge ▸ hc).eq
    have hle : Subgroup.closure (lclass D x P) ≤ Subgroup.centralizer {q} := by
      rw [Subgroup.closure_le]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.2 (hE e he).eq.symm
    rw [(h.setup hC).gen] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  obtain ⟨q, hq, hqa⟩ := hex
  set d := (q : G) * a * (q : G)⁻¹ with hd
  have hdD : d ∈ D := hN _ a h.ha
  have hda : d ≠ a := by
    intro he
    apply hqa
    show (q : G) * a = a * q
    calc (q : G) * a = (q : G) * a * (q : G)⁻¹ * q := by group
      _ = a * q := by rw [← hd, he]
  have hadQ : a * d ∈ qcore D x P := by
    set â : lsub D x P := ⟨a, mem_lsub_of_mem h.ha h.haP⟩
    have hmem : â * q * â⁻¹ * q⁻¹ ∈ CFSG.pCore 2 (lsub D x P) :=
      (CFSG.pCore 2 _).mul_mem (CFSG.pCore_normal.conj_mem q hq â) ((CFSG.pCore 2 _).inv_mem hq)
    refine ⟨_, hmem, ?_⟩
    change a * (q : G) * a⁻¹ * (q : G)⁻¹ = a * ((q : G) * a * (q : G)⁻¹)
    rw [hD.inv_eq h.ha]
    group
  have hdX : d ∈ lsub D x P := (lsub D x P).mul_mem ((lsub D x P).mul_mem q.2
    (mem_lsub_of_mem h.ha h.haP)) ((lsub D x P).inv_mem q.2)
  have hdP : d ∈ P := by
    refine h.mem_of_isPGroup hC (h.isPGroup_sup_qcore hC) (fun l _ hlP => Subgroup.mem_sup_left hlP)
      hdD (Subgroup.mem_centralizer_singleton_iff.1 (h.lsub_le_centralizer hdX)) ?_
    have hqQ : (q : G) ∈ (P ⊔ qcore D x P : Subgroup G) :=
      Subgroup.mem_sup_right ⟨q, hq, rfl⟩
    exact (P ⊔ qcore D x P).mul_mem ((P ⊔ qcore D x P).mul_mem hqQ
      (Subgroup.mem_sup_left h.haP)) ((P ⊔ qcore D x P).inv_mem hqQ)
  exact ⟨d, hdD, hdP, hda, hadQ⟩

end Step6

end CFSG.Timmesfeld.Bridge
