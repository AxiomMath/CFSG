module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem not_dvd_card_theta (hp : p.Prime) : ¬ p ∣ Nat.card (aschbacherSolvableCore p H) :=
  (solvable_prime_complement_core_characterization hp).2.2.1

theorem pGroup_inf_theta (hp : p.Prime) {P : Subgroup H} (hP : IsPGroup p P) :
    P ⊓ aschbacherSolvableCore p H = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  exact (Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_theta hp)))).eq_bot

theorem card_comap_mk (K : Subgroup (H ⧸ aschbacherSolvableCore p H)) :
    Nat.card (K.comap (QuotientGroup.mk' (aschbacherSolvableCore p H))) =
      Nat.card K * Nat.card (aschbacherSolvableCore p H) := by
  set θ := aschbacherSolvableCore p H
  have h1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' θ))
  have h2 : (K.comap (QuotientGroup.mk' θ)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective θ)
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [h2] at h1
  have h5 : Nat.card (K.comap (QuotientGroup.mk' θ)) * K.index =
      (Nat.card K * Nat.card θ) * K.index := by
    rw [h1, h4, ← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem isPGroup_center_quotient (hp : p.Prime) :
    IsPGroup p (Subgroup.center (H ⧸ aschbacherSolvableCore p H)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsolv, -, hcop, hmax, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  intro z
  set θ := aschbacherSolvableCore p H with hθ
  have hz : ((z : Subgroup.center (H ⧸ θ)) : H ⧸ θ) ∈ Subgroup.center (H ⧸ θ) := z.2
  obtain ⟨n, hn⟩ : ∃ n, n = orderOf ((z : H ⧸ θ)) := ⟨_, rfl⟩
  have hn0 : 0 < n := hn ▸ orderOf_pos _
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' p hp.ne_one
  refine ⟨e, ?_⟩
  set w : H ⧸ θ := ((z : H ⧸ θ)) ^ (p ^ e) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero)
      (by rw [← hn, hnm]; exact dvd_mul_right _ _),
      ← hn, hnm]
    exact Nat.mul_div_cancel_left _ (pow_pos hp.pos _)
  have hwc : w ∈ Subgroup.center (H ⧸ θ) := Subgroup.pow_mem _ hz _
  set W : Subgroup (H ⧸ θ) := Subgroup.zpowers w with hW
  have hWc : W ≤ Subgroup.center (H ⧸ θ) := (Subgroup.zpowers_le.2 hwc)
  have hWn : W.Normal := ⟨fun x hx g => by
    rw [(Subgroup.mem_center_iff.1 (hWc hx)) g]; simpa using hx⟩
  set Hw : Subgroup H := W.comap (QuotientGroup.mk' θ) with hHw
  have hHwn : Hw.Normal := Subgroup.normal_comap _
  have hker : (QuotientGroup.mk' θ).ker = θ := QuotientGroup.ker_mk' θ
  have hcardHw : Nat.card Hw = Nat.card W * Nat.card θ := card_comap_mk W
  have hWcard : Nat.card W = m := by rw [hW, Nat.card_zpowers, hwo]
  have hθHw : θ ≤ Hw := fun x hx => by
    show (QuotientGroup.mk' θ) x ∈ W
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact W.one_mem
  have hHwsolv : Group.IsSolvable Hw := by
    have : Group.IsSolvable θ := hsolv
    have hWsolv : Group.IsSolvable W := inferInstance
    let f : ↥θ →* ↥Hw := Subgroup.inclusion hθHw
    let g : ↥Hw →* ↥W := ((QuotientGroup.mk' θ).comp Hw.subtype).codRestrict W (fun h => h.2)
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro h hh
    have h1 : (QuotientGroup.mk' θ) (h : H) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hh)
    have h2 : (h : H) ∈ θ := (QuotientGroup.eq_one_iff _).1 h1
    exact ⟨⟨h, h2⟩, rfl⟩
  have hHwcop : ¬ p ∣ Nat.card Hw := by
    rw [hcardHw, hWcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
    · exact hm h1
    · exact hcop h1
  have hle := hmax Hw hHwn hHwsolv hHwcop
  have hw1 : w = 1 := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective w
    have hhH : h ∈ Hw := by
      show (QuotientGroup.mk' θ) h ∈ W
      rw [QuotientGroup.mk'_apply, hh]
      exact Subgroup.mem_zpowers w
    have := (QuotientGroup.eq_one_iff h).2 (hle hhH)
    rw [← hh]
    exact this
  exact Subtype.ext hw1

theorem exists_commute_lift (hp : p.Prime) {c n : H} (hc : c ^ p = 1)
    (hq : (c : H ⧸ aschbacherSolvableCore p H) * (n : H ⧸ aschbacherSolvableCore p H) =
      (n : H ⧸ aschbacherSolvableCore p H) * (c : H ⧸ aschbacherSolvableCore p H)) :
    ∃ m : H, (m : H ⧸ aschbacherSolvableCore p H) = (n : H ⧸ aschbacherSolvableCore p H) ∧
      c * m = m * c := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p H with hθ
  let S : Type _ := {m : H // (m : H ⧸ θ) = (n : H ⧸ θ)}
  have hconj : ∀ m : S, ((c * m.1 * c⁻¹ : H) : H ⧸ θ) = (n : H ⧸ θ) := by
    intro m
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, m.2, hq]
    exact mul_inv_cancel_right _ _
  let f0 : S → S := fun m => ⟨c * m.1 * c⁻¹, hconj m⟩
  have hiter : ∀ k : ℕ, ∀ m : S, (f0^[k] m).1 = c ^ k * m.1 * (c ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [Function.iterate_succ_apply, ih]
      simp only [f0, pow_succ, mul_inv_rev, mul_assoc]
  let f : Function.End S := f0
  have hf : f ^ p ^ 1 = 1 := by
    funext m
    apply Subtype.ext
    show (f0^[p ^ 1] m).1 = m.1
    rw [hiter, pow_one, hc]
    simp
  let eS : S ≃ θ :=
    { toFun := fun m => ⟨n⁻¹ * m.1, by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, m.2]
        group⟩
      invFun := fun t => ⟨n * t.1, by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (t : H)).2 t.2, mul_one]⟩
      left_inv := fun m => Subtype.ext (by simp)
      right_inv := fun t => Subtype.ext (by simp) }
  have : Fintype S := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := S) (p := p) (n := 1) hf
  have hcardS : Fintype.card S = Nat.card θ := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr eS
  have hne : Nonempty (Function.fixedPoints f) := by
    by_contra hcon
    have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => hcon ⟨x⟩⟩
    rw [h0, hcardS] at hmod
    exact not_dvd_card_theta hp ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨m, hm⟩⟩ := hne
  refine ⟨m.1, m.2, ?_⟩
  have h1 : (f m).1 = m.1 := congrArg Subtype.val hm
  have h2 : c * m.1 * c⁻¹ = m.1 := h1
  calc c * m.1 = (c * m.1 * c⁻¹) * c := by group
    _ = m.1 * c := by rw [h2]

theorem card_map_mk_of_isPGroup (hp : p.Prime) {A : Subgroup H} (hA : IsPGroup p A) :
    Nat.card (A.map (QuotientGroup.mk' (aschbacherSolvableCore p H))) = Nat.card A := by
  have hinj := injOn_mk_of_isPGroup hp hA
  have h1 : Nat.card (QuotientGroup.mk' (aschbacherSolvableCore p H) '' (A : Set H)) =
      Nat.card (A : Set H) := Nat.card_image_of_injOn hinj
  have e1 : Nat.card (A.map (QuotientGroup.mk' (aschbacherSolvableCore p H))) =
      Nat.card (QuotientGroup.mk' (aschbacherSolvableCore p H) '' (A : Set H)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e1, h1]
  rfl

theorem exists_pGroup_cover (hp : p.Prime) {P : Subgroup H} (hP : IsPGroup p P)
    {F : Subgroup (H ⧸ aschbacherSolvableCore p H)} (hF : IsPGroup p F)
    (hPF : P.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) ≤ F) :
    ∃ F₃ : Subgroup H, P ≤ F₃ ∧ IsPGroup p F₃ ∧
      F₃.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) = F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p H with hθ
  set π := QuotientGroup.mk' θ with hπ
  set F₁ : Subgroup H := F.comap π with hF₁
  have hPF₁ : P ≤ F₁ := fun x hx => hPF (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow (hP.comap_subtype (K := F₁))
  set F₃ : Subgroup H := (S : Subgroup F₁).map F₁.subtype with hF₃
  have hF₃F₁ : F₃ ≤ F₁ := Subgroup.map_subtype_le _
  have hPF₃ : P ≤ F₃ := fun x hx =>
    ⟨⟨x, hPF₁ hx⟩, hPS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hF₃p : IsPGroup p F₃ := S.2.map F₁.subtype
  refine ⟨F₃, hPF₃, hF₃p, ?_⟩
  have hle : F₃.map π ≤ F := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact hF₃F₁ hx
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hF
  have hcardF₁ : Nat.card F₁ = Nat.card F * Nat.card θ := card_comap_mk F
  have hfac : (Nat.card F₁).factorization p = j := by
    rw [hcardF₁, hj, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_theta hp)]
    simp [hp.factorization_pow]
  have hSc : Nat.card S = p ^ j := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hF₃c : Nat.card F₃ = p ^ j := by
    rw [hF₃, Subgroup.card_map_of_injective F₁.subtype_injective]
    exact hSc
  have hmapc : Nat.card (F₃.map π) = Nat.card F₃ := card_map_mk_of_isPGroup hp hF₃p
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmapc, hF₃c, hj])

theorem exists_normalizer_lift (hp : p.Prime) {A : Subgroup H} (hA : IsPGroup p A) {n : H}
    (hy : (n : H ⧸ aschbacherSolvableCore p H) ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) :
        Subgroup (H ⧸ aschbacherSolvableCore p H)) : Set (H ⧸ aschbacherSolvableCore p H))) :
    ∃ w ∈ Subgroup.normalizer (A : Set H),
      ∃ e ∈ A.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
        (n : H ⧸ aschbacherSolvableCore p H) = e * (w : H ⧸ aschbacherSolvableCore p H) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p H with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ē : Subgroup (H ⧸ θ) := A.map π with hĒ
  set Ph : Subgroup H := Ē.comap π with hPh
  have hAPh : A ≤ Ph := fun x hx => Subgroup.mem_map_of_mem _ hx
  set S₂ : Subgroup H := A.map (MulAut.conj n).toMonoidHom with hS₂
  have hnorm := Subgroup.mem_normalizer_iff.1 hy
  have hS₂Ph : S₂ ≤ Ph := by
    rintro _ ⟨z, hz, rfl⟩
    show π (n * z * n⁻¹) ∈ Ē
    rw [map_mul, map_mul, map_inv]
    exact (hnorm (π z)).1 (Subgroup.mem_map_of_mem _ hz)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcardPh : Nat.card Ph = p ^ k * Nat.card θ := by
    rw [hPh, card_comap_mk, hĒ, card_map_mk_of_isPGroup hp hA, hk]
  have hfac : (Nat.card Ph).factorization p = k := by
    rw [hcardPh, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_theta hp)]
    simp [hp.factorization_pow]
  have hcardS₂ : Nat.card S₂ = p ^ k := by
    rw [hS₂, Subgroup.card_map_of_injective (MulAut.conj n).injective, hk]
  have hA₁ : Nat.card (A.subgroupOf Ph) = p ^ (Nat.card ↥Ph).factorization p := by
    rw [hfac, ← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAPh).toEquiv
  have hA₂ : Nat.card (S₂.subgroupOf Ph) = p ^ (Nat.card ↥Ph).factorization p := by
    rw [hfac, ← hcardS₂]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₂Ph).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Ph) (Sylow.ofCard (S₂.subgroupOf Ph) hA₂)
    (Sylow.ofCard (A.subgroupOf Ph) hA₁)
  have hconj : ∀ z ∈ S₂, (g : H) * z * (g : H)⁻¹ ∈ A := by
    intro z hz
    have hz' : (⟨z, hS₂Ph hz⟩ : ↥Ph) ∈ S₂.subgroupOf Ph := Subgroup.mem_subgroupOf.2 hz
    have h3 : ((g • (Sylow.ofCard (S₂.subgroupOf Ph) hA₂) : Sylow p ↥Ph) : Subgroup ↥Ph) =
        A.subgroupOf Ph := by
      rw [hg]
      rfl
    have h2 : (g : ↥Ph) * ⟨z, hS₂Ph hz⟩ * g⁻¹ ∈ (A.subgroupOf Ph) := by
      rw [← h3, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (⟨z, hS₂Ph hz⟩ : ↥Ph) (MulAut.conj g) _ hz'
    exact Subgroup.mem_subgroupOf.1 h2
  set w₀ : H := (g : H) * n with hw₀
  have hmap : A.map (MulAut.conj w₀).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    have : w₀ * a * w₀⁻¹ = (g : H) * (n * a * n⁻¹) * (g : H)⁻¹ := by rw [hw₀]; group
    show w₀ * a * w₀⁻¹ ∈ A
    rw [this]
    exact hconj _ ⟨a, ha, rfl⟩
  have hw₀N : w₀ ∈ Subgroup.normalizer (A : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj w₀).injective])
  refine ⟨w₀, hw₀N, ((g : H) : H ⧸ θ)⁻¹, ?_, ?_⟩
  · exact Subgroup.inv_mem _ g.2
  · show (n : H ⧸ θ) = ((g : H) : H ⧸ θ)⁻¹ * ((g * n : H) : H ⧸ θ)
    rw [QuotientGroup.mk_mul]
    group

end CFSG.RankThree.PartOne.Q1327T
