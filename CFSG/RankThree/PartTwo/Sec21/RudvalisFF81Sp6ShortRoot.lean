module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6ShortRootH6
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55Defs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6RefS

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

section Transport

variable {G X : Type} [Group G] [Group X]

theorem map_le_cenS {f : G →* X} {A B : Subgroup G} (h : A ≤ CenS B) :
    A.map f ≤ CenS (B.map f) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [CenS, Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h ha) b hb]

theorem map_mem_cenS {f : G →* X} {B : Subgroup G} {v : G} (h : v ∈ CenS B) :
    f v ∈ CenS (B.map f) := by
  rw [CenS, Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp h b hb]

theorem isElemAb_map {f : G →* X} (hf : Function.Injective f) {A : Subgroup G}
    (h : IsElemAb 2 3 A) : IsElemAb 2 3 (A.map f) := by
  refine ⟨{ is_comm := ⟨fun x y => ?_⟩, exponent_dvd_p := ?_ }, ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
    obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
    apply Subtype.ext
    show f a ^ 2 = 1
    have e := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.1.exponent_dvd_p ⟨a, ha⟩
    rw [← map_pow, show a ^ 2 = 1 from congrArg Subtype.val e, map_one]
  · rw [Subgroup.card_map_of_injective hf]
    exact h.2

theorem SRConcl.map {f : G →* X} (hf : Function.Injective f) {a₁ a₂ a₃ t : G}
    (h : SRConcl (⊤ : Subgroup G) a₁ a₂ a₃ t) :
    SRConcl ((⊤ : Subgroup G).map f) (f a₁) (f a₂) (f a₃) (f t) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : f a₁ * (f a₂ * f a₃) = f (a₁ * (a₂ * a₃)) := by simp only [map_mul]
  have e2 : f a₂ * f a₃ = f (a₂ * a₃) := (map_mul f a₂ a₃).symm
  have e3 : (f a₁)⁻¹ * (f a₂ * f a₃) = f (a₁⁻¹ * (a₂ * a₃)) := by simp only [map_mul, map_inv]
  have hLt : ∀ b : G,
      (⊤ : Subgroup G).map f ⊓ Cen (f t) ⊓ Cen (f b) = (⊤ ⊓ Cen t ⊓ Cen b).map f := by
    intro b
    rw [map_inf_cen hf, map_inf_cen hf]
  unfold SRConcl
  rw [e1, e3, e2]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv, h4, hv1, hvt⟩ := h1
    refine ⟨f v, ?_, by rw [← map_pow, h4, map_one],
      fun e => hv1 (hf (by rw [e, map_one])), fun e => hvt (hf e)⟩
    rw [hLt]
    exact Subgroup.mem_map_of_mem f hv
  · obtain ⟨v, hv, hsq, hcomm, hv1, hvt⟩ := h2
    refine ⟨f v, ?_, by rw [← map_mul, hsq, map_one], fun g hg => ?_,
      fun e => hv1 (hf (by rw [e, map_one])), fun e => hvt (hf e)⟩
    · rw [hLt]
      exact Subgroup.mem_map_of_mem f hv
    · rw [hLt] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have e := congrArg f (hcomm g' hg')
      simpa only [map_mul, map_inv] using e
  · intro R hRL h2R hN hR
    have hRrange : R ≤ f.range := by
      rw [MonoidHom.range_eq_map]
      exact hRL.trans inf_le_left
    obtain ⟨R', rfl⟩ : ∃ R' : Subgroup G, R = R'.map f :=
      ⟨R.comap f, (Subgroup.map_comap_eq_self hRrange).symm⟩
    have hR'C : R' ≤ ⊤ ⊓ Cen t := by
      intro x hx
      have hfx : f x ∈ Cen (f t) := (hRL (Subgroup.mem_map_of_mem f hx)).2
      rw [Subgroup.mem_centralizer_singleton_iff] at hfx
      exact ⟨Subgroup.mem_top x, Subgroup.mem_centralizer_singleton_iff.mpr
        (hf (by rw [map_mul, map_mul, hfx]))⟩
    have h2R' : IsPGroup 2 R' := by
      have := h2R.comap_of_injective f hf
      rwa [Subgroup.comap_map_eq_self_of_injective hf] at this
    have hN' : ⊤ ⊓ Cen t ≤ Nor R' := by
      intro c hc
      have hfc : f c ∈ (⊤ : Subgroup G).map f ⊓ Cen (f t) := by
        rw [← map_inf_cen hf]
        exact Subgroup.mem_map_of_mem f hc
      have hn := hN hfc
      rw [Nor, Subgroup.mem_normalizer_iff] at hn ⊢
      intro x
      have h1 := hn (f x)
      rw [Subgroup.mem_map_iff_mem hf, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hf] at h1
      exact h1
    have htR' : t ∈ R' := (Subgroup.mem_map_iff_mem hf).mp hR
    have m1 := map_inf_cen hf R' a₁
    have m2 := map_inf_cen hf R' (a₁ * (a₂ * a₃))
    have m3 := map_inf_cen hf R' (a₁⁻¹ * (a₂ * a₃))
    have mY : (R' ⊓ Cen (a₁ * (a₂ * a₃)) ⊔ R' ⊓ Cen (a₁⁻¹ * (a₂ * a₃))).map f =
        R'.map f ⊓ Cen (f (a₁ * (a₂ * a₃))) ⊔ R'.map f ⊓ Cen (f (a₁⁻¹ * (a₂ * a₃))) := by
      rw [Subgroup.map_sup, m2, m3]
    rcases h3 R' hR'C h2R' hN' htR' with hc | hc | hc | hc
    · obtain ⟨c1, c2, c3, c4⟩ := hc
      refine Or.inl ⟨?_, ?_, ?_, ?_⟩
      · rw [Subgroup.card_map_of_injective hf]; exact c1
      · rw [card_map_inf_cen hf]; exact c2
      · rw [card_map_inf_cen hf]; exact c3
      · rw [card_map_inf_cen hf]; exact c4
    · obtain ⟨c1, c2, c3, c4, c5⟩ := hc
      refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, fun v hv h4 => ?_⟩)
      · rw [Subgroup.card_map_of_injective hf]; exact c1
      · rw [card_map_inf_cen hf]; exact c2
      · rw [card_map_inf_cen hf]; exact c3
      · rw [card_map_inf_cen hf]; exact c4
      · rw [hLt] at hv
        obtain ⟨v', hv', rfl⟩ := hv
        exact map_mem_cenS (c5 v' hv' (hf (by rw [map_pow, h4, map_one])))
    · obtain ⟨c1, c2, c3, c4, c5⟩ := hc
      refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, fun v hv hsq hcomm => ?_⟩))
      · rw [Subgroup.card_map_of_injective hf]; exact c1
      · rw [card_map_inf_cen hf]; exact c2
      · rw [card_map_inf_cen hf]; exact c3
      · rw [card_map_inf_cen hf]; exact c4
      · rw [hLt] at hv
        obtain ⟨v', hv', rfl⟩ := hv
        refine map_mem_cenS (c5 v' hv' (hf (by rw [map_mul, hsq, map_one])) fun g hg => ?_)
        have e := hcomm (f g) (by rw [hLt]; exact Subgroup.mem_map_of_mem f hg)
        exact hf (by simpa only [map_mul, map_inv] using e)
    · obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hc
      rw [← mY, ← m1, ← m2, ← m3]
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, isElemAb_map hf c5, map_le_cenS c6,
        map_le_cenS c7, map_le_cenS c8, ?_, ?_, ?_, ?_, ?_⟩))
      · rw [Subgroup.card_map_of_injective hf]; exact c1
      · rw [Subgroup.card_map_of_injective hf]; exact c2
      · rw [Subgroup.card_map_of_injective hf]; exact c3
      · rw [card_map_inf_cen hf]; exact c4
      · rw [Subgroup.card_map_of_injective hf]; exact c9
      · rintro _ ⟨q, hq, rfl⟩ hcen
        refine (c10 q hq fun y hy => hf ?_).imp (fun e => by rw [e, map_one]) (fun e => by rw [e])
        rw [map_mul, map_mul]
        exact hcen (f y) (Subgroup.mem_map_of_mem f hy)
      · rintro _ ⟨q, hq, rfl⟩
        refine (c11 q hq).imp (fun e => ?_) (fun e => ?_)
        · rw [← map_mul, e, map_one]
        · rw [← map_mul, e]
      · rintro _ ⟨q, hq, rfl⟩ _ ⟨y, hy, rfl⟩
        refine (c12 q hq y hy).imp (fun e => ?_) (fun e => ?_)
        · have e' := congrArg f e
          simpa only [map_mul, map_inv, map_one] using e'
        · have e' := congrArg f e
          simpa only [map_mul, map_inv] using e'
      · obtain ⟨A, hAY, hA, htA⟩ := c13
        exact ⟨A.map f, Subgroup.map_mono hAY, isElemAb_map hf hA, Subgroup.mem_map_of_mem f htA⟩

end Transport

section Main


theorem exists_hom_sH {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 3 2 1) {b₁ b₂ b₃ : X}
    (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L) (hB : IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}))
    (hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X))
    {s : X} (hs : s ∈ L) (hs2 : orderOf s = 2) (hs1 : s * b₁ = b₁ * s)
    (hsu : s * (b₂ * b₃) = b₂ * b₃ * s) (hsw : s * (b₂ * b₃ ^ 2) * s⁻¹ = (b₂ * b₃ ^ 2)⁻¹) :
    ∃ f : H6 →* X, Function.Injective f ∧ (⊤ : Subgroup H6).map f = L ∧ f (zH 0) = b₁ ∧
      f (zH 1) = b₂ ∧ f (zH 2) = b₃ ∧ f sH = s := by
  obtain ⟨f, hf, hfL, e0, e1, e2⟩ := Sp6RefS.exists_hom_std hL hb₁ hb₂ hb₃ hB hmono
  subst e0 e1 e2
  rw [← hfL] at hs
  obtain ⟨s', -, rfl⟩ := hs
  have hord : orderOf s' = 2 := by rw [← orderOf_injective f hf s']; exact hs2
  have hss : s' * s' = 1 := by
    have h := pow_orderOf_eq_one s'
    rwa [hord, pow_two] at h
  have hne : s' ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    exact absurd hord (by norm_num)
  have h0 : s' * zH 0 = zH 0 * s' := hf (by rw [map_mul, map_mul]; exact hs1)
  have hu : s' * (zH 1 * zH 2) = zH 1 * zH 2 * s' := hf (by simp only [map_mul]; exact hsu)
  have hw : s' * (zH 1 * zH 2 ^ 2) * s'⁻¹ = (zH 1 * zH 2 ^ 2)⁻¹ :=
    hf (by simp only [map_mul, map_inv, map_pow]; exact hsw)
  obtain ⟨g, hg, rfl⟩ := s_cases h0 hu hss hne hw
  refine ⟨f.comp (MulAut.conj g).toMonoidHom, hf.comp (MulAut.conj g).injective, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective, hfL]
  all_goals first
    | rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg _,
        mul_inv_cancel_right]
    | rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem kf_sp6ShortRoot : KF_Sp6ShortRoot := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB _ hmono s hs hs2 hs1 hsu hsw
  obtain ⟨f, hf, hfL, e0, e1, e2, es⟩ := exists_hom_sH hL hb₁ hb₂ hb₃ hB hmono hs hs2 hs1 hsu hsw
  have key := SRConcl.map hf srConcl_H6
  rw [hfL, e0, e1, e2, es] at key
  exact key

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR
