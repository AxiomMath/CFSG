module

public import CFSG.Timmesfeld.Bridge.RootStructWTIWeyl
public import CFSG.Timmesfeld.Bridge.RootStructWTIRank
public import CFSG.Timmesfeld.Bridge.RootStructR2Thin
public import CFSG.Timmesfeld.Bridge.RootStructWTIProps

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

private theorem map_conj_mul_eq (g k : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * k)).toMonoidHom =
      (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

section Line

variable {a d : G}

theorem mul_inv_mem_of_special (hD : IsRootInvolutionSet D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hQ : Moufang.CommLambda D) (ha : a ∈ D) (hd : d ∈ D)
    (had : Commute a d) (hadD : a * d ∈ D) {y y' : G} (hy : y ∈ D) (hdy : Commute d y)
    (hdyD : d * y ∈ D) (hay : orderOf (a * y) = 4) (hy' : y' ∈ rootSet D y) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : y' * t * y'⁻¹ * t⁻¹ ∈ rootGroup D d := by
  obtain ⟨α, hα, δ, hδ, rfl⟩ := exists_mul_eq_of_mem_line hd had ht
  have hz : (a * y) ^ 2 ∈ rootSet D d :=
    hQ d hd a ha y hy had.symm (by rw [← had.eq]; exact hadD) hdy hdyD hay
  have hδy : Commute δ y' :=
    commute_of_mem_rootGroup_of_commute hδ hy'.1 ((hy'.2 d hd).2 hdy.symm).symm
  have e : y' * (α * δ) * y'⁻¹ * (α * δ)⁻¹ = y' * α * y'⁻¹ * α⁻¹ := by
    calc y' * (α * δ) * y'⁻¹ * (α * δ)⁻¹ = y' * α * (δ * y'⁻¹ * δ⁻¹) * α⁻¹ := by group
      _ = y' * α * y'⁻¹ * α⁻¹ := by rw [hδy.inv_right.eq, mul_inv_cancel_right]
  rw [e]
  rcases (mem_rootGroup_iff_of_rootClosure hD hc ha).1 hα with rfl | hαT
  · rw [mul_one, mul_inv_cancel, inv_one, mul_one]
    exact (rootGroup D d).one_mem
  · have h4 : orderOf (α * y') = 4 := orderOf_mul_eq_four_of_mem_rootSet hD ha hy hαT hy' hay
    have hw : (α * y') ^ 2 ∈ rootSet D d := by
      have := hs.mul_sq_mem_rootSet hD ha hy hay hαT hy'
      rwa [rootSet_eq_of_mem hz] at this
    have hsq : y' * α * y'⁻¹ * α⁻¹ = (y' * α) ^ 2 := by
      rw [hD.inv_eq hy'.1, hD.inv_eq hαT.1, sq]
      simp only [mul_assoc]
    rw [hsq, ← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hαT.1) (hD.mul_self_eq_one hy'.1) h4]
    exact rootSet_subset_rootGroup D d hw

theorem commute_of_mul_inv_mem (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    {p q u : G} (hp : p ∈ rootGroup D a ⊔ rootGroup D d) (hp1 : p ≠ 1)
    (hq : q ∈ rootGroup D a ⊔ rootGroup D d) (hq1 : q ≠ 1) (hqp : q ∉ rootSet D p)
    (hup : ∀ s ∈ rootGroup D p, Commute u s)
    (huT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, u * t * u⁻¹ * t⁻¹ ∈ rootGroup D p)
    (huq : ∀ s ∈ rootGroup D q, u * s * u⁻¹ ∈ rootGroup D q) {t : G}
    (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute u t := by
  have hD := h.root
  have hpD := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT hp hp1
  have hqD := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT hq hq1
  have hqL := rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT hq hq1
  have hinf : rootGroup D p ⊓ rootGroup D q = ⊥ :=
    rootGroup_inf_eq_bot_of_rootClosure hD hc hpD hqD fun e =>
      hqp (by rw [e]; exact mem_rootSet_self hqD)
  rw [← sup_rootGroup_eq_of_mem h hc hs ha hd had hadD hdT hp hq hp1 hq1 hqp] at ht
  have hle : rootGroup D p ⊔ rootGroup D q ≤ Subgroup.centralizer {u} := by
    refine sup_le (fun s hs' => Subgroup.mem_centralizer_singleton_iff.2 (hup s hs').eq.symm)
      fun s hs' => ?_
    have h1 : u * s * u⁻¹ * s⁻¹ ∈ rootGroup D p ⊓ rootGroup D q :=
      ⟨huT s (hqL hs'), Subgroup.mul_mem _ (huq s hs') (Subgroup.inv_mem _ hs')⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact Subgroup.mem_centralizer_singleton_iff.2 h1.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ht)).symm

theorem exists_mem_rootSet_conj_eq_mul (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hQ : Moufang.CommLambda D) (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    {b : G} (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D) (hdb : orderOf (d * b) = 4)
    {a₁ : G} (ha₁ : a₁ ∈ rootSet D a) : ∃ b₁ ∈ rootSet D b, b₁ * d * b₁⁻¹ = d * a₁ := by
  have hD := h.root
  have hz : (d * b) ^ 2 ∈ rootSet D a := hQ a ha d hd b hb had hadD hab habD hdb
  obtain ⟨-, h2, -⟩ := special_pair_rootSet h hc hs hd hb hdb
  obtain ⟨b₁, hb₁, hsq⟩ := h2 d (mem_rootSet_self hd) a₁ (by rw [rootSet_eq_of_mem hz]; exact ha₁)
  refine ⟨b₁, hb₁, ?_⟩
  have h4 : orderOf (d * b₁) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd hb (mem_rootSet_self hd) hb₁ hdb
  obtain ⟨-, -, -, he⟩ := sq_mem_of_orderOf_eq_four hD hd hb₁.1 h4
  rw [hD.inv_eq hb₁.1, he, hsq]

theorem conj_transvection (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {T : Subgroup G}
    {e v g : G} (hgT : ∀ t ∈ T, g⁻¹ * t * g⁻¹⁻¹ ∈ T) (hve : ∀ s ∈ rootGroup D e, Commute v s)
    (hvT : ∀ t ∈ T, v * t * v⁻¹ * t⁻¹ ∈ rootGroup D e) :
    (∀ s ∈ rootGroup D (g * e * g⁻¹), Commute (g * v * g⁻¹) s) ∧
      ∀ t ∈ T, g * v * g⁻¹ * t * (g * v * g⁻¹)⁻¹ * t⁻¹ ∈ rootGroup D (g * e * g⁻¹) := by
  rw [rootGroup_conj hclass]
  refine ⟨?_, fun t ht => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Commute.conj_iff g).2 (hve s hs)
  · refine ⟨v * (g⁻¹ * t * g⁻¹⁻¹) * v⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)⁻¹, hvT _ (hgT t ht), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_mem_closure_conj_line_eq (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hQ : Moufang.CommLambda D) (hCE : LineCentralizerEq D) (ha : a ∈ D) (hd : d ∈ D)
    (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hTI : LineTI D a d)
    {y b c : G} (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D) (hay : orderOf (a * y) = 4)
    (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D) (hbL : b ∉ rootGroup D a ⊔ rootGroup D d)
    (hcD : c ∈ D) (hac : Commute a c) (hacD : a * c ∈ D)
    (hcL : c ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ b₁ ∈ rootSet D b, ∃ k ∈ Subgroup.closure {x | x ∈ D ∧ Commute (b₁ * d * b₁⁻¹) x},
      (∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute k t) ∧
        (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj k).toMonoidHom =
          rootGroup D a ⊔ rootGroup D c := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have hdb : orderOf (d * b) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line hD hCE ha hd had hadD hdT hTI hb hab hbL
  have hdc : orderOf (d * c) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line hD hCE ha hd had hadD hdT hTI hcD hac hcL
  obtain ⟨hyc, hoddc⟩ := opposite_of_not_mem_line hclass hD hc hs hQ hCE ha hd had hadD hdT hTI
    hy hdy hdyD hay hcD hac hacD hcL
  obtain ⟨c', hc', h3c⟩ := exists_orderOf_mul_eq_three_of_oneOpposite h hc hs hQ hcD hy hyc hoddc
    ⟨a, ha, hac.symm, by rw [← hac.eq]; exact hacD, by rw [orderOf_mul_comm_eq]; exact hay⟩
  obtain ⟨hμa, hμc⟩ := map_conj_weyl_eq hclass hD hc hs hQ ha hd had hadD hy hdy hdyD hay hcD hac
    hacD hdc (mem_rootSet_self hy) hc' h3c
  have hdc' : orderOf (d * c') = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd hcD (mem_rootSet_self hd) hc' hdc
  obtain ⟨-, -, -, hc'd⟩ := sq_mem_of_orderOf_eq_four hD hd hc'.1 hdc'
  have ha₁ : (d * c') ^ 2 ∈ rootSet D a := by
    have h1 := hs.mul_sq_mem_rootSet hD hd hcD hdc (mem_rootSet_self hd) hc'
    rwa [rootSet_eq_of_mem (hQ a ha d hd c hcD had hadD hac hacD hdc)] at h1
  obtain ⟨a₁, ha₁def⟩ : ∃ a₁ : G, a₁ = (d * c') ^ 2 := ⟨_, rfl⟩
  rw [← ha₁def] at ha₁ hc'd
  obtain ⟨b₁, hb₁, hb₁d⟩ := exists_mem_rootSet_conj_eq_mul h hc hs hQ ha hd had hadD hb hab habD
    hdb ha₁
  obtain ⟨hyb, hoddb⟩ := opposite_of_not_mem_line hclass hD hc hs hQ hCE ha hd had hadD hdT hTI
    hy hdy hdyD hay hb hab habD hbL
  have hM := moufangPair_of_oneOpposite h hc hs hQ hb hy (fun h' => hyb h'.symm)
    (by rwa [orderOf_mul_comm_eq]) ⟨a, ha, hab.symm, by rw [← hab.eq]; exact habD,
      by rw [orderOf_mul_comm_eq]; exact hay⟩
  obtain ⟨y₁, hy₁, h3b⟩ := hM.2 b₁ hb₁
  obtain ⟨hra, hrb⟩ := map_conj_weyl_eq hclass hD hc hs hQ ha hd had hadD hy hdy hdyD hay hb hab
    habD hdb hy₁ hb₁ h3b
  obtain ⟨μ, hμ⟩ : ∃ μ : G, μ = c' * y * c' := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : G, r = b₁ * y₁ * b₁ := ⟨_, rfl⟩
  rw [← hμ] at hμa hμc
  rw [← hr] at hra hrb
  have hc'inv : c'⁻¹ = c' := hD.inv_eq hc'.1
  have hb₁inv : b₁⁻¹ = b₁ := hD.inv_eq hb₁.1
  have hμD : μ ∈ D := by
    have := conj_mem_of_isClass hclass c' hy
    rwa [hc'inv, ← hμ] at this
  have hrD : r ∈ D := by
    have := conj_mem_of_isClass hclass b₁ hy₁.1
    rwa [hb₁inv, ← hr] at this
  have hpD : d * a₁ ∈ D := by
    rw [← hc'd]
    have := conj_mem_of_isClass hclass c' hd
    rwa [hc'inv] at this
  have hpL : d * a₁ ∈ rootGroup D a ⊔ rootGroup D d :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_self hd)))
      (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a ha₁))
  have hpT : d * a₁ ∉ rootSet D a := by
    intro hp
    have h1 : d ∈ rootGroup D a := by
      have := Subgroup.mul_mem _ (rootSet_subset_rootGroup D a hp)
        (Subgroup.inv_mem _ (rootSet_subset_rootGroup D a ha₁))
      rwa [mul_inv_cancel_right] at this
    exact hdT (mem_rootSet_of_mem_rootGroup hclass ha hd h1)
  have hNc' : NormalizesLine D a d c' := by
    have := normalizesLine_of_special hD hs hQ hd ha had.symm hdaD hcD hac hacD hdc hc'
    intro u hu
    rw [sup_comm] at hu ⊢
    exact this u hu
  have hNb₁ : NormalizesLine D a d b₁ := by
    have := normalizesLine_of_special hD hs hQ hd ha had.symm hdaD hb hab habD hdb hb₁
    intro u hu
    rw [sup_comm] at hu ⊢
    exact this u hu
  obtain ⟨hμp, hμT⟩ := conj_transvection (T := rootGroup D a ⊔ rootGroup D d) (g := c') (e := d)
    (v := y) hclass (fun t ht => by rw [hc'inv]; exact hNc' t ht)
    (fun s hs' => (commute_of_mem_rootGroup_of_commute hs' hy hdy).symm)
    (fun t ht => mul_inv_mem_of_special hD hc hs hQ ha hd had hadD hy hdy hdyD hay
      (mem_rootSet_self hy) ht)
  obtain ⟨hrp, hrT⟩ := conj_transvection (T := rootGroup D a ⊔ rootGroup D d) (g := b₁) (e := d)
    (v := y₁) hclass (fun t ht => by rw [hb₁inv]; exact hNb₁ t ht)
    (fun s hs' => (commute_of_mem_rootGroup_of_commute hs' hy₁.1
      ((hy₁.2 d hd).2 hdy.symm).symm).symm)
    (fun t ht => mul_inv_mem_of_special hD hc hs hQ ha hd had hadD hy hdy hdyD hay hy₁ ht)
  rw [hc'inv, ← hμ, hc'd] at hμp hμT
  rw [hb₁d, hb₁inv, ← hr] at hrp hrT
  have hμ2 := hD.mul_self_eq_one hμD
  have hr2 := hD.mul_self_eq_one hrD
  have hua : (rootGroup D a).map (MulAut.conj (r * μ)).toMonoidHom = rootGroup D a := by
    rw [map_conj_mul_eq, hμa, map_conj_symm_of_mul_self_eq_one hr2 hra]
  have hu : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute (r * μ) t := by
    refine fun t ht => commute_of_mul_inv_mem h hc hs ha hd had hadD hdT hpL (hD.ne_one hpD)
      (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha))) (hD.ne_one ha)
      (fun h' => hpT (mem_rootSet_comm hpD h')) (fun s hs' => (hrp s hs').mul_left (hμp s hs'))
      (fun t ht => ?_) (fun s hs' => ?_) ht
    · have e : r * μ * t * (r * μ)⁻¹ * t⁻¹ =
          (r * (μ * t * μ⁻¹ * t⁻¹) * r⁻¹) * (r * t * r⁻¹ * t⁻¹) := by group
      rw [e, (hrp _ (hμT t ht)).eq, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ (hμT t ht) (hrT t ht)
    · rw [← hua]
      exact ⟨s, hs', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  refine ⟨b₁, hb₁, μ * r, ?_, fun t ht => ?_, ?_⟩
  · rw [hb₁d]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨hμD, (hμp _ (rootSet_subset_rootGroup D _
        (mem_rootSet_self hpD))).symm⟩)
      (Subgroup.subset_closure ⟨hrD, (hrp _ (rootSet_subset_rootGroup D _
        (mem_rootSet_self hpD))).symm⟩)
  · have := (hu t ht).inv_left
    rwa [mul_inv_rev, hD.inv_eq hμD, hD.inv_eq hrD] at this
  · rw [map_conj_mul_eq, Subgroup.map_sup, hra, hrb, Subgroup.map_sup,
      map_conj_symm_of_mul_self_eq_one hμ2 hμa, map_conj_symm_of_mul_self_eq_one hμ2 hμc]

theorem map_conj_eq_of_mul_self_eq_one {g : G} (hg : g * g = 1) {H : Subgroup G}
    (hgH : ∀ u ∈ H, g * u * g⁻¹ ∈ H) : H.map (MulAut.conj g).toMonoidHom = H := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  refine le_antisymm ?_ fun u hu => ⟨g * u * g⁻¹, hgH u hu, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hgH u hu
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hinv]
    calc g * (g * u * g) * g = g * g * u * (g * g) := by group
      _ = u := by rw [hg, one_mul, mul_one]

theorem exists_special_of_not_mem_line (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hCE : LineCentralizerEq D) (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (hTI : LineTI D a d) {b : G} (hb : b ∈ D) (hab : Commute a b)
    (habD : a * b ∈ D) (hbT : b ∉ rootSet D a) (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ y ∈ D, Commute d y ∧ d * y ∈ D ∧ orderOf (a * y) = 4 := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨g, hg⟩ := isConj_iff.1 (h.isConj ha hd)
  have hconjD : ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun x hx => conj_mem_of_isClass hclass g hx
  have hcomm : ∀ {x : G}, Commute a x → Commute d (g * x * g⁻¹) := fun hx => by
    rw [← hg]; exact (Commute.conj_iff g).2 hx
  have hmul : ∀ {x : G}, a * x ∈ D → d * (g * x * g⁻¹) ∈ D := fun {x} hx => by
    rw [← hg, show g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ by group]
    exact hconjD _ hx
  have hnT : ∀ {x : G}, x ∉ rootSet D a → g * x * g⁻¹ ∉ rootSet D d := fun {x} hx h' => by
    rw [← hg, rootSet_conj hclass] at h'
    obtain ⟨e, he, he'⟩ := h'
    have hex : e = x := by simpa using he'
    exact hx (hex ▸ he)
  have hspecial : ∀ {x : G}, x ∈ D → Commute d x → x ∉ rootGroup D a ⊔ rootGroup D d →
      orderOf (a * x) = 4 := fun hx hdx hxL => by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line' hD hCE ha hd had hadD hdT hTI hx hdx hxL
  by_cases hb₁ : g * b * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d
  · by_cases hd₁ : g * d * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d
    · exfalso
      have key : ∀ {x : G}, x ∈ D → Commute a x → x ∉ rootSet D a →
          g * x * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d →
          (rootGroup D a ⊔ rootGroup D x).map (MulAut.conj g).toMonoidHom =
            rootGroup D a ⊔ rootGroup D d := by
        intro x hx hax hxT hxL
        have hx' := hconjD x hx
        rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass, hg]
        refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right
          (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT hxL (hD.ne_one hx'))) ?_
        rw [card_sup_rootGroup h hc ha hd had hdT, card_sup_rootGroup h hc hd hx' (hcomm hax)
          (hnT hxT), card_rootGroup_eq hclass hD hc ha hd, card_rootGroup_eq hclass hD hc ha hx']
      have h1 := key hb hab hbT hb₁
      rw [← key hd had hdT hd₁] at h1
      have h3 := Subgroup.map_injective (MulAut.conj g).injective h1
      have hbL' : b ∈ rootGroup D a ⊔ rootGroup D b :=
        Subgroup.mem_sup_right (rootSet_subset_rootGroup D b (mem_rootSet_self hb))
      rw [h3] at hbL'
      exact hbL hbL'
    · exact ⟨_, hconjD d hd, hcomm had, hmul hadD, hspecial (hconjD d hd) (hcomm had) hd₁⟩
  · exact ⟨_, hconjD b hb, hcomm hab, hmul habD, hspecial (hconjD b hb) (hcomm hab) hb₁⟩

end Line

namespace LineSetting

variable {D : Set G} (hL : LineSetting G D)
include hL

theorem lineTI {b b' : G} (hb : b ∈ D) (hb' : b' ∈ D) (hbb' : Commute b b') (hbb'D : b * b' ∈ D)
    (hb'T : b' ∉ rootSet D b) : LineTI D b b' := by
  obtain ⟨a, ha, d, hd, had, hadD, hdT, hTI⟩ := hL.line
  exact lineTI_of_lineTI hL.hyp hL.closure hL.special hL.conn ha hd had hadD hdT hTI hb hb' hbb'
    hbb'D hb'T

theorem lineCentralizerEq : LineCentralizerEq D :=
  lineCentralizerEq_of_hyp hL.hyp hL.closure hL.special hL.conn

theorem commLambda : Moufang.CommLambda D := by
  intro y hy x₁ hx₁ x₂ hx₂ hyx₁ hyx₁D hyx₂ hyx₂D h4
  have hD := hL.hyp.root
  have hx₁y : x₁ * y ∈ D := by rw [← hyx₁.eq]; exact hyx₁D
  have hx₁₂ := not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hx₁)
    (hD.mul_self_eq_one hx₂) h4
  have hyT : y ∉ rootSet D x₁ := fun h' => hx₁₂ ((h'.2 x₂ hx₂).1 hyx₂)
  have hTI := hL.lineTI hx₁ hy hyx₁.symm hx₁y hyT
  have h1 := mem_rootSet_sq_of_lineTI hL.hyp hL.closure hL.special hx₁ hx₂ hy h4 hyx₁.symm hx₁y
    hyx₂.symm hTI
  exact mem_rootSet_comm (hD.sq_mem hx₁ hx₂ h4) h1

theorem mem_rootSet_or_collinear {x c : G} (hx : x ∈ D) (hcD : c ∈ D) (hcx : Commute c x) :
    c ∈ rootSet D x ∨ (Commute x c ∧ x * c ∈ D) := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  obtain ⟨a, ha, d, hd, had, hadD, hdT, hTI⟩ := hL.line
  obtain ⟨g, hg⟩ := isConj_iff.1 (hL.hyp.isConj ha hx)
  have hd' : g * d * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hd
  have hxd : Commute x (g * d * g⁻¹) := by rw [← hg]; exact (Commute.conj_iff g).2 had
  have hxdD : x * (g * d * g⁻¹) ∈ D := by
    rw [← hg, show g * a * g⁻¹ * (g * d * g⁻¹) = g * (a * d) * g⁻¹ by group]
    exact conj_mem_of_isClass hclass g hadD
  have hdT' : g * d * g⁻¹ ∉ rootSet D x := by
    rw [← hg, rootSet_conj hclass]
    rintro ⟨e, he, he'⟩
    have : e = d := by simpa using he'
    exact hdT (this ▸ he)
  have hTI' : LineTI D x (g * d * g⁻¹) := by
    have := lineTI_conj hclass hTI g
    rwa [hg] at this
  exact mem_rootSet_or_collinear_of_lineTI hL.hyp hL.closure hL.special hL.conn hx hd' hxd hxdD
    hdT' hTI' hcD hcx

theorem closure_commute_le_nCore {x : G} (hx : x ∈ D) :
    Subgroup.closure {c | c ∈ D ∧ Commute x c} ≤ nCore D x := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  have hD := hL.hyp.root
  rw [Subgroup.closure_le]
  rintro c ⟨hcD, hxc⟩
  rcases hL.mem_rootSet_or_collinear hx hcD hxc.symm with hcT | ⟨h1, h2⟩
  · exact mem_nCore_of_mem_twoCore hcD (rootSet_subset_twoCore_self hclass hD hL.closure hx c hcT).2
  · exact mem_nCore_of_collinear hclass hD hx hcD h1.symm (by rw [← h1.eq]; exact h2)

theorem sup_rootGroup_eq_of_mem_sup {a b c : G} (ha : a ∈ D) (hb : b ∈ D) (hcD : c ∈ D)
    (hab : Commute a b) (hbT : b ∉ rootSet D a) (hac : Commute a c) (hacD : a * c ∈ D)
    (hcT : c ∉ rootSet D a) (hbL : b ∈ rootGroup D a ⊔ rootGroup D c) :
    rootGroup D a ⊔ rootGroup D b = rootGroup D a ⊔ rootGroup D c := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left
    (rootGroup_le_sup_of_mem hL.hyp hL.closure hL.special ha hcD hac hacD hcT hbL (hD.ne_one hb)))
    ?_
  rw [card_sup_rootGroup hL.hyp hL.closure ha hcD hac hcT,
    card_sup_rootGroup hL.hyp hL.closure ha hb hab hbT,
    card_rootGroup_eq hclass hD hL.closure hb hcD]

theorem exists_mem_nCore_conj_line_eq {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {b c : G} (hb : b ∈ D) (hab : Commute a b)
    (habD : a * b ∈ D) (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) (hcD : c ∈ D)
    (hac : Commute a c) (hacD : a * c ∈ D) (hcL : c ∉ rootGroup D a ⊔ rootGroup D d) :
    ∃ k ∈ nCore D d ⊓ Subgroup.centralizer {a},
      (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj k).toMonoidHom =
        rootGroup D a ⊔ rootGroup D c := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hTI := hL.lineTI ha hd had hadD hdT
  have hCE := hL.lineCentralizerEq
  have hQ := hL.commLambda
  have hbT : b ∉ rootSet D a := fun h' =>
    hbL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hcT : c ∉ rootSet D a := fun h' =>
    hcL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  by_cases hbc : rootGroup D a ⊔ rootGroup D b = rootGroup D a ⊔ rootGroup D c
  · refine ⟨1, ⟨(nCore D d).one_mem, (Subgroup.centralizer _).one_mem⟩, ?_⟩
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hbc, h1, Subgroup.map_id]
  obtain ⟨y, hy, hdy, hdyD, hay⟩ := exists_special_of_not_mem_line hL.hyp hL.closure hL.special
    hCE ha hd had hadD hdT hTI hb hab habD hbT hbL
  obtain ⟨b₁, hb₁, k, hk, hkT, hkL⟩ := exists_mem_closure_conj_line_eq hL.hyp hL.closure
    hL.special hQ hCE ha hd had hadD hdT hTI hy hdy hdyD hay hb hab habD hbL hcD hac hacD hcL
  have hb₁2 := hD.mul_self_eq_one hb₁.1
  have hb₁inv : b₁⁻¹ = b₁ := hD.inv_eq hb₁.1
  have hab₁ : Commute a b₁ := ((hb₁.2 a ha).2 hab.symm).symm
  have hb₁b : (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj b₁).toMonoidHom =
      rootGroup D a ⊔ rootGroup D b :=
    map_conj_eq_of_mul_self_eq_one hb₁2 fun u hu => Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_right (rootSet_subset_rootGroup D b hb₁)) hu)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right (rootSet_subset_rootGroup D b hb₁)))
  have hbLc : b ∉ rootGroup D a ⊔ rootGroup D c := fun h' =>
    hbc (hL.sup_rootGroup_eq_of_mem_sup ha hb hcD hab hbT hac hacD hcT h')
  have hcb : orderOf (c * b) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line hD hCE ha hcD hac hacD hcT
      (hL.lineTI ha hcD hac hacD hcT) hb hab hbLc
  have hb₁c : (rootGroup D a ⊔ rootGroup D c).map (MulAut.conj b₁).toMonoidHom =
      rootGroup D a ⊔ rootGroup D c := by
    have hN := normalizesLine_of_special hD hL.special hQ hcD ha hac.symm
      (by rw [← hac.eq]; exact hacD) hb hab habD hcb hb₁
    refine map_conj_eq_of_mul_self_eq_one hb₁2 fun u hu => ?_
    rw [sup_comm] at hu ⊢
    exact hN u hu
  refine ⟨b₁⁻¹ * k * b₁, ⟨?_, ?_⟩, ?_⟩
  · have hk' := Subgroup.mem_map_of_mem (MulAut.conj b₁⁻¹).toMonoidHom hk
    rw [MonoidHom.map_closure] at hk'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk'
    refine hL.closure_commute_le_nCore hd (Subgroup.closure_mono ?_ hk')
    rintro _ ⟨x, ⟨hxD, hpx⟩, rfl⟩
    simp only [MulAut.conj_apply, inv_inv]
    refine ⟨?_, ?_⟩
    · have := conj_mem_of_isClass hclass b₁⁻¹ hxD
      rwa [inv_inv] at this
    · have := (Commute.conj_iff b₁⁻¹).2 hpx
      rwa [inv_inv, show b₁⁻¹ * (b₁ * d * b₁⁻¹) * b₁ = d by group] at this
  · have hka : Commute k a :=
      hkT a (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha)))
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((hab₁.symm.inv_left.mul_left hka).mul_left hab₁.symm).eq
  · rw [show b₁⁻¹ * k * b₁ = b₁⁻¹ * k * b₁ from rfl, map_conj_mul_eq, hb₁b, map_conj_mul_eq, hkL,
      hb₁inv, hb₁c]

end LineSetting

end CFSG.Timmesfeld.Bridge
