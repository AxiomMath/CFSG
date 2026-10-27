module

public import CFSG.Timmesfeld.Bridge.RootStructR2Sub
public import CFSG.Timmesfeld.Bridge.RootStructWTIProps
public import CFSG.Timmesfeld.Bridge.RootStructThmE
public import CFSG.Timmesfeld.Bridge.RootStructWTIWeyl

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem exists_conj_eq_mul_of_sq_mem_rootSet (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) {a d t β γ : G} (hd : d ∈ D) (ht : t ∈ D) (h4 : orderOf (d * t) = 4)
    (hw : (d * t) ^ 2 ∈ rootSet D a) (hβ : β ∈ rootSet D a) (hγ : γ ∈ rootSet D d)
    (hβγ : Commute β γ) : ∃ τ ∈ rootSet D t, β * γ = τ * γ * τ⁻¹ := by
  have hD := h.root
  obtain ⟨-, h2, -⟩ := special_pair_rootSet h hc hs hd ht h4
  rw [rootSet_eq_of_mem hw] at h2
  obtain ⟨τ, hτ, hγτ⟩ := h2 γ hγ β hβ
  refine ⟨τ, hτ, ?_⟩
  rw [hβγ.eq, ← hγτ, hD.inv_eq hτ.1, sq]
  calc γ * (γ * τ * (γ * τ)) = (γ * γ) * τ * γ * τ := by simp only [mul_assoc]
    _ = τ * γ * τ := by rw [hD.mul_self_eq_one hγ.1, one_mul]

theorem conj_mem_of_map_eq {H K : Subgroup G} {k u : G}
    (hmap : H.map (MulAut.conj k).toMonoidHom = K) (hu : u ∈ H) : k * u * k⁻¹ ∈ K := by
  rw [← hmap]
  exact ⟨u, hu, by simp⟩

@[expose] def StabReach (D : Set G) (a x y : G) : Prop :=
  ∃ g : G, g * a * g⁻¹ ∈ rootSet D a ∧ g * y * g⁻¹ ∈ rootSet D x

theorem StabReach.of_mem {a x y : G} (ha : a ∈ D) (hy : y ∈ rootSet D x) : StabReach D a x y :=
  ⟨1, by simpa using mem_rootSet_self ha, by simpa using hy⟩

theorem StabReach.of_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a x y k : G}
    (hk : k * a * k⁻¹ ∈ rootSet D a) (h' : StabReach D a x (k * y * k⁻¹)) :
    StabReach D a x y := by
  obtain ⟨g, hga, hgy⟩ := h'
  refine ⟨g * k, ?_, ?_⟩
  · have : g * (k * a * k⁻¹) * g⁻¹ ∈ rootSet D (g * a * g⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨_, hk, rfl⟩
    rw [rootSet_eq_of_mem hga] at this
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using hgy

section Collinear

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem collinear_of_collinear_mem_rootSet {e e' y : G} (he : e ∈ D) (he' : e' ∈ rootSet D e)
    (hy : y ∈ D) (hye : Commute y e') (hyeD : y * e' ∈ D) (hyT : y ∉ rootSet D e) :
    Commute e y ∧ e * y ∈ D := by
  have := h.finite
  have hD := h.root
  have hyQ : y ∈ Moufang.twoCore e' := mem_twoCore_of_collinear h.isClass hD he'.1 hy hye hyeD
  have hyQ' : y ∈ Moufang.twoCore e :=
    mem_twoCore_of_mem_rootSet_self h.isClass hD (mem_rootSet_comm he he') hy hyQ
  rcases mem_rootSet_or_collinear_of_mem_twoCore h.isClass hD (oppositeDetermines_of_hyp h) hc
      hs (nCoreCommutatorInRoot_of_hyp h hc) he hy hyQ' with hT | hcol
  · exact absurd hT hyT
  · exact hcol

end Collinear

structure GateConfig (D : Set G) (a x c : G) : Prop where
  ha : a ∈ D
  hx : x ∈ D
  hc : c ∈ D
  hac : Commute a c
  hacD : a * c ∈ D
  hcT : c ∉ rootSet D a
  hax : ¬ Commute a x
  hoddax : Odd (orderOf (a * x))
  h4 : orderOf (x * c) = 4
  heD : (c * x) ^ 2 ∈ D
  hce : Commute c ((c * x) ^ 2)
  hceD : c * (c * x) ^ 2 ∈ D
  hxe : Commute x ((c * x) ^ 2)
  hxeD : x * (c * x) ^ 2 ∈ D
  heL : (c * x) ^ 2 ∉ rootGroup D a ⊔ rootGroup D c
  hcTe : c ∉ rootSet D ((c * x) ^ 2)
  h4ea : orderOf ((c * x) ^ 2 * a) = 4
  hsq : (a * (c * x) ^ 2) ^ 2 ∈ rootSet D c

theorem GateConfig.of (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) {a x c : G} (ha : a ∈ D)
    (hx : x ∈ D) (hcD : c ∈ D) (hac : Commute a c) (hacD : a * c ∈ D) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) (h4 : orderOf (x * c) = 4) : GateConfig D a x c := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hcT : c ∉ rootSet D a := fun hcT => by
    have h1 := (orderOf_mul_eq_four_iff_of_mem_rootSet hD ha hcT hx).1
      ((orderOf_mul_comm_eq x c).trans h4)
    rw [h1] at hoddax
    exact absurd hoddax (by decide)
  have h4' : orderOf (c * x) = 4 := by rwa [orderOf_mul_comm_eq]
  obtain ⟨heD, hce, hxe, -⟩ := sq_mem_of_orderOf_eq_four hD hcD hx h4'
  have hceD := mul_sq_mem_of_orderOf_eq_four hclass hD hcD hx h4'
  have hxeD : x * (c * x) ^ 2 ∈ D := by
    rw [← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hcD) h4]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD hx hcD h4
  have hL := hAll a ha c hcD hac hacD hcT
  have heL : (c * x) ^ 2 ∉ rootGroup D a ⊔ rootGroup D c := fun heL =>
    not_commute_of_mem_line_of_opposite h hc hs ha hcD hac hacD hcT hx hax hoddax heD heL hxe
  have hxc : ¬ Commute x c := not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hx)
    (hD.mul_self_eq_one hcD) h4
  have hcTe : c ∉ rootSet D ((c * x) ^ 2) := fun h' => hxc (((h'.2 x hx).2 hxe.symm).symm)
  have hCE := lineCentralizerEq_of_hyp h hc hs hconn
  have h4ea : orderOf ((c * x) ^ 2 * a) = 4 :=
    orderOf_mul_eq_four_of_not_mem_line' hD hCE ha hcD hac hacD hcT hL heD hce heL
  have h4ae : orderOf (a * (c * x) ^ 2) = 4 := by rwa [orderOf_mul_comm_eq]
  have hsq : (a * (c * x) ^ 2) ^ 2 ∈ rootSet D c :=
    mem_rootSet_comm (hD.sq_mem ha heD h4ae)
      (mem_rootSet_sq_of_lineTI h hc hs ha heD hcD h4ae hac hacD hce.symm hL)
  exact ⟨ha, hx, hcD, hac, hacD, hcT, hax, hoddax, h4, heD, hce, hceD, hxe, hxeD, heL, hcTe, h4ea,
    hsq⟩

theorem opposite_conj_of_mem_rootSet (hD : IsRootInvolutionSet D)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a y g : G} (ha : a ∈ D) (hy : y ∈ D)
    (hga : g * a * g⁻¹ ∈ rootSet D a) (hay : ¬ Commute a y) (hodd : Odd (orderOf (a * y))) :
    ¬ Commute a (g * y * g⁻¹) ∧ Odd (orderOf (a * (g * y * g⁻¹))) := by
  have h1 : ¬ Commute (g * a * g⁻¹) (g * y * g⁻¹) ∧
      Odd (orderOf (g * a * g⁻¹ * (g * y * g⁻¹))) :=
    ⟨fun hc => hay ((Commute.conj_iff g).1 hc), by
      rw [show g * a * g⁻¹ * (g * y * g⁻¹) = g * (a * y) * g⁻¹ by group, orderOf_conj_eq]
      exact hodd⟩
  exact opposite_of_mem_rootSet_of_opposite hD hga.1 (conj_mem_of_isClass hclass g hy)
    (mem_rootSet_comm ha hga) (mem_rootSet_self (conj_mem_of_isClass hclass g hy)) h1

section Reduction

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem GateConfig.stabReach_of_mem_line {a x c y : G} (hG : GateConfig D a x c) (hy : y ∈ D)
    (hyM : y ∈ rootGroup D ((c * x) ^ 2) ⊔ rootGroup D x) (hyT : y ∉ rootSet D ((c * x) ^ 2)) :
    StabReach D a x y := by
  have hD := h.root
  have hex : Commute ((c * x) ^ 2) x := hG.hxe.symm
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hG.hx hex hyM
  by_cases hγ1 : γ = 1
  · subst hγ1
    rw [mul_one] at hy hyT
    exact absurd (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.heD hβ (hD.ne_one hy)) hyT
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [one_mul] at hy ⊢
    exact StabReach.of_mem hG.ha (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.hx hγ hγ1)
  have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.heD hβ hβ1
  have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.hx hγ hγ1
  have hw : (x * c) ^ 2 ∈ rootSet D ((c * x) ^ 2) := by
    rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hG.hx) (hD.mul_self_eq_one hG.hc) hG.h4]
    exact mem_rootSet_self hG.heD
  obtain ⟨τ, hτ, hτeq⟩ := exists_conj_eq_mul_of_sq_mem_rootSet h hc hs hG.hx hG.hc hG.h4 hw hβT hγT
    (commute_of_mem_rootGroup_of_commute' hG.hx hβ hγ hex)
  have hτa : Commute τ a := (hτ.2 a hG.ha).2 hG.hac.symm
  have hτ2 := hD.mul_self_eq_one hτ.1
  have hτaT : τ * a * τ⁻¹ ∈ rootSet D a := by
    rw [hτa.eq, mul_inv_cancel_right]
    exact mem_rootSet_self hG.ha
  refine StabReach.of_conj h.isClass hτaT ?_
  rw [hτeq, show τ * (τ * γ * τ⁻¹) * τ⁻¹ = (τ * τ) * γ * (τ * τ)⁻¹ by group, hτ2, one_mul,
    inv_one, mul_one]
  exact StabReach.of_mem hG.ha hγT

end Reduction

theorem GateConfig.stabReach_of_collinear {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (hReg : RootLinesRegularStep) {a x c y : G} (hG : GateConfig D a x c)
    (hy : y ∈ D) (hay : ¬ Commute a y) (hodday : Odd (orderOf (a * y)))
    (hey : Commute ((c * x) ^ 2) y) (heyD : (c * x) ^ 2 * y ∈ D) : StabReach D a x y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  set e := (c * x) ^ 2 with he
  have hL := hAll a hG.ha c hG.hc hG.hac hG.hacD hG.hcT
  have hec : Commute e c := hG.hce.symm
  have hecD : e * c ∈ D := by rw [← hG.hce.eq]; exact hG.hceD
  have hex : Commute e x := hG.hxe.symm
  have hexD : e * x ∈ D := by rw [← hG.hxe.eq]; exact hG.hxeD
  have hTe : ∀ {z : G}, z ∈ rootSet D e → orderOf (z * a) = 4 := fun hz =>
    (orderOf_mul_eq_four_iff_of_mem_rootSet hD hG.heD hz hG.ha).2 hG.h4ea
  have hyT : y ∉ rootSet D e := fun hyT => by
    have := hTe hyT
    rw [orderOf_mul_comm_eq, this] at hodday
    exact absurd hodday (by decide)
  by_cases hyM : y ∈ rootGroup D e ⊔ rootGroup D x
  · exact hG.stabReach_of_mem_line h hc hs hy hyM hyT
  have hoffN : ∀ {z : G}, z ∈ D → ¬ Commute a z → Odd (orderOf (a * z)) →
      z ∉ rootGroup D e ⊔ rootGroup D c := fun hz haz hoddaz hzN =>
    not_commute_of_collinear hD hz hG.hc (fun h' => haz h'.symm)
      (by rw [orderOf_mul_comm_eq]; exact hoddaz) hG.hac hG.hacD
      (commute_of_mem_sup_rootGroup hG.heD hG.hc hec hzN (right_mem_line hG.hc))
  have hLS : LineSetting G D :=
    ⟨h, hc, hs, hconn, ⟨a, hG.ha, c, hG.hc, hG.hac, hG.hacD, hG.hcT, hL⟩⟩
  obtain ⟨⟨k, hk, hkmap⟩, -⟩ := hReg G D hLS e hG.heD c hG.hc hec hecD hG.hcTe y hy hey heyD
    (hoffN hy hay hodday) x hG.hx hex hexD (hoffN hG.hx hG.hax hG.hoddax)
  have hkc : Commute k c := commute_of_mem_nCore hk.1
  have hkN : k ∈ Subgroup.normalizer ((rootGroup D a ⊔ rootGroup D c : Subgroup G) : Set G) := by
    refine (Subgroup.closure_le _).2 (fun s hs' => ?_) hk.1
    exact mem_normalizer_of_normalizesLine hD hs'.1 (normalizesLine_of_commute h hc hs hG.ha
      hG.hc hG.hac hG.hacD hG.hcT hL hG.hc (right_mem_line hG.hc) hs'.1
      (Moufang.commute_of_mem_twoCore hs'.2))
  have ha'L : k * a * k⁻¹ ∈ rootGroup D a ⊔ rootGroup D c :=
    (Subgroup.mem_normalizer_iff.1 hkN a).1 (left_mem_line hG.ha)
  have ha'D : k * a * k⁻¹ ∈ D := conj_mem_of_isClass hclass k hG.ha
  have ha'T : k * a * k⁻¹ ∉ rootSet D c := by
    intro h'
    apply hG.hcT
    have : k * a * k⁻¹ ∈ rootSet D (k * c * k⁻¹) := by
      rw [hkc.eq, mul_inv_cancel_right]
      exact h'
    rw [rootSet_conj hclass] at this
    obtain ⟨z, hz, hza⟩ := this
    have hza' : z = a := by
      have := congrArg (fun w => k⁻¹ * w * k) hza
      simpa [mul_assoc] using this
    rw [hza'] at hz
    exact mem_rootSet_comm hG.hc hz
  obtain ⟨σ, hσa, hσL⟩ : ∃ σ : G, σ * (k * a * k⁻¹) * σ⁻¹ ∈ rootSet D a ∧
      ∀ u ∈ rootGroup D e ⊔ rootGroup D x, Commute σ u := by
    rw [sup_comm] at ha'L
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := exists_mul_eq_of_mem_line hG.ha hG.hac.symm ha'L
    have hγ1 : γ ≠ 1 := by
      rintro rfl
      rw [mul_one] at hβγ
      apply ha'T
      rw [hβγ]
      exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.hc hβ
        (by rw [← hβγ]; exact hD.ne_one ha'D)
    have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.ha hγ hγ1
    by_cases hβ1 : β = 1
    · refine ⟨1, ?_, fun u _ => Commute.one_left u⟩
      rw [hβγ, hβ1, one_mul]
      simpa using hγT
    have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.hc hβ hβ1
    have h4ae : orderOf (a * e) = 4 := by rw [orderOf_mul_comm_eq]; exact hG.h4ea
    obtain ⟨τ, hτ, hτeq⟩ :=
      exists_conj_eq_mul_of_sq_mem_rootSet h hc hs hG.ha hG.heD h4ae hG.hsq hβT hγT
        (commute_of_mem_rootGroup_of_commute' hG.ha hβ hγ hG.hac.symm)
    have hτ2 := hD.mul_self_eq_one hτ.1
    refine ⟨τ, ?_, fun u hu => commute_of_mem_line hτ.1
      (commute_of_mem_rootSet hG.heD hτ (mem_rootSet_self hG.heD)) ((hτ.2 x hG.hx).2 hex) hu⟩
    rw [hβγ, hτeq, show τ * (τ * γ * τ⁻¹) * τ⁻¹ = (τ * τ) * γ * (τ * τ)⁻¹ by group, hτ2,
      one_mul, inv_one, mul_one]
    exact hγT
  have hga : (σ * k) * a * (σ * k)⁻¹ ∈ rootSet D a := by
    rw [show σ * k * a * (σ * k)⁻¹ = σ * (k * a * k⁻¹) * σ⁻¹ by group]
    exact hσa
  have hkyM : k * y * k⁻¹ ∈ rootGroup D e ⊔ rootGroup D x :=
    conj_mem_of_map_eq hkmap (right_mem_line hy)
  have hgy : (σ * k) * y * (σ * k)⁻¹ = k * y * k⁻¹ := by
    rw [show σ * k * y * (σ * k)⁻¹ = σ * (k * y * k⁻¹) * σ⁻¹ by group, (hσL _ hkyM).eq,
      mul_inv_cancel_right]
  have hy'D : k * y * k⁻¹ ∈ D := conj_mem_of_isClass hclass k hy
  have hopp := opposite_conj_of_mem_rootSet hD hclass hG.ha hy hga hay hodday
  rw [hgy] at hopp
  have hy'T : k * y * k⁻¹ ∉ rootSet D e := fun h' => by
    have := hTe h'
    rw [orderOf_mul_comm_eq, this] at hopp
    exact absurd hopp.2 (by decide)
  refine StabReach.of_conj hclass hga ?_
  rw [hgy]
  exact hG.stabReach_of_mem_line h hc hs hy'D hkyM hy'T

theorem GateConfig.stabReach_of_special_mem_line {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (hReg : RootLinesRegularStep) {a x c y : G} (hG : GateConfig D a x c)
    (hy : y ∈ D) (hay : ¬ Commute a y) (hodday : Odd (orderOf (a * y)))
    (h4y : orderOf (y * c) = 4)
    (heyL : (c * y) ^ 2 ∈ rootGroup D c ⊔ rootGroup D ((c * x) ^ 2)) : StabReach D a x y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  set e := (c * x) ^ 2 with he
  have hGy := GateConfig.of h hc hs hconn hAll hG.ha hy hG.hc hG.hac hG.hacD hay hodday h4y
  have hTe : ∀ {z : G}, z ∈ rootSet D e → orderOf (z * a) = 4 := fun hz =>
    (orderOf_mul_eq_four_iff_of_mem_rootSet hD hG.heD hz hG.ha).2 hG.h4ea
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := exists_mul_eq_of_mem_line hG.heD hG.hce heyL
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hβγ
    apply hGy.hcTe
    have hT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.hc hβ
      (by rw [← hβγ]; exact hD.ne_one hGy.heD)
    rw [← hβγ] at hT
    exact mem_rootSet_comm hG.hc hT
  have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.heD hγ hγ1
  by_cases hβ1 : β = 1
  · have hT : (c * y) ^ 2 ∈ rootSet D e := by rw [hβγ, hβ1, one_mul]; exact hγT
    have hyT : y ∉ rootSet D e := fun h' => by
      have := hTe h'
      rw [orderOf_mul_comm_eq, this] at hodday
      exact absurd hodday (by decide)
    obtain ⟨hey, heyD⟩ :=
      collinear_of_collinear_mem_rootSet h hc hs hG.heD hT hy hGy.hxe hGy.hxeD hyT
    exact hG.stabReach_of_collinear h hc hs hconn hAll hReg hy hay hodday hey heyD
  have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.hc hβ hβ1
  have hsq' : (e * a) ^ 2 ∈ rootSet D c := by
    rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hG.heD) (hD.mul_self_eq_one hG.ha) hG.h4ea]
    exact hG.hsq
  obtain ⟨τ, hτ, hτeq⟩ := exists_conj_eq_mul_of_sq_mem_rootSet h hc hs hG.heD hG.ha hG.h4ea hsq' hβT
    hγT (commute_of_mem_rootGroup_of_commute' hG.heD hβ hγ hG.hce)
  have hτc : Commute τ c := (hτ.2 c hG.hc).2 hG.hac
  have hτa : Commute τ a := commute_of_mem_rootSet hG.ha hτ (mem_rootSet_self hG.ha)
  have hτ2 := hD.mul_self_eq_one hτ.1
  have hτaT : τ * a * τ⁻¹ ∈ rootSet D a := by
    rw [hτa.eq, mul_inv_cancel_right]
    exact mem_rootSet_self hG.ha
  have hy'D := conj_mem_of_isClass hclass τ hy
  have hcy' : c * (τ * y * τ⁻¹) = τ * (c * y) * τ⁻¹ := by
    calc c * (τ * y * τ⁻¹) = (c * τ) * y * τ⁻¹ := by group
      _ = (τ * c) * y * τ⁻¹ := by rw [hτc.eq]
      _ = τ * (c * y) * τ⁻¹ := by group
  have hsqy' : (c * (τ * y * τ⁻¹)) ^ 2 = γ := by
    rw [hcy', conj_pow, hβγ, hτeq, show τ * (τ * γ * τ⁻¹) * τ⁻¹ = (τ * τ) * γ * (τ * τ)⁻¹ by group,
      hτ2, one_mul, inv_one, mul_one]
  have h4y' : orderOf (τ * y * τ⁻¹ * c) = 4 := by
    have heq : τ * y * τ⁻¹ * c = τ * (y * c) * τ⁻¹ := by
      calc τ * y * τ⁻¹ * c = τ * y * (τ⁻¹ * c) := by group
        _ = τ * y * (c * τ⁻¹) := by rw [(hτc.inv_left).eq]
        _ = τ * (y * c) * τ⁻¹ := by group
    rw [heq, orderOf_conj_eq]
    exact h4y
  have hopp := opposite_conj_of_mem_rootSet hD hclass hG.ha hy hτaT hay hodday
  have hGy' := GateConfig.of h hc hs hconn hAll hG.ha hy'D hG.hc hG.hac hG.hacD hopp.1 hopp.2 h4y'
  have hxe' := hGy'.hxe
  have hxeD' := hGy'.hxeD
  rw [hsqy'] at hxe' hxeD'
  have hyT' : τ * y * τ⁻¹ ∉ rootSet D e := fun h' => by
    have := hTe h'
    rw [orderOf_mul_comm_eq, this] at hopp
    exact absurd hopp.2 (by decide)
  obtain ⟨hey', hey'D⟩ :=
    collinear_of_collinear_mem_rootSet h hc hs hG.heD hγT hy'D hxe' hxeD' hyT'
  exact StabReach.of_conj hclass hτaT
    (hG.stabReach_of_collinear h hc hs hconn hAll hReg hy'D hopp.1 hopp.2 hey' hey'D)

theorem GateConfig.stabReach_of_special {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (hReg : RootLinesRegularStep) {a x c y : G} (hG : GateConfig D a x c)
    (hy : y ∈ D) (hay : ¬ Commute a y) (hodday : Odd (orderOf (a * y)))
    (h4y : orderOf (y * c) = 4) : StabReach D a x y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hGy := GateConfig.of h hc hs hconn hAll hG.ha hy hG.hc hG.hac hG.hacD hay hodday h4y
  by_cases hN : (c * y) ^ 2 ∈ rootGroup D c ⊔ rootGroup D ((c * x) ^ 2)
  · exact hG.stabReach_of_special_mem_line h hc hs hconn hAll hReg hy hay hodday h4y hN
  have hL := hAll a hG.ha c hG.hc hG.hac hG.hacD hG.hcT
  have hLS : LineSetting G D :=
    ⟨h, hc, hs, hconn, ⟨a, hG.ha, c, hG.hc, hG.hac, hG.hacD, hG.hcT, hL⟩⟩
  have hcaD : c * a ∈ D := by rw [← hG.hac.eq]; exact hG.hacD
  have haT : a ∉ rootSet D c := fun h' => hG.hcT (mem_rootSet_comm hG.hc h')
  have heyL : (c * y) ^ 2 ∉ rootGroup D c ⊔ rootGroup D a := by
    rw [sup_comm]
    exact hGy.heL
  have hexL : (c * x) ^ 2 ∉ rootGroup D c ⊔ rootGroup D a := by
    rw [sup_comm]
    exact hG.heL
  obtain ⟨⟨k, hk, hkmap⟩, -⟩ := hReg G D hLS c hG.hc a hG.ha hG.hac.symm hcaD haT _ hGy.heD
    hGy.hce hGy.hceD heyL _ hG.heD hG.hce hG.hceD hexL
  have hka : Commute k a := commute_of_mem_nCore hk.1
  have hkc : Commute k c := Subgroup.mem_centralizer_singleton_iff.1 hk.2
  have hkaT : k * a * k⁻¹ ∈ rootSet D a := by
    rw [hka.eq, mul_inv_cancel_right]
    exact mem_rootSet_self hG.ha
  have hy'D := conj_mem_of_isClass hclass k hy
  have hopp := opposite_conj_of_mem_rootSet hD hclass hG.ha hy hkaT hay hodday
  have hcy' : c * (k * y * k⁻¹) = k * (c * y) * k⁻¹ := by
    calc c * (k * y * k⁻¹) = (c * k) * y * k⁻¹ := by group
      _ = (k * c) * y * k⁻¹ := by rw [hkc.eq]
      _ = k * (c * y) * k⁻¹ := by group
  have h4y' : orderOf (k * y * k⁻¹ * c) = 4 := by
    have heq : k * y * k⁻¹ * c = k * (y * c) * k⁻¹ := by
      calc k * y * k⁻¹ * c = k * y * (k⁻¹ * c) := by group
        _ = k * y * (c * k⁻¹) := by rw [(hkc.inv_left).eq]
        _ = k * (y * c) * k⁻¹ := by group
    rw [heq, orderOf_conj_eq]
    exact h4y
  have hN' : (c * (k * y * k⁻¹)) ^ 2 ∈ rootGroup D c ⊔ rootGroup D ((c * x) ^ 2) := by
    rw [hcy', conj_pow]
    exact conj_mem_of_map_eq hkmap (right_mem_line hGy.heD)
  exact StabReach.of_conj hclass hkaT (hG.stabReach_of_special_mem_line h hc hs hconn hAll hReg
    hy'D hopp.1 hopp.2 h4y' hN')

theorem GateConfig.stabReach_of_gate_mem_line {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (hReg : RootLinesRegularStep) {a x c y cy : G} (hG : GateConfig D a x c)
    (hy : y ∈ D) (hay : ¬ Commute a y) (hodday : Odd (orderOf (a * y))) (hcy : cy ∈ D)
    (hacy : Commute a cy) (hacyD : a * cy ∈ D) (h4y : orderOf (y * cy) = 4)
    (hcyL : cy ∈ rootGroup D a ⊔ rootGroup D c) : StabReach D a x y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hGy := GateConfig.of h hc hs hconn hAll hG.ha hy hcy hacy hacyD hay hodday h4y
  have hLeq : rootGroup D a ⊔ rootGroup D cy = rootGroup D a ⊔ rootGroup D c :=
    sup_rootGroup_eq_of_mem h hc hs hG.ha hG.hc hG.hac hG.hacD hG.hcT (left_mem_line hG.ha) hcyL
      (hD.ne_one hG.ha) (hD.ne_one hcy) hGy.hcT
  have hcL : c ∈ rootGroup D a ⊔ rootGroup D cy := by
    rw [hLeq]
    exact right_mem_line hG.hc
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := exists_mul_eq_of_mem_line hcy hacy hcL
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hβγ
    apply hG.hcT
    rw [hβγ]
    exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.ha hβ
      (by rw [← hβγ]; exact hD.ne_one hG.hc)
  have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcy hγ hγ1
  by_cases hβ1 : β = 1
  · have hcT : c ∈ rootSet D cy := by rw [hβγ, hβ1, one_mul]; exact hγT
    have h4c : orderOf (y * c) = 4 := by
      rw [orderOf_mul_comm_eq]
      exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD hcy hcT hy).2
        (by rw [orderOf_mul_comm_eq]; exact h4y)
    exact hG.stabReach_of_special h hc hs hconn hAll hReg hy hay hodday h4c
  have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hG.ha hβ hβ1
  obtain ⟨τ, hτ, hτa, hτeq⟩ :=
    exists_conj_eq_mul_of_mem_rootSet h hc hs hG.ha hcy hacy hacyD hGy.hcT hβT hγT
  have hτaT : τ * a * τ⁻¹ ∈ rootSet D a := by
    rw [hτa.eq, mul_inv_cancel_right]
    exact mem_rootSet_self hG.ha
  have hy'D := conj_mem_of_isClass hclass τ hy
  have hopp := opposite_conj_of_mem_rootSet hD hclass hG.ha hy hτaT hay hodday
  have h4γ : orderOf (y * γ) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD hcy hγT hy).2
      (by rw [orderOf_mul_comm_eq]; exact h4y)
  have h4y' : orderOf (τ * y * τ⁻¹ * c) = 4 := by
    rw [hβγ, hτeq, show τ * y * τ⁻¹ * (τ * γ * τ⁻¹) = τ * (y * γ) * τ⁻¹ by group,
      orderOf_conj_eq]
    exact h4γ
  exact StabReach.of_conj hclass hτaT
    (hG.stabReach_of_special h hc hs hconn hAll hReg hy'D hopp.1 hopp.2 h4y')

theorem exists_third_line (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ThreeLines D) {a u v : G} (ha : a ∈ D) (hu : u ∈ D) (hv : v ∈ D) (hau : Commute a u)
    (hauD : a * u ∈ D) (huT : u ∉ rootSet D a) (hav : Commute a v) (havD : a * v ∈ D)
    (hvT : v ∉ rootSet D a) :
    ∃ d ∈ D, Commute a d ∧ a * d ∈ D ∧ d ∉ rootSet D a ∧ d ∉ rootGroup D a ⊔ rootGroup D u ∧
      d ∉ rootGroup D a ⊔ rootGroup D v := by
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨b, hb, c₁, hc₁, c₂, hc₂, c₃, hc₃, hcol, h21, h31, h32⟩ := h3
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hb ha)
  have hline : ∀ {y z : G}, g * z * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D (g * y * g⁻¹) ↔
      z ∈ rootGroup D b ⊔ rootGroup D y := by
    intro y z
    constructor
    · intro hz
      have := conj_inv_mem_line hclass hz
      simpa [mul_assoc] using this
    · intro hz
      rw [rootGroup_conj hclass, rootGroup_conj hclass, ← Subgroup.map_sup]
      exact ⟨z, hz, by simp⟩
  have hc' : ∀ y ∈ ({c₁, c₂, c₃} : Set G), g * y * g⁻¹ ∈ D ∧
      Commute (g * b * g⁻¹) (g * y * g⁻¹) ∧ g * b * g⁻¹ * (g * y * g⁻¹) ∈ D ∧
      g * y * g⁻¹ ∉ rootSet D (g * b * g⁻¹) := by
    intro y hy
    obtain ⟨hby, hbyD, hyT⟩ := hcol y hy
    have hyD : y ∈ D := by
      rcases hy with rfl | rfl | rfl
      · exact hc₁
      · exact hc₂
      · exact hc₃
    refine ⟨conj_mem_of_isClass hclass g hyD, (Commute.conj_iff g).2 hby, ?_, ?_⟩
    · rw [show g * b * g⁻¹ * (g * y * g⁻¹) = g * (b * y) * g⁻¹ by group]
      exact conj_mem_of_isClass hclass g hbyD
    · rw [rootSet_conj hclass]
      rintro ⟨z, hz, hzy⟩
      apply hyT
      have : z = y := by
        have := congrArg (fun w => g⁻¹ * w * g) hzy
        simpa [mul_assoc] using this
      rw [← this]
      exact hz
  have hsame : ∀ {w y z : G}, w ∈ D → Commute (g * b * g⁻¹) w → g * b * g⁻¹ * w ∈ D →
      w ∉ rootSet D (g * b * g⁻¹) → y ∈ ({c₁, c₂, c₃} : Set G) → z ∈ D →
      g * y * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D w →
      g * z * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D w →
      z ∈ rootGroup D b ⊔ rootGroup D y := by
    intro w y z hw hbw hbwD hwT hy hz hyw hzw
    obtain ⟨hyD', hby', hbyD', hyT'⟩ := hc' y hy
    have hLeq := sup_rootGroup_eq_of_mem h hc hs ha hw hbw hbwD hwT (left_mem_line ha) hyw
      (hD.ne_one ha) (hD.ne_one hyD') hyT'
    rw [← hLeq] at hzw
    exact hline.1 hzw
  obtain ⟨h1D, h1b, h1bD, h1T⟩ := hc' c₁ (by simp)
  obtain ⟨h2D, h2b, h2bD, h2T⟩ := hc' c₂ (by simp)
  obtain ⟨h3D, h3b, h3bD, h3T⟩ := hc' c₃ (by simp)
  have hmem1 : c₁ ∈ ({c₁, c₂, c₃} : Set G) := by simp
  have hmem2 : c₂ ∈ ({c₁, c₂, c₃} : Set G) := by simp
  by_cases hu1 : g * c₁ * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D u
  · by_cases hu2 : g * c₂ * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D u
    · exact absurd (hsame hu hau hauD huT hmem1 hc₂ hu1 hu2) h21
    by_cases hv2 : g * c₂ * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D v
    ·
      refine ⟨_, h3D, h3b, h3bD, h3T, fun hu3 => h31 (hsame hu hau hauD huT hmem1 hc₃ hu1 hu3),
        fun hv3 => h32 (hsame hv hav havD hvT hmem2 hc₃ hv2 hv3)⟩
    · exact ⟨_, h2D, h2b, h2bD, h2T, hu2, hv2⟩
  by_cases hv1 : g * c₁ * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D v
  · by_cases hv2 : g * c₂ * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D v
    · exact absurd (hsame hv hav havD hvT hmem1 hc₂ hv1 hv2) h21
    by_cases hu2 : g * c₂ * g⁻¹ ∈ rootGroup D (g * b * g⁻¹) ⊔ rootGroup D u
    · refine ⟨_, h3D, h3b, h3bD, h3T, fun hu3 => h32 (hsame hu hau hauD huT hmem2 hc₃ hu2 hu3),
        fun hv3 => h31 (hsame hv hav havD hvT hmem1 hc₃ hv1 hv3)⟩
    · exact ⟨_, h2D, h2b, h2bD, h2T, hu2, hv2⟩
  · exact ⟨_, h1D, h1b, h1bD, h1T, hu1, hv1⟩

theorem not_mem_line_symm (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {a u d : G} (ha : a ∈ D) (hu : u ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (huT : u ∉ rootSet D a) (hdL : d ∉ rootGroup D a ⊔ rootGroup D u) :
    u ∉ rootGroup D a ⊔ rootGroup D d := by
  intro huL
  have hD := h.root
  have hLeq := sup_rootGroup_eq_of_mem h hc hs ha hd had hadD hdT (left_mem_line ha) huL
    (hD.ne_one ha) (hD.ne_one hu) huT
  exact hdL (by rw [hLeq]; exact right_mem_line hd)

theorem GateConfig.stabReach_of_oneOpposite {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (hReg : RootLinesRegularStep) (h3 : ThreeLines D) {a x c y : G}
    (hG : GateConfig D a x c) (hy : y ∈ D) (hay : ¬ Commute a y) (hodday : Odd (orderOf (a * y)))
    (hy1 : OneOpposite D a y) : StabReach D a x y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨cy, hcy, hacy, hacyD, h4y⟩ := hy1
  by_cases hcyL : cy ∈ rootGroup D a ⊔ rootGroup D c
  · exact hG.stabReach_of_gate_mem_line h hc hs hconn hAll hReg hy hay hodday hcy hacy hacyD h4y
      hcyL
  have hGy := GateConfig.of h hc hs hconn hAll hG.ha hy hcy hacy hacyD hay hodday h4y
  obtain ⟨d, hd, had, hadD, hdT, hdc, hdcy⟩ := exists_third_line h hc hs h3 hG.ha hG.hc hcy
    hG.hac hG.hacD hG.hcT hacy hacyD hGy.hcT
  have hL := hAll a hG.ha c hG.hc hG.hac hG.hacD hG.hcT
  have hLS : LineSetting G D :=
    ⟨h, hc, hs, hconn, ⟨a, hG.ha, c, hG.hc, hG.hac, hG.hacD, hG.hcT, hL⟩⟩
  obtain ⟨⟨k, hk, hkmap⟩, -⟩ := hReg G D hLS a hG.ha d hd had hadD hdT cy hcy hacy hacyD
    (not_mem_line_symm h hc hs hG.ha hcy hd had hadD hdT hGy.hcT hdcy) c hG.hc hG.hac hG.hacD
    (not_mem_line_symm h hc hs hG.ha hG.hc hd had hadD hdT hG.hcT hdc)
  have hka : Commute k a := Subgroup.mem_centralizer_singleton_iff.1 hk.2
  have hkaT : k * a * k⁻¹ ∈ rootSet D a := by
    rw [hka.eq, mul_inv_cancel_right]
    exact mem_rootSet_self hG.ha
  have hy'D := conj_mem_of_isClass hclass k hy
  have hopp := opposite_conj_of_mem_rootSet hD hclass hG.ha hy hkaT hay hodday
  have hcy'D := conj_mem_of_isClass hclass k hcy
  have hacy' : Commute a (k * cy * k⁻¹) := by
    have := (Commute.conj_iff k).2 hacy
    rwa [hka.eq, mul_inv_cancel_right] at this
  have hacy'D : a * (k * cy * k⁻¹) ∈ D := by
    have : k * (a * cy) * k⁻¹ ∈ D := conj_mem_of_isClass hclass k hacyD
    rwa [show k * (a * cy) * k⁻¹ = k * a * k⁻¹ * (k * cy * k⁻¹) by group, hka.eq,
      mul_inv_cancel_right] at this
  have h4y' : orderOf (k * y * k⁻¹ * (k * cy * k⁻¹)) = 4 := by
    rw [show k * y * k⁻¹ * (k * cy * k⁻¹) = k * (y * cy) * k⁻¹ by group, orderOf_conj_eq]
    exact h4y
  have hcy'L : k * cy * k⁻¹ ∈ rootGroup D a ⊔ rootGroup D c :=
    conj_mem_of_map_eq hkmap (right_mem_line hcy)
  exact StabReach.of_conj hclass hkaT (hG.stabReach_of_gate_mem_line h hc hs hconn hAll hReg
    hy'D hopp.1 hopp.2 hcy'D hacy' hacy'D h4y' hcy'L)

theorem exists_conj_of_oneOpposite {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hc : RootClosure D) (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) (hReg : RootLinesRegularStep) (h3 : ThreeLines D) {a x y : G}
    (ha : a ∈ D) (hx : x ∈ D) (hax : ¬ Commute a x) (hoddax : Odd (orderOf (a * x)))
    (hx1 : OneOpposite D a x) (hy : y ∈ D) (hay : ¬ Commute a y)
    (hodday : Odd (orderOf (a * y))) (hy1 : OneOpposite D a y) : StabReach D a x y := by
  obtain ⟨c, hcD, hac, hacD, h4⟩ := hx1
  exact (GateConfig.of h hc hs hconn hAll ha hx hcD hac hacD hax hoddax h4).stabReach_of_oneOpposite
    h hc hs hconn hAll hReg h3 hy hay hodday hy1

end CFSG.Timmesfeld.Bridge
