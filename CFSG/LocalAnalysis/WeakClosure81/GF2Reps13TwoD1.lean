module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Hyp
public import CFSG.Quasithin.EmptyFaithful.S145Cop

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

private theorem w16g_zpow_apply_eq {a : MulAut W} {u : W} (h : a u = u) (m : ℤ) :
    (a ^ m) u = u := by
  have h1 : a ∈ MulAction.stabilizer (MulAut W) u := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have h2 := (MulAction.stabilizer (MulAut W) u).zpow_mem h1 m
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2

private theorem w16g_le_stabSub_of_stable {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : StableUnder X U) : X ≤ stabSub U := by
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hxu => by
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hxu
    rwa [show x⁻¹ (x u) = u by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h1, h x hx u⟩

private theorem w16g_stableUnder_sup {X Y : Subgroup (MulAut W)} {U : Subgroup W}
    (hX : StableUnder X U) (hY : StableUnder Y U) : StableUnder (X ⊔ Y) U := by
  intro g hg u hu
  have hsup : g ∈ stabSub U :=
    sup_le (w16g_le_stabSub_of_stable hX) (w16g_le_stabSub_of_stable hY) hg
  exact (mem_stabSub.mp hsup u).2 hu

private theorem w16g_stableUnder_fixV_of_comm {Y : Subgroup (MulAut W)} {z : MulAut W}
    (h : ∀ y ∈ Y, y * z = z * y) : StableUnder Y (fixV (Subgroup.zpowers z)) := by
  intro y hy u hu
  rw [mem_fixV] at hu ⊢
  intro a ha
  have hay : a * y = y * a := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.symm (show Commute y z from h y hy)).zpow_left m).eq
  calc a (y u) = (a * y) u := rfl
    _ = (y * a) u := by rw [hay]
    _ = y (a u) := rfl
    _ = y u := by rw [hu a ha]

private theorem w16g_commSub_map_conj (X : Subgroup (MulAut W)) (φ : MulAut W) :
    commSub ⊤ (X.map (MulAut.conj φ).toMonoidHom) = (commSub ⊤ X).map φ.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, w, -, rfl⟩
    refine ⟨x (φ⁻¹ w) * (φ⁻¹ w)⁻¹, ⟨x, hx, φ⁻¹ w, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨d, ⟨x, hx, w, -, rfl⟩, rfl⟩
    refine ⟨φ * x * φ⁻¹, ⟨x, hx, rfl⟩, φ w, Subgroup.mem_top _, ?_⟩
    simp [MulAut.mul_apply]

private theorem w16g_stableUnder_commSub_of_comm {Y : Subgroup (MulAut W)} {z : MulAut W}
    (h : ∀ y ∈ Y, y * z = z * y) : StableUnder Y (commSub ⊤ (Subgroup.zpowers z)) := by
  intro y hy u hu
  have hconj : (Subgroup.zpowers z).map (MulAut.conj y).toMonoidHom = Subgroup.zpowers z := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change MulAut.conj y z = z
    rw [MulAut.conj_apply, h y hy, mul_assoc, mul_inv_cancel, mul_one]
  have hmap := w16g_commSub_map_conj (Subgroup.zpowers z) y
  rw [hconj] at hmap
  rw [hmap]
  exact ⟨u, hu, rfl⟩

theorem w16h_central_center (h : Cfg132 t P) (hind : NoDecomp132 t P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) :
    ∃ z : MulAut W, z ∈ P ∧ orderOf z = 3 ∧ (∀ y ∈ P, y * z = z * y) ∧
      (∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) ∧
      (∀ u : W, z u = u → u = 1) ∧ rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 2 := by
  classical
  have hW := h.hW
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr h.hne
  obtain ⟨n, hn⟩ := h.hP.exists_card_eq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hn
      exact h.hne ((Subgroup.card_eq_one).mp hn)
    · exact hpos
  obtain ⟨k, hkpos, hkcard⟩ :=
    IsPGroup.card_center_eq_prime_pow (p := 3) (G := ↥P) hn hnpos
  have hdvd : 3 ∣ Nat.card (Subgroup.center ↥P) := by
    rw [hkcard]
    exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hkpos)
  obtain ⟨xc, hxc3⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥P) 3 hdvd
  let z : MulAut W := (xc : ↥P)
  have hzP : z ∈ P := xc.1.2
  have hzc : ∀ y ∈ P, y * z = z * y := by
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp xc.2 ⟨y, hy⟩)
  have hz3 : orderOf z = 3 := by
    have h1 : orderOf z = orderOf (xc : ↥P) := Subgroup.orderOf_coe (xc : ↥P)
    exact h1.trans ((Subgroup.orderOf_coe xc).trans hxc3)
  let G : Subgroup (MulAut W) := P ⊔ Subgroup.zpowers t
  let T : Subgroup W := commSub ⊤ (Subgroup.zpowers t)
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hPG : P ≤ G := le_sup_left
  have htcomm : t * z = z * t := by
    have h1 := hZ z hzP hzc
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [h1]
  have hfix_stabG : StableUnder G (fixV (Subgroup.zpowers z)) := by
    refine w16g_stableUnder_sup (X := P) (Y := Subgroup.zpowers t) ?_ ?_
    · exact w16g_stableUnder_fixV_of_comm (Y := P) hzc
    · apply w16g_stableUnder_fixV_of_comm (Y := Subgroup.zpowers t)
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left htcomm m).eq
  have hcomm_stabG : StableUnder G (commSub ⊤ (Subgroup.zpowers z)) := by
    refine w16g_stableUnder_sup (X := P) (Y := Subgroup.zpowers t) ?_ ?_
    · exact w16g_stableUnder_commSub_of_comm (Y := P) hzc
    · apply w16g_stableUnder_commSub_of_comm (Y := Subgroup.zpowers t)
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((show Commute t z from htcomm).zpow_left m).eq
  have hodd : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz3]
    norm_num
  have hcompl : IsCompl (fixV (Subgroup.zpowers z)) (commSub ⊤ (Subgroup.zpowers z)) := by
    have hc := isCompl_fixV_commV_of_odd (Subgroup.zpowers z) hodd hW
    rwa [commV_eq_commSub] at hc
  have hz_ne_one : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz3
    norm_num at hz3
  have hdecomp := hind (fixV (Subgroup.zpowers z)) (commSub ⊤ (Subgroup.zpowers z))
    hfix_stabG hcomm_stabG hcompl.inf_eq_bot hcompl.sup_eq_top
  have hfixV : fixV (Subgroup.zpowers z) = ⊥ := by
    rcases hdecomp with htop | htop
    · exfalso
      apply hz_ne_one
      ext u
      have hu : u ∈ fixV (Subgroup.zpowers z) := by rw [htop]; exact Subgroup.mem_top u
      exact (mem_fixV.mp hu) z (Subgroup.mem_zpowers z)
    · simpa [htop] using hcompl.inf_eq_bot
  have hcommV : commSub ⊤ (Subgroup.zpowers z) = ⊤ := by
    rcases hdecomp with htop | htop
    · exfalso
      apply hz_ne_one
      ext u
      have hu : u ∈ fixV (Subgroup.zpowers z) := by rw [htop]; exact Subgroup.mem_top u
      exact (mem_fixV.mp hu) z (Subgroup.mem_zpowers z)
    · exact htop
  have hfix : ∀ u : W, z u = u → u = 1 := by
    intro u hu
    have humem : u ∈ fixV (Subgroup.zpowers z) := by
      rw [mem_fixV]
      intro a ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact w16g_zpow_apply_eq hu m
    rw [hfixV] at humem
    exact Subgroup.mem_bot.mp humem
  have hzT : StableUnder (Subgroup.zpowers z) T := by
    apply w16g_stableUnder_commSub_of_comm (Y := Subgroup.zpowers z) (z := t)
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (((show Commute t z from htcomm).symm).zpow_left m).eq
  have hz3pow : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hz3] at h1
  have heven : Even (rk ↥T) :=
    w16h_even_rk_of_fixedFree hW hz3pow (hzT z (Subgroup.mem_zpowers z))
      (fun u _ hzu => hfix u hzu)
  have hTne : T ≠ ⊥ := by
    intro hbot
    have ht1 : t = 1 := by
      ext u
      have hu : t u * u⁻¹ ∈ T :=
        Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, Subgroup.mem_top u, rfl⟩
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hu
      exact hu
    have hht : orderOf t = 2 := h.ht
    rw [ht1, orderOf_one] at hht
    norm_num at hht
  have hrkT_ne0 : rk ↥T ≠ 0 := by
    intro h0
    exact hTne ((rk_eq_zero_iff hW).mp h0)
  have hrk2 : rk ↥T = 2 := by
    obtain ⟨m, hm⟩ := heven
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exfalso
        apply hrkT_ne0
        rw [hm, h0, add_zero]
      · exact hpos
    have hle3 : rk ↥T ≤ 3 := h.hrk
    omega
  let S : Subgroup W := Subgroup.closure (⋃ g : ↥G, ((g : MulAut W) '' (T : Set W)))
  have hSstab : StableUnder G S := by
    intro hh hhh
    let H : Subgroup W :=
      { carrier := {x | hh x ∈ S}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          change hh (x * y) ∈ S
          rw [map_mul]
          exact S.mul_mem hx hy
        inv_mem' := by
          intro x hx
          change hh x⁻¹ ∈ S
          rw [map_inv]
          exact S.inv_mem hx }
    have hsH : (⋃ g : ↥G, ((g : MulAut W) '' (T : Set W))) ⊆ H := by
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨g, v, hv, rfl⟩ := hx
      change hh ((g : MulAut W) v) ∈ S
      have heq : hh ((g : MulAut W) v) = ((⟨hh, hhh⟩ * g : ↥G) : MulAut W) v := by
        rw [Subgroup.coe_mul, MulAut.mul_apply]
      rw [heq]
      exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨⟨hh, hhh⟩ * g, ⟨v, hv, rfl⟩⟩)
    intro x hx
    exact (Subgroup.closure_le (K := H)).mpr hsH hx
  have hTS : T ≤ S := by
    intro u hu
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨(1 : ↥G), ⟨u, hu, by simp⟩⟩)
  have hSP : ∀ x ∈ P, ∀ u ∈ S, x u ∈ S := fun x hx u hu => hSstab x (hPG hx) u hu
  have hSt : ∀ u ∈ S, t u ∈ S := fun u hu => hSstab t htG u hu
  have ht_triv : ∀ u : W, t u * u⁻¹ ∈ S := fun u =>
    hTS (Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, Subgroup.mem_top u, rfl⟩)
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h1
    exact h1
  have hPtriv : ∀ x ∈ P, ∀ u : W, x u * u⁻¹ ∈ S :=
    w16h_acts_trivially_of_comm_eq_self htt h.hn h.hc hSP hSt ht_triv
  have hzS : commSub ⊤ (Subgroup.zpowers z) ≤ S := by
    rw [commSub]
    apply (Subgroup.closure_le (K := S)).mpr
    rintro c ⟨x, hx, w, -, rfl⟩
    exact hPtriv x (Subgroup.zpowers_le.mpr hzP hx) w
  have hSW : S = ⊤ := top_le_iff.mp (hcommV ▸ hzS)
  let Zc : Subgroup (MulAut W) := P ⊓ Subgroup.centralizer (P : Set (MulAut W))
  have hZcP : Zc ≤ P := inf_le_left
  have hzZc : z ∈ Zc := ⟨hzP, (Subgroup.mem_centralizer_iff).mpr hzc⟩
  have hZcPgrp : IsPGroup 3 ↥Zc := h.hP.to_le hZcP
  have hZcT : StableUnder Zc T := by
    apply w16g_stableUnder_commSub_of_comm (Y := Zc) (z := t)
    intro y hy
    have hyP : y ∈ P := hy.1
    have hyc : ∀ w ∈ P, w * y = y * w := Subgroup.mem_centralizer_iff.mp hy.2
    have hyt := hZ y hyP hyc
    calc y * t = (t * y * t⁻¹) * t := by rw [hyt]
      _ = t * y := by group
  have hZc_stab : Zc ≤ stabSub T := w16g_le_stabSub_of_stable hZcT
  let φ : Zc →* MulAut ↥T := (resHom T).comp (Subgroup.inclusion hZc_stab)
  have hφeq : φ = (resHom T).comp (Subgroup.inclusion hZc_stab) := rfl
  have hcG_comm : ∀ c ∈ Zc, ∀ g ∈ G, c * g = g * c := by
    intro c hc g hg
    have hcc : ∀ y ∈ P, y * c = c * y := Subgroup.mem_centralizer_iff.mp hc.2
    have hct : c * t = t * c := by
      have h1 := hZ c hc.1 hcc
      calc c * t = (t * c * t⁻¹) * t := by rw [h1]
        _ = t * c := by group
    have hle : G ≤ Subgroup.centralizer ({c} : Set (MulAut W)) := by
      apply sup_le
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro hh hhh
        rw [Set.mem_singleton_iff] at hhh
        rw [hhh]
        exact (hcc y hy).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro hh hhh
        rw [Set.mem_singleton_iff] at hhh
        rw [hhh]
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_right hct m).eq
    exact Subgroup.mem_centralizer_iff.mp (hle hg) c (Set.mem_singleton c)
  have hcSfix : ∀ c ∈ Zc, (∀ u ∈ T, c u = u) → ∀ u ∈ S, c u = u := by
    intro c hc hcT
    let H : Subgroup W :=
      { carrier := {x | c x = x}
        one_mem' := map_one c
        mul_mem' := by
          intro x y hx hy
          change c (x * y) = x * y
          rw [map_mul, hx, hy]
        inv_mem' := by
          intro x hx
          change c x⁻¹ = x⁻¹
          rw [map_inv, hx] }
    have hsH : (⋃ g : ↥G, ((g : MulAut W) '' (T : Set W))) ⊆ H := by
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨g, v, hv, rfl⟩ := hx
      have hcg : c * (g : MulAut W) = (g : MulAut W) * c := hcG_comm c hc g g.2
      show c ((g : MulAut W) v) = (g : MulAut W) v
      calc c ((g : MulAut W) v) = (c * (g : MulAut W)) v := rfl
        _ = ((g : MulAut W) * c) v := by rw [hcg]
        _ = (g : MulAut W) (c v) := rfl
        _ = (g : MulAut W) v := by rw [hcT v hv]
    intro x hx
    exact (Subgroup.closure_le (K := H)).mpr hsH hx
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcT : ∀ u ∈ T, (c : MulAut W) u = u := by
      intro u hu
      have h2 := congrArg (fun ψ : MulAut ↥T => (ψ ⟨u, hu⟩ : W)) hc
      rw [hφeq, MonoidHom.comp_apply, resHom_apply] at h2
      simpa using h2
    have hfixall : ∀ u ∈ S, (c : MulAut W) u = u := hcSfix (c : MulAut W) c.2 hcT
    ext u
    exact hfixall u (by rw [hSW]; exact Subgroup.mem_top u)
  have hcardZc : Nat.card Zc = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
  have hdvd : Nat.card φ.range ∣ Nat.card (MulAut ↥T) := Subgroup.card_subgroup_dvd_card φ.range
  have hTcard : Nat.card T = 2 ^ 2 := by
    rw [card_eq_two_pow hW T, hrk2]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥T) (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by simpa using hW (a : W))) (n := 2) hTcard
  have hAutT : Nat.card (MulAut ↥T) = 6 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2) (W := ↥T) e,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 2, Fin.prod_univ_two]
    norm_num
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hZcPgrp
  have hdvd' : 3 ^ j ∣ 6 := by
    have h1 : Nat.card Zc ∣ Nat.card (MulAut ↥T) := by
      rw [hcardZc]
      exact hdvd
    rw [hj, hAutT] at h1
    exact h1
  have hj1 : j ≤ 1 := by
    by_contra hjle
    have h2j : 2 ≤ j := by omega
    have h9 : 9 ∣ 3 ^ j := by
      have h22 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [← h22]
      exact pow_dvd_pow 3 h2j
    have h96 : 9 ∣ 6 := h9.trans hdvd'
    have hle := Nat.le_of_dvd (by norm_num) h96
    norm_num at hle
  have hZc_le3 : Nat.card Zc ≤ 3 := by
    rw [hj]
    calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 3 := pow_one 3
  have hZc_ge3 : 3 ≤ Nat.card Zc := by
    have hzpowZc : Subgroup.zpowers z ≤ Zc := Subgroup.zpowers_le.mpr hzZc
    have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hzpowZc)
      (Subgroup.inclusion_injective hzpowZc)
    rwa [Nat.card_zpowers, hz3] at hcard
  have hZc_card3 : Nat.card Zc = 3 := le_antisymm hZc_le3 hZc_ge3
  have hZc_eq : Zc = Subgroup.zpowers z := by
    have hle : Subgroup.zpowers z ≤ Zc := Subgroup.zpowers_le.mpr hzZc
    exact (Subgroup.eq_of_le_of_card_ge hle (by simp [hZc_card3, Nat.card_zpowers, hz3])).symm
  have hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z := by
    intro x hx hxc
    have hxZc : x ∈ Zc := ⟨hx, (Subgroup.mem_centralizer_iff).mpr hxc⟩
    rwa [hZc_eq] at hxZc
  exact ⟨z, hzP, hz3, hzc, hZP, hfix, hrk2⟩

private theorem w16g_zpowers_eq_one_or_self {A : Type*} [Group A] {t : A} (ht : t * t = 1)
    {b : A} (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact ht
  have hmod := zpow_eq_zpow_emod k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hmod, h, zpow_zero]
  · right; rw [hmod, h, zpow_one]

private theorem w16g_exists_inverted (h : Cfg132 t P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) :
    ∃ x ∈ P, x ∉ Subgroup.zpowers z ∧ x ^ 3 ∈ Subgroup.zpowers z ∧
      (∀ g ∈ P, ∃ i : Fin 3, g * x * g⁻¹ = x * z ^ (i : ℕ)) ∧
      ∃ j : Fin 3, t * x * t⁻¹ = x⁻¹ * z ^ (j : ℕ) := by
  classical
  have htt : t * t = 1 := by rw [← pow_two, ← h.ht]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hz3pow : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hz3] at h1
  have hnab : ∃ a b : ↥P, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hle : P ≤ Subgroup.zpowers z := fun x hx =>
      hZP x hx (fun g hg => (congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨g, hg⟩)).symm)
    have htcent : ∀ x ∈ P, t * x * t⁻¹ = x := fun x hx =>
      hZ x hx (fun g hg => (congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨g, hg⟩)).symm)
    have hbot : ⁅P, Subgroup.zpowers t⁆ = ⊥ := by
      apply le_antisymm _ bot_le
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      rcases w16g_zpowers_eq_one_or_self htt hb with hb1 | hbt
      · rw [hb1]; simp
      · rw [hbt]
        exact (show t * a = a * t from by
          calc t * a = (t * a * t⁻¹) * t := by group
            _ = a * t := by rw [htcent a ha]).symm
    exact h.hne (by rw [← h.hc, hbot])
  let Zc : Subgroup (MulAut W) := (Subgroup.upperCentralSeries ↥P 1).map P.subtype
  have hzcent : ∀ y ∈ Subgroup.zpowers z, y ∈ Subgroup.centralizer (P : Set (MulAut W)) := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [← hm]
    exact (Commute.zpow_right (hzc g hg) m).eq
  have hZc_eq : Zc = Subgroup.zpowers z := by
    dsimp only [Zc]
    rw [Subgroup.upperCentralSeries_one]
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hZP y.1 y.2 fun g hg => by
        calc g * y.1 = (⟨g, hg⟩ * y : ↥P).1 := rfl
          _ = (y * ⟨g, hg⟩ : ↥P).1 := by rw [Subgroup.mem_center_iff.mp hy ⟨g, hg⟩]
          _ = y.1 * g := rfl
    · intro x hx
      refine ⟨⟨x, Subgroup.zpowers_le.mpr hzP hx⟩, ?_, rfl⟩
      change (⟨x, Subgroup.zpowers_le.mpr hzP hx⟩ : ↥P) ∈ Subgroup.center ↥P
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simpa using Subgroup.mem_centralizer_iff.mp (hzcent x hx) g.1 g.2
  let Z2 : Subgroup (MulAut W) := (Subgroup.upperCentralSeries ↥P 2).map P.subtype
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥P := Subtype.finite
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent h.hP
  have hstrict : Subgroup.upperCentralSeries ↥P 1 < Subgroup.upperCentralSeries ↥P 2 := by
    refine lt_of_le_of_ne (Subgroup.upperCentralSeries_mono ↥P (by norm_num)) ?_
    intro heq
    have htop := Subgroup.upperCentralSeries.eq_top (G := ↥P) (a := 1) (b := 2) (by norm_num) heq
    rw [Subgroup.upperCentralSeries_one] at htop
    haveI : IsMulCommutative ↥P := Subgroup.center_eq_top_iff.mp htop
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsMulCommutative.is_comm (M := ↥P)).comm a b)
  have hZc_le : Zc ≤ Z2 :=
    Subgroup.map_mono (f := P.subtype) (Subgroup.upperCentralSeries_mono ↥P (by norm_num))
  have hZ2_lt : Zc < Z2 := by
    refine lt_of_le_of_ne hZc_le ?_
    intro heq
    exact absurd (Subgroup.map_injective (f := P.subtype) P.subtype_injective heq)
      (ne_of_lt hstrict)
  have htZc : ∀ c ∈ Zc, t * c * t⁻¹ = c := by
    intro c hc
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hZc_eq ▸ hc)
    rw [← hm, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hZ z hzP hzc]
  have hZc_central : ∀ c ∈ Zc, ∀ g ∈ P, c * g = g * c := by
    intro c hc g hg
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hZc_eq ▸ hc)
    rw [← hm]
    exact (Commute.zpow_right (hzc g hg) m).eq.symm
  have hfin : ∀ c ∈ Zc, ∃ i : Fin 3, c = z ^ (i : ℕ) := by
    intro c hc
    have hmem := (mem_zpowers_iff_mem_range_orderOf).mp (hZc_eq ▸ hc)
    rw [hz3] at hmem
    obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hmem
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, hiz.symm⟩
  have hmem_Z2 : ∀ x : MulAut W, x ∈ Z2 ↔ x ∈ P ∧ ∀ g ∈ P, ⁅x, g⁆ ∈ Zc := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun g hg => ?_⟩
      have h1 : ⁅y, (⟨g, hg⟩ : ↥P)⁆ ∈ Subgroup.upperCentralSeries ↥P 1 :=
        Subgroup.mem_upperCentralSeries_succ_iff.mp hy ⟨g, hg⟩
      exact ⟨⁅y, (⟨g, hg⟩ : ↥P)⁆, h1, map_commutatorElement P.subtype y ⟨g, hg⟩⟩
    · rintro ⟨hxP, hx⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      refine (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr ?_
      intro g
      rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
      intro hh
      apply Subtype.ext
      change hh.1 * ⁅x, g.1⁆ = ⁅x, g.1⁆ * hh.1
      exact (hZc_central ⁅x, g.1⁆ (hx g.1 g.2) hh.1 hh.2).symm
  have hZ2_t : ∀ x ∈ Z2, t * x * t⁻¹ ∈ Z2 := by
    intro x hx2
    obtain ⟨hxP, hx⟩ := (hmem_Z2 x).mp hx2
    rw [hmem_Z2]
    refine ⟨h.hn x hxP, fun g hg => ?_⟩
    have hg' : t⁻¹ * g * t ∈ P := by
      rw [htinv]
      simpa [htinv] using h.hn g hg
    have hconj : ⁅t * x * t⁻¹, g⁆ = t * ⁅x, t⁻¹ * g * t⁆ * t⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hconj, htZc ⁅x, t⁻¹ * g * t⁆ (hx (t⁻¹ * g * t) hg')]
    exact hx (t⁻¹ * g * t) hg'
  have hex : ∃ x ∈ Z2, x ∉ Zc ∧ ∃ c ∈ Zc, t * x * t⁻¹ = x⁻¹ * c := by
    by_contra hno
    have hnoinv : ∀ x ∈ Z2, (∃ c ∈ Zc, t * x * t⁻¹ = x⁻¹ * c) → x ∈ Zc := by
      intro x hx2 hxinv
      by_contra hxZ
      exact hno ⟨x, hx2, hxZ, hxinv⟩
    have htcent : ∀ x ∈ Z2, t * x * t⁻¹ = x := by
      intro x hx2
      have hxP : x ∈ P := ((hmem_Z2 x).mp hx2).1
      let b : MulAut W := x * (t * x * t⁻¹)⁻¹
      have hb2 : b ∈ Z2 := Z2.mul_mem hx2 (Z2.inv_mem (hZ2_t x hx2))
      have hbinv : t * b * t⁻¹ = b⁻¹ := by
        have hconj2 : MulAut.conj t (MulAut.conj t x) = x := by
          rw [MulAut.conj_apply, MulAut.conj_apply]
          calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
            _ = x := by rw [htinv, htt]; group
        dsimp only [b]
        rw [show (t * x * t⁻¹)⁻¹ = (MulAut.conj t x)⁻¹ by rw [MulAut.conj_apply],
          ← MulAut.conj_apply, map_mul, map_inv, hconj2, mul_inv_rev, inv_inv]
      have hbZc : b ∈ Zc := hnoinv b hb2 ⟨1, Zc.one_mem, by rw [hbinv, mul_one]⟩
      have hb_eq : x * (t * x * t⁻¹)⁻¹ = b := rfl
      have htx_eq : t * x * t⁻¹ = x * b⁻¹ := by
        have h1 : (t * x * t⁻¹)⁻¹ = x⁻¹ * b := by rw [← hb_eq]; group
        calc t * x * t⁻¹ = ((t * x * t⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
          _ = (x⁻¹ * b)⁻¹ := by rw [h1]
          _ = b⁻¹ * x := by group
          _ = x * b⁻¹ := (show Commute b x from hZc_central b hbZc x hxP).inv_left.eq
      have h1 : t * (t * x * t⁻¹) * t⁻¹ = x := by
        calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
          _ = x := by rw [htinv, htt]; group
      have h2 : t * (x * b⁻¹) * t⁻¹ = x * b⁻¹ * b⁻¹ := by
        rw [show t * (x * b⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * b⁻¹ * t⁻¹) by group,
          htx_eq, htZc b⁻¹ (Zc.inv_mem hbZc)]
      rw [htx_eq, h2] at h1
      have hb2pow : b ^ 2 = 1 := by
        have hc1 : b⁻¹ * b⁻¹ = 1 := by
          have hx1 : x * (b⁻¹ * b⁻¹) = x * 1 := by rw [← mul_assoc, h1, mul_one]
          exact mul_left_cancel hx1
        have h2' : b * b = (b⁻¹ * b⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
        rw [pow_two, h2', hc1, inv_one]
      have hb3 : b ^ 3 = 1 := by
        have hdvd : orderOf b ∣ 3 := by
          rw [← hz3]
          exact orderOf_dvd_of_mem_zpowers (hZc_eq ▸ hbZc)
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have hb1 : b = 1 := by
        have h : b = b ^ 3 * (b ^ 2)⁻¹ := by group
        rw [hb2pow, hb3] at h
        simpa using h
      rw [htx_eq, hb1, inv_one, mul_one]
    have hZ2_central_t : ⁅Z2, Subgroup.zpowers t⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rcases w16g_zpowers_eq_one_or_self htt hs with hs1 | hst
      · rw [hs1]; simp
      · rw [hst]
        have h1 : t * x = x * t := by
          calc t * x = (t * x * t⁻¹) * t := by group
            _ = x * t := by rw [htcent x hx]
        exact h1
    have hPZ2_le : ⁅P, Z2⁆ ≤ Zc := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_le]
      intro x hx g hg
      exact ((hmem_Z2 x).mp hx).2 g hg
    have hcomm1 : ⁅⁅P, Z2⁆, Subgroup.zpowers t⁆ = ⊥ := by
      apply le_bot_iff.mp
      calc ⁅⁅P, Z2⁆, Subgroup.zpowers t⁆ ≤ ⁅Zc, Subgroup.zpowers t⁆ :=
            Subgroup.commutator_mono hPZ2_le le_rfl
        _ = ⊥ := by
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
            intro c hc
            rw [Subgroup.mem_centralizer_iff]
            intro s hs
            rcases w16g_zpowers_eq_one_or_self htt hs with hs1 | hst
            · rw [hs1]; simp
            · rw [hst]
              have h1 : t * c = c * t := by
                calc t * c = (t * c * t⁻¹) * t := by group
                  _ = c * t := by rw [htZc c hc]
              exact h1
    have hcomm2 : ⁅⁅Z2, Subgroup.zpowers t⁆, P⁆ = ⊥ := by rw [hZ2_central_t]; simp
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hcomm1 hcomm2
    rw [Subgroup.commutator_comm (Subgroup.zpowers t) P, h.hc] at h3
    have hle : Z2 ≤ Zc := by
      intro x hx
      have hxP : x ∈ P := ((hmem_Z2 x).mp hx).1
      have hxcent : x ∈ Subgroup.centralizer (P : Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact h3) hx
      exact (by
        rw [hZc_eq]
        exact hZP x hxP fun g hg => Subgroup.mem_centralizer_iff.mp hxcent g hg)
    exact hZ2_lt.2 hle
  obtain ⟨x, hx2, hxZc, c, hcZc, htx⟩ := hex
  have hxP : x ∈ P := ((hmem_Z2 x).mp hx2).1
  have hxcomm : ∀ g ∈ P, ⁅x, g⁆ ∈ Zc := ((hmem_Z2 x).mp hx2).2
  obtain ⟨n, hn⟩ := h.hP.exists_orderOf_eq_pow (⟨x, hxP⟩ : ↥P)
  have hxord : orderOf x = 3 ^ n := (Subgroup.orderOf_coe (⟨x, hxP⟩ : ↥P)).trans hn
  have hx3n : x ^ (3 ^ n) = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hexists : ∃ m, 0 < m ∧ x ^ (3 ^ m) ∈ Zc := by
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    rw [pow_succ, pow_mul, hx3n, one_pow]
    exact Zc.one_mem
  let m : ℕ := Nat.find hexists
  have hm_pos : 0 < m := (Nat.find_spec hexists).1
  have hm_mem : x ^ (3 ^ m) ∈ Zc := (Nat.find_spec hexists).2
  have hm_min : ∀ k < m, x ^ (3 ^ k) ∉ Zc := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hxZc
    · exact fun hmem => Nat.find_min hexists hk ⟨hkpos, hmem⟩
  let y : MulAut W := x ^ (3 ^ (m - 1))
  have hyP : y ∈ P := P.pow_mem hxP _
  have hyZc : y ∉ Zc := hm_min (m - 1) (Nat.sub_lt hm_pos (by norm_num))
  have hy3 : y ^ 3 ∈ Zc := by
    have hpow : y ^ 3 = x ^ (3 ^ m) := by
      dsimp only [y]
      rw [← pow_mul, ← pow_succ]
      congr 1
      congr 1
      exact Nat.succ_pred_eq_of_pos hm_pos
    rw [hpow]; exact hm_mem
  have hyZ2 : y ∈ Z2 := by
    have hxZ2 : x ∈ Z2 := hx2
    exact Z2.pow_mem hxZ2 _
  have hy_comm : ∀ g ∈ P, ∃ i : Fin 3, g * y * g⁻¹ = y * z ^ (i : ℕ) := by
    intro g hg
    have h1 : ⁅y, g⁆ ∈ Zc := ((hmem_Z2 y).mp hyZ2).2 g hg
    have h2 : g * y * g⁻¹ * y⁻¹ ∈ Zc := by
      have h3 : ⁅g, y⁆ ∈ Zc := by
        rw [← commutatorElement_inv y g]
        exact Zc.inv_mem h1
      simpa [commutatorElement_def] using h3
    have hcy : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    obtain ⟨i, hi⟩ := hfin (g * y * g⁻¹ * y⁻¹) h2
    refine ⟨i, ?_⟩
    rw [hcy, hi]
    exact hZc_central (z ^ (i : ℕ)) (by rw [hZc_eq]; exact Subgroup.npow_mem_zpowers z i) y hyP
  have hy_inv : ∃ c' ∈ Zc, t * y * t⁻¹ = y⁻¹ * c' := by
    refine ⟨c ^ (3 ^ (m - 1)), Zc.pow_mem hcZc _, ?_⟩
    have hcomm : Commute x⁻¹ c := Commute.inv_left (hZc_central c hcZc x hxP).symm
    dsimp only [y]
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, htx, hcomm.mul_pow, inv_pow]
  refine ⟨y, hyP, ?_, ?_, hy_comm, ?_⟩
  · rw [← hZc_eq]; exact hyZc
  · rw [← hZc_eq]; exact hy3
  · obtain ⟨c', hc'Z, hc'⟩ := hy_inv
    obtain ⟨j, hj⟩ := hfin c' hc'Z
    exact ⟨j, by rw [hc', hj]⟩

private theorem w16g_exists_K (h : Cfg132 t P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z) :
    ∃ k ∈ P, k ∉ Subgroup.zpowers z ∧ k ^ 3 = 1 ∧
      (∀ g ∈ P, ∃ i : Fin 3, g * k * g⁻¹ = k * z ^ (i : ℕ)) ∧
      ∃ j : Fin 3, t * k * t⁻¹ = k⁻¹ * z ^ (j : ℕ) := by
  obtain ⟨x, hxP, hxZ, hx3Z, hxconj, j, hj⟩ := w16g_exists_inverted h hZ hzP hz3 hzc hZP
  have hz3pow : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hz3] at h1
  have htz : t * z * t⁻¹ = z := hZ z hzP hzc
  have hconj : MulAut.conj t z = z := by
    rw [MulAut.conj_apply, htz]
  have ht_zpow : ∀ m : ℤ, t * z ^ m * t⁻¹ = z ^ m := by
    intro m
    calc t * z ^ m * t⁻¹ = MulAut.conj t (z ^ m) := by rw [MulAut.conj_apply]
      _ = (MulAut.conj t z) ^ m := map_zpow (MulAut.conj t) z m
      _ = z ^ m := by rw [hconj]
  have hx3 : x ^ 3 = 1 := by
    have h1 : t * x ^ 3 * t⁻¹ = x ^ 3 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx3Z
      rw [← hm]
      exact ht_zpow m
    have h2 : t * x ^ 3 * t⁻¹ = (x⁻¹ * z ^ (j : ℕ)) ^ 3 := by
      have hc : t * x ^ 3 * t⁻¹ = (t * x * t⁻¹) ^ 3 := by
        rw [← MulAut.conj_apply t (x ^ 3), map_pow (MulAut.conj t) x 3, MulAut.conj_apply]
      rw [hc, hj]
    have h3 : (x⁻¹ * z ^ (j : ℕ)) ^ 3 = (x ^ 3)⁻¹ := by
      have hxz : Commute x z := hzc x hxP
      have hcomm : Commute x⁻¹ (z ^ (j : ℕ)) := (hxz.inv_left).zpow_right (j : ℕ)
      rw [hcomm.mul_pow, inv_pow]
      have hzj : (z ^ (j : ℕ)) ^ 3 = 1 := by
        rw [← pow_mul, show (j : ℕ) * 3 = 3 * (j : ℕ) by ring, pow_mul, hz3pow, one_pow]
      rw [hzj, mul_one]
    have heq : x ^ 3 = (x ^ 3)⁻¹ := h1.symm.trans (h2.trans h3)
    have h6 : x ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add]
      nth_rewrite 2 [heq]
      exact mul_inv_cancel _
    obtain ⟨n, hn⟩ := h.hP.exists_orderOf_eq_pow ⟨x, hxP⟩
    have hxord : orderOf x = 3 ^ n := by rw [← Subgroup.orderOf_mk x hxP]; exact hn
    have hdvd : orderOf x ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr h6
    rw [hxord] at hdvd
    have hn1 : n ≤ 1 := by
      by_contra hnle
      have h2n : 2 ≤ n := by omega
      have h9 : 9 ∣ 3 ^ n := by
        have h22 : (3 : ℕ) ^ 2 = 9 := by norm_num
        rw [← h22]
        exact pow_dvd_pow 3 h2n
      have h96 : 9 ∣ 6 := h9.trans hdvd
      have hle := Nat.le_of_dvd (by norm_num) h96
      norm_num at hle
    have h3dvd : orderOf x ∣ 3 := by
      rw [hxord]
      exact pow_dvd_pow 3 hn1
    exact orderOf_dvd_iff_pow_eq_one.mp h3dvd
  exact ⟨x, hxP, hxZ, hx3, hxconj, j, hj⟩

private theorem w16g_fixV_map_conj (D : Subgroup (MulAut W)) (φ : MulAut W) :
    fixV (D.map (MulAut.conj φ).toMonoidHom) = (fixV D).map φ.toMonoidHom := by
  ext v
  constructor
  · intro hv
    refine ⟨φ⁻¹ v, ?_, by simp⟩
    intro d hd
    have h := hv (φ * d * φ⁻¹) (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
    have h2 : φ (d (φ⁻¹ v)) = φ (φ⁻¹ v) := by
      simpa [MulAut.mul_apply] using h
    exact φ.injective h2
  · rintro ⟨w, hw, rfl⟩ x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    simp [MulAut.conj_apply, MulAut.mul_apply, hw d hd]

private theorem w16g_map_fixV_zpowers (d φ : MulAut W) :
    (fixV (Subgroup.zpowers d)).map φ.toMonoidHom = fixV (Subgroup.zpowers (φ * d * φ⁻¹)) := by
  rw [← w16g_fixV_map_conj (Subgroup.zpowers d) φ]
  congr 1
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

private theorem w16g_zpow_fin_add {A : Type*} [Group A] {z : A} (hz : z ^ 3 = 1) (i j : Fin 3) :
    z ^ ((i + j : Fin 3) : ℕ) = z ^ (i : ℕ) * z ^ (j : ℕ) := by
  rw [Fin.val_add, ← pow_eq_pow_mod ((i : ℕ) + (j : ℕ)) hz, pow_add]

private theorem w16g_zpow_fin_neg {A : Type*} [Group A] {z : A} (hz : z ^ 3 = 1) (i : Fin 3) :
    z ^ ((-i : Fin 3) : ℕ) = (z ^ (i : ℕ))⁻¹ := by
  have hmod : (((-i : Fin 3) : ℕ) + (i : ℕ)) % 3 = 0 := by
    have h1 : ((-i : Fin 3) + i).val = 0 := by rw [neg_add_cancel]; rfl
    rwa [Fin.val_add] at h1
  have hmul : z ^ ((-i : Fin 3) : ℕ) * z ^ (i : ℕ) = 1 := by
    rw [← pow_add, pow_eq_pow_mod _ hz, hmod, pow_zero]
  exact eq_inv_of_mul_eq_one_left hmul

theorem w16h_central_decomp (h : Cfg132 t P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z)
    (hfix : ∀ u : W, z u = u → u = 1) (hrk2 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 2) :
    ∃ U : Fin 3 → Subgroup W, iSupIndep U ∧ (⨆ i, U i) = ⊤ ∧ (∀ i, rk ↥(U i) = 2) ∧
      (∀ i, ∀ u ∈ U i, z u ∈ U i) ∧
      (∀ x ∈ P, ∃ c : Fin 3, ∀ i, ∀ u ∈ U i, x u ∈ U (i + c)) ∧
      (∃ y ∈ P, ∀ i, ∀ u ∈ U i, y u ∈ U (i + 1)) ∧
      (∃ σ : Equiv.Perm (Fin 3), ∀ i, ∀ u ∈ U i, t u ∈ U (σ i)) := by
  classical
  obtain ⟨k, hkP, hkZ, hk3, hkconj, j, hj⟩ := w16g_exists_K h hZ hzP hz3 hzc hZP
  have hz3pow : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hz3] at h1
  have hk_ne1 : k ≠ 1 := fun h1 => hkZ (h1 ▸ Subgroup.one_mem _)
  have hkord : orderOf k = 3 := orderOf_eq_prime hk3 hk_ne1
  have hzk : Commute z k := (hzc k hkP).symm
  let K : Subgroup (MulAut W) := Subgroup.zpowers z ⊔ Subgroup.zpowers k
  have hK : CFSG.Open.IsElemAbelian 3 K :=
    w16g_isElemAbelian_sup_zpowers hz3pow hk3 hzk
  have hKcard : Nat.card K = 3 ^ 2 :=
    w16g_card_sup_zpowers Nat.prime_three hz3 hkord hzk hkZ
  have hfixbot : fixV (Subgroup.zpowers z) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    exact hfix u ((mem_fixV.mp hu) z (Subgroup.mem_zpowers z))
  have hcommz : commSub ⊤ (Subgroup.zpowers z) = ⊤ := by
    haveI : Finite (Subgroup.zpowers z) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hz3]; norm_num)
    have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
      rw [Nat.card_zpowers, hz3]; norm_num
    have hcompl := isCompl_fixV_commV_of_odd (Subgroup.zpowers z) hodd h.hW
    have hcv : commV (Subgroup.zpowers z) = ⊤ := by
      simpa [hfixbot] using hcompl.2
    rwa [commV_eq_commSub] at hcv
  have hV : commSub ⊤ K = ⊤ := by
    have hle : commSub ⊤ (Subgroup.zpowers z) ≤ commSub ⊤ K :=
      commSub_mono le_rfl le_sup_left
    rw [hcommz] at hle
    exact eq_top_iff.mpr hle
  have hhyp := w16g_hyperplanes_sup_zpowers Nat.prime_three hz3 hkord hzk hkZ
  obtain ⟨hindFull, hsupFull⟩ :=
    fixV_hyperplane_decomposition h.hW Nat.prime_three (by norm_num) K hK hV
  let U : Fin 3 → Subgroup W := fun i => fixV (Subgroup.zpowers (k * z ^ (i : ℕ)))
  have hmem_hyper : ∀ i : Fin 3, Subgroup.zpowers (k * z ^ (i : ℕ)) ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 K := by
    intro i
    rw [hhyp]
    exact Or.inr ⟨i, rfl⟩
  let f : Fin 3 → CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 3 K :=
    fun i => ⟨Subgroup.zpowers (k * z ^ (i : ℕ)), hmem_hyper i⟩
  have hf_inj : Function.Injective f := fun i i' hii =>
    (w16g_zpowers_mul_pow_injective Nat.prime_three hz3 hkord hzk hkZ).1
      (congrArg Subtype.val hii)
  have hindU : iSupIndep U := hindFull.comp hf_inj
  have hsupU : (⨆ i, U i) = ⊤ := by
    have h2 : ⊤ ≤ ⨆ i, U i := by
      rw [← hsupFull]
      refine iSup_le fun D => ?_
      have hD : D.1 ∈ ({Subgroup.zpowers z} ∪
          Set.range (fun i : Fin 3 => Subgroup.zpowers (k * z ^ (i:ℕ)))) := by
        rw [← hhyp]
        exact D.2
      rcases hD with hD | ⟨i, hDi⟩
      · rw [Set.mem_singleton_iff] at hD
        change fixV D.1 ≤ ⨆ i, U i
        rw [hD, hfixbot]
        exact bot_le
      · change fixV D.1 ≤ ⨆ i, U i
        rw [← hDi]
        exact le_iSup U i
    exact top_le_iff.mp h2
  have hzU : ∀ i, ∀ u ∈ U i, z u ∈ U i := by
    intro i u hu
    have hzk' : z * k = k * z := (hzc k hkP).symm
    have hzcomm : z * (k * z ^ (i : ℕ)) * z⁻¹ = k * z ^ (i : ℕ) := by
      rw [show z * (k * z ^ (i:ℕ)) * z⁻¹
          = (z * k * z⁻¹) * (z * z ^ (i:ℕ) * z⁻¹) by group]
      rw [show z * k * z⁻¹ = k by rw [hzk']; group,
        show z * z ^ (i:ℕ) * z⁻¹ = z ^ (i:ℕ) by group]
    have hmem : z u ∈ (fixV (Subgroup.zpowers (k * z ^ (i:ℕ)))).map z.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rw [w16g_map_fixV_zpowers (k * z ^ (i:ℕ)) z, hzcomm] at hmem
    exact hmem
  have hmap : ∀ (x : MulAut W) (_ : x ∈ P) (c : Fin 3),
      x * k * x⁻¹ = k * z ^ (c : ℕ) → ∀ i, ∀ u ∈ U i, x u ∈ U (i + c) := by
    intro x hxP c hc i u hu
    have hxz : x * z * x⁻¹ = z := by
      rw [hzc x hxP]
      group
    have hxzi : x * z ^ (i : ℕ) * x⁻¹ = z ^ (i : ℕ) := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hxz]
    have hconj : x * (k * z ^ (i : ℕ)) * x⁻¹ = k * z ^ ((i + c : Fin 3) : ℕ) := by
      have h1 : x * (k * z ^ (i:ℕ)) * x⁻¹
          = (x * k * x⁻¹) * (x * z ^ (i:ℕ) * x⁻¹) := by group
      rw [h1, hc, hxzi]
      rw [mul_assoc, show z ^ (c:ℕ) * z ^ (i:ℕ) = z ^ ((i+c : Fin 3):ℕ) by
        rw [w16g_zpow_fin_add hz3pow i c, ← pow_add, add_comm, pow_add]]
    have hmem : x u ∈ (fixV (Subgroup.zpowers (k * z ^ (i:ℕ)))).map x.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rw [w16g_map_fixV_zpowers (k * z ^ (i:ℕ)) x, hconj] at hmem
    exact hmem
  have hPU : ∀ x ∈ P, ∃ c : Fin 3, ∀ i, ∀ u ∈ U i, x u ∈ U (i + c) := by
    intro x hx
    obtain ⟨c, hc⟩ := hkconj x hx
    exact ⟨c, hmap x hx c hc⟩
  have hyU : ∃ y ∈ P, ∀ i, ∀ u ∈ U i, y u ∈ U (i + 1) := by
    let c : ↥P → Fin 3 := fun x => Classical.choose (hkconj x x.2)
    have hc : ∀ x : ↥P, (x : MulAut W) * k * (x : MulAut W)⁻¹ = k * z ^ ((c x : ℕ)) :=
      fun x => Classical.choose_spec (hkconj x x.2)
    have hex : ∃ x : ↥P, c x ≠ 0 := by
      by_contra hcontra
      push Not at hcontra
      have hkcentral : ∀ y ∈ P, y * k = k * y := by
        intro y hy
        have h1 := hc ⟨y, hy⟩
        rw [hcontra ⟨y, hy⟩, Fin.val_zero, pow_zero, mul_one] at h1
        calc y * k = (y * k * y⁻¹) * y := by group
          _ = k * y := by rw [h1]
      exact hkZ (hZP k hkP hkcentral)
    obtain ⟨x0, hx0⟩ := hex
    have h1or2 : c x0 = 1 ∨ c x0 = 2 := by
      obtain ⟨n, hn⟩ : ∃ n : Fin 3, c x0 = n := ⟨c x0, rfl⟩
      fin_cases n
      · exact absurd hn hx0
      · exact Or.inl hn
      · exact Or.inr hn
    rcases h1or2 with hc1 | hc2
    · refine ⟨(x0 : MulAut W), x0.2, fun i u hu => ?_⟩
      have hc' : (x0 : MulAut W) * k * (x0 : MulAut W)⁻¹ = k * z ^ ((1 : Fin 3) : ℕ) := by
        rw [hc x0, hc1]
      exact hmap (x0 : MulAut W) x0.2 1 hc' i u hu
    · refine ⟨(x0 : MulAut W) ^ 2, P.pow_mem x0.2 2, fun i u hu => ?_⟩
      have hc0 : (x0 : MulAut W) * k * (x0 : MulAut W)⁻¹ = k * z ^ (2 : ℕ) := by
        rw [hc x0, hc2]
        norm_num
      have hxz : (x0 : MulAut W) * z * (x0 : MulAut W)⁻¹ = z := by
        rw [hzc x0 x0.2]
        group
      have hxzi : (x0 : MulAut W) * z ^ (2:ℕ) * (x0 : MulAut W)⁻¹ = z ^ (2:ℕ) := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hxz]
      have hc' : (x0 : MulAut W) ^ 2 * k * ((x0 : MulAut W) ^ 2)⁻¹
          = k * z ^ ((1 : Fin 3) : ℕ) := by
        rw [show (x0 : MulAut W) ^ 2 * k * ((x0 : MulAut W) ^ 2)⁻¹
            = (x0 : MulAut W) * ((x0 : MulAut W) * k * (x0 : MulAut W)⁻¹)
              * (x0 : MulAut W)⁻¹ by rw [pow_two]; group, hc0]
        rw [show (x0 : MulAut W) * (k * z ^ (2:ℕ)) * (x0 : MulAut W)⁻¹
            = ((x0 : MulAut W) * k * (x0 : MulAut W)⁻¹)
              * ((x0 : MulAut W) * z ^ (2:ℕ) * (x0 : MulAut W)⁻¹) by group,
          hc0, hxzi, mul_assoc, ← pow_add]
        rw [show (2:ℕ) + 2 = 4 by norm_num, show (4:ℕ) = 3 + 1 by norm_num, pow_add,
          hz3pow, one_mul]
        norm_num
      exact hmap ((x0 : MulAut W) ^ 2) (P.pow_mem x0.2 2) 1 hc' i u hu
  have hσ_ne : ∃ i : Fin 3, -(j + i) ≠ i := by
    fin_cases j
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  let σfun : Fin 3 → Fin 3 := fun i => -(j + i)
  have hσbij : Function.Bijective σfun := by
    constructor
    · intro a b hab
      exact add_left_cancel (neg_inj.mp hab)
    · intro b
      refine ⟨-(j + b), ?_⟩
      change -(j + (-(j + b))) = b
      rw [show j + (-(j + b)) = -b by abel, neg_neg]
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective σfun hσbij
  have hσi : ∀ i, σ i = -(j + i) := fun i => rfl
  have hσU : ∀ i, ∀ u ∈ U i, t u ∈ U (σ i) := by
    have htz : t * z * t⁻¹ = z := hZ z hzP hzc
    intro i u hu
    have htzpow : t * z ^ (i:ℕ) * t⁻¹ = z ^ (i:ℕ) := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, htz]
    have hconj : t * (k * z ^ (i:ℕ)) * t⁻¹ = k⁻¹ * z ^ ((j+i : Fin 3):ℕ) := by
      rw [show t * (k * z ^ (i:ℕ)) * t⁻¹
          = (t * k * t⁻¹) * (t * z ^ (i:ℕ) * t⁻¹) by group, hj, htzpow, mul_assoc,
        w16g_zpow_fin_add hz3pow j i]
    have hmem : t u ∈ (fixV (Subgroup.zpowers (k * z ^ (i:ℕ)))).map t.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rw [w16g_map_fixV_zpowers (k * z ^ (i:ℕ)) t, hconj] at hmem
    have hgen : k⁻¹ * z ^ ((j+i : Fin 3):ℕ) = (k * z ^ ((σ i):ℕ))⁻¹ := by
      rw [hσi i]
      rw [show (k * z ^ ((-(j+i) : Fin 3):ℕ))⁻¹
          = (z ^ ((-(j+i) : Fin 3):ℕ))⁻¹ * k⁻¹ by group,
        w16g_zpow_fin_neg hz3pow (j+i)]
      exact (hzk.symm.inv_left.zpow_right ((j+i : Fin 3) : ℕ)).eq
    rw [hgen, Subgroup.zpowers_inv] at hmem
    exact hmem
  have htU : ∃ σ : Equiv.Perm (Fin 3), ∀ i, ∀ u ∈ U i, t u ∈ U (σ i) := ⟨σ, hσU⟩
  obtain ⟨y, hyP, hyU'⟩ := hyU
  have hcard_le : ∀ i, Nat.card ↥(U i) ≤ Nat.card ↥(U (i + 1)) := by
    intro i
    refine Nat.card_le_card_of_injective
      (fun u : ↥(U i) => (⟨y u.1, hyU' i u.1 u.2⟩ : ↥(U (i + 1)))) ?_
    intro u v huv
    exact Subtype.ext (y.injective (Subtype.ext_iff.mp huv))
  have h01 := hcard_le 0
  have h12 := hcard_le 1
  have h20 := hcard_le 2
  have hcard_eq0 : ∀ i, Nat.card ↥(U i) = Nat.card ↥(U 0) := by
    intro i
    fin_cases i
    · rfl
    · exact le_antisymm (le_trans h12 h20) h01
    · exact le_antisymm h20 (le_trans h01 h12)
  have hrk_eq0 : ∀ i, rk ↥(U i) = rk ↥(U 0) := fun i => by
    unfold rk
    rw [hcard_eq0 i]
  have hEven : ∀ i, Even (rk ↥(U i)) := fun i =>
    w16h_even_rk_of_fixedFree h.hW hz3pow (hzU i) (fun u _ hu => hfix u hu)
  obtain ⟨i₀, hi₀⟩ := hσ_ne
  have hσi₀ : σ i₀ = -(j + i₀) := hσi i₀
  have hne_i₀ : σ i₀ ≠ i₀ := by rw [hσi₀]; exact hi₀
  have hdisj : U i₀ ⊓ U (σ i₀) = ⊥ :=
    (hindU.pairwiseDisjoint (Ne.symm hne_i₀)).eq_bot
  have hbound : rk ↥(U i₀) ≤ 2 := by
    let φ : ↥(U i₀) →* W :=
      { toFun := fun u => u.1 * t u.1
        map_one' := by simp
        map_mul' := by
          intro u v
          simp only [Subgroup.coe_mul, map_mul]
          ac_rfl }
    have hker : φ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      change u.1 * t u.1 = 1 at hu
      have ht_inv : t u.1 = u.1 := by
        have h2 : t u.1 = u.1⁻¹ := eq_inv_of_mul_eq_one_right hu
        have huu : u.1 * u.1 = 1 := by rw [← pow_two]; exact h.hW u.1
        rw [h2, inv_eq_of_mul_eq_one_right huu]
      apply Subtype.ext
      have h3 : u.1 ∈ U i₀ ⊓ U (σ i₀) :=
        ⟨u.2, by rw [← ht_inv]; exact hσU i₀ u.1 u.2⟩
      rw [hdisj, Subgroup.mem_bot] at h3
      exact h3
    have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
    have hrange : φ.range ≤ commSub ⊤ (Subgroup.zpowers t) := by
      rintro w ⟨u, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨t, Subgroup.mem_zpowers t, u.1, Subgroup.mem_top _, ?_⟩
      show t u.1 * u.1⁻¹ = u.1 * t u.1
      have huu : u.1 * u.1 = 1 := by rw [← pow_two]; exact h.hW u.1
      rw [inv_eq_of_mul_eq_one_right huu]
      exact mul_comm _ _
    have hcardφ : Nat.card ↥(U i₀) = Nat.card ↥(φ.range) :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    have hdvd : Nat.card ↥(φ.range) ∣ Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      Subgroup.card_dvd_of_le hrange
    have hle : rk ↥(U i₀) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
      unfold rk
      rw [hcardφ]
      exact padicValNat_two_le_of_dvd (card_subgroup_pos _).ne' hdvd
    rwa [hrk2] at hle
  have ht_ne_one : t ≠ 1 := by
    intro h1
    have h2 : orderOf t = 1 := by rw [h1, orderOf_one]
    rw [h.ht] at h2
    norm_num at h2
  have htop_ne_bot : (⊤ : Subgroup W) ≠ ⊥ := by
    intro htop
    apply ht_ne_one
    ext w
    have hw : w = 1 := by
      have : w ∈ (⊥ : Subgroup W) := by rw [← htop]; exact Subgroup.mem_top w
      rwa [Subgroup.mem_bot] at this
    rw [hw, map_one, MulAut.one_apply]
  have hU0_ne : U 0 ≠ ⊥ := by
    intro hbot
    have hall : ∀ i, U i = ⊥ := by
      intro i
      have h1 : Nat.card ↥(U i) = 1 := by
        rw [hcard_eq0 i, hbot, Subgroup.card_bot]
      exact (Subgroup.card_eq_one).mp h1
    have hsupbot : (⨆ i, U i) = ⊥ := by
      rw [show (⨆ i, U i) = ⨆ _ : Fin 3, (⊥ : Subgroup W) from iSup_congr hall]
      simp
    rw [hsupU] at hsupbot
    exact htop_ne_bot hsupbot
  have hrkU : ∀ i, rk ↥(U i) = 2 := by
    have hpos : 0 < rk ↥(U i₀) := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      apply hU0_ne
      have hUi0 : U i₀ = ⊥ := (rk_eq_zero_iff h.hW).mp h0
      have hc : Nat.card ↥(U 0) = 1 := by
        rw [← hcard_eq0 i₀, hUi0, Subgroup.card_bot]
      exact (Subgroup.card_eq_one).mp hc
    have h2 : rk ↥(U i₀) = 2 := by
      obtain ⟨m, hm⟩ := hEven i₀
      omega
    have h2' : rk ↥(U 0) = 2 := by rw [← hrk_eq0 i₀]; exact h2
    intro i
    rw [hrk_eq0 i, h2']
  exact ⟨U, hindU, hsupU, hrkU, hzU, hPU, ⟨y, hyP, hyU'⟩, htU⟩

end CFSG.LocalAnalysis.WeakClosure81
