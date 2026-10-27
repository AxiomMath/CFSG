module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private def w16g_C (p : ℕ) (A : Subgroup (MulAut W)) (L : Subgroup (MulAut W)) :
    Subgroup (MulAut W) where
  carrier := {c | c ∈ pCoreOf p A ∧ ∀ w : W, c w * w⁻¹ ∈ commSub ⊤ L}
  one_mem' := ⟨(pCoreOf p A).one_mem, fun w => by simp⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨(pCoreOf p A).mul_mem ha.1 hb.1, fun w => ?_⟩
    have h1 := ha.2 (b w)
    have h2 := hb.2 w
    have heq : (a * b) w * w⁻¹ = (a (b w) * (b w)⁻¹) * (b w * w⁻¹) := by
      change a (b w) * w⁻¹ = (a (b w) * (b w)⁻¹) * (b w * w⁻¹)
      group
    rw [heq]
    exact (commSub ⊤ L).mul_mem h1 h2
  inv_mem' := by
    intro a ha
    refine ⟨(pCoreOf p A).inv_mem ha.1, fun w => ?_⟩
    have h1 := (commSub ⊤ L).inv_mem (ha.2 (a⁻¹ w))
    have heq : (a⁻¹) w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by
      change a.symm w * w⁻¹ = (a (a.symm w) * (a.symm w)⁻¹)⁻¹
      simp [mul_inv_rev]
    rw [heq]
    exact h1

private theorem w16g_le_C {p : ℕ} {L : Subgroup (MulAut W)} (hLO : L ≤ pCoreOf p A) :
    L ≤ w16g_C p A L :=
  fun _ hl => ⟨hLO hl, fun w => Subgroup.subset_closure ⟨_, hl, w, Subgroup.mem_top w, rfl⟩⟩

private theorem w16g_C_le_pCore (p : ℕ) (A L : Subgroup (MulAut W)) :
    w16g_C p A L ≤ pCoreOf p A := fun _ hc => hc.1

private theorem w16g_C_isPGroup {p : ℕ} {L : Subgroup (MulAut W)} (hLO : L ≤ pCoreOf p A) :
    IsPGroup p ↥(w16g_C p A L) :=
  (s13_pCore_facts A p).2.2.to_le (w16g_C_le_pCore p A L)

private theorem w16g_C_le_stabSub (p : ℕ) (A L : Subgroup (MulAut W)) :
    w16g_C p A L ≤ stabSub (commSub ⊤ L) := by
  intro c hc
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : u * (c u)⁻¹ ∈ commSub ⊤ L := by
      have := (commSub ⊤ L).inv_mem (hc.2 u)
      simpa [mul_inv_rev] using this
    have := (commSub ⊤ L).mul_mem h1 hu
    simpa [mul_assoc] using this
  · intro hu
    have := (commSub ⊤ L).mul_mem (hc.2 u) hu
    simpa [mul_assoc] using this

private theorem w16g_C_inf_centSub_eq_bot {p : ℕ} (hW : ∀ w : W, w * w = 1) (hodd : Odd p)
    {L : Subgroup (MulAut W)} (hLO : L ≤ pCoreOf p A) :
    w16g_C p A L ⊓ centSub (commSub ⊤ L) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  have hcC : c ∈ w16g_C p A L := hc.1
  have hcW : ∀ u ∈ commSub ⊤ L, c u = u := mem_centSub.mp hc.2
  have hc2 : c ^ 2 = 1 := by
    ext w
    have hd : c w * w⁻¹ ∈ commSub ⊤ L := hcC.2 w
    have hcd : c (c w * w⁻¹) = c w * w⁻¹ := hcW _ hd
    have hdw : c w * w⁻¹ * w = c w := by group
    calc (c ^ 2) w = c (c w) := by rw [pow_two]; rfl
      _ = c ((c w * w⁻¹) * w) := by rw [hdw]
      _ = c (c w * w⁻¹) * c w := map_mul c _ _
      _ = (c w * w⁻¹) * c w := by rw [hcd]
      _ = (c w * w⁻¹) * ((c w * w⁻¹) * w) := by rw [hdw]
      _ = ((c w * w⁻¹) * (c w * w⁻¹)) * w := by rw [← mul_assoc]
      _ = 1 * w := by rw [hW (c w * w⁻¹)]
      _ = w := one_mul w
  have hCgrp : IsPGroup p ↥(w16g_C p A L) := w16g_C_isPGroup hLO
  obtain ⟨k, hk⟩ := hCgrp ⟨c, hcC⟩
  have hcpow : c ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdiv : orderOf c ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hcpow
  have hoddord : Odd (orderOf c) := (hodd.pow).of_dvd_nat hdiv
  have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hc2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h)
  · rw [h] at hoddord
    norm_num at hoddord

private theorem w16g_C_embed_dvd (p : ℕ) (A L : Subgroup (MulAut W))
    (hW : ∀ w : W, w * w = 1) (hodd : Odd p) (hLO : L ≤ pCoreOf p A) :
    Nat.card ↥(w16g_C p A L) ∣ Nat.card (MulAut ↥(commSub ⊤ L)) := by
  have hstab := w16g_C_le_stabSub p A L
  have hinf := w16g_C_inf_centSub_eq_bot hW hodd hLO
  have hcard := card_autSub_mul (A := w16g_C p A L) (U := commSub ⊤ L) hstab
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

private noncomputable def w16g_autSubEquiv {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hX : X ≤ stabSub U) (hinf : X ⊓ centSub U = ⊥) : ↥X ≃* ↥(autSub X U) := by
  let f : ↥X →* MulAut U := (resHom U).comp (Subgroup.inclusion hX)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxcent : (x : MulAut W) ∈ centSub U := by
        rw [mem_centSub]
        intro u hu
        have h1 := congrArg (fun φ : MulAut U => (φ ⟨u, hu⟩ : W)) hx
        have h2 : ((f x) ⟨u, hu⟩ : W) = (x : MulAut W) u := rfl
        rw [h2] at h1
        simpa using h1
      have hmem : (x : MulAut W) ∈ X ⊓ centSub U := ⟨x.2, hxcent⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hx
      rw [hx, map_one]
  have hrange : f.range = autSub X U := by
    rw [show f = (resHom U).comp (Subgroup.inclusion hX) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range hX]
    rfl
  exact (MonoidHom.ofInjective (f := f) hf).trans (MulEquiv.subgroupCongr hrange)

private theorem w16g_card_mulAut_eq_card_GL (hW : ∀ w : W, w ^ 2 = 1) :
    Nat.card (MulAut W) =
      Nat.card (GL (Fin (rk ↥(⊤ : Subgroup W))) (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardW : Nat.card W = 2 ^ rk ↥(⊤ : Subgroup W) := by
    rw [← Subgroup.card_top]
    exact card_eq_two_pow hW ⊤
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) hW hcardW
  exact CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e

private theorem w16g_card_mulAut_four {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk ↥(⊤ : Subgroup W) = 4) :
    Nat.card (MulAut W) = 20160 := by
  rw [w16g_card_mulAut_eq_card_GL hW, hrk,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 4]
  norm_num [Fin.prod_univ_succ]

private theorem w16g_card_mulAut_six {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk ↥(⊤ : Subgroup W) = 6) :
    Nat.card (MulAut W) = 20158709760 := by
  rw [w16g_card_mulAut_eq_card_GL hW, hrk,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) 6]
  norm_num [Fin.prod_univ_succ]

private theorem w16g_isZ3WrZ3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsZ3WrZ3 X) : IsZ3WrZ3 Y := by
  obtain ⟨hcard, z, b, hz, hcomm, hb, hconj, hgen⟩ := h
  refine ⟨?_, fun i => e (z i), e b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, hcard]
  · intro i; rw [← map_pow, hz i, map_one]
  · intro i j; exact (hcomm i j).map e
  · rw [← map_pow, hb, map_one]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hconj i]
  · have himg : Set.range (fun i => e (z i)) ∪ {e b} =
        (e : X →* Y) '' (Set.range z ∪ {b}) := by
      ext y
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨z i, Or.inl ⟨i, rfl⟩, rfl⟩
        · exact ⟨b, Or.inr rfl, rfl⟩
      · rintro ⟨x, hx | rfl, rfl⟩
        · obtain ⟨i, rfl⟩ := hx; exact Or.inl ⟨i, rfl⟩
        · exact Or.inr rfl
    have hmap := MonoidHom.map_closure (e : X →* Y) (Set.range z ∪ {b})
    rw [hgen, Subgroup.map_top_of_surjective _ e.surjective] at hmap
    rw [← himg] at hmap
    exact hmap.symm

private theorem w16g_isPOnePlusTwo_of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPOnePlusTwo p X) : IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · haveI : CFSG.IsExtraspecial p X := hX
    exact isExtraspecial_of_mulEquiv e.symm
  · rw [← Nat.card_congr e.toEquiv, hc]
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hp x, map_one]

private theorem w16g_extraspecial_unique_of_isZ3WrZ3 {X : Type} [Group X] (hX : IsZ3WrZ3 X) :
    ∀ Q Q' : Subgroup X, IsPOnePlusTwo 3 ↥Q → IsPOnePlusTwo 3 ↥Q' → Q = Q' := by
  obtain ⟨e⟩ := W16GTwoCB.w16g_nonempty_mulEquiv_zwr_one hX
  obtain ⟨M, -, huniq, -⟩ := W16GTwoCB.w16g_wr_unique_of_mulEquiv e
  intro Q Q' hQ hQ'
  rw [huniq Q hQ, huniq Q' hQ']

private theorem w16g_conj_le_C {p : ℕ} {L : Subgroup (MulAut W)} (hLO : L ≤ pCoreOf p A)
    {g : MulAut W} (hgA : g ∈ A)
    (hgW : (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L) :
    L.map (MulAut.conj g).toMonoidHom ≤ w16g_C p A L := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  refine ⟨?_, fun w => ?_⟩
  · simpa [MulAut.conj_apply] using (s13_pCore_facts A p).1 g hgA l (hLO hl)
  · have hgen : l (g⁻¹ w) * (g⁻¹ w)⁻¹ ∈ commSub ⊤ L :=
      Subgroup.subset_closure ⟨_, hl, g⁻¹ w, Subgroup.mem_top _, rfl⟩
    have hmap : g (l (g⁻¹ w) * (g⁻¹ w)⁻¹) ∈ commSub ⊤ L := by
      rw [← hgW]
      exact Subgroup.mem_map.mpr ⟨_, hgen, rfl⟩
    have heq : ((MulAut.conj g).toMonoidHom l) w * w⁻¹ =
        g (l (g⁻¹ w) * (g⁻¹ w)⁻¹) := by
      change (MulAut.conj g l) w * w⁻¹ = g (l (g⁻¹ w) * (g⁻¹ w)⁻¹)
      rw [MulAut.conj_apply]
      change g (l (g⁻¹ w)) * w⁻¹ = g (l (g⁻¹ w) * (g⁻¹ w)⁻¹)
      rw [show w⁻¹ = g ((g⁻¹ w)⁻¹) by simp, ← map_mul]
    rw [heq]
    exact hmap

theorem s13_U3_five (h : Cfg133 A t 5) {L : Subgroup (MulAut W)} (hLO : L ≤ pCoreOf 5 A)
    (hL5 : IsCyclicOrd ↥L 5) (hLr : rk ↥(commSub ⊤ L) = 4) :
    ∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L →
      L.map (MulAut.conj g).toMonoidHom = L := by
  intro g hgA hgW
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hW2 : ∀ w : W, w * w = 1 := h.hW
  have hW'2 : ∀ w : ↥(commSub ⊤ L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa [pow_two] using h.hW (w : W))
  have hrk4 : rk ↥(⊤ : Subgroup ↥(commSub ⊤ L)) = 4 := by
    rw [rk_top]
    exact hLr
  have hLC : L ≤ w16g_C 5 A L := w16g_le_C hLO
  have hCgrp : IsPGroup 5 ↥(w16g_C 5 A L) := w16g_C_isPGroup hLO
  have hLcard : Nat.card ↥L = 5 := hL5.2
  have hdvd : Nat.card ↥(w16g_C 5 A L) ∣ 20160 := by
    rw [← w16g_card_mulAut_four hW'2 hrk4]
    exact w16g_C_embed_dvd 5 A L hW2 (by norm_num) hLO
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hCgrp
  have hk1 : k ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ k := by omega
    have h25 : 25 ∣ 20160 := by
      have h5k : 5 ^ k ∣ 20160 := by rw [← hk]; exact hdvd
      simpa using (pow_dvd_pow 5 h2).trans h5k
    norm_num at h25
  have hkpos : 1 ≤ k := by
    have hdvd5 : 5 ∣ 5 ^ k := by
      have hsub := Subgroup.card_dvd_of_le hLC
      rw [hLcard, hk] at hsub
      exact hsub
    by_contra hcon
    have hk0 : k = 0 := by omega
    rw [hk0] at hdvd5
    norm_num at hdvd5
  have hkeq : k = 1 := by omega
  have hCcard : Nat.card ↥(w16g_C 5 A L) = 5 := by rw [hk, hkeq, pow_one]
  have hLCeq : L = w16g_C 5 A L :=
    Subgroup.eq_of_le_of_card_ge hLC (by rw [hLcard, hCcard])
  have hgL_le_C : L.map (MulAut.conj g).toMonoidHom ≤ w16g_C 5 A L :=
    w16g_conj_le_C hLO hgA hgW
  have hcardmap : Nat.card ↥(L.map (MulAut.conj g).toMonoidHom) = 5 := by
    rw [Subgroup.card_map_of_injective (K := L) (MulAut.conj g).injective, hLcard]
  have hfin : L.map (MulAut.conj g).toMonoidHom = w16g_C 5 A L :=
    Subgroup.eq_of_le_of_card_ge hgL_le_C (by rw [hcardmap, hCcard])
  rwa [hLCeq.symm] at hfin

theorem s13_U3_three (h : Cfg133 A t 3) {L : Subgroup (MulAut W)} (hLO : L ≤ pCoreOf 3 A)
    (hLe : IsPOnePlusTwo 3 ↥L) (hLr : rk ↥(commSub ⊤ L) = 6) :
    ∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L →
      L.map (MulAut.conj g).toMonoidHom = L := by
  intro g hgA hgW
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW2 : ∀ w : W, w * w = 1 := h.hW
  have hW'2 : ∀ w : ↥(commSub ⊤ L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa [pow_two] using h.hW (w : W))
  have hrk6 : rk ↥(⊤ : Subgroup ↥(commSub ⊤ L)) = 6 := by
    rw [rk_top]
    exact hLr
  have hLC : L ≤ w16g_C 3 A L := w16g_le_C hLO
  have hCgrp : IsPGroup 3 ↥(w16g_C 3 A L) := w16g_C_isPGroup hLO
  have hLcard : Nat.card ↥L = 27 := by rw [hLe.2.1]; norm_num
  have hdvd : Nat.card ↥(w16g_C 3 A L) ∣ 20158709760 := by
    rw [← w16g_card_mulAut_six hW'2 hrk6]
    exact w16g_C_embed_dvd 3 A L hW2 (by norm_num) hLO
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hCgrp
  have hk4 : k ≤ 4 := by
    by_contra hcon
    have h5 : 5 ≤ k := by omega
    have h243 : 3 ^ 5 ∣ 20158709760 := by
      have h3k : 3 ^ k ∣ 20158709760 := by rw [← hk]; exact hdvd
      exact (pow_dvd_pow 3 h5).trans h3k
    norm_num at h243
  have hk3 : 3 ≤ k := by
    have hdvd27 : 27 ∣ Nat.card ↥(w16g_C 3 A L) := by
      have hsub := Subgroup.card_dvd_of_le hLC
      rwa [hLcard] at hsub
    rw [hk] at hdvd27
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp (by simpa using hdvd27)
  have hkcase : k = 3 ∨ k = 4 := by omega
  rcases hkcase with hk3eq | hk4eq
  · have hCcard : Nat.card ↥(w16g_C 3 A L) = 27 := by rw [hk, hk3eq]; norm_num
    have hLCeq : L = w16g_C 3 A L :=
      Subgroup.eq_of_le_of_card_ge hLC (by rw [hLcard, hCcard])
    have hgL_le_C : L.map (MulAut.conj g).toMonoidHom ≤ w16g_C 3 A L :=
      w16g_conj_le_C hLO hgA hgW
    have hcardmap : Nat.card ↥(L.map (MulAut.conj g).toMonoidHom) = 27 := by
      rw [Subgroup.card_map_of_injective (K := L) (MulAut.conj g).injective, hLcard]
    have hfin : L.map (MulAut.conj g).toMonoidHom = w16g_C 3 A L :=
      Subgroup.eq_of_le_of_card_ge hgL_le_C (by rw [hcardmap, hCcard])
    rwa [hLCeq.symm] at hfin
  · have hCcard : Nat.card ↥(w16g_C 3 A L) = 81 := by rw [hk, hk4eq]; norm_num
    have hCstab : w16g_C 3 A L ≤ stabSub (commSub ⊤ L) := w16g_C_le_stabSub 3 A L
    have hCinf : w16g_C 3 A L ⊓ centSub (commSub ⊤ L) = ⊥ :=
      w16g_C_inf_centSub_eq_bot hW2 (by norm_num) hLO
    have eC : ↥(w16g_C 3 A L) ≃* ↥(autSub (w16g_C 3 A L) (commSub ⊤ L)) :=
      w16g_autSubEquiv hCstab hCinf
    have hCbarcard : Nat.card ↥(autSub (w16g_C 3 A L) (commSub ⊤ L)) = 81 := by
      rw [← Nat.card_congr eC.toEquiv]
      exact hCcard
    have hCbargrp : IsPGroup 3 ↥(autSub (w16g_C 3 A L) (commSub ⊤ L)) :=
      hCgrp.of_equiv eC
    have hwr : IsZ3WrZ3 ↥(autSub (w16g_C 3 A L) (commSub ⊤ L)) :=
      w16h_isZ3WrZ3_of_card_81 hW'2 hrk6 hCbargrp hCbarcard
    have hIsZ3 : IsZ3WrZ3 ↥(w16g_C 3 A L) :=
      w16g_isZ3WrZ3_of_mulEquiv eC.symm hwr
    have hgL_le_C : L.map (MulAut.conj g).toMonoidHom ≤ w16g_C 3 A L :=
      w16g_conj_le_C hLO hgA hgW
    have hLsub : IsPOnePlusTwo 3 ↥(L.subgroupOf (w16g_C 3 A L)) :=
      w16g_isPOnePlusTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hLe
    have hMsub :
        IsPOnePlusTwo 3 ↥((L.map (MulAut.conj g).toMonoidHom).subgroupOf (w16g_C 3 A L)) := by
      have hMext : IsPOnePlusTwo 3 ↥(L.map (MulAut.conj g).toMonoidHom) :=
        w16g_isPOnePlusTwo_of_mulEquiv
          (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective) hLe
      exact w16g_isPOnePlusTwo_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hgL_le_C).symm hMext
    have huniq := w16g_extraspecial_unique_of_isZ3WrZ3 hIsZ3
    have h1 : L.subgroupOf (w16g_C 3 A L) =
        (L.map (MulAut.conj g).toMonoidHom).subgroupOf (w16g_C 3 A L) :=
      huniq _ _ hLsub hMsub
    have h2 := congrArg (fun H : Subgroup ↥(w16g_C 3 A L) => H.map (w16g_C 3 A L).subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hLC,
      Subgroup.map_subgroupOf_eq_of_le hgL_le_C] at h2
    exact h2.symm

end CFSG.LocalAnalysis.WeakClosure81
