module

public import CFSG.Quasithin.Background.B5NonB

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

section Reduced

variable {V : Type} [CommGroup V] [Finite V]

structure Red (G L A : Subgroup (MulAut V)) : Prop where
  o2 : pCoreOf 2 G = ⊥
  fstar : quasithinGenFitting G = L
  quasi : CFSG.Open.IsQuasisimple ↥L
  sqtk : SQTKGroup ↥L
  min : IsFFStarMin G A
  strong : rAV A < 1
  comm : ⁅L, A⁆ = L

variable {G L A : Subgroup (MulAut V)}

theorem Red.le_G (h : Red G L A) : L ≤ G := h.fstar ▸ quasithinGenFitting_le G

theorem Red.normal (h : Red G L A) : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  intro g hg l hl
  have := le_normalizer_quasithinGenFitting G hg
  rw [h.fstar] at this
  exact (Subgroup.mem_normalizer_iff.mp this l).mp hl

theorem Red.A_le_G (h : Red G L A) : A ≤ G := h.min.1.1

theorem Red.A_normal (h : Red G L A) : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L :=
  fun a ha l hl => h.normal a (h.A_le_G ha) l hl

theorem Red.A_normalizer (h : Red G L A) : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  le_normalizer_of_conj h.A_normal

theorem Red.perfect (h : Red G L A) : Group.IsPerfect ↥L := ⟨h.quasi.1⟩

theorem Red.nontrivial (h : Red G L A) : Nontrivial ↥L :=
  CFSG.ComponentClassification.Quasisimple.nontrivial h.quasi

theorem Red.centralizer_le (h : Red G L A) :
    G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
  have := centralizer_quasithinGenFitting_le G
  rwa [h.fstar] at this

theorem Red.A_el (h : Red G L A) : IsElemAbelian2 A := h.min.1.2.2.1

theorem Red.A_ne (h : Red G L A) : A ≠ ⊥ := h.min.1.2.1

theorem Red.sq_mem (h : Red G L A) : ∀ y ∈ L ⊔ A, y ^ 2 ∈ L :=
  B1Red.sq_mem_of_mem_sup h.A_normalizer h.A_el.2

theorem Red.sup_normal (h : Red G L A) : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
  intro y hy l hl
  obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer h.A_normalizer).1 hy
  have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
  rw [e]
  exact L.mul_mem (L.mul_mem hl' (h.A_normal a ha l hl)) (L.inv_mem hl')

theorem Red.sup_le_G (h : Red G L A) : L ⊔ A ≤ G := sup_le h.le_G h.A_le_G

theorem Red.o2_sup (h : Red G L A) : pCoreOf 2 (L ⊔ A) = ⊥ := by
  set Y := L ⊔ A with hYdef
  set N := pCoreOf 2 Y with hNdef
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hNY : N ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hNLn : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L := fun n hn l hl => h.sup_normal n (hNY hn) l hl
  have hLNn : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N := fun l hl n hn =>
    B1Red.conj_mem_pCoreOf (le_sup_left (a := L) (b := A) hl) hn
  have hnle : ¬ L ≤ N := by
    intro hle
    have := h.nontrivial
    have := h.perfect
    exact Group.IsPerfect.not_isNilpotent ↥L (hN2.to_le hle).isNilpotent
  have hcomm := B1Red.commute_of_normal_not_le h.quasi hNLn hLNn hnle
  have hNc : N ≤ Subgroup.centralizer (L : Set (MulAut V)) := fun n hn =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn l hl).symm
  have hNL : N ≤ L := fun n hn => h.centralizer_le ⟨h.sup_le_G (hNY hn), hNc hn⟩
  exact B1More.eq_bot_of_le_center_genFitting h.o2 hN2 (by rw [h.fstar]; exact hNL)
    (by rw [h.fstar]; exact hNc)

theorem Red.fstar_sup (h : Red G L A) : quasithinGenFitting (L ⊔ A) = L :=
  B1Red.quasithinGenFitting_eq_of_two_quot le_sup_left h.sup_normal h.quasi h.sq_mem h.o2_sup

theorem Red.A_offender_sup (h : Red G L A) : IsFFStarOffender (L ⊔ A) A :=
  ⟨le_sup_right, h.A_ne, h.A_el, h.min.1.2.2.2⟩

theorem Red.ffJ_sup (h : Red G L A) : L ⊔ A = ffJ (L ⊔ A) := by
  set Y := L ⊔ A with hY
  have hA : A ≤ ffJ Y := B6.le_ffJ h.A_offender_sup
  have hJn : ∀ y ∈ Y, ∀ j ∈ ffJ Y, y * j * y⁻¹ ∈ ffJ Y := fun y hy j hj =>
    (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ Y hy) j).1 hj
  have hL : L ≤ ffJ Y := by
    have hcomm : ⁅L, A⁆ ≤ ffJ Y := by
      rw [Subgroup.commutator_le]
      intro l hl a ha
      have e : l * a * l⁻¹ * a⁻¹ = (l * a * l⁻¹) * a⁻¹ := rfl
      show l * a * l⁻¹ * a⁻¹ ∈ ffJ Y
      rw [e]
      exact (ffJ Y).mul_mem (hJn l ((le_sup_left : L ≤ L ⊔ A) hl) a (hA ha)) ((ffJ Y).inv_mem (hA ha))
    rwa [h.comm] at hcomm
  exact le_antisymm (sup_le hL hA) (B6.ffJ_le Y)

theorem Red.centerOf_sup_le (h : Red G L A) : centerOf (L ⊔ A) ≤ L := by
  intro x hx
  have h1 : (L ⊔ A) ⊓ Subgroup.centralizer ((L ⊔ A : Subgroup (MulAut V)) : Set (MulAut V)) ≤
      (L ⊔ A) ⊓ Subgroup.centralizer (L : Set (MulAut V)) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
  have h2 := centralizer_quasithinGenFitting_le (L ⊔ A)
  rw [h.fstar_sup] at h2
  exact h2 (h1 hx)

theorem Red.b51Hyp (h : Red G L A) : B51Hyp (L ⊔ A) L := by
  refine ⟨?_, B1Red.isQuasisimple_of_open h.quasi, h.sqtk, le_sup_left, h.o2_sup, h.ffJ_sup⟩
  rw [h.fstar_sup]
  exact (sup_eq_left.2 h.centerOf_sup_le).symm

theorem arith_section_strict {sS u w v a cV cW cU cS : ℕ} (hsu : sS * u = w)
    (hcw : cW ≤ cS * cU) (hcu : cU ≤ u) (hn : w * cV ≤ v * cW) (hv : v < a * cV)
    (hcW : 0 < cW) : sS < a * cS := by
  have h1 : w * cV < (a * cW) * cV := by
    calc w * cV ≤ v * cW := hn
      _ < (a * cV) * cW := Nat.mul_lt_mul_of_pos_right hv hcW
      _ = (a * cW) * cV := by ring
  have hA : w < a * cW := Nat.lt_of_mul_lt_mul_right h1
  have h2 : sS * u < (a * cS) * u := by
    calc sS * u = w := hsu
      _ < a * cW := hA
      _ ≤ a * (cS * cU) := Nat.mul_le_mul_left _ hcw
      _ = a * cS * cU := by ring
      _ ≤ (a * cS) * u := Nat.mul_le_mul_left _ hcu
  exact Nat.lt_of_mul_lt_mul_right h2

theorem sec_strict {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hv : Nat.card V < Nat.card A * Nat.card (fixV A)) (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    Nat.card (Sec W U) < Nat.card A * Nat.card (fixV (autSec A W U)) := by
  have hn : Nat.card W * Nat.card (fixV A) ≤ Nat.card V * Nat.card ↥(W ⊓ fixV A) := by
    rw [← card_mul_card_fixV_le A W]
    exact Nat.mul_le_mul_right _ (by
      simpa using Subgroup.card_le_of_le (le_top : (W ⊔ fixV A) ≤ ⊤))
  have hcu : Nat.card ↥(U ⊓ fixV A) ≤ Nat.card U := Subgroup.card_le_of_le inf_le_left
  exact arith_section_strict (card_sec_mul hUW) (card_inf_fixV_le_autSec hUW hAW) hcu hn hv
    Nat.card_pos

theorem exists_irrPlus {L : Subgroup (MulAut V)} (hq : CFSG.Open.IsQuasisimple ↥L) :
    ∃ I, I ∈ IrrPlus L (⊤ : Subgroup V) := by
  have hLperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  have hne : commV L ≠ ⊥ := by
    intro h
    rw [commV_eq_commSub, commSub_eq_bot_iff] at h
    obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
    apply hl
    apply Subtype.ext
    ext v
    exact h (Subgroup.mem_top v) l l.2
  exact B1Red.exists_mem_irrPlus (Subgroup.isPerfect_iff.1 hLperf) hne

theorem Red.A_stab_irr (hV : ∀ v : V, v ^ 2 = 1) (h : Red G L A) {I : Subgroup V}
    (hI : I ∈ IrrPlus L (⊤ : Subgroup V)) : ∀ b ∈ A, ∀ w ∈ I, b w ∈ I := by
  intro b hb w hw
  have hE : oTwoUpper L = L := B1Red.oTwoUpper_eq_of_perfect h.perfect
  have hCF : AllTwoChiefFactorsCentral L := B1Red.allTwoChiefFactorsCentral_of_quasisimple h.quasi
  have h1 := B1_5_3 hV h.min hE h.comm hCF b hb I hI
  have h2 : b w ∈ I.map b.toMonoidHom := Subgroup.mem_map_of_mem _ hw
  rwa [h1] at h2

theorem Red.secCtx (hV : ∀ v : V, v ^ 2 = 1) (h : Red G L A) {I : Subgroup V}
    (hI : I ∈ IrrPlus L (⊤ : Subgroup V)) :
    B5.SecCtx (L ⊔ A) L A I (I ⊓ fixV L) := by
  obtain ⟨hLinv, hcomm, hlt, -⟩ := (mem_irrPlus_top_iff).1 hI
  have hAI := h.A_stab_irr hV hI
  have hAU : ∀ b ∈ A, ∀ w ∈ I ⊓ fixV L, b w ∈ I ⊓ fixV L :=
    isInv_inf hAI (B1Red.fixV_inv_of_normalizes h.A_normal)
  refine ⟨le_sup_right, h.A_el, h.A_ne, inf_le_left, ?_, ?_, ?_⟩
  · exact sup_le (B1.le_stabSub_of_invariant hLinv) (B1.le_stabSub_of_invariant hAI)
  · exact sup_le (B1.le_stabSub_of_invariant (isInv_inf hLinv (isInv_fixV L)))
      (B1.le_stabSub_of_invariant hAU)
  · rw [hcomm]
    exact not_le_of_gt hlt

theorem Red.b4Hyp (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1) (h : Red G L A)
    {I : Subgroup V} (hI : I ∈ IrrPlus L (⊤ : Subgroup V)) :
    B4Hyp (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec L I (I ⊓ fixV L)) := by
  obtain ⟨-, -, hlt, hirr⟩ := (mem_irrPlus_top_iff).1 hI
  exact B5.b4Hyp_sec h.b51Hyp (h.secCtx hV hI) hA21 hlt hirr

theorem Red.strong_section (hV : ∀ v : V, v ^ 2 = 1) (h : Red G L A) {I : Subgroup V}
    (hI : I ∈ IrrPlus L (⊤ : Subgroup V)) :
    IsA2 (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec A I (I ⊓ fixV L)) ∧
      rAV (autSec A I (I ⊓ fixV L)) < 1 := by
  have hc := h.secCtx hV hI
  have hA2 : IsA2 G A := h.min.1.isA2
  have hv : Nat.card V < Nat.card A * Nat.card (fixV A) :=
    (rAV_lt_one_iff hV hA2).1 h.strong
  have hAW : A ≤ stabSub I := le_sup_right.trans hc.hMW
  have hAU : A ≤ stabSub (I ⊓ fixV L) := le_sup_right.trans hc.hMU
  have hS := sec_strict hv hc.hUW hAW
  have hfaith := B5.sec_A_inf_centSec h.b51Hyp hc
  have hcard : Nat.card (autSec A I (I ⊓ fixV L)) = Nat.card A := by
    have := card_autSec_mul hAW hAU
    rw [hfaith, Subgroup.card_bot, mul_one] at this
    exact this
  have hA'2 := B5.isA2_secA h.b51Hyp hc
  refine ⟨hA'2, ?_⟩
  rw [rAV_lt_one_iff (sq_eq_one_sec hV I (I ⊓ fixV L)) hA'2, hcard]
  exact hS

theorem Red.exists_strong_section (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1)
    (h : Red G L A) :
    ∃ I : Subgroup V, I ∈ IrrPlus L (⊤ : Subgroup V) ∧
      B4Hyp (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec L I (I ⊓ fixV L)) ∧
      ∃ B, B ≤ autSec A I (I ⊓ fixV L) ∧ IsFFStarOffender (autSec (L ⊔ A) I (I ⊓ fixV L)) B ∧
        rAV B < 1 := by
  obtain ⟨I, hI⟩ := exists_irrPlus h.quasi
  obtain ⟨hA'2, hr⟩ := h.strong_section hV hI
  obtain ⟨B, hBA, hB, hBr⟩ := B1_4_4_lt (sq_eq_one_sec hV I (I ⊓ fixV L)) hA'2 hr
  exact ⟨I, hI, h.b4Hyp hA21 hV hI, B, hBA, hB, hBr⟩

@[expose] def B42Case10ii {S : Type} [CommGroup S] (G L : Subgroup (MulAut S)) [Finite S] : Prop :=
  SLExteriorTwo L ⊤ ⊥ 4 ∧ G = ffJ G ∧ Nonempty (↥G ≃* Equiv.Perm (Fin 8)) ∧
    qOf G = ((3 / 4 : ℚ) : WithTop ℚ)

theorem b42_strong {S : Type} [CommGroup S] [Finite S] (hS : ∀ s : S, s ^ 2 = 1)
    {G L A : Subgroup (MulAut S)} (h : B42Conclusion G L A) (hstrong : IsStrongFFModule G) :
    B42Case2 G L ∨ B42Case3 G L ∨ B42Case9 G L ∨ B42Case10ii G L := by
  have hq1 : ∀ {r : WithTop ℚ}, qOf G = r → (1 : WithTop ℚ) ≤ r → False := by
    intro r hr h1
    exact not_isStrongFFModule_of_one_le_qOf hS (hr ▸ h1) hstrong
  have h1 : ((1 : ℚ) : WithTop ℚ) = 1 := WithTop.coe_one
  rcases h with c | c | c | c | c | c | c | c | c | c | c
  · exact (hq1 c.2.2.2 (by rw [h1])).elim
  · exact Or.inl c
  · exact Or.inr (Or.inl c)
  · exact (hq1 c.2 (by rw [h1])).elim
  · exact (hq1 c.2 (by rw [h1])).elim
  · exact (hq1 c.2.2.2.1 (by rw [h1])).elim
  · exact (hq1 c.2.2.2.2.1 (by rw [h1])).elim
  · exact (hq1 c.2.2.1 (by rw [h1])).elim
  · exact Or.inr (Or.inr (Or.inl c))
  · rcases c.2 with c' | c'
    · exact (hq1 c'.2.2.2 (by rw [h1])).elim
    · exact Or.inr (Or.inr (Or.inr ⟨c.1, c'⟩))
  · exact (hq1 c.2.2.2.1 (by rw [h1])).elim

theorem Red.exists_strong_case (h42 : AsB42) (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1)
    (h : Red G L A) :
    ∃ I : Subgroup V, I ∈ IrrPlus L (⊤ : Subgroup V) ∧
      (B42Case2 (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec L I (I ⊓ fixV L)) ∨
        B42Case3 (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec L I (I ⊓ fixV L)) ∨
        B42Case9 (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec L I (I ⊓ fixV L)) ∨
        B42Case10ii (autSec (L ⊔ A) I (I ⊓ fixV L)) (autSec L I (I ⊓ fixV L))) := by
  obtain ⟨I, hI, hB4, B, -, hB, hBr⟩ := h.exists_strong_section hA21 hV
  refine ⟨I, hI, ?_⟩
  have hS := sq_eq_one_sec hV I (I ⊓ fixV L)
  have hstrong : IsStrongFFModule (autSec (L ⊔ A) I (I ⊓ fixV L)) :=
    (isStrongFFModule_iff hS).2 ⟨B, hB.isA2, hBr⟩
  exact b42_strong hS (h42 _ hS _ _ hB4 B hB) hstrong

end Reduced

end B69

end CFSG.Quasithin
