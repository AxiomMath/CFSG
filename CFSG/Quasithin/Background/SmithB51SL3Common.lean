module

public import CFSG.Quasithin.Background.B5NonPart1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

@[expose] def AsB51NonirrSL3IH : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], B51Part1Below (Nat.card V) → (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → commV L ∉ IrrPlus L ⊤ →
      (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥L ≃* ↥(StatedSL 3 K))) →
      B51Case1ii G L

@[expose] def AsB51NonirrLnIH : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], B51Part1Below (Nat.card V) → (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → commV L ∉ IrrPlus L ⊤ →
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
          Nonempty (↥L ≃* ↥(StatedSL 4 K))) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
          Nonempty (↥L ≃* ↥(StatedSL 5 K)))) →
      (∃ n, B51Case1iii G L n) ∨ B51Case1iv G L

section Induction

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem part1_of_nonirr_ind (hSL3 : AsB51NonirrSL3IH) (hLn : AsB51NonirrLnIH)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∉ IrrPlus L ⊤) (hT : IsL345Type ↥L) : B51Part1 G L := by
  refine part1_of_cases h ?_
  rcases hT with ⟨n, K, hK, hf, hc, ⟨e⟩⟩ | ⟨K, hK, hf, hc, ⟨e⟩⟩ | ⟨K, hK, hf, hc, ⟨e⟩⟩
  · exact Or.inl (hSL3 V hIH hV G L h hU ⟨n, K, hK, hf, hc, ⟨e⟩⟩)
  · rcases hLn V hIH hV G L h hU (Or.inl ⟨K, hK, hf, hc, ⟨e⟩⟩) with h3 | h4
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)
  · rcases hLn V hIH hV G L h hU (Or.inr ⟨K, hK, hf, hc, ⟨e⟩⟩) with h3 | h4
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)

end Induction

theorem part1_below_ind (hI : B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover)
    (hSL3 : AsB51NonirrSL3IH) (hLn : AsB51NonirrLnIH) : ∀ N, B51Part1Below N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ hVN hV G L h
    by_cases hU : commV L ∈ IrrPlus L ⊤
    · exact part1_of_irr hI hV h hU
    · have hIH : B51Part1Below (Nat.card V) := ih (Nat.card V) hVN
      exact part1_of_nonirr_ind hSL3 hLn hIH hV h hU
        (nonirr_identify hA21 hI.b42 hA36 hIH hV h hU)

theorem asB51NonirrSL3_of_ind (hI : B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) (hSL3 : AsB51NonirrSL3IH) (hLn : AsB51NonirrLnIH) :
    AsB51NonirrSL3 := fun V _ _ hV G L h hU hT =>
  hSL3 V (part1_below_ind hI hA21 hA36 hSL3 hLn (Nat.card V)) hV G L h hU hT

theorem asB51NonirrLn_of_ind (hI : B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) (hSL3 : AsB51NonirrSL3IH) (hLn : AsB51NonirrLnIH) :
    AsB51NonirrLn := fun V _ _ hV G L h hU hT =>
  hLn V (part1_below_ind hI hA21 hA36 hSL3 hLn (Nat.card V)) hV G L h hU hT

section Max

variable {V' : Type*} [CommGroup V'] [Finite V']

omit [Finite V'] in
theorem isQuadratic_of_le {A B : Subgroup (MulAut V')} (hA : IsQuadratic A) (hBA : B ≤ A) :
    IsQuadratic B := by
  have h1 : commV B ≤ commV A := by
    apply Subgroup.closure_mono
    rintro _ ⟨x, hx, v, rfl⟩
    exact ⟨x, hBA hx, v, rfl⟩
  exact (h1.trans hA).trans (B1.fixV_le_fixV hBA)

theorem exists_offender_max (hV' : ∀ v : V', v ^ 2 = 1) {X A : Subgroup (MulAut V')}
    (hA : IsA2 X A) (hr : rAV A ≤ 1) :
    ∃ B, B ≤ A ∧ IsFFStarOffender X B ∧
      Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B) := by
  have hle := (rAV_le_one_iff hV' hA).1 hr
  obtain ⟨B, hBA, hB, hBc⟩ := B1.exists_offender_below hA
    (Nat.card A * Nat.card (fixV A) - Nat.card V') (by omega)
  exact ⟨B, hBA, hB, by omega⟩

theorem rk_add_le_of_card_le (hV' : ∀ v : V', v ^ 2 = 1) {A B : Subgroup (MulAut V')}
    (hA : IsElemAbelian2 A) (hB : IsElemAbelian2 B)
    (hcard : Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B)) :
    rk A + rkIdx (fixV B) ≤ rk B + rkIdx (fixV A) := by
  rw [B1.card_elemAbelian hA, B1.card_elemAbelian hB, card_eq_two_pow hV' (fixV A),
    card_eq_two_pow hV' (fixV B), ← pow_add, ← pow_add] at hcard
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have h2 := rk_add_rkIdx (fixV A)
  have h3 := rk_add_rkIdx (fixV B)
  omega

theorem le_rAV_of_card_le (hV' : ∀ v : V', v ^ 2 = 1) {A B : Subgroup (MulAut V')}
    (hBA : B ≤ A) (hA : IsElemAbelian2 A) (hBne : B ≠ ⊥)
    (hcard : Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B))
    {ρ : ℚ} (hρ : ρ ≤ 1) (hB : ρ ≤ rAV B) : ρ ≤ rAV A := by
  have hBel : IsElemAbelian2 B := ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb),
    fun a ha => hA.2 a (hBA ha)⟩
  have hk := rk_add_le_of_card_le hV' hA hBel hcard
  have hb : 0 < rk B := hBel.rk_pos hBne
  have hba : rk B ≤ rk A := by
    have h1 := B1.card_elemAbelian hA
    have h2 := B1.card_elemAbelian hBel
    have h3 : Nat.card B ≤ Nat.card A := Subgroup.card_le_of_le hBA
    rw [h1, h2] at h3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have ha : 0 < rk A := lt_of_lt_of_le hb hba
  unfold rAV at hB ⊢
  rw [le_div_iff₀ (by exact_mod_cast hb)] at hB
  rw [le_div_iff₀ (by exact_mod_cast ha)]
  have hk' : (rk A : ℚ) + (rkIdx (fixV B) : ℚ) ≤ (rk B : ℚ) + (rkIdx (fixV A) : ℚ) := by
    exact_mod_cast hk
  have hba' : (rk B : ℚ) ≤ (rk A : ℚ) := by exact_mod_cast hba
  nlinarith

theorem eq_of_card_le_of_rAV (hV' : ∀ v : V', v ^ 2 = 1) {A B : Subgroup (MulAut V')}
    (hBA : B ≤ A) (hA : IsElemAbelian2 A) (hBne : B ≠ ⊥)
    (hcard : Nat.card A * Nat.card (fixV A) ≤ Nat.card B * Nat.card (fixV B))
    (hρ : rAV A < 1) (hB : rAV A ≤ rAV B) : B = A := by
  have hBel : IsElemAbelian2 B := ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb),
    fun a ha => hA.2 a (hBA ha)⟩
  have hk := rk_add_le_of_card_le hV' hA hBel hcard
  have hb : 0 < rk B := hBel.rk_pos hBne
  have hba : rk B ≤ rk A := by
    have h3 : Nat.card B ≤ Nat.card A := Subgroup.card_le_of_le hBA
    rw [B1.card_elemAbelian hA, B1.card_elemAbelian hBel] at h3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have ha : 0 < rk A := lt_of_lt_of_le hb hba
  have hab : rk A ≤ rk B := by
    by_contra hlt
    push Not at hlt
    unfold rAV at hρ hB
    rw [div_lt_one (by exact_mod_cast ha)] at hρ
    rw [div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)] at hB
    have hk' : (rk A : ℚ) + (rkIdx (fixV B) : ℚ) ≤ (rk B : ℚ) + (rkIdx (fixV A) : ℚ) := by
      exact_mod_cast hk
    have hlt' : (rk B : ℚ) < (rk A : ℚ) := by exact_mod_cast hlt
    have hb' : (0 : ℚ) < (rk B : ℚ) := by exact_mod_cast hb
    nlinarith
  refine Subgroup.eq_of_le_of_card_ge hBA ?_
  rw [B1.card_elemAbelian hA, B1.card_elemAbelian hBel]
  exact Nat.pow_le_pow_right (by norm_num) hab

end Max

section Sections

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W U : Subgroup V}

theorem b42_trichotomy (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (c : SecCtx G L A W U)
    (hirr : XMod.IsIrrSec ↥(autSec L W U) (⊥ : Subgroup (Sec W U)) ⊤)
    {B : Subgroup (MulAut (Sec W U))} (hB : IsFFStarOffender (autSec (L ⊔ A) W U) B) :
    B42Case2 (autSec (L ⊔ A) W U) (autSec L W U) ∨
      B42Case9 (autSec (L ⊔ A) W U) (autSec L W U) ∨
      ((2 / 3 : ℚ) : WithTop ℚ) ≤ qOf (autSec (L ⊔ A) W U) := by
  have hc := hB42 (Sec W U) (sq_eq_one_sec hV W U) _ _ (b4Hyp_sec' h c hA21 hirr) B hB
  have one : ((2 / 3 : ℚ) : WithTop ℚ) ≤ ((1 : ℚ) : WithTop ℚ) :=
    WithTop.coe_le_coe.2 (by norm_num)
  rcases hc with ⟨-, -, -, hq⟩ | h2 | ⟨-, hq⟩ | ⟨-, hq⟩ | ⟨-, hq⟩ |
    ⟨-, -, -, hq, -⟩ | ⟨-, -, -, -, hq, -⟩ | ⟨-, -, hq, -⟩ | h9 |
    ⟨-, ⟨-, -, -, hq⟩ | ⟨-, -, hq⟩⟩ | ⟨-, -, -, hq, -⟩
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inl h2
  · exact Or.inr (Or.inr hq.ge)
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inr (Or.inl h9)
  · exact Or.inr (Or.inr (hq ▸ one))
  · exact Or.inr (Or.inr (hq ▸ WithTop.coe_le_coe.2 (by norm_num)))
  · exact Or.inr (Or.inr (hq ▸ one))

theorem sec_cases_IH (hA21 : AsA21SQTKSection) (hIH : B51Part1Below (Nat.card V))
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (c : SecCtx G L A W U) (hquad : IsQuadratic A)
    (hcard : Nat.card (Sec W U) < Nat.card V)
    (hch : ∀ X : Subgroup V, L ⊔ A ≤ stabSub X → U ≤ X → X ≤ W → X = U ∨ X = W)
    (hr : rAV (autSec A W U) < 1) :
    ∃ B, B ≤ autSec A W U ∧ IsFFStarOffender (autSec (L ⊔ A) W U) B ∧
      Nat.card (autSec A W U) * Nat.card (fixV (autSec A W U)) ≤
        Nat.card B * Nat.card (fixV B) ∧
      (XMod.IsIrrSec ↥(autSec L W U) (⊥ : Subgroup (Sec W U)) ⊤ ∨
        (∃ n, B51Case1iii (autSec L W U ⊔ B) (autSec L W U) n) ∨
          B51Case1iv (autSec L W U ⊔ B) (autSec L W U)) := by
  have hS2 := sq_eq_one_sec hV W U
  have hA2 := isA2_secA h c
  obtain ⟨B, hBA, hB, hBc⟩ := exists_offender_max hS2 hA2 hr.le
  refine ⟨B, hBA, hB, hBc, ?_⟩
  have hlt : U < W := by
    refine lt_of_le_of_ne c.hUW fun heq => c.hnc ?_
    exact (commSub_le_of_invariant (fun x hx w hw =>
      (c.hMW (Subgroup.mem_sup_left hx) w).2 hw)).trans heq.symm.le
  obtain ⟨-, hcase⟩ := hIH (Sec W U) hcard hS2 _ _ (b51Hyp_secY h c hA21 hB)
  rcases hcase with hi | hii | hiii | hiv
  · exact Or.inl (isIrrSec_secL_of_irrPlus h c (isIrrSec_secX c hlt hch) hi.1)
  · exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hq⟩ := hii
    have hBq : IsQuadratic B := isQuadratic_of_le (isQuadratic_secA c hquad) hBA
    have hBY : IsA2 (autSec L W U ⊔ B) B := ⟨le_sup_right, hB.2.1, hB.2.2.1⟩
    have h1 : qOf (autSec L W U ⊔ B) ≤ ((rAV B : ℚ) : WithTop ℚ) :=
      qOf_le_iff.2 ⟨B, hBY, hBq, le_rfl⟩
    rw [hq] at h1
    have h2 : (1 : ℚ) ≤ rAV B := by exact_mod_cast h1
    have h3 := le_rAV_of_card_le hS2 hBA hA2.2.2 hB.2.1 hBc le_rfl h2
    exact absurd hr (not_lt.2 h3)
  · exact Or.inr (Or.inl hiii)
  · exact Or.inr (Or.inr hiv)

theorem sec_faithful (hA36 : AsA36NoOddCover) (h : B51Hyp G L) (c : SecCtx G L A W U)
    (hT : IsL345Type ↥(autSec L W U)) : (L ⊔ A) ⊓ centSec W U = ⊥ := by
  have hLM : L ≤ L ⊔ A := le_sup_left
  have hmem : ∀ l : ↥L, (secHom (L ⊔ A) c.hMW c.hMU) (Subgroup.inclusion hLM l) ∈
      autSec L W U := by
    intro l
    rw [← map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU hLM]
    exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLM l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  let f : ↥L →* ↥(autSec L W U) :=
    ((secHom (L ⊔ A) c.hMW c.hMU).comp (Subgroup.inclusion hLM)).codRestrict (autSec L W U) hmem
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : MulAut (Sec W U)) ∈ (L.subgroupOf (L ⊔ A)).map (secHom (L ⊔ A) c.hMW c.hMU) := by
      rw [map_secHom_eq_autSec (L ⊔ A) c.hMW c.hMU hLM]; exact y.2
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, Subtype.ext hgy⟩
  have hker : ∀ x : ↥L, f x = 1 ↔ (x : MulAut V) ∈ centSec W U := by
    intro x
    constructor
    · intro hx
      have h1 : Subgroup.inclusion hLM x ∈ (secHom (L ⊔ A) c.hMW c.hMU).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact (mem_ker_secHom (L ⊔ A) c.hMW c.hMU _).1 h1
    · intro hx
      apply Subtype.ext
      have h1 : Subgroup.inclusion hLM x ∈ (secHom (L ⊔ A) c.hMW c.hMU).ker :=
        (mem_ker_secHom (L ⊔ A) c.hMW c.hMU _).2 hx
      exact h1
  have hodd : ∀ x ∈ f.ker, Odd (orderOf x) := by
    intro x hx
    have h2 := (hker x).1 hx
    have hxc : (x : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
      (secKernel_le h c).2 ⟨Subgroup.mem_sup_left x.2, h2⟩
    have hxG : (x : MulAut V) ∈ G := le_G h x.2
    have := odd_orderOf_of_mem_centralizer h hxG hxc
    rwa [Subgroup.orderOf_coe] at this
  have hinj := hA36 ↥L ↥(autSec L W U) (quasi_L h) h.2.2.1 f hsurj hodd hT
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ L := (secKernel_le h c).1 hx
  have h1 : f ⟨x, hxL⟩ = 1 := (hker ⟨x, hxL⟩).2 hx.2
  have h2 : (⟨x, hxL⟩ : ↥L) = 1 := hinj (h1.trans f.map_one.symm)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)

theorem le_L_of_ffJ_eq (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (c : SecCtx G L A W U)
    (hquad : IsQuadratic A) (hfaith : (L ⊔ A) ⊓ centSec W U = ⊥)
    (hJ : ffJ (autSec (L ⊔ A) W U) = autSec L W U)
    (hq : ((rAV (autSec A W U) : ℚ) : WithTop ℚ) ≤ qOf (autSec (L ⊔ A) W U))
    (hr : rAV (autSec A W U) < 1) : A ≤ L := by
  have hS2 := sq_eq_one_sec hV W U
  have hA2 := isA2_secA h c
  obtain ⟨B, hBA, hB, hBc⟩ := exists_offender_max hS2 hA2 hr.le
  have hBJ : B ≤ ffJ (autSec (L ⊔ A) W U) := B6.le_ffJ hB
  have hBq : IsQuadratic B := isQuadratic_of_le (isQuadratic_secA c hquad) hBA
  have h1 : qOf (autSec (L ⊔ A) W U) ≤ ((rAV B : ℚ) : WithTop ℚ) :=
    qOf_le_iff.2 ⟨B, hB.isA2, hBq, le_rfl⟩
  have h2 : rAV (autSec A W U) ≤ rAV B := by exact_mod_cast hq.trans h1
  have h3 := eq_of_card_le_of_rAV hS2 hBA hA2.2.2 hB.2.1 hBc hr h2
  rw [h3, hJ] at hBJ
  exact le_of_autSec_le c.hMW c.hMU hfaith le_sup_left le_sup_right hBJ

end Sections

section Lift

theorem map_fixV_eq_of_card_le {V' : Type*} [CommGroup V'] [Finite V'] {A : Subgroup (MulAut V')}
    {U : Subgroup V'}
    (h : Nat.card (fixV (autQuot A U)) * Nat.card ↥(U ⊓ fixV A) ≤ Nat.card (fixV A)) :
    (fixV A).map (QuotientGroup.mk' U) = fixV (autQuot A U) := by
  have h1 := B1More.card_map_mul_card_inf_ker (fixV A) (QuotientGroup.mk' U)
  have h2 : (fixV A).map (QuotientGroup.mk' U) ≤ fixV (autQuot A U) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mk_mem_fixV_autQuot.2 fun g hg _ => by rw [hv g hg]; simp
  have h3 : fixV A ⊓ (QuotientGroup.mk' U).ker = U ⊓ fixV A := by
    rw [QuotientGroup.ker_mk', inf_comm]
  rw [h3] at h1
  refine Subgroup.eq_of_le_of_card_ge h2 ?_
  have hpos : 0 < Nat.card ↥(U ⊓ fixV A) := Nat.card_pos
  have h4 : Nat.card (fixV (autQuot A U)) * Nat.card ↥(U ⊓ fixV A) ≤
      Nat.card ↥((fixV A).map (QuotientGroup.mk' U)) * Nat.card ↥(U ⊓ fixV A) := by
    rw [h1]; exact h
  exact Nat.le_of_mul_le_mul_right h4 hpos

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_lift_sec {A : Subgroup (MulAut V)} {W U : Subgroup V} (hUW : U ≤ W)
    (hAW : A ≤ stabSub W)
    (h : Nat.card (fixV (autSec A W U)) * Nat.card ↥(U ⊓ fixV A) ≤ Nat.card ↥(W ⊓ fixV A))
    (s : Sec W U) (hs : s ∈ fixV (autSec A W U)) :
    ∃ w : ↥W, (w : V) ∈ fixV A ∧ (QuotientGroup.mk w : Sec W U) = s := by
  have hW : Nat.card (fixV (autSub A W)) = Nat.card ↥(W ⊓ fixV A) := by
    rw [← map_subtype_fixV_autSub hAW, Subgroup.card_map_of_injective W.subtype_injective]
  have hU : Nat.card ↥(U.subgroupOf W ⊓ fixV (autSub A W)) = Nat.card ↥(U ⊓ fixV A) := by
    have h4 : (U.subgroupOf W ⊓ fixV (autSub A W)).map W.subtype = U ⊓ fixV A := by
      rw [Subgroup.map_inf _ _ _ W.subtype_injective, map_subtype_fixV_autSub hAW,
        Subgroup.map_subgroupOf_eq_of_le hUW, ← inf_assoc, inf_eq_left.2 hUW]
    rw [← h4, Subgroup.card_map_of_injective W.subtype_injective]
  have heq := map_fixV_eq_of_card_le (A := autSub A W) (U := U.subgroupOf W)
    (by rw [hW, hU]; exact h)
  have hs' : s ∈ (fixV (autSub A W)).map (QuotientGroup.mk' (U.subgroupOf W)) := by
    rw [heq]; exact hs
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hs'
  refine ⟨w, ?_, rfl⟩
  intro a ha
  exact (mem_fixV_autSub.1 hw) a ha (hAW ha)

theorem card_le_of_mu_eq (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hUW : U ≤ W)
    (heq : rk W - rk ↥(W ⊓ fixV A) ≤ rkIdx (fixV (autSec A W U)) + (rk U - rk ↥(U ⊓ fixV A))) :
    Nat.card (fixV (autSec A W U)) * Nat.card ↥(U ⊓ fixV A) ≤ Nat.card ↥(W ⊓ fixV A) := by
  have h1 := rk_sec_add hUW
  have h3 := rk_add_rkIdx (fixV (autSec A W U))
  have h4 : rk ↥(U ⊓ fixV A) ≤ rk U := rk_mono inf_le_left
  have h5 : rk ↥(W ⊓ fixV A) ≤ rk W := rk_mono inf_le_left
  have h6 : rk (fixV (autSec A W U)) + rk ↥(U ⊓ fixV A) ≤ rk ↥(W ⊓ fixV A) := by omega
  have c1 : Nat.card ↥(W ⊓ fixV A) = 2 ^ rk ↥(W ⊓ fixV A) := card_eq_two_pow hV _
  have c2 : Nat.card ↥(U ⊓ fixV A) = 2 ^ rk ↥(U ⊓ fixV A) := card_eq_two_pow hV _
  have c3 : Nat.card (fixV (autSec A W U)) = 2 ^ rk (fixV (autSec A W U)) :=
    card_eq_two_pow_of_isPGroup ((isPGroup_sec hV W U).to_subgroup _)
  rw [c1, c2, c3, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) h6

theorem comm_mem_of_rkIdx_eq_zero (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    {W U : Subgroup V} (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U)
    (h0 : rkIdx (fixV (autSec A W U)) = 0) : ∀ a ∈ A, ∀ w ∈ W, a w * w⁻¹ ∈ U := by
  have htop : fixV (autSec A W U) = ⊤ := by
    have h1 := B1.index_eq_two_pow (sq_eq_one_sec hV W U) (fixV (autSec A W U))
    rw [h0, pow_zero] at h1
    exact Subgroup.index_eq_one.1 h1
  intro a ha w hw
  have hs : (QuotientGroup.mk ⟨w, hw⟩ : Sec W U) ∈ fixV (autSec A W U) := by
    rw [htop]; trivial
  have hg : resHom W ⟨a, hAW ha⟩ ∈ autSub A W := mem_autSub.2 ⟨⟨a, hAW ha⟩, ha, rfl⟩
  have := (mk_mem_fixV_autQuot.1 hs) _ hg (autSub_le_stabSub_subgroupOf hAU hg)
  rw [Subgroup.mem_subgroupOf] at this
  simpa [resHom_apply] using this

theorem chain_extremal (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {Y I Y₂ W₂ : Subgroup V} (hYI : Y ≤ I) (hIY₂ : I ≤ Y₂)
    (hY₂W₂ : Y₂ ≤ W₂) (hAI : A ≤ stabSub I) (hAY₂ : A ≤ stabSub Y₂)
    (hAW₂ : A ≤ stabSub W₂)
    (hsum : rk A ≤ rkIdx (fixV (autSec A I Y)) + rkIdx (fixV (autSec A W₂ Y₂))) :
    Y ≤ fixV A ∧ (∀ a ∈ A, ∀ y ∈ Y₂, a y * y⁻¹ ∈ I) ∧ (∀ a ∈ A, ∀ v : V, a v * v⁻¹ ∈ W₂) ∧
      rkIdx (fixV A) = rk A ∧
      Nat.card (fixV (autSec A I Y)) * Nat.card ↥(Y ⊓ fixV A) ≤ Nat.card ↥(I ⊓ fixV A) ∧
      Nat.card (fixV (autSec A Y₂ I)) * Nat.card ↥(I ⊓ fixV A) ≤ Nat.card ↥(Y₂ ⊓ fixV A) ∧
      Nat.card (fixV (autSec A W₂ Y₂)) * Nat.card ↥(Y₂ ⊓ fixV A) ≤ Nat.card ↥(W₂ ⊓ fixV A) ∧
      Nat.card (fixV (autSec A ⊤ W₂)) * Nat.card ↥(W₂ ⊓ fixV A) ≤
        Nat.card ↥((⊤ : Subgroup V) ⊓ fixV A) := by
  have hAtop : A ≤ stabSub (⊤ : Subgroup V) := fun g _ u => by simp
  have e1 := rk_mu_section hV hYI hAI
  have e2 := rk_mu_section hV hIY₂ hAY₂
  have e3 := rk_mu_section hV hY₂W₂ hAW₂
  have e4 := rk_mu_section hV (le_top : W₂ ≤ ⊤) hAtop
  have e5 := rk_add_rkIdx (fixV A)
  have e6 := rkIdx_fixV_le_rk hV hA
  rw [top_inf_eq, rk_top] at e4
  have hY0 : rk Y ≤ rk ↥(Y ⊓ fixV A) := by omega
  have hYfix : Y ≤ fixV A :=
    inf_eq_left.1 (eq_of_le_of_rk_le hV inf_le_left hY0)
  have h2 : rkIdx (fixV (autSec A Y₂ I)) = 0 := by omega
  have h3 : rkIdx (fixV (autSec A ⊤ W₂)) = 0 := by omega
  refine ⟨hYfix, comm_mem_of_rkIdx_eq_zero hV hAY₂ hAI h2,
    fun a ha v => comm_mem_of_rkIdx_eq_zero hV hAtop hAW₂ h3 a ha v (Subgroup.mem_top v),
    by omega, card_le_of_mu_eq hV hYI (by omega), card_le_of_mu_eq hV hIY₂ (by omega),
    card_le_of_mu_eq hV hY₂W₂ (by omega), card_le_of_mu_eq hV (le_top : W₂ ≤ ⊤) ?_⟩
  rw [top_inf_eq, rk_top]
  omega

end Lift

section Central

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem L_comm_mem_of_A (h : B51Hyp G L) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hA2 : IsPGroup 2 A) (hAne : A ≠ ⊥) {W U : Subgroup V} (hLW : L ≤ stabSub W)
    (hLU : L ≤ stabSub U) (hA : ∀ a ∈ A, ∀ w ∈ W, a w * w⁻¹ ∈ U) :
    ∀ l ∈ L, ∀ w ∈ W, l w * w⁻¹ ∈ U := by
  set N := L ⊓ centSec W U with hN
  have hq := B1Red.isQuasisimple_to_open (quasi_L h)
  have hAN : A ≤ N := fun a ha => ⟨hAL ha, hLW (hAL ha), hA a ha⟩
  have hDnorm : (N.subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨L.mul_mem (L.mul_mem g.2 hx.1) (L.inv_mem g.2),
      conj_mem_centSec (hLW g.2) (hLU g.2) hx.2⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    (N.subgroupOf L) with hc | htop
  · exfalso
    have hAc : A ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem : (⟨a, hAL ha⟩ : ↥L) ∈ N.subgroupOf L := hAN ha
      have := Subgroup.mem_center_iff.mp (hc hmem) ⟨l, hl⟩
      exact congrArg Subtype.val this
    have h2 := two_inf_centralizer_eq_bot h ((hAL.trans (le_G h))) hA2
    exact hAne (eq_bot_iff.2 (h2 ▸ le_inf le_rfl hAc))
  · intro l hl w hw
    have : (⟨l, hl⟩ : ↥L) ∈ N.subgroupOf L := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.1 this).2.2 w hw

end Central

end B5

end CFSG.Quasithin
