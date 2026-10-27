module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBAct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Aut

variable {S : Type} [Group S] [Finite S]

theorem s16n9b_case7_card_mulAut_dvd (hS : IsL3 S 1) :
    Nat.card (MulAut (Multiplicative (ZMod 7) × S)) ∣ 336 * 6 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcS : center S = ⊥ := center_eq_bot_of_isL3 hS
  have hpS : _root_.commutator S = ⊤ := s16c1610_commutator_of_isL3 hS
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (Multiplicative (ZMod 7) × S),
      K = _root_.commutator (Multiplicative (ZMod 7) × S) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup (Multiplicative (ZMod 7) × S),
      Z = center (Multiplicative (ZMod 7) × S) := ⟨_, rfl⟩
  haveI : K.Characteristic := by rw [hK]; infer_instance
  haveI : Z.Characteristic := by rw [hZ]; infer_instance
  have hZmem : ∀ a : Multiplicative (ZMod 7), ((a, 1) : Multiplicative (ZMod 7) × S) ∈ Z := by
    intro a
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    exact Prod.ext (mul_comm g.1 a) (by simp)
  have hZle : ∀ x ∈ Z, x.2 = 1 := by
    intro x hx
    rw [hZ, Subgroup.mem_center_iff] at hx
    have h2 : x.2 ∈ center S := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact congrArg Prod.snd (hx ((1 : Multiplicative (ZMod 7)), t))
    rw [hcS, Subgroup.mem_bot] at h2
    exact h2
  have hKmem : ∀ s : S, ((1, s) : Multiplicative (ZMod 7) × S) ∈ K := by
    intro s
    have hs : s ∈ _root_.commutator S := by rw [hpS]; exact Subgroup.mem_top s
    have h1 : (MonoidHom.inr (Multiplicative (ZMod 7)) S) s ∈
        (_root_.commutator S).map (MonoidHom.inr (Multiplicative (ZMod 7)) S) :=
      Subgroup.mem_map_of_mem _ hs
    rw [hK]
    exact ((Subgroup.map_commutator _ _ _).le.trans (Subgroup.commutator_mono le_top le_top)) h1
  have hKle : ∀ x ∈ K, x.1 = 1 := by
    intro x hx
    have hker : K ≤ (MonoidHom.fst (Multiplicative (ZMod 7)) S).ker := by
      rw [hK, _root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    exact hker hx
  let eK : ↥K ≃* S :=
    { toFun := fun x => x.1.2
      invFun := fun s => ⟨(1, s), hKmem s⟩
      left_inv := fun x => Subtype.ext (Prod.ext (hKle x.1 x.2).symm rfl)
      right_inv := fun s => rfl
      map_mul' := fun x y => rfl }
  let eZ : ↥Z ≃* Multiplicative (ZMod 7) :=
    { toFun := fun x => x.1.1
      invFun := fun a => ⟨(a, 1), hZmem a⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl (hZle x.1 x.2).symm)
      right_inv := fun a => rfl
      map_mul' := fun x y => rfl }
  have hZc : Nat.card ↥Z = 7 := by
    rw [Nat.card_congr eZ.toEquiv]
    simp
  haveI : IsCyclic ↥Z := isCyclic_of_prime_card hZc
  have hAutZ : Nat.card (MulAut ↥Z) = 6 := by
    rw [IsCyclic.card_mulAut, hZc, Nat.totient_prime (by norm_num)]
  have hAutK : Nat.card (MulAut ↥K) ∣ 336 := by
    rw [Nat.card_congr (MulAut.congr eK).toEquiv]
    exact card_mulAut_dvd_of_isL3 hS
  let ρ : MulAut (Multiplicative (ZMod 7) × S) →* MulAut ↥K × MulAut ↥Z :=
    (MulAut.characteristic K).prod (MulAut.characteristic Z)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 : MulAut.characteristic K φ = 1 := congrArg Prod.fst hφ
    have h2 : MulAut.characteristic Z φ = 1 := congrArg Prod.snd hφ
    have hfK : ∀ k ∈ K, φ k = k := fun k hk =>
      congrArg (fun f : MulAut ↥K => (f ⟨k, hk⟩ : Multiplicative (ZMod 7) × S)) h1
    have hfZ : ∀ z ∈ Z, φ z = z := fun z hz =>
      congrArg (fun f : MulAut ↥Z => (f ⟨z, hz⟩ : Multiplicative (ZMod 7) × S)) h2
    apply MulEquiv.ext
    rintro ⟨a, s⟩
    have e1 : ((a, s) : Multiplicative (ZMod 7) × S) = (a, 1) * (1, s) := by simp
    rw [e1, map_mul, hfZ _ (hZmem a), hfK _ (hKmem s)]
    rfl
  have hdvd := Subgroup.card_dvd_of_injective ρ hρ
  rw [Nat.card_prod, hAutZ] at hdvd
  exact hdvd.trans (mul_dvd_mul_right hAutK 6)

theorem s16n9b_case7_card_le_seven {F : Type} [Group F] (hS : IsL3 S 1)
    (e : F ≃* Multiplicative (ZMod 7) × S) {A : Subgroup (MulAut F)} (hA : IsElemAbelian 7 A) :
    Nat.card A ≤ 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : Nat.card A ∣ 336 * 6 := by
    refine (Subgroup.card_subgroup_dvd_card A).trans ?_
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact s16n9b_case7_card_mulAut_dvd hS
  haveI : Finite A := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hdvd
    omega
  obtain ⟨j, hj⟩ := hA.isPGroup.exists_card_eq
  rw [hj] at hdvd ⊢
  have hj1 : j ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h49 : 7 ^ 2 ∣ 336 * 6 := (Nat.pow_dvd_pow 7 hlt).trans hdvd
    omega
  calc 7 ^ j ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
    _ = 7 := pow_one 7

theorem s16n9b_case7_card_center_le {F : Type} [Group F] (hS : IsL3 S 1)
    (e : F ≃* Multiplicative (ZMod 7) × S) : Nat.card (center F) ≤ 7 := by
  have hcS : center S = ⊥ := center_eq_bot_of_isL3 hS
  have hsnd : ∀ z : center F, (e z.1).2 = 1 := by
    intro z
    have hz : (e z.1).2 ∈ center S := by
      rw [Subgroup.mem_center_iff]
      intro t
      have h1 := congrArg e (Subgroup.mem_center_iff.mp z.2 (e.symm (1, t)))
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
      exact congrArg Prod.snd h1
    rw [hcS, Subgroup.mem_bot] at hz
    exact hz
  have hinj : Function.Injective (fun x : center F => (e x.1).1) := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    exact Prod.ext h (by rw [hsnd x, hsnd y])
  calc Nat.card (center F) ≤ Nat.card (Multiplicative (ZMod 7)) :=
      Nat.card_le_card_of_injective _ hinj
    _ = 7 := by simp

end Aut

theorem s16n9b_case7_card_le_forty_nine {Γ : Type} [Group Γ] [Finite Γ] {F : Subgroup Γ}
    [F.Normal] (hF : centralizer (F : Set Γ) ≤ F) {S : Type} [Group S] [Finite S]
    (hS : IsL3 S 1) (e : ↥F ≃* Multiplicative (ZMod 7) × S) {E : Subgroup Γ}
    (hE : IsElemAbelian 7 E) :
    Nat.card E ≤ 49 := by
  have h1 := s16n9b_card_le_mul_card_inf_centralizer (p := 7) (U := F) (E := E)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hE (b := 7)
    fun A hA => s16n9b_case7_card_le_seven hS e hA
  have h2 : Nat.card ↥(E ⊓ centralizer (F : Set Γ)) ≤ 7 := by
    have hmem : ∀ x : ↥(E ⊓ centralizer (F : Set Γ)),
        (⟨(x : Γ), hF x.2.2⟩ : ↥F) ∈ center ↥F := by
      intro x
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 (g : Γ) g.2)
    refine le_trans (Nat.card_le_card_of_injective
      (fun x => (⟨⟨(x : Γ), hF x.2.2⟩, hmem x⟩ : center ↥F)) ?_)
      (s16n9b_case7_card_center_le hS e)
    intro x y h
    exact Subtype.ext (congrArg (fun z : center ↥F => ((z : ↥F) : Γ)) h)
  calc Nat.card E ≤ 7 * Nat.card ↥(E ⊓ centralizer (F : Set Γ)) := h1
    _ ≤ 7 * 7 := Nat.mul_le_mul_left 7 h2
    _ = 49 := by norm_num

theorem s16n9b_pRank_lt_of_fstar_zmod7_l3 {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q)
    {S : Type} [Group S] (hS : IsL3 S 1)
    (hF : Nonempty (↥(Fstar H) ≃* (Multiplicative (ZMod 7) × S))) :
    CFSG.Open.pRank 7 H < 3 := by
  classical
  obtain ⟨e'⟩ := hF
  haveI : Finite ↥H := Subtype.finite
  haveI : Finite S := Finite.of_injective
    (fun s : S => e'.symm ((1 : Multiplicative (ZMod 7)), s)) fun a b h =>
      (Prod.mk.inj (e'.symm.injective h)).2
  haveI hnorm : (genFittingFStar ↥H).Normal :=
    CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal
  have hself : centralizer (genFittingFStar ↥H : Set ↥H) ≤ genFittingFStar ↥H :=
    CFSG.ClassicalInvolution.Q3.centralizer_genFittingFStar_le
  let e₀ : ↥(genFittingFStar ↥H) ≃* Multiplicative (ZMod 7) × S :=
    (Subgroup.equivMapOfInjective (genFittingFStar ↥H) H.subtype H.subtype_injective).trans e'
  have h1 : CFSG.Open.pRank 7 H = CFSG.Open.pRank 7 (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
  have h2 : CFSG.Open.pRank 7 (⊤ : Subgroup ↥H) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    have h49 := s16n9b_case7_card_le_forty_nine hself hS e₀ hE
    simpa using h49
  omega

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case7_pRank_lt (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h7 : Case168_7 D V₀ V hV L) : CFSG.Open.pRank 7 (Mbar D.M V₀ V hV) < 3 :=
  s16n9b_pRank_lt_of_fstar_zmod7_l3 _ h7.2.1 h7.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
