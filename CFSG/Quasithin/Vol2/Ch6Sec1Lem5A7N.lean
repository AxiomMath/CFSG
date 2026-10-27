module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5A7S
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5A7M
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E

public section

namespace CFSG.Quasithin.H13.A7N

open Equiv Equiv.Perm CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open A7S A7M CFSG.QuasithinUnique.Setup.SL2Modules Module
open scoped commutatorElement

theorem trList_fix_checks_ch615 : (trList.all fun t => decide (t 6 = 6)) = true := by
  decide +kernel

theorem fix_six_of_swap_ch615 {x : Perm (Fin 7)} (hx : x ∈ stab4)
    (h : swap (x 4) (x 5) ∈ trList) : x 6 = 6 := by
  have h6 : swap (x 4) (x 5) 6 = 6 := by
    have := List.all_eq_true.mp trList_fix_checks_ch615 _ h
    simpa using this
  have hge : ∀ i : Fin 7, 4 ≤ (i : ℕ) → 4 ≤ ((x i : Fin 7) : ℕ) := fun i hi => by
    by_contra hlt
    have := (hx i).mpr (by omega)
    omega
  have hne : ∀ i j : Fin 7, i ≠ j → ((x i : Fin 7) : ℕ) ≠ ((x j : Fin 7) : ℕ) := fun i j hij e =>
    hij (x.injective (Fin.ext e))
  by_contra h66
  have h66' : ((x 6 : Fin 7) : ℕ) ≠ 6 := fun e => h66 (Fin.ext e)
  have l4 := (x 4).isLt
  have l5 := (x 5).isLt
  have l6 := (x 6).isLt
  have g4 := hge 4 (by decide)
  have g5 := hge 5 (by decide)
  have g6 := hge 6 (by decide)
  have n45 := hne 4 5 (by decide)
  have n46 := hne 4 6 (by decide)
  have n56 := hne 5 6 (by decide)
  rcases (by omega : ((x 4 : Fin 7) : ℕ) = 6 ∨ ((x 5 : Fin 7) : ℕ) = 6) with e | e
  · have e' : x 4 = 6 := Fin.ext e
    rw [e', swap_apply_left] at h6
    exact n45 (by rw [e, h6]; rfl)
  · have e' : x 5 = 6 := Fin.ext e
    rw [e', swap_apply_right] at h6
    exact n45 (by rw [h6, e]; rfl)

section Coords

variable {V : Type} [CommGroup V]

theorem coords_alt7_ch615 {F : Subgroup (MulAut V)} (h : AlternatingNatural F (commV F) ⊥ 7)
    (htop : commV F = ⊤) :
    ∃ (ι : ↥F ≃* ↥(alternatingGroup (Fin 7))) (β : V ≃* ↥(G6.coreMod 7)),
      ∀ (f : ↥F) (v : V), (β ((f : MulAut V) v) : G6.PermMod 7) = G6.permAct 7 (ι f) (β v) := by
  obtain ⟨π₀, hπ₀⟩ := h
  let π : ↥(alternatingGroup (Fin 7)) →* ↥F := π₀
  have hπ : (FFModel.altDn 7).RealizesVia F (commV F) ⊥ π := hπ₀
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  obtain ⟨hsurj, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := hπ
  let K : Subgroup ↥(G6.coreMod 7) :=
    (Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7).subgroupOf (G6.coreMod 7)
  let β₁ : ↥(commV F) →* ↥(G6.coreMod 7) ⧸ K := β₀
  have hK : K = ⊥ := by
    show (Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7).subgroupOf (G6.coreMod 7) = ⊥
    rw [Vol2.Ch10.SecB.C11AmS.K8.dnZ_seven, Subgroup.bot_subgroupOf]
  have hβi : Function.Injective β₁ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβk u).1 hu
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  let qe : (↥(G6.coreMod 7) ⧸ K) ≃* ↥(G6.coreMod 7) :=
    (QuotientGroup.quotientMulEquivOfEq hK).trans QuotientGroup.quotientBot
  have hqe : ∀ m : ↥(G6.coreMod 7), qe (QuotientGroup.mk m) = m := fun _ => rfl
  let eV : V ≃* ↥(commV F) := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  let eπ : ↥(alternatingGroup (Fin 7)) ≃* ↥F := MulEquiv.ofBijective π ⟨hinj, hsurj⟩
  refine ⟨eπ.symm, (eV.trans (MulEquiv.ofBijective β₁ ⟨hβi, hβs⟩)).trans qe, fun f v => ?_⟩
  have hmk : β₁ (eV v) = QuotientGroup.mk (qe (β₁ (eV v))) := qe.injective (by rw [hqe])
  have hf : π (eπ.symm f) = f := eπ.apply_symm_apply f
  have hu : ((π (eπ.symm f) : ↥F) : MulAut V) ((eV v : ↥(commV F)) : V) ∈ commV F :=
    (Subgroup.eq_top_iff' _).1 htop _
  have hm' : G6.permAct 7 ((eπ.symm f : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))
      ((qe (β₁ (eV v)) : ↥(G6.coreMod 7)) : G6.PermMod 7) ∈ G6.coreMod 7 :=
    G6.permAct_mem_coreMod _ (qe (β₁ (eV v))).2
  have he := hβe (eπ.symm f) (eV v) (qe (β₁ (eV v))) hu hm' hmk
  have hval : (⟨((π (eπ.symm f) : ↥F) : MulAut V) ((eV v : ↥(commV F)) : V), hu⟩ :
      ↥(commV F)) = eV ((f : MulAut V) v) :=
    Subtype.ext (congrArg (fun g : ↥F => (g : MulAut V) v) hf)
  have key : β₁ (eV ((f : MulAut V) v)) = QuotientGroup.mk ⟨_, hm'⟩ := by
    rw [← hval]
    exact he
  show ((qe (β₁ (eV ((f : MulAut V) v))) : ↥(G6.coreMod 7)) : G6.PermMod 7) =
    G6.permAct 7 ((eπ.symm f : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))
      ((qe (β₁ (eV v)) : ↥(G6.coreMod 7)) : G6.PermMod 7)
  rw [key, hqe]

end Coords

theorem card_evenWeight_inf_ch615 (P : Subgroup (Perm (Fin 7))) :
    Nat.card ↥(evenWeight (Fin 7) ⊓ fixedVectors P) =
      2 ^ finrank (ZMod 2) ↥(evenWeight (Fin 7) ⊓ fixedVectors P) := by
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := ↥(evenWeight (Fin 7) ⊓ fixedVectors P))
  rw [Nat.card_zmod] at h
  exact h

section Config

variable {V : Type} [CommGroup V] {F : Subgroup (MulAut V)}

theorem five_or_six_ch615 {S : Subgroup (MulAut V)}
    (ι : ↥F ≃* ↥(alternatingGroup (Fin 7))) (hSF : S ≤ F)
    (hDS : ∀ d ∈ Even7.D, ∃ s, ∃ hs : s ∈ S, (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) = d)
    {R₁ R₂ : Subgroup (MulAut V)} (h1S : S ≤ R₁) (h1F : R₁ ≤ F) (h1ne : R₁ ≠ S)
    (h1s : Group.IsSolvable ↥R₁) (h2S : S ≤ R₂) (h2F : R₂ ≤ F) (h2ne : R₂ ≠ S)
    (h2s : Group.IsSolvable ↥R₂) (hgen : F ≤ R₁ ⊔ R₂) :
    (∀ x (hx : x ∈ R₂), (ι ⟨x, h2F hx⟩ : Perm (Fin 7)) ∈ Even7.Lm 5) ∨
      ((∀ x (hx : x ∈ R₁), (ι ⟨x, h1F hx⟩ : Perm (Fin 7)) ∈ Even7.Lm 5) ∧
        ∀ x (hx : x ∈ R₂), (ι ⟨x, h2F hx⟩ : Perm (Fin 7)) ∈ Even7.Lm 6) := by
  classical
  set img : Subgroup (MulAut V) → Subgroup (Perm (Fin 7)) := fun R =>
    ((R.subgroupOf F).map ι.toMonoidHom).map (alternatingGroup (Fin 7)).subtype with himg
  have hin : ∀ (R : Subgroup (MulAut V)) (f : ↥F), (f : MulAut V) ∈ R →
      (ι f : Perm (Fin 7)) ∈ img R := fun R f hf =>
    ⟨ι f, ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩, rfl⟩
  have hout : ∀ (R : Subgroup (MulAut V)) (z : Perm (Fin 7)), z ∈ img R →
      ∃ f : ↥F, (f : MulAut V) ∈ R ∧ (ι f : Perm (Fin 7)) = z := by
    rintro R _ ⟨y, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, Subgroup.mem_subgroupOf.mp hf, rfl⟩
  have hA : ∀ R, img R ≤ alternatingGroup (Fin 7) := fun R => by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hD : ∀ R, S ≤ R → Even7.D ≤ img R := fun R hSR d hd => by
    obtain ⟨s, hs, rfl⟩ := hDS d hd
    exact hin R _ (hSR hs)
  have hrefl : ∀ R R' : Subgroup (MulAut V), R ≤ F → img R ≤ img R' → R ≤ R' := by
    intro R R' hRF h x hx
    obtain ⟨f, hf, hfx⟩ := hout R' _ (h (hin R ⟨x, hRF hx⟩ hx))
    have : f = ⟨x, hRF hx⟩ := ι.injective (Subtype.ext hfx)
    rw [this] at hf
    exact hf
  have hne : ∀ R, S ≤ R → R ≤ F → R ≠ S → img R ≠ Even7.D := by
    intro R hSR hRF hRS h
    refine hRS (le_antisymm (hrefl R S hRF ?_) hSR)
    rw [h]
    exact hD S le_rfl
  have hsolv : ∀ R, R ≤ F → Group.IsSolvable ↥R → Group.IsSolvable ↥(img R) := fun R hRF hR => by
    have := hR
    have : Group.IsSolvable ↥((R.subgroupOf F).map ι.toMonoidHom) :=
      Group.isSolvable_of_surjective
        (f := ((Subgroup.subgroupOfEquivOfLe hRF).symm.trans
          (Subgroup.equivMapOfInjective _ ι.toMonoidHom ι.injective)).toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective
      ((alternatingGroup (Fin 7)).subtype.subgroupMap_surjective _)
  have hgen' : alternatingGroup (Fin 7) ≤ img R₁ ⊔ img R₂ := by
    intro z hz
    have h1 : img (R₁ ⊔ R₂) = img R₁ ⊔ img R₂ := by
      simp only [himg]
      rw [Subgroup.subgroupOf_sup h1F h2F, Subgroup.map_sup, Subgroup.map_sup]
    rw [← h1]
    have := hin (R₁ ⊔ R₂) (ι.symm ⟨z, hz⟩) (hgen (ι.symm ⟨z, hz⟩).2)
    rwa [MulEquiv.apply_symm_apply] at this
  have himg_le : ∀ R (hRF : R ≤ F) (Y : Subgroup (Perm (Fin 7))), img R ≤ Y →
      ∀ x (hx : x ∈ R), (ι ⟨x, hRF hx⟩ : Perm (Fin 7)) ∈ Y := fun R hRF Y h x hx =>
    h (hin R _ hx)
  by_cases h5 : img R₂ = Even7.Lm 5
  · exact Or.inl (himg_le R₂ h2F _ h5.le)
  · have h15 : img R₁ = Even7.Lm 5 := by
      rcases Even7.eq_five_of_gen_ch615 (hD R₁ h1S) (hA R₁) (hne R₁ h1S h1F h1ne)
        (hsolv R₁ h1F h1s) (hD R₂ h2S) (hA R₂) (hne R₂ h2S h2F h2ne) (hsolv R₂ h2F h2s)
        hgen' with h | h
      · exact h
      · exact absurd h h5
    obtain ⟨b, hb1, hb6, hb⟩ := Even7.idx_of_solvable_ch615 (hD R₂ h2S) (hA R₂)
      (hne R₂ h2S h2F h2ne) (hsolv R₂ h2F h2s)
    have hb5 : b ≠ 5 := fun h => h5 (by rw [hb, h])
    rw [h15, hb] at hgen'
    exact Or.inr ⟨himg_le R₁ h1F _ h15.le, himg_le R₂ h2F _
      (hb.le.trans (le_six_of_gen_ch615 hb1 hb6 hb5 hgen'))⟩

variable (ι : ↥F ≃* ↥(alternatingGroup (Fin 7))) (β : V ≃* ↥(G6.coreMod 7))
  (hβ : ∀ (f : ↥F) (v : V), (β ((f : MulAut V) v) : G6.PermMod 7) = G6.permAct 7 (ι f) (β v))
include hβ

theorem fix_iff_ch615 (x : ↥(Subgroup.normalizer (F : Set (MulAut V)))) (v : V) :
    (x : MulAut V) v = v ↔ G6.permAct 7 (sig_ch615 ι x) (β v) = β v := by
  constructor
  · intro h
    rw [← sig_spec_ch615 ι β hβ x v, h]
  · intro h
    have := sig_spec_ch615 ι β hβ x v
    rw [h] at this
    exact β.injective (Subtype.ext this)

omit hβ in
theorem sig_mem_normalizer_ch615 {S : Subgroup (MulAut V)} (hSF : S ≤ F)
    (hSD : ∀ s (hs : s ∈ S), (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) ∈ Even7.D)
    (hDS : ∀ d ∈ Even7.D, ∃ s, ∃ hs : s ∈ S, (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) = d)
    (t : ↥(Subgroup.normalizer (F : Set (MulAut V))))
    (htS : ∀ s ∈ S, (t : MulAut V) * s * (t : MulAut V)⁻¹ ∈ S) :
    sig_ch615 ι t ∈ Subgroup.normalizer (Even7.D : Set (Perm (Fin 7))) := by
  refine mem_normalizer_of_conj_mem_ch615 fun d hd => ?_
  obtain ⟨s, hs, rfl⟩ := hDS d hd
  have hts := htS s hs
  have e : sig_ch615 ι t * (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) * (sig_ch615 ι t)⁻¹ =
      (ι ⟨(t : MulAut V) * s * (t : MulAut V)⁻¹, hSF hts⟩ : Perm (Fin 7)) := by
    rw [← sig_of_mem_ch615 ι ⟨s, hSF hs⟩, ← sig_of_mem_ch615 ι ⟨_, hSF hts⟩, ← map_mul,
      ← map_inv, ← map_mul]
    congr 1
  rw [e]
  exact hSD _ hts

omit hβ in
theorem imgS_mono_ch615 {A B : Subgroup (MulAut V)} (h : A ≤ B) :
    imgS_ch615 ι A ≤ imgS_ch615 ι B := fun z hz => by
  obtain ⟨x, hx, rfl⟩ := (mem_imgS_ch615 ι).mp hz
  exact (mem_imgS_ch615 ι).mpr ⟨x, h hx, rfl⟩

theorem good_ch615 {S Tx : Subgroup (MulAut V)} (hSF : S ≤ F)
    (hSD : ∀ s (hs : s ∈ S), (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) ∈ Even7.D)
    (hDS : ∀ d ∈ Even7.D, ∃ s, ∃ hs : s ∈ S, (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) = d)
    (hTN : Tx ≤ Subgroup.normalizer (F : Set (MulAut V)))
    (hTS : ∀ t ∈ Tx, ∀ s ∈ S, t * s * t⁻¹ ∈ S) {d : MulAut V} (hdF : d ∈ F)
    (hd5 : (ι ⟨d, hdF⟩ : Perm (Fin 7)) ∈ Even7.Lm 5) :
    ∃ w : V, w ≠ 1 ∧ (∀ t ∈ Tx, t w = w) ∧ d w = w ∧
      ∃ G₁ : Subgroup (MulAut V), G₁ ≤ F ∧ IsSimpleGroup ↥G₁ ∧ ¬ Group.IsSolvable ↥G₁ ∧
        d ∈ G₁ ∧ ∀ g ∈ G₁, g w = w := by
  set w := β.symm ⟨vc, vc_mem⟩ with hw
  have hβw : (β w : G6.PermMod 7) = vc := by rw [hw, MulEquiv.apply_symm_apply]
  have hfixw : ∀ x : ↥(Subgroup.normalizer (F : Set (MulAut V))), sig_ch615 ι x 6 = 6 →
      (x : MulAut V) w = w := fun x hx =>
    (fix_iff_ch615 ι β hβ x w).mpr (by rw [hβw]; exact permAct_vc hx)
  have hfixF : ∀ f : ↥F, (ι f : Perm (Fin 7)) 6 = 6 → (f : MulAut V) w = w := fun f hf =>
    hfixw ⟨f, Subgroup.le_normalizer f.2⟩ (by rw [sig_of_mem_ch615]; exact hf)
  refine ⟨w, fun h => vc_ne_one ?_, fun t ht => hfixw ⟨t, hTN ht⟩
    (fix_six_of_mem_normalizer (sig_mem_normalizer_ch615 ι hSF hSD hDS _ (hTS t ht))),
    hfixF ⟨d, hdF⟩ (fix_six_of_mem_five hd5), ?_⟩
  · rw [← hβw, h, map_one]
    rfl
  set St := alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) with hSt
  set G₁ := ((St.subgroupOf (alternatingGroup (Fin 7))).map ι.symm.toMonoidHom).map F.subtype
    with hG₁
  have eG : ↥G₁ ≃* ↥St :=
    ((Subgroup.equivMapOfInjective _ F.subtype F.subtype_injective).symm.trans
      (Subgroup.equivMapOfInjective _ ι.symm.toMonoidHom ι.symm.injective).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  refine ⟨G₁, fun g hg => by obtain ⟨f, -, rfl⟩ := hg; exact f.2, ?_, ?_, ?_, ?_⟩
  · have := isSimpleGroup_altStab_ch615
    exact eG.isSimpleGroup
  · intro h
    have := h
    exact not_isSolvable_altStab_ch615 (Group.isSolvable_of_surjective (f := eG.toMonoidHom)
      eG.surjective)
  · refine ⟨⟨d, hdF⟩, ⟨ι ⟨d, hdF⟩, Subgroup.mem_subgroupOf.mpr
      ⟨(ι ⟨d, hdF⟩).2, fix_six_of_mem_five hd5⟩, by simp⟩, rfl⟩
  · rintro _ ⟨f, ⟨a, ha, rfl⟩, rfl⟩
    refine hfixF _ ?_
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_subgroupOf.mp ha).2

variable [Finite V]

theorem bad_ch615 {S Tx Jx Kx : Subgroup (MulAut V)} (hSF : S ≤ F)
    (hSD : ∀ s (hs : s ∈ S), (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) ∈ Even7.D)
    (hDS : ∀ d ∈ Even7.D, ∃ s, ∃ hs : s ∈ S, (ι ⟨s, hSF hs⟩ : Perm (Fin 7)) = d)
    (hTN : Tx ≤ Subgroup.normalizer (F : Set (MulAut V)))
    (hTS : ∀ t ∈ Tx, ∀ s ∈ S, t * s * t⁻¹ ∈ S) (hJT : Jx ≤ Tx)
    (hJgen : Jx ≤ Subgroup.closure {y | ∃ A : Subgroup (MulAut V), A ≤ Jx ∧
      IsFFStarOffender Tx A ∧ y ∈ A})
    (hKF : Kx ≤ F) (hK5 : ∀ k (hk : k ∈ Kx), (ι ⟨k, hKF hk⟩ : Perm (Fin 7)) ∈ Even7.Lm 5)
    (hKJ : Kx ≤ ⁅Kx, Jx⁆) {d : MulAut V} (hdF : d ∈ F)
    (hd6 : (ι ⟨d, hdF⟩ : Perm (Fin 7)) ∈ Even7.Lm 6) (hdJ : ∀ j ∈ Jx, d * j * d⁻¹ ∈ Jx) :
    (∀ v, (∀ s ∈ S, s v = v) → d v = v) ∨ IsPGroup 2 ↥Kx := by
  classical
  set N := Subgroup.normalizer (F : Set (MulAut V)) with hN
  have hσT : ∀ t (ht : t ∈ Tx), sig_ch615 ι ⟨t, hTN ht⟩ ∈
      Subgroup.normalizer (Even7.D : Set (Perm (Fin 7))) := fun t ht =>
    sig_mem_normalizer_ch615 ι hSF hSD hDS _ (hTS t ht)
  by_cases hc : (swap 4 5 : Perm (Fin 7)) ∈ imgS_ch615 ι Jx
  · left
    obtain ⟨j, hjJ, hjσ⟩ := (mem_imgS_ch615 ι).mp hc
    set dN : ↥N := ⟨d, Subgroup.le_normalizer hdF⟩ with hdN
    have hσd : sig_ch615 ι dN = (ι ⟨d, hdF⟩ : Perm (Fin 7)) := sig_of_mem_ch615 ι ⟨d, hdF⟩
    have hdj : d * (j : MulAut V) * d⁻¹ ∈ Jx := hdJ _ hjJ
    have h1 : sig_ch615 ι (dN * j * dN⁻¹) ∈
        Subgroup.normalizer (Even7.D : Set (Perm (Fin 7))) := by
      have e : dN * j * dN⁻¹ = ⟨d * (j : MulAut V) * d⁻¹, hTN (hJT hdj)⟩ := Subtype.ext rfl
      rw [e]
      exact hσT _ (hJT hdj)
    rw [map_mul, map_mul, map_inv, hjσ, hσd, ← swap_apply_apply] at h1
    have hne : (ι ⟨d, hdF⟩ : Perm (Fin 7)) 4 ≠ (ι ⟨d, hdF⟩ : Perm (Fin 7)) 5 := fun e =>
      absurd ((ι ⟨d, hdF⟩ : Perm (Fin 7)).injective e) (by decide)
    have h4 := six_le_stab4 hd6
    have h6 := fix_six_of_swap_ch615 h4 (mem_trList_of_mem_normalizer hne h1)
    intro v hv
    refine (fix_iff_ch615 ι β hβ dN v).mpr ?_
    rw [hσd]
    refine permAct_of_fixD h6 h4 fun d' hd' => ?_
    obtain ⟨s, hs, rfl⟩ := hDS d' hd'
    rw [← hβ]
    exact congrArg (fun x : ↥(G6.coreMod 7) => (x : G6.PermMod 7)) (congrArg β (hv s hs))
  · right
    set C := Subgroup.closure {g : Perm (Fin 7) | g ∈ j1List} with hC
    have hmem : ∀ (Y : Subgroup (Perm (Fin 7))) (x : ↥N),
        (x : MulAut V) ∈ (Y.comap (sig_ch615 ι)).map N.subtype ↔ sig_ch615 ι x ∈ Y := by
      intro Y x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro h
        exact ⟨x, h, rfl⟩
    have hJC : Jx ≤ (C.comap (sig_ch615 ι)).map N.subtype := by
      refine hJgen.trans ((Subgroup.closure_le _).mpr ?_)
      rintro y ⟨A, hAJ, hoff, hyA⟩
      have hAN : A ≤ N := (hAJ.trans hJT).trans hTN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := B1.isElementaryAbelian_of_isElemAbelian2 hoff.2.2.1
      have : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf N) :=
        CFSG.IsElementaryAbelian.subgroupOf hAN
      have : CFSG.IsElementaryAbelian 2 ↥(imgS_ch615 ι A) :=
        CFSG.IsElementaryAbelian.map (sig_ch615 ι)
      obtain ⟨r, hr⟩ : ∃ r, Nat.card ↥A = 2 ^ r := ⟨_, B1.card_elemAbelian hoff.2.2.1⟩
      have hcard : Nat.card ↥(imgS_ch615 ι A) = 2 ^ r := by
        rw [card_imgS_ch615 ι β hβ hAN, hr]
      have himgN : imgS_ch615 ι A ≤ Subgroup.normalizer (Even7.D : Set (Perm (Fin 7))) := by
        intro z hz
        obtain ⟨x, hxA, rfl⟩ := (mem_imgS_ch615 ι).mp hz
        exact hσT _ (hJT (hAJ hxA))
      have hfin : 6 ≤ finrank (ZMod 2)
          ↥(evenWeight (Fin 7) ⊓ fixedVectors (imgS_ch615 ι A)) + r := by
        have h0 := hoff.2.2.2 ⊥ bot_le
        rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul,
          Nat.card_congr β.toEquiv, B45Alt7.card_coreMod7, hr, card_fixV_imgS_ch615 ι β hβ hAN,
          card_evenWeight_inf_ch615, ← pow_add] at h0
        rw [add_comm]
        exact (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).1 (by simpa using h0)
      have hle := le_closure_trList_ch615 hcard himgN hfin
      have hgen : {t : Perm (Fin 7) | t ∈ trList ∧ t ∈ imgS_ch615 ι A} ⊆
          {g | g ∈ j1List} := by
        rintro t ⟨ht, htA⟩
        have ht' : t ≠ swap 4 5 := fun e => hc (e ▸ imgS_mono_ch615 ι hAJ htA)
        simp only [trList, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · simp [j1List]
        · simp [j1List]
        · exact absurd rfl ht'
      exact (hmem C ⟨y, hAN hyA⟩).mpr
        (Subgroup.closure_mono hgen (hle ((mem_imgS_ch615 ι).mpr ⟨⟨y, hAN hyA⟩, hyA, rfl⟩)))
    have hKJQ : ⁅Kx, Jx⁆ ≤ (qSub.comap (sig_ch615 ι)).map N.subtype := by
      rw [Subgroup.commutator_le]
      intro k hk j hj
      set kN : ↥N := ⟨k, Subgroup.le_normalizer (hKF hk)⟩ with hkN
      set jN : ↥N := ⟨j, hTN (hJT hj)⟩ with hjN
      have hσk : sig_ch615 ι kN = (ι ⟨k, hKF hk⟩ : Perm (Fin 7)) := sig_of_mem_ch615 ι ⟨k, hKF hk⟩
      have h1 : sig_ch615 ι ⁅kN, jN⁆ ∈ qSub := by
        rw [map_commutatorElement]
        refine comm_five_le_qSub (Subgroup.commutator_mem_commutator ?_ ?_)
        · rw [hσk]
          exact hK5 k hk
        · exact (hmem C jN).mp (hJC hj)
      exact (hmem qSub ⁅kN, jN⁆).mpr h1
    intro g
    obtain ⟨y, hy, hyg⟩ := hKJQ (hKJ g.2)
    have hsq := sq_of_mem_qSub hy
    have h1 : y * y = 1 := sig_injective_ch615 ι β hβ (by rw [map_mul, hsq, map_one])
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hyg]
    exact congrArg Subtype.val h1

end Config

end CFSG.Quasithin.H13.A7N
