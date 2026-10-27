module

public import CFSG.Quasithin.EmptyFaithful.S14620A
public import CFSG.Quasithin.EmptyFaithful.S14620B
public import CFSG.Quasithin.EmptyFaithful.S14620C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.C2Push CFSG.LieType.BorelTits

section K0

variable {G : Type} [Group G]

theorem mk_mem_normalizer_imageOTwoQuot_of_mem {X A : Subgroup G} {s : G} (hs : s ∈ X)
    (hA : s ∈ Subgroup.normalizer (A : Set G)) :
    (QuotientGroup.mk ⟨s, hs⟩ : OTwoQuot X) ∈
      Subgroup.normalizer (imageOTwoQuot X A : Set (OTwoQuot X)) := by
  have h1 : conjSub s A = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hA
  have h2 := imageOTwoQuot_conjSub (X := X) (K := A) hs
  rw [h1] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2.symm

end K0

section Inner

variable {Y : Type*} [Group Y]

theorem mem_normalizer_of_inner {L P E : Subgroup Y} {s c k : Y} (hPE : P ≤ E) (hEL : E ≤ L)
    (hk : k ∈ L) (hs : s = c * k) (hc : ∀ w ∈ L, c * w * c⁻¹ = w)
    (hsP : ∀ y ∈ P, s * y * s⁻¹ ∈ P) (hP : ∀ x ∈ L, (∀ y ∈ P, x * y * x⁻¹ ∈ P) → x ∈ P) :
    s ∈ Subgroup.normalizer (E : Set Y) := by
  have hc' : ∀ w ∈ L, c⁻¹ * w * c = w := fun w hw => by
    have h := hc w hw
    calc c⁻¹ * w * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [h]
      _ = w := by group
  have hPL : P ≤ L := hPE.trans hEL
  have hkc : k = c⁻¹ * s := by rw [hs]; group
  have hknorm : ∀ y ∈ P, k * y * k⁻¹ ∈ P := by
    intro y hy
    have h1 : k * y * k⁻¹ = c⁻¹ * (s * y * s⁻¹) * c := by rw [hkc]; group
    rw [h1, hc' _ (hPL (hsP y hy))]
    exact hsP y hy
  have hkP : k ∈ P := hP k hk hknorm
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have h1 : s * u * s⁻¹ = c * (k * u * k⁻¹) * c⁻¹ := by rw [hs]; group
    have h2 : k * u * k⁻¹ ∈ E := E.mul_mem (E.mul_mem (hPE hkP) hu) (E.inv_mem (hPE hkP))
    rw [h1, hc _ (hEL h2)]
    exact h2
  · intro hw
    have h1 : u = k⁻¹ * (c⁻¹ * (s * u * s⁻¹) * c) * k := by rw [hs]; group
    rw [h1, hc' _ (hEL hw)]
    exact E.mul_mem (E.mul_mem (E.inv_mem (hPE hkP)) hw) (hPE hkP)

end Inner

section Main

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
private theorem sl3_center_trivial :
    ∀ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), (∀ y, y * x = x * y) → x = 1 := by
  have := slThree_isSimple
  intro x hx
  have hxc : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Subgroup.mem_center_iff.mpr hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) with h | h
  · exact Subgroup.mem_bot.mp (h ▸ hxc)
  · exfalso
    obtain ⟨a, b, hab⟩ := slThree_nonabelian
    have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := h ▸ trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

private theorem trivial_centre_of_mulEquiv_sl3 {Y : Type*} [Group Y] {L : Subgroup Y}
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1 := by
  intro x hx hc
  have h1 : e ⟨x, hx⟩ = 1 := by
    refine sl3_center_trivial _ fun y => ?_
    have hy := hc (e.symm y : ↥L) (e.symm y).2
    have h2 : (e.symm y) * (⟨x, hx⟩ : ↥L) = (⟨x, hx⟩ : ↥L) * (e.symm y) := Subtype.ext hy
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  have : (⟨x, hx⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

end Main

section K0Main

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven in
theorem input14620K0 : Input14620K0 := by
  intro G _ _ K T hsyl hKc hpair hL3 hinner
  obtain ⟨t, htT, htK, hK₀, hcomm⟩ := hpair
  set K₀ : Subgroup G := conjClosure K T with hK₀def
  set X : Subgroup G := K₀ ⊔ T with hXdef
  have hTX : T ≤ X := le_sup_right
  have htX : t ∈ X := hTX htT
  have hKX : K ≤ X := le_of_mem_cComp hKc
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hTN₀ : T ≤ Subgroup.normalizer (K₀ : Set G) := le_normalizer_conjClosure K T
  have hKtc : conjSub t K ∈ cComp X := map_conj_mem_cComp hKc htX
  have hKtX : conjSub t K ≤ X := le_of_mem_cComp hKtc
  have hXK : X = (K ⊔ conjSub t K) ⊔ T := by rw [hXdef, hK₀]
  set Kh : Subgroup (OTwoQuot X) := imageOTwoQuot X K with hKh
  set Kth : Subgroup (OTwoQuot X) := imageOTwoQuot X (conjSub t K) with hKth
  set Th : Subgroup (OTwoQuot X) := imageOTwoQuot X T with hTh
  set th : OTwoQuot X := QuotientGroup.mk ⟨t, htX⟩ with hth
  have hKth' : Kth = conjSub th Kh := imageOTwoQuot_conjSub htX
  obtain ⟨eK⟩ := hL3
  obtain ⟨eI⟩ := nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (subnormal_of_mem_cComp hKc)
  let e₁ : ↥Kh ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (eI.symm.trans (kbarEquiv K).symm).trans eK
  have hsimple := slThree_isSimple
  have hKsimple : IsSimpleGroup ↥Kh := MulEquiv.isSimpleGroup e₁
  have hKz := trivial_centre_of_mulEquiv_sl3 e₁
  let eKt : ↥Kth ≃* ↥Kh :=
    (MulEquiv.subgroupCongr hKth').trans (MulEquiv.subgroupMap (MulAut.conj th) Kh).symm
  have hKtsimple : IsSimpleGroup ↥Kth := MulEquiv.isSimpleGroup eKt
  have hKtz := trivial_centre_of_mulEquiv_sl3 (eKt.trans e₁)
  have hcard : Nat.card ↥Kh = Nat.card ↥Kth := (Nat.card_congr eKt.toEquiv).symm
  have hcent : Kh ≤ Subgroup.centralizer (Kth : Set (OTwoQuot X)) :=
    imageOTwoQuot_le_centralizer fun x hx c hc => by
      have := hcomm (Subgroup.commutator_mem_commutator hx hc)
      simpa [commutatorElement_def] using this
  have hAB : ∀ a ∈ Kh, ∀ b ∈ Kth, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hcent ha)) b hb).symm
  have hAB' : ∀ a ∈ Kth, ∀ b ∈ Kh, a * b = b * a := fun a ha b hb => (hAB b hb a ha).symm
  have hjoin : Kh ⊔ Kth = imageOTwoQuot X K₀ := by
    rw [hK₀, imageOTwoQuot_sup hKX hKtX]
  have hnormX : ∀ s (hs : s ∈ T), (QuotientGroup.mk ⟨s, hTX hs⟩ : OTwoQuot X) ∈
      Subgroup.normalizer ((Kh ⊔ Kth : Subgroup (OTwoQuot X)) : Set (OTwoQuot X)) := by
    intro s hs
    rw [hjoin]
    exact mk_mem_normalizer_imageOTwoQuot_of_mem (hTX hs) (hTN₀ hs)
  have hperm : ∀ s ∈ T, s ∈ Subgroup.normalizer (K : Set G) ∨
      t⁻¹ * s ∈ Subgroup.normalizer (K : Set G) := by
    intro s hs
    have hsX : s ∈ X := hTX hs
    rcases conjSub_eq_or_eq_of_commuting hAB hKsimple hKz hcard (hnormX s hs) with h | h
    · left
      apply le_normalizer_of_mk_mem_normalizer_imageOTwoQuot hKc hsX
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    · right
      have htsX : t⁻¹ * s ∈ X := X.mul_mem (X.inv_mem htX) hsX
      apply le_normalizer_of_mk_mem_normalizer_imageOTwoQuot hKc htsX
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      have e1 : (QuotientGroup.mk ⟨t⁻¹ * s, htsX⟩ : OTwoQuot X) =
          th⁻¹ * QuotientGroup.mk ⟨s, hsX⟩ := by
        rw [hth, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [e1]
      show conjSub (th⁻¹ * QuotientGroup.mk ⟨s, hsX⟩) Kh = Kh
      rw [conjSub_mul, h, hKth', conjSub_conjSub_inv]
  have hperm2 : ∀ d ∈ T, d ∈ Subgroup.normalizer (K : Set G) →
      t⁻¹ * d * t ∈ Subgroup.normalizer (K : Set G) := by
    intro d hd hdK
    have hdX : d ∈ X := hTX hd
    have hdKh : conjSub (QuotientGroup.mk ⟨d, hdX⟩ : OTwoQuot X) Kh = Kh :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (mk_mem_normalizer_imageOTwoQuot_of_mem hdX hdK)
    have hnormX' : (QuotientGroup.mk ⟨d, hdX⟩ : OTwoQuot X) ∈
        Subgroup.normalizer ((Kth ⊔ Kh : Subgroup (OTwoQuot X)) : Set (OTwoQuot X)) := by
      rw [sup_comm]
      exact hnormX d hd
    have hdKt : d ∈ Subgroup.normalizer (conjSub t K : Set G) := by
      apply le_normalizer_of_mk_mem_normalizer_imageOTwoQuot hKtc hdX
      rcases conjSub_eq_or_eq_of_commuting hAB' hKtsimple hKtz hcard.symm hnormX' with h | h
      · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
      · exfalso
        have h1 : Kth = Kh := by
          have : conjSub (QuotientGroup.mk ⟨d, hdX⟩ : OTwoQuot X) Kth =
              conjSub (QuotientGroup.mk ⟨d, hdX⟩ : OTwoQuot X) Kh := by rw [h, hdKh]
          exact (conjSub_inj _).mp this
        apply htK
        apply le_normalizer_of_mk_mem_normalizer_imageOTwoQuot hKc htX
        apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        show conjSub th Kh = Kh
        rw [← hKth', h1]
    have h2 : conjSub d (conjSub t K) = conjSub t K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hdKt
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    show conjSub (t⁻¹ * d * t) K = K
    rw [conjSub_mul, conjSub_mul, h2, conjSub_conjSub_inv]
  have ht2 : t * t ∈ Subgroup.normalizer (K : Set G) := by
    rcases hperm (t * t) (T.mul_mem htT htT) with h | h
    · exact h
    · exfalso
      apply htK
      simpa using h
  have hsylK : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hKc) hsyl
  have hP₁ : IsSylowTwoOf (imageOTwoQuot X (T ⊓ K)) Kh :=
    (isSylowTwoOf_imageOTwoQuot_iff hKX inf_le_right hsylK.2.1
      (fun x hx => ⟨hQT hx.2, hx.1⟩)).mp hsylK
  obtain ⟨hnormP, E₁, E₂, hPE₁, hPE₂, hE₁L, hE₂L, hsE₁, hsE₂, hE₁₂⟩ :=
    exists_solvable_overgroups_of_mulEquiv_sl3 e₁ hP₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinnerE : ∀ E : Subgroup (OTwoQuot X), imageOTwoQuot X (T ⊓ K) ≤ E → E ≤ Kh →
      ∀ d (hd : d ∈ T), d ∈ Subgroup.normalizer (K : Set G) →
        (QuotientGroup.mk ⟨d, hTX hd⟩ : OTwoQuot X) ∈
          Subgroup.normalizer (E : Set (OTwoQuot X)) := by
    intro E hPE hEK d hd hdK
    have hdX : d ∈ X := hTX hd
    have hin := hinner d ⟨hd, hdK⟩
    unfold KbarInducesOuter at hin
    push Not at hin
    obtain ⟨k, hkK, hkc⟩ := hin
    have hkX : k ∈ X := hKX hkK
    have hcX : d * k⁻¹ ∈ X := X.mul_mem hdX (X.inv_mem hkX)
    have hc : ∀ w ∈ Kh, (QuotientGroup.mk ⟨d * k⁻¹, hcX⟩ : OTwoQuot X) * w *
        (QuotientGroup.mk ⟨d * k⁻¹, hcX⟩)⁻¹ = w := by
      intro w hw
      obtain ⟨x, hxX, hxK, rfl⟩ := mem_imageOTwoQuot_iff.mp hw
      have h1 : (d * k⁻¹) * x * (d * k⁻¹)⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
        have := hkc x hxK
        rw [commutatorElement_def] at this
        exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc) this
      have h2 := (mk_commute_iff (⟨d * k⁻¹, hcX⟩ : ↥X) ⟨x, hxX⟩).mpr h1
      rw [mul_inv_eq_iff_eq_mul]
      exact h2
    have hs : (QuotientGroup.mk ⟨d, hdX⟩ : OTwoQuot X) =
        QuotientGroup.mk ⟨d * k⁻¹, hcX⟩ * QuotientGroup.mk ⟨k, hkX⟩ := by
      rw [← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp
    have hsP : ∀ y ∈ imageOTwoQuot X (T ⊓ K), (QuotientGroup.mk ⟨d, hdX⟩ : OTwoQuot X) * y *
        (QuotientGroup.mk ⟨d, hdX⟩)⁻¹ ∈ imageOTwoQuot X (T ⊓ K) := by
      have hdN : d ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hd, hdK⟩
      have := mk_mem_normalizer_imageOTwoQuot_of_mem hdX hdN
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp this y).mp hy
    have hk' : (QuotientGroup.mk ⟨k, hkX⟩ : OTwoQuot X) ∈ Kh :=
      mem_imageOTwoQuot_iff.mpr ⟨k, hkX, hkK, rfl⟩
    exact mem_normalizer_of_inner hPE hEK hk' hs hc hsP hnormP
  have hTnorm : ∀ E : Subgroup (OTwoQuot X), imageOTwoQuot X (T ⊓ K) ≤ E → E ≤ Kh →
      ∀ s (hs : s ∈ T), (QuotientGroup.mk ⟨s, hTX hs⟩ : OTwoQuot X) ∈
        Subgroup.normalizer ((E ⊔ conjSub th E : Subgroup (OTwoQuot X)) : Set (OTwoQuot X)) := by
    intro E hPE hEK s hs
    have hsX : s ∈ X := hTX hs
    have hD1 : ∀ d (hd : d ∈ T), d ∈ Subgroup.normalizer (K : Set G) →
        conjSub (QuotientGroup.mk ⟨d, hTX hd⟩ : OTwoQuot X) E = E := fun d hd hdK =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hinnerE E hPE hEK d hd hdK)
    have hD2 : ∀ d (hd : d ∈ T), d ∈ Subgroup.normalizer (K : Set G) →
        conjSub (QuotientGroup.mk ⟨d, hTX hd⟩ : OTwoQuot X) (conjSub th E) = conjSub th E := by
      intro d hd hdK
      have hd' : t⁻¹ * d * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem htT) hd) htT
      have hd'K := hperm2 d hd hdK
      have e1 : (QuotientGroup.mk ⟨d, hTX hd⟩ : OTwoQuot X) * th =
          th * QuotientGroup.mk ⟨t⁻¹ * d * t, hTX hd'⟩ := by
        rw [hth, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        show d * t = t * (t⁻¹ * d * t)
        group
      rw [← conjSub_mul, e1, conjSub_mul, hD1 _ hd' hd'K]
    have hT2 : conjSub th (conjSub th E) = E := by
      have e2 : th * th = QuotientGroup.mk ⟨t * t, hTX (T.mul_mem htT htT)⟩ := by
        rw [hth, ← QuotientGroup.mk_mul]
        rfl
      rw [← conjSub_mul, e2]
      exact hD1 _ (T.mul_mem htT htT) ht2
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    show conjSub (QuotientGroup.mk ⟨s, hsX⟩ : OTwoQuot X) (E ⊔ conjSub th E) = E ⊔ conjSub th E
    rw [conjSub_sup]
    rcases hperm s hs with hsK | hsK
    · rw [hD1 s hs hsK, hD2 s hs hsK]
    · have hd : t⁻¹ * s ∈ T := T.mul_mem (T.inv_mem htT) hs
      have e3 : (QuotientGroup.mk ⟨s, hsX⟩ : OTwoQuot X) =
          th * QuotientGroup.mk ⟨t⁻¹ * s, hTX hd⟩ := by
        rw [hth, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        simp
      rw [e3, conjSub_mul, conjSub_mul, hD1 _ hd hsK, hD2 _ hd hsK, hT2, sup_comm]
  have hThs : Group.IsSolvable ↥Th := by
    have h2 : IsPGroup 2 ↥Th := isPGroup_imageOTwoQuot' hsyl.2.1
    have := h2.isNilpotent
    infer_instance
  have hsolvE : ∀ E : Subgroup (OTwoQuot X), imageOTwoQuot X (T ⊓ K) ≤ E → E ≤ Kh →
      Group.IsSolvable ↥E → Group.IsSolvable ↥((E ⊔ conjSub th E) ⊔ Th) := by
    intro E hPE hEK hE
    have hE' : Group.IsSolvable ↥(conjSub th E) := isSolvable_conjSub th E hE
    have hE'Kt : conjSub th E ≤ Kth := hKth' ▸ conjSub_mono th hEK
    have hcommE : conjSub th E ≤ Subgroup.normalizer (E : Set (OTwoQuot X)) := fun z hz =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun h hh => hAB h (hEK hh) z (hE'Kt hz))
    have h1 : Group.IsSolvable ↥(E ⊔ conjSub th E) :=
      isSolvable_sup_of_le_normalizer_of_isSolvable hcommE hE hE'
    have hThN : Th ≤ Subgroup.normalizer ((E ⊔ conjSub th E : Subgroup (OTwoQuot X)) :
        Set (OTwoQuot X)) := by
      intro u hu
      obtain ⟨s, hsX, hsT, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
      exact hTnorm E hPE hEK s hsT
    exact isSolvable_sup_of_le_normalizer_of_isSolvable hThN h1 hThs
  refine solvGen_eq_of_quotient hTX hQT hsyl.2.1
    {(E₁ ⊔ conjSub th E₁) ⊔ Th, (E₂ ⊔ conjSub th E₂) ⊔ Th} ?_ ?_ ?_
  · intro Y hY
    rcases hY with rfl | hY
    · exact hsolvE E₁ hPE₁ hE₁L hsE₁
    · rw [Set.mem_singleton_iff] at hY
      rw [hY]
      exact hsolvE E₂ hPE₂ hE₂L hsE₂
  · intro Y hY
    rcases hY with rfl | hY
    · exact le_sup_right
    · rw [Set.mem_singleton_iff] at hY
      rw [hY]
      exact le_sup_right
  · rw [sSup_pair]
    have himX : (Kh ⊔ Kth) ⊔ Th = ⊤ := by
      have h1 : imageOTwoQuot X ((K ⊔ conjSub t K) ⊔ T) = (Kh ⊔ Kth) ⊔ Th := by
        rw [imageOTwoQuot_sup (sup_le hKX hKtX) hTX, imageOTwoQuot_sup hKX hKtX]
      rw [← h1, ← hXK]
      exact imageOTwoQuot_self_eq_top X
    have hKt12 : Kth = conjSub th E₁ ⊔ conjSub th E₂ := by
      rw [hKth', ← hE₁₂, conjSub_sup]
    set Y₁ : Subgroup (OTwoQuot X) := (E₁ ⊔ conjSub th E₁) ⊔ Th with hY₁
    set Y₂ : Subgroup (OTwoQuot X) := (E₂ ⊔ conjSub th E₂) ⊔ Th with hY₂
    have hA1 : E₁ ≤ Y₁ := le_trans le_sup_left le_sup_left
    have hA2 : E₂ ≤ Y₂ := le_trans le_sup_left le_sup_left
    have hB1 : conjSub th E₁ ≤ Y₁ := le_trans le_sup_right le_sup_left
    have hB2 : conjSub th E₂ ≤ Y₂ := le_trans le_sup_right le_sup_left
    have hKh12 : Kh ≤ Y₁ ⊔ Y₂ := by
      calc Kh = E₁ ⊔ E₂ := hE₁₂.symm
        _ ≤ Y₁ ⊔ Y₂ := sup_le (hA1.trans le_sup_left) (hA2.trans le_sup_right)
    have hKth12 : Kth ≤ Y₁ ⊔ Y₂ := by
      calc Kth = conjSub th E₁ ⊔ conjSub th E₂ := hKt12
        _ ≤ Y₁ ⊔ Y₂ := sup_le (hB1.trans le_sup_left) (hB2.trans le_sup_right)
    rw [eq_top_iff, ← himX]
    exact sup_le (sup_le (hKh12.trans le_sup_left) (hKth12.trans le_sup_left)) le_sup_right

end K0Main

end CFSG.Quasithin
