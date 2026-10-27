module

public import CFSG.Timmesfeld.ARS.Sec8Closure
public import CFSG.Timmesfeld.ARS.Sec8Orbit
public import CFSG.Timmesfeld.ARS.Sec8Projection

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Levi

theorem commutator_eq_of_commuting_iff (h : Hyp G R) {A A₀ X X' P : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hX : X ∈ leviSet R A A₀) (hX' : X' ∈ leviSet R A A₀)
    (hXX' : ∀ Y ∈ leviSet R A A₀, Commuting X Y ↔ Commuting X' Y)
    (hP : P ∈ lambdaStar R A A₀) (hPX : ¬ Commuting P X) : ⁅P, X⁆ = ⁅P, X'⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  have hXR : X ∈ R := hX.1.1
  have hX'R : X' ∈ R := hX'.1.1
  have hPR : P ∈ R := hP.1.1.1
  have hnl : ∀ {Y : Subgroup G}, Y ∈ leviSet R A A₀ → Y ∉ lambdaSet R A := fun hY hl =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hY.2.2.2
  have hPX' : ¬ Commuting P X' := fun hc =>
    hPX ((commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hX hX' hXX' hP).2 hc)
  have hsX : Special R P X :=
    (CentralOrbit.commutator_mem_lambdaSet h hA hX.1 (hnl hX) hP.1 fun hc => hPX hc.symm).1.symm
  have hsX' : Special R P X' :=
    (CentralOrbit.commutator_mem_lambdaSet h hA hX'.1 (hnl hX') hP.1 fun hc => hPX' hc.symm).1.symm
  by_contra hne
  set D := ⁅P, X⁆ with hDdef
  set C := ⁅P, X'⁆ with hCdef
  have hDR : D ∈ R := hsX.1
  have hCR : C ∈ R := hsX'.1
  obtain ⟨hPD, hXD⟩ := mem_lambdaSet_commutator hR hiso hPR hXR hsX
  obtain ⟨hPC, hX'C⟩ := mem_lambdaSet_commutator hR hiso hPR hX'R hsX'
  have hDst : D ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX hP hsX).1 D hDR le_sup_right
  have hCst : C ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX' hP hsX').1 C hCR le_sup_right
  have hDX' : Commuting D X' :=
    (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hX hX' hXX' hDst).1 hXD.1.2.2
  have hCX : Commuting C X :=
    (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hX hX' hXX' hCst).2 hX'C.1.2.2
  have hCD : C ∈ lambdaSet R D := by
    have hCM : C ≤ M R D :=
      commutator_le_of_le_normalizer (QD.le_M hPD) (QD.le_normalizer_M hR hDR ⟨hX'R, hDX'⟩)
    have hmem : C ∈ {Y | Y ∈ R ∧ Y ≤ M R D} := ⟨hCR, hCM⟩
    rw [(Q_eq_M h hDR).2.1] at hmem
    exact hmem.resolve_left (Ne.symm hne)
  have hDC : D ∈ lambdaSet R C := mem_lambdaSet_comm hDR hCD
  have huniq : ∀ {Y Z : Subgroup G}, Y ∈ lambdaStar R A A₀ → Z ∈ lambdaStar R A A₀ →
      Z ≤ A ⊔ Y → Z = Y := fun {Y Z} hY hZ hZle => by
    obtain ⟨D', -, hu⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hY.1
    exact (hu Z ⟨hZ.1.1.1, hZle, hZ.2⟩).trans (hu Y ⟨hY.1.1.1, le_sup_right, hY.2⟩).symm
  have hline : ∀ Q ∈ R, Q ≤ C ⊔ D → Q ∈ lambdaSet R A := by
    intro Q hQ hQle
    have hmem : Q ∈ {Y | Y ∈ R ∧ Y ≤ M R A} :=
      ⟨hQ, hQle.trans (sup_le (QD.le_M hCst.1) (QD.le_M hDst.1))⟩
    rw [(Q_eq_M h hA).2.1] at hmem
    refine hmem.resolve_left fun e => ?_
    have hAle : A ≤ C ⊔ D := by rw [← e]; exact hQle
    have h1 := (mem_lambdaSet_of_le_sup hR hiso hCR hDC hCR le_sup_left hA hAle
      hCst.1.1.2.1).2
    exact hne (huniq hCst hDst (le_sup_right.trans (h1.symm.le.trans (sup_comm C A).le)))
  obtain ⟨-, -, htrans⟩ := plane_transitive hR hiso hA hCR hDC hline
  have hAN : A ≤ A ⊔ C ⊔ D := le_sup_left.trans le_sup_left
  have hCN : C ≤ A ⊔ C ⊔ D := le_sup_right.trans le_sup_left
  have hDN : D ≤ A ⊔ C ⊔ D := le_sup_right
  obtain ⟨T, hTR, hT⟩ := htrans D hDR A hA hDN hAN hDst.1.1.2.1
  have hCL : ¬ C ≤ D ⊔ A := fun hle =>
    hne (huniq hDst hCst (hle.trans (sup_comm D A).le)).symm
  obtain ⟨Q', hQ'R, hQ'le, hQ'C, hQ'D⟩ := exists_mem_le_sup_ne_ne hR hiso hCR hDC C D
  obtain ⟨t₀, ht₀, hCt₀⟩ := hT.2.2.2 C hCR hCN hCL Q' hQ'R hQ'le hQ'D
  have hTC : ¬ Commuting T C := fun hc =>
    hQ'C (hCt₀.symm.trans (conjSub_of_forall_commute fun c hc' => hc t₀ ht₀ c hc'))
  have ht₀1 : t₀ ≠ 1 := fun e => hQ'C (by rw [← hCt₀, e, conjSub_one])
  have hTA : Commuting A T := hT.2.2.1.mono le_sup_right le_rfl
  have hTD : Commuting D T := hT.2.2.1.mono le_sup_left le_rfl
  have hCTle : ⁅C, T⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    exact fun c hc t ht => hT.2.1 t ht c (hCN hc)
  have hTA' : T ≠ A := fun e => hTC (by rw [e]; exact hCst.1.1.2.2)
  have hTl : T ∉ lambdaSet R A := by
    intro hTl
    apply hTC
    rw [commuting_iff_commutator_eq_bot, Subgroup.commutator_comm, ← le_bot_iff]
    have h1 : ⁅C, T⁆ ≤ A :=
      (Subgroup.commutator_mono (QD.le_M hCst.1) (QD.le_M hTl)).trans hcommA.le
    exact (le_inf h1 hCTle).trans (inf_eq_bot hR hiso hA hDR hDst.1.1.2.1.symm).le
  have hTσ : T ∈ sigmaSet R A := ⟨hTR, hTA', hTA⟩
  obtain ⟨hsTC, -, hTW, -⟩ := CentralOrbit.commutator_mem_lambdaSet h hA hTσ hTl hCst.1 hTC
  have hTCD : ⁅T, C⁆ = D := by
    rw [Subgroup.commutator_comm]
    exact QD.eq_of_le_of_mem hR hiso (by rw [Subgroup.commutator_comm]; exact hsTC.1) hDR hCTle
  have hTDl : T ∈ lambdaSet R D := hTCD ▸ hTW
  have hPCM : P ⊔ C ≤ M R D := sup_le (QD.le_M hPD) (QD.le_M hCD)
  have hD2 : IsPGroup 2 ↥(M R D) := (Q_eq_M h hDR).2.2.2.2
  obtain ⟨PT, hPTR, hPTle, hTPT⟩ : ∃ PT ∈ R, PT ≤ P ⊔ C ∧ Commuting T PT := by
    by_cases hTP : Commuting T P
    · exact ⟨P, hPR, le_sup_left, hTP⟩
    have hsPT : Special R P T := by
      rcases hR.rel P hPR T hTR (fun e => hTP (by rw [← e]; exact hR.commuting_self hPR))
        with hc | ho | hs
      · exact absurd hc.symm hTP
      · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hPR hTR
          (hD2.to_le (sup_le (QD.le_M hPD) (QD.le_M hTDl))))
      · exact hs
    have hPTD : ⁅P, T⁆ = D := QD.eq_of_le_of_mem hR hiso hsPT.1 hDR
      ((Subgroup.commutator_mono (QD.le_M hPD) (QD.le_M hTDl)).trans
        (Q_eq_M h hDR).2.2.1.le)
    obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
    have hct : ⁅c, t₀⁆ ∈ D := hCTle (Subgroup.commutator_mem_commutator hc ht₀)
    obtain ⟨p, hp, hpt⟩ := (bijOn_commutator_left hR hiso hPR hTR hsPT ht₀ ht₀1).surjOn
      (show ⁅c, t₀⁆⁻¹ ∈ ((⁅P, T⁆ : Subgroup G) : Set G) from hPTD ▸ D.inv_mem hct)
    have hpt' : ⁅p, t₀⁆ = ⁅c, t₀⁆⁻¹ := hpt
    have hy : ⁅p * c, t₀⁆ = 1 := by
      rw [Plane.commutatorElement_mul_left_of_commute, hpt', mul_inv_cancel]
      exact (hPD.1.2.2 _ hct p hp).symm
    have hy1 : p * c ≠ 1 := by
      intro e
      have hc' : c = p⁻¹ := eq_inv_of_mul_eq_one_right e
      have hmem : c ∈ P ⊓ C := ⟨hc' ▸ P.inv_mem hp, hc⟩
      rw [inf_eq_bot hR hiso hPR hCR hPC.1.2.1, Subgroup.mem_bot] at hmem
      exact hc1 hmem
    obtain ⟨Q, hQR, hQle', hyQ⟩ :=
      hPC.2 (p * c) (Subgroup.mul_mem _ (Subgroup.mem_sup_right hp) (Subgroup.mem_sup_left hc))
        hy1
    have hQle : Q ≤ P ⊔ C := hQle'.trans (sup_comm _ _).le
    refine ⟨Q, hQR, hQle, ?_⟩
    by_cases hTQ : T = Q
    · rw [← hTQ]
      exact hR.commuting_self hTR
    rcases hR.rel T hTR Q hQR hTQ with hc' | ho | hs
    · exact hc'
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hTR hQR
        (hD2.to_le (sup_le (QD.le_M hTDl) (hQle.trans hPCM))))
    · exact absurd (eq_one_of_commute_of_special hR hiso hTR hQR hs ht₀ ht₀1 hyQ
        (commutatorElement_eq_one_iff_mul_comm.1 hy).symm) hy1
  have hPTC : PT ≠ C := fun e => hTC (by rw [← e]; exact hTPT)
  obtain ⟨x', hx', hPTx'⟩ := QD.exists_eq_conjSub_of_le_sup hR hiso hPR hX'R hsX' hPTR
    (hPTle.trans (sup_comm P C).le) hPTC
  have hx'x' : x' * x' = 1 := hR.mul_self X' hX'R x' hx'
  have hinv : ∀ Z : Subgroup G, conjSub (conjSub Z x') x' = Z := fun Z => by
    rw [← conjSub_mul, hx'x', conjSub_one]
  have hx'A : conjSub A x' = A :=
    conjSub_of_forall_commute fun a ha => (hX'.1.2.2 a ha x' hx').symm
  have hx'D : conjSub D x' = D := conjSub_of_forall_commute fun d hd => (hDX' d hd x' hx').symm
  have hx'C : conjSub C x' = C :=
    conjSub_of_forall_commute fun c hc => (hX'C.1.2.2 c hc x' hx').symm
  set T' := conjSub T x' with hT'def
  have hT'R : T' ∈ R := hR.conjSub_mem hTR x'
  have hT'A : Commuting A T' := by
    have := hTA.conjSub x'
    rwa [hx'A] at this
  have hT'P : Commuting T' P := by
    have := hTPT.conjSub x'
    rwa [hPTx', hinv] at this
  have hT'C : ¬ Commuting T' C := fun hc => hTC (by
    have := hc.conjSub x'
    rwa [hT'def, hinv, hx'C] at this)
  have hT'D : T' ∈ lambdaSet R D := by
    have := conjSub_mem_lambdaSet hR hTDl x'
    rwa [hx'D] at this
  have hT'l : T' ∉ lambdaSet R A := by
    intro hT'l
    apply hT'C
    rw [commuting_iff_commutator_eq_bot, Subgroup.commutator_comm, ← le_bot_iff]
    have h1 : ⁅C, T'⁆ ≤ A :=
      (Subgroup.commutator_mono (QD.le_M hCst.1) (QD.le_M hT'l)).trans hcommA.le
    have h2 : ⁅C, T'⁆ ≤ D :=
      (Subgroup.commutator_mono (QD.le_M hCD) (QD.le_M hT'D)).trans (Q_eq_M h hDR).2.2.1.le
    exact (le_inf h1 h2).trans (inf_eq_bot hR hiso hA hDR hDst.1.1.2.1.symm).le
  have hT'σ : T' ∈ sigmaSet R A := ⟨hT'R, fun e => hT'C (by rw [e]; exact hCst.1.1.2.2), hT'A⟩
  obtain ⟨m, hm, hY⟩ := exists_mem_M_conjSub_mem_leviSet h hA hAne hA₀ hT'σ hT'l
  set Y := conjSub T' m with hYdef
  have hYR : Y ∈ R := hY.1.1
  have hMnorm : ∀ {Z : Subgroup G}, A ≤ Z → Z ≤ M R A → conjSub Z m = Z := fun hAZ hZM =>
    conjSub_eq_self_iff.2 (le_normalizer_of_commutator_le hZM (hcommA.le.trans hAZ) hm)
  have hmA : conjSub A m = A :=
    conjSub_of_forall_commute fun a ha => (QD.commuting_M hR hA a ha m hm).symm
  have hDm : conjSub D m = D := by
    have hDmle : conjSub D m ≤ A ⊔ D := by
      rw [← hMnorm le_sup_left (sup_le QD.le_M_self (QD.le_M hDst.1))]
      exact Subgroup.map_mono le_sup_right
    have hDmR : conjSub D m ∈ R := hR.conjSub_mem hDR m
    have hDml : conjSub D m ∈ lambdaSet R A := by
      have := conjSub_mem_lambdaSet hR hDst.1 m
      rwa [hmA] at this
    have hYDm : Y ∈ lambdaSet R (conjSub D m) := conjSub_mem_lambdaSet hR hT'D m
    have hDmst := mem_lambdaStar_of_mem_lambdaSet hR hA₀ hY hDml (mem_lambdaSet_comm hDmR hYDm)
    exact huniq hDst hDmst hDmle
  have hYD : Y ∈ lambdaSet R D := by
    have := conjSub_mem_lambdaSet hR hT'D m
    rwa [hDm] at this
  have hYP : Commuting Y P := by
    have hAP : Commuting (A ⊔ P) T' := Commuting.sup_left hT'A hT'P.symm
    have := hAP.conjSub m
    rw [hMnorm le_sup_left (sup_le QD.le_M_self (QD.le_M hP.1))] at this
    exact (this.mono le_sup_right le_rfl).symm
  have hYC : ¬ Commuting Y C := by
    intro hc
    apply hT'C
    have h1 := hc.conjSub m⁻¹
    rw [hYdef, Plane.conjSub_conjSub_inv] at h1
    have hCle : C ≤ A ⊔ conjSub C m⁻¹ := by
      have hle : A ⊔ conjSub C m⁻¹ ≤ M R A := sup_le QD.le_M_self
        ((Subgroup.map_mono (QD.le_M hCst.1)).trans (conjSub_of_mem (Subgroup.inv_mem _ hm)).le)
      calc C = conjSub (conjSub C m⁻¹) m := (Plane.conjSub_inv_conjSub C m).symm
        _ ≤ conjSub (A ⊔ conjSub C m⁻¹) m := Subgroup.map_mono le_sup_right
        _ = A ⊔ conjSub C m⁻¹ := hMnorm le_sup_left hle
    exact (Commuting.sup_right hT'A.symm h1).mono le_rfl hCle
  have hXY : Commuting X Y := by
    by_contra hc
    have hne' : X ≠ Y := fun e => hc (by rw [← e]; exact hR.commuting_self hXR)
    rcases hR.rel X hXR Y hYR hne' with hc' | ho | hs
    · exact hc hc'
    · exact not_commuting_of_opposite_of_mem_lambdaSet hR hXR ho (mem_lambdaSet_comm hDR hYD)
        hXD.1.2.2.symm
    · have hWD : ⁅X, Y⁆ = D := QD.eq_of_le_of_mem hR hiso hs.1 hDR
        ((Subgroup.commutator_mono (QD.le_M hXD) (QD.le_M hYD)).trans (Q_eq_M h hDR).2.2.1.le)
      have hDΛ : D ∈ leviSet R A A₀ :=
        hWD ▸ commutator_mem_leviSet hR hA hA₀ hX hY hs
      exact hnl hDΛ hDst.1
  have hX'Y : ¬ Commuting X' Y := by
    intro hc
    apply hYC
    refine Sec3.commuting_of_forall_conjSub_eq hR hYR hCR (fun y hy => ?_) hiso
    rw [hCdef, conjSub, Subgroup.map_commutator]
    change ⁅conjSub P y, conjSub X' y⁆ = ⁅P, X'⁆
    rw [conjSub_of_forall_commute fun p hp => hYP y hy p hp,
      conjSub_of_forall_commute fun x hx => (hc x hx y hy).symm]
  exact hX'Y ((hXX' Y hY).1 hXY)

end Levi

end CFSG.Timmesfeld.ARS
