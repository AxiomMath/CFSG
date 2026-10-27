module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Final
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux7

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.Nonsolvable (IsASimple)

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm311b

variable {Γ : Type*} [Group Γ]

theorem isChiefFactorOf_of_isASimple {H L : Subgroup Γ} (h : IsASimple H L) :
    IsChiefFactorOf (L ⊔ H) L ⊥ := by
  obtain ⟨hHL, ⟨x, hx, y, hy, hxy⟩, hmin⟩ := h
  have hLbot : ⊥ < L := by
    refine bot_lt_iff_ne_bot.mpr fun hL => hxy ?_
    rw [hL, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  refine ⟨⟨bot_le, Subgroup.le_normalizer_of_normal⟩,
    ⟨le_sup_left, sup_le Subgroup.le_normalizer hHL⟩, hLbot, fun K hK _ hKL => ?_⟩
  have hnorm : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr (le_sup_left.trans hK.2)
  exact hmin K hKL hnorm (le_sup_right.trans hK.2)

theorem map_conj_eq_self_of_commute {J : Subgroup Γ} {r b : Γ} (hrb : r * b = b * r)
    (hJ : J.map (MulAut.conj r).toMonoidHom = J.map (MulAut.conj b).toMonoidHom)
    (hcop : Nat.Coprime (orderOf r) (orderOf b)) :
    J.map (MulAut.conj r).toMonoidHom = J := by
  have hk : ∀ k : ℕ, J.map (MulAut.conj (r ^ k)).toMonoidHom =
      J.map (MulAut.conj (b ^ k)).toMonoidHom := by
    intro k
    induction k with
    | zero => simp only [pow_zero]
    | succ k ih =>
      have hcomm : r * b ^ k = b ^ k * r := (Commute.pow_right (show Commute r b from hrb) k).eq
      calc J.map (MulAut.conj (r ^ (k + 1))).toMonoidHom
          = (J.map (MulAut.conj (r ^ k)).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
            rw [Thm210.map_conj_map_conj, pow_succ']
        _ = (J.map (MulAut.conj (b ^ k)).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
            rw [ih]
        _ = J.map (MulAut.conj (r * b ^ k)).toMonoidHom := Thm210.map_conj_map_conj J _ _
        _ = J.map (MulAut.conj (b ^ k * r)).toMonoidHom := by rw [hcomm]
        _ = (J.map (MulAut.conj r).toMonoidHom).map (MulAut.conj (b ^ k)).toMonoidHom :=
            (Thm210.map_conj_map_conj J r (b ^ k)).symm
        _ = (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj (b ^ k)).toMonoidHom := by
            rw [hJ]
        _ = J.map (MulAut.conj (b ^ k * b)).toMonoidHom := Thm210.map_conj_map_conj J b (b ^ k)
        _ = J.map (MulAut.conj (b ^ (k + 1))).toMonoidHom := by rw [pow_succ]
  have hm : b ^ orderOf r ∈ Subgroup.normalizer (J : Set Γ) := by
    rw [Lemma212.mem_normalizer_iff_map_conj, ← hk, pow_orderOf_eq_one, Thm210.map_conj_one]
  obtain ⟨k, hk'⟩ := exists_pow_eq_self_of_coprime hcop
  have hb : b ∈ Subgroup.normalizer (J : Set Γ) := hk' ▸ pow_mem hm k
  rw [hJ]
  exact (Lemma212.mem_normalizer_iff_map_conj J b).mp hb

theorem not_le_centralizer_map_conj {D J : Subgroup Γ} (g : Γ)
    (h : ¬ D ≤ Subgroup.centralizer (J : Set Γ)) :
    ¬ D.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((J.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ) := by
  intro hle
  apply h
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := Subgroup.mem_centralizer_iff.mp (hle ⟨x, hx, rfl⟩) (g * j * g⁻¹) ⟨j, hj, rfl⟩
  have h2 : g * (j * x) * g⁻¹ = g * (x * j) * g⁻¹ := by
    calc g * (j * x) * g⁻¹ = (g * j * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (g * x * g⁻¹) * (g * j * g⁻¹) := by simpa [MulAut.conj_apply] using h1
      _ = g * (x * j) * g⁻¹ := by group
  simpa using h2

section Free

variable [Finite Γ] {p : ℕ} {A G Bf : Subgroup Γ}

theorem isSimple_of_isDiagonal {T : Set (Subgroup Γ)} {D J : Subgroup Γ}
    (hL : IsDirectProduct T (sSup T)) (hJ : J ∈ T) (hJs : IsSimpleGroup J)
    (hJnc : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) (hD : IsDiagonal T D) :
    IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  obtain ⟨hDle, hDJ⟩ := hD
  obtain ⟨hbot, hproj⟩ := hDJ J hJ
  let ψ : ↥D →* ↥J := (hL.coord hJ).comp (Subgroup.inclusion hDle)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((Subgroup.inclusion hDle x : ↥(sSup T)) : Γ) ∈ sSup (T \ {J}) :=
      (hL.coord_eq_one_iff hJ _).mp hx
    have h2 : (x : Γ) ∈ D ⊓ sSup (T \ {J}) := Subgroup.mem_inf.mpr ⟨x.2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective ψ := by
    intro z
    have hz : (z : Γ) ∈ projIn T J D := by
      rw [hproj]
      exact z.2
    obtain ⟨y, hyD, hyz⟩ := (hL.mem_projIn_iff hJ).mp hz
    exact ⟨⟨y, hyD⟩, Subtype.ext hyz⟩
  let e : ↥D ≃* ↥J := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have : IsSimpleGroup ↥J := hJs
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hJnc
  refine ⟨(e.symm ⟨x, hx⟩ : Γ), (e.symm ⟨x, hx⟩).2, (e.symm ⟨y, hy⟩ : Γ),
    (e.symm ⟨y, hy⟩).2, fun h => hxy ?_⟩
  have h1 : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ = e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ := Subtype.ext h
  have h2 := congrArg e h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2

theorem projIn_cenIn (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ))
    {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    projIn (lcal G) J (cenIn (kOf G) (Bf : Set Γ)) = J := by
  have h := projIn_centralizer_eq hyp.hK (fun a ha J' hJ' => hyp.A_perm_lcal (hBA ha) hJ') hJ
  refine h.trans (inf_eq_left.mpr fun j hj => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hfree J hJ hx) j hj).symm

theorem exists_diag (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    ∃ S : Set (Subgroup Γ), IsDirectProduct S (cenIn (kOf G) (Bf : Set Γ)) ∧
      (∀ D ∈ S, IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) ∧
      (∀ D ∈ S, ∃ J ∈ lcal G, ¬ D ≤ Subgroup.centralizer (J : Set Γ)) ∧
      (∀ J ∈ lcal G, ∃ D ∈ S, ¬ D ≤ Subgroup.centralizer (J : Set Γ)) ∧
      (∀ J ∈ lcal G, ∀ D ∈ S, ∀ D' ∈ S, ¬ D ≤ Subgroup.centralizer (J : Set Γ) →
        ¬ D' ≤ Subgroup.centralizer (J : Set Γ) → D = D') := by
  have hK := hyp.hK
  have hss : IsSemisimple (kOf G) := hyp.semisimpleAction.semisimple
  obtain ⟨P, hP0, hPU, hPd, hPdp, hPdiag⟩ := exists_partition_isDiagonal hss
    (inf_le_left : cenIn (kOf G) (Bf : Set Γ) ≤ kOf G)
    (by rw [hyp.lcal_kOf]; exact fun J hJ => projIn_cenIn hyp hBA hfree hJ)
  rw [hyp.lcal_kOf] at hPU
  have hTsub : ∀ T ∈ P, T ⊆ lcal G := fun T hT => hPU ▸ Set.subset_sUnion_of_mem hT
  have hTne : ∀ T ∈ P, T.Nonempty := fun T hT =>
    Set.nonempty_iff_ne_empty.mpr fun h => hP0 (h ▸ hT)
  have hnot : ∀ T ∈ P, ∀ J ∈ T,
      ¬ cenIn (kOf G) (Bf : Set Γ) ⊓ sSup T ≤ Subgroup.centralizer (J : Set Γ) := by
    intro T hT J hJ hle
    have hdp : IsDirectProduct T (sSup T) := Thm210.isDirectProduct_of_subset hK (hTsub T hT)
    obtain ⟨-, x, hx, y, hy, hxy⟩ := Lemma27.simple_of_mem_lcal (hTsub T hT hJ)
    have hxm : x ∈ projIn T J (cenIn (kOf G) (Bf : Set Γ) ⊓ sSup T) := by
      have h' : projIn T J (cenIn (kOf G) (Bf : Set Γ) ⊓ sSup T) = J :=
        ((hPdiag T hT).2 J hJ).2
      rw [h']
      exact hx
    obtain ⟨w, hwD, hwx⟩ := (hdp.mem_projIn_iff hJ).mp hxm
    have hwy : (w : Γ) * y = y * w :=
      (Subgroup.mem_centralizer_iff.mp (hle hwD) y hy).symm
    have h1 : w * ⟨y, hdp.le hJ hy⟩ = ⟨y, hdp.le hJ hy⟩ * w := Subtype.ext hwy
    have h2 := congrArg (hdp.coord hJ) h1
    rw [map_mul, map_mul] at h2
    have h3 : hdp.coord hJ ⟨y, hdp.le hJ hy⟩ = ⟨y, hy⟩ := Subtype.ext (hdp.coord_of_mem hJ hy)
    rw [h3] at h2
    exact hxy (by
      have := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul] at this
      rw [← hwx]
      exact this)
  have hout : ∀ T ∈ P, ∀ J ∈ lcal G, J ∉ T →
      cenIn (kOf G) (Bf : Set Γ) ⊓ sSup T ≤ Subgroup.centralizer (J : Set Γ) := by
    intro T hT J hJ hJT
    refine inf_le_right.trans (sSup_le fun K hKT x hx => ?_)
    have hne : K ≠ J := fun h => hJT (h ▸ hKT)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hK.commute K (hTsub T hT hKT) J hJ hne x hx y hy).eq.symm
  refine ⟨(fun T => cenIn (kOf G) (Bf : Set Γ) ⊓ sSup T) '' P, hPdp, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨J, hJ⟩ := hTne T hT
    obtain ⟨hJs, hJnc⟩ := Lemma27.simple_of_mem_lcal (hTsub T hT hJ)
    exact isSimple_of_isDiagonal (Thm210.isDirectProduct_of_subset hK (hTsub T hT)) hJ hJs hJnc
      (hPdiag T hT)
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨J, hJ⟩ := hTne T hT
    exact ⟨J, hTsub T hT hJ, hnot T hT J hJ⟩
  · intro J hJ
    have hJU : J ∈ ⋃₀ P := hPU ▸ hJ
    obtain ⟨T, hT, hJT⟩ := hJU
    exact ⟨_, ⟨T, hT, rfl⟩, hnot T hT J hJT⟩
  · rintro J hJ _ ⟨T, hT, rfl⟩ _ ⟨T', hT', rfl⟩ h1 h2
    have hJT : J ∈ T := by
      by_contra hJT
      exact h1 (hout T hT J hJ hJT)
    have hJT' : J ∈ T' := by
      by_contra hJT'
      exact h2 (hout T' hT' J hJ hJT')
    have hTT : T = T' := by
      by_contra hne
      exact Set.disjoint_left.mp (hPd hT hT' hne) hJT hJT'
    rw [hTT]

theorem le_normalizer_cenIn (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A) :
    A ⊔ cenIn G (Bf : Set Γ) ≤ Subgroup.normalizer (cenIn (kOf G) (Bf : Set Γ) : Set Γ) := by
  refine sup_le (fun a ha => ?_) (fun c hc => ?_)
  · refine Lemma212.mem_normalizer_cenIn (hyp.A_le_normalizer ha) ?_
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => hyp.comm (hBA hb) ha
  · exact Lemma212.mem_normalizer_cenIn (hyp.G_le_normalizer (Subgroup.mem_inf.mp hc).1)
      (Subgroup.mem_inf.mp hc).2

theorem isASimple_cenIn (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    IsASimple (A ⊔ cenIn G (Bf : Set Γ)) (cenIn (kOf G) (Bf : Set Γ)) := by
  obtain ⟨S, hS, hSs, hSd, hSb, hSc⟩ := exists_diag hyp hBA hfree
  obtain ⟨J₀, hJ₀⟩ := hyp.exists_lcal
  obtain ⟨D₀, hD₀, -⟩ := hSb J₀ hJ₀
  have hHL := le_normalizer_cenIn hyp hBA
  refine Lemma27.isASimple_of_isDirectProduct hS hSs ⟨D₀, hD₀⟩ hHL ?_
  intro D hD D' hD'
  obtain ⟨J, hJ, hJD⟩ := hSd D hD
  obtain ⟨J', hJ', hJ'D'⟩ := hSd D' hD'
  obtain ⟨a, ha, d, hd, hJJ'⟩ := hyp.transitive hJ hJ'
  have hdB : d ∈ cenIn G (Bf : Set Γ) :=
    ⟨(Subgroup.mem_inf.mp hd).1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA)
      (Subgroup.mem_inf.mp hd).2⟩
  have hmem : a * d ∈ A ⊔ cenIn G (Bf : Set Γ) :=
    mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hdB)
  refine ⟨a * d, hmem, ?_⟩
  have hlcal := Lemma27.lcal_eq_of_isDirectProduct hS hSs
  have hDS : D.map (MulAut.conj (a * d)).toMonoidHom ∈ S := by
    have h1 : D ∈ lcal (cenIn (kOf G) (Bf : Set Γ)) := hlcal.symm ▸ hD
    have h2 := map_conj_mem_lcal h1 (hHL hmem)
    rwa [hlcal] at h2
  refine (hSc J' hJ' _ hDS D' hD' ?_ hJ'D').symm
  rw [hJJ']
  exact not_le_centralizer_map_conj (a * d) hJD

theorem isChiefFactorOf_cenIn (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    IsChiefFactorOf (A ⊔ cenIn G (Bf : Set Γ)) (cenIn (kOf G) (Bf : Set Γ)) ⊥ := by
  have h := isChiefFactorOf_of_isASimple (isASimple_cenIn hyp hBA hfree)
  have hZle : cenIn (kOf G) (Bf : Set Γ) ≤ A ⊔ cenIn G (Bf : Set Γ) :=
    le_sup_of_le_right (inf_le_inf_right _ (kOf_le G))
  rwa [sup_eq_right.mpr hZle] at h

theorem not_isSolvable_cenIn (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    ¬ Group.IsSolvable ↥(cenIn (kOf G) (Bf : Set Γ)) :=
  Thm32.not_isSolvable_of_chief_bot (isChiefFactorOf_cenIn hyp hBA hfree)
    (isASimple_cenIn hyp hBA hfree).2.1

theorem eq_one_of_centralizes (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ))
    {r : Γ} (hrG : r ∈ G) (hrB : ∀ b ∈ Bf, b * r = r * b)
    (hrZ : ∀ z ∈ cenIn (kOf G) (Bf : Set Γ), z * r = r * z) : r = 1 := by
  have hK := hyp.hK
  have hrN : r ∈ Subgroup.normalizer (G : Set Γ) := Subgroup.le_normalizer hrG
  have hperm : ∀ J ∈ lcal G, J.map (MulAut.conj r).toMonoidHom ∈ lcal G := fun J hJ =>
    Lemma212.perm_lcal hrN hJ
  have hrord : orderOf r ∣ Nat.card G := Subgroup.orderOf_dvd_natCard G hrG
  have hcent : ∀ J ∈ lcal G, ∀ j ∈ J, j * r = r * j := by
    intro J hJ
    set Ω : Set (Subgroup Γ) := {K | ∃ b ∈ Bf, K = J.map (MulAut.conj b).toMonoidHom} with hΩdef
    have hΩ : IsDirectProduct Ω (orbitClosure J Bf) :=
      isDirectProduct_orbit (hBA.trans hyp.near.admits) hJ
    have hΩsub : Ω ⊆ lcal G := by
      rintro _ ⟨b, hb, rfl⟩
      exact hyp.A_perm_lcal (hBA hb) hJ
    have hJΩ : J ∈ Ω := ⟨1, one_mem _, (Thm210.map_conj_one J).symm⟩
    have hΩperm : ∀ b ∈ Bf, ∀ K ∈ Ω, K.map (MulAut.conj b).toMonoidHom ∈ Ω := by
      rintro b hb _ ⟨b', hb', rfl⟩
      exact ⟨b * b', mul_mem hb hb', Thm210.map_conj_map_conj J b' b⟩
    have hproj : projIn Ω J (orbitClosure J Bf ⊓ Subgroup.centralizer (Bf : Set Γ)) = J := by
      refine (projIn_centralizer_eq hΩ hΩperm hJΩ).trans (inf_eq_left.mpr fun j hj => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hfree J hJ hx) j hj).symm
    have hOK : orbitClosure J Bf ≤ kOf G :=
      Lemma212.orbitClosure_le_of_normalizer (hK.le hJ) (hBA.trans hyp.A_le_normalizer)
    have key : ∀ j ∈ J, ∃ x : Γ, ∃ hxK : x ∈ kOf G, x ∈ orbitClosure J Bf ∧
        x ∈ cenIn (kOf G) (Bf : Set Γ) ∧ ((hK.coord hJ ⟨x, hxK⟩ : ↥J) : Γ) = j := by
      intro j hj
      have hjP : j ∈ projIn Ω J (orbitClosure J Bf ⊓ Subgroup.centralizer (Bf : Set Γ)) := by
        rw [hproj]
        exact hj
      obtain ⟨y, hy, hyj⟩ := (hΩ.mem_projIn_iff hJΩ).mp hjP
      have hyK : (y : Γ) ∈ kOf G := hOK y.2
      refine ⟨y, hyK, y.2, ⟨hyK, (Subgroup.mem_inf.mp hy).2⟩, ?_⟩
      rw [← hyj]
      exact (Thm210.coord_eq_of_subset hK hΩ hΩsub hJΩ y.2).symm
    have hcoord : ∀ x : Γ, ∀ hxK : x ∈ kOf G, x ∈ cenIn (kOf G) (Bf : Set Γ) →
        ((hK.coord (hperm J hJ) ⟨x, hxK⟩ : ↥(J.map (MulAut.conj r).toMonoidHom)) : Γ) =
          r * ((hK.coord hJ ⟨x, hxK⟩ : ↥J) : Γ) * r⁻¹ := by
      intro x hxK hxZ
      have hxr : r * x * r⁻¹ = x := by rw [← hrZ x hxZ, mul_inv_cancel_right]
      have h := hK.coord_conj (fun J' hJ' => hperm J' hJ') hJ hxK
      have e : (⟨r * x * r⁻¹, hK.conj_mem (fun J' hJ' => hperm J' hJ') hxK⟩ : ↥(kOf G)) =
          ⟨x, hxK⟩ := Subtype.ext hxr
      rw [e] at h
      exact h
    have hJr : J.map (MulAut.conj r).toMonoidHom = J := by
      obtain ⟨y₀, hy₀, hy₀1⟩ : ∃ y ∈ J, y ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact Lemma212.ne_bot_of_mem_lcal hJ ((Subgroup.eq_bot_iff_forall J).mpr hcon)
      obtain ⟨x, hxK, hxO, hxZ, hx⟩ := key y₀ hy₀
      have hmem : J.map (MulAut.conj r).toMonoidHom ∈ Ω := by
        by_contra hnot
        have hle : sSup Ω ≤ sSup (lcal G \ {J.map (MulAut.conj r).toMonoidHom}) :=
          sSup_le_sSup fun K hK' => ⟨hΩsub hK', fun h => hnot (h ▸ hK')⟩
        have hxs : x ∈ sSup (lcal G \ {J.map (MulAut.conj r).toMonoidHom}) :=
          hle (hΩ.sSup_eq ▸ hxO)
        have h1 := (hK.coord_eq_one_iff (hperm J hJ) ⟨x, hxK⟩).mpr hxs
        have h2 := hcoord x hxK hxZ
        rw [h1, hx] at h2
        apply hy₀1
        have h3 : r * y₀ * r⁻¹ = 1 := h2.symm
        calc y₀ = r⁻¹ * (r * y₀ * r⁻¹) * r := by group
          _ = 1 := by rw [h3]; group
      obtain ⟨b, hb, hbJ⟩ := hmem
      have hrb : r * b = b * r := (hrB b hb).symm
      have hbord : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one (hyp.near.elemAbelian.2 b (hBA hb))
      have hcop : Nat.Coprime (orderOf r) (orderOf b) :=
        (((hyp.coprime.symm).coprime_dvd_left hrord).coprime_dvd_right hbord)
      exact map_conj_eq_self_of_commute hrb hbJ hcop
    intro j hj
    obtain ⟨x, hxK, -, hxZ, hx⟩ := key j hj
    have h1 := hcoord x hxK hxZ
    rw [hK.coord_val_congr (hperm J hJ) hJ hJr ⟨x, hxK⟩, hx] at h1
    calc j * r = r * j * r⁻¹ * r := by rw [← h1]
      _ = r * j := by group
  have hrC : r ∈ Subgroup.centralizer (kOf G : Set Γ) := by
    have : kOf G ≤ Subgroup.centralizer ({r} : Set Γ) := by
      rw [← hK.sSup_eq]
      refine sSup_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcent J hJ j hj
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hk)
  have hmem : r ∈ G ⊓ Subgroup.centralizer (kOf G : Set Γ) := Subgroup.mem_inf.mpr ⟨hrG, hrC⟩
  rw [centralizer_kOf_eq_bot hyp.sol_eq] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem sol_cenIn_eq_bot (hyp : Lemma212.Hyp p A G) (hBA : Bf ≤ A)
    (hfree : ∀ J ∈ lcal G,
      Bf ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    sol (cenIn G (Bf : Set Γ)) = ⊥ := by
  set C := cenIn G (Bf : Set Γ) with hCdef
  set Z := cenIn (kOf G) (Bf : Set Γ) with hZdef
  set R := sol C with hRdef
  have hCG : C ≤ G := inf_le_left
  have hRC : R ≤ C := sol_le C
  have hCR : C ≤ Subgroup.normalizer (R : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp (normal_sol_subgroupOf C)
  have hZC : Z ≤ C := inf_le_inf_right _ (kOf_le G)
  have hCZ : C ≤ Subgroup.normalizer (Z : Set Γ) := fun c hc =>
    Lemma212.mem_normalizer_cenIn (hyp.G_le_normalizer (hCG hc)) (Subgroup.mem_inf.mp hc).2
  have hAcen : A ≤ Subgroup.centralizer (Bf : Set Γ) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hyp.comm (hBA hb) ha
  have hAC : A ≤ Subgroup.normalizer (C : Set Γ) := fun a ha =>
    Lemma212.mem_normalizer_cenIn (hyp.near.admits ha) (hAcen ha)
  have hAR : A ≤ Subgroup.normalizer (R : Set Γ) := fun a ha =>
    Lemma212.normalizer_le_normalizer_sol C (hAC ha)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set Γ) :=
    le_sup_left.trans (le_normalizer_cenIn hyp hBA)
  have h1 : R ⊓ Z = ⊥ := by
    have hAS := isASimple_cenIn hyp hBA hfree
    have hnorm : ((R ⊓ Z).subgroupOf Z).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact hZC.trans (Thm32.le_normalizer_inf hCR hCZ)
    have hH : A ⊔ C ≤ Subgroup.normalizer ((R ⊓ Z : Subgroup Γ) : Set Γ) :=
      sup_le (Thm32.le_normalizer_inf hAR hAZ) (Thm32.le_normalizer_inf hCR hCZ)
    rcases hAS.2.2 (R ⊓ Z) inf_le_right hnorm hH with h | h
    · exact h
    · exfalso
      exact not_isSolvable_cenIn hyp hBA hfree
        (Thm211.isSolvable_of_le (inf_eq_right.mp h) (isSolvable_sol C))
  have h2 : ∀ r ∈ R, ∀ z ∈ Z, z * r = r * z := by
    intro r hr z hz
    have hmem : r * z * r⁻¹ * z⁻¹ ∈ R ⊓ Z := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h3 : z * r⁻¹ * z⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hCR (hZC hz)) r⁻¹).mp (inv_mem hr)
        have : r * z * r⁻¹ * z⁻¹ = r * (z * r⁻¹ * z⁻¹) := by group
        rw [this]
        exact mul_mem hr h3
      · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hCZ (hRC hr)) z).mp hz) (inv_mem hz)
    rw [h1, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem.symm
  rw [eq_bot_iff]
  intro r hr
  exact Subgroup.mem_bot.mpr (eq_one_of_centralizes hyp hBA hfree (hCG (hRC hr))
    (fun b hb => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hRC hr)).2 b hb)
    (h2 r hr))

end Free

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm311b
