module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Toral
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CoverData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


@[expose] def Q2RLevel (kind : Q2RowKind) : Prop :=
  ∀ (p d Q : ℕ) (lab : LargeEvenLabel), LargeEvenInLambda2 lab → q2RowFits kind p d Q lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      ∀ u ∈ A, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = Q →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
          ∀ M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)),
            (∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J, (j' : R) = a j →
              α (QuotientGroup.mk j) = QuotientGroup.mk j') →
            Q2LinearLift M)

private theorem l02qq2cv_ggInducedAut_mem {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ)
    (b : ↥Bs) : ggInducedAut θ (ggGamma L hN b) ∈ I := by
  obtain ⟨φ, hφI, hφ⟩ := hact ((b : G)⁻¹) (Bs.inv_mem b.2)
  have hφ' : LargeEvenInduces θ (fun l l' : ↥L => l' = ggGamma L hN b l) φ := by
    intro l l' hl
    have h2 : (l' : G) = (((b : G)⁻¹))⁻¹ * (l : G) * ((b : G)⁻¹) := by
      rw [hl, ggGamma_coe]
      group
    exact hφ l l' h2
  have hEq : ggInducedAut θ (ggGamma L hN b) = φ := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply]
    exact (hφ' l (ggGamma L hN b l) rfl).symm
  rw [hEq]
  exact hφI

private theorem l02qq2cv_isElemAbelian_range {G : Type} [Group G] {Bs : Subgroup G}
    {p : ℕ} (hE : IsElemAbelian p Bs) {L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian p (ggGamma L hN).range := by
  haveI : IsMulCommutative ↥Bs := hE.1
  exact isElemAbelian_range
    (fun a b : ↥Bs => mul_comm' a b)
    (fun a : ↥Bs => Subtype.ext (by simpa using hE.2 a a.2))
    (ggGamma L hN)

private theorem l02qq2cv_range_map_mem {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ a ∈ (ggGamma L hN).range.map (ggInducedAut θ), a ∈ I := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
  rw [← hb]
  exact l02qq2cv_ggInducedAut_mem hN θ hact b

private theorem l02qq2cv_ggBsAut_apply_coe {G : Type} [Group G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (b : ↥Bs) (j : ↥J) :
    (((ggBsAut hN b) j : ↥J) : G) = (b : G) * (j : G) * (b : G)⁻¹ :=
  rfl

private theorem l02qq2cv_two_le_n {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hpq : p ∣ 2 ^ n - 1) : 2 ≤ n := by
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  by_contra h
  have hn1 : n = 1 := by omega
  subst hn1
  norm_num at hpq
  omega

private theorem l02qq2cv_three_le_d {p d Q : ℕ} {lab : LargeEvenLabel} {kind : Q2RowKind}
    (hΛ : LargeEvenInLambda2 lab) (hfits : q2RowFits kind p d Q lab)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) : 3 ≤ d := by
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  cases kind <;> rw [q2RowFits.eq_def] at hfits
  ·
    obtain ⟨-, -, -, -, htag, hrank, -⟩ := hfits
    have hA := hΛ
    simp only [LargeEvenInLambda2] at hA
    rw [htag] at hA
    have h1d : 1 ≤ d := by rw [← hrank]; exact hA.2.1
    have := Nat.le_of_dvd (by omega : 0 < d) hpd
    omega
  ·
    obtain ⟨-, -, -, -, htag, hrank, -⟩ := hfits
    rcases htag with hB | hC
    · have hA := hΛ
      simp only [LargeEvenInLambda2] at hA
      rw [hB] at hA
      have h2d : 2 ≤ d := by rw [← hrank]; exact hA.2.1
      have := Nat.le_of_dvd (by omega : 0 < d) hpd
      omega
    · have hA := hΛ
      simp only [LargeEvenInLambda2] at hA
      rw [hC] at hA
      have h2d : 2 ≤ d := by rw [← hrank]; exact hA.2.1
      have := Nat.le_of_dvd (by omega : 0 < d) hpd
      omega
  ·
    obtain ⟨-, -, -, -, htag, hrank, -⟩ := hfits
    have hA := hΛ
    simp only [LargeEvenInLambda2] at hA
    rw [htag] at hA
    have h3d : 3 ≤ d := by rw [← hrank]; exact hA.2
    exact h3d
  ·
    obtain ⟨-, -, -, -, htag, hrank, -⟩ := hfits
    have hA := hΛ
    simp only [LargeEvenInLambda2] at hA
    rw [htag] at hA
    have h1d : 1 ≤ d := by omega
    have := Nat.le_of_dvd (by omega : 0 < d) hpd
    omega
  ·
    obtain ⟨-, -, -, -, htag, hn, hrankor, hp3', -⟩ := hfits
    have hA := hΛ
    simp only [LargeEvenInLambda2] at hA
    rw [htag] at hA
    have hrank2 : 2 ≤ lab.rank := by
      have h1 := hA.2.1
      by_contra h
      have h1' : lab.rank = 1 := by omega
      have h2 := hA.2.2 h1'
      omega
    have hd1 : 1 ≤ d := by
      rcases hrankor with h | h
      · omega
      · omega
    have hp_eq : p = 3 := hp3'
    have : p ≤ d := Nat.le_of_dvd (by omega : 0 < d) hpd
    omega
  ·
    obtain ⟨-, -, -, -, -, -, hd6, -⟩ := hfits
    omega
  ·
    obtain ⟨-, -, -, -, -, -, hd7, -⟩ := hfits
    omega
  ·
    obtain ⟨-, -, -, -, -, -, hd9, -⟩ := hfits
    omega

private theorem l02qq2cv_exists_pow {p d N : ℕ} {lab : LargeEvenLabel} {kind : Q2RowKind}
    (hΛ : LargeEvenInLambda2 lab) (hfits : q2RowFits kind p d N lab)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ N - 1) : ∃ m, 2 ≤ m ∧ N = 2 ^ m := by
  cases kind <;> rw [q2RowFits.eq_def] at hfits
  · obtain ⟨-, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩
  · obtain ⟨-, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩
  · obtain ⟨-, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩
  · obtain ⟨-, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hN4⟩ := hfits
    exact ⟨2, by norm_num, by rw [hN4]; norm_num⟩
  · obtain ⟨-, -, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩
  · obtain ⟨-, -, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩
  · obtain ⟨-, -, -, -, -, -, -, hQeq⟩ := hfits
    exact ⟨lab.n, l02qq2cv_two_le_n hp hp2 hΛ.1 (by rwa [hQeq] at hpq), hQeq⟩

private theorem l02qq2cv_numerics {p d N : ℕ} {lab : LargeEvenLabel} {kind : Q2RowKind}
    (hΛ : LargeEvenInLambda2 lab) (hfits : q2RowFits kind p d N lab)
    (hpd : p ∣ d) (hpq : p ∣ N - 1) : 3 ≤ d ∧ ∃ m, 2 ≤ m ∧ N = 2 ^ m := by
  have hfits0 := hfits
  rw [q2RowFits.eq_def] at hfits
  have hp : p.Prime := hfits.1
  have hp2 : p ≠ 2 := hfits.2.1
  exact ⟨l02qq2cv_three_le_d hΛ hfits0 hp hp2 hpd,
    l02qq2cv_exists_pow hΛ hfits0 hp hp2 hpq⟩

theorem q2RowSolverInput_of_rLevel {kind : Q2RowKind} (h : Q2RLevel kind) : Q2RowSolverInput kind := by
  intro G _ _ p B Bs x L D J hcfg hInner hN d K _ _ θ hpd hpq hlab
  unfold Q2RLevel at h
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hlab
  obtain ⟨R, instR, I, F, hsimple, hnab, θL, hfits, hsplit, hNL, hact⟩ :=
    largeEvenRawDatum_exists hraw
  have hraw' := (h p d (Nat.card K) lab hΛ hfits) _ hraw
  obtain ⟨R', instR', I', F', hmark', hQ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hsimple', hnab', θL', hfits', hsplit', hNL', hact'⟩ := hmark'
  obtain ⟨y, u, hyD, hyu, huord, hcomm, hJL, hJcomp⟩ := q1_fixed_component_data hcfg hNL'
  let π : ↥L →* R' := q2CoverMap θL'
  obtain ⟨hJ₀comp, ι, ι_mk⟩ := q2_cover_data hperf θL' u (J.subgroupOf L) hJcomp
  let J₀ : Subgroup R' := (J.subgroupOf L).map π
  let β : MulAut R' := ggInducedAut θL' u
  let A' : Subgroup (MulAut R') := (ggGamma L hNL').range.map (ggInducedAut θL')
  let φ : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  let e : ↥J ⧸ Subgroup.center ↥J ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (centerQuotCongr φ).symm.trans ι
  let θ' : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
    e.symm.trans θ
  let M₀ : Subgroup (MulAut (↥J₀ ⧸ Subgroup.center ↥J₀)) :=
    ((ggBsAut hN).range.map (centerQuotAut ↥J)).map (MulAut.congr e).toMonoidHom
  have hcomm_all : ∀ (a : MulAut ↥L) (x : ↥L),
      π (a x) = ggInducedAut θL' a (π x) := by
    intro a x
    simpa [π, q2CoverMap] using (ggInducedAut_apply θL' a x).symm
  have hAb : IsElemAbelian p A' :=
    (l02qq2cv_isElemAbelian_range hcfg.2.1.2.1 hNL').map (ggInducedAut θL')
  have hAI : ∀ a ∈ A', a ∈ I' := l02qq2cv_range_map_mem hNL' θL' hact'
  have hu_range : u ∈ (ggGamma L hNL').range := ⟨y, hyu⟩
  have hβmem : β ∈ A' := Subgroup.mem_map.mpr ⟨u, hu_range, rfl⟩
  have hβord : orderOf β = p := by
    have hinj : Function.Injective (ggInducedAut θL') :=
      ggInducedAut_injective_of_perfect hperf θL'
    have h1 : orderOf (ggInducedAut θL' u) = orderOf u :=
      orderOf_injective (ggInducedAut θL') hinj u
    change orderOf (ggInducedAut θL' u) = p
    rw [h1, huord]
  have hAJ : ∀ a ∈ A', ∀ j ∈ J₀, a j ∈ J₀ := by
    intro a ha j hj
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
    rw [← hb]
    obtain ⟨j', hj', hjj'⟩ := Subgroup.mem_map.mp hj
    rw [← hjj']
    rw [← hcomm_all]
    refine Subgroup.mem_map.mpr ⟨ggGamma L hNL' b j', ?_, rfl⟩
    show ((ggGamma L hNL' b j' : ↥L) : G) ∈ J
    rw [ggGamma_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hN b.2) (j' : G)).mp
      (Subgroup.mem_subgroupOf.mp hj')
  have hP0 : Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := ⟨θ'⟩
  have hMind : ∀ α ∈ M₀, ∃ a ∈ A', ∀ j j' : ↥J₀,
      (j' : R') = a j → α (QuotientGroup.mk j) = QuotientGroup.mk j' := by
    intro α hα
    obtain ⟨c, hc, hcα⟩ := Subgroup.mem_map.mp hα
    obtain ⟨d0, hd0, hd0c⟩ := Subgroup.mem_map.mp hc
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hd0
    rw [← hb] at hd0c
    refine ⟨ggInducedAut θL' (ggGamma L hNL' b),
      Subgroup.mem_map.mpr ⟨ggGamma L hNL' b, ⟨b, rfl⟩, rfl⟩, ?_⟩
    intro j j' hjj'
    obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.mp j.2
    let xJ : ↥(J.subgroupOf L) := ⟨x, hx⟩
    have hxJmem : ggGamma L hNL' b x ∈ J.subgroupOf L := by
      show ((ggGamma L hNL' b x : ↥L) : G) ∈ J
      rw [ggGamma_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hN b.2) (x : G)).mp
        (Subgroup.mem_subgroupOf.mp hx)
    have hιx : ι (QuotientGroup.mk xJ) = QuotientGroup.mk j := by
      rw [ι_mk]
      congr 1
      exact Subtype.ext hxj
    have hes : e.symm (QuotientGroup.mk j) = QuotientGroup.mk (φ xJ) := by
      dsimp only [e]
      rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, ← hιx,
        MulEquiv.symm_apply_apply, centerQuotCongr_mk]
    have he_mk : ∀ y : ↥J, e (QuotientGroup.mk y) = QuotientGroup.mk
        ⟨π (φ.symm y), Subgroup.mem_map_of_mem _ (φ.symm y).2⟩ := by
      intro y
      dsimp only [e]
      rw [MulEquiv.trans_apply, ← centerQuotCongr_symm, centerQuotCongr_mk, ι_mk]
    have hxx : φ ⟨ggGamma L hNL' b x, hxJmem⟩ = (ggBsAut hN b) (φ xJ) := by
      dsimp only [φ]
      apply Subtype.ext
      rw [Subgroup.subgroupOfEquivOfLe_apply_coe, l02qq2cv_ggBsAut_apply_coe,
        Subgroup.subgroupOfEquivOfLe_apply_coe]
      simp only [ggGamma_coe, Subgroup.coe_subgroupOf]
      rfl
    have hxx' : (⟨ggGamma L hNL' b x, hxJmem⟩ : ↥(J.subgroupOf L)) =
        φ.symm ((ggBsAut hN b) (φ xJ)) := by
      rw [← hxx, MulEquiv.symm_apply_apply]
    rw [← hcα, ← hd0c]
    change MulAut.congr e (centerQuotAut ↥J (ggBsAut hN b)) (QuotientGroup.mk j) =
      QuotientGroup.mk j'
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    rw [hes, centerQuotAut_mk, he_mk]
    congr 1
    apply Subtype.ext
    rw [← hxx']
    show π (ggGamma L hNL' b x) = (j' : R')
    rw [hcomm_all]
    rw [← hxj] at hjj'
    exact hjj'.symm
  have hLift : Q2LinearLift M₀ :=
    hQ A' hAb hAI β hβmem hβord J₀ hJ₀comp hAJ K rfl hP0 M₀ hMind
  obtain ⟨hd, m, hm, hKm⟩ := l02qq2cv_numerics hΛ hfits' hpd hpq
  have hcomm := q2_commutative_of_linearLift hLift hd hm hKm θ'
  have hcomp : (MulAut.congr θ').toMonoidHom.comp (MulAut.congr e).toMonoidHom
      = (MulAut.congr θ).toMonoidHom := by
    have heθ' : e.trans θ' = θ := by
      dsimp only [θ']
      ext x
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have h1 : (MulAut.congr e).trans (MulAut.congr θ') = MulAut.congr θ := by
      have h2 : (MulAut.congr e).trans (MulAut.congr θ') = MulAut.congr (e.trans θ') := by
        ext α
        rfl
      rw [h2, heθ']
    calc (MulAut.congr θ').toMonoidHom.comp (MulAut.congr e).toMonoidHom
        = ((MulAut.congr e).trans (MulAut.congr θ')).toMonoidHom := rfl
      _ = (MulAut.congr θ).toMonoidHom := by rw [h1]
  have hMeq : M₀.map (MulAut.congr θ').toMonoidHom
      = (ggBsAut hN).range.map (kgInducedAut θ) := by
    dsimp only [M₀]
    simp only [Subgroup.map_map]
    rw [← MonoidHom.comp_assoc, hcomp]
    rfl
  rw [hMeq] at hcomm
  exact hcomm

end CFSG.StandardType
