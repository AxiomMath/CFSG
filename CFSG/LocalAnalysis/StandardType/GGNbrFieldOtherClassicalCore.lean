module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixCore
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsWrap
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusNoLineFieldComp_of_fixDataSC {p r : ℕ} (hp : p.Prime) {R : Type}
    [Group R] {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p r R I)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataSC p r I x) :
    GGTorusNoLineFieldComp p r R I F := by
  intro L' _ _ ψ hψ hker hperf A hAe hAind hcard1 hcard3 hsc
  obtain ⟨J, S, hJI, hJS, hN, hgen, hS⟩ := hcyc
  have hIJ : ∀ φ : MulAut R, φ ∈ I ↔ φ ∈ J := fun φ => by rw [← hJI]; rfl
  obtain ⟨Ind, hInd⟩ := ggInducedHom_exists ψ hψ A (fun a ha => by
    obtain ⟨φ, -, h⟩ := hAind a ha
    exact ⟨φ, h⟩)
  have hIndcl : ∀ a : A, Ind a ∈ Subgroup.closure (I ∪ F) := by
    intro a
    obtain ⟨φ, hφ, h⟩ := hAind a a.2
    rw [ggInduced_unique hψ (hInd a) h]
    exact hφ
  have hexp : ∀ u ∈ A, u ^ p = 1 := hAe.2
  have hIndp : ∀ a : A, Ind a ^ p = 1 := by
    intro a
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hexp a a.2)
    rw [this, map_one]
  have hIndS : ∀ a : A, Ind a ∈ S := fun a => hS _ (hIndcl a) ⟨1, by simpa using hIndp a⟩
  let A₀ : Subgroup (MulAut L') := (J.comap Ind).map A.subtype
  have hA₀A : A₀ ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hmem : ∀ a : A, (a : MulAut L') ∈ A₀ ↔ Ind a ∈ J := by
    intro a
    constructor
    · rintro ⟨a', ha', h⟩
      have : a' = a := Subtype.ext h
      subst this
      exact ha'
    · intro h
      exact ⟨a, h, rfl⟩
  obtain ⟨hcardle, hgenA⟩ := ggCyclicSplit hp hA₀A hexp Ind hN hgen hIndS hmem
  by_cases hAA₀ : A ≤ A₀
  · have hind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l) := by
      intro a ha
      exact ⟨Ind ⟨a, ha⟩, (hIJ _).mpr ((hmem ⟨a, ha⟩).mp (hAA₀ ha)), hInd ⟨a, ha⟩⟩
    have hc1 : p ^ r ≤ Nat.card A :=
      le_trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ r)) hcard1
    obtain ⟨W, h1, h2⟩ := hin L' ψ hψ hker hperf A hAe hind hc1 hcard3 hsc
    exact ⟨W, h1, fun hN' a₀ ha₀ hne _ hcl => h2 hN' a₀ ha₀ hne hcl⟩
  · obtain ⟨b, hbA, hbA₀⟩ := SetLike.not_le_iff_exists.mp hAA₀
    set x : MulAut R := Ind ⟨b, hbA⟩ with hx
    have hxcl : x ∈ Subgroup.closure (I ∪ F) := hIndcl _
    have hxI : x ∉ I := fun h => hbA₀ ((hmem ⟨b, hbA⟩).mpr ((hIJ _).mp h))
    obtain ⟨R₀, _, I₀, θ₀, hs₀, hna₀, hgeom, -, hline₀, hscr₀⟩ := hfix x hxcl hxI (hIndp _)
    have hK : ⁅ggFixDer x, ggFixDer x⁆ = ggFixDer x := ggFixDer_perfect θ₀ hs₀ hna₀
    obtain ⟨ψ'', hψ''eq, hψ''s, -, hψ''kc, hψ''perf⟩ :=
      ggSubfieldCore ψ hψ hker (ggFixDer x) hK θ₀
    have hmapK : (ggCore ψ (ggFixDer x)).map ψ = ggFixDer x :=
      (ggPerfectCore ψ hψ hker (ggFixDer x) hK).1
    have hHK : ∀ l ∈ ggCore ψ (ggFixDer x), ψ l ∈ ggFixDer x := fun l hl => by
      rw [← hmapK]
      exact Subgroup.mem_map_of_mem ψ hl
    have hcomm : ∀ a : A, Ind a * x = x * Ind a := by
      intro a
      rw [hx, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.comm a.2 hbA)
    have hstab : ∀ a ∈ A, ∀ l ∈ ggCore ψ (ggFixDer x), a l ∈ ggCore ψ (ggFixDer x) :=
      fun a ha l hl =>
        ggCore_stab ψ (ggFixDer x) a (Ind ⟨a, ha⟩) (hInd ⟨a, ha⟩)
          (fun g hg => ggFixDer_map_mem (hcomm ⟨a, ha⟩) hg) l hl
    have hbH : ∀ l ∈ ggCore ψ (ggFixDer x), b l = l := fun l hl =>
      mem_ggFixSub.mp (ggFixes_core ψ hker b x (fun l => (hInd ⟨b, hbA⟩ l).symm)
        ((ggFixDer x).comap ψ) (fun l hl => ggFixDer_le_ggFixSub x hl) hl)
    generalize ggCore ψ (ggFixDer x) = H at hmapK hHK hstab hbH ψ'' hψ''eq hψ''s hψ''kc hψ''perf
    obtain ⟨res, hres⟩ := ggAutRestrictHom H A₀ (fun a ha => hstab a (hA₀A ha))
    have hdec := ggTransfer_decomp (A := A) (A₀ := A₀) (H := H) hbH (hgenA b hbA hbA₀)
    have hcJ : ∀ c : A₀, Ind ⟨(c : MulAut L'), hA₀A c.2⟩ ∈ J := fun c => (hmem _).mp c.2
    have hinj : Function.Injective res := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have h1 : Ind ⟨(c : MulAut L'), hA₀A c.2⟩ = 1 := by
        refine hgeom.2 _ ((hIJ _).mpr (hcJ c)) (hcomm _) ?_
        intro g hg
        have hg' : g ∈ H.map ψ := by rw [hmapK]; exact hg
        obtain ⟨l, hl, rfl⟩ := hg'
        have e : ((res c ⟨l, hl⟩ : H) : L') = (c : MulAut L') l := hres c ⟨l, hl⟩
        rw [hc] at e
        rw [hInd _ l, ← e]
        rfl
      refine Subtype.ext (ggAut_eq_one_of_induced_one ψ hker hperf c fun l => ?_)
      rw [← hInd ⟨(c : MulAut L'), hA₀A c.2⟩ l, h1]
      rfl
    have hB₀ind : ∀ a ∈ res.range, ∃ φ₀ ∈ I₀, ∀ l : H, φ₀ (ψ'' l) = ψ'' (a l) := by
      rintro _ ⟨c, rfl⟩
      obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := hgeom.1 (Ind ⟨(c : MulAut L'), hA₀A c.2⟩) ((hIJ _).mpr (hcJ c))
        (hcomm _)
      refine ⟨φ₀, hφ₀, fun l => ?_⟩
      rw [hψ''eq l (hHK l l.2), hψ''eq (res c l) (hHK _ (res c l).2), ← hφ₀eq (ψ l) (hHK l l.2)]
      congr 2
      rw [hInd _ l, hres c l]
    have hconj : ∀ n ∈ H, MulAut.conj n ∈ A → MulAut.conj n ∈ A₀ := by
      intro n _ hn
      have e : Ind ⟨MulAut.conj n, hn⟩ = MulAut.conj (ψ n) :=
        ggInduced_unique hψ (hInd _) (fun l => ggInduced_conj ψ n l)
      exact (hmem ⟨MulAut.conj n, hn⟩).mpr (by rw [e, ← hIJ]; exact hInn _)
    have hnorm : ∀ n ∈ H, ∀ a ∈ A₀, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A₀ := by
      intro n _ a ha hc
      have e : Ind ⟨MulAut.conj n * a * (MulAut.conj n)⁻¹, hc⟩ =
          MulAut.conj (ψ n) * Ind ⟨a, hA₀A ha⟩ * (MulAut.conj (ψ n))⁻¹ :=
        ggInduced_unique hψ (hInd _) (ggInduced_conj_mul_conj_inv ψ n (hInd ⟨a, hA₀A ha⟩))
      have hcn : MulAut.conj (ψ n) ∈ J := (hIJ _).mp (hInn _)
      refine (hmem ⟨_, hc⟩).mpr ?_
      rw [e]
      exact J.mul_mem (J.mul_mem hcn ((hmem ⟨a, hA₀A ha⟩).mp ha)) (J.inv_mem hcn)
    have hcardA₀ : p ^ r ≤ Nat.card A₀ := by
      have h : p * p ^ r ≤ p * Nat.card A₀ :=
        calc p * p ^ r = p ^ (r + 1) := by ring
          _ ≤ Nat.card A := hcard1
          _ ≤ p * Nat.card A₀ := hcardle
      exact Nat.le_of_mul_le_mul_left h hp.pos
    have hcardB₀ : Nat.card res.range = Nat.card A₀ :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hsc₀ := ggTransfer_selfCent res hres hdec hsc hconj
    have h3₀ : p ^ 3 ≤ Nat.card res.range :=
      hscr₀ H ψ'' hψ''s hψ''kc hψ''perf res.range (ggIsElemAbelian_range hA₀A hAe res) hB₀ind
        hsc₀
    obtain ⟨W₀, h1, h2⟩ := hline₀ H ψ'' hψ''s hψ''kc hψ''perf res.range
      (ggIsElemAbelian_range hA₀A hAe res) hB₀ind (hcardB₀ ▸ hcardA₀) h3₀ hsc₀
    refine ⟨Subtype.val '' W₀, ggTransfer_first res hres hdec h1, ?_⟩
    intro hN' a₀ ha₀ hne hind _
    have ha₀A₀ : a₀ ∈ A₀ := by
      obtain ⟨φ, hφ, h⟩ := hind
      have e := ggInduced_unique hψ (hInd ⟨a₀, ha₀⟩) h
      exact (hmem ⟨a₀, ha₀⟩).mpr (by rw [e]; exact (hIJ _).mp hφ)
    exact ggTransfer_second res hres hinj hA₀A hnorm h2 hN' a₀ ha₀A₀ hne

theorem ggTorusFieldTransferSC {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hin : GGTorusNoLineComp p r R I)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S)
    (hfix : ∀ x ∈ Subgroup.closure (I ∪ F), x ∉ I → x ^ p = 1 → GGFixDataSC p r I x) :
    GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F :=
  ⟨ggTorusLiftFix_of_fixData fun x hx hxI hxp => (hfix x hx hxI hxp).fixData,
    ggTorusNoLineFieldComp_of_fixDataSC hp hInn hin hcyc hfix⟩

theorem ggFixDataSC_of_rawDatum {p r : ℕ} {lab₀ : LargeEvenLabel}
    (hRow₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlainSC p r))
    {R : Type} [Group R] {I : Set (MulAut R)} {x : MulAut R}
    (h : LargeEvenRawDatum lab₀ fun R₀ _ I₀ _ => IsSimpleGroup R₀ ∧
      (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer x ≃* R₀, GGFixGeom I x I₀ θ₀) :
    GGFixDataSC p r I x := by
  obtain ⟨R₀, inst₀, I₀, F₀, ⟨hs, hna, θ₀, hgeom⟩, ⟨-, hlift, hline⟩, hscr⟩ :=
    largeEvenRawDatum_exists (hRow₀ _ h)
  exact ⟨R₀, inst₀, I₀, θ₀, hs, hna, hgeom, hlift, hline hs hna, hscr hs hna⟩

theorem largeEvenLabelAll_fieldFixSC {p r : ℕ} (hp : p.Prime) {lab lab₀ : LargeEvenLabel}
    (hRow : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r))
    (hRow₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlainSC p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hfix : LargeEvenLabelAll lab (GGRawFieldFix p lab₀)) :
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F := by
  refine (largeEvenLabelAll_and hRow (largeEvenLabelAll_and hcyc hfix)).mono ?_
  rintro R _ I F ⟨⟨hInn, hlift, hin⟩, hc, hf⟩ hs hna
  exact ggTorusFieldTransferSC hp hInn (hin hs hna) (hc hs hna)
    fun x hx hxI hxp => ggFixDataSC_of_rawDatum hRow₀ (hf hs hna x hx hxI hxp)

theorem largeEvenLabelAll_fieldKLevelComp_of_fixSC {p r : ℕ} (hp : p.Prime)
    {lab lab₀ : LargeEvenLabel}
    (hRow : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r))
    (hRow₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlainSC p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hfix : LargeEvenLabelAll lab (GGRawFieldFix p lab₀)) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  largeEvenLabelAll_fieldKLevelComp_of_row hRow
    (largeEvenLabelAll_fieldFixSC hp hRow hRow₀ hcyc hfix)

theorem largeEvenLabelAll_fieldKLevelComp_of_stdSC {p r : ℕ} (hp : p.Prime)
    {lab lab₀ : LargeEvenLabel} (hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p r))
    (hR₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlainSC p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hconj : LargeEvenLabelAll lab (GGRawFieldConj p))
    (hcen : LargeEvenLabelAll lab GGRawFieldCentral)
    (hinn : LargeEvenLabelAll lab (GGRawInnField p))
    (hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p lab₀)) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r) :=
    hR.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (hn hs hna)⟩
  have hAll := largeEvenLabelAll_and hconj
    (largeEvenLabelAll_and hcen (largeEvenLabelAll_and hinn hstd))
  have hFx : LargeEvenLabelAll lab (GGRawFieldFix p lab₀) :=
    (largeEvenLabelAll_and hcyc hAll).mono fun _ _ _ _ ⟨hcy, hc, hce, hi, hst⟩ hs hna =>
      ggRawFieldFix_of_std hc (ggRawFieldNorm_of_central hce hi hs hna) hcy hst hs hna
  exact largeEvenLabelAll_fieldKLevelComp_of_fixSC hp hRK hR₀ hcyc hFx

theorem ggFieldKLevel_of_fixKnownRowSC {r : ℕ} {S Rw : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab →
      p ∣ lab.n ∧ Rw p lab ∧ Rw p ⟨lab.tag, lab.rank, lab.n / p⟩)
    (hΛ : ∀ p lab, LargeEvenInLambda2 lab → S p lab →
      LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩)
    (hNot : ∀ p lab, Rw p lab → GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3))
    (hFix : GGFieldFixKnown S)
    (hRow : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      Rw p lab → LargeEvenLabelAll lab (GGNbrWeylRowPlainSC p r))
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hSl
  obtain ⟨hdvd, hrow, hrow₀⟩ := hS p lab hSl
  have hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p r) :=
    (hRow p lab hp hp2 hlab hrow).mono fun _ _ _ _ h => h.1
  have hR₀ : LargeEvenLabelAll ⟨lab.tag, lab.rank, lab.n / p⟩ (GGNbrWeylRowPlainSC p r) :=
    hRow p _ hp hp2 (hΛ p lab hlab hSl) hrow₀
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab (hNot p lab hrow).1).mono fun _ _ _ _ h =>
      ggRawFieldCycW_of_pCyclic h
  exact largeEvenLabelAll_fieldKLevelComp_of_stdSC hp hR hR₀ hCyc
    (hconj p hp hp2 lab hlab (hNot p lab hrow).2) (hcen lab hlab) (hinn p hp hp2 lab hlab)
    (hFix p lab hp hp2 hlab hSl)

end CFSG.StandardType

end
