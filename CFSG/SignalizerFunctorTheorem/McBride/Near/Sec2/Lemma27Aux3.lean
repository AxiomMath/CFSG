module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux2
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux1

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ]

theorem conjOrbit_eq_of_mem {Z J K' : Subgroup Γ} (h : K' ∈ L514.conjOrbit Z J) :
    L514.conjOrbit Z K' = L514.conjOrbit Z J := by
  ext M
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨b * c, mul_mem hb hc, (L514.map_conj_map_conj J c b)⟩
  · intro hM
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨b, hb, rfl⟩ := hM
    refine ⟨b * c⁻¹, mul_mem hb (inv_mem hc), ?_⟩
    rw [L514.map_conj_map_conj]
    simp

theorem orbitClosure_eq_of_mem {Z J K' : Subgroup Γ} (h : K' ∈ L514.conjOrbit Z J) :
    orbitClosure K' Z = orbitClosure J Z := by
  rw [L514.orbitClosure_eq_sSup, L514.orbitClosure_eq_sSup, conjOrbit_eq_of_mem h]

variable [Finite Γ]

theorem isDirectPair_orbitClosure_outsideOrbit' {Z K J : Subgroup Γ}
    (hK : IsDirectProduct (lcal K) K) (hZK : Z ≤ Subgroup.normalizer (K : Set Γ))
    (hJ : J ∈ lcal K) :
    IsDirectPair (orbitClosure J Z) (L514.outsideOrbit K Z J) K := by
  have hL := L514.isDirectProduct_conjOrbit hZK hJ
  have hsub : L514.conjOrbit Z J ⊆ lcal K := L514.conjOrbit_subset_lcal hZK hJ
  have hLeq : sSup (L514.conjOrbit Z J) = orbitClosure J Z := hL.sSup_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLeq]
    refine L514.commute_of_forall_commute_sSup fun J₁ hJ₁ J₂ hJ₂ x hx y hy => ?_
    exact hK.commute J₁ (hsub hJ₁) J₂ hJ₂.1 (fun h => hJ₂.2 (h ▸ hJ₁)) x hx y hy
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzL, hzM⟩ := Subgroup.mem_inf.mp hz
    have hzL' : z ∈ sSup (L514.conjOrbit Z J) := hLeq ▸ hzL
    have hzK : z ∈ K := hK.sSup_diff_le _ hsub hzL'
    have hone : (⟨z, hzK⟩ : K) = 1 := by
      apply hK.ext_coord
      intro J'' hJ''
      rw [map_one, hK.coord_eq_one_iff hJ'']
      by_cases hmem : J'' ∈ L514.conjOrbit Z J
      · have hss : lcal K \ L514.conjOrbit Z J ⊆ lcal K \ {J''} :=
          Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hmem)
        exact sSup_le_sSup hss hzM
      · have hss : L514.conjOrbit Z J ⊆ lcal K \ {J''} := fun J₁ hJ₁ =>
          ⟨hsub hJ₁, fun h => hmem (h ▸ hJ₁)⟩
        exact sSup_le_sSup hss hzL'
    simpa using congrArg Subtype.val hone
  · rw [← hLeq, L514.outsideOrbit, ← sSup_union, Set.union_sdiff_cancel hsub, hK.sSup_eq]

@[expose] def diagOf (K : Subgroup Γ) (a : Γ) (J : Subgroup Γ) : Subgroup Γ :=
  (K ⊓ Subgroup.centralizer {a}) ⊓ orbitClosure J (Subgroup.zpowers a)

@[expose] def diagSet (K : Subgroup Γ) (a : Γ) : Set (Subgroup Γ) := diagOf K a '' lcal K

omit [Finite Γ] in
theorem diagOf_le_cen (K : Subgroup Γ) (a : Γ) (J : Subgroup Γ) :
    diagOf K a J ≤ K ⊓ Subgroup.centralizer {a} := inf_le_left

omit [Finite Γ] in
theorem diagOf_le_orbitClosure (K : Subgroup Γ) (a : Γ) (J : Subgroup Γ) :
    diagOf K a J ≤ orbitClosure J (Subgroup.zpowers a) := inf_le_right

theorem orbitClosure_le_of_mem_lcal {K Z J : Subgroup Γ} (hK : IsDirectProduct (lcal K) K)
    (hZK : Z ≤ Subgroup.normalizer (K : Set Γ)) (hJ : J ∈ lcal K) : orbitClosure J Z ≤ K := by
  have hL := L514.isDirectProduct_conjOrbit hZK hJ
  rw [← hL.sSup_eq]
  exact hK.sSup_diff_le _ (L514.conjOrbit_subset_lcal hZK hJ)

omit [Finite Γ] in
theorem centralizer_zpowers_eq (a : Γ) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer {a} := Diag.centralizer_zpowers a

theorem projIn_orbit_centralizer {p : ℕ} (hp : p.Prime) {K : Subgroup Γ}
    {a : Γ} (haK : a ∈ Subgroup.normalizer (K : Set Γ))
    (hap : a ^ p = 1) {J : Subgroup Γ} (hJ : J ∈ lcal K)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) :
    projIn (L514.conjOrbit (Subgroup.zpowers a) J) J
      (orbitClosure J (Subgroup.zpowers a) ⊓ Subgroup.centralizer {a}) = J := by
  set Z := Subgroup.zpowers a with hZ
  have hZK : Z ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.zpowers_le.mpr haK
  have hL := L514.isDirectProduct_conjOrbit hZK hJ
  have hJO : J ∈ L514.conjOrbit Z J := L514.self_mem_conjOrbit Z J
  have hper : ∀ b ∈ Z, ∀ J' ∈ L514.conjOrbit Z J,
      J'.map (MulAut.conj b).toMonoidHom ∈ L514.conjOrbit Z J :=
    fun b hb J' hJ' => L514.map_conj_mem_conjOrbit hJ' hb
  have h1 := projIn_centralizer_eq hL hper hJO
  rw [centralizer_zpowers_eq, Diag.zpowers_inf_eq_bot hp hap haJ] at h1
  rw [h1]
  refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
  rw [hh]
  simp

theorem exists_mulEquiv_diagOf {p : ℕ} (hp : p.Prime) {K : Subgroup Γ}
    (hK : IsDirectProduct (lcal K) K) {a : Γ} (haK : a ∈ Subgroup.normalizer (K : Set Γ))
    (hap : a ^ p = 1) {J : Subgroup Γ} (hJ : J ∈ lcal K)
    (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) : Nonempty (↥(diagOf K a J) ≃* ↥J) := by
  set Z := Subgroup.zpowers a with hZ
  have hZK : Z ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.zpowers_le.mpr haK
  have hL := L514.isDirectProduct_conjOrbit hZK hJ
  have hOS : L514.conjOrbit Z J ⊆ lcal K := L514.conjOrbit_subset_lcal hZK hJ
  have hJO : J ∈ L514.conjOrbit Z J := L514.self_mem_conjOrbit Z J
  have hper : ∀ b ∈ Z, ∀ J' ∈ L514.conjOrbit Z J,
      J'.map (MulAut.conj b).toMonoidHom ∈ L514.conjOrbit Z J :=
    fun b hb J' hJ' => L514.map_conj_mem_conjOrbit hJ' hb
  have htrans : ∀ K' ∈ L514.conjOrbit Z J, ∃ b ∈ Z, K' = J.map (MulAut.conj b).toMonoidHom :=
    fun K' hK' => hK'
  have hLK : orbitClosure J Z ≤ K := orbitClosure_le_of_mem_lcal hK hZK hJ
  have hDK : diagOf K a J ≤ K := inf_le_left.trans inf_le_left
  let φ : ↥(diagOf K a J) →* ↥J := (hK.coord hJ).comp (Subgroup.inclusion hDK)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : Γ) ∈ sSup (lcal K \ {J}) := (hK.coord_eq_one_iff hJ _).mp hx
    have hxD := x.2
    obtain ⟨hxKC, hxL⟩ := Subgroup.mem_inf.mp hxD
    have hxC : (x : Γ) ∈ Subgroup.centralizer {a} := (Subgroup.mem_inf.mp hxKC).2
    have hxO : (x : Γ) ∈ sSup (L514.conjOrbit Z J) := by
      rw [← L514.orbitClosure_eq_sSup]; exact hxL
    have hx2 : (x : Γ) ∈ sSup (L514.conjOrbit Z J \ {J}) :=
      Diag.sSup_inf_sSup_diff_le hK hOS hJO ⟨hxO, hx1⟩
    have hbot := inf_centralizer_inf_sSup_eq_bot_of_transitive hL hper hJO htrans
    have hmem : (x : Γ) ∈ orbitClosure J Z ⊓ Subgroup.centralizer (Z : Set Γ) ⊓
        sSup (L514.conjOrbit Z J \ {J}) :=
      ⟨⟨hxL, by rw [hZ, centralizer_zpowers_eq]; exact hxC⟩, hx2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hsurj : Function.Surjective φ := by
    intro j
    have hj : (j : Γ) ∈ J := j.2
    have hjproj : (j : Γ) ∈ projIn (L514.conjOrbit Z J) J
        (orbitClosure J Z ⊓ Subgroup.centralizer {a}) := by
      rw [projIn_orbit_centralizer hp haK hap hJ haJ]; exact hj
    obtain ⟨-, l, hl, hjl⟩ :=
      (mem_proj_iff (hL.commute_sSup_diff hJO)).mp hjproj
    have hl' : l ∈ sSup (lcal K \ {J}) :=
      sSup_le_sSup (Set.sdiff_subset_sdiff_left hOS) hl
    have hy : (j : Γ) * l ∈ diagOf K a J :=
      ⟨⟨hLK hjl.1, hjl.2⟩, hjl.1⟩
    refine ⟨⟨(j : Γ) * l, hy⟩, Subtype.ext ?_⟩
    exact hK.coord_mul hJ hj hl'
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

omit [Finite Γ] in
theorem exists_split_of_centralizes {L M : Subgroup Γ} {a y : Γ}
    (hcomm : ∀ x ∈ L, ∀ z ∈ M, Commute x z) (hdisj : L ⊓ M = ⊥)
    (haL : a ∈ Subgroup.normalizer (L : Set Γ)) (haM : a ∈ Subgroup.normalizer (M : Set Γ))
    (hy : y ∈ L ⊔ M) (hya : y ∈ Subgroup.centralizer {a}) :
    ∃ l ∈ L, l ∈ Subgroup.centralizer {a} ∧ ∃ m ∈ M, m ∈ Subgroup.centralizer {a} ∧ y = l * m := by
  obtain ⟨l, hl, m, hm, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hy
  have hl' : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL l).mp hl
  have hm' : a * m * a⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp haM m).mp hm
  have hy' : (l * m) * a = a * (l * m) := Subgroup.mem_centralizer_singleton_iff.mp hya
  have hprod : (a * l * a⁻¹) * (a * m * a⁻¹) = l * m := by
    calc (a * l * a⁻¹) * (a * m * a⁻¹) = a * (l * m) * a⁻¹ := by group
      _ = (l * m) * a * a⁻¹ := by rw [← hy']
      _ = l * m := by group
  have h1 : l⁻¹ * (a * l * a⁻¹) = m * (a * m * a⁻¹)⁻¹ := by
    have : l⁻¹ * ((a * l * a⁻¹) * (a * m * a⁻¹)) * (a * m * a⁻¹)⁻¹ = m * (a * m * a⁻¹)⁻¹ := by
      rw [hprod]; group
    rw [← this]; group
  have hmem : l⁻¹ * (a * l * a⁻¹) ∈ L ⊓ M :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hl) hl', by rw [h1]; exact mul_mem hm (inv_mem hm')⟩
  rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hlc : l * a = a * l := by
    have := congrArg (· * a) hmem
    simpa [mul_assoc] using this
  have hmc : m * a = a * m := by
    have hm1 : a * m * a⁻¹ = m := by
      have h2 := hprod
      rw [← hmem] at h2
      simpa using h2
    have := congrArg (· * a) hm1
    simpa [mul_assoc] using this.symm
  exact ⟨l, hl, Subgroup.mem_centralizer_singleton_iff.mpr hlc, m, hm,
    Subgroup.mem_centralizer_singleton_iff.mpr hmc, rfl⟩

theorem sSup_inf_centralizer_le_iSup_diagOf {K : Subgroup Γ} (hK : IsDirectProduct (lcal K) K)
    {a : Γ} (haK : a ∈ Subgroup.normalizer (K : Set Γ)) :
    ∀ (n : ℕ) (T : Set (Subgroup Γ)), T ⊆ lcal K →
      (∀ g ∈ Subgroup.zpowers a, ∀ J ∈ T, J.map (MulAut.conj g).toMonoidHom ∈ T) →
      T.ncard = n → sSup T ⊓ Subgroup.centralizer {a} ≤ ⨆ J ∈ T, diagOf K a J := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hTS hTst hTn
  set Z := Subgroup.zpowers a with hZ
  have hZK : Z ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.zpowers_le.mpr haK
  rcases T.eq_empty_or_nonempty with rfl | ⟨J, hJT⟩
  · simp
  have hJK : J ∈ lcal K := hTS hJT
  set O := L514.conjOrbit Z J with hO
  have hOT : O ⊆ T := by
    rintro _ ⟨g, hg, rfl⟩
    exact hTst g hg J hJT
  set T' := T \ O with hT'
  have hT'S : T' ⊆ lcal K \ O := fun x hx => ⟨hTS hx.1, hx.2⟩
  have hT'st : ∀ g ∈ Z, ∀ J' ∈ T', J'.map (MulAut.conj g).toMonoidHom ∈ T' := by
    intro g hg J' hJ'
    refine ⟨hTst g hg J' hJ'.1, fun hmem => hJ'.2 ?_⟩
    have := L514.map_conj_mem_conjOrbit hmem (inv_mem hg : g⁻¹ ∈ Z)
    rwa [L514.map_conj_map_conj_inv] at this
  have hdp := isDirectPair_orbitClosure_outsideOrbit' hK hZK hJK
  have hM : sSup T' ≤ L514.outsideOrbit K Z J := sSup_le_sSup hT'S
  have hLK : orbitClosure J Z ≤ K := orbitClosure_le_of_mem_lcal hK hZK hJK
  have hcomm : ∀ x ∈ orbitClosure J Z, ∀ z ∈ sSup T', Commute x z :=
    fun x hx z hz => hdp.commute x hx z (hM hz)
  have hdisj : orbitClosure J Z ⊓ sSup T' = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hM).trans hdp.inf_eq_bot.le)
  have haL : a ∈ Subgroup.normalizer ((orbitClosure J Z : Subgroup Γ) : Set Γ) :=
    L514.mem_normalizer_orbitClosure (Subgroup.mem_zpowers a)
  have haM : a ∈ Subgroup.normalizer ((sSup T' : Subgroup Γ) : Set Γ) :=
    L514.mem_normalizer_sSup (fun J' hJ' => hT'st a (Subgroup.mem_zpowers a) J' hJ')
      (fun J' hJ' => hT'st a⁻¹ (inv_mem (Subgroup.mem_zpowers a)) J' hJ')
  have hsup : sSup T = orbitClosure J Z ⊔ sSup T' := by
    rw [L514.orbitClosure_eq_sSup, ← sSup_union]
    congr 1
    exact (Set.union_sdiff_cancel hOT).symm
  have hlt : T'.ncard < n := by
    rw [← hTn]
    refine Set.ncard_lt_ncard (lt_of_le_of_ne Set.sdiff_subset fun h => ?_) (Set.toFinite T)
    have : J ∈ T' := by rw [h]; exact hJT
    exact this.2 (L514.self_mem_conjOrbit Z J)
  intro y hy
  obtain ⟨hyT, hyc⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨l, hl, hlc, m, hm, hmc, rfl⟩ :=
    exists_split_of_centralizes hcomm hdisj haL haM (hsup ▸ hyT) hyc
  have hlD : l ∈ diagOf K a J := ⟨⟨hLK hl, hlc⟩, hl⟩
  have hmD := ih _ hlt T' (hT'S.trans Set.sdiff_subset) hT'st rfl ⟨hm, hmc⟩
  have h1 : diagOf K a J ≤ ⨆ J' ∈ T, diagOf K a J' := le_iSup₂_of_le J hJT le_rfl
  have h2 : (⨆ J' ∈ T', diagOf K a J') ≤ ⨆ J' ∈ T, diagOf K a J' :=
    biSup_mono fun i hi => hi.1
  exact mul_mem (h1 hlD) (h2 hmD)

omit [Finite Γ] in
theorem diagOf_eq_of_orbit_eq {K Z J₁ J₂ : Subgroup Γ} {a : Γ} (hZ : Z = Subgroup.zpowers a)
    (h : L514.conjOrbit Z J₁ = L514.conjOrbit Z J₂) : diagOf K a J₁ = diagOf K a J₂ := by
  unfold diagOf
  rw [← hZ, L514.orbitClosure_eq_sSup, L514.orbitClosure_eq_sSup, h]

theorem isDirectProduct_diagSet {K : Subgroup Γ}
    (hK : IsDirectProduct (lcal K) K) {a : Γ} (haK : a ∈ Subgroup.normalizer (K : Set Γ)) :
    IsDirectProduct (diagSet K a) (K ⊓ Subgroup.centralizer {a}) := by
  set Z := Subgroup.zpowers a with hZ
  have hZK : Z ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.zpowers_le.mpr haK
  have hstab : ∀ g ∈ Z, ∀ J ∈ lcal K, J.map (MulAut.conj g).toMonoidHom ∈ lcal K :=
    fun g hg J hJ => map_conj_mem_lcal hJ (hZK hg)
  have hdisj : ∀ J₁ ∈ lcal K, ∀ J₂ ∈ lcal K, diagOf K a J₁ ≠ diagOf K a J₂ →
      ∀ J ∈ L514.conjOrbit Z J₁, J ∉ L514.conjOrbit Z J₂ := by
    intro J₁ hJ₁ J₂ hJ₂ hne J h1 h2
    exact hne (diagOf_eq_of_orbit_eq hZ
      ((conjOrbit_eq_of_mem h1).symm.trans (conjOrbit_eq_of_mem h2)))
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩ hne x hx y hy
    have hx' : x ∈ sSup (L514.conjOrbit Z J₁) := by
      rw [← L514.orbitClosure_eq_sSup]; exact diagOf_le_orbitClosure K a J₁ hx
    have hy' : y ∈ sSup (L514.conjOrbit Z J₂) := by
      rw [← L514.orbitClosure_eq_sSup]; exact diagOf_le_orbitClosure K a J₂ hy
    refine L514.commute_of_forall_commute_sSup (fun J h1 J' h2 u hu v hv => ?_) x hx' y hy'
    exact hK.commute J (L514.conjOrbit_subset_lcal hZK hJ₁ h1) J'
      (L514.conjOrbit_subset_lcal hZK hJ₂ h2) (fun h => hdisj J₁ hJ₁ J₂ hJ₂ hne J h1 (h ▸ h2))
      u hu v hv
  · rintro _ ⟨J₁, hJ₁, rfl⟩
    have hdp := isDirectPair_orbitClosure_outsideOrbit' hK hZK hJ₁
    have hle : sSup (diagSet K a \ {diagOf K a J₁}) ≤ L514.outsideOrbit K Z J₁ := by
      refine sSup_le fun D hD => ?_
      obtain ⟨⟨J₂, hJ₂, rfl⟩, hne⟩ := hD
      refine (diagOf_le_orbitClosure K a J₂).trans ?_
      rw [L514.orbitClosure_eq_sSup]
      refine sSup_le_sSup fun J hJ => ⟨L514.conjOrbit_subset_lcal hZK hJ₂ hJ, fun h1 => ?_⟩
      exact hdisj J₂ hJ₂ J₁ hJ₁ (fun h => hne (by rw [h]; rfl)) J hJ h1
    exact (disjoint_iff.mpr hdp.inf_eq_bot).mono (diagOf_le_orbitClosure K a J₁) hle
  · refine le_antisymm (sSup_le ?_) ?_
    · rintro _ ⟨J, hJ, rfl⟩
      exact diagOf_le_cen K a J
    · have h1 := sSup_inf_centralizer_le_iSup_diagOf hK haK _ (lcal K) subset_rfl hstab rfl
      rw [hK.sSup_eq] at h1
      refine h1.trans ?_
      rw [diagSet, sSup_image]

omit [Finite Γ] in
theorem orbitClosure_map_conj {Z J : Subgroup Γ} {c : Γ} (hc : ∀ g ∈ Z, c * g = g * c) :
    (orbitClosure J Z).map (MulAut.conj c).toMonoidHom =
      orbitClosure (J.map (MulAut.conj c).toMonoidHom) Z := by
  unfold orbitClosure
  rw [Subgroup.map_iSup]
  refine iSup_congr fun g => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hg => ?_
  rw [L514.map_conj_map_conj, L514.map_conj_map_conj, hc g hg]

omit [Finite Γ] in
theorem diagOf_map_conj {K : Subgroup Γ} {a c : Γ} (hcK : c ∈ Subgroup.normalizer (K : Set Γ))
    (hca : c * a = a * c) (J : Subgroup Γ) :
    (diagOf K a J).map (MulAut.conj c).toMonoidHom =
      diagOf K a (J.map (MulAut.conj c).toMonoidHom) := by
  have hcZ : ∀ g ∈ Subgroup.zpowers a, c * g = g * c := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_right (show Commute c a from hca) k)).eq
  ext x
  rw [L514.mem_map_conj_iff]
  unfold diagOf
  rw [← orbitClosure_map_conj hcZ]
  simp only [Subgroup.mem_inf, L514.mem_map_conj_iff]
  have hK1 : c⁻¹ * x * c ∈ K ↔ x ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcK) x)
    simpa using this.symm
  have hC1 : c⁻¹ * x * c ∈ Subgroup.centralizer {a} ↔ x ∈ Subgroup.centralizer {a} := by
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hcac : c * a * c⁻¹ = a := by rw [hca]; group
      calc x * a = x * (c * a * c⁻¹) := by rw [hcac]
        _ = c * (c⁻¹ * x * c * a) * c⁻¹ := by group
        _ = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
        _ = (c * a * c⁻¹) * x := by group
        _ = a * x := by rw [hcac]
    · intro h
      calc c⁻¹ * x * c * a = c⁻¹ * x * (c * a) := by group
        _ = c⁻¹ * x * (a * c) := by rw [hca]
        _ = c⁻¹ * (x * a) * c := by group
        _ = c⁻¹ * (a * x) * c := by rw [h]
        _ = a * (c⁻¹ * x * c) := by
          have : c⁻¹ * a = a * c⁻¹ := by
            have h2 := congrArg (fun z => c⁻¹ * z * c⁻¹) hca
            simpa [mul_assoc] using h2.symm
          calc c⁻¹ * (a * x) * c = (c⁻¹ * a) * x * c := by group
            _ = (a * c⁻¹) * x * c := by rw [this]
            _ = a * (c⁻¹ * x * c) := by group
  rw [hK1, hC1]

omit [Finite Γ] in
theorem conj_mem_centralizer_of_commute {a c x : Γ} (hca : c * a = a * c)
    (hx : x ∈ Subgroup.centralizer {a}) : c * x * c⁻¹ ∈ Subgroup.centralizer {a} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have hcac : c * a * c⁻¹ = a := by rw [hca]; group
  have hc' : c⁻¹ * a = a * c⁻¹ := by
    have h2 := congrArg (fun z => c⁻¹ * z * c⁻¹) hca
    simpa [mul_assoc] using h2.symm
  calc c * x * c⁻¹ * a = c * x * (c⁻¹ * a) := by group
    _ = c * x * (a * c⁻¹) := by rw [hc']
    _ = c * (x * a) * c⁻¹ := by group
    _ = c * (a * x) * c⁻¹ := by rw [hx]
    _ = (c * a * c⁻¹) * (c * x * c⁻¹) := by group
    _ = a * (c * x * c⁻¹) := by rw [hcac]

omit [Finite Γ] in
theorem mem_normalizer_centralizer_of_commute {a c : Γ} (hca : c * a = a * c) :
    c ∈ Subgroup.normalizer ((Subgroup.centralizer {a} : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_centralizer_of_commute hca, fun h => ?_⟩
  have hc' : c⁻¹ * a = a * c⁻¹ := by
    have h2 := congrArg (fun z => c⁻¹ * z * c⁻¹) hca
    simpa [mul_assoc] using h2.symm
  simpa [mul_assoc] using conj_mem_centralizer_of_commute hc' h

theorem orbitClosure_inf_eq_bot {K Z J₁ J₂ : Subgroup Γ} (hK : IsDirectProduct (lcal K) K)
    (hZK : Z ≤ Subgroup.normalizer (K : Set Γ)) (hJ₁ : J₁ ∈ lcal K) (hJ₂ : J₂ ∈ lcal K)
    (hdisj : J₂ ∉ L514.conjOrbit Z J₁) : orbitClosure J₁ Z ⊓ orbitClosure J₂ Z = ⊥ := by
  have hdp := isDirectPair_orbitClosure_outsideOrbit' hK hZK hJ₁
  have hle : orbitClosure J₂ Z ≤ L514.outsideOrbit K Z J₁ := by
    rw [L514.orbitClosure_eq_sSup]
    refine sSup_le_sSup fun J hJ => ⟨L514.conjOrbit_subset_lcal hZK hJ₂ hJ, fun h1 => hdisj ?_⟩
    rw [← conjOrbit_eq_of_mem h1, conjOrbit_eq_of_mem hJ]
    exact L514.self_mem_conjOrbit Z J₂
  exact eq_bot_iff.mpr ((inf_le_inf_left _ hle).trans hdp.inf_eq_bot.le)

@[expose] def CycStab (A K : Subgroup Γ) : Prop :=
  ∀ J ∈ lcal K, ∃ n ∈ A, A ⊓ Subgroup.normalizer (J : Set Γ) ≤
    (A ⊓ Subgroup.centralizer (K : Set Γ)) ⊔ Subgroup.zpowers n

theorem diagOf_ne_bot {p : ℕ} (hp : p.Prime) {K : Subgroup Γ} (hK : IsDirectProduct (lcal K) K)
    {a : Γ} (haK : a ∈ Subgroup.normalizer (K : Set Γ)) (hap : a ^ p = 1) {J : Subgroup Γ}
    (hJ : J ∈ lcal K) (haJ : a ∉ Subgroup.normalizer (J : Set Γ)) : diagOf K a J ≠ ⊥ := by
  intro hbot
  obtain ⟨e⟩ := exists_mulEquiv_diagOf hp hK haK hap hJ haJ
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  have hsub : Subsingleton ↥(diagOf K a J) := by rw [hbot]; infer_instance
  have hsubJ : Subsingleton ↥J := e.symm.injective.subsingleton
  exact hnc (isMulCommutative_iff.mpr fun x y => by rw [Subsingleton.elim x y])

theorem diagSetting_centralizer {p : ℕ} {A K : Subgroup Γ} (h : DiagSetting p A K)
    {N : Subgroup Γ} (hN : ∀ J ∈ lcal K, N = A ⊓ Subgroup.normalizer (J : Set Γ)) {a : Γ}
    (ha : a ∈ A) (haN : a ∉ N) :
    DiagSetting p A (K ⊓ Subgroup.centralizer {a}) ∧
      (∀ D ∈ lcal (K ⊓ Subgroup.centralizer {a}), ∃ J ∈ lcal K, D = diagOf K a J) ∧
      (CycStab A K → CycStab A (K ⊓ Subgroup.centralizer {a})) := by
  have hp := h.prime
  have hK := h.direct
  have hap : a ^ p = 1 := h.elemAbelian.2 a ha
  have haK : a ∈ Subgroup.normalizer (K : Set Γ) := h.normalizes ha
  have haJ : ∀ J ∈ lcal K, a ∉ Subgroup.normalizer (J : Set Γ) := fun J hJ hJa =>
    haN ((hN J hJ).symm ▸ Subgroup.mem_inf.mpr ⟨ha, hJa⟩)
  have hsimple : ∀ D ∈ diagSet K a, IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
    rintro _ ⟨J, hJ, rfl⟩
    obtain ⟨e⟩ := exists_mulEquiv_diagOf hp hK haK hap hJ (haJ J hJ)
    obtain ⟨-, -, hJs, hnc⟩ := mem_lcal_iff.mp hJ
    refine ⟨e.isSimpleGroup, ?_⟩
    obtain ⟨x, y, hxy⟩ : ∃ x y : ↥J, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      exact hnc (isMulCommutative_iff.mpr hcon)
    refine ⟨e.symm x, (e.symm x).2, e.symm y, (e.symm y).2, fun hc => hxy ?_⟩
    have := congrArg e (Subtype.ext hc : e.symm x * e.symm y = e.symm y * e.symm x)
    simpa using this
  have hdp := isDirectProduct_diagSet hK haK
  have hlcal : lcal (K ⊓ Subgroup.centralizer {a}) = diagSet K a :=
    lcal_eq_of_isDirectProduct hdp hsimple
  refine ⟨⟨hp, h.elemAbelian, ?_, hlcal ▸ hdp, ?_, ?_⟩, ?_, ?_⟩
  · intro c hc
    exact L514.mem_normalizer_inf (h.normalizes hc) (mem_normalizer_centralizer_of_commute
      (commute_of_mem h.elemAbelian.1 hc ha).eq)
  · rw [hlcal]
    obtain ⟨J, hJ⟩ := h.nonempty
    exact ⟨diagOf K a J, J, hJ, rfl⟩
  · rw [hlcal]
    rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩
    obtain ⟨c, hc, rfl⟩ := h.transitive J₁ hJ₁ J₂ hJ₂
    exact ⟨c, hc, (diagOf_map_conj (h.normalizes hc)
      (commute_of_mem h.elemAbelian.1 hc ha).eq J₁).symm⟩
  · rw [hlcal]
    rintro _ ⟨J, hJ, rfl⟩
    exact ⟨J, hJ, rfl⟩
  · intro hcyc D hD
    rw [hlcal] at hD
    obtain ⟨J, hJ, rfl⟩ := hD
    obtain ⟨n, hnA, hn⟩ := hcyc J hJ
    refine ⟨n, hnA, fun c hc => ?_⟩
    obtain ⟨hcA, hcD⟩ := Subgroup.mem_inf.mp hc
    have hca : c * a = a * c := (commute_of_mem h.elemAbelian.1 hcA ha).eq
    set Z := Subgroup.zpowers a with hZ
    have hZK : Z ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.zpowers_le.mpr haK
    have hZA : Z ≤ A := Subgroup.zpowers_le.mpr ha
    have hJc : J.map (MulAut.conj c).toMonoidHom ∈ lcal K := map_conj_mem_lcal hJ (h.normalizes hcA)
    have hDc : (diagOf K a J).map (MulAut.conj c).toMonoidHom = diagOf K a J :=
      L514.map_conj_eq_of_mem_normalizer hcD
    have hDc' : diagOf K a (J.map (MulAut.conj c).toMonoidHom) = diagOf K a J := by
      rw [← diagOf_map_conj (h.normalizes hcA) hca J]; exact hDc
    have hmem : J.map (MulAut.conj c).toMonoidHom ∈ L514.conjOrbit Z J := by
      by_contra hnot
      have hbot := orbitClosure_inf_eq_bot hK hZK hJ hJc hnot
      apply diagOf_ne_bot hp hK haK hap hJ (haJ J hJ)
      rw [eq_bot_iff, ← hbot]
      refine le_inf (diagOf_le_orbitClosure K a J) ?_
      rw [← hDc']
      exact diagOf_le_orbitClosure K a _
    obtain ⟨g, hg, hgJ⟩ := hmem
    have hgc : g⁻¹ * c ∈ Subgroup.normalizer (J : Set Γ) :=
      Diag.mem_normalizer_of_map_conj_eq hgJ
    have hgcA : g⁻¹ * c ∈ A := mul_mem (inv_mem (hZA hg)) hcA
    have h1 := hn (Subgroup.mem_inf.mpr ⟨hgcA, hgc⟩)
    have hgY : g ∈ Subgroup.centralizer ((K ⊓ Subgroup.centralizer {a} : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyC : y ∈ Subgroup.centralizer (Z : Set Γ) := by
        rw [hZ, centralizer_zpowers_eq]; exact (Subgroup.mem_inf.mp hy).2
      exact (Subgroup.mem_centralizer_iff.mp hyC g hg).symm
    have h2 : g⁻¹ * c ∈ (A ⊓ Subgroup.centralizer
        ((K ⊓ Subgroup.centralizer {a} : Subgroup Γ) : Set Γ)) ⊔ Subgroup.zpowers n :=
      (sup_le_sup_right (inf_le_inf_left _ (Subgroup.centralizer_le fun x hx => hx.1)) _) h1
    have hc' : c = g * (g⁻¹ * c) := by group
    rw [hc']
    exact mul_mem (Subgroup.mem_sup_left ⟨hZA hg, hgY⟩) h2

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
