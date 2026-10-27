module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem424N
public import CFSG.Quasithin.Vol2.Ch4Sec3Lem431

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {L X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(L ⊔ X) * Nat.card ↥(L ⊓ X) = Nat.card ↥L * Nat.card ↥X := by
  have h1 : L.relIndex (X ⊔ L) = L.relIndex X := relIndex_sup_eq_of_le_normalizer' hX
  rw [sup_comm] at h1
  have h2 := Subgroup.relIndex_mul_card L (L ⊔ X)
  have h3 := Subgroup.relIndex_mul_card L X
  rw [inf_eq_left.mpr le_sup_left] at h2
  rw [← h2, ← h3, h1]
  ring

@[expose] def IsCand432 (T M L I : Subgroup G) : Prop :=
  L ≤ I ∧ I ≤ L ⊔ (T ⊓ centralizerSection M L (pCoreOf 2 L)) ∧ ¬ IsUniqueM I M

structure Setting432 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ)
    (I H : Subgroup G) : Prop where
  hyp : Hyp5_0_1 G T M L n
  cand : IsCand432 T M L I
  card_le : ∀ I' : Subgroup G, IsCand432 T M L I' → Nat.card I' ≤ Nat.card I
  inM : InM I H
  ne : H ≠ M
  card_S_le : ∀ I' H' : Subgroup G, IsCand432 T M L I' → Nat.card I' = Nat.card I →
    InM I' H' → H' ≠ M → Nat.card ↥(T ⊓ H') ≤ Nat.card ↥(T ⊓ H)

theorem exists_setting432 {T M L : Subgroup G} {n : ℕ} (h : Hyp5_0_1 G T M L n)
    (hL : ¬ IsUniqueM L M) : ∃ I H : Subgroup G, Setting432 G T M L n I H := by
  classical
  have hcandL : IsCand432 T M L L := ⟨le_rfl, le_sup_left, hL⟩
  obtain ⟨I, hI, hImax⟩ := Set.exists_max_image {I | IsCand432 T M L I} (fun I => Nat.card I)
    (Set.toFinite _) ⟨L, hcandL⟩
  set Pairs : Set (Subgroup G × Subgroup G) := {p | IsCand432 T M L p.1 ∧
    Nat.card p.1 = Nat.card I ∧ InM p.1 p.2 ∧ p.2 ≠ M} with hPairs
  have hne : Pairs.Nonempty := by
    have : ∃ M', InM I M' ∧ M' ≠ M := by
      by_contra hno
      exact hI.2.2 ⟨⟨h.maxTwoLocal, hI.2.1.trans (_root_.sup_le h.L_le
        (inf_le_left.trans h.T_le))⟩, fun M' hM' => by_contra fun h' => hno ⟨M', hM', h'⟩⟩
    obtain ⟨M', hM', hne'⟩ := this
    exact ⟨(I, M'), hI, rfl, hM', hne'⟩
  obtain ⟨⟨I₀, H₀⟩, h₀, hmax₀⟩ := Set.exists_max_image Pairs (fun p => Nat.card ↥(T ⊓ p.2))
    (Set.toFinite _) hne
  refine ⟨I₀, H₀, h, h₀.1, fun I' hI' => h₀.2.1 ▸ hImax I' hI', h₀.2.2.1, h₀.2.2.2,
    fun I' H' hI' hcard hH' hne' => hmax₀ (I', H') ⟨hI', hcard.trans h₀.2.1, hH', hne'⟩⟩

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem hyp421 : Hyp4_2_1 G T M L :=
  ⟨s.hyp.simple, s.hyp.nonabelian, s.hyp.qtke, s.hyp.sylow, s.hyp.maxTwoLocal, s.hyp.T_le,
    s.hyp.maximal, s.hyp.faithful, s.hyp.L_le, s.hyp.isQuasisimple⟩

theorem L_le_I : L ≤ I := s.cand.1

theorem I_le_M : I ≤ M :=
  s.cand.2.1.trans (_root_.sup_le s.hyp.L_le (inf_le_left.trans s.hyp.T_le))

theorem inH : InH I H := inH_of_inM s.inM

theorem not_le_M : ¬ H ≤ M := fun hle => s.ne (s.inM.1.2 M s.hyp.maxTwoLocal.1 hle).symm

theorem isSylowTwoOf_Rp :
    IsSylowTwoOf (T ⊓ centralizerSection M L (pCoreOf 2 L))
      (centralizerSection M L (pCoreOf 2 L)) := by
  have hT : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (L : Set G)) := by
    rw [inf_eq_left.mpr s.hyp.normal]
    exact isSylowTwoOf_of_le s.hyp.sylow s.hyp.T_le
  exact isSylowTwoOf_inf_centralizerSection hT

omit s in
theorem pCoreOf_facts (h : Hyp5_0_1 G T M L n) {J : Subgroup G} (hLJ : L ≤ J) (hJM : J ≤ M) :
    L ⊓ pCoreOf 2 J ≤ pCoreOf 2 L ∧
      pCoreOf 2 J ≤ centralizerSection M L (pCoreOf 2 L) := by
  have h1 : L ⊓ pCoreOf 2 J ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => mem_normalizer_inf (Subgroup.le_normalizer hl)
        (le_normalizer_pCoreOf 2 J (hLJ hl)))
      ((pCoreOf_isPGroup 2 J).to_le inf_le_right)
  refine ⟨h1, (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr
    ⟨(pCoreOf_le 2 J).trans hJM, ?_⟩⟩
  have hc1 : ⁅L, pCoreOf 2 J⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((pCoreOf_le 2 J).trans (hJM.trans h.normal))
  have hc2 : ⁅L, pCoreOf 2 J⁆ ≤ pCoreOf 2 J := Subgroup.le_normalizer_iff_commutator_le_right.mp
    (hLJ.trans (le_normalizer_pCoreOf 2 J))
  exact (le_inf hc1 hc2).trans h1

omit s in
theorem inf_pCoreOf_eq (h : Hyp5_0_1 G T M L n) {J : Subgroup G} (hLJ : L ≤ J) (hJM : J ≤ M) :
    L ⊓ pCoreOf 2 J = pCoreOf 2 L := by
  refine le_antisymm (pCoreOf_facts h hLJ hJM).1 (le_inf (pCoreOf_le 2 L) ?_)
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLJ)
    ((hJM.trans h.normal).trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

theorem pCoreOf_eq :
    pCoreOf 2 I = I ⊓ (T ⊓ centralizerSection M L (pCoreOf 2 L)) := by
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  have hRpL : Rp ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans (s.hyp.T_le.trans s.hyp.normal)
  have hLRp : L ≤ Subgroup.normalizer (Rp : Set G) :=
    le_sup_left.trans (s.hyp421.sup_le_normalizer_Rp s.hyp.normal)
  have hdec : ∀ x ∈ I, ∃ l ∈ L, ∃ r ∈ I ⊓ Rp, l * r = x := by
    intro x hx
    have hx' : x ∈ ((L : Set G) * (Rp : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L Rp hRpL]
      exact s.cand.2.1 hx
    obtain ⟨l, hl, r, hr, rfl⟩ := hx'
    have hrI : r ∈ I := by
      have := I.mul_mem (I.inv_mem (s.L_le_I hl)) hx
      simpa using this
    exact ⟨l, hl, r, ⟨hrI, hr⟩, rfl⟩
  have hge : I ⊓ Rp ≤ pCoreOf 2 I := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => ?_)
      (s.hyp.sylow.1.to_le (inf_le_right.trans inf_le_left))
    obtain ⟨l, hl, r, hr, rfl⟩ := hdec x hx
    refine Subgroup.mul_mem _ ?_ (Subgroup.le_normalizer hr)
    exact mem_normalizer_inf (Subgroup.le_normalizer (s.L_le_I hl)) (hLRp hl)
  refine le_antisymm (le_inf (pCoreOf_le 2 I) (le_inf ?_ (pCoreOf_facts s.hyp s.L_le_I s.I_le_M).2))
    hge
  intro x hx
  obtain ⟨l, hl, r, hr, rfl⟩ := hdec x (pCoreOf_le 2 I hx)
  have hlO : l ∈ pCoreOf 2 I := by
    have := (pCoreOf 2 I).mul_mem hx ((pCoreOf 2 I).inv_mem (hge hr))
    simpa using this
  have hlT : l ∈ T := s.hyp421.pCoreOf_L_le_T s.hyp.normal ((pCoreOf_facts s.hyp s.L_le_I
    s.I_le_M).1 ⟨hl, hlO⟩)
  exact T.mul_mem hlT hr.2.1

theorem sup_pCoreOf : L ⊔ pCoreOf 2 I = I := by
  refine le_antisymm (_root_.sup_le s.L_le_I (pCoreOf_le 2 I)) fun x hx => ?_
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  have hRpL : Rp ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans (s.hyp.T_le.trans s.hyp.normal)
  have hx' : x ∈ ((L : Set G) * (Rp : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L Rp hRpL]
    exact s.cand.2.1 hx
  obtain ⟨l, hl, r, hr, rfl⟩ := hx'
  have hrI : r ∈ I := by
    have := I.mul_mem (I.inv_mem (s.L_le_I hl)) hx
    simpa using this
  have hrR : r ∈ pCoreOf 2 I := by
    rw [s.pCoreOf_eq]
    exact ⟨hrI, hr⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hrR)

theorem pCoreOf_ne_bot : pCoreOf 2 I ≠ ⊥ := by
  intro h0
  apply hyp501_pCoreOf_ne_bot s.hyp
  rw [← inf_pCoreOf_eq s.hyp s.L_le_I s.I_le_M, h0, inf_bot_eq]

theorem isSigma : IsSigma M L (L ⊔ centralizerSection M L (pCoreOf 2 L)) :=
  ⟨_root_.sup_le s.hyp.L_le (centralizerSection_le_left _ _ _), le_rfl⟩

theorem isIota : IsIota M L (L ⊔ centralizerSection M L (pCoreOf 2 L)) I := by
  have hIC : I ≤ L ⊔ centralizerSection M L (pCoreOf 2 L) :=
    s.cand.2.1.trans (sup_le_sup_left inf_le_right L)
  exact ⟨hIC, le_antisymm (_root_.sup_le hIC le_sup_right) (sup_le_sup_right s.L_le_I _),
    s.L_le_I.trans le_sup_left, s.pCoreOf_ne_bot⟩

theorem isGammaStar : IsGammaStar M L (L ⊔ centralizerSection M L (pCoreOf 2 L)) I := by
  set C := centralizerSection M L (pCoreOf 2 L) with hC
  set Rp := T ⊓ C with hRp
  refine ⟨⟨s.isIota, H, s.inH, s.not_le_M⟩, fun I₁ hI₁ hle hlt => ?_⟩
  have hLI₁ : L ≤ I₁ := by
    have := hle.2
    rw [inf_eq_right.mpr s.L_le_I] at this
    exact this.trans inf_le_left
  have hI₁M : I₁ ≤ M := hI₁.1.1.trans s.isSigma.1
  set R' := pCoreOf 2 I₁ with hR'
  have hR'C : R' ≤ C := (pCoreOf_facts s.hyp hLI₁ hI₁M).2
  obtain ⟨P, hP, hR'P⟩ := exists_isSylowTwoOf_ge hR'C (pCoreOf_isPGroup 2 I₁)
  obtain ⟨c, hc, hcP⟩ := exists_conj_of_isSylowTwoOf s.isSylowTwoOf_Rp hP
  have hcM : c ∈ M := centralizerSection_le_left _ _ _ hc
  have hR'c : R'.map (MulAut.conj c⁻¹).toMonoidHom ≤ Rp := by
    intro x hx
    rw [mem_map_conj_iff, inv_inv] at hx
    have := (hcP _).mp (hR'P hx)
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rwa [e] at this
  have hLc : L.map (MulAut.conj c⁻¹).toMonoidHom = L :=
    map_conj_eq_of_mem_normalizer (s.hyp.normal (M.inv_mem hcM))
  set I' := L ⊔ R'.map (MulAut.conj c⁻¹).toMonoidHom with hI'
  have hI'eq : I' = (L ⊔ R').map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Subgroup.map_sup, hLc]
  have hcand : IsCand432 T M L I' := by
    refine ⟨le_sup_left, sup_le_sup_left hR'c L, fun hU => ?_⟩
    have hU' := isUniqueM_map_conj hU hcM
    rw [hI'eq, map_conj_map_conj_inv] at hU'
    obtain ⟨H₁, hH₁, hH₁M⟩ := hI₁.2
    exact hH₁M (isUniqueM_le_of_inH
      (isUniqueM_mono hU' (_root_.sup_le hLI₁ (pCoreOf_le 2 I₁)) hI₁M) hH₁)
  have hcard' : Nat.card I' = Nat.card ↥(L ⊔ R') := by
    rw [hI'eq]
    exact Nat.card_congr ((L ⊔ R').equivMapOfInjective _ (MulAut.conj c⁻¹).injective).toEquiv.symm
  have hR'L : R' ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le 2 I₁).trans (hI₁M.trans s.hyp.normal)
  have hRL : pCoreOf 2 I ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le 2 I).trans (s.I_le_M.trans s.hyp.normal)
  have e1 := card_sup_mul_card_inf_of_le_normalizer hR'L
  have e2 := card_sup_mul_card_inf_of_le_normalizer hRL
  rw [inf_pCoreOf_eq s.hyp hLI₁ hI₁M] at e1
  rw [inf_pCoreOf_eq s.hyp s.L_le_I s.I_le_M, s.sup_pCoreOf] at e2
  have hlt' : Nat.card ↥(pCoreOf 2 I) < Nat.card R' := Subgroup.card_lt_of_lt hlt
  have hgt : Nat.card I < Nat.card ↥(L ⊔ R') := by
    have hpos : 0 < Nat.card ↥(pCoreOf 2 L) := Nat.card_pos
    have hLpos : 0 < Nat.card ↥L := Nat.card_pos
    refine Nat.lt_of_mul_lt_mul_right (a := Nat.card ↥(pCoreOf 2 L)) ?_
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_left hlt' hLpos
  have := s.card_le I' hcand
  rw [hcard'] at this
  exact absurd this (not_le.mpr hgt)

theorem hyp4_2_3N : Hyp4_2_3N G T M L (L ⊔ centralizerSection M L (pCoreOf 2 L)) I :=
  { s.hyp421 with
    normal := s.hyp.normal
    sigma := s.isSigma
    gammaStar := s.isGammaStar
    R_le := s.pCoreOf_eq.le.trans inf_le_right
    L_le_I := s.L_le_I }

end Setting432

theorem card_eq_of_isSylowTwoOf {A B K : Subgroup G} (hA : IsSylowTwoOf A K)
    (hB : IsSylowTwoOf B K) : Nat.card A = Nat.card B := by
  obtain ⟨c, -, hc⟩ := exists_conj_of_isSylowTwoOf hA hB
  have hBA : B = A.map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [mem_map_conj_iff]
    exact hc x
  rw [hBA]
  exact Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj c).injective).toEquiv

theorem isSylowTwoOf_of_card_le {X P K : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup 2 X)
    (hP : IsSylowTwoOf P K) (hcard : Nat.card P ≤ Nat.card X) : IsSylowTwoOf X K := by
  obtain ⟨Q, hQ, hXQ⟩ := exists_isSylowTwoOf_ge hXK hX
  have hQX : Nat.card Q ≤ Nat.card X := (card_eq_of_isSylowTwoOf hQ hP).le.trans hcard
  rw [Subgroup.eq_of_le_of_card_ge hXQ hQX]
  exact hQ

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem pCoreOf_le_S : pCoreOf 2 I ≤ T ⊓ H :=
  le_inf (s.pCoreOf_eq.le.trans (inf_le_right.trans inf_le_left))
    ((pCoreOf_le 2 I).trans s.inM.2)

theorem isSylowTwoOf_S (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    IsSylowTwoOf (T ⊓ H) (H ⊓ M) := by
  have h3 := s.hyp4_2_3N
  have h41 := h3.hyp4_1_1 h37 h38 h39
  set R := pCoreOf 2 I with hR
  set CH := centralizerSection (H ⊓ M) L (pCoreOf 2 L) with hCH
  have hsyl : IsSylowTwoOf R CH := by
    have := (lemma_4_1_4_four h41 s.isSigma s.isGammaStar s.inH s.not_le_M).2
    rwa [h3.oTwoUpper_inf_eq h37 h38 h39 s.inM.2] at this
  have hRHM : R ≤ H ⊓ M := hsyl.1.trans (centralizerSection_le_left _ _ _)
  obtain ⟨P, hP, hRP⟩ := exists_isSylowTwoOf_ge hRHM (pCoreOf_isPGroup 2 I)
  have hCHn : H ⊓ M ≤ Subgroup.normalizer (CH : Set G) :=
    le_normalizer_centralizerSection' (inf_le_right.trans s.hyp.normal)
  have hPCH : P ⊓ CH = R := by
    refine le_antisymm ?_ (le_inf hRP hsyl.1)
    exact (isSylowTwoOf_iff_maximal.mp hsyl).2.2 _ inf_le_right (hP.2.1.to_le inf_le_left)
      (le_inf hRP hsyl.1)
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [← hPCH]
    exact mem_normalizer_inf (Subgroup.le_normalizer hx) (hCHn (hP.1 hx))
  have hPM : P ≤ M := hP.1.trans inf_le_right
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowTwoOf_ge hPM hP.2.1
  obtain ⟨c, hc, hcQ⟩ := exists_conj_of_isSylowTwoOf (isSylowTwoOf_of_le s.hyp.sylow s.hyp.T_le) hQ
  set φ := (MulAut.conj c⁻¹).toMonoidHom with hφ
  have hPT : P.map φ ≤ T := by
    intro x hx
    rw [hφ, mem_map_conj_iff, inv_inv] at hx
    have := (hcQ _).mp (hPQ hx)
    simpa [mul_assoc] using this
  have hcM : c⁻¹ ∈ M := M.inv_mem hc
  have hLc : L.map φ = L := map_conj_eq_of_mem_normalizer (s.hyp.normal hcM)
  have hCc : (centralizerSection M L (pCoreOf 2 L)).map φ ≤ centralizerSection M L (pCoreOf 2 L) :=
    map_conj_le_of_mem_normalizer (le_normalizer_centralizerSection' s.hyp.normal hcM)
  have hIc : I.map φ = L ⊔ R.map φ := by
    rw [← s.sup_pCoreOf, Subgroup.map_sup, hLc]
  have hcand : IsCand432 T M L (I.map φ) := by
    refine ⟨hIc ▸ le_sup_left, ?_, fun hU => s.cand.2.2 ?_⟩
    · rw [hIc]
      refine sup_le_sup_left (le_inf ((map_conj_mono hRP c⁻¹).trans hPT) ?_) L
      exact (map_conj_mono (pCoreOf_facts s.hyp s.L_le_I s.I_le_M).2 c⁻¹).trans hCc
    · have := isUniqueM_map_conj hU (M.inv_mem hcM)
      rwa [hφ, map_conj_inv_map_conj] at this
  have hcardI : Nat.card ↥(I.map φ) = Nat.card I :=
    Nat.card_congr (I.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).toEquiv.symm
  have hInM : InM (I.map φ) (H.map φ) :=
    ⟨isMaxTwoLocal_map_conj s.inM.1 c⁻¹, map_conj_mono s.inM.2 c⁻¹⟩
  have hneH : H.map φ ≠ M := by
    intro he
    apply s.ne
    have := congrArg (fun K : Subgroup G => K.map (MulAut.conj c).toMonoidHom) he
    simp only [hφ] at this
    rw [map_conj_map_conj_inv, map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer hc)] at this
    exact this
  have hle := s.card_S_le _ _ hcand hcardI hInM hneH
  have hPle : Nat.card P ≤ Nat.card ↥(T ⊓ H.map φ) := by
    have h1 : Nat.card P = Nat.card ↥(P.map φ) :=
      Nat.card_congr (P.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).toEquiv
    rw [h1]
    exact Subgroup.card_le_of_le (le_inf hPT (map_conj_mono (hP.1.trans inf_le_left) c⁻¹))
  exact isSylowTwoOf_of_card_le (le_inf inf_le_right (inf_le_left.trans s.hyp.T_le))
    (s.hyp.sylow.1.to_le inf_le_left) hP (hPle.trans hle)

theorem lemma_4_3_3_a {X : Subgroup G} (hSX : T ⊓ H < X) (hXT : X ≤ T) :
    IsUniqueM (L ⊔ X) M := by
  by_contra hU
  have hLXM : L ⊔ X ≤ M := _root_.sup_le s.hyp.L_le (hXT.trans s.hyp.T_le)
  have : ∃ M', InM (L ⊔ X) M' ∧ M' ≠ M := by
    by_contra hno
    exact hU ⟨⟨s.hyp.maxTwoLocal, hLXM⟩, fun M' hM' => by_contra fun h' => hno ⟨M', hM', h'⟩⟩
  obtain ⟨M', hM', hne⟩ := this
  have hIX : I ≤ L ⊔ X := by
    rw [← s.sup_pCoreOf]
    exact sup_le_sup_left (s.pCoreOf_le_S.trans hSX.le) L
  have hle := s.card_S_le I M' s.cand rfl ⟨hM'.1, hIX.trans hM'.2⟩ hne
  have hlt : Nat.card ↥(T ⊓ H) < Nat.card ↥(T ⊓ M') :=
    lt_of_lt_of_le (Subgroup.card_lt_of_lt hSX)
      (Subgroup.card_le_of_le (le_inf hXT (le_sup_right.trans hM'.2)))
  exact absurd hle (not_le.mpr hlt)

theorem lemma_4_3_4 :
    pCoreOf 2 I = T ⊓ H ⊓ (T ⊓ centralizerSection M L (pCoreOf 2 L)) := by
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  set I' := L ⊔ (T ⊓ H ⊓ Rp) with hI'
  have hRS : pCoreOf 2 I ≤ T ⊓ H ⊓ Rp :=
    le_inf s.pCoreOf_le_S (s.pCoreOf_eq.le.trans inf_le_right)
  have hII' : I ≤ I' := by
    rw [← s.sup_pCoreOf]
    exact sup_le_sup_left hRS L
  have hcand : IsCand432 T M L I' := by
    refine ⟨le_sup_left, sup_le_sup_left inf_le_right L, fun hU => s.ne ?_⟩
    exact hU.2 H ⟨s.inM.1, _root_.sup_le (s.L_le_I.trans s.inM.2) (inf_le_left.trans inf_le_right)⟩
  have heq : I = I' := Subgroup.eq_of_le_of_card_ge hII' (s.card_le I' hcand)
  refine le_antisymm hRS ?_
  rw [s.pCoreOf_eq]
  exact le_inf (heq ▸ le_sup_right) inf_le_right

end Setting432

end CFSG.Quasithin.H13.Ch4
