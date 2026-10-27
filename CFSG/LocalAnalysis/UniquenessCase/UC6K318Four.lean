module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Step
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318M11L34
public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjRepL2
public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjTits
public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjA10
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87EngCC
public import CFSG.RankThree.OddKernel.SectionRep

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K318

open Subgroup CFSG.RepresentationTheory
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open scoped Matrix commutatorElement

@[expose] def List620' (r : ℕ) (X : Type) [Group X] : Prop :=
  (r ≠ 3 ∧ LieModel X .PSL 2 r 2) ∨ (r = 3 ∧ (IsSpor X .M11 ∨ LieModel X .PSL 3 2 2)) ∨
    (r = 5 ∧ (LieModel X .Tits 0 2 1 ∨ IsAlt X 10))

variable {q n : ℕ} [Fact q.Prime]

@[expose] noncomputable def matRep (Q : Subgroup (GL (Fin n) (ZMod q))) :
    Representation (ZMod q) Q (Fin n → ZMod q) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (ZMod q) ≃ₐ[ZMod q] _).toMonoidHom.comp
    ((Units.coeHom _).comp Q.subtype)

theorem eq_bot_of_isPGroup {P Q : Subgroup (GL (Fin n) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep P.subtype) (hQ : IsPGroup q Q)
    (hnorm : ∀ g ∈ P, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : Q = ⊥ := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [eq_bot_iff]
    intro x _
    rw [mem_bot]
    exact Units.ext (Matrix.ext fun i => Fin.elim0 i)
  let W : Submodule (ZMod q) (Fin n → ZMod q) :=
    { carrier := {v | ∀ x ∈ Q, (x : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ v = v}
      add_mem' := fun ha hb x hx => by rw [Matrix.mulVec_add, ha x hx, hb x hx]
      zero_mem' := fun x _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv x hx => by rw [Matrix.mulVec_smul, hv x hx] }
  have hWinv : ∀ g : P, ∀ w ∈ W, (P.subtype g : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ w ∈ W := by
    intro g w hw x hx
    have hx' : ((g : GL (Fin n) (ZMod q))⁻¹ * x * (g : GL (Fin n) (ZMod q))) ∈ Q := by
      have := hnorm _ (inv_mem g.2) x hx
      rwa [inv_inv] at this
    have h1 := hw _ hx'
    have e : (x : Matrix (Fin n) (Fin n) (ZMod q)) * (g : GL (Fin n) (ZMod q)) =
        (g : GL (Fin n) (ZMod q)) * (((g : GL (Fin n) (ZMod q))⁻¹ * x *
          (g : GL (Fin n) (ZMod q)) : GL (Fin n) (ZMod q)) : Matrix (Fin n) (Fin n) (ZMod q)) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    show (x : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ
      ((g : GL (Fin n) (ZMod q)) : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ w = _
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, h1]
    rfl
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial (Fin n → ZMod q) := Function.nontrivial
  have hQfin : Finite Q := inferInstance
  obtain ⟨v, hv0, hv⟩ := CFSG.RankThree.OddKernel.exists_ne_zero_fixed hQ (matRep Q)
  rcases hirr W hWinv with hW | hW
  · exfalso
    apply hv0
    have hvW : v ∈ W := fun x hx => hv ⟨x, hx⟩
    rw [hW] at hvW
    exact (Submodule.mem_bot _).1 hvW
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    have hw : w ∈ W := hW ▸ Submodule.mem_top
    rw [Matrix.toLin'_apply, hw x hx, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]

theorem fixed_eq_zero_of_central {P : Subgroup (GL (Fin n) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep P.subtype) {c : GL (Fin n) (ZMod q)}
    (hc : ∀ g ∈ P, g * c = c * g) (hc1 : c ≠ 1) :
    ∀ v, (c : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ v = v → v = 0 := by
  let W : Submodule (ZMod q) (Fin n → ZMod q) :=
    { carrier := {v | (c : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ v = v}
      add_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [Matrix.mulVec_add, ha, hb]
      zero_mem' := Matrix.mulVec_zero _
      smul_mem' := fun a v hv => by
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [Matrix.mulVec_smul, hv] }
  have hWinv : ∀ g : P, ∀ w ∈ W, (P.subtype g : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ w ∈ W := by
    intro g w hw
    show (c : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ
      ((g : GL (Fin n) (ZMod q)) : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ w = _
    have hw' : (c : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ w = w := hw
    have e := congrArg Units.val (hc g g.2)
    rw [Units.val_mul, Units.val_mul] at e
    rw [Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec, hw']
    rfl
  intro v hv
  rcases hirr W hWinv with hW | hW
  · have hvW : v ∈ W := hv
    rw [hW] at hvW
    exact (Submodule.mem_bot _).1 hvW
  · exfalso
    apply hc1
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    have hw : w ∈ W := hW ▸ Submodule.mem_top
    have hw' : (c : Matrix (Fin n) (Fin n) (ZMod q)) *ᵥ w = w := hw
    rw [Matrix.toLin'_apply, hw', Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]

theorem exists_central_commutator {T : Type*} [Group T] [Finite T] {s : ℕ} [Fact s.Prime]
    (hT : IsPGroup s T) (hnc : ¬ ∀ a b : T, a * b = b * a) :
    ∃ x y : T, ⁅y, x⁆ ∈ center T ∧ ⁅y, x⁆ ≠ 1 := by
  have hZ : center T ≠ ⊤ := by
    intro h
    apply hnc
    intro a b
    have hb : b ∈ center T := h ▸ mem_top b
    exact (mem_center_iff.1 hb a)
  have : Nontrivial (T ⧸ center T) := by
    obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hZ)
    exact ⟨⟨(g : T ⧸ center T), 1, fun h1 => hg ((QuotientGroup.eq_one_iff g).1 h1)⟩⟩
  have hQ : IsPGroup s (T ⧸ center T) := hT.to_quotient (center T)
  have := hQ.center_nontrivial
  obtain ⟨⟨xb, hxb⟩, hxb1⟩ := exists_ne (1 : center (T ⧸ center T))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hxZ : x ∉ center T := by
    intro h
    apply hxb1
    exact Subtype.ext ((QuotientGroup.eq_one_iff x).2 h)
  rw [mem_center_iff] at hxZ
  push Not at hxZ
  obtain ⟨y, hy⟩ := hxZ
  refine ⟨x, y, ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      mem_center_iff.1 hxb (y : T ⧸ center T)]
    group
  · intro h
    apply hy
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact h

theorem le_center_of_pCores {P : Type*} [Group P] [Finite P] {R : Subgroup P}
    (hRs : Group.IsSolvable R)
    (h : ∀ s ∈ (Nat.card R).primeFactors, (CFSG.pCore s R).map R.subtype ≤ center P) :
    R ≤ center P := by
  have hF : (⊤ : Subgroup P) ≤
      centralizer (((CFSG.fittingSubgroup R).map R.subtype : Subgroup P) : Set P) := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ (fun s g _ => ?_)
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_center_iff.1 (h s.1.1 s.1.2 hz) g).symm
  intro y hy
  have hyF : (⟨y, hy⟩ : R) ∈ CFSG.fittingSubgroup R := by
    apply CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hRs
    rw [mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact mem_centralizer_iff.1 (hF (mem_top y)) (f : P) (mem_map_of_mem _ hf)
  rw [mem_center_iff]
  intro g
  exact (mem_centralizer_iff.1 (hF (mem_top g)) y (mem_map.2 ⟨⟨y, hy⟩, hyF, rfl⟩)).symm

theorem le_center_of_irreducible (hn : n ≤ 4) (hn2 : ∀ s : ℕ, s.Prime → s ∣ n → s = 2)
    {P : Subgroup (GL (Fin n) (ZMod q))} [Group.IsPerfect P]
    (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hRodd : Odd (Nat.card R)) : R ≤ center P := by
  classical
  have hq : q.Prime := Fact.out
  apply le_center_of_pCores hRs
  intro s hsR
  have hs : s.Prime := Nat.prime_of_mem_primeFactors hsR
  haveI : Fact s.Prime := ⟨hs⟩
  have hs2 : s ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hRodd) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hsR))
  let S : Subgroup P := (CFSG.pCore s R).map R.subtype
  have hSn : S.Normal := ConjAct.normal_of_characteristic_of_normal
  let T : Subgroup (GL (Fin n) (ZMod q)) := S.map P.subtype
  have hT : IsPGroup s T := ((CFSG.pCore_isPGroup (p := s) (G := R)).map R.subtype).map P.subtype
  have hTP : ∀ g ∈ P, ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hx
    have h1 : (⟨g, hg⟩ : P) * a * (⟨g, hg⟩ : P)⁻¹ ∈ S := hSn.conj_mem a ha _
    refine mem_map.2 ⟨_, h1, ?_⟩
    simp
  suffices hcent : ∀ g ∈ P, ∀ z ∈ T, g * z = z * g by
    intro a ha
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcent g g.2 a (mem_map_of_mem _ ha)
  by_cases hsq : s = q
  · subst hsq
    have hbot := eq_bot_of_isPGroup hirr hT hTP
    intro g _ z hz
    rw [hbot, mem_bot] at hz
    rw [hz, mul_one, one_mul]
  have hcop : ∀ U : Subgroup (GL (Fin n) (ZMod q)), U ≤ T →
      Nat.Coprime (Nat.card U) (ringChar (ZMod q)) := by
    intro U hU
    obtain ⟨k, hk⟩ := (hT.to_le hU).exists_card_eq
    rw [ZMod.ringChar_zmod_n, hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hs hq).2 hsq)
  have hcard : Fintype.card (Fin n) ≤ 4 := by rw [Fintype.card_fin]; exact hn
  by_cases hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x
  · exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.perfect_centralizes_coprime_abelian hcard T P
      hab (hcop T le_rfl) inferInstance hTP
  exfalso
  have hTnc : ¬ ∀ a b : T, a * b = b * a := fun h => hab (fun x hx y hy =>
    congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨x, y, hcZ, hc1⟩ := exists_central_commutator hT hTnc
  set Z : Subgroup (GL (Fin n) (ZMod q)) := (center T).map T.subtype with hZdef
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.1 hb a)
  have hZP : ∀ g ∈ P, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    rintro g hg _ ⟨a, ha, rfl⟩
    refine ⟨⟨g * a * g⁻¹, hTP g hg a a.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro b
    apply Subtype.ext
    have hb : g⁻¹ * b * g⁻¹⁻¹ ∈ T := hTP g⁻¹ (inv_mem hg) b b.2
    have h1 := congrArg Subtype.val (mem_center_iff.1 ha ⟨_, hb⟩)
    simp only [Subgroup.coe_mul, inv_inv] at h1
    show (b : GL (Fin n) (ZMod q)) * (g * a * g⁻¹) = g * a * g⁻¹ * b
    calc (b : GL (Fin n) (ZMod q)) * (g * a * g⁻¹)
        = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * b := by group
  have hZcent := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.perfect_centralizes_coprime_abelian hcard
    Z P hZab (hcop Z (map_subtype_le _)) inferInstance hZP
  set c : GL (Fin n) (ZMod q) := ((⁅y, x⁆ : T) : GL (Fin n) (ZMod q)) with hcdef
  have hcZ' : c ∈ Z := mem_map_of_mem _ hcZ
  have hcP : ∀ g ∈ P, g * c = c * g := fun g hg => hZcent g hg c hcZ'
  have hcne : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hfix := fixed_eq_zero_of_central hirr hcP hcne
  obtain ⟨j, hj⟩ := hT ⁅y, x⁆
  have hcj : c ^ (s ^ j) = 1 := by
    rw [hcdef, ← Subgroup.coe_pow, hj, Subgroup.coe_one]
  have hxy : (y : GL (Fin n) (ZMod q)) * x * (y : GL (Fin n) (ZMod q))⁻¹ = c * x := by
    rw [hcdef, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcx : c * x = x * c := (congrArg Subtype.val (mem_center_iff.1 hcZ x)).symm
  have hcy : c * y = y * c := (congrArg Subtype.val (mem_center_iff.1 hcZ y)).symm
  have hdvd := dvd_of_conj_eq_central_mul hxy hcx hcy hcj hfix
  exact hs2 (hn2 s hs hdvd)

theorem kProjRep620_holds : UCK.KProjRep620 :=
  UCK.kProjRep620_of_clauses UCK.kProjRepL2_holds
    (fun J _ _ hq N _ hN h q hq' hq5 d hd f => UCK.kProjRep_Tits J hq N hN h q hq' hq5 d hd f)
    (fun J _ _ hq N _ hN h q hq' hq5 d hd f => UCK.kProjRep_A10 J hq N hN h q hq' hq5 d hd f)

theorem false_of_dim_four (hq2 : q ≠ 2) {P : Subgroup (GL (Fin 4) (ZMod q))} [Group.IsPerfect P]
    (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hRodd : Odd (Nat.card R)) (hs : IsSimpleGroup (P ⧸ R))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hqr : q ≠ r) {X : Type} [Group X]
    (hX : List620' r X) (e : P ⧸ R ≃* X) : False := by
  have hq : q.Prime := Fact.out
  have hRZ : R ≤ center P := by
    refine le_center_of_irreducible le_rfl (fun s hs hs4 => ?_) hirr R hRs hRodd
    exact (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1
      (hs.dvd_of_dvd_pow (show s ∣ 2 ^ 2 by norm_num; exact hs4))
  have hZR : center P ≤ R := by
    rcases le_or_eq_top_of_normal hRs hs (center P) with h | h
    · exact h
    · exfalso
      exact not_comm_of_simple hs fun a b => (mem_center_iff.1 (h ▸ mem_top b) a)
  have hR : R = center P := le_antisymm hRZ hZR
  have hqs : CFSG.Open.IsQuasisimple P :=
    ⟨Group.IsPerfect.commutator_eq_top,
      (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientMulEquivOfEq hR)).1 hs⟩
  have e' : P ⧸ center P ≃* X := (QuotientGroup.quotientMulEquivOfEq hR.symm).trans e
  set f : P →* GL (Fin 4) (ZMod q) ⧸ center (GL (Fin 4) (ZMod q)) :=
    (QuotientGroup.mk' (center (GL (Fin 4) (ZMod q)))).comp P.subtype with hf
  have hcentral : f = 1 → False := by
    intro h1
    apply not_comm_of_simple hs
    intro a b
    have hb : (b : GL (Fin 4) (ZMod q)) ∈ center (GL (Fin 4) (ZMod q)) := by
      rw [← QuotientGroup.eq_one_iff]
      exact DFunLike.congr_fun h1 b
    exact Subtype.ext (mem_center_iff.1 hb a)
  have hr5 : r ≠ 3 → 5 ≤ r := by
    intro h3
    have := hr.two_le
    have h4 : r ≠ 4 := by
      rintro rfl
      norm_num at hr
    omega
  rcases hX with ⟨hr3, hL⟩ | ⟨rfl, hX3⟩ | ⟨rfl, hX5⟩
  · exact hcentral (kProjRep620_holds P hqs R hRZ r hr (hr5 hr3)
      (Or.inl (hL.of_mulEquiv e.symm)) q hq hqr 4 (by norm_num) f)
  · refine UCK.false_of_irreducible_gl4_m11_l34 hq2 hqr hqs hirr ?_
    rcases hX3 with h | hL
    · obtain ⟨e₁⟩ := h
      exact Or.inl ⟨e'.trans e₁⟩
    · exact Or.inr (hL.of_mulEquiv e'.symm)
  · refine hcentral (kProjRep620_holds P hqs R hRZ 5 hr le_rfl (Or.inr ⟨rfl, ?_⟩) q hq hqr 4
      (by norm_num) f)
    rcases hX5 with hT | h
    · exact Or.inl (hT.of_mulEquiv e.symm)
    · obtain ⟨e₁⟩ := h
      exact Or.inr ⟨e.trans e₁⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6.K318
