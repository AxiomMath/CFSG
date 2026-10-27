module

public import CFSG.Quasithin.Background.B5IrrA
public import CFSG.Quasithin.Background.A1cModuleBridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section NatModule

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def trvSL (i j : Fin n) (hij : i ≠ j) (c : K) : ↥(StatedSL n K) :=
  ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact isUnit_one),
    Subgroup.subset_closure (by simpa using Matrix.det_transvection_of_ne i j hij c)⟩

theorem trvSL_mulVec (i j : Fin n) (hij : i ≠ j) (c : K) (v : Fin n → K) :
    (((trvSL i j hij c : ↥(StatedSL n K)) : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).mulVec v = v + Pi.single i (c * v j) := by
  have : (((trvSL i j hij c : ↥(StatedSL n K)) : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Matrix.transvection i j c := rfl
  rw [this, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
  by_cases hk : i = k
  · subst hk; simp
  · simp [hk, Ne.symm hk]

theorem natAct_trvSL (i j : Fin n) (hij : i ≠ j) (c : K) (x : Multiplicative (Fin n → K)) :
    natAct (StatedSL n K) (trvSL i j hij c) x =
      Multiplicative.ofAdd (Multiplicative.toAdd x + Pi.single i (c * Multiplicative.toAdd x j)) := by
  unfold natAct
  rw [trvSL_mulVec]

theorem natural_invariant_eq (hn : 2 ≤ n) (J : Subgroup (Multiplicative (Fin n → K)))
    (hJ : ∀ (γ : ↥(StatedSL n K)) (x : Multiplicative (Fin n → K)), x ∈ J →
      natAct (StatedSL n K) γ x ∈ J) : J = ⊥ ∨ J = ⊤ := by
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨v, hvJ⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hv0 : Multiplicative.toAdd v ≠ 0 := fun h => hv1' (by simpa using congrArg Multiplicative.ofAdd h)
  obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext hcon)
  have hs1 : ∀ i, i ≠ j → ∀ a : K, Multiplicative.ofAdd (Pi.single i a : Fin n → K) ∈ J := by
    intro i hij a
    have h1 := J.mul_mem (hJ (trvSL i j hij (a / Multiplicative.toAdd v j)) v hvJ) (J.inv_mem hvJ)
    have e : natAct (StatedSL n K) (trvSL i j hij (a / Multiplicative.toAdd v j)) v * v⁻¹ =
        Multiplicative.ofAdd (Pi.single i a : Fin n → K) := by
      rw [natAct_trvSL]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv]
      rw [div_mul_cancel₀ _ hj]
      abel
    rwa [e] at h1
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, i₀ ≠ j := by
    by_cases hj0 : j = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [hj0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h => hj0 h.symm⟩
  have hs2 : ∀ c : K, Multiplicative.ofAdd (Pi.single j c : Fin n → K) ∈ J := by
    intro c
    have hx0 := hs1 i₀ hi₀ 1
    have h1 := J.mul_mem (hJ (trvSL j i₀ hi₀.symm c) _ hx0) (J.inv_mem hx0)
    have e : natAct (StatedSL n K) (trvSL j i₀ hi₀.symm c)
        (Multiplicative.ofAdd (Pi.single i₀ 1 : Fin n → K)) *
          (Multiplicative.ofAdd (Pi.single i₀ 1 : Fin n → K))⁻¹ =
        Multiplicative.ofAdd (Pi.single j c : Fin n → K) := by
      rw [natAct_trvSL]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv]
      simp
    rwa [e] at h1
  have hs3 : ∀ (i : Fin n) (a : K), Multiplicative.ofAdd (Pi.single i a : Fin n → K) ∈ J := by
    intro i a
    by_cases hij : i = j
    · subst hij; exact hs2 a
    · exact hs1 i hij a
  rw [eq_top_iff]
  intro y _
  have : y = ∏ i : Fin n, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd y i) : Fin n → K) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    exact (Finset.univ_sum_single (Multiplicative.toAdd y)).symm
  rw [this]
  exact J.prod_mem fun i _ => hs3 i _

end NatModule

section LinModel

@[expose] noncomputable def natQuotEquiv (M : Type) [CommGroup M] :
    (↥(⊤ : Subgroup M) ⧸ ((⊥ : Subgroup M).subgroupOf ⊤)) ≃* M :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (⊤ : Subgroup M))).trans
    ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)

theorem natQuotEquiv_mk (M : Type) [CommGroup M] (m : M) :
    natQuotEquiv M (QuotientGroup.mk ⟨m, trivial⟩) = m := rfl

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)}
  {L : Subgroup (MulAut V)} {I : Subgroup V} {π : ↥Γ →* ↥L}

theorem exists_linModel (hD : (FFModel.nat Γ).RealizesVia L I ⊥ π) :
    ∃ e : ↥I ≃* Multiplicative (Fin n → K), ∀ (γ : ↥Γ) (u : ↥I)
      (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ I),
      e ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ = natAct Γ γ (e u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hD
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  let e : ↥I ≃* Multiplicative (Fin n → K) :=
    (MulEquiv.ofBijective β ⟨hinj, hβs⟩).trans (natQuotEquiv (Multiplicative (Fin n → K)))
  refine ⟨e, fun γ u hu => ?_⟩
  have h1 : β u = QuotientGroup.mk ⟨e u, trivial⟩ := by
    apply (natQuotEquiv (Multiplicative (Fin n → K))).injective
    exact (rfl : natQuotEquiv (Multiplicative (Fin n → K)) (β u) = e u)
  have h2 := hβe γ u ⟨e u, trivial⟩ hu trivial h1
  have h3 := congrArg (natQuotEquiv (Multiplicative (Fin n → K))) h2
  exact h3

end LinModel
section SecIso

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

theorem secIsoL_iff {I Z I' Z' : Subgroup V} : SecIsoL L I Z I' Z' ↔
    Z ≤ I ∧ Z' ≤ I' ∧ (∀ h : ↥L, ∀ u ∈ I, (h : MulAut V) u ∈ I) ∧
      (∀ h : ↥L, ∀ z ∈ Z, (h : MulAut V) z ∈ Z) ∧ (∀ γ : ↥L, ∀ m ∈ I', (γ : MulAut V) m ∈ I') ∧
      (∀ γ : ↥L, ∀ m ∈ Z', (γ : MulAut V) m ∈ Z') ∧
      ∃ β : ↥I →* ↥I' ⧸ Z'.subgroupOf I', Function.Surjective β ∧ (∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z) ∧
        ∀ (γ : ↥L) (u : ↥I) (m : ↥I') (hu : (γ : MulAut V) (u : V) ∈ I)
          (hm : (γ : MulAut V) (m : V) ∈ I'),
          β u = QuotientGroup.mk m →
            β ⟨(γ : MulAut V) (u : V), hu⟩ = QuotientGroup.mk ⟨(γ : MulAut V) (m : V), hm⟩ := by
  constructor
  · rintro ⟨-, h1, h2, h3, h4, h5, h6, β, hs, hk, he⟩
    exact ⟨h1, h2, h3, h4, h5, h6, β, hs, hk, he⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, β, hs, hk, he⟩
    exact ⟨Function.surjective_id, h1, h2, h3, h4, h5, h6, β, hs, hk, he⟩

theorem secIsoL_of_iso {J J' : Subgroup V} (hJ : XMod.IsInv ↥L J) (hJ' : XMod.IsInv ↥L J')
    (h : XMod.Iso ↥L J J') : SecIsoL L J ⊥ J' ⊥ := by
  obtain ⟨φ, hφ⟩ := h
  rw [secIsoL_iff]
  refine ⟨bot_le, bot_le, fun g u hu => hJ g u hu, fun g z hz => ?_, fun γ m hm => hJ' γ m hm,
    fun γ m hm => ?_, ?_⟩
  · have : z = 1 := Subgroup.mem_bot.1 hz
    rw [this, map_one]; exact Subgroup.one_mem _
  · have : m = 1 := Subgroup.mem_bot.1 hm
    rw [this, map_one]; exact Subgroup.one_mem _
  refine ⟨(QuotientGroup.mk' ((⊥ : Subgroup V).subgroupOf J')).comp φ.toMonoidHom,
    (QuotientGroup.mk'_surjective _).comp φ.surjective, fun u => ?_, ?_⟩
  · show (QuotientGroup.mk' ((⊥ : Subgroup V).subgroupOf J') (φ u) = 1) ↔ (u : V) ∈ (⊥ : Subgroup V)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
      Subgroup.mem_bot]
    constructor
    · intro h1
      have h2 : φ u = 1 := Subtype.ext h1
      have h3 : u = 1 := φ.injective (h2.trans (map_one φ).symm)
      exact congrArg Subtype.val h3
    · intro h1
      have h3 : u = 1 := Subtype.ext h1
      rw [h3, map_one]; rfl
  · intro γ u m hu hm hum
    have hum' : (QuotientGroup.mk (φ u) : ↥J' ⧸ (⊥ : Subgroup V).subgroupOf J') =
        QuotientGroup.mk m := hum
    have hum'' := QuotientGroup.eq.1 hum'
    rw [Subgroup.mem_subgroupOf] at hum''
    have h1 : φ u = m := by
      have : ((φ u)⁻¹ * m : ↥J') = 1 := Subtype.ext (by simpa using hum'')
      exact (inv_mul_eq_one.1 this)
    have h2 := hφ γ u ⟨(γ : MulAut V) (u : V), hu⟩ rfl
    show (QuotientGroup.mk (φ ⟨(γ : MulAut V) (u : V), hu⟩) :
      ↥J' ⧸ (⊥ : Subgroup V).subgroupOf J') = QuotientGroup.mk ⟨(γ : MulAut V) (m : V), hm⟩
    congr 1
    apply Subtype.ext
    show ((φ ⟨(γ : MulAut V) (u : V), hu⟩ : ↥J') : V) = (γ : MulAut V) (m : V)
    rw [← h2, h1]
    rfl

theorem secIsoL_refl {U Z : Subgroup V} (hU : ∀ x ∈ L, ∀ w ∈ U, x w ∈ U)
    (hZ : ∀ x ∈ L, ∀ w ∈ Z, x w ∈ Z) (hZU : Z ≤ U) : SecIsoL L U Z U Z := by
  rw [secIsoL_iff]
  refine ⟨hZU, hZU, fun g u hu => hU g g.2 u hu, fun g z hz => hZ g g.2 z hz,
    fun γ m hm => hU γ γ.2 m hm, fun γ m hm => hZ γ γ.2 m hm, ?_⟩
  refine ⟨QuotientGroup.mk' (Z.subgroupOf U), QuotientGroup.mk'_surjective _, fun u => ?_, ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro γ u m hu hm hum
    have hum'' := QuotientGroup.eq.1 hum
    rw [Subgroup.mem_subgroupOf] at hum''
    show (QuotientGroup.mk ⟨(γ : MulAut V) (u : V), hu⟩ : ↥U ⧸ Z.subgroupOf U) =
      QuotientGroup.mk ⟨(γ : MulAut V) (m : V), hm⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hZ γ γ.2 _ hum''
    simpa [map_mul, map_inv] using this

end SecIso



section NatCopies

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K] {L : Subgroup (MulAut V)}
  {π : ↥(StatedSL n K) →* ↥L} {I I' : Subgroup V}

theorem nat_fixed_eq_one (hn : 2 ≤ n)
    (hD : (FFModel.nat (StatedSL n K)).RealizesVia L I ⊥ π) :
    ∀ u ∈ I, (∀ l ∈ L, l u = u) → u = 1 := by
  obtain ⟨e, he⟩ := exists_linModel hD
  intro u hu hfix
  by_contra hne
  set x : Multiplicative (Fin n → K) := e ⟨u, hu⟩ with hx
  have hx1 : x ≠ 1 := by
    intro h
    exact hne (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  have hfixx : ∀ γ : ↥(StatedSL n K), natAct (StatedSL n K) γ x = x := by
    intro γ
    have hπu : ((π γ : ↥L) : MulAut V) u = u := hfix _ (π γ).2
    have h1 := he γ ⟨u, hu⟩ (by rw [hπu]; exact hu)
    have h2 : (⟨((π γ : ↥L) : MulAut V) (u : V), (by rw [hπu]; exact hu)⟩ : ↥I) = ⟨u, hu⟩ :=
      Subtype.ext hπu
    rw [h2] at h1
    exact h1.symm
  have hv0 : Multiplicative.toAdd x ≠ 0 := fun h => hx1 (by simpa using congrArg Multiplicative.ofAdd h)
  obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd x j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext hcon)
  obtain ⟨i, hij⟩ : ∃ i : Fin n, i ≠ j := by
    by_cases hj0 : j = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [hj0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h => hj0 h.symm⟩
  have h3 := hfixx (trvSL i j hij 1)
  rw [natAct_trvSL] at h3
  have h4 := congrArg Multiplicative.toAdd h3
  simp only [toAdd_ofAdd] at h4
  have h5 := congrFun h4 i
  simp [hj] at h5

theorem isIrr_of_realizes (hn : 2 ≤ n)
    (hD : (FFModel.nat (StatedSL n K)).RealizesVia L I ⊥ π) : XMod.IsIrr ↥L I := by
  obtain ⟨e, he⟩ := exists_linModel hD
  have hinv : XMod.IsInv ↥L I := fun a u hu => hD.2.2.2.1 a u hu
  refine ⟨hinv, ?_, ?_⟩
  · refine bot_lt_iff_ne_bot.2 fun hbot => ?_
    have hsub : Subsingleton ↥I := by
      rw [hbot]; infer_instance
    have hnt : Nontrivial (Multiplicative (Fin n → K)) := by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      infer_instance
    have : Subsingleton (Multiplicative (Fin n → K)) := e.symm.injective.subsingleton
    exact (not_subsingleton _) this
  · intro J hJ _ hJI
    have hJ' : ∀ (γ : ↥(StatedSL n K)) (x : Multiplicative (Fin n → K)),
        x ∈ (J.subgroupOf I).map e.toMonoidHom → natAct (StatedSL n K) γ x ∈ (J.subgroupOf I).map e.toMonoidHom := by
      intro γ x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
      have huJ : (u : V) ∈ J := Subgroup.mem_subgroupOf.1 hu
      have hπuJ : ((π γ : ↥L) : MulAut V) (u : V) ∈ J := hJ (π γ) _ huJ
      have hπuI : ((π γ : ↥L) : MulAut V) (u : V) ∈ I := hinv (π γ) _ u.2
      refine Subgroup.mem_map.2 ⟨⟨_, hπuI⟩, Subgroup.mem_subgroupOf.2 hπuJ, ?_⟩
      exact he γ u hπuI
    rcases natural_invariant_eq hn _ hJ' with h | h
    · left
      have : J.subgroupOf I = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have : e u ∈ (J.subgroupOf I).map e.toMonoidHom := Subgroup.mem_map_of_mem _ hu
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (e.injective (this.trans (map_one e).symm))
      rw [eq_bot_iff]
      intro w hw
      have : (⟨w, hJI hw⟩ : ↥I) ∈ J.subgroupOf I := hw
      rw [‹J.subgroupOf I = ⊥›, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · right
      refine le_antisymm hJI fun w hw => ?_
      have hmem : e ⟨w, hw⟩ ∈ (J.subgroupOf I).map e.toMonoidHom := by rw [h]; trivial
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hmem
      have : u = ⟨w, hw⟩ := e.injective hue
      rw [this] at hu
      exact Subgroup.mem_subgroupOf.1 hu

theorem iso_of_realizes (hπ : Function.Surjective π)
    (hI : (FFModel.nat (StatedSL n K)).RealizesVia L I ⊥ π)
    (hI' : (FFModel.nat (StatedSL n K)).RealizesVia L I' ⊥ π) : XMod.Iso ↥L I I' := by
  obtain ⟨e, he⟩ := exists_linModel hI
  obtain ⟨e', he'⟩ := exists_linModel hI'
  refine ⟨e.trans e'.symm, fun a l l' hl => ?_⟩
  obtain ⟨γ, rfl⟩ := hπ a
  have hl2 : ((π γ : ↥L) : MulAut V) (l : V) ∈ I := hI.2.2.2.1 (π γ) _ l.2
  have hl' : l' = ⟨((π γ : ↥L) : MulAut V) (l : V), hl2⟩ := Subtype.ext hl.symm
  have h1 : e l' = natAct (StatedSL n K) γ (e l) := by
    rw [hl']; exact he γ l hl2
  set u' : ↥I' := e'.symm (e l) with hu'
  have hu'2 : ((π γ : ↥L) : MulAut V) (u' : V) ∈ I' := hI'.2.2.2.1 (π γ) _ u'.2
  have h2 : e' ⟨((π γ : ↥L) : MulAut V) (u' : V), hu'2⟩ = natAct (StatedSL n K) γ (e l) := by
    rw [he' γ u' hu'2, hu']; simp
  have h3 : (e.trans e'.symm) l' = ⟨((π γ : ↥L) : MulAut V) (u' : V), hu'2⟩ := by
    show e'.symm (e l') = _
    rw [h1, ← h2]; simp
  show ((π γ : ↥L) : MulAut V) (((e.trans e'.symm) l : ↥I') : V) = (((e.trans e'.symm) l' : ↥I') : V)
  rw [h3]
  rfl

theorem iso_of_irr_le_iSup {ι : Type} (I : ι → Subgroup V) (hirr : ∀ i, XMod.IsIrr ↥L (I i))
    (hiso : ∀ i j, XMod.Iso ↥L (I i) (I j)) (i₀ : ι) {J : Subgroup V} (hJ : XMod.IsIrr ↥L J)
    (hJU : J ≤ ⨆ i, I i) : XMod.Iso ↥L J (I i₀) := by
  have hIinv : ∀ i, XMod.IsInv ↥L (I i) := fun i => (hirr i).1
  have hJinv : XMod.IsInv ↥L J := hJ.1
  let s : Set (Submodule ↥(XMod.opRing ↥L V) (Additive V)) :=
    Set.range fun i => XMod.toSubmod (hIinv i)
  have hsimple : ∀ m : s, IsSimpleModule ↥(XMod.opRing ↥L V) m := by
    rintro ⟨m, ⟨i, rfl⟩⟩
    exact (XMod.isIrr_iff (hIinv i)).1 (hirr i)
  have : IsSimpleModule ↥(XMod.opRing ↥L V) (XMod.toSubmod hJinv) := (XMod.isIrr_iff hJinv).1 hJ
  have hle : XMod.toSubmod hJinv ≤ sSup s := by
    rw [sSup_range, ← XMod.toSubmod_iSup hIinv]
    exact (XMod.toSubmod_le_iff (hL := hJinv) (hL' := XMod.isInv_iSup hIinv)).2 hJU
  obtain ⟨S, ⟨i, rfl⟩, ⟨eqv⟩⟩ := Submodule.linearEquiv_of_le_sSup (XMod.toSubmod hJinv) s hle
  exact ((XMod.iso_iff hJinv (hIinv i)).2 ⟨eqv⟩).trans (hiso i i₀)

theorem homogeneous_of_nat_copies {ι : Type} [Nonempty ι] (hn : 2 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
    (I : ι → Subgroup V) (hreal : ∀ i, (FFModel.nat (StatedSL n K)).RealizesVia L (I i) ⊥ π) :
    fixV L ⊓ (⨆ i, I i) = ⊥ ∧ HomogeneousSec L (⨆ i, I i) ⊥ := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hπ : Function.Surjective π := (hreal i₀).1
  have hirr : ∀ i, XMod.IsIrr ↥L (I i) := fun i => isIrr_of_realizes hn (hreal i)
  have hiso : ∀ i j, XMod.Iso ↥L (I i) (I j) := fun i j => iso_of_realizes hπ (hreal i) (hreal j)
  have key : ∀ J : Subgroup V, XMod.IsIrr ↥L J → J ≤ ⨆ i, I i → XMod.Iso ↥L J (I i₀) :=
    fun J hJ hJU => iso_of_irr_le_iSup I hirr hiso i₀ hJ hJU
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hx1' : x ≠ 1 := fun h => hx1 (Subgroup.mem_bot.2 h)
    have hxfix : ∀ l ∈ L, l x = x := fun l hl => hx.1 l hl
    have hxsq : x ^ 2 = 1 := hV x
    have hS : XMod.IsIrr ↥L (Subgroup.zpowers x) := by
      have hel : ∀ y ∈ Subgroup.zpowers x, y = 1 ∨ y = x := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have : x ^ k = x ^ (k % 2) := by
          conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
          have : x ^ (2 : ℤ) = 1 := by simpa using hxsq
          rw [this, one_zpow, mul_one]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left; rw [this, h]; simp
        · right; rw [this, h]; simp
      refine ⟨fun a y hy => ?_, bot_lt_iff_ne_bot.2 fun hb => ?_, fun J hJ _ hJS => ?_⟩
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have : (a : MulAut V) (x ^ k) = x ^ k := by rw [map_zpow, hxfix a a.2]
        change (a : MulAut V) (x ^ k) ∈ _
        rw [this]; exact Subgroup.zpow_mem_zpowers x k
      · exact hx1' (Subgroup.mem_bot.1 (hb ▸ Subgroup.mem_zpowers x))
      · by_cases hJb : J = ⊥
        · exact Or.inl hJb
        · right
          obtain ⟨⟨y, hyJ⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hJb
          have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
          rcases hel y (hJS hyJ) with h | h
          · exact absurd h hy1'
          · rw [h] at hyJ
            exact le_antisymm hJS (Subgroup.zpowers_le.2 hyJ)
    have hSU : Subgroup.zpowers x ≤ ⨆ i, I i := Subgroup.zpowers_le.2 hx.2
    obtain ⟨φ, hφ⟩ := key _ hS hSU
    set z := φ ⟨x, Subgroup.mem_zpowers x⟩ with hz
    have hz1 : z ≠ 1 := by
      intro h
      have : (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) = 1 :=
        φ.injective (h.trans (map_one φ).symm)
      exact hx1' (congrArg Subtype.val this)
    have hzfix : ∀ l ∈ L, l (z : V) = (z : V) := by
      intro l hl
      have := hφ ⟨l, hl⟩ ⟨x, Subgroup.mem_zpowers x⟩ ⟨x, Subgroup.mem_zpowers x⟩ (hxfix l hl)
      exact this
    exact hz1 (Subtype.ext (nat_fixed_eq_one hn (hreal i₀) z z.2 hzfix))
  ·
    refine iSup_le fun i => le_sup_of_le_right (le_iSup₂_of_le (I i) ?_ le_rfl)
    exact ⟨bot_le, le_iSup I i, (hirr i).1, (hirr i).2⟩
  · intro J J' hJ hJ'
    obtain ⟨-, hJU, hJinv, hJirr⟩ := hJ
    obtain ⟨-, hJ'U, hJ'inv, hJ'irr⟩ := hJ'
    have h1 := key J ⟨hJinv, hJirr⟩ hJU
    have h2 := key J' ⟨hJ'inv, hJ'irr⟩ hJ'U
    exact secIsoL_of_iso hJinv hJ'inv (h1.trans (XMod.Iso.symm hJ'inv h2))

end NatCopies

section Part3

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

omit [Finite V] in
theorem homogeneous_of_irrPlus {U : Subgroup V} (hU : U ∈ IrrPlus L ⊤) :
    HomogeneousSec L U (fixV L ⊓ U) := by
  obtain ⟨hinv, -, hlt, hirr⟩ := irr_data hU
  rw [inf_comm]
  have hZinv : ∀ x ∈ L, ∀ w ∈ U ⊓ fixV L, x w ∈ U ⊓ fixV L := fun x hx w hw => by
    rw [hw.2 x hx]; exact hw
  have hUinv : XMod.IsInv ↥L U := fun a u hu => hinv a a.2 u hu
  have hirrSec : XMod.IsIrrSec ↥L (U ⊓ fixV L) U :=
    ⟨hlt, fun J hJ hZJ hJU => hirr J (fun x hx w hw => hJ ⟨x, hx⟩ w hw) hZJ hJU⟩
  refine ⟨le_sup_of_le_right (le_iSup₂_of_le U ⟨inf_le_left, le_rfl, hUinv, hirrSec⟩ le_rfl), ?_⟩
  have hall : ∀ J : Subgroup V, (U ⊓ fixV L ≤ J ∧ J ≤ U ∧ XMod.IsInv ↥L J ∧
      XMod.IsIrrSec ↥L (U ⊓ fixV L) J) → J = U := by
    rintro J ⟨hZJ, hJU, hJinv, hJ1, hJ2⟩
    rcases hirr J (fun x hx w hw => hJinv ⟨x, hx⟩ w hw) hZJ hJU with h | h
    · exact absurd h hJ1.ne'
    · exact h
  intro J J' hJ hJ'
  rw [hall J hJ, hall J' hJ']
  exact secIsoL_refl hinv hZinv inf_le_left

theorem part3_of_part1 (hV : ∀ v : V, v ^ 2 = 1) (h1 : B51Part1 G L) : B51Part3 L := by
  obtain ⟨-, hcase⟩ := h1
  rcases hcase with hi | hii | ⟨n, hiii⟩ | hiv
  · exact Or.inl (homogeneous_of_irrPlus hi.1)
  · obtain ⟨-, n, K, hK, hf, hcK, I', π, -, hU, hreal, -, -⟩ := hii
    obtain ⟨hfix, hhom⟩ := homogeneous_of_nat_copies (ι := Fin 2) (n := 3) (by norm_num) hV I' hreal
    left
    rw [← hU, hfix]
    exact hhom
  · exact Or.inr ⟨n, hiii.2⟩
  · obtain ⟨-, n, hn45, k, hk1, -, I', π, -, -, hU, hreal⟩ := hiv
    have : Nonempty (Fin k) := ⟨⟨0, hk1⟩⟩
    have hn2 : 2 ≤ n := by rcases hn45 with rfl | rfl <;> norm_num
    obtain ⟨hfix, hhom⟩ := homogeneous_of_nat_copies hn2 hV I' hreal
    left
    rw [bot_sup_eq] at hU
    rw [← hU, hfix]
    exact hhom

end Part3


end B5

end CFSG.Quasithin
