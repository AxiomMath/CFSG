module

import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofObs
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofW
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_conj_eq_of_center_eq_bot {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥)
    {y z : Q} (hyz : MulAut.conj y = MulAut.conj z) : y = z := by
  have hc : z⁻¹ * y ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 := congrArg (fun σ : MulAut Q => σ w) hyz
    simp only [MulAut.conj_apply] at h1
    calc w * (z⁻¹ * y) = z⁻¹ * (z * w * z⁻¹) * y := by group
      _ = z⁻¹ * (y * w * y⁻¹) * y := by rw [h1]
      _ = z⁻¹ * y * w := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc y = z * (z⁻¹ * y) := by group
    _ = z := by rw [hc, mul_one]

theorem conj_apply_eq_mul {Q : Type*} [Group Q] (σ : MulAut Q) (x : Q) :
    MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
  ext z
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem eq_one_of_act_of_mem_zpowers {e α : G} {X : Subgroup G}
    (hXe : X ≤ Subgroup.centralizer ({e} : Set G))
    (hZ : Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) = ⊥)
    {y : ↥X ⧸ aschbacherSolvableCore 3 ↥X} (hαe : α ∈ Subgroup.zpowers e)
    (hact : ∀ l m : ↥X, (m : G) = α * l * α⁻¹ →
      (m : ↥X ⧸ aschbacherSolvableCore 3 ↥X) = y * (l : ↥X ⧸ aschbacherSolvableCore 3 ↥X) * y⁻¹) :
    y = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hαe
  have hc : y ∈ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hle : (l : G) * e = e * l := Subgroup.mem_centralizer_singleton_iff.mp (hXe l.2)
    have hle' : (l : G) * e ^ k = e ^ k * l := (Commute.zpow_right hle k).eq
    have h1 := hact l l (by rw [← hk, ← hle', mul_inv_cancel_right])
    calc (l : ↥X ⧸ aschbacherSolvableCore 3 ↥X) * y =
          y * (l : ↥X ⧸ aschbacherSolvableCore 3 ↥X) * y⁻¹ * y := by rw [← h1]
      _ = y * l := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc


theorem exists_inner_e9 {A L : Subgroup G} {c e : G} (h : Sec14Std G A c L) (heA : e ∈ A)
    (he1 : e ≠ 1) {X : Subgroup G}
    (φJ : ↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* CFSG.Blueprint.NativeSporadic.J2)
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (hker : ∀ α ∈ A, (∀ x ∈ X, x⁻¹ * (α * x * α⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) X) →
      α ∈ Subgroup.zpowers e) :
    ∃ E : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X), Nat.card E = 9 ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ∀ y ∈ E, ∃ α ∈ A, ∀ l m : ↥X, (m : G) = α * l * α⁻¹ →
        (m : ↥X ⧸ aschbacherSolvableCore 3 ↥X) =
          y * (l : ↥X ⧸ aschbacherSolvableCore 3 ↥X) * y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  have hZ : Subgroup.center (↥X ⧸ θ) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  set N := Subgroup.normalizer (X : Set G) with hNdef
  set ψ : ↥N →* MulAut (↥X ⧸ θ) := (Sec4.thetaQuotMulAut ↥X).comp X.normalizerMonoidHom
    with hψdef
  set A' := A.subgroupOf N with hA'def
  set f : ↥A' →* MulAut (↥X ⧸ θ) := ψ.comp A'.subtype with hfdef
  have hfA : ∀ α : ↥A', ((α : ↥N) : G) ∈ A := fun α => Subgroup.mem_subgroupOf.mp α.2
  have hfapp : ∀ (α : ↥A') (l m : ↥X), (m : G) = ((α : ↥N) : G) * l * ((α : ↥N) : G)⁻¹ →
      f α (l : ↥X ⧸ θ) = (m : ↥X ⧸ θ) := by
    intro α l m hm
    have hm' : X.normalizerMonoidHom (α : ↥N) l = m := Subtype.ext hm.symm
    show ((X.normalizerMonoidHom (α : ↥N) l : ↥X) : ↥X ⧸ θ) = (m : ↥X ⧸ θ)
    rw [hm']
  have hfpow : ∀ (α : ↥A'), α ^ 3 = 1 := fun α =>
    Subtype.ext (Subtype.ext (by simpa using hA3 _ (hfA α)))
  have hfc : ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subtype.ext (hAc _ (hfA α) _ (hfA β)))
  have hf3 : ∀ x ∈ f.range, x ^ 3 = 1 := by
    rintro _ ⟨α, rfl⟩
    rw [← MonoidHom.map_pow f α 3, hfpow α, map_one]
  have hrange : CFSG.Assembly.IsElemAbelian 3 f.range :=
    ⟨⟨⟨fun x y => Subtype.ext (hfc _ x.2 _ y.2)⟩⟩, hf3⟩
  have h9 : Nat.card f.range ≤ 9 := Sec10.Item1015Proof.card_le_nine_of_mulAut_J2 φJ f.range hrange
  have hkerf : ∀ α : ↥A', f α = 1 → ((α : ↥N) : G) ∈ Subgroup.zpowers e := by
    intro α hα
    refine hker _ (hfA α) fun x hx => ?_
    have hm : ((α : ↥N) : G) * x * ((α : ↥N) : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (α : ↥N).2 x).mp hx
    have h1 := hfapp α ⟨x, hx⟩ ⟨_, hm⟩ rfl
    rw [hα, MulAut.one_apply, QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  have hker3 : Nat.card f.ker ≤ 3 := by
    have hb3card : Nat.card (Subgroup.zpowers e) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hA3 e heA) he1
    refine (Nat.card_le_card_of_injective
      (fun (x : ↥f.ker) => (⟨(((x : ↥A') : ↥N) : G), hkerf x (MonoidHom.mem_ker.mp x.2)⟩ :
        Subgroup.zpowers e)) ?_).trans hb3card.le
    intro x y hxy
    have hxy' := congrArg Subtype.val hxy
    simp only at hxy'
    exact Subtype.ext (Subtype.ext (Subtype.ext hxy'))
  have hA'card : Nat.card A' = 27 := by
    rw [hA'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA.2]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hA'card] at hcard
  have key : ∀ k r : ℕ, k * r = 27 → k ≤ 3 → r ≤ 9 → r = 9 := by
    intro k r h1 h2 h3
    rcases Nat.lt_or_ge r 9 with hlt | hge
    · have := Nat.mul_le_mul h2 (Nat.le_of_lt_succ hlt : r ≤ 8)
      omega
    · omega
  have hrange9 : Nat.card f.range = 9 := key _ _ hcard hker3 h9
  have hinn := KFacts.ks17J2AutThree_of_outer
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  have hrange_inner : f.range ≤ (MulAut.conj : (↥X ⧸ θ) →* MulAut (↥X ⧸ θ)).range :=
    fun σ hσ => hinn (↥X ⧸ θ) ⟨φJ⟩ σ (hf3 σ hσ)
  have hinj : Function.Injective (MulAut.conj : (↥X ⧸ θ) →* MulAut (↥X ⧸ θ)) :=
    fun y z hyz => eq_of_conj_eq_of_center_eq_bot hZ hyz
  refine ⟨f.range.comap (MulAut.conj : (↥X ⧸ θ) →* MulAut (↥X ⧸ θ)), ?_, ?_, ?_, ?_⟩
  · have hc := Subgroup.card_map_of_injective
        (K := f.range.comap (MulAut.conj : (↥X ⧸ θ) →* MulAut (↥X ⧸ θ))) hinj
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hrange_inner, hrange9] at hc
    exact hc.symm
  · intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    exact hfc _ hx _ hy
  · intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hf3 _ hx
  · intro y hy
    obtain ⟨α, hα⟩ := (hy : MulAut.conj y ∈ f.range)
    refine ⟨_, hfA α, fun l m hm => ?_⟩
    rw [← hfapp α l m hm, hα, MulAut.conj_apply]

theorem le_theta_of_act {e e' : G} {X : Subgroup G}
    (hXe : X ≤ Subgroup.centralizer ({e} : Set G))
    (hNX : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hZ : Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) = ⊥)
    (he'N : e' ∈ Subgroup.normalizer (X : Set G)) {eb : ↥X ⧸ aschbacherSolvableCore 3 ↥X}
    (hact : ∀ l m : ↥X, (m : G) = e' * l * e'⁻¹ →
      (m : ↥X ⧸ aschbacherSolvableCore 3 ↥X) =
        eb * (l : ↥X ⧸ aschbacherSolvableCore 3 ↥X) * eb⁻¹) :
    (((CFSG.pCore 2 ↥(Subgroup.normalizer (Subgroup.zpowers eb :
        Set (↥X ⧸ aschbacherSolvableCore 3 ↥X)))).map
        (Subgroup.normalizer (Subgroup.zpowers eb :
          Set (↥X ⧸ aschbacherSolvableCore 3 ↥X))).subtype).comap
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))).map X.subtype ⊓
      Subgroup.centralizer ({e'} : Set G) ≤
      inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ((Subgroup.closure {e', e} : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) with hπ
  set N := Subgroup.normalizer (X : Set G) with hNdef
  set ψ : ↥N →* MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (Sec4.thetaQuotMulAut ↥X).comp X.normalizerMonoidHom with hψdef
  have hψ : ∀ (n : ↥N) (l : ↥X), ψ n (π l) = π (X.normalizerMonoidHom n l) := fun _ _ => rfl
  have hψe : ψ ⟨e', he'N⟩ = MulAut.conj eb := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) q
    rw [hψ, MulAut.conj_apply]
    exact hact l (X.normalizerMonoidHom ⟨e', he'N⟩ l) rfl
  set D := Subgroup.closure {e', e} with hD
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({e'} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) :=
    Main148.centralizer_closure_pair148 _ e
  set Nb := Subgroup.normalizer (Subgroup.zpowers eb :
    Set (↥X ⧸ aschbacherSolvableCore 3 ↥X)) with hNb
  set Wb := (CFSG.pCore 2 ↥Nb).map Nb.subtype with hWb
  set W : Subgroup G :=
    ((Wb.comap π).map X.subtype) ⊓ Subgroup.centralizer ({e'} : Set G) with hW
  have hWX : W ≤ X := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer (D : Set G) := by
    rw [hCD]
    exact le_inf inf_le_right (hWX.trans hXe)
  have hWn : ∀ g ∈ Subgroup.centralizer (D : Set G), ∀ x ∈ W, g * x * g⁻¹ ∈ W := by
    intro g hg x hx
    rw [hCD] at hg
    obtain ⟨hge', hge⟩ := hg
    have hgN : g ∈ N := hNX hge
    obtain ⟨⟨x', hx', rfl⟩, hxe'⟩ := hx
    have hge'c : (⟨g, hgN⟩ : ↥N) * ⟨e', he'N⟩ * (⟨g, hgN⟩ : ↥N)⁻¹ = ⟨e', he'N⟩ := by
      apply Subtype.ext
      show g * e' * g⁻¹ = e'
      rw [Subgroup.mem_centralizer_singleton_iff.mp hge', mul_inv_cancel_right]
    have h1 : ψ ⟨g, hgN⟩ * MulAut.conj eb * (ψ ⟨g, hgN⟩)⁻¹ = MulAut.conj eb := by
      rw [← hψe, ← map_inv, ← map_mul, ← map_mul, hge'c]
    have hσe : ψ ⟨g, hgN⟩ eb = eb :=
      eq_of_conj_eq_of_center_eq_bot hZ ((conj_apply_eq_mul _ eb).trans h1)
    refine ⟨⟨X.normalizerMonoidHom ⟨g, hgN⟩ x', ?_, rfl⟩, ?_⟩
    · show π (X.normalizerMonoidHom ⟨g, hgN⟩ x') ∈ Wb
      rw [← hψ]
      exact Desc143X.map_pCore_two_le (ψ ⟨g, hgN⟩) hσe ⟨π x', hx', rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hge' hxe') (Subgroup.inv_mem _ hge')
  set ρ : ↥W →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) := π.comp (Subgroup.inclusion hWX) with hρ
  have hρW : ∀ w : ↥W, ρ w ∈ Wb := by
    rintro ⟨_, ⟨⟨x', hx', rfl⟩, -⟩⟩
    exact hx'
  have hWb2 : IsPGroup 2 Wb := CFSG.pCore_isPGroup.map _
  have hrange2 : IsPGroup 2 ρ.range := hWb2.to_le (by rintro _ ⟨w, rfl⟩; exact hρW w)
  have hkerρ : ∀ w : ↥W, w ∈ ρ.ker → Subgroup.inclusion hWX w ∈ aschbacherSolvableCore 3 ↥X := by
    intro w hw
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hw
    exact hw
  let κ : ↥ρ.ker →* ↥(aschbacherSolvableCore 3 ↥X) :=
    ((Subgroup.inclusion hWX).comp ρ.ker.subtype).codRestrict (aschbacherSolvableCore 3 ↥X)
      (fun w => hkerρ w w.2)
  have hκ : Function.Injective κ := by
    intro x y hxy
    have hκz : ∀ z : ↥ρ.ker, ((κ z : ↥X) : G) = ((z : ↥W) : G) := fun z => rfl
    have h1 := congrArg (fun z : ↥(aschbacherSolvableCore 3 ↥X) => ((z : ↥X) : G)) hxy
    simp only [hκz] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hW3 : ¬ 3 ∣ Nat.card W := by
    have hcardW : Nat.card W = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    rw [hcardW]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hrange2
      rw [hk] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    · exact hθ3 (h3.trans (Subgroup.card_dvd_of_injective κ hκ))
  have hWs : Group.IsSolvable ↥W := by
    have : Group.IsNilpotent ↥ρ.range := hrange2.isNilpotent
    have : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥X) := hθs
    have : Group.IsSolvable ↥ρ.ker := Group.isSolvable_of_isSolvable_injective hκ
    exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  set CD := Subgroup.centralizer (D : Set G) with hCDdef
  set R := W.subgroupOf CD with hR
  have hRn : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hR, Subgroup.mem_subgroupOf] at hx ⊢
    exact hWn g g.2 x hx
  have hReq : ↥R ≃* ↥W := Subgroup.subgroupOfEquivOfLe hWC
  have hRs : Group.IsSolvable ↥R :=
    Group.isSolvable_of_isSolvable_injective (f := hReq.toMonoidHom) hReq.injective
  have hR3 : ¬ 3 ∣ Nat.card R := by rwa [Nat.card_congr hReq.toEquiv]
  have hRθ := (solvable_prime_complement_core_characterization (H := ↥CD)
    Nat.prime_three).2.2.2.1 R hRn hRs hR3
  exact fun x hx => ⟨⟨x, hWC hx⟩, hRθ (show (⟨x, hWC hx⟩ : ↥CD) ∈ R from hx), rfl⟩

theorem false_of_j2_of_inner {A L : Subgroup G} {c e : G} (h : Sec14Std G A c L) (heA : e ∈ A)
    (he1 : e ≠ 1) (hΩ : Subgroup.zpowers e ∉ omegaA A) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 e)
    (hφ : Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hNX : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hker : ∀ α ∈ A, (∀ x ∈ X, x⁻¹ * (α * x * α⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) X) →
      α ∈ Subgroup.zpowers e) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  obtain ⟨φJ⟩ := hφ
  have hZ : Subgroup.center (↥X ⧸ θ) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  have hXe : X ≤ Subgroup.centralizer ({e} : Set G) := le_centralizer_of_mem_thetaComponentsAt hX
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    (Desc143X.le_centralizer_of_isE27 hA heA).trans hNX
  obtain ⟨E, hE9, hEc, hE3, hEact⟩ := exists_inner_e9 h heA he1 φJ hAN hker
  obtain ⟨eb, heb, heb1, fb, hfb, wb, hwb, hne⟩ := Desc143X.j2_exists_not_comm ⟨φJ⟩ hEc hE3 hE9
  obtain ⟨e', he'A, hacte⟩ := hEact eb heb
  obtain ⟨f', hf'A, hactf⟩ := hEact fb hfb
  have he'N : e' ∈ Subgroup.normalizer (X : Set G) := hAN he'A
  have hf'N : f' ∈ Subgroup.normalizer (X : Set G) := hAN hf'A
  have heb3 : eb ^ 3 = 1 := hE3 eb heb
  have he'e : e' ∉ Subgroup.zpowers e := fun hmem =>
    heb1 (eq_one_of_act_of_mem_zpowers hXe hZ hmem hacte)
  have he'1 : e' ≠ 1 := fun h1 => he'e (h1 ▸ Subgroup.one_mem _)
  have hoe : orderOf e = 3 := orderOf_eq_prime (hA3 e heA) he1
  have hoe' : orderOf e' = 3 := orderOf_eq_prime (hA3 e' he'A) he'1
  have hee' : e ∉ Subgroup.zpowers e' := fun h1 =>
    he'e ((Desc143X.zpowers_eq_of_mem hoe hoe' h1) ▸ Subgroup.mem_zpowers e')
  have hDh : IsHyperplane A (Subgroup.closure {e', e}) :=
    Main148.isHyperplane_closure_pair148 hA he'A heA he'1 hee'
  have heD : e ∈ Subgroup.closure {e', e} := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hWθ := le_theta_of_act hXe hNX hZ he'N hacte
  have hstar := starConditionAt_of_not_mem_omegaA hA.1 heA he1 hΩ
  have hcomm := commutator_theta_le_of_starConditionAt hA heA he1 hstar hDh heD
  have hθX := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hX
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective θ wb
  have hwbe : wb * eb = eb * wb :=
    Subgroup.mem_centralizer_singleton_iff.mp (Desc143X.pCore_two_le_centralizer heb3 hwb)
  have hθN3 : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) X)) := by
    rw [show inSubgroup (aschbacherSolvableCore 3) X = θ.map X.subtype from rfl,
      Subgroup.card_map_of_injective X.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hBN : Subgroup.zpowers e' ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    Subgroup.zpowers_le.mpr
      (mem_normalizer_of_conj_mem fun t ht => Sec12.conj_mem_inSubgroup_theta he'N ht)
  have hB3 : IsPGroup 3 (Subgroup.zpowers e') := isPGroup_three_of_pow148 fun β hβ => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3 e' he'A, one_zpow]
  set N := Subgroup.normalizer (X : Set G) with hNdef
  set ψ : ↥N →* MulAut (↥X ⧸ θ) := (Sec4.thetaQuotMulAut ↥X).comp X.normalizerMonoidHom
    with hψdef
  have hψ : ∀ (n : ↥N) (l : ↥X), ψ n (π l) = π (X.normalizerMonoidHom n l) := fun _ _ => rfl
  have hψe : ψ ⟨e', he'N⟩ = MulAut.conj eb := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    rw [hψ, MulAut.conj_apply]
    exact hacte l _ rfl
  have hactn : ∀ n : ℤ, ∀ l m : ↥X, (m : G) = e' ^ n * l * (e' ^ n)⁻¹ →
      (m : ↥X ⧸ θ) = eb ^ n * (l : ↥X ⧸ θ) * (eb ^ n)⁻¹ := by
    intro n l m hm
    have hm' : X.normalizerMonoidHom ((⟨e', he'N⟩ : ↥N) ^ n) l = m := by
      apply Subtype.ext
      rw [hm]
      show (((⟨e', he'N⟩ : ↥N) ^ n : ↥N) : G) * l * (((⟨e', he'N⟩ : ↥N) ^ n : ↥N) : G)⁻¹ = _
      rw [Subgroup.coe_zpow]
    have h1 : ψ ((⟨e', he'N⟩ : ↥N) ^ n) (π l) = π m := by rw [hψ, hm']
    rw [map_zpow, hψe, ← map_zpow, MulAut.conj_apply] at h1
    exact h1.symm
  have hk : ∀ β ∈ Subgroup.zpowers e',
      (x : G)⁻¹ * (β * x * β⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    intro β hβ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
    have hmX : e' ^ n * x * (e' ^ n)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ he'N n) x).mp x.2
    have h1 := hactn n x ⟨_, hmX⟩ rfl
    have hc : Commute (eb ^ n) wb := Commute.zpow_left hwbe.symm n
    have hz : π (x⁻¹ * ⟨_, hmX⟩) = 1 := by
      have h1' : π ⟨_, hmX⟩ = eb ^ n * π x * (eb ^ n)⁻¹ := h1
      rw [map_mul, map_inv, h1', hx, hc.eq, mul_inv_cancel_right, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
    exact ⟨_, hz, by simp⟩
  obtain ⟨y, hy, hye⟩ := exists_commute_mem_coset148 hB3 hθN3 hBN hk
  have hyX : y ∈ X := by
    have h1 : (x : G)⁻¹ * y ∈ X := Subgroup.map_subtype_le _ hy
    simpa using X.mul_mem x.2 h1
  have hπy : π ⟨y, hyX⟩ = wb := by
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : (z : G) = (x : G)⁻¹ * y := hzy
    have hxz : (⟨y, hyX⟩ : ↥X) = x * z := Subtype.ext (by
      show y = ((x * z : ↥X) : G)
      rw [Subgroup.coe_mul, hzy', mul_inv_cancel_left])
    rw [hxz, map_mul, show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
    exact hx
  have hyW : y ∈ ((((CFSG.pCore 2 ↥(Subgroup.normalizer (Subgroup.zpowers eb :
      Set (↥X ⧸ θ)))).map (Subgroup.normalizer (Subgroup.zpowers eb :
        Set (↥X ⧸ θ))).subtype).comap π).map X.subtype ⊓
      Subgroup.centralizer ({e'} : Set G)) := by
    refine ⟨⟨⟨y, hyX⟩, ?_, rfl⟩, ?_⟩
    · exact Subgroup.mem_comap.mpr (by rw [hπy]; exact hwb)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hye _ (Subgroup.mem_zpowers _)).symm
  have hyf : ⁅y, f'⁆ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    rw [hθX]
    refine ⟨?_, hcomm (Subgroup.commutator_mem_commutator (hWθ hyW) hf'A)⟩
    have e1 : ⁅y, f'⁆ = y * (f' * y⁻¹ * f'⁻¹) := by simp only [commutatorElement_def]; group
    rw [e1]
    exact X.mul_mem hyX ((Subgroup.mem_normalizer_iff.mp hf'N _).mp (X.inv_mem hyX))
  obtain ⟨z, hz, hzc⟩ := hyf
  have hzc' : (z : G) = ⁅y, f'⁆ := hzc
  have h1 := hactf ⟨y, hyX⟩ (z⁻¹ * ⟨y, hyX⟩) (by
    show ((z : G))⁻¹ * y = f' * y * f'⁻¹
    rw [hzc', commutatorElement_def]
    group)
  have hπz : (z : ↥X ⧸ θ) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπz, inv_one, one_mul] at h1
  have hπy' : ((⟨y, hyX⟩ : ↥X) : ↥X ⧸ θ) = wb := hπy
  rw [hπy'] at h1
  apply hne
  calc fb * wb = fb * wb * fb⁻¹ * fb := by group
    _ = wb * fb := by rw [← h1]

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
