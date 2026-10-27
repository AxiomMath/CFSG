module

public import CFSG.Quasithin.EmptyFaithful.LRed4Nat
public import CFSG.Quasithin.EmptyFaithful.SBc32Five
public import CFSG.Quasithin.EmptyFaithful.SBc3List
public import CFSG.Quasithin.EmptyFaithful.S153D57
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.SteinbergCCPerfectCentralization

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.Quasithin.InternalSec
open scoped commutatorElement IsMulCommutative

namespace LRed4

theorem orthogonal_of_b51 (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X S : Subgroup (MulAut V)} (V₂ : Subgroup V) (y : MulAut V)
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) (hS : IsSylowTwoOf S X)
    (hcomm : commV ⁅X, X⁆ = ⊤) (hB : B51Hyp (ffJ X) ⁅X, X⁆)
    (hV₂ : Nat.card ↥V₂ = 4) (hSV₂ : ∀ s ∈ S, ∀ v ∈ V₂, s v ∈ V₂)
    (hy : y ∈ ⁅X, X⁆) (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂) (hyfix : ∀ v ∈ V₂, y v = v → v = 1) :
    ∃ q : V → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
      (∃ E : Subgroup V, Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) ∧ Nat.card V = 2 ^ 6 ∧
        X = orthogonalGroupOf q := by
  have halt := alt15127_of_b51 h51 hI16 hA8 hV hB (Or.inl (isPSL_comm_s8 θ))
  obtain ⟨h4, h4'⟩ := excl34 θ hS hV₂ hSV₂ hy hyV₂ hyfix
  obtain ⟨Z, hZc, hZ2, hsym⟩ := sym_of_alt θ hcomm halt h4 h4'
  have hZ : Z = ⊥ := ctrivial hV hS hcomm hZc hZ2 hsym hV₂ hSV₂ hy hyV₂ hyfix
  subst hZ
  exact exists_quad_of_symmetricNatural_eight hsym

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_of_pCore {I U : Subgroup G} (hUI : U ≤ I)
    (hIU : I ≤ Subgroup.normalizer (U : Set G)) (hUe : IsElemAbelian 2 U)
    (hP : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G)) : IsTwoReducedIn I U := by
  refine ⟨hUI, hIU, hUe, fun D hDI hID hD => ?_⟩
  have hD2 : IsPGroup 2 ↥D := by
    rintro ⟨d, hd⟩
    obtain ⟨k, hk⟩ := hD d hd
    have hmem : d ^ 2 ^ k ∈ pCoreOf 2 I := hP ▸ ⟨I.pow_mem (hDI hd) _, hk⟩
    obtain ⟨f, hf⟩ := pCoreOf_isPGroup 2 I ⟨d ^ 2 ^ k, hmem⟩
    refine ⟨k + f, Subtype.ext ?_⟩
    have := congrArg Subtype.val hf
    simpa [pow_add, pow_mul] using this
  have hDle : D ≤ pCoreOf 2 I := le_pCoreOf_of_le_normalizer 2 hDI hID hD2
  rw [hP] at hDle
  exact fun x hx => (hDle hx).2

theorem exists_equiv_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : ∀ a, f a = 1 ↔ g a = 1) : Nonempty (B ≃* C) := by
  have hk : f.ker = g.ker := by
    ext a
    exact hker a
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivOfSurjective g hg))⟩

theorem normal_perfect_eq_alt8 {K : Subgroup (Equiv.Perm (Fin 8))} (hn : K.Normal)
    (hperf : commutator ↥K = ⊤) (hbot : K ≠ ⊥) : K = alternatingGroup (Fin 8) := by
  have hle : K ≤ alternatingGroup (Fin 8) := by
    intro k hk
    have hker := Abelianization.commutator_subset_ker
      ((Equiv.Perm.sign : Equiv.Perm (Fin 8) →* ℤˣ).comp K.subtype)
    have hmem : (⟨k, hk⟩ : ↥K) ∈ commutator ↥K := by rw [hperf]; trivial
    have := hker hmem
    simpa [Equiv.Perm.mem_alternatingGroup] using this
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ K.subgroupOf (alternatingGroup (Fin 8)) := hx
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

end Helpers

section B51

variable {G : Type} [Group G] [Finite G] {W Y L : Subgroup G} [IsMulCommutative ↥W]

theorem b51Hyp_of_K_le (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hLY : L ≤ Y)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G))
    (hO2 : pCoreOf 2 (autOn Y W) = ⊥) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hS : SQTKGroup ↥(autOn L W)) (hKJ : autOn L W ≤ ffJ (autOn Y W)) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) := by
  set X := autOn Y W with hX
  set K := autOn L W with hK
  set J := ffJ X with hJ
  have hKn := autOn_normal_of (U := W) hYL
  have hX2 := autOn_two_of (Y := Y) ((hLY.trans hYW)) h2
  have hJX : J ≤ X := B6.ffJ_le X
  have hJn : (J.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hQ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J X hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hF : quasithinGenFitting J = K :=
    quasithinGenFitting_eq_of_two_pow hKJ (fun y hy l hl => hKn y (hJX hy) l hl)
      (B1Red.isQuasisimple_to_open hq) (fun y hy => hX2 y (hJX hy)) hQ
  have hZ : centerOf J ≤ K := hF ▸ centerOf_le_quasithinGenFitting J
  exact ⟨by rw [hF, sup_eq_left.2 hZ], hq, hS, hKJ, hQ, (ffJ_ffJ _).symm⟩

end B51

section FPF

variable {V : Type} [CommGroup V]

theorem mem_four_line32 [Finite V] {V₂ : Subgroup V} (hV₂ : Nat.card ↥V₂ = 4) {v w : V} (hv : v ∈ V₂)
    (hw : w ∈ V₂) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v ≠ w) (hV : ∀ v : V, v ^ 2 = 1) :
    ∀ x ∈ V₂, x = 1 ∨ x = v ∨ x = w ∨ x = v * w := by
  classical
  have hvwm : v * w ∈ V₂ := V₂.mul_mem hv hw
  have hvw1 : v * w ≠ 1 := by
    intro h
    apply hvw
    have : w = v⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)).symm
  let F : Finset V := {1, v, w, v * w}
  have hv1' : (1 : V) ≠ v := fun h => hv1 h.symm
  have hw1' : (1 : V) ≠ w := fun h => hw1 h.symm
  have hvm : (1 : V) ≠ v * w := fun h => hvw1 h.symm
  have hnm : v ≠ v * w := fun h =>
    hw1 (mul_left_cancel (a := v) (b := 1) (c := w) (by rw [mul_one]; exact h)).symm
  have hnm' : w ≠ v * w := fun h =>
    hv1 (mul_right_cancel (a := 1) (b := w) (c := v) (by rw [one_mul]; exact h)).symm
  have hF : F.card = 4 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [hnm']
    · simp [hvw, hnm]
    · simp [hv1', hw1', hvm]
  have hsub : (F : Set V) ⊆ (V₂ : Set V) := by
    intro x hx
    simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact V₂.one_mem
    · exact hv
    · exact hw
    · exact hvwm
  have hcard : (V₂ : Set V).ncard ≤ (F : Set V).ncard := by
    rw [Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq]
    exact hV₂.le
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro x hx
  have : x ∈ (F : Set V) := by rw [heq]; exact hx
  simpa [F] using this

theorem fpf_of_odd_line32 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {V₂ : Subgroup V} (hV₂ : Nat.card ↥V₂ = 4)
    {y : MulAut V} (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂) (hodd : Odd (orderOf y))
    (hnt : ∃ v ∈ V₂, y v ≠ v) : ∀ v ∈ V₂, y v = v → v = 1 := by
  intro v hv hyv
  by_contra hv1
  obtain ⟨w, hw, hyw⟩ := hnt
  have hw1 : w ≠ 1 := fun h => hyw (by rw [h, map_one])
  have hvw : v ≠ w := fun h => hyw (by rw [← h]; exact hyv)
  have hmem := mem_four_line32 hV₂ hv hw hv1 hw1 hvw hV
  have hyw' : y w ∈ V₂ := hyV₂ w hw
  have hy1 : y w ≠ 1 := fun h => hw1 (y.injective (h.trans (map_one y).symm))
  have hywv : y w ≠ v := fun h => hvw (y.injective (hyv.trans h.symm))
  have hyww : y w = v * w := by
    rcases hmem _ hyw' with h | h | h | h
    · exact absurd h hy1
    · exact absurd h hywv
    · exact absurd h hyw
    · exact h
  have hy2v : y (y v) = v := by rw [hyv, hyv]
  have hy2w : y (y w) = w := by
    rw [hyww, map_mul, hyv, hyww, ← mul_assoc, ← pow_two, hV v, one_mul]
  have hy2 : ∀ u ∈ V₂, y (y u) = u := by
    intro u hu
    rcases hmem u hu with h | h | h | h
    · rw [h, map_one, map_one]
    · rw [h, hy2v]
    · rw [h, hy2w]
    · rw [h, map_mul, map_mul, hy2v, hy2w]
  have hpow : ∀ k : ℕ, ∀ u ∈ V₂, (y ^ (2 * k)) u = u := by
    intro k
    induction k with
    | zero => intro u hu; rw [Nat.mul_zero, pow_zero]; rfl
    | succ k ih =>
      intro u hu
      have : y ^ (2 * (k + 1)) = y ^ (2 * k) * (y * y) := by
        rw [Nat.mul_succ, pow_add, ← pow_two]
      rw [this]
      show (y ^ (2 * k)) (y (y u)) = u
      rw [hy2 u hu]
      exact ih u hu
  obtain ⟨k, hk⟩ := hodd
  apply hyw
  have hyk : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  rw [hk, pow_succ] at hyk
  have := congrArg (fun f : MulAut V => f w) hyk
  simp only [MulAut.mul_apply, MulAut.one_apply] at this
  rw [hpow k _ (hyV₂ w hw)] at this
  exact this

end FPF

section Perm8

variable {V : Type} [CommGroup V] {X K : Subgroup (MulAut V)}

theorem eq_comm_of_normal_quasisimple (θ : ↥X ≃* Equiv.Perm (Fin 8)) (hKX : K ≤ X)
    (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hq : CFSG.IsQuasisimple ↥K) : K = ⁅X, X⁆ := by
  set N : Subgroup ↥X := K.subgroupOf X with hN
  have hNn : N.Normal := ⟨fun k hk x => by
    rw [hN, Subgroup.mem_subgroupOf] at hk ⊢
    simpa using hn x x.2 k hk⟩
  set Kθ : Subgroup (Equiv.Perm (Fin 8)) := N.map θ.toMonoidHom with hKθ
  have hKθn : Kθ.Normal := hNn.map θ.toMonoidHom θ.surjective
  let eAK : ↥K ≃* ↥Kθ := (Subgroup.subgroupOfEquivOfLe hKX).symm.trans (θ.subgroupMap N)
  have hqK : CFSG.IsQuasisimple ↥Kθ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eAK hq
  have hperf : commutator ↥Kθ = ⊤ := hqK.1.commutator_eq_top
  have hbot : Kθ ≠ ⊥ := by
    intro hb
    obtain ⟨-, -, a, b, hab⟩ := hqK
    have hs : Subsingleton ↥Kθ := by rw [hb]; infer_instance
    have : Subsingleton (↥Kθ ⧸ Subgroup.center ↥Kθ) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim x y]⟩
    exact hab (Subsingleton.elim _ _)
  have hA : Kθ = alternatingGroup (Fin 8) := normal_perfect_eq_alt8 hKθn hperf hbot
  ext k
  constructor
  · intro hk
    have hkX : k ∈ X := hKX hk
    rw [theta_mem_alt θ k hkX, ← hA]
    exact Subgroup.mem_map_of_mem θ.toMonoidHom (show (⟨k, hkX⟩ : ↥X) ∈ N from hk)
  · intro hk
    have hkX : k ∈ X := commutator_le_self X hk
    have hmem : θ ⟨k, hkX⟩ ∈ Kθ := by rw [hA]; exact (theta_mem_alt θ k hkX).1 hk
    obtain ⟨c, hc, hcθ⟩ := Subgroup.mem_map.1 hmem
    have : c = ⟨k, hkX⟩ := θ.injective hcθ
    rw [this] at hc
    exact hc

end Perm8

section Assembly

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem ker_UI_eq_ker_UL (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) (hpre : Preamble32 T V₁ I L) :
    I ⊓ Subgroup.centralizer (UI153 T I : Set G) = I ⊓ Subgroup.centralizer (UL153 T I L : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.toFacts153.sylow
  have hUIc : UI153 T I ≤ centerOf (pCoreOf 2 I) :=
    (conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 c25.ctx.charTwo
      (SBc3.omegaOneCenter_le_Sgp153 hh)).1
  have hOCUI : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hUIc hu).2 x hx).symm
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) :=
    (S153H.L_le_I c).trans (le_normalizer_conjClosure _ I)
  have hULle : UL153 T I L ≤ UI153 T I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
  refine le_antisymm (inf_le_inf_left I (Subgroup.centralizer_le hULle)) fun x hx => ⟨hx.1, ?_⟩
  have hxO : x ∈ pCoreOf 2 I := by rw [hpre.2.1]; exact hx
  exact hOCUI hxO

theorem exists_equiv_autOn_UL (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) (hpre : Preamble32 T V₁ I L) :
    Nonempty (↥(autOn I (UL153 T I L)) ≃* Equiv.Perm (Fin 8)) := by
  obtain ⟨e⟩ := c.c31
  have hIUI : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hIUL : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hker := ker_UI_eq_ker_UL c hpre
  obtain ⟨e2⟩ := exists_equiv_of_ker_eq (S153D.autOnHom hIUL) (S153D.autOnHom hIUI)
    (S153D.autOnHom_surjective hIUL) (S153D.autOnHom_surjective hIUI) fun a => by
      rw [S153D.autOnHom_eq_one_iff, S153D.autOnHom_eq_one_iff]
      constructor
      · intro h
        have : (a : G) ∈ I ⊓ Subgroup.centralizer (UL153 T I L : Set G) := ⟨a.2, h⟩
        rw [← hker] at this
        exact this.2
      · intro h
        have : (a : G) ∈ I ⊓ Subgroup.centralizer (UI153 T I : Set G) := ⟨a.2, h⟩
        rw [hker] at this
        exact this.2
  exact ⟨e2.trans e⟩

theorem comm_UL_eq (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) : ⁅UL153 T I L, L⁆ = UL153 T I L := by
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hLleI : L ≤ I := le_of_mem_cComp hLI
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIUL : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hUIle : UI153 T I ≤ I := (S153H.UI_le_pCoreOf c).trans (pCoreOf_le 2 I)
  have hULL : ⁅UL153 T I L, L⁆ ≤ UL153 T I L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLleI.trans hIUL)
  refine le_antisymm hULL ?_
  have hN : ∀ k ∈ I, ∀ n ∈ ⁅UL153 T I L, L⁆, k * n * k⁻¹ ∈ ⁅UL153 T I L, L⁆ := fun k hk n hn =>
    (Subgroup.mem_normalizer_iff.mp (S153H.mem_normalizer_commutator (hIUL hk) (hIL hk)) n).mp hn
  have h2 : ⁅⁅L, UI153 T I⁆, L⁆ ≤ ⁅UL153 T I L, L⁆ := by
    rw [Subgroup.commutator_comm L (UI153 T I)]
  have h3 := SteinbergCC.commutator_le_of_perfect_mod hLleI hUIle hN (Subgroup.isPerfect_iff.2 hperf) h2
  rw [Subgroup.commutator_comm L (UI153 T I)] at h3
  exact h3

theorem exists_odd_acting (h113 : StageLemma14113) (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) :
    ∃ g ∈ Yp, Odd (orderOf g) ∧ ∃ v ∈ V₂, g * v * g⁻¹ ≠ v := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := c25.facts.case_two.2
  have h2 : ⁅V₂, Yp⁆ = V₂ := by
    rw [hYp]
    exact hyp.hyp.commutator_V₂_Yplus h113 hyp.decomp
  by_contra hcon
  push Not at hcon
  have hgen : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≤
      Subgroup.centralizer (V₂ : Set G) := by
    rw [oTwoUpper, Subgroup.closure_le]
    intro x hx
    have hxYp : x ∈ Yp := by rw [hYp]; exact Subgroup.subset_closure hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    have h := hcon x hxYp hx.2 v hv
    calc v * x = (x * v * x⁻¹) * x := by rw [h]
      _ = x * v := by group
  have hYC : Yp ≤ Subgroup.centralizer (V₂ : Set G) := by rwa [← hYp] at hgen
  have hbot : ⁅V₂, Yp⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
  rw [hbot] at h2
  have h4 := hyp.decomp.card₂
  rw [← h2, Subgroup.card_bot] at h4
  omega

theorem input32One_of_b51 (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (h113 : StageLemma14113) : Input32One := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hpre
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have D : Decomp153 T M V₁ V₂ t := hh.decomp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hsyl.2.1
  obtain ⟨hLc, -, -, -, -, hLQ⟩ := c25.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLleI : L ≤ I := le_of_mem_cComp hLI
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hIUL : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hLUL : L ≤ Subgroup.normalizer (UL153 T I L : Set G) := hLleI.trans hIUL
  have hUe : IsElemAbelian 2 (UL153 T I L) := SBc.isElemAbelian_UL c
  have : IsMulCommutative ↥(UL153 T I L) := hUe.1
  have hV₂UL : V₂ ≤ UL153 T I L := SBc.V₂_le_UL h113 c
  have hULI : UL153 T I L ≤ I := (S153H.UL_le_Sgp153 c).trans hSI
  have hred : IsTwoReducedIn I (UL153 T I L) := isTwoReducedIn_of_pCore hULI hIUL hUe hpre.2.1
  have hO2 : pCoreOf 2 (autOn I (UL153 T I L)) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2L : pCoreOf 2 (autOn L (UL153 T I L)) = ⊥ := pCoreOf_autOn_L_eq_bot1527d hLleI hIL hO2
  have hcomm : ⁅UL153 T I L, L⁆ = UL153 T I L := comm_UL_eq c
  have hnt : ¬ L ≤ Subgroup.centralizer (UL153 T I L : Set G) := by
    intro h
    have h0 : ⁅UL153 T I L, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
    rw [hcomm] at h0
    have hV₂bot : V₂ = ⊥ := le_bot_iff.1 (h0 ▸ hV₂UL)
    have h4 := D.card₂
    rw [hV₂bot, Subgroup.card_bot] at h4
    omega
  have hqa : CFSG.IsQuasisimple ↥(autOn L (UL153 T I L)) := isQuasisimple_autOn hLUL hLQ hO2L hnt
  obtain ⟨θ⟩ := exists_equiv_autOn_UL c hpre
  have hKX : autOn L (UL153 T I L) = ⁅autOn I (UL153 T I L), autOn I (UL153 T I L)⁆ :=
    eq_comm_of_normal_quasisimple θ (InternalSec.autOn_le_autOn_of_le hLleI)
      (InternalSec.autOn_normal_of hIL) hqa
  have hsqI : SQTKGroup ↥I := sqtkGroup_of_pCoreOf_ne_bot hh.hyp.qtfe.qtke hh.hyp.qtfe.simple
    hh.hyp.qtfe.nonabelian c25.ctx.inH.1.2
  have hSQL : SQTKGroup ↥L := B5.sqtk_of_le hsqI hLleI
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (UL153 T I L : Set G)) :=
    (pCoreOf_isPGroup 2 I).to_le fun x hx => by
      have hx' : x ∈ I ⊓ Subgroup.centralizer (UL153 T I L : Set G) := ⟨hLleI hx.1, hx.2⟩
      rw [← hpre.2.1] at hx'
      exact hx'
  have hSQa : SQTKGroup ↥(autOn L (UL153 T I L)) := InternalSec.sqtkGroup_autOn hLUL hSQL hker
  have h2 : ∀ y ∈ I, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (UL153 T I L : Set G) := fun y hy => by
    obtain ⟨e, he⟩ := InternalSec.two_of_sup hS2 (hSI.trans hIL) y (hIeq ▸ hy)
    exact ⟨e, Subgroup.mem_sup_left he⟩
  have hKJ : autOn L (UL153 T I L) ≤ ffJ (autOn I (UL153 T I L)) :=
    (InternalSec.autOn_le_autOn_of_le (le_of_mem_cComp hLc)).trans
      (SBc3.autOn_thompsonJ_le_ffJ hUe hULI hIUL)
  have hB : B51Hyp (ffJ (autOn I (UL153 T I L))) ⁅autOn I (UL153 T I L), autOn I (UL153 T I L)⁆ := by
    rw [← hKX]
    exact b51Hyp_of_K_le hIUL hLleI hIL h2 hO2 hqa hSQa hKJ
  have hcommV : commV ⁅autOn I (UL153 T I L), autOn I (UL153 T I L)⁆ = ⊤ := by
    rw [← hKX]
    exact InternalSec.commV_autOn_eq_top hLUL hcomm
  have hV : ∀ v : ↥(UL153 T I L), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hUe.2 v v.2)
  have hS : IsSylowTwoOf (autOn (Sgp153 T V₁) (UL153 T I L)) (autOn I (UL153 T I L)) :=
    Setup.isSylowTwoOf_autOn hsyl hIUL
  have hV₂card : Nat.card ↥(V₂.subgroupOf (UL153 T I L)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂UL).toEquiv]
    exact D.card₂
  have hSV₂ : ∀ s ∈ autOn (Sgp153 T V₁) (UL153 T I L), ∀ v ∈ V₂.subgroupOf (UL153 T I L),
      s v ∈ V₂.subgroupOf (UL153 T I L) := by
    intro s hs v hv
    obtain ⟨g, hgS, rfl⟩ := Setup.mem_autOn_iff.1 hs
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    rw [InternalSec.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (Hyp153.Sgp153_le_normalizer_V₂ hh.hyp D hgS) _).mp hv
  obtain ⟨g, hgYp, hgodd, v₀, hv₀, hgv₀⟩ := exists_odd_acting h113 c
  have hgL : g ∈ L := c.c27.Yp_le hgYp
  have hgN : g ∈ Subgroup.normalizer (UL153 T I L : Set G) := hLUL hgL
  have hgV₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Hyp15310.Yp_le_normalizer_V₂ hh c25.facts.case_two.2 hgYp
  have hyK : conjAct (UL153 T I L) ⟨g, hgN⟩ ∈ autOn L (UL153 T I L) :=
    Setup.mem_autOn_iff.2 ⟨⟨g, hgN⟩, hgL, rfl⟩
  have hyV₂ : ∀ v ∈ V₂.subgroupOf (UL153 T I L),
      conjAct (UL153 T I L) ⟨g, hgN⟩ v ∈ V₂.subgroupOf (UL153 T I L) := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    rw [InternalSec.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp hgV₂ _).mp hv
  have hodd : Odd (orderOf (conjAct (UL153 T I L) ⟨g, hgN⟩)) := by
    have hd : orderOf (conjAct (UL153 T I L) ⟨g, hgN⟩) ∣ orderOf g := by
      have := orderOf_map_dvd (conjAct (UL153 T I L)) (⟨g, hgN⟩ : Subgroup.normalizer (UL153 T I L : Set G))
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hgodd hd
  have hnt2 : ∃ v ∈ V₂.subgroupOf (UL153 T I L), conjAct (UL153 T I L) ⟨g, hgN⟩ v ≠ v := by
    refine ⟨⟨v₀, hV₂UL hv₀⟩, Subgroup.mem_subgroupOf.2 hv₀, fun h => hgv₀ ?_⟩
    have := congrArg Subtype.val h
    rwa [InternalSec.coe_conjAct_apply] at this
  have hyfix := fpf_of_odd_line32 hV hV₂card hyV₂ hodd hnt2
  exact orthogonal_of_b51 h51 hI16 hA8 hV (V₂.subgroupOf (UL153 T I L)) _ θ hS hcommV hB hV₂card hSV₂
    (hKX ▸ hyK) hyV₂ hyfix

end Assembly

end LRed4

end CFSG.Quasithin
