module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Smith81.Sec115Dim

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace Stroth57D

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem central_V (M₀ : Tim79.QuadModel QF V K γ) (R : Tim79.GammaReg QF V γ)
    {x v : G} (hx : x ∈ QF) (hv : v ∈ V) : x * v = v * x := by
  have hvQ : v ∈ QF := R.V_le hv
  refine (Tim79.QuadModel.comm_iff_B M₀ R hx hvQ).mpr ?_
  rw [(M₀.π_ker v hvQ).mpr hv, map_zero]

theorem lagrangian_img [Finite K] (M₀ : Tim79.QuadModel QF V K γ)
    (R : Tim79.GammaReg QF V γ) (hK2 : (2 : K) = 0) (hKV : Nat.card K = Nat.card V)
    {n : ℕ} (hE : Module.finrank K M₀.E = 2 * n) {D : Subgroup G} (hDQ : D ≤ QF)
    (hVD : V ≤ D) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDcard : Nat.card D = Nat.card K ^ (n + 1)) :
    ∃ W : Submodule K M₀.E, (∀ e, e ∈ M₀.img D ↔ e ∈ W) ∧ Module.finrank K W = n ∧
      M₀.B.orthogonal W = W := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqpos : 0 < Nat.card K := by omega
  have hiso : ∀ e ∈ M₀.img D, ∀ f ∈ M₀.img D, M₀.B e f = 0 := by
    rintro _ ⟨x, hxD, hxQ, rfl⟩ _ ⟨y, hyD, hyQ, rfl⟩
    exact (Tim79.QuadModel.comm_iff_B M₀ R hxQ hyQ).mp (hDc x hxD y hyD)
  obtain ⟨W, hW⟩ : ∃ W : Submodule K M₀.E, W = Submodule.span K (M₀.img D : Set M₀.E) :=
    ⟨_, rfl⟩
  have hsub : ∀ e ∈ M₀.img D, e ∈ W := fun e he => by
    rw [hW]
    exact Submodule.subset_span he
  have hWker : ∀ e ∈ M₀.img D, W ≤ LinearMap.ker (M₀.B.flip e) := fun e he => by
    rw [hW, Submodule.span_le]
    exact fun u hu => hiso u hu e he
  have hWiso : ∀ u ∈ W, ∀ v ∈ W, M₀.B u v = 0 := by
    intro u hu
    have h2 : W ≤ LinearMap.ker (M₀.B u) := by
      rw [hW, Submodule.span_le]
      intro e he
      exact (hWker e he) hu
    intro v hv
    exact LinearMap.mem_ker.mp (h2 hv)
  have hWle : W ≤ M₀.B.orthogonal W := fun v hv =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => hWiso u hu v hv
  have hnd : M₀.B.Nondegenerate := Smith81.Sec115Dim.nondeg_of M₀.B hK2 M₀.alt M₀.nondeg
  have hfinW : 2 * Module.finrank K W ≤ Module.finrank K M₀.E :=
    Smith81.Sec115Dim.two_mul_finrank_le_of_iso M₀.B hK2 M₀.alt M₀.nondeg W hWiso
  have hfinO : Module.finrank K (M₀.B.orthogonal W) =
      Module.finrank K M₀.E - Module.finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hnd W
  have hcardD : Nat.card (M₀.img D) = Nat.card K ^ n := by
    have h := Tim79.QuadModel.card_eq M₀ hDQ hVD
    rw [hDcard, ← hKV, pow_succ] at h
    apply Nat.eq_of_mul_eq_mul_left hqpos
    rw [← h]
    ring
  have hWcard : Nat.card W = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
  have hle1 : Nat.card (M₀.img D) ≤ Nat.card W :=
    Nat.card_le_card_of_injective (fun x => (⟨x.1, hsub x.1 x.2⟩ : W))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  have hnW : n ≤ Module.finrank K W := by
    rw [hcardD, hWcard] at hle1
    exact (Nat.pow_le_pow_iff_right hq1).mp hle1
  have hWn : Module.finrank K W = n := by omega
  have hcardEq : Nat.card (M₀.img D) = Nat.card W := by
    rw [hcardD, hWcard, hWn]
  have hinj : Function.Injective (fun x : ↥(M₀.img D) => (⟨x.1, hsub x.1 x.2⟩ : ↥W)) :=
    fun a b h => Subtype.ext (Subtype.mk.inj h)
  have hbij := (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hcardEq⟩
  have hmem : ∀ e, e ∈ M₀.img D ↔ e ∈ W := by
    intro e
    refine ⟨hsub e, fun heW => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 ⟨e, heW⟩
    have h1 : (x : M₀.E) = e := congrArg Subtype.val hx
    rw [← h1]
    exact x.2
  have hOW : M₀.B.orthogonal W = W := by
    refine (Submodule.eq_of_le_of_finrank_eq hWle ?_).symm
    rw [hfinO, hWn]
    omega
  exact ⟨W, hmem, hWn, hOW⟩

theorem mem_of_comm [Finite K] (M₀ : Tim79.QuadModel QF V K γ)
    (R : Tim79.GammaReg QF V γ) (hK2 : (2 : K) = 0) (hKV : Nat.card K = Nat.card V)
    {n : ℕ} (hE : Module.finrank K M₀.E = 2 * n) {D : Subgroup G} (hDQ : D ≤ QF)
    (hVD : V ≤ D) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDcard : Nat.card D = Nat.card K ^ (n + 1)) {l : G} (hl : l ∈ QF)
    (hcomm : ∀ d ∈ D, l * d = d * l) : l ∈ D := by
  obtain ⟨W, hmem, -, hWo⟩ := lagrangian_img M₀ R hK2 hKV hE hDQ hVD hDc hDcard
  have hpi : M₀.π l ∈ M₀.B.orthogonal W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨x, hxD, hxQ, rfl⟩ := (hmem u).mpr hu
    exact (Tim79.QuadModel.comm_iff_B M₀ R hxQ hl).mp (hcomm x hxD).symm
  rw [hWo] at hpi
  obtain ⟨x, hxD, hxQ, hx⟩ := (hmem _).mpr hpi
  have hxl : x⁻¹ * l ∈ V := (Tim79.QuadModel.pi_eq_iff M₀ hxQ hl).mp hx
  have hl' : l = x * (x⁻¹ * l) := by group
  rw [hl']
  exact D.mul_mem hxD (hVD hxl)

theorem finrank_of_card [Finite K] [Finite G] (M₀ : Tim79.QuadModel QF V K γ)
    (R : Tim79.GammaReg QF V γ) (hKV : Nat.card K = Nat.card V) {n : ℕ}
    (hQF : Nat.card QF = Nat.card V ^ (2 * n + 1)) : Module.finrank K M₀.E = 2 * n := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqpos : 0 < Nat.card K := by omega
  have h1 := Tim79.QuadModel.card_eq M₀ (le_refl QF) R.V_le
  have htop : M₀.img QF = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro e
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e
    exact ⟨x, hxQ, hxQ, hx⟩
  rw [hQF, htop, AddSubgroup.card_top, ← hKV, pow_succ] at h1
  have hEcard : Nat.card M₀.E = Nat.card K ^ (2 * n) := by
    apply Nat.eq_of_mul_eq_mul_left hqpos
    rw [← h1]
    ring
  have hfin : Nat.card K ^ Module.finrank K M₀.E = Nat.card K ^ (2 * n) := by
    rw [← Module.natCard_eq_pow_finrank, hEcard]
  exact Nat.pow_right_injective (by omega) hfin

theorem nat_count_aux {q n t L Y C : ℕ} (hq : 0 < q) (hn : n ≤ t) (ht : t ≤ 2 * n)
    (hC : C = q * q ^ (2 * n - t)) (hkey : q ^ n * L ≤ q ^ t * Y) :
    C * L ≤ q ^ (n + 1) * Y := by
  subst hC
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hs : s ≤ n := by omega
  have h2 : 2 * n - (n + s) = n - s := by omega
  rw [h2]
  have hL : L ≤ q ^ s * Y := by
    rw [pow_add, mul_assoc] at hkey
    exact Nat.le_of_mul_le_mul_left hkey (pow_pos hq n)
  have hpow : q ^ (n - s) * q ^ s = q ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  calc q * q ^ (n - s) * L ≤ q * q ^ (n - s) * (q ^ s * Y) := Nat.mul_le_mul_left _ hL
    _ = q ^ (n + 1) * Y := by
      rw [show q * q ^ (n - s) * (q ^ s * Y) = q * (q ^ (n - s) * q ^ s) * Y by ring, hpow]
      ring

theorem card_count [Finite K] [Finite G] (M₀ : Tim79.QuadModel QF V K γ)
    (R : Tim79.GammaReg QF V γ) (hK2 : (2 : K) = 0) (hKV : Nat.card K = Nat.card V)
    {n : ℕ} (hE : Module.finrank K M₀.E = 2 * n) {D : Subgroup G} (hDQ : D ≤ QF)
    (hVD : V ≤ D) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDcard : Nat.card D = Nat.card K ^ (n + 1)) {Λ : Subgroup G} (hΛ : Λ ≤ QF) :
    Nat.card ↥(D ⊓ Subgroup.centralizer (Λ : Set G)) * Nat.card Λ ≤
      Nat.card K ^ (n + 1) * Nat.card ↥(Λ ⊓ D) := by
  obtain ⟨W, hmem, hWn, hWo⟩ := lagrangian_img M₀ R hK2 hKV hE hDQ hVD hDc hDcard
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hnd : M₀.B.Nondegenerate := Smith81.Sec115Dim.nondeg_of M₀.B hK2 M₀.alt M₀.nondeg
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = D ⊓ Subgroup.centralizer (Λ : Set G) :=
    ⟨_, rfl⟩
  rw [← hCdef]
  obtain ⟨S, hS⟩ : ∃ S : Submodule K M₀.E, S = Submodule.span K (M₀.img Λ : Set M₀.E) :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Submodule K M₀.E, T = W ⊔ S := ⟨_, rfl⟩
  have hWT : W ≤ T := by
    rw [hT]
    exact le_sup_left
  have hST : S ≤ T := by
    rw [hT]
    exact le_sup_right
  have hSimg : ∀ l ∈ Λ, M₀.π l ∈ S := fun l hl => by
    rw [hS]
    exact Submodule.subset_span (Tim79.QuadModel.pi_mem_img M₀ hl (hΛ hl))
  have hCD : ∀ x ∈ C, x ∈ D ∧ ∀ l ∈ Λ, l * x = x * l := fun x hx => by
    rw [hCdef] at hx
    exact ⟨(Subgroup.mem_inf.mp hx).1,
      fun l hl => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl⟩
  have hCmem : ∀ x ∈ D, (∀ l ∈ Λ, l * x = x * l) → x ∈ C := fun x hx h => by
    rw [hCdef]
    exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr h⟩
  have hCQF : C ≤ QF := fun x hx => hDQ (hCD x hx).1
  have hVC : V ≤ C := fun v hv =>
    hCmem v (hVD hv) fun l hl => central_V M₀ R (hΛ hl) hv
  have hCimg : (M₀.img C : Set M₀.E) = (M₀.B.orthogonal T : Set M₀.E) := by
    ext e
    constructor
    · rintro ⟨x, hxC, hxQ, rfl⟩
      obtain ⟨hxD, hxΛ⟩ := hCD x hxC
      have hSker : S ≤ LinearMap.ker (M₀.B.flip (Tim79.QuadModel.π M₀ x)) := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨l, hl, hlQ, rfl⟩
        exact (Tim79.QuadModel.comm_iff_B M₀ R hlQ hxQ).mp (hxΛ l hl)
      have hWker' : W ≤ LinearMap.ker (M₀.B.flip (Tim79.QuadModel.π M₀ x)) := by
        intro w hw
        obtain ⟨y, hyD, hyQ, hy⟩ := (hmem w).mpr hw
        show M₀.B w (Tim79.QuadModel.π M₀ x) = 0
        rw [← hy]
        exact (Tim79.QuadModel.comm_iff_B M₀ R hyQ hxQ).mp (hDc y hyD x hxD)
      have hker : T ≤ LinearMap.ker (M₀.B.flip (Tim79.QuadModel.π M₀ x)) := by
        rw [hT]
        exact sup_le hWker' hSker
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      exact hker hu
    · intro he
      rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff] at he
      have heW : e ∈ W := by
        have h1 : e ∈ M₀.B.orthogonal W := LinearMap.BilinForm.mem_orthogonal_iff.mpr
          fun u hu => he u (hWT hu)
        rw [hWo] at h1
        exact h1
      obtain ⟨x, hxD, hxQ, hx⟩ := (hmem e).mpr heW
      refine ⟨x, hCmem x hxD fun l hl => ?_, hxQ, hx⟩
      refine (Tim79.QuadModel.comm_iff_B M₀ R (hΛ hl) hxQ).mpr ?_
      rw [hx]
      exact he _ (hST (hSimg l hl))
  have hCcard : Nat.card ↥C = Nat.card K * Nat.card ↥(M₀.B.orthogonal T) := by
    rw [Tim79.QuadModel.card_eq M₀ hCQF hVC, ← hKV]
    congr 1
    exact congrArg (fun s : Set M₀.E => Nat.card ↥s) hCimg
  have hOT : Nat.card ↥(M₀.B.orthogonal T) = Nat.card K ^ (2 * n - Module.finrank K T) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(M₀.B.orthogonal T)),
      LinearMap.BilinForm.finrank_orthogonal hnd T, hE]
  have hTn : n ≤ Module.finrank K T := by
    rw [← hWn]
    exact Submodule.finrank_mono hWT
  have hTle : Module.finrank K T ≤ 2 * n := by
    rw [← hE]
    exact Submodule.finrank_le T
  have hHle : Λ ⊔ D ≤ QF := sup_le hΛ hDQ
  have hconjD : ∀ x ∈ QF, ∀ h ∈ D, x * h * x⁻¹ ∈ D := by
    intro x hx h hh
    have hcV : ⁅x, h⁆ ∈ V := M₀.comm_mem x hx h (hDQ hh)
    have e : x * h * x⁻¹ = ⁅x, h⁆ * h := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact D.mul_mem (hVD hcV) hh
  have hΛN : Λ ≤ Subgroup.normalizer (D : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjD l (hΛ hl) h hh
    · intro hh
      have h2 := hconjD l⁻¹ (QF.inv_mem (hΛ hl)) _ hh
      rwa [show l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h by group] at h2
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hΛN
  have hHcard : Nat.card ↥(Λ ⊔ D) = Nat.card K * Nat.card ↥(M₀.img (Λ ⊔ D)) := by
    rw [Tim79.QuadModel.card_eq M₀ hHle (hVD.trans le_sup_right), ← hKV]
  let P : Subgroup G :=
    { carrier := {x | x ∈ QF ∧ M₀.π x ∈ T}
      mul_mem' := fun {a b} ha hb => ⟨QF.mul_mem ha.1 hb.1, by
        rw [Tim79.QuadModel.π_mul M₀ a ha.1 b hb.1]
        exact T.add_mem ha.2 hb.2⟩
      one_mem' := ⟨QF.one_mem, by
        rw [Tim79.QuadModel.pi_one M₀]
        exact T.zero_mem⟩
      inv_mem' := fun {a} ha => ⟨QF.inv_mem ha.1, by
        rw [Tim79.QuadModel.pi_inv M₀ ha.1]
        exact T.neg_mem ha.2⟩ }
  have hPmem : ∀ x, x ∈ P ↔ x ∈ QF ∧ M₀.π x ∈ T := fun x => Iff.rfl
  have hPle : Λ ⊔ D ≤ P := by
    refine sup_le (fun l hl => (hPmem l).mpr ⟨hΛ hl, hST (hSimg l hl)⟩)
      (fun d hd => (hPmem d).mpr ⟨hDQ hd, hWT ((hmem _).mp
        (Tim79.QuadModel.pi_mem_img M₀ hd (hDQ hd)))⟩)
  have himgT : ∀ e ∈ M₀.img (Λ ⊔ D), e ∈ T := by
    rintro _ ⟨x, hx, hxQ, rfl⟩
    exact ((hPmem x).mp (hPle hx)).2
  have himgle : Nat.card ↥(M₀.img (Λ ⊔ D)) ≤ Nat.card K ^ Module.finrank K T := by
    have h1 : Nat.card ↥(M₀.img (Λ ⊔ D)) ≤ Nat.card ↥T :=
      Nat.card_le_card_of_injective (fun x => (⟨x.1, himgT x.1 x.2⟩ : ↥T))
        (fun a b h => Subtype.ext (Subtype.mk.inj h))
    exact h1.trans (le_of_eq Module.natCard_eq_pow_finrank)
  have hkey : Nat.card K ^ n * Nat.card Λ ≤
      Nat.card K ^ Module.finrank K T * Nat.card ↥(Λ ⊓ D) := by
    have e1 : Nat.card K * (Nat.card ↥(M₀.img (Λ ⊔ D)) * Nat.card ↥(Λ ⊓ D)) =
        Nat.card K * (Nat.card K ^ n * Nat.card Λ) := by
      rw [← mul_assoc (Nat.card K) (Nat.card ↥(M₀.img (Λ ⊔ D))) (Nat.card ↥(Λ ⊓ D)),
        ← hHcard, hprod, hDcard]
      ring
    have e2 := Nat.eq_of_mul_eq_mul_left hqpos e1
    calc Nat.card K ^ n * Nat.card Λ
        = Nat.card ↥(M₀.img (Λ ⊔ D)) * Nat.card ↥(Λ ⊓ D) := e2.symm
      _ ≤ Nat.card K ^ Module.finrank K T * Nat.card ↥(Λ ⊓ D) :=
          Nat.mul_le_mul_right _ himgle
  have hCval : Nat.card ↥C = Nat.card K * Nat.card K ^ (2 * n - Module.finrank K T) := by
    rw [hCcard, hOT]
  exact nat_count_aux hqpos hTn hTle hCval hkey

end Stroth57D

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.LB_hom_inj (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) {l : G} (hl : l ∈ QB B ⊓ M)
    (hlD : ∀ d ∈ Q ⊓ QB B, ⁅l, d⁆ ∈ Z) : l ∈ Q := by
  have hD : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (stroth_3_5 h34 hc h.width h.n_gt h.noA2 h.gen).2.2.2
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  obtain ⟨K, _, _, _, γ, M₀, hGM⟩ := stroth_globalModelData hc.hyp
  have hK2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hKV : Nat.card K = Nat.card (conjSubgroup g Z) := by
    rw [card_conjSubgroup, hGM.card]
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := h.width
  have hQF : Nat.card (conjSubgroup g Q) = Nat.card (conjSubgroup g Z) ^ (2 * n + 1) := by
    rw [card_conjSubgroup, card_conjSubgroup, hw]
  have R' := Tim79.GammaReg.conj hGM.reg g
  have hE := Stroth57D.finrank_of_card (M₀.conj g) R' hKV hQF
  have hDQF : Q ⊓ QB B ≤ conjSubgroup g Q := fun x hx => by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hx).2
  have hVD : conjSubgroup g Z ≤ Q ⊓ QB B := by
    rw [← hg]
    exact le_inf hc.le hc.B_le_QB
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (n + 1) := by
    rw [hD, hGM.card]
  have hl' : l ∈ conjSubgroup g Q := by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hl).1
  have hcomm : ∀ d ∈ Q ⊓ QB B, l * d = d * l := by
    intro d hd
    have h2 : ⁅l, d⁆ ∈ B := by
      rw [hg]
      exact (M₀.conj g).comm_mem l hl' d (hDQF hd)
    have h3 : ⁅l, d⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hlD d hd, h2⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  exact (Subgroup.mem_inf.mp (Stroth57D.mem_of_comm (M₀.conj g) R' hK2 hKV hE hDQF hVD hDc
    hDcard hl' hcomm)).1

theorem Ctx.pairing_count (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) {Λ A : Subgroup G} (hΛ : Λ ≤ QB B ⊓ M) (hA : A ≤ Q ⊓ QB B)
    (hAZ : A ⊓ Z = ⊥) (hcomm : ∀ l ∈ Λ, ∀ a ∈ A, ⁅l, a⁆ = 1)
    (hcard : Nat.card Z ^ n * Nat.card ↥(Λ ⊓ Q) ≤ Nat.card A * Nat.card Λ) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ Λ, ⁅l, d⁆ ∈ Z) → d ∈ A ⊔ Z := by
  have hD : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (stroth_3_5 h34 hc h.width h.n_gt h.noA2 h.gen).2.2.2
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  obtain ⟨K, _, _, _, γ, M₀, hGM⟩ := stroth_globalModelData hc.hyp
  have hK2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hKV : Nat.card K = Nat.card (conjSubgroup g Z) := by
    rw [card_conjSubgroup, hGM.card]
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := h.width
  have hQF : Nat.card (conjSubgroup g Q) = Nat.card (conjSubgroup g Z) ^ (2 * n + 1) := by
    rw [card_conjSubgroup, card_conjSubgroup, hw]
  have R' := Tim79.GammaReg.conj hGM.reg g
  have hE := Stroth57D.finrank_of_card (M₀.conj g) R' hKV hQF
  have hDQF : Q ⊓ QB B ≤ conjSubgroup g Q := fun x hx => by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hx).2
  have hVD : conjSubgroup g Z ≤ Q ⊓ QB B := by
    rw [← hg]
    exact le_inf hc.le hc.B_le_QB
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (n + 1) := by
    rw [hD, hGM.card]
  have hΛQF : Λ ≤ conjSubgroup g Q := fun l hl => by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp (hΛ hl)).1
  have hcount := Stroth57D.card_count (M₀.conj g) R' hK2 hKV hE hDQF hVD hDc hDcard hΛQF
  have hΛD : Λ ⊓ (Q ⊓ QB B) = Λ ⊓ Q := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, (Subgroup.mem_inf.mp (hΛ h1)).1⟩
  rw [hΛD, hGM.card] at hcount
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = (Q ⊓ QB B) ⊓ Subgroup.centralizer (Λ : Set G) :=
    ⟨_, rfl⟩
  rw [← hCdef] at hcount
  have hΛpos : 0 < Nat.card Λ := Nat.card_pos
  have hCle : Nat.card ↥C ≤ Nat.card Z * Nat.card A := by
    refine Nat.le_of_mul_le_mul_right ?_ hΛpos
    calc Nat.card ↥C * Nat.card Λ ≤ Nat.card Z ^ (n + 1) * Nat.card ↥(Λ ⊓ Q) := hcount
      _ = Nat.card Z * (Nat.card Z ^ n * Nat.card ↥(Λ ⊓ Q)) := by ring
      _ ≤ Nat.card Z * (Nat.card A * Nat.card Λ) := Nat.mul_le_mul_left _ hcard
      _ = Nat.card Z * Nat.card A * Nat.card Λ := by ring
  have hZc : ∀ z ∈ Z, ∀ a ∈ Q, z * a = a * z := fun z hz a ha =>
    hc.hyp.toHyp79.V_central hz ha
  have hZA : Nat.card ↥(A ⊔ Z) = Nat.card A * Nat.card Z := by
    have hZN : Z ≤ Subgroup.normalizer (A : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have haQ : a ∈ Q := (Subgroup.mem_inf.mp (hA ha)).1
        have e : z * a * z⁻¹ = a := by
          rw [hZc z hz a haQ]
          group
        rw [e]
        exact ha
      · intro ha
        have haQ : z * a * z⁻¹ ∈ Q := (Subgroup.mem_inf.mp (hA ha)).1
        have e2 : z⁻¹ * (z * a * z⁻¹) * z = z * a * z⁻¹ := by
          calc z⁻¹ * (z * a * z⁻¹) * z = z⁻¹ * ((z * a * z⁻¹) * z) := by group
            _ = z⁻¹ * (z * (z * a * z⁻¹)) := by rw [hZc z hz _ haQ]
            _ = z * a * z⁻¹ := by group
        have e : z * a * z⁻¹ = a := by
          calc z * a * z⁻¹ = z⁻¹ * (z * a * z⁻¹) * z := e2.symm
            _ = a := by group
        rw [e] at ha
        exact ha
    have e := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hZN
    rw [inf_comm Z A, hAZ, Subgroup.card_bot, mul_one, sup_comm, mul_comm] at e
    exact e
  have hAC : A ≤ C := fun a ha => by
    rw [hCdef]
    exact Subgroup.mem_inf.mpr ⟨hA ha, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      commutatorElement_eq_one_iff_mul_comm.mp (hcomm l hl a ha)⟩
  have hZC : Z ≤ C := fun z hz => by
    rw [hCdef]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, hc.Z_le_QB.1 hz⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    exact (Subgroup.mem_centralizer_iff.mp (Ctx.QB_inf_M_le hc (hΛ hl)) z hz).symm
  have hACeq : A ⊔ Z = C :=
    Subgroup.eq_of_le_of_card_ge (sup_le hAC hZC) (by rw [hZA, mul_comm]; exact hCle)
  intro d hd hdz
  have hdC : d ∈ C := by
    rw [hCdef]
    refine Subgroup.mem_inf.mpr ⟨hd, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hlQF : l ∈ conjSubgroup g Q := by
      rw [← hQB]
      exact (Subgroup.mem_inf.mp (hΛ hl)).1
    have h2 : ⁅l, d⁆ ∈ B := by
      rw [hg]
      exact (M₀.conj g).comm_mem l hlQF d (hDQF hd)
    have h3 : ⁅l, d⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hdz l hl, h2⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  rw [← hACeq] at hdC
  exact hdC

end CFSG.RankThree.GF2n.Stroth80
