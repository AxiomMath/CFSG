module

public import CFSG.Quasithin.MS93.S36Lin
public import CFSG.Quasithin.MS93.S33Base
public import CFSG.Quasithin.MS93.S33Trans

public section

namespace CFSG.Quasithin.MS93.S36

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

section TNormal

variable {T : Subgroup G}

theorem le_normalizer_tImage {K : Subgroup G} (hKn : T ≤ Subgroup.normalizer (K : Set G))
    (ψ : MulAut ↥T) : T ≤ Subgroup.normalizer (tImage ψ K : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ tImage ψ K, t * x * t⁻¹ ∈ tImage ψ K := by
    intro t ht x hx
    obtain ⟨k, hk, rfl⟩ := mem_tImage.mp hx
    obtain ⟨t', ht'⟩ := ψ.surjective ⟨t, ht⟩
    have htt : t = ((ψ t' : ↥T) : G) := by rw [ht']
    rw [htt]
    refine mem_tImage.mpr ⟨t' * k * t'⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hKn t'.2) k).mp hk
    · simp [map_mul, map_inv]
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

end TNormal

section Data

variable [Finite G] {M T L : Subgroup G}

theorem s33i_data (h : PUHyp M T L) (ψ : MulAut ↥T)
    (hS : S33i h ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _)
      (Qv (puAmalgam h.le) (baseA _))) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ Function.Surjective a ∧
      IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1 ∧
      Xq M = Zq M L ⊔ Uq M T L ∧ Zq M L ⊓ Uq M T L = ⊥ ∧
      Nat.card ↥⁅Z0q M T, tImage ψ (Z0q M T)⁆ = 2 ^ n ∧
      Nat.card ↥⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ = 2 ^ n * 2 ^ n := by
  obtain ⟨n, F, hF, hFt, a, hq, ha, hU, hXZU, hZU, hR, hRH⟩ := hS
  have hZM : Z0q M T ≤ M := Z0q_le M T
  have hψM : tImage ψ (Z0q M T) ≤ M := (tImage_le ψ _).trans h.le
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hcrit : critR (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) =
      imM h.le ⁅Z0q M T, tImage ψ (Z0q M T)⁆ := by
    rw [critR, puAmalgam.zm_baseA, zm_inr h ψ, imM_commutator h.le hZM hψM]
  have hQZ : Qv (puAmalgam h.le) (baseA _) ⊔ ZM (puAmalgam h.le) (baseA _) =
      imM h.le (pCoreOf 2 M) := by
    rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, puAmalgam.zm_baseA,
      ← S33.imM_sup h.le hQM hZM, sup_eq_left.mpr h.Z0q_le_pCoreOf]
  have hRle : ⁅Z0q M T, tImage ψ (Z0q M T)⁆ ≤ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ :=
    Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl
  rw [hcrit, S33.card_imM h.le (commutator_le_of_le hZM hψM)] at hR
  rw [hcrit, hQZ, zm_inr h ψ, ← imM_commutator h.le hQM hψM,
    S33.relIndex_imM h.le (commutator_le_of_le hQM hψM)] at hRH
  refine ⟨n, F, hF, hFt, a, hq, ha, hU, hXZU, hZU, hR, ?_⟩
  have := Subgroup.relIndex_mul_card ⁅Z0q M T, tImage ψ (Z0q M T)⁆
    ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆
  rw [inf_eq_left.mpr hRle, hRH, hR] at this
  exact this.symm

theorem not_le_tImage_inv (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    {ψ : MulAut ↥T} (hψ : ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M)) :
    ¬ Z0q M T ≤ tImage ψ⁻¹ (pCoreOf 2 M) := by
  rw [le_tImage_inv_iff ψ (Z0q_le_T h) h.pCore_le]
  exact (not_le_tImage_iff h hb ψ).mp hψ

end Data

section Structure

variable [Finite G] {M T L : Subgroup G} (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSL 3 F)} (N : NatSec L (Uq M T L) ⊥ a false)

omit [Fintype F] in
include h in
theorem T_le_normalizer_Uq : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
  h.le.trans (le_normalizer_Uq h.le_normalizer)

omit [Fintype F] in
include h in
theorem T_le_normalizer_L : T ≤ Subgroup.normalizer (L : Set G) :=
  h.le.trans h.le_normalizer

include h N in
theorem linear_of_commImg_le (ha : Function.Surjective a) {t : G} (htT : t ∈ T)
    {P : Subgroup G} (hP : commImg (uq_comm h) (T_le_normalizer_Uq h htT) ≤ P)
    (hPc : Nat.card ↥P ≤ Fintype.card F) {f : (Fin 3 → F) →+ (Fin 3 → F)}
    (hf : IsCoordMap N t f) : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
  refine hf.linear_of_card ha (T_le_normalizer_Uq h htT) (T_le_normalizer_L h htT) ?_
  have hm := card_commImg_mul (uq_comm h) (T_le_normalizer_Uq h htT)
  have hU := N.card_eq
  rw [Nat.card_eq_fintype_card (α := F)] at hU
  have hI := (Subgroup.card_le_of_le hP).trans hPc
  set q := Fintype.card F
  set C := Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer ({t} : Set G))
  set I := Nat.card ↥(commImg (uq_comm h) (T_le_normalizer_Uq h htT))
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hC : q ^ 2 ≤ C := by
    by_contra hlt
    push Not at hlt
    have h1 : I * C < q * q ^ 2 := Nat.mul_lt_mul_of_le_of_lt hI hlt (by omega)
    rw [hm, hU] at h1
    ring_nf at h1
    omega
  rw [hU]
  calc q ^ 3 < q ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
    _ = (q ^ 2) ^ 2 := by ring
    _ ≤ C ^ 2 := Nat.pow_le_pow_left hC 2

include h N in
theorem commutator_H_le [CharP F 2] (ha : Function.Surjective a)
    (hb : critDist (puAmalgam h.le) = 2) {ψ : MulAut ↥T}
    (hψ : ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M))
    (hR' : Nat.card ↥⁅Z0q M T, tImage ψ⁻¹ (Z0q M T)⁆ = Fintype.card F)
    (hH : Nat.card ↥⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ = Fintype.card F * Fintype.card F) :
    ⁅⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆, pCoreOf 2 M⁆ ≤ ⁅Z0q M T, tImage ψ (Z0q M T)⁆ := by
  set Q := pCoreOf 2 M with hQdef
  set U := Uq M T L with hUdef
  set Zα := Z0q M T with hZα
  set B := tImage ψ⁻¹ Zα with hBdef
  set Q' := tImage ψ⁻¹ Q with hQ'def
  set q := Fintype.card F with hqdef
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hZT : Zα ≤ T := Z0q_le_T h
  have hQT : Q ≤ T := h.pCore_le
  have hUT : U ≤ T := (Uq_le_Z0q h.L_le).trans hZT
  have hBT : B ≤ T := tImage_le _ _
  have hQ'T : Q' ≤ T := tImage_le _ _
  have hBQ' : B ≤ Q' := tImage_mono ψ⁻¹ h.Z0q_le_pCoreOf
  have hTU := T_le_normalizer_Uq h
  have hQn : T ≤ Subgroup.normalizer (Q : Set G) := h.le.trans (le_normalizer_pCoreOf M)
  have hZn : T ≤ Subgroup.normalizer (Zα : Set G) := h.le.trans (le_normalizer_Z0q M T)
  have hTQ' : T ≤ Subgroup.normalizer (Q' : Set G) := le_normalizer_tImage hQn ψ⁻¹
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := le_normalizer_tImage hZn ψ⁻¹
  have hUc := N.card_eq
  rw [Nat.card_eq_fintype_card (α := F)] at hUc
  have hBQ : ¬ B ≤ Q := (not_le_tImage_iff h hb ψ⁻¹).mp (not_le_tImage_inv h hb hψ)
  obtain ⟨b₀, hb₀B, hb₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp hBQ
  have hcent := S33.inf_centralizer_Uq h
  have hR'U : ⁅U, B⁆ = ⁅Zα, B⁆ := (S33.commutator_Z0q_eq h hBT).symm
  have hcR' : Nat.card ↥⁅U, B⁆ = q := by rw [hR'U]; exact hR'
  have hcommB : ∀ b (hb : b ∈ B), commImg (uq_comm h) (hTU (hBT hb)) ≤ ⁅U, B⁆ := by
    intro b hb x hx
    obtain ⟨u, hu, rfl⟩ := (mem_commImg _ _).mp hx
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hb hu
  have hlinB : ∀ b ∈ B, ∃ f, IsCoordMap N b f ∧ ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x :=
    fun b hb => by
      obtain ⟨f, hf⟩ := exists_isCoordMap N (hTU (hBT hb))
      exact ⟨f, hf, linear_of_commImg_le h N ha (hBT hb) (hcommB b hb) hcR'.le hf⟩
  set CB := U ⊓ Subgroup.centralizer (B : Set G) with hCB
  have hCBF : IsFClosed N CB := by
    intro x hx y hy c hc
    refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    obtain ⟨f, hf, hlin⟩ := hlinB b hb
    have hxb : x ∈ U ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 b hb).symm⟩
    have := isFClosed_fix (hTU (hBT hb)) hf hlin x hxb y hy c hc
    exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
  obtain ⟨f₀, hf₀, hlin₀⟩ := hlinB b₀ hb₀B
  have hb₀U : commImg (uq_comm h) (hTU (hBT hb₀B)) ≠ ⊥ := by
    intro hbot
    apply hb₀Q
    rw [hQdef, ← hcent]
    refine ⟨hBT hb₀B, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have : b₀ * u * b₀⁻¹ * u⁻¹ ∈ commImg (uq_comm h) (hTU (hBT hb₀B)) :=
      (mem_commImg _ _).mpr ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    calc u * b₀ = (b₀ * u * b₀⁻¹ * u⁻¹)⁻¹ * (b₀ * u) := by group
      _ = b₀ * u := by rw [this, inv_one, one_mul]
  have hI₀F := isFClosed_commImg (uq_comm h) (hTU (hBT hb₀B)) hf₀ hlin₀
  have hI₀c : Nat.card ↥(commImg (uq_comm h) (hTU (hBT hb₀B))) = q := by
    refine le_antisymm ((Subgroup.card_le_of_le (hcommB b₀ hb₀B)).trans hcR'.le) ?_
    have := hI₀F.card_ge (commImg_le _ _) hb₀U
    rwa [Nat.card_eq_fintype_card] at this
  have hR'eq : commImg (uq_comm h) (hTU (hBT hb₀B)) = ⁅U, B⁆ :=
    Subgroup.eq_of_le_of_card_ge (hcommB b₀ hb₀B) (by rw [hI₀c, hcR'])
  have hR'F : IsFClosed N ⁅U, B⁆ := hR'eq ▸ hI₀F
  have hC₀ : Nat.card ↥(U ⊓ Subgroup.centralizer ({b₀} : Set G)) = q * q := by
    have hm := card_commImg_mul (uq_comm h) (hTU (hBT hb₀B))
    rw [hI₀c, hUc] at hm
    have hq0 : 0 < q := by omega
    have : q * Nat.card ↥(U ⊓ Subgroup.centralizer ({b₀} : Set G)) = q * (q * q) := by
      rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hq0 this
  have hCBc : Nat.card ↥CB ≤ q * q := by
    rw [← hC₀]
    refine Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le ?_))
    exact Set.singleton_subset_iff.mpr hb₀B
  set π' := ⁅U, Q'⁆ with hπ'
  have hπ'U : π' ≤ U := commutator_le_left_of_le_normalizer (hQ'T.trans hTU)
  have hπ'Q' : π' ≤ Q' := by
    rw [hπ', Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hUT.trans hTQ')
  have hπ'CB : π' ≤ CB := by
    intro x hx
    refine ⟨hπ'U hx, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hbX : b ∈ tImage ψ⁻¹ (Xq M) := tImage_mono ψ⁻¹ h.Z0q_le_Xq hb
    exact (commute_of_mem_tImage (fun q hq x hx => commute_of_mem_pCoreOf_Xq hq hx)
      (hπ'Q' hx) hbX).symm
  have hπ'eq : π' = ⁅Q', Zα⁆ := by
    rw [hπ', ← S33.commutator_Z0q_eq h hQ'T, Subgroup.commutator_comm]
  have hπ'ψ : tImage ψ π' = ⁅Q, tImage ψ Zα⁆ := by
    rw [hπ'eq, tImage_commutator ψ hQ'T hZT, tImage_tImage_inv ψ hQT]
  have hπ'c : Nat.card ↥π' = q * q := by
    rw [← card_tImage ψ (hπ'U.trans hUT), hπ'ψ, hH]
  have hπ'CBeq : π' = CB :=
    Subgroup.eq_of_le_of_card_ge hπ'CB (by rw [hπ'c]; exact hCBc)
  have hπ'F : IsFClosed N π' := hπ'CBeq ▸ hCBF
  have hR'π' : ⁅U, B⁆ ≤ π' := Subgroup.commutator_mono le_rfl hBQ'
  have hUπ' : ¬ U ≤ π' := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [hπ'c, hUc] at this
    nlinarith
  have hπ'n : ∀ y ∈ Q', ∀ x ∈ π', y * x * y⁻¹ ∈ π' := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_commutator hTU hTQ' (hQ'T hy)) x).mp hx
  have hR'n : ∀ y ∈ Q', ∀ x ∈ ⁅U, B⁆, y * x * y⁻¹ ∈ ⁅U, B⁆ := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_commutator hTU hTB (hQ'T hy)) x).mp hx
  have key : ∀ y ∈ Q', ∀ x ∈ π', y * x * y⁻¹ * x⁻¹ ∈ ⁅U, B⁆ := by
    intro y hy x hx
    obtain ⟨f, hf⟩ := exists_isCoordMap N (hTU (hQ'T hy))
    have hlin := hf.linear_of_le ha (hTU (hQ'T hy)) (T_le_normalizer_L h (hQ'T hy)) hπ'F hπ'U hUπ'
      (fun u hu => by
        have := Subgroup.commutator_mem_commutator hy hu
        rw [Subgroup.commutator_comm] at this
        simpa [commutatorElement_def] using this)
    obtain ⟨e, he⟩ := h.isPGroup ⟨y, hQ'T hy⟩
    have he' : y ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    refine commutator_mem_of_two hR'F hπ'F hR'π' hπ'U (by rw [hcR', Nat.card_eq_fintype_card])
      (by rw [hπ'c, Nat.card_eq_fintype_card]) (hTU (hQ'T hy)) hf hlin (hR'n y hy)
      (hπ'n y hy) he' hx
  have hcomm : ⁅π', Q'⁆ ≤ ⁅U, B⁆ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have := (⁅U, B⁆).inv_mem (key y hy x hx)
    rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = ⁅x, y⁆ by rw [commutatorElement_def]; group] at this
  have hRψ : tImage ψ ⁅U, B⁆ = ⁅Zα, tImage ψ Zα⁆ := by
    rw [hR'U, tImage_commutator ψ hZT hBT, tImage_tImage_inv ψ hZT, Subgroup.commutator_comm]
  have h1 := tImage_mono ψ hcomm
  rwa [tImage_commutator ψ (hπ'U.trans hUT) hQ'T, hπ'ψ, tImage_tImage_inv ψ hQT, hRψ] at h1

omit [Fintype F] in
include h in
theorem commutator_Vq_le (hb : critDist (puAmalgam h.le) = 2) {ψ : MulAut ↥T}
    (hψ : ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M))
    (hHQ : ⁅⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆, pCoreOf 2 M⁆ ≤ ⁅Z0q M T, tImage ψ (Z0q M T)⁆) :
    ⁅Vq M L, pCoreOf 2 M⁆ ≤ Uq M T L := by
  have hZψT : tImage ψ (Z0q M T) ≤ T := tImage_le _ _
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hQn := le_normalizer_pCoreOf M
  have hconjQ : ∀ g ∈ M, ∀ q ∈ pCoreOf 2 M, g * q * g⁻¹ ∈ pCoreOf 2 M :=
    fun g hg q hq => (Subgroup.mem_normalizer_iff.mp (hQn hg) q).mp hq
  have hHM : ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ ≤ M := commutator_le_of_le hQM (hZψT.trans h.le)
  set N := normalClosureIn M ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ with hN
  have hNM : N ≤ M := normalClosureIn_le M _
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).1 (normalClosureIn_normal M _)
  have hconjN : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp (hNn hg) n).mp hn
  let K : Subgroup G :=
    { carrier := {x | x ∈ M ∧ ∀ q ∈ pCoreOf 2 M, ⁅q, x⁆ ∈ N}
      one_mem' := ⟨M.one_mem, fun q _ => by rw [commutatorElement_one_right]; exact N.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨M.mul_mem hxM hyM, fun q hq => ?_⟩
        rw [show ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) by
          simp only [commutatorElement_def]; group]
        exact N.mul_mem (hx q hq) (hconjN x hxM _ (hy q hq))
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨M.inv_mem hxM, fun q hq => ?_⟩
        rw [show ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x⁻¹⁻¹ by
          simp only [commutatorElement_def]; group]
        exact hconjN _ (M.inv_mem hxM) _ (N.inv_mem (hx q hq)) }
  have hKM : K ≤ M := fun x hx => hx.1
  have hKn : (K.subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨M.mul_mem (M.mul_mem m.2 x.2) (M.inv_mem m.2), fun q hq => ?_⟩
    have hq' : (m : G)⁻¹ * q * (m : G)⁻¹⁻¹ ∈ pCoreOf 2 M := hconjQ _ (M.inv_mem m.2) q hq
    rw [show ⁅q, (m : G) * x * (m : G)⁻¹⁆ =
        m * ⁅(m : G)⁻¹ * q * (m : G)⁻¹⁻¹, (x : G)⁆ * (m : G)⁻¹ by
      simp only [commutatorElement_def]; group]
    exact hconjN _ m.2 _ (hx.2 _ hq')
  have hZK : tImage ψ (Z0q M T) ⊓ M ≤ K := by
    rintro z ⟨hz, hzM⟩
    refine ⟨hzM, fun q hq => ?_⟩
    exact le_normalClosureIn hHM (Subgroup.commutator_mem_commutator hq hz)
  have hZψQ : ¬ tImage ψ (Z0q M T) ≤ pCoreOf 2 M := (not_le_tImage_iff h hb ψ).mp hψ
  have hLK : L ≤ K :=
    (le_normalClosureIn_of_not_le h hZψT hZψQ).trans (normalClosureIn_le_of hKM hKn hZK)
  have hVN : Vq M L ≤ N := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    exact (hLK hl).2 q hq
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hconjU : ∀ g ∈ M, ∀ u ∈ Uq M T L, g * u * g⁻¹ ∈ Uq M T L :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp (hUn hg) u).mp hu
  let K' : Subgroup G :=
    { carrier := {x | x ∈ M ∧ ∀ q ∈ pCoreOf 2 M, ⁅x, q⁆ ∈ Uq M T L}
      one_mem' := ⟨M.one_mem, fun q _ => by
        rw [commutatorElement_one_left]; exact (Uq M T L).one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨M.mul_mem hxM hyM, fun q hq => ?_⟩
        rw [show ⁅x * y, q⁆ = (x * ⁅y, q⁆ * x⁻¹) * ⁅x, q⁆ by
          simp only [commutatorElement_def]; group]
        exact (Uq M T L).mul_mem (hconjU x hxM _ (hy q hq)) (hx q hq)
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        refine ⟨M.inv_mem hxM, fun q hq => ?_⟩
        rw [show ⁅x⁻¹, q⁆ = x⁻¹ * ⁅x, q⁆⁻¹ * x⁻¹⁻¹ by
          simp only [commutatorElement_def]; group]
        exact hconjU _ (M.inv_mem hxM) _ ((Uq M T L).inv_mem (hx q hq)) }
  have hK'M : K' ≤ M := fun x hx => hx.1
  have hK'n : (K'.subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨M.mul_mem (M.mul_mem m.2 x.2) (M.inv_mem m.2), fun q hq => ?_⟩
    have hq' : (m : G)⁻¹ * q * (m : G)⁻¹⁻¹ ∈ pCoreOf 2 M := hconjQ _ (M.inv_mem m.2) q hq
    rw [show ⁅(m : G) * x * (m : G)⁻¹, q⁆ =
        m * ⁅(x : G), (m : G)⁻¹ * q * (m : G)⁻¹⁻¹⁆ * (m : G)⁻¹ by
      simp only [commutatorElement_def]; group]
    exact hconjU _ m.2 _ (hx.2 _ hq')
  have hRU : ⁅Z0q M T, tImage ψ (Z0q M T)⁆ ≤ Uq M T L := by
    rw [S33.commutator_Z0q_eq h hZψT]
    exact commutator_le_left_of_le_normalizer (hZψT.trans (T_le_normalizer_Uq h))
  have hHK' : ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ ⊓ M ≤ K' := by
    rintro x ⟨hx, hxM⟩
    exact ⟨hxM, fun q hq => hRU (hHQ (Subgroup.commutator_mem_commutator hx hq))⟩
  have hNK' : N ≤ K' := normalClosureIn_le_of hK'M hK'n hHK'
  rw [Subgroup.commutator_le]
  intro v hv q hq
  exact (hNK' (hVN hv)).2 q hq

end Structure

end CFSG.Quasithin.MS93.S36
