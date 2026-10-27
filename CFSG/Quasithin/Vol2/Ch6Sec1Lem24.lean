module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem21

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise MatrixGroups

theorem det_sub_one_ne_zero_of_odd {F : Type*} [Field F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (hA : A ≠ 1) (hodd : Odd (orderOf A)) :
    ((A : Matrix (Fin 2) (Fin 2) F) - 1).det ≠ 0 := by
  intro h0
  set M := (A : Matrix (Fin 2) (Fin 2) F) with hM
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact A.2
  rw [Matrix.det_fin_two] at h0
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h0
  have htr : M 0 0 + M 1 1 = 0 := by linear_combination -h0 + hd + h2
  have hsq : A ^ 2 = 1 := by
    ext i j
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← hM]
    · linear_combination M 0 0 * htr - hd - h2
    · linear_combination M 0 1 * htr
    · linear_combination M 1 0 * htr
    · linear_combination M 1 1 * htr - hd - h2
  have hdvd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf A = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact hA (orderOf_eq_one_iff.mp h1)

open Matrix in
theorem le_commutator_sup_of_sumNatural {G : Type} [Group G] {F : Type*} [Field F] [CharP F 2]
    {s : ℕ} {X R E D : Subgroup G} (hsum : IsSumOfNaturalSL2ModulesOver F s X R R E)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hDX : D ≤ X) {d : G} (hd : d ∈ D)
    (hdR : d ∉ R) (hodd : Odd (orderOf d)) : R ≤ ⁅R, D⁆ ⊔ E := by
  intro r hr
  obtain ⟨β, φ, -, hβk, hφs, hφk, heqv⟩ := hsum
  set A := β ⟨d, hDX hd⟩ with hAdef
  have hA1 : A ≠ 1 := fun h => hdR ((hβk _).mp h)
  have hAodd : Odd (orderOf A) := by
    refine Odd.of_dvd_nat hodd ?_
    have := orderOf_map_dvd β ⟨d, hDX hd⟩
    rwa [Subgroup.orderOf_mk] at this
  have hdet := det_sub_one_ne_zero_of_odd A hA1 hAodd
  set N := (A : Matrix (Fin 2) (Fin 2) F) - 1 with hN
  have hNN : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N (isUnit_iff_ne_zero.mpr hdet)
  have key : ∀ v : Fin 2 → F, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v - v = N *ᵥ v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  set w := Multiplicative.toAdd (φ ⟨r, hr⟩) with hw
  obtain ⟨x, hx⟩ := hφs (Multiplicative.ofAdd fun j => N⁻¹ *ᵥ w j)
  have hy : d * (x : G) * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hXR (hDX hd)) x).mp x.2
  have hφy := heqv ⟨d, hDX hd⟩ x ⟨d * x * d⁻¹, hy⟩ rfl
  have hc : φ (⟨d * x * d⁻¹, hy⟩ * x⁻¹) = φ ⟨r, hr⟩ := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hφy, hx, toAdd_ofAdd, toAdd_ofAdd]
    funext j
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [← hAdef]
    change (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (N⁻¹ *ᵥ w j) + -(N⁻¹ *ᵥ w j) = w j
    rw [← sub_eq_add_neg, key, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hE : ((⟨d * x * d⁻¹, hy⟩ * x⁻¹)⁻¹ * ⟨r, hr⟩ : ↥R) ∈ E.subgroupOf R := by
    rw [Subgroup.mem_subgroupOf]
    refine (hφk _).mp ?_
    rw [map_mul, map_inv, hc, inv_mul_cancel]
  rw [Subgroup.mem_subgroupOf] at hE
  have hcomm : d * (x : G) * d⁻¹ * (x : G)⁻¹ ∈ ⁅R, D⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hd x.2
  have e : r = (d * (x : G) * d⁻¹ * (x : G)⁻¹) *
      ((d * (x : G) * d⁻¹ * (x : G)⁻¹)⁻¹ * r) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right ?_)
  simpa using hE

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem conjClosure_sup_T_eq (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ T) =
      conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  refine le_antisymm ?_ (conjClosure_mono le_rfl le_sup_left)
  have hTI : T ≤ Subgroup.normalizer
      ((Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) :=
    h.toHyp611Nat.T_le_normalizer_ZS.trans (F7.normalizer_le_normalizer_centralizer _)
  refine CFSG.Quasithin.conjClosure_le fun x hx v hv => ?_
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTI] at hx
  obtain ⟨i, hi, t, ht, rfl⟩ := hx
  have htv : t * v * t⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (h.toHyp611.T_le_normalizer ht) v).mp hv
  have e : i * t * v * (i * t)⁻¹ = i * (t * v * t⁻¹) * i⁻¹ := by group
  rw [e]
  exact mem_conjClosure hi htv

theorem V_le_inf_conjSubgroup (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L) :
    V ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
      conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l := by
  refine le_inf (le_conjClosure V _) ?_
  have h1 := conjSub_mono l⁻¹ (le_conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))
  rwa [conjSub_eq_of_mem_normalizer'
    (Subgroup.inv_mem _ (h.toHyp611.L_le_normalizer hl))] at h1

theorem lemma_6_1_24_one (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        Subgroup.centralizer (V : Set G) =
      centralizerMod (ch6ZS T L V)
        (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) := by
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  obtain ⟨-, -, ⟨-, -, -, hEN⟩, ⟨-, -, hCE⟩, -, hRO⟩ := h21
  obtain ⟨hUO, hUOZ⟩ := h.lemma_6_1_20_one h432
  have hZE := (inf_le_left : ch6ZS T L V ≤ V).trans (h.V_le_inf_conjSubgroup hl)
  have hRMV := hRO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  ext x
  rw [mem_centralizerMod]
  constructor
  · intro hx
    have hxR := centralizerMod_le_left _ _ _ (hCE ▸ hx)
    refine ⟨hxR, Subgroup.centralizer_le_normalizer _ ?_, fun u hu => ?_⟩
    · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        (inf_le_left : ch6ZS T L V ≤ V)) hx.2
    · exact hUOZ (Subgroup.commutator_mem_commutator hx.1 (hUO hu))
  · rintro ⟨hxR, -, hxc⟩
    rw [hCE]
    exact ⟨hxR, hEN (hRMV hxR), fun u hu => hZE (hxc u hu)⟩

theorem lemma_6_1_24_two (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    IsElemAbelianMod
        (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          Subgroup.centralizer (V : Set G)) ∧
      (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          Subgroup.centralizer (V : Set G)).relIndex
          (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
            conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l)) *
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          Subgroup.centralizer (V : Set G)).relIndex
          (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
            conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l)) =
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l).relIndex
          (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
            conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l)) ∧
      ∀ DL : Subgroup G,
        QuasithinUnique.Lin2.IsHallTwoPrimeOf DL
          (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) →
        ∀ D : Subgroup G, D ≤ DL → D ≠ ⊥ →
          pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
              conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l) =
            ⁅pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
                conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l), D⁆ ⊔
              (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
                Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hL1 : U ⊔ conjSubgroup U l = L ⊔ U := h21.1.2.2
  obtain ⟨-, ⟨hRAB, -⟩, ⟨-, -, -, hEN⟩, ⟨hRE, hABE, -⟩, -, -⟩ := h21
  set R := pCoreOf 2 (U ⊔ conjSubgroup U l) with hR
  set E := U ⊓ conjSubgroup U l with hE
  set A := U ⊓ Subgroup.centralizer (V : Set G) with hA
  set B := conjSubgroup U l ⊓ Subgroup.centralizer (V : Set G) with hB
  have hEA : E ≤ A := hABE ▸ inf_le_left
  have hAR : A ≤ R := hRAB ▸ le_sup_left
  have hBR : B ≤ R := hRAB ▸ le_sup_right
  refine ⟨fun u hu v hv => ⟨hEA (hRE u hu v hv).1, hEA (hRE u hu v hv).2⟩, ?_, ?_⟩
  ·
    have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
      intro b hb
      refine mem_normalizer_of_forall_conj_mem_of_le fun a ha => ?_
      have e : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact A.mul_mem (hEA (hRE b (hBR hb) a (hAR ha)).1) ha
    have h1 : A.relIndex R = E.relIndex B := by
      rw [hRAB, sup_comm, relIndex_sup_eq_relIndex_of_le_normalizer hBA,
        ← Subgroup.inf_relIndex_right, hABE]
    have hlMV : l ∈ ch6MV M V := ⟨h.L_le hl, h.toHyp611.L_le_normalizer hl⟩
    have hEl : conjSub l⁻¹ E = E := conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ (hEN hlMV))
    have hAl : conjSub l⁻¹ A = B := by
      show conjSub l⁻¹ (U ⊓ Subgroup.centralizer (V : Set G)) =
        conjSub l⁻¹ U ⊓ Subgroup.centralizer (V : Set G)
      rw [conjSub_inf, conjSub_centralizer', conjSub_eq_of_mem_normalizer'
        (Subgroup.inv_mem _ (h.toHyp611.L_le_normalizer hl))]
    have h2 : E.relIndex B = E.relIndex A := by
      calc E.relIndex B = (conjSub l⁻¹ E).relIndex (conjSub l⁻¹ A) := by rw [hEl, hAl]
        _ = E.relIndex A := Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective
    rw [← Subgroup.relIndex_mul_relIndex E A R hEA hAR, h1, h2]
  ·
    intro DL hDL D hD hD0
    obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD0
    have hd1' : d ≠ 1 := fun h0 => hd1 (Subtype.ext h0)
    have hDL' : D ≤ L := hD.trans (hDL.1.trans inf_le_left)
    have hodd : Odd (orderOf d) := by
      refine Odd.of_dvd_nat hDL.2.1 ?_
      exact (Subgroup.orderOf_dvd_natCard D hdD).trans (Subgroup.card_dvd_of_le hD)
    have hdR : d ∉ R := by
      intro hdR
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (U ⊔ conjSubgroup U l))) ⟨d, hdR⟩
      rw [Subgroup.orderOf_mk] at hk
      rw [hk] at hodd
      have hk0 : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
      rw [hk0, pow_zero] at hk
      exact hd1' (orderOf_eq_one_iff.mp hk)
    have hyp := h.almostSpecialL2Hyp h432 h6111 h6119
    have hUeq := h.conjClosure_normalizer_eq h432
    have hrc : ∀ X : Subgroup G, rconj X l = conjSubgroup X l := fun X => rfl
    have h6 := hyp.G23_six' (U := conjClosure V (Subgroup.normalizer (ch6ZS T L V : Set G)))
      rfl hl hlN rfl rfl rfl
    rw [hUeq, hrc] at h6
    obtain ⟨s, hsum⟩ := h6.1
    have hXR : U ⊔ conjSubgroup U l ≤ Subgroup.normalizer (R : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hDX : D ≤ U ⊔ conjSubgroup U l := hL1 ▸ hDL'.trans le_sup_left
    have hle := le_commutator_sup_of_sumNatural hsum hXR hDX hdD hdR hodd
    refine le_antisymm (hle.trans (sup_le_sup_left hEA _)) (sup_le ?_ hAR)
    rw [Subgroup.commutator_le]
    intro r hr x hx
    have e : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
    rw [commutatorElement_def, e]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hXR (hDX hx)) r⁻¹).mp
      (R.inv_mem hr))

theorem lemma_6_1_24_four (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    IsO2Trivial (Subgroup.centralizer (ch6ZS T L V : Set G))
      (centralizerMod (ch6ZS T L V) (Subgroup.centralizer (ch6ZS T L V : Set G))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))) := by
  have h17 := (stmt6_1_17 h432 G T M L V n h _ h.isInHS_sup).2.1.1
  rw [inf_eq_right.mpr le_sup_left, h.conjClosure_sup_T_eq] at h17
  exact h17.2.2.2.2.2

end Hyp6116

end CFSG.Quasithin.H13
