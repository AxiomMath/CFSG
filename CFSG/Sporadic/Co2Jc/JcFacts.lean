module

public import CFSG.Sporadic.Co2Jc.ModuleFacts
public import CFSG.Sporadic.Co2Jc.Centralizer

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.EvenSporadicStandard.Co2Std.Exclusion


@[expose] noncomputable def T0 : Subgroup K :=
  (sylS.comap Jc.normalizerMonoidHom).map (normalizer (Jc : Set K)).subtype

private theorem mem_T0_iff {x : K} :
    x ∈ T0 ↔ ∃ n : ↥(normalizer (Jc : Set K)),
      Jc.normalizerMonoidHom n ∈ sylS ∧ (n : K) = x := by
  rw [T0, Subgroup.mem_map]
  exact Iff.rfl

theorem T0_le_normalizer : T0 ≤ normalizer (Jc : Set K) := by
  intro x hx
  obtain ⟨n, -, rfl⟩ := mem_T0_iff.1 hx
  exact n.2

theorem Jc_le_T0 : Jc ≤ T0 := by
  intro x hx
  refine mem_T0_iff.2 ⟨⟨x, Subgroup.le_normalizer hx⟩, ?_, rfl⟩
  have h1 : Jc.normalizerMonoidHom ⟨x, Subgroup.le_normalizer hx⟩ = 1 := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
    show x * (y : K) * x⁻¹ = (y : K)
    rw [Jc_comm hx y.2]
    group
  rw [h1]
  exact sylS.one_mem

theorem centralizer_Jc_eq : centralizer (Jc : Set K) = Jc := by
  refine le_antisymm centralizer_Jc_le fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Jc_comm hx hy).symm

private theorem qA_zero_tA : qA 0 tA = tA := by
  apply Subtype.ext
  rw [coe_qA_apply (k := 0) (by norm_num) (x := tA), coe_tA, qK_comm_z0 (by norm_num)]
  group

private theorem qA_one_tA : qA 1 tA = tA := by
  apply Subtype.ext
  rw [coe_qA_apply (k := 1) (by norm_num) (x := tA), coe_tA, qK_comm_z0 (by norm_num)]
  group

private theorem qWord_tA_of_lt_two {w : List ℕ} (hw : ∀ k ∈ w, k < 2) :
    qWord w tA = tA := by
  induction w with
  | nil => rw [qWord_nil]; rfl
  | cons k w ih =>
    have hk : k < 2 := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [qWord_cons, MulAut.mul_apply, ih hw']
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact qA_zero_tA
    · exact qA_one_tA

private theorem sylW_all_lt_two :
    Data.sylW.all (fun w => w.all fun j => decide (j < 2)) = true := by
  rfl

private theorem sylW_mem_lt_two {w : List ℕ} (hw : w ∈ Data.sylW) : ∀ j ∈ w, j < 2 := by
  have h := sylW_all_lt_two
  rw [List.all_eq_true] at h
  have hw' := h w hw
  rw [List.all_eq_true] at hw'
  intro j hj
  exact of_decide_eq_true (hw' j hj)

private theorem sylW_getD_lt_two {k : ℕ} (hk : k < 4) :
    ∀ j ∈ Data.sylW.getD k [], j < 2 := by
  have hk' : k < Data.sylW.length := by simpa [Data.sylW] using hk
  rw [List.getD_eq_getElem (l := Data.sylW) (n := k) (d := []) hk']
  exact sylW_mem_lt_two (List.getElem_mem hk')

private theorem qWord_flatMap_tA {u : List ℕ} (hu : ∀ k ∈ u, k < 4) :
    qWord (u.flatMap fun j => Data.sylW.getD j []) tA = tA := by
  induction u with
  | nil => rw [List.flatMap_nil, qWord_nil]; rfl
  | cons j u ih =>
    have hj : j < 4 := hu j List.mem_cons_self
    have hu' : ∀ k ∈ u, k < 4 := fun k hk => hu k (List.mem_cons_of_mem _ hk)
    rw [List.flatMap_cons, qWord_append, MulAut.mul_apply, ih hu',
      qWord_tA_of_lt_two (sylW_getD_lt_two hj)]

private theorem sylS_le_stabilizer :
    sylS ≤ MulAction.stabilizer (MulAut ↥Jc) tA := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := exists_word hg
  rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
  exact qWord_flatMap_tA hu

private theorem Qj_eq_normalizerMonoidHom_range :
    Qj = Jc.normalizerMonoidHom.range := by
  rw [Qj, autImage]
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion inf_le_right y, rfl⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨(n : K), ⟨Subgroup.mem_top _, n.2⟩⟩, ?_⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [conjN_apply]
    rfl

theorem card_T0 : Nat.card T0 = 2 ^ 18 := by
  have hmap : Nat.card T0 = Nat.card ↥(sylS.comap Jc.normalizerMonoidHom) := by
    rw [T0]
    exact Subgroup.card_map_of_injective (normalizer (Jc : Set K)).subtype_injective
  rw [hmap]
  let ψ : ↥(sylS.comap Jc.normalizerMonoidHom) →* MulAut ↥Jc :=
    Jc.normalizerMonoidHom.comp (sylS.comap Jc.normalizerMonoidHom).subtype
  have hker : ψ.ker =
      (Jc.normalizerMonoidHom.ker).subgroupOf (sylS.comap Jc.normalizerMonoidHom) := by
    dsimp only [ψ]
    exact MonoidHom.ker_domRestrict (sylS.comap Jc.normalizerMonoidHom)
      Jc.normalizerMonoidHom
  have hle : Jc.normalizerMonoidHom.ker ≤ sylS.comap Jc.normalizerMonoidHom := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    rw [Subgroup.mem_comap, hn]
    exact sylS.one_mem
  have hker_card : Nat.card ψ.ker = 1024 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.normalizerMonoidHom_ker, centralizer_Jc_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.le_normalizer : Jc ≤ normalizer (Jc : Set K))).toEquiv, card_Jc]
  have hrangeQj : Jc.normalizerMonoidHom.range = Qj := Qj_eq_normalizerMonoidHom_range.symm
  have hsyl : sylS ≤ Jc.normalizerMonoidHom.range := by
    rw [hrangeQj]
    exact sylS_le_Qj
  have hrange : ψ.range = sylS := by
    dsimp only [ψ]
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq_self hsyl]
  have hOS := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at hOS
  rw [hrange, card_sylS, hker_card] at hOS
  rw [hOS]
  norm_num

private theorem factorization_natCard_Co2 : (Nat.card K).factorization 2 = 18 := by
  rw [CFSG.Sporadic.Co2Cert.natCard_Co2,
    show (42305421312000 : ℕ) = 2 ^ 18 * 161382375 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem isPGroup_T0 : IsPGroup 2 T0 :=
  IsPGroup.of_card card_T0

theorem eq_T0_of_le {R : Subgroup K} (hR : IsPGroup 2 R) (h : T0 ≤ R) : R = T0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co2Cert.natCard_Co2]; norm_num)
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  have hQ' : Nat.card ↥(Q : Subgroup K) = 2 ^ 18 := by
    rw [Sylow.card_eq_multiplicity (P := Q), factorization_natCard_Co2]
  have hQ : Nat.card ↥(Q : Subgroup K) = Nat.card T0 := by
    rw [hQ', card_T0]
  have hle_card : Nat.card R ≤ Nat.card T0 := by
    rw [← hQ]
    exact Subgroup.card_le_of_le hRQ
  exact (Subgroup.eq_of_le_of_card_ge h hle_card).symm

theorem commute_tA_of_mem_T0 {s : K} (hs : s ∈ T0) : s * (tA : K) = (tA : K) * s := by
  obtain ⟨n, hn, rfl⟩ := mem_T0_iff.1 hs
  have hfix : Jc.normalizerMonoidHom n tA = tA := by
    have h := sylS_le_stabilizer hn
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
  have hconj : (n : K) * (tA : K) * (n : K)⁻¹ = (tA : K) := by
    have h := congrArg Subtype.val hfix
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  calc (n : K) * (tA : K) = ((n : K) * (tA : K) * (n : K)⁻¹) * (n : K) := by group
    _ = (tA : K) * (n : K) := by rw [hconj]

private theorem moduleFacts_autImage :
    @ModuleFacts ↥Jc Jc.toGroup (autImage (⊤ : Subgroup K) Jc) ⟨(tA : K), tA.2⟩ :=
  moduleFacts_Qj

private theorem hE_Jc :
    (⊤ ⊓ centralizer ({(tA : K)} : Set K)) = centralizer ({z0} : Set K) := by
  rw [top_inf_eq, coe_tA]

private theorem perfect_E :
    commutator ↥(⊤ ⊓ centralizer ({(tA : K)} : Set K)) = ⊤ := by
  rw [hE_Jc]
  exact commutator_Cz_eq_top

private noncomputable def subgroupEquiv_E :
    ↥(⊤ ⊓ centralizer ({(tA : K)} : Set K)) ≃* ↥(centralizer ({z0} : Set K)) :=
  MulEquiv.subgroupCongr hE_Jc

private theorem out_E :
    ∀ α : MulAut ↥(⊤ ⊓ centralizer ({(tA : K)} : Set K)),
      ∃ e : ↥(⊤ ⊓ centralizer ({(tA : K)} : Set K)), α = MulAut.conj e :=
  CFSG.Sporadic.Co2Schreier.forall_inner_of_mulEquiv
    (K := ↥(⊤ ⊓ centralizer ({(tA : K)} : Set K)))
    (H := ↥(centralizer ({z0} : Set K))) subgroupEquiv_E exists_eq_conj_Cz

theorem jcFacts_T0 : JcFacts (⊤ : Subgroup K) Jc T0 (tA : K) :=
  { le := le_top
    t_mem := tA.2
    T_le := T0_le_normalizer
    centralizer_eq := by rw [top_inf_eq, centralizer_Jc_eq]
    module := moduleFacts_autImage
    perfectE := perfect_E
    outE := out_E }

end CFSG.Sporadic.Co2Jc
